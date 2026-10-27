module

public import CFSG.RankThree.PartOne.K133C.InnerPlane
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneLines
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneProjection
public import CFSG.Open.StatedDefs
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Assembly.QuasithinDefs
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneOrthogonal
public import CFSG.RankThree.PartOne.S11.TwoActionWiring
public import CFSG.RankThree.PartOne.S12.InputsSec15
public import CFSG.RankThree.PartOne.S12.Sec137
public import CFSG.RankThree.PartOne.S12.Sec15FA
public import CFSG.RankThree.PartOne.S12.Sec15Items
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.theorem_3_6
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CommutatorNormalizer
public import Certificates.Certificate116
public import Certificates.Certificate119
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate45
public import Certificates.Certificate49
public import Certificates.Certificate53
public import Certificates.Certificate59
public import Certificates.Certificate68
public import Certificates.Certificate72

public section

namespace CFSG.RankThree.PartOne.K133C

open Matrix CFSG CFSG.RankThree.PartOne.KCUnitaryPlane CFSG.Assembly.LowTwoRank

section Algebra

variable {K : Type} [Field K] {n : ℕ}

@[expose] def radSub (W : Submodule K (Fin n → K)) : Subgroup (GL (Fin n) K) where
  carrier := {g | (∀ w ∈ W, (g : Matrix (Fin n) (Fin n) K) *ᵥ w = w) ∧
    ∀ v, (g : Matrix (Fin n) (Fin n) K) *ᵥ v - v ∈ W}
  one_mem' := ⟨fun w _ => by simp, fun v => by simp⟩
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨fun w hw => ?_, fun v => ?_⟩
    · rw [Units.val_mul, ← mulVec_mulVec, hb1 w hw, ha1 w hw]
    · have h : ((a * b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v - v =
          ((a : Matrix (Fin n) (Fin n) K) *ᵥ ((b : Matrix (Fin n) (Fin n) K) *ᵥ v) -
            (b : Matrix (Fin n) (Fin n) K) *ᵥ v) +
          ((b : Matrix (Fin n) (Fin n) K) *ᵥ v - v) := by
        rw [Units.val_mul, ← mulVec_mulVec]
        abel
      rw [h]
      exact W.add_mem (ha2 _) (hb2 v)
  inv_mem' := by
    rintro g ⟨hg1, hg2⟩
    have hinv : ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (g : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hinv' : (g : Matrix (Fin n) (Fin n) K) *
        ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    refine ⟨fun w hw => ?_, fun v => ?_⟩
    · have := congrArg (fun M : Matrix (Fin n) (Fin n) K => M *ᵥ w) hinv
      simp only [← mulVec_mulVec, one_mulVec, hg1 w hw] at this
      exact this
    · set u : Fin n → K := ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v with hu
      have hgu : (g : Matrix (Fin n) (Fin n) K) *ᵥ u = v := by
        rw [hu, mulVec_mulVec, hinv', one_mulVec]
      have h2 := hg2 u
      rw [hgu] at h2
      have : u - v = -(v - u) := by abel
      show u - v ∈ W
      rw [this]
      exact W.neg_mem h2

theorem radSub_sq [CharP K 2] {W : Submodule K (Fin n → K)} {g : GL (Fin n) K}
    (hg : g ∈ radSub W) : g * g = 1 := by
  obtain ⟨hg1, hg2⟩ := hg
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hsq : (g : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [Matrix.ext_iff_mulVec]
    intro v
    rw [← mulVec_mulVec, one_mulVec]
    set u := (g : Matrix (Fin n) (Fin n) K) *ᵥ v - v with hu
    have hguv : (g : Matrix (Fin n) (Fin n) K) *ᵥ v = v + u := by rw [hu]; abel
    calc (g : Matrix (Fin n) (Fin n) K) *ᵥ ((g : Matrix (Fin n) (Fin n) K) *ᵥ v)
        = (g : Matrix (Fin n) (Fin n) K) *ᵥ (v + u) := by rw [← hguv]
      _ = (g : Matrix (Fin n) (Fin n) K) *ᵥ v + (g : Matrix (Fin n) (Fin n) K) *ᵥ u := mulVec_add _ _ _
      _ = (v + u) + u := by rw [hguv, hg1 u (hg2 v)]
      _ = v + (2 : K) • u := by rw [two_smul]; abel
      _ = v := by rw [h2, zero_smul, add_zero]
  exact Units.ext (by rw [Units.val_mul, hsq, Units.val_one])

theorem radSub_isPGroup [CharP K 2] (W : Submodule K (Fin n → K)) : IsPGroup 2 (radSub W) :=
  fun g => ⟨1, by
    rw [pow_one, pow_two]
    exact Subtype.ext (radSub_sq g.2)⟩

theorem det_eq_one_of_mul_self [CharP K 2] {g : GL (Fin n) K} (h : g * g = 1) :
    (g : Matrix (Fin n) (Fin n) K).det = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hsq : (g : Matrix (Fin n) (Fin n) K).det ^ 2 = 1 := by
    rw [sq, ← det_mul, ← Units.val_mul, h, Units.val_one, det_one]
  have h3 : ((g : Matrix (Fin n) (Fin n) K).det - 1) ^ 2 = 0 := by
    linear_combination hsq + (1 - (g : Matrix (Fin n) (Fin n) K).det) * h2
  exact sub_eq_zero.1 ((pow_eq_zero_iff (by norm_num)).1 h3)

theorem radSub_le_statedSL [CharP K 2] (W : Submodule K (Fin n → K)) :
    radSub W ≤ StatedSL n K := fun _ hg =>
  Subgroup.subset_closure (det_eq_one_of_mul_self (radSub_sq hg))

theorem radSub_normalized {W : Submodule K (Fin n → K)} {h : GL (Fin n) K}
    (hh : ∀ w ∈ W, (h : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W)
    (hh' : ∀ w ∈ W, ((h⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W)
    {g : GL (Fin n) K} (hg : g ∈ radSub W) : h * g * h⁻¹ ∈ radSub W := by
  obtain ⟨hg1, hg2⟩ := hg
  have hhh : (h : Matrix (Fin n) (Fin n) K) *
      ((h⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  refine ⟨fun w hw => ?_, fun v => ?_⟩
  · rw [Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec,
      hg1 _ (hh' w hw), mulVec_mulVec, hhh, one_mulVec]
  · set u : Fin n → K := ((h⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v with hu
    have hhu : (h : Matrix (Fin n) (Fin n) K) *ᵥ u = v := by
      rw [hu, mulVec_mulVec, hhh, one_mulVec]
    have : (((h * g * h⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) *ᵥ v - v =
        (h : Matrix (Fin n) (Fin n) K) *ᵥ ((g : Matrix (Fin n) (Fin n) K) *ᵥ u - u) := by
      rw [mulVec_sub, hhu, Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec]
    rw [this]
    exact hh _ (hg2 u)

end Algebra

section PlaneLemma

variable {K : Type} [Field K]

theorem exists_fixed_of_plane {V : Type*} [AddCommGroup V] [Module K V] [Nontrivial V]
    {P : Type*} [Group P] [Fintype P] {p : ℕ} (hP : IsPlane p P) (hpK : (p : K) ≠ 0)
    (ρ : P →* LinearMap.GeneralLinearGroup K V) :
    ∃ x : P, x ≠ 1 ∧ ∃ v : V, v ≠ 0 ∧ act ρ x v = v := by
  classical
  by_contra hcon
  push Not at hcon
  have hfix : ∀ (L : Subgroup P), L ≠ ⊥ → ∀ v : V, sumOp ρ L v = 0 := by
    intro L hL v
    obtain ⟨⟨y, hyL⟩, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hL
    have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
    have h1 : act ρ y (sumOp ρ L v) = sumOp ρ L v := by
      have := congrArg (fun f : Module.End K V => f v) (mul_sumOp ρ hyL)
      simpa using this
    by_contra h0
    exact hcon y hy1' _ h0 h1
  have hp1 : p ≠ 1 := hP.prime.one_lt.ne'
  have hsum : ∑ L ∈ lines p P, sumOp ρ L = 0 := by
    refine Finset.sum_eq_zero fun L hL => ?_
    have hLc : Nat.card L = p := mem_lines.1 hL
    have hLb : L ≠ ⊥ := by
      rintro rfl
      rw [Subgroup.card_bot] at hLc
      exact hp1 hLc.symm
    exact LinearMap.ext fun v => hfix L hLb v
  have htop : sumOp ρ ⊤ = 0 := by
    have hTb : (⊤ : Subgroup P) ≠ ⊥ := by
      intro h
      have h1 : Nat.card (⊤ : Subgroup P) = 1 := by rw [h, Subgroup.card_bot]
      rw [Subgroup.card_top, hP.card] at h1
      have : p ^ 2 ≠ 1 := by
        have := hP.prime.one_lt
        exact (Nat.one_lt_pow (by norm_num) this).ne'
      exact this h1
    exact LinearMap.ext fun v => hfix ⊤ hTb v
  have key := hP.sum_lines_sumOp ρ
  rw [hsum, htop, add_zero] at key
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have h1 := congrArg (fun f : Module.End K V => f v) key
  simp only [LinearMap.zero_apply, LinearMap.smul_apply, Module.End.one_apply] at h1
  exact hv ((smul_eq_zero.1 h1.symm).resolve_left hpK)

@[expose] def fixSub {n : ℕ} (x : GL (Fin n) K) : Submodule K (Fin n → K) where
  carrier := {v | (x : Matrix (Fin n) (Fin n) K) *ᵥ v = v}
  zero_mem' := by simp
  add_mem' := fun {a b} ha hb => by
    change _ *ᵥ a = a at ha
    change _ *ᵥ b = b at hb
    change _ *ᵥ (a + b) = a + b
    rw [mulVec_add, ha, hb]
  smul_mem' := fun c a ha => by
    change _ *ᵥ a = a at ha
    change _ *ᵥ (c • a) = c • a
    rw [mulVec_smul, ha]

theorem dual_apply_eq {n : ℕ} (f : Module.Dual K (Fin n → K)) (u : Fin n → K) :
    f u = (fun j => f (Pi.single j 1)) ⬝ᵥ u := by
  conv_lhs => rw [← Finset.univ_sum_single u]
  simp only [map_sum, dotProduct]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : (Pi.single j (u j) : Fin n → K) = u j • Pi.single j 1 := by
    ext i
    by_cases h : i = j <;> simp [h]
  rw [this, map_smul, smul_eq_mul, mul_comm]

theorem one_add_pow_of_sq_zero {n : ℕ} {N : Matrix (Fin n) (Fin n) K} (hN : N * N = 0) (k : ℕ) :
    (1 + N) ^ k = 1 + (k : K) • N := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih]
    simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, hN, smul_zero, add_zero,
      Nat.cast_succ, add_smul, one_smul]
    abel

theorem exists_moving_radSub [CharP K 2] {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 0 < n)
    (P : Subgroup (GL (Fin n) K)) [Finite P] (hPe : IsElementaryAbelian p P)
    (hc : Nat.card P = p ^ 2) :
    ∃ W : Submodule K (Fin n → K),
      (∀ h ∈ P, ∀ w ∈ W, (h : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W) ∧
      ∃ g ∈ radSub W, ∃ h ∈ P, h * g * h⁻¹ ≠ g := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype P := Fintype.ofFinite P
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hpK : (p : K) ≠ 0 := by
    intro h
    have := (CharP.cast_eq_zero_iff K 2 p).1 h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 this).symm
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  let ρ : ↥P →* LinearMap.GeneralLinearGroup K (Fin n → K) :=
    (Matrix.GeneralLinearGroup.toLin :
      GL (Fin n) K ≃* LinearMap.GeneralLinearGroup K (Fin n → K)).toMonoidHom.comp P.subtype
  have hρ : ∀ (x : ↥P) (v : Fin n → K),
      act ρ x v = ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v := fun x v => rfl
  have hpow : ∀ x : ↥P, x ^ p = 1 := fun x =>
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p p P) x
  have hplane : IsPlane p ↥P := ⟨hp, hc, hpow⟩
  obtain ⟨x, hx1, v₀, hv₀, hxv₀⟩ := exists_fixed_of_plane hplane hpK ρ
  rw [hρ] at hxv₀
  set xg : GL (Fin n) K := (x : GL (Fin n) K) with hxg
  set W : Submodule K (Fin n → K) := fixSub xg with hW
  have hcomm : ∀ h ∈ P, xg * h = h * xg := fun h hh =>
    congrArg Subtype.val (hPe.is_comm.comm x ⟨h, hh⟩)
  have hstab : ∀ h ∈ P, ∀ w ∈ W, (h : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W := by
    intro h hh w hw
    have hw' : (xg : Matrix (Fin n) (Fin n) K) *ᵥ w = w := hw
    show (xg : Matrix (Fin n) (Fin n) K) *ᵥ ((h : Matrix (Fin n) (Fin n) K) *ᵥ w) =
      (h : Matrix (Fin n) (Fin n) K) *ᵥ w
    rw [mulVec_mulVec, ← Units.val_mul, hcomm h hh, Units.val_mul, ← mulVec_mulVec, hw']
  refine ⟨W, hstab, ?_⟩
  obtain ⟨u, hu⟩ : ∃ u : Fin n → K, (xg : Matrix (Fin n) (Fin n) K) *ᵥ u - u ∉ W := by
    by_contra hall
    push Not at hall
    have hN : ((xg : Matrix (Fin n) (Fin n) K) - 1) * ((xg : Matrix (Fin n) (Fin n) K) - 1) = 0 := by
      rw [Matrix.ext_iff_mulVec]
      intro v
      have e : ∀ w : Fin n → K, ((xg : Matrix (Fin n) (Fin n) K) - 1) *ᵥ w =
          (xg : Matrix (Fin n) (Fin n) K) *ᵥ w - w := fun w => by rw [sub_mulVec, one_mulVec]
      have h1 : (xg : Matrix (Fin n) (Fin n) K) *ᵥ ((xg : Matrix (Fin n) (Fin n) K) *ᵥ v - v) =
          (xg : Matrix (Fin n) (Fin n) K) *ᵥ v - v := hall v
      rw [← mulVec_mulVec, zero_mulVec, e, e, h1, sub_self]
    have hpowx : (xg : Matrix (Fin n) (Fin n) K) ^ p = 1 := by
      have := congrArg (fun y : ↥P => ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) (hpow x)
      simpa using this
    have hxN : (xg : Matrix (Fin n) (Fin n) K) = 1 + ((xg : Matrix (Fin n) (Fin n) K) - 1) := by
      abel
    rw [hxN, one_add_pow_of_sq_zero hN p] at hpowx
    have hz : (p : K) • ((xg : Matrix (Fin n) (Fin n) K) - 1) = 0 := by
      have := congrArg (fun M => M - 1) hpowx
      simpa using this
    have hz' : (xg : Matrix (Fin n) (Fin n) K) - 1 = 0 := by
      rw [Matrix.ext_iff_mulVec] at hz ⊢
      intro v
      have h3 := hz v
      rw [smul_mulVec, zero_mulVec] at h3
      rw [zero_mulVec]
      exact (smul_eq_zero.1 h3).resolve_left hpK
    have hx1' : (xg : Matrix (Fin n) (Fin n) K) = 1 := sub_eq_zero.1 hz'
    exact hx1 (Subtype.ext (Units.ext hx1'))
  obtain ⟨f, hfy, hfW⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hu inferInstance
  set φ : Fin n → K := fun j => f (Pi.single j 1) with hφ
  have hφW : ∀ w ∈ W, φ ⬝ᵥ w = 0 := by
    intro w hw
    rw [← dual_apply_eq]
    have : f w ∈ W.map f := Submodule.mem_map_of_mem hw
    rw [hfW] at this
    exact (Submodule.mem_bot K).1 this
  have hφy : φ ⬝ᵥ ((xg : Matrix (Fin n) (Fin n) K) *ᵥ u - u) ≠ 0 := by
    rw [← dual_apply_eq]
    exact hfy
  have hv₀W : v₀ ∈ W := hxv₀
  set R : Matrix (Fin n) (Fin n) K := vecMulVec v₀ φ with hR
  have hR2 : R * R = 0 := by
    rw [hR, vecMulVec_mul_vecMulVec, hφW v₀ hv₀W, zero_smul, vecMulVec_zero]
  have hRw : ∀ w : Fin n → K, R *ᵥ w = (φ ⬝ᵥ w) • v₀ := fun w => by
    rw [hR, vecMulVec_mulVec, op_smul_eq_smul]
  have hg2 : (1 + R) * (1 + R) = 1 := by
    have : (1 + R) * (1 + R) = 1 + (R + R) + R * R := by
      simp only [add_mul, mul_add, one_mul, mul_one]
      abel
    rw [this, hR2, add_zero, ← two_smul K R, h2, zero_smul, add_zero]
  let g : GL (Fin n) K := ⟨1 + R, 1 + R, hg2, hg2⟩
  have hgmem : g ∈ radSub W := by
    refine ⟨fun w hw => ?_, fun v => ?_⟩
    · show (1 + R) *ᵥ w = w
      rw [add_mulVec, one_mulVec, hRw, hφW w hw, zero_smul, add_zero]
    · show (1 + R) *ᵥ v - v ∈ W
      rw [add_mulVec, one_mulVec, hRw, add_sub_cancel_left]
      exact W.smul_mem _ hv₀W
  refine ⟨g, hgmem, xg, x.2, fun hEq => ?_⟩
  have hxg' : xg * g = g * xg := by
    have := congrArg (fun y => y * xg) hEq
    simpa [mul_assoc] using this
  have hxR : (xg : Matrix (Fin n) (Fin n) K) * R = R * (xg : Matrix (Fin n) (Fin n) K) := by
    have := congrArg (fun y : GL (Fin n) K => (y : Matrix (Fin n) (Fin n) K)) hxg'
    simp only [Units.val_mul] at this
    have h1 : (xg : Matrix (Fin n) (Fin n) K) * (1 + R) = (1 + R) * (xg : Matrix (Fin n) (Fin n) K) := this
    rw [mul_add, add_mul, mul_one, one_mul] at h1
    exact add_left_cancel h1
  have := congrArg (fun M : Matrix (Fin n) (Fin n) K => M *ᵥ u) hxR
  simp only [← mulVec_mulVec, hRw, mulVec_smul, hxv₀] at this
  have h3 : (φ ⬝ᵥ ((xg : Matrix (Fin n) (Fin n) K) *ᵥ u - u)) • v₀ = 0 := by
    rw [dotProduct_sub, sub_smul, ← this, sub_self]
  exact hφy ((smul_eq_zero.1 h3).resolve_right hv₀)

end PlaneLemma

end CFSG.RankThree.PartOne.K133C
