module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Position
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.StepACore
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.IDPSU
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.IDCommute
public import CFSG.LieType.Universal.Unitary.Extras
public import CFSG.LieType.BorelTits.UnitaryForm
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.FEPSU
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelSelfDualPSU
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelDualPairPSU
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.DualPairCharPSU
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.DualPairLiftPSU
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoRootConversePSU
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockRankDvd
public import CFSG.GroupTheory.OddKernelImage
public import CFSG.LocalAnalysis.StandardType.SUCenterOdd
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWFusion
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWSylow
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWZero

public section

namespace CFSG.StandardType.ClassicalPosition

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos

private noncomputable abbrev nbrPSU_F (g : ℕ) : Type := GaloisField 2 (2 * (g + 1))

private noncomputable abbrev nbrPSU_sigmae (g : ℕ) : nbrPSU_F g ≃+* nbrPSU_F g :=
  CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)

private noncomputable abbrev nbrPSU_sigma (g : ℕ) : nbrPSU_F g →+* nbrPSU_F g :=
  (nbrPSU_sigmae g).toRingHom

private lemma nbrPSU_isGLLift_inv {U X ι F : Type} [Group U] [Finite U] [Group X] [Fintype ι]
    [DecidableEq ι] [Field F] {j : U →* GL ι F} (hj : Function.Injective j) {ψ : U →* X}
    {s : GL ι F} {b : X} (hs : IsGLLift j ψ s b) : IsGLLift j ψ s⁻¹ b⁻¹ := by
  classical
  let c : U → U := fun u => Classical.choose (hs u)
  have hc_j : ∀ u, j (c u) = s * j u * s⁻¹ := fun u => (Classical.choose_spec (hs u)).1
  have hc_b : ∀ u, b⁻¹ * ψ u * b = ψ (c u) := fun u => (Classical.choose_spec (hs u)).2
  have hc_inj : Function.Injective c := by
    intro a b' hab
    have h : j (c a) = j (c b') := congrArg j hab
    rw [hc_j a, hc_j b'] at h
    exact hj (mul_left_cancel (mul_right_cancel h))
  have hc_surj : Function.Surjective c := (Finite.injective_iff_surjective).mp hc_inj
  intro u
  obtain ⟨u', hu'⟩ := hc_surj u
  refine ⟨u', ?_, ?_⟩
  · have h := hc_j u'
    rw [hu'] at h
    rw [h]
    group
  · have h := hc_b u'
    rw [hu'] at h
    rw [← h]
    group

private lemma nbrPSU_isGLLift_zpow {U X ι F : Type} [Group U] [Finite U] [Group X] [Fintype ι]
    [DecidableEq ι] [Field F] {j : U →* GL ι F} (hj : Function.Injective j) {ψ : U →* X}
    {s : GL ι F} {b : X} (hs : IsGLLift j ψ s b) (k : ℤ) :
    IsGLLift j ψ (s ^ k) (b ^ k) := by
  obtain ⟨n, h | h⟩ := Int.eq_nat_or_neg k
  · rw [h]
    simpa only [zpow_natCast] using hs.pow n
  · rw [h]
    have hinv : IsGLLift j ψ s⁻¹ b⁻¹ := nbrPSU_isGLLift_inv hj hs
    have h1 : IsGLLift j ψ ((s⁻¹) ^ n) ((b⁻¹) ^ n) := hinv.pow n
    have hs' : s ^ (-(n : ℤ)) = (s⁻¹) ^ n := by
      rw [zpow_neg, zpow_natCast]
      group
    have hb' : b ^ (-(n : ℤ)) = (b⁻¹) ^ n := by
      rw [zpow_neg, zpow_natCast]
      group
    rw [hs', hb']
    exact h1

private lemma nbrPSU_l3_blockIdempotent
    (n g : ℕ) (S_e : Set (GL (Fin n) (nbrPSU_F g)))
    (hS_e : ∀ s ∈ S_e, ∀ s' ∈ S_e, Commute s s')
    (K' : Subgroup ↥(Unitary.SU (nbrPSU_sigmae g) n))
    (hK' : IsComponentOf K' ((Subgroup.centralizer S_e).comap
        ((Unitary.SU (nbrPSU_sigmae g) n).subtype))) :
    ∃ ε : Matrix (Fin n) (Fin n) (nbrPSU_F g),
      IsPrimAdjIdemIn (nbrPSU_sigma g) (Unitary.antidiag n)
        (Algebra.adjoin (nbrPSU_F g) (Units.val '' S_e)) ε ∧
      IsComponentOf K'
        ⁅glBlockCentralizer ((Unitary.SU (nbrPSU_sigmae g) n).subtype) S_e ε,
          glBlockCentralizer ((Unitary.SU (nbrPSU_sigmae g) n).subtype) S_e ε⁆ := by
  exact exists_isComponentOf_glBlockCentralizer_PSU (F := nbrPSU_F g) (f := g + 1) n S_e hS_e hK'

private lemma nbrPSU_l4_blockDegree
    {X : Type} [Group X] (n g : ℕ) (ψ : ↥(Unitary.SU (nbrPSU_sigmae g) n) →* X)
    (hψ : ψ.ker ≤ Subgroup.center ↥(Unitary.SU (nbrPSU_sigmae g) n))
    (S_e : Set (GL (Fin n) (nbrPSU_F g)))
    (hSU : ∀ s ∈ S_e, Unitary.conjTr (nbrPSU_sigmae g)
        (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) * Unitary.antidiag n *
        (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) = Unitary.antidiag n)
    (hS_e : ∀ s ∈ S_e, ∀ s' ∈ S_e, Commute s s')
    (hodd : ∀ s ∈ S_e, Odd (orderOf s))
    {ε : Matrix (Fin n) (Fin n) (nbrPSU_F g)}
    (hε : IsPrimAdjIdemIn (nbrPSU_sigma g) (Unitary.antidiag n)
        (Algebra.adjoin (nbrPSU_F g) (Units.val '' S_e)) ε)
    {K' : Subgroup ↥(Unitary.SU (nbrPSU_sigmae g) n)}
    (hK' : IsComponentOf K'
        ⁅glBlockCentralizer ((Unitary.SU (nbrPSU_sigmae g) n).subtype) S_e ε,
          glBlockCentralizer ((Unitary.SU (nbrPSU_sigmae g) n).subtype) S_e ε⁆)
    (hnoext : ¬ GGSixLSevenFieldExtCase (K'.map ψ) .PSU (g + 1)) :
    ∃ e : Matrix (Fin n) (Fin n) (nbrPSU_F g),
      IsPrimIdemIn (Algebra.adjoin (nbrPSU_F g) (Units.val '' S_e)) e ∧ e * ε = e ∧
      blockDegree (Algebra.adjoin (nbrPSU_F g) (Units.val '' S_e)) e < 2 ∧
      (e = ε ∨ (e ≠ ε ∧ formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e ≠ e ∧
        ε = e + formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e)) := by
  obtain ⟨e, heprim, heε, hsplit⟩ :=
    exists_isPrimIdemIn_of_isPrimAdjIdemIn_PSU n g S_e hSU hS_e hε
  refine ⟨e, heprim, heε, ?_, hsplit⟩
  by_contra hlt
  have hlt2 : 2 ≤ blockDegree (Algebra.adjoin (nbrPSU_F g) (Units.val '' S_e)) e := by omega
  have hc : Nat.card (nbrPSU_F g) = (2 ^ (g + 1)) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul 2 (g + 1) (by omega)
  exact hnoext (ggSixLSevenFieldExtCase_PSU (F := nbrPSU_F g) (f := g + 1) hc n ψ hψ
    S_e hSU hS_e hodd hε hK' heprim heε hlt2)

private theorem nbrPSU_odd_card_sub_one {F : Type} {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f) : Odd (Nat.card F - 1) := by
  have hpowF : Nat.card F = 2 * 2 ^ (2 * f - 1) := by
    calc Nat.card F = (2 ^ f) ^ 2 := hc
      _ = 2 ^ (f * 2) := by rw [pow_mul]
      _ = 2 ^ (2 * f) := by rw [mul_comm f 2]
      _ = 2 * 2 ^ (2 * f - 1) := by
            conv_lhs => rw [show 2 * f = (2 * f - 1) + 1 by omega]
            rw [pow_add, pow_one]
            ring
  rw [hpowF]
  refine ⟨2 ^ (2 * f - 1) - 1, ?_⟩
  have hX : 1 ≤ 2 ^ (2 * f - 1) := Nat.one_le_two_pow
  omega

private theorem nbrPSU_lift_odd_scalar {F : Type} [Field F] [Finite F] [CharP F 2] {f n : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (hn : 3 ≤ n) (hf : 1 ≤ f)
    {X : Type} [Group X]
    (ψ : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {d : X}
    (hdp : d ^ p = 1) {s : GL (Fin n) F}
    (hs : IsGLLift (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype
      ψ s d) :
    Odd (orderOf s) ∧ ∃ c : F, (s : Matrix (Fin n) (Fin n) F) ^ p =
      Matrix.scalar (Fin n) c := by
  haveI : Fintype F := Fintype.ofFinite F
  have hsp : IsGLLift (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype
      ψ (s ^ p) 1 := by
    have h := hs.pow p
    rwa [hdp] at h
  obtain ⟨c, hc_eq⟩ := isGLLift_unique_PSU hc n ψ hψ hsp isGLLift_one
  have hsmat : (s : Matrix (Fin n) (Fin n) F) ^ p = Matrix.scalar (Fin n) c := by
    have h := hc_eq
    rw [inv_one, one_mul] at h
    simpa only [Units.val_pow_eq_pow_val] using h
  have hcne : c ≠ 0 := by
    have hunit : IsUnit ((s : Matrix (Fin n) (Fin n) F) ^ p) := IsUnit.pow p ⟨s, rfl⟩
    have hm : IsUnit ((Matrix.scalar (Fin n) c : Matrix (Fin n) (Fin n) F).det) := by
      rw [← hsmat]
      exact (Matrix.isUnit_iff_isUnit_det
        (A := (s : Matrix (Fin n) (Fin n) F) ^ p)).mp hunit
    have hdet : (Matrix.scalar (Fin n) c : Matrix (Fin n) (Fin n) F).det = c ^ n := by
      rw [Matrix.scalar_apply, Matrix.det_diagonal]
      simp [Finset.prod_const, Fintype.card_fin]
    rw [hdet] at hm
    have hn0 : n ≠ 0 := by omega
    exact ((isUnit_pow_iff (a := c) (n := n) hn0).mp hm).ne_zero
  refine ⟨?_, c, hsmat⟩
  let u : Fˣ := Units.mk0 c hcne
  have hspu : s ^ p = Matrix.GeneralLinearGroup.scalar (Fin n) u := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hsmat, Matrix.GeneralLinearGroup.coe_scalar]
    rfl
  have hpow1 : s ^ (p * orderOf u) = 1 := by
    rw [pow_mul, hspu, ← map_pow, pow_orderOf_eq_one, map_one]
  have hdvd : orderOf s ∣ p * orderOf u := orderOf_dvd_iff_pow_eq_one.mpr hpow1
  have hoddF : Odd (Nat.card F - 1) := nbrPSU_odd_card_sub_one hc hf
  have hu_pow : u ^ (Nat.card F - 1) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card_sub_one_eq_one (u : F) (Units.ne_zero u)
  have hodd_u : Odd (orderOf u) :=
    Odd.of_dvd_nat hoddF (orderOf_dvd_iff_pow_eq_one.mpr hu_pow)
  have hodd_p : Odd p := hp.odd_of_ne_two hp2
  exact Odd.of_dvd_nat (Nat.odd_mul.mpr ⟨hodd_p, hodd_u⟩) hdvd

private lemma nbrPSU_l1_liftDataChar
    {X : Type} [Group X] [Finite X] (n g : ℕ) (ψ : ↥(Unitary.SU (nbrPSU_sigmae g) n) →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X) (hH : GGSixPosHyp .PSU n (g + 1) ψ p G₀ B₁ D J L x)
    (e : X) (he : e ∈ D) :
    ∃ (S : Set (GL (Fin n) (nbrPSU_F g))) (J' : Subgroup ↥(Unitary.SU (nbrPSU_sigmae g) n))
      (s_e : GL (Fin n) (nbrPSU_F g)),
      (∀ s : GL (Fin n) (nbrPSU_F g), s ∈ S ↔
        Unitary.conjTr (nbrPSU_sigmae g) (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) *
            Unitary.antidiag n * (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) = Unitary.antidiag n ∧
          ∃ d ∈ D, IsGLLift ((Unitary.SU (nbrPSU_sigmae g) n).subtype) ψ s d) ∧
      (∀ s ∈ S, Unitary.conjTr (nbrPSU_sigmae g) (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) *
          Unitary.antidiag n * (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) = Unitary.antidiag n) ∧
      (∀ s ∈ S, ∀ s' ∈ S, Commute s s') ∧
      (∀ s ∈ S, Odd (orderOf s)) ∧
      (∀ s ∈ S, ∃ c : nbrPSU_F g,
          (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) ^ p = Matrix.scalar (Fin n) c) ∧
      IsComponentOf J' ((Subgroup.centralizer S).comap
          ((Unitary.SU (nbrPSU_sigmae g) n).subtype)) ∧
      J'.map ψ = J ∧
      (Unitary.conjTr (nbrPSU_sigmae g) (s_e : Matrix (Fin n) (Fin n) (nbrPSU_F g)) *
          Unitary.antidiag n * (s_e : Matrix (Fin n) (Fin n) (nbrPSU_F g)) =
        Unitary.antidiag n) ∧
      IsGLLift ((Unitary.SU (nbrPSU_sigmae g) n).subtype) ψ s_e e := by
  have hH' : GGSixPosHyp .PSU n (g + 1) ψ p G₀ B₁ D J L x := hH
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩ := hH'
  have hc : Nat.card (nbrPSU_F g) = (2 ^ (g + 1)) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul 2 (g + 1) (by omega)
  have hadm : CFSG.Open.StatedLieAdmissible .PSU n 2 (g + 1) := h3.admissible
  have hn : 3 ≤ n := hadm.2.2.1
  have hB₁N : B₁ ≤ Subgroup.normalizer (ψ.range : Set X) := by
    have hψrange : (ψ.range : Set X) = (G₀ : Set X) :=
      congrArg (fun H : Subgroup X => (H : Set X)) h1
    rw [hψrange]
    exact h7
  have hdiag : ∀ b ∈ B₁, GGPsiInnerDiag (Unitary.rootDatum hc n) ψ b :=
    fun b hb => h8 b hb
  have hf : 1 ≤ g + 1 := hadm.2.1
  have hpow9 : ∀ b ∈ B₁, b ^ p = 1 := by
    obtain ⟨-, hpow⟩ := h9
    exact hpow
  let P : GL (Fin n) (nbrPSU_F g) → Prop := fun s =>
    Unitary.conjTr (nbrPSU_sigmae g) (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) *
      Unitary.antidiag n * (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) = Unitary.antidiag n
  let S : Set (GL (Fin n) (nbrPSU_F g)) :=
    {s | P s ∧ ∃ d ∈ D, IsGLLift ((Unitary.SU (nbrPSU_sigmae g) n).subtype) ψ s d}
  have hDp : ∀ d ∈ D, d ^ p = 1 := fun d hd => hpow9 d (h11 hd)
  have hHN : p ∣ 2 ^ (g + 1) + 1 →
      B₁ ⊓ Subgroup.centralizer (ψ.range : Set X) = ⊥ ∧ p ^ (n - 3) ≤ Nat.card B₁ := by
    intro hpdiv
    obtain ⟨hint, hle⟩ := h30 (Or.inr ⟨rfl, hpdiv⟩)
    refine ⟨?_, hle⟩
    have hψrange : (ψ.range : Set X) = (G₀ : Set X) :=
      congrArg (fun H : Subgroup X => (H : Set X)) h1
    rw [hψrange]
    exact hint
  have h15' : IsComponentOf J (ψ.range ⊓ Subgroup.centralizer (D : Set X)) := by
    rw [show ψ.range = G₀ from h1]
    exact h15
  have hlift : ∀ d ∈ D, ∃ s : GL (Fin n) (nbrPSU_F g),
      P s ∧ IsGLLift ((Unitary.SU (nbrPSU_sigmae g) n).subtype) ψ s d := by
    intro d hd
    obtain ⟨s, hsP, hsl⟩ := exists_isGLLift_PSU hc n hn ψ h2 (hB₁N (h11 hd)) (hdiag d (h11 hd))
    exact ⟨s, hsP, hsl⟩
  have hSU : ∀ s ∈ S, Unitary.conjTr (nbrPSU_sigmae g) (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) *
      Unitary.antidiag n * (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) = Unitary.antidiag n :=
    fun s hs => hs.1
  have hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s' := by
    intro s hs s' hs'
    obtain ⟨-, d, hd, hsl⟩ := hs
    obtain ⟨-, d', hd', hsl'⟩ := hs'
    exact isGLLift_commute_PSU hc n ψ h2 hadm h5 h6 hB₁N hdiag h9 h10 hHN
      (h11 hd) (h11 hd') hsl hsl'
  have hodd : ∀ s ∈ S, Odd (orderOf s) := by
    intro s hs
    obtain ⟨-, d, hd, hsl⟩ := hs
    exact (nbrPSU_lift_odd_scalar hc hn hf ψ h2 h5 h6 (hDp d hd) hsl).1
  have hpowS : ∀ s ∈ S, ∃ c : nbrPSU_F g,
      (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) ^ p = Matrix.scalar (Fin n) c := by
    intro s hs
    obtain ⟨-, d, hd, hsl⟩ := hs
    exact (nbrPSU_lift_odd_scalar hc hn hf ψ h2 h5 h6 (hDp d hd) hsl).2
  obtain ⟨J', hJ'comp, hJ'map⟩ :=
    StepA.exists_isComponentOf_comap_lift_of_isGLLift ((Unitary.SU (nbrPSU_sigmae g) n).subtype)
      (Subgroup.subtype_injective _) ψ h2 P h15' hlift
  obtain ⟨s_e, hs_e_iso, hs_e_lift⟩ :=
    exists_isGLLift_PSU hc n hn ψ h2 (hB₁N (h11 he)) (hdiag e (h11 he))
  exact ⟨S, J', s_e, fun s => Iff.rfl, hSU, hS, hodd, hpowS, hJ'comp, hJ'map, hs_e_iso, hs_e_lift⟩

private lemma nbrPSU_sigma_involutive (g : ℕ) (x : nbrPSU_F g) :
    nbrPSU_sigma g (nbrPSU_sigma g x) = x := by
  have hc : Nat.card (nbrPSU_F g) = (2 ^ (g + 1)) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul 2 (g + 1) (by omega)
  exact CFSG.LieType.BorelTits.unitaryInvolution_involutive hc x

private lemma nbrPSU_antidiag_transpose_map (n g : ℕ) :
    Matrix.transpose (((Unitary.antidiag n : Matrix (Fin n) (Fin n) (nbrPSU_F g)).map
      (nbrPSU_sigma g))) = Unitary.antidiag n := by
  ext i j
  rw [Matrix.transpose_apply, Matrix.map_apply]
  have hanti : ∀ (a b : Fin n),
      (Unitary.antidiag n : Matrix (Fin n) (Fin n) (nbrPSU_F g)) a b
      = if b = a.rev then 1 else 0 := fun a b => rfl
  rw [hanti j i, hanti i j]
  by_cases h : i = j.rev
  · have h2 : j = i.rev := by rw [h, Fin.rev_rev]
    rw [if_pos h, if_pos h2, map_one]
  · have h2 : j ≠ i.rev := by
      intro h2
      apply h
      rw [h2, Fin.rev_rev]
    rw [if_neg h, if_neg h2, map_zero]

private lemma nbrPSU_unitaryTransvection_mem (n g : ℕ) {v : Fin n → nbrPSU_F g} (hv : v ≠ 0)
    (hviso : Matrix.vecMul (fun i => nbrPSU_sigma g (v i)) (Unitary.antidiag n) ⬝ᵥ v = 0) :
    ∃ t : GL (Fin n) (nbrPSU_F g),
      (t : Matrix (Fin n) (Fin n) (nbrPSU_F g)) =
        1 + Matrix.vecMulVec v
          (Matrix.vecMul (fun i => nbrPSU_sigma g (v i)) (Unitary.antidiag n)) ∧
      t ∈ unitTransvGroup (nbrPSU_sigma g) (Unitary.antidiag n) v ∧ t ≠ 1 := by
  have hG : IsUnit (Unitary.antidiag n : Matrix (Fin n) (Fin n) (nbrPSU_F g)).det :=
    isUnit_iff_ne_zero.mpr (Unitary.det_antidiag_ne_zero n)
  let φ : Fin n → nbrPSU_F g :=
    Matrix.vecMul (fun i => nbrPSU_sigma g (v i)) (Unitary.antidiag n)
  have hφne : φ ≠ 0 := by
    intro hφ0
    have hinj := Matrix.vecMul_injective_of_isUnit
      ((Matrix.isUnit_iff_isUnit_det _).mpr hG)
    have h1 : (fun i => nbrPSU_sigma g (v i)) = 0 := by
      apply hinj
      show Matrix.vecMul (fun i => nbrPSU_sigma g (v i)) (Unitary.antidiag n) =
        Matrix.vecMul (0 : Fin n → nbrPSU_F g) (Unitary.antidiag n)
      rw [show Matrix.vecMul (fun i => nbrPSU_sigma g (v i)) (Unitary.antidiag n) = φ from rfl,
        hφ0]
      simp
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
    simp only [Pi.zero_apply] at hi
    have h2 : (nbrPSU_sigmae g) (v i) = (nbrPSU_sigmae g) 0 := by
      have := congrFun h1 i
      simpa using this
    exact hi (by simpa using (nbrPSU_sigmae g).injective h2)
  let N : Matrix (Fin n) (Fin n) (nbrPSU_F g) := Matrix.vecMulVec v φ
  have hN2 : N * N = 0 := by
    rw [Matrix.vecMulVec_mul_vecMulVec]
    rw [show (φ ⬝ᵥ v) = 0 from hviso]
    simp
  have hNN : N + N = 0 := by
    ext i j
    exact CharTwo.add_self_eq_zero (N i j)
  have h11 : (1 + N) * (1 + N) = 1 := by
    calc (1 + N) * (1 + N) = 1 + N + N + N * N := by noncomm_ring
      _ = 1 + (N + N) + N * N := by abel
      _ = 1 + 0 + 0 := by rw [hNN, hN2]
      _ = 1 := by simp
  let t : GL (Fin n) (nbrPSU_F g) := Units.mk (1 + N) (1 + N) h11 h11
  have hNne : N ≠ 0 := by
    intro hN0
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
    simp only [Pi.zero_apply] at hi
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hφne
    simp only [Pi.zero_apply] at hj
    have h := congrFun (congrFun hN0 i) j
    have h' : v i * φ j = 0 := by simpa [N, Matrix.vecMulVec_apply] using h
    exact (mul_ne_zero hi hj) h'
  refine ⟨t, ?_, ?_, ?_⟩
  · simp [t, N, φ]
  · apply Subgroup.subset_closure
    refine ⟨1, by simp, ?_⟩
    show (t : Matrix (Fin n) (Fin n) (nbrPSU_F g)) =
      1 + (1 : nbrPSU_F g) • Matrix.vecMulVec v
        (Matrix.vecMul (fun i => nbrPSU_sigma g (v i)) (Unitary.antidiag n))
    simp [t, N, φ]
  · intro h
    have hN0 : N = 0 := by
      have hmat : (1 + N : Matrix (Fin n) (Fin n) (nbrPSU_F g)) = 1 := by
        have := congrArg (fun u : GL (Fin n) (nbrPSU_F g) =>
          (u : Matrix (Fin n) (Fin n) (nbrPSU_F g))) h
        simpa [t] using this
      have := congrArg (fun M : Matrix (Fin n) (Fin n) (nbrPSU_F g) => M - 1) hmat
      simpa using this
    exact hNne hN0

private lemma nbrPSU_unitaryTransvection_rank (n g : ℕ) {v : Fin n → nbrPSU_F g} (hv : v ≠ 0) :
    (Matrix.vecMulVec v
      (Matrix.vecMul (fun i => nbrPSU_sigma g (v i)) (Unitary.antidiag n)) :
        Matrix (Fin n) (Fin n) (nbrPSU_F g)).rank = 1 := by
  have hG : IsUnit (Unitary.antidiag n : Matrix (Fin n) (Fin n) (nbrPSU_F g)).det :=
    isUnit_iff_ne_zero.mpr (Unitary.det_antidiag_ne_zero n)
  let φ : Fin n → nbrPSU_F g :=
    Matrix.vecMul (fun i => nbrPSU_sigma g (v i)) (Unitary.antidiag n)
  have hφne : φ ≠ 0 := by
    intro hφ0
    have hinj := Matrix.vecMul_injective_of_isUnit
      ((Matrix.isUnit_iff_isUnit_det _).mpr hG)
    have h1 : (fun i => nbrPSU_sigma g (v i)) = 0 := by
      apply hinj
      show Matrix.vecMul (fun i => nbrPSU_sigma g (v i)) (Unitary.antidiag n) =
        Matrix.vecMul (0 : Fin n → nbrPSU_F g) (Unitary.antidiag n)
      rw [show Matrix.vecMul (fun i => nbrPSU_sigma g (v i)) (Unitary.antidiag n) = φ from rfl,
        hφ0]
      simp
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
    simp only [Pi.zero_apply] at hi
    have h2 : (nbrPSU_sigmae g) (v i) = (nbrPSU_sigmae g) 0 := by
      have := congrFun h1 i
      simpa using this
    exact hi (by simpa using (nbrPSU_sigmae g).injective h2)
  exact CFSG.SeitzReduction.LinearPilot.rank_vecMulVec_eq_one hv hφne

private lemma nbrPSU_dualPair_rank_dvd_of_mem (n g : ℕ) (S_e : Set (GL (Fin n) (nbrPSU_F g)))
    (hSU : ∀ s ∈ S_e, Unitary.conjTr (nbrPSU_sigmae g)
        (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) * Unitary.antidiag n *
        (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) = Unitary.antidiag n)
    (hS_e : ∀ s ∈ S_e, ∀ s' ∈ S_e, Commute s s')
    (hodd : ∀ s ∈ S_e, Odd (orderOf s))
    {e : Matrix (Fin n) (Fin n) (nbrPSU_F g)}
    (he : IsPrimIdemIn (Algebra.adjoin (nbrPSU_F g) (Units.val '' S_e)) e)
    (hpair : formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e ≠ e)
    {K' : Subgroup ↥(Unitary.SU (nbrPSU_sigmae g) n)}
    (hK' : IsComponentOf K'
        ⁅glBlockCentralizer ((Unitary.SU (nbrPSU_sigmae g) n).subtype) S_e
            (e + formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e),
          glBlockCentralizer ((Unitary.SU (nbrPSU_sigmae g) n).subtype) S_e
            (e + formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e)⁆)
    {k : ↥(Unitary.SU (nbrPSU_sigmae g) n)} (hk : k ∈ K') :
    2 * blockDegree (Algebra.adjoin (nbrPSU_F g) (Units.val '' S_e)) e ∣
      (((k : GL (Fin n) (nbrPSU_F g)) : Matrix (Fin n) (Fin n) (nbrPSU_F g)) - 1).rank := by
  have hKG : K' ≤ glBlockCentralizer ((Unitary.SU (nbrPSU_sigmae g) n).subtype) S_e
      (e + formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e) :=
    le_trans hK'.1 (Subgroup.commutator_le_self _)
  have hkG : (k : GL (Fin n) (nbrPSU_F g)) ∈ Subgroup.centralizer S_e := by
    have hk' := hKG hk
    rw [glBlockCentralizer, Subgroup.mem_comap, Subgroup.mem_inf] at hk'
    exact hk'.1
  have hkge : (k : GL (Fin n) (nbrPSU_F g)) ∈
      glFixing (1 - (e + formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e)) := by
    have hk' := hKG hk
    rw [glBlockCentralizer, Subgroup.mem_comap, Subgroup.mem_inf] at hk'
    exact hk'.2
  let kM : Matrix (Fin n) (Fin n) (nbrPSU_F g) := (k : GL (Fin n) (nbrPSU_F g))
  have hkiso : Matrix.transpose (kM.map (nbrPSU_sigma g)) * Unitary.antidiag n * kM =
      Unitary.antidiag n := by
    simpa [kM, Unitary.conjTr] using (Unitary.mem_SU.mp k.2).2
  have hSU' : ∀ s ∈ S_e, Matrix.transpose
      ((((s : GL (Fin n) (nbrPSU_F g)) : Matrix (Fin n) (Fin n) (nbrPSU_F g)).map
        (nbrPSU_sigma g))) * Unitary.antidiag n *
      ((s : GL (Fin n) (nbrPSU_F g)) : Matrix (Fin n) (Fin n) (nbrPSU_F g)) =
      Unitary.antidiag n :=
    fun s hs => by simpa [Unitary.conjTr] using hSU s hs
  have hG : IsUnit (Unitary.antidiag n : Matrix (Fin n) (Fin n) (nbrPSU_F g)).det :=
    isUnit_iff_ne_zero.mpr (Unitary.det_antidiag_ne_zero n)
  exact two_mul_blockDegree_dvd_rank_sub_one_of_formAdj_ne (nbrPSU_sigma g)
    (nbrPSU_sigma_involutive g) hG (nbrPSU_antidiag_transpose_map n g) hSU' hS_e hodd he hpair
    hkG hkiso hkge

private lemma nbrPSU_dualPairLongExclusionCore
    (n g : ℕ) (S_e : Set (GL (Fin n) (nbrPSU_F g)))
    (hSU : ∀ s ∈ S_e, Unitary.conjTr (nbrPSU_sigmae g)
        (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) * Unitary.antidiag n *
        (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) = Unitary.antidiag n)
    (hS_e : ∀ s ∈ S_e, ∀ s' ∈ S_e, Commute s s')
    (hodd : ∀ s ∈ S_e, Odd (orderOf s))
    {e : Matrix (Fin n) (Fin n) (nbrPSU_F g)}
    (he : IsPrimIdemIn (Algebra.adjoin (nbrPSU_F g) (Units.val '' S_e)) e)
    (hpair : formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e ≠ e)
    {K' : Subgroup ↥(Unitary.SU (nbrPSU_sigmae g) n)}
    (hK' : IsComponentOf K'
        ⁅glBlockCentralizer ((Unitary.SU (nbrPSU_sigmae g) n).subtype) S_e
            (e + formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e),
          glBlockCentralizer ((Unitary.SU (nbrPSU_sigmae g) n).subtype) S_e
            (e + formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e)⁆)
    {v : Fin n → nbrPSU_F g} (hv : v ≠ 0)
    (hviso : Matrix.vecMul (fun i => nbrPSU_sigmae g (v i)) (Unitary.antidiag n) ⬝ᵥ v = 0)
    (hle : unitTransvGroup (nbrPSU_sigma g) (Unitary.antidiag n) v ≤
        K'.map ((Unitary.SU (nbrPSU_sigmae g) n).subtype)) : False := by
  obtain ⟨t, htmat, htmem, htne⟩ := nbrPSU_unitaryTransvection_mem n g hv hviso
  have htK : t ∈ K'.map ((Unitary.SU (nbrPSU_sigmae g) n).subtype) := hle htmem
  obtain ⟨k, hkK', hkj⟩ := Subgroup.mem_map.mp htK
  have hdiv := nbrPSU_dualPair_rank_dvd_of_mem n g S_e hSU hS_e hodd he hpair hK' hkK'
  have hkmat : (k : GL (Fin n) (nbrPSU_F g)) = t := hkj
  have hrank : (((k : GL (Fin n) (nbrPSU_F g)) : Matrix (Fin n) (Fin n) (nbrPSU_F g)) - 1).rank =
      1 := by
    rw [hkmat, htmat]
    rw [show (1 + Matrix.vecMulVec v
        (Matrix.vecMul (fun i => nbrPSU_sigma g (v i)) (Unitary.antidiag n)) : Matrix (Fin n)
          (Fin n) (nbrPSU_F g)) - 1 =
        Matrix.vecMulVec v (Matrix.vecMul (fun i => nbrPSU_sigma g (v i))
          (Unitary.antidiag n)) by abel]
    exact nbrPSU_unitaryTransvection_rank n g hv
  rw [hrank] at hdiv
  have h1 : 2 * blockDegree (Algebra.adjoin (nbrPSU_F g) (Units.val '' S_e)) e = 1 :=
    Nat.dvd_one.mp hdiv
  omega

private lemma nbrPSU_l8_dualPairLongExclusion
    (n g : ℕ) (S_e : Set (GL (Fin n) (nbrPSU_F g)))
    (hSU : ∀ s ∈ S_e, Unitary.conjTr (nbrPSU_sigmae g)
        (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) * Unitary.antidiag n *
        (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) = Unitary.antidiag n)
    (hS_e : ∀ s ∈ S_e, ∀ s' ∈ S_e, Commute s s')
    (hodd : ∀ s ∈ S_e, Odd (orderOf s))
    {e : Matrix (Fin n) (Fin n) (nbrPSU_F g)}
    (he : IsPrimIdemIn (Algebra.adjoin (nbrPSU_F g) (Units.val '' S_e)) e)
    (hpair : formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e ≠ e)
    {K' : Subgroup ↥(Unitary.SU (nbrPSU_sigmae g) n)}
    (hK' : IsComponentOf K'
        ⁅glBlockCentralizer ((Unitary.SU (nbrPSU_sigmae g) n).subtype) S_e
            (e + formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e),
          glBlockCentralizer ((Unitary.SU (nbrPSU_sigmae g) n).subtype) S_e
            (e + formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e)⁆)
    {v : Fin n → nbrPSU_F g} (hv : v ≠ 0)
    (hviso : Matrix.vecMul (fun i => nbrPSU_sigmae g (v i)) (Unitary.antidiag n) ⬝ᵥ v = 0)
    (hle : unitTransvGroup (nbrPSU_sigma g) (Unitary.antidiag n) v ≤
        K'.map ((Unitary.SU (nbrPSU_sigmae g) n).subtype)) : False := by
  exact nbrPSU_dualPairLongExclusionCore n g S_e hSU hS_e hodd he hpair hK' hv hviso hle

private lemma nbrPSU_mem_adjoin_commute {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {S : Set (GL ι F)} {T : GL ι F} (hT : T ∈ Subgroup.centralizer S)
    {ε : Matrix ι ι F} (hε : ε ∈ Algebra.adjoin F (Units.val '' S)) :
    (T : Matrix ι ι F) * ε = ε * (T : Matrix ι ι F) := by
  have hgen : (Units.val '' S : Set (Matrix ι ι F)) ⊆
      (Subalgebra.centralizer F ({(T : Matrix ι ι F)} : Set (Matrix ι ι F)) :
        Set (Matrix ι ι F)) := by
    rintro x ⟨s, hs, rfl⟩
    refine (Subalgebra.mem_centralizer_iff F).mpr ?_
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact congrArg (fun u : GL ι F => (u : Matrix ι ι F))
      ((Subgroup.mem_centralizer_iff.mp hT) s hs).symm
  have hA : Algebra.adjoin F (Units.val '' S) ≤
      Subalgebra.centralizer F ({(T : Matrix ι ι F)} : Set (Matrix ι ι F)) :=
    Algebra.adjoin_le hgen
  exact (Subalgebra.mem_centralizer_iff F).mp (hA hε) (T : Matrix ι ι F)
    (Set.mem_singleton (T : Matrix ι ι F))

private lemma nbrPSU_adjoin_commute {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {S : Set (GL ι F)} (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {a b : Matrix ι ι F} (ha : a ∈ Algebra.adjoin F (Units.val '' S))
    (hb : b ∈ Algebra.adjoin F (Units.val '' S)) : a * b = b * a := by
  have hgen : (Units.val '' S : Set (Matrix ι ι F)) ⊆
      (Subalgebra.centralizer F (Units.val '' S) : Set (Matrix ι ι F)) := by
    rintro x ⟨s, hs, rfl⟩
    refine (Subalgebra.mem_centralizer_iff F).mpr ?_
    intro y hy
    obtain ⟨s', hs', rfl⟩ := hy
    exact congrArg (fun u : GL ι F => (u : Matrix ι ι F)) ((hS s hs s' hs').eq).symm
  have hA : Algebra.adjoin F (Units.val '' S) ≤ Subalgebra.centralizer F (Units.val '' S) :=
    Algebra.adjoin_le hgen
  have haC : a ∈ Subalgebra.centralizer F (Units.val '' S) := hA ha
  refine Algebra.adjoin_induction (p := fun b _ => a * b = b * a) ?_ ?_ ?_ ?_ hb
  · intro x hx
    exact ((Subalgebra.mem_centralizer_iff F).mp haC x hx).symm
  · intro r
    exact (Algebra.commute_algebraMap_left r a).eq.symm
  · intro x y _ _ ihx ihy
    rw [mul_add, add_mul, ihx, ihy]
  · intro x y _ _ ihx ihy
    rw [← mul_assoc, ihx, mul_assoc, ihy, ← mul_assoc]

private lemma nbrPSU_l8_neighbourStarBlock
    {n g : ℕ} (K' : Subgroup ↥(Unitary.SU (nbrPSU_sigmae g) n))
    (s_e : GL (Fin n) (nbrPSU_F g))
    (hK'comp : IsComponentOf K'
      ((Subgroup.centralizer ({s_e} : Set (GL (Fin n) (nbrPSU_F g)))).comap
        ((Unitary.SU (nbrPSU_sigmae g) n).subtype))) :
    ∃ ε : Matrix (Fin n) (Fin n) (nbrPSU_F g),
      IsPrimAdjIdemIn (nbrPSU_sigma g) (Unitary.antidiag n)
        (Algebra.adjoin (nbrPSU_F g) (Units.val '' ({s_e} : Set (GL (Fin n) (nbrPSU_F g))))) ε ∧
      IsComponentOf K'
        ⁅glBlockCentralizer ((Unitary.SU (nbrPSU_sigmae g) n).subtype)
            ({s_e} : Set (GL (Fin n) (nbrPSU_F g))) ε,
          glBlockCentralizer ((Unitary.SU (nbrPSU_sigmae g) n).subtype)
            ({s_e} : Set (GL (Fin n) (nbrPSU_F g))) ε⁆ := by
  have hS_e : ∀ s ∈ ({s_e} : Set (GL (Fin n) (nbrPSU_F g))),
      ∀ s' ∈ ({s_e} : Set (GL (Fin n) (nbrPSU_F g))), Commute s s' := by
    intro s hs s' hs'
    rw [Set.mem_singleton_iff] at hs hs'
    rw [hs, hs']
  exact nbrPSU_l3_blockIdempotent n g ({s_e} : Set (GL (Fin n) (nbrPSU_F g))) hS_e K' hK'comp

private lemma nbrPSU_l8_neighbourPrimitiveBlock
    (n g : ℕ) (S_e : Set (GL (Fin n) (nbrPSU_F g)))
    (hSU : ∀ s ∈ S_e, Unitary.conjTr (nbrPSU_sigmae g) (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) *
        Unitary.antidiag n * (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) = Unitary.antidiag n)
    (hS_e : ∀ s ∈ S_e, ∀ s' ∈ S_e, Commute s s')
    {ε : Matrix (Fin n) (Fin n) (nbrPSU_F g)}
    (hε : IsPrimAdjIdemIn (nbrPSU_sigma g) (Unitary.antidiag n)
      (Algebra.adjoin (nbrPSU_F g) (Units.val '' S_e)) ε) :
    ∃ e' : Matrix (Fin n) (Fin n) (nbrPSU_F g),
      IsPrimIdemIn (Algebra.adjoin (nbrPSU_F g) (Units.val '' S_e)) e' ∧ e' * ε = e' ∧
      (e' = ε ∨ (e' ≠ ε ∧ formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e' ≠ e' ∧
        ε = e' + formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e')) := by
  exact exists_isPrimIdemIn_of_isPrimAdjIdemIn_PSU n g S_e hSU hS_e hε

private lemma nbrPSU_l8_baseBlockDataChar
    {X : Type} [Group X] [Finite X] (n g : ℕ) (ψ : ↥(Unitary.SU (nbrPSU_sigmae g) n) →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X) (hH : GGSixPosHyp .PSU n (g + 1) ψ p G₀ B₁ D J L x)
    (e : X) (he : e ∈ D) :
    ∃ (S : Set (GL (Fin n) (nbrPSU_F g))) (J' : Subgroup ↥(Unitary.SU (nbrPSU_sigmae g) n))
      (ε_J e_J : Matrix (Fin n) (Fin n) (nbrPSU_F g)),
      (∀ s : GL (Fin n) (nbrPSU_F g), s ∈ S ↔
        Unitary.conjTr (nbrPSU_sigmae g) (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) *
            Unitary.antidiag n * (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) = Unitary.antidiag n ∧
          ∃ d ∈ D, IsGLLift ((Unitary.SU (nbrPSU_sigmae g) n).subtype) ψ s d) ∧
      (∀ s ∈ S, Unitary.conjTr (nbrPSU_sigmae g) (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) *
          Unitary.antidiag n * (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) = Unitary.antidiag n) ∧
      (∀ s ∈ S, ∀ s' ∈ S, Commute s s') ∧
      (∀ s ∈ S, Odd (orderOf s)) ∧
      IsComponentOf J' ((Subgroup.centralizer S).comap
        ((Unitary.SU (nbrPSU_sigmae g) n).subtype)) ∧
      J'.map ψ = J ∧
      IsPrimAdjIdemIn (nbrPSU_sigma g) (Unitary.antidiag n)
        (Algebra.adjoin (nbrPSU_F g) (Units.val '' S)) ε_J ∧
      IsComponentOf J' ⁅glBlockCentralizer ((Unitary.SU (nbrPSU_sigmae g) n).subtype) S ε_J,
        glBlockCentralizer ((Unitary.SU (nbrPSU_sigmae g) n).subtype) S ε_J⁆ ∧
      IsPrimIdemIn (Algebra.adjoin (nbrPSU_F g) (Units.val '' S)) e_J ∧ e_J * ε_J = e_J ∧
      blockDegree (Algebra.adjoin (nbrPSU_F g) (Units.val '' S)) e_J < 2 := by
  have hH' : GGSixPosHyp .PSU n (g + 1) ψ p G₀ B₁ D J L x := hH
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩ := hH'
  obtain ⟨S, J', s_e, hSdef, hSU, hS, hodd, hpow, hJ'comp, hJ'map, hs_e_iso, hs_e_lift⟩ :=
    nbrPSU_l1_liftDataChar n g ψ p G₀ B₁ D J L x hH e he
  have hFJ : ¬ GGSixLSevenFieldExtCase (J'.map ψ) .PSU (g + 1) := by
    rw [hJ'map]
    exact h29
  obtain ⟨ε_J, hεJ, hJ'block⟩ :=
    exists_isComponentOf_glBlockCentralizer_PSU (F := nbrPSU_F g) (f := g + 1) n S hS hJ'comp
  obtain ⟨e_J, heJ, heJε, hdegJ, _hsplitJ⟩ :=
    nbrPSU_l4_blockDegree n g ψ h2 S hSU hS hodd hεJ hJ'block hFJ
  exact ⟨S, J', ε_J, e_J, hSdef, hSU, hS, hodd, hJ'comp, hJ'map, hεJ, hJ'block, heJ, heJε, hdegJ⟩

private lemma nbrPSU_l8_baseAdjIdem_le
    {n g : ℕ} {S S_e : Set (GL (Fin n) (nbrPSU_F g))} (hSe : S_e ⊆ S)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε_J ε : Matrix (Fin n) (Fin n) (nbrPSU_F g)}
    (hεJ : IsPrimAdjIdemIn (nbrPSU_sigma g) (Unitary.antidiag n)
      (Algebra.adjoin (nbrPSU_F g) (Units.val '' S)) ε_J)
    (hε : IsPrimAdjIdemIn (nbrPSU_sigma g) (Unitary.antidiag n)
      (Algebra.adjoin (nbrPSU_F g) (Units.val '' S_e)) ε)
    {J' K' : Subgroup ↥(Unitary.SU (nbrPSU_sigmae g) n)}
    (hJ' : IsComponentOf J'
      ⁅glBlockCentralizer ((Unitary.SU (nbrPSU_sigmae g) n).subtype) S ε_J,
        glBlockCentralizer ((Unitary.SU (nbrPSU_sigmae g) n).subtype) S ε_J⁆)
    (hK' : IsComponentOf K'
      ⁅glBlockCentralizer ((Unitary.SU (nbrPSU_sigmae g) n).subtype) S_e ε,
        glBlockCentralizer ((Unitary.SU (nbrPSU_sigmae g) n).subtype) S_e ε⁆)
    (hJK : J' ≤ K') :
    ε_J * ε = ε_J := by
  let j : ↥(Unitary.SU (nbrPSU_sigmae g) n) →* GL (Fin n) (nbrPSU_F g) :=
    (Unitary.SU (nbrPSU_sigmae g) n).subtype
  have hAe_le : Algebra.adjoin (nbrPSU_F g) (Units.val '' S_e) ≤
      Algebra.adjoin (nbrPSU_F g) (Units.val '' S) :=
    Algebra.adjoin_mono (Set.image_mono hSe)
  have hεA : ε ∈ Algebra.adjoin (nbrPSU_F g) (Units.val '' S) := hAe_le hε.1
  have hcommA : ∀ a ∈ Algebra.adjoin (nbrPSU_F g) (Units.val '' S),
      ∀ b ∈ Algebra.adjoin (nbrPSU_F g) (Units.val '' S), a * b = b * a :=
    fun a ha b hb => nbrPSU_adjoin_commute hS ha hb
  have hmem : ε_J * ε ∈ Algebra.adjoin (nbrPSU_F g) (Units.val '' S) :=
    Subalgebra.mul_mem _ hεJ.1 hεA
  have hidem : IsIdempotentElem (ε_J * ε) := by
    rw [IsIdempotentElem]
    calc (ε_J * ε) * (ε_J * ε) = ε_J * (ε * (ε_J * ε)) := by rw [mul_assoc]
      _ = ε_J * ((ε * ε_J) * ε) := by rw [mul_assoc]
      _ = ε_J * ((ε_J * ε) * ε) := by rw [hcommA ε hεA ε_J hεJ.1]
      _ = ε_J * (ε_J * (ε * ε)) := by rw [mul_assoc]
      _ = ε_J * (ε_J * ε) := by rw [hε.2.1.eq]
      _ = (ε_J * ε_J) * ε := by rw [← mul_assoc]
      _ = ε_J * ε := by rw [hεJ.2.1.eq]
  have hbelow : (ε_J * ε) * ε_J = ε_J * ε := by
    rw [mul_assoc, hcommA ε hεA ε_J hεJ.1, ← mul_assoc, hεJ.2.1.eq]
  have hG : IsUnit (Unitary.antidiag n : Matrix (Fin n) (Fin n) (nbrPSU_F g)).det :=
    isUnit_iff_ne_zero.mpr (Unitary.det_antidiag_ne_zero n)
  have hadj : formAdj (nbrPSU_sigma g) (Unitary.antidiag n) (ε_J * ε) = ε_J * ε := by
    rw [CFSG.StandardType.ClassicalPosition.Geo.formAdj_mul (nbrPSU_sigma g) hG ε_J ε,
      hε.2.2.2.1, hεJ.2.2.2.1]
    exact hcommA ε hεA ε_J hεJ.1
  rcases hεJ.2.2.2.2 (ε_J * ε) hmem hidem hadj hbelow with h0 | heq
  · exfalso
    have hJ'bot : J' = ⊥ := by
      rw [eq_bot_iff]
      intro u hu
      have huG : u ∈ glBlockCentralizer j S ε_J := by
        have h := (Subgroup.commutator_le_sup _ _) (hJ'.1 hu)
        rwa [sup_idem] at h
      have huGe : u ∈ glBlockCentralizer j S_e ε := by
        have h := (Subgroup.commutator_le_sup _ _) (hK'.1 (hJK hu))
        rwa [sup_idem] at h
      have huG' : j u ∈ Subgroup.centralizer S ⊓ glFixing (1 - ε_J) :=
        Subgroup.mem_comap.mp huG
      have huGe' : j u ∈ Subgroup.centralizer S_e ⊓ glFixing (1 - ε) :=
        Subgroup.mem_comap.mp huGe
      have huc : j u ∈ Subgroup.centralizer S := huG'.1
      let ju : Matrix (Fin n) (Fin n) (nbrPSU_F g) := j u
      have hfixJ : ju * (1 - ε_J) = 1 - ε_J := huG'.2
      have hfixe : ju * (1 - ε) = 1 - ε := huGe'.2
      have hcomm_u : ju * ε_J = ε_J * ju := nbrPSU_mem_adjoin_commute (S := S) huc hεJ.1
      have h1 : ε_J * (1 - ε) = ε_J := by rw [mul_sub, mul_one, h0, sub_zero]
      have hmat_eJ : ju * ε_J = ε_J := by
        calc ju * ε_J = ju * (ε_J * (1 - ε)) := by rw [h1]
          _ = (ju * ε_J) * (1 - ε) := by rw [mul_assoc]
          _ = (ε_J * ju) * (1 - ε) := by rw [hcomm_u]
          _ = ε_J * (ju * (1 - ε)) := by rw [mul_assoc]
          _ = ε_J * (1 - ε) := by rw [hfixe]
          _ = ε_J := h1
      have hmat_one : ju = 1 := by
        calc ju = ju * 1 := by rw [mul_one]
          _ = ju * (ε_J + (1 - ε_J)) := by rw [add_sub_cancel]
          _ = ju * ε_J + ju * (1 - ε_J) := by rw [mul_add]
          _ = ε_J + (1 - ε_J) := by rw [hmat_eJ, hfixJ]
          _ = 1 := by rw [add_sub_cancel]
      have hu1 : u = 1 := by
        apply Subgroup.subtype_injective (Unitary.SU (nbrPSU_sigmae g) n)
        rw [map_one]
        exact Units.ext hmat_one
      exact Subgroup.mem_bot.mpr hu1
    have hnt : Nontrivial ↥J' := CFSG.ComponentClassification.Quasisimple.nontrivial hJ'.2.2
    exact (Subgroup.nontrivial_iff_ne_bot J').mp hnt hJ'bot
  · exact heq

private lemma nbrPSU_l8_blockFieldEmbedding_of_mul
    {n g : ℕ} {S S_e : Set (GL (Fin n) (nbrPSU_F g))} (hSe : S_e ⊆ S)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e_J ε : Matrix (Fin n) (Fin n) (nbrPSU_F g)}
    (heJ : IsPrimIdemIn (Algebra.adjoin (nbrPSU_F g) (Units.val '' S)) e_J)
    (hε : IsPrimIdemIn (Algebra.adjoin (nbrPSU_F g) (Units.val '' S_e)) ε)
    (heJε : e_J * ε = e_J) :
    blockDegree (Algebra.adjoin (nbrPSU_F g) (Units.val '' S_e)) ε ≤
      blockDegree (Algebra.adjoin (nbrPSU_F g) (Units.val '' S)) e_J := by
  have hS_e : ∀ s ∈ S_e, ∀ s' ∈ S_e, Commute s s' :=
    fun s hs s' hs' => hS s (hSe hs) s' (hSe hs')
  have hodd_e : ∀ s ∈ S_e, Odd (orderOf s) := fun s hs => hodd s (hSe hs)
  have hAe_le : Algebra.adjoin (nbrPSU_F g) (Units.val '' S_e) ≤
      Algebra.adjoin (nbrPSU_F g) (Units.val '' S) :=
    Algebra.adjoin_mono (Set.image_mono hSe)
  have hεA : ε ∈ Algebra.adjoin (nbrPSU_F g) (Units.val '' S) := hAe_le hε.1
  have hcommA : ∀ a ∈ Algebra.adjoin (nbrPSU_F g) (Units.val '' S),
      ∀ b ∈ Algebra.adjoin (nbrPSU_F g) (Units.val '' S), a * b = b * a :=
    fun a ha b hb => nbrPSU_adjoin_commute hS ha hb
  obtain ⟨Ke, hKeField, hKeAlg, hKefin, πe, hπe_surj, hπe_ker, hπe_fin⟩ :=
    exists_blockField (F := nbrPSU_F g) hS_e hodd_e hε
  letI : Field Ke := hKeField
  letI : Algebra (nbrPSU_F g) Ke := hKeAlg
  letI : Finite Ke := hKefin
  obtain ⟨KJ, hKJField, hKJAlg, hKJfin, πJ, hπJ_surj, hπJ_ker, hπJ_fin⟩ :=
    exists_blockField (F := nbrPSU_F g) hS hodd heJ
  letI : Field KJ := hKJField
  letI : Algebra (nbrPSU_F g) KJ := hKJAlg
  letI : Finite KJ := hKJfin
  let φ : Algebra.adjoin (nbrPSU_F g) (Units.val '' S_e) →ₐ[nbrPSU_F g] KJ :=
    πJ.comp (Subalgebra.inclusion hAe_le)
  have hker_le : RingHom.ker πe ≤ RingHom.ker φ := by
    intro a ha
    rw [RingHom.mem_ker] at ha ⊢
    have haε : (a : Matrix (Fin n) (Fin n) (nbrPSU_F g)) * ε = 0 := (hπe_ker a).mp ha
    have heJ_eq : e_J = ε * e_J := (heJε.symm).trans (hcommA e_J heJ.1 ε hεA)
    have hae : (a : Matrix (Fin n) (Fin n) (nbrPSU_F g)) * e_J = 0 := by
      calc (a : Matrix (Fin n) (Fin n) (nbrPSU_F g)) * e_J
          = (a : Matrix (Fin n) (Fin n) (nbrPSU_F g)) * (ε * e_J) :=
            congrArg (fun x => (a : Matrix (Fin n) (Fin n) (nbrPSU_F g)) * x) heJ_eq
        _ = ((a : Matrix (Fin n) (Fin n) (nbrPSU_F g)) * ε) * e_J := by rw [mul_assoc]
        _ = 0 := by rw [haε, zero_mul]
    exact (hπJ_ker (Subalgebra.inclusion hAe_le a)).mpr (by simpa using hae)
  let lift : (Algebra.adjoin (nbrPSU_F g) (Units.val '' S_e) ⧸ RingHom.ker πe)
      →ₐ[nbrPSU_F g] Ke :=
    Ideal.Quotient.liftₐ (RingHom.ker πe) πe (fun a ha => ha)
  have hlift_surj : Function.Surjective lift := by
    intro x
    obtain ⟨a, rfl⟩ := hπe_surj x
    exact ⟨Ideal.Quotient.mkₐ (nbrPSU_F g) (RingHom.ker πe) a, by
      rw [show lift (Ideal.Quotient.mkₐ (nbrPSU_F g) (RingHom.ker πe) a) = πe a from
        Ideal.Quotient.liftₐ_apply _ _ _ _]⟩
  have hlift_inj : Function.Injective lift := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mkₐ_surjective (nbrPSU_F g) (RingHom.ker πe) x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mkₐ_surjective (nbrPSU_F g) (RingHom.ker πe) y
    rw [show lift (Ideal.Quotient.mkₐ (nbrPSU_F g) (RingHom.ker πe) a) = πe a from
        Ideal.Quotient.liftₐ_apply _ _ _ _,
      show lift (Ideal.Quotient.mkₐ (nbrPSU_F g) (RingHom.ker πe) b) = πe b from
        Ideal.Quotient.liftₐ_apply _ _ _ _] at hxy
    have hab : a - b ∈ RingHom.ker πe := by
      rw [RingHom.mem_ker, map_sub, hxy, sub_self]
    have : Ideal.Quotient.mkₐ (nbrPSU_F g) (RingHom.ker πe) a =
        Ideal.Quotient.mkₐ (nbrPSU_F g) (RingHom.ker πe) b := by
      change Ideal.Quotient.mk (RingHom.ker πe) a = Ideal.Quotient.mk (RingHom.ker πe) b
      rw [Ideal.Quotient.eq]
      exact hab
    exact this
  let qe : (Algebra.adjoin (nbrPSU_F g) (Units.val '' S_e) ⧸ RingHom.ker πe)
      ≃ₐ[nbrPSU_F g] Ke :=
    AlgEquiv.ofBijective lift ⟨hlift_inj, hlift_surj⟩
  let ψ : Ke →ₐ[nbrPSU_F g] KJ :=
    (Ideal.Quotient.liftₐ (RingHom.ker πe) φ hker_le).comp qe.symm.toAlgHom
  have hψ_inj : Function.Injective ψ := by
    intro x y hxy
    have hmem : x - y ∈ RingHom.ker ψ := by rw [RingHom.mem_ker, map_sub, hxy, sub_self]
    have hbot : RingHom.ker ψ = ⊥ := by
      rcases Ideal.eq_bot_or_top (RingHom.ker ψ) with h | h
      · exact h
      · exfalso
        have h1 : ψ (1 : Ke) = 0 := by
          have : (1 : Ke) ∈ RingHom.ker ψ := by rw [h]; trivial
          rwa [RingHom.mem_ker] at this
        rw [map_one] at h1
        exact one_ne_zero h1
    rw [hbot, Submodule.mem_bot] at hmem
    exact sub_eq_zero.mp hmem
  have hfin : Module.finrank (nbrPSU_F g) Ke ≤ Module.finrank (nbrPSU_F g) KJ :=
    LinearMap.finrank_le_finrank_of_injective (f := ψ.toLinearMap) hψ_inj
  rw [← hπe_fin]
  calc Module.finrank (nbrPSU_F g) Ke
      ≤ Module.finrank (nbrPSU_F g) KJ := hfin
    _ = blockDegree (Algebra.adjoin (nbrPSU_F g) (Units.val '' S)) e_J := hπJ_fin

private lemma nbrPSU_l8_dualPair_below
    {n g : ℕ} {S S_e : Set (GL (Fin n) (nbrPSU_F g))} (hSe : S_e ⊆ S)
    (hSU : ∀ s ∈ S_e, Unitary.conjTr (nbrPSU_sigmae g) (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) *
        Unitary.antidiag n * (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) = Unitary.antidiag n)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e_J ε e' : Matrix (Fin n) (Fin n) (nbrPSU_F g)}
    (heJ : IsPrimIdemIn (Algebra.adjoin (nbrPSU_F g) (Units.val '' S)) e_J)
    (he' : IsPrimIdemIn (Algebra.adjoin (nbrPSU_F g) (Units.val '' S_e)) e')
    (he'ε : e' * ε = e')
    (hsplit : e' ≠ ε ∧ formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e' ≠ e' ∧
      ε = e' + formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e')
    (heJε : e_J * ε = e_J) :
    ∃ e'' : Matrix (Fin n) (Fin n) (nbrPSU_F g),
      IsPrimIdemIn (Algebra.adjoin (nbrPSU_F g) (Units.val '' S_e)) e'' ∧ e'' * ε = e'' ∧
      e_J * e'' = e_J ∧
      (e'' ≠ ε ∧ formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e'' ≠ e'' ∧
        ε = e'' + formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e'') := by
  let estar : Matrix (Fin n) (Fin n) (nbrPSU_F g) := formAdj (nbrPSU_sigma g) (Unitary.antidiag n)
      e'
  have hG : IsUnit (Unitary.antidiag n : Matrix (Fin n) (Fin n) (nbrPSU_F g)).det :=
    isUnit_iff_ne_zero.mpr (Unitary.det_antidiag_ne_zero n)
  have hσ : ∀ x : nbrPSU_F g, nbrPSU_sigma g (nbrPSU_sigma g x) = x := nbrPSU_sigma_involutive g
  have hGh : ((Unitary.antidiag n : Matrix (Fin n) (Fin n) (nbrPSU_F g)).map (nbrPSU_sigma
      g)).transpose =
      Unitary.antidiag n := nbrPSU_antidiag_transpose_map n g
  have hff : formAdj (nbrPSU_sigma g) (Unitary.antidiag n) estar = e' :=
    CFSG.StandardType.ClassicalPosition.Geo.formAdj_formAdj (nbrPSU_sigma g) hσ hG hGh e'
  have hAe_le : Algebra.adjoin (nbrPSU_F g) (Units.val '' S_e) ≤
      Algebra.adjoin (nbrPSU_F g) (Units.val '' S) := Algebra.adjoin_mono (Set.image_mono hSe)
  have hcommS : ∀ a ∈ Algebra.adjoin (nbrPSU_F g) (Units.val '' S),
      ∀ b ∈ Algebra.adjoin (nbrPSU_F g) (Units.val '' S), a * b = b * a :=
    fun a ha b hb => nbrPSU_adjoin_commute hS ha hb
  have hcommSe : ∀ a ∈ Algebra.adjoin (nbrPSU_F g) (Units.val '' S_e),
      ∀ b ∈ Algebra.adjoin (nbrPSU_F g) (Units.val '' S_e), a * b = b * a :=
    fun a ha b hb => hcommS a (hAe_le ha) b (hAe_le hb)
  have he'S : e' ∈ Algebra.adjoin (nbrPSU_F g) (Units.val '' S) := hAe_le he'.1
  have hestSe : estar ∈ Algebra.adjoin (nbrPSU_F g) (Units.val '' S_e) :=
    CFSG.StandardType.ClassicalPosition.Geo.formAdj_mem_adjoin (nbrPSU_sigma g) hG hSU he'.1
  have hestS : estar ∈ Algebra.adjoin (nbrPSU_F g) (Units.val '' S) := hAe_le hestSe
  have hestar_idem : IsIdempotentElem estar := by
    rw [IsIdempotentElem]
    rw [show estar * estar = formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e' *
        formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e' from rfl,
      ← CFSG.StandardType.ClassicalPosition.Geo.formAdj_mul (nbrPSU_sigma g) hG e' e',
      he'.2.1.eq]
  have he'e_star : e' * estar = 0 := by
    have hsum : e' * e' + e' * estar = e' := by
      rw [← mul_add, ← hsplit.2.2]
      exact he'ε
    rw [he'.2.1.eq] at hsum
    exact add_left_cancel (by rw [add_zero]; exact hsum)
  have hestar_e : estar * e' = 0 := by
    rw [hcommSe estar hestSe e' he'.1, he'e_star]
  have hstar_ε : estar * ε = estar := by
    rw [hsplit.2.2, mul_add, hestar_e, hestar_idem.eq, zero_add]
  have hsplit_star : estar ≠ ε ∧ formAdj (nbrPSU_sigma g) (Unitary.antidiag n) estar ≠ estar ∧
      ε = estar + formAdj (nbrPSU_sigma g) (Unitary.antidiag n) estar := by
    refine ⟨?_, ?_, ?_⟩
    · intro h
      apply he'.2.2.1
      have h2 : e' + estar = 0 + estar := by rw [zero_add, ← hsplit.2.2, h]
      exact add_right_cancel h2
    · rw [hff]
      intro h
      exact hsplit.2.1 ((congrArg (fun x => formAdj (nbrPSU_sigma g) (Unitary.antidiag n) x)
          h).trans hff)
    · rw [hff, add_comm]
      exact hsplit.2.2
  have hestar_prim : IsPrimIdemIn (Algebra.adjoin (nbrPSU_F g) (Units.val '' S_e)) estar := by
    refine ⟨hestSe, hestar_idem, ?_, ?_⟩
    · intro hzero
      exact he'.2.2.1 (by rw [← hff, hzero]; simp [formAdj])
    · intro x hx hxidem hxbelow
      have hxadj_mem : formAdj (nbrPSU_sigma g) (Unitary.antidiag n) x ∈
          Algebra.adjoin (nbrPSU_F g) (Units.val '' S_e) :=
        CFSG.StandardType.ClassicalPosition.Geo.formAdj_mem_adjoin (nbrPSU_sigma g) hG hSU hx
      have hxadj_idem : IsIdempotentElem (formAdj (nbrPSU_sigma g) (Unitary.antidiag n) x) := by
        rw [IsIdempotentElem, ← CFSG.StandardType.ClassicalPosition.Geo.formAdj_mul (nbrPSU_sigma g)
            hG x x,
          hxidem.eq]
      have hxadj_below : formAdj (nbrPSU_sigma g) (Unitary.antidiag n) x * e' =
          formAdj (nbrPSU_sigma g) (Unitary.antidiag n) x := by
        rw [← hff, ← CFSG.StandardType.ClassicalPosition.Geo.formAdj_mul (nbrPSU_sigma g) hG estar
            x,
          hcommSe estar hestSe x hx, hxbelow]
      rcases he'.2.2.2 (formAdj (nbrPSU_sigma g) (Unitary.antidiag n) x) hxadj_mem hxadj_idem
        hxadj_below with h0 | hE
      · left
        rw [← CFSG.StandardType.ClassicalPosition.Geo.formAdj_formAdj (nbrPSU_sigma g) hσ hG hGh x,
            h0]
        simp [formAdj]
      · right
        rw [← CFSG.StandardType.ClassicalPosition.Geo.formAdj_formAdj (nbrPSU_sigma g) hσ hG hGh x,
            hE, ← hff]
        exact CFSG.StandardType.ClassicalPosition.Geo.formAdj_formAdj (nbrPSU_sigma g) hσ hG hGh
            estar
  have heJ_e' : e_J * e' = 0 ∨ e_J * e' = e_J := by
    apply heJ.2.2.2
    · exact Subalgebra.mul_mem _ heJ.1 he'S
    · rw [IsIdempotentElem]
      calc (e_J * e') * (e_J * e') = e_J * (e' * (e_J * e')) := by rw [mul_assoc]
        _ = e_J * ((e' * e_J) * e') := by rw [mul_assoc]
        _ = e_J * ((e_J * e') * e') := by rw [hcommS e' he'S e_J heJ.1]
        _ = e_J * (e_J * (e' * e')) := by rw [mul_assoc]
        _ = e_J * (e_J * e') := by rw [he'.2.1.eq]
        _ = (e_J * e_J) * e' := by rw [mul_assoc]
        _ = e_J * e' := by rw [heJ.2.1.eq]
    · rw [mul_assoc, hcommS e' he'S e_J heJ.1, ← mul_assoc, heJ.2.1.eq]
  have heJ_estar : e_J * estar = 0 ∨ e_J * estar = e_J := by
    apply heJ.2.2.2
    · exact Subalgebra.mul_mem _ heJ.1 hestS
    · rw [IsIdempotentElem]
      calc (e_J * estar) * (e_J * estar) = e_J * (estar * (e_J * estar)) := by rw [mul_assoc]
        _ = e_J * ((estar * e_J) * estar) := by rw [mul_assoc]
        _ = e_J * ((e_J * estar) * estar) := by rw [hcommS estar hestS e_J heJ.1]
        _ = e_J * (e_J * (estar * estar)) := by rw [mul_assoc]
        _ = e_J * (e_J * estar) := by rw [hestar_idem.eq]
        _ = (e_J * e_J) * estar := by rw [mul_assoc]
        _ = e_J * estar := by rw [heJ.2.1.eq]
    · rw [mul_assoc, hcommS estar hestS e_J heJ.1, ← mul_assoc, heJ.2.1.eq]
  have hsumJ : e_J * e' + e_J * estar = e_J := by
    rw [← mul_add, ← hsplit.2.2]
    exact heJε
  rcases heJ_e' with h0 | hE
  · rcases heJ_estar with h0' | hE'
    · exfalso
      have : e_J = 0 := by rw [← hsumJ, h0, h0', add_zero]
      exact heJ.2.2.1 this
    · exact ⟨estar, hestar_prim, hstar_ε, hE', hsplit_star⟩
  · exact ⟨e', he', he'ε, hE, hsplit⟩

private lemma nbrPSU_l8_le_of_map_le_of_quasisimple
    {U X : Type} [Group U] [Group X] (ψ : U →* X) (hψ : ψ.ker ≤ Subgroup.center U)
    {J' K' : Subgroup U} (hJ' : CFSG.Assembly.IsQuasisimple ↥J') (hle : J'.map ψ ≤ K'.map ψ) :
    J' ≤ K' := by
  haveI : Group.IsPerfect ↥J' := Group.IsPerfect.mk hJ'.1
  have hperf : ⁅J', J'⁆ = J' := Subgroup.commutator_eq_self
  have hK'le : ⁅K', K'⁆ ≤ K' := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [commutatorElement_def]
    exact K'.mul_mem (K'.mul_mem (K'.mul_mem hx hy) (K'.inv_mem hx)) (K'.inv_mem hy)
  rw [← hperf, Subgroup.commutator_le]
  intro a ha b hb
  obtain ⟨k, hkK, hk⟩ := Subgroup.mem_map.mp (hle (Subgroup.mem_map_of_mem ψ ha))
  obtain ⟨l, hlK, hl⟩ := Subgroup.mem_map.mp (hle (Subgroup.mem_map_of_mem ψ hb))
  have hza : k⁻¹ * a ∈ Subgroup.center U := by
    apply hψ
    rw [MonoidHom.mem_ker, map_mul, map_inv, hk]
    group
  have hzb : l⁻¹ * b ∈ Subgroup.center U := by
    apply hψ
    rw [MonoidHom.mem_ker, map_mul, map_inv, hl]
    group
  have hza' : ∀ g : U, g * (k⁻¹ * a) = (k⁻¹ * a) * g := Subgroup.mem_center_iff.mp hza
  have hzb' : ∀ g : U, g * (l⁻¹ * b) = (l⁻¹ * b) * g := Subgroup.mem_center_iff.mp hzb
  have hkb : @Bracket.bracket U U commutatorElement k (l⁻¹ * b) = 1 := by
    rw [commutatorElement_def, hzb' k]
    group
  have hzab : @Bracket.bracket U U commutatorElement (k⁻¹ * a) (l * (l⁻¹ * b)) = 1 := by
    rw [commutatorElement_def, (hza' (l * (l⁻¹ * b))).symm]
    group
  have hce : @Bracket.bracket U U commutatorElement (k * (k⁻¹ * a)) (l * (l⁻¹ * b)) =
      @Bracket.bracket U U commutatorElement k l := by
    rw [commutatorElement_mul_left_eq_conj_mul, hzab, commutatorElement_mul_right_eq_mul_conj, hkb]
    group
  have hA : a = k * (k⁻¹ * a) := by group
  have hB : b = l * (l⁻¹ * b) := by group
  rw [hA, hB, hce]
  exact hK'le (Subgroup.commutator_mem_commutator hkK hlK)

private lemma nbrPSU_l8_rootLiftKind
    {X : Type} [Group X] (n g : ℕ) (ψ : ↥(Unitary.SU (nbrPSU_sigmae g) n) →* X) (p : ℕ)
    (J K : Subgroup X) (R Rm : Subgroup X) (hR : R ≤ J) (hJK : J ≤ K)
    (hR0 : GGRootPosG0 .PSU n (g + 1) p ψ R Rm)
    (hψker : ψ.ker ≤ Subgroup.center ↥(Unitary.SU (nbrPSU_sigmae g) n))
    (hn : 3 ≤ n) (hc : Nat.card (nbrPSU_F g) = (2 ^ (g + 1)) ^ 2)
    (K' : Subgroup ↥(Unitary.SU (nbrPSU_sigmae g) n)) (hK'map : K'.map ψ = K) :
    ∃ R' : Subgroup ↥(Unitary.SU (nbrPSU_sigmae g) n),
      R'.map ψ = R ∧ R' ≤ K' ∧
      ((∃ v : Fin n → nbrPSU_F g, v ≠ 0 ∧
          Matrix.vecMul (fun i => nbrPSU_sigmae g (v i)) (Unitary.antidiag n) ⬝ᵥ v = 0 ∧
          R'.map ((Unitary.SU (nbrPSU_sigmae g) n).subtype) =
            unitTransvGroup (nbrPSU_sigma g) (Unitary.antidiag n) v) ∨
       (∃ v w : Fin n → nbrPSU_F g, v ≠ 0 ∧ w ≠ 0 ∧
          LinearIndependent (nbrPSU_F g) ![v, w] ∧
          Matrix.vecMul (fun i => nbrPSU_sigmae g (v i)) (Unitary.antidiag n) ⬝ᵥ v = 0 ∧
          Matrix.vecMul (fun i => nbrPSU_sigmae g (w i)) (Unitary.antidiag n) ⬝ᵥ w = 0 ∧
          Matrix.vecMul (fun i => nbrPSU_sigmae g (v i)) (Unitary.antidiag n) ⬝ᵥ w = 0 ∧
          R'.map ((Unitary.SU (nbrPSU_sigmae g) n).subtype) =
            unitPairGroup (nbrPSU_sigma g) (Unitary.antidiag n) v w)) := by
  obtain ⟨β, hβroot, hkind, u, hRsub, -⟩ := hR0
  let R' : Subgroup ↥(Unitary.SU (nbrPSU_sigmae g) n) :=
    ((ggU .PSU n (g + 1)).D.rootGroup β).map (MulAut.conj u).toMonoidHom
  have hR'map : R'.map ψ = R := by
    rw [hRsub]
    rfl
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hroot : IsPGroup 2 ((ggU .PSU n (g + 1)).D.rootGroup β) :=
    CFSG.LieType.Steinberg.isPGroup_rootGroup
      (CFSG.LieType.BorelTits.unitaryInvolution_involutive hc)
      (Unitary.SUExtras.toStd_ne_zero_of_mem_roots hβroot)
  have hRp : IsPGroup 2 R' := hroot.map (MulAut.conj u).toMonoidHom
  have hodd_ker : Odd (Nat.card ↥ψ.ker) :=
    CFSG.StandardType.odd_natCard_of_le_center_SU (nbrPSU_sigmae g) hψker
  have hle_map : R'.map ψ ≤ K'.map ψ := by
    rw [hR'map, hK'map]
    exact le_trans hR hJK
  have hR'K' : R' ≤ K' :=
    CFSG.GroupTheory.le_of_map_le_map_of_odd (Φ := ψ) hψker hodd_ker hRp hle_map
  refine ⟨R', hR'map, hR'K', ?_⟩
  by_cases hlong : GGLongRoot (ggU .PSU n (g + 1)).D β
  · obtain ⟨v, hv, hviso, hEq⟩ := exists_unitTransvGroup_eq_rootGroup_PSU n g hβroot hlong u
    exact Or.inl ⟨v, hv, hviso, hEq⟩
  · have hshort := hkind.resolve_left hlong
    obtain ⟨v, w, hv, hw, hli, hviso, hwiso, hpair, hEq⟩ :=
      exists_unitPairGroup_eq_rootGroup_PSU n g hβroot hlong hshort.2 u
    exact Or.inr ⟨v, w, hv, hw, hli, hviso, hwiso, hpair, hEq⟩

private lemma nbrPSUx_rank_lt {n : ℕ} {F : Type} [Field F]
    {a b : Matrix (Fin n) (Fin n) F} (ha : IsIdempotentElem a) (hab : a * b = a)
    (hba : b * a = a) (hne : a ≠ b) :
    Module.finrank F (LinearMap.range (Matrix.toLin' a)) <
      Module.finrank F (LinearMap.range (Matrix.toLin' b)) := by
  have hle : LinearMap.range (Matrix.toLin' a) ≤ LinearMap.range (Matrix.toLin' b) := by
    rintro _ ⟨y, rfl⟩
    exact ⟨Matrix.toLin' a y, by rw [← Matrix.toLin'_mul_apply, hba]⟩
  have hlt : LinearMap.range (Matrix.toLin' a) < LinearMap.range (Matrix.toLin' b) := by
    refine lt_of_le_of_ne hle fun heq => hne ?_
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun x => ?_
    have hx : Matrix.toLin' b x ∈ LinearMap.range (Matrix.toLin' a) := by
      rw [heq]
      exact ⟨x, rfl⟩
    obtain ⟨z, hz⟩ := hx
    have h1 : Matrix.toLin' a (Matrix.toLin' b x) = Matrix.toLin' a x := by
      rw [← Matrix.toLin'_mul_apply, hab]
    have h2 : Matrix.toLin' a (Matrix.toLin' a z) = Matrix.toLin' a z := by
      rw [← Matrix.toLin'_mul_apply, ha.eq]
    rw [← h1, ← hz, h2]
  exact Submodule.finrank_lt_finrank_of_lt hlt

private lemma nbrPSUx_J_split
    (n g : ℕ) (S : Set (GL (Fin n) (nbrPSU_F g)))
    (hSU : ∀ s ∈ S, Unitary.conjTr (nbrPSU_sigmae g)
        (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) * Unitary.antidiag n *
        (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) = Unitary.antidiag n)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε_J e_J : Matrix (Fin n) (Fin n) (nbrPSU_F g)}
    (hεJ : IsPrimAdjIdemIn (nbrPSU_sigma g) (Unitary.antidiag n)
      (Algebra.adjoin (nbrPSU_F g) (Units.val '' S)) ε_J)
    (heJ : IsPrimIdemIn (Algebra.adjoin (nbrPSU_F g) (Units.val '' S)) e_J)
    (heJε : e_J * ε_J = e_J) :
    (e_J = ε_J ∧ formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e_J = e_J) ∨
      (e_J ≠ ε_J ∧ formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e_J ≠ e_J ∧
        ε_J = e_J + formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e_J) := by
  by_cases hadj : formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e_J = e_J
  · refine Or.inl ⟨?_, hadj⟩
    rcases hεJ.2.2.2.2 e_J heJ.1 heJ.2.1 hadj heJε with h0 | heq
    · exact absurd h0 heJ.2.2.1
    · exact heq
  · have hG : IsUnit (Unitary.antidiag n : Matrix (Fin n) (Fin n) (nbrPSU_F g)).det :=
      isUnit_iff_ne_zero.mpr (Unitary.det_antidiag_ne_zero n)
    have hσ : ∀ x : nbrPSU_F g, nbrPSU_sigma g (nbrPSU_sigma g x) = x :=
      nbrPSU_sigma_involutive g
    have hGh : Matrix.transpose ((Unitary.antidiag n : Matrix (Fin n) (Fin n) (nbrPSU_F g)).map
        (nbrPSU_sigma g)) = Unitary.antidiag n := nbrPSU_antidiag_transpose_map n g
    have hSU' : ∀ s ∈ S, Matrix.transpose
        (((s : GL (Fin n) (nbrPSU_F g)) : Matrix (Fin n) (Fin n) (nbrPSU_F g)).map
          (nbrPSU_sigma g)) * Unitary.antidiag n *
        ((s : GL (Fin n) (nbrPSU_F g)) : Matrix (Fin n) (Fin n) (nbrPSU_F g)) =
        Unitary.antidiag n := fun s hs => by simpa [Unitary.conjTr] using hSU s hs
    have hest_mem : formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e_J ∈
        Algebra.adjoin (nbrPSU_F g) (Units.val '' S) :=
      Geo.formAdj_mem_adjoin (nbrPSU_sigma g) hG hSU' heJ.1
    have hest_idem : IsIdempotentElem (formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e_J) := by
      rw [IsIdempotentElem,
        ← Geo.formAdj_mul (nbrPSU_sigma g) hG e_J e_J, heJ.2.1.eq]
    have hest_adj : formAdj (nbrPSU_sigma g) (Unitary.antidiag n)
        (formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e_J) = e_J :=
      Geo.formAdj_formAdj (nbrPSU_sigma g) hσ hG hGh e_J
    have hcomm_est : e_J * formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e_J =
        formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e_J * e_J :=
      nbrPSU_adjoin_commute hS heJ.1 hest_mem
    have hεJ_est : ε_J * formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e_J =
        formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e_J := by
      have h := Geo.formAdj_mul (nbrPSU_sigma g) hG e_J ε_J
      rw [heJε, hεJ.2.2.2.1] at h
      exact h.symm
    have hest_εJ : formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e_J * ε_J =
        formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e_J :=
      (nbrPSU_adjoin_commute hS hest_mem hεJ.1).trans hεJ_est
    have hself_mat : e_J * formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e_J +
        e_J * formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e_J = 0 := by
      ext i j
      exact CharTwo.add_self_eq_zero _
    have hx_mem : e_J + formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e_J ∈
        Algebra.adjoin (nbrPSU_F g) (Units.val '' S) :=
      Subalgebra.add_mem _ heJ.1 hest_mem
    have hx_idem : IsIdempotentElem
        (e_J + formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e_J) := by
      rw [IsIdempotentElem]
      calc (e_J + formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e_J) *
            (e_J + formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e_J)
          = e_J * e_J + (e_J * formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e_J +
              formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e_J * e_J) +
              formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e_J *
              formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e_J := by noncomm_ring
        _ = e_J + formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e_J := by
              rw [heJ.2.1.eq, hest_idem.eq, ← hcomm_est, hself_mat, add_zero]
    have hx_adj : formAdj (nbrPSU_sigma g) (Unitary.antidiag n)
        (e_J + formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e_J) =
        e_J + formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e_J := by
      rw [Geo.formAdj_add, hest_adj, add_comm]
    have hx_εJ : (e_J + formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e_J) * ε_J =
        e_J + formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e_J := by
      rw [add_mul, heJε, hest_εJ]
    have hself_est : formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e_J +
        formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e_J = 0 := by
      ext i j
      exact CharTwo.add_self_eq_zero _
    have hx_ne : e_J + formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e_J ≠ 0 := by
      intro h0
      have h : e_J = formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e_J := by
        have h1 : e_J + formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e_J +
            formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e_J =
            formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e_J := by rw [h0, zero_add]
        rwa [add_assoc, hself_est, add_zero] at h1
      exact hadj h.symm
    refine Or.inr ⟨?_, hadj, ?_⟩
    · intro h
      have h1 : formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e_J = e_J := by
        rw [h, hεJ.2.2.2.1]
      exact hadj h1
    · rcases hεJ.2.2.2.2 (e_J + formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e_J)
        hx_mem hx_idem hx_adj hx_εJ with h0 | heq
      · exact absurd h0 hx_ne
      · exact heq.symm

private lemma nbrPSUx_dual_nbr {n : ℕ} {F : Type} [Field F]
    {e est e' : Matrix (Fin n) (Fin n) F}
    (he : IsIdempotentElem e) (hest : IsIdempotentElem est)
    (horth : e * est = 0) (horth' : est * e = 0)
    (hr : Module.finrank F (LinearMap.range (Matrix.toLin' est)) =
      Module.finrank F (LinearMap.range (Matrix.toLin' e))) (hsum : (e + est) * e' = e + est) :
    2 * Module.finrank F (LinearMap.range (Matrix.toLin' e)) ≤
      Module.finrank F (LinearMap.range (Matrix.toLin' e')) := by
  have hsup : LinearMap.range (Matrix.toLin' (e + est)) =
      LinearMap.range (Matrix.toLin' e) ⊔ LinearMap.range (Matrix.toLin' est) := by
    apply le_antisymm
    · rintro x ⟨y, rfl⟩
      have h : Matrix.toLin' (e + est) y = Matrix.toLin' e y + Matrix.toLin' est y := by
        rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.add_mulVec]
      rw [h]
      exact Submodule.add_mem _
        (Submodule.mem_sup_left (LinearMap.mem_range.mpr ⟨y, rfl⟩))
        (Submodule.mem_sup_right (LinearMap.mem_range.mpr ⟨y, rfl⟩))
    · apply sup_le
      · rintro x ⟨y, rfl⟩
        refine LinearMap.mem_range.mpr ⟨Matrix.toLin' e y, ?_⟩
        rw [← Matrix.toLin'_mul_apply, add_mul, he.eq, horth', add_zero]
      · rintro x ⟨y, rfl⟩
        refine LinearMap.mem_range.mpr ⟨Matrix.toLin' est y, ?_⟩
        rw [← Matrix.toLin'_mul_apply, add_mul, horth, hest.eq, zero_add]
  have hinf : LinearMap.range (Matrix.toLin' e) ⊓ LinearMap.range (Matrix.toLin' est) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨y, hy⟩, ⟨z, hz⟩⟩
    have hx_e : Matrix.toLin' e x = x := by
      rw [← hy, ← Matrix.toLin'_mul_apply, he.eq]
    have hx_e0 : Matrix.toLin' e x = 0 := by
      rw [← hz, ← Matrix.toLin'_mul_apply, horth, map_zero, LinearMap.zero_apply]
    exact hx_e.symm.trans hx_e0
  have hfin_sum : Module.finrank F (LinearMap.range (Matrix.toLin' (e + est))) =
      Module.finrank F (LinearMap.range (Matrix.toLin' e)) +
      Module.finrank F (LinearMap.range (Matrix.toLin' est)) := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq
      (LinearMap.range (Matrix.toLin' e)) (LinearMap.range (Matrix.toLin' est))
    rw [← hsup, hinf] at h
    simpa using h
  have hle' : Module.finrank F (LinearMap.range (Matrix.toLin' (e + est))) ≤
      Module.finrank F (LinearMap.range (Matrix.toLin' e')) := by
    calc Module.finrank F (LinearMap.range (Matrix.toLin' (e + est)))
        = Module.finrank F (LinearMap.range (Matrix.toLin' ((e + est) * e'))) := by rw [hsum]
      _ = Module.finrank F (LinearMap.range ((Matrix.toLin' (e + est)).comp
            (Matrix.toLin' e'))) := by rw [Matrix.toLin'_mul]
      _ = Module.finrank F ((LinearMap.range (Matrix.toLin' e')).map
            (Matrix.toLin' (e + est))) := by rw [LinearMap.range_comp]
      _ ≤ Module.finrank F (LinearMap.range (Matrix.toLin' e')) :=
            Submodule.finrank_map_le _ _
  calc 2 * Module.finrank F (LinearMap.range (Matrix.toLin' e))
      = Module.finrank F (LinearMap.range (Matrix.toLin' e)) +
        Module.finrank F (LinearMap.range (Matrix.toLin' est)) := by rw [hr]; ring
    _ = Module.finrank F (LinearMap.range (Matrix.toLin' (e + est))) := hfin_sum.symm
    _ ≤ Module.finrank F (LinearMap.range (Matrix.toLin' e')) := hle'

private lemma nbrPSUx_blockDegree_eq_one {F : Type} [Field F] {n : ℕ}
    {A : Subalgebra F (Matrix (Fin n) (Fin n) F)} {e : Matrix (Fin n) (Fin n) F}
    (he : IsPrimIdemIn A e) (hdeg : blockDegree A e < 2) : blockDegree A e = 1 := by
  let M : Submodule F (Matrix (Fin n) (Fin n) F) :=
    (Subalgebra.toSubmodule A).map (LinearMap.mulRight F e)
  have heM : e ∈ M := ⟨e, he.1, by rw [LinearMap.mulRight_apply, he.2.1.eq]⟩
  have hne : (⟨e, heM⟩ : M) ≠ 0 := by
    intro h
    exact he.2.2.1 (by simpa using congrArg Subtype.val h)
  haveI : Nontrivial M := ⟨⟨⟨e, heM⟩, 0, hne⟩⟩
  have hpos : 0 < Module.finrank F M := Module.finrank_pos_iff.mpr inferInstance
  have hlt : Module.finrank F M < 2 := hdeg
  change Module.finrank F M = 1
  omega

private lemma nbrPSUx_block_scalar {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {A : Subalgebra F (Matrix ι ι F)} {e : Matrix ι ι F}
    (he : IsPrimIdemIn A e) (hdeg : blockDegree A e = 1) {a : Matrix ι ι F}
    (ha : a ∈ A) : ∃ c : F, a * e = c • e := by
  let M : Submodule F (Matrix ι ι F) :=
    (Subalgebra.toSubmodule A).map (LinearMap.mulRight F e)
  have hMdeg : Module.finrank F M = 1 := hdeg
  have heM : e ∈ M := ⟨e, he.1, by rw [LinearMap.mulRight_apply, he.2.1.eq]⟩
  have hene : (⟨e, heM⟩ : M) ≠ 0 := by
    intro h
    exact he.2.2.1 (by simpa using congrArg Subtype.val h)
  have haM : a * e ∈ M := ⟨a, ha, by rw [LinearMap.mulRight_apply]⟩
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨e, heM⟩ : M) hene).mp hMdeg
    (⟨a * e, haM⟩ : M)
  exact ⟨c, by simpa using congrArg Subtype.val hc.symm⟩

private lemma nbrPSUx_selfDual_nbr
    {n g : ℕ} {S : Set (GL (Fin n) (nbrPSU_F g))} (s_e : GL (Fin n) (nbrPSU_F g))
    (hs_eS : s_e ∈ S)
    (hSU : ∀ s ∈ S, Unitary.conjTr (nbrPSU_sigmae g)
        (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) * Unitary.antidiag n *
        (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) = Unitary.antidiag n)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e_J : Matrix (Fin n) (Fin n) (nbrPSU_F g)}
    (heJ : IsPrimIdemIn (Algebra.adjoin (nbrPSU_F g) (Units.val '' S)) e_J)
    (hadj : formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e_J = e_J)
    (hdegJ : blockDegree (Algebra.adjoin (nbrPSU_F g) (Units.val '' S)) e_J < 2)
    {ε : Matrix (Fin n) (Fin n) (nbrPSU_F g)}
    {e' : Matrix (Fin n) (Fin n) (nbrPSU_F g)}
    (he' : IsPrimIdemIn (Algebra.adjoin (nbrPSU_F g)
      (Units.val '' ({s_e} : Set (GL (Fin n) (nbrPSU_F g))))) e')
    (hdeg' : blockDegree (Algebra.adjoin (nbrPSU_F g)
      (Units.val '' ({s_e} : Set (GL (Fin n) (nbrPSU_F g))))) e' < 2)
    (hsplit : e' = ε ∨ (e' ≠ ε ∧ formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e' ≠ e' ∧
      ε = e' + formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e'))
    (hmul : e_J * ε = e_J) :
    e' = ε := by
  by_contra hne'
  have hdual : e' ≠ ε ∧ formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e' ≠ e' ∧
      ε = e' + formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e' := hsplit.resolve_left hne'
  let est : Matrix (Fin n) (Fin n) (nbrPSU_F g) := formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e'
  let q : ℕ := 2 ^ (g + 1)
  have hc : Nat.card (nbrPSU_F g) = (2 ^ (g + 1)) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul 2 (g + 1) (by omega)
  have hG : IsUnit (Unitary.antidiag n : Matrix (Fin n) (Fin n) (nbrPSU_F g)).det :=
    isUnit_iff_ne_zero.mpr (Unitary.det_antidiag_ne_zero n)
  have hσ : ∀ x : nbrPSU_F g, nbrPSU_sigma g (nbrPSU_sigma g x) = x := nbrPSU_sigma_involutive g
  have hGh : Matrix.transpose ((Unitary.antidiag n : Matrix (Fin n) (Fin n) (nbrPSU_F g)).map
      (nbrPSU_sigma g)) = Unitary.antidiag n := nbrPSU_antidiag_transpose_map n g
  have hSU' : ∀ s ∈ S, Matrix.transpose
      (((s : GL (Fin n) (nbrPSU_F g)) : Matrix (Fin n) (Fin n) (nbrPSU_F g)).map
        (nbrPSU_sigma g)) * Unitary.antidiag n *
      ((s : GL (Fin n) (nbrPSU_F g)) : Matrix (Fin n) (Fin n) (nbrPSU_F g)) = Unitary.antidiag n :=
    fun s hs => by simpa [Unitary.conjTr] using hSU s hs
  have hSU_e : ∀ s ∈ ({s_e} : Set (GL (Fin n) (nbrPSU_F g))),
      Unitary.conjTr (nbrPSU_sigmae g)
        (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) * Unitary.antidiag n *
        (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) = Unitary.antidiag n := by
    intro s hs
    rw [Set.mem_singleton_iff] at hs
    rw [hs]
    exact hSU s_e hs_eS
  have hSU_eT : ∀ s ∈ ({s_e} : Set (GL (Fin n) (nbrPSU_F g))),
      Matrix.transpose (((s : GL (Fin n) (nbrPSU_F g)) : Matrix (Fin n) (Fin n) (nbrPSU_F g)).map
        (nbrPSU_sigma g)) * Unitary.antidiag n *
      ((s : GL (Fin n) (nbrPSU_F g)) : Matrix (Fin n) (Fin n) (nbrPSU_F g)) = Unitary.antidiag n :=
    fun s hs => by simpa [Unitary.conjTr] using hSU_e s hs
  have hS_e : ∀ s ∈ ({s_e} : Set (GL (Fin n) (nbrPSU_F g))),
      ∀ s' ∈ ({s_e} : Set (GL (Fin n) (nbrPSU_F g))), Commute s s' := by
    intro s hs s' hs'
    rw [Set.mem_singleton_iff] at hs hs'
    rw [hs, hs']
  obtain ⟨s, hs, c, hce, hcζ⟩ :=
    exists_dualPair_char_ne_PSU hc n ({s_e} : Set (GL (Fin n) (nbrPSU_F g))) hSU_e hS_e he'
      hdeg' hdual.2.1
  rw [Set.mem_singleton_iff] at hs
  rw [hs] at hce
  have he'_mem : e' ∈ Algebra.adjoin (nbrPSU_F g) (Units.val '' S) :=
    Algebra.adjoin_mono (Set.image_mono (Set.singleton_subset_iff.mpr hs_eS)) he'.1
  have hest_mem : est ∈ Algebra.adjoin (nbrPSU_F g) (Units.val '' S) := by
    have := Geo.formAdj_mem_adjoin (nbrPSU_sigma g) hG hSU' he'_mem
    simpa [est] using this
  have hest_mem_e : est ∈ Algebra.adjoin (nbrPSU_F g)
      (Units.val '' ({s_e} : Set (GL (Fin n) (nbrPSU_F g)))) := by
    have := Geo.formAdj_mem_adjoin (nbrPSU_sigma g) hG hSU_eT he'.1
    simpa [est] using this
  have hest_idem : IsIdempotentElem est := by
    rw [IsIdempotentElem, ← Geo.formAdj_mul (nbrPSU_sigma g) hG e' e', he'.2.1.eq]
  have hcomm_est : (s_e : Matrix (Fin n) (Fin n) (nbrPSU_F g)) * est =
      est * (s_e : Matrix (Fin n) (Fin n) (nbrPSU_F g)) := by
    have := nbrPSU_adjoin_commute hS_e
      (Algebra.subset_adjoin ⟨s_e, Set.mem_singleton s_e, rfl⟩) hest_mem_e
    simpa [est] using this
  have hcne : c ≠ 0 := by
    intro hc0
    have h0 : (s_e : Matrix (Fin n) (Fin n) (nbrPSU_F g)) * e' = 0 := by rw [hce, hc0, zero_smul]
    have he0 : e' = 0 := by
      calc e' = 1 * e' := (Matrix.one_mul e').symm
        _ = (((s_e⁻¹ : GL (Fin n) (nbrPSU_F g)) : Matrix (Fin n) (Fin n) (nbrPSU_F g)) *
              (s_e : Matrix (Fin n) (Fin n) (nbrPSU_F g))) * e' := by
              rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
        _ = ((s_e⁻¹ : GL (Fin n) (nbrPSU_F g)) : Matrix (Fin n) (Fin n) (nbrPSU_F g)) *
              ((s_e : Matrix (Fin n) (Fin n) (nbrPSU_F g)) * e') := by rw [Matrix.mul_assoc]
        _ = 0 := by rw [h0, Matrix.mul_zero]
    exact he'.2.2.1 he0
  have hσc : nbrPSU_sigma g c ≠ 0 := by
    intro h0
    refine hcne ?_
    have := congrArg (nbrPSU_sigma g) h0
    rwa [map_zero, hσ c] at this
  have hs_inv : formAdj (nbrPSU_sigma g) (Unitary.antidiag n)
      (s_e : Matrix (Fin n) (Fin n) (nbrPSU_F g)) =
      ((s_e⁻¹ : GL (Fin n) (nbrPSU_F g)) : Matrix (Fin n) (Fin n) (nbrPSU_F g)) :=
    Geo.formAdj_eq_inv_of_isometry (nbrPSU_sigma g) hG s_e (hSU s_e hs_eS)
  have hce_star : (s_e : Matrix (Fin n) (Fin n) (nbrPSU_F g)) * est =
      (nbrPSU_sigma g c)⁻¹ • est := by
    have h := Geo.formAdj_mul (nbrPSU_sigma g) hG (s_e : Matrix (Fin n) (Fin n) (nbrPSU_F g)) e'
    rw [hce, Geo.formAdj_smul, hs_inv] at h
    have h2 : est = nbrPSU_sigma g c • (est * (s_e : Matrix (Fin n) (Fin n) (nbrPSU_F g))) := by
      calc est = est * 1 := (Matrix.mul_one _).symm
        _ = est * (((s_e⁻¹ : GL (Fin n) (nbrPSU_F g)) :
              Matrix (Fin n) (Fin n) (nbrPSU_F g)) *
              (s_e : Matrix (Fin n) (Fin n) (nbrPSU_F g))) := by
              rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
        _ = (est * ((s_e⁻¹ : GL (Fin n) (nbrPSU_F g)) :
              Matrix (Fin n) (Fin n) (nbrPSU_F g))) *
              (s_e : Matrix (Fin n) (Fin n) (nbrPSU_F g)) := by
              rw [Matrix.mul_assoc]
        _ = (nbrPSU_sigma g c • est) * (s_e : Matrix (Fin n) (Fin n) (nbrPSU_F g)) := by
              rw [show est * ((s_e⁻¹ : GL (Fin n) (nbrPSU_F g)) :
                  Matrix (Fin n) (Fin n) (nbrPSU_F g)) =
                nbrPSU_sigma g c • est by simpa [est] using h.symm]
        _ = nbrPSU_sigma g c • (est * (s_e : Matrix (Fin n) (Fin n) (nbrPSU_F g))) := by
              rw [Matrix.smul_mul]
    have h1 : est * (s_e : Matrix (Fin n) (Fin n) (nbrPSU_F g)) = (nbrPSU_sigma g c)⁻¹ • est := by
      calc est * (s_e : Matrix (Fin n) (Fin n) (nbrPSU_F g)) = (nbrPSU_sigma g c)⁻¹ •
            (nbrPSU_sigma g c • (est * (s_e : Matrix (Fin n) (Fin n) (nbrPSU_F g)))) := by
              rw [smul_smul, inv_mul_cancel₀ hσc, one_smul]
        _ = (nbrPSU_sigma g c)⁻¹ • est := by rw [← h2]
    rw [hcomm_est, h1]
  have hdeg1 : blockDegree (Algebra.adjoin (nbrPSU_F g) (Units.val '' S)) e_J = 1 :=
    nbrPSUx_blockDegree_eq_one heJ hdegJ
  obtain ⟨z, hze⟩ := nbrPSUx_block_scalar heJ hdeg1
    (Algebra.subset_adjoin ⟨s_e, hs_eS, rfl⟩)
  have hs_comm_J : (s_e : Matrix (Fin n) (Fin n) (nbrPSU_F g)) * e_J =
      e_J * (s_e : Matrix (Fin n) (Fin n) (nbrPSU_F g)) :=
    nbrPSU_adjoin_commute hS (Algebra.subset_adjoin ⟨s_e, hs_eS, rfl⟩) heJ.1
  have hzsq : nbrPSU_sigma g z * z = 1 := by
    have h := Geo.formAdj_mul (nbrPSU_sigma g) hG (s_e : Matrix (Fin n) (Fin n) (nbrPSU_F g)) e_J
    rw [hze, Geo.formAdj_smul, hadj, hs_inv] at h
    have h2 : (nbrPSU_sigma g z • e_J) * (s_e : Matrix (Fin n) (Fin n) (nbrPSU_F g)) = e_J := by
      rw [h, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
    have h2' : (nbrPSU_sigma g z * z) • e_J =
        (nbrPSU_sigma g z • e_J) * (s_e : Matrix (Fin n) (Fin n) (nbrPSU_F g)) := by
      rw [← smul_smul, ← hze, hs_comm_J, ← Matrix.smul_mul]
    have h3 : (nbrPSU_sigma g z * z) • e_J = 1 • e_J := by
      rw [h2', h2, one_smul]
    exact smul_left_injective (nbrPSU_F g) heJ.2.2.1 (by simpa using h3)
  have hσz : nbrPSU_sigma g z = z ^ q := by
    show (nbrPSU_sigmae g) z = z ^ q
    rw [show q = 2 ^ (g + 1) from rfl]
    exact CFSG.LieType.BorelTits.unitaryInvolution_apply (nbrPSU_F g) 2 (g + 1) z
  have hzq : z ^ (q + 1) = 1 := by
    rw [mul_comm] at hzsq
    rw [hσz] at hzsq
    rwa [← pow_succ'] at hzsq
  have hσc : nbrPSU_sigma g c = c ^ q := by
    show (nbrPSU_sigmae g) c = c ^ q
    rw [show q = 2 ^ (g + 1) from rfl]
    exact CFSG.LieType.BorelTits.unitaryInvolution_apply (nbrPSU_F g) 2 (g + 1) c
  have hxq : (c ^ (q + 1)) ^ q = c ^ (q + 1) := by
    rw [← pow_mul, show (q + 1) * q = q ^ 2 + q by ring, pow_add]
    have hcpow : c ^ (q ^ 2) = c := by
      haveI : Fintype (nbrPSU_F g) := Fintype.ofFinite _
      have h1 : Fintype.card (nbrPSU_F g) = q ^ 2 := by
        rw [← Nat.card_eq_fintype_card]
        exact hc
      rw [← h1]
      exact FiniteField.pow_card c
    rw [hcpow, ← pow_succ']
  have hsum : e_J * e' + e_J * est = e_J := by
    rw [← mul_add]
    rw [show e' + est = ε by simpa [est] using hdual.2.2.symm]
    exact hmul
  have hp_mem : e_J * e' ∈ Algebra.adjoin (nbrPSU_F g) (Units.val '' S) :=
    Subalgebra.mul_mem _ heJ.1 he'_mem
  have hq_mem : e_J * est ∈ Algebra.adjoin (nbrPSU_F g) (Units.val '' S) :=
    Subalgebra.mul_mem _ heJ.1 hest_mem
  have hp_idem : IsIdempotentElem (e_J * e') := by
    rw [IsIdempotentElem]
    calc (e_J * e') * (e_J * e') = e_J * (e' * (e_J * e')) := by rw [mul_assoc]
      _ = e_J * ((e' * e_J) * e') := by rw [mul_assoc]
      _ = e_J * ((e_J * e') * e') := by rw [nbrPSU_adjoin_commute hS he'_mem heJ.1]
      _ = e_J * (e_J * (e' * e')) := by rw [mul_assoc]
      _ = e_J * (e_J * e') := by rw [he'.2.1.eq]
      _ = (e_J * e_J) * e' := by rw [mul_assoc]
      _ = e_J * e' := by rw [heJ.2.1.eq]
  have hp_below : (e_J * e') * e_J = e_J * e' := by
    rw [mul_assoc, nbrPSU_adjoin_commute hS he'_mem heJ.1, ← mul_assoc, heJ.2.1.eq]
  have hq_idem : IsIdempotentElem (e_J * est) := by
    rw [IsIdempotentElem]
    calc (e_J * est) * (e_J * est) = e_J * (est * (e_J * est)) := by rw [mul_assoc]
      _ = e_J * ((est * e_J) * est) := by rw [mul_assoc]
      _ = e_J * ((e_J * est) * est) := by rw [nbrPSU_adjoin_commute hS hest_mem heJ.1]
      _ = e_J * (e_J * (est * est)) := by rw [mul_assoc]
      _ = e_J * (e_J * est) := by rw [hest_idem.eq]
      _ = (e_J * e_J) * est := by rw [mul_assoc]
      _ = e_J * est := by rw [heJ.2.1.eq]
  have hq_below : (e_J * est) * e_J = e_J * est := by
    rw [mul_assoc, nbrPSU_adjoin_commute hS hest_mem heJ.1, ← mul_assoc, heJ.2.1.eq]
  rcases heJ.2.2.2 (e_J * e') hp_mem hp_idem hp_below with hp0 | hpE
  · have hqE : e_J * est = e_J := by
      have := hsum
      rw [hp0, zero_add] at this
      exact this
    have hz : z = (nbrPSU_sigma g c)⁻¹ := by
      have h1 : e_J * (s_e : Matrix (Fin n) (Fin n) (nbrPSU_F g)) = (nbrPSU_sigma g c)⁻¹ • e_J := by
        calc e_J * (s_e : Matrix (Fin n) (Fin n) (nbrPSU_F g)) =
              (e_J * est) * (s_e : Matrix (Fin n) (Fin n) (nbrPSU_F g)) := by rw [hqE]
          _ = e_J * (est * (s_e : Matrix (Fin n) (Fin n) (nbrPSU_F g))) := by rw [mul_assoc]
          _ = e_J * ((s_e : Matrix (Fin n) (Fin n) (nbrPSU_F g)) * est) := by rw [← hcomm_est]
          _ = e_J * ((nbrPSU_sigma g c)⁻¹ • est) := by rw [hce_star]
          _ = (nbrPSU_sigma g c)⁻¹ • (e_J * est) := by rw [Matrix.mul_smul]
          _ = (nbrPSU_sigma g c)⁻¹ • e_J := by rw [hqE]
      have h2 : e_J * (s_e : Matrix (Fin n) (Fin n) (nbrPSU_F g)) = z • e_J := by
        rw [← hs_comm_J]; exact hze
      rw [h1] at h2
      exact (smul_left_injective (nbrPSU_F g) heJ.2.2.1 h2).symm
    have h4 : ((nbrPSU_sigma g c)⁻¹) ^ (q + 1) = 1 := by rw [← hz]; exact hzq
    rw [hσc] at h4
    have h5 : (c ^ q) ^ (q + 1) = 1 := by
      have h7 : (c ^ q) ^ (q + 1) * ((c ^ q)⁻¹) ^ (q + 1) = 1 := by
        rw [← mul_pow, mul_inv_cancel₀ (pow_ne_zero q hcne), one_pow]
      rw [h4, mul_one] at h7
      exact h7
    rw [← pow_mul, show q * (q + 1) = (q + 1) * q by ring, pow_mul, hxq] at h5
    exact hcζ (by simpa [q] using h5)
  · have hz : z = c := by
      have h1 : e_J * (s_e : Matrix (Fin n) (Fin n) (nbrPSU_F g)) = c • e_J := by
        calc e_J * (s_e : Matrix (Fin n) (Fin n) (nbrPSU_F g)) =
              (e_J * e') * (s_e : Matrix (Fin n) (Fin n) (nbrPSU_F g)) := by rw [hpE]
          _ = e_J * (e' * (s_e : Matrix (Fin n) (Fin n) (nbrPSU_F g))) := by rw [mul_assoc]
          _ = e_J * ((s_e : Matrix (Fin n) (Fin n) (nbrPSU_F g)) * e') := by
                rw [nbrPSU_adjoin_commute hS he'_mem (Algebra.subset_adjoin ⟨s_e, hs_eS, rfl⟩)]
          _ = e_J * (c • e') := by rw [hce]
          _ = c • (e_J * e') := by rw [Matrix.mul_smul]
          _ = c • e_J := by rw [hpE]
      have h2 : e_J * (s_e : Matrix (Fin n) (Fin n) (nbrPSU_F g)) = z • e_J := by
        rw [← hs_comm_J]; exact hze
      rw [h1] at h2
      exact (smul_left_injective (nbrPSU_F g) heJ.2.2.1 h2).symm
    have hc1 : c ^ (q + 1) = 1 := by rw [← hz]; exact hzq
    exact hcζ (by simpa [q] using hc1)

private lemma nbrPSUx_basePow
    {X : Type} [Group X] [Finite X] (n g : ℕ)
    (ψ : ↥(Unitary.SU (nbrPSU_sigmae g) n) →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X)
    (hH : GGSixPosHyp .PSU n (g + 1) ψ p G₀ B₁ D J L x)
    (S : Set (GL (Fin n) (nbrPSU_F g)))
    (hSdef : ∀ s : GL (Fin n) (nbrPSU_F g), s ∈ S ↔
      Unitary.conjTr (nbrPSU_sigmae g) (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) *
          Unitary.antidiag n * (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) = Unitary.antidiag n ∧
        ∃ d ∈ D, IsGLLift ((Unitary.SU (nbrPSU_sigmae g) n).subtype) ψ s d) :
    ∀ s ∈ S, ∃ c : nbrPSU_F g,
      (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) ^ p = Matrix.scalar (Fin n) c := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩ := hH
  have hc : Nat.card (nbrPSU_F g) = (2 ^ (g + 1)) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul 2 (g + 1) (by omega)
  have hadm : CFSG.Open.StatedLieAdmissible .PSU n 2 (g + 1) := h3.admissible
  have hn : 3 ≤ n := hadm.2.2.1
  have hf : 1 ≤ g + 1 := hadm.2.1
  intro s hs
  obtain ⟨-, d, hd, hsl⟩ := (hSdef s).mp hs
  exact (nbrPSU_lift_odd_scalar hc hn hf ψ h2 h5 h6 (h9.2 d (h11 hd)) hsl).2

private lemma nbrPSUx_neighbourLiftData
    {X : Type} [Group X] [Finite X] (n g : ℕ)
    (ψ : ↥(Unitary.SU (nbrPSU_sigmae g) n) →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X)
    (hH : GGSixPosHyp .PSU n (g + 1) ψ p G₀ B₁ D J L x)
    (e : X) (he : e ∈ D) (K : Subgroup X)
    (hKcomp : IsComponentOf K (G₀ ⊓ Subgroup.centralizer ({e} : Set X))) :
    ∃ (s_e : GL (Fin n) (nbrPSU_F g)) (K' : Subgroup ↥(Unitary.SU (nbrPSU_sigmae g) n)),
      K'.map ψ = K ∧
      IsComponentOf K' ((Subgroup.centralizer ({s_e} : Set (GL (Fin n) (nbrPSU_F g)))).comap
        ((Unitary.SU (nbrPSU_sigmae g) n).subtype)) ∧
      Odd (orderOf s_e) ∧
      Unitary.conjTr (nbrPSU_sigmae g) (s_e : Matrix (Fin n) (Fin n) (nbrPSU_F g)) *
          Unitary.antidiag n * (s_e : Matrix (Fin n) (Fin n) (nbrPSU_F g)) =
        Unitary.antidiag n ∧
      IsGLLift ((Unitary.SU (nbrPSU_sigmae g) n).subtype) ψ s_e e := by
  have hH' : GGSixPosHyp .PSU n (g + 1) ψ p G₀ B₁ D J L x := hH
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩ := hH'
  have hc : Nat.card (nbrPSU_F g) = (2 ^ (g + 1)) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul 2 (g + 1) (by omega)
  have hadm : CFSG.Open.StatedLieAdmissible .PSU n 2 (g + 1) := h3.admissible
  have hn : 3 ≤ n := hadm.2.2.1
  have hf : 1 ≤ g + 1 := hadm.2.1
  have hB₁N : B₁ ≤ Subgroup.normalizer (ψ.range : Set X) := by
    have hψrange : (ψ.range : Set X) = (G₀ : Set X) :=
      congrArg (fun H : Subgroup X => (H : Set X)) h1
    rw [hψrange]
    exact h7
  have hdiag : ∀ b ∈ B₁, GGPsiInnerDiag (Unitary.rootDatum hc n) ψ b := fun b hb => h8 b hb
  obtain ⟨s_e, hs_e_iso, hs_e_lift⟩ :=
    exists_isGLLift_PSU hc n hn ψ h2 (hB₁N (h11 he)) (hdiag e (h11 he))
  have hep : e ^ p = 1 := h9.2 e (h11 he)
  have hodd_se : Odd (orderOf s_e) :=
    (nbrPSU_lift_odd_scalar hc hn hf ψ h2 h5 h6 hep hs_e_lift).1
  have hcentD : Subgroup.centralizer (Subgroup.zpowers e : Set X) =
      Subgroup.centralizer ({e} : Set X) := by
    rw [Subgroup.zpowers_eq_closure e]
    exact Subgroup.centralizer_closure ({e} : Set X)
  have hJsub : ψ.range ⊓ Subgroup.centralizer (Subgroup.zpowers e : Set X) =
      G₀ ⊓ Subgroup.centralizer ({e} : Set X) := by
    rw [hcentD]
    exact congrArg (fun H : Subgroup X => H ⊓ Subgroup.centralizer ({e} : Set X)) h1
  have hJ : IsComponentOf K (ψ.range ⊓ Subgroup.centralizer (Subgroup.zpowers e : Set X)) := by
    rw [hJsub]
    exact hKcomp
  let P : GL (Fin n) (nbrPSU_F g) → Prop := fun s => ∃ k : ℤ, s = s_e ^ k
  let T : Set (GL (Fin n) (nbrPSU_F g)) :=
    {s | P s ∧ ∃ d ∈ Subgroup.zpowers e,
      IsGLLift ((Unitary.SU (nbrPSU_sigmae g) n).subtype) ψ s d}
  have hlift : ∀ d ∈ Subgroup.zpowers e,
      ∃ s, P s ∧ IsGLLift ((Unitary.SU (nbrPSU_sigmae g) n).subtype) ψ s d := by
    intro d hd
    rw [Subgroup.mem_zpowers_iff] at hd
    obtain ⟨k, hk⟩ := hd
    rw [← hk]
    exact ⟨s_e ^ k, ⟨k, rfl⟩, nbrPSU_isGLLift_zpow (Subgroup.subtype_injective _) hs_e_lift k⟩
  obtain ⟨K', hK'comp, hK'map⟩ :=
    StepA.exists_isComponentOf_comap_lift_of_isGLLift ((Unitary.SU (nbrPSU_sigmae g) n).subtype)
      (Subgroup.subtype_injective _) ψ h2 P hJ hlift
  have hcentT : Subgroup.centralizer ({s_e} : Set (GL (Fin n) (nbrPSU_F g))) =
      Subgroup.centralizer T := by
    apply le_antisymm
    · intro g hg
      have hcomm : Commute s_e g :=
        (Subgroup.mem_centralizer_iff.mp hg) s_e (Set.mem_singleton s_e)
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      obtain ⟨⟨k, rfl⟩, -⟩ := ht
      exact (hcomm.zpow_left k).eq
    · intro g hg
      rw [Subgroup.mem_centralizer_iff] at hg ⊢
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact hg s_e ⟨⟨1, by rw [zpow_one]⟩, e,
        Subgroup.mem_zpowers_iff.mpr ⟨1, by rw [zpow_one]⟩, hs_e_lift⟩
  refine ⟨s_e, K', hK'map, ?_, hodd_se, hs_e_iso, hs_e_lift⟩
  rw [hcentT]
  exact hK'comp

private lemma nbrPSUx_neighbourBlockData
    (n g : ℕ) (S : Set (GL (Fin n) (nbrPSU_F g)))
    (J' : Subgroup ↥(Unitary.SU (nbrPSU_sigmae g) n))
    (ε_J e_J : Matrix (Fin n) (Fin n) (nbrPSU_F g))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    (hεJ : IsPrimAdjIdemIn (nbrPSU_sigma g) (Unitary.antidiag n)
      (Algebra.adjoin (nbrPSU_F g) (Units.val '' S)) ε_J)
    (hJ'block : IsComponentOf J'
      ⁅glBlockCentralizer ((Unitary.SU (nbrPSU_sigmae g) n).subtype) S ε_J,
        glBlockCentralizer ((Unitary.SU (nbrPSU_sigmae g) n).subtype) S ε_J⁆)
    (heJ : IsPrimIdemIn (Algebra.adjoin (nbrPSU_F g) (Units.val '' S)) e_J)
    (heJε : e_J * ε_J = e_J)
    (hdegJ : blockDegree (Algebra.adjoin (nbrPSU_F g) (Units.val '' S)) e_J < 2)
    (K' : Subgroup ↥(Unitary.SU (nbrPSU_sigmae g) n)) (hJ'K' : J' ≤ K')
    (s_e : GL (Fin n) (nbrPSU_F g)) (hs_eS : s_e ∈ S)
    (hK'comp : IsComponentOf K'
      ((Subgroup.centralizer ({s_e} : Set (GL (Fin n) (nbrPSU_F g)))).comap
        ((Unitary.SU (nbrPSU_sigmae g) n).subtype)))
    (hodd_se : Odd (orderOf s_e))
    (hiso : Unitary.conjTr (nbrPSU_sigmae g) (s_e : Matrix (Fin n) (Fin n) (nbrPSU_F g)) *
        Unitary.antidiag n * (s_e : Matrix (Fin n) (Fin n) (nbrPSU_F g)) = Unitary.antidiag n) :
    ∃ (ε e' : Matrix (Fin n) (Fin n) (nbrPSU_F g)),
      IsPrimAdjIdemIn (nbrPSU_sigma g) (Unitary.antidiag n)
        (Algebra.adjoin (nbrPSU_F g) (Units.val '' ({s_e} : Set (GL (Fin n) (nbrPSU_F g))))) ε ∧
      IsComponentOf K'
        ⁅glBlockCentralizer ((Unitary.SU (nbrPSU_sigmae g) n).subtype)
            ({s_e} : Set (GL (Fin n) (nbrPSU_F g))) ε,
          glBlockCentralizer ((Unitary.SU (nbrPSU_sigmae g) n).subtype)
            ({s_e} : Set (GL (Fin n) (nbrPSU_F g))) ε⁆ ∧
      IsPrimIdemIn (Algebra.adjoin (nbrPSU_F g)
        (Units.val '' ({s_e} : Set (GL (Fin n) (nbrPSU_F g))))) e' ∧ e' * ε = e' ∧
      blockDegree (Algebra.adjoin (nbrPSU_F g)
        (Units.val '' ({s_e} : Set (GL (Fin n) (nbrPSU_F g))))) e' < 2 ∧
      (e' = ε ∨ (e' ≠ ε ∧ formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e' ≠ e' ∧
        ε = e' + formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e')) ∧
      e_J * ε = e_J ∧ e_J * e' = e_J := by
  have hSe : ({s_e} : Set (GL (Fin n) (nbrPSU_F g))) ⊆ S := Set.singleton_subset_iff.mpr hs_eS
  have hSU_e : ∀ s ∈ ({s_e} : Set (GL (Fin n) (nbrPSU_F g))),
      Unitary.conjTr (nbrPSU_sigmae g) (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) *
          Unitary.antidiag n * (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) =
        Unitary.antidiag n := by
    intro s hs
    rw [Set.mem_singleton_iff] at hs
    rw [hs]
    exact hiso
  have hS_e : ∀ s ∈ ({s_e} : Set (GL (Fin n) (nbrPSU_F g))),
      ∀ s' ∈ ({s_e} : Set (GL (Fin n) (nbrPSU_F g))), Commute s s' := by
    intro s hs s' hs'
    rw [Set.mem_singleton_iff] at hs hs'
    rw [hs, hs']
  have hodd_e : ∀ s ∈ ({s_e} : Set (GL (Fin n) (nbrPSU_F g))), Odd (orderOf s) := by
    intro s hs
    rw [Set.mem_singleton_iff] at hs
    rw [hs]
    exact hodd_se
  obtain ⟨ε, hε, hK'ε⟩ := nbrPSU_l8_neighbourStarBlock K' s_e hK'comp
  obtain ⟨e', he', he'ε, hsplit⟩ :=
    nbrPSU_l8_neighbourPrimitiveBlock n g ({s_e} : Set (GL (Fin n) (nbrPSU_F g))) hSU_e hS_e hε
  have hεJε : ε_J * ε = ε_J :=
    nbrPSU_l8_baseAdjIdem_le hSe hS hεJ hε hJ'block hK'ε hJ'K'
  have heJε' : e_J * ε = e_J := by
    calc e_J * ε = (e_J * ε_J) * ε := by rw [heJε]
      _ = e_J * (ε_J * ε) := mul_assoc _ _ _
      _ = e_J * ε_J := by rw [hεJε]
      _ = e_J := heJε
  rcases hsplit with hself | hdual
  · have hmul : e_J * e' = e_J := by rw [hself]; exact heJε'
    exact ⟨ε, e', hε, hK'ε, he', he'ε,
      lt_of_le_of_lt (nbrPSU_l8_blockFieldEmbedding_of_mul hSe hS hodd heJ he' hmul) hdegJ,
      Or.inl hself, heJε', hmul⟩
  · obtain ⟨e'', he'', he''ε, hmul, hsplit''⟩ :=
      nbrPSU_l8_dualPair_below hSe hSU_e hS heJ he' he'ε hdual heJε'
    exact ⟨ε, e'', hε, hK'ε, he'', he''ε,
      lt_of_le_of_lt (nbrPSU_l8_blockFieldEmbedding_of_mul hSe hS hodd heJ he'' hmul) hdegJ,
      Or.inr hsplit'', heJε', hmul⟩

private lemma nbrPSUx_GGLongRoot_mem_roots {U : Type} [Group U] {Δ : UniversalRootDatum U}
    {γ : Fin Δ.rank → ℤ} (hγ : GGLongRoot Δ γ) : γ ∈ Δ.roots := by
  obtain ⟨w, γ₀, hγ₀, -, rfl⟩ := hγ
  exact weylAction_mem_roots Δ.isFiniteType w hγ₀

private lemma nbrPSUx_eq_one_of_range_top {n : ℕ} {F : Type} [Field F]
    {a : Matrix (Fin n) (Fin n) F} (ha : IsIdempotentElem a)
    (htop : LinearMap.range (Matrix.toLin' a) = ⊤) : a = 1 := by
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun x => ?_
  obtain ⟨y, hy⟩ : x ∈ LinearMap.range (Matrix.toLin' a) := by
    rw [htop]
    trivial
  rw [Matrix.toLin'_one, LinearMap.id_apply, ← hy, ← Matrix.toLin'_mul_apply, ha.eq]

private lemma nbrPSUx_scalar_lift_commute {X : Type} [Group X] (n g : ℕ)
    (ψ : ↥(Unitary.SU (nbrPSU_sigmae g) n) →* X)
    {s : GL (Fin n) (nbrPSU_F g)} {b : X}
    (hs : IsGLLift ((Unitary.SU (nbrPSU_sigmae g) n).subtype) ψ s b)
    (hsc : ∃ c : nbrPSU_F g,
      (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) = c • 1)
    (u : ↥(Unitary.SU (nbrPSU_sigmae g) n)) : b⁻¹ * ψ u * b = ψ u := by
  obtain ⟨u', hu'j, hu'ψ⟩ := hs u
  obtain ⟨c, hc⟩ := hsc
  have hcen : s * (Unitary.SU (nbrPSU_sigmae g) n).subtype u =
      (Unitary.SU (nbrPSU_sigmae g) n).subtype u * s := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hc, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
      Matrix.mul_one]
  have hu'u : u' = u := by
    apply Subgroup.subtype_injective (Unitary.SU (nbrPSU_sigmae g) n)
    rw [hu'j, mul_inv_eq_iff_eq_mul]
    exact hcen
  exact hu'ψ.trans (congrArg ψ hu'u)

private lemma nbrPSUx_J_self
    {X : Type} [Group X] [Finite X] (n g : ℕ)
    (ψ : ↥(Unitary.SU (nbrPSU_sigmae g) n) →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X)
    (hH : GGSixPosHyp .PSU n (g + 1) ψ p G₀ B₁ D J L x)
    (S : Set (GL (Fin n) (nbrPSU_F g))) (J' : Subgroup ↥(Unitary.SU (nbrPSU_sigmae g) n))
    (ε_J e_J : Matrix (Fin n) (Fin n) (nbrPSU_F g))
    (hSdef : ∀ s : GL (Fin n) (nbrPSU_F g), s ∈ S ↔
      Unitary.conjTr (nbrPSU_sigmae g) (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) *
          Unitary.antidiag n * (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) = Unitary.antidiag n ∧
        ∃ d ∈ D, IsGLLift ((Unitary.SU (nbrPSU_sigmae g) n).subtype) ψ s d)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hJ'map : J'.map ψ = J)
    (hJ'block : IsComponentOf J'
      ⁅glBlockCentralizer ((Unitary.SU (nbrPSU_sigmae g) n).subtype) S ε_J,
        glBlockCentralizer ((Unitary.SU (nbrPSU_sigmae g) n).subtype) S ε_J⁆)
    (heJ : IsPrimIdemIn (Algebra.adjoin (nbrPSU_F g) (Units.val '' S)) e_J)
    (hdegJ : blockDegree (Algebra.adjoin (nbrPSU_F g) (Units.val '' S)) e_J < 2)
    (hself : e_J = ε_J ∧ formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e_J = e_J) :
    ∃ (R Rm : Subgroup X),
      R ≤ J ∧ Rm ≤ J ∧
      (∃ (β : Fin (ggU .PSU n (g + 1)).D.rank → ℤ),
        β ∈ (ggU .PSU n (g + 1)).D.roots ∧ GGLongRoot (ggU .PSU n (g + 1)).D β ∧
        ∃ u : (ggU .PSU n (g + 1)).K,
          R = ggRootSub (ggU .PSU n (g + 1)).D ψ β u ∧
          Rm = ggRootSub (ggU .PSU n (g + 1)).D ψ (-β) u) ∧
      (∃ (mJ : ℕ) (βJ : Fin (ggU .PSU mJ (g + 1)).D.rank → ℤ),
        mJ < n ∧ mJ = Module.finrank (nbrPSU_F g) (LinearMap.range (Matrix.toLin' e_J)) ∧
        βJ ∈ (ggU .PSU mJ (g + 1)).D.roots ∧ GGLongRoot (ggU .PSU mJ (g + 1)).D βJ ∧
        GGRootVia (ggU .PSU mJ (g + 1)) J R βJ) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩ := hH
  have hc : Nat.card (nbrPSU_F g) = (2 ^ (g + 1)) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul 2 (g + 1) (by omega)
  have hadm : CFSG.Open.StatedLieAdmissible .PSU n 2 (g + 1) := h3.admissible
  have hn : 3 ≤ n := hadm.2.2.1
  have hdiag : ∀ b ∈ B₁, GGPsiInnerDiag (Unitary.rootDatum hc n) ψ b := fun b hb => h8 b hb
  have hJ'e : IsComponentOf J'
      ⁅glBlockCentralizer ((Unitary.SU (nbrPSU_sigmae g) n).subtype) S e_J,
        glBlockCentralizer ((Unitary.SU (nbrPSU_sigmae g) n).subtype) S e_J⁆ := by
    rw [hself.1]
    exact hJ'block
  obtain ⟨r, ι, β₀, hr, hβ₀long, hιcent, hιrange, v, w, hv, hw, hvw, hroot1, hroot2⟩ :=
    exists_blockModel_selfDual_PSU_explicit n g S hS heJ hself.2 hdegJ hJ'e
  obtain ⟨β, hβroot, hβlong, u, hu1, hu2⟩ :=
    exists_conj_rootGroup_eq_unitTransvGroup_PSU hc n (by omega) v w hv hw hvw
  have hRX : (((ggU .PSU r (g + 1)).D.rootGroup β₀).map ι) =
      (((Unitary.rootDatum hc n).rootGroup β).map (MulAut.conj u).toMonoidHom) :=
    Subgroup.map_injective (Subgroup.subtype_injective _) (hroot1.trans hu1.symm)
  have hRXneg : (((ggU .PSU r (g + 1)).D.rootGroup (-β₀)).map ι) =
      (((Unitary.rootDatum hc n).rootGroup (-β)).map (MulAut.conj u).toMonoidHom) :=
    Subgroup.map_injective (Subgroup.subtype_injective _) (hroot2.trans hu2.symm)
  have hRle : ggRootSub (ggU .PSU n (g + 1)).D ψ β u ≤ J := by
    rw [← hJ'map, ← hιrange]
    unfold ggRootSub
    exact (Subgroup.map_mono (le_of_eq hRX.symm)).trans
      (Subgroup.map_mono (Subgroup.map_le_range ι _))
  have hRmle : ggRootSub (ggU .PSU n (g + 1)).D ψ (-β) u ≤ J := by
    rw [← hJ'map, ← hιrange]
    unfold ggRootSub
    exact (Subgroup.map_mono (le_of_eq hRXneg.symm)).trans
      (Subgroup.map_mono (Subgroup.map_le_range ι _))
  have hviaJ : GGRootVia (ggU .PSU r (g + 1)) J
      (ggRootSub (ggU .PSU n (g + 1)).D ψ β u) β₀ := by
    have hconj : ∀ H : Subgroup (ggU .PSU r (g + 1)).K,
        H.map (MulAut.conj (1 : (ggU .PSU r (g + 1)).K)).toMonoidHom = H := by
      intro H
      ext y
      simp
    have hRvia : ggRootSub (ggU .PSU n (g + 1)).D ψ β u =
        ggRootSub (ggU .PSU r (g + 1)).D (ψ.comp ι) β₀ 1 := by
      unfold ggRootSub
      rw [hconj, ← Subgroup.map_map]
      exact congrArg (Subgroup.map ψ) hRX.symm
    refine ⟨ψ.comp ι, ?_, ?_, 1, hRvia⟩
    · rw [MonoidHom.range_comp, hιrange, hJ'map]
    · intro y hy
      have hy1 : ψ (ι y) = 1 := by
        have := MonoidHom.mem_ker.mp hy
        simpa [MonoidHom.comp_apply] using this
      exact hιcent y (h2 (MonoidHom.mem_ker.mpr hy1))
  have hmJn : r < n := by
    by_contra hnot
    have hle : Module.finrank (nbrPSU_F g) (LinearMap.range (Matrix.toLin' e_J)) ≤ n := by
      calc Module.finrank (nbrPSU_F g) (LinearMap.range (Matrix.toLin' e_J))
          ≤ Module.finrank (nbrPSU_F g) (Fin n → nbrPSU_F g) := Submodule.finrank_le _
        _ = n := by simp
    have hrle : r ≤ n := by rw [hr]; exact hle
    have heq : r = n := le_antisymm hrle (by omega)
    have htop : LinearMap.range (Matrix.toLin' e_J) = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [show Module.finrank (nbrPSU_F g) (LinearMap.range (Matrix.toLin' e_J)) = n by
        rw [← hr, heq]]
      simp
    have he1 : e_J = 1 := nbrPSUx_eq_one_of_range_top heJ.2.1 htop
    have hDcent : D ≤ Subgroup.centralizer (G₀ : Set X) := by
      intro d hd
      have hdB : d ∈ B₁ := h11 hd
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hlG : l ∈ ψ.range := h1.symm ▸ hl
      obtain ⟨w', rfl⟩ := hlG
      have hdN : d ∈ Subgroup.normalizer (ψ.range : Set X) := h1.symm ▸ h7 hdB
      obtain ⟨s, hsP, hsl⟩ := exists_isGLLift_PSU hc n hn ψ h2 hdN (hdiag d hdB)
      have hsS : s ∈ S := (hSdef s).mpr ⟨hsP, d, hd, hsl⟩
      have hdeg1 : blockDegree (Algebra.adjoin (nbrPSU_F g) (Units.val '' S)) e_J = 1 :=
        nbrPSUx_blockDegree_eq_one heJ hdegJ
      obtain ⟨c, hsc⟩ := nbrPSUx_block_scalar heJ hdeg1
        (Algebra.subset_adjoin ⟨s, hsS, rfl⟩)
      rw [he1, Matrix.mul_one] at hsc
      have hcomm := nbrPSUx_scalar_lift_commute n g ψ hsl ⟨c, hsc⟩ w'
      calc ψ w' * d = d * (d⁻¹ * ψ w' * d) := by group
        _ = d * ψ w' := by rw [hcomm]
    exact h22 (le_trans hDcent (Subgroup.centralizer_le h19))
  exact ⟨ggRootSub (ggU .PSU n (g + 1)).D ψ β u, ggRootSub (ggU .PSU n (g + 1)).D ψ (-β) u,
    hRle, hRmle, ⟨β, hβroot, hβlong, u, rfl, rfl⟩,
    ⟨r, β₀, hmJn, hr, nbrPSUx_GGLongRoot_mem_roots hβ₀long, hβ₀long, hviaJ⟩⟩

private lemma nbrPSUx_rank_map {n : ℕ} {F : Type} [Field F] [Finite F]
    (σ : F →+* F) (hσ : ∀ x, σ (σ x) = x) (A : Matrix (Fin n) (Fin n) F) :
    (A.map σ).rank = A.rank := by
  let τ : (Fin n → F) → (Fin n → F) := fun v => σ ∘ v
  have hτ_inj : Function.Injective τ := by
    intro u v huv
    funext i
    have h := congrFun huv i
    simp only [τ, Function.comp_apply] at h
    have h2 := congrArg σ h
    rwa [hσ (u i), hσ (v i)] at h2
  have hτ_surj : Function.Surjective τ := by
    intro u
    refine ⟨τ u, ?_⟩
    funext i
    simp only [τ, Function.comp_apply]
    exact hσ (u i)
  have hcomm : ∀ v, Matrix.toLin' (A.map σ) (τ v) = τ (Matrix.toLin' A v) := by
    intro v
    ext i
    simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Matrix.map_apply, τ,
      Function.comp_apply]
    rw [map_sum]
    exact Finset.sum_congr rfl (fun j _ => by rw [map_mul])
  have hrange : LinearMap.range (Matrix.toLin' (A.map σ)) =
      τ '' (LinearMap.range (Matrix.toLin' A)) := by
    ext w
    constructor
    · rintro ⟨u, rfl⟩
      obtain ⟨v, hv⟩ := hτ_surj u
      exact ⟨Matrix.toLin' A v, ⟨v, rfl⟩, by rw [← hv, hcomm v]⟩
    · rintro ⟨y, ⟨v, rfl⟩, rfl⟩
      exact ⟨τ v, hcomm v⟩
  have hcard : Nat.card (LinearMap.range (Matrix.toLin' (A.map σ))) =
      Nat.card (LinearMap.range (Matrix.toLin' A)) := by
    have h := Nat.card_image_of_injective hτ_inj (LinearMap.range (Matrix.toLin' A))
    rwa [← hrange] at h
  have h1 := Module.natCard_eq_pow_finrank (K := F)
    (V := LinearMap.range (Matrix.toLin' (A.map σ)))
  have h2 := Module.natCard_eq_pow_finrank (K := F)
    (V := LinearMap.range (Matrix.toLin' A))
  have hpow : (Nat.card F) ^ Module.finrank F (LinearMap.range (Matrix.toLin' (A.map σ))) =
      (Nat.card F) ^ Module.finrank F (LinearMap.range (Matrix.toLin' A)) := by
    rw [← h1, ← h2]
    exact hcard
  have hF2 : 2 ≤ Nat.card F := by
    haveI : Fintype F := Fintype.ofFinite F
    have h : 1 < Nat.card F := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card
    omega
  exact Nat.pow_right_injective hF2 hpow

private lemma nbrPSUx_finrank_range_formAdj {n : ℕ} {F : Type} [Field F] [Finite F]
    (σ : F →+* F) (hσ : ∀ x, σ (σ x) = x) {G : Matrix (Fin n) (Fin n) F} (hG : IsUnit G.det) (A : Matrix (Fin n) (Fin n) F) :
    Module.finrank F (LinearMap.range (Matrix.toLin' (formAdj σ G A))) =
      Module.finrank F (LinearMap.range (Matrix.toLin' A)) := by
  have hbridge : ∀ B : Matrix (Fin n) (Fin n) F,
      Module.finrank F (LinearMap.range (Matrix.toLin' B)) = B.rank := by
    intro B
    rw [Matrix.rank_eq_finrank_range_toLin B (Pi.basisFun F (Fin n)) (Pi.basisFun F (Fin n)),
      Matrix.toLin_eq_toLin']
  rw [hbridge (formAdj σ G A), hbridge A]
  have hGinv_mul : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G hG
  have hdet : (G⁻¹).det * G.det = 1 := by
    rw [← Matrix.det_mul, hGinv_mul, Matrix.det_one]
  have hGinv_det : IsUnit (G⁻¹).det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    rw [h0, zero_mul] at hdet
    exact one_ne_zero hdet.symm
  rw [show formAdj σ G A = G⁻¹ * Matrix.transpose (A.map σ) * G from rfl]
  calc (G⁻¹ * Matrix.transpose (A.map σ) * G).rank
      = (G⁻¹ * Matrix.transpose (A.map σ)).rank :=
          Matrix.rank_mul_eq_left_of_isUnit_det G _ hG
    _ = (Matrix.transpose (A.map σ)).rank :=
          Matrix.rank_mul_eq_right_of_isUnit_det G⁻¹ _ hGinv_det
    _ = (A.map σ).rank := Matrix.rank_transpose _
    _ = A.rank := nbrPSUx_rank_map σ hσ A

private lemma nbrPSUx_J_dual
    {X : Type} [Group X] [Finite X] (n g : ℕ)
    (ψ : ↥(Unitary.SU (nbrPSU_sigmae g) n) →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X)
    (hH : GGSixPosHyp .PSU n (g + 1) ψ p G₀ B₁ D J L x)
    (S : Set (GL (Fin n) (nbrPSU_F g))) (J' : Subgroup ↥(Unitary.SU (nbrPSU_sigmae g) n))
    (ε_J e_J : Matrix (Fin n) (Fin n) (nbrPSU_F g))
    (hSdef : ∀ s : GL (Fin n) (nbrPSU_F g), s ∈ S ↔
      Unitary.conjTr (nbrPSU_sigmae g) (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) *
          Unitary.antidiag n * (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) = Unitary.antidiag n ∧
        ∃ d ∈ D, IsGLLift ((Unitary.SU (nbrPSU_sigmae g) n).subtype) ψ s d)
    (hSU : ∀ s ∈ S, Unitary.conjTr (nbrPSU_sigmae g)
        (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) * Unitary.antidiag n *
        (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) = Unitary.antidiag n)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hJ'map : J'.map ψ = J)
    (hεJ : IsPrimAdjIdemIn (nbrPSU_sigma g) (Unitary.antidiag n)
      (Algebra.adjoin (nbrPSU_F g) (Units.val '' S)) ε_J)
    (hJ'block : IsComponentOf J'
      ⁅glBlockCentralizer ((Unitary.SU (nbrPSU_sigmae g) n).subtype) S ε_J,
        glBlockCentralizer ((Unitary.SU (nbrPSU_sigmae g) n).subtype) S ε_J⁆)
    (heJ : IsPrimIdemIn (Algebra.adjoin (nbrPSU_F g) (Units.val '' S)) e_J)
    (heJε : e_J * ε_J = e_J)
    (hdegJ : blockDegree (Algebra.adjoin (nbrPSU_F g) (Units.val '' S)) e_J < 2)
    (hpowS : ∀ s ∈ S, ∃ c : nbrPSU_F g,
        (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) ^ p = Matrix.scalar (Fin n) c)
    (hdual : e_J ≠ ε_J ∧ formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e_J ≠ e_J ∧
      ε_J = e_J + formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e_J) :
    ∃ (R Rm : Subgroup X),
      R ≤ J ∧ Rm ≤ J ∧
      (∃ (kJ : ℕ) (φJ : (ggU .PSL (kJ + 1) (2 * (g + 1))).K →* X)
          (βJ : Fin (ggU .PSL (kJ + 1) (2 * (g + 1))).D.rank → ℤ),
        2 * (kJ + 1) ≤ n ∧
        kJ + 1 = Module.finrank (nbrPSU_F g) (LinearMap.range (Matrix.toLin' e_J)) ∧
        βJ ∈ (ggU .PSL (kJ + 1) (2 * (g + 1))).D.roots ∧
        φJ.range = J ∧ φJ.ker ≤ Subgroup.center (ggU .PSL (kJ + 1) (2 * (g + 1))).K ∧
        (∃ u : (ggU .PSL (kJ + 1) (2 * (g + 1))).K,
          R = ggRootSub (ggU .PSL (kJ + 1) (2 * (g + 1))).D φJ βJ u) ∧
        (∀ b ∈ B₁, ∃ s : GL (Fin (kJ + 1)) (GaloisField 2 (2 * (g + 1))),
          IsGLLift Matrix.SpecialLinearGroup.toGL φJ s b) ∧
        p ∣ 2 ^ (g + 1) - 1) ∧
      (∃ (β : Fin (ggU .PSU n (g + 1)).D.rank → ℤ),
        β ∈ (ggU .PSU n (g + 1)).D.roots ∧ 2 • β ∉ (ggU .PSU n (g + 1)).D.roots ∧
        ∃ u : (ggU .PSU n (g + 1)).K,
          R = ggRootSub (ggU .PSU n (g + 1)).D ψ β u ∧
          Rm = ggRootSub (ggU .PSU n (g + 1)).D ψ (-β) u) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩ := hH
  have hc : Nat.card (nbrPSU_F g) = (2 ^ (g + 1)) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul 2 (g + 1) (by omega)
  have hadm : CFSG.Open.StatedLieAdmissible .PSU n 2 (g + 1) := h3.admissible
  have hn : 3 ≤ n := hadm.2.2.1
  have hG : IsUnit (Unitary.antidiag n : Matrix (Fin n) (Fin n) (nbrPSU_F g)).det :=
    isUnit_iff_ne_zero.mpr (Unitary.det_antidiag_ne_zero n)
  have hSU' : ∀ s ∈ S, Matrix.transpose
      (((s : GL (Fin n) (nbrPSU_F g)) : Matrix (Fin n) (Fin n) (nbrPSU_F g)).map
        (nbrPSU_sigma g)) * Unitary.antidiag n *
      ((s : GL (Fin n) (nbrPSU_F g)) : Matrix (Fin n) (Fin n) (nbrPSU_F g)) = Unitary.antidiag n :=
    fun s hs => by simpa [Unitary.conjTr] using hSU s hs
  have hdiag : ∀ b ∈ B₁, GGPsiInnerDiag (Unitary.rootDatum hc n) ψ b := fun b hb => h8 b hb
  have hB₁N : B₁ ≤ Subgroup.normalizer (ψ.range : Set X) := by
    have hψrange : (ψ.range : Set X) = (G₀ : Set X) :=
      congrArg (fun H : Subgroup X => (H : Set X)) h1
    rw [hψrange]
    exact h7
  have hpq : p ∣ 2 ^ (g + 1) - 1 :=
    dvd_two_pow_sub_one_of_dualPair_PSU hc n S hSU hS heJ hdegJ hdual.2.1 h5 hpowS
  have hJ'e : IsComponentOf J'
      ⁅glBlockCentralizer ((Unitary.SU (nbrPSU_sigmae g) n).subtype) S
          (e_J + formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e_J),
        glBlockCentralizer ((Unitary.SU (nbrPSU_sigmae g) n).subtype) S
          (e_J + formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e_J)⁆ := by
    rw [← hdual.2.2]
    exact hJ'block
  obtain ⟨k, ι, β₀, hrk, hequiv, hβ₀long, hιcent, hιrange, h4n, v₁, w₁, v₂, w₂, h₁, h₂, h₀,
    hroot1, hroot2⟩ :=
    exists_blockModel_dualPair_PSU_explicitModel n g S hSU hS heJ hdual.2.1 hdegJ hJ'e
  obtain ⟨β, hβroot, h2β, u, hu1, hu2⟩ :=
    exists_conj_rootGroup_eq_unitPairGroup_PSU hc n h4n v₁ w₁ v₂ w₂ h₁ h₂ h₀
  have hRX : (((ggU .PSL (k + 1) (2 * (g + 1))).D.rootGroup β₀).map ι) =
      (((Unitary.rootDatum hc n).rootGroup β).map (MulAut.conj u).toMonoidHom) :=
    Subgroup.map_injective (Subgroup.subtype_injective _) (hroot1.trans hu1.symm)
  have hRXneg : (((ggU .PSL (k + 1) (2 * (g + 1))).D.rootGroup (-β₀)).map ι) =
      (((Unitary.rootDatum hc n).rootGroup (-β)).map (MulAut.conj u).toMonoidHom) :=
    Subgroup.map_injective (Subgroup.subtype_injective _) (hroot2.trans hu2.symm)
  have hRle : ggRootSub (ggU .PSU n (g + 1)).D ψ β u ≤ J := by
    rw [← hJ'map, ← hιrange]
    unfold ggRootSub
    exact (Subgroup.map_mono (le_of_eq hRX.symm)).trans
      (Subgroup.map_mono (Subgroup.map_le_range ι _))
  have hRmle : ggRootSub (ggU .PSU n (g + 1)).D ψ (-β) u ≤ J := by
    rw [← hJ'map, ← hιrange]
    unfold ggRootSub
    exact (Subgroup.map_mono (le_of_eq hRXneg.symm)).trans
      (Subgroup.map_mono (Subgroup.map_le_range ι _))
  have h2k : 2 * (k + 1) ≤ n := by
    rw [hrk]
    have hest : IsIdempotentElem (formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e_J) := by
      rw [IsIdempotentElem, ← Geo.formAdj_mul (nbrPSU_sigma g) hG e_J e_J, heJ.2.1.eq]
    have horth : e_J * formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e_J = 0 := by
      have h := heJε
      rw [hdual.2.2, mul_add, heJ.2.1.eq] at h
      exact add_left_cancel (by rw [h, add_zero])
    have horth' : formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e_J * e_J = 0 := by
      have hmem : formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e_J ∈
          Algebra.adjoin (nbrPSU_F g) (Units.val '' S) :=
        Geo.formAdj_mem_adjoin (nbrPSU_sigma g) hG hSU' heJ.1
      rw [nbrPSU_adjoin_commute hS hmem heJ.1, horth]
    have hrk_eq : Module.finrank (nbrPSU_F g)
        (LinearMap.range (Matrix.toLin' (formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e_J))) =
        Module.finrank (nbrPSU_F g) (LinearMap.range (Matrix.toLin' e_J)) :=
      nbrPSUx_finrank_range_formAdj (nbrPSU_sigma g) (nbrPSU_sigma_involutive g) hG e_J
    have hsum : (e_J + formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e_J) * ε_J =
        e_J + formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e_J := by
      rw [← hdual.2.2]
      exact hεJ.2.1.eq
    have hineq := nbrPSUx_dual_nbr heJ.2.1 hest horth horth' hrk_eq hsum
    have hle : Module.finrank (nbrPSU_F g) (LinearMap.range (Matrix.toLin' ε_J)) ≤ n := by
      calc Module.finrank (nbrPSU_F g) (LinearMap.range (Matrix.toLin' ε_J))
          ≤ Module.finrank (nbrPSU_F g) (Fin n → nbrPSU_F g) := Submodule.finrank_le _
        _ = n := by simp
    exact le_trans hineq hle
  have hconj : ∀ H : Subgroup (ggU .PSL (k + 1) (2 * (g + 1))).K,
      H.map (MulAut.conj (1 : (ggU .PSL (k + 1) (2 * (g + 1))).K)).toMonoidHom = H := by
    intro H
    ext y
    simp
  have hRvia : ggRootSub (ggU .PSU n (g + 1)).D ψ β u =
      ggRootSub (ggU .PSL (k + 1) (2 * (g + 1))).D (ψ.comp ι) β₀ 1 := by
    unfold ggRootSub
    rw [hconj, ← Subgroup.map_map]
    exact congrArg (Subgroup.map ψ) hRX.symm
  have hrange : (ψ.comp ι).range = J := by
    rw [MonoidHom.range_comp, hιrange, hJ'map]
  have hker : (ψ.comp ι).ker ≤ Subgroup.center (ggU .PSL (k + 1) (2 * (g + 1))).K := by
    intro y hy
    have hy1 : ψ (ι y) = 1 := by
      have := MonoidHom.mem_ker.mp hy
      simpa [MonoidHom.comp_apply] using this
    exact hιcent y (h2 (MonoidHom.mem_ker.mpr hy1))
  have hB₁lift : ∀ b ∈ B₁, ∃ s : GL (Fin (k + 1)) (GaloisField 2 (2 * (g + 1))),
      IsGLLift Matrix.SpecialLinearGroup.toGL (ψ.comp ι) s b := by
    intro b hb
    obtain ⟨γ, hγU, hγlift⟩ :=
      exists_isGLLift_PSU hc n hn ψ h2 (hB₁N hb) (hdiag b hb)
    have hbD : ∀ d ∈ D, b * d = d * b := by
      intro d hd
      have h := h9.1.is_comm.comm (⟨b, hb⟩ : ↥B₁) (⟨d, h11 hd⟩ : ↥B₁)
      show ((⟨b, hb⟩ : ↥B₁) : X) * ((⟨d, h11 hd⟩ : ↥B₁) : X) =
        ((⟨d, h11 hd⟩ : ↥B₁) : X) * ((⟨b, hb⟩ : ↥B₁) : X)
      rw [← Subgroup.coe_mul, ← Subgroup.coe_mul]
      exact congrArg Subtype.val h
    have hγe : γ * e_J = e_J * γ := by
      have hslift : ∀ s ∈ S, ∃ d ∈ D,
          IsGLLift ((Unitary.SU (nbrPSU_sigmae g) n).subtype) ψ s d :=
        fun s hs => ((hSdef s).mp hs).2
      exact commute_adjoin_of_isGLLift_PSU hc n ψ h2 S hSU h5 hpq hpowS D hslift hbD hγU hγlift
        e_J heJ.1
    obtain ⟨a, ha⟩ := hequiv γ hγU hγe
    refine ⟨a, ?_⟩
    intro x
    obtain ⟨x', hx'j, hx'γ⟩ := ha x
    obtain ⟨u', hu'j, hu'ψ⟩ := hγlift (ι x)
    refine ⟨x', hx'j, ?_⟩
    have hu'eq : u' = ι x' := by
      apply Subgroup.subtype_injective (Unitary.SU (nbrPSU_sigmae g) n)
      have h1 : γ * (Unitary.SU (nbrPSU_sigmae g) n).subtype (ι x) =
          (Unitary.SU (nbrPSU_sigmae g) n).subtype (ι x') * γ := hx'γ
      calc (Unitary.SU (nbrPSU_sigmae g) n).subtype u' =
            γ * (Unitary.SU (nbrPSU_sigmae g) n).subtype (ι x) * γ⁻¹ := hu'j
        _ = ((Unitary.SU (nbrPSU_sigmae g) n).subtype (ι x') * γ) * γ⁻¹ := by rw [h1]
        _ = (Unitary.SU (nbrPSU_sigmae g) n).subtype (ι x') := by group
    show b⁻¹ * ψ (ι x) * b = ψ (ι x')
    rw [← hu'eq]
    exact hu'ψ
  exact ⟨ggRootSub (ggU .PSU n (g + 1)).D ψ β u, ggRootSub (ggU .PSU n (g + 1)).D ψ (-β) u,
    hRle, hRmle,
    ⟨k, ψ.comp ι, β₀, h2k, hrk, nbrPSUx_GGLongRoot_mem_roots hβ₀long, hrange, hker, ⟨1, hRvia⟩,
      hB₁lift, hpq⟩,
    ⟨β, hβroot, h2β, u, rfl, rfl⟩⟩

private lemma nbrPSUx_glBlockCentralizer_le {n g : ℕ}
    {S S_e : Set (GL (Fin n) (nbrPSU_F g))} (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin n) (Fin n) (nbrPSU_F g)}
    (he : IsPrimIdemIn (Algebra.adjoin (nbrPSU_F g) (Units.val '' S)) e)
    (hdeg : blockDegree (Algebra.adjoin (nbrPSU_F g) (Units.val '' S)) e < 2)
    (heSe : e ∈ Algebra.adjoin (nbrPSU_F g) (Units.val '' S_e)) :
    glBlockCentralizer ((Unitary.SU (nbrPSU_sigmae g) n).subtype) S_e e ≤
      glBlockCentralizer ((Unitary.SU (nbrPSU_sigmae g) n).subtype) S e := by
  intro u hu
  obtain ⟨huc, hufix⟩ : (Unitary.SU (nbrPSU_sigmae g) n).subtype u ∈
      Subgroup.centralizer S_e ⊓ glFixing (1 - e) := Subgroup.mem_comap.mp hu
  have hfix : (((Unitary.SU (nbrPSU_sigmae g) n).subtype u : GL (Fin n) (nbrPSU_F g)) :
      Matrix (Fin n) (Fin n) (nbrPSU_F g)) * (1 - e) = 1 - e := hufix
  have hcomm_e : (((Unitary.SU (nbrPSU_sigmae g) n).subtype u : GL (Fin n) (nbrPSU_F g)) :
      Matrix (Fin n) (Fin n) (nbrPSU_F g)) * e =
      e * (((Unitary.SU (nbrPSU_sigmae g) n).subtype u : GL (Fin n) (nbrPSU_F g)) :
        Matrix (Fin n) (Fin n) (nbrPSU_F g)) :=
    nbrPSU_mem_adjoin_commute (S := S_e) huc heSe
  refine Subgroup.mem_comap.mpr ⟨Subgroup.mem_centralizer_iff.mpr ?_, hufix⟩
  intro s hs
  have hsA : (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) ∈
      Algebra.adjoin (nbrPSU_F g) (Units.val '' S) := Algebra.subset_adjoin ⟨s, hs, rfl⟩
  obtain ⟨c, hc⟩ := nbrPSUx_block_scalar he (nbrPSUx_blockDegree_eq_one he hdeg) hsA
  have hse : (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) * e =
      e * (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) := nbrPSU_adjoin_commute hS hsA he.1
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  set G' := (((Unitary.SU (nbrPSU_sigmae g) n).subtype u : GL (Fin n) (nbrPSU_F g)) :
      Matrix (Fin n) (Fin n) (nbrPSU_F g)) with hGdef
  set Sm := (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) with hSmdef
  have hG : G' = G' * e + (1 - e) := by
    have h := hfix
    rw [Matrix.mul_sub, Matrix.mul_one] at h
    calc G' = (G' - G' * e) + G' * e := by abel
      _ = (1 - e) + G' * e := by rw [h]
      _ = G' * e + (1 - e) := by abel
  have hSG : Sm * G' = c • (G' * e) + (Sm - c • e) := by
    calc Sm * G' = Sm * (G' * e + (1 - e)) := by rw [← hG]
      _ = Sm * (G' * e) + (Sm - Sm * e) := by
        rw [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one]
      _ = c • (G' * e) + (Sm - c • e) := by
        rw [hc, hcomm_e, ← Matrix.mul_assoc, hc, Matrix.smul_mul]
  have hGS : G' * Sm = c • (G' * e) + (Sm - c • e) := by
    calc G' * Sm = (G' * e + (1 - e)) * Sm := by rw [← hG]
      _ = G' * (e * Sm) + (Sm - e * Sm) := by
        rw [Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
      _ = c • (G' * e) + (Sm - c • e) := by rw [← hse, hc, Matrix.mul_smul]
  rw [hSG, hGS]

private lemma nbrPSUx_component_eq_of_le {G : Type} [Group G]
    {H A B : Subgroup G} (hA : IsComponentOf A H) (hB : IsComponentOf B H) (hAB : A ≤ B) :
    A = B := by
  have hsub : IsSubnormal A B := by
    have h := hA.2.1.inf_of_le hB.1
    rwa [inf_eq_left.2 hAB] at h
  rcases CFSG.Fischer.Classification.Recognition.IsSubnormal.eq_or_le_center
      (CFSG.Assembly.isSubnormal_iff_open.mp hsub) hB.2.2 with h | h
  · exact h
  · exfalso
    refine CFSG.Fischer.Classification.Recognition.IsQuasisimple.not_le_of_comm hA.2.2
      (A := (Subgroup.center B).map B.subtype) ?_ h
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact (congrArg B.subtype (Subgroup.mem_center_iff.mp ha b)).symm

private lemma nbrPSUx_K_self
    {X : Type} [Group X] [Finite X] (n g : ℕ)
    (ψ : ↥(Unitary.SU (nbrPSU_sigmae g) n) →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X)
    (hH : GGSixPosHyp .PSU n (g + 1) ψ p G₀ B₁ D J L x)
    (S : Set (GL (Fin n) (nbrPSU_F g))) (J' : Subgroup ↥(Unitary.SU (nbrPSU_sigmae g) n))
    (ε_J e_J : Matrix (Fin n) (Fin n) (nbrPSU_F g))
    (hSdef : ∀ s : GL (Fin n) (nbrPSU_F g), s ∈ S ↔
      Unitary.conjTr (nbrPSU_sigmae g) (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) *
          Unitary.antidiag n * (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) = Unitary.antidiag n ∧
        ∃ d ∈ D, IsGLLift ((Unitary.SU (nbrPSU_sigmae g) n).subtype) ψ s d)
    (hSU : ∀ s ∈ S, Unitary.conjTr (nbrPSU_sigmae g)
        (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) * Unitary.antidiag n *
        (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) = Unitary.antidiag n)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s))
    (hJ'comp : IsComponentOf J' ((Subgroup.centralizer S).comap
        ((Unitary.SU (nbrPSU_sigmae g) n).subtype)))
    (hJ'map : J'.map ψ = J)
    (hεJ : IsPrimAdjIdemIn (nbrPSU_sigma g) (Unitary.antidiag n)
      (Algebra.adjoin (nbrPSU_F g) (Units.val '' S)) ε_J)
    (hJ'block : IsComponentOf J'
      ⁅glBlockCentralizer ((Unitary.SU (nbrPSU_sigmae g) n).subtype) S ε_J,
        glBlockCentralizer ((Unitary.SU (nbrPSU_sigmae g) n).subtype) S ε_J⁆)
    (heJ : IsPrimIdemIn (Algebra.adjoin (nbrPSU_F g) (Units.val '' S)) e_J)
    (heJε : e_J * ε_J = e_J)
    (hdegJ : blockDegree (Algebra.adjoin (nbrPSU_F g) (Units.val '' S)) e_J < 2)
    (hself : e_J = ε_J ∧ formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e_J = e_J)
    (mJ : ℕ) (hmJ : mJ = Module.finrank (nbrPSU_F g)
      (LinearMap.range (Matrix.toLin' e_J)))
    (R Rm : Subgroup X) (hR : R ≤ J)
    (hR0L : ∃ (β : Fin (ggU .PSU n (g + 1)).D.rank → ℤ),
      β ∈ (ggU .PSU n (g + 1)).D.roots ∧ GGLongRoot (ggU .PSU n (g + 1)).D β ∧
      ∃ u : (ggU .PSU n (g + 1)).K,
        R = ggRootSub (ggU .PSU n (g + 1)).D ψ β u ∧
        Rm = ggRootSub (ggU .PSU n (g + 1)).D ψ (-β) u)
    (e : X) (he : e ∈ D) (K : Subgroup X)
    (hKcomp : IsComponentOf K (G₀ ⊓ Subgroup.centralizer ({e} : Set X))) (hJK : J ≤ K)
    (hKne : K ≠ J) :
    ∃ (mK : ℕ) (βK : Fin (ggU .PSU mK (g + 1)).D.rank → ℤ),
      mJ < mK ∧ βK ∈ (ggU .PSU mK (g + 1)).D.roots ∧
      GGLongRoot (ggU .PSU mK (g + 1)).D βK ∧
      GGRootVia (ggU .PSU mK (g + 1)) K R βK := by
  have hH' : GGSixPosHyp .PSU n (g + 1) ψ p G₀ B₁ D J L x := hH
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩ := hH'
  have hc : Nat.card (nbrPSU_F g) = (2 ^ (g + 1)) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul 2 (g + 1) (by omega)
  have hadm : CFSG.Open.StatedLieAdmissible .PSU n 2 (g + 1) := h3.admissible
  have hn : 3 ≤ n := hadm.2.2.1
  have hψker : ψ.ker ≤ Subgroup.center ↥(Unitary.SU (nbrPSU_sigmae g) n) := h2
  obtain ⟨s_e, K', hK'map, hK'comp, hodd_se, hiso, hs_e_lift⟩ :=
    nbrPSUx_neighbourLiftData n g ψ p G₀ B₁ D J L x hH e he K hKcomp
  have hs_eS : s_e ∈ S := (hSdef s_e).mpr ⟨hiso, e, he, hs_e_lift⟩
  have hJ'K' : J' ≤ K' :=
    nbrPSU_l8_le_of_map_le_of_quasisimple ψ hψker hJ'comp.2.2
      (by rw [hJ'map, hK'map]; exact hJK)
  obtain ⟨ε, e', hε, hK'ε, he', he'ε, hdeg, hsplit, heJ_ε, heJ_e'⟩ :=
    nbrPSUx_neighbourBlockData n g S J' ε_J e_J hS hodd hεJ hJ'block heJ heJε hdegJ K' hJ'K'
      s_e hs_eS hK'comp hodd_se hiso
  have hε_eq : e' = ε :=
    nbrPSUx_selfDual_nbr s_e hs_eS hSU hS heJ hself.2 hdegJ he' hdeg hsplit heJ_ε
  have hK'e' : IsComponentOf K'
      ⁅glBlockCentralizer ((Unitary.SU (nbrPSU_sigmae g) n).subtype)
          ({s_e} : Set (GL (Fin n) (nbrPSU_F g))) e',
        glBlockCentralizer ((Unitary.SU (nbrPSU_sigmae g) n).subtype)
          ({s_e} : Set (GL (Fin n) (nbrPSU_F g))) e'⁆ := by
    rw [hε_eq]
    exact hK'ε
  obtain ⟨β, hβroot, hβlong, u, hRsub, hRmsub⟩ := hR0L
  let R' : Subgroup ↥(Unitary.SU (nbrPSU_sigmae g) n) :=
    ((ggU .PSU n (g + 1)).D.rootGroup β).map (MulAut.conj u).toMonoidHom
  have hR'map : R'.map ψ = R := by
    rw [hRsub]
    rfl
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hroot : IsPGroup 2 ((ggU .PSU n (g + 1)).D.rootGroup β) :=
    CFSG.LieType.Steinberg.isPGroup_rootGroup
      (CFSG.LieType.BorelTits.unitaryInvolution_involutive hc)
      (Unitary.SUExtras.toStd_ne_zero_of_mem_roots hβroot)
  have hRp : IsPGroup 2 R' := hroot.map (MulAut.conj u).toMonoidHom
  have hodd_ker : Odd (Nat.card ↥ψ.ker) :=
    CFSG.StandardType.odd_natCard_of_le_center_SU (nbrPSU_sigmae g) hψker
  have hle_map : R'.map ψ ≤ K'.map ψ := by
    rw [hR'map, hK'map]
    exact le_trans hR hJK
  have hR'K' : R' ≤ K' :=
    CFSG.GroupTheory.le_of_map_le_map_of_odd (Φ := ψ) hψker hodd_ker hRp hle_map
  obtain ⟨v, hv, hviso, hEq⟩ := exists_unitTransvGroup_eq_rootGroup_PSU n g hβroot hβlong u
  have hle : unitTransvGroup (nbrPSU_sigma g) (Unitary.antidiag n) v ≤
      K'.map ((Unitary.SU (nbrPSU_sigmae g) n).subtype) := by
    rw [← hEq]
    exact Subgroup.map_mono hR'K'
  have hS_e : ∀ s ∈ ({s_e} : Set (GL (Fin n) (nbrPSU_F g))),
      ∀ s' ∈ ({s_e} : Set (GL (Fin n) (nbrPSU_F g))), Commute s s' := by
    intro s hs s' hs'
    rw [Set.mem_singleton_iff] at hs hs'
    rw [hs, hs']
  have hadj' : formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e' = e' := by
    rw [hε_eq]
    exact hε.2.2.2.1
  obtain ⟨r, ι, hr, hcenter, hιrange, hlong, -⟩ :=
    exists_blockModelClosure_selfDual_PSU_explicit n g ({s_e} : Set (GL (Fin n) (nbrPSU_F g)))
      hS_e he' hadj' hdeg hK'e'
  obtain ⟨βK, uK, hβKroot, hβKlong, hEqK⟩ := hlong v hv hviso hle
  have hR'eq : R' = (((ggU .PSU r (g + 1)).D.rootGroup βK).map
      (MulAut.conj uK).toMonoidHom).map ι :=
    Subgroup.map_injective (Subgroup.subtype_injective _) (hEq.trans hEqK.symm)
  have hRsubK : R = ggRootSub (ggU .PSU r (g + 1)).D (ψ.comp ι) βK uK := by
    rw [← hR'map, hR'eq]
    unfold ggRootSub
    rw [Subgroup.map_map]
  have hrange : (ψ.comp ι).range = K := by
    rw [MonoidHom.range_comp, hιrange, hK'map]
  have hker : (ψ.comp ι).ker ≤ Subgroup.center (ggU .PSU r (g + 1)).K := by
    intro y hy
    have hy1 : ψ (ι y) = 1 := by
      have := MonoidHom.mem_ker.mp hy
      simpa [MonoidHom.comp_apply] using this
    exact hcenter y (hψker (MonoidHom.mem_ker.mpr hy1))
  have hνε : e_J ≠ e' := by
    intro heq
    have hεeJ : ε = e_J := hε_eq.symm.trans heq.symm
    have hK'G : K' ≤ glBlockCentralizer ((Unitary.SU (nbrPSU_sigmae g) n).subtype)
        ({s_e} : Set (GL (Fin n) (nbrPSU_F g))) ε :=
      le_trans hK'ε.1 (Subgroup.commutator_le_self _)
    have hle_gl : glBlockCentralizer ((Unitary.SU (nbrPSU_sigmae g) n).subtype)
        ({s_e} : Set (GL (Fin n) (nbrPSU_F g))) ε ≤
        glBlockCentralizer ((Unitary.SU (nbrPSU_sigmae g) n).subtype) S e_J := by
      rw [hεeJ]
      exact nbrPSUx_glBlockCentralizer_le (S := S) (S_e := ({s_e} : Set _)) hS heJ hdegJ
        (by rw [heq]; exact he'.1)
    have hK'G_S : K' ≤ glBlockCentralizer ((Unitary.SU (nbrPSU_sigmae g) n).subtype) S e_J :=
      le_trans hK'G hle_gl
    have hK'H_S : K' ≤
        (Subgroup.centralizer S).comap ((Unitary.SU (nbrPSU_sigmae g) n).subtype) :=
      le_trans hK'G_S (Subgroup.comap_mono inf_le_left)
    have hH_Se : (Subgroup.centralizer S).comap ((Unitary.SU (nbrPSU_sigmae g) n).subtype) ≤
        (Subgroup.centralizer ({s_e} : Set (GL (Fin n) (nbrPSU_F g)))).comap
          ((Unitary.SU (nbrPSU_sigmae g) n).subtype) :=
      Subgroup.comap_mono (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hs_eS))
    have hK'comp_S : IsComponentOf K'
        ((Subgroup.centralizer S).comap ((Unitary.SU (nbrPSU_sigmae g) n).subtype)) :=
      IsComponentOf.of_le_of_le hK'comp hK'H_S hH_Se
    have hJ'eqK' : J' = K' := nbrPSUx_component_eq_of_le hJ'comp hK'comp_S hJ'K'
    exact hKne (by rw [← hK'map, ← hJ'map, hJ'eqK'])
  have hmJlt : mJ < r := by
    rw [hmJ, hr]
    have he'_mem : e' ∈ Algebra.adjoin (nbrPSU_F g) (Units.val '' S) :=
      Algebra.adjoin_mono (Set.image_mono (Set.singleton_subset_iff.mpr hs_eS)) he'.1
    have hba : e' * e_J = e_J :=
      (nbrPSU_adjoin_commute hS he'_mem heJ.1).trans heJ_e'
    exact nbrPSUx_rank_lt heJ.2.1 heJ_e' hba hνε
  exact ⟨r, βK, hmJlt, hβKroot, hβKlong, ⟨ψ.comp ι, hrange, hker, uK, hRsubK⟩⟩

private lemma nbrPSUx_dualPair_ne
    {X : Type} [Group X] (n g : ℕ)
    (ψ : ↥(Unitary.SU (nbrPSU_sigmae g) n) →* X)
    (S : Set (GL (Fin n) (nbrPSU_F g))) (s_e : GL (Fin n) (nbrPSU_F g)) (hs_eS : s_e ∈ S)
    (hSU : ∀ s ∈ S, Unitary.conjTr (nbrPSU_sigmae g)
        (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) * Unitary.antidiag n *
        (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) = Unitary.antidiag n)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (K' : Subgroup ↥(Unitary.SU (nbrPSU_sigmae g) n)) (K : Subgroup X)
    (hK'map : K'.map ψ = K)
    (J : Subgroup X) (J' : Subgroup ↥(Unitary.SU (nbrPSU_sigmae g) n))
    (hJ'map : J'.map ψ = J)
    (hJ'comp : IsComponentOf J' ((Subgroup.centralizer S).comap
        ((Unitary.SU (nbrPSU_sigmae g) n).subtype)))
    (hK'comp : IsComponentOf K' ((Subgroup.centralizer
        ({s_e} : Set (GL (Fin n) (nbrPSU_F g)))).comap
        ((Unitary.SU (nbrPSU_sigmae g) n).subtype)))
    (hJ'K' : J' ≤ K') (hKne : K ≠ J)
    (e_J ε e' : Matrix (Fin n) (Fin n) (nbrPSU_F g))
    (hK'ε : IsComponentOf K'
      ⁅glBlockCentralizer ((Unitary.SU (nbrPSU_sigmae g) n).subtype)
          ({s_e} : Set (GL (Fin n) (nbrPSU_F g))) ε,
        glBlockCentralizer ((Unitary.SU (nbrPSU_sigmae g) n).subtype)
          ({s_e} : Set (GL (Fin n) (nbrPSU_F g))) ε⁆)
    (heJ : IsPrimIdemIn (Algebra.adjoin (nbrPSU_F g) (Units.val '' S)) e_J)
    (hdegJ : blockDegree (Algebra.adjoin (nbrPSU_F g) (Units.val '' S)) e_J < 2)
    (hdual' : e' ≠ ε ∧ formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e' ≠ e' ∧
      ε = e' + formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e')
    (he' : IsPrimIdemIn (Algebra.adjoin (nbrPSU_F g)
      (Units.val '' ({s_e} : Set (GL (Fin n) (nbrPSU_F g))))) e') :
    e_J ≠ e' := by
  have hG : IsUnit (Unitary.antidiag n : Matrix (Fin n) (Fin n) (nbrPSU_F g)).det :=
    isUnit_iff_ne_zero.mpr (Unitary.det_antidiag_ne_zero n)
  intro heq
  have heJ' : IsPrimIdemIn (Algebra.adjoin (nbrPSU_F g) (Units.val '' S)) e' := by
    rw [← heq]; exact heJ
  have hdegJ' : blockDegree (Algebra.adjoin (nbrPSU_F g) (Units.val '' S)) e' < 2 := by
    rw [← heq]; exact hdegJ
  have hK'H : K' ≤ (Subgroup.centralizer S).comap ((Unitary.SU (nbrPSU_sigmae g) n).subtype) := by
    intro u hu
    have huG : (Unitary.SU (nbrPSU_sigmae g) n).subtype u ∈
        Subgroup.centralizer ({s_e} : Set (GL (Fin n) (nbrPSU_F g))) ⊓ glFixing (1 - ε) :=
      Subgroup.mem_comap.mp (le_trans hK'ε.1 (Subgroup.commutator_le_self _) hu)
    obtain ⟨hcent_e, hfix⟩ := huG
    refine Subgroup.mem_comap.mpr (Subgroup.mem_centralizer_iff.mpr ?_)
    intro s hs
    have hse : (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) ∈
        Algebra.adjoin (nbrPSU_F g) (Units.val '' S) := Algebra.subset_adjoin ⟨s, hs, rfl⟩
    obtain ⟨c_s, hc_s⟩ := nbrPSUx_block_scalar heJ' (nbrPSUx_blockDegree_eq_one heJ' hdegJ') hse
    have hsE : (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) * e' =
        e' * (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) :=
      nbrPSU_adjoin_commute (S := S) hS hse heJ'.1
    have hformAdj_mem_S : formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e' ∈
        Algebra.adjoin (nbrPSU_F g) (Units.val '' S) :=
      Geo.formAdj_mem_adjoin (nbrPSU_sigma g) hG
        (fun t ht => by simpa [Unitary.conjTr] using hSU t ht) heJ'.1
    have hsF : (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) *
        formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e' =
        formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e' *
        (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) :=
      nbrPSU_adjoin_commute (S := S) hS hse hformAdj_mem_S
    have hε_mem_S : ε ∈ Algebra.adjoin (nbrPSU_F g) (Units.val '' S) := by
      rw [hdual'.2.2]; exact add_mem heJ'.1 hformAdj_mem_S
    have hs_eps : (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) * ε =
        ε * (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) :=
      nbrPSU_adjoin_commute (S := S) hS hse hε_mem_S
    have hs1e : (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) * (1 - ε) =
        (1 - ε) * (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) := by
      rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul, hs_eps]
    have huE : (((Unitary.SU (nbrPSU_sigmae g) n).subtype u : GL (Fin n) (nbrPSU_F g)) :
        Matrix (Fin n) (Fin n) (nbrPSU_F g)) * e' =
        e' * (((Unitary.SU (nbrPSU_sigmae g) n).subtype u : GL (Fin n) (nbrPSU_F g)) :
          Matrix (Fin n) (Fin n) (nbrPSU_F g)) :=
      nbrPSU_mem_adjoin_commute (S := ({s_e} : Set (GL (Fin n) (nbrPSU_F g)))) hcent_e he'.1
    have hformAdj_mem_se : formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e' ∈
        Algebra.adjoin (nbrPSU_F g) (Units.val '' ({s_e} : Set (GL (Fin n) (nbrPSU_F g)))) :=
      Geo.formAdj_mem_adjoin (nbrPSU_sigma g) hG
        (fun t ht => by
          rw [Set.mem_singleton_iff] at ht
          rw [ht]
          simpa [Unitary.conjTr] using hSU s_e hs_eS) he'.1
    have huF : (((Unitary.SU (nbrPSU_sigmae g) n).subtype u : GL (Fin n) (nbrPSU_F g)) :
        Matrix (Fin n) (Fin n) (nbrPSU_F g)) * formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e' =
        formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e' *
        (((Unitary.SU (nbrPSU_sigmae g) n).subtype u : GL (Fin n) (nbrPSU_F g)) :
          Matrix (Fin n) (Fin n) (nbrPSU_F g)) :=
      nbrPSU_mem_adjoin_commute (S := ({s_e} : Set (GL (Fin n) (nbrPSU_F g)))) hcent_e
        hformAdj_mem_se
    have hisom : Matrix.transpose
        (((s : GL (Fin n) (nbrPSU_F g)) : Matrix (Fin n) (Fin n) (nbrPSU_F g)).map
          (nbrPSU_sigma g)) * Unitary.antidiag n *
        (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) = Unitary.antidiag n := by
      simpa [Unitary.conjTr] using hSU s hs
    have hss : (((s⁻¹ : GL (Fin n) (nbrPSU_F g)) : Matrix (Fin n) (Fin n) (nbrPSU_F g)) *
        (s : Matrix (Fin n) (Fin n) (nbrPSU_F g))) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hc_ne : c_s ≠ 0 := by
      intro h0
      have h1 : (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) * e' = 0 := by rw [hc_s, h0, zero_smul]
      have h2 := congrArg (fun M : Matrix (Fin n) (Fin n) (nbrPSU_F g) =>
        (((s⁻¹ : GL (Fin n) (nbrPSU_F g)) : Matrix (Fin n) (Fin n) (nbrPSU_F g))) * M) h1
      rw [Matrix.mul_zero, ← Matrix.mul_assoc, hss, Matrix.one_mul] at h2
      exact heJ'.2.2.1 h2
    have hσc : nbrPSU_sigma g c_s ≠ 0 := fun h =>
      hc_ne ((nbrPSU_sigma g).injective (by rw [h, map_zero]))
    have h2 : formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e' =
        (nbrPSU_sigma g c_s) • ((s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) *
          formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e') := by
      have h := congrArg (fun M : Matrix (Fin n) (Fin n) (nbrPSU_F g) =>
        M * (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)))
        (show formAdj (nbrPSU_sigma g) (Unitary.antidiag n)
            ((s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) * e') =
          formAdj (nbrPSU_sigma g) (Unitary.antidiag n) (c_s • e') from by rw [hc_s])
      rw [Geo.formAdj_mul (nbrPSU_sigma g) hG,
        Geo.formAdj_eq_inv_of_isometry (nbrPSU_sigma g) hG s hisom, Geo.formAdj_smul,
        Matrix.mul_assoc, hss, Matrix.mul_one, Matrix.smul_mul, ← hsF] at h
      exact h
    have hd_s : (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) *
        formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e' =
        (nbrPSU_sigma g c_s)⁻¹ • formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e' := by
      have h3 := congrArg (fun M : Matrix (Fin n) (Fin n) (nbrPSU_F g) =>
        (nbrPSU_sigma g c_s)⁻¹ • M) h2
      rw [smul_smul, inv_mul_cancel₀ hσc, one_smul] at h3
      exact h3.symm
    have hkill1 : ((((Unitary.SU (nbrPSU_sigmae g) n).subtype u : GL (Fin n) (nbrPSU_F g)) :
        Matrix (Fin n) (Fin n) (nbrPSU_F g)) * (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) -
        (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) *
        (((Unitary.SU (nbrPSU_sigmae g) n).subtype u : GL (Fin n) (nbrPSU_F g)) :
          Matrix (Fin n) (Fin n) (nbrPSU_F g))) * e' = 0 := by
      rw [Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_assoc, hc_s, Matrix.mul_smul, huE,
        ← Matrix.mul_assoc, hc_s, Matrix.smul_mul, sub_self]
    have hkill2 : ((((Unitary.SU (nbrPSU_sigmae g) n).subtype u : GL (Fin n) (nbrPSU_F g)) :
        Matrix (Fin n) (Fin n) (nbrPSU_F g)) * (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) -
        (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) *
        (((Unitary.SU (nbrPSU_sigmae g) n).subtype u : GL (Fin n) (nbrPSU_F g)) :
          Matrix (Fin n) (Fin n) (nbrPSU_F g))) *
        formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e' = 0 := by
      rw [Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_assoc, hd_s, Matrix.mul_smul, huF,
        ← Matrix.mul_assoc, hd_s, Matrix.smul_mul, sub_self]
    have hkill3 : ((((Unitary.SU (nbrPSU_sigmae g) n).subtype u : GL (Fin n) (nbrPSU_F g)) :
        Matrix (Fin n) (Fin n) (nbrPSU_F g)) * (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) -
        (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) *
        (((Unitary.SU (nbrPSU_sigmae g) n).subtype u : GL (Fin n) (nbrPSU_F g)) :
          Matrix (Fin n) (Fin n) (nbrPSU_F g))) * (1 - ε) = 0 := by
      rw [Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_assoc, hs1e, ← Matrix.mul_assoc, hfix,
        hs1e, sub_self]
    have hsum : e' + formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e' + (1 - ε) = 1 := by
      rw [hdual'.2.2]; abel
    have hzero : ((((Unitary.SU (nbrPSU_sigmae g) n).subtype u : GL (Fin n) (nbrPSU_F g)) :
        Matrix (Fin n) (Fin n) (nbrPSU_F g)) * (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) -
        (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) *
        (((Unitary.SU (nbrPSU_sigmae g) n).subtype u : GL (Fin n) (nbrPSU_F g)) :
          Matrix (Fin n) (Fin n) (nbrPSU_F g))) = 0 := by
      calc ((((Unitary.SU (nbrPSU_sigmae g) n).subtype u : GL (Fin n) (nbrPSU_F g)) :
          Matrix (Fin n) (Fin n) (nbrPSU_F g)) * (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) -
          (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) *
          (((Unitary.SU (nbrPSU_sigmae g) n).subtype u : GL (Fin n) (nbrPSU_F g)) :
            Matrix (Fin n) (Fin n) (nbrPSU_F g)))
          = _ * 1 := by rw [Matrix.mul_one]
        _ = _ * (e' + formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e' + (1 - ε)) := by
              rw [hsum]
        _ = _ * e' + _ * formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e' + _ * (1 - ε) := by
              rw [Matrix.mul_add, Matrix.mul_add]
        _ = 0 := by rw [hkill1, hkill2, hkill3]; abel
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    exact (sub_eq_zero.mp hzero).symm
  have hSe : (Subgroup.centralizer S).comap ((Unitary.SU (nbrPSU_sigmae g) n).subtype) ≤
      (Subgroup.centralizer ({s_e} : Set (GL (Fin n) (nbrPSU_F g)))).comap
        ((Unitary.SU (nbrPSU_sigmae g) n).subtype) :=
    Subgroup.comap_mono (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hs_eS))
  have hK'compS : IsComponentOf K'
      ((Subgroup.centralizer S).comap ((Unitary.SU (nbrPSU_sigmae g) n).subtype)) :=
    IsComponentOf.of_le_of_le hK'comp hK'H hSe
  have hJK' : J' = K' := nbrPSUx_component_eq_of_le hJ'comp hK'compS hJ'K'
  exact hKne (by rw [← hK'map, ← hJ'map, hJK'])

private lemma nbrPSUx_K_dual_self
    {X : Type} [Group X] (n g : ℕ)
    (ψ : ↥(Unitary.SU (nbrPSU_sigmae g) n) →* X)
    (S : Set (GL (Fin n) (nbrPSU_F g))) (s_e : GL (Fin n) (nbrPSU_F g)) (hs_eS : s_e ∈ S)
    (K' : Subgroup ↥(Unitary.SU (nbrPSU_sigmae g) n)) (K : Subgroup X)
    (hK'map : K'.map ψ = K)
    (J' : Subgroup ↥(Unitary.SU (nbrPSU_sigmae g) n)) (hJ'K' : J' ≤ K')
    (ε_J e_J ε e' : Matrix (Fin n) (Fin n) (nbrPSU_F g)) (kJ : ℕ)
    (hrankJ : kJ + 1 = Module.finrank (nbrPSU_F g) (LinearMap.range (Matrix.toLin' e_J)))
    (hSU : ∀ s ∈ S, Unitary.conjTr (nbrPSU_sigmae g)
        (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) * Unitary.antidiag n *
        (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) = Unitary.antidiag n)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hεJ : IsPrimAdjIdemIn (nbrPSU_sigma g) (Unitary.antidiag n)
      (Algebra.adjoin (nbrPSU_F g) (Units.val '' S)) ε_J)
    (hJ'block : IsComponentOf J'
      ⁅glBlockCentralizer ((Unitary.SU (nbrPSU_sigmae g) n).subtype) S ε_J,
        glBlockCentralizer ((Unitary.SU (nbrPSU_sigmae g) n).subtype) S ε_J⁆)
    (hK'ε : IsComponentOf K'
      ⁅glBlockCentralizer ((Unitary.SU (nbrPSU_sigmae g) n).subtype)
          ({s_e} : Set (GL (Fin n) (nbrPSU_F g))) ε,
        glBlockCentralizer ((Unitary.SU (nbrPSU_sigmae g) n).subtype)
          ({s_e} : Set (GL (Fin n) (nbrPSU_F g))) ε⁆)
    (heJ : IsPrimIdemIn (Algebra.adjoin (nbrPSU_F g) (Units.val '' S)) e_J)
    (hdual : e_J ≠ ε_J ∧ formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e_J ≠ e_J ∧
      ε_J = e_J + formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e_J)
    (heJε : e_J * ε_J = e_J)
    (hε : IsPrimAdjIdemIn (nbrPSU_sigma g) (Unitary.antidiag n)
      (Algebra.adjoin (nbrPSU_F g) (Units.val '' ({s_e} : Set (GL (Fin n) (nbrPSU_F g))))) ε)
    (he' : IsPrimIdemIn (Algebra.adjoin (nbrPSU_F g)
      (Units.val '' ({s_e} : Set (GL (Fin n) (nbrPSU_F g))))) e')
    (hself : e' = ε)
    (hdeg : blockDegree (Algebra.adjoin (nbrPSU_F g)
      (Units.val '' ({s_e} : Set (GL (Fin n) (nbrPSU_F g))))) e' < 2)
    (hψker : ψ.ker ≤ Subgroup.center ↥(Unitary.SU (nbrPSU_sigmae g) n))
    (R : Subgroup X) (R' : Subgroup ↥(Unitary.SU (nbrPSU_sigmae g) n))
    (hR'map : R'.map ψ = R) (hR'K' : R' ≤ K')
    (hkind : (∃ v : Fin n → nbrPSU_F g, v ≠ 0 ∧
        Matrix.vecMul (fun i => nbrPSU_sigmae g (v i)) (Unitary.antidiag n) ⬝ᵥ v = 0 ∧
        R'.map ((Unitary.SU (nbrPSU_sigmae g) n).subtype) =
          unitTransvGroup (nbrPSU_sigma g) (Unitary.antidiag n) v) ∨
      (∃ v w : Fin n → nbrPSU_F g, v ≠ 0 ∧ w ≠ 0 ∧
        LinearIndependent (nbrPSU_F g) ![v, w] ∧
        Matrix.vecMul (fun i => nbrPSU_sigmae g (v i)) (Unitary.antidiag n) ⬝ᵥ v = 0 ∧
        Matrix.vecMul (fun i => nbrPSU_sigmae g (w i)) (Unitary.antidiag n) ⬝ᵥ w = 0 ∧
        Matrix.vecMul (fun i => nbrPSU_sigmae g (v i)) (Unitary.antidiag n) ⬝ᵥ w = 0 ∧
        R'.map ((Unitary.SU (nbrPSU_sigmae g) n).subtype) =
          unitPairGroup (nbrPSU_sigma g) (Unitary.antidiag n) v w)) :
    ∃ (mK : ℕ) (βK : Fin (ggU .PSU mK (g + 1)).D.rank → ℤ), 2 * (kJ + 1) ≤ mK ∧
      βK ∈ (ggU .PSU mK (g + 1)).D.roots ∧
      (GGLongRoot (ggU .PSU mK (g + 1)).D βK ∨
        2 • βK ∉ (ggU .PSU mK (g + 1)).D.roots) ∧
      GGRootVia (ggU .PSU mK (g + 1)) K R βK := by
  have hG : IsUnit (Unitary.antidiag n : Matrix (Fin n) (Fin n) (nbrPSU_F g)).det :=
    isUnit_iff_ne_zero.mpr (Unitary.det_antidiag_ne_zero n)
  have hSe : ({s_e} : Set (GL (Fin n) (nbrPSU_F g))) ⊆ S :=
    Set.singleton_subset_iff.mpr hs_eS
  have hS_e : ∀ s ∈ ({s_e} : Set (GL (Fin n) (nbrPSU_F g))),
      ∀ s' ∈ ({s_e} : Set (GL (Fin n) (nbrPSU_F g))), Commute s s' := by
    intro s hs s' hs'
    rw [Set.mem_singleton_iff] at hs hs'
    rw [hs, hs']
  have hεJε : ε_J * ε = ε_J :=
    nbrPSU_l8_baseAdjIdem_le hSe hS hεJ hε hJ'block hK'ε hJ'K'
  have hK'e' : IsComponentOf K'
      ⁅glBlockCentralizer ((Unitary.SU (nbrPSU_sigmae g) n).subtype)
          ({s_e} : Set (GL (Fin n) (nbrPSU_F g))) e',
        glBlockCentralizer ((Unitary.SU (nbrPSU_sigmae g) n).subtype)
          ({s_e} : Set (GL (Fin n) (nbrPSU_F g))) e'⁆ := by
    rw [hself]
    exact hK'ε
  have hadj' : formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e' = e' := by
    rw [hself]
    exact hε.2.2.2.1
  obtain ⟨r, ι, hr, hcenter, hιrange, hlong, hshort⟩ :=
    exists_blockModelClosure_selfDual_PSU_explicit n g ({s_e} : Set (GL (Fin n) (nbrPSU_F g)))
      hS_e he' hadj' hdeg hK'e'
  have h2k : 2 * (kJ + 1) ≤ r := by
    rw [hrankJ, hr]
    have hest : IsIdempotentElem (formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e_J) := by
      rw [IsIdempotentElem, ← Geo.formAdj_mul (nbrPSU_sigma g) hG e_J e_J, heJ.2.1.eq]
    have horth : e_J * formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e_J = 0 := by
      have h := heJε
      rw [hdual.2.2, mul_add, heJ.2.1.eq] at h
      exact add_left_cancel (by rw [h, add_zero])
    have horth' : formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e_J * e_J = 0 := by
      have hmem : formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e_J ∈
          Algebra.adjoin (nbrPSU_F g) (Units.val '' S) :=
        Geo.formAdj_mem_adjoin (nbrPSU_sigma g) hG
          (fun s hs => by simpa [Unitary.conjTr] using hSU s hs) heJ.1
      rw [nbrPSU_adjoin_commute hS hmem heJ.1, horth]
    have hrk_eq : Module.finrank (nbrPSU_F g)
        (LinearMap.range (Matrix.toLin' (formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e_J))) =
        Module.finrank (nbrPSU_F g) (LinearMap.range (Matrix.toLin' e_J)) :=
      nbrPSUx_finrank_range_formAdj (nbrPSU_sigma g) (nbrPSU_sigma_involutive g) hG e_J
    have hsum : (e_J + formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e_J) * e' =
        e_J + formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e_J := by
      rw [hself, ← hdual.2.2]
      exact hεJε
    exact nbrPSUx_dual_nbr heJ.2.1 hest horth horth' hrk_eq hsum
  rcases hkind with hkind | hkind
  · obtain ⟨v, hv, hviso, hEq⟩ := hkind
    have hle : unitTransvGroup (nbrPSU_sigma g) (Unitary.antidiag n) v ≤
        K'.map ((Unitary.SU (nbrPSU_sigmae g) n).subtype) := by
      rw [← hEq]
      exact Subgroup.map_mono hR'K'
    obtain ⟨βK, uK, hβKroot, hβKlong, hEqK⟩ := hlong v hv hviso hle
    have hR'eq : R' = (((ggU .PSU r (g + 1)).D.rootGroup βK).map
        (MulAut.conj uK).toMonoidHom).map ι :=
      Subgroup.map_injective (Subgroup.subtype_injective _) (hEq.trans hEqK.symm)
    have hRsubK : R = ggRootSub (ggU .PSU r (g + 1)).D (ψ.comp ι) βK uK := by
      rw [← hR'map, hR'eq]
      unfold ggRootSub
      rw [Subgroup.map_map]
    have hrange : (ψ.comp ι).range = K := by
      rw [MonoidHom.range_comp, hιrange, hK'map]
    have hker : (ψ.comp ι).ker ≤ Subgroup.center (ggU .PSU r (g + 1)).K := by
      intro y hy
      have hy1 : ψ (ι y) = 1 := by
        have := MonoidHom.mem_ker.mp hy
        simpa [MonoidHom.comp_apply] using this
      exact hcenter y (hψker (MonoidHom.mem_ker.mpr hy1))
    exact ⟨r, βK, h2k, hβKroot, Or.inl hβKlong,
      ⟨ψ.comp ι, hrange, hker, uK, hRsubK⟩⟩
  · obtain ⟨v, w, hv, hw, hli, hviso, hwiso, hpair, hEq⟩ := hkind
    have hle : unitPairGroup (nbrPSU_sigma g) (Unitary.antidiag n) v w ≤
        K'.map ((Unitary.SU (nbrPSU_sigmae g) n).subtype) := by
      rw [← hEq]
      exact Subgroup.map_mono hR'K'
    obtain ⟨βK, uK, hβKroot, hβKshort, h2βK, hEqK⟩ :=
      hshort v w hv hw hli hviso hwiso hpair hle
    have hR'eq : R' = (((ggU .PSU r (g + 1)).D.rootGroup βK).map
        (MulAut.conj uK).toMonoidHom).map ι :=
      Subgroup.map_injective (Subgroup.subtype_injective _) (hEq.trans hEqK.symm)
    have hRsubK : R = ggRootSub (ggU .PSU r (g + 1)).D (ψ.comp ι) βK uK := by
      rw [← hR'map, hR'eq]
      unfold ggRootSub
      rw [Subgroup.map_map]
    have hrange : (ψ.comp ι).range = K := by
      rw [MonoidHom.range_comp, hιrange, hK'map]
    have hker : (ψ.comp ι).ker ≤ Subgroup.center (ggU .PSU r (g + 1)).K := by
      intro y hy
      have hy1 : ψ (ι y) = 1 := by
        have := MonoidHom.mem_ker.mp hy
        simpa [MonoidHom.comp_apply] using this
      exact hcenter y (hψker (MonoidHom.mem_ker.mpr hy1))
    exact ⟨r, βK, h2k, hβKroot, Or.inr h2βK,
      ⟨ψ.comp ι, hrange, hker, uK, hRsubK⟩⟩

private lemma nbrPSUx_K_dual_pair
    {X : Type} [Group X] (n g : ℕ)
    (ψ : ↥(Unitary.SU (nbrPSU_sigmae g) n) →* X)
    (S : Set (GL (Fin n) (nbrPSU_F g))) (s_e : GL (Fin n) (nbrPSU_F g)) (hs_eS : s_e ∈ S)
    (K' : Subgroup ↥(Unitary.SU (nbrPSU_sigmae g) n)) (K : Subgroup X)
    (hK'map : K'.map ψ = K)
    (J : Subgroup X) (J' : Subgroup ↥(Unitary.SU (nbrPSU_sigmae g) n))
    (hJ'map : J'.map ψ = J)
    (hJ'comp : IsComponentOf J' ((Subgroup.centralizer S).comap
        ((Unitary.SU (nbrPSU_sigmae g) n).subtype)))
    (hK'comp : IsComponentOf K' ((Subgroup.centralizer
        ({s_e} : Set (GL (Fin n) (nbrPSU_F g)))).comap
        ((Unitary.SU (nbrPSU_sigmae g) n).subtype)))
    (hJ'K' : J' ≤ K') (hKne : K ≠ J)
    (e_J ε e' : Matrix (Fin n) (Fin n) (nbrPSU_F g)) (kJ : ℕ)
    (hrankJ : kJ + 1 = Module.finrank (nbrPSU_F g) (LinearMap.range (Matrix.toLin' e_J)))
    (hSU : ∀ s ∈ S, Unitary.conjTr (nbrPSU_sigmae g)
        (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) * Unitary.antidiag n *
        (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) = Unitary.antidiag n)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s))
    (hK'ε : IsComponentOf K'
      ⁅glBlockCentralizer ((Unitary.SU (nbrPSU_sigmae g) n).subtype)
          ({s_e} : Set (GL (Fin n) (nbrPSU_F g))) ε,
        glBlockCentralizer ((Unitary.SU (nbrPSU_sigmae g) n).subtype)
          ({s_e} : Set (GL (Fin n) (nbrPSU_F g))) ε⁆)
    (heJ : IsPrimIdemIn (Algebra.adjoin (nbrPSU_F g) (Units.val '' S)) e_J)
    (hdegJ : blockDegree (Algebra.adjoin (nbrPSU_F g) (Units.val '' S)) e_J < 2)
    (he' : IsPrimIdemIn (Algebra.adjoin (nbrPSU_F g)
      (Units.val '' ({s_e} : Set (GL (Fin n) (nbrPSU_F g))))) e')
    (hdual' : e' ≠ ε ∧ formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e' ≠ e' ∧
      ε = e' + formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e')
    (heJ_e' : e_J * e' = e_J)
    (hdeg : blockDegree (Algebra.adjoin (nbrPSU_F g)
      (Units.val '' ({s_e} : Set (GL (Fin n) (nbrPSU_F g))))) e' < 2)
    (hψker : ψ.ker ≤ Subgroup.center ↥(Unitary.SU (nbrPSU_sigmae g) n))
    (R : Subgroup X) (R' : Subgroup ↥(Unitary.SU (nbrPSU_sigmae g) n))
    (hR'map : R'.map ψ = R) (hR'K' : R' ≤ K')
    (hkind : (∃ v : Fin n → nbrPSU_F g, v ≠ 0 ∧
        Matrix.vecMul (fun i => nbrPSU_sigmae g (v i)) (Unitary.antidiag n) ⬝ᵥ v = 0 ∧
        R'.map ((Unitary.SU (nbrPSU_sigmae g) n).subtype) =
          unitTransvGroup (nbrPSU_sigma g) (Unitary.antidiag n) v) ∨
      (∃ v w : Fin n → nbrPSU_F g, v ≠ 0 ∧ w ≠ 0 ∧
        LinearIndependent (nbrPSU_F g) ![v, w] ∧
        Matrix.vecMul (fun i => nbrPSU_sigmae g (v i)) (Unitary.antidiag n) ⬝ᵥ v = 0 ∧
        Matrix.vecMul (fun i => nbrPSU_sigmae g (w i)) (Unitary.antidiag n) ⬝ᵥ w = 0 ∧
        Matrix.vecMul (fun i => nbrPSU_sigmae g (v i)) (Unitary.antidiag n) ⬝ᵥ w = 0 ∧
        R'.map ((Unitary.SU (nbrPSU_sigmae g) n).subtype) =
          unitPairGroup (nbrPSU_sigma g) (Unitary.antidiag n) v w)) :
    ∃ (kK : ℕ) (βK : Fin (ggU .PSL (kK + 1) (2 * (g + 1))).D.rank → ℤ), kJ < kK ∧
      βK ∈ (ggU .PSL (kK + 1) (2 * (g + 1))).D.roots ∧
      GGRootVia (ggU .PSL (kK + 1) (2 * (g + 1))) K R βK := by
  have hSU_e : ∀ s ∈ ({s_e} : Set (GL (Fin n) (nbrPSU_F g))),
      Unitary.conjTr (nbrPSU_sigmae g) (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) *
          Unitary.antidiag n * (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) = Unitary.antidiag n := by
    intro s hs
    rw [Set.mem_singleton_iff] at hs
    rw [hs]
    exact hSU s_e hs_eS
  have hS_e : ∀ s ∈ ({s_e} : Set (GL (Fin n) (nbrPSU_F g))),
      ∀ s' ∈ ({s_e} : Set (GL (Fin n) (nbrPSU_F g))), Commute s s' := by
    intro s hs s' hs'
    rw [Set.mem_singleton_iff] at hs hs'
    rw [hs, hs']
  have hodd_e : ∀ s ∈ ({s_e} : Set (GL (Fin n) (nbrPSU_F g))), Odd (orderOf s) := by
    intro s hs
    rw [Set.mem_singleton_iff] at hs
    rw [hs]
    exact hodd s_e hs_eS
  obtain ⟨k, ι, hk, hcenter, hιrange, hlong⟩ :=
    exists_blockModelClosure_dualPair_PSU_explicitModel n g ({s_e} : Set (GL (Fin n) (nbrPSU_F g)))
      hSU_e hS_e he' hdual'.2.1 hdeg (by rw [← hdual'.2.2]; exact hK'ε)
  have hne : e_J ≠ e' :=
    nbrPSUx_dualPair_ne n g ψ S s_e hs_eS hSU hS K' K hK'map J J' hJ'map hJ'comp hK'comp hJ'K'
      hKne e_J ε e' hK'ε heJ hdegJ hdual' he'
  have hkk : kJ < k := by
    have he'_mem : e' ∈ Algebra.adjoin (nbrPSU_F g) (Units.val '' S) :=
      Algebra.adjoin_mono (Set.image_mono (Set.singleton_subset_iff.mpr hs_eS)) he'.1
    have hba : e' * e_J = e_J :=
      (nbrPSU_adjoin_commute hS he'_mem heJ.1).trans heJ_e'
    have hlt := nbrPSUx_rank_lt heJ.2.1 heJ_e' hba hne
    exact Nat.lt_of_succ_lt_succ (by
      change kJ + 1 < k + 1
      rw [hrankJ, hk]
      exact hlt)
  rcases hkind with hkind | hkind
  · obtain ⟨v, hv, hviso, hEq⟩ := hkind
    exact (nbrPSU_l8_dualPairLongExclusion n g ({s_e} : Set (GL (Fin n) (nbrPSU_F g)))
      hSU_e hS_e hodd_e he' hdual'.2.1 (by rw [← hdual'.2.2]; exact hK'ε) hv hviso (by
        rw [← hEq]
        exact Subgroup.map_mono hR'K')).elim
  · obtain ⟨v, w, hv, hw, hli, hviso, hwiso, hpair, hEq⟩ := hkind
    have hle : unitPairGroup (nbrPSU_sigma g) (Unitary.antidiag n) v w ≤
        K'.map ((Unitary.SU (nbrPSU_sigmae g) n).subtype) := by
      rw [← hEq]
      exact Subgroup.map_mono hR'K'
    obtain ⟨βK, uK, hβKroot, hβKlong, hEqK⟩ :=
      hlong v w hv hw hli hviso hwiso hpair hle
    have hR'eq : R' = (((ggU .PSL (k + 1) (2 * (g + 1))).D.rootGroup βK).map
        (MulAut.conj uK).toMonoidHom).map ι :=
      Subgroup.map_injective (Subgroup.subtype_injective _) (hEq.trans hEqK.symm)
    have hRsubK : R = ggRootSub (ggU .PSL (k + 1) (2 * (g + 1))).D (ψ.comp ι) βK uK := by
      rw [← hR'map, hR'eq]
      unfold ggRootSub
      rw [Subgroup.map_map]
    have hrange : (ψ.comp ι).range = K := by
      rw [MonoidHom.range_comp, hιrange, hK'map]
    have hker : (ψ.comp ι).ker ≤ Subgroup.center (ggU .PSL (k + 1) (2 * (g + 1))).K := by
      intro y hy
      have hy1 : ψ (ι y) = 1 := by
        have := MonoidHom.mem_ker.mp hy
        simpa [MonoidHom.comp_apply] using this
      exact hcenter y (hψker (MonoidHom.mem_ker.mpr hy1))
    exact ⟨k, βK, hkk, hβKroot, ⟨ψ.comp ι, hrange, hker, uK, hRsubK⟩⟩

private lemma nbrPSUx_K_dual
    {X : Type} [Group X] [Finite X] (n g : ℕ)
    (ψ : ↥(Unitary.SU (nbrPSU_sigmae g) n) →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X)
    (hH : GGSixPosHyp .PSU n (g + 1) ψ p G₀ B₁ D J L x)
    (S : Set (GL (Fin n) (nbrPSU_F g))) (J' : Subgroup ↥(Unitary.SU (nbrPSU_sigmae g) n))
    (ε_J e_J : Matrix (Fin n) (Fin n) (nbrPSU_F g))
    (hSdef : ∀ s : GL (Fin n) (nbrPSU_F g), s ∈ S ↔
      Unitary.conjTr (nbrPSU_sigmae g) (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) *
          Unitary.antidiag n * (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) = Unitary.antidiag n ∧
        ∃ d ∈ D, IsGLLift ((Unitary.SU (nbrPSU_sigmae g) n).subtype) ψ s d)
    (hSU : ∀ s ∈ S, Unitary.conjTr (nbrPSU_sigmae g)
        (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) * Unitary.antidiag n *
        (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) = Unitary.antidiag n)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s))
    (hJ'comp : IsComponentOf J' ((Subgroup.centralizer S).comap
        ((Unitary.SU (nbrPSU_sigmae g) n).subtype)))
    (hJ'map : J'.map ψ = J)
    (hεJ : IsPrimAdjIdemIn (nbrPSU_sigma g) (Unitary.antidiag n)
      (Algebra.adjoin (nbrPSU_F g) (Units.val '' S)) ε_J)
    (hJ'block : IsComponentOf J'
      ⁅glBlockCentralizer ((Unitary.SU (nbrPSU_sigmae g) n).subtype) S ε_J,
        glBlockCentralizer ((Unitary.SU (nbrPSU_sigmae g) n).subtype) S ε_J⁆)
    (heJ : IsPrimIdemIn (Algebra.adjoin (nbrPSU_F g) (Units.val '' S)) e_J)
    (heJε : e_J * ε_J = e_J)
    (hdegJ : blockDegree (Algebra.adjoin (nbrPSU_F g) (Units.val '' S)) e_J < 2)
    (hdual : e_J ≠ ε_J ∧ formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e_J ≠ e_J ∧
      ε_J = e_J + formAdj (nbrPSU_sigma g) (Unitary.antidiag n) e_J)
    (hpdiv : p ∣ 2 ^ (g + 1) - 1)
    (kJ : ℕ) (hrankJ : kJ + 1 = Module.finrank (nbrPSU_F g)
      (LinearMap.range (Matrix.toLin' e_J)))
    (R Rm : Subgroup X) (hR : R ≤ J)
    (hR0S : ∃ (β : Fin (ggU .PSU n (g + 1)).D.rank → ℤ),
      β ∈ (ggU .PSU n (g + 1)).D.roots ∧ 2 • β ∉ (ggU .PSU n (g + 1)).D.roots ∧
      ∃ u : (ggU .PSU n (g + 1)).K,
        R = ggRootSub (ggU .PSU n (g + 1)).D ψ β u ∧
        Rm = ggRootSub (ggU .PSU n (g + 1)).D ψ (-β) u)
    (e : X) (he : e ∈ D) (K : Subgroup X)
    (hKcomp : IsComponentOf K (G₀ ⊓ Subgroup.centralizer ({e} : Set X))) (hJK : J ≤ K)
    (hKne : K ≠ J) :
    (∃ (kK : ℕ) (βK : Fin (ggU .PSL (kK + 1) (2 * (g + 1))).D.rank → ℤ), kJ < kK ∧
      βK ∈ (ggU .PSL (kK + 1) (2 * (g + 1))).D.roots ∧
      GGRootVia (ggU .PSL (kK + 1) (2 * (g + 1))) K R βK) ∨
    (∃ (mK : ℕ) (βK : Fin (ggU .PSU mK (g + 1)).D.rank → ℤ), 2 * (kJ + 1) ≤ mK ∧
      βK ∈ (ggU .PSU mK (g + 1)).D.roots ∧
      (GGLongRoot (ggU .PSU mK (g + 1)).D βK ∨
        2 • βK ∉ (ggU .PSU mK (g + 1)).D.roots) ∧
      GGRootVia (ggU .PSU mK (g + 1)) K R βK) := by
  have hH' : GGSixPosHyp .PSU n (g + 1) ψ p G₀ B₁ D J L x := hH
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩ := hH'
  have hc : Nat.card (nbrPSU_F g) = (2 ^ (g + 1)) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul 2 (g + 1) (by omega)
  have hadm : CFSG.Open.StatedLieAdmissible .PSU n 2 (g + 1) := h3.admissible
  have hn : 3 ≤ n := hadm.2.2.1
  have hψker : ψ.ker ≤ Subgroup.center ↥(Unitary.SU (nbrPSU_sigmae g) n) := h2
  have hG : IsUnit (Unitary.antidiag n : Matrix (Fin n) (Fin n) (nbrPSU_F g)).det :=
    isUnit_iff_ne_zero.mpr (Unitary.det_antidiag_ne_zero n)
  obtain ⟨s_e, K', hK'map, hK'comp, hodd_se, hiso, hs_e_lift⟩ :=
    nbrPSUx_neighbourLiftData n g ψ p G₀ B₁ D J L x hH e he K hKcomp
  have hs_eS : s_e ∈ S := (hSdef s_e).mpr ⟨hiso, e, he, hs_e_lift⟩
  have hJ'K' : J' ≤ K' :=
    nbrPSU_l8_le_of_map_le_of_quasisimple ψ hψker hJ'comp.2.2
      (by rw [hJ'map, hK'map]; exact hJK)
  obtain ⟨ε, e', hε, hK'ε, he', he'ε, hdeg, hsplit, heJ_ε, heJ_e'⟩ :=
    nbrPSUx_neighbourBlockData n g S J' ε_J e_J hS hodd hεJ hJ'block heJ heJε hdegJ K' hJ'K'
      s_e hs_eS hK'comp hodd_se hiso
  have hSe : ({s_e} : Set (GL (Fin n) (nbrPSU_F g))) ⊆ S := Set.singleton_subset_iff.mpr hs_eS
  have hSU_e : ∀ s ∈ ({s_e} : Set (GL (Fin n) (nbrPSU_F g))),
      Unitary.conjTr (nbrPSU_sigmae g) (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) *
          Unitary.antidiag n * (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) =
        Unitary.antidiag n := by
    intro s hs
    rw [Set.mem_singleton_iff] at hs
    rw [hs]
    exact hiso
  have hS_e : ∀ s ∈ ({s_e} : Set (GL (Fin n) (nbrPSU_F g))),
      ∀ s' ∈ ({s_e} : Set (GL (Fin n) (nbrPSU_F g))), Commute s s' := by
    intro s hs s' hs'
    rw [Set.mem_singleton_iff] at hs hs'
    rw [hs, hs']
  have hodd_e : ∀ s ∈ ({s_e} : Set (GL (Fin n) (nbrPSU_F g))), Odd (orderOf s) := by
    intro s hs
    rw [Set.mem_singleton_iff] at hs
    rw [hs]
    exact hodd_se
  obtain ⟨β₀, hβ₀root, h2β₀, u₀, hRsub₀, hRmsub₀⟩ := hR0S
  have hR0 : GGRootPosG0 .PSU n (g + 1) p ψ R Rm :=
    ⟨β₀, hβ₀root, Or.inr ⟨Or.inr (Or.inr ⟨Or.inl rfl, hpdiv⟩), h2β₀⟩, u₀, hRsub₀, hRmsub₀⟩
  obtain ⟨R', hR'map, hR'K', hkind⟩ :=
    nbrPSU_l8_rootLiftKind n g ψ p J K R Rm hR hJK hR0 hψker hn hc K' hK'map
  have hεJε : ε_J * ε = ε_J :=
    nbrPSU_l8_baseAdjIdem_le hSe hS hεJ hε hJ'block hK'ε hJ'K'
  rcases hsplit with hself | hdual'
  · exact Or.inr (nbrPSUx_K_dual_self n g ψ S s_e hs_eS K' K hK'map J' hJ'K' ε_J e_J ε e' kJ
      hrankJ hSU hS hεJ hJ'block hK'ε heJ hdual heJε hε he' hself hdeg hψker R R' hR'map hR'K'
      hkind)
  · exact Or.inl (nbrPSUx_K_dual_pair n g ψ S s_e hs_eS K' K hK'map J J' hJ'map hJ'comp hK'comp
      hJ'K' hKne e_J ε e' kJ hrankJ hSU hS hodd hK'ε heJ hdegJ he'
      hdual' heJ_e' hdeg hψker R R' hR'map hR'K' hkind)

theorem ggSixPSUPosExplicit_holds
    {X : Type} [Group X] [Finite X] (n f : ℕ) (ψ : (ggU .PSU n f).K →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X) (hH : GGSixPosHyp .PSU n f ψ p G₀ B₁ D J L x) :
    ∃ (R Rm : Subgroup X),
      R ≤ J ∧ Rm ≤ J ∧ 1 ≤ f ∧
      ((∃ (mJ : ℕ) (βJ : Fin (ggU .PSU mJ f).D.rank → ℤ), mJ < n ∧
          βJ ∈ (ggU .PSU mJ f).D.roots ∧ GGLongRoot (ggU .PSU mJ f).D βJ ∧
          GGRootVia (ggU .PSU mJ f) J R βJ ∧
          (∃ β : Fin (ggU .PSU n f).D.rank → ℤ, β ∈ (ggU .PSU n f).D.roots ∧
            GGLongRoot (ggU .PSU n f).D β ∧ ∃ u : (ggU .PSU n f).K,
              R = ggRootSub (ggU .PSU n f).D ψ β u ∧ Rm = ggRootSub (ggU .PSU n f).D ψ (-β) u) ∧
          ∀ e ∈ D, e ≠ 1 → ∀ K : Subgroup X, K ≤ G₀ →
            CFSG.Assembly.IsComponentOf K (Subgroup.centralizer {e}) → J ≤ K → K ≠ J →
            Odd (Nat.card (Subgroup.center ↥K)) →
            ∃ (mK : ℕ) (βK : Fin (ggU .PSU mK f).D.rank → ℤ), mJ < mK ∧
              βK ∈ (ggU .PSU mK f).D.roots ∧ GGLongRoot (ggU .PSU mK f).D βK ∧
              GGRootVia (ggU .PSU mK f) K R βK) ∨
        (∃ (kJ : ℕ) (φJ : (ggU .PSL (kJ + 1) (2 * f)).K →* X)
            (βJ : Fin (ggU .PSL (kJ + 1) (2 * f)).D.rank → ℤ), 2 * (kJ + 1) ≤ n ∧
          βJ ∈ (ggU .PSL (kJ + 1) (2 * f)).D.roots ∧
          φJ.range = J ∧ φJ.ker ≤ Subgroup.center (ggU .PSL (kJ + 1) (2 * f)).K ∧
          (∃ u : (ggU .PSL (kJ + 1) (2 * f)).K,
            R = ggRootSub (ggU .PSL (kJ + 1) (2 * f)).D φJ βJ u) ∧
          (∀ b ∈ B₁, ∃ s : GL (Fin (kJ + 1)) (GaloisField 2 (2 * f)),
            IsGLLift Matrix.SpecialLinearGroup.toGL φJ s b) ∧
          p ∣ 2 ^ f - 1 ∧
          (∃ β : Fin (ggU .PSU n f).D.rank → ℤ, β ∈ (ggU .PSU n f).D.roots ∧
            2 • β ∉ (ggU .PSU n f).D.roots ∧ ∃ u : (ggU .PSU n f).K,
              R = ggRootSub (ggU .PSU n f).D ψ β u ∧ Rm = ggRootSub (ggU .PSU n f).D ψ (-β) u) ∧
          ∀ e ∈ D, e ≠ 1 → ∀ K : Subgroup X, K ≤ G₀ →
            CFSG.Assembly.IsComponentOf K (Subgroup.centralizer {e}) → J ≤ K → K ≠ J →
            Odd (Nat.card (Subgroup.center ↥K)) →
            (∃ (kK : ℕ) (βK : Fin (ggU .PSL (kK + 1) (2 * f)).D.rank → ℤ), kJ < kK ∧
              βK ∈ (ggU .PSL (kK + 1) (2 * f)).D.roots ∧
              GGRootVia (ggU .PSL (kK + 1) (2 * f)) K R βK) ∨
            (∃ (mK : ℕ) (βK : Fin (ggU .PSU mK f).D.rank → ℤ), 2 * (kJ + 1) ≤ mK ∧
              βK ∈ (ggU .PSU mK f).D.roots ∧
              (GGLongRoot (ggU .PSU mK f).D βK ∨ 2 • βK ∉ (ggU .PSU mK f).D.roots) ∧
              GGRootVia (ggU .PSU mK f) K R βK))) := by
  have hH' : GGSixPosHyp .PSU n f ψ p G₀ B₁ D J L x := hH
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩ := hH'
  have hadm : CFSG.Open.StatedLieAdmissible .PSU n 2 f := h3.admissible
  have hf : 1 ≤ f := hadm.2.1
  obtain ⟨g, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : f ≠ 0)
  obtain ⟨S, J', ε_J, e_J, hSdef, hSU, hS, hodd, hJ'comp, hJ'map, hεJ, hJ'block, heJ, heJε,
    hdegJ⟩ :=
    nbrPSU_l8_baseBlockDataChar n g ψ p G₀ B₁ D J L x hH x h17
  have hpowS : ∀ s ∈ S, ∃ c : nbrPSU_F g,
      (s : Matrix (Fin n) (Fin n) (nbrPSU_F g)) ^ p = Matrix.scalar (Fin n) c :=
    nbrPSUx_basePow n g ψ p G₀ B₁ D J L x hH S hSdef
  rcases nbrPSUx_J_split n g S hSU hS hεJ heJ heJε with
      ⟨hself_eq, hself_adj⟩ | ⟨hdual_ne, hdual_adjne, hdual_sum⟩
  · obtain ⟨R, Rm, hRle, hRmle, hR0L, mJ, βJ, hmJn, hmJrank, hβJroot, hβJlong, hviaJ⟩ :=
      nbrPSUx_J_self n g ψ p G₀ B₁ D J L x hH S J' ε_J e_J hSdef hS hJ'map
        hJ'block heJ hdegJ ⟨hself_eq, hself_adj⟩
    refine ⟨R, Rm, hRle, hRmle, hf, Or.inl ⟨mJ, βJ, hmJn, hβJroot, hβJlong, hviaJ, hR0L, ?_⟩⟩
    intro e he he1 K hKG0 hKcomp hJK hKne hZodd
    have hKcomp' : IsComponentOf K (G₀ ⊓ Subgroup.centralizer ({e} : Set X)) :=
      IsComponentOf.of_le_of_le hKcomp (le_inf hKG0 hKcomp.1) inf_le_right
    exact nbrPSUx_K_self n g ψ p G₀ B₁ D J L x hH S J' ε_J e_J hSdef hSU hS hodd hJ'comp hJ'map
      hεJ hJ'block heJ heJε hdegJ ⟨hself_eq, hself_adj⟩ mJ hmJrank R Rm hRle hR0L e he K hKcomp' hJK hKne
  · rcases nbrPSUx_J_dual n g ψ p G₀ B₁ D J L x hH S J' ε_J e_J hSdef hSU hS hJ'map
        hεJ hJ'block heJ heJε hdegJ hpowS ⟨hdual_ne, hdual_adjne, hdual_sum⟩ with
      ⟨R, Rm, hRle, hRmle,
        ⟨kJ, φJ, βJ, hdimJ, hrankJ, hβJroot, hφrange, hφker, ⟨u, hRvia⟩, hBlift, hpdiv⟩,
        β, hβroot, h2β, u', hRu, hRmu⟩
    refine ⟨R, Rm, hRle, hRmle, hf, Or.inr ⟨kJ, φJ, βJ, hdimJ, hβJroot, hφrange, hφker,
      ⟨u, hRvia⟩, hBlift, hpdiv, ⟨β, hβroot, h2β, u', hRu, hRmu⟩, ?_⟩⟩
    intro e he he1 K hKG0 hKcomp hJK hKne hZodd
    have hKcomp' : IsComponentOf K (G₀ ⊓ Subgroup.centralizer ({e} : Set X)) :=
      IsComponentOf.of_le_of_le hKcomp (le_inf hKG0 hKcomp.1) inf_le_right
    exact nbrPSUx_K_dual n g ψ p G₀ B₁ D J L x hH S J' ε_J e_J hSdef hSU hS hodd hJ'comp hJ'map
      hεJ hJ'block heJ heJε hdegJ ⟨hdual_ne, hdual_adjne, hdual_sum⟩ hpdiv kJ hrankJ R Rm
      hRle ⟨β, hβroot, h2β, u', hRu, hRmu⟩ e he K hKcomp' hJK hKne

end CFSG.StandardType.ClassicalPosition
