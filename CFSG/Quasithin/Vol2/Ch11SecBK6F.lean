module

public import CFSG.Quasithin.Vol2.Ch11SecAKB2
public import CFSG.Quasithin.Vol2.KGNatSL3LineFacts
public import CFSG.Quasithin.Vol2.Ch11SecBK2D
public import CFSG.Quasithin.Vol2.Ch11G2Q8AutV
public import CFSG.Quasithin.Vol2.Ch11SecA02Eight
public import CFSG.Quasithin.Vol2.Ch11SecA12Out2
public import CFSG.Quasithin.Vol2.Ch11SecBK2G
public import CFSG.Quasithin.Vol2.Ch11SecBK7E
public import CFSG.Quasithin.Vol2.Ch11SecBK7G

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Quasithin Matrix
open CFSG.Quasithin.Vol2.KGNat
open CFSG.Assembly.LowTwoRank (StatedSL specialLinearGroupEquivStatedSL)
open CFSG.ClassicalInvolution.ModelFacts.OddCover (uSL coe_uSL)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (flagSpace)
open CFSG.Open (pCoreOf)
open scoped IsMulCommutative

namespace BK6

@[expose] def lowT {K : Type} [Field K] (t : K) : SpecialLinearGroup (Fin 3) K :=
  ⟨!![1, 0, 0; t, 1, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

theorem lowT_mulVec {K : Type} [Field K] (t : K) (x : Fin 3 → K) :
    ((lowT t : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ x =
      ![x 0, t * x 0 + x 1, x 2] := by
  show !![(1 : K), 0, 0; t, 1, 0; 0, 0, 1] *ᵥ x = _
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem lowT_mem_stabRow2 {K : Type} [Field K] (t : K) : lowT t ∈ stabRow2 K :=
  mem_stabRow2.mpr ⟨rfl, rfl, rfl⟩

variable {G : Type} [Group G] [Finite G] {L V X T V₁ V₂ : Subgroup G} {n : ℕ}

theorem exists_rad2_of_mem_r2 (hfl : Flag24 L V X T V₁ V₂ n) [IsMulCommutative ↥V]
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ n)
    {π : ↥(StatedSL 3 K) →* ↥(autOn L V)} {f : ↥V → (Fin 3 → K)}
    (hf : IsCoord (linModelNat (StatedSL 3 K)) (autOn L V)
      ((Subgroup.centralizer (L : Set G)).subgroupOf V) π f)
    {g : SpecialLinearGroup (Fin 3) K}
    (hV₂ : V₂.subgroupOf V = hf.pre (gmap g (flagSpace 3 K 2)).toAddSubgroup) {r : G}
    (hr : r ∈ pCoreOf 2 (LOf L V₂ ⊔ T)) :
    ∃ b c : K, SecA.conjV V r (K7.r2_le_normalizer hfl hr) =
      ((rho3 π (g * uSL 0 b c * g⁻¹) : ↥(autOn L V)) : MulAut ↥V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSL := commutator_SL2_eq_top (four_le_card hfl.two_le hK)
  obtain ⟨⟨⟨hrV, hrL⟩, hrV₂⟩, -⟩ := K7.r2_le hfl hr
  set k := SecA.conjV V r hrV with hk
  have hkZ' : ∀ z ∈ (Subgroup.centralizer (L : Set G)).subgroupOf V, k z ∈
      (Subgroup.centralizer (L : Set G)).subgroupOf V := fun z hz =>
    G2Q8.conjV_mem_centralizer hrL hrV hz
  have hkinv : k⁻¹ = SecA.conjV V r⁻¹ (Subgroup.inv_mem _ hrV) := (SecA.conjV_inv V hrV).symm
  have hkZ'' : ∀ z ∈ (Subgroup.centralizer (L : Set G)).subgroupOf V, k⁻¹ z ∈
      (Subgroup.centralizer (L : Set G)).subgroupOf V := fun z hz => by
    rw [hkinv]
    exact G2Q8.conjV_mem_centralizer (Subgroup.inv_mem _ hrL) (Subgroup.inv_mem _ hrV) hz
  have hkH : ∀ h ∈ autOn L V, k * h * k⁻¹ ∈ autOn L V := fun h hh =>
    G2Q8.conjV_mul_conjV_inv_mem hrL hrV hh
  have hkH' : ∀ h ∈ autOn L V, k⁻¹ * h * k ∈ autOn L V := fun h hh => by
    have := G2Q8.conjV_mul_conjV_inv_mem (Subgroup.inv_mem _ hrL) (Subgroup.inv_mem _ hrV) hh
    rwa [← hkinv, inv_inv] at this
  have hkU : k ∈ SecA.stabW (hf.pre (gmap g (flagSpace 3 K 2)).toAddSubgroup) := by
    rw [← hV₂]
    exact (SecA.conjV_mem_stabW_iff hfl.le₂ hrV).mpr hrV₂
  have hL₂L : LOf L V₂ ≤ L := (perfectCore_le _).trans inf_le_left
  have hkc : ∀ s ∈ perfectCore (autOn L V ⊓
      SecA.stabW (hf.pre (gmap g (flagSpace 3 K 2)).toAddSubgroup)),
      k * s * k⁻¹ * s⁻¹ ∈ pCoreOf 2 (perfectCore (autOn L V ⊓
        SecA.stabW (hf.pre (gmap g (flagSpace 3 K 2)).toAddSubgroup))) := by
    rw [← hV₂, ← SecA.autOn_lOf hfl.le_normalizer hfl.le₂,
      ← SecA.autOn_pCoreOf (hL₂L.trans hfl.le_normalizer)
        (hfl.cL_two.to_le (inf_le_inf_right _ hL₂L))]
    intro s hs
    obtain ⟨y, hyL₂, hyV, rfl⟩ := SecA.mem_autOn_iff.mp hs
    rw [hkinv, ← SecA.conjV_inv V hyV, ← SecA.conjV_mul, ← SecA.conjV_mul, ← SecA.conjV_mul]
    exact SecA.conjV_mem_autOn (K7.comm_mem_pCoreOf hfl hr hyL₂) _
  have he0 : (![1, 0, 0] : Fin 3 → K) ≠ 0 := fun h => one_ne_zero (congrFun h 0)
  obtain ⟨σ, hσ⟩ := hf.exists_semilinear (fun T hT => commutant_statedSL (by norm_num) T hT)
    he0 k hkZ' hkZ'' hkH'
  set Tm := hf.autMap k hkZ' with hTm
  have hTf : ∀ w, Tm (f w) = f (k w) := hf.autMap_apply k hkZ'
  set giM := ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hgiM
  set gM := (g : Matrix (Fin 3) (Fin 3) K) with hgM
  set Tc : (Fin 3 → K) → (Fin 3 → K) := fun x => giM *ᵥ Tm (gM *ᵥ x) with hTc
  have hTcf : ∀ w, giM *ᵥ f (k w) = Tc (giM *ᵥ f w) := fun w => by
    rw [hTc]
    simp only
    rw [hgM, hgiM, g_ginv_mulVec, hTf]
  have hTc_add : ∀ x y, Tc (x + y) = Tc x + Tc y := fun x y => by
    simp only [hTc, Matrix.mulVec_add, map_add]
  have hTc_smul : ∀ (c : K) x, Tc (c • x) = σ c • Tc x := fun c x => by
    simp only [hTc, Matrix.mulVec_smul, hσ]
  have hcommB : ∀ B ∈ stabRow2 K, ∃ B' : SpecialLinearGroup (Fin 3) K,
      (∀ x : Fin 3 → K, x 2 = 0 → (B' : Matrix (Fin 3) (Fin 3) K) *ᵥ x = x) ∧
      ∀ x, Tc ((B : Matrix (Fin 3) (Fin 3) K) *ᵥ x) =
        (B' : Matrix (Fin 3) (Fin 3) K) *ᵥ ((B : Matrix (Fin 3) (Fin 3) K) *ᵥ Tc x) := by
    intro B hB
    set s := ((rho3 π (g * B * g⁻¹) : ↥(autOn L V)) : MulAut ↥V) with hs
    have hsS : s ∈ perfectCore (autOn L V ⊓
        SecA.stabW (hf.pre (gmap g (flagSpace 3 K 2)).toAddSubgroup)) :=
      (mem_perfectCore_HU2_iff hSL hf g s).mpr ⟨B, hB, rfl⟩
    obtain ⟨B', -, hB'0, hB'1, hB'eq⟩ := levi_of_mem_pCoreOf_HU2 hSL hf g (hkc s hsS)
    refine ⟨B', fun x hx => ?_, fun x => ?_⟩
    · rw [vec3_decomp x hx, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hB'0,
        hB'1]
    · obtain ⟨w, hw⟩ := hf.surj (gM *ᵥ x)
      have hgw : giM *ᵥ f w = x := by rw [hw, hgM, hgiM, ginv_g_mulVec]
      have hid : k (s w) = (k * s * k⁻¹ * s⁻¹) (s (k w)) := by
        simp only [MulAut.mul_apply, MulAut.inv_apply_self]
      have e1 : giM *ᵥ f (k (s w)) = Tc ((B : Matrix (Fin 3) (Fin 3) K) *ᵥ x) := by
        rw [hTcf, hs, hgiM, PointStab.ginv_f_rho hf g B w, ← hgiM, hgw]
      have e2 : giM *ᵥ f ((k * s * k⁻¹ * s⁻¹) (s (k w))) =
          (B' : Matrix (Fin 3) (Fin 3) K) *ᵥ ((B : Matrix (Fin 3) (Fin 3) K) *ᵥ Tc x) := by
        rw [hB'eq, hgiM, PointStab.ginv_f_rho hf g B', hs, PointStab.ginv_f_rho hf g B, ← hgiM,
          hTcf, hgw]
      rw [← e1, ← e2, hid]
  have hTcF : ∀ x : Fin 3 → K, x 2 = 0 → Tc x 2 = 0 := by
    intro x hx
    obtain ⟨w, hw⟩ := hf.surj (gM *ᵥ x)
    have hgw : giM *ᵥ f w = x := by rw [hw, hgM, hgiM, ginv_g_mulVec]
    have hwU : w ∈ hf.pre (gmap g (flagSpace 3 K 2)).toAddSubgroup := by
      rw [mem_pre_plane_iff, ← hgiM, hgw]
      exact hx
    have h1 := (mem_pre_plane_iff hf g _).mp ((SecA.mem_stabW.mp hkU w).mp hwU)
    rw [← hgiM, hTcf, hgw] at h1
    exact h1
  have hcommF : ∀ B ∈ stabRow2 K, ∀ x : Fin 3 → K, x 2 = 0 →
      Tc ((B : Matrix (Fin 3) (Fin 3) K) *ᵥ x) = (B : Matrix (Fin 3) (Fin 3) K) *ᵥ Tc x := by
    intro B hB x hx
    obtain ⟨B', hB', hB'c⟩ := hcommB B hB
    rw [hB'c x, hB' _ (by rw [BK2.stabRow2_mulVec_two hB]; exact hTcF x hx)]
  set y₀ := Tc ![1, 0, 0] with hy₀
  set y₁ := Tc ![0, 1, 0] with hy₁
  have hy₀2 : y₀ 2 = 0 := hTcF _ (by simp)
  have hy₁2 : y₁ 2 = 0 := hTcF _ (by simp)
  have hy₀1 : y₀ 1 = 0 := by
    have h := congrFun (hcommF _ (BK2.uSL_mem_stabRow2 1 0 0) ![1, 0, 0] (by simp)) 0
    rw [coe_uSL, uMat_mulVec, uMat_mulVec] at h
    simpa using h
  have hy₁0 : y₁ 0 = 0 := by
    have h := congrFun (hcommF _ (lowT_mem_stabRow2 1) ![0, 1, 0] (by simp)) 1
    rw [lowT_mulVec, lowT_mulVec] at h
    simpa using h
  have hσt : ∀ t : K, σ t * y₀ 0 = t * y₁ 1 := by
    intro t
    have h := congrFun (hcommF _ (BK2.uSL_mem_stabRow2 t 0 0) ![0, 1, 0] (by simp)) 0
    rw [coe_uSL, uMat_mulVec, uMat_mulVec] at h
    have e : (![(![0, 1, 0] : Fin 3 → K) 0 + t * (![0, 1, 0] : Fin 3 → K) 1 +
        0 * (![0, 1, 0] : Fin 3 → K) 2, (![0, 1, 0] : Fin 3 → K) 1 +
        0 * (![0, 1, 0] : Fin 3 → K) 2, (![0, 1, 0] : Fin 3 → K) 2] : Fin 3 → K) =
        t • ![1, 0, 0] + ![0, 1, 0] := KGNat.vec3_eq (by simp) (by simp) (by simp)
    rw [e, hTc_add, hTc_smul] at h
    simpa [← hy₀, ← hy₁, hy₁0, hy₁2] using h
  have hμ0 : y₀ 0 ≠ 0 := by
    intro h0
    have hy : y₀ = 0 := KGNat.vec3_eq (by simp [h0]) (by simp [hy₀1]) (by simp [hy₀2])
    obtain ⟨w₀, hw₀⟩ := hf.surj (gM *ᵥ ![1, 0, 0])
    have hgw : giM *ᵥ f w₀ = ![1, 0, 0] := by rw [hw₀, hgM, hgiM, ginv_g_mulVec]
    have h1 : giM *ᵥ f (k w₀) = 0 := by rw [hTcf, hgw, ← hy₀, hy]
    have h2 : f (k w₀) = 0 := by
      have := congrArg (fun v => gM *ᵥ v) h1
      simp only [Matrix.mulVec_zero, hgM, hgiM, g_ginv_mulVec] at this
      exact this
    have h3 := hkZ'' _ ((hf.ker _).mp h2)
    rw [MulAut.inv_apply_self] at h3
    have h4 := (hf.ker w₀).mpr h3
    rw [hw₀] at h4
    exact g_e0_ne_zero g h4
  have hμ : y₁ 1 = y₀ 0 := by
    have h := hσt 1
    rw [map_one, one_mul, one_mul] at h
    exact h.symm
  have hσid : ∀ t, σ t = t := fun t => by
    have h := hσt t
    rw [hμ] at h
    exact mul_right_cancel₀ hμ0 h
  set y₂ := Tc ![0, 0, 1] with hy₂
  have hlin : ∀ x : Fin 3 → K, Tc x = ![y₀ 0 * x 0 + y₂ 0 * x 2, y₀ 0 * x 1 + y₂ 1 * x 2,
      y₂ 2 * x 2] := by
    intro x
    have hx : x = x 0 • ![1, 0, 0] + x 1 • ![0, 1, 0] + x 2 • ![0, 0, 1] :=
      KGNat.vec3_eq (by simp) (by simp) (by simp)
    conv_lhs => rw [hx]
    rw [hTc_add, hTc_add, hTc_smul, hTc_smul, hTc_smul, hσid, hσid, hσid, ← hy₀, ← hy₁, ← hy₂]
    refine KGNat.vec3_eq ?_ ?_ ?_ <;> simp [hy₀1, hy₀2, hy₁0, hy₁2, hμ] <;> ring
  obtain ⟨m, hm⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (LOf L V₂ ⊔ T) ⟨r, hr⟩
  have hrm : r ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hkm : k ^ 2 ^ m = 1 := SecA.conjV_pow_eq_one V hrV hrm
  have hiter : ∀ j : ℕ, ∀ w, giM *ᵥ f ((k ^ j) w) = Tc^[j] (giM *ᵥ f w) := by
    intro j
    induction j with
    | zero => intro w; rfl
    | succ j ih =>
      intro w
      rw [pow_succ', MulAut.mul_apply, hTcf, ih, Function.iterate_succ_apply']
  have hid : ∀ x, Tc^[2 ^ m] x = x := by
    intro x
    obtain ⟨w, hw⟩ := hf.surj (gM *ᵥ x)
    have hgw : giM *ᵥ f w = x := by rw [hw, hgM, hgiM, ginv_g_mulVec]
    rw [← hgw, ← hiter, hkm, MulAut.one_apply]
  have hpow0 : ∀ j : ℕ, (Tc^[j] ![1, 0, 0]) = y₀ 0 ^ j • ![1, 0, 0] := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Function.iterate_succ_apply', ih, hlin]
      refine KGNat.vec3_eq ?_ (by simp) (by simp)
      simp only [Matrix.cons_val_zero, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_two,
        Matrix.tail_cons, Matrix.head_cons, mul_one, mul_zero, add_zero]
      ring
  have hpow2 : ∀ j : ℕ, ∀ x, (Tc^[j] x) 2 = y₂ 2 ^ j * x 2 := by
    intro j
    induction j with
    | zero => intro x; simp
    | succ j ih =>
      intro x
      rw [Function.iterate_succ_apply', hlin]
      simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      rw [ih, pow_succ]
      ring
  have hμ1 : y₀ 0 = 1 := by
    have h := congrFun ((hpow0 (2 ^ m)).symm.trans (hid _)) 0
    simp only [Pi.smul_apply, smul_eq_mul] at h
    exact eq_one_of_pow_two_pow (by simpa using h)
  have hν1 : y₂ 2 = 1 := by
    have h := hpow2 (2 ^ m) ![0, 0, 1]
    rw [hid] at h
    exact eq_one_of_pow_two_pow (by simpa using h.symm)
  refine ⟨y₂ 0, y₂ 1, ?_⟩
  refine BK2.eq_pi_of_modZ_nat hf (fun h hh z hz => SecA.autOn_fixes_cV h hh z hz)
    (K7.commV_autOn_eq_top hfl.le_normalizer hfl.commutator_eq) hkH
    (γ := specialLinearGroupEquivStatedSL 3 K (g * uSL 0 (y₂ 0) (y₂ 1) * g⁻¹)) fun w => ?_
  have e1 : f (k w) = gM *ᵥ Tc (giM *ᵥ f w) := by
    rw [← hTcf, hgM, hgiM, g_ginv_mulVec]
  rw [e1, hlin, show ((specialLinearGroupEquivStatedSL 3 K (g * uSL 0 (y₂ 0) (y₂ 1) * g⁻¹) :
      GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = ((g * uSL 0 (y₂ 0) (y₂ 1) * g⁻¹ :
        SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) from rfl, gconj_mulVec,
    coe_uSL, uMat_mulVec, hμ1, hν1, hgM, hgiM]
  congr 1
  refine KGNat.vec3_eq ?_ ?_ ?_ <;> simp

end BK6

end CFSG.Quasithin.Vol2.Ch11.SecB
