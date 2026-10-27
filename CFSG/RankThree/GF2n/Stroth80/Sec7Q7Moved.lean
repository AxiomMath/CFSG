module

public import CFSG.RankThree.GF2n.Stroth80.Sec7Q7Fixed
public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsAux
public import CFSG.RankThree.GF2n.Stroth80.Sec5OmegaConsumers
public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsComm

public section

namespace CFSG.RankThree.GF2n.Stroth80

section QBConj

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.conj_mem_inf_QB_of_le_sup_Z (hc : Ctx M Q Z B) {u : G} (huM : u ∈ M)
    (hle : conjSubgroup u B ≤ B ⊔ Z) {x : G} (hx : x ∈ Q ⊓ QB B) :
    u * x * u⁻¹ ∈ Q ⊓ QB B := by
  obtain ⟨p, hpQ, hp⟩ := hc.exists_conj_of_le_ZB (hc.conj_of_mem huM)
    (by rw [sup_comm]; exact hle)
  have hpM : p ∈ M := hc.hyp.Q_normal.1 hpQ
  obtain ⟨c, hcdef⟩ : ∃ c : G, c = p⁻¹ * u := ⟨_, rfl⟩
  have hu : u = p * c := by
    rw [hcdef]
    group
  have hcM : c ∈ M := by
    rw [hcdef]
    exact M.mul_mem (M.inv_mem hpM) huM
  have hcB : conjSubgroup c B = B := by
    rw [hcdef, conjSubgroup_mul, ← hp, ← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
  have hQBc : conjSubgroup c (QB B) = QB B := by
    rw [← QB_conj, hcB]
  have hcN : c ∈ Subgroup.normalizer (QB B : Set G) := conjSubgroup_eq_self_iff.mp hQBc
  have hcy : c * x * c⁻¹ ∈ Q ⊓ QB B :=
    Subgroup.mem_inf.mpr
      ⟨(Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hcM) x).mp (Subgroup.mem_inf.mp hx).1,
        (Subgroup.mem_normalizer_iff.mp hcN x).mp (Subgroup.mem_inf.mp hx).2⟩
  have hconj : ∀ y ∈ Q ⊓ QB B, p * y * p⁻¹ ∈ Q ⊓ QB B := by
    intro y hy
    have hZ : ⁅p, y⁆ ∈ Z := hc.hyp.toHyp79.comm_mem_V hpQ (Subgroup.mem_inf.mp hy).1
    have hZL : Z ≤ Q ⊓ QB B := le_trans le_sup_left hc.ZB_le_inf
    have e : p * y * p⁻¹ = ⁅p, y⁆ * y := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (Q ⊓ QB B).mul_mem (hZL hZ) hy
  have hkey : u * x * u⁻¹ = p * (c * x * c⁻¹) * p⁻¹ := by
    rw [hu]
    group
  rw [hkey]
  exact hconj _ hcy

theorem Ctx.comm_mem_sup_Z_of_mem_LB (hc : Ctx M Q Z B) {l w : G} (hl : l ∈ LB M Q B)
    (hw : w ∈ Q ⊓ QB B) : ⁅l, w⁆ ∈ B ⊔ Z := by
  obtain ⟨s, hs, y, hy, rfl⟩ := hc.exists_mul_of_mem_LB hl
  have hsM : s ∈ M := (Subgroup.mem_inf.mp hs).2
  have hsQB : s ∈ QB B := (Subgroup.mem_inf.mp hs).1
  have hwQ : w ∈ Q := (Subgroup.mem_inf.mp hw).1
  have hwQB : w ∈ QB B := (Subgroup.mem_inf.mp hw).2
  have h1 : ⁅y, w⁆ ∈ Z := hc.hyp.toHyp79.comm_mem_V hy hwQ
  have h2 : ⁅s, ⁅y, w⁆⁆ ∈ Z := by
    rw [commutatorElement_def]
    exact Z.mul_mem ((Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hsM) ⁅y, w⁆).mp h1)
      (Z.inv_mem h1)
  have h3 : ⁅s, w⁆ ∈ B := hc.comm_QB_le_B hsQB hwQB
  have e : ⁅s * y, w⁆ = ⁅s, ⁅y, w⁆⁆ * ⁅y, w⁆ * ⁅s, w⁆ := by
    simp only [commutatorElement_def]
    group
  have hZB : Z ≤ B ⊔ Z := le_sup_right
  have hBB : B ≤ B ⊔ Z := le_sup_left
  rw [e]
  exact (B ⊔ Z).mul_mem ((B ⊔ Z).mul_mem (hZB h2) (hZB h1)) (hBB h3)

omit [Finite G] in
theorem IsOppDecomp.exists_mul {G : Type} [Group G] {P I L₁ L₂ A₁ A₂ : Subgroup G}
    (hd : IsOppDecomp P I L₁ L₂ A₁ A₂) {x : G} (hx : x ∈ P) :
    ∃ a₁ ∈ A₁, ∃ a₂ ∈ A₂, x = a₁ * a₂ := by
  obtain ⟨hIA₁, hA₁P, hIA₂, hA₂P, hsup, -, hcomm, -, -, -⟩ := hd
  have hN : A₁ ≤ Subgroup.normalizer (A₂ : Set G) := by
    have hconj : ∀ a ∈ A₁, ∀ k ∈ A₂, a * k * a⁻¹ ∈ A₂ := by
      intro a ha k hk
      have e : a * k * a⁻¹ = ⁅a, k⁆ * k := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact A₂.mul_mem (hIA₂ (hcomm a (hA₁P ha) k (hA₂P hk))) hk
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · intro hk
      exact hconj a ha k hk
    · intro hk
      have h1 : a⁻¹ * (a * k * a⁻¹) * a⁻¹⁻¹ ∈ A₂ := hconj a⁻¹ (A₁.inv_mem ha) _ hk
      have e : a⁻¹ * (a * k * a⁻¹) * a⁻¹⁻¹ = k := by group
      rw [e] at h1
      exact h1
  have hx' : x ∈ A₁ ⊔ A₂ := by
    rw [hsup]
    exact hx
  obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hN hx'
  exact ⟨a₁, ha₁, a₂, ha₂, rfl⟩

theorem sec7CV_conj (hCV : Sec7CVStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec7Hyp hc n t) {r : G} (hr : r ∈ Rt M (LB M Q B) t) {x : G} (hxQ : x ∈ Q)
    (h : ∀ y ∈ LB M Q (conjSubgroup r B) ⊓ hc.CN t, ⁅y, x⁆ ∈ Z) :
    x ∈ Vt M (LB M Q B) B Z t := by
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hrM : r ∈ M := hc.Rt_le_M t hr
  have hrN : r ∈ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) :=
    hc.Rt_normalizes_Vt ht hr
  have hrZ : r ∈ Subgroup.normalizer (Z : Set G) := hc.hyp.Z_normal.2 hrM
  have hrQ : r ∈ Subgroup.normalizer (Q : Set G) := hc.hyp.Q_normal.2 hrM
  have hx'Q : r⁻¹ * x * r ∈ Q := by
    refine (Subgroup.mem_normalizer_iff.mp hrQ (r⁻¹ * x * r)).mpr ?_
    rw [show r * (r⁻¹ * x * r) * r⁻¹ = x by group]
    exact hxQ
  have hkey : ∀ y' ∈ LB M Q B ⊓ hc.CN t, ⁅y', r⁻¹ * x * r⁆ ∈ Z := by
    intro y' hy'
    obtain ⟨hy'L, hy'N⟩ := Subgroup.mem_inf.mp hy'
    have hy'R : y' ∈ Rt M (LB M Q B) t := (Ctx.mem_CN.mp hy'N).1
    have hyL : r * y' * r⁻¹ ∈ LB M Q (conjSubgroup r B) := by
      rw [hc.LB_conj hrM, mem_conjSubgroup,
        show r⁻¹ * (r * y' * r⁻¹) * r = y' by group]
      exact hy'L
    have hyN : r * y' * r⁻¹ ∈ hc.CN t := by
      refine Ctx.mem_CN.mpr ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hr hy'R)
        (Subgroup.inv_mem _ hr), fun v hv => ?_⟩
      have hw : r⁻¹ * v * r ∈ Vt M (LB M Q B) B Z t := by
        refine (Subgroup.mem_normalizer_iff.mp hrN (r⁻¹ * v * r)).mpr ?_
        rw [show r * (r⁻¹ * v * r) * r⁻¹ = v by group]
        exact hv
      have hc1 : ⁅y', r⁻¹ * v * r⁆ ∈ Z := (Ctx.mem_CN.mp hy'N).2 _ hw
      have e : ⁅r * y' * r⁻¹, v⁆ = r * ⁅y', r⁻¹ * v * r⁆ * r⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp hrZ _).mp hc1
    have hyx : ⁅r * y' * r⁻¹, x⁆ ∈ Z :=
      h (r * y' * r⁻¹) (Subgroup.mem_inf.mpr ⟨hyL, hyN⟩)
    have e : ⁅r * y' * r⁻¹, x⁆ = r * ⁅y', r⁻¹ * x * r⁆ * r⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e] at hyx
    exact (Subgroup.mem_normalizer_iff.mp hrZ _).mpr hyx
  have hx'V : r⁻¹ * x * r ∈ Vt M (LB M Q B) B Z t :=
    (hCV G M Q Z B hc n t hs (r⁻¹ * x * r) hx'Q).mpr hkey
  have hconj := (Subgroup.mem_normalizer_iff.mp hrN (r⁻¹ * x * r)).mp hx'V
  rwa [show r * (r⁻¹ * x * r) * r⁻¹ = x by group] at hconj

end QBConj

section PointPerp

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.ClassicalGroups.Orthogonal
open CFSG.LieType.Universal.Spin QuadraticMap
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.conj_sup_inf_QB_le_Z (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec5Hyp hc n t)
    (hnatSO : SpNat hc t ∨ OmegaNat hc t)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = Nat.card Z) {ι : Type} [Fintype ι]
    [DecidableEq ι] [Nonempty ι] {Q' : QuadraticForm K (ι → K)} {X : Subgroup (GL ι K)}
    (E : ElemMatrixIso Q' X) (hQ : (polarBilin Q').Nondegenerate)
    (h3 : 3 ≤ Module.finrank K (ι → K)) (hX : AddCommutantScalar X)
    (hnat : NaturalRep (ι := ι) K X (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z (hc.CN t))
    {r : G} (hr : r ∈ Rt M (LB M Q B) t) (hpl : HypPlane Q Z B (conjSubgroup r B) t) :
    (conjSubgroup r B ⊔ Z) ⊓ (Vt M (LB M Q B) B Z t ⊓ QB B) ≤ Z := by
  classical
  obtain ⟨φ, hφ, hker, hact⟩ := hnat
  obtain ⟨hnorm, hn, ψ, hψ⟩ := hact
  haveI := hn
  have hsing := hc.omega_singular h34 hRoot hs hnatSO hK E hQ h3 hX φ hφ ψ hψ
  obtain ⟨u, -, -, hBiff, hW, -, hpts⟩ :=
    hc.omega_points_core h34 hRoot hs hnatSO hK E hQ h3 hX φ hφ hker ψ hψ hsing
  have ht : t ∈ LB M Q B := hs.mem
  have hVR := hc.Rt_normalizes_Vt ht
  have hBV : B ≤ Vt M (LB M Q B) B Z t := hc.B_le_Vt ht
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hrM : r ∈ M := hc.Rt_le_M t hr
  have hBM : B ≤ M := fun b hb => hc.hyp.Q_normal.1 (hVQ (hBV hb))
  have hAM : conjSubgroup r B ≤ M := by
    intro a ha
    have h1 := M.mul_mem (M.mul_mem hrM (hBM (mem_conjSubgroup.mp ha))) (M.inv_mem hrM)
    rwa [show r * (r⁻¹ * a * r) * r⁻¹ = a by group] at h1
  have hAN : conjSubgroup r B ≤ Subgroup.normalizer (Z : Set G) := fun a ha =>
    hc.hyp.Z_normal.2 (hAM ha)
  intro x hx
  obtain ⟨hxA, hxVQ⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨hxV, hxQB⟩ := Subgroup.mem_inf.mp hxVQ
  obtain ⟨a, ha, z, hz, haz⟩ := exists_mul_of_mem_sup_of_le_normalizer hAN hxA
  have hb : r⁻¹ * a * r ∈ B := mem_conjSubgroup.mp ha
  have haV : a ∈ Vt M (LB M Q B) B Z t := by
    have h1 := (Subgroup.mem_normalizer_iff.mp (hVR hr) (r⁻¹ * a * r)).mp (hBV hb)
    rwa [show r * (r⁻¹ * a * r) * r⁻¹ = a by group] at h1
  have hzV : z ∈ Vt M (LB M Q B) B Z t := hZV hz
  have hxa : (⟨x, hxV⟩ : ↥(Vt M (LB M Q B) B Z t)) = ⟨a, haV⟩ * ⟨z, hzV⟩ :=
    Subtype.ext haz.symm
  have hvx : secVec ψ ⟨x, hxV⟩ = secVec ψ ⟨a, haV⟩ := by
    rw [hxa, secVec_mul, (secVec_eq_zero_iff ψ ⟨z, hzV⟩).mpr hz, add_zero]
  obtain ⟨c, hcvec⟩ :=
    (hBiff (secVec ψ ⟨r⁻¹ * a * r, hBV hb⟩)).mp ⟨⟨r⁻¹ * a * r, hBV hb⟩, hb, rfl⟩
  have hva : secVec ψ ⟨a, haV⟩ = c • ((φ ⟨r, hr⟩ : Matrix ι ι K) *ᵥ u) := by
    have e1 : secVec ψ ⟨a, haV⟩ =
        (φ ⟨r, hr⟩ : Matrix ι ι K) *ᵥ secVec ψ ⟨r⁻¹ * a * r, hBV hb⟩ :=
      hψ ⟨r, hr⟩ ⟨r⁻¹ * a * r, hBV hb⟩ ⟨a, haV⟩ (by group)
    rw [e1, hcvec, Matrix.mulVec_smul]
  have hpol : polar Q' u ((φ ⟨r, hr⟩ : Matrix ι ι K) *ᵥ u) ≠ 0 := (hpts ⟨r, hr⟩).1.mp hpl
  have hWx : polar Q' u (secVec ψ ⟨x, hxV⟩) = 0 :=
    (hW (secVec ψ ⟨x, hxV⟩)).mp ⟨⟨x, hxV⟩, Subgroup.mem_inf.mpr ⟨hxV, hxQB⟩, rfl⟩
  rw [hvx, hva, polar_smul_right_eq] at hWx
  have hc0 : c = 0 := (mul_eq_zero.mp hWx).resolve_right hpol
  have hxz : secVec ψ ⟨x, hxV⟩ = 0 := by rw [hvx, hva, hc0, zero_smul]
  exact (secVec_eq_zero_iff ψ ⟨x, hxV⟩).mp hxz

theorem sec7_conj_sup_inf_QB_le_Z (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t) {r : G}
    (hr : r ∈ Rt M (LB M Q B) t) (hpl : HypPlane Q Z B (conjSubgroup r B) t) :
    (conjSubgroup r B ⊔ Z) ⊓ (Vt M (LB M Q B) B Z t ⊓ QB B) ≤ Z := by
  have hs5 := hs.toSec5
  obtain ⟨m, hm, hpm⟩ := hs.orth
  rcases hpm with ⟨K, fK, finK, hK, hnat⟩ | ⟨K, fK, finK, hK, b, c, hirr, hnat⟩
  · have hm3 : 3 ≤ m := by
      by_contra hlt
      have : m = 2 := by omega
      subst this
      exact hs.notPlus4 ⟨K, fK, finK, hK, hnat⟩
    have hnatSO : SpNat hc t ∨ OmegaNat hc t :=
      Or.inr ⟨K, fK, finK, hK, Or.inl ⟨m, hm3, hnat⟩⟩
    haveI : CharP K 2 := sec7ctr_charP hc hK
    haveI : Nonempty (Fin m ⊕ Fin m) := ⟨Sum.inl ⟨0, by omega⟩⟩
    have h3 : 3 ≤ Module.finrank K (Fin m ⊕ Fin m → K) := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]; omega
    exact hc.conj_sup_inf_QB_le_Z h34 hRoot hs5 hnatSO hK (ElemMatrixIso.plus hm3)
      (nondegenerate_polarBilin_quadPlus m K) h3 (addCommutantScalar_statedOmegaPlus hm3) hnat
      hr hpl
  · have hnatSO : SpNat hc t ∨ OmegaNat hc t :=
      Or.inr ⟨K, fK, finK, hK, Or.inr ⟨m, b, c, hm, hirr, hnat⟩⟩
    haveI : CharP K 2 := sec7ctr_charP hc hK
    haveI : Nonempty (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) := ⟨Sum.inr (Sum.inr 0)⟩
    have h3 : 3 ≤ Module.finrank K (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum,
        Fintype.card_fin, Fintype.card_fin]; omega
    exact hc.conj_sup_inf_QB_le_Z h34 hRoot hs5 hnatSO hK (ElemMatrixIso.minus hm hirr)
      (nondegenerate_polarBilin_quadMinus_of_finite m K hirr) h3
      (addCommutantScalar_statedOmegaMinus hm hirr) hnat hr hpl

end PointPerp

section RootInvariant

open CFSG.ClassicalGroups.Orthogonal QuadraticMap

theorem submodule_le_perp_or_eq_top {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {Q' : QuadraticForm K (ι → K)} (hQ : (polarBilin Q').Nondegenerate) {u : ι → K}
    (hu : Q' u = 0) (hu0 : u ≠ 0)
    (h4 : ∃ w₁ w₂ : ι → K, polar Q' u w₁ = 0 ∧ polar Q' u w₂ = 0 ∧ polar Q' w₁ w₂ ≠ 0)
    (S : Submodule K (ι → K))
    (hS : ∀ w : ι → K, polar Q' u w = 0 → ∀ s ∈ S, eichler Q' u w s ∈ S) :
    (∀ s ∈ S, polar Q' s u = 0) ∨ S = ⊤ := by
  clear hQ hu0
  by_cases hperp : ∀ s ∈ S, polar Q' s u = 0
  · exact Or.inl hperp
  right
  push_neg at hperp
  obtain ⟨s, hsS, hsu⟩ := hperp
  have key : ∀ w : ι → K, polar Q' u w = 0 →
      polar Q' s u • w - (polar Q' s w + Q' w * polar Q' s u) • u ∈ S := by
    intro w hw
    have e : eichler Q' u w s - s =
        polar Q' s u • w - (polar Q' s w + Q' w * polar Q' s u) • u := by
      rw [eichler_apply hu hw]
      module
    rw [← e]
    exact S.sub_mem (hS w hw s hsS) hsS
  obtain ⟨w₁, w₂, hw₁, hw₂, hw₁₂⟩ := h4
  have hadd : polar Q' u (w₁ + w₂) = 0 := by
    rw [polar_add_right, hw₁, hw₂, add_zero]
  have hcross : (polar Q' s u * polar Q' w₁ w₂) • u ∈ S := by
    have e : (polar Q' s u * polar Q' w₁ w₂) • u =
        (polar Q' s u • w₁ - (polar Q' s w₁ + Q' w₁ * polar Q' s u) • u) +
          (polar Q' s u • w₂ - (polar Q' s w₂ + Q' w₂ * polar Q' s u) • u) -
        (polar Q' s u • (w₁ + w₂) -
          (polar Q' s (w₁ + w₂) + Q' (w₁ + w₂) * polar Q' s u) • u) := by
      rw [polar_add_right, QuadraticMap.map_add Q' w₁ w₂]
      module
    rw [e]
    exact S.sub_mem (S.add_mem (key w₁ hw₁) (key w₂ hw₂)) (key (w₁ + w₂) hadd)
  have hu_mem : u ∈ S := by
    have h := S.smul_mem (polar Q' s u * polar Q' w₁ w₂)⁻¹ hcross
    rwa [smul_smul, inv_mul_cancel₀ (mul_ne_zero hsu hw₁₂), one_smul] at h
  have hperp_mem : ∀ w : ι → K, polar Q' u w = 0 → w ∈ S := by
    intro w hw
    have h := S.add_mem (key w hw) (S.smul_mem (polar Q' s w + Q' w * polar Q' s u) hu_mem)
    rw [sub_add_cancel] at h
    have h' := S.smul_mem (polar Q' s u)⁻¹ h
    rwa [smul_smul, inv_mul_cancel₀ hsu, one_smul] at h'
  refine Submodule.eq_top_iff'.2 fun y => ?_
  have hw : polar Q' u (y - (polar Q' y u * (polar Q' s u)⁻¹) • s) = 0 := by
    rw [polar_comm, polar_sub_left, polar_smul_left_eq, inv_mul_cancel_right₀ hsu, sub_self]
  have hy := S.add_mem (hperp_mem _ hw) (S.smul_mem (polar Q' y u * (polar Q' s u)⁻¹) hsS)
  rwa [sub_add_cancel] at hy

theorem exists_polar_perp_pair {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {Q' : QuadraticForm K (ι → K)} (hQ : (polarBilin Q').Nondegenerate)
    (h3 : 3 ≤ Module.finrank K (ι → K)) {u : ι → K} (hu0 : u ≠ 0) :
    ∃ w₁ w₂ : ι → K, polar Q' u w₁ = 0 ∧ polar Q' u w₂ = 0 ∧ polar Q' w₁ w₂ ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨y₀, hy₀⟩ := exists_polar_eq_one_of_ne_zero hQ hu0
  have hker : LinearMap.ker (polarBilin Q' u) ≤ Submodule.span K {u} := by
    intro w hw
    rw [LinearMap.mem_ker, polarBilin_apply_apply] at hw
    have h := eq_smul_of_polar_perp hQ hy₀ (fun w' hw' => hcon w' w hw' hw)
    rw [Submodule.mem_span_singleton]
    exact ⟨polar Q' y₀ w, h.symm⟩
  have hrange : Module.finrank K (LinearMap.range (polarBilin Q' u)) ≤ 1 := by
    have h1 := Submodule.finrank_le (LinearMap.range (polarBilin Q' u))
    rwa [Module.finrank_self] at h1
  have hker1 : Module.finrank K (LinearMap.ker (polarBilin Q' u)) ≤ 1 := by
    have h1 := Submodule.finrank_mono hker
    rwa [finrank_span_singleton hu0] at h1
  have hrn := LinearMap.finrank_range_add_finrank_ker (polarBilin Q' u)
  omega

end RootInvariant

section KernelScalar
open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.exists_smul_mem_inf_conj (hc : Ctx M Q Z B) {t : G} {K : Type} [Field K] [Finite K]
    {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} (h : GlobalModelData M Q Z γ M₀) {g : G}
    (hg : g ∈ M) (c : K) {v : G}
    (hv : v ∈ Vt M (LB M Q B) B Z t ⊓ conjSubgroup g (Vt M (LB M Q B) B Z t)) :
    ∃ w ∈ Vt M (LB M Q B) B Z t ⊓ conjSubgroup g (Vt M (LB M Q B) B Z t),
      M₀.π w = c • M₀.π v := by
  set V := Vt M (LB M Q B) B Z t
  obtain ⟨hvV, hvg⟩ := Subgroup.mem_inf.mp hv
  have hVQ : V ≤ Q := hc.Vt_le_Q t
  have hZV : Z ≤ V := sec39_Z_le_Vt
  obtain ⟨σ, _, T, hT, hTπ, _, _⟩ := h.act g hg
  have hv₀V : g⁻¹ * v * g ∈ V := mem_conjSubgroup.mp hvg
  have hv₀Q : g⁻¹ * v * g ∈ Q := hVQ hv₀V
  have hπv : M₀.π v = T (M₀.π (g⁻¹ * v * g)) := by
    have h1 := hTπ _ hv₀Q
    rwa [show g * (g⁻¹ * v * g) * g⁻¹ = v by group] at h1
  obtain ⟨w, hwV, hwQ, hwπ⟩ := (M₀.mem_img).mp
    (hc.smul_mem_img_Vt h t c (M₀.pi_mem_img hvV (hVQ hvV)))
  have hc' : T (σ.symm c • M₀.π (g⁻¹ * v * g)) = c • M₀.π v := by
    rw [hT, RingEquiv.apply_symm_apply, hπv]
  obtain ⟨v₁, hv₁V, hv₁Q, hv₁π⟩ := (M₀.mem_img).mp
    (hc.smul_mem_img_Vt h t (σ.symm c) (M₀.pi_mem_img hv₀V hv₀Q))
  have hw'Q : g * v₁ * g⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hg) v₁).mp hv₁Q
  have hw'π : M₀.π (g * v₁ * g⁻¹) = c • M₀.π v := by
    rw [hTπ v₁ hv₁Q, hv₁π, hc']
  have hw'V : g * v₁ * g⁻¹ ∈ V := by
    have hz : w⁻¹ * (g * v₁ * g⁻¹) ∈ Z :=
      (M₀.pi_eq_iff hwQ hw'Q).mp (hwπ.trans hw'π.symm)
    have h2 := V.mul_mem hwV (hZV hz)
    rwa [show w * (w⁻¹ * (g * v₁ * g⁻¹)) = g * v₁ * g⁻¹ by group] at h2
  have hw'g : g * v₁ * g⁻¹ ∈ conjSubgroup g V :=
    mem_conjSubgroup.mpr (by rw [show g⁻¹ * (g * v₁ * g⁻¹) * g = v₁ by group]; exact hv₁V)
  exact ⟨g * v₁ * g⁻¹, Subgroup.mem_inf.mpr ⟨hw'V, hw'g⟩, hw'π⟩

end KernelScalar

section Assembly

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

@[expose] def Sec7Q7KernelStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ∀ g ∈ M, g ∈ Subgroup.normalizer (LB M Q B : Set G) →
    Vt M (LB M Q B) B Z t ⊓ conjSubgroup g (Vt M (LB M Q B) B Z t) ≤ QB B ∨
      conjSubgroup g (Vt M (LB M Q B) B Z t) = Vt M (LB M Q B) B Z t

omit [Finite G] in
theorem comm_mul_right_expand (a b c : G) : ⁅a, b * c⁆ = ⁅a, b⁆ * (b * ⁅a, c⁆ * b⁻¹) := by
  simp only [commutatorElement_def]
  group

theorem sec7Q7Moved_of_kernel (hA : Sec7AExistsStatement) (h34 : Stroth34Statement)
    (hRoot : Stroth310RootStatement) (h52a : Stroth52aStatement) (h52b : Stroth52bStatement)
    (hCV : Sec7CVStatement) (hKer : Sec7Q7KernelStatement) : Sec7Q7MovedStatement := by
  intro G _ _ M Q Z B hc n t hs g hg hgN hVW hNn hmoved
  obtain ⟨v₁, hv₁, l₁, hl₁, hmove⟩ := hmoved
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hRM : Rt M (LB M Q B) t ≤ M := hc.Rt_le_M t
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hWQ : Wt Q (Vt M (LB M Q B) B Z t) ≤ Q := inf_le_left
  have hZQB : Z ≤ QB B := hc.Z_le_QB.1
  have hVn : ∀ y ∈ Rt M (LB M Q B) t, ∀ v ∈ Vt M (LB M Q B) B Z t,
      y * v * y⁻¹ ∈ Vt M (LB M Q B) B Z t := fun y hy v hv =>
    (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht hy) v).mp hv
  have hWN := sec7_N_comm_W_le_V h52a hA hc hs
  rcases hKer G M Q Z B hc n t hs g hg hgN with hK | hVeq
  ·
    obtain ⟨r, hr⟩ := hA G M Q Z B hc n t hs
    have hrM : r ∈ M := hRM hr.mem
    have hd := h52b G M Q Z B hc n t hs.toSec5 hs.omegaNat r hr.mem hr.plane
      (conjSubgroup r B) (LB M Q B) (LB M Q (conjSubgroup r B)) (Vt M (LB M Q B) B Z t)
      (Wt Q (Vt M (LB M Q B) B Z t)) rfl rfl rfl rfl rfl
    have hVW' : Vt M (LB M Q B) B Z t ≤ Wt Q (Vt M (LB M Q B) B Z t) := hd.1.trans hd.2.1
    have hWcent : ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ∀ v ∈ Vt M (LB M Q B) B Z t,
        w * v * w⁻¹ = v := fun w hw v hv => by
      have := Subgroup.mem_centralizer_iff.mp hw.2 v hv
      rw [← this]
      group
    obtain ⟨a₁, ha₁, a₂, ha₂, hva⟩ := hd.exists_mul (hVW hv₁)
    have ha₁W : a₁ ∈ Wt Q (Vt M (LB M Q B) B Z t) := hd.2.1 ha₁
    have ha₂W : a₂ ∈ Wt Q (Vt M (LB M Q B) B Z t) := hd.2.2.2.1 ha₂
    have ha₂V : a₂ ∉ Vt M (LB M Q B) B Z t := by
      intro h
      have h1 : v₁ ∈ (QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔ Vt M (LB M Q B) B Z t := by
        rw [hva]
        exact Subgroup.mul_mem _ ha₁ (hd.1 h)
      exact hmove ((hd.2.2.2.2.2.2.2.2.1 v₁ (hVW hv₁)).mp h1 l₁ hl₁)
    have hVnorm : ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t),
        w ∈ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) := fun w hw =>
      Subgroup.centralizer_le_normalizer (Vt M (LB M Q B) B Z t : Set G) hw.2
    have hmain : ∀ y ∈ LB M Q (conjSubgroup r B) ⊓ hc.CN t, ⁅y, a₂⁆ ∈ Z := by
      intro y hy
      obtain ⟨hyLA, hyN⟩ := Subgroup.mem_inf.mp hy
      have hyR : y ∈ Rt M (LB M Q B) t := (Ctx.mem_CN.mp hyN).1
      have hyM : y ∈ M := hRM hyR
      have hyV : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅y, v⁆ ∈ Z := (Ctx.mem_CN.mp hyN).2
      have hyW : ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅y, w⁆ ∈ Vt M (LB M Q B) B Z t :=
        fun w hw => hWN y hyN w hw
      have hBle : conjSubgroup y B ≤ B ⊔ Z := by
        intro x hx
        have hb : y⁻¹ * x * y ∈ B := mem_conjSubgroup.mp hx
        have hbV : y⁻¹ * x * y ∈ Vt M (LB M Q B) B Z t := hc.B_le_Vt ht hb
        have e : x = ⁅y, y⁻¹ * x * y⁆ * (y⁻¹ * x * y) := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (hyV _ hbV)) (Subgroup.mem_sup_left hb)
      have hPres : ∀ q ∈ Q ⊓ QB B, y * q * y⁻¹ ∈ Q ⊓ QB B :=
        fun q hq => hc.conj_mem_inf_QB_of_le_sup_Z hyM hBle hq
      obtain ⟨q₀, hq₀, v₀, hv₀, hdec₁⟩ := exists_mul_of_mem_sup_of_le_normalizer
        (H := QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) (K := Vt M (LB M Q B) B Z t)
        (fun w hw => hVnorm w hw.2) ha₁
      have hc₁ : ⁅y, a₁⁆ ∈ Vt M (LB M Q B) B Z t ⊓ QB B := by
        rw [← hdec₁, comm_mul_right_expand]
        have h1 : ⁅y, q₀⁆ ∈ Vt M (LB M Q B) B Z t := hyW q₀ hq₀.2
        rw [hWcent q₀ hq₀.2 _ (hZV (hyV _ hv₀))]
        refine Subgroup.mem_inf.mpr ⟨(Vt M (LB M Q B) B Z t).mul_mem h1 (hZV (hyV _ hv₀)), ?_⟩
        refine (QB B).mul_mem ?_ (hZQB (hyV _ hv₀))
        have hq₀' : y * q₀ * y⁻¹ ∈ Q ⊓ QB B := hPres q₀ ⟨hWQ hq₀.2, hq₀.1⟩
        rw [commutatorElement_def]
        exact (QB B).mul_mem hq₀'.2 ((QB B).inv_mem hq₀.1)
      have hcV : ⁅y, v₁⁆ ∈ Vt M (LB M Q B) B Z t := hyW v₁ (hVW hv₁)
      have hcV' : ⁅y, v₁⁆ ∈ conjSubgroup g (Vt M (LB M Q B) B Z t) := by
        have h1 : y * v₁ * y⁻¹ ∈ conjSubgroup g (Vt M (LB M Q B) B Z t) :=
          (Subgroup.mem_normalizer_iff.mp (hNn y hyN) v₁).mp hv₁
        rw [commutatorElement_def]
        exact (conjSubgroup g (Vt M (LB M Q B) B Z t)).mul_mem h1
          ((conjSubgroup g (Vt M (LB M Q B) B Z t)).inv_mem hv₁)
      have hcQB : ⁅y, v₁⁆ ∈ QB B := hK (Subgroup.mem_inf.mpr ⟨hcV, hcV'⟩)
      have hid : ⁅y, v₁⁆ = ⁅y, a₁⁆ * ⁅y, a₂⁆ := by
        rw [hva, comm_mul_right_expand, hWcent a₁ ha₁W _ (hyW a₂ ha₂W)]
      have hx : ⁅y, a₂⁆ ∈ Vt M (LB M Q B) B Z t ⊓ QB B := by
        have e : ⁅y, a₂⁆ = ⁅y, a₁⁆⁻¹ * ⁅y, v₁⁆ := by
          rw [hid, inv_mul_cancel_left]
        rw [e]
        exact Subgroup.mem_inf.mpr
          ⟨(Vt M (LB M Q B) B Z t).mul_mem ((Vt M (LB M Q B) B Z t).inv_mem
            (Subgroup.mem_inf.mp hc₁).1) hcV,
          (QB B).mul_mem ((QB B).inv_mem (Subgroup.mem_inf.mp hc₁).2) hcQB⟩
      obtain ⟨q₀', hq₀', v₀', hv₀', hdec₂⟩ := exists_mul_of_mem_sup_of_le_normalizer
        (H := QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t))
        (K := Vt M (LB M Q B) B Z t) (fun w hw => hVnorm w hw.2) ha₂
      have hxA : ⁅y, a₂⁆ ∈ conjSubgroup r B ⊔ Z := by
        rw [← hdec₂, comm_mul_right_expand]
        rw [hWcent q₀' hq₀'.2 _ (hZV (hyV _ hv₀'))]
        refine Subgroup.mul_mem _ ?_ (Subgroup.mem_sup_right (hyV _ hv₀'))
        exact (hc.conj_of_mem hrM).comm_mem_sup_Z_of_mem_LB hyLA ⟨hWQ hq₀'.2, hq₀'.1⟩
      exact sec7_conj_sup_inf_QB_le_Z h34 hRoot hc hs hr.mem hr.plane
        (Subgroup.mem_inf.mpr ⟨hxA, hx⟩)
    exact ha₂V (sec7CV_conj hCV hc hs hr.mem (hWQ ha₂W) hmain)
  · have hv₁V : v₁ ∈ Vt M (LB M Q B) B Z t := by rw [← hVeq]; exact hv₁
    apply hmove
    rw [commutatorElement_def]
    exact (Vt M (LB M Q B) B Z t).mul_mem (hVn l₁ (hLR hl₁) v₁ hv₁V)
      ((Vt M (LB M Q B) B Z t).inv_mem hv₁V)

theorem sec7Q7_of_kernel (hA : Sec7AExistsStatement) (h34 : Stroth34Statement)
    (hRoot : Stroth310RootStatement) (h52a : Stroth52aStatement) (h52b : Stroth52bStatement)
    (hCV : Sec7CVStatement) (hKer : Sec7Q7KernelStatement) : Sec7Q7Statement :=
  sec7Q7_of_moved hA (sec5NatPointsOmega_of h34 hRoot) hCV
    (sec7Q7Moved_of_kernel hA h34 hRoot h52a h52b hCV hKer)

end Assembly

section KernelOmega

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Open.StatedAPI
  CFSG.ClassicalGroups.Symplectic CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  QuadraticMap
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.kernel_omega (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec5Hyp hc n t) (hnatSO : SpNat hc t ∨ OmegaNat hc t)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = Nat.card Z) {ι : Type} [Fintype ι]
    [DecidableEq ι] [Nonempty ι] {Q' : QuadraticForm K (ι → K)} {X : Subgroup (GL ι K)}
    (E : ElemMatrixIso Q' X) (hQ : (polarBilin Q').Nondegenerate)
    (h3 : 3 ≤ Module.finrank K (ι → K)) (hX : AddCommutantScalar X)
    (hnat : NaturalRep (ι := ι) K X (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z (hc.CN t))
    {g : G} (hg : g ∈ M) (hgN : g ∈ Subgroup.normalizer (LB M Q B : Set G)) :
    Vt M (LB M Q B) B Z t ⊓ conjSubgroup g (Vt M (LB M Q B) B Z t) ≤ QB B ∨
      conjSubgroup g (Vt M (LB M Q B) B Z t) = Vt M (LB M Q B) B Z t := by
  classical
  obtain ⟨φ, hφ, hker, hact⟩ := hnat
  obtain ⟨hnorm, hn, ψ, hψ⟩ := hact
  haveI := hn
  have hsing := hc.omega_singular h34 hRoot hs hnatSO hK E hQ h3 hX φ hφ ψ hψ
  obtain ⟨u, hQu, hu0, -, hW, hL, -⟩ :=
    hc.omega_points_core h34 hRoot hs hnatSO hK E hQ h3 hX φ hφ hker ψ hψ hsing
  have ht : t ∈ LB M Q B := hs.mem
  obtain ⟨nn, γ, M₀, hglob, θ, hθ⟩ := hc.exists_globalRingEquiv ht hK hX φ hφ ψ hψ
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hZV' : Z ≤ conjSubgroup g (Vt M (LB M Q B) B Z t) := hc.Z_le_conjSubgroup hZV hg
  have hZQB : Z ≤ QB B := hc.Z_le_QB.1
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht
  have hVR := hc.Rt_normalizes_Vt ht
  have hLn' : ∀ l ∈ LB M Q B, g⁻¹ * l * g ∈ LB M Q B := fun l hl => by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgN) l).mp hl
    simpa using this
  let S : Submodule K (ι → K) :=
    { carrier := {x | ∃ k : ↥(Vt M (LB M Q B) B Z t),
        (k : G) ∈ conjSubgroup g (Vt M (LB M Q B) B Z t) ∧ secVec ψ k = x}
      add_mem' := by
        rintro _ _ ⟨k₁, hk₁, rfl⟩ ⟨k₂, hk₂, rfl⟩
        exact ⟨k₁ * k₂, (conjSubgroup g (Vt M (LB M Q B) B Z t)).mul_mem hk₁ hk₂,
          (secVec_mul ψ k₁ k₂)⟩
      zero_mem' := ⟨1, (conjSubgroup g (Vt M (LB M Q B) B Z t)).one_mem,
        (secVec_eq_zero_iff ψ 1).mpr (by simpa using Z.one_mem)⟩
      smul_mem' := by
        rintro c _ ⟨k, hk, rfl⟩
        obtain ⟨w, hw, hπ⟩ := hc.exists_smul_mem_inf_conj hglob hg (θ.symm c)
          (Subgroup.mem_inf.mpr ⟨k.2, hk⟩)
        refine ⟨⟨w, (Subgroup.mem_inf.mp hw).1⟩, (Subgroup.mem_inf.mp hw).2, ?_⟩
        have key := hθ (θ.symm c) k ⟨w, (Subgroup.mem_inf.mp hw).1⟩ hπ
        rw [RingEquiv.apply_symm_apply] at key
        exact key }
  have hS : ∀ w : ι → K, polar Q' u w = 0 → ∀ s ∈ S, eichler Q' u w s ∈ S := by
    intro w hw s hs'
    obtain ⟨k, hk, rfl⟩ := hs'
    obtain ⟨l, hlL, hlA⟩ := exists_mem_act_eq_eichler E φ hL hw
    have hlR : (l : G) ∈ Rt M (LB M Q B) t := l.2
    have hlM : (l : G) ∈ M := hc.Rt_le_M t hlR
    have hkV : (l : G) * (k : G) * (l : G)⁻¹ ∈ Vt M (LB M Q B) B Z t :=
      (Subgroup.mem_normalizer_iff.mp (hVR hlR) (k : G)).mp k.2
    have hkV' : (l : G) * (k : G) * (l : G)⁻¹ ∈ conjSubgroup g (Vt M (LB M Q B) B Z t) := by
      rw [mem_conjSubgroup] at hk ⊢
      have h1 := (Subgroup.mem_normalizer_iff.mp (hVR (hLR (hLn' l hlL))) (g⁻¹ * (k : G) * g)).mp hk
      have e : g⁻¹ * ((l : G) * (k : G) * (l : G)⁻¹) * g =
          g⁻¹ * (l : G) * g * (g⁻¹ * (k : G) * g) * (g⁻¹ * (l : G) * g)⁻¹ := by group
      rw [e]
      exact h1
    refine ⟨⟨(l : G) * (k : G) * (l : G)⁻¹, hkV⟩, hkV', ?_⟩
    have h1 := hψ l k ⟨(l : G) * (k : G) * (l : G)⁻¹, hkV⟩ rfl
    have h2 : secVec ψ ⟨(l : G) * (k : G) * (l : G)⁻¹, hkV⟩ = (φ l : Matrix ι ι K) *ᵥ secVec ψ k :=
      h1
    rw [h2, hlA]
  have hdich := submodule_le_perp_or_eq_top hQ hQu hu0 (exists_polar_perp_pair hQ h3 hu0) S hS
  rcases hdich with hperp | htop
  · left
    intro x hx
    obtain ⟨hxV, hxV'⟩ := Subgroup.mem_inf.mp hx
    have hmem : secVec ψ ⟨x, hxV⟩ ∈ S := ⟨⟨x, hxV⟩, hxV', rfl⟩
    have h0 : polar Q' u (secVec ψ ⟨x, hxV⟩) = 0 := by
      rw [polar_comm]
      exact hperp _ hmem
    obtain ⟨w, hwQB, hwx⟩ := (hW (secVec ψ ⟨x, hxV⟩)).mpr h0
    have hz : (w : G) * x⁻¹ ∈ Z := (secVec_eq_iff ψ w ⟨x, hxV⟩).mp hwx
    have e : x = ((w : G) * x⁻¹)⁻¹ * (w : G) := by group
    rw [e]
    exact (QB B).mul_mem ((QB B).inv_mem (hZQB hz)) (Subgroup.mem_inf.mp hwQB).2
  · right
    have hle : Vt M (LB M Q B) B Z t ≤ conjSubgroup g (Vt M (LB M Q B) B Z t) := by
      intro v hv
      have hmem : secVec ψ ⟨v, hv⟩ ∈ S := by rw [htop]; exact Submodule.mem_top
      obtain ⟨k, hk, hkv⟩ := hmem
      have hz : (k : G) * v⁻¹ ∈ Z := (secVec_eq_iff ψ k ⟨v, hv⟩).mp hkv
      have e : v = ((k : G) * v⁻¹)⁻¹ * (k : G) := by group
      rw [e]
      exact (conjSubgroup g (Vt M (LB M Q B) B Z t)).mul_mem
        ((conjSubgroup g (Vt M (LB M Q B) B Z t)).inv_mem (hZV' hz)) hk
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSubgroup])).symm

theorem sec7Q7Kernel_of_inputs (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement) :
    Sec7Q7KernelStatement := by
  intro G _ _ M Q Z B hc n t hs g hg hgN
  have hs5 := hs.toSec5
  obtain ⟨m, hm, hpm⟩ := hs.orth
  rcases hpm with ⟨K, fK, finK, hK, hnat⟩ | ⟨K, fK, finK, hK, b, c, hirr, hnat⟩
  · have hm3 : 3 ≤ m := by
      by_contra hlt
      have : m = 2 := by omega
      subst this
      exact hs.notPlus4 ⟨K, fK, finK, hK, hnat⟩
    have hnatSO : SpNat hc t ∨ OmegaNat hc t :=
      Or.inr ⟨K, fK, finK, hK, Or.inl ⟨m, hm3, hnat⟩⟩
    haveI : CharP K 2 := sec7ctr_charP hc hK
    haveI : Nonempty (Fin m ⊕ Fin m) := ⟨Sum.inl ⟨0, by omega⟩⟩
    have h3 : 3 ≤ Module.finrank K (Fin m ⊕ Fin m → K) := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]; omega
    exact hc.kernel_omega h34 hRoot hs5 hnatSO hK (ElemMatrixIso.plus hm3)
      (nondegenerate_polarBilin_quadPlus m K) h3 (addCommutantScalar_statedOmegaPlus hm3) hnat
      hg hgN
  · have hnatSO : SpNat hc t ∨ OmegaNat hc t :=
      Or.inr ⟨K, fK, finK, hK, Or.inr ⟨m, b, c, hm, hirr, hnat⟩⟩
    haveI : CharP K 2 := sec7ctr_charP hc hK
    haveI : Nonempty (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) := ⟨Sum.inr (Sum.inr 0)⟩
    have h3 : 3 ≤ Module.finrank K (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum,
        Fintype.card_fin, Fintype.card_fin]; omega
    exact hc.kernel_omega h34 hRoot hs5 hnatSO hK (ElemMatrixIso.minus hm hirr)
      (nondegenerate_polarBilin_quadMinus_of_finite m K hirr) h3
      (addCommutantScalar_statedOmegaMinus hm hirr) hnat hg hgN

end KernelOmega

end CFSG.RankThree.GF2n.Stroth80
