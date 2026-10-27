module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

namespace CFSG.StandardType

namespace NoOffRest

open Module

section Dual

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

@[expose] def eigSp (T : V →ₗ[K] V) (c : K) : Submodule K V :=
  LinearMap.ker (T - c • LinearMap.id)

theorem mem_eigSp {T : V →ₗ[K] V} {c : K} {x : V} : x ∈ eigSp T c ↔ T x = c • x := by
  rw [eigSp, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    sub_eq_zero]

@[expose] def fixSp (U : V →ₗ[K] V) : Submodule K V :=
  LinearMap.ker (U - LinearMap.id)

theorem mem_fixSp {U : V →ₗ[K] V} {x : V} : x ∈ fixSp U ↔ U x = x := by
  rw [fixSp, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]

variable {T U : V →ₗ[K] V}

theorem add_smul_mem_eigSp (hT2 : ∀ x, T (T x) = -x) {lam : K} (hlam : lam * lam = -1)
    (x : V) : T x + lam • x ∈ eigSp T lam := by
  rw [mem_eigSp, map_add, map_smul, hT2, smul_add, smul_smul, hlam, neg_one_smul, add_comm]

theorem sub_smul_mem_eigSp (hT2 : ∀ x, T (T x) = -x) {lam : K} (hlam : lam * lam = -1)
    (x : V) : T x - lam • x ∈ eigSp T (-lam) := by
  rw [mem_eigSp, map_sub, map_smul, hT2, smul_sub, smul_smul, neg_mul, hlam, neg_neg, one_smul,
    neg_smul]
  abel

theorem two_mul_ne_zero {lam : K} (hlam : lam * lam = -1) (h2 : (2 : K) ≠ 0) :
    (2 : K) * lam ≠ 0 := by
  refine mul_ne_zero h2 fun h0 => ?_
  rw [h0, mul_zero] at hlam
  exact one_ne_zero (neg_eq_zero.mp hlam.symm)

theorem one_ne_neg_one (h2 : (2 : K) ≠ 0) : (1 : K) ≠ -1 := by
  intro h
  apply h2
  calc (2 : K) = 1 - -1 := by ring
    _ = 0 := by rw [← h, sub_self]

theorem eq_decomp {lam : K} (hlam : lam * lam = -1) (h2 : (2 : K) ≠ 0) (x : V) :
    x = (2 * lam)⁻¹ • (T x + lam • x) + (2 * lam)⁻¹ • -(T x - lam • x) := by
  have h3 : (T x + lam • x) + -(T x - lam • x) = (2 * lam) • x := by
    rw [mul_smul, two_smul]
    abel
  rw [← smul_add, h3, inv_smul_smul₀ (two_mul_ne_zero hlam h2)]

theorem eig_sup_eq_top (hT2 : ∀ x, T (T x) = -x) {lam : K} (hlam : lam * lam = -1)
    (h2 : (2 : K) ≠ 0) : eigSp T lam ⊔ eigSp T (-lam) = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  rw [eq_decomp hlam h2 x]
  exact Submodule.add_mem_sup (Submodule.smul_mem _ _ (add_smul_mem_eigSp hT2 hlam x))
    (Submodule.smul_mem _ _ (Submodule.neg_mem _ (sub_smul_mem_eigSp hT2 hlam x)))

theorem eig_inf_eq_bot {lam : K} (hlam : lam * lam = -1) (h2 : (2 : K) ≠ 0) :
    eigSp T lam ⊓ eigSp T (-lam) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx1, hx2⟩
  rw [SetLike.mem_coe, mem_eigSp] at hx1 hx2
  have h : (2 * lam) • x = 0 := by
    calc (2 * lam) • x = lam • x - (-lam) • x := by
          rw [mul_smul, two_smul, neg_smul, sub_neg_eq_add]
      _ = T x - T x := by rw [← hx1, ← hx2]
      _ = 0 := sub_self _
  exact (Submodule.mem_bot K).mpr ((smul_eq_zero.mp h).resolve_left (two_mul_ne_zero hlam h2))

theorem eig_isotropic {β : LinearMap.BilinForm K V} (hT : ∀ x y, β (T x) (T y) = β x y)
    {c : K} (hc : c * c ≠ 1) {x y : V} (hx : x ∈ eigSp T c) (hy : y ∈ eigSp T c) :
    β x y = 0 := by
  rw [mem_eigSp] at hx hy
  have h := hT x y
  rw [hx, hy, LinearMap.map_smul₂, map_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc] at h
  have h' : (c * c - 1) * β x y = 0 := by rw [sub_mul, h, one_mul, sub_self]
  exact (mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr hc)

theorem map_mem_eigSp (hTU : ∀ x, T (U x) = U (T x)) {c : K} {x : V} (hx : x ∈ eigSp T c) :
    U x ∈ eigSp T c := by
  rw [mem_eigSp] at hx ⊢
  rw [hTU, hx, map_smul]

theorem injective_of_isometry {β : LinearMap.BilinForm K V} (hβ : β.Nondegenerate)
    (hU : ∀ x y, β (U x) (U y) = β x y) : Function.Injective U := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  refine (Submodule.mem_bot K).mpr (hβ.1 x fun y => ?_)
  rw [← hU, hx, LinearMap.map_zero₂]

end Dual

section Main

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {β : LinearMap.BilinForm K V} {T U : V →ₗ[K] V}

structure DualHyp (β : LinearMap.BilinForm K V) (T U : V →ₗ[K] V) (lam : K) : Prop where
  nondeg : β.Nondegenerate
  isomT : ∀ x y, β (T x) (T y) = β x y
  isomU : ∀ x y, β (U x) (U y) = β x y
  comm : ∀ x, T (U x) = U (T x)
  sq : ∀ x, T (T x) = -x
  lam_sq : lam * lam = -1
  two_ne : (2 : K) ≠ 0

omit [FiniteDimensional K V] in
theorem DualHyp.lam_ne {lam : K} (h : DualHyp β T U lam) : lam * lam ≠ 1 := by
  rw [h.lam_sq]
  exact (one_ne_neg_one h.two_ne).symm

omit [FiniteDimensional K V] in
theorem DualHyp.neg_lam_ne {lam : K} (h : DualHyp β T U lam) : -lam * -lam ≠ 1 := by
  rw [neg_mul_neg]
  exact h.lam_ne

omit [FiniteDimensional K V] in
theorem DualHyp.eq_zero {lam : K} (h : DualHyp β T U lam) {z : V}
    (h1 : ∀ v ∈ eigSp T lam, β v z = 0) (h2 : ∀ v ∈ eigSp T (-lam), β v z = 0) : z = 0 := by
  refine h.nondeg.2 z fun v => ?_
  have hv : v ∈ eigSp T lam ⊔ eigSp T (-lam) := by
    rw [eig_sup_eq_top h.sq h.lam_sq h.two_ne]
    exact Submodule.mem_top
  obtain ⟨e, he, e', he', rfl⟩ := Submodule.mem_sup.mp hv
  rw [LinearMap.map_add₂, h1 e he, h2 e' he', add_zero]

theorem DualHyp.finrank_eq {lam : K} (h : DualHyp β T U lam) :
    finrank K V = finrank K (eigSp T lam) + finrank K (eigSp T (-lam)) := by
  have d := Submodule.finrank_sup_add_finrank_inf_eq (eigSp T lam) (eigSp T (-lam))
  rw [eig_sup_eq_top h.sq h.lam_sq h.two_ne, eig_inf_eq_bot h.lam_sq h.two_ne, finrank_bot,
    add_zero, finrank_top] at d
  exact d

theorem DualHyp.finrank_eig_eq {lam : K} (h : DualHyp β T U lam) :
    finrank K (eigSp T lam) = finrank K (eigSp T (-lam)) := by
  have hoE : β.orthogonal (eigSp T lam) = eigSp T lam := by
    apply le_antisymm
    · intro y hy
      have hy' : y ∈ eigSp T lam ⊔ eigSp T (-lam) := by
        rw [eig_sup_eq_top h.sq h.lam_sq h.two_ne]
        exact Submodule.mem_top
      obtain ⟨e, he, e', he', rfl⟩ := Submodule.mem_sup.mp hy'
      have he'0 : e' = 0 := by
        refine h.eq_zero (fun v hv => ?_) fun v hv => eig_isotropic h.isomT h.neg_lam_ne hv he'
        have h1 := (LinearMap.BilinForm.mem_orthogonal_iff.mp hy) v hv
        rw [map_add, eig_isotropic h.isomT h.lam_ne hv he, zero_add] at h1
        exact h1
      rw [he'0, add_zero]
      exact he
    · exact fun e he => LinearMap.BilinForm.mem_orthogonal_iff.mpr fun n hn =>
        eig_isotropic h.isomT h.lam_ne hn he
  have d := LinearMap.BilinForm.finrank_orthogonal h.nondeg (eigSp T lam)
  rw [hoE] at d
  have d7 := h.finrank_eq
  omega

theorem DualHyp.finrank_eig_fix_eq {lam : K} (h : DualHyp β T U lam) :
    finrank K ↥(eigSp T lam ⊓ fixSp U) = finrank K ↥(eigSp T (-lam) ⊓ fixSp U) := by
  set E := eigSp T lam with hE
  set E' := eigSp T (-lam) with hE'
  set F := fixSp U with hF
  have hsup : E ⊔ E' = ⊤ := eig_sup_eq_top h.sq h.lam_sq h.two_ne
  have hinf : E ⊓ E' = ⊥ := eig_inf_eq_bot h.lam_sq h.two_ne
  set W := E.map (U - LinearMap.id) with hW
  have hWE : W ≤ E := by
    rintro _ ⟨e, he, rfl⟩
    exact sub_mem (map_mem_eigSp h.comm he) he
  have hEW : E ≤ β.orthogonal W := fun e he =>
    LinearMap.BilinForm.mem_orthogonal_iff.mpr fun n hn =>
      eig_isotropic h.isomT h.lam_ne (hWE hn) he
  have hUsurj : ∀ e ∈ E, ∃ e₀ ∈ E, U e₀ = e := by
    let U' : E →ₗ[K] E := U.restrict fun x hx => map_mem_eigSp h.comm hx
    have hinj : Function.Injective U' := fun a b hab =>
      Subtype.ext (injective_of_isometry h.nondeg h.isomU (congrArg Subtype.val hab))
    intro e he
    obtain ⟨e₀, he₀⟩ := (LinearMap.injective_iff_surjective.mp hinj) ⟨e, he⟩
    exact ⟨e₀.1, e₀.2, congrArg Subtype.val he₀⟩
  have hC1 : E' ⊓ β.orthogonal W = E' ⊓ F := by
    ext y
    simp only [Submodule.mem_inf, LinearMap.BilinForm.mem_orthogonal_iff, hF, mem_fixSp]
    constructor
    · rintro ⟨hyE', hyW⟩
      refine ⟨hyE', ?_⟩
      have hz : U y - y = 0 := by
        refine h.eq_zero (fun v hv => ?_) fun v hv =>
          eig_isotropic h.isomT h.neg_lam_ne hv (sub_mem (map_mem_eigSp h.comm hyE') hyE')
        obtain ⟨e₀, he₀, rfl⟩ := hUsurj v hv
        have h1 := hyW ((U - LinearMap.id : V →ₗ[K] V) e₀) ⟨e₀, he₀, rfl⟩
        rw [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.map_sub₂] at h1
        rw [map_sub, h.isomU e₀ y, ← neg_sub, h1, neg_zero]
      exact sub_eq_zero.mp hz
    · rintro ⟨hyE', hyF⟩
      refine ⟨hyE', fun n hn => ?_⟩
      obtain ⟨e, he, rfl⟩ := hn
      have h1 := h.isomU e y
      rw [hyF] at h1
      rw [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.map_sub₂, h1, sub_self]
  have hC4 : β.orthogonal W = E ⊔ (E' ⊓ β.orthogonal W) := by
    rw [← sup_inf_assoc_of_le E' hEW, hsup, top_inf_eq]
  have d3 := LinearMap.BilinForm.finrank_orthogonal h.nondeg W
  have d5 := Submodule.finrank_sup_add_finrank_inf_eq E (E' ⊓ β.orthogonal W)
  have hEX : E ⊓ (E' ⊓ β.orthogonal W) = ⊥ :=
    eq_bot_iff.mpr (le_trans (inf_le_inf_left _ inf_le_left) hinf.le)
  rw [← hC4, hEX, finrank_bot, add_zero] at d5
  have d7 : finrank K V = finrank K E + finrank K E' := h.finrank_eq
  have d8 : finrank K E = finrank K E' := h.finrank_eig_eq
  have d6 : finrank K W + finrank K ↥(E ⊓ F) = finrank K E := by
    have h6 := LinearMap.finrank_range_add_finrank_ker ((U - LinearMap.id).domRestrict E)
    rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at h6
    rw [← h6, ← Submodule.finrank_map_subtype_eq E, Submodule.map_comap_subtype]
    rfl
  rw [← hC1]
  omega

theorem DualHyp.finrank_fix_eq_two_mul {lam : K} (h : DualHyp β T U lam) :
    finrank K (fixSp U) = 2 * finrank K ↥(eigSp T lam ⊓ fixSp U) := by
  have hle : fixSp U ≤ (eigSp T lam ⊓ fixSp U) ⊔ (eigSp T (-lam) ⊓ fixSp U) := by
    intro x hx
    have hUx := mem_fixSp.mp hx
    rw [eq_decomp h.lam_sq h.two_ne x]
    refine Submodule.add_mem_sup (Submodule.smul_mem _ _ ⟨add_smul_mem_eigSp h.sq h.lam_sq x, ?_⟩)
      (Submodule.smul_mem _ _ (Submodule.neg_mem _ ⟨sub_smul_mem_eigSp h.sq h.lam_sq x, ?_⟩))
    · rw [SetLike.mem_coe, mem_fixSp, map_add, map_smul, ← h.comm, hUx]
    · rw [SetLike.mem_coe, mem_fixSp, map_sub, map_smul, ← h.comm, hUx]
  have heq : fixSp U = (eigSp T lam ⊓ fixSp U) ⊔ (eigSp T (-lam) ⊓ fixSp U) :=
    le_antisymm hle (sup_le inf_le_right inf_le_right)
  have d := Submodule.finrank_sup_add_finrank_inf_eq (eigSp T lam ⊓ fixSp U)
    (eigSp T (-lam) ⊓ fixSp U)
  have hbot : (eigSp T lam ⊓ fixSp U) ⊓ (eigSp T (-lam) ⊓ fixSp U) = ⊥ :=
    eq_bot_iff.mpr (le_trans (inf_le_inf inf_le_left inf_le_left)
      (eig_inf_eq_bot h.lam_sq h.two_ne).le)
  rw [← heq, hbot, finrank_bot, add_zero, ← h.finrank_eig_fix_eq] at d
  omega

end Main

end NoOffRest

end CFSG.StandardType
