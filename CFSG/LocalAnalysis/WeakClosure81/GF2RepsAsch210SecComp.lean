module

public import CFSG.LocalAnalysis.WeakClosure81.EightEightDefs
import CFSG.LocalAnalysis.WeakClosure81.W183Br1Comp2

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch210

open CFSG.Quasithin CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem a210sc_hasQuotShape_of_mulEquiv {K L L' : Subgroup G} (e : ↥L ≃* ↥L')
    (hK : ∀ l : ↥L, (l : G) ∈ K ↔ (e l : G) ∈ K) {P : ∀ (X : Type) [Group X], Prop}
    (hQ : HasQuotShape L K P) : HasQuotShape L' K P := by
  obtain ⟨X, hX, φ, hφs, hφk, hPX⟩ := hQ
  refine ⟨X, hX, φ.comp e.symm.toMonoidHom, hφs.comp e.symm.surjective, ?_, hPX⟩
  intro k
  change φ (e.symm k) = 1 ↔ (k : G) ∈ K
  rw [hφk (e.symm k)]
  have h := hK (e.symm k)
  rwa [show e (e.symm k) = k from e.apply_symm_apply k] at h

omit [Finite G] in
private theorem a210sc_isComponentModN_map_mulEquiv {K H L : Subgroup G} (e : G ≃* G)
    (hK : K.map e.toMonoidHom = K) (hH : H.map e.toMonoidHom = H)
    (h : IsComponentModN K H L) :
    IsComponentModN K H (L.map e.toMonoidHom) := by
  have hfe : Function.Injective e.toMonoidHom := fun a _b hab => e.injective (by simpa using hab)
  refine ⟨h.1, ?_, ?_, ?_, ?_⟩
  · intro k hk
    have hk' : e.symm k ∈ K := by
      rw [← hK] at hk
      obtain ⟨k', hk'K, hk'eq⟩ := Subgroup.mem_map.1 hk
      have hkk : k' = e.symm k := by
        rw [← hk'eq]
        change k' = e.symm (e k')
        rw [e.symm_apply_apply]
      rwa [hkk] at hk'K
    exact Subgroup.mem_map.2 ⟨e.symm k, h.2.1 hk', by simp⟩
  · rintro x ⟨l, hl, rfl⟩
    rw [← hH]
    exact Subgroup.mem_map_of_mem e.toMonoidHom (h.2.2.1 hl)
  · have hsub := h.2.2.2.1.map e.toMonoidHom
    rwa [hH] at hsub
  · refine a210sc_hasQuotShape_of_mulEquiv
      (Subgroup.equivMapOfInjective L e.toMonoidHom hfe) ?_ h.2.2.2.2
    intro l
    constructor
    · intro hl
      rw [Subgroup.coe_equivMapOfInjective_apply, ← hK]
      exact Subgroup.mem_map_of_mem e.toMonoidHom hl
    · intro hl
      rw [Subgroup.coe_equivMapOfInjective_apply, ← hK] at hl
      obtain ⟨k, hkK, hkeq⟩ := Subgroup.mem_map.1 hl
      have hkl : k = l := e.injective hkeq
      rwa [hkl] at hkK

omit [Finite G] in
private theorem a210sc_isQuasisimple_image_quotient {K H L : Subgroup G}
    (hKn : (K.subgroupOf H).Normal) (hLH : L ≤ H)
    (hQ : HasQuotShape L (K : Set G) (fun X _ => CFSG.IsQuasisimple X)) :
    CFSG.IsQuasisimple ((L.subgroupOf H).map (QuotientGroup.mk' (K.subgroupOf H))) := by
  classical
  have := hKn
  obtain ⟨X, hX, φ, hφs, hφk, hXq⟩ := hQ
  let q := QuotientGroup.mk' (K.subgroupOf H)
  let A : Subgroup (↥H ⧸ (K.subgroupOf H)) := (L.subgroupOf H).map q
  let eL : ↥(L.subgroupOf H) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLH
  let φ' : ↥(L.subgroupOf H) →* X := φ.comp eL.toMonoidHom
  have hφ's : Function.Surjective φ' := hφs.comp eL.surjective
  let ψ : ↥(L.subgroupOf H) →* A := q.subgroupMap (L.subgroupOf H)
  have hψs : Function.Surjective ψ := q.subgroupMap_surjective (L.subgroupOf H)
  have hker : φ'.ker = ψ.ker := by
    ext k
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    have h1 : φ' k = 1 ↔ (k : G) ∈ K := by
      show φ (eL k) = 1 ↔ (k : G) ∈ K
      rw [hφk (eL k)]
      rfl
    have h2 : ψ k = 1 ↔ (k : G) ∈ K := by
      constructor
      · intro hk
        have hq1 : q k = 1 := congrArg Subtype.val hk
        rw [show q = QuotientGroup.mk' (K.subgroupOf H) from rfl, QuotientGroup.mk'_apply,
          QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hq1
        exact hq1
      · intro hk
        apply Subtype.ext
        show q k = 1
        rw [show q = QuotientGroup.mk' (K.subgroupOf H) from rfl, QuotientGroup.mk'_apply,
          QuotientGroup.eq_one_iff]
        exact Subgroup.mem_subgroupOf.mpr hk
    exact h1.trans h2.symm
  let e : X ≃* A :=
    (QuotientGroup.quotientKerEquivOfSurjective φ' hφ's).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker).trans
        (QuotientGroup.quotientKerEquivOfSurjective ψ hψs))
  exact CFSG.IsQuasisimple.of_mulEquiv e.symm hXq

theorem exists_four_components {Q : Type} [Group Q] [Finite Q] {H K L : Subgroup Q}
    [(K.subgroupOf H).Normal] (hL : IsComponentModN K H L) (h3 : 3 ∣ K.relIndex L)
    (t : Fin 4 → Q) (ht : ∀ i, t i ∈ H)
    (hinj : Function.Injective fun i => conjSubgroup L (t i)) :
    ∃ A : Fin 4 → Subgroup (↥H ⧸ K.subgroupOf H), (∀ i, CFSG.IsQuasisimple ↥(A i)) ∧
      (∀ i j, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, a * b = b * a) ∧
      ∀ i, 3 ∣ Nat.card ↥(A i) := by
  classical
  let K0 : Subgroup ↥H := K.subgroupOf H
  let π : ↥H →* ↥H ⧸ K0 := QuotientGroup.mk' K0
  let Li : Fin 4 → Subgroup Q := fun i => conjSubgroup L (t i)
  let A : Fin 4 → Subgroup (↥H ⧸ K0) := fun i => ((Li i).subgroupOf H).map π
  have hker : ∀ x : ↥H, π x = 1 ↔ (x : Q) ∈ K := by
    intro x
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hHnorm : H ≤ Subgroup.normalizer (K : Set Q) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hL.2.1.trans hL.2.2.1)).mp hL.1
  have hKmap : ∀ i, K.map (MulAut.conj (t i)⁻¹).toMonoidHom = K := fun i =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hHnorm (H.inv_mem (ht i)))
  have hHmap : ∀ i, H.map (MulAut.conj (t i)⁻¹).toMonoidHom = H := fun i =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer (H.inv_mem (ht i)))
  have hLi : ∀ i, IsComponentModN K H (Li i) := fun i =>
    a210sc_isComponentModN_map_mulEquiv (MulAut.conj (t i)⁻¹) (hKmap i) (hHmap i) hL
  refine ⟨A, ?_, ?_, ?_⟩
  · intro i
    exact a210sc_isQuasisimple_image_quotient (K := K) (H := H) (L := Li i)
      (hLi i).1 (hLi i).2.2.1 (hLi i).2.2.2.2
  · intro i j hij a ha b hb
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
    have hne : Li i ≠ Li j := fun h => hij (hinj h)
    have hcommG : ((a' : Q) * (b' : Q) * (a' : Q)⁻¹ * (b' : Q)⁻¹) ∈ K :=
      w183_components_commute (hLi i) (hLi j) hne (a' : Q)
        (Subgroup.mem_subgroupOf.mp ha') (b' : Q) (Subgroup.mem_subgroupOf.mp hb')
    have h1 : π a' * π b' * (π a')⁻¹ * (π b')⁻¹ = 1 := by
      have h0 : π (a' * b' * a'⁻¹ * b'⁻¹) = 1 := by
        rw [hker]
        simpa using hcommG
      simpa only [map_mul, map_inv] using h0
    calc π a' * π b'
        = (π a' * π b' * (π a')⁻¹ * (π b')⁻¹) * (π b' * π a') := by group
      _ = 1 * (π b' * π a') := by rw [h1]
      _ = π b' * π a' := by group
  · intro i
    have hcard : Nat.card ↥(A i) = K.relIndex L := by
      have hcard1 : Nat.card ↥(((Li i).subgroupOf H).map π) =
          K0.relIndex ((Li i).subgroupOf H) := by
        rw [← Subgroup.relIndex_ker (K := (Li i).subgroupOf H) π, QuotientGroup.ker_mk']
      have hcard2 : K0.relIndex ((Li i).subgroupOf H) = K.relIndex (Li i) :=
        Subgroup.relIndex_subgroupOf (H := K) (K := Li i) (L := H) (hLi i).2.2.1
      have hcard3 : K.relIndex (Li i) = K.relIndex L := by
        show K.relIndex (L.map (MulAut.conj (t i)⁻¹).toMonoidHom) = K.relIndex L
        have h := Subgroup.relIndex_map_map_of_injective
          (f := (MulAut.conj (t i)⁻¹).toMonoidHom) K L (MulAut.conj (t i)⁻¹).injective
        rwa [hKmap i] at h
      exact hcard1.trans (hcard2.trans hcard3)
    rw [hcard]
    exact h3

end CFSG.LocalAnalysis.WeakClosure81.Asch210
