module

public import CFSG.Quasithin.Recognition.CertOvergroup

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin

theorem conj_mem_of_closed {G : Type*} [Group G] [Finite G] {Γ : Set G} {cl : List G}
    (h4 : ∀ c ∈ cl, ∀ s ∈ Γ, s * c * s⁻¹ ∈ cl) {a : G} (ha : a ∈ Subgroup.closure Γ) :
    ∀ c ∈ cl, a * c * a⁻¹ ∈ cl := by
  have key := closure_subset_of_right_closed (S := Γ)
    (P := {a : G | ∀ c ∈ cl, a * c * a⁻¹ ∈ cl})
    (fun s _ => by
      obtain ⟨n, hn, h⟩ := (isOfFinOrder_of_finite s).exists_pow_eq_one
      exact ⟨n, hn, h⟩)
    (fun c hc => by simpa using hc)
    (fun p hp s hs c hc => by
      have h := hp _ (h4 c hc s hs)
      simpa [mul_assoc] using h)
  exact key ha

theorem card_centralizer_mul_of_closed_class {G : Type*} [Group G] [Finite G] {Γ : Set G}
    {H : Subgroup G} (hH : Subgroup.closure Γ = H) {f : G} (hf : f ∈ H) {cl : List G}
    (h1 : cl.Nodup) (h2 : ∀ c ∈ cl, ∃ a ∈ H, c = a * f * a⁻¹) (h3 : f ∈ cl)
    (h4 : ∀ c ∈ cl, ∀ s ∈ Γ, s * c * s⁻¹ ∈ cl) :
    Nat.card (Subgroup.centralizer ({(⟨f, hf⟩ : H)} : Set H)) * cl.length = Nat.card H := by
  classical
  subst hH
  set H := Subgroup.closure Γ with hH
  set f' : H := ⟨f, hf⟩ with hf'
  have hset : conjugatesOf f' = {a : H | (a : G) ∈ cl} := by
    ext a
    show IsConj f' a ↔ (a : G) ∈ cl
    constructor
    · intro hc
      obtain ⟨g, hg⟩ := isConj_iff.1 hc
      have : (a : G) = g * f * g⁻¹ := by rw [← hg]; rfl
      rw [this]
      exact conj_mem_of_closed h4 g.2 f h3
    · intro ha
      obtain ⟨b, hb, hab⟩ := h2 _ ha
      refine isConj_iff.2 ⟨⟨b, hb⟩, Subtype.ext ?_⟩
      simpa using hab.symm
  have hsub : (↑cl.toFinset : Set G) ⊆ Set.range (Subtype.val : H → G) := by
    intro c hc
    obtain ⟨a, ha, rfl⟩ := h2 c (List.mem_toFinset.1 hc)
    exact ⟨⟨a * f * a⁻¹, H.mul_mem (H.mul_mem ha hf) (H.inv_mem ha)⟩, rfl⟩
  have hnc : (conjugatesOf f').ncard = cl.length := by
    rw [hset]
    have e : {a : H | (a : G) ∈ cl} = (Subtype.val : H → G) ⁻¹' (↑cl.toFinset : Set G) := by
      ext a; simp
    rw [e, Set.ncard_preimage_of_injective_subset_range Subtype.val_injective hsub,
      Set.ncard_coe_finset, List.toFinset_card_of_nodup h1]
  have h := Subgroup.card_mul_index (H := Subgroup.centralizer ({f'} : Set H))
  rw [Subgroup.index_centralizer_eq_ncard, hnc] at h
  exact h

end CFSG.Quasithin.H13.F431.U42Aut
