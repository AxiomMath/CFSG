module

public import CFSG.Quasithin.Vol2.Ch12Sec8OneA7Cert

public section

namespace CFSG.Quasithin.H13.L14324

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (V ≃ₗ[ZMod 2] V)} {v₁ : V}
  {W : Submodule (ZMod 2) V} {X X₀ : Subgroup (V ≃ₗ[ZMod 2] V)}

theorem card_le_four_of_concl4 (H : G111Hyp B Γ v₁ W X X₀)
    (hC4 : G112Concl4 Γ) : Nat.card X ≤ 4 := by
  classical
  obtain ⟨S', hS'syl, hXS', -⟩ := H.four
  have hS'Γ := L128P.isSylowTwoOf_of_stabilizer hS'syl H.odd_index
  have hS'v : ∀ s ∈ S', s v₁ = v₁ := fun s hs' =>
    MulAction.mem_stabilizer_iff.1 (hS'syl.1 hs').2
  obtain ⟨Up, hUpS, hUpv, hvUp, hcases⟩ :=
    H13.a7NatFact12813 V B Γ S' v₁ hC4 H.alt H.nondegenerate H.isometry hS'Γ H.point hS'v
  have hUE : ∀ w ∈ Up, w ∈ W → w = 0 := by
    intro w hwU hwW
    by_contra hw0
    have hspan : (⟨w, hwW⟩ : W) ∉ (ZMod 2) ∙ (⟨v₁, H.mem_W⟩ : W) := by
      intro hmem
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
      have hc' : c • v₁ = w := by
        have := congrArg Subtype.val hc
        simpa using this
      rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
      · exact hw0 (by rw [← hc', zero_smul])
      · rw [one_smul] at hc'
        exact hvUp (by rw [hc']; exact hwU)
    obtain ⟨f, hf, hker⟩ := Submodule.exists_le_ker_of_notMem hspan
    have hfv : f ⟨v₁, H.mem_W⟩ = 0 :=
      LinearMap.mem_ker.1 (hker (Submodule.mem_span_singleton_self _))
    obtain ⟨x, hxX, hx⟩ := H.transvection_full f hfv
    have h1 := hx ⟨w, hwW⟩
    have hf1 : f ⟨w, hwW⟩ = 1 := (by decide : ∀ c : ZMod 2, c ≠ 0 → c = 1) _ hf
    rw [hf1, one_smul] at h1
    have h1' : x w = w + v₁ := by simpa using h1
    have hxw : x w ∈ Up := hUpS x (hXS' hxX) w hwU
    apply hvUp
    have e : v₁ = x w - w := by
      rw [h1']
      abel
    rw [e]
    exact Up.sub_mem hxw hwU
  have hXU : ∀ x ∈ X, ∀ u ∈ Up, x u = u := by
    intro x hx u hu
    have h1 := H.commutator_le x hx u (hUpv u hu)
    have h2 : x u - u ∈ Up := Up.sub_mem (hUpS x (hXS' hx) u hu) hu
    exact sub_eq_zero.1 (hUE _ h2 h1)
  have hXel : IsElemAbelian 2 X :=
    ⟨⟨⟨fun a b => Subtype.ext (H.X_comm _ a.2 _ b.2)⟩⟩, fun x hx => by
      rw [sq]
      exact H.X_sq x hx⟩
  rcases hcases with h2 | ⟨h4, -⟩
  · exact (h2 X hXS' hXel hXU).trans (by norm_num)
  · exact h4 X hXS' hXel hXU

end CFSG.Quasithin.H13.L14324
