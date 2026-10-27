module

public import CFSG.LocalAnalysis.StandardType.FS81.Defs
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly

@[expose] def RowElemAb3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K A : Subgroup G) (r : Row),
    IsRow r K → Subgroup.center K = ⊥ → A ≤ K → IsElemAbelian 3 A → Nat.card A = 3 ^ r.n →
      (∀ A' : Subgroup G, A' ≤ K → IsElemAbelian 3 A' → Nat.card A' ≤ 3 ^ r.n) ∧
      (∀ A' : Subgroup G, A' ≤ K → IsElemAbelian 3 A' → Nat.card A' = 3 ^ r.n →
        ∃ k ∈ K, A'.map (MulAut.conj k).toMonoidHom = A)

theorem rowElemAb3_of_mulEquiv {G M : Type} [Group G] [Finite G] [Group M] {K A : Subgroup G}
    {n : ℕ} (φ : ↥K ≃* M)
    (h1 : ∀ E : Subgroup M, IsElemAbelian 3 E → Nat.card E ≤ 3 ^ n)
    (h2 : ∀ E E' : Subgroup M, IsElemAbelian 3 E → IsElemAbelian 3 E' → Nat.card E = 3 ^ n →
      Nat.card E' = 3 ^ n → ∃ c : M, E'.map (MulAut.conj c).toMonoidHom = E)
    (hAK : A ≤ K) (hA : IsElemAbelian 3 A) (hAcard : Nat.card A = 3 ^ n) :
    (∀ A' : Subgroup G, A' ≤ K → IsElemAbelian 3 A' → Nat.card A' ≤ 3 ^ n) ∧
      (∀ A' : Subgroup G, A' ≤ K → IsElemAbelian 3 A' → Nat.card A' = 3 ^ n →
        ∃ k ∈ K, A'.map (MulAut.conj k).toMonoidHom = A) := by
  have himg_el : ∀ A' : Subgroup G, IsElemAbelian 3 A' →
      IsElemAbelian 3 ((A'.subgroupOf K).map φ.toMonoidHom) :=
    fun A' h => (h.subgroupOf K).map _
  have himg_card : ∀ A' : Subgroup G, A' ≤ K →
      Nat.card ((A'.subgroupOf K).map φ.toMonoidHom) = Nat.card A' := fun A' hA' => by
    rw [Subgroup.card_map_of_injective φ.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA').toEquiv]
  refine ⟨fun A' hA'K hA' => ?_, fun A' hA'K hA' hcard => ?_⟩
  · rw [← himg_card A' hA'K]
    exact h1 _ (himg_el A' hA')
  · obtain ⟨c, hc⟩ := h2 _ _ (himg_el A hA) (himg_el A' hA')
      (by rw [himg_card A hAK, hAcard]) (by rw [himg_card A' hA'K, hcard])
    refine ⟨(φ.symm c : G), (φ.symm c).2, ?_⟩
    have hle : A'.map (MulAut.conj (φ.symm c : G)).toMonoidHom ≤ A := by
      rintro _ ⟨y, hy, rfl⟩
      have hyK := hA'K hy
      have hmem : φ (φ.symm c * ⟨y, hyK⟩ * (φ.symm c)⁻¹) ∈ (A.subgroupOf K).map φ.toMonoidHom := by
        rw [← hc, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
        exact ⟨φ ⟨y, hyK⟩, ⟨⟨y, hyK⟩, hy, rfl⟩, rfl⟩
      obtain ⟨z, hz, hzeq⟩ := hmem
      have hz' : z = φ.symm c * ⟨y, hyK⟩ * (φ.symm c)⁻¹ := φ.injective hzeq
      rw [hz'] at hz
      exact hz
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj (φ.symm c : G)).injective, hcard, hAcard]

end CFSG.StandardType.FrameRoute.FS81

end
