module

public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma41Base

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.F4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF79
  CFSG.RankThree.PartTwo.Sec21.FF79.L41

@[expose] def invClosure {G : Type*} [Group G] (V : Subgroup G) : Subgroup G :=
  Subgroup.closure {x | x ∈ V ∧ orderOf x = 2}

theorem map_invClosure {G H : Type*} [Group G] [Group H] (f : G →* H) (hf : Function.Injective f)
    (V : Subgroup G) : (invClosure V).map f = invClosure (V.map f) := by
  unfold invClosure
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  simp only [Set.mem_image, Set.mem_setOf_eq, Subgroup.mem_map]
  constructor
  · rintro ⟨x, ⟨hx, ho⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, by rw [orderOf_injective f hf x, ho]⟩
  · rintro ⟨⟨x, hx, rfl⟩, ho⟩
    exact ⟨x, ⟨hx, by rwa [orderOf_injective f hf x] at ho⟩, rfl⟩

theorem invClosure_ne_iff_map {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) (V : Subgroup G) :
    invClosure (V.map f) ≠ V.map f ↔ invClosure V ≠ V := by
  rw [← map_invClosure f hf, Ne, Ne, (Subgroup.map_injective hf).eq_iff]

theorem invClosure_conjBy {G : Type} [Group G] (g : G) (V : Subgroup G) :
    invClosure (conjBy g V) = conjBy g (invClosure V) :=
  (map_invClosure (MulAut.conj g).toMonoidHom (MulAut.conj g).injective V).symm

theorem forall_isSylowOf_of_one {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {H V₁ : Subgroup G} (hV₁ : IsSylowOf p V₁ H) (P : Subgroup G → Prop)
    (hP : ∀ g ∈ H, ∀ V, P V → P (conjBy g V)) (h₁ : P V₁) :
    ∀ V, IsSylowOf p V H → P V := by
  intro V hV
  obtain ⟨k, hk, hkV⟩ := exists_conjBy_eq_sylowOf hV hV₁
  rw [← hkV]
  exact hP k hk V₁ h₁

end CFSG.RankThree.PartTwo.Sec21.FF81.F4
