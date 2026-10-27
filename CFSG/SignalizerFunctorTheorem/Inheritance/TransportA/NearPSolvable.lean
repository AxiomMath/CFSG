module

public import CFSG.Open.SignalizerFunctorDefs
public import CFSG.SignalizerFunctorTheorem.Inheritance.Pullback

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.TransportA

theorem nearSimpleModel_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) {p : ℕ}
    (h : signalizerNearSimpleModel p A) : signalizerNearSimpleModel p B := by
  rcases h with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨n, hn, ⟨φ⟩⟩ | ⟨⟨φ⟩⟩
  · exact Or.inl ⟨e.symm.trans φ⟩
  · exact Or.inr (Or.inl ⟨e.symm.trans φ⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨n, hn, ⟨e.symm.trans φ⟩⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨e.symm.trans φ⟩))

theorem nearPSolvable_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) {p : ℕ}
    (h : signalizerNearPSolvable p X) : signalizerNearPSolvable p Y := by
  refine ⟨Nat.card_congr e.toEquiv ▸ h.1, ?_⟩
  intro K L hLK _ hsimple hnonab
  have := normal_comap_subgroupOf (e : X →* Y) hLK
  let φ := comapSectionEquiv (e : X →* Y) e.surjective (K := K) (L := L)
  have hsimple' := φ.isSimpleGroup (H := K ⧸ L.subgroupOf K)
  have hnonab' : ∃ a b : K.comap (e : X →* Y) ⧸
      (L.comap (e : X →* Y)).subgroupOf (K.comap (e : X →* Y)), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnonab
    refine ⟨φ.symm a, φ.symm b, fun h => hab ?_⟩
    simpa using congrArg φ h
  exact nearSimpleModel_of_mulEquiv φ (h.2 _ _ (Subgroup.comap_mono hLK) hsimple' hnonab')

end CFSG.SignalizerFunctorTheorem.TransportA
