module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7SUDefs

public section

namespace CFSG.StandardType.HdRo7SU

open CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem hdRo7SGrAux_mono {α : Type*} {r p : α → α → Prop}
    (h : ∀ a b, r a b → p a b) {a b : α} (hab : Relation.ReflTransGen r a b) :
    Relation.ReflTransGen p a b := by
  induction hab with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail (h _ _ hbc)

theorem su_graph_holds : SUGraphLeaf := by
  intro p _ V _ _ AL AK J SL SK hSL hAL hSLconn hSK hAK hSKconn hJAL hJAK hJnab
  by_cases hcross : ∃ s ∈ SL, ∃ t ∈ SK, ¬ Commute s t
  · obtain ⟨s₁, hs₁, t₁, ht₁, hnc⟩ := hcross
    refine ⟨SL ∪ SK, ?_, ?_, ?_⟩
    · rintro s (hs | hs)
      · exact ⟨Subgroup.mem_sup_left (hSL s hs).1, (hSL s hs).2⟩
      · exact ⟨Subgroup.mem_sup_right (hSK s hs).1, (hSK s hs).2⟩
    · rw [hAL, hAK, Subgroup.closure_union]
    · intro s hsS t htS
      have monoSL : ∀ {u v : V ≃ₗ[ZMod p] V}, Relation.ReflTransGen
          (fun u v => u ∈ SL ∧ v ∈ SL ∧ ¬ Commute u v) u v →
          Relation.ReflTransGen
            (fun u v => u ∈ SL ∪ SK ∧ v ∈ SL ∪ SK ∧ ¬ Commute u v) u v :=
        fun h => hdRo7SGrAux_mono
          (fun a b hab => ⟨Or.inl hab.1, Or.inl hab.2.1, hab.2.2⟩) h
      have monoSK : ∀ {u v : V ≃ₗ[ZMod p] V}, Relation.ReflTransGen
          (fun u v => u ∈ SK ∧ v ∈ SK ∧ ¬ Commute u v) u v →
          Relation.ReflTransGen
            (fun u v => u ∈ SL ∪ SK ∧ v ∈ SL ∪ SK ∧ ¬ Commute u v) u v :=
        fun h => hdRo7SGrAux_mono
          (fun a b hab => ⟨Or.inr hab.1, Or.inr hab.2.1, hab.2.2⟩) h
      rcases hsS with hsL | hsK
      · rcases htS with htL | htK
        · exact monoSL (hSLconn s hsL t htL)
        · exact (monoSL (hSLconn s hsL s₁ hs₁)).trans
            ((Relation.ReflTransGen.single ⟨Or.inl hs₁, Or.inr ht₁, hnc⟩).trans
              (monoSK (hSKconn t₁ ht₁ t htK)))
      · rcases htS with htL | htK
        · exact (monoSK (hSKconn s hsK t₁ ht₁)).trans
            ((Relation.ReflTransGen.single ⟨Or.inr ht₁, Or.inl hs₁, fun h => hnc h.symm⟩).trans
              (monoSL (hSLconn s₁ hs₁ t htL)))
        · exact monoSK (hSKconn s hsK t htK)
  · exfalso
    have hnoCross : ∀ s ∈ SL, ∀ t ∈ SK, Commute s t := by
      intro s hs t ht
      by_contra h
      exact hcross ⟨s, hs, t, ht, h⟩
    have hstep : ∀ s ∈ SL, ∀ b ∈ AK, s * b = b * s := by
      intro s hs b hb
      have hsub : SK ⊆ Subgroup.centralizer ({s} : Set (V ≃ₗ[ZMod p] V)) := by
        intro t ht
        exact Subgroup.mem_centralizer_singleton_iff.mpr (hnoCross s hs t ht).symm
      have hcl : AK ≤ Subgroup.centralizer ({s} : Set (V ≃ₗ[ZMod p] V)) := by
        rw [hAK]
        exact (Subgroup.closure_le _).mpr hsub
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hcl hb)).symm
    have hcomm : ∀ a ∈ AL, ∀ b ∈ AK, a * b = b * a := by
      intro a ha b hb
      have hsub : SL ⊆ Subgroup.centralizer ({b} : Set (V ≃ₗ[ZMod p] V)) := by
        intro s hs
        exact Subgroup.mem_centralizer_singleton_iff.mpr (hstep s hs b hb)
      have hcl : AL ≤ Subgroup.centralizer ({b} : Set (V ≃ₗ[ZMod p] V)) := by
        rw [hAL]
        exact (Subgroup.closure_le _).mpr hsub
      exact Subgroup.mem_centralizer_singleton_iff.mp (hcl ha)
    obtain ⟨a, haJ, b, hbJ, hne⟩ := hJnab
    exact hne (hcomm a (hJAL haJ) b (hJAK hbJ))

end CFSG.StandardType.HdRo7SU
