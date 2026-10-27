module

public import CFSG.LocalAnalysis.StandardType.GGD4OddCentKnownInputs
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitMarking

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section Transport

variable {G : Type} [Group G]

theorem ggD4OddCent_jMarking_of_kMarking {K J S : Subgroup G} (hJK : J ≤ K)
    (hN : S ≤ Subgroup.normalizer (K : Set G))
    (Φ : LargeEvenLabel → Prop → Prop → Prop → Prop)
    (h : LargeEvenMarking ↥(J.subgroupOf K) fun lab _ _ I _ θ' =>
      Φ lab (Subgroup.center ↥(J.subgroupOf K) = ⊥)
        (GGAutsInduceOn (ggAutsOf K S hN) (J.subgroupOf K) θ' I)
        (GGAutsFixedInCenter (ggAutsOf K S hN) (J.subgroupOf K))) :
    LargeEvenMarking ↥J fun lab _ _ I _ θ =>
      Φ lab (Subgroup.center ↥J = ⊥) (GGConjInducesOn S J θ I) (GGConjFixedInCenter S J) := by
  set e := Subgroup.subgroupOfEquivOfLe hJK with he
  refine largeEvenMarking_congr e.symm (fun lab R _ I F θ hθ => ?_) h
  have hind := ggAutsInduceOn_iff hN hJK θ I
  have hfix := ggAutsFixedInCenter_iff hN hJK
  have hcen : (Subgroup.center ↥(J.subgroupOf K) = ⊥) ↔ (Subgroup.center ↥J = ⊥) :=
    ⟨center_eq_bot_of_mulEquiv e.symm, center_eq_bot_of_mulEquiv e⟩
  rw [centerQuotCongr_symm]
  rw [propext hind, propext hfix, propext hcen] at hθ
  exact hθ

theorem ggD4OddCent_jInduce_of_lInduce {L J S : Subgroup G} (hJL : J ≤ L)
    (hN : S ≤ Subgroup.normalizer (L : Set G))
    (h : GGMarkingAll (K := ↥(J.subgroupOf L)) fun _ _ _ I' _ θ' =>
      GGAutsInduceOn (ggAutsOf L S hN) (J.subgroupOf L) θ' I') :
    GGMarkingAll (K := ↥J) fun _ _ _ I' _ θ' => GGConjInducesOn S J θ' I' := by
  set e := Subgroup.subgroupOfEquivOfLe hJL with he
  refine ggMarkingAll_congr e (fun lab R _ I F θ hθ => ?_) h
  have := (ggAutsInduceOn_iff hN hJL ((centerQuotCongr e).trans θ) I).1 hθ
  rwa [centerQuotCongr_symm_trans_trans] at this

end Transport

section Clause3

variable {G : Type} [Group G] [Finite G]

theorem ggInducedInn_of_clause3 {B L : Subgroup G} (hBN : B ≤ Subgroup.normalizer (L : Set G))
    {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R) {I : Set (MulAut R)}
    (h3 : ∀ b ∈ B, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) :
    GGInducedInn (ggAutsOf L B hBN) θ I := by
  intro a ha
  obtain ⟨s, hs, rfl⟩ := (mem_ggAutsOf hBN).1 ha
  rw [← ggLAut_eq_ggInducedAut]
  exact ggLAut_mem_of_induces L θ hBN h3 hs

theorem ggD4OddCent_lMarking {B : Subgroup G} {x : G} {L : Subgroup G}
    (hst : LargeEvenStandardType 3 B x L) (hBN : B ≤ Subgroup.normalizer (L : Set G))
    (S : LargeEvenLabel → Prop)
    (hS : GGMarkingAll (K := ↥L) fun lab _ _ _ _ _ => LargeEvenSplit 3 lab → S lab) :
    LargeEvenMarking ↥L fun lab _ _ I _ θ =>
      S lab ∧ LargeEvenSplit 3 lab ∧ GGInducedInn (ggAutsOf L B hBN) θ I := by
  refine largeEvenMarking_mono ?_ (hS _ hst.1)
  rintro lab R _ I F θ ⟨⟨hsp, -, h3⟩, hSS⟩
  exact ⟨hSS hsp, hsp, ggInducedInn_of_clause3 hBN θ h3⟩

end Clause3

end CFSG.StandardType
