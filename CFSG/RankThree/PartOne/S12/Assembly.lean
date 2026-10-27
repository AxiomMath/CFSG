module

public import CFSG.RankThree.PartOne.S12.Hyp
import CFSG.RankThree.PartOne.S10.PreferredSetupExistence
import CFSG.RankThree.PartOne.S10.AmbientTheta
public import CFSG.RankThree.PartOne.Assembly

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory

theorem center_eq_bot_of_simple_nonabelian {G : Type} [Group G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) : Subgroup.center G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnonab
    have : a ∈ Subgroup.center G := by rw [h]; exact Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.mp this b).symm

theorem exists_maximal_elementary_abelian_centralizer {G : Type} [Group G] [Finite G] (p : ℕ)
    (A : Subgroup G) (hA : IsElementaryAbelian p A) :
    ∃ E : Subgroup G, IsElementaryAbelian p E ∧ E ≤ Subgroup.centralizer (A : Set G) ∧
      ∀ F : Subgroup G, IsElementaryAbelian p F → F ≤ Subgroup.centralizer (A : Set G) →
        E ≤ F → F = E := by
  have hAC : A ≤ Subgroup.centralizer (A : Set G) := by
    intro a ha b hb
    exact congrArg Subtype.val (hA.is_comm.comm ⟨b, hb⟩ ⟨a, ha⟩)
  let S : Set (Subgroup G) :=
    {F | IsElementaryAbelian p F ∧ F ≤ Subgroup.centralizer (A : Set G) ∧ A ≤ F}
  obtain ⟨E, hE, hmax⟩ := (Set.toFinite S).exists_maximalFor id S ⟨A, hA, hAC, le_rfl⟩
  refine ⟨E, hE.1, hE.2.1, fun F hF hFC hEF => ?_⟩
  exact le_antisymm (hmax ⟨hF, hFC, hE.2.2.trans hEF⟩ hEF) hEF

theorem nonempty_mulEquiv_of_eq_top {G : Type} [Group G] {I : Subgroup G} (hI : I = ⊤) :
    Nonempty (G ≃* I) :=
  ⟨Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hI).symm⟩

theorem nonempty_quotient_center_mulEquiv_of_eq_top {G : Type} [Group G] {I : Subgroup G}
    (hI : I = ⊤) (hc : Subgroup.center G = ⊥) : Nonempty (G ≃* (I ⧸ Subgroup.center I)) := by
  have hI' : Subgroup.center I = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_center_iff] at hx
    have hxG : (x : G) ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := hx ⟨g, hI ▸ Subgroup.mem_top g⟩
      exact congrArg Subtype.val this
    rw [hc, Subgroup.mem_bot] at hxG
    exact Subtype.ext hxG
  obtain ⟨e⟩ := nonempty_mulEquiv_of_eq_top hI
  exact ⟨e.trans ((QuotientGroup.quotientBot (G := I)).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hI'.symm))⟩

theorem iModel_of_outcome {G : Type} [Group G] (hc : Subgroup.center G = ⊥) {p : ℕ}
    {E A I : Subgroup G} (hI : I = ⊤) (h : Outcome152 p E A I) : IModel G := by
  obtain ⟨e⟩ := nonempty_mulEquiv_of_eq_top hI
  rcases h with ⟨f, hf, -, ⟨φ⟩, -⟩ | ⟨f, hf, -, ⟨φ⟩, -⟩ | ⟨f, hf, -, ⟨b, c, hbc, ⟨φ⟩⟩, -⟩ |
    ⟨f, hf, -, ⟨b, c, hbc, ⟨φ⟩⟩, -⟩ | ⟨f, hf, -, ⟨φ⟩, -⟩
  · exact ⟨f, hf, Or.inr (Or.inr (Or.inl ⟨e.trans φ⟩))⟩
  · exact ⟨f, hf, Or.inr (Or.inr (Or.inr ⟨e.trans φ⟩))⟩
  · exact ⟨f, hf, Or.inr (Or.inl ⟨b, c, hbc, ⟨e.trans φ⟩⟩)⟩
  · exact ⟨f, hf, Or.inr (Or.inl ⟨b, c, hbc, ⟨e.trans φ⟩⟩)⟩
  · obtain ⟨e'⟩ := nonempty_quotient_center_mulEquiv_of_eq_top hI hc
    exact ⟨f, hf, Or.inl ⟨e'.trans φ⟩⟩

@[expose] def Sec11One : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G), SteinbergBM.SectionTenSetup G p A →
    ∃ L : Subgroup G, L ∈ sectionTenZeroStar p A ∩ sectionTenOne p A

@[expose] def Sec12to14Claim : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E → Outcome152 p E A (lieGenerated p E)

@[expose] def Sec15Claim : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E → Outcome152 p E A (lieGenerated p E) → lieGenerated p E = ⊤

theorem vanishingRecognition_of_sections (h11 : Sec11One) (h1214 : Sec12to14Claim)
    (h15 : Sec15Claim) : VanishingRecognition := by
  intro G _ _ _ hnonab hK hchar hrank hvan
  obtain ⟨p, A, hS⟩ := section_ten_preferred_setup_existence_of_milestone hnonab hK hchar hrank hvan
  obtain ⟨L, hL0, hL1⟩ := h11 G p A hS
  obtain ⟨c, hcA, hc1, hLc⟩ := mem_thetaComponentFamily_iff.mp
    ((sectionTenZeroStar_subset p A).2.2.1 hL0.2)
  obtain ⟨E, hE1, hE2, hE3⟩ :=
    exists_maximal_elementary_abelian_centralizer p A hS.2.2.2.2.2.2.1
  have h12 : Sec12Hyp G p A c L E := ⟨hS, hcA, hc1, ⟨⟨hL0, hL1⟩, hLc⟩, hE1, hE2, hE3⟩
  exact iModel_of_outcome (center_eq_bot_of_simple_nonabelian hnonab) (h15 G p A c L E h12
    (h1214 G p A c L E h12)) (h1214 G p A c L E h12)

end CFSG.RankThree.PartOne
