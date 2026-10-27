module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirtySixAN3E
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U3CartanRankHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SU3EightBorelNineHolds
public import CFSG.GroupTheory.CommutingPairNineRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.BorelTorusAbelianHolds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC6S846

variable {G : Type} [Group G] [Finite G]


theorem four_le_pRank_three_of_two_conj_of_three_dvd_center
    (hCen : UCK.U3Center) (hK9 : K_SU3EightTorusE9) {D : Data G} {L : Subgroup G}
    (hL : L ∈ calC D.M) (hshape : IsSU3 (Bar2 L) 3)
    (hZ : 3 ∣ Nat.card (Subgroup.center (Bar2 L)))
    {K₁ K₂ : Subgroup G} (hK₁ : K₁ ∈ conjSetOf D.M L) (hK₂ : K₂ ∈ conjSetOf D.M L)
    (hne : K₁ ≠ K₂) :
    4 ≤ CFSG.Open.pRank 3 D.M := by
  classical
  have hZcard : Nat.card (Subgroup.center (Bar2 L)) = 3 :=
    Nat.dvd_antisymm (hCen (Bar2 L) 3 hshape) hZ
  have hK₁C : K₁ ∈ calC D.M := uc22p2214_calC_of_mem_conjSetOf hL hK₁
  have hK₂C : K₂ ∈ calC D.M := uc22p2214_calC_of_mem_conjSetOf hL hK₂
  let C₁ : Subgroup (Bar2 D.M) := barImage D.M K₁
  let C₂ : Subgroup (Bar2 D.M) := barImage D.M K₂
  have hcomm : ∀ a ∈ C₁, ∀ b ∈ C₂, a * b = b * a :=
    fun a ha b hb => uc22p22l_barImage_commute hK₁C hK₂C hne a ha b hb
  have hSU₁ : IsSU3 ↥C₁ 3 := by
    obtain ⟨e⟩ := s13_bar_equiv hK₁C
    exact uc22p20p_isSU3_of_mulEquiv e (isSU3_bar2_of_mem_conjSet hK₁ hshape)
  have hSU₂ : IsSU3 ↥C₂ 3 := by
    obtain ⟨e⟩ := s13_bar_equiv hK₂C
    exact uc22p20p_isSU3_of_mulEquiv e (isSU3_bar2_of_mem_conjSet hK₂ hshape)
  have hZ₁ : Nat.card (Subgroup.center ↥C₁) = 3 := by
    refine Nat.dvd_antisymm (hCen ↥C₁ 3 hSU₁) ?_
    have hcongr : Nat.card (Subgroup.center ↥C₁) =
        Nat.card (Subgroup.center (Bar2 K₁)) := by
      obtain ⟨e⟩ := s13_bar_equiv hK₁C
      exact (Nat.card_congr (Subgroup.centerCongr e).toEquiv).symm
    rw [hcongr]
    obtain ⟨g, -, rfl⟩ := hK₁
    rw [card_center_bar2_map (MulAut.conj g) L, hZcard]
  have hZ₂ : Nat.card (Subgroup.center ↥C₂) = 3 := by
    refine Nat.dvd_antisymm (hCen ↥C₂ 3 hSU₂) ?_
    have hcongr : Nat.card (Subgroup.center ↥C₂) =
        Nat.card (Subgroup.center (Bar2 K₂)) := by
      obtain ⟨e⟩ := s13_bar_equiv hK₂C
      exact (Nat.card_congr (Subgroup.centerCongr e).toEquiv).symm
    rw [hcongr]
    obtain ⟨g, -, rfl⟩ := hK₂
    rw [card_center_bar2_map (MulAut.conj g) L, hZcard]
  obtain ⟨x₁, E₁, hx₁ord, hx₁cube, hE₁el, hE₁card, hx₁E⟩ :=
    hK9 ↥C₁ hSU₁ (by rw [hZ₁])
  obtain ⟨x₂, E₂, hx₂ord, hx₂cube, hE₂el, hE₂card, hx₂E⟩ :=
    hK9 ↥C₂ hSU₂ (by rw [hZ₂])
  let x₁' : Bar2 D.M := (x₁ : C₁)
  let x₂' : Bar2 D.M := (x₂ : C₂)
  let E₁' : Subgroup (Bar2 D.M) := E₁.map C₁.subtype
  let E₂' : Subgroup (Bar2 D.M) := E₂.map C₂.subtype
  have hx₁'ord : orderOf x₁' = 9 := by
    change orderOf ((x₁ : C₁) : Bar2 D.M) = 9
    rw [Subgroup.orderOf_coe]
    exact hx₁ord
  have hx₂'ord : orderOf x₂' = 9 := by
    change orderOf ((x₂ : C₂) : Bar2 D.M) = 9
    rw [Subgroup.orderOf_coe]
    exact hx₂ord
  have hE₁'el : IsElemAbelian 3 E₁' := hE₁el.map C₁.subtype
  have hE₂'el : IsElemAbelian 3 E₂' := hE₂el.map C₂.subtype
  have hE₁'card : Nat.card E₁' = 9 := by
    rw [Subgroup.card_map_of_injective C₁.subtype_injective, hE₁card]
  have hE₂'card : Nat.card E₂' = 9 := by
    rw [Subgroup.card_map_of_injective C₂.subtype_injective, hE₂card]
  have hx₁'E : ∀ e ∈ E₁', e * x₁' = x₁' * e := by
    intro e he
    obtain ⟨e₀, he₀, rfl⟩ := Subgroup.mem_map.mp he
    exact congrArg (fun z : C₁ => (z : Bar2 D.M)) (hx₁E e₀ he₀)
  have hx₂'E : ∀ e ∈ E₂', e * x₂' = x₂' * e := by
    intro e he
    obtain ⟨e₀, he₀, rfl⟩ := Subgroup.mem_map.mp he
    exact congrArg (fun z : C₂ => (z : Bar2 D.M)) (hx₂E e₀ he₀)
  have hCinfZ₁ : C₁ ⊓ C₂ ≤ (Subgroup.center ↥C₁).map C₁.subtype := by
    rintro x ⟨hx₁, hx₂⟩
    refine Subgroup.mem_map.mpr ⟨⟨x, hx₁⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact hcomm y y.2 x hx₂
  have hCinfZ₂ : C₁ ⊓ C₂ ≤ (Subgroup.center ↥C₂).map C₂.subtype := by
    rintro x ⟨hx₁, hx₂⟩
    refine Subgroup.mem_map.mpr ⟨⟨x, hx₂⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact (hcomm x hx₁ y y.2).symm
  have hZ₁map : Nat.card ↥((Subgroup.center ↥C₁).map C₁.subtype) = 3 := by
    rw [Subgroup.card_map_of_injective C₁.subtype_injective, hZ₁]
  have hZ₂map : Nat.card ↥((Subgroup.center ↥C₂).map C₂.subtype) = 3 := by
    rw [Subgroup.card_map_of_injective C₂.subtype_injective, hZ₂]
  have hdvd : Nat.card ↥(C₁ ⊓ C₂) ∣ 3 := by
    have h := Subgroup.card_dvd_of_le hCinfZ₁
    rwa [hZ₁map] at h
  have hinter : C₁ ⊓ C₂ = ⊥ ∨
      (Nat.card ↥(C₁ ⊓ C₂) = 3 ∧ x₁' ^ 3 ∈ C₁ ⊓ C₂ ∧ x₂' ^ 3 ∈ C₁ ⊓ C₂) := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact Or.inl (Subgroup.eq_bot_of_card_eq _ h1)
    · have hx₁mem : x₁' ^ 3 ∈ (Subgroup.center ↥C₁).map C₁.subtype := by
        refine Subgroup.mem_map.mpr ⟨x₁ ^ 3, hx₁cube, ?_⟩
        exact SubgroupClass.coe_pow x₁ 3
      have hx₂mem : x₂' ^ 3 ∈ (Subgroup.center ↥C₂).map C₂.subtype := by
        refine Subgroup.mem_map.mpr ⟨x₂ ^ 3, hx₂cube, ?_⟩
        exact SubgroupClass.coe_pow x₂ 3
      have heq₁ : C₁ ⊓ C₂ = (Subgroup.center ↥C₁).map C₁.subtype :=
        Subgroup.eq_of_le_of_card_ge hCinfZ₁ (by rw [h3, hZ₁map])
      have heq₂ : C₁ ⊓ C₂ = (Subgroup.center ↥C₂).map C₂.subtype :=
        Subgroup.eq_of_le_of_card_ge hCinfZ₂ (by rw [h3, hZ₂map])
      exact Or.inr ⟨h3, by rw [heq₁]; exact hx₁mem, by rw [heq₂]; exact hx₂mem⟩
  obtain ⟨F, hFel, hFcard⟩ :=
    CFSG.GroupTheory.exists_elemAbelian_card_eightyOne_of_commuting_pair
      (C₁ := C₁) (C₂ := C₂) (E₁ := E₁') (E₂ := E₂') (x₁ := x₁') (x₂ := x₂')
      hcomm (Subgroup.map_subtype_le E₁) (Subgroup.map_subtype_le E₂) hE₁'el hE₂'el
      hE₁'card hE₂'card (show x₁' ∈ C₁ from x₁.2) (show x₂' ∈ C₂ from x₂.2)
      hx₁'ord hx₂'ord hx₁'E hx₂'E hinter
  have h4bar : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 D.M)) :=
    CFSG.SectionRank.le_pRank (p := 3) (by norm_num) le_top hFel (k := 4) hFcard
  have hnotdvd : ¬ 3 ∣ Nat.card (CFSG.pCore 2 ↥D.M) :=
    CFSG.LocalAnalysis.SQTKTwoCoreQuotient.not_dvd_card_pCore_two Nat.prime_three (by norm_num)
  have hquot := CFSG.SectionRank.pRank_quotient_eq (p := 3) (hp := ⟨Nat.prime_three⟩)
    (N := CFSG.pCore 2 ↥D.M) hnotdvd
  have htop : CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 D.M)) = CFSG.Open.pRank 3 D.M := by
    rw [show CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 D.M)) =
        CFSG.Open.pRank 3 (⊤ : Subgroup ↥D.M) from hquot]
    exact (CFSG.SectionRank.pRank_eq_pRank_top_subgroup D.M).symm
  rwa [htop] at h4bar

theorem gap17_36a_n3_two_Q_of_inputs (D : Data G) (V₀ V L : Subgroup G) (n : ℕ)
    (hSg : UC6S846.SigmaStd D) (hCen : UCK.U3Center) (hK9 : K_SU3EightTorusE9) :
    Gap17_36a_n3_two_Q D V₀ V L n := by
  intro c _ hn hZ hcard h3 Q _
  exfalso
  subst hn
  obtain ⟨K₁, K₂, hne, hset⟩ := Set.ncard_eq_two.mp hcard
  have hK₁ : K₁ ∈ conjSetOf D.M L := by
    rw [hset]
    exact Set.mem_insert_iff.mpr (Or.inl rfl)
  have hK₂ : K₂ ∈ conjSetOf D.M L := by
    rw [hset]
    exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton _))
  exact h3 (hSg.four_mem 3 Nat.prime_three (by norm_num)
    (four_le_pRank_three_of_two_conj_of_three_dvd_center hCen hK9 c.mem_calC c.shape hZ
      hK₁ hK₂ hne))

theorem seventeen_thirtysix_a_of_inputs
    (D : Data G)
    (V₀ V : Subgroup G)
    (h35 : R17_35At D V₀ V) (h1 : ∀ (hV : Hyp125 D V₀ V), R17_1At D V₀ V hV)
    (hSg : UC6S846.SigmaStd D)
    (hCen : UCK.U3Center) (hSyl : UCK.U3Syl) :
    R17_36aAt D V₀ V := by
  have hK3 : Inputs1719.K_BorelTorusAbelian := Inputs1719.k_BorelTorusAbelian_holds
  have hBorel : K_U3CartanRank := Inputs1719.k_U3CartanRank_holds
  have hK : K_SU3EightBorelNine := Inputs1719.k_SU3EightBorelNine_holds
  have hK9 : K_SU3EightTorusE9 := Inputs1719.k_SU3EightTorusE9_holds
  exact seventeen_thirtysix_a_of_subgaps D V₀ V h35.2 h1 hSg hK3 hCen hSyl hBorel
    (fun L n => gap17_36a_n3_two_p_of_inputs D V₀ V L n hK hCen hK3 hSg
      (gap17_36a_n3_two_Q_of_inputs D V₀ V L n hSg hCen hK9))
    (fun L n => gap17_36a_n3_three_torus_of_inputs D V₀ V L n hK hCen hK3)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
