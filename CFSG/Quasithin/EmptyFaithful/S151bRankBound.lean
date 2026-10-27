module

public import CFSG.Quasithin.EmptyFaithful.S151bSeven
public import CFSG.Quasithin.EmptyFaithful.S151Basic
public import CFSG.Quasithin.Vol2.Ch3Sec1Aux
public import CFSG.Quasithin.EmptyFaithful.S151bShape

public section

namespace CFSG.Quasithin

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_autI_case_one151b {M V : Subgroup G} {A₀ : Subgroup (MulAut V)}
    (h : Case1517One M V A₀) : Nat.card (autOn M V) = 6 := by
  obtain ⟨-, hA, ⟨e⟩⟩ := h
  rw [hA, Nat.card_congr e.toEquiv, DihedralGroup.nat_card]

omit [Finite G] in
theorem card_autI_case_two151b {M V : Subgroup G} {A₀ : Subgroup (MulAut V)}
    (h : Case1517Two M V A₀) : Nat.card (autOn M V) = 18 := by
  obtain ⟨-, -, ⟨e⟩⟩ := h
  have h3 : Nat.card (Multiplicative (ZMod 3)) = 3 := by
    rw [Nat.card_eq_fintype_card]
    rfl
  rw [Nat.card_congr e.toEquiv, Nat.card_prod, DihedralGroup.nat_card, h3]

theorem card_le_four_of_equiv_W3151b {W : Type*} [CommGroup W] [Finite W]
    {X E : Subgroup (MulAut W)} (hE : IsElemAbelian2 E) (hEX : E ≤ X)
    (φ : ↥X ≃* S152N.W3) : Nat.card E ≤ 4 := by
  set E' : Subgroup S152N.W3 := (E.subgroupOf X).map φ.toMonoidHom with hE'
  have hc : ∀ a ∈ E', ∀ b ∈ E', a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have ha' : (a : MulAut W) ∈ E := Subgroup.mem_subgroupOf.mp ha
    have hb' : (b : MulAut W) ∈ E := Subgroup.mem_subgroupOf.mp hb
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hE.1 _ ha' _ hb')
  have h2 : ∀ a ∈ E', a ^ 2 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    have ha' : (a : MulAut W) ∈ E := Subgroup.mem_subgroupOf.mp ha
    rw [← map_pow]
    have : a ^ 2 = 1 := Subtype.ext (by simpa using hE.2 _ ha')
    rw [this, map_one]
  have hle := S152N.card_le_four_of_elemAbelian_W3 hc h2
  have hcardE' : Nat.card E' = Nat.card (E.subgroupOf X) :=
    Subgroup.card_map_of_injective φ.injective
  have hcardE : Nat.card (E.subgroupOf X) = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEX).toEquiv
  rw [← hcardE, ← hcardE']
  exact hle

theorem rank_bound_of_cases151b {T Mc M : Subgroup G} (h : quasithinQTFE14Cat G T Mc)
    (hM : IsMf T Mc M) (hV : IsElemAbelian 2 (V154 T Mc M))
    (hred : IsTwoReducedIn M (V154 T Mc M))
    (hcases : Lemma1517Cases T M (V154 T Mc M) (mBar0 T Mc M))
    (hnot3 : ¬ Case1517Three M (V154 T Mc M) (mBar0 T Mc M))
    (h110 : Case1517Six T M (V154 T Mc M) (mBar0 T Mc M) 3 →
      Nonempty (↥(autOn M (V154 T Mc M)) ≃* S152N.W3))
    (h5 : Case1517Six T M (V154 T Mc M) (mBar0 T Mc M) 5 →
      ∀ E : Subgroup (MulAut (IntMod (V154 T Mc M) hV)), E ≤ autI hV T → IsElemAbelian2 E →
        Nat.card E ≤ 4) :
    ∀ E : Subgroup (MulAut (IntMod (V154 T Mc M) hV)), E ≤ autI hV T → IsElemAbelian2 E →
      Nat.card E ≤ 4 := by
  intro E hET hE
  have hTM : T ≤ M := hM.1.1.2
  have hMN : M ≤ Subgroup.normalizer (V154 T Mc M : Set G) := le_normalizer_V154 T Mc M
  have hEM : E ≤ autI hV M := hET.trans (autI_mono hV hTM)
  have hM2 : pCoreOf 2 M ≠ ⊥ := pCoreOf_ne_bot_of_isTwoLocal hM.1.1.1.1
  have hO2 : pCoreOf 2 (autI hV M) = ⊥ := pCoreOf_autOn_eq_bot_of_isTwoReducedIn hred
  rcases hcases with h1 | h2 | h3 | h4 | h5' | ⟨p, hp, h6⟩ | h7
  · refine (card_le_two_of_not_four_dvd151b hE hEM ?_).trans (by norm_num)
    have := card_autI_case_one151b h1
    change ¬ 4 ∣ Nat.card (autOn M (V154 T Mc M))
    omega
  · refine (card_le_two_of_not_four_dvd151b hE hEM ?_).trans (by norm_num)
    have := card_autI_case_two151b h2
    change ¬ 4 ∣ Nat.card (autOn M (V154 T Mc M))
    omega
  · exact absurd h3 hnot3
  · obtain ⟨-, -, hf⟩ := h4
    obtain ⟨f⟩ := hf
    exact (card_le_two_of_le_cyclic151b hE hET (Or.inr rfl) f).trans (by norm_num)
  · obtain ⟨-, -, hT, -⟩ := h5'
    rcases hT with hT | hT
    · obtain ⟨f⟩ := hT
      exact (card_le_two_of_le_cyclic151b hE hET (Or.inl rfl) f).trans (by norm_num)
    · obtain ⟨f⟩ := hT
      exact (card_le_two_of_le_cyclic151b hE hET (Or.inr rfl) f).trans (by norm_num)
  · rcases hp with rfl | rfl
    · obtain ⟨φ⟩ := h110 h6
      exact card_le_four_of_equiv_W3151b hE hEM φ
    · exact h5 h6 E hET hE
  · obtain ⟨-, -, hP⟩ := h7.2.1
    exact card_le_four_of_threeGroup151b h.qtke hM2 hV hMN hO2 hP hEM hE

end CFSG.Quasithin
