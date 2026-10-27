module

public import CFSG.Quasithin.Vol2.Ch11SecSShape
public import CFSG.Quasithin.Vol2.Ch11SecSFacts3
public import CFSG.Quasithin.Vol2.Ch11SecSPGL
public import CFSG.Quasithin.Vol2.Ch11SecSXK3

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 SecA

structure InspData {Q : Type} [Group Q] (S B₁ B₂ E : Subgroup Q) : Prop where
  syl : QuasithinUnique.IsSylowTwoOf S ⊤
  ne : B₁ ≠ B₂
  ne₁ : B₁ ≠ ⊥
  ne₂ : B₂ ≠ ⊥
  p₁ : ⁅B₁, B₁⁆ = B₁
  p₂ : ⁅B₂, B₂⁆ = B₂
  n₁ : S ≤ Subgroup.normalizer (B₁ : Set Q)
  n₂ : S ≤ Subgroup.normalizer (B₂ : Set Q)
  sl₁ : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
    Nonempty (↥B₁ ⧸ CFSG.pCore 2 ↥B₁ ≃* Matrix.SpecialLinearGroup (Fin 2) F)
  sl₂ : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
    Nonempty (↥B₂ ⧸ CFSG.pCore 2 ↥B₂ ≃* Matrix.SpecialLinearGroup (Fin 2) F)
  card : Nat.card ↥E = 9
  exp : ∀ e ∈ E, e ^ 3 = 1
  e₁ : E ≤ Subgroup.normalizer (B₁ : Set Q)
  e₂ : E ≤ Subgroup.normalizer (B₂ : Set Q)
  m₁ : E ⊓ B₁ ≠ ⊥
  m₂ : E ⊓ B₂ ≠ ⊥
  c₁ : E ⊓ sectionCentralizer B₁ (pCoreOf 2 B₁) ≠ ⊥
  c₂ : E ⊓ sectionCentralizer B₂ (pCoreOf 2 B₂) ≠ ⊥

theorem InspData.shape {Q : Type} [Group Q] [Finite Q] {S B₁ B₂ E : Subgroup Q}
    (hIns : FactShapeInspect) (hD : InspData S B₁ B₂ E) (hc : Concl1111 Q 2)
    (hJ : ¬ IsSporadic .J4 Q) : Shape4 Q ∧ B₁ ⊔ B₂ = ⊤ :=
  hIns Q hc hJ S B₁ B₂ E hD.syl hD.ne hD.ne₁ hD.ne₂ hD.p₁ hD.p₂ hD.n₁ hD.n₂ hD.sl₁ hD.sl₂
    hD.card hD.exp hD.e₁ hD.e₂ hD.m₁ hD.m₂ hD.c₁ hD.c₂

theorem ne_top_of_sl2 {Q : Type} [Group Q] [Finite Q] (hQ : IsPSL 3 2 2 Q) {B : Subgroup Q}
    (hB : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
      Nonempty (↥B ⧸ CFSG.pCore 2 ↥B ≃* Matrix.SpecialLinearGroup (Fin 2) F)) : B ≠ ⊤ := by
  rintro rfl
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hB
  obtain ⟨a, ha⟩ := card_of_quot_SL2 (n := 2) (hF.trans (by norm_num)) e
  rw [Subgroup.card_top, card_L34 hQ] at ha
  have h1 := eq_of_two_pow_mul_odd (a := 6) (b := a + 2) (by decide) (odd_oSL2 (by norm_num)) ha
  rw [← h1] at ha
  have h2 : (315 : ℕ) = oSL2 2 := Nat.eq_of_mul_eq_mul_left (by positivity) ha
  exact absurd h2 (by decide)

theorem InspData.false_of_isPSL {Q : Type} [Group Q] [Finite Q] {S B₁ B₂ E : Subgroup Q}
    (hNo : FactL34NoE9) (hD : InspData S B₁ B₂ E) (hQ : IsPSL 3 2 2 Q) : False :=
  hNo Q hQ S hD.syl B₁ B₂ hD.ne hD.ne₁ hD.ne₂ (ne_top_of_sl2 hQ hD.sl₁) (ne_top_of_sl2 hQ hD.sl₂)
    hD.p₁ hD.p₂ hD.n₁ hD.n₂ E hD.e₁ hD.e₂ hD.card

variable {G : Type} [Group G] [Finite G]

namespace StarHyp

variable {T L I V₁ V₂ X K : Subgroup G}

theorem inspData (hN : NatFacts) (h1102 : Stmt11_0_2) (h : StarHyp G T L I V₁ V₂ X K)
    (cL : CartanL L V₁ V₂ X) {K₀ I₀ : Subgroup G} (hK₀p : ⁅K₀, K₀⁆ = K₀) (hK₀ne : K₀ ≠ ⊥)
    (hTK₀ : T ≤ Subgroup.normalizer (K₀ : Set G)) (hXK₀ : X ≤ Subgroup.normalizer (K₀ : Set G))
    (hK₀L : ¬ K₀ ≤ Subgroup.normalizer (L : Set G))
    (hK₀SL : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
      Nonempty (↥K₀ ⧸ CFSG.pCore 2 ↥K₀ ≃* Matrix.SpecialLinearGroup (Fin 2) F))
    (hXK₀b : X ⊓ K₀ ≠ ⊥) (hX₁ : xOne X K₀ ≠ ⊥) (hTI₀ : T ≤ Subgroup.normalizer (I₀ : Set G))
    (hK₀I₀ : K₀ ≤ I₀) (hL₂I₀ : LOf L V₂ ≤ I₀) (hXI₀ : X ≤ I₀) :
    InspData (modO2Image I₀ (T ⊓ I₀)) (modO2Image I₀ K₀) (modO2Image I₀ (LOf L V₂))
      (modO2Image I₀ X) := by
  have hL₂L : LOf L V₂ ≤ Subgroup.normalizer (L : Set G) :=
    ((perfectCore_le _).trans inf_le_left).trans Subgroup.le_normalizer
  have hSI : QuasithinUnique.IsSylowTwoOf (T ⊓ I₀) I₀ :=
    A4.isSylowTwoOf_inf_normal (isSylowTwoOf_of_quasithinIsSylowTwo h.sylow le_sup_right)
      le_sup_left (sup_le Subgroup.le_normalizer hTI₀)
  have hOI : pCoreOf 2 I₀ ≤ T := (pCoreOf_two_le_of_isSylowTwoOf hSI).trans inf_le_left
  have hQs := isSolvable_pCoreOf_two I₀
  have hTL₂ := h.T_le_normalizer_L₂
  have hL₂p : ⁅LOf L V₂, LOf L V₂⁆ = LOf L V₂ := perfectCore_perfect _
  have hL₂ne : LOf L V₂ ≠ ⊥ :=
    ne_bot_of_mem_cComp (lOf_mem_lFamily hN h1102 h.hyp h.v₂ (Or.inr rfl) le_rfl)
  have hXL₂ : X ≤ Subgroup.normalizer (LOf L V₂ : Set G) :=
    cartan_le_normalizer_lOf hN h1102 h.hyp (Or.inr rfl) h.v₂ h.cartan
  have hXN : X ≤ Subgroup.normalizer (LOf L V₁ : Set G) :=
    cartan_le_normalizer_lOf hN h1102 h.hyp (Or.inl rfl) h.v₁ h.cartan
  have hbot := cartan_inf_lOf_inf_sectionCentralizer hN h1102 h.hyp h.v₁ h.cartan
  have hXodd : Odd (Nat.card ↥X) := h.cartan.2.1
  have hne : modO2Image I₀ K₀ ≠ modO2Image I₀ (LOf L V₂) := by
    intro heq
    apply hK₀L
    have h1 := sup_eq_of_modO2Image_eq hK₀I₀ hL₂I₀ heq
    rw [← perfectCore_sup_eq hK₀p hQs (hOI.trans hTK₀), h1,
      perfectCore_sup_eq hL₂p hQs (hOI.trans hTL₂)]
    exact hL₂L
  have hSL₂ : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
      Nonempty (↥(modO2Image I₀ (LOf L V₂)) ⧸ CFSG.pCore 2 ↥(modO2Image I₀ (LOf L V₂)) ≃*
        Matrix.SpecialLinearGroup (Fin 2) F) := by
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := lOf_quot_SL2 hN h1102 h.hyp (Or.inr rfl) h.v₂
    obtain ⟨e₁⟩ := modO2Image_quotEquiv hL₂I₀
    exact ⟨F, inferInstance, inferInstance, hF.trans (by norm_num), ⟨e₁.symm.trans e⟩⟩
  have hSL₁ : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
      Nonempty (↥(modO2Image I₀ K₀) ⧸ CFSG.pCore 2 ↥(modO2Image I₀ K₀) ≃*
        Matrix.SpecialLinearGroup (Fin 2) F) := by
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hK₀SL
    obtain ⟨e₁⟩ := modO2Image_quotEquiv hK₀I₀
    exact ⟨F, inferInstance, inferInstance, hF, ⟨e₁.symm.trans e⟩⟩
  have hcard : Nat.card ↥(modO2Image I₀ X) = 9 := by
    rw [card_modO2Image_of_odd hXI₀ hXodd, card_cartan cL hXN hbot]
  have hexp : ∀ e ∈ modO2Image I₀ X, e ^ 3 = 1 := by
    rintro _ ⟨⟨x, hx⟩, hxX, rfl⟩
    have h3 : (⟨x, hx⟩ : ↥I₀) ^ 3 = 1 :=
      Subtype.ext (by simpa using pow_three_cartan cL hXN hbot hxX)
    rw [← map_pow, h3, map_one]
  obtain ⟨x₁, hx₁, hx₁1⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left hXK₀b
  obtain ⟨x₂, hx₂, hx₂1⟩ := exists_ne_one_of_card_three cL.card₂
  obtain ⟨x₃, hx₃, hx₃1⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left hX₁
  obtain ⟨x₄, hx₄, hx₄1⟩ := exists_ne_one_of_card_three cL.cardX₂
  exact ⟨isSylowTwoOf_modO2Image hSI, hne, modO2Image_ne_bot hK₀I₀ hK₀p hK₀ne,
    modO2Image_ne_bot hL₂I₀ hL₂p hL₂ne, modO2Image_perfect hK₀I₀ hK₀p,
    modO2Image_perfect hL₂I₀ hL₂p, modO2Image_le_normalizer (inf_le_left.trans hTK₀),
    modO2Image_le_normalizer (inf_le_left.trans hTL₂), hSL₁, hSL₂, hcard, hexp,
    modO2Image_le_normalizer hXK₀, modO2Image_le_normalizer hXL₂,
    modO2Image_inf_ne_bot_of_mem hXI₀ hXodd hx₁.1 hx₁1 ⟨⟨x₁, hXI₀ hx₁.1⟩, hx₁.2, rfl⟩,
    modO2Image_inf_ne_bot_of_mem hXI₀ hXodd hx₂.1 hx₂1 ⟨⟨x₂, hXI₀ hx₂.1⟩, hx₂.2, rfl⟩,
    modO2Image_inf_ne_bot_of_mem hXI₀ hXodd hx₃.1 hx₃1
      (mk_mem_sectionCentralizer hK₀I₀ (hXI₀ hx₃.1) hx₃.2),
    modO2Image_inf_ne_bot_of_mem hXI₀ hXodd hx₄.1 hx₄1
      (mk_mem_sectionCentralizer hL₂I₀ (hXI₀ hx₄.1) hx₄.2)⟩

end StarHyp

end CFSG.Quasithin.Vol2.Ch11.SecS
