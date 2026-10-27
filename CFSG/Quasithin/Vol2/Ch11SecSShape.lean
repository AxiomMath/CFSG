module

public import CFSG.Quasithin.Vol2.Ch11SecA11Exists
public import CFSG.Quasithin.Vol2.Ch11SecA11Cases2
public import CFSG.Quasithin.Vol2.Ch11SecA11Nonquasi2
public import CFSG.Quasithin.Vol2.Ch11SecA11Transport
public import CFSG.Quasithin.Vol2.Ch11SecSCartanT
public import CFSG.Quasithin.Vol2.Ch11SecSQuot
public import CFSG.Quasithin.Vol2.Ch11SecSSetup

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 SecA

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem perfect_sup {A B : Subgroup G} (hA : ⁅A, A⁆ = A) (hB : ⁅B, B⁆ = B) :
    ⁅A ⊔ B, A ⊔ B⁆ = A ⊔ B := by
  refine le_antisymm ?_ (sup_le ?_ ?_)
  · rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact (A ⊔ B).mul_mem ((A ⊔ B).mul_mem ((A ⊔ B).mul_mem ha hb) ((A ⊔ B).inv_mem ha))
      ((A ⊔ B).inv_mem hb)
  · calc A = ⁅A, A⁆ := hA.symm
      _ ≤ ⁅A ⊔ B, A ⊔ B⁆ := Subgroup.commutator_mono le_sup_left le_sup_left
  · calc B = ⁅B, B⁆ := hB.symm
      _ ≤ ⁅A ⊔ B, A ⊔ B⁆ := Subgroup.commutator_mono le_sup_right le_sup_right

omit [Finite G] in
theorem le_normalizer_sup' {S A B : Subgroup G} (hA : S ≤ Subgroup.normalizer (A : Set G))
    (hB : S ≤ Subgroup.normalizer (B : Set G)) :
    S ≤ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := fun s hs => by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hA hs),
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hB hs)]

omit [Finite G] in
theorem exists_ne_one_of_card_three {H : Subgroup G} (h : Nat.card ↥H = 3) :
    ∃ x ∈ H, x ≠ 1 := by
  have hne : H ≠ ⊥ := fun hb => by
    rw [hb, Subgroup.card_bot] at h
    omega
  obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  exact ⟨x, hx, fun h1 => hx1 (Subtype.ext h1)⟩

theorem modO2Image_inf_ne_bot_of_mem {Y X : Subgroup G} {C : Subgroup (↥Y ⧸ CFSG.pCore 2 ↥Y)}
    (hXY : X ≤ Y) (hX : Odd (Nat.card ↥X)) {x : G} (hx : x ∈ X) (hx1 : x ≠ 1)
    (hC : QuotientGroup.mk' (CFSG.pCore 2 ↥Y) ⟨x, hXY hx⟩ ∈ C) : modO2Image Y X ⊓ C ≠ ⊥ := by
  intro hbot
  have hm : QuotientGroup.mk' (CFSG.pCore 2 ↥Y) ⟨x, hXY hx⟩ ∈ modO2Image Y X ⊓ C :=
    ⟨⟨⟨x, hXY hx⟩, hx, rfl⟩, hC⟩
  rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hm
  have hxO : x ∈ pCoreOf 2 Y := by
    rw [pCoreOf_two_eq_map]
    exact ⟨_, hm, rfl⟩
  have hbot' := inf_eq_bot_of_odd (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y) hX
  have : x ∈ pCoreOf 2 Y ⊓ X := ⟨hxO, hx⟩
  rw [hbot', Subgroup.mem_bot] at this
  exact hx1 this

namespace StarHyp

variable {T L I V₁ V₂ X K : Subgroup G}

theorem concl1111_of_cComp
    (hFp : FactL2Parabolic) (hN : NatFacts) (h1102 : Stmt11_0_2)
    (h36 : A36ForSQTK) (h312 : A312ForSQTK) (h : StarHyp G T L I V₁ V₂ X K)
    {Y I₀ : Subgroup G} (hTY : T ≤ Y) (hL₂Y : LOf L V₂ ≤ Y) (hY : pCoreOf 2 Y ≠ ⊥)
    (hI : I₀ ∈ cComp Y) (hL₂I : LOf L V₂ ≤ I₀) (hne : LOf L V₂ ≠ I₀) :
    Concl1111 (↥I₀ ⧸ CFSG.pCore 2 ↥I₀) 2 := by
  have hS := isSylowTwoOf_of_quasithinIsSylowTwo h.sylow hTY
  have hB := lOf_mem_lFamily hN h1102 h.hyp h.v₂ (Or.inr rfl) (le_refl T)
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := lOf_quot_SL2 hN h1102 h.hyp (Or.inr rfl) h.v₂
  obtain ⟨e₁⟩ := modO2Image_quotEquiv hL₂Y
  have hD := barData_of_quot_SL2 h.hyp.one_lt hF (e₁.symm.trans e)
  obtain ⟨e₂⟩ := modO2_mulEquiv hI
  rcases CFSG.Quasithin.lemma_1_2_4_list h.hyp.fsu.qtke h.hyp.fsu.simple h.hyp.fsu.nonabelian
      h312 hY hS hL₂Y hB hI hL₂I with heq | hcase | hnq
  · exact absurd (eq_of_modO2Image_eq hS (le_of_mem_cComp hI) hL₂I (perfect_of_mem_cComp hI)
      h.T_le_normalizer_L₂ heq) hne
  · exact Concl1111.of_mulEquiv e₂.symm (concl_of_a312Case hFp hD hcase)
  · have hQ := sqtkHyp_quotient_of_pCoreOf_ne_bot h.hyp.fsu.qtke h.hyp.fsu.simple
      h.hyp.fsu.nonabelian hY
    have hBL : modO2Image Y (LOf L V₂) ≤ modO2Image Y I₀ :=
      Subgroup.map_mono fun x hx => hL₂I hx
    exact Concl1111.of_mulEquiv e₂.symm
      (concl_of_nonquasi hD hBL (h36 _ hQ _ (modO2Image_mem_cComp hI)) hnq)

end StarHyp

end CFSG.Quasithin.Vol2.Ch11.SecS
