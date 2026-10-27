module

public import CFSG.Quasithin.Vol2.Ch11SecQ9aAmH
public import CFSG.Quasithin.EmptyFaithful.S1421L16
public import CFSG.Quasithin.Background.G2A5Iso
public import CFSG.Quasithin.Vol2.Ch11SecSShape

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 SecA

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isL2Quot_two_of_SL2 {J : Subgroup G}
    (hJ : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
      Nonempty (↥J ⧸ CFSG.pCore 2 ↥J ≃* Matrix.SpecialLinearGroup (Fin 2) F)) :
    IsL2Quot 2 (oTwoQuot ↥J) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hJ
  have : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic (k := 2)
      Nat.prime_two (by norm_num) (by rw [hF]; norm_num)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨f₁⟩ := CFSG.Quasithin.A5Model.sl2_four_equiv_alt5 F hF
    (CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A.card_SL2_four hF)
  have hK : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]; norm_num
  have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2)) = 60 := by
    rw [card_sl_two_gf2 2 (by norm_num)]; norm_num
  obtain ⟨f₂⟩ := CFSG.Quasithin.A5Model.sl2_four_equiv_alt5 (GaloisField 2 2) hK hSL
  have e₀ : oTwoQuot ↥J ≃* (↥J ⧸ CFSG.pCore 2 ↥J) :=
    QuotientGroup.quotientMulEquivOfEq (CFSG.Quasithin.BlueprintB2.pCore_eq_open_pCore 2 ↥J).symm
  exact ⟨e₀.trans (e.trans (f₁.trans (f₂.symm.trans (pslTwoGf2EquivSl 2).symm)))⟩

omit [Finite G] in
theorem card_oTwoQuot_of_SL2 {J : Subgroup G}
    (hJ : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
      Nonempty (↥J ⧸ CFSG.pCore 2 ↥J ≃* Matrix.SpecialLinearGroup (Fin 2) F)) :
    Nat.card (oTwoQuot ↥J) = 60 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hJ
  have e₀ : oTwoQuot ↥J ≃* (↥J ⧸ CFSG.pCore 2 ↥J) :=
    QuotientGroup.quotientMulEquivOfEq (CFSG.Quasithin.BlueprintB2.pCore_eq_open_pCore 2 ↥J).symm
  rw [Nat.card_congr (e₀.trans e).toEquiv, CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A.card_SL2_four hF]

theorem charTwo_normalizer {T L I V₁ V₂ X K : Subgroup G} (h : StarHyp G T L I V₁ V₂ X K)
    {U : Subgroup G} (hU : U ≠ ⊥) (hU2 : IsPGroup 2 ↥U)
    (hTU : T ≤ Subgroup.normalizer (U : Set G)) :
    QuasithinUnique.CharTwo (Subgroup.normalizer (U : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine charTwo_of_inH' h.hyp.fsu.qtke h.sylow ⟨hTU, fun hb => hU ?_⟩
  have := CFSG.LieType.BorelTits.le_pCoreOf_normalizer (r := 2) U hU2
  rw [hb] at this
  exact le_bot_iff.mp this

section Star

variable {T L I V₁ V₂ X K : Subgroup G} {P₁ P₂ : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)}

theorem hyp111At_k0Of (hN : NatFacts) (h1102 : Stmt11_0_2) (h : StarHyp G T L I V₁ V₂ X K)
    (cL : CartanL L V₁ V₂ X) (hP : ParData T K (LOf L V₁) P₁ P₂) :
    Hyp111At (k0Of K P₂) (LOf L V₂) (sXT X T) := by
  have hXV₁ := cartan_le_normalizer_Vi hN h1102 h.hyp (Or.inl rfl) h.v₁ h.cartan
  have hTK₀ := h.T_le_normalizer_k0Of hP
  have hXK₀ := h.cartan_le_normalizer_k0Of hN h1102 hP
  have hB₂ := borelOf_L₂_le hN h1102 h cL
  refine ⟨inferInstance, isPGroup_sXT X T, (sXT_le_T h.sylow).trans hTK₀, ?_,
    Or.inl ⟨2, by norm_num, isL2Quot_two_of_SL2 (k0Of_quot_SL2 h hP)⟩,
    hB₂.trans (sup_le hXK₀ hTK₀), ?_⟩
  · rw [sXT_inf_eq h.sylow (inf_k0Of_le_sXT hN h1102 h hP)]
    exact isSylowTwoOf_inf_of h hTK₀
  · refine charTwo_of_le (charTwo_normalizer h h.V₁_ne_bot h.isPGroup_V₁ h.T_le_normalizer_V₁)
      (sup_le (sup_le ((k0Of_le K P₂).trans h.K_le_normalizer_V₁)
        ((sXT_le_T h.sylow).trans h.T_le_normalizer_V₁))
        (hB₂.trans (sup_le hXV₁ h.T_le_normalizer_V₁))) ?_
    exact (pCoreOf_normalizer_le_sXT h.sylow hXV₁ h.T_le_normalizer_V₁).trans
      (le_sup_right.trans le_sup_left)

theorem hyp111At_L₂ (hN : NatFacts) (h1102 : Stmt11_0_2) (h : StarHyp G T L I V₁ V₂ X K)
    (cL : CartanL L V₁ V₂ X) (hP : ParData T K (LOf L V₁) P₁ P₂) :
    Hyp111At (LOf L V₂) (k0Of K P₂) (sXT X T) := by
  have hXV₂ := cartan_le_normalizer_Vi hN h1102 h.hyp (Or.inr rfl) h.v₂ h.cartan
  have hTV₂ : T ≤ Subgroup.normalizer (V₂ : Set G) := h.v₂.2
  have hXL₂ := cartan_le_normalizer_lOf hN h1102 h.hyp (Or.inr rfl) h.v₂ h.cartan
  have hB₁ := borelOf_k0Of_le hN h1102 h cL hP
  have hV₂ : V₂ ≠ ⊥ := SecA.IsVi.ne_bot h.hyp h.v₂ (by norm_num)
  have hV₂2 : IsPGroup 2 ↥V₂ := (SecA.isPGroup_fsuV h.hyp).to_le (SecA.IsVi.le_fsuV h.v₂)
  refine ⟨inferInstance, isPGroup_sXT X T, (sXT_le_T h.sylow).trans h.T_le_normalizer_L₂, ?_,
    Or.inl ⟨2, by norm_num, isL2Quot_two_of_SL2 (lOf_two_quot_SL2 hN h1102 h)⟩,
    hB₁.trans (sup_le hXL₂ h.T_le_normalizer_L₂), ?_⟩
  · rw [sXT_inf_eq h.sylow (inf_L₂_le_sXT hN h1102 h)]
    exact isSylowTwoOf_inf_of h h.T_le_normalizer_L₂
  · refine charTwo_of_le (charTwo_normalizer h hV₂ hV₂2 hTV₂)
      (sup_le (sup_le ((perfectCore_le _).trans inf_le_right) ((sXT_le_T h.sylow).trans hTV₂))
        (hB₁.trans (sup_le hXV₂ hTV₂))) ?_
    exact (pCoreOf_normalizer_le_sXT h.sylow hXV₂ hTV₂).trans (le_sup_right.trans le_sup_left)

theorem le_normalizer_sup_sXT (hN : NatFacts) (h1102 : Stmt11_0_2)
    (h : StarHyp G T L I V₁ V₂ X K) (hP : ParData T K (LOf L V₁) P₁ P₂) :
    k0Of K P₂ ⊔ LOf L V₂ ⊔ X ⊔ T ≤
      Subgroup.normalizer ((k0Of K P₂ ⊔ LOf L V₂ ⊔ sXT X T : Subgroup G) : Set G) := by
  have hXL₂ := cartan_le_normalizer_lOf hN h1102 h.hyp (Or.inr rfl) h.v₂ h.cartan
  have hXS : X ≤ Subgroup.normalizer (sXT X T : Set G) := le_sup_left.trans (le_normalizer_sXT X T)
  have hTS : T ≤ Subgroup.normalizer (sXT X T : Set G) :=
    le_sup_right.trans (le_normalizer_sXT X T)
  refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
  · exact (le_sup_left.trans le_sup_left).trans Subgroup.le_normalizer
  · exact (le_sup_right.trans le_sup_left).trans Subgroup.le_normalizer
  · exact le_normalizer_sup' (le_normalizer_sup' (h.cartan_le_normalizer_k0Of hN h1102 hP) hXL₂)
      hXS
  · exact le_normalizer_sup' (le_normalizer_sup' (h.T_le_normalizer_k0Of hP) h.T_le_normalizer_L₂)
      hTS

theorem hyp111_of (hN : NatFacts) (h1102 : Stmt11_0_2) (h : StarHyp G T L I V₁ V₂ X K)
    (cL : CartanL L V₁ V₂ X) (hP : ParData T K (LOf L V₁) P₁ P₂)
    (hY : pCoreOf 2 (k0Of K P₂ ⊔ LOf L V₂ ⊔ X ⊔ T) = ⊥) :
    Hyp111 (k0Of K P₂) (LOf L V₂) (sXT X T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨hyp111At_k0Of hN h1102 h cL hP, hyp111At_L₂ hN h1102 h cL hP, ?_⟩
  have hNY : k0Of K P₂ ⊔ LOf L V₂ ⊔ sXT X T ≤ k0Of K P₂ ⊔ LOf L V₂ ⊔ X ⊔ T :=
    sup_le (le_sup_left.trans le_sup_left) ((sXT_le_T h.sylow).trans le_sup_right)
  rw [← le_bot_iff, ← hY]
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hNY)
    ((le_normalizer_sup_sXT hN h1102 h hP).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)

theorem isQuasithinSub_of (h : StarHyp G T L I V₁ V₂ X K) (A : Subgroup G) : IsQuasithinSub A :=
  S1421.isQuasithinSub_of_qtke h.hyp.fsu.qtke A

theorem normal_sXT_sup (hN : NatFacts) (h1102 : Stmt11_0_2) (h : StarHyp G T L I V₁ V₂ X K)
    (cL : CartanL L V₁ V₂ X) (hP : ParData T K (LOf L V₁) P₁ P₂) :
    ((sXT X T).subgroupOf (sXT X T ⊔ borelOf (k0Of K P₂) (sXT X T))).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
    (sup_le Subgroup.le_normalizer
      ((borelOf_k0Of_le hN h1102 h cL hP).trans (le_normalizer_sXT X T)))

end Star

end CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS
