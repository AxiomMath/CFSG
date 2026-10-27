module

public import CFSG.Quasithin.Vol2.Ch11SecO3Fact
public import CFSG.Quasithin.Vol2.Ch11SecFOblAlpha
public import CFSG.Quasithin.Vol2.Ch11SecFBasic
public import CFSG.Quasithin.Vol2.KGNatTI
public import CFSG.Quasithin.Vol2.Ch11SecD551D

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecF

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13

theorem obl11_5_7Sp4Alpha_of (h1102 : Stmt11_0_2) (h1110 : Stmt11_1_0) (h1112 : Stmt11_1_2)
    (h1141 : Stmt11_4_1) (h1143 : Stmt11_4_3) : Obl11_5_7Sp4Alpha := by
  intro G _ _ T L I n V₁ V₃ X y h hV₁ hV₃ hk _ _ _ hX _ _ _ _ hVQ
  exfalso
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS := SecD.natSetting11_of h1102 h1141 h hV₁
  apply factSp4V3R1X_holds G T L I n V₁ V₃ X hS hk hV₁ hV₃ hX
  set K := KOf L V₁ V₁ with hKdef
  have hRX := ((h1141 G T L I n V₁ X h hV₁ hX).2.2 K
    (SecD.kOf_cComp_centralizer KGNat.pointsTIFact_holds h1102 h1110 h1112 h1141 h1143 h hV₁)
    (le_conjClosure _ _)).2
  have hXN : X ≤ Subgroup.normalizer (pCoreOf 2 (LOf L V₁) : Set G) := fun x hx =>
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _
      (SecD.mem_normalizer_lOf (Subgroup.le_normalizer (hX.1 hx).1)
        (SecO1.cartan_le_normalizer_Vi hS (Or.inl rfl) hV₁ hX hx))
  have h1 : ⁅pCoreOf 2 (LOf L V₁), X⁆ ≤ K ⊓ pCoreOf 2 (K ⊔ T) :=
    le_inf ((Subgroup.le_normalizer_iff_commutator_le_left.mp hXN).trans
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (le_conjClosure _ _)))
      ((Subgroup.commutator_mono (SecA.pCoreOf_lOf_le_ROf h hV₁) le_rfl).trans hRX)
  have h2 : K ⊓ pCoreOf 2 (K ⊔ T) ≤ pCoreOf 2 K :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun k hk => SecD.mem_normalizer_inf (Subgroup.le_normalizer hk)
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ (le_sup_left (α := Subgroup G) hk)))
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_right)
  have h3 : pCoreOf 2 K ≤ pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) :=
    pCoreOf_le_pCoreOf_of_le_normalizer (kOf_le_normalizer_V₁ L V₁)
      (SecD.normalizer_le_normalizer_kOf L V₁ V₁)
  exact eq_bot_iff.mpr ((Subgroup.commutator_mono le_rfl (h1.trans (h2.trans h3))).trans hVQ.le)

end CFSG.Quasithin.Vol2.Ch11.SecF
