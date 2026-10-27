module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.NPrime
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.L3YC.L3YCF12

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417 CFSG.Quasithin.SBd7
  CFSG.Quasithin.S153D
open scoped commutatorElement Pointwise

namespace Stellmacher.L3YC

theorem centralizes_c134Q_of_N0 (h113 : StageLemma14113) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
    (c : Ctx15316 T Mc M V₁ V₂ Yp I L t) (hq : IsLnTwoQuot L 3) (c12 : Concl15312Two Yp L)
    (hV : ⁅VZ T M, YL153 Yp L⁆ ≠ ⊥) (hYY : Yp = Y153 Mc M)
    (hSL : Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G))
    {t' : G} (ht'T : t' ∈ T) (ht'S : t' ∉ Sgp153 T V₁)
    (hswap : B6.conjSub t' (YL153 Yp L) = YC153 Yp L)
    (h4 : MS93.IsC134Case4Corr (L ⊔ Sgp153 T V₁) (Sgp153 T V₁) L) :
    ∀ g ∈ N0 L, (∃ m : ℕ, g ^ 3 ^ m = 1) →
      (∀ v ∈ c134CQ (L ⊔ Sgp153 T V₁) L, g * v * g⁻¹ = v) →
      ∀ q ∈ c134Q (L ⊔ Sgp153 T V₁) L, g * q * g⁻¹ = q := by
  classical
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.ctx.hyp
  have hyp : Hyp153 G T Mc M := hh.hyp
  have hev : evenRank G ≤ 2 := hyp.qtfe.qtke.2.2
  obtain ⟨hC4, hCsq⟩ := c134CQ_card_four hq h4
  have hlab := SBd5.l3YLLabel_of_l3 h113 h37 h38 SBd3.l3SolvableOverSylow_holds G T Mc M V₁ V₂ Yp
    I L t c hq c12 hV hYY
  have hYLN := Hyp153.Y153_le_normalizer_V h113 hyp hh.decomp
  have hVab : ∀ a ∈ VZ T M, ∀ b ∈ VZ T M, a * b = b * a := fun a ha b hb => by
    have := hyp.elemAbelian.1
    exact setLike_mul_comm ha hb
  have hYCgen : ∀ K : Subgroup G, (∀ y ∈ YC153 Yp L, Odd (orderOf y) → y ∈ K) →
      YC153 Yp L ≤ K := by
    intro K hK
    refine (Subgroup.closure_le K).mpr ?_
    rintro y ⟨hyX, hyodd⟩
    exact hK y (mem_oTwoUpper_of_odd hyX hyodd) hyodd
  obtain ⟨Vc, Vn, -, hF1, hVcCQ, -, -⟩ :=
    Stellmacher.PU.L3YC.pu_f1_f2 h113 h37 h38 c hq c12 hV hYY hSL ht'T ht'S hswap h4
  obtain ⟨Vc', Vn', hsup', hc4', hYCn', hYCc'⟩ : ∃ Vc' Vn' : Subgroup G,
      Vc' ⊔ Vn' = VZ T M ∧ Nat.card Vc' = 4 ∧
      YC153 Yp L ≤ Subgroup.centralizer (Vn' : Set G) ∧
      YC153 Yp L ≤ Subgroup.normalizer (Vc' : Set G) := by
    rcases hlab with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨V₁, V₂, hh.decomp.sup, hh.decomp.card₁, ?_, ?_⟩
      · rw [h2]; exact (oTwoUpper_le _).trans inf_le_right
      · intro y hy
        apply hYLN.1
        rw [h2] at hy
        exact ((oTwoUpper_le _).trans inf_le_left) hy
    · refine ⟨V₂, V₁, by rw [sup_comm]; exact hh.decomp.sup, hh.decomp.card₂, ?_, ?_⟩
      · rw [h2]; exact (oTwoUpper_le _).trans inf_le_right
      · intro y hy
        apply hYLN.2
        rw [h2] at hy
        exact ((oTwoUpper_le _).trans inf_le_left) hy
  have hcomm : ⁅VZ T M, YC153 Yp L⁆ ≤ Vc' :=
    SBd6.comm_le_of_decomp hVab (by rw [sup_comm]; exact hsup') hYCn' hYCc'
  have hVcle : c134CQ (L ⊔ Sgp153 T V₁) L ≤ Vc' := by
    rw [← hVcCQ, ← hF1]
    exact hcomm
  have hVc'eq : c134CQ (L ⊔ Sgp153 T V₁) L = Vc' :=
    Subgroup.eq_of_le_of_card_ge hVcle (by rw [hC4, hc4'])
  have hCne : c134CQ (L ⊔ Sgp153 T V₁) L ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hC4
    omega
  have hCnt : ⁅VZ T M, YC153 Yp L⁆ ≠ ⊥ := by
    rw [hF1, hVcCQ]
    exact hCne
  have hmove : ∃ y ∈ YC153 Yp L, Odd (orderOf y) ∧
      ∃ x ∈ c134CQ (L ⊔ Sgp153 T V₁) L, y * x * y⁻¹ ≠ x := by
    by_contra hcon
    push Not at hcon
    apply hCnt
    have hYCC : YC153 Yp L ≤ Subgroup.centralizer (Vc' : Set G) := by
      refine hYCgen _ fun y hy hodd => ?_
      refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
      have := hcon y hy hodd x (hVc'eq ▸ hx)
      calc x * y = (y * x * y⁻¹) * y := by rw [this]
        _ = y * x := by group
    exact SBd7.commutator_eq_bot_of_centralizes hVab hsup' hYCC hYCn'
  obtain ⟨y, hy, hodd, x, hx, hyx⟩ := hmove
  have hyN : y ∈ N0 L := by
    obtain ⟨-, hyL, -, hyc⟩ := oTwoUpper_le _ hy
    refine ⟨hyL, fun l hl => ?_⟩
    have h1 := (pCoreOf 2 L).inv_mem (hyc l hl)
    have e : (l * y * l⁻¹ * y⁻¹)⁻¹ = y * l * y⁻¹ * l⁻¹ := by group
    rwa [e] at h1
  have hyV : y ∈ Subgroup.normalizer ((c134CQ (L ⊔ Sgp153 T V₁) L : Subgroup G) : Set G) :=
    (N0_le_normalizer hSL h4 hyN).2
  obtain ⟨r, a, hya, x', hx', hmv⟩ := exists_threePart_moves hC4 hCsq hyV hodd ⟨x, hx, hyx⟩
  intro g hg ⟨m, hgm⟩ hgV
  exact centralizes_c134Q_of_N0_of_moved hev hq hSL h4 (pow_mem hyN r) hya ⟨x', hx', hmv⟩ hg hgm hgV

end Stellmacher.L3YC

end CFSG.Quasithin
