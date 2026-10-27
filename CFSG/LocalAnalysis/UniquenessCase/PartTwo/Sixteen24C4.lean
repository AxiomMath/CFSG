module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen24C4Frame
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen24Beta
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenT7Aut
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenCore
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalFamily
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinearStrong
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4FrameM
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSixtyOne
public import CFSG.Quasithin.Background.HFF
public import CFSG.Quasithin.Background.HL3WrNPrime
public import CFSG.Quasithin.Background.HPairBridge
public import CFSG.Quasithin.Background.HSL3Inner
public import CFSG.Sporadic.Schreier.J4SCommGenBase1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

namespace Sixteen24

theorem exists_uFrame_v1Sub_of_case4 {D : Data G} {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (h4 : Case167_4 D V₀ V hV L) :
    Nonempty (UFrame (v1Sub D.M V₀ V hV L) V hV L) :=
  exists_uFrame_of_natSUn (X := v1Sub D.M V₀ V hV L) h4.2.1

theorem wStar_eq_top_of_uFrame (D : Data G) {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    (hV : IsElemAbelian 2 V) (F : UFrame (v1Sub D.M V₀ V hV L) V hV L) :
    wStar D.M V₀ V hV L = ⊤ :=
  (s15_T7_wStar_eq_commSub D h).trans F.wTil_eq_top

theorem wSub_sup_v1Sub_eq_of_uFrame (D : Data G) {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    (hV : IsElemAbelian 2 V) (F : UFrame (v1Sub D.M V₀ V hV L) V hV L) :
    wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L = V :=
  s15_Two_eq_of_imgTil_eq_top hV (s15_T7_wSub_sup_v1Sub_le h) le_sup_right
    ((s15_T7_imgTil_wSub_sup_v1Sub h).trans (wStar_eq_top_of_uFrame D h hV F))

theorem nBar_eq_of_uFrame (D : Data G) {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    (hV : IsElemAbelian 2 V) (F : UFrame (v1Sub D.M V₀ V hV L) V hV L) :
    nBar D.M V₀ V hV L = D.M := by
  rw [← inf_normalizer_wSub_sup_v1Sub_eq_nBar D h hV, wSub_sup_v1Sub_eq_of_uFrame D h hV F]
  exact inf_eq_left.2 h.hyp125.pairFacts.le_normalizer

theorem centralizesMod_v1Sub_iff (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) {m : G} (hm : m ∈ D.M) :
    CentralizesMod (v1Sub D.M V₀ V hV L) V m ↔ CentralizesMod V₀ V m := by
  have key : ∀ X : Subgroup G, m ∈ normalizer (X : Set G) →
      (m ∈ F11.CTilde D.M X V ↔ CentralizesMod X V m) := by
    intro X hX
    unfold F11.CTilde
    simp only [Subgroup.mem_iInf]
    exact ⟨fun hc v hv => (hc v hv).2.2, fun hc v hv => ⟨hm, hX, hc v hv⟩⟩
  rw [← key _ (s15_Infra_le_normalizer_v1Sub h.hyp125 hV hm),
    ← key _ (h.hyp125.pairFacts.le_normalizer₀ hm), fifteen_two_cent D h1217 h hV]

theorem barSub_v1Sub_le_of_le (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) {Y Y' : Subgroup G} (hY : Y ≤ D.M)
    (hY' : Y' ≤ D.M) (hle : barSub V₀ V hV Y ≤ barSub V₀ V hV Y') :
    barSub (v1Sub D.M V₀ V hV L) V hV Y ≤ barSub (v1Sub D.M V₀ V hV L) V hV Y' := by
  have hMs₀ : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  have hMs₁ : D.M ≤ stabTil (v1Sub D.M V₀ V hV L) V := s15_T7_le_stabTil_v1Sub h
  intro φ hφ
  obtain ⟨y, hyY, rfl⟩ := (mem_barSub _ V hV Y φ).1 hφ
  have hyM : (y : G) ∈ D.M := hY hyY
  obtain ⟨y', hy'Y', hyy'⟩ := (mem_barSub V₀ V hV Y' _).1
    (hle (actTil_mem_barSub V₀ V hV hyY (hMs₀ hyM)))
  have hy'M : (y' : G) ∈ D.M := hY' hy'Y'
  have h0 : actTil V₀ V hV (y'⁻¹ * ⟨(y : G), hMs₀ hyM⟩) = 1 := by
    rw [map_mul, map_inv, hyy', inv_mul_cancel]
  have hc0 : CentralizesMod V₀ V ((y' : G)⁻¹ * y) := by
    have h0' := (actTil_eq_one_iff V₀ V hV _).1 h0
    intro v hv
    simpa using h0' v hv
  have hc1 : CentralizesMod (v1Sub D.M V₀ V hV L) V ((y' : G)⁻¹ * y) :=
    (centralizesMod_v1Sub_iff D h1217 h hV (D.M.mul_mem (D.M.inv_mem hy'M) hyM)).2 hc0
  have h1 : actTil (v1Sub D.M V₀ V hV L) V hV (⟨(y' : G), hMs₁ hy'M⟩⁻¹ * y) = 1 :=
    (actTil_eq_one_iff _ V hV _).2 fun v hv => by simpa using hc1 v hv
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  rw [← h1]
  exact actTil_mem_barSub _ V hV hy'Y' (hMs₁ hy'M)

theorem actTil_v1Sub_mem_normalizer (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) {g : G} (hg : g ∈ D.M)
    (hgN : g ∈ nBar D.M V₀ V hV L) (hg₁ : g ∈ stabTil (v1Sub D.M V₀ V hV L) V) :
    actTil (v1Sub D.M V₀ V hV L) V hV ⟨g, hg₁⟩ ∈
      normalizer (lBar (v1Sub D.M V₀ V hV L) V hV L :
        Set (MulAut (Vtil (v1Sub D.M V₀ V hV L) V hV))) := by
  have heq₀ : barSub V₀ V hV (conjSubgroup L g) = barSub V₀ V hV L :=
    (s15_Infra_mem_nBar_iff h.hyp125 hV hg).1 hgN
  have hLM : L ≤ D.M := h.le
  have hLgM : conjSubgroup L g ≤ D.M := by
    intro x hx
    rw [mem_conjSubgroup_iff] at hx
    have e : x = g⁻¹ * (g * x * g⁻¹) * g := by group
    rw [e]
    exact D.M.mul_mem (D.M.mul_mem (D.M.inv_mem hg) (hLM hx)) hg
  have heq₁ : barSub (v1Sub D.M V₀ V hV L) V hV (conjSubgroup L g) =
      barSub (v1Sub D.M V₀ V hV L) V hV L :=
    le_antisymm (barSub_v1Sub_le_of_le D h1217 h hV hLgM hLM heq₀.le)
      (barSub_v1Sub_le_of_le D h1217 h hV hLM hLgM heq₀.ge)
  have hmap : (barSub (v1Sub D.M V₀ V hV L) V hV L).map
      (MulAut.conj (actTil (v1Sub D.M V₀ V hV L) V hV ⟨g, hg₁⟩)⁻¹).toMonoidHom =
        barSub (v1Sub D.M V₀ V hV L) V hV L := by
    rw [← s15_Infra_barSub_conjSubgroup _ V hV hg₁ L]
    exact heq₁
  exact (inv_mem_iff).1 ((Subgroup.mem_normalizer_iff_map_conj_eq).2 hmap)

theorem mBarGT_one_of_case4 (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV) (h4 : Case167_4 D V₀ V hV L) :
    MBarGT D.M V₀ V 1 := by
  have h : Hyp151 D V₀ V L := hS.setting.hyp151
  obtain ⟨F⟩ := exists_uFrame_v1Sub_of_case4 h4
  have hle : v1Sub D.M V₀ V hV L ≤ V := s15_Infra_v1Sub_le h.hyp125 hV
  have h01 : V₀ ≤ v1Sub D.M V₀ V hV L := s15_Infra_le_v1Sub D.M V₀ V hV L
  have hN : nBar D.M V₀ V hV L = D.M := nBar_eq_of_uFrame D h hV F
  refine ⟨fun m hm hnot _ => ?_, fun _ => ?_⟩
  · have hms₁ : m ∈ stabTil (v1Sub D.M V₀ V hV L) V := s15_T7_le_stabTil_v1Sub h hm
    have hnot₁ : ¬ CentralizesMod (v1Sub D.M V₀ V hV L) V m :=
      fun hc => hnot ((centralizesMod_v1Sub_iff D h1217 h hV hm).1 hc)
    have hmN : m ∈ nBar D.M V₀ V hV L := by rw [hN]; exact hm
    have hnorm := actTil_v1Sub_mem_normalizer D h1217 h hV hm hmN hms₁
    have h4' := F.four_mul_card_centMod_le hle hms₁ hnorm hnot₁
    have hsub : centMod V₀ V m ⊆ centMod (v1Sub D.M V₀ V hV L) V m :=
      fun v hv => ⟨hv.1, h01 hv.2⟩
    have hcard : Nat.card (centMod V₀ V m) ≤ Nat.card (centMod (v1Sub D.M V₀ V hV L) V m) :=
      Nat.card_mono (Set.toFinite _) hsub
    calc 2 ^ (1 + 1) * Nat.card (centMod V₀ V m)
        ≤ 2 ^ 2 * Nat.card (centMod (v1Sub D.M V₀ V hV L) V m) := Nat.mul_le_mul_left _ hcard
      _ ≤ Nat.card V := h4'
  · have hcard : Nat.card V₀ ≤ Nat.card (v1Sub D.M V₀ V hV L) := Subgroup.card_le_of_le h01
    rw [F.card_V_of_le hle]
    calc 2 ^ (1 + 1) * Nat.card V₀ ≤ 2 ^ (1 + 1) * Nat.card (v1Sub D.M V₀ V hV L) :=
          Nat.mul_le_mul_left _ hcard
      _ ≤ 2 ^ 8 * Nat.card (v1Sub D.M V₀ V hV L) :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by norm_num))

theorem k_lt_betaN_of_case4 (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (h1217 : R1217 D) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV)
    (h4 : Case167_4 D V₀ V hV L) : (D.k : ℕ∞) < betaN 0 D.M V := by
  have hk : D.k = 1 :=
    Data.k_eq_one_of_three_mem D hSg h1219 (by rw [h4.2.2]; exact Set.mem_singleton 3)
  rw [hk]
  exact lt_betaN_zero_of_mBarGT D hS.setting.hyp16.hyp125 (mBarGT_one_of_case4 D h1217 hS h4)

end Sixteen24

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
