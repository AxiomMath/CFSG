module

public import CFSG.Quasithin.Background.S1567V6c
public import CFSG.Quasithin.MS93.C134L32CorrMOne

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped Matrix commutatorElement

namespace S1567

section Corr

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ E : Subgroup G} {t s : G}

theorem alpha153_eq_one_of_mem_commutator (h113 : StageLemma14113) (c : Ctx153 G T Mc M V₁ V₂ t)
    (ld : LineData153 T M V₁ V₂ E) (r66 : Res15366B T Mc M V₁ V₂ E)
    (r68 : Res15368NoTwo T Mc M E s) {A B : Subgroup G} (hA : A ≤ G0_153 T Mc M E s)
    (hB : B ≤ G0_153 T Mc M E s) :
    ∀ x ∈ ⁅A, B⁆, ∃ hx : x ∈ G0_153 T Mc M E s,
      alpha153 T Mc M E s r68.le_normalizer ⟨x, hx⟩ = 1 := by
  have hcard := card_mulAut_quot_YE h113 c ld r66
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcyc : IsCyclic (MulAut (↥(YE153 Mc M E) ⧸ CFSG.Open.pCore 2 ↥(YE153 Mc M E))) :=
    isCyclic_of_prime_card hcard
  have hcomm : IsMulCommutative (MulAut (↥(YE153 Mc M E) ⧸ CFSG.Open.pCore 2 ↥(YE153 Mc M E))) :=
    (MonoidHom.id _).isMulCommutative_of_isCyclic_of_ker_le_center (by simp)
  have hker : ⁅A, B⁆ ≤ (alpha153 T Mc M E s r68.le_normalizer).ker.map
      (G0_153 T Mc M E s).subtype := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    refine ⟨⁅(⟨g₁, hA hg₁⟩ : ↥(G0_153 T Mc M E s)), ⟨g₂, hB hg₂⟩⁆, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact hcomm.is_comm.comm _ _
  intro x hx
  obtain ⟨y, hy, hyx⟩ := hker hx
  subst hyx
  exact ⟨y.2, hy⟩

theorem c134Q_le_centralizer_V (h113 : StageLemma14113) (k : Ctx67 G T Mc M V₁ V₂ E t)
    (r67 : Res15367 T Mc M V₁ V₂ E) (gl : GoldLine153 T V₁ E s) (r68 : Res15368NoTwo T Mc M E s)
    {L : Subgroup G} (hLG : L ≤ G0_153 T Mc M E s) :
    c134Q (G0_153 T Mc M E s) L ≤ Subgroup.centralizer (VZ T M : Set G) := by
  unfold c134Q
  rw [Subgroup.commutator_le]
  intro q hq l hl
  have hmem : ⁅q, l⁆ ∈ ⁅pCoreOf 2 (G0_153 T Mc M E s), L⁆ :=
    Subgroup.commutator_mem_commutator hq hl
  have hQ : ⁅q, l⁆ ∈ pCoreOf 2 (G0_153 T Mc M E s) := c134Q_le_pCoreOf hLG hmem
  obtain ⟨hxG, hα⟩ :=
    alpha153_eq_one_of_mem_commutator h113 k.c k.L k.r66 r68 (pCoreOf_le 2 _) hLG _ hmem
  exact pCore_inf_ker_alpha_le_centralizer_V h113 k r67 gl r68 hQ hxG hα

theorem false_of_c134Case4_corrM (h113 : StageLemma14113) (k : Ctx67 G T Mc M V₁ V₂ E t)
    (r67 : Res15367 T Mc M V₁ V₂ E) (gl : GoldLine153 T V₁ E s) (r68 : Res15368NoTwo T Mc M E s)
    {L : Subgroup G} (hLG : L ≤ G0_153 T Mc M E s) (hO : oTwoUpper (G0_153 T Mc M E s) ≤ L)
    (α₀ : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2))) (h₀s : Function.Surjective α₀)
    (h₀k : α₀.ker = CFSG.pCore 2 ↥L)
    (h : C134Case4Min (G0_153 T Mc M E s) (TE153 T E) L) : False := by
  obtain ⟨⟨n, F, _, _, α, hF, ⟨hαs, hαk⟩, -, -, hU, -, -⟩, -⟩ := h
  have hF2 := card_field_eq_two α₀ h₀s h₀k α hαs hαk
  have hU8 : Nat.card ↥(⁅centerOf (c134Q (G0_153 T Mc M E s) L), L⁆) = 8 := by
    have h3 := card_of_isSumOfNaturalModulesVia hU
    rw [Subgroup.card_bot, hF2, Fintype.card_fin] at h3
    rw [h3]
    norm_num
  have hQV := c134Q_le_centralizer_V h113 k r67 gl r68 hLG
  have hVQ : VZ T M ≤ c134Q (G0_153 T Mc M E s) L :=
    (V_le_Q k gl r68).trans (Subgroup.commutator_mono le_rfl hO)
  have hVZ : VZ T M ≤ centerOf (c134Q (G0_153 T Mc M E s) L) := by
    intro v hv
    refine ⟨hVQ hv, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
    exact (Subgroup.mem_centralizer_iff.mp (hQV hx) v hv).symm
  have hVU : VZ T M ≤ ⁅centerOf (c134Q (G0_153 T Mc M E s) L), L⁆ :=
    calc VZ T M = ⁅VZ T M, YF153 Mc M E s⁆ := (comm_V_YF k gl).symm
      _ ≤ _ := Subgroup.commutator_mono hVZ (YF_le_oTwoUpper_G0.trans hO)
  have hle := Subgroup.card_le_of_le hVU
  rw [k.c.hyp.card_VZ, hU8] at hle
  omega

theorem false_of_c134Case4_corr (h113 : StageLemma14113) (k : Ctx67 G T Mc M V₁ V₂ E t)
    (r67 : Res15367 T Mc M V₁ V₂ E) (gl : GoldLine153 T V₁ E s) (r68 : Res15368NoTwo T Mc M E s)
    {L : Subgroup G} (hLG : L ≤ G0_153 T Mc M E s) (hO : oTwoUpper (G0_153 T Mc M E s) ≤ L)
    (α₀ : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2))) (h₀s : Function.Surjective α₀)
    (h₀k : α₀.ker = CFSG.pCore 2 ↥L)
    (h : MS93.IsC134Case4Corr (G0_153 T Mc M E s) (TE153 T E) L) : False :=
  false_of_c134Case4_corrM h113 k r67 gl r68 hLG hO α₀ h₀s h₀k
    (CFSG.Quasithin.MS93.IsC134CaseCorr.toCaseM (i := 4) h)

end Corr

end S1567

theorem input15368PsiL3Loc_of_c134_corrM (h11 : StageLemma14111) (h113 : StageLemma14113)
    (hM : C134L32CorrM) (hcase3 : Case3Excl) : Input15368PsiL3Loc := by
  intro G _ _ T Mc M V₁ V₂ E t s c r45 r46 r49 r50 ld r66 r67 gl r68 hL3
  have k : Ctx67 G T Mc M V₁ V₂ E t :=
    ⟨c, r45, r46, r49, r50, ld, r66, ⟨r67.sylow_GE, r67.baum_le, r67.CGS_le⟩⟩
  obtain ⟨L, hL, hN, hprod, ⟨α, hαs, hαk⟩, hMSP⟩ :=
    S1567.exists_L_isMSPair h11 h113 k r67 gl r68 hL3
  have hLG : L ≤ G0_153 T Mc M E s := le_of_mem_cComp hL
  have hn : ∃ (F : Type) (_ : Field F) (_ : Fintype F)
      (α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)),
      Fintype.card F = 2 ∧ IsModO2Surj L α :=
    ⟨ZMod 2, inferInstance, inferInstance, α, ZMod.card 2, ⟨hαs, hαk⟩⟩
  obtain ⟨i, hi⟩ := hM G (G0_153 T Mc M E s) (TE153 T E) L hMSP hL hprod hn
  have hO : oTwoUpper (G0_153 T Mc M E s) ≤ L :=
    S1567.oTwoUpper_G0_le_of_mul_TE k hN hLG hprod
  have hle : Nat.card ↥⁅pCoreOf 2 (G0_153 T Mc M E s), oTwoUpper (G0_153 T Mc M E s)⁆ ≤
      Nat.card ↥(c134Q (G0_153 T Mc M E s) L) :=
    Subgroup.card_le_of_le (Subgroup.commutator_mono le_rfl hO)
  rcases i with _ | _ | _ | _ | _ | _ | i
  · exact hi.elim
  · have h1 : IsC134Case1 (G0_153 T Mc M E s) (TE153 T E) L := hi
    have := S1567.card_c134Q_of_case1 α hαs hαk h1
    exact hle.trans (by rw [this]; norm_num)
  · have h2 : IsC134Case2 (G0_153 T Mc M E s) (TE153 T E) L := hi
    have := S1567.card_c134Q_of_case2 α hαs hαk h2
    exact hle.trans (by rw [this]; norm_num)
  · have h3 : IsC134Case3 (G0_153 T Mc M E s) (TE153 T E) L := hi
    exact (hcase3 G T Mc M V₁ V₂ E t s L c r45 r46 r49 r50 ld r66 r67 gl r68 hL3 hL hN hprod h3).elim
  · have h4 : C134Case4Min (G0_153 T Mc M E s) (TE153 T E) L := hi
    exact (S1567.false_of_c134Case4_corrM h113 k r67 gl r68 hLG hO α hαs hαk h4).elim
  · have h5 : IsC134Case5 (G0_153 T Mc M E s) (TE153 T E) L := hi
    have := S1567.card_c134Q_of_case5 h5
    exact hle.trans (by rw [this]; norm_num)
  · exact hi.elim

theorem input15368PsiL3Loc_of_ms_corrM (h11 : StageLemma14111) (h113 : StageLemma14113)
    (hM : C134L32CorrM) : Input15368PsiL3Loc :=
  input15368PsiL3Loc_of_c134_corrM h11 h113 hM (S1567.case3Excl h113)

end CFSG.Quasithin
