module

public import CFSG.Quasithin.EmptyFaithful.FLcP0
public import CFSG.Quasithin.Background.FLc3Set
public import CFSG.Quasithin.EmptyFaithful.Der6AGen
public import CFSG.Quasithin.EmptyFaithful.S14117Coprime
public import CFSG.Quasithin.EmptyFaithful.S152UGen

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

theorem input15129MFrattini_of (h159 : StageLemma1519) : Input15129MFrattini := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L n W hc hF
  have hq := hc.base.ctx.qtfe
  have hM := hc.base.ctx.mf
  have hCE := hc.base.ctx.ce
  have hS := hc.base.ctx.setting
  have h17 := hc.base.h17
  have h18 := hc.base.h18
  have h24 := hc.base.h24
  have h28 := hc.h28
  have hL := hc.base.hL
  obtain ⟨hP1a, hP1b, hP1c⟩ := input15129P0_holds G T Mc M Z₁ Z₂ V₁ V₂ L n W hc hF
  have h19' : Lemma1519Concl T Mc M := h159 G T Mc M hq hM hCE
  have hLG : L ≤ g1_1516 Z₁ := le_of_mem_cComp hL.comp
  have hSG : s1516 T Z₁ ≤ g1_1516 Z₁ := s1516_le_g1 T Z₁
  have hSyl : IsSylowTwoOf (s1516 T Z₁) (g1_1516 Z₁) := h18.four
  have hSP : ∀ i, s1516 T Z₁ ≤ pPar15129 T Z₁ L n W i := fun i => by
    unfold pPar15129 flagParab
    exact le_inf le_sup_right (le_iInf₂ fun j hj => (hF.flag.2 j hj.1 hj.2.1).2.2.1)
  have hPG : ∀ i, pPar15129 T Z₁ L n W i ≤ g1_1516 Z₁ := fun i =>
    (flagParab_le _ n W i).trans (sup_le hLG hSG)
  have hPSyl : ∀ i, IsSylowTwoOf (s1516 T Z₁) (pPar15129 T Z₁ L n W i) := fun i =>
    A4.isSylowTwoOf_mono hSyl (hSP i) (hPG i)
  have hLN : L ⊔ s1516 T Z₁ ≤ Subgroup.normalizer (L : Set G) :=
    sup_le Subgroup.le_normalizer hF.normalizes
  have hO2L : oTwoUpper (L ⊔ s1516 T Z₁) ≤ L :=
    Der6A.oTwoUpper_le_of_normal_sup le_sup_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hLN) hSyl.2.1 le_sup_right le_rfl
  have hP1d : ¬ oTwoUpper (pPar15129 T Z₁ L n W 1) ≤ mZ1516 Mc Z₁ := by
    intro hY
    apply hP1a
    have hYL : oTwoUpper (pPar15129 T Z₁ L n W 1) ≤ L :=
      (oTwoUpper_mono (flagParab_le _ n W 1)).trans hO2L
    have hYN : oTwoUpper (pPar15129 T Z₁ L n W 1) ≤ Subgroup.normalizer (W 1 : Set G) := by
      have h : oTwoUpper (pPar15129 T Z₁ L n W 1) ≤
          L ⊓ Subgroup.normalizer (zUOf1528 Z₂ L : Set G) := h28.2.2.2 ▸ le_inf hY hYL
      rw [← hF.w1] at h
      exact fun x hx => (h hx).2
    have hSN : s1516 T Z₁ ≤ Subgroup.normalizer (W 1 : Set G) :=
      (hF.flag.2 1 le_rfl (by rcases hF.n_eq with h | h <;> omega)).2.2.1
    exact (eq_oTwoUpper_sup_of_isSylowTwoOf (hPSyl 1)).le.trans (sup_le hYN hSN)
  have hT2 : IsPGroup 2 T := hq.sylow.1
  have hZT : quasithinOmegaOneCenter T ≤ T := (quasithinOmegaOneCenter_le_center T).trans inf_le_left
  have hT1 : T ≠ ⊥ := fun hbot => hq.omegaOneCenter_ne_bot (le_bot_iff.mp (hZT.trans hbot.le))
  have hJM : Subgroup.normalizer (thompsonJ T : Set G) ≤ M :=
    (S1414.normalizer_thompsonJ_le_CGS hT2 hT1).trans h19'.one_cgs
  have hJle : thompsonJ (s1516 T Z₁) ≤ pCoreOf 2 (pPar15129 T Z₁ L n W 1) := by
    rw [hP1b]
    refine le_inf (B6.thompsonJ_le _) ?_
    rw [h17.jS]
    have h1 : thompsonJ T ≤ Subgroup.centralizer (V154 T Mc M : Set G) :=
      Subgroup.le_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h19'.one_commute)
    exact h1.trans (Subgroup.centralizer_le hS.v2_le)
  have hQS : pCoreOf 2 (pPar15129 T Z₁ L n W 1) ≤ s1516 T Z₁ := by
    rw [hP1b]; exact inf_le_left
  have hJQ : thompsonJ (pCoreOf 2 (pPar15129 T Z₁ L n W 1)) = thompsonJ (s1516 T Z₁) :=
    B6.thompsonJ_eq_of_le hJle hQS
  have hP1J : pPar15129 T Z₁ L n W 1 ≤ Subgroup.normalizer (thompsonJ T : Set G) := by
    intro x hx
    have h1 : x ∈ Subgroup.normalizer (pCoreOf 2 (pPar15129 T Z₁ L n W 1) : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hx
    have h2 := normalizer_le_normalizer_thompsonJ (pCoreOf 2 (pPar15129 T Z₁ L n W 1)) h1
    rw [hJQ, h17.jS] at h2
    exact h2
  have hP1M : pPar15129 T Z₁ L n W 1 ≤ M := fun x hx => hJM (hP1J hx)
  have hY₀Y : oTwoUpper (pPar15129 T Z₁ L n W 1) ≤ oPrimeResidualOf 3 (M ⊓ g1_1516 Z₁) :=
    hP1c.trans (oPrimeResidualOf_mono1516 3 (le_inf hP1M (hPG 1)))
  have hY₀V : ⁅V₂, oTwoUpper (pPar15129 T Z₁ L n W 1)⁆ = V₂ :=
    (h24.three _ (oTwoUpper_idem _) hY₀Y hP1d).1
  have hTM : T ≤ M := hM.1.1.2
  have hMV : M ≤ Subgroup.normalizer (V154 T Mc M : Set G) := le_normalizer_V154 T Mc M
  have hTV : T ≤ Subgroup.normalizer (V154 T Mc M : Set G) := hTM.trans hMV
  have hHM : M ⊓ g1_1516 Z₁ ≤ M := inf_le_left
  have hHV : M ⊓ g1_1516 Z₁ ≤ Subgroup.normalizer (V154 T Mc M : Set G) := hHM.trans hMV
  have hY₀H : oTwoUpper (pPar15129 T Z₁ L n W 1) ≤ oTwoUpper (M ⊓ g1_1516 Z₁) :=
    oTwoUpper_mono (le_inf hP1M (hPG 1))
  have hY₀M : oTwoUpper (pPar15129 T Z₁ L n W 1) ≤ M :=
    ((oTwoUpper_le _).trans hP1M)
  have hY₀V' : oTwoUpper (pPar15129 T Z₁ L n W 1) ≤ Subgroup.normalizer (V154 T Mc M : Set G) :=
    hY₀M.trans hMV
  have hSM : s1516 T Z₁ ≤ T := s1516_le T Z₁
  have hY₀ne : autOn (oTwoUpper (pPar15129 T Z₁ L n W 1)) (V154 T Mc M) ≠ ⊥ := by
    intro hbot
    have hcent : oTwoUpper (pPar15129 T Z₁ L n W 1) ≤ Subgroup.centralizer (V₂ : Set G) := by
      intro y hy
      have hmem := (FLc.mem_autOn_iff (H := oTwoUpper (pPar15129 T Z₁ L n W 1))
        (V := V154 T Mc M)).2 ⟨y, hY₀V' hy, hy, rfl⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have h1 := congrArg (fun a : MulAut ↥(V154 T Mc M) =>
        ((a (⟨v, hS.v2_le hv⟩ : ↥(V154 T Mc M)) : ↥(V154 T Mc M)) : G)) hmem
      simp only [FLc.conjAct_coe (hY₀V' hy)] at h1
      have h2 : y * v * y⁻¹ = v := h1
      calc v * y = (y * v * y⁻¹) * y := by rw [h2]
        _ = y * v := by group
    have hcomm : ⁅V₂, oTwoUpper (pPar15129 T Z₁ L n W 1)⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact Subgroup.le_centralizer_iff.mp hcent
    rw [hcomm] at hY₀V
    have h4 := (hS.ranks_four hF.four).2.1
    rw [← hY₀V, Subgroup.card_bot] at h4
    exact absurd h4 (by norm_num)
  have hprime := (hS.extra_small (Or.inl hF.four)).prime_o2
  have hO : autOn (oTwoUpper (M ⊓ g1_1516 Z₁)) (V154 T Mc M) ≤
      autOn (oTwoUpper (pPar15129 T Z₁ L n W 1)) (V154 T Mc M) := by
    rw [← A4.oTwoUpper_autOn hHV]
    have hle : autOn (oTwoUpper (pPar15129 T Z₁ L n W 1)) (V154 T Mc M) ≤
        oTwoUpper (autOn (M ⊓ g1_1516 Z₁) (V154 T Mc M)) := by
      rw [A4.oTwoUpper_autOn hHV]
      exact A4.autOn_mono hY₀H
    have hdvd := Subgroup.card_dvd_of_le hle
    have hne1 : Nat.card ↥(autOn (oTwoUpper (pPar15129 T Z₁ L n W 1)) (V154 T Mc M)) ≠ 1 :=
      fun h1 => hY₀ne (Subgroup.card_eq_one.1 h1)
    have hcard : Nat.card ↥(autOn (oTwoUpper (pPar15129 T Z₁ L n W 1)) (V154 T Mc M)) =
        Nat.card ↥(oTwoUpper (autOn (M ⊓ g1_1516 Z₁) (V154 T Mc M))) :=
      ((Nat.dvd_prime hprime).1 hdvd).resolve_left hne1
    exact (Subgroup.eq_of_le_of_card_ge hle hcard.ge).ge
  have hHsyl : IsSylowTwoOf (s1516 T Z₁) (M ⊓ g1_1516 Z₁) := by
    rw [inf_comm]
    exact hS.sylow
  have hHeq : M ⊓ g1_1516 Z₁ = oTwoUpper (M ⊓ g1_1516 Z₁) ⊔ s1516 T Z₁ :=
    eq_oTwoUpper_sup_of_isSylowTwoOf hHsyl
  have hautH : autOn (M ⊓ g1_1516 Z₁) (V154 T Mc M) ≤
      autOn (T ⊔ oTwoUpper (pPar15129 T Z₁ L n W 1)) (V154 T Mc M) := by
    have e1 : autOn (M ⊓ g1_1516 Z₁) (V154 T Mc M) =
        autOn (oTwoUpper (M ⊓ g1_1516 Z₁) ⊔ s1516 T Z₁) (V154 T Mc M) :=
      congrArg (fun X => autOn X (V154 T Mc M)) hHeq
    rw [e1, autOn_sup ((oTwoUpper_le _).trans hHV) ((hSM.trans hTV))]
    exact sup_le (hO.trans (A4.autOn_mono le_sup_right)) (A4.autOn_mono (hSM.trans le_sup_left))
  have hautM : autOn M (V154 T Mc M) ≤
      autOn (T ⊔ oTwoUpper (pPar15129 T Z₁ L n W 1)) (V154 T Mc M) := by
    have e2 : autOn M (V154 T Mc M) = autOn ((M ⊓ g1_1516 Z₁) ⊔ T) (V154 T Mc M) :=
      congrArg (fun X => autOn X (V154 T Mc M)) (hS.caseI_small (Or.inl hF.four)).symm
    rw [e2, autOn_sup hHV hTV]
    exact sup_le hautH (A4.autOn_mono le_sup_left)
  intro m hm
  have hmN : m ∈ Subgroup.normalizer (V154 T Mc M : Set G) := hMV hm
  have hmem : conjAct (V154 T Mc M) ⟨m, hmN⟩ ∈ autOn M (V154 T Mc M) :=
    FLc.mem_autOn_iff.2 ⟨m, hmN, hm, rfl⟩
  obtain ⟨x, hxN, hxX, hxeq⟩ := FLc.mem_autOn_iff.1 (hautM hmem)
  have hxM : x ∈ M := (sup_le hTM hY₀M) hxX
  refine ⟨x, hxX, x⁻¹ * m, ⟨M.mul_mem (M.inv_mem hxM) hm, ?_⟩, by group⟩
  show x⁻¹ * m ∈ Subgroup.centralizer (VZ T M : Set G)
  rw [← hS.hV, Subgroup.mem_centralizer_iff]
  intro v hv
  have h1 := congrArg (fun a : MulAut ↥(V154 T Mc M) => ((a ⟨v, hv⟩ : ↥(V154 T Mc M)) : G)) hxeq
  simp only [FLc.conjAct_coe hxN, FLc.conjAct_coe hmN] at h1
  calc v * (x⁻¹ * m) = x⁻¹ * ((x * v * x⁻¹) * m) := by group
    _ = x⁻¹ * ((m * v * m⁻¹) * m) := by rw [h1]
    _ = (x⁻¹ * m) * v := by group

end CFSG.Quasithin
