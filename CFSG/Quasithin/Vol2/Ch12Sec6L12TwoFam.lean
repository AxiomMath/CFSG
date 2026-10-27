module

public import CFSG.Quasithin.Vol2.Ch12Sec6L12TwoCore
public import CFSG.GH74.SmallRanks.PSL
public import CFSG.GH74.Filter.Small.RankThree
public import CFSG.GH74.KGroups.CoverEven
public import CFSG.GH74.GLS.Stage4.LocalSE
public import CFSG.Milestones.CL_LIT_Borel_Tits_local_parabolic
public import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.Quasithin.Background.KGSchurMult2Pf

public section

namespace CFSG.Quasithin.H13.K1262Two

open CFSG.Open CFSG.Blueprint Subgroup

structure XData {X : Type} [Group X] [Finite X] (Y F : Subgroup X) : Prop where
  cfg : A6Config Y F
  card16 : 16 ≤ Nat.card ↥F
  dvd5760 : 5760 ∣ Nat.card X
  four : 4 ≤ CFSG.Open.twoRank X

theorem sixteen_dvd_of_elemAbelian {X : Type} [Group X] [Finite X] {F : Subgroup X}
    (hF : IsElemAbelian 2 F) (h16 : 16 ≤ Nat.card ↥F) : 16 ∣ Nat.card ↥F := by
  have hP : IsPGroup 2 ↥F := fun g => ⟨1, Subtype.ext (by simpa using hF.2 g.1 g.2)⟩
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hn4 : 4 ≤ n := by
    by_contra hlt
    have : 2 ^ n < 2 ^ 4 := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  rw [hn]
  exact pow_dvd_pow 2 hn4

theorem isPGroup_pCoreOf {X : Type} [Group X] (Y : Subgroup X) : IsPGroup 2 ↥(pCoreOf 2 Y) := by
  intro g
  obtain ⟨w, hw, hwg⟩ := Subgroup.mem_map.mp g.2
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥Y)) ⟨w, hw⟩
  refine ⟨k, Subtype.ext ?_⟩
  have hk' : w ^ 2 ^ k = 1 := congrArg Subtype.val hk
  rw [Subgroup.coe_pow, Subgroup.coe_one, ← hwg, ← map_pow, hk', map_one]

theorem xdata_of_config {X : Type} [Group X] [Finite X] {Y F : Subgroup X}
    (hY : A6Config Y F) (h16 : 16 ≤ Nat.card ↥F) : XData Y F where
  cfg := hY
  card16 := h16
  dvd5760 := five_dvd_of_config hY (sixteen_dvd_of_elemAbelian hY.2.2.2.1 h16)
  four := four_le_twoRank_of_config hY.2.2.2.1 h16

theorem false_of_card_not_dvd {X : Type} [Group X] [Finite X] {Y F : Subgroup X}
    (hD : XData Y F) {c : ℕ} (hc : Nat.card X = c) (hnd : ¬ 5760 ∣ c) : False :=
  hnd (hc ▸ hD.dvd5760)

theorem false_of_lt16 {X : Type} [Group X] [Finite X] {Y F : Subgroup X}
    (hD : XData Y F) (h : Nat.card ↥F < 16) : False := by
  have := hD.card16
  omega

theorem card_alt_fin (m : ℕ) (hm : 2 ≤ m) : Nat.card (alternatingGroup (Fin m)) = m.factorial / 2 := by
  haveI : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem false_of_alt_fin {X : Type} [Group X] [Finite X] {Y F : Subgroup X} (hD : XData Y F)
    {n : ℕ} (h5 : 5 ≤ n) (h8 : n ≤ 8) (e : X ≃* alternatingGroup (Fin n)) : False := by
  have hc : Nat.card X = Nat.card (alternatingGroup (Fin n)) := Nat.card_congr e.toEquiv
  rw [card_alt_fin n (by omega)] at hc
  exact false_of_card_not_dvd hD hc (by interval_cases n <;> norm_num [Nat.factorial])

theorem false_of_odd {X : Type} [Group X] [Finite X] {Y F : Subgroup X} (hD : XData Y F)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : (∃ f : ℕ, (f = 1 ∨ f = 2) ∧ StatedClassicalModel X .PSL 2 p f) ∨
      StatedClassicalModel X .PSL 3 p 1 ∨ StatedClassicalModel X .PSU 3 p 1) : False := by
  have hrk : CFSG.Open.twoRank X ≤ 2 := by
    rcases h with ⟨f, -, hf⟩ | hf | hf
    · exact CFSG.GH74.SmallRanks.twoRank_le_two_of_statedClassicalModel_PSL_two_odd hp hp2 hf
    · exact CFSG.GH74.Filter.t_PSL_three_odd X p 1 hp2 hf
    · exact CFSG.GH74.Filter.t_PSU_three_odd X p 1 hp2 hf
  have := hD.four
  omega

theorem false_of_L2_even {X : Type} [Group X] [Finite X] {Y F : Subgroup X} (hD : XData Y F)
    {f : ℕ} (hf : 2 ≤ f) (h : StatedClassicalModel X .PSL 2 2 f) : False := by
  have hL : LieModel X .PSL 2 2 f := Or.inl ⟨by decide, h⟩
  obtain ⟨e⟩ := CFSG.GH74.KGroups.equiv_psl2_of_lieModel_even hf hL
  have hS : ∀ S : Sylow 2 X, ∀ x ∈ (S : Subgroup X), ∀ y ∈ (S : Subgroup X), x * y = y * x := by
    intro S x hx y hy
    exact congrArg Subtype.val
      ((CFSG.GH74.GLS.Stage4.sylow_comm_of_psl2Model (by omega) e S).is_comm.comm
        (⟨x, hx⟩ : ↥(S : Subgroup X)) ⟨y, hy⟩)
  obtain ⟨φ, hφs, -⟩ := hD.cfg.2.1
  exact false_of_sylow_comm_alt6 hS Y φ hφs

theorem false_of_levi (hLevi : LeviA6Free) {X : Type} [Group X] [Finite X]
    {t : StatedLieTag} {n f : ℕ} (hfam : Char2LeviFamily t n f) (hmodel : LieModel X t n 2 f)
    {Y F : Subgroup X} (hD : XData Y F) : False := by
  have hU : pCoreOf 2 Y ≠ ⊥ := by
    intro h
    have hF0 : F ≤ ⊥ := h ▸ hD.cfg.2.2.1
    have := Subgroup.card_le_of_le hF0
    rw [Subgroup.card_bot] at this
    have := hD.card16
    omega
  obtain ⟨S, P, hP, hN, -, -, hNS, hTits⟩ :=
    CFSG.Milestones.cl_lit_borel_tits_local_parabolic_all_models X t n 2 f hmodel
      (pCoreOf 2 Y) hU (isPGroup_pCoreOf Y)
  have hYP : Y ≤ P := (le_normalizer_pCoreOf Y).trans hN
  obtain ⟨φ, hφs, -⟩ := hD.cfg.2.1
  exact hLevi X t n f hfam hmodel S P hP hNS hTits Y hYP φ hφs

theorem false_of_sz {X : Type} [Group X] [Finite X] {Y F : Subgroup X} (hD : XData Y F)
    {f : ℕ} (h : SuzukiModel X 2 f) : False := by
  obtain ⟨-, a, -, K, _, _, hfa, hK, ⟨e⟩⟩ := h
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [← hfa]; exact hK
  have hcard : Nat.card X = (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) *
      ((2 ^ (2 * a + 1)) ^ 2 + 1) := by
    rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hK']
  have h3 : 3 ∣ Nat.card X := (by norm_num : 3 ∣ 5760).trans hD.dvd5760
  rw [hcard] at h3
  exact CFSG.GH74.GLS.Stage4.not_three_dvd_suzuki_order a h3

theorem false_of_L4 {X : Type} [Group X] [Finite X] {Y F : Subgroup X} (hD : XData Y F)
    (h : StatedClassicalModel X .PSL 4 2 1) : False :=
  false_of_card_not_dvd hD (CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_four_two h)
    (by norm_num)

theorem card_center_L52_eq_one {K : Type} [Group K] [Finite K] (hK : CFSG.IsQuasisimple K)
    (h : StatedClassicalModel (K ⧸ Subgroup.center K) .PSL 5 2 1) :
    Nat.card ↥(Subgroup.center K) = 1 := by
  have hK' : CFSG.Open.IsQuasisimple K := ⟨Group.isPerfect_def.mp hK.1, hK.2.1⟩
  have := CFSG.Quasithin.SchurMult2.card_center_dvd_row hK' (MulEquiv.refl _)
    (CFSG.LieType.Steinberg.CentralExt.GriessClassical.psl_row h)
  simpa [CFSG.Blueprint.Multiplier.genericOrders, CFSG.Blueprint.Multiplier.exceptionalOrders]
    using this

theorem card_center_M23_eq_one {K : Type} [Group K] [Finite K] (hK : CFSG.IsQuasisimple K)
    (e : K ⧸ Subgroup.center K ≃* CFSG.Blueprint.NativeSporadic.M23) :
    Nat.card ↥(Subgroup.center K) = 1 :=
  CFSG.Sporadic.Recognition.M23Multiplier.card_center_eq_one_of_certificate
    hK.1 e

theorem odd_card_center_M24 {K : Type} [Group K] [Finite K] (hK : CFSG.IsQuasisimple K)
    (e : K ⧸ Subgroup.center K ≃* CFSG.Blueprint.NativeSporadic.M24) :
    Odd (Nat.card ↥(Subgroup.center K)) :=
  CFSG.ComponentClassification.RankTwoSporadic.oddMultiplier_of_noPerfectDoubleCover
    CFSG.Monster.Schur.noPerfectDoubleCover_nativeM24 K (Group.isPerfect_def.mp hK.1) ⟨e⟩

end CFSG.Quasithin.H13.K1262Two
