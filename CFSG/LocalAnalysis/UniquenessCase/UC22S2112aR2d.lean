module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R76Sig
public import CFSG.LocalAnalysis.UniquenessCase.UCFront07Card
public import CFSG.LocalAnalysis.UniquenessCase.UC6Inst
public import CFSG.LocalAnalysis.UniquenessCase.UC7P3Defs
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR2dL2
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR2Basic
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR2Gamma
import CFSG.LocalAnalysis.UniquenessCase.UC6S846g
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h
import CFSG.LocalAnalysis.UniquenessCase.UC22R82Four
import CFSG.LocalAnalysis.UniquenessCase.UCFront07Use
import CFSG.LocalAnalysis.UniquenessCase.UCFront07CardFour
import CFSG.LocalAnalysis.UniquenessCase.UC22Sec7Three
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.QuotInfBar2
import CFSG.Quasithin.Vol2.Ch3Sec3InspWalterHolds
import CFSG.Quasithin.Vol2.GoldschmidtF134OddDickson
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846d
public import CFSG.LocalAnalysis.UniquenessCase.UCR638
public import CFSG.Quasithin.Background.B2FactorizationResidual

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.UC6S846 (rhoL rhoL_fix_iff rhoL_mk_coe isPGroup_pCoreOf
  eq_one_of_mem_isPGroup_of_mem_isPGroup)

variable {G : Type} [Group G] [Finite G]

theorem uc22s2112r2d_three_le_pRank (hGA : GriessAllModelsStatement) {M L : Subgroup G}
    (hL : L ∈ calC M) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hX : LieModel (BarInf L) .PSL 2 p 3) : 3 ≤ Open.pRank p L := by
  have hp : p.Prime := Fact.out
  have hZ : center (Bar2 L) = ⊥ :=
    uc22s2112r2_center_bar2_eq_bot hGA hL hp2 (fun _ => by norm_num) hX
  have hrad := solvableRadical_eq_pCore_of_center_bar2_eq_bot hL.2.2 hZ
  obtain ⟨eL⟩ := CFSG.Quasithin.H13.NQCore.nonempty_mulEquiv_psl2_odd
    (CFSG.Blueprint.LieModel.statedClassicalModel hX (by decide))
  have hkerL : IsPGroup 2 (QuotientGroup.mk' (CFSG.solvableRadical ↥L)).ker := by
    rw [QuotientGroup.ker_mk', hrad]
    exact CFSG.pCore_isPGroup
  exact uc22s2112r2_le_pRank (QuotientGroup.mk' (CFSG.solvableRadical ↥L))
    (QuotientGroup.mk'_surjective _) hkerL hp hp2
    (CFSG.Quasithin.H13.S3320.le_pRank_of_psl2 (by norm_num) eL)

theorem uc22s2112r2d_bar2_equiv {M L : Subgroup G} (hL : L ∈ calC M) (hZ : center (Bar2 L) = ⊥)
    {p : ℕ} [Fact p.Prime] (hX : LieModel (BarInf L) .PSL 2 p 3) :
    Nonempty (Bar2 L ≃* CFSG.GorensteinWalter.PSL2 (GaloisField p 3)) := by
  obtain ⟨φ⟩ := uc22p21k_barInf_equiv_of_center_bot hL.2.2 hZ
  obtain ⟨eL⟩ := CFSG.Quasithin.H13.NQCore.nonempty_mulEquiv_psl2_odd
    (CFSG.Blueprint.LieModel.statedClassicalModel hX (by decide))
  exact ⟨φ.symm.trans eL⟩

theorem uc22s2112r2d_key {M L : Subgroup G} (hLM : L ≤ M) (hN : M ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (eL : Bar2 L ≃* CFSG.GorensteinWalter.PSL2 (GaloisField p 3))
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p) (hOp : UC22.F10.OpRes q M = M)
    (hrank : 3 ≤ Open.pRank q M) :
    ∃ S E A : Subgroup G, S ≤ L ∧ IsPGroup p S ∧
      (∀ T : Subgroup G, T ≤ L → IsPGroup p T → S ≤ T → T = S) ∧
      E ≤ S ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
      A ≤ M ∧ A ≤ centralizer (E : Set G) ∧ IsElemAbelian q A ∧ Nat.card A = q ^ 2 ∧
      ∃ Sb : Subgroup (Bar2 L), IsPGroup p Sb ∧ ¬ p ∣ Sb.index ∧
        (S.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) = Sb := by
  classical
  have hp : p.Prime := Fact.out
  have : Fact q.Prime := ⟨hq⟩
  set N : Subgroup G := normalizer (L : Set G) with hNdef
  set O : Subgroup G := pCoreOf 2 L with hOdef
  let π : ↥L →* Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  have hker : IsPGroup 2 π.ker := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hNO : N ≤ normalizer (O : Set G) := UC6S846.normalizer_le_normalizer_pCoreOf L
  have hLN : L ≤ N := Subgroup.le_normalizer
  have hOpg : IsPGroup 2 O := UC6S846.isPGroup_pCoreOf L
  have hOL : O ≤ L := Subgroup.map_subtype_le _
  obtain ⟨A₀, hA₀M, hA₀el, hA₀card⟩ := UC6S846.exists_elemAbelian_card_of_le_pRank hq hrank
  let ρ : ↥N →* MulAut (Bar2 L) := UC6S846.rhoL L
  let A₀N : Subgroup ↥N := A₀.subgroupOf N
  have hA₀N : A₀ ≤ N := hA₀M.trans hN
  have hA₀Nel : IsElemAbelian q A₀N := hA₀el.subgroupOf N
  let R : Subgroup (MulAut (Bar2 L)) := A₀N.map ρ
  have hRel : IsElemAbelian q R := hA₀Nel.map ρ
  have hRi : R ≤ (MulAut.conj : Bar2 L →* MulAut (Bar2 L)).range := by
    let MN : Subgroup ↥N := M.subgroupOf N
    have hgen := UC6S846.closure_pPrime_map ρ MN
      (UC6S846.closure_pPrime_subgroupOf hN (p := q) hOp)
    rintro _ ⟨a, ha, rfl⟩
    have haA : (a : G) ∈ A₀ := ha
    have hap : ρ a ^ q = 1 := by
      rw [← map_pow]
      have : a ^ q = 1 := Subtype.ext (by simpa using hA₀el.2 _ haA)
      rw [this, map_one]
    exact uc22s2112r2d_inner eL hq (MN.map ρ) hgen
      (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 (hA₀M haA))) hap
  have hRcard : Nat.card R ≤ q := uc22s2112r2d_card_le eL hq hq2 hqp R hRel hRi
  let φ : ↥A₀N →* MulAut (Bar2 L) := ρ.comp A₀N.subtype
  have hφrange' : φ.range = R := by
    ext y
    simp only [φ, R, MonoidHom.mem_range, Subgroup.mem_map, MonoidHom.comp_apply,
      Subgroup.coe_subtype]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, a.2, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
  have hφrange : Nat.card φ.range = Nat.card R := by rw [hφrange']
  have hA₀Ncard : Nat.card A₀N = q ^ 3 := by
    rw [← hA₀card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA₀N).toEquiv
  have hKcard : q ^ 2 ≤ Nat.card φ.ker := by
    have h1 : Nat.card φ.ker * φ.ker.index = Nat.card A₀N := Subgroup.card_mul_index φ.ker
    rw [Subgroup.index_ker, hφrange, hA₀Ncard] at h1
    by_contra hlt
    replace hlt := not_le.1 hlt
    have h2 : Nat.card φ.ker * Nat.card R ≤ Nat.card φ.ker * q := Nat.mul_le_mul_left _ hRcard
    have h3 : Nat.card φ.ker * q < q ^ 2 * q := Nat.mul_lt_mul_of_pos_right hlt hq.pos
    have h4 : q ^ 3 < q ^ 3 :=
      calc q ^ 3 = Nat.card φ.ker * Nat.card R := h1.symm
        _ ≤ Nat.card φ.ker * q := h2
        _ < q ^ 2 * q := h3
        _ = q ^ 3 := by ring
    exact lt_irrefl _ h4
  let AE : Subgroup G := (φ.ker.map A₀N.subtype).map N.subtype
  have hAEcard : Nat.card AE = Nat.card φ.ker := by
    rw [Subgroup.card_map_of_injective N.subtype_injective,
      Subgroup.card_map_of_injective A₀N.subtype_injective]
  have hAEle : AE ≤ A₀ :=
    calc AE ≤ A₀N.map N.subtype := Subgroup.map_mono (Subgroup.map_subtype_le _)
      _ = A₀ := Subgroup.map_subgroupOf_eq_of_le hA₀N
  obtain ⟨A₂, hA₂AE, hA₂el, hA₂card⟩ :=
    UC6S846.exists_card_p_sq hq (hA₀el.mono hAEle) (by rw [hAEcard]; exact hKcard)
  have hA₂M : A₂ ≤ M := hA₂AE.trans (hAEle.trans hA₀M)
  obtain ⟨P⟩ : Nonempty (Sylow p (Bar2 L)) := inferInstance
  let Sb : Subgroup (Bar2 L) := P
  have hSbp : IsPGroup p Sb := P.isPGroup'
  have hSbi : ¬ p ∣ Sb.index := P.not_dvd_index
  obtain ⟨hSbel, hSbcard⟩ := uc22s2112r2d_sylow hp2 eL Sb hSbp hSbi
  obtain ⟨E₀, hE₀S, hE₀el, hE₀card⟩ :=
    UC6S846.exists_card_p_sq hp hSbel
      (by rw [hSbcard]; exact Nat.pow_le_pow_right hp.pos (by norm_num))
  obtain ⟨SL, hSLp, hSLmap, hSLdisj⟩ :=
    UC6S846.exists_lift_pGroup π hπsurj hker hp hp2 Sb hSbp
  have hSmax : ∀ T : Subgroup (Bar2 L), IsPGroup p T → Sb ≤ T → T = Sb :=
    fun T hT hST => P.is_maximal' hT hST
  have hSLmax := UC6S846.lift_maximal π SL Sb hSLmap hSLdisj hker hp hp2 hSmax hSLp
  let E' : Subgroup ↥L := SL ⊓ E₀.comap π
  have hE'map : E'.map π = E₀ := by
    ext y
    constructor
    · rintro ⟨x, ⟨_, hx2⟩, rfl⟩
      exact hx2
    · intro hy
      have hyS : y ∈ SL.map π := by rw [hSLmap]; exact hE₀S hy
      obtain ⟨x, hxS, rfl⟩ := hyS
      exact ⟨x, ⟨hxS, hy⟩, rfl⟩
  have hE'disj : Disjoint E' π.ker := hSLdisj.mono_left inf_le_left
  have hE'card : Nat.card E' = p ^ 2 := by
    rw [← UC6S846.card_map_of_disjoint_ker π E' hE'disj, hE'map, hE₀card]
  have hE'el : IsElemAbelian p E' :=
    UC6S846.isElemAbelian_of_disjoint_ker π E' hE'disj (by rw [hE'map]; exact hE₀el)
  let SG : Subgroup G := SL.map L.subtype
  let EG : Subgroup G := E'.map L.subtype
  have hSGL : SG ≤ L := Subgroup.map_subtype_le _
  have hEGS : EG ≤ SG := Subgroup.map_mono inf_le_left
  have hSGp : IsPGroup p SG := hSLp.map L.subtype
  have hEGcard : Nat.card EG = p ^ 2 := by
    rw [Subgroup.card_map_of_injective L.subtype_injective, hE'card]
  have hEGel : IsElemAbelian p EG := hE'el.map L.subtype
  have hSGmax : ∀ T : Subgroup G, T ≤ L → IsPGroup p T → SG ≤ T → T = SG := by
    intro T hTL hT hST
    have hT' : IsPGroup p (T.subgroupOf L) :=
      hT.of_equiv (Subgroup.subgroupOfEquivOfLe hTL).symm
    have hSLT : SL ≤ T.subgroupOf L := by
      intro x hx
      exact hST ⟨x, hx, rfl⟩
    have h1 := hSLmax _ hT' hSLT
    calc T = (T.subgroupOf L).map L.subtype := (Subgroup.map_subgroupOf_eq_of_le hTL).symm
      _ = SL.map L.subtype := by rw [h1]
  have hELO : EG ≤ normalizer (O : Set G) := (hEGS.trans hSGL).trans (hLN.trans hNO)
  have hA₂comm : ∀ e ∈ EG, ∀ a ∈ A₂, e * a * e⁻¹ * a⁻¹ ∈ O := by
    intro e he a ha
    obtain ⟨e', -, rfl⟩ := he
    obtain ⟨_, ⟨c, hc, rfl⟩, rfl⟩ := hA₂AE ha
    have hc1 : ρ (c : ↥N) = 1 := hc
    have h2 : UC6S846.rhoL L (c : ↥N) (QuotientGroup.mk e') = QuotientGroup.mk e' := by
      change ρ (c : ↥N) (QuotientGroup.mk e') = QuotientGroup.mk e'
      rw [hc1, MulAut.one_apply]
    have h3 := (UC6S846.rhoL_fix_iff L (c : ↥N) e').1 h2
    have h4 := O.inv_mem h3
    have h5 : ((e' : G)) * (((c : ↥N) : G)) * (e' : G)⁻¹ * (((c : ↥N) : G))⁻¹ =
        (((c : ↥N) : G) * (e' : G) * ((c : ↥N) : G)⁻¹ * (e' : G)⁻¹)⁻¹ := by group
    simpa [h5] using h4
  obtain ⟨A', hA'c, hA'le, ⟨eA⟩⟩ := UC6S846.exists_centralizing_copy hp hp2 hq hq2 O A₂ EG hOpg
    (hA₂M.trans (hN.trans hNO)) hELO hA₂el.isPGroup hEGel.isPGroup hA₂comm
  refine ⟨SG, EG, A', hSGL, hSGp, hSGmax, hEGS, hEGel, hEGcard, ?_, hA'c, ?_, ?_, Sb, hSbp, hSbi,
    ?_⟩
  · exact hA'le.trans (sup_le hA₂M (hOL.trans hLM))
  · exact UC6S846.isElemAbelian_of_mulEquiv eA hA₂el
  · rw [Nat.card_congr eA.toEquiv, hA₂card]
  · have : SG.subgroupOf L = SL := Subgroup.comap_map_eq_self_of_injective L.subtype_injective SL
    rw [this]
    exact hSLmap

theorem uc22s2112r2d_isStronglyPEmbedded (hGA : GriessAllModelsStatement) {D : Data G}
    (hσ : UC6S846.SigmaStd D) (h82 : F08.R82 D) (h76 : F07.R76Sig D) (h614 : UC6.R6_14 D)
    {L : Subgroup G} (hL : L ∈ calC D.M) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpσ : p ∉ D.sig)
    (hX : LieModel (BarInf L) .PSL 2 p 3) : IsStronglyPEmbedded p D.M := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hns : ¬ Group.IsSolvable ↥D.M := UC6S846.not_solvable_of_mem_calC hL
  have hLM : L ≤ D.M := hL.1.le
  have h3L : 3 ≤ Open.pRank p L := uc22s2112r2d_three_le_pRank hGA hL hp2 hX
  by_cases hp3 : p = 3
  · subst hp3
    exact h82 L ⟨hL.1, hL.2.1, by omega,
      Or.inl (CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hL.2.2)⟩
  have hp5 : 5 ≤ p := Nat.Prime.five_le_of_ne_two_of_ne_three hp hp2 hp3
  have hZ : center (Bar2 L) = ⊥ :=
    uc22s2112r2_center_bar2_eq_bot hGA hL hp2 (fun h => absurd h hp3) hX
  have hN : D.M ≤ normalizer (L : Set G) := by
    by_contra hnN
    obtain ⟨E, hEL, hEel, hEcard⟩ := UC6S846.exists_elemAbelian_card_of_le_pRank hp h3L
    have hZp : ¬ p ∣ Nat.card (center (Bar2 L)) := by
      rw [hZ, Subgroup.card_bot]
      exact hp.not_dvd_one
    have h6 := UC6S846.calCRankTwice D.M L hL hnN p hp hp2 hZp E hEL hEel 3 hEcard
    exact hpσ (hσ.four_mem p hp hp2 (by omega))
  obtain ⟨q, hqσ⟩ := hσ.nonempty
  obtain ⟨hq, hq2⟩ := D.sig_prime q hqσ
  have hqp : q ≠ p := fun h => hpσ (h ▸ hqσ)
  have hsq : IsStronglyPEmbedded q D.M := UC6S846.sp_of_mem_sig hσ hns hqσ
  have hOp : UC22.F10.OpRes q D.M = D.M :=
    UC6.opRes_eq_of_stronglyEmbedded_uc6 D.standing.simple D.standing.nonab hq hsq
  obtain ⟨eL⟩ := uc22s2112r2d_bar2_equiv hL hZ hX
  obtain ⟨S, E, A, hSL, hSp, hSmax, hES, hEel, hEcard, hAM, hAC, hAel, hAcard, Sb, hSbp, hSbidx,
    hSbmap⟩ := uc22s2112r2d_key hLM hN hp2 eL hq hq2 hqp hOp (hσ.three_le q hqσ)
  have hAle : 2 ≤ Open.pRank q (D.M ⊓ centralizer (E : Set G)) :=
    UC6S846.le_pRank' hq (le_inf hAM hAC) hAel hAcard
  have hSM : S ≤ D.M := hSL.trans hLM
  have hEM : E ≤ D.M := hES.trans hSM
  have hG : rankThreeGamma 1 p E ≤ D.M := by
    refine h76 q hqσ hq2 hsq p hp E hEM hEel hEcard (by omega) ?_
    intro X hXE _
    have hCN : D.M ⊓ centralizer (E : Set G) ≤ D.M ⊓ normalizer (X : Set G) :=
      inf_le_inf_left _ ((Subgroup.centralizer_le hXE).trans
        (Subgroup.centralizer_le_normalizer _))
    have := CFSG.PreuniquenessRankFour.Helpers.pRank_mono q hq hCN
    omega
  obtain ⟨R', hR'⟩ := (hSp.comap_subtype : IsPGroup p (S.subgroupOf D.M)).exists_le_sylow
  let R : Subgroup G := (R' : Subgroup ↥D.M).map D.M.subtype
  have hRsyl : CFSG.ABGLocalTools.IsSylowOf p R D.M := ⟨R', rfl⟩
  have hRp : IsPGroup p R := R'.isPGroup'.map _
  have hRM : R ≤ D.M := Subgroup.map_subtype_le _
  have hSR : S ≤ R := fun x hx => ⟨⟨x, hSM hx⟩, hR' (Subgroup.mem_subgroupOf.2 hx), rfl⟩
  have hRL : R ⊓ L = S := hSmax _ inf_le_right (hRp.to_le inf_le_left) (le_inf hSR hSL)
  have hEZ : E ≤ R ⊓ centralizer (R : Set G) := by
    refine le_inf (hES.trans hSR) ?_
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hrN : r ∈ normalizer (L : Set G) := hN (hRM hr)
    let m : ↥(normalizer (L : Set G)) := ⟨r, hrN⟩
    have hα1 : ∃ k : ℕ, (rhoL L m) ^ (p ^ k) = 1 := by
      obtain ⟨k, hk⟩ := hRp ⟨r, hr⟩
      refine ⟨k, ?_⟩
      rw [← map_pow]
      have : m ^ p ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
      rw [this, map_one]
    have hα2 : ∀ s ∈ Sb, rhoL L m s ∈ Sb := by
      intro s hs
      rw [← hSbmap] at hs ⊢
      obtain ⟨y, hy, rfl⟩ := hs
      have hyS : (y : G) ∈ S := hy
      refine ⟨Subgroup.normalizerMonoidHom L m y, ?_, rfl⟩
      show ((Subgroup.normalizerMonoidHom L m y : ↥L) : G) ∈ S
      have hmemR : ((Subgroup.normalizerMonoidHom L m y : ↥L) : G) ∈ R := by
        rw [rhoL_mk_coe]
        exact R.mul_mem (R.mul_mem hr (hSR hyS)) (R.inv_mem hr)
      have hboth : ((Subgroup.normalizerMonoidHom L m y : ↥L) : G) ∈ R ⊓ L :=
        ⟨hmemR, (Subgroup.normalizerMonoidHom L m y).2⟩
      rw [hRL] at hboth
      exact hboth
    have hfix := uc22s2112r2d_fix_sylow hp5 eL Sb hSbp hSbidx (rhoL L m) hα1 hα2
    have heS : e ∈ S := hES he
    have heL : e ∈ L := hSL heS
    have hēSb : (QuotientGroup.mk (⟨e, heL⟩ : ↥L) : Bar2 L) ∈ Sb := by
      rw [← hSbmap]
      exact ⟨⟨e, heL⟩, heS, rfl⟩
    have h1 := hfix _ hēSb
    have h2 := (rhoL_fix_iff L m ⟨e, heL⟩).1 h1
    have heR : e ∈ R := hSR heS
    have h3 : r * e * r⁻¹ * e⁻¹ ∈ R :=
      R.mul_mem (R.mul_mem (R.mul_mem hr heR) (R.inv_mem hr)) (R.inv_mem heR)
    have h4 : r * e * r⁻¹ * e⁻¹ = 1 :=
      eq_one_of_mem_isPGroup_of_mem_isPGroup hp hp2 hRp (isPGroup_pCoreOf L) h3 h2
    have h5 : r * e * r⁻¹ = e := mul_inv_eq_one.1 h4
    calc r * e = (r * e * r⁻¹) * r := by group
      _ = e * r := by rw [h5]
  exact h614 (UC6S846.sig_subset_sig1 hσ hns) p hp hp2 hpσ R hRsyl E hEZ hEel hEcard hG

theorem s21_12aFR2d_of_r74Card (hGA : GriessAllModelsStatement) {D : Data G}
    {Ch : Choice2011 G} (hσ : UC6S846.SigmaStd D) (h82 : F08.R82 D) (h76 : F07.R76Sig D)
    (h614 : UC6.R6_14 D) (h74 : F07.R74Card D)
    (hres : ∀ (_hGA : GriessAllModelsStatement) (_h74 : F07.R74Card D) (_hH : H1930 D)
      (c : Ctx21 D Ch) {L : Subgroup G} (_hL : L ∈ calC D.M) {p f : ℕ} [Fact p.Prime]
      (_hp2 : p ≠ 2) (_hMs : IsStronglyPEmbedded p D.M) (_hX : LieModel (BarInf L) .PSL 2 p f)
      {b : G} (_hbB : b ∈ c.B0) (hb : b ∈ normalizer (L : Set G)) {r : ℕ} (_hr : r.Prime)
      (_hr2 : r ≠ 2) (_hbr : orderOf b = r)
      (_hθ : inducedBarInfAutHom L ⟨b, hb⟩ ∉
        (MulAut.conj : BarInf L →* MulAut (BarInf L)).range), False) :
    S21_12aFR2d D Ch :=
  fun hH c L hL p hp hp2 hpσ hX _ ⟨_, hbB, hb, hb3, hθ⟩ =>
    haveI : Fact p.Prime := ⟨hp⟩
    (hres hGA h74 hH c hL hp2 (uc22s2112r2d_isStronglyPEmbedded hGA hσ h82 h76 h614 hL hp hp2 hpσ
      hX) hX hbB hb Nat.prime_three (by norm_num) hb3 hθ).elim

theorem s21_12aFR2d_of_inputs (hGA : GriessAllModelsStatement) {D : Data G} {Ch : Choice2011 G}
    (hσ : UC6S846.SigmaStd D) (h82 : F08.R82 D) (h76 : F07.R76Sig D) (h614 : UC6.R6_14 D)
    (h74 : F07.R74Card D) : S21_12aFR2d D Ch :=
  s21_12aFR2d_of_r74Card hGA hσ h82 h76 h614 h74 fun hGA => uc22s2112r2_false_of_r74Card hGA

open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt) in
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
  (StronglyEmbeddedFive StronglyEmbeddedThree BadNoStrongThree c76Three_of_inputs) in
theorem s21_12aFR2d_dataOfSetup4_of_r74Card (hGA : GriessAllModelsStatement)
    (hSE : StronglyEmbeddedFive) (hK3 : StronglyEmbeddedThree) (hB3 : BadNoStrongThree)
    (hS : Standing4 G) (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G) (hMS : S.InMSigma)
    (hPart : PartIAt S.M) {Ch : Choice2011 G}
    (hres : ∀ (_hGA : GriessAllModelsStatement) (_h74 : F07.R74Card (UC6.dataOfSetup4 hS hU S))
      (_hH : H1930 (UC6.dataOfSetup4 hS hU S)) (c : Ctx21 (UC6.dataOfSetup4 hS hU S) Ch)
      {L : Subgroup G} (_hL : L ∈ calC (UC6.dataOfSetup4 hS hU S).M) {p f : ℕ} [Fact p.Prime]
      (_hp2 : p ≠ 2) (_hMs : IsStronglyPEmbedded p (UC6.dataOfSetup4 hS hU S).M)
      (_hX : LieModel (BarInf L) .PSL 2 p f)
      {b : G} (_hbB : b ∈ c.B0) (hb : b ∈ normalizer (L : Set G)) {r : ℕ} (_hr : r.Prime)
      (_hr2 : r ≠ 2) (_hbr : orderOf b = r)
      (_hθ : inducedBarInfAutHom L ⟨b, hb⟩ ∉
        (MulAut.conj : BarInf L →* MulAut (BarInf L)).range), False) :
    S21_12aFR2d (UC6.dataOfSetup4 hS hU S) Ch := by
  have hC76 := c76Three_of_inputs hSE hK3 hB3 hS hU S
  have h76 : F07.R76Sig (UC6.dataOfSetup4 hS hU S) := fun p hp _ hsp => by
    by_cases h3 : 3 ∈ CFSG.Open.uniqueFourBeta G
    · exact hC76 hMS h3 p hp hsp
    · exact UC6.conclusion76_dataOfSetup4 hSE hS hU S h3 hp hsp
  exact s21_12aFR2d_of_r74Card hGA (UC6S846.sigmaStd_dataOfSetup4 hS hU S)
    (r82_dataOfSetup4 hS hU S hPart.2.2) h76 ((UC6.r6_14_dataOfSetup4_iff hS hU S).2 hPart.2.1)
    (F07.r74Card_dataOfSetup4 hSE hK3 hB3 hS hU S hMS hPart.1) hres

open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt) in
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
  (StronglyEmbeddedFive StronglyEmbeddedThree BadNoStrongThree) in
theorem s21_12aFR2d_dataOfSetup4 (hGA : GriessAllModelsStatement)
    (hSE : StronglyEmbeddedFive) (hK3 : StronglyEmbeddedThree) (hB3 : BadNoStrongThree)
    (hS : Standing4 G) (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G) (hMS : S.InMSigma)
    (hPart : PartIAt S.M) {Ch : Choice2011 G} : S21_12aFR2d (UC6.dataOfSetup4 hS hU S) Ch :=
  s21_12aFR2d_dataOfSetup4_of_r74Card hGA hSE hK3 hB3 hS hU S hMS hPart fun hGA =>
    uc22s2112r2_false_of_r74Card hGA

end CFSG.LocalAnalysis.UniquenessCase.UC22
