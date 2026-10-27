module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFiftyFiveCStar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFiftyFiveSchur
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BarSubBar2Equiv
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeS
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2251a
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22u
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22yg
public import CFSG.GroupTheory.NormalizerInfCentralizer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem uc22p22g_opEq_of_surjective {M : Subgroup G}
    {H : Type} [Group H] (π : ↥M →* H) (hπ : Function.Surjective π) {p : ℕ} (hp : p.Prime)
    (h : CFSG.LocalAnalysis.UniquenessCase.UC22.F10.OpRes p M = M) : uc22p22g_OpEq p H := by
  intro Q _ f hf
  let g : ↥M →* Q := f.comp π
  have hrange : g.range = f.range := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 hπ, ← MonoidHom.range_eq_map]
  have hf' : IsPGroup p ↥g.range := by rw [hrange]; exact hf
  have hN : IsPGroup p (↥M ⧸ g.ker) :=
    hf'.of_equiv (QuotientGroup.quotientKerEquivRange g).symm
  have hker : g.ker = ⊤ := UC6.eq_top_of_isPGroup_quotient_of_opRes_eq_uc6 hp h g.ker hN
  rw [MonoidHom.range_eq_bot_iff]
  ext y
  obtain ⟨m, rfl⟩ := hπ y
  have hm : m ∈ g.ker := by rw [hker]; trivial
  exact MonoidHom.mem_ker.1 hm

theorem opEq_mbar_of_opRes (D : Data G) {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMs : D.M ≤ stabTil V₀ V) {p : ℕ} (hp : p.Prime)
    (hOp : CFSG.LocalAnalysis.UniquenessCase.UC22.F10.OpRes p D.M = D.M) :
    uc22p22g_OpEq p ↥(Mbar D.M V₀ V hV) := by
  let π0 : ↥D.M →* MulAut (Vtil V₀ V hV) :=
    (actTil V₀ V hV).comp (Subgroup.inclusion hMs)
  have hmem : ∀ m : ↥D.M, π0 m ∈ Mbar D.M V₀ V hV := fun m =>
    actTil_mem_barSub V₀ V hV m.2 (hMs m.2)
  refine uc22p22g_opEq_of_surjective (π0.codRestrict _ hmem) ?_ hp hOp
  rintro ⟨φ, hφ⟩
  obtain ⟨g, hg, rfl⟩ := (mem_barSub V₀ V hV D.M φ).1 hφ
  exact ⟨⟨g, hg⟩, Subtype.ext rfl⟩

theorem exists_sigma_prime_1755 (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (hSg : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D)
    (hns : ¬ Group.IsSolvable ↥D.M) {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hVin : InCalV D.M V) (hTI : ¬ CFSG.CGT.Timmesfeld75.IsTI V) :
    ∃ p ∈ D.sig, p.Prime ∧ p ≠ 2 ∧ CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M ∧
      CFSG.LocalAnalysis.UniquenessCase.UC22.F10.OpRes p D.M = D.M ∧
      2 ≤ CFSG.Open.pRank p (⊤ : Subgroup ↥(Mbar D.M ⊥ V hV)) := by
  obtain ⟨p, hpσ⟩ := hSg.nonempty
  obtain ⟨hp, hp2⟩ := D.sig_prime p hpσ
  have hsp := CFSG.LocalAnalysis.UniquenessCase.UC6S846.sp_of_mem_sig hSg hns hpσ
  refine ⟨p, hpσ, hp, hp2, hsp,
    UC6.opRes_eq_of_stronglyEmbedded_uc6 D.standing.simple D.standing.nonab hp hsp, ?_⟩
  have hbot : D.M ≤ normalizer ((⊥ : Subgroup G) : Set G) := by
    rw [Subgroup.normalizer_eq_top]; exact le_top
  have hMs : D.M ≤ stabTil (⊥ : Subgroup G) V := le_stabTil hVin.2.2.1 hbot
  haveI : ((F11.CTilde D.M ⊥ V).subgroupOf D.M).Normal :=
    s15_Three_cTilde_normal hVin.2.2.2 hMs
  have hle := uc22p2251a_pRank_sub_one_le D h61 hVin hTI (p := p) hpσ
  rw [UC22.pRank_mbar D.M V p, s15_Three_pRank_MBar11 hVin.2.2.2 hMs p] at hle
  have h3 := hx.three_le p hpσ
  omega

theorem exists_order_prime_centralizer_1755 (D : Data G) {V₀ V : Subgroup G}
    (hV : IsElemAbelian 2 V) {L : Subgroup G} (hLM : L ≤ D.M)
    (hNL : D.M ≤ normalizer (L : Set G)) {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hL2 : IsL2 ↥(barSub V₀ V hV L) n)
    (hOp : uc22p22g_OpEq p ↥(Mbar D.M V₀ V hV))
    (hrank : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup ↥(Mbar D.M V₀ V hV))) :
    ∃ c ∈ Mbar D.M V₀ V hV, c ≠ 1 ∧ c ^ p = 1 ∧
      ∀ l ∈ barSub V₀ V hV L, c * l = l * c := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hLbM : barSub V₀ V hV L ≤ Mbar D.M V₀ V hV :=
    barSub_mono V₀ V hV hLM
  haveI : ((barSub V₀ V hV L).subgroupOf (Mbar D.M V₀ V hV)).Normal :=
    barSub_subgroupOf_mbar_normal hV hLM hNL
  have hL2' : IsL2 ↥((barSub V₀ V hV L).subgroupOf (Mbar D.M V₀ V hV)) n :=
    CFSG.Blueprint.LieModel.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLbM).symm hL2
  by_contra hcon
  have hC : ∀ c ∈ Subgroup.centralizer
      (((barSub V₀ V hV L).subgroupOf (Mbar D.M V₀ V hV) :
        Subgroup ↥(Mbar D.M V₀ V hV)) : Set ↥(Mbar D.M V₀ V hV)),
      ∀ k : ℕ, c ^ (p ^ k) = 1 → c = 1 := by
    intro c hc k hk
    by_contra hc1
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one hk)
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact hc1 (orderOf_eq_one_iff.1 (by simpa using hm))
    have hdvd : p ^ (m - 1) ∣ orderOf c := hm ▸ pow_dvd_pow p (Nat.sub_le m 1)
    have hdord : orderOf (c ^ (p ^ (m - 1))) = p := by
      rw [orderOf_pow_of_dvd (pow_ne_zero _ hp.ne_zero) hdvd, hm,
        Nat.pow_div (Nat.sub_le m 1) hp.pos]
      have : m - (m - 1) = 1 := by omega
      rw [this, pow_one]
    have hdC : c ^ (p ^ (m - 1)) ∈ Subgroup.centralizer
        (((barSub V₀ V hV L).subgroupOf (Mbar D.M V₀ V hV) :
          Subgroup ↥(Mbar D.M V₀ V hV)) : Set ↥(Mbar D.M V₀ V hV)) :=
      Subgroup.pow_mem _ hc _
    apply hcon
    refine ⟨((c ^ (p ^ (m - 1)) : ↥(Mbar D.M V₀ V hV)) :
      MulAut (Vtil V₀ V hV)), (c ^ (p ^ (m - 1))).2, ?_, ?_, ?_⟩
    · intro h1
      have h1' : c ^ (p ^ (m - 1)) = 1 := Subtype.ext h1
      rw [h1', orderOf_one] at hdord
      exact hp.one_lt.ne hdord
    · have h1 := pow_orderOf_eq_one (c ^ (p ^ (m - 1)))
      rw [hdord] at h1
      rw [← Subgroup.coe_pow, h1, Subgroup.coe_one]
    · intro l hl
      have hlmem : (⟨l, hLbM hl⟩ : ↥(Mbar D.M V₀ V hV)) ∈
          (barSub V₀ V hV L).subgroupOf (Mbar D.M V₀ V hV) :=
        Subgroup.mem_subgroupOf.2 hl
      have h := Subgroup.mem_centralizer_iff.1 hdC _ hlmem
      exact (congrArg Subtype.val h).symm
  have hle := uc22p22g_pRank_le_one _ hp hp2 hL2' hOp hC
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at hle
  omega

theorem mem_pCoreOf_of_actTil_eq_one_of_isSimpleGroup {V : Subgroup G}
    (hV : IsElemAbelian 2 V) {L : Subgroup G} (hLS : L ≤ stabTil (⊥ : Subgroup G) V)
    (h2 : barSub (⊥ : Subgroup G) V hV (pCoreOf 2 L) = ⊥)
    (hsimple : IsSimpleGroup (Bar2 L)) (hL1 : barSub (⊥ : Subgroup G) V hV L ≠ ⊥)
    {x : G} (hxL : x ∈ L) (hxs : x ∈ stabTil (⊥ : Subgroup G) V)
    (hact : actTil (⊥ : Subgroup G) V hV ⟨x, hxs⟩ = 1) : x ∈ pCoreOf 2 L := by
  let φ0 : ↥L →* ↥(barSub (⊥ : Subgroup G) V hV L) :=
    ((actTil (⊥ : Subgroup G) V hV).comp (Subgroup.inclusion hLS)).codRestrict
      (barSub (⊥ : Subgroup G) V hV L)
      (fun y => actTil_mem_barSub (⊥ : Subgroup G) V hV y.2 (hLS y.2))
  have hker0 : CFSG.pCore 2 ↥L ≤ φ0.ker := by
    intro y hy
    rw [MonoidHom.mem_ker]
    have hyP : (y : G) ∈ pCoreOf 2 L := ⟨y, hy, rfl⟩
    have hmem := actTil_mem_barSub (⊥ : Subgroup G) V hV hyP (hLS y.2)
    rw [h2, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  let ψ : Bar2 L →* ↥(barSub (⊥ : Subgroup G) V hV L) :=
    QuotientGroup.lift (CFSG.pCore 2 ↥L) φ0 hker0
  have hψ : Function.Surjective ψ := by
    rintro ⟨y, hy⟩
    obtain ⟨a, haL, hay⟩ := (mem_barSub (⊥ : Subgroup G) V hV L y).1 hy
    refine ⟨QuotientGroup.mk ⟨a, haL⟩, ?_⟩
    apply Subtype.ext
    change actTil (⊥ : Subgroup G) V hV ⟨a, hLS haL⟩ = y
    exact hay
  have hψker : ψ.ker = ⊥ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top ψ.ker with hbot | htop
    · exact hbot
    · exfalso
      haveI : Nontrivial ↥(barSub (⊥ : Subgroup G) V hV L) :=
        (Subgroup.nontrivial_iff_ne_bot _).2 hL1
      obtain ⟨y, hy1⟩ := exists_ne (1 : ↥(barSub (⊥ : Subgroup G) V hV L))
      obtain ⟨a, ha⟩ := hψ y
      have hmem : a ∈ ψ.ker := by rw [htop]; exact Subgroup.mem_top a
      rw [MonoidHom.mem_ker] at hmem
      exact hy1 (ha.symm.trans hmem)
  have hxbar : (QuotientGroup.mk ⟨x, hxL⟩ : Bar2 L) ∈ ψ.ker := by
    rw [MonoidHom.mem_ker]
    have hval : ψ (QuotientGroup.mk ⟨x, hxL⟩) =
        (⟨actTil (⊥ : Subgroup G) V hV ⟨x, hLS hxL⟩,
          actTil_mem_barSub (⊥ : Subgroup G) V hV hxL (hLS hxL)⟩ :
          ↥(barSub (⊥ : Subgroup G) V hV L)) := rfl
    rw [hval]
    refine Subtype.ext ?_
    have h1 : actTil (⊥ : Subgroup G) V hV ⟨x, hLS hxL⟩ = 1 := by
      rwa [show (⟨x, hLS hxL⟩ : stabTil (⊥ : Subgroup G) V) = ⟨x, hxs⟩ from rfl]
    simpa using h1
  rw [hψker, Subgroup.mem_bot] at hxbar
  exact Subgroup.mem_map.2 ⟨⟨x, hxL⟩, (QuotientGroup.eq_one_iff _).1 hxbar, rfl⟩

theorem actTil_mem_centralizer_iff_1755 (D : Data G) {V : Subgroup G}
    (hV : IsElemAbelian 2 V) (hMs : D.M ≤ stabTil (⊥ : Subgroup G) V)
    {L : Subgroup G} (hLM : L ≤ D.M) (hNL : D.M ≤ normalizer (L : Set G))
    (hsimple : IsSimpleGroup (Bar2 L))
    (h2 : barSub (⊥ : Subgroup G) V hV (pCoreOf 2 L) = ⊥)
    (hL1 : barSub (⊥ : Subgroup G) V hV L ≠ ⊥) {m : G} (hm : m ∈ D.M) :
    m ∈ cStar1755 D L hNL ↔
      ∀ l ∈ barSub (⊥ : Subgroup G) V hV L,
        actTil (⊥ : Subgroup G) V hV ⟨m, hMs hm⟩ * l =
          l * actTil (⊥ : Subgroup G) V hV ⟨m, hMs hm⟩ := by
  constructor
  · intro hmC l hl
    obtain ⟨a, haL, hact⟩ := (mem_barSub (⊥ : Subgroup G) V hV L l).1 hl
    have haL' : (a : G) ∈ D.M := hLM haL
    have hmker : (⟨m, hm⟩ : ↥D.M) ∈
        ((CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL L).comp
          (Subgroup.inclusion hNL)).ker := by
      obtain ⟨y, hyker, hyval⟩ := Subgroup.mem_map.1 hmC
      have hy : y = ⟨m, hm⟩ := Subtype.ext hyval
      rwa [hy] at hyker
    have hρ : CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL L ⟨m, hNL hm⟩ = 1 := by
      have hincl : Subgroup.inclusion hNL ⟨m, hm⟩ =
          (⟨m, hNL hm⟩ : ↥(normalizer (L : Set G))) := Subtype.ext rfl
      have h1 := MonoidHom.mem_ker.1 hmker
      rwa [MonoidHom.comp_apply, hincl] at h1
    have hcommO2 : m * (a : G) * m⁻¹ * (a : G)⁻¹ ∈ pCoreOf 2 L :=
      (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL_fix_iff L
        ⟨m, hNL hm⟩ ⟨(a : G), haL⟩).1 (by rw [hρ]; simp)
    have hcommM : m * (a : G) * m⁻¹ * (a : G)⁻¹ ∈ D.M :=
      D.M.mul_mem (D.M.mul_mem (D.M.mul_mem hm haL') (D.M.inv_mem hm)) (D.M.inv_mem haL')
    have hact1 : actTil (⊥ : Subgroup G) V hV
        ⟨m * (a : G) * m⁻¹ * (a : G)⁻¹, hMs hcommM⟩ = 1 := by
      have hmem := actTil_mem_barSub (⊥ : Subgroup G) V hV (X := pCoreOf 2 L)
        hcommO2 (hMs hcommM)
      rw [h2, Subgroup.mem_bot] at hmem
      exact hmem
    have hprod : actTil (⊥ : Subgroup G) V hV ⟨m, hMs hm⟩ *
        actTil (⊥ : Subgroup G) V hV a *
        (actTil (⊥ : Subgroup G) V hV ⟨m, hMs hm⟩)⁻¹ *
        (actTil (⊥ : Subgroup G) V hV a)⁻¹ = 1 := by
      have heq : (⟨m * (a : G) * m⁻¹ * (a : G)⁻¹, hMs hcommM⟩ :
            stabTil (⊥ : Subgroup G) V) =
          ⟨m, hMs hm⟩ * a * (⟨m, hMs hm⟩)⁻¹ * a⁻¹ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      have h1 : actTil (⊥ : Subgroup G) V hV
          (⟨m, hMs hm⟩ * a * (⟨m, hMs hm⟩)⁻¹ * a⁻¹) = 1 := by
        rw [← heq]
        exact hact1
      simpa only [map_mul, map_inv] using h1
    rw [← hact]
    calc actTil (⊥ : Subgroup G) V hV ⟨m, hMs hm⟩ * actTil (⊥ : Subgroup G) V hV a
        = (actTil (⊥ : Subgroup G) V hV ⟨m, hMs hm⟩ * actTil (⊥ : Subgroup G) V hV a *
            (actTil (⊥ : Subgroup G) V hV ⟨m, hMs hm⟩)⁻¹ *
            (actTil (⊥ : Subgroup G) V hV a)⁻¹) *
            (actTil (⊥ : Subgroup G) V hV a * actTil (⊥ : Subgroup G) V hV ⟨m, hMs hm⟩) := by
          group
      _ = actTil (⊥ : Subgroup G) V hV a * actTil (⊥ : Subgroup G) V hV ⟨m, hMs hm⟩ := by
          rw [hprod, one_mul]
  · intro hcomm
    have hρ : CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL L ⟨m, hNL hm⟩ = 1 := by
      refine MulEquiv.ext fun z => ?_
      induction z using QuotientGroup.induction_on with
      | H a =>
        have hacta : actTil (⊥ : Subgroup G) V hV ⟨a, hMs (hLM a.2)⟩ ∈
            barSub (⊥ : Subgroup G) V hV L :=
          actTil_mem_barSub (⊥ : Subgroup G) V hV a.2 (hMs (hLM a.2))
        have hprod : actTil (⊥ : Subgroup G) V hV ⟨m, hMs hm⟩ *
            actTil (⊥ : Subgroup G) V hV ⟨a, hMs (hLM a.2)⟩ *
            (actTil (⊥ : Subgroup G) V hV ⟨m, hMs hm⟩)⁻¹ *
            (actTil (⊥ : Subgroup G) V hV ⟨a, hMs (hLM a.2)⟩)⁻¹ = 1 := by
          have h1 := hcomm _ hacta
          calc actTil (⊥ : Subgroup G) V hV ⟨m, hMs hm⟩ *
                actTil (⊥ : Subgroup G) V hV ⟨a, hMs (hLM a.2)⟩ *
                (actTil (⊥ : Subgroup G) V hV ⟨m, hMs hm⟩)⁻¹ *
                (actTil (⊥ : Subgroup G) V hV ⟨a, hMs (hLM a.2)⟩)⁻¹
              = (actTil (⊥ : Subgroup G) V hV ⟨m, hMs hm⟩ *
                  actTil (⊥ : Subgroup G) V hV ⟨a, hMs (hLM a.2)⟩) *
                  (actTil (⊥ : Subgroup G) V hV ⟨a, hMs (hLM a.2)⟩ *
                    actTil (⊥ : Subgroup G) V hV ⟨m, hMs hm⟩)⁻¹ := by
                group
            _ = (actTil (⊥ : Subgroup G) V hV ⟨m, hMs hm⟩ *
                  actTil (⊥ : Subgroup G) V hV ⟨a, hMs (hLM a.2)⟩) *
                  (actTil (⊥ : Subgroup G) V hV ⟨m, hMs hm⟩ *
                    actTil (⊥ : Subgroup G) V hV ⟨a, hMs (hLM a.2)⟩)⁻¹ := by
                rw [← h1]
            _ = 1 := mul_inv_cancel _
        have hcommO2 : m * (a : G) * m⁻¹ * (a : G)⁻¹ ∈ pCoreOf 2 L := by
          have hcommM : m * (a : G) * m⁻¹ * (a : G)⁻¹ ∈ D.M :=
            D.M.mul_mem (D.M.mul_mem (D.M.mul_mem hm (hLM a.2)) (D.M.inv_mem hm))
              (D.M.inv_mem (hLM a.2))
          have hprod' : actTil (⊥ : Subgroup G) V hV
              ⟨m * (a : G) * m⁻¹ * (a : G)⁻¹, hMs hcommM⟩ = 1 := by
            have heq : (⟨m * (a : G) * m⁻¹ * (a : G)⁻¹, hMs hcommM⟩ :
                  stabTil (⊥ : Subgroup G) V) =
                ⟨m, hMs hm⟩ * ⟨a, hMs (hLM a.2)⟩ *
                  (⟨m, hMs hm⟩)⁻¹ * (⟨a, hMs (hLM a.2)⟩)⁻¹ := by
              apply Subtype.ext
              simp only [Subgroup.coe_mul, Subgroup.coe_inv]
            rw [heq]
            simpa only [map_mul, map_inv] using hprod
          have hxL : m * (a : G) * m⁻¹ * (a : G)⁻¹ ∈ L := by
            have h1 : m * (a : G) * m⁻¹ ∈ L :=
              (Subgroup.mem_normalizer_iff.1 (hNL hm) (a : G)).1 a.2
            exact L.mul_mem h1 (L.inv_mem a.2)
          exact mem_pCoreOf_of_actTil_eq_one_of_isSimpleGroup hV (hLM.trans hMs) h2 hsimple
            hL1 hxL (hMs (D.M.mul_mem (D.M.mul_mem (D.M.mul_mem hm (hLM a.2)) (D.M.inv_mem hm))
              (D.M.inv_mem (hLM a.2)))) hprod'
        have hfix : CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL L ⟨m, hNL hm⟩
            (QuotientGroup.mk a) = QuotientGroup.mk a :=
          (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL_fix_iff L
            ⟨m, hNL hm⟩ ⟨a, a.2⟩).2 hcommO2
        simpa using hfix
    refine Subgroup.mem_map.2 ⟨⟨m, hm⟩, ?_, rfl⟩
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
    have hincl : Subgroup.inclusion hNL ⟨m, hm⟩ = (⟨m, hNL hm⟩ : ↥(normalizer (L : Set G))) :=
      Subtype.ext rfl
    rw [hincl]
    exact hρ

theorem mem_barSub_Q0_of_commute_1755 (D : Data G) {V : Subgroup G}
    (hV : IsElemAbelian 2 V) (hMs : D.M ≤ stabTil (⊥ : Subgroup G) V)
    {L : Subgroup G} (hLM : L ≤ D.M) (hNL : D.M ≤ normalizer (L : Set G))
    {n : ℕ} (hL2 : IsL2 (Bar2 L) n) (hsimple : IsSimpleGroup (Bar2 L))
    (h2 : barSub (⊥ : Subgroup G) V hV (pCoreOf 2 L) = ⊥)
    (hL1 : barSub (⊥ : Subgroup G) V hV L ≠ ⊥)
    (hodd : ∀ c : MulAut (Vtil (⊥ : Subgroup G) V hV),
      (∀ l ∈ barSub (⊥ : Subgroup G) V hV L, c * l = l * c) → c ^ (2 ^ n - 1) = 1)
    {c : MulAut (Vtil (⊥ : Subgroup G) V hV)} (hcM : c ∈ Mbar D.M (⊥ : Subgroup G) V hV)
    (hcL : ∀ l ∈ barSub (⊥ : Subgroup G) V hV L, c * l = l * c) :
    c ∈ barSub (⊥ : Subgroup G) V hV (cStar1755 D L hNL ⊓ Q0_1755 D L hNL) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn2 : 2 ≤ n := (P22fin.isL2Ev_of_isL2 hL2).2
  have hoddPred : Odd (2 ^ n - 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [pow_succ]
    refine ⟨2 ^ m - 1, ?_⟩
    have : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    omega
  obtain ⟨hcMle, hMc, hO2, -, -, -, -, -, -, -⟩ :=
    cStar_T0_Q0_facts_1755 D hLM hNL
  obtain ⟨-, hO2T⟩ := le_inf_iff.1 hO2
  obtain ⟨⟨m, hms⟩, hmM, hmact⟩ := (mem_barSub (⊥ : Subgroup G) V hV D.M c).1 hcM
  have hmM' : m ∈ D.M := hmM
  have hmcomm : ∀ l ∈ barSub (⊥ : Subgroup G) V hV L,
      actTil (⊥ : Subgroup G) V hV ⟨m, hMs hmM'⟩ * l =
        l * actTil (⊥ : Subgroup G) V hV ⟨m, hMs hmM'⟩ := by
    intro l hl
    have h1 := hcL l hl
    have h2 : actTil (⊥ : Subgroup G) V hV ⟨m, hMs hmM'⟩ = c := by
      rw [show (⟨m, hMs hmM'⟩ : stabTil (⊥ : Subgroup G) V) = ⟨m, hms⟩ from rfl]
      exact hmact
    rw [h2]
    exact h1
  have hmC : m ∈ cStar1755 D L hNL :=
    (actTil_mem_centralizer_iff_1755 D hV hMs hLM hNL hsimple h2 hL1 hmM').2 hmcomm
  have hTCK0 : D.T ⊓ cStar1755 D L hNL ≤
      cStar1755 D L hNL ⊓ Subgroup.centralizer (V : Set G) := by
    intro t ht
    refine Subgroup.mem_inf.mpr ⟨ht.2, ?_⟩
    have htM : t ∈ D.M := D.sylowM.le ht.1
    have htcomm := (actTil_mem_centralizer_iff_1755 D hV hMs hLM hNL hsimple h2 hL1 htM).1 ht.2
    have htodd : (actTil (⊥ : Subgroup G) V hV ⟨t, hMs htM⟩) ^ (2 ^ n - 1) = 1 :=
      hodd _ htcomm
    obtain ⟨k, hk⟩ := D.sylowM.isPGroup ⟨t, ht.1⟩
    have hk' : t ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have hmapk : (actTil (⊥ : Subgroup G) V hV ⟨t, hMs htM⟩) ^ (2 ^ k) = 1 := by
      rw [← map_pow]
      have hst : (⟨t, hMs htM⟩ : stabTil (⊥ : Subgroup G) V) ^ (2 ^ k) = 1 :=
        Subtype.ext hk'
      rw [hst, map_one]
    have hdvd1 : orderOf (actTil (⊥ : Subgroup G) V hV ⟨t, hMs htM⟩) ∣ 2 ^ n - 1 :=
      orderOf_dvd_of_pow_eq_one htodd
    have hdvd2 : orderOf (actTil (⊥ : Subgroup G) V hV ⟨t, hMs htM⟩) ∣ 2 ^ k :=
      orderOf_dvd_of_pow_eq_one hmapk
    have hoddOrd : Odd (orderOf (actTil (⊥ : Subgroup G) V hV ⟨t, hMs htM⟩)) :=
      Odd.of_dvd_nat hoddPred hdvd1
    have hcop : Nat.Coprime (orderOf (actTil (⊥ : Subgroup G) V hV ⟨t, hMs htM⟩))
        (2 ^ k) := (Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hoddOrd)).symm
    have hord : orderOf (actTil (⊥ : Subgroup G) V hV ⟨t, hMs htM⟩) = 1 :=
      Nat.Coprime.eq_one_of_dvd hcop hdvd2
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have h1 : actTil (⊥ : Subgroup G) V hV ⟨t, hMs htM⟩ = 1 := orderOf_eq_one_iff.1 hord
    have h2' := (actTil_eq_one_iff (⊥ : Subgroup G) V hV ⟨t, hMs htM⟩).1 h1 v hv
    rw [Subgroup.mem_bot] at h2'
    have hcomm_tv : t * v = v * t := by
      calc t * v = (t * v * t⁻¹ * v⁻¹) * (v * t) := by group
        _ = 1 * (v * t) := by rw [h2']
        _ = v * t := one_mul _
    exact hcomm_tv.symm
  set K0 : Subgroup G := cStar1755 D L hNL ⊓ Subgroup.centralizer (V : Set G)
  have hK0leC : K0 ≤ cStar1755 D L hNL := inf_le_left
  have hMV : D.M ≤ normalizer (V : Set G) := hMs.trans (stabTil_le_normalizer (⊥ : Subgroup G) V)
  have hK0n : cStar1755 D L hNL ≤ normalizer (K0 : Set G) := by
    intro a ha
    exact CFSG.GroupTheory.mem_normalizer_inf_centralizer (L := V)
      (Q := cStar1755 D L hNL) (hMV (hcMle ha)) (Subgroup.le_normalizer ha)
  have hSylC : CFSG.ABGLocalTools.IsSylowOf 2 (D.T ⊓ cStar1755 D L hNL)
      (cStar1755 D L hNL) := D.sylowM.inf_of_le_normalizer hcMle hMc
  have hSylK0' : CFSG.ABGLocalTools.IsSylowOf 2
      (D.T ⊓ cStar1755 D L hNL ⊓ K0) K0 := hSylC.inf_of_le_normalizer hK0leC hK0n
  have hinf : D.T ⊓ cStar1755 D L hNL ⊓ K0 = D.T ⊓ cStar1755 D L hNL :=
    inf_eq_left.mpr hTCK0
  rw [hinf] at hSylK0'
  have hfr := UC6.frattini_of_isSylowOf (H := cStar1755 D L hNL) (L := K0)
    (P := D.T ⊓ cStar1755 D L hNL) hK0leC hK0n hSylK0'
  have hmRHS : m ∈ K0 ⊔ (cStar1755 D L hNL ⊓
      normalizer (((D.T ⊓ cStar1755 D L hNL : Subgroup G) : Set G))) := by
    rw [← hfr]
    exact hmC
  have hK0normal : (K0.subgroupOf (cStar1755 D L hNL)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hK0leC).2 hK0n
  haveI : (K0.subgroupOf (cStar1755 D L hNL)).Normal := hK0normal
  have hmSupC : (⟨m, hmC⟩ : ↥(cStar1755 D L hNL)) ∈
      (K0.subgroupOf (cStar1755 D L hNL)) ⊔
        ((cStar1755 D L hNL ⊓ normalizer
          (((D.T ⊓ cStar1755 D L hNL : Subgroup G) : Set G))).subgroupOf
            (cStar1755 D L hNL)) := by
    rw [← Subgroup.subgroupOf_sup hK0leC inf_le_left]
    exact Subgroup.mem_subgroupOf.mpr hmRHS
  obtain ⟨kk, hkk, mm, hmm, hprod⟩ :=
    (Subgroup.mem_sup_of_normal_left (s := K0.subgroupOf (cStar1755 D L hNL))
      (t := (cStar1755 D L hNL ⊓ normalizer
        (((D.T ⊓ cStar1755 D L hNL : Subgroup G) : Set G))).subgroupOf
          (cStar1755 D L hNL))).1 hmSupC
  let k : G := kk
  let m' : G := mm
  have hkK0 : k ∈ K0 := Subgroup.mem_subgroupOf.mp hkk
  have hm' : m' ∈ cStar1755 D L hNL ⊓ normalizer
      (((D.T ⊓ cStar1755 D L hNL : Subgroup G) : Set G)) := Subgroup.mem_subgroupOf.mp hmm
  have hkm' : k * m' = m := by
    have h1 := congrArg Subtype.val hprod
    simpa [k, m'] using h1
  have hkM : k ∈ D.M := hcMle hkK0.1
  have hkact : actTil (⊥ : Subgroup G) V hV ⟨k, hMs hkM⟩ = 1 := by
    rw [actTil_eq_one_iff]
    intro v hv
    rw [Subgroup.mem_bot]
    have hkv : v * k = k * v := Subgroup.mem_centralizer_iff.1 hkK0.2 v hv
    calc k * v * k⁻¹ * v⁻¹ = (v * k) * k⁻¹ * v⁻¹ := by rw [hkv.symm]
      _ = 1 := by group
  have hmact' : actTil (⊥ : Subgroup G) V hV ⟨m, hMs hmM'⟩ =
      actTil (⊥ : Subgroup G) V hV ⟨m', hMs (hcMle hm'.1)⟩ := by
    calc actTil (⊥ : Subgroup G) V hV ⟨m, hMs hmM'⟩
        = actTil (⊥ : Subgroup G) V hV
            (⟨k, hMs hkM⟩ * ⟨m', hMs (hcMle hm'.1)⟩) := by
          congr 1
          apply Subtype.ext
          exact hkm'.symm
      _ = actTil (⊥ : Subgroup G) V hV ⟨k, hMs hkM⟩ *
            actTil (⊥ : Subgroup G) V hV ⟨m', hMs (hcMle hm'.1)⟩ := map_mul _ _ _
      _ = actTil (⊥ : Subgroup G) V hV ⟨m', hMs (hcMle hm'.1)⟩ := by
          rw [hkact, one_mul]
  have hm'C : m' ∈ cStar1755 D L hNL := hm'.1
  have hm'M : m' ∈ D.M := hcMle hm'C
  have hρm' : CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL L ⟨m', hNL hm'M⟩ = 1 := by
    obtain ⟨y, hyker, hyval⟩ := Subgroup.mem_map.1 hm'C
    have hy : y = ⟨m', hm'M⟩ := Subtype.ext hyval
    rw [hy] at hyker
    have hincl : Subgroup.inclusion hNL ⟨m', hm'M⟩ =
        (⟨m', hNL hm'M⟩ : ↥(normalizer (L : Set G))) := Subtype.ext rfl
    have h1 := MonoidHom.mem_ker.1 hyker
    rwa [MonoidHom.comp_apply, hincl] at h1
  have hmapTL : (D.T ⊓ L).map (MulAut.conj m').toMonoidHom ≤ D.T ⊓ L := by
    rintro _ ⟨t, ht, rfl⟩
    change m' * t * m'⁻¹ ∈ D.T ⊓ L
    obtain ⟨htT, htL⟩ := ht
    have hcommO2 : m' * t * m'⁻¹ * t⁻¹ ∈ pCoreOf 2 L :=
      (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL_fix_iff L
        ⟨m', hNL hm'M⟩ ⟨t, htL⟩).1 (by rw [hρm']; simp)
    have heq : m' * t * m'⁻¹ = (m' * t * m'⁻¹ * t⁻¹) * t := by group
    refine ⟨?_, ?_⟩
    · rw [heq]
      exact D.T.mul_mem (hO2T hcommO2) htT
    · rw [heq]
      exact L.mul_mem (CFSG.LieType.BorelTits.pCoreOf_le 2 L hcommO2) htL
  have hm'NT : m' ∈ normalizer ((D.T ⊓ L : Subgroup G) : Set G) := by
    refine CFSG.RankThree.GroupTheory.SteinbergBY.mem_normalizer_of_map_conj_eq ?_
    refine Subgroup.eq_of_le_of_card_ge hmapTL ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj m').injective]
  have hm'Q : m' ∈ Q0_1755 D L hNL := by
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_right hm'C, ?_⟩
    rw [T0_eq_sup_1755 D hLM hNL]
    exact Subgroup.inf_normalizer_le_normalizer_sup (D.T ⊓ L)
      (D.T ⊓ cStar1755 D L hNL) ⟨hm'NT, hm'.2⟩
  have hcEq : c = actTil (⊥ : Subgroup G) V hV ⟨m', hMs hm'M⟩ := by
    rw [← hmact, hmact']
  rw [hcEq]
  exact actTil_mem_barSub (⊥ : Subgroup G) V hV (Subgroup.mem_inf.mpr ⟨hm'C, hm'Q⟩)
    (hMs hm'M)

theorem not_isCyclic_of_isSylowOf_Q0_1755 (D : Data G) {V : Subgroup G}
    (hV : IsElemAbelian 2 V) (hMs : D.M ≤ stabTil (⊥ : Subgroup G) V)
    {L : Subgroup G} (hLM : L ≤ D.M) (hNL : D.M ≤ normalizer (L : Set G)) {n : ℕ}
    (hL2 : IsL2 (Bar2 L) n) (hL2bar : IsL2 ↥(barSub (⊥ : Subgroup G) V hV L) n)
    (hsimple : IsSimpleGroup (Bar2 L))
    (h2 : barSub (⊥ : Subgroup G) V hV (pCoreOf 2 L) = ⊥)
    (hL1 : barSub (⊥ : Subgroup G) V hV L ≠ ⊥)
    (hodd : ∀ c : MulAut (Vtil (⊥ : Subgroup G) V hV),
      (∀ l ∈ barSub (⊥ : Subgroup G) V hV L, c * l = l * c) → c ^ (2 ^ n - 1) = 1)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {c : MulAut (Vtil (⊥ : Subgroup G) V hV)} (hcM : c ∈ Mbar D.M (⊥ : Subgroup G) V hV)
    (hc1 : c ≠ 1) (hcp : c ^ p = 1)
    (hcL : ∀ l ∈ barSub (⊥ : Subgroup G) V hV L, c * l = l * c)
    {S : Subgroup G} (hS : CFSG.ABGLocalTools.IsSylowOf p S (Q0_1755 D L hNL)) :
    ¬ IsCyclic ↥S := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hcOrd : orderOf c = p := orderOf_eq_prime hcp hc1
  have hpDvd : p ∣ 2 ^ n - 1 := by
    have hdvd : orderOf c ∣ 2 ^ n - 1 := orderOf_dvd_of_pow_eq_one (hodd c hcL)
    rwa [hcOrd] at hdvd
  obtain ⟨x, hxLQ, hxord⟩ := exists_torus_mem_Q0_1755 D hLM hNL hL2 hp hpDvd
  have hxL : x ∈ L := hxLQ.1
  have hxQ : x ∈ Q0_1755 D L hNL := hxLQ.2
  obtain ⟨-, -, -, -, -, -, -, -, hQM, -⟩ := cStar_T0_Q0_facts_1755 D hLM hNL
  have hxM : x ∈ D.M := hQM hxQ
  have hxp : x ^ p = 1 := by rw [← hxord]; exact pow_orderOf_eq_one x
  have hxbarNe : actTil (⊥ : Subgroup G) V hV ⟨x, hMs hxM⟩ ≠ 1 := by
    intro h1
    have hxO2 : x ∈ pCoreOf 2 L :=
      mem_pCoreOf_of_actTil_eq_one_of_isSimpleGroup hV (hLM.trans hMs) h2 hsimple hL1
        hxL (hMs hxM) h1
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L) ⟨x, hxO2⟩
    have hk' : x ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have hdvd2 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    have hdvdp : p ∣ 2 ^ k := by rwa [hxord] at hdvd2
    have hpodd : Odd p := hp.odd_of_ne_two hp2
    have hcop : Nat.Coprime p (2 ^ k) :=
      (Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hpodd)).symm
    exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop hdvdp)
  have hxbarOrd : orderOf (actTil (⊥ : Subgroup G) V hV ⟨x, hMs hxM⟩) = p := by
    refine orderOf_eq_prime ?_ hxbarNe
    rw [← map_pow]
    have hstp : (⟨x, hMs hxM⟩ : stabTil (⊥ : Subgroup G) V) ^ p = 1 := Subtype.ext hxp
    rw [hstp, map_one]
  have hxbarMemQ : actTil (⊥ : Subgroup G) V hV ⟨x, hMs hxM⟩ ∈
      barSub (⊥ : Subgroup G) V hV (Q0_1755 D L hNL) :=
    actTil_mem_barSub (⊥ : Subgroup G) V hV hxQ (hMs hxM)
  have hcQ : c ∈ barSub (⊥ : Subgroup G) V hV (Q0_1755 D L hNL) :=
    (barSub_mono (⊥ : Subgroup G) V hV inf_le_right)
      (mem_barSub_Q0_of_commute_1755 D hV hMs hLM hNL hL2 hsimple h2 hL1 hodd hcM hcL)
  set A : Subgroup (MulAut (Vtil (⊥ : Subgroup G) V hV)) :=
    Subgroup.zpowers (actTil (⊥ : Subgroup G) V hV ⟨x, hMs hxM⟩) with hA
  set B : Subgroup (MulAut (Vtil (⊥ : Subgroup G) V hV)) := Subgroup.zpowers c with hB
  have hcCent : c ∈ Subgroup.centralizer (barSub (⊥ : Subgroup G) V hV L : Set _) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hcL y hy).symm
  have hBA : B ≤ Subgroup.centralizer (A : Set (MulAut (Vtil (⊥ : Subgroup G) V hV))) := by
    refine Subgroup.zpowers_le.mpr ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyL : y ∈ barSub (⊥ : Subgroup G) V hV L :=
      (Subgroup.zpowers_le.mpr (actTil_mem_barSub (⊥ : Subgroup G) V hV hxL (hMs hxM))) hy
    exact (hcL y hyL).symm
  have hxp_bar : (actTil (⊥ : Subgroup G) V hV ⟨x, hMs hxM⟩) ^ p = 1 := by
    rw [← map_pow]
    have hstp : (⟨x, hMs hxM⟩ : stabTil (⊥ : Subgroup G) V) ^ p = 1 := Subtype.ext hxp
    rw [hstp, map_one]
  have hEel : IsElementaryAbelian p ↥(A ⊔ B) := by
    haveI : IsElementaryAbelian p ↥A := IsElementaryAbelian.zpowers_of_pow_eq_one hxp_bar
    haveI : IsElementaryAbelian p ↥B := IsElementaryAbelian.zpowers_of_pow_eq_one hcp
    exact IsElementaryAbelian.sup_of_le_centralizer hBA
  have hcommAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
    intro a ha b hb
    have haL : a ∈ barSub (⊥ : Subgroup G) V hV L :=
      (Subgroup.zpowers_le.mpr (actTil_mem_barSub (⊥ : Subgroup G) V hV hxL (hMs hxM))) ha
    have hbCent : b ∈ Subgroup.centralizer (barSub (⊥ : Subgroup G) V hV L : Set _) :=
      (Subgroup.zpowers_le.mpr hcCent) hb
    exact Subgroup.mem_centralizer_iff.1 hbCent a haL
  have hinf : A ⊓ B = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_bot]
    have hyL : y ∈ barSub (⊥ : Subgroup G) V hV L :=
      (Subgroup.zpowers_le.mpr (actTil_mem_barSub (⊥ : Subgroup G) V hV hxL (hMs hxM))) hy.1
    have hyCent : y ∈ Subgroup.centralizer (barSub (⊥ : Subgroup G) V hV L : Set _) :=
      (Subgroup.zpowers_le.mpr hcCent) hy.2
    have hyCenter : (⟨y, hyL⟩ : ↥(barSub (⊥ : Subgroup G) V hV L)) ∈
        Subgroup.center ↥(barSub (⊥ : Subgroup G) V hV L) := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.1 hyCent (g : _) g.2
    rw [uc22p22g_center_bot hL2bar, Subgroup.mem_bot] at hyCenter
    exact congrArg Subtype.val hyCenter
  have hcardAB := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A B hcommAB).1
  have hcardA : Nat.card ↥A = p := by rw [hA, Nat.card_zpowers, hxbarOrd]
  have hcardB : Nat.card ↥B = p := by rw [hB, Nat.card_zpowers, hcOrd]
  have hcardInf : Nat.card ↥(A ⊓ B) = 1 := by rw [hinf]; simp
  have hcardE : Nat.card ↥(A ⊔ B) = p ^ 2 := by
    rw [hcardA, hcardB, hcardInf, mul_one] at hcardAB
    rw [hcardAB, sq]
  haveI : IsElementaryAbelian p ↥(A ⊔ B) := hEel
  have hEnc : ¬ IsCyclic ↥(A ⊔ B) :=
    CFSG.IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq hcardE
  have hEp : IsPGroup p ↥(A ⊔ B) := IsElementaryAbelian.isPGroup p ↥(A ⊔ B)
  have hE_le : A ⊔ B ≤ ((Q0_1755 D L hNL).subgroupOf
      (stabTil (⊥ : Subgroup G) V)).map (actTil (⊥ : Subgroup G) V hV) := by
    exact sup_le (Subgroup.zpowers_le.mpr hxbarMemQ) (Subgroup.zpowers_le.mpr hcQ)
  exact not_isCyclic_of_isSylowOf_of_le_map (actTil (⊥ : Subgroup G) V hV)
    (hQM.trans hMs) hS hEp hEnc hE_le

theorem seventeen_fiftyfive_inPStar_of_natural (D : Data G) (hx : DataExt D)
    (h61 : UC6.R6_1 D) (hSg : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D)
    {V : Subgroup G} (hW : InCalW D.M D.T V) (hTI : ¬ CFSG.CGT.Timmesfeld75.IsTI V)
    (hV : IsElemAbelian 2 V) (hB : IsBasicModule (Mbar D.M ⊥ V hV))
    {K : Subgroup G} (hK : K ∈ calC D.M) (hKN : D.M ≤ normalizer (K : Set G))
    (hK2 : pCoreOf 2 K ≤ centralizer (V : Set G)) (hsimple : IsSimpleGroup (Bar2 K)) {n : ℕ}
    (hnat : IsL2 ↥(barSub ⊥ V hV K) n ∧
      (BinaryNaturalSL (barSub ⊥ V hV K) ⊤ (fixV (barSub ⊥ V hV K)) 2 n ∨
        (Even n ∧ NatOmegaMinus (barSub ⊥ V hV K) ⊤ ⊥ 4 (n / 2)))) :
    ∃ P : Subgroup G, InPStar D ⊥ P := by
  classical
  have hLM : K ≤ D.M := hK.1.le
  have hNL : D.M ≤ normalizer (K : Set G) := hKN
  have hMV : D.M ≤ normalizer (V : Set G) := hW.1.1.2.2.1
  have hbot : D.M ≤ normalizer ((⊥ : Subgroup G) : Set G) := by
    rw [Subgroup.normalizer_eq_top]; exact le_top
  have hMs : D.M ≤ stabTil (⊥ : Subgroup G) V := le_stabTil hMV hbot
  have hPKM : pCoreOf 2 K ≤ D.M := (CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans hLM
  have h2 : barSub (⊥ : Subgroup G) V hV (pCoreOf 2 K) = ⊥ := by
    refine (CFSG.LocalAnalysis.WeakClosure81.barSub_eq_bot_iff hV hMV hbot hPKM).2 ?_
    rw [UC22.uc22p22u_cTilde_bot]
    exact le_inf hPKM hK2
  have hbar : barSub (⊥ : Subgroup G) V hV K ≠ ⊥ := by
    intro hbotK
    have hn2 : 2 ≤ n := (P22fin.isL2Ev_of_isL2 hnat.1).2
    haveI : IsSimpleGroup ↥(barSub (⊥ : Subgroup G) V hV K) :=
      P22y.isSimpleGroup_of_isL2Ev (P22fin.isL2Ev_of_isL2 hnat.1).1 hn2
    obtain ⟨y, hy⟩ := exists_ne (1 : ↥(barSub (⊥ : Subgroup G) V hV K))
    have hy1 : (y : MulAut (Vtil (⊥ : Subgroup G) V hV)) ∈
        (⊥ : Subgroup (MulAut (Vtil (⊥ : Subgroup G) V hV))) := hbotK ▸ y.2
    exact hy (Subtype.ext (Subgroup.mem_bot.1 hy1))
  have hKS : K ≤ stabTil (⊥ : Subgroup G) V := hLM.trans hMs
  obtain ⟨eKB⟩ := nonempty_bar2_mulEquiv_barSub_of_isSimpleGroup hV hKS h2 hbar hsimple
  have hL2 : IsL2 (Bar2 K) n := CFSG.Blueprint.LieModel.of_mulEquiv eKB.symm hnat.1
  have hns : ¬ Group.IsSolvable ↥D.M := UC6S846.not_solvable_of_mem_calC hK
  obtain ⟨p, -, hp, hp2, hstr, hOpRes, hrank⟩ :=
    exists_sigma_prime_1755 D hx h61 hSg hns hV hW.1.1 hTI
  have hOp : uc22p22g_OpEq p ↥(Mbar D.M (⊥ : Subgroup G) V hV) :=
    opEq_mbar_of_opRes D hV hMs hp hOpRes
  obtain ⟨c, hcM, hc1, hcp, hcL⟩ :=
    exists_order_prime_centralizer_1755 D hV hLM hNL hp hp2 hnat.1 hOp hrank
  have hodd : ∀ c' : MulAut (Vtil (⊥ : Subgroup G) V hV),
      (∀ l ∈ barSub (⊥ : Subgroup G) V hV K, c' * l = l * c') →
        c' ^ (2 ^ n - 1) = 1 :=
    fun c' hc' => pow_eq_one_of_commute_barSub_1755 D hV hB hLM hNL hnat hc'
  have hnc : ∀ S : Subgroup G,
      CFSG.ABGLocalTools.IsSylowOf p S (Q0_1755 D K hNL) → ¬ IsCyclic ↥S :=
    fun S hS => not_isCyclic_of_isSylowOf_Q0_1755 D hV hMs hLM hNL hL2 hnat.1 hsimple h2 hbar
      hodd hp hp2 hcM hc1 hcp hcL hS
  obtain ⟨X, hXQ, hXp, hXexp, hXnc, hTX⟩ := exists_X_1755 D hLM hNL hp hp2 hnc
  obtain ⟨-, -, -, hT0T, hTT0, -, hQT0, -, hQM, -⟩ := cStar_T0_Q0_facts_1755 D hLM hNL
  haveI : Finite (CFSG.ComponentClassification.OuterAutomorphisms.Outer (Bar2 K)) :=
    (outer_finite_isCyclic_1755 hL2).1
  haveI : IsCyclic (CFSG.ComponentClassification.OuterAutomorphisms.Outer (Bar2 K)) :=
    (outer_finite_isCyclic_1755 hL2).2
  refine ⟨X, ?_⟩
  exact inPStar_of_strongly_of_le_normalizer_sup hp hp2 hstr (hXQ.trans hQM) hXp hXexp hXnc
    hT0T hTT0 (hXQ.trans hQT0) hTX (phi1755 D K hNL) (ker_phi_le_T0_1755 D hLM hNL)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
