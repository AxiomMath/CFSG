module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.InducedQuotInfAut
import CFSG.LocalAnalysis.UniquenessCase.UC22P20p
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsEleven
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddKF7
import CFSG.GH74.GLS.Stage2.Final.ECInterGriess
import CFSG.RankThree.PartOne.CTP.SeitzL2
import CFSG.Quasithin.Vol2.GoldschmidtF134OddDickson
import CFSG.Quasithin.Vol2.Ch3Sec3InspWalterHolds
import CFSG.RankThree.PartTwo.KFacts.K71bOutAbelian
import CFSG.GroupTheory.CoprimeActionSupport.CoprimeAutomorphismFixedQuotientLift

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.Blueprint.Multiplier (genericOrders exceptionalOrders)
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem uc22s2112r2_center_bar2_eq_bot (hGA : GriessAllModelsStatement) {M L : Subgroup G}
    (hL : L ∈ calC M) {p e : ℕ} (hp2 : p ≠ 2) (h9 : p = 3 → e ≠ 2)
    (hX : LieModel (BarInf L) .PSL 2 p e) : center (Bar2 L) = ⊥ := by
  obtain ⟨φ⟩ := uc22p21k_barInf_equiv_of_calC hL
  have hdvd := CFSG.RankThree.PartOne.card_center_dvd_of_model hGA
    (CFSG.Quasithin.A3.isQuasisimple_iff_open.2 hL.2.2)
    ((CFSG.Blueprint.LieModel.of_mulEquiv φ hX).statedClassicalModel (by decide))
  have hgen : genericOrders .PSL 2 p e = (Nat.gcd 2 (p ^ e - 1), 1) := rfl
  rcases CFSG.GH74.GLS.Stage2.Final.ECInterGriess.exceptionalOrders_psl2 (p := p) (f := e) hp2
    with hexc | ⟨h3, he, -⟩
  · have h2 : Nat.card (center (Bar2 L)) ∣ 2 := by
      refine hdvd.trans ?_
      simp only [hgen, hexc, mul_one]
      exact Nat.gcd_dvd_left _ _
    have hodd : Odd (Nat.card (center (Bar2 L))) := uc22p20p_odd_center_bar2 ↥L
    rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h1 | h1
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · rw [h1] at hodd
      exact absurd hodd (by decide)
  · exact absurd he (h9 h3)

theorem uc22s2112r2_exists_prime {T M L₀ B L : Subgroup G} (hB : B ∈ calB1 T M L₀) {b : G}
    (hbB : b ∈ B) (hbN : b ∈ normalizer (L : Set G))
    (hθ : inducedBarInfAutHom L ⟨b, hbN⟩ ∉ (MulAut.conj : BarInf L →* MulAut (BarInf L)).range) :
    ∃ b' ∈ B, ∃ hb' : b' ∈ normalizer (L : Set G), (orderOf b').Prime ∧ orderOf b' ≠ 2 ∧
      inducedBarInfAutHom L ⟨b', hb'⟩ ∉
        (MulAut.conj : BarInf L →* MulAut (BarInf L)).range := by
  obtain ⟨hodd, hsq⟩ := orderOf_odd_and_squarefree_of_mem_calB1 hB hbB
  have hsq' : Squarefree (orderOf (⟨b, hbN⟩ : ↥(normalizer (L : Set G)))) := by
    rwa [Subgroup.orderOf_mk]
  obtain ⟨y, hy, hyp, hyN⟩ :=
    exists_prime_order_zpowers_of_not_mem (inducedBarInfAutHom L) _ _ hsq' hθ
  refine ⟨(y : G), ?_, y.2, by rwa [Subgroup.orderOf_coe], ?_, hyN⟩
  · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [Subgroup.coe_zpow]
    exact B.zpow_mem hbB k
  · intro h2
    have hdvd := orderOf_dvd_of_mem_zpowers hy
    rw [Subgroup.orderOf_mk, ← Subgroup.orderOf_coe, h2] at hdvd
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hdvd)

theorem uc22s2112r2_fixed_psl2 {X : Type} [Group X] {p f r : ℕ} [Fact p.Prime]
    (hX : LieModel X .PSL 2 p f) (hr : r.Prime) (hr2 : r ≠ 2) {θ : MulAut X}
    (hθr : orderOf θ = r) (hθ : θ ∉ (MulAut.conj : X →* MulAut X).range) :
    r ∣ f ∧ Nonempty (↥(signalizerFixedSubgroup θ) ≃* PSL(2, GaloisField p (f / r))) := by
  have hp : p.Prime := Fact.out
  obtain ⟨e⟩ := CFSG.Quasithin.H13.NQCore.nonempty_mulEquiv_psl2_odd
    (CFSG.Blueprint.LieModel.statedClassicalModel hX (by decide))
  have hf1 : 1 ≤ f := hX.admissible.2.1
  have hF : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f (by omega)
  set σ : MulAut (CFSG.GorensteinWalter.PSL2 (GaloisField p f)) := MulAut.congr e θ with hσ
  have hσr : orderOf σ = r := by rw [hσ, MulEquiv.orderOf_eq]; exact hθr
  have hσout : ∀ g, σ ≠ MulAut.conj g := by
    intro g hg
    exact hθ ((CFSG.RankThree.PartTwo.KFacts.isInnerAut_congr e θ).1 ⟨g, hg.symm⟩)
  have hrodd : Odd r := hr.odd_of_ne_two hr2
  obtain ⟨τ, β, hτ, hστ⟩ :=
    CFSG.RankThree.PartOne.CTP.exists_conj_fieldAut hr hrodd ⟨hσr, hσout⟩
  obtain ⟨hrf, hcard⟩ := CFSG.RankThree.LinearTwo.card_fixedSubfield hp hf1 hF τ
  rw [hτ] at hrf hcard
  refine ⟨hrf, ?_⟩
  have hfix : signalizerFixedSubgroup σ = (signalizerFixedSubgroup θ).map e.toMonoidHom := by
    ext x
    constructor
    · intro hx
      have hx' : e (θ (e.symm x)) = x := hx
      refine ⟨e.symm x, ?_, by simp⟩
      change θ (e.symm x) = e.symm x
      have h := congrArg e.symm hx'
      simpa using h
    · rintro ⟨y, hy, rfl⟩
      have hy' : θ y = y := hy
      change e (θ (e.symm (e y))) = e y
      rw [e.symm_apply_apply, hy']
  obtain ⟨e1⟩ := CFSG.RankThree.PartOne.CTP.nonempty_fixed_conj_equiv β
    (CFSG.GorensteinWalter.psl2FieldAut (GaloisField p f) τ)
  obtain ⟨e2⟩ :=
    CFSG.SignalizerFunctorTheorem.CatalogBridge.nonempty_mulEquiv_fixed_psl2FieldAut hrodd hτ
  have hfr : f / r ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (by omega) hrf) hr.pos).ne'
  obtain ⟨e3⟩ := CFSG.RankThree.PartOne.CTP.nonempty_psl2_equiv_of_card_eq
    (k₁ := CFSG.ComponentClassification.CatalogueBLinearTwoDescent.fixedSubfield
      (GaloisField p f) τ)
    (k₂ := GaloisField p (f / r)) (by rw [hcard, GaloisField.card p _ hfr])
  exact ⟨((Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr hfix.symm)).trans
      ((MulEquiv.subgroupCongr (congrArg signalizerFixedSubgroup hστ)).trans
        (e1.trans (e2.trans e3)))⟩

theorem uc22s2112r2_exists_fixHom {L : Subgroup G} (hq : CFSG.Open.IsQuasisimple (Bar2 L))
    (hZ : center (Bar2 L) = ⊥) {b : G} (hb : b ∈ normalizer (L : Set G)) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hbr : orderOf b = r) :
    ∃ φ : ↥(L ⊓ centralizer ({b} : Set G)) →*
        ↥(signalizerFixedSubgroup (inducedBarInfAutHom L ⟨b, hb⟩)),
      Function.Surjective φ ∧ IsPGroup 2 φ.ker := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrad := solvableRadical_eq_pCore_of_center_bar2_eq_bot hq hZ
  set α : MulAut ↥L := L.normalizerMonoidHom ⟨b, hb⟩ with hαdef
  have hN : ∀ n ∈ CFSG.solvableRadical ↥L, α n ∈ CFSG.solvableRadical ↥L := fun n hn => by
    rw [← CFSG.LieType.SteinbergBR.solvableRadical_map_equiv α]
    exact Subgroup.mem_map_of_mem _ hn
  have hbpow : (⟨b, hb⟩ : ↥(normalizer (L : Set G))) ^ r = 1 := by
    rw [← hbr, ← Subgroup.orderOf_mk b hb]
    exact pow_orderOf_eq_one _
  have hα : α ^ r = 1 := by rw [hαdef, ← map_pow, hbpow, map_one]
  have hrN : ¬ r ∣ Nat.card ↥(CFSG.solvableRadical ↥L) := by
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).exists_card_eq
    rw [hrad, hk]
    intro h
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h))
  have hθq : ∀ z : BarInf L,
      CFSG.GroupTheory.CoprimeActionSupport.CoprimeAutomorphismFixedQuotientLift.quotientMap
        α (CFSG.solvableRadical ↥L) hN z = inducedBarInfAutHom L ⟨b, hb⟩ z := by
    intro z
    induction z using QuotientGroup.induction_on with
    | H x => rfl
  have hmem : ∀ x : ↥(L ⊓ centralizer ({b} : Set G)),
      ((QuotientGroup.mk' (CFSG.solvableRadical ↥L)).comp (Subgroup.inclusion inf_le_left)) x ∈
        signalizerFixedSubgroup (inducedBarInfAutHom L ⟨b, hb⟩) := by
    intro x
    change inducedBarInfAutHom L ⟨b, hb⟩ (QuotientGroup.mk (Subgroup.inclusion inf_le_left x)) =
      QuotientGroup.mk (Subgroup.inclusion inf_le_left x)
    rw [← hθq,
      CFSG.GroupTheory.CoprimeActionSupport.CoprimeAutomorphismFixedQuotientLift.quotientMap_mk]
    congr 1
    apply Subtype.ext
    rw [hαdef, Subgroup.normalizerMonoidHom_apply_apply_coe]
    have hxc := (mem_inf.1 x.2).2
    rw [mem_centralizer_singleton_iff] at hxc
    change b * (x : G) * b⁻¹ = x
    rw [← hxc, mul_inv_cancel_right]
  refine ⟨((QuotientGroup.mk' (CFSG.solvableRadical ↥L)).comp
    (Subgroup.inclusion inf_le_left)).codRestrict _ hmem, ?_, ?_⟩
  · rintro ⟨z, hz⟩
    have hz' :
        CFSG.GroupTheory.CoprimeActionSupport.CoprimeAutomorphismFixedQuotientLift.quotientMap
          α (CFSG.solvableRadical ↥L) hN z = z := by
      rw [hθq]
      exact hz
    obtain ⟨y, rfl, hy⟩ :=
      (CFSG.GroupTheory.CoprimeActionSupport.CoprimeAutomorphismFixedQuotientLift.fixed_quotient_iff
        α hα (CFSG.solvableRadical ↥L) hN hrN z).1 hz'
    have hyc : (y : G) ∈ centralizer ({b} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      have h1 := congrArg Subtype.val hy
      rw [hαdef, Subgroup.normalizerMonoidHom_apply_apply_coe] at h1
      change b * (y : G) * b⁻¹ = y at h1
      calc (y : G) * b = b * y * b⁻¹ * b := by rw [h1]
        _ = b * y := by group
    exact ⟨⟨y, mem_inf.2 ⟨y.2, hyc⟩⟩, rfl⟩
  · intro g
    obtain ⟨⟨x, hx⟩, hg⟩ := g
    have hmk : (QuotientGroup.mk (⟨x, (mem_inf.1 hx).1⟩ : ↥L) : BarInf L) = 1 :=
      congrArg Subtype.val (MonoidHom.mem_ker.1 hg)
    have hxN : (⟨x, (mem_inf.1 hx).1⟩ : ↥L) ∈ CFSG.pCore 2 ↥L := by
      rw [← hrad]
      exact (QuotientGroup.eq_one_iff _).1 hmk
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨_, hxN⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have h := congrArg (fun w : ↥(CFSG.pCore 2 ↥L) => ((w : ↥L) : G)) hk
    simpa using h

theorem uc22s2112r2_le_pRank {A : Subgroup G} {Q : Type} [Group Q] [Finite Q] (φ : ↥A →* Q)
    (hφ : Function.Surjective φ) (hker : IsPGroup 2 φ.ker) {q k : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) (hk : k ≤ CFSG.pRank q Q) : k ≤ Open.pRank q A := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcop : q.Coprime (Nat.card φ.ker) := by
    obtain ⟨n, hn⟩ := hker.exists_card_eq
    rw [hn]
    exact ((Nat.coprime_primes hq Nat.prime_two).2 hq2).pow_right n
  have h1 :=
    CFSG.RankThreeCoreUniqueness.Helpers.pRank_top_eq_of_coprime_kernel q hq φ hφ hcop
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup A, h1,
    ← CFSG.SectionRank.pRank_eq_open_pRank_top]
  exact hk

theorem uc22s2112r2_exists_perfect {A : Subgroup G} {S : Type} [Group S] [Group.IsPerfect S]
    (g : ↥A →* S) (hg : Function.Surjective g) :
    ∃ D0 : Subgroup G, D0 ≤ A ∧ ⁅D0, D0⁆ = D0 ∧ ∃ f0 : ↥D0 →* S, Function.Surjective f0 := by
  obtain ⟨P, hPperf, hPmap⟩ := PartOne.Section9.exists_perfect_map_eq_top g hg
  let e := P.equivMapOfInjective A.subtype A.subtype_injective
  refine ⟨P.map A.subtype, Subgroup.map_subtype_le P, ?_,
    (g.comp P.subtype).comp e.symm.toMonoidHom, ?_⟩
  · rw [← Subgroup.map_commutator, hPperf]
  · intro s
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 (hPmap ▸ Subgroup.mem_top s)
    exact ⟨e ⟨a, ha⟩, by simp⟩

theorem uc22s2112r2_not_inv {L : Subgroup G} {p f : ℕ} [Fact p.Prime]
    (hX : LieModel (BarInf L) .PSL 2 p f) {b m : G} (hb : b ∈ normalizer (L : Set G))
    (hm : m ∈ normalizer (L : Set G)) (hbo : Odd (orderOf b))
    (hθ : inducedBarInfAutHom L ⟨b, hb⟩ ∉ (MulAut.conj : BarInf L →* MulAut (BarInf L)).range) :
    m * b * m⁻¹ ≠ b⁻¹ := by
  obtain ⟨e⟩ := CFSG.Quasithin.H13.NQCore.nonempty_mulEquiv_psl2_odd
    (CFSG.Blueprint.LieModel.statedClassicalModel hX (by decide))
  intro hinv
  set θ := inducedBarInfAutHom L ⟨b, hb⟩ with hθdef
  set μ := inducedBarInfAutHom L ⟨m, hm⟩ with hμdef
  have hmb : (⟨m, hm⟩ : ↥(normalizer (L : Set G))) * ⟨b, hb⟩ * (⟨m, hm⟩)⁻¹ = (⟨b, hb⟩)⁻¹ :=
    Subtype.ext (by simpa using hinv)
  have hconj : μ * θ * μ⁻¹ = θ⁻¹ := by
    rw [hμdef, hθdef, ← map_inv, ← map_mul, ← map_mul, hmb, map_inv]
  have hc := CFSG.RankThree.PartTwo.KFacts.isInnerAut_commutator_of_mulEquiv_psl2_all e μ θ
  rw [hconj] at hc
  obtain ⟨k, hk⟩ := hbo
  have hθo : θ ^ (2 * k) * θ = 1 := by
    rw [← pow_succ, ← hk, hθdef, ← map_pow, ← Subgroup.orderOf_mk b hb, pow_orderOf_eq_one,
      map_one]
  have h4 : (θ⁻¹ * θ⁻¹) ^ k = θ := by
    rw [← mul_inv_rev, ← pow_two, inv_pow, ← pow_mul, eq_inv_of_mul_eq_one_left hθo, inv_inv]
  apply hθ
  rw [← h4]
  exact Subgroup.pow_mem _ hc k

theorem uc22s2112r2_psl2_facts {p k : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hk : 1 ≤ k)
    (h4 : 4 ≤ p ^ k) :
    IsSimpleGroup PSL(2, GaloisField p k) ∧ ¬ Group.IsSolvable PSL(2, GaloisField p k) ∧
      Group.IsPerfect PSL(2, GaloisField p k) ∧ p ^ k ∣ Nat.card PSL(2, GaloisField p k) := by
  have hp : p.Prime := Fact.out
  have hcard : Nat.card (GaloisField p k) = p ^ k := GaloisField.card p k (by omega)
  obtain ⟨hs, hns⟩ := CFSG.SignalizerFunctorTheorem.CatalogBridge.psl2_simple_not_isSolvable
    (F := GaloisField p k) (by rw [hcard]; exact h4)
  refine ⟨hs, hns, CFSG.GorensteinWalter.psl2_isPerfect_of_card_gt_three _ (by omega), ?_⟩
  have hodd : Odd (p ^ k) := (hp.odd_of_ne_two hp2).pow
  have hform := CFSG.GorensteinWalter.psl2_card_formula (GaloisField p k)
    ⟨p, k, hp, hp.odd_of_ne_two hp2, hk, hcard⟩
  rw [hcard] at hform
  change p ^ k ∣ Nat.card (CFSG.GorensteinWalter.PSL2 (GaloisField p k))
  rw [hform]
  have h2 : 2 ∣ (p ^ k) ^ 2 - 1 :=
    even_iff_two_dvd.1 (Nat.Odd.sub_odd hodd.pow odd_one)
  rw [Nat.mul_div_assoc _ h2]
  exact dvd_mul_right _ _

theorem uc22s2112r2_setup (hGA : GriessAllModelsStatement) {M L : Subgroup G} (hL : L ∈ calC M)
    {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hX : LieModel (BarInf L) .PSL 2 p f) {b : G}
    (hb : b ∈ normalizer (L : Set G)) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hbr : orderOf b = r)
    (hθ : inducedBarInfAutHom L ⟨b, hb⟩ ∉ (MulAut.conj : BarInf L →* MulAut (BarInf L)).range) :
    r ∣ f ∧ f ≤ Open.pRank p L ∧ f / r ≤ Open.pRank p (L ⊓ centralizer ({b} : Set G)) ∧
      (4 ≤ p ^ (f / r) → ∃ D0 : Subgroup G, D0 ≤ L ⊓ centralizer ({b} : Set G) ∧
        ⁅D0, D0⁆ = D0 ∧ ∃ f0 : ↥D0 →* PSL(2, GaloisField p (f / r)), Function.Surjective f0) := by
  have hp : p.Prime := Fact.out
  haveI : Fact r.Prime := ⟨hr⟩
  set θ := inducedBarInfAutHom L ⟨b, hb⟩ with hθdef
  have hbpow : (⟨b, hb⟩ : ↥(normalizer (L : Set G))) ^ r = 1 := by
    rw [← hbr, ← Subgroup.orderOf_mk b hb]
    exact pow_orderOf_eq_one _
  have hθr : orderOf θ = r := by
    refine orderOf_eq_prime ?_ ?_
    · rw [hθdef, ← map_pow, hbpow, map_one]
    · intro h1
      exact hθ (h1 ▸ Subgroup.one_mem _)
  obtain ⟨hrf, ⟨eF⟩⟩ := uc22s2112r2_fixed_psl2 hX hr hr2 hθr hθ
  have hf1 : 1 ≤ f := hX.admissible.2.1
  have hr3 : 3 ≤ r := by
    have := hr.two_le
    omega
  have hrf' : r ≤ f := Nat.le_of_dvd (by omega) hrf
  have hZ : center (Bar2 L) = ⊥ :=
    uc22s2112r2_center_bar2_eq_bot hGA hL hp2 (fun _ => by omega) hX
  have hrad := solvableRadical_eq_pCore_of_center_bar2_eq_bot hL.2.2 hZ
  obtain ⟨eL⟩ := CFSG.Quasithin.H13.NQCore.nonempty_mulEquiv_psl2_odd
    (CFSG.Blueprint.LieModel.statedClassicalModel hX (by decide))
  have hkerL : IsPGroup 2 (QuotientGroup.mk' (CFSG.solvableRadical ↥L)).ker := by
    rw [QuotientGroup.ker_mk', hrad]
    exact CFSG.pCore_isPGroup
  have h1 : f ≤ Open.pRank p L :=
    uc22s2112r2_le_pRank (QuotientGroup.mk' (CFSG.solvableRadical ↥L))
      (QuotientGroup.mk'_surjective _) hkerL hp hp2
      (CFSG.Quasithin.H13.S3320.le_pRank_of_psl2 (by omega) eL)
  obtain ⟨φ, hφ, hker⟩ := uc22s2112r2_exists_fixHom hL.2.2 hZ hb hr hr2 hbr
  have hfr0 : 0 < f / r := Nat.div_pos hrf' hr.pos
  have h2 : f / r ≤ Open.pRank p (L ⊓ centralizer ({b} : Set G)) :=
    uc22s2112r2_le_pRank φ hφ hker hp hp2 (CFSG.Quasithin.H13.S3320.le_pRank_of_psl2 hfr0 eF)
  refine ⟨hrf, h1, h2, fun h4 => ?_⟩
  haveI : Group.IsPerfect PSL(2, GaloisField p (f / r)) :=
    (uc22s2112r2_psl2_facts hp2 hfr0 h4).2.2.1
  exact uc22s2112r2_exists_perfect (eF.toMonoidHom.comp φ) (eF.surjective.comp hφ)

end CFSG.LocalAnalysis.UniquenessCase.UC22
