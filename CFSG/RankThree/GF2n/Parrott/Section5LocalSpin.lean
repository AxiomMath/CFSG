module

public import CFSG.RankThree.GF2n.Parrott.Section5LocalT
public import CFSG.RankThree.GF2n.Parrott.Section5LocalJ
public import CFSG.RankThree.GF2n.Parrott.SpinFixedCardSigma
public import CFSG.RankThree.GF2n.Parrott.Section4SpinGlue
public import CFSG.RankThree.GF2n.Parrott.Section4SylowFiveStructure
public import CFSG.Holt.PSL2Natural.Defs
public import CFSG.Holt.PermFacts
public import CFSG.Holt.ThreePoint
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Quot
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalBender
public import CFSG.LocalAnalysis.QuasithinUnique.K1.ExceptionalCatSuzuki
public import CFSG.Quasithin.Background.E2NParamStar
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS3
public import CFSG.Quasithin.Vol2.E2TenEight
public import CFSG.RankThree.GF2n.Parrott.ZFusionControl
public import CFSG.RankThree.Holt.Basic

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)

local notation "GL8" => Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)

private theorem qH_sigma1Nine_mul_sigma2_inv_eq_spin (h : Tim79a.ParrottHyp z)
    {σ₂ : ↥(H z)}
    (hq₂ : qH (z := z) D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup)) :
    qH (z := z) D (sigma1Nine (z := z) D * σ₂⁻¹) =
      (⟨sigma1, sigma1_mem_A⟩ : QA45.originalSubgroup) *
        (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup)⁻¹ := by
  rw [map_mul, map_inv, qH_sigma1Nine (z := z) D, hq₂]

private theorem conjZ_sigma2_eq_one_spin (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)}
    (hq₂ : qH (z := z) D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup)) :
    conjZ z σ₂ = 1 :=
  conjZ_eq_one_of_qH_mem_QP45 (z := z) D h σ₂ (by rw [hq₂]; exact sigma2_mem_Q)

private theorem conjZ_sigma1Nine_mul_sigma2_inv_eq_one_spin (h : Tim79a.ParrottHyp z)
    {σ₂ : ↥(H z)}
    (hq₂ : qH (z := z) D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup)) :
    conjZ z (sigma1Nine (z := z) D * σ₂⁻¹) = 1 := by
  rw [map_mul, map_inv, conjZ_sigma1Nine (z := z) h D,
    conjZ_sigma2_eq_one_spin (z := z) D h hq₂, inv_one, mul_one]

private theorem sigma1Nine_mul_sigma2_inv_pow_three_spin (h : Tim79a.ParrottHyp z)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH (z := z) D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂) :
    (sigma1Nine (z := z) D * σ₂⁻¹) ^ 3 = 1 := by
  have h3 : orderOf (sigma1Nine (z := z) D * σ₂⁻¹) = 3 := by
    rw [← Subgroup.orderOf_coe (sigma1Nine (z := z) D * σ₂⁻¹)]
    exact orderOf_sigma1Nine_mul_inv (z := z) D h hσ₂ hq₂ hc₂
  rw [← h3]
  exact pow_orderOf_eq_one _

theorem fixDimV_sigma1Nine_mul_sigma2_inv_eq_four_of_spin (h : Tim79a.ParrottHyp z)
    (P : Matrix.GeneralLinearGroup (Fin 8) (ZMod 2))
    (hP : ∀ a : ↥QA45.originalSubgroup, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)}
    (hq₂ : qH (z := z) D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup)) :
    fixDimV h (sigma1Nine (z := z) D * σ₂⁻¹) = 4 := by
  have h1 := two_pow_fixDimV_eq_of_conj_rep (z := z) D h rhoA P hP
    (sigma1Nine (z := z) D * σ₂⁻¹)
  rw [qH_sigma1Nine_mul_sigma2_inv_eq_spin (z := z) D h hq₂,
    spinFixedCard_sigma1_mul_sigma2_inv] at h1
  exact Nat.pow_right_injective (le_refl 2) (h1.trans (by norm_num))

theorem exists_conj_mem_isSylowOf_centralizer_sigma1Nine_mul_inv (h : Tim79a.ParrottHyp z)
    (P : Matrix.GeneralLinearGroup (Fin 8) (ZMod 2))
    (hP : ∀ a : ↥QA45.originalSubgroup, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH (z := z) D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂) {T₂ : Subgroup G}
    (hT₂ : IsSylowOf 2 T₂
      (H z ⊓ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G))) :
    ∀ j ∈ J z, orderOf j = 2 → j ≠ z → ∃ c ∈ H z, c * j * c⁻¹ ∈ T₂ := by
  intro j hj hord hjz
  let σ : ↥(H z) := sigma1Nine (z := z) D * σ₂⁻¹
  have hσ3 : σ ^ 3 = 1 := sigma1Nine_mul_sigma2_inv_pow_three_spin (z := z) D h hσ₂ hq₂ hc₂
  have hZσ : conjZ z σ = 1 :=
    conjZ_sigma1Nine_mul_sigma2_inv_eq_one_spin (z := z) D h hq₂
  by_cases hZj : j ∈ centerIn (J z)
  · have hmemT : j ∈ T₂ := centerIn_J_le_of_isSylowOf_centralizer h hZσ hT₂ hZj
    exact ⟨1, (H z).one_mem, by simpa using hmemT⟩
  · let jJ : J z := ⟨j, hj⟩
    have hvne : QuotientV.pi z jJ ≠ 1 := by
      intro hv
      apply hZj
      have hker : jJ ∈ (QuotientV.pi z).ker := MonoidHom.mem_ker.mpr hv
      rw [QuotientV.pi_ker] at hker
      exact Subgroup.mem_subgroupOf.mp hker
    have hj2 : j * j = 1 := by
      have h1 := pow_orderOf_eq_one j
      rwa [hord, pow_two] at h1
    have hjJ2 : jJ * jJ = 1 := by
      apply Subtype.ext
      simpa using hj2
    have hqv : qVZMod h (QuotientV.pi z jJ) = 0 := by
      rw [qVZMod_eq_zero_iff]
      have hqj : qJ h jJ = 1 := by
        apply Subtype.ext
        rw [qJ_coe, pow_two]
        simpa using congrArg Subtype.val hjJ2
      rw [qV_pi, hqj]
    have hfix4 : fixDimV h σ = 4 :=
      fixDimV_sigma1Nine_mul_sigma2_inv_eq_four_of_spin (z := z) D h P hP hq₂
    obtain ⟨w, hwne, hσw, hqw⟩ :=
      exists_fixed_singular_of_three_le_fixDimV (z := z) h (x := σ) (by rw [hfix4]; norm_num)
    obtain ⟨g, hg⟩ := exists_conj_of_qVZMod_eq_zero (z := z) D h P hP hvne hwne hqv hqw
    have hfixg : conjV h σ (QuotientV.pi z (conjJ' z g jJ)) =
        QuotientV.pi z (conjJ' z g jJ) := by
      rw [← conjV_mk h g jJ, hg, hσw]
    have hcentj : conjJ' z g jJ ∈ centralizerJ σ :=
      mem_centralizerJ_of_conjV_pi_eq (z := z) h hσ3 hZσ hfixg
    have hjGT : ((conjJ' z g jJ : J z) : G) ∈
        J z ⊓ centralizer ({(σ : G)} : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨(conjJ' z g jJ).2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact mem_centralizerJ_iff.mp hcentj
    have hT : ((conjJ' z g jJ : J z) : G) ∈ T₂ :=
      J_inf_centralizer_le_of_isSylowOf (z := z) h hT₂ hjGT
    refine ⟨(g : G), g.2, ?_⟩
    rwa [conjJ'_apply_coe] at hT

private theorem four_le_fixDimV_sigma_mul_of_mem_centerIn_spin (h : Tim79a.ParrottHyp z)
    (P : Matrix.GeneralLinearGroup (Fin 8) (ZMod 2))
    (hP : ∀ a : ↥QA45.originalSubgroup, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH (z := z) D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂) {T₂ : Subgroup G}
    (hT₂ : IsSylowOf 2 T₂
      (H z ⊓ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G)))
    {x' : ↥(H z)} (hx : (x' : G) ∈ centerIn T₂) :
    4 ≤ fixDimV h ((sigma1Nine (z := z) D * σ₂⁻¹) * x') := by
  let σ : ↥(H z) := sigma1Nine (z := z) D * σ₂⁻¹
  have hσ3 : σ ^ 3 = 1 := sigma1Nine_mul_sigma2_inv_pow_three_spin (z := z) D h hσ₂ hq₂ hc₂
  have hZσ : conjZ z σ = 1 :=
    conjZ_sigma1Nine_mul_sigma2_inv_eq_one_spin (z := z) D h hq₂
  have hfix4 : fixDimV h σ = 4 :=
    fixDimV_sigma1Nine_mul_sigma2_inv_eq_four_of_spin (z := z) D h P hP hq₂
  obtain ⟨hxT, hxcentT⟩ := Subgroup.mem_inf.mp hx
  have hfix_le : autFixedSubgroup (conjV h σ) ≤ autFixedSubgroup (conjV h (σ * x')) := by
    intro v hv
    rw [mem_autFixedSubgroup] at hv ⊢
    obtain ⟨j, rfl⟩ := QuotientV.pi_surjective z v
    have hjcent : j ∈ centralizerJ σ :=
      mem_centralizerJ_of_conjV_pi_eq (z := z) h hσ3 hZσ hv
    have hjG : (j : G) ∈ J z ⊓ centralizer ({(σ : G)} : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨j.2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact mem_centralizerJ_iff.mp hjcent
    have hjT : (j : G) ∈ T₂ :=
      J_inf_centralizer_le_of_isSylowOf (z := z) h hT₂ hjG
    have hxjcomm : (x' : G) * (j : G) = (j : G) * (x' : G) :=
      (Subgroup.mem_centralizer_iff.mp hxcentT (j : G) hjT).symm
    have hconjj : conjJ' z x' j = j := by
      apply Subtype.ext
      rw [conjJ'_apply_coe, hxjcomm]
      group
    have hxv : conjV h x' (QuotientV.pi z j) = QuotientV.pi z j := by
      rw [conjV_mk, hconjj]
    rw [map_mul, MulAut.mul_apply, hxv]
    exact hv
  have hcardle : Nat.card ↥(autFixedSubgroup (conjV h σ)) ≤
      Nat.card ↥(autFixedSubgroup (conjV h (σ * x'))) := Subgroup.card_le_of_le hfix_le
  rw [card_fix h σ, hfix4, card_fix h (σ * x')] at hcardle
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hcardle

private theorem fixCard_rhoA_mul_eq_four_of_mem_centralizer_spin
    {q : QA45.originalSubgroup}
    (hq : q ∈ Subgroup.centralizer
      ({(⟨sigma1, sigma1_mem_A⟩ : QA45.originalSubgroup) *
        (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup)⁻¹} :
        Set QA45.originalSubgroup))
    (hq1 : q ≠ 1) (h2 : ∃ k : ℕ, orderOf q = 2 ^ k) :
    fixCard (((rhoA (((⟨sigma1, sigma1_mem_A⟩ : QA45.originalSubgroup) *
      (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup)⁻¹) * q) : GL8) :
      Matrix (Fin 8) (Fin 8) (ZMod 2))) = 4 := by
  set p : QA45.originalSubgroup := (⟨sigma1, sigma1_mem_A⟩ : QA45.originalSubgroup) *
    (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup)⁻¹ with hp
  obtain ⟨c, hc, hb⟩ := exists_conj_mem_closure_t_uv_of_mem_centralizer hq h2
  set b : QA45.originalSubgroup := c * q * c⁻¹ with hbdef
  have hb1 : b ≠ 1 := by
    intro hb1
    apply hq1
    calc q = c⁻¹ * b * c := by rw [hbdef]; group
      _ = c⁻¹ * 1 * c := by rw [hb1]
      _ = 1 := by group
  have hfixb : fixCard (((rhoA (p * b) : GL8) :
      Matrix (Fin 8) (Fin 8) (ZMod 2))) = 4 := by
    have h1 := spinFixedCard_sigma1_mul_sigma2_inv_mul (b := b) hb hb1
    rwa [show ((⟨sigma1, sigma1_mem_A⟩ : QA45.originalSubgroup) *
        (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup)⁻¹) = p from rfl] at h1
  have hc' : c⁻¹ ∈ Subgroup.centralizer ({p} : Set QA45.originalSubgroup) :=
    Subgroup.inv_mem _ hc
  have hcs' : c⁻¹ * p = p * c⁻¹ :=
    Subgroup.mem_centralizer_singleton_iff.mp hc'
  have hā : q = c⁻¹ * b * c := by
    rw [hbdef]
    group
  have hpq : p * q = c⁻¹ * (p * b) * c := by
    calc p * q = p * (c⁻¹ * b * c) := by rw [hā]
      _ = (p * c⁻¹) * b * c := by group
      _ = (c⁻¹ * p) * b * c := by rw [hcs']
      _ = c⁻¹ * (p * b) * c := by group
  have hmat : ((rhoA (c⁻¹ * (p * b) * c) : GL8) :
      Matrix (Fin 8) (Fin 8) (ZMod 2)) =
      ((((rhoA c)⁻¹ * rhoA (p * b) * rhoA c : GL8) :
        Matrix (Fin 8) (Fin 8) (ZMod 2))) := by
    conv_lhs => rw [map_mul, map_mul, map_inv]
  rw [hpq, hmat]
  have hinv : ((rhoA c)⁻¹ * rhoA (p * b) * rhoA c : GL8) =
      ((rhoA c)⁻¹ * rhoA (p * b) * ((rhoA c)⁻¹)⁻¹ : GL8) := by
    rw [inv_inv]
  rw [hinv, fixCard_conj ((rhoA c)⁻¹) (rhoA (p * b))]
  exact hfixb

private theorem qH_eq_one_of_mem_centerIn_spin (h : Tim79a.ParrottHyp z)
    (P : Matrix.GeneralLinearGroup (Fin 8) (ZMod 2))
    (hP : ∀ a : ↥QA45.originalSubgroup, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH (z := z) D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂) {T₂ : Subgroup G}
    (hT₂ : IsSylowOf 2 T₂
      (H z ⊓ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G)))
    {x' : ↥(H z)} (hx : (x' : G) ∈ centerIn T₂) :
    qH D x' = 1 := by
  let σ : ↥(H z) := sigma1Nine (z := z) D * σ₂⁻¹
  obtain ⟨hxT, -⟩ := Subgroup.mem_inf.mp hx
  have hxσ : σ * x' = x' * σ := by
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hT₂.le hxT).2).symm
  have hdimge : 4 ≤ fixDimV h (σ * x') :=
    four_le_fixDimV_sigma_mul_of_mem_centerIn_spin (z := z) D h P hP hσ₂ hq₂ hc₂ hT₂ hx
  by_contra hqxne
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hT₂.isPGroup.exists_orderOf_eq_pow (⟨(x' : G), hxT⟩ : ↥T₂)
  have hkx : orderOf x' = 2 ^ k := by
    rw [← Subgroup.orderOf_coe x', Subgroup.orderOf_coe (⟨(x' : G), hxT⟩ : ↥T₂)]
    exact hk
  have hdvd : orderOf (qH D x') ∣ 2 ^ k := by
    rw [← hkx]
    exact orderOf_map_dvd (qH D) x'
  obtain ⟨m, -, hm⟩ :=
    (Nat.dvd_prime_pow (p := 2) (m := k) Nat.prime_two).mp hdvd
  let s : QA45.originalSubgroup := (⟨sigma1, sigma1_mem_A⟩ : QA45.originalSubgroup) *
    (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup)⁻¹
  have hqσ : qH D σ = s := by
    show qH D (sigma1Nine (z := z) D * σ₂⁻¹) = s
    rw [qH_sigma1Nine_mul_sigma2_inv_eq_spin (z := z) D h hq₂]
  have ha : qH D x' ∈ Subgroup.centralizer ({s} : Set QA45.originalSubgroup) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcomm : qH D σ * qH D x' = qH D x' * qH D σ := by
      rw [← map_mul, ← map_mul]
      exact congrArg (qH D) hxσ
    rw [hqσ] at hcomm
    exact hcomm.symm
  have hfixspin : fixCard (((rhoA (s * qH D x') : GL8) :
      Matrix (Fin 8) (Fin 8) (ZMod 2))) = 4 :=
    fixCard_rhoA_mul_eq_four_of_mem_centralizer_spin ha hqxne ⟨m, hm⟩
  have hqσx : qH D (σ * x') = s * qH D x' := by
    rw [map_mul, hqσ]
  have hfixcard : fixCard (((rhoA (qH D (σ * x')) : GL8) :
      Matrix (Fin 8) (Fin 8) (ZMod 2))) = 4 := by
    rw [hqσx]
    exact hfixspin
  have h2fix := two_pow_fixDimV_eq_of_conj_rep (z := z) D h rhoA P hP (σ * x')
  rw [hfixcard] at h2fix
  have hdim2 : fixDimV h (σ * x') = 2 :=
    Nat.pow_right_injective (le_refl 2) (h2fix.trans (by norm_num))
  omega

private theorem mem_centerIn_J_of_mem_centerIn_spin (h : Tim79a.ParrottHyp z)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH (z := z) D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂) {T₂ : Subgroup G}
    (hT₂ : IsSylowOf 2 T₂
      (H z ⊓ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G)))
    {x' : ↥(H z)} (hx : (x' : G) ∈ centerIn T₂) (hqx : qH D x' = 1) :
    (x' : G) ∈ centerIn (J z) := by
  let σ : ↥(H z) := sigma1Nine (z := z) D * σ₂⁻¹
  have hσ3 : σ ^ 3 = 1 := sigma1Nine_mul_sigma2_inv_pow_three_spin (z := z) D h hσ₂ hq₂ hc₂
  have hZσ : conjZ z σ = 1 :=
    conjZ_sigma1Nine_mul_sigma2_inv_eq_one_spin (z := z) D h hq₂
  obtain ⟨hxT, hxcentT⟩ := Subgroup.mem_inf.mp hx
  have hxσ : x' * σ = σ * x' := by
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp (hT₂.le hxT).2
  have hxJ : (x' : G) ∈ J z := by
    have hmem := (J_mem_iff D x').mpr hqx
    exact Subgroup.mem_subgroupOf.mp hmem
  have hxS : (x' : G) ∈ J z ⊓ centralizer ({(σ : G)} : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨hxJ, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val hxσ
  have hxcentS : (x' : G) ∈ Subgroup.centralizer
      ((J z ⊓ centralizer ({(σ : G)} : Set G) : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_iff.mp hxcentT y
      (J_inf_centralizer_le_of_isSylowOf (z := z) h hT₂ hy)
  have hxcentJinf : (x' : G) ∈ centerIn (J z ⊓ centralizer ({(σ : G)} : Set G)) :=
    Subgroup.mem_inf.mpr ⟨hxS, hxcentS⟩
  rwa [centerIn_J_inf_centralizer_eq (z := z) h (x := σ) hσ3 hZσ] at hxcentJinf

theorem centerIn_isSylowOf_centralizer_sigma1Nine_mul_inv_eq_zpowers (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) ≠ centerIn (H z))
    (P : Matrix.GeneralLinearGroup (Fin 8) (ZMod 2))
    (hP : ∀ a : ↥QA45.originalSubgroup, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH (z := z) D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂) {T₂ : Subgroup G}
    (hT₂ : IsSylowOf 2 T₂
      (H z ⊓ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G))) :
    centerIn T₂ = Subgroup.zpowers z := by
  have hZJT : centerIn T₂ ⊓ centerIn (J z) = Subgroup.zpowers z :=
    centerIn_inf_centerIn_J_eq_zpowers_of_isSylowOf_centralizer_sigma1Nine_mul_inv
      (z := z) D h hZ hσ₂ hq₂ hc₂ hT₂
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨hxT, -⟩ := Subgroup.mem_inf.mp hx
    have hxH : x ∈ H z := (hT₂.le hxT).1
    let x' : ↥(H z) := ⟨x, hxH⟩
    have hqx : qH D x' = 1 :=
      qH_eq_one_of_mem_centerIn_spin (z := z) D h P hP hσ₂ hq₂ hc₂ hT₂ hx
    have hxJZ : x ∈ centerIn (J z) :=
      mem_centerIn_J_of_mem_centerIn_spin (z := z) D h hσ₂ hq₂ hc₂ hT₂ hx hqx
    have hxinf : x ∈ centerIn T₂ ⊓ centerIn (J z) := Subgroup.mem_inf.mpr ⟨hx, hxJZ⟩
    rwa [hZJT] at hxinf
  · rw [← hZJT]
    exact inf_le_left

end CFSG.RankThree.GF2n.Parrott
