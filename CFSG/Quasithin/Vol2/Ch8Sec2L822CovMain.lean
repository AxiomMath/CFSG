module

public import CFSG.Quasithin.Vol2.Ch8Sec2L822CovMain1
public import CFSG.Quasithin.Vol2.Ch8Sec2L822CovS7Good
public import CFSG.Quasithin.Vol2.Ch8Sec2L822CovV
public import CFSG.Quasithin.Vol2.Ch3Sec1L319G6Good
public import CFSG.Quasithin.Vol2.Ch3Sec1L319G6S66Main
public import CFSG.Quasithin.Vol2.Ch8Sec2L822CovGz
public import CFSG.Quasithin.Vol2.Ch8Sec2L822CovLz
public import CFSG.Quasithin.Vol2.Ch8Sec2L822R4

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.ASInputs CFSG.Quasithin
  CFSG.Quasithin.H13.L319 CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank RegularWreathProduct
  CFSG.Quasithin.Ch3z
open scoped IsMulCommutative

theorem cov_zpowers_mem {G : Type} [Group G] {H A : Subgroup G} {d y : ↥H}
    (hy : y ∈ Subgroup.zpowers d) (hd : (d : G) ∈ A) : (y : G) ∈ A := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [Subgroup.coe_zpow]
  exact A.zpow_mem hd n

theorem not_nine_dvd_120_mul_cov {n : ℕ} (hn : ¬ 3 ∣ n) : ¬ 9 ∣ 120 * n := by
  intro h
  have h1 : 3 ∣ 40 * n := by
    have : 3 * 3 ∣ 3 * (40 * n) := by
      have e : 120 * n = 3 * (40 * n) := by ring
      rw [← e]
      exact h
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h1 with h2 | h2
  · norm_num at h2
  · exact hn h2

theorem res822CoverV_holds
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h3228 : Stmt3_2_2_eight) (h325 : Stmt3_2_5) (h331 : Stmt3_3_1) (hC58 : TheoremC58)
    (h317 : AS317Sylow) (h711n : Stmt7_1_1_normal) (hD15 : D15AsPrintedSQTK)
    (hS316 : AS316SylowNonsolvable) (hD125 : D125NonsolvableSQTK)
    (hB69 : B69Struct) (hB1 : B69One) (hM22 : M22Facts822) (hF : A318Facts) (h36 : A36ForSQTK)
    (h312 : CFSG.QuasithinUnique.Vol2Native.A312ForSQTKCat)
    (hN2 : KzM22Cover17280_kz3) (hN3 : KzCodeHexad5760_kz3)
    (hov24 : OverSylow2M24Cov) (hovHe : OverSylow2HeCov) (hJ4 : J4CoverFacts) :
    Res822CoverV := by
  intro G _ _ T L I hyp h731 h821 hc hrow hrowM hnot hcover H hH hVH L' N hstep hnc
  classical
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_case82 h711n hyp hrow
  have hL0 : fsuL0 T L = L := fsuL0_eq_of_le_normalizer hTL
  have hMeq : fsuM T L = Subgroup.normalizer (L : Set G) := by
    show Subgroup.normalizer (fsuL0 T L : Set G) = _
    rw [hL0]
  have hTM : T ≤ fsuM T L := hMeq ▸ hTL
  have hLV : L ≤ Subgroup.normalizer (fsuV T I : Set G) := by
    obtain ⟨-, hN'⟩ := stmtFSUModule_of_eight h3228 G T L I hyp.fsu
    rw [hL0] at hN'
    exact le_sup_left.trans hN'
  have hM : MathieuCode22 (autOn L (fsuV T I)) ⊤ ⊥ := by
    have h := hrowM
    unfold Row711M22Code at h
    rw [hL0] at h
    exact h
  have hA := res822_autOn_iso hM
  have hQ : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) := hyp.fsu.quasisimple
  obtain ⟨ψ₀, hψ₀s, hkerψ₀, hψ₀l⟩ := res822_psi_of hLV hA hQ
  have hcov' : IsHat (↥L ⧸ CFSG.pCore 2 ↥L) (CFSG.Blueprint.NativeSporadic.Carrier .M22) := by
    have hcov0 : CoverM22 T L := hcover
    unfold CoverM22 at hcov0
    rw [hL0] at hcov0
    have hS : (pCoreOf 2 L).subgroupOf L = CFSG.pCore 2 ↥L := by
      unfold pCoreOf
      rw [← Subgroup.comap_subtype, Subgroup.comap_map_eq_self_of_injective Subtype.val_injective]
    obtain ⟨_hnorm, hI⟩ := hcov0
    exact IsHat.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hS) hI
  have hcenter3 : Nat.card (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) = 3 := hcov'.2.1
  have hthree : ∀ y : G, y ∈ fsuM T L → orderOf y = 3 → y ∈ L := fun y hyM hy3 => by
    have h := input822ThreeInL_of hF h36 h38 h3228 h711n G T L I hyp h731 h821 hc hrow hrowM hnot y
      hyM hy3
    rw [hL0] at h
    exact h
  obtain ⟨hmin, hsq, hchar, hHMN⟩ := setting_822 h37 h38 h39 h3228 h325 h331 hC58 h317 hyp hTL hH
  have h318 := hyp318_of_normal h37 h38 h39 h3228 hyp hTL hH
  have h315 := h318.hyp315 hyp.fsu.sylow hH
  have hbase : Hyp315Base T (fsuM T L) (fsuL0 T L ⊔ T) H (fsuV T I) := h315.toHyp315Base
  obtain ⟨hq, hdual, h6i, h6ii, h6iii⟩ :=
    hM22 G T L I hyp h731 h821 hc hrow hrowM hnot hbase.reduced.2.2.1
  have hII : Hyp315.CaseII (fsuM T L) H (fsuV T I) := hHMN
  have h319 : Hyp319 T (fsuM T L) (fsuL0 T L ⊔ T) H (fsuV T I) :=
    ⟨hbase, hII, hq, h318.unique, hVH, hdual⟩
  have hconcl := Hyp319.concl_core hC58 hD15 hS316 hD125 hyp.fsu.simple hyp.fsu.nonabelian
    hyp.fsu.qtke hyp.fsu.sylow h318.inM h319
  obtain ⟨hmp, -, -, -, -, hstep2⟩ := lemma319Common_of_inputs hB69 G T hyp.fsu.simple
    hyp.fsu.nonabelian hyp.fsu.qtke hyp.fsu.sylow (fsuM T L) (fsuL0 T L ⊔ T) H (fsuV T I) h318.inM
    hbase hII hq h318.unique hVH (fun ⟨_, hd⟩ => hdual hd) hconcl
  have hKer : KerNoThree (fsuM T L) H :=
    res822CoverJ3_holds h37 h38 h39 h3228 h325 h331 hC58 h317 h711n hD15 hS316 hD125 hB69 hM22 hF h36
      G T L I hyp h731 h821 hc hrow hrowM hnot hcover H hH hVH
  have hgood : Lemma319SixGood :=
    lemma319SixGood_of_residual hC58 h317 hB69 hB1 (six6TwoIndex_of hB69 hB1)
  have hO2H : pCoreOf 2 L ≤ H := cov_pCoreL_le_H hyp.fsu.sylow hTL hH.1.1
  have hM23 : Nat.card CFSG.Blueprint.NativeSporadic.M23 = 10200960 :=
    CFSG.OddStandard.Solomon75.card_nativeM23
  have hcardJ4 : Nat.card CFSG.Blueprint.NativeSporadic.J4 = 86775571046077562880 :=
    CFSG.Sporadic.J4.card_J4
  have hcardM22 : Nat.card CFSG.Blueprint.NativeSporadic.M22 = 443520 :=
    CFSG.RankThree.PartTwo.Sec4.Item426.card_M22
  have hcontra : ((∃ _ : (L'.subgroupOf N).Normal,
        QuotIsoWith H (cSecIn H L' N) (thompsonJ H) (Equiv.Perm (Fin 5)) (Equiv.Perm (Fin 5)) ∧
          NaturalSn 5 H L' N) ∨
      (∃ _ : (L'.subgroupOf N).Normal,
        QuotIsoWith H (cSecIn H L' N) (thompsonJ H) (Equiv.Perm (Fin 5) ≀ᵣ Multiplicative (ZMod 2))
          (Equiv.Perm (Fin 5) × Equiv.Perm (Fin 5)) ∧ NaturalSnPair 5 H L' N)) → False := by
    intro hshape
    obtain ⟨hψk, key⟩ := cover_dichotomy_of_good hB69 hB1 hgood G T hyp.fsu.simple hyp.fsu.nonabelian
      hyp.fsu.qtke hyp.fsu.sylow (fsuM T L) (fsuL0 T L ⊔ T) H (fsuV T I) h318.inM hbase hII hq
      h318.unique hVH (fun ⟨_, hd⟩ => hdual hd) hconcl h6i h6iii L' N hstep hnc hshape
    have hJ : ∀ g : ↥H, (g : G) ∈ centralizerMod L' H N → ¬ 3 ∣ orderOf g := by
      intro g hg
      have hgJ : (g : G) ∈ kerIn (H ⊓ fsuM T L) H := by
        rw [← hstep2 L' N hstep hnc]
        exact hg
      have h1 : orderOf g ∣ Nat.card ↥(kerIn (H ⊓ fsuM T L) H) := by
        have h2 : orderOf (⟨(g : G), hgJ⟩ : ↥(kerIn (H ⊓ fsuM T L) H)) = orderOf g :=
          (Subgroup.orderOf_coe (⟨(g : G), hgJ⟩ : ↥(kerIn (H ⊓ fsuM T L) H))).symm.trans
            (Subgroup.orderOf_coe g)
        rw [← h2]
        exact orderOf_dvd_natCard _
      exact fun h3 => hKer (h3.trans h1)
    have hyP : ∀ y : G, y ∈ fsuM T L → y ∈ Subgroup.centralizer (fsuV T I : Set G) → orderOf y = 3 →
        y ∈ L ∧ y ∈ res822P L := by
      intro y hyM hyC hy3
      have hyL : y ∈ L := hthree y hyM hy3
      refine ⟨hyL, (res822_mem_P_iff L y).mpr ⟨hyL, ?_⟩⟩
      rw [← hkerψ₀, MonoidHom.mem_ker, hψ₀l]
      refine res822_act_one hLV y hyL (fun v hv => ?_)
      have := Subgroup.mem_centralizer_iff.mp hyC v hv
      rw [← this]
      group
    rcases key with ⟨θ, hθs, hθk, d, hdM, hdC, hd3⟩ | ⟨d, t, hdM, hdC, htT, hd3, hcomm', hnot'⟩
    ·
      obtain ⟨y', hy'd, hy'3, hy'ord, k, hk⟩ :=
        exists_three_power_cv θ d hd3 (fun g hg => hJ g ((hθk g).mp hg))
      have hy'MM : (y' : G) ∈ H ⊓ fsuM T L := cov_zpowers_mem hy'd hdM
      have hy'C : (y' : G) ∈ Subgroup.centralizer (fsuV T I : Set G) := cov_zpowers_mem hy'd hdC
      have hy'M : (y' : G) ∈ fsuM T L := hy'MM.2
      have hy'H : (y' : G) ∈ H := y'.2
      have hy'3G : (y' : G) ^ 3 = 1 := by simpa using congrArg Subtype.val hy'3
      have hθy' : θ y' ≠ 1 := by
        intro h1
        rw [h1, orderOf_one] at hy'ord
        norm_num at hy'ord
      have hy'1 : (y' : G) ≠ 1 := by
        intro h1
        apply hθy'
        have : y' = 1 := Subtype.ext h1
        rw [this, map_one]
      have hy'ord3 : orderOf (y' : G) = 3 := orderOf_eq_prime hy'3G hy'1
      obtain ⟨hy'L, hy'P⟩ := hyP (y' : G) hy'M hy'C hy'ord3
      obtain ⟨z, hz1, hz2, hzV, hHz, hTz⟩ :=
        cov_exists_z hyp hrow h711n h37 h38 h39 h3228 hC58 h317 hH
      obtain ⟨Lz, hLzG, hLzL, hTLz, hLzF, hLzperf, hLzq, hodd⟩ :=
        cov_lz_exists h711n h3228 hN2 hN3 hyp hrow hrowM hnot hcover hz1 hzV hTz
      have hyz : (y' : G) * z = z * (y' : G) :=
        (Subgroup.mem_centralizer_iff.mp hy'C z hzV).symm
      have hy'Lz : (y' : G) ∈ Lz := hodd _ hy'L hyz (by rw [hy'ord3]; decide)
      have hcomm := cov_comm_pCoreOf hLzL hy'P hy'Lz
      have hker : θ.ker = (kerIn (H ⊓ fsuM T L) H).subgroupOf H := by
        ext g
        rw [MonoidHom.mem_ker, hθk g, hstep2 L' N hstep hnc, Subgroup.mem_subgroupOf]
      have hθJ : ∀ g : ↥H, (g : G) ∈ kerIn (H ⊓ fsuM T L) H → θ g = 1 := fun g hg => by
        rw [← MonoidHom.mem_ker, hker]
        exact Subgroup.mem_subgroupOf.mpr hg
      have hH9 : ¬ 9 ∣ Nat.card H := by
        have h1 := Subgroup.card_ker_mul_card_range θ
        rw [MonoidHom.range_eq_top.mpr hθs, Subgroup.card_top, Nat.card_perm, Nat.card_fin, hker] at h1
        have h2 : Nat.card ↥((kerIn (H ⊓ fsuM T L) H).subgroupOf H) =
            Nat.card ↥(kerIn (H ⊓ fsuM T L) H) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hmp.kerIn_le_H).toEquiv
        rw [h2] at h1
        rw [← h1]
        have h3 : (Nat.factorial 5) = 120 := by decide
        rw [h3, mul_comm]
        exact not_nine_dvd_120_mul_cov hKer
      exact cov_gz_false h37 h38 h39 h36 h312 hov24 hovHe hJ4 hM23 hcardJ4 hcardM22 hyp.fsu.qtke
        hyp.fsu.simple hyp.fsu.nonabelian hz1 hz2 hHz hTz hH.1.1 hTM
        (isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow hTz) hLzG hTLz hLzF hLzperf hLzq hy'H
        hy'M hy'Lz hy'3G hy'1 hcomm hmp θ hθs hθJ hθy' hH9
    ·
      set ψ := chiefPsi (Setting.hHL hstep) (Setting.hHN hstep) with hψdef
      obtain ⟨y', hy'd, hy'3, hy'ord, k, hk⟩ :=
        exists_three_power_cv ψ d hd3 (fun g hg => hJ g ((hψk g).mp hg))
      have hy'MM : (y' : G) ∈ H ⊓ fsuM T L := cov_zpowers_mem hy'd hdM
      have hy'C : (y' : G) ∈ Subgroup.centralizer (fsuV T I : Set G) := cov_zpowers_mem hy'd hdC
      have hy'M : (y' : G) ∈ fsuM T L := hy'MM.2
      have hy'H : (y' : G) ∈ H := y'.2
      have hy'3G : (y' : G) ^ 3 = 1 := by simpa using congrArg Subtype.val hy'3
      have hψy' : ψ y' ≠ 1 := by
        intro h1
        rw [h1, orderOf_one] at hy'ord
        norm_num at hy'ord
      have hy'1 : (y' : G) ≠ 1 := by
        intro h1
        apply hψy'
        have : y' = 1 := Subtype.ext h1
        rw [this, map_one]
      have hy'ord3 : orderOf (y' : G) = 3 := orderOf_eq_prime hy'3G hy'1
      obtain ⟨hy'L, hy'P⟩ := hyP (y' : G) hy'M hy'C hy'ord3
      have hPH : res822P L ≤ H := cov_P_le_H hcenter3 hO2H hy'L hy'H hy'P hy'ord3
      have hykP : (y' : G) ^ k ∈ res822P L := (res822P L).pow_mem hy'P k
      have hconjP : (t : G) * (y' : G) ^ k * (t : G)⁻¹ ∈ res822P L :=
        res822_P_normal L (hTL htT) _ hykP
      let ψP : ↥(res822P L) →* MulAut ↥(chiefMod L' N) := ψ.comp (Subgroup.inclusion hPH)
      have hψa : ψP ⟨(y' : G) ^ k, hykP⟩ = ψ d := by
        have : Subgroup.inclusion hPH ⟨(y' : G) ^ k, hykP⟩ = y' ^ k := Subtype.ext rfl
        change ψ (Subgroup.inclusion hPH ⟨(y' : G) ^ k, hykP⟩) = ψ d
        rw [this]
        exact hk
      have hψb : ψP ⟨(t : G) * (y' : G) ^ k * (t : G)⁻¹, hconjP⟩ = ψ (t * d * t⁻¹) := by
        have : Subgroup.inclusion hPH ⟨(t : G) * (y' : G) ^ k * (t : G)⁻¹, hconjP⟩ = t * y' ^ k * t⁻¹ :=
          Subtype.ext rfl
        change ψ (Subgroup.inclusion hPH ⟨(t : G) * (y' : G) ^ k * (t : G)⁻¹, hconjP⟩) = _
        rw [this, map_mul, map_mul, map_inv, hk, map_mul, map_mul, map_inv]
      have hordb : orderOf (ψ (t * d * t⁻¹)) = 3 := by
        rw [map_mul, map_mul, map_inv]
        have := orderOf_injective (MulAut.conj (ψ t)).toMonoidHom (MulAut.conj (ψ t)).injective (ψ d)
        simpa [MulAut.conj_apply, hd3] using this
      exact false_of_two_commuting_three_cv ψP (cov_P9 L hcenter3)
        (a := ⟨(y' : G) ^ k, hykP⟩) (b := ⟨(t : G) * (y' : G) ^ k * (t : G)⁻¹, hconjP⟩)
        (by rw [hψa]; exact hd3) (by rw [hψb]; exact hordb)
        (by rw [hψa, hψb]; exact hcomm') (by rw [hψa, hψb]; exact hnot')
  exact ⟨fun h => hcontra (Or.inl h), fun h => hcontra (Or.inr h)⟩

end CFSG.Quasithin.H13
