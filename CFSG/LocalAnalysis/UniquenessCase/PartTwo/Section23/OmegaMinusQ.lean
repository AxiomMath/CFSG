module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsOmegaK
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.CentralizerOTwoB
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.ThompsonTransport
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionSetup
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4Mul
public import CFSG.Goldschmidt.Steps.G53Tools
public import CFSG.GroupTheory.OddPGroupNoncyclicChar
public import CFSG.GroupTheory.WielandtProductFinal
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsRootModule
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.SemiregularBar
public import CFSG.LocalAnalysis.UniquenessCase.UC22BarLemmas
public import CFSG.LocalAnalysis.UniquenessCase.UC6S19

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem barPreimage_eq_pCoreOf_sup_of_isSylowOf (D : Data G) {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) {Q0 : Subgroup G}
    (hQ0 : CFSG.ABGLocalTools.IsSylowOf q Q0
      (barPreimage D.M (CFSG.pCore q (Bar2 D.M)))) :
    barPreimage D.M (CFSG.pCore q (Bar2 D.M)) = pCoreOf 2 D.M ⊔ Q0 := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : (CFSG.pCore q (Bar2 D.M)).Normal := CFSG.pCore_normal
  have hbar := uc22p22u_sylow_barPreimage (M := D.M) (r := q) hq hq2
    (CFSG.pCore_isPGroup (p := q)) hQ0
  refine le_antisymm ?_ (sup_le (pCoreOf_le_barPreimage D.M _) hQ0.le)
  intro x hx
  obtain ⟨hxM, hxY⟩ := uc22p21c_mem_barPreimage.1 hx
  have hxbar : uc22p21cPi D.M ⟨x, hxM⟩ ∈ barImage D.M Q0 := by
    rw [hbar.1]
    exact hxY
  obtain ⟨y, hyQ0, hyx⟩ := uc22p21c_mem_barImage.1 hxbar
  have ho : x * (y : G)⁻¹ ∈ pCoreOf 2 D.M := by
    change ((⟨x, hxM⟩ * (y : ↥D.M)⁻¹ : ↥D.M) : G) ∈ pCoreOf 2 D.M
    rw [CFSG.mem_openPCoreOf_iff]
    exact (QuotientGroup.eq_one_iff (⟨x, hxM⟩ * (y : ↥D.M)⁻¹)).1 (by
      change uc22p21cPi D.M (⟨x, hxM⟩ * (y : ↥D.M)⁻¹) = 1
      rw [map_mul, map_inv, hyx, mul_inv_cancel])
  have hx' : x = (x * (y : G)⁻¹) * (y : G) := by group
  rw [hx']
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ho) (Subgroup.mem_sup_right hyQ0)

private theorem D_M_eq_pCoreOf_sup_normalizer (D : Data G) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {Q0 : Subgroup G}
    (hQ0 : CFSG.ABGLocalTools.IsSylowOf q Q0
      (barPreimage D.M (CFSG.pCore q (Bar2 D.M)))) :
    D.M = pCoreOf 2 D.M ⊔ (D.M ⊓ Subgroup.normalizer (Q0 : Set G)) := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : (CFSG.pCore q (Bar2 D.M)).Normal := CFSG.pCore_normal
  set Pq : Subgroup G := barPreimage D.M (CFSG.pCore q (Bar2 D.M)) with hPq
  have hPqM : Pq ≤ D.M := uc22p21c_barPreimage_le D.M _
  have hPqN : D.M ≤ Subgroup.normalizer (Pq : Set G) := uc22p22u_barPreimage_normalizes
  have hFr : D.M = Pq ⊔ (D.M ⊓ Subgroup.normalizer (Q0 : Set G)) :=
    UC6.frattini_of_isSylowOf hPqM hPqN hQ0
  have hQ0M : Q0 ≤ D.M := hQ0.le.trans hPqM
  have hPqEq : Pq = pCoreOf 2 D.M ⊔ Q0 :=
    barPreimage_eq_pCoreOf_sup_of_isSylowOf D hq hq2 hQ0
  calc D.M = Pq ⊔ (D.M ⊓ Subgroup.normalizer (Q0 : Set G)) := hFr
    _ = (pCoreOf 2 D.M ⊔ Q0) ⊔ (D.M ⊓ Subgroup.normalizer (Q0 : Set G)) := by rw [hPqEq]
    _ = pCoreOf 2 D.M ⊔ (Q0 ⊔ (D.M ⊓ Subgroup.normalizer (Q0 : Set G))) := sup_assoc _ _ _
    _ = pCoreOf 2 D.M ⊔ (D.M ⊓ Subgroup.normalizer (Q0 : Set G)) := by
      rw [sup_eq_right.mpr (le_inf hQ0M Subgroup.le_normalizer)]

private theorem T_eq_sup_of_sylow_barPreimage (D : Data G) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {Q0 : Subgroup G}
    (hQ0 : CFSG.ABGLocalTools.IsSylowOf q Q0
      (barPreimage D.M (CFSG.pCore q (Bar2 D.M)))) :
    D.T = pCoreOf 2 D.M ⊔ (D.T ⊓ Subgroup.normalizer (Q0 : Set G)) := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : (CFSG.pCore q (Bar2 D.M)).Normal := CFSG.pCore_normal
  have hM : D.M = pCoreOf 2 D.M ⊔ (D.M ⊓ Subgroup.normalizer (Q0 : Set G)) :=
    D_M_eq_pCoreOf_sup_normalizer D hq hq2 hQ0
  have hOT : pCoreOf 2 D.M ≤ D.T := uc22p22e_pCoreOf_le_T D
  have hMnormO : D.M ≤ Subgroup.normalizer (pCoreOf 2 D.M : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D.M
  set O : Subgroup G := pCoreOf 2 D.M with hO
  set N' : Subgroup G := D.M ⊓ Subgroup.normalizer (Q0 : Set G) with hN'
  have hN'O : N' ≤ Subgroup.normalizer (O : Set G) := inf_le_left.trans hMnormO
  have hMset : (D.M : Set G) = (O : Set G) * (N' : Set G) := by
    rw [hM, hO, hN']
    exact Subgroup.coe_mul_of_right_le_normalizer_left O N' hN'O
  have hTN' : D.T = O ⊔ (D.T ⊓ N') := by
    apply le_antisymm
    · intro x hx
      have hxM : x ∈ D.M := D.sylowM.le hx
      change x ∈ (D.M : Set G) at hxM
      rw [hMset] at hxM
      obtain ⟨o, ho, n, hn, hxeq⟩ := Set.mem_mul.1 hxM
      have hnT : n ∈ D.T := by
        have h1 : o⁻¹ * (o * n) ∈ D.T :=
          D.T.mul_mem (D.T.inv_mem (hOT ho)) (hxeq ▸ hx)
        simpa using h1
      rw [← hxeq]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ho)
        (Subgroup.mem_sup_right (Subgroup.mem_inf.2 ⟨hnT, hn⟩))
    · exact sup_le hOT inf_le_left
  rwa [hO, hN', ← inf_assoc, inf_eq_left.mpr D.sylowM.le] at hTN'

private theorem permutes_sup_of_le_normalizer {T N O Q : Subgroup G} (hT : T = N ⊔ O)
    (hNO : N ≤ Subgroup.normalizer (O : Set G))
    (hQO : Q ≤ Subgroup.normalizer (O : Set G))
    (hNQ : N ≤ Subgroup.normalizer (Q : Set G)) : Permutes T Q := by
  have hTset : (T : Set G) = (N : Set G) * (O : Set G) := by
    rw [hT]
    exact Subgroup.coe_mul_of_left_le_normalizer_right N O hNO
  have hOQ : (O : Set G) * (Q : Set G) = (Q : Set G) * (O : Set G) := by
    calc (O : Set G) * (Q : Set G) = ((O ⊔ Q : Subgroup G) : Set G) :=
          (Subgroup.coe_mul_of_right_le_normalizer_left O Q hQO).symm
      _ = ((Q ⊔ O : Subgroup G) : Set G) := by rw [sup_comm]
      _ = (Q : Set G) * (O : Set G) := Subgroup.coe_mul_of_left_le_normalizer_right Q O hQO
  have hNQset : (N : Set G) * (Q : Set G) = (Q : Set G) * (N : Set G) := by
    calc (N : Set G) * (Q : Set G) = ((N ⊔ Q : Subgroup G) : Set G) :=
          (Subgroup.coe_mul_of_left_le_normalizer_right N Q hNQ).symm
      _ = ((Q ⊔ N : Subgroup G) : Set G) := by rw [sup_comm]
      _ = (Q : Set G) * (N : Set G) := Subgroup.coe_mul_of_right_le_normalizer_left Q N hNQ
  unfold Permutes
  calc (T : Set G) * (Q : Set G) = ((N : Set G) * (O : Set G)) * (Q : Set G) := by
        rw [hTset]
    _ = (N : Set G) * ((O : Set G) * (Q : Set G)) := mul_assoc _ _ _
    _ = (N : Set G) * ((Q : Set G) * (O : Set G)) := by rw [hOQ]
    _ = ((N : Set G) * (Q : Set G)) * (O : Set G) := (mul_assoc _ _ _).symm
    _ = ((Q : Set G) * (N : Set G)) * (O : Set G) := by rw [hNQset]
    _ = (Q : Set G) * ((N : Set G) * (O : Set G)) := mul_assoc _ _ _
    _ = (Q : Set G) * (T : Set G) := by rw [hTset]

private theorem permutes_of_isSylowOf_barPreimage (D : Data G) {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) {Q0 Q : Subgroup G}
    (hQ0 : CFSG.ABGLocalTools.IsSylowOf q Q0
      (barPreimage D.M (CFSG.pCore q (Bar2 D.M))))
    (hQle : Q ≤ Q0)
    (hNQ : Subgroup.normalizer (Q0 : Set G) ≤ Subgroup.normalizer (Q : Set G)) :
    Permutes D.T Q := by
  classical
  set O : Subgroup G := pCoreOf 2 D.M with hO
  set N : Subgroup G := D.T ⊓ Subgroup.normalizer (Q0 : Set G) with hN
  have hT : D.T = O ⊔ N := by
    have h := T_eq_sup_of_sylow_barPreimage D hq hq2 hQ0
    simpa only [hO, hN] using h
  have hMnormO : D.M ≤ Subgroup.normalizer (O : Set G) := by
    rw [hO]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D.M
  have hNT : N ≤ D.T := by
    rw [hN]
    exact inf_le_left
  have hNO : N ≤ Subgroup.normalizer (O : Set G) := hNT.trans (D.sylowM.le.trans hMnormO)
  have hQO : Q ≤ Subgroup.normalizer (O : Set G) :=
    (hQle.trans hQ0.le).trans ((uc22p21c_barPreimage_le D.M _).trans hMnormO)
  have hNQ' : N ≤ Subgroup.normalizer (Q : Set G) := by
    rw [hN]
    exact inf_le_right.trans hNQ
  have hT' : D.T = N ⊔ O := by rw [hT, sup_comm]
  exact permutes_sup_of_le_normalizer hT' hNO hQO hNQ'

theorem injective_barImage_mk'_of_disjoint_pCoreOf {M Q : Subgroup G} {R : Subgroup (Bar2 M)}
    (hQM : Q ≤ M) (hdisj : Q ⊓ pCoreOf 2 M = ⊥) (f : ↥Q →* ↥R)
    (hf : ∀ x : ↥Q, (f x : Bar2 M) =
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) (Subgroup.inclusion hQM x)) :
    Function.Injective f := by
  intro x y hxy
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥M) (Subgroup.inclusion hQM x) =
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) (Subgroup.inclusion hQM y) := by
    rw [← hf x, ← hf y]
    exact congrArg Subtype.val hxy
  have h2 : QuotientGroup.mk' (CFSG.pCore 2 ↥M)
      (Subgroup.inclusion hQM (x⁻¹ * y)) = 1 := by
    have hmul : Subgroup.inclusion hQM (x⁻¹ * y) =
        Subgroup.inclusion hQM x⁻¹ * Subgroup.inclusion hQM y :=
      map_mul (Subgroup.inclusion hQM) x⁻¹ y
    rw [hmul, map_mul, map_inv, map_inv, h1, inv_mul_cancel]
  have h3 : (Subgroup.inclusion hQM (x⁻¹ * y) : ↥M) ∈ CFSG.pCore 2 ↥M :=
    (QuotientGroup.eq_one_iff _).1 h2
  have h4 : ((Subgroup.inclusion hQM (x⁻¹ * y) : ↥M) : G) ∈ Q ⊓ pCoreOf 2 M :=
    ⟨(x⁻¹ * y).2, ⟨_, h3, rfl⟩⟩
  have h5 : ((Subgroup.inclusion hQM (x⁻¹ * y) : ↥M) : G) = 1 :=
    Subgroup.mem_bot.1 (hdisj ▸ h4)
  have h6 : x⁻¹ * y = 1 := Subtype.ext (by simpa using h5)
  have hyx : y = x := by
    calc y = x * (x⁻¹ * y) := by group
      _ = x * 1 := by rw [h6]
      _ = x := mul_one x
  exact hyx.symm

private theorem omegaOne_is_qTorsion_of_isCyclic {Q0 : Subgroup G} {q : ℕ}
    (hQ0 : IsCyclic ↥Q0) :
    ∀ y ∈ CFSG.RankThree.PartOne.omegaOne q Q0, y ^ q = 1 := by
  have hcomm : ∀ a ∈ Q0, ∀ b ∈ Q0, a * b = b * a := by
    intro a ha b hb
    letI : IsCyclic ↥Q0 := hQ0
    letI : CommGroup ↥Q0 := IsCyclic.commGroup
    exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : ↥Q0) ⟨b, hb⟩)
  intro y hy
  have hp : y ∈ Q0 ∧ y ^ q = 1 := by
    induction hy using Subgroup.closure_induction with
    | mem z hz => exact hz
    | one => exact ⟨Q0.one_mem, by simp⟩
    | mul a b _ _ iha ihb =>
        refine ⟨Q0.mul_mem iha.1 ihb.1, ?_⟩
        have hc : Commute a b := hcomm a iha.1 b ihb.1
        rw [hc.mul_pow q, iha.2, ihb.2, one_mul]
    | inv z _ ih => exact ⟨Q0.inv_mem ih.1, by rw [inv_pow, ih.2, inv_one]⟩
  exact hp.2

private theorem omegaOne_ne_bot_of_isPGroup {Q0 : Subgroup G} {q : ℕ} (hq : q.Prime)
    (hQ0p : IsPGroup q ↥Q0) (hQ0ne : Q0 ≠ ⊥) :
    CFSG.RankThree.PartOne.omegaOne q Q0 ≠ ⊥ := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨k, hk⟩ := hQ0p.exists_card_eq
  have hk0 : k ≠ 0 := by
    intro hk0
    exact hQ0ne (Subgroup.eq_bot_of_card_eq Q0 (by simpa [hk0] using hk))
  have hqdvd : q ∣ Nat.card ↥Q0 := by
    rw [hk]
    exact dvd_pow_self q hk0
  obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' (G := ↥Q0) q hqdvd
  have hxq : (x : G) ^ q = 1 := by
    have h := pow_orderOf_eq_one x
    rw [hxord] at h
    exact congrArg Subtype.val h
  have hx1' : x ≠ 1 := by
    intro hxeq
    rw [hxeq, orderOf_one] at hxord
    exact hq.ne_one hxord.symm
  have hx1 : (x : G) ≠ 1 := fun h => hx1' (Subtype.ext h)
  intro hbot
  have hxQ : (x : G) ∈ CFSG.RankThree.PartOne.omegaOne q Q0 :=
    Subgroup.subset_closure ⟨x.2, hxq⟩
  rw [hbot] at hxQ
  exact hx1 (Subgroup.mem_bot.1 hxQ)

private theorem omegaOne_commutator_eq_bot_of_isCyclic {Q0 : Subgroup G} {q : ℕ}
    (hQ0 : IsCyclic ↥Q0) :
    ⁅⁅CFSG.RankThree.PartOne.omegaOne q Q0, CFSG.RankThree.PartOne.omegaOne q Q0⁆,
      CFSG.RankThree.PartOne.omegaOne q Q0⁆ = ⊥ := by
  have hcomm : ∀ a ∈ CFSG.RankThree.PartOne.omegaOne q Q0,
      ∀ b ∈ CFSG.RankThree.PartOne.omegaOne q Q0, a * b = b * a := by
    intro a ha b hb
    letI : IsCyclic ↥Q0 := hQ0
    letI : CommGroup ↥Q0 := IsCyclic.commGroup
    exact congrArg Subtype.val
      (mul_comm (⟨a, CFSG.RankThree.PartOne.Sec9Excl.omegaOne_le q Q0 ha⟩ : ↥Q0)
        ⟨b, CFSG.RankThree.PartOne.Sec9Excl.omegaOne_le q Q0 hb⟩)
  have hQcomm : IsMulCommutative ↥(CFSG.RankThree.PartOne.omegaOne q Q0) :=
    ⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩
  rw [Subgroup.commutator_self_eq_bot_iff.mpr hQcomm, Subgroup.commutator_bot_left]

private theorem exists_good_Q_data_cyclic (D : Data G) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {Q0 : Subgroup G}
    (hQ0 : CFSG.ABGLocalTools.IsSylowOf q Q0
      (barPreimage D.M (CFSG.pCore q (Bar2 D.M))))
    (hQ0M : Q0 ≤ D.M)
    (hbar : barImage D.M Q0 = CFSG.pCore q (Bar2 D.M) ∧ Q0 ⊓ pCoreOf 2 D.M = ⊥)
    (hQ0ne : Q0 ≠ ⊥) (hYcyc : IsCyclic ↥(CFSG.pCore q (Bar2 D.M))) :
    ∃ Q : Subgroup G, Q ≤ Q0 ∧ Q ≠ ⊥ ∧ (∀ x ∈ Q, x ^ q = 1) ∧ ⁅⁅Q, Q⁆, Q⁆ = ⊥ ∧
      (Q.subgroupOf (D.M ⊓ normalizer (Q0 : Set G))).Normal ∧ Permutes D.T Q ∧
      (¬ IsCyclic ↥(CFSG.pCore q (Bar2 D.M)) → ¬ IsCyclic ↥Q) := by
  classical
  have hQ0cyc : IsCyclic ↥Q0 := by
    let π : ↥D.M →* Bar2 D.M := QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)
    let φ : ↥Q0 →* ↥(barImage D.M Q0) :=
      (π.comp (Subgroup.inclusion hQ0M)).codRestrict (barImage D.M Q0) fun x =>
        uc22p21c_mem_barImage.2 ⟨Subgroup.inclusion hQ0M x, x.2, rfl⟩
    have hinj : Function.Injective φ :=
      injective_barImage_mk'_of_disjoint_pCoreOf hQ0M hbar.2 φ fun _ => rfl
    have hcyc : IsCyclic ↥(barImage D.M Q0) := by
      rw [hbar.1]
      exact hYcyc
    letI : IsCyclic ↥(barImage D.M Q0) := hcyc
    exact isCyclic_of_injective φ hinj
  let Q : Subgroup G := CFSG.RankThree.PartOne.omegaOne q Q0
  have hQle : Q ≤ Q0 := CFSG.RankThree.PartOne.Sec9Excl.omegaOne_le q Q0
  have hQexp : ∀ y ∈ Q, y ^ q = 1 := omegaOne_is_qTorsion_of_isCyclic hQ0cyc
  have hQne : Q ≠ ⊥ := omegaOne_ne_bot_of_isPGroup hq hQ0.isPGroup hQ0ne
  have hQcl : ⁅⁅Q, Q⁆, Q⁆ = ⊥ := omegaOne_commutator_eq_bot_of_isCyclic hQ0cyc
  have hNQ : Subgroup.normalizer (Q0 : Set G) ≤ Subgroup.normalizer (Q : Set G) :=
    fun h hh => CFSG.RankThree.PartOne.Sec9Excl.mem_normalizer_omegaOne hh
  have hperm : Permutes D.T Q := permutes_of_isSylowOf_barPreimage D hq hq2 hQ0 hQle hNQ
  have hQsub : Q ≤ D.M ⊓ Subgroup.normalizer (Q0 : Set G) :=
    le_inf (hQle.trans hQ0M)
      (hQle.trans (Subgroup.le_normalizer : Q0 ≤ Subgroup.normalizer (Q0 : Set G)))
  have hQn : (Q.subgroupOf (D.M ⊓ normalizer (Q0 : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQsub).mpr (inf_le_right.trans hNQ)
  exact ⟨Q, hQle, hQne, hQexp, hQcl, hQn, hperm, fun hY => absurd hYcyc hY⟩

private theorem exists_good_Q_data_noncyclic (D : Data G) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {Q0 : Subgroup G}
    (hQ0 : CFSG.ABGLocalTools.IsSylowOf q Q0
      (barPreimage D.M (CFSG.pCore q (Bar2 D.M))))
    (hQ0M : Q0 ≤ D.M)
    (hbar : barImage D.M Q0 = CFSG.pCore q (Bar2 D.M) ∧ Q0 ⊓ pCoreOf 2 D.M = ⊥)
    (hYnc : ¬ IsCyclic ↥(CFSG.pCore q (Bar2 D.M))) :
    ∃ Q : Subgroup G, Q ≤ Q0 ∧ Q ≠ ⊥ ∧ (∀ x ∈ Q, x ^ q = 1) ∧ ⁅⁅Q, Q⁆, Q⁆ = ⊥ ∧
      (Q.subgroupOf (D.M ⊓ normalizer (Q0 : Set G))).Normal ∧ Permutes D.T Q ∧
      (¬ IsCyclic ↥(CFSG.pCore q (Bar2 D.M)) → ¬ IsCyclic ↥Q) := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  have hQ0nc : ¬ IsCyclic ↥Q0 :=
    (uc22p22u_lift_props (r := q) hbar.1 hbar.2 hQ0M).2.2 hYnc
  obtain ⟨Q, hQle, hQne, hQnc, hQexp, hQcl, hQnorm⟩ :=
    CFSG.GroupTheory.exists_noncyclic_exponent_classTwo_normalized (G := G) (p := q)
      hq2 hQ0.isPGroup hQ0nc
  have hperm : Permutes D.T Q :=
    permutes_of_isSylowOf_barPreimage D hq hq2 hQ0 hQle hQnorm
  have hQsub : Q ≤ D.M ⊓ Subgroup.normalizer (Q0 : Set G) :=
    le_inf (hQle.trans hQ0M)
      (hQle.trans (Subgroup.le_normalizer : Q0 ≤ Subgroup.normalizer (Q0 : Set G)))
  have hQn : (Q.subgroupOf (D.M ⊓ normalizer (Q0 : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQsub).mpr (inf_le_right.trans hQnorm)
  exact ⟨Q, hQle, hQne, hQexp, hQcl, hQn, hperm, fun _ => hQnc⟩

theorem exists_good_Q (D : Data G) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hne : CFSG.pCore q (Bar2 D.M) ≠ ⊥) :
    ∃ Q₀ Q : Subgroup G,
      CFSG.ABGLocalTools.IsSylowOf q Q₀ (barPreimage D.M (CFSG.pCore q (Bar2 D.M))) ∧
      Q ≤ Q₀ ∧ Q ≠ ⊥ ∧ (∀ x ∈ Q, x ^ q = 1) ∧ ⁅⁅Q, Q⁆, Q⁆ = ⊥ ∧
      (Q.subgroupOf (D.M ⊓ normalizer (Q₀ : Set G))).Normal ∧ Permutes D.T Q ∧
      (¬ IsCyclic ↥(CFSG.pCore q (Bar2 D.M)) → ¬ IsCyclic ↥Q) := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : (CFSG.pCore q (Bar2 D.M)).Normal := CFSG.pCore_normal
  obtain ⟨Q0, hQ0⟩ := CFSG.ABGLocalTools.exists_isSylowOf q
    (barPreimage D.M (CFSG.pCore q (Bar2 D.M)))
  have hbar := uc22p22u_sylow_barPreimage (M := D.M) (r := q) hq hq2
    (CFSG.pCore_isPGroup (p := q)) hQ0
  have hQ0M : Q0 ≤ D.M := hQ0.le.trans (uc22p21c_barPreimage_le D.M _)
  have hQ0ne : Q0 ≠ ⊥ := by
    intro hbot
    apply hne
    rw [← hbar.1, hbot, barImage, Subgroup.bot_subgroupOf, Subgroup.map_bot]
  rcases Classical.em (IsCyclic ↥(CFSG.pCore q (Bar2 D.M))) with hYcyc | hYnc
  · obtain ⟨Q, hQle, hQne, hQexp, hQcl, hQn, hperm, himp⟩ :=
      exists_good_Q_data_cyclic D hq hq2 hQ0 hQ0M hbar hQ0ne hYcyc
    exact ⟨Q0, Q, hQ0, hQle, hQne, hQexp, hQcl, hQn, hperm, himp⟩
  · obtain ⟨Q, hQle, hQne, hQexp, hQcl, hQn, hperm, himp⟩ :=
      exists_good_Q_data_noncyclic D hq hq2 hQ0 hQ0M hbar hYnc
    exact ⟨Q0, Q, hQ0, hQle, hQne, hQexp, hQcl, hQn, hperm, himp⟩

theorem Ctx23L.inf_N_eq_bot {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (h1930 : H1930 D) (h72 : S23_7_2 D Ch) (h72s : S23_7_2_sig D Ch)
    (hsig : D.sig.Nonempty) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {Q₀ Q : Subgroup G}
    (hQ₀ : CFSG.ABGLocalTools.IsSylowOf q Q₀
      (barPreimage D.M (CFSG.pCore q (Bar2 D.M))))
    (hQQ₀ : Q ≤ Q₀) (hexp : ∀ x ∈ Q, x ^ q = 1) (hcl : ⁅⁅Q, Q⁆, Q⁆ = ⊥)
    (hQn : (Q.subgroupOf (D.M ⊓ normalizer (Q₀ : Set G))).Normal) (hTQ : Permutes D.T Q)
    (hcase : q ∈ D.sig ∨ ¬ IsCyclic ↥Q) : Q ⊓ c.N = ⊥ := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : (CFSG.pCore q (Bar2 D.M)).Normal := CFSG.pCore_normal
  set P : Subgroup G := barPreimage D.M (CFSG.pCore q (Bar2 D.M)) with hP
  have hPM : P ≤ D.M := uc22p21c_barPreimage_le D.M _
  have hQM : Q ≤ D.M := hQQ₀.trans (hQ₀.le.trans hPM)
  have hQp : IsPGroup q ↥Q := hQ₀.isPGroup.to_le hQQ₀
  have hQle : Q ≤ D.M ⊓ Subgroup.normalizer (Q₀ : Set G) :=
    le_inf hQM (hQQ₀.trans (Subgroup.le_normalizer : Q₀ ≤ normalizer (Q₀ : Set G)))
  by_cases hqsig : q ∈ D.sig
  · exact h72s h1930 c q hqsig Q hQM hQp hexp hcl c.N c.N_mem_calMOf_T c.N_ne_M hTQ
  · have hQnc : ¬ IsCyclic ↥Q := by
      rcases hcase with h | h
      · exact absurd h hqsig
      · exact h
    obtain ⟨p, hp⟩ := hsig
    have hpp : p.Prime := (D.sig_prime p hp).1
    have hp2 : p ≠ 2 := (D.sig_prime p hp).2
    have hpq : p ≠ q := fun h => hqsig (h ▸ hp)
    have hPn : (P.subgroupOf D.M).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hPM).mpr uc22p22u_barPreimage_normalizes
    have hPO : P ≤ CFSG.Open.relPPrimeCore p D.M :=
      barPreimage_le_relPPrimeCore (CFSG.pCore_normal (p := q)) (CFSG.pCore_isPGroup (p := q))
        hpp hq hpq hp2
    exact h72 h1930 c q hq hq2 Q hQM hQp hQnc hexp hcl p hp P hPM hPn hPO Q₀ hQ₀ hQle hQn
      c.N c.N_mem_calMOf_T c.N_ne_M hTQ

private theorem jOf_le (T : Subgroup G) : F12.jOf T ≤ T := by
  rw [F12.jOf, CFSG.inSubgroup]
  exact Subgroup.map_subtype_le _

theorem zOneOf_le (T : Subgroup G) : zOneOf T ≤ T := by
  rw [zOneOf, CFSG.inSubgroup]
  exact Subgroup.map_subtype_le _

private theorem map_jOf_subgroupOf {T X : Subgroup G} (hTX : T ≤ X) :
    (F12.jOf (T.subgroupOf X)).map X.subtype = F12.jOf T := by
  rw [F12.jOf, F12.jOf, CFSG.inSubgroup, CFSG.inSubgroup,
    ← CFSG.higherElemThompson_zero, ← CFSG.higherElemThompson_zero]
  exact CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.map_higherElemThompson_subgroupOf hTX 0

private theorem map_zOneOf_subgroupOf {T X : Subgroup G} (hTX : T ≤ X) :
    (zOneOf (T.subgroupOf X)).map X.subtype = zOneOf T := by
  rw [zOneOf, zOneOf, CFSG.inSubgroup, CFSG.inSubgroup]
  exact CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.map_higherElemThompsonOmega_subgroupOf
    hTX 1

private theorem isSolvable_sup_of_isPGroup_permutes {P T : Subgroup G} {q : ℕ} (hq : q.Prime)
    (hPq : IsPGroup q P) (hT2 : IsPGroup 2 T) (hq2 : q ≠ 2) (hPT : Permutes P T) :
    Group.IsSolvable ↥(P ⊔ T) := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  have hdisj : P ⊓ T = ⊥ :=
    disjoint_iff.1 (IsPGroup.disjoint_of_ne q 2 hq2 P T hPq hT2)
  have hcardP : Nat.card ↥(P.subgroupOf (P ⊔ T)) = Nat.card P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv
  have hcardT : Nat.card ↥(T.subgroupOf (P ⊔ T)) = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  obtain ⟨k, hk⟩ := hPq.exists_card_eq
  obtain ⟨m, hm⟩ := hT2.exists_card_eq
  have hcop : Nat.Coprime (Nat.card ↥(P.subgroupOf (P ⊔ T)))
      (Nat.card ↥(T.subgroupOf (P ⊔ T))) := by
    rw [hcardP, hcardT, hk, hm]
    exact Nat.Coprime.pow k m ((Nat.coprime_primes hq Nat.prime_two).mpr hq2)
  have hfac : ∀ g : ↥(P ⊔ T), ∃ a ∈ P.subgroupOf (P ⊔ T),
      ∃ b ∈ T.subgroupOf (P ⊔ T), g = a * b := by
    intro g
    have hU : ((P ⊔ T : Subgroup G) : Set G) = (P : Set G) * (T : Set G) :=
      CFSG.Quasithin.H23P4.coe_sup_eq_mul_of_mul_comm hPT
    have hg : (g : G) ∈ (P : Set G) * (T : Set G) := by
      rw [← hU]
      exact g.property
    obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.1 hg
    exact ⟨⟨a, Subgroup.mem_sup_left ha⟩, ha, ⟨b, Subgroup.mem_sup_right hb⟩, hb,
      Subtype.ext hab.symm⟩
  exact CFSG.GroupTheory.WielandtProduct.wielandt_coprime_product
    (P.subgroupOf (P ⊔ T)) (T.subgroupOf (P ⊔ T))
    (hPq.comap_subtype.isNilpotent) (hT2.comap_subtype.isNilpotent) hcop hfac

private theorem not_three_dvd_sup_of_isPGroup_permutes {P T : Subgroup G} {q : ℕ} (hq : q.Prime)
    (hPq : IsPGroup q P) (hT2 : IsPGroup 2 T) (hq5 : 5 ≤ q) (hPT : Permutes P T) :
    ¬ 3 ∣ Nat.card ↥(P ⊔ T) := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  have hq2 : q ≠ 2 := by omega
  have hdisj : P ⊓ T = ⊥ :=
    disjoint_iff.1 (IsPGroup.disjoint_of_ne q 2 hq2 P T hPq hT2)
  have hU : ((P ⊔ T : Subgroup G) : Set G) = (P : Set G) * (T : Set G) :=
    CFSG.Quasithin.H23P4.coe_sup_eq_mul_of_mul_comm hPT
  have hcard : Nat.card ↥(P ⊔ T) = Nat.card P * Nat.card T :=
    CFSG.Quasithin.H23P4.card_eq_mul_of_coe_eq_mul hU hdisj
  intro h3
  rw [hcard] at h3
  rcases (Nat.prime_three.dvd_mul).1 h3 with h | h
  · obtain ⟨k, hk⟩ := hPq.exists_card_eq
    rw [hk] at h
    have h3q : 3 ∣ q := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    have h3eq : 3 = q := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).mp h3q
    omega
  · obtain ⟨m, hm⟩ := hT2.exists_card_eq
    rw [hm] at h
    have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    norm_num at h32

private theorem charTwo_sup {M P T : Subgroup G} (hPM : P ≤ M) (hTM : T ≤ M)
    (hOT : pCoreOf 2 M ≤ T)
    (hMchar : M ⊓ Subgroup.centralizer (pCoreOf 2 M : Set G) ≤ pCoreOf 2 M) :
    CFSG.QuasithinUnique.CharTwo (P ⊔ T) := by
  intro x hx
  have hxM : x ∈ M := (sup_le hPM hTM) hx.1
  have hOleX : pCoreOf 2 M ≤ P ⊔ T := hOT.trans le_sup_right
  have hOlePC : pCoreOf 2 M ≤ pCoreOf 2 (P ⊔ T) :=
    uc22p21c_le_pCoreOf hOleX (uc22p21c_isPGroup_pCoreOf M) fun k hk y hy =>
      uc22p21c_conj_mem_pCoreOf_self ((sup_le hPM hTM) hk) hy
  have hxCO : x ∈ Subgroup.centralizer (pCoreOf 2 M : Set G) :=
    (Subgroup.centralizer_le hOlePC) hx.2
  exact hOlePC (hMchar (Subgroup.mem_inf.mpr ⟨hxM, hxCO⟩))

private theorem exists_sylow_two_subgroupOf (D : Data G) {q : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q)
    {Q : Subgroup G} (hQq : IsPGroup q ↥Q) (hTQ : Permutes D.T Q) :
    ∃ P : Sylow 2 ↥(Q ⊔ D.T), (P : Subgroup ↥(Q ⊔ D.T)) = D.T.subgroupOf (Q ⊔ D.T) := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  have hq2 : q ≠ 2 := by omega
  have hT2 : IsPGroup 2 ↥D.T := D.sylowM.isPGroup
  have hdisj : Q ⊓ D.T = ⊥ :=
    disjoint_iff.1 (IsPGroup.disjoint_of_ne q 2 hq2 Q D.T hQq hT2)
  have hU : ((Q ⊔ D.T : Subgroup G) : Set G) = (D.T : Set G) * (Q : Set G) := by
    rw [CFSG.Quasithin.H23P4.coe_sup_eq_mul_of_mul_comm hTQ.symm]
    exact hTQ.symm
  have hrel : D.T.relIndex (Q ⊔ D.T) = Nat.card ↥Q :=
    CFSG.Quasithin.H23P4.relIndex_eq_card_of_coe_eq_mul le_sup_right hU
      (by rw [inf_comm]; exact hdisj)
  have hindex : ¬ 2 ∣ (D.T.subgroupOf (Q ⊔ D.T)).index := by
    rw [show (D.T.subgroupOf (Q ⊔ D.T)).index = D.T.relIndex (Q ⊔ D.T) from rfl, hrel]
    obtain ⟨k, hk⟩ := hQq.exists_card_eq
    rw [hk]
    intro h2
    have h2q : 2 ∣ q := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2
    exact hq2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).mp h2q).symm
  have hTsub2 : IsPGroup 2 (D.T.subgroupOf (Q ⊔ D.T)) := hT2.comap_subtype
  exact ⟨hTsub2.toSylow hindex, hTsub2.toSylow_coe hindex⟩

private theorem thompson_QT_jOf_image (D : Data G) {Q : Subgroup G}
    {P : Sylow 2 ↥(Q ⊔ D.T)}
    (hPsub : (P : Subgroup ↥(Q ⊔ D.T)) = D.T.subgroupOf (Q ⊔ D.T)) :
    (F12.jOf (P : Subgroup ↥(Q ⊔ D.T))).map (Q ⊔ D.T).subtype = F12.jOf D.T := by
  rw [hPsub]
  exact map_jOf_subgroupOf le_sup_right

private theorem thompson_QT_zOne_image (D : Data G) {Q : Subgroup G}
    {P : Sylow 2 ↥(Q ⊔ D.T)}
    (hPsub : (P : Subgroup ↥(Q ⊔ D.T)) = D.T.subgroupOf (Q ⊔ D.T)) :
    (zOneOf (P : Subgroup ↥(Q ⊔ D.T))).map (Q ⊔ D.T).subtype = zOneOf D.T := by
  rw [hPsub]
  exact map_zOneOf_subgroupOf le_sup_right

private theorem thompson_QT_normalizer_image_j (D : Data G) {Q : Subgroup G}
    {P : Sylow 2 ↥(Q ⊔ D.T)}
    (hPsub : (P : Subgroup ↥(Q ⊔ D.T)) = D.T.subgroupOf (Q ⊔ D.T)) :
    (Q ⊔ D.T).subtype ''
        (Subgroup.normalizer (F12.jOf (P : Subgroup ↥(Q ⊔ D.T)) : Set ↥(Q ⊔ D.T))) =
      (((Q ⊔ D.T) ⊓ Subgroup.normalizer (F12.jOf D.T : Set G) : Subgroup G) : Set G) := by
  have hJle : F12.jOf D.T ≤ Q ⊔ D.T := (jOf_le D.T).trans le_sup_right
  have hJ := thompson_QT_jOf_image D hPsub
  have hJsub : F12.jOf (P : Subgroup ↥(Q ⊔ D.T)) =
      (F12.jOf D.T).subgroupOf (Q ⊔ D.T) := by
    apply Subgroup.map_injective (Q ⊔ D.T).subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hJle]
    exact hJ
  have hNJ : (Subgroup.normalizer
      (F12.jOf (P : Subgroup ↥(Q ⊔ D.T)) : Set ↥(Q ⊔ D.T))).map (Q ⊔ D.T).subtype =
        (Q ⊔ D.T) ⊓ Subgroup.normalizer (F12.jOf D.T : Set G) := by
    rw [hJsub]
    exact CFSG.Goldschmidt.G53.map_subtype_normalizer_subgroupOf hJle
  have := congrArg (fun N : Subgroup G => (N : Set G)) hNJ
  simpa [Subgroup.map] using this

private theorem thompson_QT_normalizer_image_z (D : Data G) {Q : Subgroup G}
    {P : Sylow 2 ↥(Q ⊔ D.T)}
    (hPsub : (P : Subgroup ↥(Q ⊔ D.T)) = D.T.subgroupOf (Q ⊔ D.T)) :
    (Q ⊔ D.T).subtype ''
        (Subgroup.normalizer (zOneOf (P : Subgroup ↥(Q ⊔ D.T)) : Set ↥(Q ⊔ D.T))) =
      (((Q ⊔ D.T) ⊓ Subgroup.normalizer (zOneOf D.T : Set G) : Subgroup G) : Set G) := by
  have hZle : zOneOf D.T ≤ Q ⊔ D.T := (zOneOf_le D.T).trans le_sup_right
  have hZ := thompson_QT_zOne_image D hPsub
  have hZsub : zOneOf (P : Subgroup ↥(Q ⊔ D.T)) =
      (zOneOf D.T).subgroupOf (Q ⊔ D.T) := by
    apply Subgroup.map_injective (Q ⊔ D.T).subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hZle]
    exact hZ
  have hNZ : (Subgroup.normalizer
      (zOneOf (P : Subgroup ↥(Q ⊔ D.T)) : Set ↥(Q ⊔ D.T))).map (Q ⊔ D.T).subtype =
        (Q ⊔ D.T) ⊓ Subgroup.normalizer (zOneOf D.T : Set G) := by
    rw [hZsub]
    exact CFSG.Goldschmidt.G53.map_subtype_normalizer_subgroupOf hZle
  have := congrArg (fun N : Subgroup G => (N : Set G)) hNZ
  simpa [Subgroup.map] using this

private theorem thompson_QT_transport (D : Data G) {Q : Subgroup G}
    {P : Sylow 2 ↥(Q ⊔ D.T)}
    (hPsub : (P : Subgroup ↥(Q ⊔ D.T)) = D.T.subgroupOf (Q ⊔ D.T))
    (hK : (Set.univ : Set ↥(Q ⊔ D.T)) =
      (Subgroup.normalizer (F12.jOf (P : Subgroup ↥(Q ⊔ D.T)) : Set ↥(Q ⊔ D.T)) : Set _) *
      (Subgroup.normalizer (zOneOf (P : Subgroup ↥(Q ⊔ D.T)) : Set ↥(Q ⊔ D.T)) : Set _)) :
    ((Q ⊔ D.T : Subgroup G) : Set G) =
      (((Q ⊔ D.T) ⊓ normalizer (F12.jOf D.T : Set G) : Subgroup G) : Set G) *
        (((Q ⊔ D.T) ⊓ normalizer (zOneOf D.T : Set G) : Subgroup G) : Set G) := by
  have hNJimg := thompson_QT_normalizer_image_j D hPsub
  have hNZimg := thompson_QT_normalizer_image_z D hPsub
  have hrange : Set.range (Q ⊔ D.T).subtype = ((Q ⊔ D.T : Subgroup G) : Set G) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hK' := congrArg (fun s : Set ↥(Q ⊔ D.T) => (Q ⊔ D.T).subtype '' s) hK
  rw [Set.image_univ, Set.image_mul, hrange, hNJimg, hNZimg] at hK'
  exact hK'

theorem thompson_QT (D : Data G) (hThomp : KThomp) {q : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q)
    {Q : Subgroup G} (hQ : Q ≤ barPreimage D.M (CFSG.pCore q (Bar2 D.M)))
    (hQq : IsPGroup q ↥Q) (hTQ : Permutes D.T Q) :
    ((Q ⊔ D.T : Subgroup G) : Set G) =
      (((Q ⊔ D.T) ⊓ normalizer (F12.jOf D.T : Set G) : Subgroup G) : Set G) *
        (((Q ⊔ D.T) ⊓ normalizer (zOneOf D.T : Set G) : Subgroup G) : Set G) := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  have hq2 : q ≠ 2 := by omega
  have hT2 : IsPGroup 2 ↥D.T := D.sylowM.isPGroup
  have hQM : Q ≤ D.M := hQ.trans (uc22p21c_barPreimage_le D.M _)
  have hsolv : Group.IsSolvable ↥(Q ⊔ D.T) :=
    isSolvable_sup_of_isPGroup_permutes hq hQq hT2 hq2 hTQ.symm
  have h3 : ¬ 3 ∣ Nat.card ↥(Q ⊔ D.T) :=
    not_three_dvd_sup_of_isPGroup_permutes hq hQq hT2 hq5 hTQ.symm
  have hcharX : CFSG.QuasithinUnique.CharTwo (Q ⊔ D.T) :=
    charTwo_sup hQM D.sylowM.le (uc22p22e_pCoreOf_le_T D)
      (D.standing.charTwo D.M D.maxLocal.1)
  have hchar : Subgroup.centralizer (CFSG.pCore 2 ↥(Q ⊔ D.T) : Set ↥(Q ⊔ D.T)) ≤
      CFSG.pCore 2 ↥(Q ⊔ D.T) :=
    (CFSG.QuasithinUnique.charTwo_iff_internal).mp hcharX
  obtain ⟨P, hPsub⟩ := exists_sylow_two_subgroupOf D hq hq5 hQq hTQ
  have hK := hThomp ↥(Q ⊔ D.T) hsolv h3 hchar P
  exact thompson_QT_transport D hPsub hK

theorem isCyclic_pCore_three_of_sylow (D : Data G)
    (h : ∀ P : Sylow 3 ↥(oTwoThreeOf D.M), IsCyclic ↥P) :
    IsCyclic ↥(CFSG.pCore 3 (Bar2 D.M)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 3 ↥(oTwoThreeOf D.M)))
  let Q : Subgroup G := (P : Subgroup ↥(oTwoThreeOf D.M)).map (oTwoThreeOf D.M).subtype
  have hQcyc : IsCyclic ↥Q := by
    let e := Subgroup.equivMapOfInjective (P : Subgroup ↥(oTwoThreeOf D.M))
      (oTwoThreeOf D.M).subtype (oTwoThreeOf D.M).subtype_injective
    letI : IsCyclic ↥(P : Subgroup ↥(oTwoThreeOf D.M)) := h P
    exact isCyclic_of_surjective e.toMonoidHom e.surjective
  have hQ0 : CFSG.ABGLocalTools.IsSylowOf 3 Q (oTwoThreeOf D.M) := ⟨P, rfl⟩
  have hbar := uc22p22u_sylow_barPreimage (M := D.M) (r := 3) Nat.prime_three (by norm_num)
    (CFSG.pCore_isPGroup (p := 3)) hQ0
  have hQleM : Q ≤ D.M := hQ0.le.trans (uc22p21c_barPreimage_le D.M _)
  have himp := (uc22p22u_lift_props (r := 3) hbar.1 hbar.2 hQleM).2.2
  by_contra hnc
  exact himp hnc hQcyc

theorem isCyclic_fitting_of_forall_pCore (D : Data G)
    (h : ∀ q : ℕ, q.Prime → q ≠ 2 → IsCyclic ↥(CFSG.pCore q (Bar2 D.M))) :
    IsCyclic ↥(CFSG.fittingSubgroup (Bar2 D.M)) := by
  by_contra hF
  obtain ⟨q, hq, hq2, hqnc⟩ :=
    exists_odd_prime_pCore_bar2_not_isCyclic (M := D.M) hF
  exact hqnc (h q hq hq2)

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
