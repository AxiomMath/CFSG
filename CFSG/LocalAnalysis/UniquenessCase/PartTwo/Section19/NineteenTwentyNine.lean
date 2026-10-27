module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.CtxLemmas
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenTwentyFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFactsNineteen
public import CFSG.GH74.Uniqueness.Section15HeringEnd2
public import CFSG.GroupTheory.QuasisimpleAutQuotient
public import CFSG.GroupTheory.SteinbergCBFTFactorization
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64AsmTwoBasic
public import CFSG.GroupTheory.PermutingProducts
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22rh
public import CFSG.Quasithin.Background.HTriPermute
public import CFSG.SignalizerFunctorTheorem.McBride.Models.Suzuki.Arith
public import CFSG.Adapters.Certificate43Check
public import CFSG.Quasithin.H13.NQCatC2JH
public import CFSG.Goldschmidt.Steps.G36Setup
public import CFSG.Timmesfeld.Orders.Bang

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F10
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped commutatorElement Pointwise IsMulCommutative

variable {G : Type} [Group G] [Finite G]

theorem inf_component_isSylow (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G}
    {t : G} {B : Subgroup G} {r : ℕ} {A₀ H : Subgroup G}
    (h : Ctx19_23 D V₀ V p L A t B r A₀ H)
    (h28 : R19_28At D V₀ V p L A t B r A₀ H h)
    {S K : Subgroup G} (hS : CFSG.ABGLocalTools.IsSylowOf 2 S (H ⊓ D.M))
    (hK : K ≤ H) (hcomp : CFSG.IsComponent (K.subgroupOf H)) :
    CFSG.ABGLocalTools.IsSylowOf 2 (S ⊓ K) K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact uc22p22r_fo_sylow_inf (h28 S hS).2.2
    (CFSG.Goldschmidt.isSubnormal_of_subgroupOf hK hcomp.2)

theorem not_le_M_of_actsFaithfullyOn (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L A : Subgroup G} {t : G} {B : Subgroup G} {r : ℕ} {A₀ H : Subgroup G}
    (h : Ctx19_23 D V₀ V p L A t B r A₀ H)
    {K : Subgroup G} (hK : K ≤ H) (hcomp : CFSG.IsComponent (K.subgroupOf H))
    (hfaith : ActsFaithfullyOn V₀ K) : ¬ K ≤ D.M := by
  intro hKM
  have hV0ne : V₀ ≠ ⊥ := ne_bot_of_one_lt_mSub h.ctx22.ctx.hyp.big
  have hV0in : InCalV D.M V₀ := (inCalV0_of_hyp125 h.ctx22.ctx.hyp.hyp125 hV0ne).1
  have hV0N : V₀ ≤ normalizer (K : Set G) := nineteen_twentyfour_two D h K hK hcomp
  have hKNV : K ≤ normalizer (V₀ : Set G) := hKM.trans hV0in.2.2.1
  have hKq : CFSG.IsQuasisimple ↥K :=
    (CFSG.IsQuasisimple.congr (Subgroup.subgroupOfEquivOfLe hK)).mp hcomp.1
  have hKperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp hKq.1
  let Dsub : Subgroup G := ⁅K, V₀⁆
  have hDsubV0 : Dsub ≤ V₀ :=
    (Subgroup.le_normalizer_iff_commutator_le_right (H := K) (K := V₀)).mp hKNV
  have hDsubK : Dsub ≤ K :=
    (Subgroup.le_normalizer_iff_commutator_le_left (H := V₀) (K := K)).mp hV0N
  have hDsubNormal : (Dsub.subgroupOf K).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hDsubK]
    have hsup : (Dsub.subgroupOf (K ⊔ V₀)).Normal := by
      simpa [Dsub] using CFSG.commutator_normal_in_sup K V₀
    have hDsubSup : Dsub ≤ K ⊔ V₀ := hDsubK.trans le_sup_left
    exact (le_sup_left : K ≤ K ⊔ V₀).trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hDsubSup).mp hsup)
  have hKnoncomm : ¬ ∀ a b : ↥K, a * b = b * a := by
    intro hc
    have hcomm : ⁅K, K⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      simpa using congrArg Subtype.val (hc ⟨x, hx⟩ ⟨y, hy⟩).symm
    have hbot : K = ⊥ := by rw [← hKperf, hcomm]
    haveI := CFSG.LocalCores.isQuasisimple_nontrivial hKq
    haveI : Subsingleton ↥K := by rw [hbot]; infer_instance
    exact not_subsingleton ↥K inferInstance
  have hDsubCent : Dsub ≤ (Subgroup.center ↥K).map K.subtype := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hKq hDsubNormal with htop | hcenter
    · exfalso
      have hDK : Dsub = K := by
        rw [← Subgroup.map_subgroupOf_eq_of_le hDsubK, htop, Subgroup.map_top,
          Subgroup.range_subtype]
      have hKV0 : K ≤ V₀ := hDK ▸ hDsubV0
      apply hKnoncomm
      intro a b
      apply Subtype.ext
      have h := hV0in.2.2.2.1.is_comm.comm
        (⟨(a : G), hKV0 a.2⟩ : ↥V₀) (⟨(b : G), hKV0 b.2⟩ : ↥V₀)
      simpa using congrArg Subtype.val h
    · calc Dsub = (Dsub.subgroupOf K).map K.subtype :=
            (Subgroup.map_subgroupOf_eq_of_le hDsubK).symm
        _ ≤ (Subgroup.center ↥K).map K.subtype := Subgroup.map_mono hcenter
  have hDsubCentral : ⁅Dsub, K⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro d hd
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    obtain ⟨z, hz, hzeq⟩ := Subgroup.mem_map.mp (hDsubCent hd)
    rw [← hzeq]
    simpa using congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨k, hk⟩)
  have h1 : ⁅⁅K, V₀⁆, K⁆ = ⊥ := hDsubCentral
  have h2 : ⁅⁅V₀, K⁆, K⁆ = ⊥ := by
    rwa [Subgroup.commutator_comm (H₁ := V₀) (H₂ := K)]
  have hrot : ⁅⁅K, K⁆, V₀⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := K) (H₂ := K) (H₃ := V₀) h1 h2
  have hKV0 : ⁅K, V₀⁆ = ⊥ := by rwa [hKperf] at hrot
  have hV0K : ⁅V₀, K⁆ = ⊥ := by
    rwa [Subgroup.commutator_comm (H₁ := V₀) (H₂ := K)]
  have hV0cent : V₀ ≤ Subgroup.centralizer (K : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := V₀) (H₂ := K)).mp hV0K
  have hle : V₀ ≤ V₀ ⊓ Subgroup.centralizer (K : Set G) := le_inf le_rfl hV0cent
  rw [hfaith] at hle
  exact hV0ne (le_bot_iff.mp hle)

theorem r_ne_three {A : Subgroup G} {n r : ℕ} (hA : IsZModSq A n) (hr : r ∈ piSet A)
    (hn : Odd n) : r ≠ 3 := by
  obtain ⟨hrp, hrdvd⟩ := hr
  have hcard := card_eq_of_isZModSq hA
  have hdvd : r ∣ 2 ^ n - 1 := by
    rw [hcard, ← pow_two] at hrdvd
    exact hrp.dvd_of_dvd_pow hrdvd
  rintro rfl
  exact CFSG.GH74.Uniqueness.Hering.three_not_dvd_two_pow_sub_one hn hdvd

theorem permutes_ES_of_ctx (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G}
    {t : G} {B : Subgroup G} {r : ℕ} {A₀ H : Subgroup G}
    (h : Ctx19_23 D V₀ V p L A t B r A₀ H)
    (h28 : R19_28At D V₀ V p L A t B r A₀ H h)
    {S E : Subgroup G} (hS : CFSG.ABGLocalTools.IsSylowOf 2 S (H ⊓ D.M))
    (hEA : E ≤ A) (hEel : CFSG.Open.IsElemAbelian r E) (hEcard : Nat.card E = r ^ 2) :
    Permutes E S := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hASperm, hASidx, _hSH⟩ := h28 S hS
  have hAcomm : IsMulCommutative ↥A := isMulCommutative_of_isZModSq h.ctx22.ctx.hAcard
  haveI : IsMulCommutative ↥A := hAcomm
  have hAodd : Odd (Nat.card A) := odd_card_of_ctx19_10 h.ctx22.ctx
  have hS2 : IsPGroup 2 ↥S := hS.isPGroup
  have hASdisj : A ⊓ S = ⊥ := by
    refine disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard ?_)
    obtain ⟨k, hk⟩ := hS2.exists_card_eq
    rw [hk]
    exact (Nat.coprime_two_right.mpr hAodd).pow_right k
  have hAH : A ≤ H := A_le_H_of_ctx19_23 h
  have hAM : A ≤ D.M := A_le_M_of_ctx19_10 D h.ctx22.ctx
  have hASle : A ⊔ S ≤ H ⊓ D.M := sup_le (le_inf hAH hAM) hS.le
  let P : Subgroup G := pCoreOf 2 (A ⊔ S)
  have hP2 : IsPGroup 2 ↥P := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (A ⊔ S)
  have hPleAS : P ≤ A ⊔ S := CFSG.LieType.BorelTits.pCoreOf_le 2 (A ⊔ S)
  have hAnormP : A ≤ normalizer (P : Set G) :=
    le_sup_left.trans ((Subgroup.le_normalizer (H := A ⊔ S)).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (A ⊔ S)))
  have hSleNP : S ≤ normalizer (P : Set G) :=
    le_sup_right.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (A ⊔ S))
  have hPleS : P ≤ S := by
    have hQ2 : IsPGroup 2 ↥(P ⊔ S) := IsPGroup.to_sup_of_normal_left' hP2 hS2 hSleNP
    have hQle : P ⊔ S ≤ H ⊓ D.M := sup_le (hPleAS.trans hASle) hS.le
    have heq : P ⊔ S = S := hS.eq_of_le le_sup_right hQle hQ2
    exact le_sup_left.trans (le_of_eq heq)
  have hAPdisj : A ⊓ P = ⊥ := by
    refine disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard ?_)
    obtain ⟨k, hk⟩ := hP2.exists_card_eq
    rw [hk]
    exact (Nat.coprime_two_right.mpr hAodd).pow_right k
  have hcardAP : Nat.card ↥(A ⊔ P) = Nat.card A * Nat.card P := by
    rw [sup_comm, Nat.mul_comm]
    refine CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer P A hAnormP ?_
    exact disjoint_comm.mpr (disjoint_iff.mpr hAPdisj)
  have hcardAS : Nat.card ↥(A ⊔ S) = Nat.card A * Nat.card S := by
    have hcoe : ((A ⊔ S : Subgroup G) : Set G) = (A : Set G) * (S : Set G) :=
      CFSG.Quasithin.A4.coe_sup_eq_mul_of_mul_comm hASperm.symm
    have h1 := CFSG.GroupTheory.FT63ChII.card_setMul_mul_card_inf A S
    rw [hASdisj, Subgroup.card_bot, mul_one] at h1
    have hEq : ↥(A ⊔ S) = ↥(((A ⊔ S : Subgroup G) : Set G)) := rfl
    rw [hEq, hcoe]
    exact h1
  have hAPleAS : A ⊔ P ≤ A ⊔ S := sup_le le_sup_left (hPleS.trans le_sup_right)
  have hrel : (A ⊔ P).relIndex (A ⊔ S) = P.relIndex S := by
    have h1 := Subgroup.relIndex_mul_card (A ⊔ P) (A ⊔ S)
    rw [inf_eq_left.mpr hAPleAS, hcardAP, hcardAS] at h1
    have h2 := Subgroup.relIndex_mul_card P S
    rw [inf_eq_left.mpr hPleS] at h2
    have heq : (A ⊔ P).relIndex (A ⊔ S) * (Nat.card A * Nat.card P) =
        P.relIndex S * (Nat.card A * Nat.card P) := by
      calc (A ⊔ P).relIndex (A ⊔ S) * (Nat.card A * Nat.card P)
          = Nat.card A * Nat.card S := h1
        _ = Nat.card S * Nat.card A := Nat.mul_comm _ _
        _ = (P.relIndex S * Nat.card P) * Nat.card A := by rw [h2]
        _ = P.relIndex S * (Nat.card A * Nat.card P) := by ring
    exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos (Nat.card_pos (α := ↥A))
      (Nat.card_pos (α := ↥P))) heq
  have hnormal : ((A ⊔ P).subgroupOf (A ⊔ S)).Normal := by
    have hindex : ((A ⊔ P).subgroupOf (A ⊔ S)).index = (A ⊔ P).relIndex (A ⊔ S) := rfl
    have hidx2 : P.relIndex S ≤ 2 := hASidx
    have hle : ((A ⊔ P).subgroupOf (A ⊔ S)).index ≤ 2 := hindex.trans_le (hrel.le.trans hidx2)
    rcases Nat.lt_or_ge ((A ⊔ P).subgroupOf (A ⊔ S)).index 2 with hlt | hge
    · have hne := Subgroup.index_ne_zero_of_finite (H := (A ⊔ P).subgroupOf (A ⊔ S))
      have hone : ((A ⊔ P).subgroupOf (A ⊔ S)).index = 1 := by omega
      rw [Subgroup.index_eq_one] at hone
      rw [hone]
      infer_instance
    · have htwo : ((A ⊔ P).subgroupOf (A ⊔ S)).index = 2 := by omega
      exact Subgroup.normal_of_index_eq_two htwo
  have hASleN : A ⊔ S ≤ normalizer ((A ⊔ P : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAPleAS).mp hnormal
  have hSleN : S ≤ normalizer ((A ⊔ P : Subgroup G) : Set G) :=
    fun s hs => hASleN (Subgroup.mem_sup_right hs)
  have hEeq : E = (MonoidHom.ker (powMonoidHom r : ↥A →* ↥A)).map A.subtype :=
    eq_powTorsionSubgroup_of_isElemAbelian_card h.ctx22.ctx.hAcard h.ctx22.ctx.hr.1
      h.ctx22.ctx.hr.2 hEA hEel hEcard
  have hEleNP : E ≤ normalizer (P : Set G) := hEA.trans hAnormP
  have hAPcoe : ((A ⊔ P : Subgroup G) : Set G) = (A : Set G) * (P : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right A P hAnormP
  have hconj_mem : ∀ s ∈ S, ∀ e ∈ E, s * e * s⁻¹ ∈ E ⊔ P := by
    intro s hs e he
    have hx : s * e * s⁻¹ ∈ A ⊔ P :=
      (Subgroup.mem_normalizer_iff.mp (hSleN hs) e).1 (Subgroup.mem_sup_left (hEA he))
    have hx' : s * e * s⁻¹ ∈ ((A ⊔ P : Subgroup G) : Set G) := hx
    rw [hAPcoe] at hx'
    obtain ⟨a, ha, p, hp, hap⟩ := hx'
    have hxr : (s * e * s⁻¹) ^ r = 1 := by
      have h1 : (s * e * s⁻¹) ^ r = (MulAut.conj s) (e ^ r) := by
        rw [show s * e * s⁻¹ = (MulAut.conj s) e from (MulAut.conj_apply s e).symm,
          ← map_pow]
      rw [h1, hEel.2 e he, map_one]
    have hapr : (a * p) ^ r = 1 := by
      rw [show a * p = s * e * s⁻¹ from hap]
      exact hxr
    have hkey : ∀ n : ℕ, ∃ q ∈ P, (a * p) ^ n = a ^ n * q := by
      intro n
      induction n with
      | zero => exact ⟨1, P.one_mem, by simp⟩
      | succ n ih =>
          obtain ⟨q, hq, hqn⟩ := ih
          have hq' : a⁻¹ * q * a ∈ P := by
            simpa using (Subgroup.mem_normalizer_iff.mp
              (Subgroup.inv_mem _ (hAnormP ha)) q).1 hq
          refine ⟨a⁻¹ * q * a * p, P.mul_mem hq' hp, ?_⟩
          rw [pow_succ (a * p) n, hqn, pow_succ a n]
          group
    obtain ⟨q, hq, hqr⟩ := hkey r
    have hmemP : a ^ r ∈ P := by
      have h1 : a ^ r * q = 1 := by rw [← hqr]; exact hapr
      have h2 : a ^ r = q⁻¹ := by
        calc a ^ r = (a ^ r * q) * q⁻¹ := by group
          _ = 1 * q⁻¹ := by rw [h1]
          _ = q⁻¹ := by simp
      rw [h2]
      exact P.inv_mem hq
    have har1 : a ^ r = 1 := by
      have hbot : a ^ r ∈ A ⊓ P := ⟨A.pow_mem ha r, hmemP⟩
      rw [hAPdisj] at hbot
      exact Subgroup.mem_bot.mp hbot
    have haE : a ∈ E := by
      rw [hEeq]
      exact mem_powTorsionSubgroup.mpr ⟨ha, har1⟩
    rw [← hap]
    exact Subgroup.mul_mem_sup haE hp
  have hstep : ∀ t ∈ S, ∀ x ∈ (E ⊔ P : Subgroup G), t * x * t⁻¹ ∈ E ⊔ P := by
    intro t ht x hx
    have hcomap : (E ⊔ P : Subgroup G) ≤
        Subgroup.comap (MulAut.conj t).toMonoidHom (E ⊔ P) := by
      refine sup_le ?_ ?_
      · intro e he
        simpa [MulAut.conj_apply] using hconj_mem t ht e he
      · intro p hp
        simpa [MulAut.conj_apply] using
          (Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hSleNP ht) p).1 hp) :
            t * p * t⁻¹ ∈ E ⊔ P)
    exact hcomap hx
  have hSleNEP : S ≤ normalizer ((E ⊔ P : Subgroup G) : Set G) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact ⟨fun hx => hstep s hs x hx, fun hx => by
      have h := hstep s⁻¹ (S.inv_mem hs) (s * x * s⁻¹) hx
      have hx' : s⁻¹ * (s * x * s⁻¹) * s⁻¹⁻¹ = x := by group
      rwa [hx'] at h⟩
  have hEPcoe : ((E ⊔ P : Subgroup G) : Set G) = (E : Set G) * (P : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right E P hEleNP
  have hSEES : (S : Set G) * (E : Set G) ⊆ (E : Set G) * (S : Set G) := by
    rintro z ⟨s, hs, e, he, rfl⟩
    have h1 : s * e * s⁻¹ ∈ E ⊔ P := hconj_mem s hs e he
    have h1' : s * e * s⁻¹ ∈ ((E ⊔ P : Subgroup G) : Set G) := h1
    rw [hEPcoe] at h1'
    obtain ⟨e', he', p, hp, hep⟩ := h1'
    refine ⟨e', he', p * s, S.mul_mem (hPleS hp) hs, ?_⟩
    calc e' * (p * s) = (e' * p) * s := by group
      _ = (s * e * s⁻¹) * s := by rw [← hep]
      _ = s * e := by group
  have hESSE : (E : Set G) * (S : Set G) ⊆ (S : Set G) * (E : Set G) := by
    rintro z ⟨e, he, s, hs, rfl⟩
    have hmem : s⁻¹ * e⁻¹ ∈ (S : Set G) * (E : Set G) :=
      ⟨s⁻¹, S.inv_mem hs, e⁻¹, E.inv_mem he, rfl⟩
    obtain ⟨e', he', s', hs', heq⟩ := hSEES hmem
    refine ⟨s'⁻¹, S.inv_mem hs', e'⁻¹, E.inv_mem he', ?_⟩
    calc s'⁻¹ * e'⁻¹ = (e' * s')⁻¹ := by group
      _ = (s⁻¹ * e⁻¹)⁻¹ := congrArg Inv.inv heq
      _ = e * s := by group
  exact Set.Subset.antisymm hESSE hSEES

theorem p_sylow_of_ctx (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G}
    {t : G} {B : Subgroup G} {r : ℕ} {A₀ H : Subgroup G}
    (h : Ctx19_23 D V₀ V p L A t B r A₀ H)
    (h27 : R19_27At D V₀ V p L A t B r A₀ H h)
    (h28 : R19_28At D V₀ V p L A t B r A₀ H h)
    {E K S : Subgroup G} (hEA : E ≤ A) (hEel : CFSG.Open.IsElemAbelian r E)
    (hEcard : Nat.card E = r ^ 2) (hK : K ≤ H)
    (hcomp : CFSG.IsComponent (K.subgroupOf H))
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S (H ⊓ D.M)) :
    CFSG.ABGLocalTools.IsSylowOf 2 (S ⊓ normalizer (K : Set G))
      ((K ⊔ E ⊔ (S ⊓ normalizer (K : Set G))) ⊓ normalizer (K : Set G)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Subgroup G := S ⊓ normalizer (K : Set G)
  let EP : Subgroup G := E ⊔ P
  let N : Subgroup G := (K ⊔ E ⊔ P) ⊓ normalizer (K : Set G)
  have hE_norm : E ≤ normalizer (K : Set G) := hEA.trans (h27 K hK hcomp)
  have hP_norm : P ≤ normalizer (K : Set G) := inf_le_right
  have hEP_norm : EP ≤ normalizer (K : Set G) := sup_le hE_norm hP_norm
  have hS2 : IsPGroup 2 ↥S := hS.isPGroup
  have hP2 : IsPGroup 2 ↥P := hS2.to_le inf_le_left
  have hPleN : P ≤ N := le_inf (le_sup_right : P ≤ K ⊔ E ⊔ P) (inf_le_right :
    P ≤ normalizer (K : Set G))
  have hsup_le : K ⊔ E ⊔ P ≤ normalizer (K : Set G) :=
    sup_le (sup_le (Subgroup.le_normalizer) hE_norm) hP_norm
  have hN : N = K ⊔ E ⊔ P := inf_eq_left.mpr hsup_le
  have hN_eq : N = K ⊔ EP := by
    rw [hN, sup_assoc]
  have hES : Permutes E S := permutes_ES_of_ctx D h h28 hS hEA hEel hEcard
  have hES_coe : ((E ⊔ S : Subgroup G) : Set G) = (E : Set G) * (S : Set G) :=
    CFSG.Quasithin.A4.coe_sup_eq_mul_of_mul_comm hES.symm
  have hEP_le_ES : EP ≤ E ⊔ S := sup_le le_sup_left (inf_le_left.trans le_sup_right)
  have hEP_set : ((EP : Subgroup G) : Set G) = (E : Set G) * (P : Set G) := by
    refine Set.Subset.antisymm ?_ ?_
    · intro x hx
      have hxES : x ∈ (E ⊔ S : Subgroup G) := hEP_le_ES hx
      change x ∈ ((E ⊔ S : Subgroup G) : Set G) at hxES
      rw [hES_coe] at hxES
      obtain ⟨e, he, s, hs, rfl⟩ := hxES
      have hxN : e * s ∈ normalizer (K : Set G) := hEP_norm hx
      have heN : e ∈ normalizer (K : Set G) := hE_norm he
      have hsN : s ∈ normalizer (K : Set G) := by
        have h1 : e⁻¹ ∈ normalizer (K : Set G) := Subgroup.inv_mem _ heN
        have h2 : e⁻¹ * (e * s) ∈ normalizer (K : Set G) := Subgroup.mul_mem _ h1 hxN
        simpa using h2
      exact ⟨e, he, s, Subgroup.mem_inf.mpr ⟨hs, hsN⟩, rfl⟩
    · rintro _ ⟨e, he, p, hp, rfl⟩
      exact Subgroup.mul_mem_sup he hp
  have hEP_disj : E ⊓ P = ⊥ := by
    have hAodd : Odd (Nat.card A) := odd_card_of_ctx19_10 h.ctx22.ctx
    have hEodd : Odd (Nat.card E) := Odd.of_dvd_nat hAodd (Subgroup.card_dvd_of_le hEA)
    obtain ⟨k, hk⟩ := hP2.exists_card_eq
    refine disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard ?_)
    rw [hk]
    exact (Nat.coprime_two_right.mpr hEodd).pow_right k
  have hEP_card : Nat.card ↥EP = Nat.card ↥E * Nat.card ↥P := by
    have h := CFSG.GroupTheory.FT63ChII.card_setMul_mul_card_inf E P
    rw [← hEP_set, hEP_disj, Subgroup.card_bot, mul_one] at h
    exact h
  have hN_card : Nat.card ↥N * Nat.card ↥(K ⊓ EP) = Nat.card ↥K * Nat.card ↥EP := by
    have hN_set : ((N : Subgroup G) : Set G) = (K : Set G) * (EP : Set G) := by
      rw [hN_eq]
      exact Subgroup.coe_mul_of_right_le_normalizer_left K EP hEP_norm
    have h := CFSG.GroupTheory.FT63ChII.card_setMul_mul_card_inf K EP
    rw [← hN_set] at h
    exact h
  have hSylK : CFSG.ABGLocalTools.IsSylowOf 2 (S ⊓ K) K :=
    inf_component_isSylow D h h28 hS hK hcomp
  have hKcapP : K ⊓ P = S ⊓ K := by
    dsimp only [P]
    have hKS_le_N : S ⊓ K ≤ normalizer (K : Set G) :=
      (inf_le_right : S ⊓ K ≤ K).trans (Subgroup.le_normalizer)
    calc K ⊓ (S ⊓ normalizer (K : Set G)) = (K ⊓ S) ⊓ normalizer (K : Set G) :=
          (inf_assoc K S (normalizer (K : Set G))).symm
      _ = (S ⊓ K) ⊓ normalizer (K : Set G) :=
          congrArg (fun X => X ⊓ normalizer (K : Set G)) (inf_comm K S)
      _ = S ⊓ K := inf_eq_left.mpr hKS_le_N
  have hKcapP_card : Nat.card ↥(K ⊓ P) = 2 ^ (Nat.card ↥K).factorization 2 := by
    rw [hKcapP]
    exact hSylK.card_eq
  have hKcapP_fac : (Nat.card ↥(K ⊓ P)).factorization 2 =
      (Nat.card ↥K).factorization 2 := by
    rw [hKcapP_card]
    have h2 : Nat.Prime 2 := Nat.prime_two
    rw [h2.factorization_pow]
    simp
  have hfac_le1 : (Nat.card ↥(K ⊓ P)).factorization 2 ≤
      (Nat.card ↥(K ⊓ EP)).factorization 2 :=
    ((Nat.factorization_le_iff_dvd (Nat.card_pos.ne') (Nat.card_pos.ne')).mpr
      (Subgroup.card_dvd_of_le (inf_le_inf_left K (le_sup_right : P ≤ EP)))) 2
  have hfac_le2 : (Nat.card ↥(K ⊓ EP)).factorization 2 ≤
      (Nat.card ↥K).factorization 2 :=
    ((Nat.factorization_le_iff_dvd (Nat.card_pos.ne') (Nat.card_pos.ne')).mpr
      (Subgroup.card_dvd_of_le (inf_le_left : K ⊓ EP ≤ K))) 2
  have hKcapEP_fac : (Nat.card ↥(K ⊓ EP)).factorization 2 =
      (Nat.card ↥K).factorization 2 := by omega
  have hAodd : Odd (Nat.card A) := odd_card_of_ctx19_10 h.ctx22.ctx
  have hEodd : Odd (Nat.card E) := Odd.of_dvd_nat hAodd (Subgroup.card_dvd_of_le hEA)
  have h2dvd : ¬ 2 ∣ Nat.card ↥E := fun hd =>
    (Nat.not_even_iff_odd.mpr hEodd) (even_iff_two_dvd.mpr hd)
  have hEfac : (Nat.card ↥E).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd h2dvd
  have hfacN : (Nat.card ↥N).factorization 2 + (Nat.card ↥(K ⊓ EP)).factorization 2 =
      (Nat.card ↥K).factorization 2 + (Nat.card ↥EP).factorization 2 := by
    have hfac := congrArg (fun m : ℕ => m.factorization 2) hN_card
    rw [Nat.factorization_mul (Nat.card_pos.ne') (Nat.card_pos.ne'),
      Nat.factorization_mul (Nat.card_pos.ne') (Nat.card_pos.ne')] at hfac
    change (Nat.card ↥N).factorization 2 + (Nat.card ↥(K ⊓ EP)).factorization 2 =
      (Nat.card ↥K).factorization 2 + (Nat.card ↥EP).factorization 2 at hfac
    exact hfac
  have hEP_fac : (Nat.card ↥EP).factorization 2 = (Nat.card ↥P).factorization 2 := by
    rw [hEP_card, Nat.factorization_mul (Nat.card_pos.ne') (Nat.card_pos.ne')]
    change (Nat.card ↥E).factorization 2 + (Nat.card ↥P).factorization 2 =
      (Nat.card ↥P).factorization 2
    rw [hEfac, zero_add]
  have hN_fac : (Nat.card ↥N).factorization 2 = (Nat.card ↥P).factorization 2 := by omega
  obtain ⟨k, hk⟩ := hP2.exists_card_eq
  have hP_card : Nat.card ↥P = 2 ^ (Nat.card ↥N).factorization 2 := by
    rw [hk] at hN_fac ⊢
    rw [hN_fac]
    have h2 : Nat.Prime 2 := Nat.prime_two
    rw [h2.factorization_pow]
    simp
  exact CFSG.ABGLocalTools.isSylowOf_of_card hPleN hP_card

open scoped MatrixGroups in
theorem k_J1JankoRee_holds :
    ∀ (X : Type) [Group X], CFSG.LocalAnalysis.UniquenessCase.UC22.IsJ1 X →
      CFSG.LocalAnalysis.UniquenessCase.UC22.F10.IsJankoReeType10 X := by
  intro X _ hX
  obtain ⟨e⟩ := hX
  let e' : X ≃* CFSG.Open.walterJ1 := e.trans CFSG.Walter.walterJ1EquivNative.symm
  haveI : Finite X := Finite.of_equiv _ e'.toEquiv.symm
  let hJ : CFSG.Walter.J1.JankoHyp X :=
    CFSG.Quasithin.H13.NQCat.C2.jankoHypOfMulEquiv CFSG.Walter.J1Props.jankoHyp e'
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨φ⟩ := CFSG.SectionRank.Ccomm.projective_five_alternating
  refine ⟨fun P => ?_, hJ.t, hJ.F, ZMod 5, inferInstance, inferInstance, hJ.orderOf_t,
    by rw [ZMod.card]; decide, by rw [ZMod.card]; decide, hJ.t_not_mem, hJ.le_centralizer,
    hJ.centralizer_eq, ⟨hJ.iso.trans φ.symm⟩⟩
  obtain ⟨hcard, hsq, hcomm, -⟩ := hJ.sylow_structure P
  exact ⟨hcard, fun x hx y hy => ⟨hcomm x hx y hy, by rw [pow_two]; exact hsq x hx⟩⟩

theorem not_thirteen_dvd_two_pow_sub_one_of_odd {n : ℕ} (hn : Odd n) : ¬ 13 ∣ 2 ^ n - 1 := by
  intro hdvd
  have h2pow : (2 : ZMod 13) ^ n = 1 :=
    (CFSG.Timmesfeld.Bang.dvd_two_pow_sub_one_iff n).mp hdvd
  have hord : orderOf (2 : ZMod 13) = 12 := by
    rw [orderOf_eq_iff (by norm_num : 0 < 12)]
    refine ⟨by decide, ?_⟩
    intro m hm _
    interval_cases m <;> decide
  have h12 : 12 ∣ n := by
    rw [← hord]
    exact orderOf_dvd_iff_pow_eq_one.mpr h2pow
  obtain ⟨k, rfl⟩ := hn
  omega

theorem nineteen_twentynine
    (V : LieAutVocab10) (D : Data G) {V₀ Vsub : Subgroup G} {p : ℕ}
    {L A : Subgroup G} {t : G} {B : Subgroup G} {r : ℕ} {A₀ H E K S : Subgroup G}
    (h : Ctx19_23 D V₀ Vsub p L A t B r A₀ H)
    (h12 : R19_12At D V₀ Vsub p L A t B r h.ctx22.ctx)
    (h26 : R19_26At D V₀ Vsub p L A t B r A₀ H h)
    (h27 : R19_27At D V₀ Vsub p L A t B r A₀ H h)
    (h28 : R19_28At D V₀ Vsub p L A t B r A₀ H h)
    (hK101 : CFSG.LocalAnalysis.UniquenessCase.UC22.F10.K101)
    (hK104 : CFSG.LocalAnalysis.UniquenessCase.UC22.F10.K104 V)
    (hK105 : CFSG.LocalAnalysis.UniquenessCase.UC22.F10.K105)
    (hcat : K_CatalogModels) (hTits : K_TitsOddPrimes) :
    R19_29At V D V₀ Vsub p L A t B r A₀ H E K S h := by
  intro hEA hEel hEcard hKH hKcomp hfaith hS
  classical
  let P : Subgroup G := S ⊓ normalizer (K : Set G)
  let N : Subgroup G := (K ⊔ E ⊔ P) ⊓ normalizer (K : Set G)
  have hPsyl : CFSG.ABGLocalTools.IsSylowOf 2 P N :=
    p_sylow_of_ctx D h h27 h28 hEA hEel hEcard hKH hKcomp hS
  let f : ↥N →* MulAut ↥K :=
    (Subgroup.normalizerMonoidHom (H := K)).comp (Subgroup.inclusion inf_le_right)
  let CK : Subgroup ↥N := CFSG.GroupTheory.quasisimpleActionKernel N K inf_le_right
  letI : CK.Normal := CFSG.GroupTheory.quasisimpleActionKernel_normal N K inf_le_right
  let G₀ : Type := ↥N ⧸ CK
  let Kbar : Subgroup G₀ := (K.subgroupOf N).map (QuotientGroup.mk' CK)
  let Ebar : Subgroup G₀ := (E.subgroupOf N).map (QuotientGroup.mk' CK)
  let Tbar : Subgroup G₀ := (S.subgroupOf N).map (QuotientGroup.mk' CK)
  change (∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ UC22.IsChev Kbar q) ∨
    UC22.F10.IsJankoReeType10 Kbar ∨
    (UC22.IsChev Kbar 2 ∧ ∃ x ∈ Ebar, V.InducesField Kbar x) ∨
    (UC22.IsChev Kbar 2 ∧ (∀ x ∈ Ebar, ¬ V.InducesField Kbar x) ∧
      ∃ C : Subgroup G₀, UC22.F10.CartanActing10 (Kbar ⊔ Ebar) Tbar C ∧ Ebar ≤ C)
  have hE_norm : E ≤ normalizer (K : Set G) := hEA.trans (h27 K hKH hKcomp)
  have hKN : K ≤ N := le_inf (le_sup_left.trans le_sup_left) Subgroup.le_normalizer
  have hEN : E ≤ N := le_inf ((le_sup_right : E ≤ K ⊔ E).trans le_sup_left) hE_norm
  have hPN : P ≤ N := le_inf le_sup_right inf_le_right
  have hPleS : P ≤ S := inf_le_left
  have hNnorm : N ≤ normalizer (K : Set G) := inf_le_right
  have hPsub_syl : CFSG.ABGLocalTools.IsSylowOf 2 (P.subgroupOf N) ⊤ := by
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff N]
    have htopN : (⊤ : Subgroup ↥N).map N.subtype = N := by
      rw [Subgroup.map_top, Subgroup.range_subtype]
    rw [htopN, Subgroup.map_subgroupOf_eq_of_le hPN]
    exact hPsyl
  have hSN_eq : S.subgroupOf N = P.subgroupOf N := by
    ext x
    change ((x : G) ∈ S) ↔ ((x : G) ∈ P)
    constructor
    · intro hxS
      exact ⟨hxS, hNnorm x.2⟩
    · intro hxP
      exact hxP.1
  have hTbar_syl : CFSG.ABGLocalTools.IsSylowOf 2 Tbar ⊤ := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h := uc22p22r_isSylowOf_map_top (QuotientGroup.mk'_surjective CK) hPsub_syl
    simpa [Tbar, hSN_eq] using h
  have hKq : CFSG.IsQuasisimple ↥K :=
    (CFSG.IsQuasisimple.congr (Subgroup.subgroupOfEquivOfLe hKH)).mp hKcomp.1
  have hKbar_simple : IsSimpleGroup ↥Kbar := by
    simpa [Kbar, CK, f, G₀, CFSG.GroupTheory.quasisimpleActionKernel] using
      CFSG.GroupTheory.quasisimple_isSimpleGroup_image N K hKN inf_le_right hKq
  have hKbar_nonab : ∃ a b : ↥Kbar, a * b ≠ b * a := by
    simpa [Kbar, CK, f, G₀, CFSG.GroupTheory.quasisimpleActionKernel] using
      CFSG.GroupTheory.quasisimple_nonabelian_image N K hKN inf_le_right hKq
  have hFstar : CFSG.Open.genFittingFStar G₀ = Kbar := by
    simpa [G₀, Kbar, CK, f, CFSG.GroupTheory.quasisimpleActionKernel] using
      CFSG.GroupTheory.quasisimple_genFittingFStar_image_eq N K hKN inf_le_right hKq
  haveI : IsSimpleGroup G := D.standing.simple
  have hcenter : Subgroup.center G = ⊥ :=
    CFSG.Walter.center_eq_bot_of_isSimpleGroup D.standing.nonab
  have hHne_top : H ≠ ⊤ := by
    intro hHtop
    have hA0center : A₀ ≤ Subgroup.center G := by
      intro a ha
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ Subgroup.centralizer (A₀ : Set G) := by
        rw [← h.hH, hHtop]
        exact Subgroup.mem_top g
      exact (Subgroup.mem_centralizer_iff.mp hg a ha).symm
    have hA0bot : A₀ = ⊥ := le_bot_iff.mp (hA0center.trans (le_of_eq hcenter))
    have hcard := h.ctx22.hcard
    rw [hA0bot, Subgroup.card_bot] at hcard
    have hr2 : 2 ≤ r := h.ctx22.ctx.hr.1.two_le
    omega
  have hKne_top : K ≠ ⊤ := fun hKtop => hHne_top (top_unique (hKtop ▸ hKH))
  let φ : ↥K →* ↥Kbar :=
    MonoidHom.codRestrict ((QuotientGroup.mk' CK).comp (Subgroup.inclusion hKN)) Kbar
      (fun k => Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr k.2))
  have hφ_surj : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective CK y
    obtain ⟨x, hx, hxeq⟩ := Subgroup.mem_map.mp hy
    have hxK : (x : G) ∈ K := Subgroup.mem_subgroupOf.mp hx
    refine ⟨⟨(x : G), hxK⟩, ?_⟩
    apply Subtype.ext
    exact hxeq
  have hKbar_cat : CFSG.Open.IsCatalogGroup ↥Kbar :=
    CFSG.KCore.KProperNonab.catalogue_of_surjective CFSG.Open.isCatalogGroup_isoInvariant
      D.standing.kProper K hKne_top hKbar_nonab φ hφ_surj
  have hEbar_ne : Ebar ≠ ⊥ := by
    intro hbot
    have hE_cent : E ≤ Subgroup.centralizer (K : Set G) := by
      intro e he
      have hmem : (⟨e, hEN he⟩ : ↥N) ∈ CK := by
        have h1 : QuotientGroup.mk' CK ⟨e, hEN he⟩ = 1 := by
          have h2 : QuotientGroup.mk' CK ⟨e, hEN he⟩ ∈ Ebar :=
            Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr he)
          rwa [hbot] at h2
        exact (QuotientGroup.eq_one_iff _).mp h1
      have hf : f ⟨e, hEN he⟩ = 1 := MonoidHom.mem_ker.mp hmem
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have hval : (f ⟨e, hEN he⟩) ⟨k, hk⟩ = ⟨k, hk⟩ := by rw [hf]; rfl
      have hconj : e * k * e⁻¹ = k := by
        have := congrArg Subtype.val hval
        simpa [f, Subgroup.normalizerMonoidHom_apply_apply_coe] using this
      calc k * e = (e * k * e⁻¹) * e := by rw [hconj]
        _ = e * k := by group
    have hK_cent : K ≤ Subgroup.centralizer (E : Set G) :=
      (Subgroup.le_centralizer_iff (H := K) (K := E)).mpr hE_cent
    have hEU : E ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet D.M := h12 E hEA hEel hEcard
    have hNE : normalizer (E : Set G) ≤ D.M :=
      CFSG.LocalAnalysis.RankThreeUC.normalizer_le_of_mem_uniqueSet D.maxLocal hEU
    have hKM : K ≤ D.M := hK_cent.trans (Subgroup.centralizer_le_normalizer _ |>.trans hNE)
    exact not_le_M_of_actsFaithfullyOn D h hKH hKcomp hfaith hKM
  have hEbar_comm : IsMulCommutative ↥Ebar := by
    have hEcomm : IsMulCommutative ↥E := hEel.1
    simpa [Ebar, CK, f, G₀] using Subgroup.map_isMulCommutative (E.subgroupOf N)
      (QuotientGroup.mk' CK)
  have hcardE : Nat.card ↥(E.subgroupOf N) = Nat.card ↥E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEN).toEquiv
  have hEbar_odd : Odd (Nat.card ↥Ebar) := by
    have hEodd : Odd (Nat.card ↥E) :=
      Odd.of_dvd_nat (odd_card_of_ctx19_10 h.ctx22.ctx) (Subgroup.card_dvd_of_le hEA)
    exact Odd.of_dvd_nat hEodd
      (hcardE ▸ Subgroup.card_map_dvd (E.subgroupOf N) (QuotientGroup.mk' CK))
  have hEP : Permutes E P :=
    CFSG.GroupTheory.permutes_inf_of_le hE_norm (permutes_ES_of_ctx D h h28 hS hEA hEel hEcard)
  have hEPN : Permutes (E.subgroupOf N) (P.subgroupOf N) :=
    CFSG.Quasithin.H.Tri.subgroupOf_mul_comm hEN hPN hEP
  have hEbar_perm : Permutes Ebar Tbar := by
    change Permutes ((E.subgroupOf N).map (QuotientGroup.mk' CK))
      ((S.subgroupOf N).map (QuotientGroup.mk' CK))
    rw [hSN_eq]
    exact CFSG.GroupTheory.map_permutes_map (QuotientGroup.mk' CK) hEPN
  have hEbar_dvd : Nat.card ↥Ebar ∣ Nat.card ↥E := by
    have h := Subgroup.card_map_dvd (E.subgroupOf N) (QuotientGroup.mk' CK)
    rwa [show Nat.card ↥Ebar = Nat.card ↥((E.subgroupOf N).map (QuotientGroup.mk' CK)) from rfl,
      hcardE] at h
  have hEbar_rank : ∀ q : ℕ, q.Prime → q ∣ Nat.card ↥Ebar →
      CFSG.Open.pRank q Ebar ≤ 2 := by
    intro q hq hdvd
    have hqr : q = r := by
      have hdvd' : q ∣ r ^ 2 := by
        rw [← hEcard]
        exact hdvd.trans hEbar_dvd
      have hqr' : q ∣ r := hq.dvd_of_dvd_pow hdvd'
      exact ((Nat.Prime.dvd_iff_eq h.ctx22.ctx.hr.1 hq.ne_one).mp hqr').symm
    rw [hqr]
    refine CFSG.SectionRank.pRank_le h.ctx22.ctx.hr.1.one_lt ?_
    intro F hF hFel
    have hdvdF : Nat.card ↥F ∣ r ^ 2 := by
      rw [← hEcard]
      exact (Subgroup.card_dvd_of_le hF).trans hEbar_dvd
    exact Nat.le_of_dvd (pow_pos h.ctx22.ctx.hr.1.pos 2) hdvdF
  have hHyp10 : UC22.F10.Hyp10 Tbar Ebar :=
    ⟨hTbar_syl, hEbar_comm, hEbar_odd, hEbar_perm, hEbar_rank⟩
  have hcontra3 : IsPGroup 3 ↥Ebar → False := by
    intro h3
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨k, hk⟩ := h3.exists_card_eq
    have hdvd : Nat.card ↥Ebar ∣ r ^ 2 := by
      rw [← hEcard]
      exact hEbar_dvd
    rw [hk] at hdvd
    have hr3 : r ≠ 3 := r_ne_three h.ctx22.ctx.hAcard h.ctx22.ctx.hr h26
    have h3r : ¬ 3 ∣ r ^ 2 := by
      intro hdv
      have h3dvd : 3 ∣ r := Nat.prime_three.dvd_of_dvd_pow hdv
      exact hr3 ((Nat.Prime.dvd_iff_eq h.ctx22.ctx.hr.1 (by norm_num : 3 ≠ 1)).mp h3dvd)
    have hk0 : k = 0 := by
      by_contra hk0
      have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
      exact h3r ((dvd_pow_self 3 hkpos.ne').trans hdvd)
    have hcard1 : Nat.card ↥Ebar = 1 := by rw [hk, hk0]; simp
    exact hEbar_ne (Subgroup.card_eq_one.mp hcard1)
  have hrdvd : r ∣ 2 ^ (S17.nOf L) - 1 := by
    obtain ⟨hrp, hrdvdA⟩ := h.ctx22.ctx.hr
    rw [card_eq_of_isZModSq h.ctx22.ctx.hAcard, ← pow_two] at hrdvdA
    exact hrp.dvd_of_dvd_pow hrdvdA
  have hrodd : Odd r :=
    Odd.of_dvd_nat (odd_card_of_ctx19_10 h.ctx22.ctx) h.ctx22.ctx.hr.2
  have hr_ne_two : r ≠ 2 := by
    intro h2
    rw [h2] at hrodd
    norm_num at hrodd
  have hr_ne_three : r ≠ 3 := r_ne_three h.ctx22.ctx.hAcard h.ctx22.ctx.hr h26
  rcases CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64Asm.catalog_trichotomy hKbar_cat hKbar_nonab
    with halt | ⟨rL, hLie⟩ | ⟨s, hSpor⟩
  ·
    obtain ⟨n, hn, ⟨e⟩⟩ := halt
    have h3 : IsPGroup 3 ↥Ebar :=
      hK101 G₀ Tbar Ebar hHyp10 (by rw [hFstar]; exact ⟨n, ⟨e⟩⟩)
    exact (hcontra3 h3).elim
  ·
    have hchev : UC22.IsChev ↥Kbar rL := hcat.1 ↥Kbar rL hLie
    have hprime : rL.Prime := by
      obtain ⟨idx, -, hidx⟩ := hLie
      exact hidx ▸ idx.1.characteristic_prime
    by_cases hrL : rL = 2
    ·
      subst hrL
      have hnotTits : ¬ UC22.F10.IsTits10 ↥Kbar := by
        intro hT
        have hT' : UC22.F10.IsTits10 ↥(CFSG.Open.genFittingFStar G₀) := by
          rw [hFstar]
          exact hT
        have hCstar : Subgroup.centralizer (CFSG.Open.genFittingFStar G₀ : Set G₀) = ⊥ := by
          rw [hFstar]
          simpa [Kbar, CK, f, G₀, CFSG.GroupTheory.quasisimpleActionKernel] using
            CFSG.GroupTheory.quasisimple_centralizer_image_eq_bot N K hKN inf_le_right hKq
        haveI : Fact (Nat.Prime r) := ⟨h.ctx22.ctx.hr.1⟩
        have hEbarp : IsPGroup r ↥Ebar := by
          have hEsubp : IsPGroup r ↥(E.subgroupOf N) :=
            hEel.isPGroup.comap_subtype (K := N)
          simpa [Ebar] using hEsubp.map (QuotientGroup.mk' CK)
        have hdvdEbar : r ∣ Nat.card ↥Ebar := by
          obtain ⟨k, hk⟩ := hEbarp.exists_card_eq
          have hkpos : 0 < k := by
            by_contra hk0
            have hk0' : k = 0 := Nat.eq_zero_of_not_pos hk0
            rw [hk0', pow_zero] at hk
            exact hEbar_ne (Subgroup.card_eq_one.mp hk)
          rw [hk]
          exact dvd_pow_self r hkpos.ne'
        have htopcard : Nat.card ↥(⊤ : Subgroup G₀) = Nat.card G₀ :=
          Nat.card_congr (Subgroup.topEquiv (G := G₀)).toEquiv
        have hdvdG : r ∣ Nat.card G₀ :=
          hdvdEbar.trans (htopcard ▸ Subgroup.card_dvd_of_le le_top)
        rcases hTits G₀ hT' hCstar r h.ctx22.ctx.hr.1 hr_ne_two hdvdG with h3 | h5 | h13
        · exact hr_ne_three h3
        · subst h5
          obtain ⟨m, hm⟩ : Odd (S17.nOf L) := h26
          rw [hm] at hrdvd
          exact CFSG.SignalizerFunctorTheorem.McBride.SzModel.not_five_dvd_two_pow_sub_one m hrdvd
        · subst h13
          exact not_thirteen_dvd_two_pow_sub_one_of_odd h26 hrdvd
      by_cases hfield : ∃ x ∈ Ebar, V.InducesField Kbar x
      · exact Or.inr (Or.inr (Or.inl ⟨hchev, hfield⟩))
      · push Not at hfield
        have h3not : ¬ 3 ∣ Nat.card ↥Ebar := by
          intro h3dvd
          have hdvd : Nat.card ↥Ebar ∣ r ^ 2 := by
            rw [← hEcard]
            exact hEbar_dvd
          have h3r2 : 3 ∣ r ^ 2 := h3dvd.trans hdvd
          have h3r : 3 ∣ r := Nat.prime_three.dvd_of_dvd_pow h3r2
          exact hr_ne_three ((Nat.Prime.dvd_iff_eq h.ctx22.ctx.hr.1 (by norm_num : 3 ≠ 1)).mp h3r)
        obtain ⟨C, hC⟩ :=
          hK104 G₀ Tbar Ebar hHyp10 Kbar (by rw [hFstar]) hchev hnotTits h3not hfield
        exact Or.inr (Or.inr (Or.inr ⟨hchev, hfield, C,
          by simpa [sup_comm] using hC.1, hC.2⟩))
    ·
      exact Or.inl ⟨rL, hprime, hrL, hchev⟩
  ·
    have hSpor' : ∃ s, UC22.IsSpor ↥Kbar s := ⟨s, hcat.2 ↥Kbar s hSpor⟩
    have hK105' : IsPGroup 3 ↥Ebar ∨ (UC22.IsJ1 G₀ ∧ Nat.card ↥Ebar = 7) :=
      hK105 G₀ Tbar Ebar hHyp10 (by rw [hFstar]; exact hSpor')
    rcases hK105' with h3 | ⟨hJ1G, hcard7⟩
    · exact (hcontra3 h3).elim
    · haveI :
      ∀ s t : Equiv.Perm (Fin 3),
        (s ≠ 1 ∧ s ^ 2 = 1) → (t ≠ 1 ∧ t ^ 2 = 1) → s ≠ t →
          (s * t) ^ 3 = 1 ∧ s * t ≠ 1 := CFSG.Adapters.certificate43_holds
      haveI := CFSG.Walter.J1Props.isSimpleGroup_walterJ1
      haveI : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .J1) :=
        MulEquiv.isSimpleGroup CFSG.Walter.walterJ1EquivNative.symm
      haveI : IsSimpleGroup G₀ := by
        obtain ⟨e⟩ := hJ1G
        exact MulEquiv.isSimpleGroup e
      have hnonab : ∃ a b : G₀, a * b ≠ b * a := by
        obtain ⟨a, b, hab⟩ := hKbar_nonab
        exact ⟨a, b, fun hc => hab (Subtype.ext hc)⟩
      have hGtop : CFSG.Open.genFittingFStar G₀ = ⊤ :=
        CFSG.ComponentClassification.StandardRecognition.genFittingFStar_eq_top_of_isSimpleGroup
          hnonab
      have hKbar_top : Kbar = ⊤ := by rw [← hFstar, hGtop]
      have hJ1Kbar : UC22.IsJ1 ↥Kbar := by
        obtain ⟨e⟩ := hJ1G
        rw [hKbar_top]
        exact ⟨(Subgroup.topEquiv (G := G₀)).trans e⟩
      exact Or.inr (Or.inl (k_J1JankoRee_holds ↥Kbar hJ1Kbar))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

