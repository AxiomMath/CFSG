module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenTwentyNine
public import CFSG.GroupTheory.QuasisimpleInvolutionFixed
public import CFSG.GroupTheory.TripleProductCentralizer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSevenDiag
public import CFSG.CGT.T75G.Sec68Basic
public import CFSG.CGT.Foote82.D1Steps
public import CFSG.Timmesfeld.Bridge.Asc72YCount
public import CFSG.GH74.GLS.AssemblyComponents

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.GH74.GLS.Stage2.Signalizer.Ivk8 (Zsub Zsub_le)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem center_facts_of_ctx19_23 (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G}
    {t : G} {B : Subgroup G} {r : ℕ} {A₀ H : Subgroup G}
    (h : Ctx19_23 D V₀ V p L A t B r A₀ H) {K : Subgroup G} (hK : K ≤ H)
    (hKcomp : CFSG.IsComponent (K.subgroupOf H)) :
    Odd (Nat.card (Subgroup.center ↥K)) ∧ V₀ ≤ centralizer (Zsub K : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKsubH : CFSG.Assembly.IsSubnormal K H :=
    (CFSG.Assembly.IsSubnormal.iff_subgroupOf hK).mpr hKcomp.2
  have hKsubHopen : CFSG.Open.IsSubnormal K H :=
    CFSG.Assembly.isSubnormal_iff_open.mp hKsubH
  have hZsubK : (Zsub K).subgroupOf K = Subgroup.center ↥K := by
    rw [Zsub]
    exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
  have hZrelK : CFSG.Open.IsSubnormal (Zsub K) K := by
    refine CFSG.Open.IsSubnormal.step (H := Zsub K) (M := K) (Zsub_le K) ?_
      (CFSG.Open.IsSubnormal.refl K)
    rw [hZsubK]
    infer_instance
  have hZrelH : CFSG.Open.IsSubnormal (Zsub K) H := hZrelK.trans hKsubHopen
  have hZsubH : ((Zsub K).subgroupOf H).IsSubnormal :=
    CFSG.Open.IsSubnormal.subgroupOf hZrelH
  have hPcore_le : pCoreOf 2 K ≤ K := CFSG.LieType.BorelTits.pCoreOf_le 2 K
  have hPcore_norm : K ≤ normalizer (pCoreOf 2 K : Set G) := by
    have hsub : (pCoreOf 2 K).subgroupOf K = CFSG.pCore 2 ↥K := by
      rw [pCoreOf]
      exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hPcore_le).mp (by rw [hsub]; infer_instance)
  have hPcore_normal : ((pCoreOf 2 K).subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPcore_le).mpr hPcore_norm
  have hPcore_subK : CFSG.Open.IsSubnormal (pCoreOf 2 K) K :=
    CFSG.Open.IsSubnormal.step (H := pCoreOf 2 K) (M := K) hPcore_le hPcore_normal
      (CFSG.Open.IsSubnormal.refl K)
  have hPcore_subH : CFSG.Open.IsSubnormal (pCoreOf 2 K) H :=
    hPcore_subK.trans hKsubHopen
  have hPcoreH : pCoreOf 2 (pCoreOf 2 K) ≤ pCoreOf 2 H :=
    CFSG.CGT.Foote82.pCoreOf_le_pCoreOf_of_isSubnormal hPcore_subH
  rw [h.hO2] at hPcoreH
  have hPself : pCoreOf 2 (pCoreOf 2 K) = pCoreOf 2 K := by
    refine le_antisymm (CFSG.LieType.BorelTits.pCoreOf_le 2 _) ?_
    exact CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_pCoreOf 2 _ _ le_rfl
      (by rw [Subgroup.subgroupOf_self]; infer_instance)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
  have hPbot : pCoreOf 2 K = ⊥ := by rw [← hPself]; exact le_bot_iff.mp hPcoreH
  have hKcore : CFSG.pCore 2 ↥K = ⊥ := by
    apply (Subgroup.map_eq_bot_iff_of_injective (H := CFSG.pCore 2 ↥K)
      (f := K.subtype) K.subtype_injective).mp
    simpa [CFSG.Open.pCoreOf] using hPbot
  have hZcenterOdd : Odd (Nat.card (Subgroup.center ↥K)) :=
    CFSG.Timmesfeld.Bridge.Asc72.CentralQuot.odd_card_center hKcore
  have hZodd : Odd (Nat.card (Zsub K)) := by
    rw [Zsub, Subgroup.card_map_of_injective K.subtype_injective]
    exact hZcenterOdd
  have hZleO : Zsub K ≤ Oodd H := by
    have hZH : Zsub K ≤ H := (Zsub_le K).trans hK
    have hcardZ' : Nat.card ↥((Zsub K).subgroupOf H) = Nat.card (Zsub K) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZH).toEquiv
    have hcop : Nat.Coprime 2 (Nat.card ↥((Zsub K).subgroupOf H)) :=
      Nat.coprime_two_left.mpr (by rw [hcardZ']; exact hZodd)
    have hle := CFSG.GH74.GLS.le_pPrimeCore_of_subnormal (X := ↥H) 2 hZsubH hcop
    change (Zsub K).subgroupOf H ≤ CFSG.pPrimeCore 2 ↥H at hle
    have hmap := Subgroup.map_mono (f := H.subtype) hle
    rwa [Subgroup.map_subgroupOf_eq_of_le hZH] at hmap
  have hZleC : Zsub K ≤ centralizer (V₀ : Set G) := by
    have h24_1 : ⁅V₀, Oodd H⁆ = ⊥ := nineteen_twentyfour_one D h
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hmem : ⁅v, z⁆ ∈ ⁅V₀, Oodd H⁆ :=
      Subgroup.commutator_mem_commutator hv (hZleO hz)
    rw [h24_1] at hmem
    exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp hmem)
  exact ⟨hZcenterOdd, Subgroup.le_centralizer_iff.mp hZleC⟩

theorem nineteen_twentysix_orbit_three (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L A : Subgroup G} {t : G} {B : Subgroup G} {A₀ H : Subgroup G}
    (h : Ctx19_23 D V₀ V p L A t B 3 A₀ H) {E K : Subgroup G} (hEA : E ≤ A)
    (hEel : IsElemAbelian 3 E) (hEcard : Nat.card E = 9) (hA₀E : A₀ ≤ E)
    (hNEM : normalizer (E : Set G) ≤ D.M) (hKH : K ≤ H)
    (hKcomp : CFSG.IsComponent (K.subgroupOf H)) (hfaith : ActsFaithfullyOn V₀ K)
    (hZodd : Odd (Nat.card (Subgroup.center ↥K)))
    (hENK : ¬ E ≤ normalizer (K : Set G)) : False := by
  classical
  obtain ⟨e, heE, heNK⟩ := Set.not_subset.mp hENK
  have he3 : e ^ 3 = 1 := hEel.2 e heE
  have hAH : A ≤ H := A_le_H_of_ctx19_23 h
  have heH : e ∈ H := hAH (hEA heE)
  have he2H : e ^ 2 ∈ H := by
    rw [pow_two]
    exact H.mul_mem heH heH
  have hA₀CH : A₀ ≤ Subgroup.centralizer (H : Set G) :=
    Subgroup.le_centralizer_iff.mp (h.hH ▸ le_rfl)
  have hA₀CK : A₀ ≤ Subgroup.centralizer (K : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hmem : a ∈ Subgroup.centralizer (H : Set G) := hA₀CH ha
    rw [Subgroup.mem_centralizer_iff] at hmem
    exact hmem k (hKH hk)
  have hA₀NK : A₀ ≤ normalizer (K : Set G) :=
    hA₀CK.trans (Subgroup.centralizer_le_normalizer (K : Set G))
  have heA₀ : e ∉ A₀ := fun hea => heNK (hA₀NK hea)
  have hKeH : K.map (MulAut.conj e).toMonoidHom ≤ H := by
    rintro x ⟨k, hk, rfl⟩
    exact H.mul_mem (H.mul_mem heH (hKH hk)) (H.inv_mem heH)
  have hKe2H : K.map (MulAut.conj (e ^ 2)).toMonoidHom ≤ H := by
    rintro x ⟨k, hk, rfl⟩
    exact H.mul_mem (H.mul_mem he2H (hKH hk)) (H.inv_mem he2H)
  have hKecomp : CFSG.IsComponent
      ((K.map (MulAut.conj e).toMonoidHom).subgroupOf H) := by
    rw [CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18.subgroupOf_map_conj_of_le hKH heH]
    exact CFSG.LocalCores.isComponent_map_mulEquiv
      (MulAut.conj (⟨e, heH⟩ : ↥H)) hKcomp
  have hKe2comp : CFSG.IsComponent
      ((K.map (MulAut.conj (e ^ 2)).toMonoidHom).subgroupOf H) := by
    rw [CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18.subgroupOf_map_conj_of_le hKH he2H]
    exact CFSG.LocalCores.isComponent_map_mulEquiv
      (MulAut.conj (⟨e ^ 2, he2H⟩ : ↥H)) hKcomp
  have hKe_ne : K.map (MulAut.conj e).toMonoidHom ≠ K := fun hmap =>
    heNK (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmap)
  have he2NK : e ^ 2 ∉ normalizer (K : Set G) := by
    intro hmem
    apply heNK
    have h4 : (e ^ 2) ^ 2 = e := by
      have h4' : e ^ 4 = e := by
        rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_succ, he3, one_mul]
      calc (e ^ 2) ^ 2 = e ^ (2 * 2) := (pow_mul e 2 2).symm
        _ = e ^ 4 := by norm_num
        _ = e := h4'
    simpa [h4] using (normalizer (K : Set G)).pow_mem hmem 2
  have hKe2_ne : K.map (MulAut.conj (e ^ 2)).toMonoidHom ≠ K := fun hmap =>
    he2NK (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmap)
  have hK1 : ⁅K, K.map (MulAut.conj e).toMonoidHom⁆ = ⊥ := by
    have hcommH : ⁅K.subgroupOf H,
        (K.map (MulAut.conj e).toMonoidHom).subgroupOf H⁆ = ⊥ := by
      rcases CFSG.LocalCores.distinct_components_commute hKcomp hKecomp with h | h
      · exfalso
        apply hKe_ne
        have := (congrArg (Subgroup.map H.subtype) h).symm
        rwa [Subgroup.map_subgroupOf_eq_of_le hKH,
          Subgroup.map_subgroupOf_eq_of_le hKeH] at this
      · exact h
    have := congrArg (Subgroup.map H.subtype) hcommH
    rwa [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hKH,
      Subgroup.map_subgroupOf_eq_of_le hKeH, Subgroup.map_bot] at this
  have hK2 : ⁅K, K.map (MulAut.conj (e ^ 2)).toMonoidHom⁆ = ⊥ := by
    have hcommH : ⁅K.subgroupOf H,
        (K.map (MulAut.conj (e ^ 2)).toMonoidHom).subgroupOf H⁆ = ⊥ := by
      rcases CFSG.LocalCores.distinct_components_commute hKcomp hKe2comp with h | h
      · exfalso
        apply hKe2_ne
        have := (congrArg (Subgroup.map H.subtype) h).symm
        rwa [Subgroup.map_subgroupOf_eq_of_le hKH,
          Subgroup.map_subgroupOf_eq_of_le hKe2H] at this
      · exact h
    have := congrArg (Subgroup.map H.subtype) hcommH
    rwa [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hKH,
      Subgroup.map_subgroupOf_eq_of_le hKe2H, Subgroup.map_bot] at this
  have he1 : e ≠ 1 := by
    intro heq
    exact heNK (heq ▸ (normalizer (K : Set G)).one_mem)
  have hecard : Nat.card (Subgroup.zpowers e) = 3 := by
    have hdvd : orderOf e ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr he3
    have hord : orderOf e = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
      · exact absurd (orderOf_eq_one_iff.mp h1) he1
      · exact h3
    rw [Nat.card_zpowers, hord]
  have hinf : A₀ ⊓ Subgroup.zpowers e = ⊥ := by
    by_contra hne
    have hcarddvd : Nat.card ↥(A₀ ⊓ Subgroup.zpowers e) ∣ 3 := by
      simpa [h.ctx22.hcard] using
        Subgroup.card_dvd_of_le (inf_le_left : A₀ ⊓ Subgroup.zpowers e ≤ A₀)
    have hcardne : Nat.card ↥(A₀ ⊓ Subgroup.zpowers e) ≠ 1 := fun h1 =>
      hne (Subgroup.card_eq_one.mp h1)
    have hcardinf : Nat.card ↥(A₀ ⊓ Subgroup.zpowers e) = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hcarddvd with h1 | h3
      · exact absurd h1 hcardne
      · exact h3
    have hinf_zpow : A₀ ⊓ Subgroup.zpowers e = Subgroup.zpowers e :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hcardinf, hecard])
    have hzpow_le : Subgroup.zpowers e ≤ A₀ := by
      rw [← hinf_zpow]
      exact inf_le_left
    exact heA₀ (hzpow_le (Subgroup.mem_zpowers e))
  have hcomm : ∀ x ∈ A₀, ∀ y ∈ Subgroup.zpowers e, x * y = y * x := by
    intro x hx y hy
    have hxE : x ∈ E := hA₀E hx
    have hyE : y ∈ E := Subgroup.zpowers_le.mpr heE hy
    have h := hEel.1.is_comm.comm (⟨x, hxE⟩ : ↥E) (⟨y, hyE⟩ : ↥E)
    simpa using congrArg Subtype.val h
  have hcardsup : Nat.card ↥(A₀ ⊔ Subgroup.zpowers e) = 9 := by
    have hprod := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A₀
      (Subgroup.zpowers e) hcomm).1
    rw [hinf, Subgroup.card_bot, mul_one, h.ctx22.hcard, hecard] at hprod
    exact hprod
  have hsupE : A₀ ⊔ Subgroup.zpowers e ≤ E := by
    refine sup_le hA₀E (Subgroup.zpowers_le.mpr heE)
  have hEeq : E = A₀ ⊔ Subgroup.zpowers e :=
    (Subgroup.eq_of_le_of_card_ge hsupE (by rw [hcardsup, hEcard])).symm
  have hnuM : ∀ c ∈ K,
      c * (e * c * e⁻¹) * (e ^ 2 * c * e⁻¹ ^ 2) ∈ D.M := by
    intro c hc
    have hνe : Commute (c * (e * c * e⁻¹) * (e ^ 2 * c * e⁻¹ ^ 2)) e := by
      have hmem :=
        CFSG.GroupTheory.triple_product_mem_centralizer he3 hK1 hK2 hc
      rw [Subgroup.mem_centralizer_iff] at hmem
      exact (hmem e (Set.mem_singleton e)).symm
    have hA₀Cν : A₀ ≤ Subgroup.centralizer
        ({c * (e * c * e⁻¹) * (e ^ 2 * c * e⁻¹ ^ 2)} : Set G) := by
      intro a ha
      have hac : Commute a c := by
        have hmem : c ∈ Subgroup.centralizer (A₀ : Set G) := h.hH ▸ (hKH hc)
        exact Subgroup.mem_centralizer_iff.mp hmem a ha
      have hae : Commute a e := by
        have hmem : e ∈ Subgroup.centralizer (A₀ : Set G) := h.hH ▸ heH
        exact Subgroup.mem_centralizer_iff.mp hmem a ha
      have hc1 : Commute a (e * c * e⁻¹) :=
        (hae.mul_right hac).mul_right hae.inv_right
      have hc2 : Commute a (e ^ 2 * c * e⁻¹ ^ 2) :=
        ((hae.pow_right 2).mul_right hac).mul_right (hae.inv_right.pow_right 2)
      have hνa : Commute a (c * (e * c * e⁻¹) * (e ^ 2 * c * e⁻¹ ^ 2)) :=
        (hac.mul_right hc1).mul_right hc2
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      exact hνa.symm.eq
    have heCν : Subgroup.zpowers e ≤ Subgroup.centralizer
        ({c * (e * c * e⁻¹) * (e ^ 2 * c * e⁻¹ ^ 2)} : Set G) :=
      Subgroup.zpowers_le.mpr (by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst y
        exact hνe.eq)
    have hECν : E ≤ Subgroup.centralizer
        ({c * (e * c * e⁻¹) * (e ^ 2 * c * e⁻¹ ^ 2)} : Set G) := by
      rw [hEeq]
      exact sup_le hA₀Cν heCν
    have hνC : c * (e * c * e⁻¹) * (e ^ 2 * c * e⁻¹ ^ 2) ∈
        Subgroup.centralizer (E : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hx' : x ∈ Subgroup.centralizer
          ({c * (e * c * e⁻¹) * (e ^ 2 * c * e⁻¹ ^ 2)} : Set G) :=
        hECν (hEeq ▸ hx)
      rw [Subgroup.mem_centralizer_iff] at hx'
      exact (hx' _ (Set.mem_singleton _)).symm
    exact hNEM ((Subgroup.centralizer_le_normalizer (E : Set G)) hνC)
  have hconjM : ∀ c ∈ K, ∀ s ∈ K, s ∈ D.M → c * s * c⁻¹ ∈ D.M := by
    intro c hc s hsK hsM
    have hcent1 : K ≤ Subgroup.centralizer
        ((K.map (MulAut.conj e).toMonoidHom) : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hK1
    have hcent2 : K ≤ Subgroup.centralizer
        ((K.map (MulAut.conj (e ^ 2)).toMonoidHom) : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hK2
    have hc1mem : e * c * e⁻¹ ∈ K.map (MulAut.conj e).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨c, hc, by simp [MulAut.conj_apply]⟩
    have hc2mem : e ^ 2 * c * e⁻¹ ^ 2 ∈
        K.map (MulAut.conj (e ^ 2)).toMonoidHom := by
      refine Subgroup.mem_map.mpr ⟨c, hc, ?_⟩
      change (MulAut.conj (e ^ 2)) c = e ^ 2 * c * e⁻¹ ^ 2
      rw [MulAut.conj_apply, inv_pow]
    have hcs1 : (e * c * e⁻¹) * s = s * (e * c * e⁻¹) :=
      Subgroup.mem_centralizer_iff.mp (hcent1 hsK) _ hc1mem
    have hcs2 : (e ^ 2 * c * e⁻¹ ^ 2) * s = s * (e ^ 2 * c * e⁻¹ ^ 2) :=
      Subgroup.mem_centralizer_iff.mp (hcent2 hsK) _ hc2mem
    have hc1conj : (e * c * e⁻¹) * s * (e * c * e⁻¹)⁻¹ = s := by
      rw [hcs1]
      group
    have hc2conj : (e ^ 2 * c * e⁻¹ ^ 2) * s * (e ^ 2 * c * e⁻¹ ^ 2)⁻¹ = s := by
      rw [hcs2]
      group
    have hνconj : (c * (e * c * e⁻¹) * (e ^ 2 * c * e⁻¹ ^ 2)) * s *
        (c * (e * c * e⁻¹) * (e ^ 2 * c * e⁻¹ ^ 2))⁻¹ = c * s * c⁻¹ := by
      calc (c * (e * c * e⁻¹) * (e ^ 2 * c * e⁻¹ ^ 2)) * s *
            (c * (e * c * e⁻¹) * (e ^ 2 * c * e⁻¹ ^ 2))⁻¹
          = c * (e * c * e⁻¹) *
              ((e ^ 2 * c * e⁻¹ ^ 2) * s * (e ^ 2 * c * e⁻¹ ^ 2)⁻¹) *
              (e * c * e⁻¹)⁻¹ * c⁻¹ := by group
        _ = c * (e * c * e⁻¹) * s * (e * c * e⁻¹)⁻¹ * c⁻¹ := by rw [hc2conj]
        _ = c * ((e * c * e⁻¹) * s * (e * c * e⁻¹)⁻¹) * c⁻¹ := by group
        _ = c * s * c⁻¹ := by rw [hc1conj]
    rw [← hνconj]
    exact D.M.mul_mem (D.M.mul_mem (hnuM c hc) hsM) (D.M.inv_mem (hnuM c hc))
  have hnorm : ((K ⊓ D.M).subgroupOf K).Normal := by
    refine ⟨fun x hx c => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨hxK, hxM⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨(c * x * c⁻¹).2, ?_⟩
    have hcx := hconjM (c : G) c.2 (x : G) hxK hxM
    simpa using hcx
  have hV0ne : V₀ ≠ ⊥ := ne_bot_of_one_lt_mSub h.ctx22.ctx.hyp.big
  have hV0in : InCalV D.M V₀ := (inCalV0_of_hyp125 h.ctx22.ctx.hyp.hyp125 hV0ne).1
  have hV0M : normalizer (V₀ : Set G) = D.M := normalizer_eq_of_inCalV D hV0in
  have hV0el : IsElemAbelian 2 V₀ := hV0in.2.2.2
  have hTI : CFSG.CGT.Timmesfeld75.IsTI V₀ := isTI_of_hyp19 h.ctx22.ctx.hyp
  have hV0NK : V₀ ≤ normalizer (K : Set G) := nineteen_twentyfour_two D h K hKH hKcomp
  obtain ⟨v, hv1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hV0ne
  have hvv : (v : G) * v = 1 := by
    have := hV0el.2 (v : G) v.2
    rwa [pow_two] at this
  have hKq : CFSG.IsQuasisimple ↥K :=
    (CFSG.IsQuasisimple.congr (Subgroup.subgroupOfEquivOfLe hKH)).mp hKcomp.1
  have hKq' : CFSG.Open.IsQuasisimple ↥K :=
    CFSG.Quasithin.A3.isQuasisimple_iff_open.mp hKq
  obtain ⟨k, hk, hkZ, hvk⟩ :=
    CFSG.GroupTheory.exists_noncentral_commute_of_odd_center hKq hZodd hvv (hV0NK v.2)
  have hv1' : (v : G) ≠ 1 := fun h1 => hv1 (Subtype.ext h1)
  have hkM : k ∈ D.M := by
    have hzle : Subgroup.zpowers (v : G) ≤ V₀ := Subgroup.zpowers_le.mpr v.2
    have hzne : Subgroup.zpowers (v : G) ≠ ⊥ := by
      intro hbot
      apply hv1'
      have : (v : G) ∈ Subgroup.zpowers (v : G) := Subgroup.mem_zpowers _
      rw [hbot] at this
      exact Subgroup.mem_bot.mp this
    have hkN : k ∈ normalizer ((Subgroup.zpowers (v : G) : Subgroup G) : Set G) := by
      have hkC : k ∈ Subgroup.centralizer ((Subgroup.zpowers (v : G) : Subgroup G) : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        exact ((Commute.zpow_left (show Commute (v : G) k from hvk) n)).eq
      exact Subgroup.centralizer_le_normalizer _ hkC
    rw [← hV0M]
    exact CFSG.CGT.T75G.normalizer_le_of_isTI hTI hzle hzne hkN
  exact not_le_M_of_actsFaithfullyOn D h hKH hKcomp hfaith
    (CFSG.GroupTheory.le_of_normal_inf_of_noncentral_mem hKq' hnorm hk hkZ hkM)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
