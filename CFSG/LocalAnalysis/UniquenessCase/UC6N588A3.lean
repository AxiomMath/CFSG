module

public import CFSG.LocalAnalysis.UniquenessCase.UC6N588A2
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Core
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.Adapters.WholeGroupLayer
public import CFSG.GroupTheory.BurnsideNormalComplement

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.N588A

open Subgroup CFSG.ABGLocalTools
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)

theorem normal_of_conjugate_eq {G : Type} [Group G] {H : Subgroup G}
    (hH : ∀ g : G, CFSG.conjugate H g = H) : H.Normal :=
  ⟨fun x hx g => mem_conjugate_iff.mp ((hH g).symm ▸ hx)⟩

section Subnormal

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem map_pPrimeCore_le_of_normal [Fact p.Prime] {H K : Subgroup G} (hle : H ≤ K)
    (hN : (H.subgroupOf K).Normal) :
    (CFSG.pPrimeCore p H).map H.subtype ≤ (CFSG.pPrimeCore p K).map K.subtype := by
  set H' : Subgroup K := H.subgroupOf K with hH'
  have : H'.Normal := hN
  let e : H' ≃* H := Subgroup.subgroupOfEquivOfLe hle
  have hA : ((CFSG.pPrimeCore p H').map H'.subtype).Normal := inferInstance
  have hAcop : Nat.Coprime p (Nat.card ((CFSG.pPrimeCore p H').map H'.subtype)) := by
    rw [Subgroup.card_map_of_injective H'.subtype_injective]
    exact CFSG.pPrimeCore_coprime_card
  have hAle : (CFSG.pPrimeCore p H').map H'.subtype ≤ CFSG.pPrimeCore p K :=
    le_sSup ⟨hA, hAcop⟩
  have hid : (CFSG.pPrimeCore p H).map H.subtype =
      ((CFSG.pPrimeCore p H').map H'.subtype).map K.subtype := by
    rw [Subgroup.map_map, ← CFSG.pPrimeCore_map_iso p e, Subgroup.map_map]
    rfl
  rw [hid]
  exact Subgroup.map_mono hAle

theorem map_pPrimeCore_le_of_isSubnormal [Fact p.Prime] {H : Subgroup G}
    (hH : H.IsSubnormal) : (CFSG.pPrimeCore p H).map H.subtype ≤ CFSG.pPrimeCore p G := by
  induction hH with
  | top => exact (CFSG.pPrimeCore_map_iso p (Subgroup.topEquiv (G := G))).le
  | step H K hle hK hN ih => exact (map_pPrimeCore_le_of_normal hle hN).trans ih

theorem le_pPrimeCore_of_isSubnormal [Fact p.Prime] {A : Subgroup G} (hA : A.IsSubnormal)
    (hcop : Nat.Coprime p (Nat.card A)) : A ≤ CFSG.pPrimeCore p G := by
  refine le_trans ?_ (map_pPrimeCore_le_of_isSubnormal hA)
  have htop : (⊤ : Subgroup A) ≤ CFSG.pPrimeCore p A := by
    refine le_sSup ⟨inferInstance, ?_⟩
    simpa using hcop
  intro a ha
  exact ⟨⟨a, ha⟩, htop (Subgroup.mem_top _), rfl⟩

theorem dvd_card_of_isSubnormal (hp : p.Prime) (hcore : CFSG.pPrimeCore p G = ⊥)
    {H : Subgroup G} (hH : H.IsSubnormal) (hne : H ≠ ⊥) : p ∣ Nat.card H := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hdvd
  have hle := le_pPrimeCore_of_isSubnormal hH ((Nat.Prime.coprime_iff_not_dvd hp).mpr hdvd)
  rw [hcore, le_bot_iff] at hle
  exact hne hle

theorem isSylowOf_inf_of_isSubnormal [Fact p.Prime] {S H : Subgroup G} (hS : IsSylowOf p S ⊤)
    (hH : H.IsSubnormal) : IsSylowOf p (S ⊓ H) H := by
  induction hH with
  | top => rwa [inf_top_eq]
  | step H K hle hK hN ih =>
    have hKH : K ≤ Subgroup.normalizer (H : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mp hN
    have h := ih.inf_of_le_normalizer hle hKH
    rwa [inf_assoc, inf_eq_right.mpr hle] at h

end Subnormal

theorem not_dvd_card_of_normalizer_le_centralizer {J : Type} [Group J] [Finite J] {p : ℕ}
    [Fact p.Prime] (hperf : Group.IsPerfect J) (P : Sylow p J)
    (hNC : Subgroup.normalizer (P : Set J) ≤ Subgroup.centralizer (P : Set J)) :
    ¬ p ∣ Nat.card J := by
  obtain ⟨K, _, hKp, -, -, -, -, -, -, -, hab⟩ := CFSG.GroupTheory.burnside_normal_complement P hNC
  have hcomm : commutator J ≤ K := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [← QuotientGroup.eq_one_iff, commutatorElement_def]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [hab (a : J ⧸ K) b]
    group
  rw [hperf.commutator_eq_top, top_le_iff] at hcomm
  rw [hcomm, Subgroup.card_top] at hKp
  exact hKp

theorem not_dvd_card_of_sylow_le_center {J : Type} [Group J] [Finite J] {p : ℕ} [Fact p.Prime]
    (hperf : Group.IsPerfect J) (P : Sylow p J) (hP : (P : Subgroup J) ≤ center J) :
    ¬ p ∣ Nat.card J := by
  refine not_dvd_card_of_normalizer_le_centralizer hperf P fun g _ => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact (Subgroup.mem_center_iff.mp (hP hx) g).symm

namespace Hyp

variable {G : Type} [Group G] [Finite G] {p : ℕ} {S Z : Subgroup G}

theorem normal_of_le_normal_isPGroup (h : Hyp G p S Z) {P : Subgroup G} [P.Normal]
    (hP : IsPGroup p P) (hZP : Z ≤ P) : Z.Normal := by
  haveI := h.fact
  obtain ⟨Q, hQS⟩ := exists_sylow_of_isSylowOf_top h.sylow
  have hPS : P ≤ S := hQS ▸ hP.le_sylow_of_normal Q
  refine normal_of_conjugate_eq fun g => h.wc g fun x hx => hPS ?_
  have hx' := hZP (mem_conjugate_iff.mp hx)
  have e : x = g⁻¹ * (g * x * g⁻¹) * g := by group
  rw [e]
  have := (inferInstance : P.Normal).conj_mem _ hx' g⁻¹
  simpa using this

theorem dvd_card_of_isComponent (h : Hyp G p S Z) (hcore : CFSG.pPrimeCore p G = ⊥)
    {J : Subgroup G} (hJ : CFSG.IsComponent J) : p ∣ Nat.card J := by
  have : Nontrivial J := CFSG.LocalCores.isQuasisimple_nontrivial hJ.1
  exact dvd_card_of_isSubnormal h.prime hcore hJ.2 ((Subgroup.nontrivial_iff_ne_bot J).mp this)

theorem exists_component (h : Hyp G p S Z) (hcore : CFSG.pPrimeCore p G = ⊥) (hZ : ¬ Z.Normal) :
    ∃ J : Subgroup G, CFSG.IsComponent J ∧ ¬ Z ≤ Subgroup.centralizer (J : Set G) := by
  haveI := h.fact
  by_contra hall
  push Not at hall
  have hF : CFSG.fittingSubgroup G = CFSG.pCore p G := CFSG.Fitting_eq_pcore G p hcore
  obtain ⟨Q, hQS⟩ := exists_sylow_of_isSylowOf_top h.sylow
  haveI : (CFSG.pCore p G).Normal := CFSG.pCore_normal
  have hPS : CFSG.pCore p G ≤ S := hQS ▸ CFSG.pCore_isPGroup.le_sylow_of_normal Q
  have hZF : Z ≤ Subgroup.centralizer (CFSG.fittingSubgroup G : Set G) := by
    rw [Subgroup.le_centralizer_iff, hF]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact h.comm hz (hPS hx)
  have hZE : Z ≤ Subgroup.centralizer (CFSG.layer G : Set G) := by
    rw [Subgroup.le_centralizer_iff, CFSG.layer.eq_sSup]
    exact sSup_le fun J hJ => (Subgroup.le_centralizer_iff).mp (hall J hJ)
  have hZFs : Z ≤ Subgroup.centralizer (CFSG.generalizedFitting G : Set G) := by
    rw [Subgroup.le_centralizer_iff, CFSG.generalizedFitting.eq_sup]
    exact sup_le ((Subgroup.le_centralizer_iff).mp hZF) ((Subgroup.le_centralizer_iff).mp hZE)
  have hZP : Z ≤ CFSG.pCore p G :=
    hF ▸ hZFs.trans (CFSG.Adapters.centralizer_generalizedFitting_le_fittingSubgroup G)
  exact hZ (h.normal_of_le_normal_isPGroup CFSG.pCore_isPGroup hZP)

theorem le_normalizer_of_isComponent (h : Hyp G p S Z) (hcore : CFSG.pPrimeCore p G = ⊥)
    {J : Subgroup G} (hJ : CFSG.IsComponent J) : Z ≤ Subgroup.normalizer (J : Set G) := by
  haveI := h.fact
  intro z hz
  have hmap : J.map (MulAut.conj z).toMonoidHom = J := by
    by_contra hne
    have hJ' : CFSG.IsComponent (J.map (MulAut.conj z).toMonoidHom) :=
      CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj z) hJ
    have hcomm : ⁅J, J.map (MulAut.conj z).toMonoidHom⁆ = ⊥ :=
      (CFSG.LocalCores.distinct_components_commute hJ hJ').resolve_left (Ne.symm hne)
    have hTJ' : S ⊓ J ≤ J.map (MulAut.conj z).toMonoidHom := by
      intro x hx
      refine ⟨x, hx.2, ?_⟩
      change z * x * z⁻¹ = x
      rw [h.comm hz hx.1, mul_inv_cancel_right]
    obtain ⟨P, hP⟩ := isSylowOf_inf_of_isSubnormal h.sylow hJ.2
    have hPc : (P : Subgroup J) ≤ center J := by
      intro x hx
      have hxT : (x : G) ∈ S ⊓ J := hP ▸ ⟨x, hx, rfl⟩
      have hxC : (x : G) ∈ Subgroup.centralizer (J : Set G) :=
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
          ((Subgroup.commutator_comm _ _).trans hcomm)) (hTJ' hxT)
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC y y.2)
    exact not_dvd_card_of_sylow_le_center hJ.1.1 P hPc (h.dvd_card_of_isComponent hcore hJ)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← hmap]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← hmap] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have hxy : y = x := by
      have e : z * y * z⁻¹ = z * x * z⁻¹ := hyx
      simpa using e
    exact hxy ▸ hy

end Hyp

end CFSG.LocalAnalysis.UniquenessCase.UCK.N588A
