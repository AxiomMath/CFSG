module


import CFSG.RankThree.PartTwo.Sec6.Item65Tools
import CFSG.RankThree.PartTwo.Sec18.Item189KType
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.RankThree.PartTwo.Sec21.Item2119End3Proof2125Unique
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.RankThree.PartTwo.Sec4.Notation
import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {M : Subgroup G}

@[expose] noncomputable def imM (M K : Subgroup G) : Subgroup (↥M ⧸ aschbacherSolvableCore 3 ↥M) :=
  (K.subgroupOf M).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥M))

theorem mem_imM_iff {K : Subgroup G} {x : ↥M ⧸ aschbacherSolvableCore 3 ↥M} :
    x ∈ imM M K ↔ ∃ (k : G) (hkM : k ∈ M), k ∈ K ∧
      (QuotientGroup.mk (⟨k, hkM⟩ : ↥M) : ↥M ⧸ aschbacherSolvableCore 3 ↥M) = x := by
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact ⟨y, y.2, hy, rfl⟩
  · rintro ⟨k, hkM, hk, rfl⟩
    exact Subgroup.mem_map.mpr ⟨⟨k, hkM⟩, hk, rfl⟩

theorem mk_mem_imM {K : Subgroup G} {k : G} (hkM : k ∈ M) (hk : k ∈ K) :
    (QuotientGroup.mk (⟨k, hkM⟩ : ↥M) : ↥M ⧸ aschbacherSolvableCore 3 ↥M) ∈ imM M K :=
  mem_imM_iff.mpr ⟨k, hkM, hk, rfl⟩

private theorem quot_mem_theta_iff (L : Subgroup G) (x : ↥L) :
    x ∈ aschbacherSolvableCore 3 ↥L ↔ (x : G) ∈ inSubgroup (aschbacherSolvableCore 3) L := by
  rw [inSubgroup]
  exact (Subgroup.mem_map_iff_mem L.subtype_injective).symm

private theorem quot_mk_commute_iff (d k : ↥M) :
    (QuotientGroup.mk d : ↥M ⧸ aschbacherSolvableCore 3 ↥M) * QuotientGroup.mk k =
      QuotientGroup.mk k * QuotientGroup.mk d ↔ ⁅d, k⁆ ∈ aschbacherSolvableCore 3 ↥M := by
  have key : ⁅(QuotientGroup.mk d : ↥M ⧸ aschbacherSolvableCore 3 ↥M), QuotientGroup.mk k⁆ =
      QuotientGroup.mk ⁅d, k⁆ :=
    (map_commutatorElement (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥M)) d k).symm
  change Commute (QuotientGroup.mk d : ↥M ⧸ aschbacherSolvableCore 3 ↥M) (QuotientGroup.mk k) ↔ _
  rw [← commutatorElement_eq_one_iff_commute, key, QuotientGroup.eq_one_iff]

private theorem quot_comm_mem_iff (d k : ↥M) :
    ⁅d, k⁆ ∈ aschbacherSolvableCore 3 ↥M ↔
      k⁻¹ * (d * k * d⁻¹) ∈ aschbacherSolvableCore 3 ↥M := by
  have hn := aschbacherSolvableCore_normal 3 ↥M
  constructor
  · intro h
    have e : k⁻¹ * (d * k * d⁻¹) = k⁻¹ * ⁅d, k⁆ * k⁻¹⁻¹ := by
      rw [commutatorElement_def]; group
    rw [e]
    exact hn.conj_mem _ h k⁻¹
  · intro h
    have e : ⁅d, k⁆ = k * (k⁻¹ * (d * k * d⁻¹)) * k⁻¹ := by
      rw [commutatorElement_def]; group
    rw [e]
    exact hn.conj_mem _ h k

private theorem quot_commute_imM_iff (d k : ↥M) :
    (QuotientGroup.mk d : ↥M ⧸ aschbacherSolvableCore 3 ↥M) * QuotientGroup.mk k =
      QuotientGroup.mk k * QuotientGroup.mk d ↔
      (k : G)⁻¹ * ((d : G) * k * (d : G)⁻¹) ∈ inSubgroup (aschbacherSolvableCore 3) M := by
  rw [quot_mk_commute_iff, quot_comm_mem_iff, quot_mem_theta_iff]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]

private theorem quot_conj_mem_theta_iff {K : Subgroup G} (hK : K ∈ thetaComponentsIn M)
    {d : G} (hdN : d ∈ Subgroup.normalizer (K : Set G)) {k : G} (hk : k ∈ K) :
    k⁻¹ * (d * k * d⁻¹) ∈ inSubgroup (aschbacherSolvableCore 3) K ↔
      k⁻¹ * (d * k * d⁻¹) ∈ inSubgroup (aschbacherSolvableCore 3) M := by
  have hmem : k⁻¹ * (d * k * d⁻¹) ∈ K :=
    K.mul_mem (K.inv_mem hk) ((Subgroup.mem_normalizer_iff.mp hdN k).mp hk)
  rw [Sec6.theta_eq_inf_of_mem_thetaComponentsIn hK, Subgroup.mem_inf]
  exact ⟨fun h => h.2, fun h => ⟨hmem, h⟩⟩

private theorem quot_commute_imM_of_le {D K : Subgroup G} (hK : K ∈ thetaComponentsIn M)
    (hDM : D ≤ M) (hD : D ≤ Sec4.thetaQuotCentralizer K) :
    ∀ x ∈ imM M D, ∀ y ∈ imM M K, x * y = y * x := by
  rintro _ hx _ hy
  obtain ⟨d, hdM, hdD, rfl⟩ := mem_imM_iff.mp hx
  obtain ⟨k, hkM, hkK, rfl⟩ := mem_imM_iff.mp hy
  obtain ⟨hdN, hcomm⟩ := Sec6.mem_thetaQuotCentralizer_iff.mp (hD hdD)
  exact (quot_commute_imM_iff ⟨d, hdM⟩ ⟨k, hkM⟩).mpr
    ((quot_conj_mem_theta_iff hK hdN hkK).mp (hcomm k hkK))

private theorem quot_le_thetaQuotCentralizer_of_commute {D K : Subgroup G}
    (hK : K ∈ thetaComponentsIn M) (hDM : D ≤ M) (hDn : D ≤ Subgroup.normalizer (K : Set G))
    (hc : ∀ x ∈ imM M D, ∀ y ∈ imM M K, x * y = y * x) :
    D ≤ Sec4.thetaQuotCentralizer K := by
  intro d hd
  have hdM : d ∈ M := hDM hd
  have hKM := le_of_mem_thetaComponentsIn hK
  refine Sec6.mem_thetaQuotCentralizer_iff.mpr ⟨hDn hd, fun k hk => ?_⟩
  have hkM : k ∈ M := hKM hk
  exact (quot_conj_mem_theta_iff hK (hDn hd) hk).mpr
    ((quot_commute_imM_iff ⟨d, hdM⟩ ⟨k, hkM⟩).mp
      (hc _ (mk_mem_imM hdM hd) _ (mk_mem_imM hkM hk)))

private theorem quot_conj_mem_imM {K : Subgroup G} {e : G} (heM : e ∈ M)
    (heN : e ∈ Subgroup.normalizer (K : Set G)) {m : ↥M ⧸ aschbacherSolvableCore 3 ↥M}
    (hm : m ∈ imM M K) :
    (QuotientGroup.mk (⟨e, heM⟩ : ↥M) : ↥M ⧸ aschbacherSolvableCore 3 ↥M) * m *
      (QuotientGroup.mk (⟨e, heM⟩ : ↥M))⁻¹ ∈ imM M K := by
  obtain ⟨k, hkM, hkK, rfl⟩ := mem_imM_iff.mp hm
  have hk' : e * k * e⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp heN k).mp hkK
  have hM' : e * k * e⁻¹ ∈ M := M.mul_mem (M.mul_mem heM hkM) (M.inv_mem heM)
  have key : (QuotientGroup.mk (⟨e * k * e⁻¹, hM'⟩ : ↥M) : ↥M ⧸ aschbacherSolvableCore 3 ↥M) =
      QuotientGroup.mk ⟨e, heM⟩ * QuotientGroup.mk ⟨k, hkM⟩ * (QuotientGroup.mk ⟨e, heM⟩)⁻¹ := by
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    rfl
  rw [← key]
  exact mk_mem_imM hM' hk'

private theorem quot_range_comp_inclusion {D : Subgroup G} (hDM : D ≤ M) :
    ((QuotientGroup.mk' (aschbacherSolvableCore 3 ↥M)).comp (Subgroup.inclusion hDM)).range =
      imM M D := by
  ext x
  rw [MonoidHom.mem_range, mem_imM_iff]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨(y : G), hDM y.2, y.2, rfl⟩
  · rintro ⟨k, hkM, hkD, rfl⟩
    exact ⟨⟨k, hkD⟩, rfl⟩

private theorem quot_card_range_mul_card_ker {X Y : Type} [Group X] [Group Y] (φ : X →* Y) :
    Nat.card φ.range * Nat.card φ.ker = Nat.card X := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv] at h
  exact h.symm

private theorem quot_card_imM_mul_card_ker {D : Subgroup G} (hDM : D ≤ M) :
    Nat.card (imM M D) *
      Nat.card ((QuotientGroup.mk' (aschbacherSolvableCore 3 ↥M)).comp
        (Subgroup.inclusion hDM)).ker = Nat.card D := by
  have h := quot_card_range_mul_card_ker
    ((QuotientGroup.mk' (aschbacherSolvableCore 3 ↥M)).comp (Subgroup.inclusion hDM))
  rw [quot_range_comp_inclusion hDM] at h
  exact h

private theorem quot_ker_comp_inclusion {K : Subgroup G} (hK : K ∈ thetaComponentsIn M) :
    ((QuotientGroup.mk' (aschbacherSolvableCore 3 ↥M)).comp
      (Subgroup.inclusion (le_of_mem_thetaComponentsIn hK))).ker =
      aschbacherSolvableCore 3 ↥K := by
  ext x
  change (QuotientGroup.mk (Subgroup.inclusion (le_of_mem_thetaComponentsIn hK) x) :
    ↥M ⧸ aschbacherSolvableCore 3 ↥M) = 1 ↔ x ∈ aschbacherSolvableCore 3 ↥K
  rw [QuotientGroup.eq_one_iff, quot_mem_theta_iff M, quot_mem_theta_iff K,
    Sec6.theta_eq_inf_of_mem_thetaComponentsIn hK, Subgroup.mem_inf]
  exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩

theorem imM_mono {K K' : Subgroup G} (h : K ≤ K') : imM M K ≤ imM M K' := by
  intro x hx
  obtain ⟨k, hkM, hk, rfl⟩ := mem_imM_iff.mp hx
  exact mk_mem_imM hkM (h hk)

theorem imM_card_eq_of_isPGroup {D : Subgroup G} (hDM : D ≤ M) (hD : IsPGroup 3 D) :
    Nat.card (imM M D) = Nat.card D := by
  have hbot : ((QuotientGroup.mk' (aschbacherSolvableCore 3 ↥M)).comp
      (Subgroup.inclusion hDM)).ker = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hθ : Subgroup.inclusion hDM x ∈ aschbacherSolvableCore 3 ↥M :=
      (QuotientGroup.eq_one_iff (Subgroup.inclusion hDM x)).mp (MonoidHom.mem_ker.mp hx)
    obtain ⟨k, hk⟩ := hD x
    have hpow : (Subgroup.inclusion hDM x) ^ 3 ^ k = 1 := by
      rw [← map_pow, hk, map_one]
    have h1 : Subgroup.inclusion hDM x = 1 :=
      CFSG.RankThree.PartTwo.Sec19.Step1914TriProof.eq_one_of_mem_theta' (I := ↥M) hθ hpow
    have h2 : ((Subgroup.inclusion hDM x : ↥M) : G) = ((1 : ↥M) : G) :=
      congrArg Subtype.val h1
    exact Subtype.ext h2
  have h := quot_card_imM_mul_card_ker hDM
  rw [hbot, Subgroup.card_bot, mul_one] at h
  exact h

theorem imM_isElemAbelian {D : Subgroup G} (hDM : D ≤ M) (hD : CFSG.Open.IsElemAbelian 3 D) :
    CFSG.Open.IsElemAbelian 3 (imM M D) :=
  CFSG.SectionRank.isElemAbelian_map (CFSG.Open.IsElemAbelian.subgroupOf hD M)
    (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥M))

theorem nonempty_thetaQuot_equiv_imM {K : Subgroup G} (hK : K ∈ thetaComponentsIn M) :
    Nonempty (↥K ⧸ aschbacherSolvableCore 3 ↥K ≃* ↥(imM M K)) := by
  have h := quot_ker_comp_inclusion hK
  have h' := quot_range_comp_inclusion (le_of_mem_thetaComponentsIn hK)
  exact ⟨(QuotientGroup.quotientMulEquivOfEq h.symm).trans
    ((QuotientGroup.quotientKerEquivRange
      ((QuotientGroup.mk' (aschbacherSolvableCore 3 ↥M)).comp
        (Subgroup.inclusion (le_of_mem_thetaComponentsIn hK)))).trans
      (MulEquiv.subgroupCongr h'))⟩

theorem imM_isQuasisimple {K : Subgroup G} (hK : K ∈ thetaComponentsIn M) :
    IsQuasisimple ↥(imM M K) := by
  obtain ⟨e⟩ := nonempty_thetaQuot_equiv_imM hK
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e (quasisimple_of_mem_thetaComponentsIn hK)

theorem imM_isPerfect {K : Subgroup G} (hK : K ∈ thetaComponentsIn M) :
    Group.IsPerfect ↥(imM M K) :=
  (imM_isQuasisimple hK).1

theorem three_dvd_card_imM {K : Subgroup G} (hK : K ∈ thetaComponentsIn M)
    (h3 : 3 ∣ Nat.card K) : 3 ∣ Nat.card (imM M K) := by
  have h := quot_card_imM_mul_card_ker (le_of_mem_thetaComponentsIn hK)
  rw [quot_ker_comp_inclusion hK] at h
  have hθ : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 ↥K) := by
    have h0 := (Sec6.theta_solvable_and_not_dvd K).2
    rwa [inSubgroup, Subgroup.card_map_of_injective K.subtype_injective] at h0
  rw [← h] at h3
  exact ((Nat.Prime.dvd_mul Nat.prime_three).mp h3).resolve_right hθ

theorem imM_commute_of_ne {K K' : Subgroup G} (hK : K ∈ thetaComponentsIn M)
    (hK' : K' ∈ thetaComponentsIn M) (hne : K ≠ K') :
    ∀ x ∈ imM M K, ∀ y ∈ imM M K', x * y = y * x :=
  quot_commute_imM_of_le hK' (le_of_mem_thetaComponentsIn hK)
    (Sec21.Item2119End3Proof.le_thetaQuotCentralizer_of_ne hK' hK hne.symm)

theorem le_thetaQuotCentralizer_iff_imM_commute {D K : Subgroup G} (hK : K ∈ thetaComponentsIn M)
    (hDM : D ≤ M) (hDn : D ≤ Subgroup.normalizer (K : Set G)) :
    D ≤ Sec4.thetaQuotCentralizer K ↔ ∀ x ∈ imM M D, ∀ y ∈ imM M K, x * y = y * x :=
  ⟨quot_commute_imM_of_le hK hDM, quot_le_thetaQuotCentralizer_of_commute hK hDM hDn⟩

theorem imM_commute_of_le_thetaQuotCentralizer {D K : Subgroup G} (hK : K ∈ thetaComponentsIn M)
    (hDM : D ≤ M) (hD : D ≤ Sec4.thetaQuotCentralizer K) :
    ∀ x ∈ imM M D, ∀ y ∈ imM M K, x * y = y * x :=
  quot_commute_imM_of_le hK hDM hD

theorem imM_sup {P R : Subgroup G} (hP : P ≤ M) (hR : R ≤ M) :
    imM M (P ⊔ R) = imM M P ⊔ imM M R := by
  unfold imM
  rw [Subgroup.subgroupOf_sup hP hR, Subgroup.map_sup]

theorem imM_le_imM_iff {K K' : Subgroup G} (hK : K ≤ M) (hK' : K' ≤ M) :
    imM M K' ≤ imM M K ↔ K' ≤ K ⊔ inSubgroup (aschbacherSolvableCore 3) M := by
  constructor
  · intro h k' hk'
    obtain ⟨k, hkM, hkK, hkeq⟩ := mem_imM_iff.mp (h (mk_mem_imM (hK' hk') hk'))
    have h1 := (quot_mem_theta_iff M _).mp (QuotientGroup.eq.mp hkeq)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
    have e : k' = k * (k⁻¹ * k') := by group
    rw [e]
    exact mul_mem (Subgroup.mem_sup_left hkK) (Subgroup.mem_sup_right h1)
  · intro hsub x hx
    obtain ⟨k', hk'M, hk'K', rfl⟩ := mem_imM_iff.mp hx
    have hN : K ≤ Subgroup.normalizer (inSubgroup (aschbacherSolvableCore 3) M : Set G) :=
      hK.trans (Sec6.le_normalizer_theta M)
    have hmem : k' ∈ (K : Set G) * (inSubgroup (aschbacherSolvableCore 3) M : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right K _ hN]
      exact hsub hk'K'
    obtain ⟨k, hkK, t, ht, hkt⟩ := hmem
    subst hkt
    have hkM : k ∈ M := hK hkK
    have htM : t ∈ M := Sec6.theta_le M ht
    have ht' : (⟨t, htM⟩ : ↥M) ∈ aschbacherSolvableCore 3 ↥M := (quot_mem_theta_iff M _).mpr ht
    have key : (QuotientGroup.mk (⟨k * t, hk'M⟩ : ↥M) : ↥M ⧸ aschbacherSolvableCore 3 ↥M) =
        QuotientGroup.mk ⟨k, hkM⟩ := by
      rw [QuotientGroup.eq]
      have e : (⟨k * t, hk'M⟩ : ↥M)⁻¹ * ⟨k, hkM⟩ = (⟨t, htM⟩ : ↥M)⁻¹ := by
        ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk]
        group
      rw [e]
      exact (aschbacherSolvableCore 3 ↥M).inv_mem ht'
    rw [key]
    exact mk_mem_imM hkM hkK

theorem imM_inf_eq_bot {K K' : Subgroup G} (hK : K ≤ M) (hK' : K' ≤ M)
    (h : K' ⊓ (K ⊔ inSubgroup (aschbacherSolvableCore 3) M) = ⊥) :
    imM M K' ⊓ imM M K = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx', hx⟩
  obtain ⟨k', hk'M, hk'K', rfl⟩ := mem_imM_iff.mp hx'
  obtain ⟨k, hkM, hkK, hkeq⟩ := mem_imM_iff.mp hx
  have h1 := (quot_mem_theta_iff M _).mp (QuotientGroup.eq.mp hkeq)
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
  have hmem : k' ∈ K' ⊓ (K ⊔ inSubgroup (aschbacherSolvableCore 3) M) := by
    refine ⟨hk'K', ?_⟩
    have e : k' = k * (k⁻¹ * k') := by group
    rw [e]
    exact mul_mem (Subgroup.mem_sup_left hkK) (Subgroup.mem_sup_right h1)
  rw [h, Subgroup.mem_bot] at hmem
  rw [Subgroup.mem_bot]
  have h1' : (⟨k', hk'M⟩ : ↥M) = 1 := Subtype.ext hmem
  rw [h1', QuotientGroup.mk_one]

theorem imM_le_normalizer {D K : Subgroup G} (hDM : D ≤ M) (hKM : K ≤ M)
    (hDn : D ≤ Subgroup.normalizer (K : Set G)) :
    imM M D ≤ Subgroup.normalizer (imM M K : Set (↥M ⧸ aschbacherSolvableCore 3 ↥M)) := by
  intro x hx
  obtain ⟨d, hdM, hdD, rfl⟩ := mem_imM_iff.mp hx
  exact Subgroup.mem_normalizer_fintype (fun n hn => quot_conj_mem_imM hdM (hDn hdD) hn)

theorem normal_imM {R : Subgroup G} (hRM : R ≤ M) (hRn : M ≤ Subgroup.normalizer (R : Set G)) :
    (imM M R).Normal :=
  ((Subgroup.normal_subgroupOf_iff_le_normalizer hRM).mpr hRn).map _
    (QuotientGroup.mk'_surjective _)

theorem isSolvable_imM {R : Subgroup G} (hR : Group.IsSolvable R) :
    Group.IsSolvable (imM M R) := by
  have hS : Group.IsSolvable ↥(R.subgroupOf M) := by
    let f : ↥(R.subgroupOf M) →* ↥R :=
      ((M.subtype.comp (R.subgroupOf M).subtype).codRestrict R
        (fun x => Subgroup.mem_subgroupOf.mp x.2))
    have hinj : Function.Injective f := by
      intro a b h
      have h' : ((f a : ↥R) : G) = ((f b : ↥R) : G) := congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext h')
    exact Group.isSolvable_of_isSolvable_injective (f := f) hinj
  exact Group.isSolvable_of_surjective
    (f := MonoidHom.subgroupMap (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥M))
      (R.subgroupOf M))
    (MonoidHom.subgroupMap_surjective _ _)

theorem isSolvable_oTwoP (M : Subgroup G) :
    Group.IsSolvable ((Sec4.oTwoP 3 M).map M.subtype) := by
  set N : Subgroup ↥M := CFSG.pCore 2 ↥M with hN
  have hNT : N ≤ Sec4.oTwoP 3 ↥M := by
    intro x hx
    change QuotientGroup.mk' N x ∈ CFSG.pCore 3 (↥M ⧸ N)
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff (x : ↥M)).mpr hx]
    exact one_mem _
  have h2 : IsPGroup 2 N := CFSG.pCore_isPGroup (p := 2) (G := ↥M)
  have h3 : IsPGroup 3 (CFSG.pCore 3 (↥M ⧸ N)) := CFSG.pCore_isPGroup (p := 3) (G := ↥M ⧸ N)
  haveI : Group.IsSolvable ↥N := by
    haveI := h2.isNilpotent
    infer_instance
  haveI : Group.IsSolvable ↥(CFSG.pCore 3 (↥M ⧸ N)) := by
    haveI := h3.isNilpotent
    infer_instance
  let g : ↥(Sec4.oTwoP 3 ↥M) →* ↥(CFSG.pCore 3 (↥M ⧸ N)) :=
    ((QuotientGroup.mk' N).comp (Sec4.oTwoP 3 ↥M).subtype).codRestrict _ (fun x => x.2)
  have hfg : g.ker ≤ (Subgroup.inclusion hNT).range := by
    intro x hx
    have hx' : g x = 1 := MonoidHom.mem_ker.mp hx
    have hx1 : ((x : ↥M) : ↥M ⧸ N) = 1 := congrArg Subtype.val hx'
    exact ⟨⟨(x : ↥M), (QuotientGroup.eq_one_iff _).mp hx1⟩, Subtype.ext rfl⟩
  have hT : Group.IsSolvable ↥(Sec4.oTwoP 3 ↥M) :=
    Group.isSolvable_of_ker_le_range (Subgroup.inclusion hNT) g hfg
  exact Group.isSolvable_of_isSolvable_injective
    (f := ((Sec4.oTwoP 3 ↥M).equivMapOfInjective M.subtype M.subtype_injective).symm.toMonoidHom)
    (MulEquiv.injective _)

theorem le_normalizer_oTwoP_map (M : Subgroup G) :
    M ≤ Subgroup.normalizer (((Sec4.oTwoP 3 M).map M.subtype : Subgroup G) : Set G) := by
  have hT : (Sec4.oTwoP 3 ↥M).Normal := by
    unfold Sec4.oTwoP
    haveI := CFSG.pCore_normal (p := 3) (G := ↥M ⧸ CFSG.pCore 2 ↥M)
    infer_instance
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨(⟨m, hm⟩ : ↥M) * t * (⟨m, hm⟩ : ↥M)⁻¹, hT.conj_mem t ht _, by simp⟩
  · rintro ⟨t, ht, hth⟩
    refine ⟨(⟨m, hm⟩ : ↥M)⁻¹ * t * ⟨m, hm⟩, ?_, ?_⟩
    · have := hT.conj_mem t ht (⟨m, hm⟩ : ↥M)⁻¹
      simpa using this
    · simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk] at hth ⊢
      rw [hth]
      group

end CFSG.RankThree.PartTwo.Sec18
