module

public import CFSG.RankThree.PartOne.S10.SectionTenNodesUnconditional
public import CFSG.RankThree.PartOne.S11.TwoActionWiring
import CFSG.RankThree.PartOne.S10.AmbientTheta

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

structure PlaneOn {T : Type} [Group T] (p : ℕ) (E : Subgroup (MulAut T)) (U : Subgroup T) :
    Prop where
  prime : p.Prime
  three_lt : 3 < p
  elementary : IsElementaryAbelian p E
  card : Nat.card E = p ^ 2
  two_group : IsPGroup 2 U
  normalized : ∀ e ∈ E, ∀ u ∈ U, e u ∈ U

section Action

variable {G : Type} [Group G]

@[expose] noncomputable def centerQuotientConj (L : Subgroup G) :
    Subgroup.normalizer (L : Set G) →* MulAut (L ⧸ Subgroup.center L) :=
  (mulAutQuotientHom (Subgroup.center L)).comp L.normalizerMonoidHom

@[expose] noncomputable def centerQuotientAction {A L : Subgroup G}
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) : A →* MulAut (L ⧸ Subgroup.center L) :=
  (centerQuotientConj L).comp (Subgroup.inclusion hAL)

theorem centerQuotientAction_mk {A L : Subgroup G} (hAL : A ≤ Subgroup.normalizer (L : Set G))
    (a : A) (l : L) :
    centerQuotientAction hAL a (l : L ⧸ Subgroup.center L) =
      ((L.normalizerMonoidHom ⟨a, hAL a.2⟩ l : L) : L ⧸ Subgroup.center L) :=
  rfl

theorem coe_normalizerMonoidHom_apply {L : Subgroup G} (g : Subgroup.normalizer (L : Set G))
    (l : L) : ((L.normalizerMonoidHom g l : L) : G) = (g : G) * l * (g : G)⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe L g l

theorem centerQuotientAction_eq_one_iff {A L : Subgroup G}
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) (a : A) :
    centerQuotientAction hAL a = 1 ↔
      ∀ l : L, (L.normalizerMonoidHom ⟨a, hAL a.2⟩ l) / l ∈ Subgroup.center L := by
  constructor
  · intro h l
    have h1 := congrArg (fun φ : MulAut (L ⧸ Subgroup.center L) =>
      φ (l : L ⧸ Subgroup.center L)) h
    simp only [centerQuotientAction_mk, MulAut.one_apply] at h1
    rwa [QuotientGroup.eq_iff_div_mem] at h1
  · intro h
    ext q
    induction q using QuotientGroup.induction_on with
    | H l =>
      rw [centerQuotientAction_mk, MulAut.one_apply, QuotientGroup.eq_iff_div_mem]
      exact h l

theorem commute_of_centerQuotientAction_eq_one {A L : Subgroup G}
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) [Group.IsPerfect L] (a : A)
    (ha : centerQuotientAction hAL a = 1) (l : L) : (a : G) * l = l * (a : G) := by
  have hcen := (centerQuotientAction_eq_one_iff hAL a).mp ha
  let φ : L →* L := (L.normalizerMonoidHom ⟨a, hAL a.2⟩).toMonoidHom
  have hφ : ∀ x : L, x⁻¹ * φ x ∈ Subgroup.center L := by
    intro x
    have hc : φ x / x ∈ Subgroup.center L := hcen x
    have hcx := Subgroup.mem_center_iff.mp hc x⁻¹
    have hφx : φ x = (φ x / x) * x := (div_mul_cancel (φ x) x).symm
    have : x⁻¹ * φ x = φ x / x := by
      calc x⁻¹ * φ x = x⁻¹ * ((φ x / x) * x) := by rw [← hφx]
        _ = (x⁻¹ * (φ x / x)) * x := by rw [mul_assoc]
        _ = ((φ x / x) * x⁻¹) * x := by rw [hcx]
        _ = φ x / x := by rw [mul_assoc, inv_mul_cancel, mul_one]
    rw [this]
    exact hc
  have hid := CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_id_of_central_displacement
    φ hφ
  have hc := congrArg (fun ψ : L →* L => ((ψ l : L) : G)) hid
  simp only [φ, MulEquiv.coe_toMonoidHom, MonoidHom.id_apply, coe_normalizerMonoidHom_apply]
    at hc
  calc (a : G) * l = (a : G) * l * (a : G)⁻¹ * a := by group
    _ = l * a := by rw [hc]

theorem centerQuotientAction_mem_map {A L S : Subgroup G}
    (hAL : A ≤ Subgroup.normalizer (L : Set G))
    (hAS : A ≤ Subgroup.normalizer (S : Set G)) (a : A) {u : L ⧸ Subgroup.center L}
    (hu : u ∈ (S.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center L))) :
    centerQuotientAction hAL a u ∈
      (S.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center L)) := by
  obtain ⟨s, hs, rfl⟩ := hu
  refine ⟨L.normalizerMonoidHom ⟨a, hAL a.2⟩ s, ?_, rfl⟩
  have hs' : (s : G) ∈ S := Subgroup.mem_subgroupOf.mp hs
  rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, coe_normalizerMonoidHom_apply]
  have := (Subgroup.mem_normalizer_iff.mp (hAS a.2) (s : G)).mp hs'
  simpa using this

end Action

section Plane

variable {G : Type} [Group G] [Finite G]

theorem inSubgroup_theta_le_center {p : ℕ} (hp : p.Prime) {L : Subgroup G}
    (hq : CFSG.IsQuasisimple L) :
    inSubgroup (aschbacherSolvableCore p) L ≤ (Subgroup.center L).map L.subtype := by
  have hnt : Nontrivial L := CFSG.LocalCores.isQuasisimple_nontrivial hq
  have hperf : Group.IsPerfect L := hq.1
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq
      (aschbacherSolvableCore_normal p L) with htop | hle
  · exfalso
    have hsol : Group.IsSolvable (aschbacherSolvableCore p L) :=
      (solvable_prime_complement_core_characterization (H := L) hp).1
    rw [htop] at hsol
    have hsolL : Group.IsSolvable L := Group.isSolvable_of_surjective
      (f := (Subgroup.topEquiv (G := L)).toMonoidHom) (Subgroup.topEquiv (G := L)).surjective
    exact (Group.IsSolvable.commutator_lt_top_of_nontrivial (G := L)).ne
      hperf.commutator_eq_top
  · exact Subgroup.map_mono hle

theorem moving_maximal_data_at (hS : SchreierFor InCatalog) {p : ℕ} {A : Subgroup G}
    (h : SteinbergBM.SectionTenSetup G p A) {L : Subgroup G} (hL : L ∈ sectionTenZeroStar p A)
    {c : G} (hcA : c ∈ A) (hc1 : c ≠ 1) (hLc : L ∈ thetaComponentsAt p c) :
    CFSG.IsQuasisimple L ∧ A ≤ Subgroup.normalizer (L : Set G) ∧
      thetaQuotientCentralizer p A L = Subgroup.zpowers c := by
  have hqs := section_ten_maximal_moving_theta_components_quasisimple hS twoActionInputs_of_S9
    G p A h L hL
  obtain ⟨hAN, hcyc⟩ := section_ten_maximal_component_quotient_actor_kernel_cyclic hS G p A h L
    hL.2
  refine ⟨hqs, hAN, ?_⟩
  set C := thetaQuotientCentralizer p A L with hC
  have hLc' := (mem_thetaComponentsAt_iff.mp hLc).1
  have hcC : c ∈ C := by
    rw [hC, mem_thetaQuotientCentralizer_iff]
    refine ⟨hcA, hAN hcA, fun k hk => ?_⟩
    have hck : c * k = k * c :=
      (Subgroup.mem_centralizer_singleton_iff.mp (hLc' hk) : k * c = c * k).symm
    have : c * k * c⁻¹ * k⁻¹ = 1 := by rw [hck]; group
    rw [this]
    exact Subgroup.one_mem _
  have hCA : C ≤ A := inf_le_left
  have hAe : IsElementaryAbelian p A := h.2.2.2.2.2.2.1
  have hp := sectionTenSetup_prime h
  have hpe : ∀ x ∈ C, x ^ p = 1 := fun x hx =>
    elemPow_eq_one_of_isElementaryAbelian (A := A) x (hCA hx)
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hgp : (g : G) ^ p = 1 := hpe g g.2
  have hord : orderOf (g : G) ∣ p := orderOf_dvd_of_pow_eq_one hgp
  rcases (Nat.dvd_prime hp).mp hord with h1 | h1
  · exfalso
    have hg1 : (g : G) = 1 := orderOf_eq_one_iff.mp h1
    have hgC : ∀ x : C, x = 1 := fun x => by
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hg x)
      have : g = 1 := Subtype.ext hg1
      rw [this, one_zpow] at hn
      exact hn.symm
    exact hc1 (congrArg Subtype.val (hgC ⟨c, hcC⟩))
  ·
    have hCcard : Nat.card C = p := by
      rw [← orderOf_eq_card_of_forall_mem_zpowers hg, ← h1]
      exact (Subgroup.orderOf_coe g).symm
    have hcord : orderOf c = p := by
      have hcp : c ^ p = 1 := hpe c hcC
      rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hcp) with h2 | h2
      · exact absurd (orderOf_eq_one_iff.mp h2) hc1
      · exact h2
    have hz : Subgroup.zpowers c ≤ C := (Subgroup.zpowers_le).mpr hcC
    have hzcard : Nat.card (Subgroup.zpowers c) = p := by rw [Nat.card_zpowers, hcord]
    exact (Subgroup.eq_of_le_of_card_ge hz (by rw [hCcard, hzcard])).symm

theorem moving_maximal_quasisimple_data (hS : SchreierFor InCatalog) {p : ℕ} {A : Subgroup G}
    (h : SteinbergBM.SectionTenSetup G p A) {L : Subgroup G} (hL : L ∈ sectionTenZeroStar p A) :
    CFSG.IsQuasisimple L ∧ A ≤ Subgroup.normalizer (L : Set G) ∧
      ∃ c ∈ A, c ≠ 1 ∧ L ∈ thetaComponentsAt p c ∧
        Nat.card (thetaQuotientCentralizer p A L) = p := by
  obtain ⟨c, hcA, hc1, hLc⟩ := mem_thetaComponentFamily_iff.mp
    ((sectionTenZeroStar_subset p A).2.2.1 hL.2)
  obtain ⟨hq, hAN, hker⟩ := moving_maximal_data_at hS h hL hcA hc1 hLc
  refine ⟨hq, hAN, c, hcA, hc1, hLc, ?_⟩
  have hp := sectionTenSetup_prime h
  have hAe : IsElementaryAbelian p A := h.2.2.2.2.2.2.1
  have hcord : orderOf c = p := by
    have hcp : c ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian (A := A) c hcA
    rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hcp) with h2 | h2
    · exact absurd (orderOf_eq_one_iff.mp h2) hc1
    · exact h2
  rw [hker, Nat.card_zpowers, hcord]

theorem isElementaryAbelian_range {p : ℕ} {A S : Type*} [Group A] [Group S]
    (hA : IsElementaryAbelian p A) (f : A →* S) : IsElementaryAbelian p f.range := by
  have : IsMulCommutative A := hA.toIsMulCommutative
  refine { toIsMulCommutative := ⟨⟨?_⟩⟩, exponent_dvd_p := ?_ }
  · rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
    exact Subtype.ext (by
      simp only [Subgroup.coe_mul, ← map_mul, (IsMulCommutative.is_comm (M := A)).comm a b])
  · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
    rintro ⟨_, a, rfl⟩
    refine Subtype.ext ?_
    have h1 := (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hA.exponent_dvd_p) a
    simp only [OneMemClass.coe_one, SubmonoidClass.coe_pow, ← map_pow, h1, map_one]

theorem moving_maximal_plane_witness (hS : SchreierFor InCatalog) {p : ℕ} {A : Subgroup G}
    (h : SteinbergBM.SectionTenSetup G p A) {L : Subgroup G} (hL : L ∈ sectionTenZeroStar p A) :
    ∃ hAL : A ≤ Subgroup.normalizer (L : Set G),
      ∃ U : Subgroup (L ⧸ Subgroup.center L),
        PlaneOn p (centerQuotientAction hAL).range U ∧
          ∃ e ∈ (centerQuotientAction hAL).range, ∃ u ∈ U, e u ≠ u := by
  obtain ⟨hq, hAL, c, hcA, hc1, hLc, hcard⟩ := moving_maximal_quasisimple_data hS h hL
  refine ⟨hAL, ?_⟩
  have hp := sectionTenSetup_prime h
  have hperf : Group.IsPerfect L := hq.1
  have hAe : IsElementaryAbelian p A := h.2.2.2.2.2.2.1
  have hAcard : Nat.card A = p ^ 3 := h.2.2.2.2.2.2.2.1
  set f := centerQuotientAction hAL with hf
  have hker : f.ker = (thetaQuotientAction p hAL).ker := by
    ext a
    rw [mem_ker_thetaQuotientAction_iff, MonoidHom.mem_ker]
    constructor
    · intro ha k hk
      have hcomm := commute_of_centerQuotientAction_eq_one hAL a ha ⟨k, hk⟩
      have h1 : (a : G) * k * (a : G)⁻¹ * k⁻¹ = 1 := by
        have : (a : G) * k = k * (a : G) := hcomm
        rw [this]; group
      rw [h1]
      exact Subgroup.one_mem _
    · intro ha
      rw [hf, centerQuotientAction_eq_one_iff]
      intro l
      obtain ⟨z, hz, hzeq⟩ := inSubgroup_theta_le_center hp hq (ha l l.2)
      have hzl : z = L.normalizerMonoidHom ⟨a, hAL a.2⟩ l / l := by
        apply Subtype.ext
        rw [Subgroup.coe_subtype] at hzeq
        simp only [div_eq_mul_inv, Subgroup.coe_mul, Subgroup.coe_inv,
          coe_normalizerMonoidHom_apply]
        rw [hzeq]
      rw [← hzl]
      exact hz
  have hcardker : Nat.card f.ker = p := by
    calc Nat.card f.ker = Nat.card (thetaQuotientAction p hAL).ker := by rw [hker]
      _ = Nat.card ((thetaQuotientAction p hAL).ker.map A.subtype) :=
        (Subgroup.card_map_of_injective A.subtype_injective).symm
      _ = Nat.card (thetaQuotientCentralizer p A L) := by
        rw [thetaQuotientCentralizer_eq_map_ker p hAL]
      _ = p := hcard
  have hcardrange : Nat.card f.range = p ^ 2 := by
    have h1 := Subgroup.card_ker_mul_card_range f
    rw [hcardker, hAcard] at h1
    have hp0 : 0 < p := hp.pos
    have : p * Nat.card f.range = p * p ^ 2 := by rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_left hp0 this
  obtain ⟨-, S, hSL, hS1, hS2, hAS, hSA⟩ := hL.1
  refine ⟨(S.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center L)), ⟨hp,
    sectionTenSetup_three_lt h, isElementaryAbelian_range hAe f, hcardrange,
    (hS2.comap_subtype).map _, ?_⟩, ?_⟩
  · rintro _ ⟨a, rfl⟩ u hu
    exact centerQuotientAction_mem_map hAL hAS a hu
  · by_contra hcon
    push Not at hcon
    have hcommZ : ⁅S, A⁆ ≤ (Subgroup.center L).map L.subtype := by
      rw [Subgroup.commutator_le]
      intro s hs a ha
      have hsL : s ∈ L := hSL hs
      have hsmem : (⟨s, hsL⟩ : L) ∈ S.subgroupOf L := Subgroup.mem_subgroupOf.mpr hs
      have hmove := hcon (f ⟨a, ha⟩) ⟨⟨a, ha⟩, rfl⟩
        (QuotientGroup.mk' (Subgroup.center L) ⟨s, hsL⟩) ⟨_, hsmem, rfl⟩
      rw [QuotientGroup.mk'_apply, hf, centerQuotientAction_mk,
        QuotientGroup.eq_iff_div_mem] at hmove
      have hz : (L.normalizerMonoidHom ⟨a, hAL ha⟩ ⟨s, hsL⟩ / ⟨s, hsL⟩ : L) ∈
          Subgroup.center L := hmove
      have hval : ((L.normalizerMonoidHom ⟨a, hAL ha⟩ ⟨s, hsL⟩ / ⟨s, hsL⟩ : L) : G) = ⁅a, s⁆ := by
        simp only [div_eq_mul_inv, Subgroup.coe_mul, Subgroup.coe_inv,
          coe_normalizerMonoidHom_apply, commutatorElement_def]
      have hmem : ⁅a, s⁆ ∈ (Subgroup.center L).map L.subtype :=
        ⟨_, hz, by rw [Subgroup.coe_subtype]; exact hval⟩
      rw [← commutatorElement_inv]
      exact ((Subgroup.center L).map L.subtype).inv_mem hmem
    have hSZ : S ≤ (Subgroup.center L).map L.subtype := hSA.le.trans hcommZ
    have hSθ : S ≤ inSubgroup (aschbacherSolvableCore p) L := by
      set N : Subgroup L := S.subgroupOf L with hN
      have hNc : N ≤ Subgroup.center L := by
        intro x hx
        obtain ⟨z, hz, hzx⟩ := hSZ (Subgroup.mem_subgroupOf.mp hx)
        have : z = x := Subtype.ext hzx
        rw [← this]
        exact hz
      have hNn : N.Normal := ⟨fun n hn g => by
        have hg := Subgroup.mem_center_iff.mp (hNc hn) g
        rw [show g * n * g⁻¹ = n by rw [hg]; group]
        exact hn⟩
      have hN2 : IsPGroup 2 N := hS2.comap_subtype
      have := hN2.isNilpotent
      have hNsol : Group.IsSolvable N := inferInstance
      have hNp : ¬ p ∣ Nat.card N := by
        obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hN2
        rw [hk]
        intro hdvd
        have h2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd)
        have h3 := sectionTenSetup_three_lt h
        omega
      have hle := (solvable_prime_complement_core_characterization (H := L) hp).2.2.2.1 N hNn
        hNsol hNp
      intro x hx
      exact Subgroup.mem_map.mpr ⟨⟨x, hSL hx⟩, hle (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
    have hSθ' : S ≤ inSubgroup (aschbacherSolvableCore p)
        (Subgroup.centralizer ({c} : Set G)) := by
      rw [theta_eq_inf_of_mem_thetaComponentsAt hp hLc] at hSθ
      exact fun x hx => (hSθ hx).2
    have hcomm := vanishing_centralizes_invariant_two_subgroups hp (sectionTenSetup_vanishing h)
      hAe hAcard hcA hc1 hSθ' hS2 hAS
    exact hS1 (by rw [hSA, hcomm])

end Plane

end CFSG.RankThree.PartOne
