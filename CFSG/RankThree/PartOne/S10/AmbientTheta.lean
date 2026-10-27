module

public import CFSG.RankThree.PartOne.S9.Sylow.ResidualBridge
public import CFSG.RankThree.PartOne.S10.Defs
import CFSG.RankThree.GroupTheory.SteinbergCDCentralizedSylowTwo
import CFSG.RankThree.GroupTheory.SteinbergBMTwoCommutatorLift
import CFSG.RankThree.GroupTheory.SteinbergBMSimplePlaneFixedTwoCommutator

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.GroupTheory.SteinbergBY
open CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement Pointwise

variable {G : Type*} [Group G]

theorem mem_image_map_subtype_iff_of_le {H L : Subgroup G} {S : Set (Subgroup H)} :
    L ∈ (fun L' : Subgroup H => L'.map H.subtype) '' S ↔ L ≤ H ∧ L.subgroupOf H ∈ S := by
  constructor
  · rintro ⟨L', hL', rfl⟩
    refine ⟨Subgroup.map_subtype_le L', ?_⟩
    rwa [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  · rintro ⟨hLH, hL⟩
    exact ⟨_, hL, Subgroup.map_subgroupOf_eq_of_le hLH⟩

theorem mem_thetaComponentsAt_iff {p : ℕ} {a : G} {L : Subgroup G} :
    L ∈ thetaComponentsAt p a ↔ L ≤ Subgroup.centralizer ({a} : Set G) ∧
      L.subgroupOf (Subgroup.centralizer ({a} : Set G)) ∈
        thetaComponents p (Subgroup.centralizer ({a} : Set G)) :=
  mem_image_map_subtype_iff_of_le

theorem mem_thetaComponentFamily_iff {p : ℕ} {A L : Subgroup G} :
    L ∈ thetaComponentFamily p A ↔ ∃ a ∈ A, a ≠ 1 ∧ L ∈ thetaComponentsAt p a := by
  simp only [thetaComponentFamily, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop, and_assoc]

theorem isSubnormal_of_mem_thetaComponentsAt {p : ℕ} {a : G} {L : Subgroup G}
    (hL : L ∈ thetaComponentsAt p a) :
    (L.subgroupOf (Subgroup.centralizer ({a} : Set G))).IsSubnormal :=
  (mem_thetaComponentsAt_iff.mp hL).2.2.1

theorem isPerfect_of_mem_thetaComponentsAt {p : ℕ} {a : G} {L : Subgroup G}
    (hL : L ∈ thetaComponentsAt p a) : Group.IsPerfect L := by
  obtain ⟨hLC, hL'⟩ := mem_thetaComponentsAt_iff.mp hL
  have := hL'.1
  exact Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hLC).toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe hLC).surjective

theorem isQuasisimple_thetaQuotient_of_mem_thetaComponentsAt [Finite G] {p : ℕ} (hp : p.Prime)
    {a : G} {L : Subgroup G} (hL : L ∈ thetaComponentsAt p a) :
    CFSG.IsQuasisimple (L ⧸ aschbacherSolvableCore p L) := by
  obtain ⟨hLC, hL'⟩ := mem_thetaComponentsAt_iff.mp hL
  set e := Subgroup.subgroupOfEquivOfLe hLC
  have : Finite (L.subgroupOf (Subgroup.centralizer ({a} : Set G))) := inferInstance
  exact LocalCores.isQuasisimple_of_mulEquiv
    (QuotientGroup.congr _ _ e (aschbacherSolvableCore_map_mulEquiv hp e)) hL'.2.2

theorem theta_eq_inf_of_mem_thetaComponentsAt [Finite G] {p : ℕ} (hp : p.Prime) {a : G}
    {L : Subgroup G} (hL : L ∈ thetaComponentsAt p a) :
    inSubgroup (aschbacherSolvableCore p) L =
      L ⊓ inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({a} : Set G)) := by
  obtain ⟨hLC, hL'⟩ := mem_thetaComponentsAt_iff.mp hL
  set C := Subgroup.centralizer ({a} : Set G)
  have h1 := solvable_prime_complement_core_subnormal_intersection hp hL'.2.1
  have h2 := congrArg (Subgroup.map C.subtype) h1
  rw [Sec9A.map_inSubgroup_theta_of_injective hp C.subtype C.subtype_injective,
    Subgroup.map_subgroupOf_eq_of_le hLC] at h2
  rw [h2, Subgroup.map_inf_eq _ _ C.subtype C.subtype_injective,
    Subgroup.map_subgroupOf_eq_of_le hLC]
  rfl

abbrev conjActionOn {K A : Subgroup G} (hAK : A ≤ normalizer (K : Set G)) :
    MulDistribMulAction A K :=
  MulDistribMulAction.compHom K (Subgroup.inclusion hAK)

theorem coe_smul_conjActionOn {K A : Subgroup G} (hAK : A ≤ normalizer (K : Set G)) (a : A)
    (k : K) :
    letI := conjActionOn hAK
    (((a • k : K)) : G) = (a : G) * k * (a : G)⁻¹ :=
  rfl

theorem le_normalizer_theta_of_le_normalizer [Finite G] {p : ℕ} (hp : p.Prime) {A L : Subgroup G}
    (hAL : A ≤ normalizer (L : Set G)) :
    A ≤ normalizer ((inSubgroup (aschbacherSolvableCore p) L : Subgroup G) : Set G) := by
  intro a ha
  have hLa : L.map (MulAut.conj a).toMonoidHom = L := mem_normalizer_iff_map_conj_eq.mp (hAL ha)
  rw [mem_normalizer_iff_map_conj_eq]
  have h := Sec9A.map_inSubgroup_theta_of_injective hp (MulAut.conj a).toMonoidHom
    (MulAut.conj a).injective L
  rw [hLa] at h
  exact h

theorem vanishing_centralizes_invariant_two_subgroups [Finite G] {p : ℕ} (hp : p.Prime)
    (hvan : AschVanishing G p) {A : Subgroup G} (hAe : IsElementaryAbelian p A)
    (hAcard : Nat.card A = p ^ 3) {c : G} (hcA : c ∈ A) (hc1 : c ≠ 1) {U : Subgroup G}
    (hU : U ≤ inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({c} : Set G)))
    (hU2 : IsPGroup 2 U) (hUA : A ≤ normalizer (U : Set G)) : ⁅U, A⁆ = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  set C := Subgroup.centralizer ({c} : Set G) with hC
  set X := inSubgroup (aschbacherSolvableCore p) C with hX
  obtain ⟨B', hB'⟩ := Sylow.exists_subgroup_card_pow_prime (G := A) p
    (n := 2) (by rw [hAcard]; exact pow_dvd_pow p (by norm_num))
  set B := B'.map A.subtype with hB
  have hBA : B ≤ A := Subgroup.map_subtype_le _
  have hBcard : Nat.card B = p ^ 2 := by
    rw [hB, Subgroup.card_map_of_injective A.subtype_injective, hB']
  obtain ⟨-, ⟨T, hT⟩, -⟩ := hvan A hAe hAcard B hBA hBcard c hcA hc1
  have hAC : A ≤ C := by
    intro a ha
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hAe.is_comm.comm (⟨a, ha⟩ : A) ⟨c, hcA⟩)
  have hAX : A ≤ normalizer (X : Set G) :=
    le_normalizer_theta_of_le_normalizer hp (hAC.trans Subgroup.le_normalizer)
  let _ : MulDistribMulAction A X := conjActionOn hAX
  have hsmul : ∀ (b : A) (x : X), ((b • x : X) : G) = (b : G) * x * (b : G)⁻¹ := fun _ _ => rfl
  have hpX : ¬ p ∣ Nat.card X := by
    have h := (solvable_prime_complement_core_characterization (H := C) hp).2.2.1
    rwa [hX, inSubgroup, Subgroup.card_map_of_injective C.subtype_injective ]
  have hT' : ∀ b : A, ∀ x ∈ (T : Subgroup X), b • x = x := by
    intro b x hx
    have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hT
    have hxc := hle (Subgroup.mem_map_of_mem X.subtype hx)
    have h : (b : G) * (x : G) = (x : G) * (b : G) :=
      Subgroup.mem_centralizer_iff.mp hxc (b : G) b.2
    apply Subtype.ext
    rw [hsmul]
    calc (b : G) * x * (b : G)⁻¹ = x * b * (b : G)⁻¹ := by rw [h]
      _ = x := by group
  have hU2' : IsPGroup 2 (U.subgroupOf X) := hU2.comap_subtype
  have hUinv : ∀ b : A, ∀ x ∈ U.subgroupOf X, b • x ∈ U.subgroupOf X := by
    intro b x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    rw [hsmul]
    exact (Subgroup.mem_normalizer_iff.mp (hUA b.2) x).mp hx
  have hmain := CFSG.RankThree.GroupTheory.centralized_sylow_two_controls_invariant_two_subgroups
    (p := p) (IsElementaryAbelian.isPGroup p A) hpX T hT' (U.subgroupOf X) hU2' hUinv
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro u hu
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  have h := hmain ⟨b, hb⟩ ⟨u, hU hu⟩ (by rw [Subgroup.mem_subgroupOf]; exact hu)
  have h' := congrArg Subtype.val h
  rw [hsmul] at h'
  calc b * u = b * u * (b : G)⁻¹ * b := by group
    _ = u * b := by simp only at h'; rw [h']

theorem le_normalizer_of_conj_mem_forall {A M : Subgroup G}
    (h : ∀ a ∈ A, ∀ x ∈ M, a * x * a⁻¹ ∈ M) : A ≤ normalizer (M : Set G) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h a ha x, fun hx => ?_⟩
  have h2 := h a⁻¹ (A.inv_mem ha) _ hx
  have e : a⁻¹ * (a * x * a⁻¹) * a⁻¹⁻¹ = x := by group
  rwa [e] at h2

theorem le_normalizer_inf_of_le_normalizer {A R N : Subgroup G}
    (hR : A ≤ normalizer (R : Set G)) (hN : A ≤ normalizer (N : Set G)) :
    A ≤ normalizer ((R ⊓ N : Subgroup G) : Set G) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro g
  simp only [Subgroup.mem_inf]
  rw [Subgroup.mem_normalizer_iff.mp (hR ha) g, Subgroup.mem_normalizer_iff.mp (hN ha) g]

theorem theta_le_and_normal (p : ℕ) (L : Subgroup G) :
    inSubgroup (aschbacherSolvableCore p) L ≤ L ∧
      ((inSubgroup (aschbacherSolvableCore p) L).subgroupOf L).Normal := by
  refine ⟨Subgroup.map_subtype_le _, ?_⟩
  have h : (inSubgroup (aschbacherSolvableCore p) L).subgroupOf L = aschbacherSolvableCore p L :=
    Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
  rw [h]
  infer_instance

theorem theta_solvable_and_not_dvd [Finite G] {p : ℕ} (hp : p.Prime) (L : Subgroup G) :
    Group.IsSolvable (inSubgroup (aschbacherSolvableCore p) L) ∧
      ¬ p ∣ Nat.card (inSubgroup (aschbacherSolvableCore p) L) := by
  obtain ⟨hs, -, hpn, -⟩ := solvable_prime_complement_core_characterization (H := L) hp
  refine ⟨Group.isSolvable_of_isSolvable_injective
    (f := ((aschbacherSolvableCore p L).equivMapOfInjective L.subtype
      L.subtype_injective).symm.toMonoidHom) (MulEquiv.injective _), ?_⟩
  rwa [inSubgroup, Subgroup.card_map_of_injective L.subtype_injective]

theorem ambient_two_commutator_lift [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {A L N M R : Subgroup G} (hA : IsPGroup p A) (hAL : A ≤ normalizer (L : Set G))
    (hNL : N ≤ L) (hNn : (N.subgroupOf L).Normal) (hAN : A ≤ normalizer (N : Set G))
    (hpN : ¬ p ∣ Nat.card N) (hML : M ≤ L) (hAM : A ≤ normalizer (M : Set G))
    (hLMN : L = M ⊔ N) (hRL : R ≤ L) (hR1 : R ≠ ⊥) (hR2 : IsPGroup 2 R)
    (hAR : A ≤ normalizer (R : Set G)) (hRA : ⁅R, A⁆ = R) (hRN : ⁅R ⊓ N, A⁆ = ⊥) :
    ∃ T : Subgroup G, T ≤ M ∧ T ≠ ⊥ ∧ IsPGroup 2 T ∧ A ≤ normalizer (T : Set G) ∧
      ⁅T, A⁆ = T := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let _ : MulDistribMulAction A L := conjActionOn hAL
  have hsmul : ∀ (a : A) (l : L), ((a • l : L) : G) = (a : G) * l * (a : G)⁻¹ := fun _ _ => rfl
  set N' := N.subgroupOf L with hN'
  have : N'.Normal := hNn
  have : CFSG.IsInvariant A L N' := ⟨fun a g => by
    rw [hN', Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hsmul]
    exact Subgroup.mem_normalizer_iff.mp (hAN a.2) g⟩
  have hpN' : ¬ p ∣ Nat.card N' := by
    rwa [hN', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNL).toEquiv]
  set M' := M.subgroupOf L with hM'
  have hMinv : ∀ a : A, ∀ x ∈ M', a • x ∈ M' := fun a x hx => by
    rw [hM', Subgroup.mem_subgroupOf] at hx ⊢
    rw [hsmul]
    exact (Subgroup.mem_normalizer_iff.mp (hAM a.2) x).mp hx
  have hLMN' : M' ⊔ N' = ⊤ := by
    rw [hM', hN', ← Subgroup.subgroupOf_sup hML hNL, ← hLMN, Subgroup.subgroupOf_self]
  set R' := R.subgroupOf L with hR'
  have hπA : ∀ (a : A) (l : L), (QuotientGroup.mk' N') (a • l) = a • (QuotientGroup.mk' N') l :=
    fun a l => (MulAction.Quotient.smul_mk (H := N') a l).symm
  have hRinv : ∀ a : A, ∀ x ∈ R', a • x ∈ R' := fun a x hx => by
    rw [hR', Subgroup.mem_subgroupOf] at hx ⊢
    rw [hsmul]
    exact (Subgroup.mem_normalizer_iff.mp (hAR a.2) x).mp hx
  have hR'A : actionCommutator A R' = R' := by
    apply Subgroup.map_injective L.subtype_injective
    rw [SteinbergBM.map_actionCommutator_conj hAL R', hR', Subgroup.map_subgroupOf_eq_of_le hRL,
      hRA]
  set E := R'.map (QuotientGroup.mk' N') with hE
  have hE1 : E ≠ ⊥ := by
    intro hE0
    have hle : R ≤ N := by
      intro r hr
      have hrL : r ∈ L := hRL hr
      have : (QuotientGroup.mk' N') ⟨r, hrL⟩ ∈ E := Subgroup.mem_map_of_mem _ (by
        rw [hR', Subgroup.mem_subgroupOf]; exact hr)
      rw [hE0, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
      exact this
    apply hR1
    rw [← hRA, ← inf_eq_left.mpr hle]
    exact hRN
  have hE2 : IsPGroup 2 E := (hR2.comap_subtype).map _
  have hEinv : ∀ a : A, ∀ x ∈ E, a • x ∈ E := by
    rintro a _ ⟨r, hr, rfl⟩
    exact ⟨a • r, hRinv a r hr, hπA a r⟩
  have hEA : actionCommutator A E = E := by
    rw [← SteinbergBM.map_actionCommutator (QuotientGroup.mk' N') hπA R', hR'A]
  obtain ⟨T', hT'M, hT'1, hT'2, hT'inv, hT'A, -⟩ :=
    SteinbergBM.coprime_two_commutator_lifts_through_invariant_supplement hp hp2 hA N' hpN' M'
      hMinv hLMN' E hE1 hE2 hEinv hEA
  set T := T'.map L.subtype with hT
  have hfwd : ∀ a ∈ A, ∀ g ∈ T, a * g * a⁻¹ ∈ T := by
    rintro a ha _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_map.mpr ⟨((⟨a, ha⟩ : A) • x), hT'inv ⟨a, ha⟩ x hx, rfl⟩
  refine ⟨T, ?_, ?_, hT'2.map _, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.mem_subgroupOf.mp (hT'M hx))
  · intro h
    apply hT'1
    exact (Subgroup.map_eq_bot_iff_of_injective T' L.subtype_injective).mp h
  · intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro g
    refine ⟨hfwd a ha g, fun h => ?_⟩
    have h2 := hfwd a⁻¹ (A.inv_mem ha) _ h
    have e : a⁻¹ * (a * g * a⁻¹) * a⁻¹⁻¹ = g := by group
    rwa [e] at h2
  · rw [← SteinbergBM.map_actionCommutator_conj hAL T', hT'A]

theorem oddCore_eq_pPrimeCore_two (X : Type*) [Group X] : oddCore X = pPrimeCore 2 X := by
  unfold oddCore pPrimeCore
  congr 1
  ext K
  simp only [Set.mem_ofPred_eq, Nat.coprime_two_left]

theorem inSubgroup_oddCore_eq {X : Type*} [Group X] (H : Subgroup X) :
    inSubgroup oddCore H = inSubgroup (pPrimeCore 2) H := by
  rw [inSubgroup, inSubgroup, oddCore_eq_pPrimeCore_two]

theorem map_inSubgroup_pPrimeCore_of_injective {X Y : Type*} [Group X] [Group Y] (q : ℕ)
    (f : X →* Y) (hf : Function.Injective f) (K : Subgroup X) :
    (inSubgroup (pPrimeCore q) K).map f = inSubgroup (pPrimeCore q) (K.map f) := by
  rw [inSubgroup, inSubgroup, ← CFSG.pPrimeCore_map_iso q (K.equivMapOfInjective f hf),
    Subgroup.map_map, Subgroup.map_map]
  rfl

theorem oddThetaCore_eq_map {G : Type} [Group G] [Finite G] {p : ℕ} (L : Subgroup G) :
    oddThetaCore p L =
      (inSubgroup (pPrimeCore 2) (aschbacherSolvableCore p L)).map L.subtype := by
  rw [map_inSubgroup_pPrimeCore_of_injective 2 L.subtype L.subtype_injective, oddThetaCore,
    inSubgroup_oddCore_eq]
  rfl

end CFSG.RankThree.PartOne
