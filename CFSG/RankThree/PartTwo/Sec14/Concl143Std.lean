module

public import CFSG.RankThree.PartTwo.Sec14.Concl142HJ
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec13.OmegaNonempty
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem Sec14Std.isE27' {A L : Subgroup G} {c : G} (h : Sec14Std G A c L) : Late.IsE27 A :=
  Late.isE27_of_mem_partTwoE h.toSec13Data.mem_partTwoE

theorem Sec14Std.maximal_isElemAbelian {A L : Subgroup G} {c : G} (h : Sec14Std G A c L) :
    Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A :=
  ⟨h.toSec13Data.isElemAbelian, fun _ hB hAB => (h.toSec13Data.eq_of_le hB hAB).le⟩

section Plane

open CFSG.RankThreeEvenClassification.Helpers

theorem commutator_thetaCoreOf_le_of_local {X : Type*} [Group X] [Finite X] (p : ℕ)
    (hp : p.Prime) (A : Subgroup X) (hab : CFSG.Open.IsElemAbelian p A)
    (hAcard : Nat.card A = p ^ 3) {e : X} (he : e ∈ A) (he1 : e ≠ 1)
    (hlocal : ∀ E : Subgroup X, E ≤ A → Nat.card E = p ^ 2 →
      thetaPlaneAlpha p (E.subgroupOf (Subgroup.centralizer ({e} : Set X))) ≤
        solvablePrimeComplementCore (Subgroup.centralizer ({e} : Set X)) p)
    {E : Subgroup X} (hEA : E ≤ A) (hEcard : Nat.card E = p ^ 2) (heE : e ∈ E) :
    ⁅thetaCoreOf p (Subgroup.centralizer (E : Set X)), A⁆ ≤
      thetaCoreOf p (Subgroup.centralizer ({e} : Set X)) := by
  have hlineLe : Subgroup.zpowers e ≤ E := Subgroup.zpowers_le_of_mem heE
  have hlineCard := elementary_line_card p hp A hab e he he1
  have hlineLt : Subgroup.zpowers e < E := by
    refine lt_of_le_of_ne hlineLe fun heq => ?_
    have hcard := congrArg (fun S : Subgroup X => Nat.card S) heq
    rw [hlineCard, hEcard] at hcard
    nlinarith [hp.two_le]
  obtain ⟨f, hfE, hfout⟩ := IsConcreteLE.exists_of_lt hlineLt
  have hf1 : f ≠ 1 := fun h => hfout (h ▸ (Subgroup.zpowers e).one_mem)
  have hfCard := elementary_line_card p hp A hab f (hEA hfE) hf1
  have heout : e ∉ Subgroup.zpowers f := by
    intro hmem
    have hlineEq : Subgroup.zpowers e = Subgroup.zpowers f :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le_of_mem hmem) (by rw [hlineCard, hfCard])
    exact hfout (hlineEq.symm ▸ Subgroup.mem_zpowers f)
  have hEeq : E = Subgroup.zpowers e ⊔ Subgroup.zpowers f := by
    refine Eq.symm (Subgroup.eq_of_le_of_card_ge
      (sup_le hlineLe (Subgroup.zpowers_le_of_mem hfE)) ?_)
    rw [independent_elementary_pair_plane_card p hp A hab e f he (hEA hfE) he1 hfout, hEcard]
  obtain ⟨D, hDA, hfD, hDcard, hAeq⟩ :=
    rank_three_actor_complementary_plane p hp A hab hAcard f e (hEA hfE) he hf1 heout
  have hDC := hDA.trans (commutative_plane_le_element_centralizer A hab.1 e he)
  have hlineN : Subgroup.zpowers e ≤ Subgroup.normalizer (D : Set X) :=
    (Subgroup.zpowers_le_of_mem he).trans (commutative_actor_normalizes_plane A D hab.1 hDA)
  have hlineFix : Subgroup.zpowers e ≤
      Subgroup.centralizer (thetaCoreOf p (Subgroup.centralizer (E : Set X)) : Set X) := by
    refine Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun x hx => ?_)
    exact (Subgroup.mem_centralizer_iff.mp (thetaCoreOf_le p _ hx) e heE).symm
  have hloc := theta_internal_element_commutator_le_local_alpha p hp D
    (Subgroup.centralizer ({e} : Set X)) hDC f hfD hf1
  rw [hAeq, Subgroup.commutator_comm,
    normalized_sup_commutator_eq_of_fixed D (Subgroup.zpowers e) _ hlineN hlineFix,
    Subgroup.commutator_comm, hEeq, centralizer_join_zpowers]
  exact hloc.trans (Subgroup.map_mono (f := (Subgroup.centralizer ({e} : Set X)).subtype)
    (hlocal D hDA hDcard))

end Plane

theorem commutator_theta_le_of_starConditionAt {A : Subgroup G} (hA : Late.IsE27 A) {a : G}
    (ha : a ∈ A) (ha1 : a ≠ 1) (hstar : StarConditionAt A a) {B : Subgroup G}
    (hB : IsHyperplane A B) (haB : a ∈ B) :
    ⁅inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer (B : Set G)), A⁆ ≤
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G)) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have h27 : Nat.card A = 3 ^ 3 := by rw [hA.2]; norm_num
  have hB9 : Nat.card B = 3 ^ 2 := by
    have := hB.2
    rw [hA.2] at this
    norm_num
    omega
  rw [inSubgroup_aschbacherSolvableCore_eq_thetaCoreOf hp,
    inSubgroup_aschbacherSolvableCore_eq_thetaCoreOf hp]
  exact commutator_thetaCoreOf_le_of_local 3 hp A hA.1 h27 ha ha1
    (fun E hE hEcard => CFSG.RankThree.Theta.raw_plane_containment_of_central_line hp A hA.1 h27
      ha ha1 hstar hE hEcard) hB.1 hB9 haB

omit [Finite G] in
theorem starConditionAt_of_not_mem_omegaA {A : Subgroup G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1)
    (hΩ : Subgroup.zpowers a ∉ omegaA A) : StarConditionAt A a := by
  by_contra h
  exact hΩ (zpowers_mem_omegaA_iff.mpr ⟨ha, Sec13.card_zpowers_eq_three hA ha ha1, h⟩)

theorem inSubgroup_theta_le_pPrimeCoreOf (X : Subgroup G) :
    inSubgroup (aschbacherSolvableCore 3) X ≤ pPrimeCoreOf 3 X := by
  obtain ⟨-, -, h3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥X) Nat.prime_three
  exact Subgroup.map_mono (le_sSup ⟨inferInstance,
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3⟩)

theorem pPrimeCoreOf_le_inSubgroup_theta {X : Subgroup G}
    (hsol : Group.IsSolvable (pPrimeCoreOf 3 X)) :
    pPrimeCoreOf 3 X ≤ inSubgroup (aschbacherSolvableCore 3) X := by
  obtain ⟨-, -, -, hmax, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥X) Nat.prime_three
  set e := (CFSG.pPrimeCore 3 ↥X).equivMapOfInjective X.subtype X.subtype_injective
  have : Group.IsSolvable ↥((CFSG.pPrimeCore 3 ↥X).map X.subtype) := hsol
  have hsol' : Group.IsSolvable (CFSG.pPrimeCore 3 ↥X) :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  have h3 : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore 3 ↥X) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card
  exact Subgroup.map_mono (hmax _ CFSG.pPrimeCore_normal hsol' h3)

theorem commutator_pPrimeCoreOf_le_of_isSolvable {A : Subgroup G} (hA : Late.IsE27 A) {a : G}
    (ha : a ∈ A) (ha1 : a ≠ 1) (hstar : StarConditionAt A a) {B : Subgroup G}
    (hB : IsHyperplane A B) (haB : a ∈ B)
    (hsol : Group.IsSolvable (pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)))) :
    ⁅pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)), A⁆ ≤
      pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) :=
  ((Subgroup.commutator_mono (pPrimeCoreOf_le_inSubgroup_theta hsol) le_rfl).trans
    (commutator_theta_le_of_starConditionAt hA ha ha1 hstar hB haB)).trans
    (inSubgroup_theta_le_pPrimeCoreOf _)

@[expose] def Step143Balance : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ a ∈ A, a ≠ 1 → Subgroup.zpowers a ∉ omegaA A →
      ∀ B : Subgroup G, IsHyperplane A B → a ∈ B →
        ¬ Group.IsSolvable (pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G))) →
          ⁅pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)), A⁆ ≤
            pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G))

theorem commutator_pPrimeCoreOf_le (hbal : Step143Balance) {A L : Subgroup G} {c : G}
    (h : Sec14Std G A c L) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1)
    (hΩ : Subgroup.zpowers a ∉ omegaA A) {B : Subgroup G} (hB : IsHyperplane A B)
    (haB : a ∈ B) :
    ⁅pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)), A⁆ ≤
      pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) := by
  by_cases hsol : Group.IsSolvable (pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)))
  · exact commutator_pPrimeCoreOf_le_of_isSolvable h.isE27' ha ha1
      (starConditionAt_of_not_mem_omegaA h.isE27'.1 ha ha1 hΩ) hB haB hsol
  · exact hbal G A c L h a ha ha1 hΩ B hB haB hsol

theorem inf_centralizer_le_commutator_sup {A : Subgroup G} (hA : Late.IsE27 A)
    (hAmax : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A)
    {X D : Subgroup G} (hX3 : ¬ 3 ∣ Nat.card X) (hAX : A ≤ Subgroup.normalizer (X : Set G))
    (hDA : D ≤ A) :
    X ⊓ Subgroup.centralizer (D : Set G) ≤ ⁅X ⊓ Subgroup.centralizer (D : Set G), A⁆ ⊔
      pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) := by
  set Y := X ⊓ Subgroup.centralizer (D : Set G) with hY
  have hY3 : ¬ 3 ∣ Nat.card Y := fun h3 => hX3 (h3.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := le_normalizer_inf_centralizer hA.1.1 hAX hDA
  have hfac := CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_factorization 3
    Nat.prime_three A Y hA.isPGroup hAY ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hY3)
  calc Y = ⁅Y, A⁆ ⊔ (Y ⊓ Subgroup.centralizer (A : Set G)) := hfac.symm
    _ ≤ _ := sup_le_sup_left (inf_centralizer_le_xA hAmax hY3) _

theorem sup_pPrimeCoreOf_mem_scriptQ {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    (hA : Late.IsE27 A)
    (hAmax : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A) {a : G}
    (ha : a ∈ A) :
    pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔
        pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ∈
      collectionIn (scriptQ A LB) (Subgroup.centralizer ({a} : Set G)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set O := pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) with hO
  set O' := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) with hO'
  have hAab : IsMulCommutative A := hA.1.1
  have hAC : A ≤ Subgroup.centralizer ({a} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hAab.is_comm.comm ⟨x, hx⟩ ⟨a, ha⟩))
  have hAA : A ≤ Subgroup.centralizer (A : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hAab
  have hCAa : Subgroup.centralizer (A : Set G) ≤ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha)
  have hON : Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (O : Set G) :=
    le_normalizer_pPrimeCoreOf 3 _
  have hO'C : O' ≤ Subgroup.centralizer (A : Set G) := pPrimeCoreOf_le 3 _
  have hO'N : O' ≤ Subgroup.normalizer (O : Set G) := (hO'C.trans hCAa).trans hON
  have hle : O ⊔ O' ≤ Subgroup.centralizer ({a} : Set G) :=
    sup_le (pPrimeCoreOf_le 3 _) (hO'C.trans hCAa)
  have hpiO : IsPiSubgroup (piCompl 3) O :=
    (isPiSubgroup_piCompl_iff Nat.prime_three O).mpr
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _))
  have hpiO' : IsPiSubgroup (piCompl 3) O' :=
    (isPiSubgroup_piCompl_iff Nat.prime_three O').mpr
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _))
  have hpi : IsPiSubgroup (piCompl 3) (O ⊔ O') := by
    rw [sup_comm]
    exact isPiSubgroup_piCompl_sup hpiO' hpiO hO'N
  have hAN : A ≤ Subgroup.normalizer ((O ⊔ O' : Subgroup G) : Set G) :=
    le_normalizer_sup (hAC.trans hON) (hAA.trans (le_normalizer_pPrimeCoreOf 3 _))
  have h3 : ¬ 3 ∣ Nat.card (O ⊔ O' : Subgroup G) :=
    (isPiSubgroup_piCompl_iff Nat.prime_three _).mp hpi
  have hcomm : ⁅O ⊔ O', A⁆ ≤ O := by
    rw [CFSG.RankThreeEvenClassification.Helpers.normalized_sup_commutator_eq_of_fixed O O' A
      hO'N hO'C]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp (hAC.trans hON)
  refine ⟨⟨⟨le_top, hpi, hAN⟩, fun D hD => ?_⟩, hle⟩
  have hfac := inf_centralizer_le_commutator_sup hA hAmax h3 hAN hD.1
  by_cases haD : a ∈ D
  ·
    have hCD : Subgroup.centralizer (D : Set G) ≤ Subgroup.centralizer ({a} : Set G) :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haD)
    have h1 : ⁅(O ⊔ O') ⊓ Subgroup.centralizer (D : Set G), A⁆ ≤
        O ⊓ Subgroup.centralizer (D : Set G) :=
      le_inf ((Subgroup.commutator_mono inf_le_left le_rfl).trans hcomm)
        ((commutator_inf_centralizer_le hAab hAN hD.1).trans inf_le_right)
    have hDN : Subgroup.centralizer (D : Set G) ≤
        Subgroup.normalizer ((O ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) :=
      fun x hx =>
        Subgroup.inf_normalizer_le_normalizer_inf ⟨hON (hCD hx), Subgroup.le_normalizer hx⟩
    have hcop : Nat.Coprime 3 (Nat.card (O ⊓ Subgroup.centralizer (D : Set G) : Subgroup G)) :=
      Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
        (coprime_card_pPrimeCoreOf 3 _)
    have h2 : O ⊓ Subgroup.centralizer (D : Set G) ≤
        pPrimeCoreOf 3 (Subgroup.centralizer (D : Set G)) :=
      le_pPrimeCoreOf inf_le_right hDN hcop
    exact hfac.trans ((sup_le_sup_right (h1.trans h2) _).trans le_sup_left)
  ·
    have hAle : A ≤ D ⊔ Subgroup.zpowers a := le_sup_zpowers_of_not_mem hA hD ha haD
    have hCA : (O ⊔ O') ⊓ Subgroup.centralizer (D : Set G) ≤
        (O ⊔ O') ⊓ Subgroup.centralizer (A : Set G) := fun x hx =>
      ⟨hx.1, mem_centralizer_of_le_sup hAle hx.2 (hle hx.1)⟩
    exact hCA.trans ((inf_centralizer_le_xA hAmax h3).trans (le_sup_right.trans le_sup_left))

theorem pPrimeCoreOf_centralizer_le_sup {A : Subgroup G} (hA : Late.IsE27 A)
    (hAmax : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A) {a : G}
    {B : Subgroup G} (hBA : B ≤ A)
    (hbal : ⁅pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)), A⁆ ≤
      pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G))) :
    pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) ≤
      pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔
        pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) := by
  set K := pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) with hK
  have hKcop : Nat.Coprime 3 (Nat.card K) := coprime_card_pPrimeCoreOf 3 _
  have hK3 : ¬ 3 ∣ Nat.card K := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hKcop
  have hAB : A ≤ Subgroup.centralizer (B : Set G) :=
    (Subgroup.le_centralizer_iff_isMulCommutative.mpr hA.1.1).trans (Subgroup.centralizer_le hBA)
  have hAK : A ≤ Subgroup.normalizer (K : Set G) := hAB.trans (le_normalizer_pPrimeCoreOf 3 _)
  have hfac := CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_factorization 3
    Nat.prime_three A K hA.isPGroup hAK hKcop
  rw [← hfac]
  exact sup_le_sup hbal (inf_centralizer_le_xA hAmax hK3)

theorem delta_le_sup_of_forall {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    (hA : Late.IsE27 A)
    (hAmax : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A) {a : G}
    (ha : a ∈ A)
    (hB : ∀ B : Subgroup G, IsHyperplane A B → a ∈ B → LB B = ⊥ ∧
      pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) ≤
        pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔
          pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))) :
    delta A LB (Subgroup.centralizer ({a} : Set G)) ≤
      pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔
        pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) := by
  refine sSup_le fun P hP => ?_
  obtain ⟨hPq, hPa⟩ := hP
  have hP3 : ¬ 3 ∣ Nat.card P := (isPiSubgroup_piCompl_iff Nat.prime_three P).mp hPq.1.2.1
  refine Sec5.le_of_forall_inf_centralizer_sub_le (k := 2) Nat.prime_three hA.1
    (by rw [hA.2]; norm_num) hPq.1.2.2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hP3)
    fun H hHA hH9 => ?_
  have hH : IsHyperplane A H := ⟨hHA, by rw [hA.2, hH9]; norm_num⟩
  by_cases haH : a ∈ H
  · obtain ⟨hLB, hK⟩ := hB H hH haH
    have h1 := hPq.2 H hH
    rw [qBound, hLB, sup_bot_eq] at h1
    exact h1.trans (sup_le hK le_sup_right)
  · have hAle := le_sup_zpowers_of_not_mem hA hH ha haH
    have hCA : P ⊓ Subgroup.centralizer (H : Set G) ≤ P ⊓ Subgroup.centralizer (A : Set G) :=
      fun x hx => ⟨hx.1, mem_centralizer_of_le_sup hAle hx.2 (hPa hx.1)⟩
    exact hCA.trans ((inf_centralizer_le_xA hAmax hP3).trans le_sup_right)

theorem delta_eq_sup_of_forall {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    (hA : Late.IsE27 A)
    (hAmax : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A) {a : G}
    (ha : a ∈ A)
    (hB : ∀ B : Subgroup G, IsHyperplane A B → a ∈ B → LB B = ⊥ ∧
      pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) ≤
        pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔
          pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))) :
    delta A LB (Subgroup.centralizer ({a} : Set G)) =
      pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔
        pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) := by
  have hmem := sup_pPrimeCoreOf_mem_scriptQ (LB := LB) hA hAmax ha
  exact le_antisymm (delta_le_sup_of_forall hA hAmax ha hB) (le_delta hmem.1 hmem.2)

theorem mem_scriptQ_of_delta_eq_sup {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    (hA : Late.IsE27 A)
    (hAmax : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A) {a : G}
    (ha : a ∈ A)
    (hΔ : delta A LB (Subgroup.centralizer ({a} : Set G)) =
      pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔
        pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)))
    {Q : Subgroup G}
    (hQ : Q ∈ invariantPiSubgroups (delta A LB (Subgroup.centralizer ({a} : Set G))) A
      (piCompl 3)) :
    Q ∈ collectionIn (scriptQ A LB) (Subgroup.centralizer ({a} : Set G)) := by
  have hmem := sup_pPrimeCoreOf_mem_scriptQ (LB := LB) hA hAmax ha
  exact ⟨mem_scriptQ_of_le hmem.1 (hQ.1.trans hΔ.le) hQ.2.2, hQ.1.trans (delta_le _)⟩

section Std

variable {A L : Subgroup G} {c : G}

theorem delta_eq_sup_of_lB_eq_bot (hbal : Step143Balance) (h : Sec14Std G A c L) {a : G}
    (ha : a ∈ A) (ha1 : a ≠ 1) (hΩ : Subgroup.zpowers a ∉ omegaA A)
    (hLB : ∀ B : Subgroup G, IsHyperplane A B → a ∈ B → lB A B = ⊥) :
    delta A (lB A) (Subgroup.centralizer ({a} : Set G)) =
      pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔
        pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) :=
  delta_eq_sup_of_forall h.isE27' h.maximal_isElemAbelian ha fun B hB haB =>
    ⟨hLB B hB haB, pPrimeCoreOf_centralizer_le_sup h.isE27' h.maximal_isElemAbelian hB.1
      (commutator_pPrimeCoreOf_le hbal h ha ha1 hΩ hB haB)⟩

theorem concl143_at_of_lB_eq_bot (hbal : Step143Balance) (h : Sec14Std G A c L) {a : G}
    (ha : a ∈ A) (ha1 : a ≠ 1) (hΩ : Subgroup.zpowers a ∉ omegaA A)
    (hLB : ∀ B : Subgroup G, IsHyperplane A B → a ∈ B → lB A B = ⊥) :
    ∀ Q ∈ maxInvariantPiSubgroups (delta A (lB A) (Subgroup.centralizer ({a} : Set G))) A
      (piCompl 3), Q ∈ collectionIn (scriptQ A (lB A)) (Subgroup.centralizer ({a} : Set G)) :=
  fun _ hQ => mem_scriptQ_of_delta_eq_sup h.isE27' h.maximal_isElemAbelian ha
    (delta_eq_sup_of_lB_eq_bot hbal h ha ha1 hΩ hLB) hQ.prop

theorem concl143_of_lB_eq_bot (hbal : Step143Balance) (h : Sec14Std G A c L)
    (hLB : ∀ B : Subgroup G, IsHyperplane A B → lB A B = ⊥) : Concl143 A (lB A) :=
  fun _ ha ha1 hΩ => concl143_at_of_lB_eq_bot hbal h ha ha1 hΩ fun B hB _ => hLB B hB

end Std

end CFSG.RankThree.PartTwo.Sec14
