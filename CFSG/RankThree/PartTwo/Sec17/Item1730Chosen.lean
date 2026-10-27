module

public import CFSG.RankThree.PartTwo.Sec17.Item1730
public import CFSG.RankThree.PartTwo.Sec13.Item13Inputs
public import CFSG.RankThree.PartTwo.KFacts.KS17J2
public import CFSG.RankThree.PartTwo.Sec14.Item1417
public import CFSG.RankThree.PartTwo.Sec15.Item15Type
import CFSG.RankThree.PartTwo.Sec13.Item136
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec13.Item136PGL

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Late
open scoped commutatorElement

section Order27

variable {X : Type*} [Group X] [Finite X]

theorem inf_center_ne_bot_of_card_nine {P F : Subgroup X} (hP : Nat.card P = 27)
    (hZ : Nat.card ↥(P ⊓ Subgroup.centralizer (P : Set X)) = 3) (hFP : F ≤ P)
    (hF : Nat.card F = 9) : F ⊓ (P ⊓ Subgroup.centralizer (P : Set X)) ≠ ⊥ := by
  intro h
  set Z := P ⊓ Subgroup.centralizer (P : Set X) with hZdef
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hFc : ∀ a b : F, a * b = b * a :=
    (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hF]; norm_num)).is_comm.comm
  have hZP : Z ≤ P := inf_le_left
  have hZC : Z ≤ Subgroup.centralizer (P : Set X) := inf_le_right
  have hFF : F ≤ Subgroup.centralizer (F : Set X) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (hFc ⟨y, hy⟩ ⟨x, hx⟩)
  have hZF : Z ≤ Subgroup.centralizer (F : Set X) :=
    hZC.trans (Subgroup.centralizer_le (by exact_mod_cast hFP))
  have hZZ : Z ≤ Subgroup.centralizer (Z : Set X) :=
    hZC.trans (Subgroup.centralizer_le (by exact_mod_cast hZP))
  have hK : F ⊔ Z ≤ Subgroup.centralizer ((F ⊔ Z : Subgroup X) : Set X) := by
    refine sup_le ?_ ?_
    · exact Subgroup.le_centralizer_iff.mpr (sup_le hFF hZF)
    · exact Subgroup.le_centralizer_iff.mpr (sup_le (Subgroup.le_centralizer_iff.mpr hZF) hZZ)
  have hZne : ¬ Z ≤ F := by
    intro hle
    have : Z = ⊥ := by rw [← h, inf_eq_right.mpr hle]
    rw [this, Subgroup.card_bot] at hZ
    norm_num at hZ
  have hKP : F ⊔ Z ≤ P := sup_le hFP hZP
  have hlt : Nat.card F < Nat.card ↥(F ⊔ Z) := by
    refine lt_of_le_of_ne (Subgroup.card_le_of_le le_sup_left) fun heq => hZne ?_
    have := Subgroup.eq_of_le_of_card_ge (le_sup_left : F ≤ F ⊔ Z) heq.ge
    exact this ▸ le_sup_right
  have hdvd : Nat.card ↥(F ⊔ Z) ∣ 3 ^ 3 := by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hP]
    exact Subgroup.card_dvd_of_le hKP
  obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  have hk3 : k = 3 := by
    rw [hkeq, hF] at hlt
    interval_cases k <;> simp_all
  have hKeq : F ⊔ Z = P :=
    Subgroup.eq_of_le_of_card_ge hKP (by rw [hP, hkeq, hk3]; norm_num)
  have hPZ : P ≤ Z := le_inf le_rfl (hKeq ▸ hK)
  have := Subgroup.card_le_of_le hPZ
  omega

theorem isQuasisimple_of_isSimpleGroup' {Q : Type*} [Group Q] (hQ : IsSimpleGroup Q)
    (hnab : ∃ a b : Q, a * b ≠ b * a) : IsQuasisimple Q := by
  have hc : Subgroup.center Q = ⊥ := Sec15.center_eq_bot_of_isSimpleGroup hQ hnab
  let e : Q ⧸ Subgroup.center Q ≃* Q :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  refine ⟨?_, e.isSimpleGroup, ?_⟩
  · refine Group.isPerfect_def.mpr ?_
    rcases (inferInstance : (commutator Q).Normal).eq_bot_or_eq_top with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      have hmem : ⁅a, b⁆ ∈ commutator Q := Subgroup.commutator_mem_commutator
        (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
      exact hab hmem
    · exact h
  · obtain ⟨a, b, hab⟩ := hnab
    exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩

end Order27

section Central

variable {G : Type} [Group G] [Finite G]

theorem exists_threeCentral_of_card_nine (h415 : Sec4.Item4_15) {L : Subgroup G}
    {N : Subgroup ↥L} [N.Normal] (hN3 : ¬ 3 ∣ Nat.card N)
    (hJ2 : Nonempty (↥L ⧸ N ≃* CFSG.Blueprint.NativeSporadic.J2)) {E : Subgroup G} (hEL : E ≤ L)
    (hE3 : ∀ x ∈ E, x ^ 3 = 1) (hE9 : Nat.card E = 9) :
    ∃ d ∈ E, d ≠ 1 ∧ IsThreeCentralIn L d := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set E' := E.subgroupOf L with hE'
  have hE'9 : Nat.card E' = 9 := by
    rw [← hE9]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv
  have hE'p : IsPGroup 3 E' := fun x =>
    ⟨1, Subtype.ext (Subtype.ext (by simpa using hE3 _ (Subgroup.mem_subgroupOf.mp x.2)))⟩
  obtain ⟨S, hES⟩ := hE'p.exists_le_sylow
  set π := QuotientGroup.mk' N with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective N
  set S' := S.mapSurjective hπs with hS'
  obtain ⟨⟨hHeis, -⟩, -⟩ := h415 _ hJ2 S' _ rfl _ rfl
  obtain ⟨hZ3, -, -⟩ := j2_sylow_facts h415 hJ2 S'
  have hinjS : ∀ x ∈ (S : Subgroup ↥L), ∀ y ∈ (S : Subgroup ↥L), π x = π y → x = y := by
    intro x hx y hy hxy
    have hO : x⁻¹ * y ∈ N := by
      rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_mul, map_inv, hxy,
        inv_mul_cancel]
    obtain ⟨k, hk⟩ := S.isPGroup' ⟨x⁻¹ * y, (S : Subgroup ↥L).mul_mem (inv_mem hx) hy⟩
    have h1 := eq_one_of_mem_of_pow_three_pow hN3 hO (k := k)
      (by simpa using congrArg Subtype.val hk)
    rw [inv_mul_eq_one] at h1
    exact h1
  have hFS : E'.map π ≤ (S' : Subgroup (↥L ⧸ N)) := by
    rw [Sylow.coe_mapSurjective]
    exact Subgroup.map_mono hES
  have hF9 : Nat.card ↥(E'.map π) = 9 := by
    rw [← hE'9]
    let f : E' → E'.map π := fun x => ⟨π x, x, x.2, rfl⟩
    have hf : Function.Bijective f := by
      refine ⟨fun x y hxy => Subtype.ext (hinjS _ (hES x.2) _ (hES y.2)
        (congrArg Subtype.val hxy)), ?_⟩
      rintro ⟨_, x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    exact (Nat.card_congr (Equiv.ofBijective f hf)).symm
  have hne := inf_center_ne_bot_of_card_nine hHeis.2.1 hZ3 hFS hF9
  obtain ⟨z, hz, hz1⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left hne
  obtain ⟨⟨e, he, rfl⟩, -, hzC⟩ := hz
  have heS : e ∈ (S : Subgroup ↥L) := hES he
  have hSe : (S : Subgroup ↥L) ≤ Subgroup.centralizer {e} := by
    intro s hs
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hπs' : π s ∈ (S' : Subgroup (↥L ⧸ N)) := by
      rw [Sylow.coe_mapSurjective]
      exact Subgroup.mem_map_of_mem π hs
    have hcomm : π (e * s) = π (s * e) := by
      rw [map_mul, map_mul]
      exact (Subgroup.mem_centralizer_iff.mp hzC (π s) hπs').symm
    exact (hinjS _ ((S : Subgroup ↥L).mul_mem heS hs) _ ((S : Subgroup ↥L).mul_mem hs heS)
      hcomm).symm
  refine ⟨(e : G), Subgroup.mem_subgroupOf.mp he, fun h1 => hz1 ?_, e.2, S, heS, hSe⟩
  have : e = 1 := Subtype.ext h1
  rw [this, map_one]

end Central

section Points

variable {G : Type} [Group G] [Finite G]

theorem exists_hj_at_point (h134 : Item134) (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15)
    {A L : Subgroup G} {c : G} (h : Sec13Data G A c L) {b d : G} {Lb : Subgroup G}
    (hb : Subgroup.zpowers b ∈ omegaA A) (hLb : Lb ∈ lA A b)
    (hJ : Nonempty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hdA : d ∈ A) (hd1 : d ≠ 1) (hdc : IsThreeCentralIn Lb d) {e : G}
    (he : Subgroup.zpowers e ∈ omegaA A) :
    ∃ Le ∈ lA A e, Nonempty (↥Le ⧸ aschbacherSolvableCore 3 ↥Le ≃*
      CFSG.Blueprint.NativeSporadic.J2) := by
  have hA : IsE27 A := isE27_of_mem_partTwoE h.mem_partTwoE
  obtain ⟨hbA, hb3, -⟩ := zpowers_mem_omegaA_iff.mp hb
  have hb1 : b ≠ 1 := by
    intro hb1
    rw [hb1, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at hb3
    exact absurd hb3 (by norm_num)
  obtain ⟨hdL, S, hdS, hSd⟩ := hdc
  obtain ⟨hθs, -, hθ3, -, -⟩ :=
    CFSG.RankThree.LocalRank.solvable_prime_complement_core_characterization (H := ↥Lb)
      Nat.prime_three
  have hS := center_sylow_eq_zpowers_of_quot_j2 h415 hθ3 hJ hdL hd1 S hdS hSd
  have hG4 : SectionFourHyp ↥(Subgroup.centralizer ({d} : Set G)) :=
    h.toTheoremFourHyp.sectionFourHyp
      (centralizer_singleton_ne_top h.isSimpleGroup h.nonabelian hd1)
  have hJq := residual_inf_centralizer_quasisimple_of_quot h415 hθ3 hθs hJ hdL hd1
    ⟨S, hdS, hSd⟩
  obtain ⟨K, hK, hJK⟩ :=
    exists_mem_thetaComponentsAt_le_residual h48 hG4 hA hbA hdA hb1 hLb.1 hJq
  have hdata : Sec13Data G A b Lb :=
    { h with zpowers_mem_omegaA := hb, mem_lA := hLb }
  have hPW : oThreeWPre A ≤ Subgroup.normalizer (A : Set G) := Subgroup.map_subtype_le _
  rcases h134 G A b Lb hdata hJ d hdA hd1 ⟨_, hS⟩ K hK hJK with
    ⟨-, -, h1⟩ | ⟨-, -, -, -, -, -, h2⟩ | ⟨-, -, h3, -⟩
  · rw [h1, Set.mem_singleton_iff] at he
    exact ⟨Lb, (lA_eq_of_zpowers_eq he) ▸ hLb, hJ⟩
  · rcases h2 with ⟨h2, -⟩ | ⟨I, -, -, -, a, -, -, h2, -, La, hLa, hJa⟩
    · rw [h2] at he
      obtain ⟨x, hx, hxe⟩ := he
      exact exists_hj_of_conj (hPW hx) hLb hJ hxe
    · rw [h2] at he
      rcases he with ⟨x, hx, hxe⟩ | ⟨x, hx, hxe⟩
      · exact exists_hj_of_conj (hPW hx) hLb hJ hxe
      · exact exists_hj_of_conj (hPW hx) (hLa ▸ Set.mem_singleton La) hJa hxe
  · rw [h3] at he
    obtain ⟨x, hx, hxe⟩ := he
    exact exists_hj_of_conj hx hLb hJ hxe

end Points

section Chosen

variable {G : Type} [Group G] [Finite G]

theorem center_quot_eq_bot_of_j2 (hJ2z : Subgroup.center CFSG.Blueprint.NativeSporadic.J2 = ⊥)
    {Q : Type*} [Group Q] (hQ : Nonempty (Q ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    Subgroup.center Q = ⊥ := by
  obtain ⟨e⟩ := hQ
  have hmap := Subgroup.map_center_eq e
  rw [hJ2z] at hmap
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp hmap

theorem exists_hj_data (h131 : Item131) (hspor : SporadicModels131) (hSLC : SLTwoCenter)
    (h134 : Item134) (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15)
    (hJs : IsSimpleGroup CFSG.Blueprint.NativeSporadic.J2) (hJ2 : KFacts.KS17J2NotList)
    {A L : Subgroup G} {c : G} (hD : Sec13Data G A c L)
    (hJ : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)) {e : G}
    (he : Subgroup.zpowers e ∈ omegaA A) :
    ∃ Le ∈ lA A e, Nonempty (↥Le ⧸ aschbacherSolvableCore 3 ↥Le ≃*
        CFSG.Blueprint.NativeSporadic.J2) ∧ e ∉ Le ∧
      ∀ K ∈ thetaComponentsAt 3 e, 3 ∣ Nat.card K → K = Le := by
  have hspor' := hspor
  obtain ⟨-, -, ⟨hJ2p, hJ2z⟩⟩ := hspor'
  have hc0 : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ := center_quot_eq_bot_of_j2 hJ2z hJ
  have hJnab : ∃ a b : CFSG.Blueprint.NativeSporadic.J2, a * b ≠ b * a := by
    by_contra hall
    push Not at hall
    have : Subgroup.center CFSG.Blueprint.NativeSporadic.J2 = ⊤ :=
      eq_top_iff.mpr fun x _ => Subgroup.mem_center_iff.mpr fun y => hall y x
    rw [hJ2z] at this
    obtain ⟨x, hx⟩ := exists_ne (1 : CFSG.Blueprint.NativeSporadic.J2)
    exact hx ((Subgroup.mem_bot).mp (this ▸ Subgroup.mem_top x))
  have hq : IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) := by
    obtain ⟨e⟩ := hJ
    refine isQuasisimple_of_isSimpleGroup' e.isSimpleGroup ?_
    obtain ⟨a, b, hab⟩ := hJnab
    exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  have hθ := aschbacherSolvableCore_eq_pCore_two hq hc0
  have hJθ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) := by
    obtain ⟨e⟩ := hJ
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hθ).trans e⟩
  have hZθ : Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) = ⊥ :=
    center_quot_eq_bot_of_j2 hJ2z hJθ
  have hcL : c ∉ L := not_mem_of_center_eq_bot hD hZθ
  have hnotL3 : ¬ IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) := by
    rintro ⟨p, e, hp, -, hiso⟩
    obtain ⟨φ⟩ := hJθ
    refine hJ2.1 p e ?_
    rcases hiso with ⟨hq, ⟨ψ⟩⟩ | ⟨hq, ⟨ψ⟩⟩
    · exact Or.inl ⟨hq, ⟨φ.symm.trans ψ⟩⟩
    · exact Or.inr ⟨hq, ⟨φ.symm.trans ψ⟩⟩
  have h9 : Nat.card (A ⊓ L : Subgroup G) = 9 := by
    rcases cases131 h131 hspor hSLC hD with ⟨-, h9, -⟩ | ⟨-, h9, -⟩ | ⟨-, hPGL, -⟩ | ⟨hcL', -⟩
    · exact h9
    · exact h9
    · exact absurd (facts_of_isZ3PGLThreePi hD hPGL).1 hnotL3
    · exact absurd hcL' hcL
  obtain ⟨-, -, hθ3, -, -⟩ :=
    CFSG.RankThree.LocalRank.solvable_prime_complement_core_characterization (H := ↥L)
      Nat.prime_three
  obtain ⟨d, hdAL, hd1, hdc⟩ := exists_threeCentral_of_card_nine h415 hθ3 hJθ inf_le_right
    (fun x hx => hD.isElemAbelian.2 x hx.1) h9
  obtain ⟨Le, hLe, hJe⟩ := exists_hj_at_point h134 h48 h415 hD hD.zpowers_mem_omegaA hD.mem_lA
    hJθ hdAL.1 hd1 hdc he
  have hDe : Sec13Data G A e Le := { hD with zpowers_mem_omegaA := he, mem_lA := hLe }
  have heLe : e ∉ Le := not_mem_of_center_eq_bot hDe (center_quot_eq_bot_of_j2 hJ2z hJe)
  exact ⟨Le, hLe, hJe, heLe, moreover_of_not_mem h131 hspor hSLC hDe heLe⟩

theorem step1730Chosen_of (h131 : Item131) (hspor : SporadicModels131) (hSLC : SLTwoCenter)
    (h134 : Item134) (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15)
    (hJs : IsSimpleGroup CFSG.Blueprint.NativeSporadic.J2) (hJ2 : KFacts.KS17J2NotList) :
    Step1730Chosen := by
  intro G _ _ A c L hD hJ
  refine chosen136_of_forall_not_mem h131 hspor hSLC hD fun e he L' hL' heL' => ?_
  obtain ⟨Le, hLe, -, heLe, huniq⟩ := exists_hj_data h131 hspor hSLC h134 h48 h415 hJs hJ2 hD hJ
    he
  have hDe : Sec13Data G A e Le := { hD with zpowers_mem_omegaA := he, mem_lA := hLe }
  by_cases h3 : 3 ∣ Nat.card L'
  · exact heLe (huniq L' hL'.1 h3 ▸ heL')
  · apply h3
    have := Subgroup.orderOf_dvd_natCard L' heL'
    rwa [hDe.orderOf_eq] at this

theorem rank3II_17_30_of_inputs (h1728 : Item1728) (h131 : Item131)
    (hspor : SporadicModels131) (hSLC : SLTwoCenter) (h134 : Item134) (h48 : Sec4.Item4_8)
    (h415 : Sec4.Item4_15) (hJs : IsSimpleGroup CFSG.Blueprint.NativeSporadic.J2)
    (hJ2 : KFacts.KS17J2NotList) (hconj : KFacts.KS17HJConjugacy) : Item1730 :=
  rank3II_17_30_of h1728 hconj (step1730Chosen_of h131 hspor hSLC h134 h48 h415 hJs hJ2)

end Chosen

end CFSG.RankThree.PartTwo.Sec17
