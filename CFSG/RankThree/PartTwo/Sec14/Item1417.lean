module

public import CFSG.RankThree.PartTwo.Sec14.Item148Solvable
public import CFSG.RankThree.PartTwo.Sec14.Item14ListStatements
import CFSG.Goldschmidt.Steps.G310Basic
import CFSG.RankThree.GroupTheory.SteinbergBYHyperplaneResidual
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.CharacterTheory.Semidihedral.Local.CoprimeCentralizerQuotient
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CanonicalLocalObstruction
public import CFSG.RankThree.PartTwo.Sec14.Item145Bot

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Late CFSG.RankThree.LocalRank CFSG.GH74.GLS

section Quot

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

omit [Finite G] in
theorem eq_one_of_mem_of_pow_three_pow {H : Type*} [Group H] {N : Subgroup H} [Finite N]
    (hN3 : ¬ 3 ∣ Nat.card N) {x : H} (hx : x ∈ N) {k : ℕ} (hk : x ^ 3 ^ k = 1) : x = 1 := by
  have h1 : orderOf (⟨x, hx⟩ : N) ∣ Nat.card N := orderOf_dvd_natCard _
  have h2 : orderOf (⟨x, hx⟩ : N) ∣ 3 ^ k :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hk))
  have hcop : Nat.Coprime (3 ^ k) (Nat.card N) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hN3)
  have h3 : orderOf (⟨x, hx⟩ : N) ∣ Nat.gcd (3 ^ k) (Nat.card N) := Nat.dvd_gcd h2 h1
  rw [Nat.Coprime.gcd_eq_one hcop, Nat.dvd_one, orderOf_eq_one_iff] at h3
  exact congrArg Subtype.val h3

theorem center_sylow_eq_zpowers_of_quot_j2 (h415 : Sec4.Item4_15) {N : Subgroup ↥L} [N.Normal]
    (hN3 : ¬ 3 ∣ Nat.card N)
    (hJ2 : Nonempty (↥L ⧸ N ≃* CFSG.Blueprint.NativeSporadic.J2)) {d : G}
    (hdL : d ∈ L) (hd1 : d ≠ 1) (S : Sylow 3 ↥L) (hdS : (⟨d, hdL⟩ : ↥L) ∈ (S : Subgroup ↥L))
    (hSd : (S : Subgroup ↥L) ≤ Subgroup.centralizer {(⟨d, hdL⟩ : ↥L)}) :
    CFSG.ABGLocalTools.IsSylowOf 3 ((S : Subgroup ↥L).map L.subtype) L ∧
      (Subgroup.center ↥((S : Subgroup ↥L).map L.subtype)).map
          ((S : Subgroup ↥L).map L.subtype).subtype = Subgroup.zpowers d := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := QuotientGroup.mk' N
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective N
  set d' : ↥L := ⟨d, hdL⟩
  set ZS := (S : Subgroup ↥L) ⊓ Subgroup.centralizer ((S : Subgroup ↥L) : Set ↥L) with hZS
  set S' := S.mapSurjective hπs
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
  have hZSle : Nat.card ZS ≤ 3 := by
    rw [← hZ3]
    refine Nat.card_le_card_of_injective (fun z : ZS => (⟨π z, ?_⟩ :
      ↥((S' : Subgroup (↥L ⧸ N)) ⊓ Subgroup.centralizer ((S' : Subgroup (↥L ⧸ N)) : Set _))))
      fun z z' h => Subtype.ext (hinjS _ z.2.1 _ z'.2.1 (congrArg Subtype.val h))
    refine ⟨?_, Subgroup.mem_centralizer_iff.mpr ?_⟩
    · rw [Sylow.coe_mapSurjective]
      exact Subgroup.mem_map_of_mem π z.2.1
    · rw [Sylow.coe_mapSurjective]
      rintro _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp z.2.2 y hy]
  have hdZ : Subgroup.zpowers d' ≤ ZS :=
    Subgroup.zpowers_le.mpr ⟨hdS, Subgroup.mem_centralizer_iff.mpr fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.mp (hSd hy)⟩
  have hd'1 : d' ≠ 1 := fun h => hd1 (congrArg Subtype.val h)
  have hZSp : IsPGroup 3 ZS := S.isPGroup'.to_le inf_le_left
  have hdeq : Subgroup.zpowers d' = ZS := by
    refine Subgroup.eq_of_le_of_card_ge hdZ ?_
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (hZSp.to_le hdZ)
    have hn1 : n ≠ 0 := by
      rintro rfl
      rw [pow_zero, Nat.card_zpowers, orderOf_eq_one_iff] at hn
      exact hd'1 hn
    have h3 : 3 ≤ Nat.card (Subgroup.zpowers d') := by
      rw [hn]
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.mpr hn1)
    omega
  set SG := (S : Subgroup ↥L).map L.subtype
  have hmap : (Subgroup.center ↥SG).map SG.subtype = ZS.map L.subtype := by
    rw [map_subtype_center_eq]
    ext x
    constructor
    · rintro ⟨⟨s, hs, rfl⟩, hxC⟩
      refine ⟨s, ⟨hs, Subgroup.mem_centralizer_iff.mpr fun y hy => Subtype.ext ?_⟩, rfl⟩
      exact Subgroup.mem_centralizer_iff.mp hxC (y : G) ⟨y, hy, rfl⟩
    · rintro ⟨s, ⟨hs, hsC⟩, rfl⟩
      refine ⟨⟨s, hs, rfl⟩, Subgroup.mem_centralizer_iff.mpr ?_⟩
      rintro _ ⟨y, hy, rfl⟩
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hsC y hy)
  refine ⟨⟨S, rfl⟩, ?_⟩
  rw [hmap, ← hdeq, MonoidHom.map_zpowers]
  rfl

theorem residual_inf_centralizer_quasisimple_of_quot (h415 : Sec4.Item4_15)
    {N : Subgroup ↥L} [N.Normal] (hN3 : ¬ 3 ∣ Nat.card N) (hNs : Group.IsSolvable ↥N)
    (hJ2 : Nonempty (↥L ⧸ N ≃* CFSG.Blueprint.NativeSporadic.J2)) {d : G}
    (hdL : d ∈ L) (hd1 : d ≠ 1)
    (hc : ∃ S : Sylow 3 ↥L, (⟨d, hdL⟩ : ↥L) ∈ (S : Subgroup ↥L) ∧
      (S : Subgroup ↥L) ≤ Subgroup.centralizer {(⟨d, hdL⟩ : ↥L)}) :
    IsQuasisimple (↥(inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G))) ⧸
      CFSG.RankThree.LocalRank.aschbacherSolvableCore 3
        ↥(inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := QuotientGroup.mk' N with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective N
  set d' : ↥L := ⟨d, hdL⟩ with hd'
  set CL := Subgroup.centralizer ({d'} : Set ↥L) with hCL
  set J' := inSubgroup perfectResidual CL with hJ'
  have hJ : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) =
      J'.map L.subtype := by
    rw [hJ', CFSG.RankThree.GroupTheory.SteinbergBY.map_inSubgroup_perfectResidual_of_injective
      L.subtype L.subtype_injective, hCL,
      CFSG.RankThree.GroupTheory.SteinbergBY.map_subtype_centralizer_singleton]
  obtain ⟨S, hdS, hSd⟩ := hc
  have hd3 : IsPGroup 3 (Subgroup.zpowers d') := S.isPGroup'.to_le (Subgroup.zpowers_le.mpr hdS)
  have hCmap : CL.map π = Subgroup.centralizer ({π d'} : Set (↥L ⧸ N)) := by
    have h := CFSG.Semidihedral.Local.map_centralizer_eq_of_coprime 3 N hN3 (Subgroup.zpowers d')
      hd3
    rw [MonoidHom.map_zpowers, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
      Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at h
    exact h
  set Cbar := Subgroup.centralizer ({π d'} : Set (↥L ⧸ N)) with hCbar
  set Q := inSubgroup perfectResidual Cbar with hQ
  have hJQ : J'.map π = Q := by
    let ψ : ↥CL →* ↥Cbar := (π.comp CL.subtype).codRestrict Cbar fun c =>
      hCmap ▸ Subgroup.mem_map_of_mem π c.2
    have hψ : Function.Surjective ψ := by
      rintro ⟨q, hq⟩
      rw [← hCmap] at hq
      obtain ⟨c, hc, rfl⟩ := hq
      exact ⟨⟨c, hc⟩, rfl⟩
    have h : (perfectResidual ↥CL).map ψ = perfectResidual ↥Cbar :=
      CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_map_eq ψ hψ
    rw [hJ', hQ, inSubgroup, inSubgroup, ← h, Subgroup.map_map, Subgroup.map_map]
    rfl
  have hd'O : π d' ≠ 1 := by
    intro h
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
    obtain ⟨k, hk⟩ := S.isPGroup' ⟨d', hdS⟩
    exact hd1 (congrArg Subtype.val (eq_one_of_mem_of_pow_three_pow hN3 h (k := k)
      (by simpa using congrArg Subtype.val hk)))
  have hQqs : IsQuasisimple ↥Q := by
    have h := j2_centralizer_residual_quasisimple h415 hJ2 hd'O
      ⟨S.mapSurjective hπs, by
        rw [Sylow.coe_mapSurjective]
        exact Subgroup.mem_map_of_mem π hdS, by
        rw [Sylow.coe_mapSurjective]
        rintro _ ⟨y, hy, rfl⟩
        rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
          Subgroup.mem_centralizer_singleton_iff.mp (hSd hy)]⟩
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((perfectResidual ↥Cbar).equivMapOfInjective Cbar.subtype Cbar.subtype_injective) h
  let ρ : ↥J' →* ↥Q := (π.comp J'.subtype).codRestrict Q fun x =>
    hJQ ▸ Subgroup.mem_map_of_mem π x.2
  have hρ : Function.Surjective ρ := by
    rintro ⟨q, hq⟩
    rw [← hJQ] at hq
    obtain ⟨x, hx, rfl⟩ := hq
    exact ⟨⟨x, hx⟩, rfl⟩
  have hkN : ∀ x : ↥ρ.ker, ((x : ↥J') : ↥L) ∈ N := by
    intro x
    have h1 : ρ x = 1 := x.2
    have h2 : π ((x : ↥J') : ↥L) = 1 := congrArg Subtype.val h1
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    exact h2
  let ι : ↥ρ.ker →* ↥N :=
    { toFun := fun x => ⟨((x : ↥J') : ↥L), hkN x⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hι : Function.Injective ι := by
    intro x y hxy
    have h := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext h)
  have hks : Group.IsSolvable ρ.ker := by
    have := hNs
    exact Group.isSolvable_of_isSolvable_injective hι
  have hk3 : ¬ 3 ∣ Nat.card ρ.ker := fun h3 =>
    hN3 (h3.trans (Subgroup.card_dvd_of_injective ι hι))
  have hJ'q := isQuasisimple_quotient_theta_of_surjective hQqs ρ hρ hks hk3
  rw [hJ]
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (quotThetaEquiv (J'.equivMapOfInjective L.subtype L.subtype_injective)) hJ'q

end Quot

variable {G : Type} [Group G] [Finite G]

theorem transOn_of_mem_scriptQ {A : Subgroup G} {LB : Subgroup G → Subgroup G} (hA : IsE27 A)
    (hbot : ∃ B, IsHyperplane A B ∧ LB B = ⊥) {Y : Subgroup G} (hYQ : Y ∈ scriptQ A LB) :
    TransOn A LB (xA A) Y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA3 : IsPGroup 3 A := hA.isPGroup
  have hY3 : ¬ 3 ∣ Nat.card Y := (isPiSubgroup_piCompl_iff Nat.prime_three Y).mp hYQ.1.2.1
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hYQ.1.2.2
  have hAC : A ≤ Subgroup.centralizer (A : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hA.1.1
  have hsyl : ∀ S ∈ scriptQPiStar A LB Y (piOf 2), CFSG.Open.fusionIsSylowIn 2 S Y ∧
      A ≤ Subgroup.normalizer (S : Set G) := by
    intro S hS
    have hS2 : IsPGroup 2 S := isPGroup_of_mem_scriptQPi Nat.prime_two hS.prop
    have hAS : A ≤ Subgroup.normalizer (S : Set G) := hS.prop.1.1.1.2.2
    obtain ⟨S', hS', hSS', hAS'⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
      Nat.prime_three Nat.prime_two hA3 hY3 hAY hS.prop.1.2 hS2 hAS
    have hS'mem : S' ∈ scriptQPi A LB Y (piOf 2) :=
      ⟨⟨mem_scriptQ_of_le hYQ hS'.1 hAS', hS'.1⟩,
        (isPiSubgroup_piOf_iff Nat.prime_two S').mpr hS'.2.1⟩
    have := hS.eq_of_le hS'mem hSS'
    exact ⟨this ▸ hS', hAS⟩
  intro S hS T hT
  obtain ⟨hSs, hAS⟩ := hsyl S hS
  obtain ⟨hTs, hAT⟩ := hsyl T hT
  obtain ⟨x, hx, hxT⟩ := CFSG.Goldschmidt.G310.exists_conj_of_invariant_sylows Nat.prime_three
    Nat.prime_two hA3 hY3 hAY hSs hTs hAS hAT
  have hCYA : Y ⊓ Subgroup.centralizer (A : Set G) ≤ xA A := by
    refine le_pPrimeCoreOf_centralizer hbot (mem_scriptQ_of_le hYQ inf_le_left ?_) inf_le_right
    exact le_normalizer_inf hAY (hAC.trans Subgroup.le_normalizer)
  exact ⟨x, ⟨hCYA hx, (Subgroup.mem_inf.mp hx).1⟩, hxT⟩

theorem exists_hj_of_conj {A : Subgroup G} {b e w : G}
    (hw : w ∈ Subgroup.normalizer (A : Set G)) {Lb : Subgroup G} (hLb : Lb ∈ lA A b)
    (hJ : Nonempty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.J2))
    (he : Subgroup.zpowers e = (Subgroup.zpowers b).map (MulAut.conj w).toMonoidHom) :
    ∃ Le ∈ lA A e, Nonempty (↥Le ⧸ aschbacherSolvableCore 3 ↥Le ≃*
      CFSG.Blueprint.NativeSporadic.J2) := by
  refine ⟨Lb.map (MulAut.conj w).toMonoidHom, ?_, ?_⟩
  · have h1 : Lb.map (MulAut.conj w).toMonoidHom ∈ lA A (w * b * w⁻¹) :=
      (map_conj_mem_lA_iff hw).mpr hLb
    have h2 : Subgroup.zpowers (w * b * w⁻¹) = Subgroup.zpowers e := by
      rw [he, MonoidHom.map_zpowers]
      rfl
    rwa [lA_eq_of_zpowers_eq h2] at h1
  · obtain ⟨φ⟩ := hJ
    exact ⟨(quotThetaEquiv (Lb.equivMapOfInjective _ (MulAut.conj w).injective)).symm.trans φ⟩

theorem exists_hj_of_hj_point (h134 : Item134) (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15)
    {A L : Subgroup G} {c : G} (h : Sec14Std G A c L) {b d : G} {Lb : Subgroup G}
    (hb : Subgroup.zpowers b ∈ omegaA A) (hLb : Lb ∈ lA A b)
    (hJ : Nonempty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hdA : d ∈ A) (hd1 : d ≠ 1) (hdc : IsThreeCentralIn Lb d) {e : G}
    (he : Subgroup.zpowers e ∈ omegaA A) :
    ∃ Le ∈ lA A e, Nonempty (↥Le ⧸ aschbacherSolvableCore 3 ↥Le ≃*
      CFSG.Blueprint.NativeSporadic.J2) := by
  have hA : IsE27 A := h.isE27
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
    { h.toSec13Data with zpowers_mem_omegaA := hb, mem_lA := hLb }
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

variable {A L : Subgroup G} {c : G}

theorem not_transOn_centralizer_of_meet (h : Sec14Std G A c L) (h146 : Item146 A (lB A))
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥)
    (hfail : ∀ Y : Subgroup G, Y = delta A (lB A) Y → Y ∈ scriptY A →
      CFSG.Open.pCoreOf 2 Y ≠ ⊥ → inSubgroup perfectResidual Y ≠ ⊥ →
        TransOn A (lB A) (xA A) Y)
    {S T : Subgroup G} (hS : S ∈ scriptQPiStar A (lB A) ⊤ (piOf 2))
    (hT : T ∈ scriptQPiStar A (lB A) ⊤ (piOf 2)) (hST : ¬ IsConjIn (xA A) S T)
    {a : G} (haA : a ∈ A) (hSa : S ⊓ Subgroup.centralizer ({a} : Set G) ≠ ⊥)
    (hTa : T ⊓ Subgroup.centralizer ({a} : Set G) ≠ ⊥) :
    ¬ TransOn A (lB A) (xA A) (Subgroup.centralizer ({a} : Set G)) := by
  intro htr
  have hA : IsE27 A := h.isE27
  have hAab : IsMulCommutative A := hA.1.1
  have hACa : A ≤ Subgroup.centralizer ({a} : Set G) := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hAab.is_comm.comm ⟨y, hy⟩ ⟨a, haA⟩))
  have hCa : A ≤ Subgroup.normalizer
      ((Subgroup.centralizer ({a} : Set G) : Subgroup G) : Set G) :=
    hACa.trans Subgroup.le_normalizer
  have hXA : xA A ≤ Subgroup.normalizer (A : Set G) :=
    (pPrimeCoreOf_le 3 _).trans (Subgroup.centralizer_le_normalizer _)
  have hnat := isNaturalFamily_lB A
  have hloc : ∀ U ∈ scriptQPiStar A (lB A) ⊤ (piOf 2),
      U ⊓ Subgroup.centralizer ({a} : Set G) ≠ ⊥ →
      ∃ U₁ ∈ scriptQPiStar A (lB A) (Subgroup.centralizer ({a} : Set G)) (piOf 2),
        ∃ U₂ ∈ scriptQPiStar A (lB A) ⊤ (piOf 2),
          U ⊓ Subgroup.centralizer ({a} : Set G) ≤ U₁ ∧ U₁ ≤ U₂ ∧ IsConjIn (xA A) U U₂ := by
    intro U hU hUa
    have hmem : U ⊓ Subgroup.centralizer ({a} : Set G) ∈
        scriptQPi A (lB A) (Subgroup.centralizer ({a} : Set G)) (piOf 2) :=
      ⟨⟨mem_scriptQ_of_le hU.prop.1.1 inf_le_left
          (le_normalizer_inf hU.prop.1.1.1.2.2 hCa), inf_le_right⟩,
        (isPiSubgroup_piOf_iff Nat.prime_two _).mpr
          ((isPGroup_of_mem_scriptQPi Nat.prime_two hU.prop).to_le inf_le_left)⟩
    obtain ⟨U₁, hUU₁, hU₁⟩ := Finite.exists_le_maximal
      (p := (· ∈ scriptQPi A (lB A) (Subgroup.centralizer ({a} : Set G)) (piOf 2))) hmem
    obtain ⟨U₂, hU₁U₂, hU₂⟩ := Finite.exists_le_maximal
      (p := (· ∈ scriptQPi A (lB A) ⊤ (piOf 2))) (a := U₁) ⟨⟨hU₁.prop.1.1, le_top⟩, hU₁.prop.2⟩
    refine ⟨U₁, hU₁, U₂, hU₂, hUU₁, hU₁U₂, ?_⟩
    by_contra hc
    have hbot' := rank3II_14_15_std h h146 hbot hfail hU hU₂ hc
    exact hUa (le_bot_iff.mp (hbot' ▸ le_inf inf_le_left (hUU₁.trans hU₁U₂)))
  obtain ⟨S₁, hS₁, S₂, hS₂, -, hS₁S₂, hSS₂⟩ := hloc S hS hSa
  obtain ⟨T₁, hT₁, T₂, hT₂, hTT₁, hT₁T₂, hTT₂⟩ := hloc T hT hTa
  obtain ⟨x, hx, hxT₁⟩ := htr S₁ hS₁ T₁ hT₁
  have hxX : x ∈ xA A := (Subgroup.mem_inf.mp hx).1
  have hS₃ : S₂.map (MulAut.conj x).toMonoidHom ∈ scriptQPiStar A (lB A) ⊤ (piOf 2) :=
    maximal_map_conj (fun Q hQ w hw => map_conj_mem_scriptQPi_top hnat (hXA hw) hQ) hS₂ hxX
  have hT₁S₃ : T₁ ≤ S₂.map (MulAut.conj x).toMonoidHom := by
    rw [hxT₁]
    exact Subgroup.map_mono hS₁S₂
  have hT₁0 : T₁ ≠ ⊥ := fun h0 => hTa (le_bot_iff.mp (h0 ▸ hTT₁))
  have hS₃T₂ : IsConjIn (xA A) (S₂.map (MulAut.conj x).toMonoidHom) T₂ := by
    by_contra hc
    have hbot' := rank3II_14_15_std h h146 hbot hfail hS₃ hT₂ hc
    exact hT₁0 (le_bot_iff.mp (hbot' ▸ le_inf hT₁S₃ hT₁T₂))
  exact hST (((hSS₂.trans ⟨x, hxX, rfl⟩).trans hS₃T₂).trans hTT₂.symm)

theorem rank3II_14_17_2 (h134 : Item134) (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15)
    (h : Sec14Std G A c L) (h146 : Item146 A (lB A)) (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥)
    (hfail : Fail1411 A (lB A)) (h2 : Item1411_2 A (lB A)) (h143 : Item143 A (lB A))
    (h1416 : ∀ c' : G, Subgroup.zpowers c' ∈ gammaA A (lB A) → ∀ L' ∈ lA A c',
      IsEmpty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.J2))
    {S T : Subgroup G} (hS : S ∈ scriptQPiStar A (lB A) ⊤ (piOf 2))
    (hT : T ∈ scriptQPiStar A (lB A) ⊤ (piOf 2)) (hST : ¬ IsConjIn (xA A) S T)
    {a : G} (haA : a ∈ A) (ha1 : a ≠ 1) (hSa : S ⊓ Subgroup.centralizer ({a} : Set G) ≠ ⊥)
    (hTa : T ⊓ Subgroup.centralizer ({a} : Set G) ≠ ⊥) :
    Subgroup.zpowers a ∈ gammaA A (lB A) := by
  have hA : IsE27 A := h.isE27
  have hnt := not_transOn_centralizer_of_meet h h146 hbot hfail.2 hS hT hST haA hSa hTa
  by_cases hΩ : Subgroup.zpowers a ∈ omegaA A
  · exact ⟨hΩ, (transOn_normalizer_iff hA haA).not.mpr hnt⟩
  exfalso
  set K := delta A (lB A) (Subgroup.centralizer ({a} : Set G)) with hKdef
  have hAK : A ≤ Subgroup.normalizer (K : Set G) := le_normalizer_sSup fun Q hQ => hQ.1.1.2.2
  obtain ⟨Q, -, hQ⟩ := Finite.exists_le_maximal
    (p := (· ∈ invariantPiSubgroups K A (piCompl 3))) (a := ⊥)
    ⟨bot_le, (isPiSubgroup_piCompl_iff Nat.prime_three ⊥).mpr (by simp),
      by rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]; exact le_top⟩
  obtain ⟨hQ𝓠, hcase⟩ := h143 a haA ha1 hΩ Q hQ
  rcases hcase with hK | ⟨b, d, Lb, hb, hLb, hJ, hdA, hd1, hdc, -, -⟩
  ·
    have hXCa : pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ≤
        Subgroup.centralizer ({a} : Set G) :=
      (pPrimeCoreOf_le 3 _).trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haA))
    have hN : pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ≤
        Subgroup.normalizer (pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) : Set G) :=
      hXCa.trans (le_normalizer_pPrimeCoreOf 3 _)
    have hK3 : ¬ 3 ∣ Nat.card K := by
      intro h3
      rw [hKdef, hK, sup_comm] at h3
      have hdvd := h3.trans (card_sup_dvd_card_mul hN)
      rcases (Nat.Prime.dvd_mul Nat.prime_three).mp hdvd with h1 | h1
      · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
          (coprime_card_pPrimeCoreOf 3 _) h1
      · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
          (coprime_card_pPrimeCoreOf 3 _) h1
    have hKmem : K ∈ invariantPiSubgroups K A (piCompl 3) :=
      ⟨le_rfl, (isPiSubgroup_piCompl_iff Nat.prime_three K).mpr hK3, hAK⟩
    have hQK : Q = K := hQ.eq_of_le hKmem hQ.prop.1
    have hKQ : K ∈ scriptQ A (lB A) := hQK ▸ hQ𝓠.1
    exact hnt (transOn_of_delta (transOn_of_mem_scriptQ hA hbot hKQ))
  ·
    obtain ⟨F, hF⟩ := rank3II_14_12_nonempty hA h2 hfail.1
    obtain ⟨-, -, c', rfl, -⟩ := hF.1
    obtain ⟨Le, hLe, ⟨φ⟩⟩ := exists_hj_of_hj_point h134 h48 h415 h hb hLb hJ hdA hd1 hdc hF.1
    exact (h1416 c' hF Le hLe).false φ

theorem rank3II_14_17 (h134 : Item134) (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15)
    (h : Sec14Std G A c L) (h146 : Item146 A (lB A)) (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥)
    (hfail : Fail1411 A (lB A)) (h2 : Item1411_2 A (lB A)) (h143 : Item143 A (lB A))
    (h1416 : ∀ c' : G, Subgroup.zpowers c' ∈ gammaA A (lB A) → ∀ L' ∈ lA A c',
      IsEmpty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.J2))
    {S T : Subgroup G} (hS : S ∈ scriptQPiStar A (lB A) ⊤ (piOf 2))
    (hT : T ∈ scriptQPiStar A (lB A) ⊤ (piOf 2)) (hST : ¬ IsConjIn (xA A) S T) :
    (∃ a ∈ A, a ≠ 1 ∧ S ⊓ Subgroup.centralizer {a} ≠ ⊥ ∧ T ⊓ Subgroup.centralizer {a} ≠ ⊥) ∧
      ∀ a ∈ A, a ≠ 1 → S ⊓ Subgroup.centralizer {a} ≠ ⊥ → T ⊓ Subgroup.centralizer {a} ≠ ⊥ →
        Subgroup.zpowers a ∈ gammaA A (lB A) :=
  ⟨rank3II_14_17_1 h.isE27 hS hT hST, fun _ haA ha1 hSa hTa =>
    rank3II_14_17_2 h134 h48 h415 h h146 hbot hfail h2 h143 h1416 hS hT hST haA ha1 hSa hTa⟩

end CFSG.RankThree.PartTwo.Sec14
