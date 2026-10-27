module

public import CFSG.RankThree.PartTwo.Sec15.Item153Twin3ProofON
public import CFSG.RankThree.PartTwo.Sec15.Item156Res4ProofCover
public import CFSG.RankThree.PartTwo.Sec15.Item156Res4ProofInner
public import CFSG.RankThree.PartTwo.Sec17.RouteForms
import CFSG.RankThree.PartTwo.Sec15.Item153Twin2ProofON
import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofRead
import CFSG.RankThree.PartTwo.Sec14.Concl142HJPoint
import CFSG.RankThree.PartTwo.Sec16.Item163Proof
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
import CFSG.LieType.BorelTits.Basic
import CFSG.GroupTheory.Fitting.CharacteristicP
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.RankThree.PartTwo.KFacts.K412Alternating
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.RankThree.PartTwo.Sec15.Item1514Steps1515
import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofTools
import CFSG.RankThree.PartTwo.Sec15.Item15More

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

namespace Proof156Res4

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem oRes3_le_of_forall' {J N : Subgroup G}
    (h : ∀ y ∈ J, ∀ k : ℕ, y ^ 3 ^ k = 1 → y ∈ N) : oPrimeResidualOf 3 J ≤ N := by
  rw [oPrimeResidualOf, oPrimeResidual, Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
  rintro x ⟨k, hk⟩
  exact h x x.2 k (by simpa using congrArg Subtype.val hk)

omit [Finite G] in
theorem mem_oRes3_of_pow' {J : Subgroup G} {y : G} (hy : y ∈ J) {k : ℕ} (hk : y ^ 3 ^ k = 1) :
    y ∈ oPrimeResidualOf 3 J :=
  ⟨⟨y, hy⟩, Subgroup.subset_closure ⟨k, Subtype.ext (by simpa using hk)⟩, rfl⟩

omit [Finite G] in
theorem oRes3_idem' (J : Subgroup G) :
    oPrimeResidualOf 3 (oPrimeResidualOf 3 J) = oPrimeResidualOf 3 J :=
  le_antisymm (Subgroup.map_subtype_le _) (oRes3_le_of_forall' fun _ hy _ hk =>
    mem_oRes3_of_pow' (mem_oRes3_of_pow' hy hk) hk)

omit [Finite G] in
theorem le_normalizer_oRes3' {H J : Subgroup G} (hHJ : H ≤ Subgroup.normalizer (J : Set G)) :
    H ≤ Subgroup.normalizer (oPrimeResidualOf 3 J : Set G) := by
  have key : ∀ g ∈ H, ∀ y ∈ oPrimeResidualOf 3 J, g * y * g⁻¹ ∈ oPrimeResidualOf 3 J := by
    intro g hg
    have hle : oPrimeResidualOf 3 J ≤
        (oPrimeResidualOf 3 J).comap (MulAut.conj g).toMonoidHom := by
      refine oRes3_le_of_forall' fun y hy k hk => ?_
      rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      refine mem_oRes3_of_pow' ((Subgroup.mem_normalizer_iff.mp (hHJ hg) y).mp hy) (k := k) ?_
      rw [conj_pow, hk, mul_one, mul_inv_cancel]
    intro y hy
    have := hle hy
    rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
  intro g hg
  refine Subgroup.mem_normalizer_iff.mpr fun y => ⟨key g hg y, fun hy => ?_⟩
  have h1 := key g⁻¹ (inv_mem hg) _ hy
  rwa [inv_inv, show g⁻¹ * (g * y * g⁻¹) * g = y by group] at h1

theorem mem_map_oRes3 {Y J : Subgroup G} (hJY : J ≤ Y) {y : G} (hyJ : y ∈ J) {f : ℕ}
    (hf : (⟨y, hJY hyJ⟩ : ↥Y) ^ 3 ^ f ∈ CFSG.pCore 2 ↥Y) :
    (QuotientGroup.mk' (CFSG.pCore 2 ↥Y) (⟨y, hJY hyJ⟩ : ↥Y)) ∈
      ((oPrimeResidualOf 3 J).subgroupOf Y).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)) := by
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥Y) with hπ
  set yY : ↥Y := ⟨y, hJY hyJ⟩ with hyY
  have hπf : π yY ^ 3 ^ f = 1 := by
    rw [← map_pow, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hf
  obtain ⟨e, r, hr3, hor⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos y).ne' 3 (by norm_num)
  have hyr : (y ^ r) ^ 3 ^ e = 1 := by rw [← pow_mul, mul_comm, ← hor, pow_orderOf_eq_one]
  have hyrK : y ^ r ∈ oPrimeResidualOf 3 J := mem_oRes3_of_pow' (pow_mem hyJ r) hyr
  by_cases hf0 : f = 0
  · subst hf0
    rw [pow_zero, pow_one] at hπf
    rw [hπf]
    exact one_mem _
  have hcop : Nat.Coprime r (3 ^ f) :=
    Nat.Coprime.pow_right f ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hr3).symm
  have hf1 : 1 < 3 ^ f := Nat.one_lt_pow hf0 (by norm_num)
  obtain ⟨s, -, hs⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hf1
  have he : π yY = π yY ^ (r * s) := by
    have hrs : r * s = 3 ^ f * (r * s / 3 ^ f) + 1 := by
      have := Nat.div_add_mod (r * s) (3 ^ f)
      omega
    rw [hrs, pow_succ, pow_mul, hπf, one_pow, one_mul]
  have hmem : ((y ^ r) ^ s) ∈ oPrimeResidualOf 3 J := pow_mem hyrK s
  refine ⟨⟨(y ^ r) ^ s, hJY (Subgroup.map_subtype_le _ hmem)⟩,
    Subgroup.mem_subgroupOf.mpr hmem, ?_⟩
  rw [he, pow_mul, ← map_pow, ← map_pow]
  congr 1

theorem exists_lift_centralizer {Y : Subgroup G} {c : G} (hcY : c ∈ Y) (hc3 : c ^ 3 = 1)
    (y : ↥Y)
    (hy : QuotientGroup.mk' (CFSG.pCore 2 ↥Y) y * QuotientGroup.mk' (CFSG.pCore 2 ↥Y) ⟨c, hcY⟩ =
      QuotientGroup.mk' (CFSG.pCore 2 ↥Y) ⟨c, hcY⟩ * QuotientGroup.mk' (CFSG.pCore 2 ↥Y) y) :
    ∃ y' : ↥Y, QuotientGroup.mk' (CFSG.pCore 2 ↥Y) y' = QuotientGroup.mk' (CFSG.pCore 2 ↥Y) y ∧
      (y' : G) * c = c * y' := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := CFSG.pCore 2 ↥Y with hP
  set π := QuotientGroup.mk' P with hπ
  set cY : ↥Y := ⟨c, hcY⟩ with hcYdef
  set Z := Subgroup.zpowers cY with hZ
  let α : ↥Z →* MulAut ↥Y := MulAut.conj.comp Z.subtype
  have hαN : ∀ a : ↥Z, ∀ n ∈ P, α a n ∈ P := fun a n hn => by
    show (a : ↥Y) * n * (a : ↥Y)⁻¹ ∈ P
    exact (CFSG.pCore_normal (p := 2) (G := ↥Y)).conj_mem n hn a
  have hZ3 : IsPGroup 3 ↥Z := by
    intro z
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp z.2
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, Subgroup.coe_pow, ← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast]
    have : cY ^ 3 = 1 := Subtype.ext (by simpa [hcYdef] using hc3)
    rw [this, one_zpow]
    rfl
  have hPc : ¬ 3 ∣ Nat.card P := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup : IsPGroup 2 P)
    rw [hn]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hlift := CFSG.Semidihedral.Principal.coprime_fixed_point_lifting 3 hZ3 α P hαN hPc
  have hmem : π y ∈ {q : ↥Y ⧸ P | ∀ a : ↥Z,
      CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction α P hαN a q = q} := by
    intro a
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.2
    show π ((a : ↥Y) * y * (a : ↥Y)⁻¹) = π y
    have hc : Commute (π cY) (π y) := hy.symm
    rw [map_mul, map_mul, map_inv, ← hk, map_zpow, ((hc.zpow_left k).eq), mul_inv_cancel_right]
  rw [hlift] at hmem
  obtain ⟨y', hy', hy'y⟩ := hmem
  refine ⟨y', hy'y, ?_⟩
  have h1 : cY * y' * cY⁻¹ = y' := hy' ⟨cY, Subgroup.mem_zpowers cY⟩
  have h2 : (c : G) * y' * c⁻¹ = y' := congrArg Subtype.val h1
  calc (y' : G) * c = c * y' * c⁻¹ * c := by rw [h2]
    _ = c * y' := by group

theorem isQuasisimple_of_isTripleCover_a6 {T : Type*} [Group T] (hperf : Group.IsPerfect T)
    (hT : Sec4.IsTripleCover T (alternatingGroup (Fin 6))) : IsQuasisimple T := by
  obtain ⟨-, ⟨e⟩⟩ := hT
  have : IsSimpleGroup ↥(alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  refine ⟨hperf, e.isSimpleGroup, e.symm ⟨KFacts.K412.fOne, ?_⟩,
    e.symm ⟨Native.ONTriple.sK1, ?_⟩, ?_⟩
  · exact KFacts.K412.eSix_le_alternatingGroup KFacts.K412.fOne_mem_eSix
  · rw [Equiv.Perm.mem_alternatingGroup]
    decide +kernel
  · intro h
    have h1 := congrArg e h
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h1
    have h2 := congrArg Subtype.val h1
    exact absurd h2 (by decide +kernel)

omit [Finite G] in
theorem le_normalizer_preimage {A Y : Subgroup G} (hAY : A ≤ Y)
    (hA3 : ∀ a ∈ A, a ^ 3 = 1) {R : Subgroup (↥Y ⧸ CFSG.pCore 2 ↥Y)}
    (hR : (A.subgroupOf Y).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)) ≤
      Subgroup.normalizer (R : Set (↥Y ⧸ CFSG.pCore 2 ↥Y))) :
    A ≤ Subgroup.normalizer
      (((R.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥Y))).map Y.subtype : Subgroup G) : Set G) := by
  intro a haA
  refine mem_normalizer_of_conj_le (hA3 a haA) fun x hx => ?_
  obtain ⟨y, hy, rfl⟩ := hx
  have haY := hAY haA
  refine ⟨⟨a, haY⟩ * y * ⟨a, haY⟩⁻¹, ?_, rfl⟩
  have haB : QuotientGroup.mk' (CFSG.pCore 2 ↥Y) ⟨a, haY⟩ ∈
      (A.subgroupOf Y).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)) :=
    ⟨⟨a, haY⟩, Subgroup.mem_subgroupOf.mpr haA, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_comap, map_mul, map_mul, map_inv]
  exact (Subgroup.mem_normalizer_iff.mp (hR haB) _).mp (Subgroup.mem_comap.mp hy)

omit [Finite G] in
theorem mem_preimage_iff {Y : Subgroup G} {R : Subgroup (↥Y ⧸ CFSG.pCore 2 ↥Y)} (y : ↥Y) :
    (y : G) ∈ (R.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥Y))).map Y.subtype ↔
      QuotientGroup.mk' (CFSG.pCore 2 ↥Y) y ∈ R := by
  constructor
  · rintro ⟨y', hy', hy'y⟩
    rwa [← Subtype.ext hy'y]
  · intro hy
    exact ⟨y, hy, rfl⟩

end Proof156Res4

open Proof156Res4

theorem step156ONK_of
    {G : Type} [Group G] [Finite G] (h134 : Item134) (h48 : Sec4.Item4_8) {A : Subgroup G}
    {c : G} {L : Subgroup G} (h : Sec14Std G A c L) (h148 : Item148 A (lB A)) :
    Step156ONK A (lB A) := by
  intro Y hY hON
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hY4 : Y ∈ scriptY4 A (lB A) := hY.prop.1
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY4.1.2
  have hO : CFSG.Open.pCoreOf 2 Y ≠ ⊥ := hY.prop.2.2
  have hq : IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y) := hY4.2.2.2
  have hAleY : A ≤ Y := le_of_isTripleCover_on h hAY hO hq.1 hON
  obtain ⟨ψ⟩ := ON134.nonempty_equiv_model hq.1 hON
  obtain ⟨c', L', hc', hL', hJ⟩ := Proof153Twin2.exists_hj_point_of_on h134 h48 h h148 hY4 hON
  have h' : Sec14Std G A c' L' := { h with zpowers_mem_omegaA := hc', mem_lA := hL' }
  have h142 : Concl142 A (lB A) := concl142_of_j2 h134 h48 h' hJ
  set P := CFSG.pCore 2 ↥Y with hP
  set π := QuotientGroup.mk' P with hπ
  set O := CFSG.Open.pCoreOf 2 Y with hOdef
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := h.toSec13Data.isElemAbelian
  have hA27 : Nat.card A = 27 := h.toSec13Data.card_eq
  have hcΩ := h.toSec13Data.zpowers_mem_omegaA
  have hcA : c ∈ A := (zpowers_mem_omegaA_iff.mp hcΩ).1
  have hcY : c ∈ Y := hAleY hcA
  set B := (A.subgroupOf Y).map π with hBdef
  have hB : Late.IsE27 B := by
    have hdisj : (A.subgroupOf Y) ⊓ π.ker = ⊥ := by
      rw [hπ, QuotientGroup.ker_mk']
      have hd : Disjoint (A.subgroupOf Y) P := Subgroup.disjoint_of_coprime_natCard (by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAleY).toEquiv, hA27]
        obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup : IsPGroup 2 P)
        rw [hn]
        exact Nat.Coprime.pow_right _ (by norm_num))
      exact hd.eq_bot
    have hcard : Nat.card B = 27 := by
      have h1 := Subgroup.relIndex_mul_card π.ker (A.subgroupOf Y)
      rw [Subgroup.relIndex_ker, inf_comm, hdisj, Subgroup.card_bot, mul_one,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAleY).toEquiv, hA27] at h1
      exact h1
    refine ⟨⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩, hcard⟩
    · obtain ⟨_, ⟨a, ha, rfl⟩⟩ := x
      obtain ⟨_, ⟨b, hb, rfl⟩⟩ := y
      apply Subtype.ext
      show π a * π b = π b * π a
      rw [← map_mul, ← map_mul]
      congr 1
      have hab : ((a : G)) * (b : G) = (b : G) * (a : G) :=
        congrArg Subtype.val (hAe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
      exact Subtype.ext hab
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow]
      have : a ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hAe.2 _ ha)
      rw [this, map_one]
  have hcB : π ⟨c, hcY⟩ ∈ B := ⟨⟨c, hcY⟩, Subgroup.mem_subgroupOf.mpr hcA, rfl⟩
  obtain ⟨Kb, hKbc, hBN, -, hperf, hTC, h3gen, h2gen⟩ := exists_cover_on ψ hON.1 hB hcB
  set Kh : Subgroup G := (Kb.comap π).map Y.subtype with hKh
  set J := Kh ⊓ Subgroup.centralizer ({c} : Set G) with hJ
  set K := oPrimeResidualOf 3 J with hK
  have hKhY : Kh ≤ Y := Subgroup.map_subtype_le _
  have hJY : J ≤ Y := inf_le_left.trans hKhY
  have hKJ : K ≤ J := Subgroup.map_subtype_le _
  have hKY : K ≤ Y := hKJ.trans hJY
  have hKc : K ≤ Subgroup.centralizer ({c} : Set G) := hKJ.trans inf_le_right
  have hAKh : A ≤ Subgroup.normalizer (Kh : Set G) :=
    le_normalizer_preimage hAleY hAe.2 hBN
  have hAC : A ≤ Subgroup.normalizer (Subgroup.centralizer ({c} : Set G) : Set G) := by
    intro a haA
    refine mem_normalizer_of_conj_le (hAe.2 a haA) fun x hx => ?_
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    have hac : a * c = c * a := congrArg Subtype.val (hAe.1.is_comm.comm ⟨a, haA⟩ ⟨c, hcA⟩)
    have hac' : a⁻¹ * c = c * a⁻¹ := by
      calc a⁻¹ * c = a⁻¹ * (c * a) * a⁻¹ := by group
        _ = a⁻¹ * (a * c) * a⁻¹ := by rw [hac]
        _ = c * a⁻¹ := by group
    calc a * x * a⁻¹ * c = a * x * (a⁻¹ * c) := by group
      _ = a * (x * c) * a⁻¹ := by rw [hac']; group
      _ = a * (c * x) * a⁻¹ := by rw [hx]
      _ = a * c * x * a⁻¹ := by group
      _ = c * a * x * a⁻¹ := by rw [hac]
      _ = c * (a * x * a⁻¹) := by group
  have hAJ : A ≤ Subgroup.normalizer (J : Set G) :=
    (le_inf hAKh hAC).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hAK : A ≤ Subgroup.normalizer (K : Set G) := le_normalizer_oRes3' hAJ
  have hKmap : (K.subgroupOf Y).map π = Kb := by
    apply le_antisymm
    · rintro _ ⟨k, hk, rfl⟩
      exact (mem_preimage_iff k).mp
        ((show J ≤ Kh from inf_le_left) (hKJ (Subgroup.mem_subgroupOf.mp hk)))
    · refine h3gen _ fun x hx hx3 => ?_
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective P x
      have hxc : π y * π ⟨c, hcY⟩ = π ⟨c, hcY⟩ * π y :=
        Subgroup.mem_centralizer_singleton_iff.mp (hKbc hx)
      obtain ⟨y', hy'y, hy'c⟩ := exists_lift_centralizer hcY (hAe.2 c hcA) y hxc
      have hy'J : (y' : G) ∈ J :=
        ⟨(mem_preimage_iff y').mpr (by rw [hy'y]; exact hx),
          Subgroup.mem_centralizer_singleton_iff.mpr hy'c⟩
      obtain ⟨e, he⟩ := hx3
      have hf : (⟨(y' : G), hJY hy'J⟩ : ↥Y) ^ 3 ^ e ∈ P := by
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
        have h1 : ((⟨(y' : G), hJY hy'J⟩ : ↥Y) : ↥Y ⧸ P) = π y := hy'y
        rw [h1]
        exact he
      have := mem_map_oRes3 hJY hy'J hf
      have e1 : QuotientGroup.mk' P (⟨(y' : G), hJY hy'J⟩ : ↥Y) = π y := hy'y
      rwa [e1] at this
  have hmemQ : ∀ R : Subgroup G, R ≤ K → ¬ 3 ∣ Nat.card R →
      A ≤ Subgroup.normalizer (R : Set G) → R ∈ scriptQ A (lB A) := fun R hRK hR3 hAR =>
    Sec16.mem_scriptQ_of_concl142 h142 hcΩ
      ⟨(hRK.trans hKc).trans (centralizer_singleton_le_normalizer_zpowers c),
        (isPiSubgroup_piCompl_iff Nat.prime_three R).mpr hR3, hAR⟩
  have hnot3 : ∀ R : Subgroup G, IsPGroup 2 R → ¬ 3 ∣ Nat.card R := by
    intro R hR h3
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hR
    rw [hn] at h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hYO : Y ≤ Subgroup.normalizer (O : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y
  have hAO : A ≤ Subgroup.normalizer (O : Set G) :=
    hAY.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)
  have hKD : K = delta A (lB A) K := by
    set D := delta A (lB A) K with hD
    refine le_antisymm ?_ (delta_le K)
    have hKO : K ⊓ O ≤ D := le_delta (hmemQ _ inf_le_left (hnot3 _ (hO2.to_le inf_le_right))
      ((le_inf hAK hAO).trans Subgroup.inf_normalizer_le_normalizer_inf)) inf_le_left
    have hKbD : Kb ≤ (D.subgroupOf Y).map π := by
      refine h2gen _ fun R hRK hBR hR2 => ?_
      set Rt := K ⊓ (R.comap π).map Y.subtype with hRt
      have hRtK : Rt ≤ K := inf_le_left
      have hRt2 : IsPGroup 2 Rt := by
        rintro ⟨g, hgK, hgR⟩
        obtain ⟨y, hy, rfl⟩ := hgR
        have hy2 : y ^ 2 ∈ P := by
          rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
          exact hR2 _ hy
        have hyO : ((y ^ 2 : ↥Y) : G) ∈ O := (mem_pCoreOf_iff_mk_eq_one _).mpr
          ((QuotientGroup.eq_one_iff _).mpr hy2)
        obtain ⟨k, hk⟩ := hO2 ⟨_, hyO⟩
        refine ⟨k + 1, Subtype.ext ?_⟩
        have hk' : ((y : G) ^ 2) ^ 2 ^ k = 1 := by
          have := congrArg Subtype.val hk
          simpa using this
        show ((y : G)) ^ 2 ^ (k + 1) = 1
        rw [pow_succ, mul_comm, pow_mul]
        exact hk'
      have hART : A ≤ Subgroup.normalizer (Rt : Set G) :=
        (le_inf hAK (le_normalizer_preimage hAleY hAe.2 hBR)).trans
          Subgroup.inf_normalizer_le_normalizer_inf
      have hRtD : Rt ≤ D := le_delta (hmemQ Rt hRtK (hnot3 _ hRt2) hART) hRtK
      intro r hr
      have hrK : r ∈ (K.subgroupOf Y).map π := hKmap ▸ hRK hr
      obtain ⟨k, hk, rfl⟩ := hrK
      have hkRt : (k : G) ∈ Rt := ⟨Subgroup.mem_subgroupOf.mp hk, (mem_preimage_iff k).mpr hr⟩
      exact ⟨k, Subgroup.mem_subgroupOf.mpr (hRtD hkRt), rfl⟩
    intro x hx
    have hxY := hKY hx
    have hπx : π ⟨x, hxY⟩ ∈ Kb := hKmap ▸ ⟨⟨x, hxY⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    obtain ⟨d, hd, hdx⟩ := hKbD hπx
    have hdK : (d : G) ∈ K := delta_le K (Subgroup.mem_subgroupOf.mp hd)
    have hdxO : ((d⁻¹ * ⟨x, hxY⟩ : ↥Y) : G) ∈ O := by
      rw [mem_pCoreOf_iff_mk_eq_one, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      have h1 : (d : ↥Y ⧸ P) = ((⟨x, hxY⟩ : ↥Y) : ↥Y ⧸ P) := hdx
      rw [h1, inv_mul_cancel]
    have hdxK : ((d⁻¹ * ⟨x, hxY⟩ : ↥Y) : G) ∈ K := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv]
      exact mul_mem (inv_mem hdK) hx
    have e : x = (d : G) * ((d⁻¹ * ⟨x, hxY⟩ : ↥Y) : G) := by simp
    rw [e]
    exact mul_mem (Subgroup.mem_subgroupOf.mp hd) (hKO ⟨hdxK, hdxO⟩)
  set f : ↥K →* ↥Y ⧸ P := π.comp (Subgroup.inclusion hKY) with hf
  have hrange : f.range = Kb := by
    rw [← hKmap]
    ext q
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨Subgroup.inclusion hKY k, Subgroup.mem_subgroupOf.mpr k.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, Subgroup.mem_subgroupOf.mp hy⟩, rfl⟩
  have hker : f.ker = CFSG.pCore 2 ↥K := by
    apply le_antisymm
    · refine le_sSup ⟨inferInstance, fun x => ?_⟩
      have hxO : ((x : ↥K) : G) ∈ O := by
        have h1 : f x = 1 := x.2
        exact (mem_pCoreOf_iff_mk_eq_one (Subgroup.inclusion hKY (x : ↥K))).mpr h1
      obtain ⟨k, hk⟩ := hO2 ⟨_, hxO⟩
      exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩
    · have hKb' : Sec4.IsTripleCover ↥f.range (alternatingGroup (Fin 6)) :=
        Proof1515.isTripleCover_congr (MulEquiv.subgroupCongr hrange.symm) hTC
      have hn : ((CFSG.pCore 2 ↥K).map f.rangeRestrict).Normal :=
        Subgroup.Normal.map inferInstance _ f.rangeRestrict_surjective
      have h2 : IsPGroup 2 ((CFSG.pCore 2 ↥K).map f.rangeRestrict) :=
        CFSG.pCore_isPGroup.map _
      have hbot := Proof153Twin3.eq_bot_of_isTripleCover hKb' h2
      intro x hx
      have h1 : f.rangeRestrict x = 1 := by
        have : f.rangeRestrict x ∈ (CFSG.pCore 2 ↥K).map f.rangeRestrict :=
          Subgroup.mem_map_of_mem _ hx
        rwa [hbot, Subgroup.mem_bot] at this
      rw [MonoidHom.mem_ker]
      exact congrArg Subtype.val h1
  have eK : ↥K ⧸ CFSG.pCore 2 ↥K ≃* ↥Kb :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      ((QuotientGroup.quotientKerEquivRange f).trans (MulEquiv.subgroupCongr hrange))
  have hKq : IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eK.symm (isQuasisimple_of_isTripleCover_a6 hperf hTC)
  have hK4 : K ∈ scriptY4 A (lB A) :=
    ⟨⟨fun htop => hY4.1.1 (top_le_iff.mp (htop ▸ hKY)), hAK⟩, (oRes3_idem' J).symm, hKD, hKq⟩
  exact ⟨c, K, hcΩ, hK4, le_inf hKY hKc,
    Proof1515.isTripleCover_congr (MulEquiv.subgroupCongr hKmap.symm) hTC⟩

theorem step156ONKR_of
    (h148 : Item148R) (h134 : Item134) (h48 : Sec4.Item4_8) : Step156ONKR :=
  fun G _ _ A c L hR => step156ONK_of h134 h48 hR.toSec14Std (h148 G A c L hR)

theorem step156ONXKR_of_items
    (h148 : Item148R) (h152 : Item152R) (h134 : Item134) (h48 : Sec4.Item4_8) : Step156ONXKR :=
  step156ONXKR_of_onk h152 (step156ONKR_of h148 h134 h48)

end CFSG.RankThree.PartTwo.Sec15
