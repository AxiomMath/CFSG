module

import CFSG.GroupTheory.PCoreOfSubnormal
import CFSG.GroupTheory.PerfectResidualNodes
import CFSG.RankThree.PartTwo.Sec18.Item189K0Generic
import CFSG.RankThree.PartTwo.Sec19.Step1910Proof
import CFSG.RankThree.PartTwo.Sec19.Hyp1921Basic
import CFSG.RankThree.PartTwo.Sec18.Item185Count
import CFSG.RankThree.PartTwo.Sec18.Item186a
import CFSG.RankThree.PartTwo.Sec20.KFactL3OddRank
import CFSG.RankThree.PartOne.S15K.ProjSLBridge
import CFSG.LocalAnalysis.AGLEmbeddingD2.L34BetaHParaK
public import CFSG.RankThree.PartTwo.Sec19.Item1923Inner
public import CFSG.RankThree.PartTwo.Sec19.Item1923Rank

public section

namespace CFSG.RankThree.PartTwo.Late

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.RankThree.PartTwo.Sec19 (starIm IsList194 IsSmall194 IsTripleA6 IsProperParabolic
  Item194UsedWide3 Item316)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {A M N L K : Subgroup G} {c : G}

private theorem inSubgroup_perfectResidual_top_normal (X : Type) [Group X] [Finite X] :
    (inSubgroup perfectResidual (⊤ : Subgroup X)).Normal := by
  have hc := (CFSG.perfect_residual_characterization (G := ↥(⊤ : Subgroup X))).2.1
  haveI := hc
  have hn : (perfectResidual ↥(⊤ : Subgroup X)).Normal := inferInstance
  exact hn.map (Subgroup.topEquiv : (⊤ : Subgroup X) ≃* X).toMonoidHom (MulEquiv.surjective _)

theorem normal_of_perfect_isSubnormal_of_pCore {X : Type} [Group X] [Finite X] {K Q : Subgroup X}
    (hK : Group.IsPerfect K) (hsn : K.IsSubnormal) (hQ : IsPGroup 2 Q) (hQn : Q.Normal)
    (hKQ : K ⊔ Q = ⊤) : K.Normal := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := hK
  haveI := hQn
  haveI : Group.IsNilpotent Q := hQ.isNilpotent
  have hKp : ⁅K, K⁆ = K := Subgroup.commutator_eq_self
  have hRs : Group.IsSolvable Q := inferInstance
  have htop := CFSG.RankThree.PartTwo.Sec18.perfectResidual_eq_of_isSubnormal hRs hsn hKp hKQ
  rw [← htop]
  exact inSubgroup_perfectResidual_top_normal X

private theorem pCoreOf_eq_inf_of_mem {K : Subgroup G} (hK : K ∈ oTwoComponentsIn M) :
    CFSG.Open.pCoreOf 2 K = K ⊓ CFSG.Open.pCoreOf 2 M := by
  have hKM : K ≤ M := le_of_mem_oTwoComponentsIn hK
  have h2 := (mem_oTwoComponentsIn_iff.mp hK).2
  obtain ⟨-, hsub, -⟩ := h2
  exact CFSG.pCoreOf_eq_inf_pCoreOf_of_isSubnormal
    ((CFSG.Open.IsSubnormal.iff_subgroupOf hKM).mpr hsub)

private theorem perfect_of_mem_oTwoComponentsIn {K : Subgroup G} (hK : K ∈ oTwoComponentsIn M) :
    Group.IsPerfect K := by
  have hKM : K ≤ M := le_of_mem_oTwoComponentsIn hK
  have h2 := (mem_oTwoComponentsIn_iff.mp hK).2
  obtain ⟨hp, -, -⟩ := h2
  haveI := hp
  exact Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hKM).toMonoidHom)
    (MulEquiv.surjective _)

private theorem isSimpleGroup_of_isL3OddType {X : Type} [Group X] (hX : IsL3OddType X) :
    IsSimpleGroup X := by
  obtain ⟨n, -, ⟨e⟩⟩ := hX
  have hP := CFSG.RankThree.PartOne.KCLinearSubfield.isSimpleGroup_projectiveSL
    (K := GaloisField 2 n) (n := 3) (by norm_num)
  haveI := hP
  have h3 := (CFSG.RankThree.PartOne.S15K.projSLEquivProjectiveSL 3
    (GaloisField 2 n)).isSimpleGroup
  haveI := h3
  exact e.isSimpleGroup

private theorem not_mem_of_isPGroup_two {P : Subgroup G} (hP : IsPGroup 2 P) {x : G}
    (hx : orderOf x = 3) : x ∉ P := by
  intro hxP
  obtain ⟨k, hk⟩ := hP ⟨x, hxP⟩
  have h1 : x ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have h2 : 3 ∣ 2 ^ k := by
    rw [← hx]
    exact orderOf_dvd_of_pow_eq_one h1
  have h3 : (3 : ℕ) ∣ 2 := Nat.prime_three.dvd_of_dvd_pow h2
  norm_num at h3

private theorem normalClosureIn_conj_mem {M : Subgroup G} (c : G) {m : G} (hm : m ∈ M) {x : G}
    (hx : x ∈ normalClosureIn M c) : m * x * m⁻¹ ∈ normalClosureIn M c := by
  have hmap : (normalClosureIn M c).map (MulAut.conj m).toMonoidHom ≤ normalClosureIn M c := by
    unfold normalClosureIn
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨m', hm', rfl⟩, rfl⟩
    refine Subgroup.subset_closure ⟨m * m', mul_mem hm hm', ?_⟩
    show m * (m' * c * m'⁻¹) * m⁻¹ = m * m' * c * (m * m')⁻¹
    group
  exact hmap (Subgroup.mem_map_of_mem _ hx)

private theorem three_c_of_orderOf (hc : orderOf c = 3) (hK : K ∈ oTwoComponentsIn M)
    (hcK : c ∈ K) (hKM : M ≤ Subgroup.normalizer (K : Set G))
    (hL3 : IsL3OddType (K ⧸ CFSG.pCore 2 K)) : K = normalClosureIn M c := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKM' : K ≤ M := le_of_mem_oTwoComponentsIn hK
  haveI := perfect_of_mem_oTwoComponentsIn hK
  haveI := isSimpleGroup_of_isL3OddType hL3
  have hRK : normalClosureIn M c ≤ K := by
    unfold normalClosureIn
    rw [Subgroup.closure_le]
    rintro _ ⟨m, hm, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hKM hm) c).mp hcK
  have hcR : c ∈ normalClosureIn M c := Subgroup.subset_closure ⟨1, M.one_mem, by simp⟩
  have hRn : ((normalClosureIn M c).subgroupOf K).Normal := by
    constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using normalClosureIn_conj_mem c (hKM' g.2) hn
  haveI := hRn
  haveI : (((normalClosureIn M c).subgroupOf K).map
      (QuotientGroup.mk' (CFSG.pCore 2 K))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  have hcases := IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (((normalClosureIn M c).subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 K)))
  have hPNR : K ≤ normalClosureIn M c ⊔ CFSG.Open.pCoreOf 2 K := by
    rcases hcases with h | h
    ·
      exfalso
      have hmem : QuotientGroup.mk' (CFSG.pCore 2 K) (⟨c, hcK⟩ : K) ∈
          ((normalClosureIn M c).subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 K)) :=
        Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hcR)
      have h1 : (⟨c, hcK⟩ : K) ∈ CFSG.pCore 2 K := by
        rw [h, Subgroup.mem_bot] at hmem
        exact (QuotientGroup.eq_one_iff _).mp hmem
      exact not_mem_of_isPGroup_two (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K) hc
        (Subgroup.mem_map_of_mem _ h1)
    · intro k hk
      have hmem : QuotientGroup.mk' (CFSG.pCore 2 K) (⟨k, hk⟩ : K) ∈
          ((normalClosureIn M c).subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 K)) := by
        rw [h]
        exact Subgroup.mem_top _
      obtain ⟨r, hr, hreq⟩ := Subgroup.mem_map.mp hmem
      have hrG : (r : G) ∈ normalClosureIn M c := Subgroup.mem_subgroupOf.mp hr
      have ho : (r⁻¹ * ⟨k, hk⟩ : K) ∈ CFSG.pCore 2 K := QuotientGroup.eq.mp hreq
      have hoG : ((r⁻¹ * ⟨k, hk⟩ : K) : G) ∈ CFSG.Open.pCoreOf 2 K :=
        Subgroup.mem_map_of_mem _ ho
      have hkG : k = (r : G) * ((r⁻¹ * ⟨k, hk⟩ : K) : G) := by simp
      rw [hkG]
      exact mul_mem (Subgroup.mem_sup_left hrG) (Subgroup.mem_sup_right hoG)
  have hR : Group.IsSolvable (CFSG.Open.pCoreOf 2 K) := by
    have hP := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K
    haveI : Group.IsNilpotent (CFSG.Open.pCoreOf 2 K) := hP.isNilpotent
    exact inferInstance
  exact CFSG.RankThree.PartTwo.Sec18.eq_of_isPerfect_of_le_sup (P := K) (N := normalClosureIn M c)
    (R := CFSG.Open.pCoreOf 2 K) inferInstance hRK (CFSG.LieType.BorelTits.pCoreOf_le 2 K)
    hRn hR hPNR

private theorem mem_pCore_iff {H : Subgroup G} (x : H) :
    x ∈ CFSG.pCore 2 H ↔ (x : G) ∈ CFSG.Open.pCoreOf 2 H := by
  constructor
  · intro hm
    exact Subgroup.mem_map_of_mem _ hm
  · intro hg'
    obtain ⟨y, hy, hyg⟩ := Subgroup.mem_map.mp hg'
    have : y = x := Subtype.ext hyg
    rw [← this]
    exact hy

private theorem commute_iff_comm_eq_one {Q : Type} [Group Q] (a b : Q) :
    Commute a b ↔ a * b * a⁻¹ * b⁻¹ = 1 :=
  commutatorElement_eq_one_iff_commute.symm

private theorem commute_mk_iff {H : Subgroup G} [Fact (Nat.Prime 2)] (x y : H) :
    Commute (QuotientGroup.mk' (CFSG.pCore 2 H) x) (QuotientGroup.mk' (CFSG.pCore 2 H) y) ↔
      (x : G) * (y : G) * (x : G)⁻¹ * (y : G)⁻¹ ∈ CFSG.Open.pCoreOf 2 H := by
  have hcomm : x * y * x⁻¹ * y⁻¹ ∈ CFSG.pCore 2 H ↔
      (x : G) * (y : G) * (x : G)⁻¹ * (y : G)⁻¹ ∈ CFSG.Open.pCoreOf 2 H := by
    rw [mem_pCore_iff]
    rfl
  have e : QuotientGroup.mk' (CFSG.pCore 2 H) x * QuotientGroup.mk' (CFSG.pCore 2 H) y *
      (QuotientGroup.mk' (CFSG.pCore 2 H) x)⁻¹ * (QuotientGroup.mk' (CFSG.pCore 2 H) y)⁻¹ =
      QuotientGroup.mk' (CFSG.pCore 2 H) (x * y * x⁻¹ * y⁻¹) := by
    simp only [map_mul, map_inv]
  rw [commute_iff_comm_eq_one, e]
  exact (QuotientGroup.eq_one_iff _).trans hcomm

private theorem mem_normalizer_of_map_conj_eq {K : Subgroup G} {g : G}
    (h : K.map (MulAut.conj g).toMonoidHom = K) : g ∈ Subgroup.normalizer (K : Set G) := by
  refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · have hmem : g * x * g⁻¹ ∈ K.map (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hx
    rw [h] at hmem
    exact hmem
  · have hmem : g * x * g⁻¹ ∈ K.map (MulAut.conj g).toMonoidHom := by
      rw [h]
      exact hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hmem
    have hxy : y = x := by
      have h2 : g * y * g⁻¹ = g * x * g⁻¹ := hyx
      simpa using h2
    rw [← hxy]
    exact hy

private theorem center_eq_bot_of_simple_nonab {Y : Type} [Group Y] [IsSimpleGroup Y]
    (hna : ∃ a b : Y, a * b ≠ b * a) : Subgroup.center Y = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Y) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hna
    apply hab
    have ha : a ∈ Subgroup.center Y := h ▸ Subgroup.mem_top a
    exact (Subgroup.mem_center_iff.mp ha b).symm

private theorem nonabelian_of_quotient_center {Y : Type} [Group Y]
    (hq : ∃ a b : Y ⧸ Subgroup.center Y, a * b ≠ b * a) : ∃ a b : Y, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := hq
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  exact ⟨a', b', fun e => hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, e])⟩

private theorem mem_pCoreOf_of_comm_mod {K' : Subgroup G} (hK'c : K' ∈ oTwoComponentsIn M)
    (hcen : Subgroup.center (K' ⧸ CFSG.pCore 2 K') = ⊥) {k : G} (hk : k ∈ K')
    (hcomm : ∀ y ∈ K', k * y * k⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 M) :
    k ∈ CFSG.Open.pCoreOf 2 K' := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hkc : (QuotientGroup.mk (⟨k, hk⟩ : K') : K' ⧸ CFSG.pCore 2 K') ∈
      Subgroup.center (K' ⧸ CFSG.pCore 2 K') := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_pCore_iff]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have hyK : (y : G) ∈ K' := y.2
    have ht : k * (y : G) * k⁻¹ * (y : G)⁻¹ ∈ CFSG.Open.pCoreOf 2 K' := by
      rw [pCoreOf_eq_inf_of_mem hK'c]
      exact ⟨K'.mul_mem (K'.mul_mem (K'.mul_mem hk hyK) (K'.inv_mem hk)) (K'.inv_mem hyK),
      hcomm _ hyK⟩
    have hyk : ((y : G) * k)⁻¹ ∈ K' := K'.inv_mem (K'.mul_mem hyK hk)
    have hz := (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K' hyk) _).mp ht
    have e : ((y : G) * k)⁻¹ * (k * (y : G)) =
        ((y : G) * k)⁻¹ * (k * (y : G) * k⁻¹ * (y : G)⁻¹) * ((y : G) * k)⁻¹⁻¹ := by group
    rw [e]
    exact hz
  rw [hcen, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hkc
  exact (mem_pCore_iff _).mp hkc

private theorem false_of_E81 (h : Hyp1921 G A M N L) {K' : Subgroup G}
    (hK'c : K' ∈ oTwoComponentsIn M) {x : G} (hxK : x ∈ K') (hx3 : orderOf x = 3)
    (hA : ∀ a ∈ A, ∀ k ∈ K', a * k * a⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 M)
    (hcenK : Subgroup.center (K' ⧸ CFSG.pCore 2 K') = ⊥) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAM : A ≤ M := h.le_M
  have hKM : K' ≤ M := le_of_mem_oTwoComponentsIn hK'c
  have hxM : x ∈ M := hKM hxK
  have hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (h.isE27.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := fun a ha => h.isE27.1.2 a ha
  have hAO : ∀ a ∈ A, a ∈ CFSG.Open.pCoreOf 2 M → a = 1 := by
    intro a ha haO
    by_contra hne
    exact not_mem_of_isPGroup_two (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M)
      (orderOf_eq_prime (hA3 a ha) hne) haO
  have hx3' : x ^ 3 = 1 := by
    rw [← hx3]
    exact pow_orderOf_eq_one x
  set AM : Subgroup M := A.subgroupOf M with hAMdef
  set xM : M := ⟨x, hxM⟩ with hxMdef
  have hxM3 : xM ^ 3 = 1 := Subtype.ext (by simpa [hxMdef] using hx3')
  set H : Subgroup (M ⧸ CFSG.pCore 2 M) := AM.map (QuotientGroup.mk' (CFSG.pCore 2 M))
    with hHdef
  set L : Subgroup (M ⧸ CFSG.pCore 2 M) :=
    Subgroup.zpowers (QuotientGroup.mk' (CFSG.pCore 2 M) xM) with hLdef
  have hg3 : QuotientGroup.mk' (CFSG.pCore 2 M) xM ^ 3 = 1 := by
    rw [← map_pow, hxM3, map_one]
  have hmkA : ∀ a : M, a ∈ AM → Commute (QuotientGroup.mk' (CFSG.pCore 2 M) a)
      (QuotientGroup.mk' (CFSG.pCore 2 M) xM) := by
    intro a ha
    rw [commute_mk_iff]
    exact hA (a : G) (Subgroup.mem_subgroupOf.mp ha) x hxK
  have hcHL : ∀ u ∈ H, ∀ v ∈ L, Commute u v := by
    intro u hu v hv
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hu
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    exact (hmkA a ha).zpow_right j
  have hHL : H ⊓ L = ⊥ := by
    rw [eq_bot_iff]
    rintro w ⟨hwH, hwL⟩
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hwH
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hwL
    have hmk : QuotientGroup.mk' (CFSG.pCore 2 M) (xM ^ j) =
        QuotientGroup.mk' (CFSG.pCore 2 M) a := by
      rw [map_zpow]
      exact hj
    have hkK : x ^ j ∈ K' := zpow_mem hxK j
    have hcomm : ∀ y ∈ K', x ^ j * y * (x ^ j)⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 M := by
      intro y hy
      have hyM : y ∈ M := hKM hy
      have c1 : Commute (QuotientGroup.mk' (CFSG.pCore 2 M) a)
          (QuotientGroup.mk' (CFSG.pCore 2 M) (⟨y, hyM⟩ : M)) := by
        rw [commute_mk_iff]
        exact hA (a : G) (Subgroup.mem_subgroupOf.mp ha) y hy
      have c2 : Commute (QuotientGroup.mk' (CFSG.pCore 2 M) (xM ^ j))
          (QuotientGroup.mk' (CFSG.pCore 2 M) (⟨y, hyM⟩ : M)) := by
        rw [hmk]
        exact c1
      have := (commute_mk_iff (xM ^ j) (⟨y, hyM⟩ : M)).mp c2
      simpa [hxMdef] using this
    have hkO : x ^ j ∈ CFSG.Open.pCoreOf 2 K' :=
      mem_pCoreOf_of_comm_mod hK'c hcenK hkK hcomm
    have hxjO : x ^ j ∈ CFSG.Open.pCoreOf 2 M := by
      rw [pCoreOf_eq_inf_of_mem hK'c] at hkO
      exact hkO.2
    have haO : ((a : M) : G) ∈ CFSG.Open.pCoreOf 2 M := by
      have h1 : (xM ^ j)⁻¹ * a ∈ CFSG.pCore 2 M := QuotientGroup.eq.mp hmk
      have h2 := (mem_pCore_iff _).mp h1
      have h3 : ((a : M) : G) = x ^ j * ((((xM ^ j)⁻¹ * a : M)) : G) := by
        simp [hxMdef]
      rw [h3]
      exact mul_mem hxjO h2
    have ha1 : ((a : M) : G) = 1 := hAO _ (Subgroup.mem_subgroupOf.mp ha) haO
    have ha1' : a = 1 := Subtype.ext ha1
    rw [Subgroup.mem_bot, ha1', map_one]
  set S : Set (M ⧸ CFSG.pCore 2 M) := (H : Set (M ⧸ CFSG.pCore 2 M)) ∪ (L : Set _) with hSdef
  have hSc : S.Pairwise Commute := by
    intro u hu v hv _
    rcases hu with hu | hu <;> rcases hv with hv | hv
    · obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hu
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hv
      rw [commute_mk_iff]
      have e : ((a : M) : G) * ((b : M) : G) * ((a : M) : G)⁻¹ * ((b : M) : G)⁻¹ = 1 := by
        rw [hAab _ (Subgroup.mem_subgroupOf.mp ha) _ (Subgroup.mem_subgroupOf.mp hb)]
        group
      rw [e]
      exact one_mem _
    · exact hcHL _ hu _ hv
    · exact (hcHL _ hv _ hu).symm
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
      exact (Commute.refl _).zpow_zpow i j
  set E : Subgroup (M ⧸ CFSG.pCore 2 M) := Subgroup.closure S with hEdef
  have hEab : IsMulCommutative E := Subgroup.isMulCommutative_closure hSc
  have hEexp : ∀ e ∈ E, e ^ 3 = 1 := by
    intro e he
    refine Subgroup.closure_induction (p := fun e _ => e ^ 3 = 1) ?_ ?_ ?_ ?_ he
    · intro u hu
      rcases hu with hu | hu
      · obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hu
        have ha3 : a ^ 3 = 1 :=
          Subtype.ext (by simpa using hA3 _ (Subgroup.mem_subgroupOf.mp ha))
        rw [← map_pow, ha3, map_one]
      · obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hg3, one_zpow]
    · simp
    · intro u v hu hv hu' hv'
      have huv : Commute u v := congrArg Subtype.val (hEab.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
      rw [huv.mul_pow, hu', hv', one_mul]
    · intro u hu hu'
      rw [inv_pow, hu', inv_one]
  let F : (AM × L) → E := fun p => ⟨QuotientGroup.mk' (CFSG.pCore 2 M) (p.1 : M) * (p.2 : _), by
    refine mul_mem (Subgroup.subset_closure (Or.inl ?_)) (Subgroup.subset_closure (Or.inr p.2.2))
    exact Subgroup.mem_map_of_mem _ p.1.2⟩
  have hFinj : Function.Injective F := by
    rintro ⟨⟨a1, ha1⟩, ⟨l1, hl1⟩⟩ ⟨⟨a2, ha2⟩, ⟨l2, hl2⟩⟩ heq
    have heq' : QuotientGroup.mk' (CFSG.pCore 2 M) a1 * l1 =
        QuotientGroup.mk' (CFSG.pCore 2 M) a2 * l2 := congrArg Subtype.val heq
    have hY : QuotientGroup.mk' (CFSG.pCore 2 M) a2 ∈ H := Subgroup.mem_map_of_mem _ ha2
    have hX : QuotientGroup.mk' (CFSG.pCore 2 M) a1 ∈ H := Subgroup.mem_map_of_mem _ ha1
    have hu : (QuotientGroup.mk' (CFSG.pCore 2 M) a2)⁻¹ *
        QuotientGroup.mk' (CFSG.pCore 2 M) a1 = l2 * l1⁻¹ := by
      have hX' : QuotientGroup.mk' (CFSG.pCore 2 M) a1 =
          QuotientGroup.mk' (CFSG.pCore 2 M) a2 * l2 * l1⁻¹ := by
        rw [← heq']
        group
      rw [hX']
      group
    have hmem : (QuotientGroup.mk' (CFSG.pCore 2 M) a2)⁻¹ *
        QuotientGroup.mk' (CFSG.pCore 2 M) a1 ∈ H ⊓ L :=
      ⟨H.mul_mem (H.inv_mem hY) hX, by rw [hu]; exact L.mul_mem hl2 (L.inv_mem hl1)⟩
    rw [hHL, Subgroup.mem_bot] at hmem
    have hmka : QuotientGroup.mk' (CFSG.pCore 2 M) a1 =
        QuotientGroup.mk' (CFSG.pCore 2 M) a2 := by
      rw [inv_mul_eq_one] at hmem
      exact hmem.symm
    have hl : l2 * l1⁻¹ = 1 := by
      rw [← hu, hmem]
    have hl12 : l1 = l2 := (mul_inv_eq_one.mp hl).symm
    have hdiv : ((a1 : M) : G)⁻¹ * ((a2 : M) : G) ∈ A :=
      mul_mem (inv_mem (Subgroup.mem_subgroupOf.mp ha1)) (Subgroup.mem_subgroupOf.mp ha2)
    have hdivO : ((a1 : M) : G)⁻¹ * ((a2 : M) : G) ∈ CFSG.Open.pCoreOf 2 M := by
      have h1 := (mem_pCore_iff _).mp (QuotientGroup.eq.mp hmka)
      simpa using h1
    have hdiv1 := hAO _ hdiv hdivO
    have ha12 : (a1 : M) = (a2 : M) := by
      have : ((a1 : M) : G) = ((a2 : M) : G) := by
        rw [inv_mul_eq_one] at hdiv1
        exact hdiv1
      exact Subtype.ext this
    exact Prod.ext (Subtype.ext ha12) (Subtype.ext hl12)
  have hcardAM : Nat.card AM = 27 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAM).toEquiv]
    exact h.isE27.2
  have hcardL : Nat.card L = 3 := by
    rw [hLdef, Nat.card_zpowers]
    apply orderOf_eq_prime hg3
    intro h1
    apply not_mem_of_isPGroup_two (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M) hx3
    have h2 : xM ∈ CFSG.pCore 2 M := (QuotientGroup.eq_one_iff xM).mp h1
    exact (mem_pCore_iff xM).mp h2
  have hcard : Nat.card (AM × L) = 81 := by
    rw [Nat.card_prod, hcardAM, hcardL]
  have hle := Nat.card_le_card_of_injective F hFinj
  have hEel : CFSG.Assembly.IsElemAbelian 3 E := ⟨hEab, hEexp⟩
  have h27 := h.card_le_of_isElemAbelian_quotient hEel
  omega

private theorem false_of_E9 {Y : Type} [Group Y] [Finite Y] (hsimp : IsSimpleGroup Y)
    (hcen : Subgroup.center Y = ⊥) (hpR : CFSG.Open.pRank 3 (⊤ : Subgroup Y) ≤ 1)
    {P : Type} [Group P] [Finite P] (hPc : IsMulCommutative P) (hPe : ∀ p : P, p ^ 3 = 1)
    (hP9 : Nat.card P = 9) (φ : P →* MulAut Y) (hφi : Function.Injective φ)
    (hφin : ∀ p, φ p ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner Y) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hconj : Function.Injective (MulAut.conj : Y →* MulAut Y) := by
    intro a b hab
    have hz : b⁻¹ * a ∈ Subgroup.center Y := by
      rw [Subgroup.mem_center_iff]
      intro g
      have e : a * g * a⁻¹ = b * g * b⁻¹ := by
        have := congrArg (fun φ' : MulAut Y => φ' g) hab
        simpa [MulAut.conj_apply] using this
      have e2 : b⁻¹ * (a * g * a⁻¹) * b = g := by
        rw [e]
        group
      calc g * (b⁻¹ * a) = b⁻¹ * (a * g * a⁻¹) * b * (b⁻¹ * a) := by rw [e2]
        _ = b⁻¹ * a * g := by group
    rw [hcen, Subgroup.mem_bot, inv_mul_eq_one] at hz
    exact hz.symm
  let e : Y ≃* (MulAut.conj : Y →* MulAut Y).range := MonoidHom.ofInjective hconj
  let Ψ : P →* (MulAut.conj : Y →* MulAut Y).range :=
    φ.codRestrict (MulAut.conj : Y →* MulAut Y).range (fun p => hφin p)
  let θ : P →* Y := e.symm.toMonoidHom.comp Ψ
  have hΨi : Function.Injective Ψ := fun p q hpq => hφi (congrArg Subtype.val hpq)
  have hθi : Function.Injective θ := e.symm.injective.comp hΨi
  have hE'c : IsMulCommutative (θ.range) := by
    refine ⟨⟨fun x y => ?_⟩⟩
    obtain ⟨p, hp⟩ := MonoidHom.mem_range.mp x.2
    obtain ⟨q, hq⟩ := MonoidHom.mem_range.mp y.2
    apply Subtype.ext
    show (x : Y) * (y : Y) = (y : Y) * (x : Y)
    have hpq : p * q = q * p := hPc.is_comm.comm p q
    rw [← hp, ← hq, ← map_mul, ← map_mul, hpq]
  have hE'e : ∀ x ∈ θ.range, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨p, hp⟩ := MonoidHom.mem_range.mp hx
    rw [← hp, ← map_pow, hPe p, map_one]
  have hE' : CFSG.Assembly.IsElemAbelian 3 (θ.range) := ⟨hE'c, hE'e⟩
  have hE'card : Nat.card (θ.range) = 9 := by
    rw [Nat.card_congr (MonoidHom.ofInjective hθi).symm.toEquiv, hP9]
  have hbdd := CFSG.RankThreeEvenClassification.Helpers.pRank_bddAbove 3 Nat.prime_three
    (⊤ : Subgroup Y)
  have h2 : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Y) := by
    apply le_csSup hbdd
    exact ⟨θ.range, le_top, hE', by rw [hE'card]; norm_num⟩
  omega

private theorem map_conj_eq_or_eq {K K' : Subgroup G} {m : G} (hS : Sec18Std G A M)
    (hKc : K ∈ oTwoComponentsIn M) (hm : m ∈ M) (hK' : K' = K.map (MulAut.conj m).toMonoidHom)
    (hne : K' ≠ K) {g : G} (hg : g ∈ M) :
    K.map (MulAut.conj g).toMonoidHom = K ∨ K.map (MulAut.conj g).toMonoidHom = K' := by
  have hS2 := Sec18.Item185Proof.ncard_conj_le_two hS hKc
  have hsub : ({K, K'} : Set (Subgroup G)) ⊆
      {K'' : Subgroup G | ∃ g ∈ M, K'' = K.map (MulAut.conj g).toMonoidHom} := by
    intro x hx
    rcases hx with rfl | rfl
    · exact ⟨1, M.one_mem, by ext y; simp⟩
    · exact ⟨m, hm, hK'⟩
  have heq := Set.eq_of_subset_of_ncard_le hsub
    (by rw [Set.ncard_pair hne.symm]; exact hS2) (Set.toFinite _)
  have hmem : K.map (MulAut.conj g).toMonoidHom ∈
      {K'' : Subgroup G | ∃ g ∈ M, K'' = K.map (MulAut.conj g).toMonoidHom} := ⟨g, hg, rfl⟩
  rw [← heq] at hmem
  rcases hmem with h1 | h1
  · exact Or.inl h1
  · exact Or.inr h1

private theorem isL3OddType_of_conj {K : Subgroup G} (m : G)
    (hL3 : IsL3OddType (K ⧸ CFSG.pCore 2 K)) :
    IsL3OddType (K.map (MulAut.conj m).toMonoidHom ⧸
      CFSG.pCore 2 (K.map (MulAut.conj m).toMonoidHom)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn, ⟨e⟩⟩ := hL3
  let ι : K ≃* K.map (MulAut.conj m).toMonoidHom := MulEquiv.subgroupMap (MulAut.conj m) K
  let q : K ⧸ CFSG.pCore 2 K ≃*
      K.map (MulAut.conj m).toMonoidHom ⧸ CFSG.pCore 2 (K.map (MulAut.conj m).toMonoidHom) :=
    QuotientGroup.congr (CFSG.pCore 2 K) (CFSG.pCore 2 (K.map (MulAut.conj m).toMonoidHom))
      ι (CFSG.pCore_map_iso 2 ι)
  exact ⟨n, hn, ⟨q.symm.trans e⟩⟩

private theorem comm_mem_of_barAut_eq_one {K' : Subgroup G} {b : G}
    (hb : b ∈ Subgroup.normalizer (K' : Set G)) (h1 : Sec3.Sims321.barAut K' ⟨b, hb⟩ = 1)
    {k : G} (hk : k ∈ K') : b * k * b⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K' := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 := congrArg (fun φ' : MulAut (K' ⧸ CFSG.pCore 2 K') =>
    φ' (QuotientGroup.mk (⟨k, hk⟩ : K'))) h1
  simp only [MulAut.one_apply] at h2
  rw [Sec3.Sims321.barAut_mk] at h2
  have h3 := QuotientGroup.eq.mp h2
  have h4 := (mem_pCore_iff _).mp h3
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h4
  have e : b * k * b⁻¹ * k⁻¹ = k * ((b * k * b⁻¹)⁻¹ * k)⁻¹ * k⁻¹ := by group
  have ht' : ((b * k * b⁻¹)⁻¹ * k)⁻¹ ∈ CFSG.Open.pCoreOf 2 K' :=
    (CFSG.Open.pCoreOf 2 K').inv_mem h4
  rw [e]
  have hnorm := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K' hk
  exact (Subgroup.mem_normalizer_iff.mp hnorm _).mp ht'

private theorem card_le_three_of_elemAbelian {Y : Type} [Group Y] [Finite Y]
    (hpR : CFSG.Open.pRank 3 (⊤ : Subgroup Y) ≤ 1) (E : Subgroup Y)
    (hE : CFSG.Assembly.IsElemAbelian 3 E) : Nat.card E ≤ 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP : IsPGroup 3 E := fun g => ⟨1, Subtype.ext (by
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact hE.2 (g : Y) g.2)⟩
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hle : n ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Y) :=
    le_csSup (CFSG.RankThreeEvenClassification.Helpers.pRank_bddAbove 3 Nat.prime_three
      (⊤ : Subgroup Y)) ⟨E, le_top, hE, hn⟩
  have hn1 : n ≤ 1 := le_trans hle hpR
  rw [hn]
  calc 3 ^ n ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hn1
    _ = 3 := by norm_num

private theorem isElemAbelian_map_of {X Y : Type} [Group X] [Group Y] (f : X →* Y)
    (F : Subgroup X) (hF : CFSG.Assembly.IsElemAbelian 3 F) :
    CFSG.Assembly.IsElemAbelian 3 (F.map f) := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
  · obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp x.2
    obtain ⟨b, hb, hby⟩ := Subgroup.mem_map.mp y.2
    apply Subtype.ext
    have hcomm : a * b = b * a := congrArg Subtype.val (hF.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    show (x : Y) * (y : Y) = (y : Y) * (x : Y)
    rw [← hax, ← hby, ← map_mul, ← map_mul, hcomm]
  · intro x hx
    obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp hx
    rw [← hax, ← map_pow, hF.2 a ha, map_one]

private theorem bezout_three_of_not_dvd {k : ℤ} (hk : ¬ (3 : ℤ) ∣ k) :
    ∃ u v : ℤ, k * u + 3 * v = 1 := by
  have h1 : k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases h1 with h1 | h1
  · exact ⟨1, -(k / 3), by omega⟩
  · exact ⟨2, -(2 * (k / 3) + 1), by omega⟩

private theorem eq_zpow_of_zpow_ne_one {c : G} (hc3 : orderOf c = 3) (k : ℤ) (hne : c ^ k ≠ 1) :
    ∃ u : ℤ, c = (c ^ k) ^ u := by
  have hc3' : c ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, ← hc3, pow_orderOf_eq_one]
  have hnd : ¬ (3 : ℤ) ∣ k := by
    rintro ⟨m, rfl⟩
    apply hne
    rw [zpow_mul, hc3', one_zpow]
  obtain ⟨u, v, huv⟩ := bezout_three_of_not_dvd hnd
  have e : c = (c ^ k) ^ u * (c ^ (3 : ℤ)) ^ v := by
    rw [← zpow_mul, ← zpow_mul, ← zpow_add, huv, zpow_one]
  exact ⟨u, e.trans (by rw [hc3', one_zpow, mul_one])⟩

private theorem zpow_eq_one_of_mem_of_not_mem {H : Subgroup G} {c : G} (hc3 : orderOf c = 3)
    (hcH : c ∉ H) (k : ℤ) (hk : c ^ k ∈ H) : c ^ k = 1 := by
  by_contra hne
  obtain ⟨u, hu⟩ := eq_zpow_of_zpow_ne_one hc3 k hne
  apply hcH
  rw [hu]
  exact H.zpow_mem hk u

private theorem mem_of_zpow_ne_one {H : Subgroup G} {c : G} (hc3 : orderOf c = 3) (k : ℤ)
    (hk : c ^ k ∈ H) (hne : c ^ k ≠ 1) : c ∈ H := by
  obtain ⟨u, hu⟩ := eq_zpow_of_zpow_ne_one hc3 k hne
  rw [hu]
  exact H.zpow_mem hk u

private theorem inf_pCoreOf_eq_one_of_E27 (h : Hyp1921 G A M N L) {a : G} (ha : a ∈ A)
    (haO : a ∈ CFSG.Open.pCoreOf 2 M) : a = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hne
  exact not_mem_of_isPGroup_two (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M)
    (orderOf_eq_prime (h.isE27.1.2 a ha) hne) haO

private theorem card_inf_le_three (h : Hyp1921 G A M N L) (hKc : K ∈ oTwoComponentsIn M)
    (hL3 : IsL3OddType (K ⧸ CFSG.pCore 2 K)) {S : Subgroup G}
    (hSdef : S = K ⊔ CFSG.Open.pCoreOf 2 M) : Nat.card (A ⊓ S : Subgroup G) ≤ 3 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKM : K ≤ M := le_of_mem_oTwoComponentsIn hKc
  have hKS : K ≤ S := by rw [hSdef]; exact le_sup_left
  have hOS : CFSG.Open.pCoreOf 2 M ≤ S := by rw [hSdef]; exact le_sup_right
  have hSM : S ≤ M := by
    rw [hSdef]
    exact sup_le hKM (CFSG.LieType.BorelTits.pCoreOf_le 2 M)
  have hprod : (S : Set G) = (K : Set G) * (CFSG.Open.pCoreOf 2 M : Set G) := by
    rw [hSdef]
    exact Subgroup.coe_mul_of_left_le_normalizer_right K _
      (fun k hk => CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M (hKM hk))
  haveI hOSn : ((CFSG.Open.pCoreOf 2 M).subgroupOf S).Normal := by
    rw [hSdef]
    exact Subgroup.normal_subgroupOf_sup_of_le_normalizer
      (fun k hk => CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M (hKM hk))
  let g : K →* S ⧸ (CFSG.Open.pCoreOf 2 M).subgroupOf S :=
    (QuotientGroup.mk' ((CFSG.Open.pCoreOf 2 M).subgroupOf S)).comp (Subgroup.inclusion hKS)
  have hker : g.ker = CFSG.pCore 2 K := by
    ext x
    rw [MonoidHom.mem_ker, mem_pCore_iff, pCoreOf_eq_inf_of_mem hKc, Subgroup.mem_inf]
    constructor
    · intro hx
      refine ⟨x.2, ?_⟩
      have hx' : (Subgroup.inclusion hKS x) ∈ (CFSG.Open.pCoreOf 2 M).subgroupOf S :=
        (QuotientGroup.eq_one_iff (Subgroup.inclusion hKS x)).mp hx
      exact Subgroup.mem_subgroupOf.mp hx'
    · rintro ⟨-, hx⟩
      exact (QuotientGroup.eq_one_iff (Subgroup.inclusion hKS x)).mpr
        (Subgroup.mem_subgroupOf.mpr hx)
  have hsurj : Function.Surjective g := by
    intro s
    obtain ⟨s', rfl⟩ := QuotientGroup.mk_surjective s
    have hs : (s' : G) ∈ (K : Set G) * (CFSG.Open.pCoreOf 2 M : Set G) := by
      rw [← hprod]
      exact s'.2
    obtain ⟨k, hk, o, ho, hko⟩ := hs
    refine ⟨⟨k, hk⟩, ?_⟩
    refine QuotientGroup.eq.mpr ?_
    have e : ((Subgroup.inclusion hKS ⟨k, hk⟩)⁻¹ * s' : S) = ⟨o, hOS ho⟩ := by
      apply Subtype.ext
      show k⁻¹ * (s' : G) = o
      rw [← hko]
      group
    rw [e]
    exact ho
  have hAO : ∀ a ∈ A, a ∈ CFSG.Open.pCoreOf 2 M → a = 1 := fun a ha haO =>
    inf_pCoreOf_eq_one_of_E27 h ha haO
  let ψ : ((A ⊓ S : Subgroup G).subgroupOf S) →* S ⧸ (CFSG.Open.pCoreOf 2 M).subgroupOf S :=
    (QuotientGroup.mk' ((CFSG.Open.pCoreOf 2 M).subgroupOf S)).comp
      ((A ⊓ S : Subgroup G).subgroupOf S).subtype
  have hψi : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro p hp
    have hp' : (p : S) ∈ (CFSG.Open.pCoreOf 2 M).subgroupOf S :=
      (QuotientGroup.eq_one_iff (p : S)).mp hp
    have hpA : ((p : S) : G) ∈ A :=
      (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp p.2)).1
    have h1 := hAO _ hpA (Subgroup.mem_subgroupOf.mp hp')
    exact Subtype.ext (Subtype.ext h1)
  have hcardψ : Nat.card ψ.range = Nat.card ((A ⊓ S : Subgroup G).subgroupOf S) :=
    Nat.card_congr (MonoidHom.ofInjective hψi).symm.toEquiv
  have hcardD' : Nat.card ((A ⊓ S : Subgroup G).subgroupOf S) = Nat.card (A ⊓ S : Subgroup G) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : A ⊓ S ≤ S)).toEquiv
  let e : K ⧸ CFSG.pCore 2 K ≃* S ⧸ (CFSG.Open.pCoreOf 2 M).subgroupOf S :=
    (QuotientGroup.quotientMulEquivOfEq hker).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective g hsurj)
  have hXcomm : ∀ p q : ((A ⊓ S : Subgroup G).subgroupOf S), p * q = q * p := by
    intro p q
    apply Subtype.ext
    apply Subtype.ext
    have hpA : ((p : S) : G) ∈ A := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp p.2)).1
    have hqA : ((q : S) : G) ∈ A := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp q.2)).1
    show ((p : S) : G) * ((q : S) : G) = ((q : S) : G) * ((p : S) : G)
    exact congrArg Subtype.val
      (h.isE27.1.1.is_comm.comm (⟨((p : S) : G), hpA⟩ : ↥A) ⟨((q : S) : G), hqA⟩)
  have hXexp : ∀ p : ((A ⊓ S : Subgroup G).subgroupOf S), p ^ 3 = 1 := fun p => by
    have hpA : ((p : S) : G) ∈ A := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp p.2)).1
    exact Subtype.ext (Subtype.ext (by simpa using h.isE27.1.2 _ hpA))
  have hTop : CFSG.Assembly.IsElemAbelian 3 (⊤ : Subgroup ((A ⊓ S : Subgroup G).subgroupOf S)) := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x _ => hXexp x⟩
    exact Subtype.ext (hXcomm x.1 y.1)
  have hψel : CFSG.Assembly.IsElemAbelian 3 ψ.range := by
    rw [MonoidHom.range_eq_map]
    exact isElemAbelian_map_of ψ ⊤ hTop
  have hEel : CFSG.Assembly.IsElemAbelian 3 (ψ.range.map e.symm.toMonoidHom) :=
    isElemAbelian_map_of _ _ hψel
  have hcardE : Nat.card (ψ.range.map e.symm.toMonoidHom) = Nat.card ψ.range :=
    Subgroup.card_map_of_injective (f := e.symm.toMonoidHom) e.symm.injective
  have hpR : CFSG.Open.pRank 3 (⊤ : Subgroup (K ⧸ CFSG.pCore 2 K)) ≤ 1 := by
    obtain ⟨n, hn, ⟨e0⟩⟩ := hL3
    exact Sec20.kFactL3OddThreeRank n hn _ ⟨e0⟩
  have h3 := card_le_three_of_elemAbelian hpR _ hEel
  omega

private theorem false_of_E81_gen (h : Hyp1921 G A M N L) {x : G} (hxM : x ∈ M)
    (hx3 : orderOf x = 3)
    (hcomm : ∀ a ∈ A, a * x * a⁻¹ * x⁻¹ ∈ CFSG.Open.pCoreOf 2 M)
    (hinter : ∀ a ∈ A, ∀ j : ℤ, (x ^ j)⁻¹ * a ∈ CFSG.Open.pCoreOf 2 M → a = 1) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAM : A ≤ M := h.le_M
  have hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (h.isE27.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := fun a ha => h.isE27.1.2 a ha
  have hx3' : x ^ 3 = 1 := by
    rw [← hx3]
    exact pow_orderOf_eq_one x
  set AM : Subgroup M := A.subgroupOf M with hAMdef
  set xM : M := ⟨x, hxM⟩ with hxMdef
  have hxM3 : xM ^ 3 = 1 := Subtype.ext (by simpa [hxMdef] using hx3')
  set H : Subgroup (M ⧸ CFSG.pCore 2 M) := AM.map (QuotientGroup.mk' (CFSG.pCore 2 M))
    with hHdef
  set L' : Subgroup (M ⧸ CFSG.pCore 2 M) :=
    Subgroup.zpowers (QuotientGroup.mk' (CFSG.pCore 2 M) xM) with hLdef
  have hg3 : QuotientGroup.mk' (CFSG.pCore 2 M) xM ^ 3 = 1 := by
    rw [← map_pow, hxM3, map_one]
  have hmkA : ∀ a : M, a ∈ AM → Commute (QuotientGroup.mk' (CFSG.pCore 2 M) a)
      (QuotientGroup.mk' (CFSG.pCore 2 M) xM) := by
    intro a ha
    rw [commute_mk_iff]
    exact hcomm (a : G) (Subgroup.mem_subgroupOf.mp ha)
  have hcHL : ∀ u ∈ H, ∀ v ∈ L', Commute u v := by
    intro u hu v hv
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hu
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    exact (hmkA a ha).zpow_right j
  have hHL : H ⊓ L' = ⊥ := by
    rw [eq_bot_iff]
    rintro w ⟨hwH, hwL⟩
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hwH
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hwL
    have hmk : QuotientGroup.mk' (CFSG.pCore 2 M) (xM ^ j) =
        QuotientGroup.mk' (CFSG.pCore 2 M) a := by
      rw [map_zpow]
      exact hj
    have h1 : (xM ^ j)⁻¹ * a ∈ CFSG.pCore 2 M := (QuotientGroup.eq.mp hmk)
    have h2 := (mem_pCore_iff _).mp h1
    have h3 : (x ^ j)⁻¹ * ((a : M) : G) ∈ CFSG.Open.pCoreOf 2 M := by
      simpa [hxMdef] using h2
    have ha1 : ((a : M) : G) = 1 := hinter _ (Subgroup.mem_subgroupOf.mp ha) j h3
    have ha1' : a = 1 := Subtype.ext ha1
    rw [Subgroup.mem_bot, ha1', map_one]
  set S' : Set (M ⧸ CFSG.pCore 2 M) := (H : Set (M ⧸ CFSG.pCore 2 M)) ∪ (L' : Set _) with hSdef'
  have hSc : S'.Pairwise Commute := by
    intro u hu v hv _
    rcases hu with hu | hu <;> rcases hv with hv | hv
    · obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hu
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hv
      rw [commute_mk_iff]
      have e : ((a : M) : G) * ((b : M) : G) * ((a : M) : G)⁻¹ * ((b : M) : G)⁻¹ = 1 := by
        rw [hAab _ (Subgroup.mem_subgroupOf.mp ha) _ (Subgroup.mem_subgroupOf.mp hb)]
        group
      rw [e]
      exact one_mem _
    · exact hcHL _ hu _ hv
    · exact (hcHL _ hv _ hu).symm
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
      exact (Commute.refl _).zpow_zpow i j
  set E : Subgroup (M ⧸ CFSG.pCore 2 M) := Subgroup.closure S' with hEdef
  have hEab : IsMulCommutative E := Subgroup.isMulCommutative_closure hSc
  have hEexp : ∀ e ∈ E, e ^ 3 = 1 := by
    intro e he
    refine Subgroup.closure_induction (p := fun e _ => e ^ 3 = 1) ?_ ?_ ?_ ?_ he
    · intro u hu
      rcases hu with hu | hu
      · obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hu
        have ha3 : a ^ 3 = 1 :=
          Subtype.ext (by simpa using hA3 _ (Subgroup.mem_subgroupOf.mp ha))
        rw [← map_pow, ha3, map_one]
      · obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hg3, one_zpow]
    · simp
    · intro u v hu hv hu' hv'
      have huv : Commute u v := congrArg Subtype.val (hEab.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
      rw [huv.mul_pow, hu', hv', one_mul]
    · intro u hu hu'
      rw [inv_pow, hu', inv_one]
  let F : (AM × L') → E := fun p => ⟨QuotientGroup.mk' (CFSG.pCore 2 M) (p.1 : M) * (p.2 : _), by
    refine mul_mem (Subgroup.subset_closure (Or.inl ?_)) (Subgroup.subset_closure (Or.inr p.2.2))
    exact Subgroup.mem_map_of_mem _ p.1.2⟩
  have hFinj : Function.Injective F := by
    rintro ⟨⟨a1, ha1⟩, ⟨l1, hl1⟩⟩ ⟨⟨a2, ha2⟩, ⟨l2, hl2⟩⟩ heq
    have heq' : QuotientGroup.mk' (CFSG.pCore 2 M) a1 * l1 =
        QuotientGroup.mk' (CFSG.pCore 2 M) a2 * l2 := congrArg Subtype.val heq
    have hY : QuotientGroup.mk' (CFSG.pCore 2 M) a2 ∈ H := Subgroup.mem_map_of_mem _ ha2
    have hX : QuotientGroup.mk' (CFSG.pCore 2 M) a1 ∈ H := Subgroup.mem_map_of_mem _ ha1
    have hu : (QuotientGroup.mk' (CFSG.pCore 2 M) a2)⁻¹ *
        QuotientGroup.mk' (CFSG.pCore 2 M) a1 = l2 * l1⁻¹ := by
      have hX' : QuotientGroup.mk' (CFSG.pCore 2 M) a1 =
          QuotientGroup.mk' (CFSG.pCore 2 M) a2 * l2 * l1⁻¹ := by
        rw [← heq']
        group
      rw [hX']
      group
    have hmem : (QuotientGroup.mk' (CFSG.pCore 2 M) a2)⁻¹ *
        QuotientGroup.mk' (CFSG.pCore 2 M) a1 ∈ H ⊓ L' :=
      ⟨H.mul_mem (H.inv_mem hY) hX, by rw [hu]; exact L'.mul_mem hl2 (L'.inv_mem hl1)⟩
    rw [hHL, Subgroup.mem_bot] at hmem
    have hmka : QuotientGroup.mk' (CFSG.pCore 2 M) a1 =
        QuotientGroup.mk' (CFSG.pCore 2 M) a2 := by
      rw [inv_mul_eq_one] at hmem
      exact hmem.symm
    have hl : l2 * l1⁻¹ = 1 := by
      rw [← hu, hmem]
    have hl12 : l1 = l2 := (mul_inv_eq_one.mp hl).symm
    have hdiv : ((a1 : M) : G)⁻¹ * ((a2 : M) : G) ∈ A :=
      mul_mem (inv_mem (Subgroup.mem_subgroupOf.mp ha1)) (Subgroup.mem_subgroupOf.mp ha2)
    have hdivO : ((a1 : M) : G)⁻¹ * ((a2 : M) : G) ∈ CFSG.Open.pCoreOf 2 M := by
      have h1 := (mem_pCore_iff _).mp (QuotientGroup.eq.mp hmka)
      simpa using h1
    have hdiv1 := inf_pCoreOf_eq_one_of_E27 h hdiv hdivO
    have ha12 : (a1 : M) = (a2 : M) := by
      have : ((a1 : M) : G) = ((a2 : M) : G) := by
        rw [inv_mul_eq_one] at hdiv1
        exact hdiv1
      exact Subtype.ext this
    exact Prod.ext (Subtype.ext ha12) (Subtype.ext hl12)
  have hcardAM : Nat.card AM = 27 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAM).toEquiv]
    exact h.isE27.2
  have hcardL : Nat.card L' = 3 := by
    rw [hLdef, Nat.card_zpowers]
    apply orderOf_eq_prime hg3
    intro h1
    apply not_mem_of_isPGroup_two (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M) hx3
    have h2 : xM ∈ CFSG.pCore 2 M := (QuotientGroup.eq_one_iff xM).mp h1
    exact (mem_pCore_iff xM).mp h2
  have hcard : Nat.card (AM × L') = 81 := by
    rw [Nat.card_prod, hcardAM, hcardL]
  have hle := Nat.card_le_card_of_injective F hFinj
  have hEel : CFSG.Assembly.IsElemAbelian 3 E := ⟨hEab, hEexp⟩
  have h27 := h.card_le_of_isElemAbelian_quotient hEel
  omega

private theorem comm_mem_of_barAut_fix {K' : Subgroup G} {b : G}
    (hb : b ∈ Subgroup.normalizer (K' : Set G)) {z : G} (hz : z ∈ K')
    (h1 : Sec3.Sims321.barAut K' ⟨b, hb⟩ (QuotientGroup.mk' (CFSG.pCore 2 K') ⟨z, hz⟩) =
      QuotientGroup.mk' (CFSG.pCore 2 K') ⟨z, hz⟩) :
    b * z * b⁻¹ * z⁻¹ ∈ CFSG.Open.pCoreOf 2 K' := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : Sec3.Sims321.barAut K' ⟨b, hb⟩ (QuotientGroup.mk (⟨z, hz⟩ : K')) =
      QuotientGroup.mk (⟨z, hz⟩ : K') := h1
  rw [Sec3.Sims321.barAut_mk] at h2
  have h3 := QuotientGroup.eq.mp h2
  have h4 := (mem_pCore_iff _).mp h3
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h4
  have e : b * z * b⁻¹ * z⁻¹ = z * ((b * z * b⁻¹)⁻¹ * z)⁻¹ * z⁻¹ := by group
  have ht' : ((b * z * b⁻¹)⁻¹ * z)⁻¹ ∈ CFSG.Open.pCoreOf 2 K' :=
    (CFSG.Open.pCoreOf 2 K').inv_mem h4
  rw [e]
  have hnorm := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K' hz
  exact (Subgroup.mem_normalizer_iff.mp hnorm _).mp ht'

private theorem exists_lift_fixed {K' : Subgroup G} (α : MulAut (K' ⧸ CFSG.pCore 2 K'))
    {y : K' ⧸ CFSG.pCore 2 K'} (hy3 : orderOf y = 3) (hyf : α y = y) :
    ∃ z : G, ∃ hz : z ∈ K', orderOf z = 3 ∧
      α (QuotientGroup.mk' (CFSG.pCore 2 K') ⟨z, hz⟩) =
        QuotientGroup.mk' (CFSG.pCore 2 K') ⟨z, hz⟩ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective y
  have hdvd : 3 ∣ orderOf k := by
    have h1 := orderOf_map_dvd (QuotientGroup.mk' (CFSG.pCore 2 K')) k
    have h2 : orderOf ((QuotientGroup.mk' (CFSG.pCore 2 K')) k) = 3 := hy3
    rw [h2] at h1
    exact h1
  obtain ⟨z', hz'⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.zpowers k)) 3
    (by rw [Nat.card_zpowers]; exact hdvd)
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp z'.2
  have hw : ((z' : K') : G) ∈ K' := (z' : K').2
  refine ⟨((z' : K') : G), hw, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz']
  · have hwk : (⟨((z' : K') : G), hw⟩ : K') = k ^ j := by
      apply Subtype.ext
      have := congrArg Subtype.val hj
      simpa using this.symm
    have hyf' : α (QuotientGroup.mk' (CFSG.pCore 2 K') k) = QuotientGroup.mk' (CFSG.pCore 2 K') k :=
      hyf
    rw [hwk, map_zpow, map_zpow, hyf']

private theorem exists_orderOf_three_of_equiv {X Y : Type} [Group X] [Group Y] (f : X ≃* Y)
    (hX : ∃ x : X, orderOf x = 3) : ∃ y : Y, orderOf y = 3 := by
  obtain ⟨x, hx⟩ := hX
  exact ⟨f x, by rw [MulEquiv.orderOf_eq]; exact hx⟩

private theorem exists_orderOf_three_of_isL3OddType {X : Type} [Group X]
    (hX : IsL3OddType X) : ∃ y : X, orderOf y = 3 := by
  obtain ⟨n, -, ⟨e⟩⟩ := hX
  have h1 : ∃ x : projSL 3 (GaloisField 2 n), orderOf x = 3 :=
    exists_orderOf_three_of_equiv
      (CFSG.RankThree.PartOne.S15K.projSLEquivProjectiveSL 3 (GaloisField 2 n)).symm
      ⟨_, CFSG.AGLEmbeddingD2.L34BetaHPara.orderOf_proj_m3⟩
  exact exists_orderOf_three_of_equiv e.symm h1

private theorem inf_le_zpowers_of_irreducible (h : Hyp1921 G A M N L) (hF : Facts1922 G A M N L c)
    {S : Subgroup G} (hcard : Nat.card (A ⊓ S : Subgroup G) ≤ 3)
    (hWD : ∀ w ∈ planeGroup A L c, ∀ d ∈ A ⊓ S, w * d * w⁻¹ ∈ A ⊓ S)
    (hWcomm : ∀ w ∈ planeGroup A L c, ∀ k : ℤ, w * c ^ k = c ^ k * w) :
    ∀ d ∈ A ⊓ S, d ∈ Subgroup.zpowers c := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcA : c ∈ A := (step1923_W h hF).mem
  have hcB : c ∉ A ⊓ L := (step1923_W h hF).not_mem
  have hc3 : orderOf c = 3 := hF.orderOf_c
  have hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (h.isE27.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hcom : ∀ a ∈ A ⊓ L, ∀ k : ℤ, c ^ k * a = a * c ^ k := fun a ha k =>
    hAab _ (zpow_mem hcA k) a (Subgroup.mem_inf.mp ha).1
  let B₀ : Subgroup (A ⊓ L : Subgroup G) :=
    { carrier := {b | ∃ i : ℤ, c ^ i * (b : G) ∈ A ⊓ S}
      mul_mem' := by
        rintro a b ⟨i, hi⟩ ⟨j, hj⟩
        refine ⟨i + j, ?_⟩
        have ha : (a : G) ∈ A ⊓ L := a.2
        have e : c ^ (i + j) * ((a * b : ↥(A ⊓ L)) : G) =
            (c ^ i * (a : G)) * (c ^ j * (b : G)) := by
          rw [Subgroup.coe_mul]
          calc c ^ (i + j) * ((a : G) * (b : G)) = c ^ i * (c ^ j * (a : G)) * (b : G) := by
                rw [zpow_add]
                simp only [mul_assoc]
            _ = c ^ i * ((a : G) * c ^ j) * (b : G) := by rw [hcom a ha j]
            _ = (c ^ i * (a : G)) * (c ^ j * (b : G)) := by simp only [mul_assoc]
        rw [e]
        exact mul_mem hi hj
      one_mem' := ⟨0, by simpa using (A ⊓ S).one_mem⟩
      inv_mem' := by
        rintro a ⟨i, hi⟩
        refine ⟨-i, ?_⟩
        have ha : (a : G) ∈ A ⊓ L := a.2
        have e : c ^ (-i) * ((a : G))⁻¹ = (c ^ i * (a : G))⁻¹ := by
          rw [mul_inv_rev, ← zpow_neg]
          exact hcom _ (inv_mem ha) (-i)
        show c ^ (-i) * ((a : G))⁻¹ ∈ A ⊓ S
        rw [e]
        exact inv_mem hi }
  have hmoveB : ∀ w ∈ planeGroup A L c,
      ∀ hwN : w ∈ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G),
      ∀ b : (A ⊓ L : Subgroup G), b ∈ B₀ →
        (⟨w * b * w⁻¹, (Subgroup.mem_normalizer_iff.mp hwN b).mp b.2⟩ :
          (A ⊓ L : Subgroup G)) ∈ B₀ := by
    rintro w hw hwN b ⟨i, hi⟩
    refine ⟨i, ?_⟩
    have e : c ^ i * (w * (b : G) * w⁻¹) = w * (c ^ i * (b : G)) * w⁻¹ := by
      calc c ^ i * (w * (b : G) * w⁻¹) = (c ^ i * w) * (b : G) * w⁻¹ := by group
        _ = (w * c ^ i) * (b : G) * w⁻¹ := by rw [hWcomm w hw i]
        _ = w * (c ^ i * (b : G)) * w⁻¹ := by group
    show c ^ i * (w * (b : G) * w⁻¹) ∈ A ⊓ S
    rw [e]
    exact hWD w hw _ hi
  have hinv : ∀ ψ ∈ Sec4.autIn (planeGroup A L c) (A ⊓ L), B₀.map ψ.toMonoidHom = B₀ := by
    intro ψ hψ
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hψ
    have hxW : (x : G) ∈ planeGroup A L c :=
      (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hx)).1
    have hxN : (x : G) ∈ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) := x.2
    apply le_antisymm
    · rintro _ ⟨b, hb, rfl⟩
      exact hmoveB x hxW hxN b hb
    · intro b hb
      have hx'W : (x : G)⁻¹ ∈ planeGroup A L c := inv_mem hxW
      have hx'N : (x : G)⁻¹ ∈ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) :=
        inv_mem hxN
      refine ⟨⟨(x : G)⁻¹ * b * ((x : G)⁻¹)⁻¹, (Subgroup.mem_normalizer_iff.mp hx'N b).mp b.2⟩,
        hmoveB (x : G)⁻¹ hx'W hx'N b hb, ?_⟩
      apply Subtype.ext
      show (x : G) * ((x : G)⁻¹ * (b : G) * ((x : G)⁻¹)⁻¹) * (x : G)⁻¹ = (b : G)
      group
  rcases (step1923_W h hF).irreducible B₀ hinv with hbot | htop
  ·
    intro d hd
    have hdA : d ∈ A := (Subgroup.mem_inf.mp hd).1
    have hcN' : c ∈ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) := by
      refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => ?_, fun hx => ?_⟩
      · have hxA := (Subgroup.mem_inf.mp hx).1
        have e : c * x * c⁻¹ = x := by
          rw [hAab c hcA x hxA]
          group
        rw [e]
        exact hx
      · have hyA := (Subgroup.mem_inf.mp hx).1
        have e2 : c⁻¹ * (c * x * c⁻¹) * c = c * x * c⁻¹ := by
          have hc' := hAab c hcA (c * x * c⁻¹) hyA
          calc c⁻¹ * (c * x * c⁻¹) * c = c⁻¹ * ((c * x * c⁻¹) * c) := by group
            _ = c⁻¹ * (c * (c * x * c⁻¹)) := by rw [← hc']
            _ = c * x * c⁻¹ := by group
        have e3 : x = c⁻¹ * (c * x * c⁻¹) * c := by group
        rw [e3, e2]
        exact hx
    have hle : Subgroup.zpowers c ≤ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) :=
      Subgroup.zpowers_le.mpr hcN'
    have hdecomp : ∀ a ∈ A, ∃ i : ℤ, ∃ b : G, b ∈ A ⊓ L ∧ a = c ^ i * b := by
      intro a ha
      have ha' : a ∈ Subgroup.zpowers c ⊔ (A ⊓ L) := by
        rw [← hF.eq_sup]
        exact ha
      have hset := Subgroup.coe_mul_of_left_le_normalizer_right (Subgroup.zpowers c) (A ⊓ L) hle
      have hmem : a ∈ (↑(Subgroup.zpowers c ⊔ (A ⊓ L)) : Set G) := ha'
      rw [hset] at hmem
      obtain ⟨u, hu, b, hb, rfl⟩ := hmem
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
      exact ⟨i, b, hb, rfl⟩
    obtain ⟨i, b, hb, rfl⟩ := hdecomp d hdA
    have hbB₀ : (⟨b, hb⟩ : (A ⊓ L : Subgroup G)) ∈ B₀ := ⟨i, hd⟩
    rw [hbot, Subgroup.mem_bot] at hbB₀
    have hb1 : b = 1 := congrArg Subtype.val hbB₀
    rw [hb1, mul_one]
    exact Subgroup.mem_zpowers_iff.mpr ⟨i, rfl⟩
  ·
    exfalso
    have hall : ∀ b : (A ⊓ L : Subgroup G), ∃ i : ℤ, c ^ i * (b : G) ∈ A ⊓ S := fun b => by
      have hb : b ∈ B₀ := by
        rw [htop]
        exact Subgroup.mem_top b
      exact hb
    choose ι hι using hall
    let F : (A ⊓ L : Subgroup G) → (A ⊓ S : Subgroup G) := fun b => ⟨c ^ ι b * (b : G), hι b⟩
    have hFinj : Function.Injective F := by
      intro b b' hbb'
      have e1 : c ^ ι b * (b : G) = c ^ ι b' * (b' : G) := congrArg Subtype.val hbb'
      have e2 : c ^ (ι b - ι b') * (b : G) = (b' : G) := by
        rw [show ι b - ι b' = -ι b' + ι b by ring, zpow_add, mul_assoc, e1, ← mul_assoc,
          ← zpow_add, neg_add_cancel, zpow_zero, one_mul]
      have hmem : c ^ (ι b - ι b') ∈ A ⊓ L := by
        have : c ^ (ι b - ι b') = (b' : G) * (b : G)⁻¹ := eq_mul_inv_of_mul_eq e2
        rw [this]
        exact mul_mem b'.2 (inv_mem b.2)
      have hz1 := zpow_eq_one_of_mem_of_not_mem hc3 hcB _ hmem
      rw [hz1, one_mul] at e2
      exact Subtype.ext e2
    have hcardle := Nat.card_le_card_of_injective F hFinj
    have h9 : Nat.card (A ⊓ L : Subgroup G) = 9 := hF.card
    omega

private theorem false_of_inf_eq_bot (kf4 : KF4) (h : Hyp1921 G A M N L) (hF : Facts1922 G A M N L c)
    (hKc : K ∈ oTwoComponentsIn M) (hL3 : IsL3OddType (K ⧸ CFSG.pCore 2 K))
    (hone : ∀ b ∈ A ⊓ L, ∀ k ∈ K, b * k * b⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K)
    {S : Subgroup G} (hSdef : S = K ⊔ CFSG.Open.pCoreOf 2 M)
    (hcN : c ∈ Subgroup.normalizer (K : Set G)) (hD1 : ∀ d ∈ A ⊓ S, d = 1) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcA : c ∈ A := (step1923_W h hF).mem
  have hc3 : orderOf c = 3 := hF.orderOf_c
  have hKM : K ≤ M := le_of_mem_oTwoComponentsIn hKc
  have hc3' : c ^ 3 = 1 := by
    rw [← hc3]
    exact pow_orderOf_eq_one c
  set α := Sec3.Sims321.barAut K ⟨c, hcN⟩ with hαdef
  have hα3 : α ^ 3 = 1 := by
    rw [hαdef, ← map_pow]
    have h1 : (⟨c, hcN⟩ : Subgroup.normalizer (K : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hc3')
    rw [h1, map_one]
  obtain ⟨y0, hy0, hfix⟩ : ∃ y0 : K ⧸ CFSG.pCore 2 K, orderOf y0 = 3 ∧ α y0 = y0 := by
    by_cases hαone : α = 1
    · obtain ⟨y0, hy0⟩ := exists_orderOf_three_of_isL3OddType hL3
      exact ⟨y0, hy0, by rw [hαone]; rfl⟩
    · have hαo : orderOf α = 3 := orderOf_eq_prime hα3 hαone
      exact kf4 _ hL3 α hαo
  obtain ⟨z, hz, hz3, hzfix⟩ := exists_lift_fixed α hy0 hfix
  have hzM : z ∈ M := hKM hz
  have hOM : ∀ x ∈ CFSG.Open.pCoreOf 2 K, x ∈ CFSG.Open.pCoreOf 2 M := fun x hx => by
    rw [pCoreOf_eq_inf_of_mem hKc] at hx
    exact hx.2
  have hcomm_c : c * z * c⁻¹ * z⁻¹ ∈ CFSG.Open.pCoreOf 2 M :=
    hOM _ (comm_mem_of_barAut_fix hcN hz hzfix)
  have hcomm_B : ∀ b ∈ A ⊓ L, b * z * b⁻¹ * z⁻¹ ∈ CFSG.Open.pCoreOf 2 M := fun b hb =>
    hOM _ (hone b hb z hz)
  have hOn : ∀ g ∈ M, ∀ t ∈ CFSG.Open.pCoreOf 2 M,
      g * t * g⁻¹ ∈ CFSG.Open.pCoreOf 2 M := fun g hg t ht =>
    (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hg) t).mp ht
  have hPa : ∀ a ∈ Subgroup.closure ({c} ∪ ((A ⊓ L : Subgroup G) : Set G)),
      a ∈ M ∧ a * z * a⁻¹ * z⁻¹ ∈ CFSG.Open.pCoreOf 2 M := by
    intro a ha
    refine Subgroup.closure_induction
      (p := fun a _ => a ∈ M ∧ a * z * a⁻¹ * z⁻¹ ∈ CFSG.Open.pCoreOf 2 M) ?_ ?_ ?_ ?_ ha
    · intro s hs
      rcases hs with hs | hs
      · rw [Set.mem_singleton_iff] at hs
        rw [hs]
        exact ⟨h.le_M hcA, hcomm_c⟩
      · exact ⟨h.le_M (Subgroup.mem_inf.mp hs).1, hcomm_B s hs⟩
    · exact ⟨M.one_mem, by simp⟩
    · intro a b _ _ ha' hb'
      refine ⟨mul_mem ha'.1 hb'.1, ?_⟩
      have e : a * b * z * (a * b)⁻¹ * z⁻¹ =
          (a * (b * z * b⁻¹ * z⁻¹) * a⁻¹) * (a * z * a⁻¹ * z⁻¹) := by group
      rw [e]
      exact mul_mem (hOn a ha'.1 _ hb'.2) ha'.2
    · intro a _ ha'
      refine ⟨inv_mem ha'.1, ?_⟩
      have e' : a⁻¹ * z * a⁻¹⁻¹ * z⁻¹ = a⁻¹ * (a * z * a⁻¹ * z⁻¹)⁻¹ * a⁻¹⁻¹ := by group
      rw [e']
      exact hOn a⁻¹ (inv_mem ha'.1) _ (inv_mem ha'.2)
  have hAsub : A ≤ Subgroup.closure ({c} ∪ ((A ⊓ L : Subgroup G) : Set G)) := by
    intro a ha
    have ha' : a ∈ Subgroup.zpowers c ⊔ (A ⊓ L) := by
      rw [← hF.eq_sup]
      exact ha
    have hle : Subgroup.zpowers c ⊔ (A ⊓ L) ≤
        Subgroup.closure ({c} ∪ ((A ⊓ L : Subgroup G) : Set G)) := by
      apply sup_le
      · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Or.inl rfl))
      · intro b hb
        exact Subgroup.subset_closure (Or.inr hb)
    exact hle ha'
  have hAcomm : ∀ a ∈ A, a * z * a⁻¹ * z⁻¹ ∈ CFSG.Open.pCoreOf 2 M := fun a ha =>
    (hPa a (hAsub ha)).2
  have hinter : ∀ a ∈ A, ∀ j : ℤ, (z ^ j)⁻¹ * a ∈ CFSG.Open.pCoreOf 2 M → a = 1 := by
    intro a ha j hj
    apply hD1 a
    refine Subgroup.mem_inf.mpr ⟨ha, ?_⟩
    rw [hSdef]
    have e : a = z ^ j * ((z ^ j)⁻¹ * a) := by group
    rw [e]
    exact mul_mem (Subgroup.mem_sup_left (zpow_mem hz j)) (Subgroup.mem_sup_right hj)
  exact false_of_E81_gen h hzM hz3 hAcomm hinter

theorem item1923_three_a (kf4 : KF4) (h : Hyp1921 G A M N L) (hF : Facts1922 G A M N L c)
    (hK : K ∈ scriptJ M N) (h2 : scriptJ M N = {K}) (hL3 : IsL3OddType (K ⧸ CFSG.pCore 2 K))
    (hone : ∀ b ∈ A ⊓ L, ∀ k ∈ K, b * k * b⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K) :
    c ∈ K ∧ A ⊓ K = Subgroup.zpowers c := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hKc, hKN⟩ := hK
  have hKM : K ≤ M := le_of_mem_oTwoComponentsIn hKc
  have hAM : A ≤ M := h.le_M
  have hcA : c ∈ A := (step1923_W h hF).mem
  have hc3 : orderOf c = 3 := hF.orderOf_c
  have hc3' : c ^ 3 = 1 := by
    rw [← hc3]
    exact pow_orderOf_eq_one c
  have hcM : c ∈ M := hAM hcA
  have hzpow_L : ∀ x ∈ Subgroup.zpowers c, ∀ l ∈ L, x * l * x⁻¹ ∈ L := by
    intro x hx l hl
    have hxc : x ∈ sectionCentralizer A L (CFSG.Open.pCoreOf 2 L) := by
      rw [hF.centralizer_eq]
      exact hx
    have hxc' : x ∈ A ∧ ∀ y ∈ L, x * y * x⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 L := hxc
    have e : x * l * x⁻¹ = (x * l * x⁻¹ * l⁻¹) * l := by group
    rw [e]
    exact mul_mem (CFSG.LieType.BorelTits.pCoreOf_le 2 L (hxc'.2 l hl)) hl
  have hcN_L : c ∈ Subgroup.normalizer (L : Set G) := by
    refine Subgroup.mem_normalizer_iff.mpr fun l =>
      ⟨fun hl => hzpow_L c (Subgroup.mem_zpowers c) l hl, fun hl => ?_⟩
    have e : l = c⁻¹ * (c * l * c⁻¹) * c⁻¹⁻¹ := by group
    rw [e]
    exact hzpow_L c⁻¹ (inv_mem (Subgroup.mem_zpowers c)) _ hl
  have hcN_N : c ∈ N := by
    rw [← hF.normalizer_eq]
    exact hcN_L
  have hNK : ∀ w ∈ N, w ∈ M → w ∈ Subgroup.normalizer (K : Set G) := by
    intro w hwN hwM
    have hwJ : K.map (MulAut.conj w).toMonoidHom ∈ scriptJ M N := by
      refine ⟨Sec18.map_conj_mem_oTwoComponentsIn hKc hwM, fun hle => hKN ?_⟩
      intro x hx
      have hxN := hle (Subgroup.mem_map_of_mem _ hx)
      have e : w⁻¹ * (w * x * w⁻¹) * w = x := by group
      rw [← e]
      exact mul_mem (mul_mem (inv_mem hwN) hxN) hwN
    rw [h2] at hwJ
    exact mem_normalizer_of_map_conj_eq hwJ
  have hcN : c ∈ Subgroup.normalizer (K : Set G) := hNK c hcN_N hcM
  have hWle := step1923_W_le h hF
  have hWK : ∀ w ∈ planeGroup A L c, w ∈ Subgroup.normalizer (K : Set G) :=
    fun w hw => hNK w (hWle hw).1.1 (hWle hw).1.2
  have hWA : ∀ w ∈ planeGroup A L c, w ∈ Subgroup.normalizer (A : Set G) :=
    fun w hw => (hWle hw).2
  have hWM : ∀ w ∈ planeGroup A L c, w ∈ M := fun w hw => (hWle hw).1.2
  have hWcomm : ∀ w ∈ planeGroup A L c, ∀ k : ℤ, w * c ^ k = c ^ k * w := by
    intro w hw k
    have hcw : Commute w c := (step1923_W h hF).commute w hw
    exact (hcw.zpow_right k).eq
  obtain ⟨S, hSdef⟩ : ∃ S : Subgroup G, S = K ⊔ CFSG.Open.pCoreOf 2 M := ⟨_, rfl⟩
  have hKS : K ≤ S := by rw [hSdef]; exact le_sup_left
  have hOS : CFSG.Open.pCoreOf 2 M ≤ S := by rw [hSdef]; exact le_sup_right
  have hSM : S ≤ M := by
    rw [hSdef]
    exact sup_le hKM (CFSG.LieType.BorelTits.pCoreOf_le 2 M)
  have hprod : (S : Set G) = (K : Set G) * (CFSG.Open.pCoreOf 2 M : Set G) := by
    rw [hSdef]
    exact Subgroup.coe_mul_of_left_le_normalizer_right K _
      (fun k hk => CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M (hKM hk))
  have hcard : Nat.card (A ⊓ S : Subgroup G) ≤ 3 := card_inf_le_three h hKc hL3 hSdef
  have hmemS : ∀ w ∈ planeGroup A L c, ∀ s ∈ S, w * s * w⁻¹ ∈ S := by
    intro w hw s hs
    have hs' : s ∈ (S : Set G) := hs
    rw [hprod] at hs'
    obtain ⟨k, hk, q, hq, rfl⟩ := hs'
    have hwq : w * q * w⁻¹ ∈ CFSG.Open.pCoreOf 2 M :=
      (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M (hWM w hw)) q).mp hq
    have hwk : w * k * w⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hWK w hw) k).mp hk
    have e : w * (k * q) * w⁻¹ = (w * k * w⁻¹) * (w * q * w⁻¹) := by group
    have hmem : (w * k * w⁻¹) * (w * q * w⁻¹) ∈ (S : Set G) := by
      rw [hprod]
      exact ⟨_, hwk, _, hwq, rfl⟩
    rw [e]
    exact hmem
  have hWD : ∀ w ∈ planeGroup A L c, ∀ d ∈ A ⊓ S, w * d * w⁻¹ ∈ A ⊓ S := fun w hw d hd =>
    Subgroup.mem_inf.mpr
      ⟨(Subgroup.mem_normalizer_iff.mp (hWA w hw) d).mp (Subgroup.mem_inf.mp hd).1,
        hmemS w hw d (Subgroup.mem_inf.mp hd).2⟩
  have hDzp : ∀ d ∈ A ⊓ S, d ∈ Subgroup.zpowers c :=
    inf_le_zpowers_of_irreducible h hF hcard hWD hWcomm
  have hcS : c ∈ S := by
    obtain ⟨d, hd, hd1⟩ : ∃ d ∈ A ⊓ S, d ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact false_of_inf_eq_bot kf4 h hF hKc hL3 hone hSdef hcN hcon
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hDzp d hd)
    have hdS : c ^ i ∈ S := by
      rw [hi]
      exact (Subgroup.mem_inf.mp hd).2
    have hne : c ^ i ≠ 1 := by
      rw [hi]
      exact hd1
    exact mem_of_zpow_ne_one hc3 i hdS hne
  haveI hKperK : Group.IsPerfect K := perfect_of_mem_oTwoComponentsIn hKc
  have hKsubM : (K.subgroupOf M).IsSubnormal := by
    obtain ⟨-, hsub, -⟩ := (mem_oTwoComponentsIn_iff.mp hKc).2
    exact hsub
  haveI hKperS : Group.IsPerfect (K.subgroupOf S) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hKS).symm.toMonoidHom)
      (MulEquiv.surjective _)
  have hKsubS : (K.subgroupOf S).IsSubnormal := Sec18.isSubnormal_subgroupOf_of_le hKsubM hSM
  have hQn : ((CFSG.Open.pCoreOf 2 M).subgroupOf S).Normal := by
    rw [hSdef]
    exact Subgroup.normal_subgroupOf_sup_of_le_normalizer
      (fun k hk => CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M (hKM hk))
  have hQp : IsPGroup 2 ((CFSG.Open.pCoreOf 2 M).subgroupOf S) := by
    intro x
    obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
      ⟨((x : S) : G), Subgroup.mem_subgroupOf.mp x.2⟩
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩
  have hKQtop : K.subgroupOf S ⊔ (CFSG.Open.pCoreOf 2 M).subgroupOf S = ⊤ := by
    rw [eq_top_iff]
    intro s _
    have hs' : (s : G) ∈ (S : Set G) := s.2
    rw [hprod] at hs'
    obtain ⟨k, hk, q, hq, hkq⟩ := hs'
    have hks : s = (⟨k, hKS hk⟩ : S) * (⟨q, hOS hq⟩ : S) :=
      Subtype.ext (show (s : G) = k * q from hkq.symm)
    rw [hks]
    exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mpr hk))
      (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mpr hq))
  haveI hKnorm : (K.subgroupOf S).Normal :=
    normal_of_perfect_isSubnormal_of_pCore hKperS hKsubS hQp hQn hKQtop
  have hcK : c ∈ K := by
    have hcS' : c ∈ (S : Set G) := hcS
    rw [hprod] at hcS'
    obtain ⟨k, hk, q, hq, hkq⟩ := hcS'
    have hkS : (⟨k, hKS hk⟩ : S) ∈ K.subgroupOf S := Subgroup.mem_subgroupOf.mpr hk
    have hqS : (⟨q, hOS hq⟩ : S) ∈ (CFSG.Open.pCoreOf 2 M).subgroupOf S :=
      Subgroup.mem_subgroupOf.mpr hq
    have hc'eq : (⟨c, hcS⟩ : S) = (⟨k, hKS hk⟩ : S) * (⟨q, hOS hq⟩ : S) :=
      Subtype.ext (show c = k * q from hkq.symm)
    have hk1 : QuotientGroup.mk' (K.subgroupOf S) (⟨k, hKS hk⟩ : S) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hkS
    have hY : QuotientGroup.mk' (K.subgroupOf S) (⟨c, hcS⟩ : S) =
        QuotientGroup.mk' (K.subgroupOf S) (⟨q, hOS hq⟩ : S) := by
      rw [hc'eq, map_mul, hk1, one_mul]
    obtain ⟨j, hj⟩ := hQp (⟨(⟨q, hOS hq⟩ : S), hqS⟩ :
      ↥((CFSG.Open.pCoreOf 2 M).subgroupOf S))
    have hq2 : (⟨q, hOS hq⟩ : S) ^ 2 ^ j = 1 := congrArg Subtype.val hj
    have hY2 : QuotientGroup.mk' (K.subgroupOf S) (⟨q, hOS hq⟩ : S) ^ 2 ^ j = 1 := by
      rw [← map_pow, hq2, map_one]
    have hc3S : (⟨c, hcS⟩ : S) ^ 3 = 1 := Subtype.ext (by simpa using hc3')
    have hY3 : QuotientGroup.mk' (K.subgroupOf S) (⟨c, hcS⟩ : S) ^ 3 = 1 := by
      rw [← map_pow, hc3S, map_one]
    have hcop : Nat.Coprime 3 (2 ^ j) := Nat.Coprime.pow_right j (by norm_num)
    have hYone : QuotientGroup.mk' (K.subgroupOf S) (⟨c, hcS⟩ : S) = 1 :=
      (pow_eq_one_iff_of_coprime hcop).mp ⟨hY3, by rw [hY]; exact hY2⟩
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff (⟨c, hcS⟩ : S)).mp hYone)
  refine ⟨hcK, le_antisymm ?_ ?_⟩
  · intro d hd
    exact hDzp d (Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hd).1, hKS (Subgroup.mem_inf.mp hd).2⟩)
  · exact Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨hcA, hcK⟩)

theorem item1923_three_b (kf1 : KF1) (h : Hyp1921 G A M N L) (hF : Facts1922 G A M N L c)
    (hK : K ∈ scriptJ M N) (h2 : scriptJ M N = {K}) (hL3 : IsL3OddType (K ⧸ CFSG.pCore 2 K))
    (hone : ∀ b ∈ A ⊓ L, ∀ k ∈ K, b * k * b⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K)
    (hcK : c ∈ K) (hAK : A ⊓ K = Subgroup.zpowers c) :
    M ≤ Subgroup.normalizer (K : Set G) := by
  obtain ⟨hKc, hKN⟩ := hK
  have hKM : K ≤ M := le_of_mem_oTwoComponentsIn hKc
  have hWle := step1923_W_le h hF
  have hWN : planeGroup A L c ≤ N := fun x hx => (hWle hx).1.1
  have hWM : planeGroup A L c ≤ M := fun x hx => (hWle hx).1.2
  have hAM : A ≤ M := h.le_M
  have hc3 : orderOf c = 3 := hF.orderOf_c
  have hAab' : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (h.isE27.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hA3' : ∀ a ∈ A, a ^ 3 = 1 := fun a ha => h.isE27.1.2 a ha
  have hWK : ∀ w ∈ planeGroup A L c, w ∈ Subgroup.normalizer (K : Set G) := by
    intro w hw
    have hwJ : K.map (MulAut.conj w).toMonoidHom ∈ scriptJ M N := by
      refine ⟨Sec18.map_conj_mem_oTwoComponentsIn hKc (hWM hw), fun hle => hKN ?_⟩
      intro x hx
      have hxN := hle (Subgroup.mem_map_of_mem _ hx)
      have e : w⁻¹ * (w * x * w⁻¹) * w = x := by group
      rw [← e]
      exact mul_mem (mul_mem (inv_mem (hWN hw)) hxN) (hWN hw)
    rw [h2] at hwJ
    exact mem_normalizer_of_map_conj_eq hwJ
  intro m hm
  by_contra hmK
  set K' : Subgroup G := K.map (MulAut.conj m).toMonoidHom with hK'def
  have hK'c : K' ∈ oTwoComponentsIn M := Sec18.map_conj_mem_oTwoComponentsIn hKc hm
  have hK'M : K' ≤ M := le_of_mem_oTwoComponentsIn hK'c
  have hne : K' ≠ K := fun e => hmK (mem_normalizer_of_map_conj_eq e)
  have hpair : ∀ g ∈ M, K.map (MulAut.conj g).toMonoidHom = K ∨
      K.map (MulAut.conj g).toMonoidHom = K' := fun g hg =>
    map_conj_eq_or_eq h.toSec18Std hKc hm hK'def hne hg
  have hWK' : ∀ w ∈ planeGroup A L c, w ∈ Subgroup.normalizer (K' : Set G) := by
    intro w hw
    have e : K'.map (MulAut.conj w).toMonoidHom = K.map (MulAut.conj (w * m)).toMonoidHom := by
      rw [hK'def, Subgroup.map_map]
      congr 1
      ext x
      simp [mul_assoc]
    rcases hpair (w * m) (mul_mem (hWM hw) hm) with h1 | h1
    · exfalso
      apply hmK
      have hwm : w * m ∈ Subgroup.normalizer (K : Set G) := mem_normalizer_of_map_conj_eq h1
      have hm' := mul_mem (inv_mem (hWK w hw)) hwm
      simpa using hm'
    · exact mem_normalizer_of_map_conj_eq (e.trans h1)
  have hBK : ∀ b ∈ A ⊓ L, b ∈ Subgroup.normalizer (K : Set G) := by
    intro b hb
    have key : ∀ b' ∈ A ⊓ L, ∀ k ∈ K, b' * k * b'⁻¹ ∈ K := by
      intro b' hb' k hk
      have h4 : b' * k * b'⁻¹ = (b' * k * b'⁻¹ * k⁻¹) * k := by group
      rw [h4]
      exact mul_mem (CFSG.LieType.BorelTits.pCoreOf_le 2 K (hone b' hb' k hk)) hk
    refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => key b hb x hx, fun hx => ?_⟩
    have e2 : b⁻¹ * (b * x * b⁻¹) * b⁻¹⁻¹ = x := by group
    rw [← e2]
    exact key b⁻¹ (inv_mem hb) _ hx
  have hBK' : ∀ b ∈ A ⊓ L, b ∈ Subgroup.normalizer (K' : Set G) := by
    intro b hb
    have hbM : b ∈ M := hAM (Subgroup.mem_inf.mp hb).1
    have e : K'.map (MulAut.conj b).toMonoidHom = K.map (MulAut.conj (b * m)).toMonoidHom := by
      rw [hK'def, Subgroup.map_map]
      congr 1
      ext x
      simp [mul_assoc]
    have hne' : K'.map (MulAut.conj b).toMonoidHom ≠ K := by
      intro e'
      apply hne
      apply Subgroup.map_injective (f := (MulAut.conj b).toMonoidHom) (MulAut.conj b).injective
      rw [e', map_conj_eq_of_mem_normalizer (hBK b hb)]
    rcases hpair (b * m) (mul_mem hbM hm) with h1 | h1
    · exact absurd (e.trans h1) hne'
    · exact mem_normalizer_of_map_conj_eq (e.trans h1)
  have hBN'' : A ⊓ L ≤ Subgroup.normalizer (K' : Set G) := fun b hb => hBK' b hb
  let φ : (A ⊓ L : Subgroup G) →* MulAut (K' ⧸ CFSG.pCore 2 K') :=
    (Sec3.Sims321.barAut K').comp (Subgroup.inclusion hBN'')
  have hirr := (step1923_W h hF).irreducible
  have hclaim : ∀ ψ ∈ Sec4.autIn (planeGroup A L c) (A ⊓ L),
      φ.ker.map ψ.toMonoidHom = φ.ker := by
    intro ψ hψ
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hψ
    have hxW : (x : G) ∈ planeGroup A L c :=
      (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hx)).1
    have hxK' : (x : G) ∈ Subgroup.normalizer (K' : Set G) := hWK' _ hxW
    have hformula : ∀ y : (A ⊓ L : Subgroup G),
        φ ((A ⊓ L).normalizerMonoidHom x y) =
          Sec3.Sims321.barAut K' ⟨(x : G), hxK'⟩ * φ y *
            (Sec3.Sims321.barAut K' ⟨(x : G), hxK'⟩)⁻¹ := by
      intro y
      have key : Subgroup.inclusion hBN'' ((A ⊓ L).normalizerMonoidHom x y) =
          (⟨(x : G), hxK'⟩ : Subgroup.normalizer (K' : Set G)) *
            Subgroup.inclusion hBN'' y *
            (⟨(x : G), hxK'⟩ : Subgroup.normalizer (K' : Set G))⁻¹ := by
        apply Subtype.ext
        rfl
      show Sec3.Sims321.barAut K' (Subgroup.inclusion hBN'' ((A ⊓ L).normalizerMonoidHom x y)) = _
      rw [key, map_mul, map_mul, map_inv]
      rfl
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      have hy' : φ y = 1 := MonoidHom.mem_ker.mp hy
      rw [MonoidHom.mem_ker]
      show φ ((A ⊓ L).normalizerMonoidHom x y) = 1
      rw [hformula, hy', mul_one, mul_inv_cancel]
    · intro y hy
      have hy' : φ y = 1 := MonoidHom.mem_ker.mp hy
      refine ⟨((A ⊓ L).normalizerMonoidHom x).symm y, ?_, ?_⟩
      · refine MonoidHom.mem_ker.mpr ?_
        have h5 := hformula (((A ⊓ L).normalizerMonoidHom x).symm y)
        rw [MulEquiv.apply_symm_apply, hy'] at h5
        have h6 := h5.symm
        calc φ (((A ⊓ L).normalizerMonoidHom x).symm y)
            = (Sec3.Sims321.barAut K' ⟨(x : G), hxK'⟩)⁻¹ *
                (Sec3.Sims321.barAut K' ⟨(x : G), hxK'⟩ *
                  φ (((A ⊓ L).normalizerMonoidHom x).symm y) *
                    (Sec3.Sims321.barAut K' ⟨(x : G), hxK'⟩)⁻¹) *
                  Sec3.Sims321.barAut K' ⟨(x : G), hxK'⟩ := by group
          _ = 1 := by rw [h6]; group
      · exact ((A ⊓ L).normalizerMonoidHom x).apply_symm_apply y
  have hL3' := isL3OddType_of_conj m hL3
  have hq' := Sec18.isQuasisimple_of_mem_oTwoComponentsIn hK'c
  have hInK' : InK194 (K' ⧸ CFSG.pCore 2 K') := by
    obtain ⟨n, hn, ⟨e⟩⟩ := hL3'
    exact ⟨hq', Or.inl (Or.inl ⟨n, hn.pos, Or.inr (Or.inl ⟨e⟩)⟩)⟩
  have hab := kf1.1 _ hInK'
  have hexp : (planeGroup A L c ⊓ Subgroup.normalizer (K' : Set G)).relIndex
      (planeGroup A L c) = 2 → OutTwoExpTwo (K' ⧸ CFSG.pCore 2 K') :=
    fun _ => kf1.2.1 _ hInK' (Or.inl hL3')
  have hsimp' : IsSimpleGroup (K' ⧸ CFSG.pCore 2 K') := isSimpleGroup_of_isL3OddType hL3'
  have hcen' : Subgroup.center (K' ⧸ CFSG.pCore 2 K') = ⊥ := by
    haveI := hsimp'
    exact center_eq_bot_of_simple_nonab (nonabelian_of_quotient_center hq'.2.2)
  rcases hirr φ.ker hclaim with hbot | htop
  ·
    have hinj : Function.Injective φ := by
      rw [injective_iff_map_eq_one]
      intro p hp
      have hpk : p ∈ φ.ker := MonoidHom.mem_ker.mpr hp
      rw [hbot, Subgroup.mem_bot] at hpk
      exact hpk
    have hpR : CFSG.Open.pRank 3 (⊤ : Subgroup (K' ⧸ CFSG.pCore 2 K')) ≤ 1 := by
      obtain ⟨n, hn, ⟨e⟩⟩ := hL3'
      exact Sec20.kFactL3OddThreeRank n hn _ ⟨e⟩
    have hinn : ∀ p : (A ⊓ L : Subgroup G),
        φ p ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (K' ⧸ CFSG.pCore 2 K') := by
      intro p
      have hmemB : (⟨(p : G), hBN'' p.2⟩ : Subgroup.normalizer (K' : Set G)) ∈
          (A ⊓ L).subgroupOf (Subgroup.normalizer (K' : Set G)) :=
        Subgroup.mem_subgroupOf.mpr p.2
      exact (step1923_inner h hF hK'c hab hexp) (Subgroup.mem_map_of_mem _ hmemB)
    have hPc : IsMulCommutative (A ⊓ L : Subgroup G) :=
      ⟨⟨fun x y => Subtype.ext (hAab' _ (Subgroup.mem_inf.mp x.2).1 _ (Subgroup.mem_inf.mp y.2).1)⟩⟩
    have hPe : ∀ p : (A ⊓ L : Subgroup G), p ^ 3 = 1 := fun p =>
      Subtype.ext (by simpa using hA3' _ (Subgroup.mem_inf.mp p.2).1)
    exact false_of_E9 hsimp' hcen' hpR hPc hPe hF.card φ hinj hinn
  ·
    have hφ1 : ∀ b (hb : b ∈ A ⊓ L), Sec3.Sims321.barAut K' ⟨b, hBK' b hb⟩ = 1 := by
      intro b hb
      have hmem : (⟨b, hb⟩ : (A ⊓ L : Subgroup G)) ∈ φ.ker := by
        rw [htop]
        exact Subgroup.mem_top _
      exact MonoidHom.mem_ker.mp hmem
    have hBtriv : ∀ b ∈ A ⊓ L, ∀ k ∈ K', b * k * b⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K' :=
      fun b hb k hk => comm_mem_of_barAut_eq_one (hBK' b hb) (hφ1 b hb) hk
    have hO'M : ∀ x ∈ CFSG.Open.pCoreOf 2 K', x ∈ CFSG.Open.pCoreOf 2 M := fun x hx => by
      rw [pCoreOf_eq_inf_of_mem hK'c] at hx
      exact hx.2
    have hcK'mem : ∀ k ∈ K', c * k * c⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 M := fun k hk =>
      Sec19.Step1910Proof.commutator_mem_pCoreOf hKc hK'c hne.symm hcK hk
    have hAcomm : ∀ a ∈ A, ∀ k ∈ K', a * k * a⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 M := by
      have hOn : ∀ g ∈ M, ∀ t ∈ CFSG.Open.pCoreOf 2 M,
          g * t * g⁻¹ ∈ CFSG.Open.pCoreOf 2 M := fun g hg t ht =>
        (Subgroup.mem_normalizer_iff.mp
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hg) t).mp ht
      have hPa : ∀ a ∈ Subgroup.closure ({c} ∪ ((A ⊓ L : Subgroup G) : Set G)),
          a ∈ M ∧ ∀ k ∈ K', a * k * a⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 M := by
        intro a ha
        refine Subgroup.closure_induction (p := fun a _ => a ∈ M ∧ ∀ k ∈ K',
          a * k * a⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 M) ?_ ?_ ?_ ?_ ha
        · intro s hs
          rcases hs with hs | hs
          · rw [Set.mem_singleton_iff] at hs
            rw [hs]
            exact ⟨hKM hcK, fun k hk => hcK'mem k hk⟩
          · exact ⟨hAM (Subgroup.mem_inf.mp hs).1, fun k hk => hO'M _ (hBtriv s hs k hk)⟩
        · exact ⟨M.one_mem, fun k _ => by simp⟩
        · intro a b _ _ ha' hb'
          refine ⟨mul_mem ha'.1 hb'.1, fun k hk => ?_⟩
          have e : a * b * k * (a * b)⁻¹ * k⁻¹ =
              (a * (b * k * b⁻¹ * k⁻¹) * a⁻¹) * (a * k * a⁻¹ * k⁻¹) := by group
          rw [e]
          exact mul_mem (hOn a ha'.1 _ (hb'.2 k hk)) (ha'.2 k hk)
        · intro a _ ha'
          refine ⟨inv_mem ha'.1, fun k hk => ?_⟩
          have e' : a⁻¹ * k * a⁻¹⁻¹ * k⁻¹ = a⁻¹ * (a * k * a⁻¹ * k⁻¹)⁻¹ * a⁻¹⁻¹ := by group
          rw [e']
          exact hOn a⁻¹ (inv_mem ha'.1) _ (inv_mem (ha'.2 k hk))
      have hAsub : A ≤ Subgroup.closure ({c} ∪ ((A ⊓ L : Subgroup G) : Set G)) := by
        intro a ha
        have ha' : a ∈ Subgroup.zpowers c ⊔ (A ⊓ L) := by
          rw [← hF.eq_sup]
          exact ha
        have hle : Subgroup.zpowers c ⊔ (A ⊓ L) ≤
            Subgroup.closure ({c} ∪ ((A ⊓ L : Subgroup G) : Set G)) := by
          apply sup_le
          · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Or.inl rfl))
          · intro b hb
            exact Subgroup.subset_closure (Or.inr hb)
        exact hle ha'
      intro a ha k hk
      exact (hPa a (hAsub ha)).2 k hk
    have hxK : m * c * m⁻¹ ∈ K' := Subgroup.mem_map_of_mem _ hcK
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hx3 : orderOf (m * c * m⁻¹) = 3 := by
      have hc3' : c ^ 3 = 1 := by
        rw [← hc3]
        exact pow_orderOf_eq_one c
      have hcube : (m * c * m⁻¹) ^ 3 = 1 := by
        have e3 : (m * c * m⁻¹) ^ 3 = m * c ^ 3 * m⁻¹ :=
          (map_pow (MulAut.conj m).toMonoidHom c 3).symm
        rw [e3, hc3', mul_one, mul_inv_cancel]
      have hne1 : m * c * m⁻¹ ≠ 1 := by
        intro e1
        have hc1 : c = 1 := by
          have e4 : c = m⁻¹ * (m * c * m⁻¹) * m := by group
          rw [e4, e1]
          group
        rw [hc1, orderOf_one] at hc3
        norm_num at hc3
      exact orderOf_eq_prime hcube hne1
    exact false_of_E81 h hK'c hxK hx3 hAcomm hcen'

theorem item1923_three_c (h : Hyp1921 G A M N L) (hF : Facts1922 G A M N L c)
    (hK : K ∈ scriptJ M N)
    (hcK : c ∈ K) (hKM : M ≤ Subgroup.normalizer (K : Set G))
    (hL3 : IsL3OddType (K ⧸ CFSG.pCore 2 K)) : K = normalClosureIn M c :=
  three_c_of_orderOf hF.orderOf_c hK.1 hcK hKM hL3

end CFSG.RankThree.PartTwo.Late
