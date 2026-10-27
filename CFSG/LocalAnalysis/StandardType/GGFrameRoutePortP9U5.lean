module

public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP9U5Torus
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerLiftLocal
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoConfig
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscape
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrHom
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrLarge
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrXGen
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbDefs
public import CFSG.LocalAnalysis.AGLEmbedding.ZZPrimeDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerLift
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.PCompBasics
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec4.Item47Statement
public import CFSG.RankThree.PartTwo.Sec4.Item47Witness
public import CFSG.RankThree.PartTwo.Sec8.Statements

public section

namespace CFSG.StandardType.FrameRoute

open Matrix CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.StandardType.LineU
open P9U5

variable {F : Type} [Field F] {G : Type} [Group G] [Finite G] {m : ℕ}

private def p9u5a_scalarKer {K : Subgroup G} (φ : ↥(unitarySU 2 1 F m) →* K) : Prop :=
  ∀ g : ↥(unitarySU 2 1 F m), φ g = 1 →
    ∃ c : F, ((g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = diagonal (fun _ => c)

private lemma p9u5a_torus_eq_of_phi_eq (h : UnitaryFieldData 2 1 F) (hF : Nat.card F = 4)
    (hm : 3 ≤ m) {K : Subgroup G} {φ : ↥(unitarySU 2 1 F m) →* K}
    (hφker : p9u5a_scalarKer φ) {s t : Fin (m - 3) → Fˣ}
    (hst : φ (torus h hF hm s) = φ (torus h hF hm t)) : s = t := by
  have hone : φ (torus h hF hm (s * t⁻¹)) = 1 := by
    have h1 : torus h hF hm (s * t⁻¹) =
        torus h hF hm s * (torus h hF hm t)⁻¹ := by
      rw [map_mul, map_inv]
    rw [h1, map_mul, map_inv, hst, mul_inv_cancel]
  obtain ⟨c, hc⟩ := hφker _ hone
  exact mul_inv_eq_one.mp (torus_eq_one_of_scalar h hF hm (s * t⁻¹) hc)

private lemma p9u5a_orderOf_eq_three {z : G} (hz1 : z ≠ 1) (hz3 : z ^ 3 = 1) :
    orderOf z = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime hz3 hz1

private lemma p9u5a_zpow_mem_of_zpow_mem {z x : G} (hord : orderOf z = 3)
    (hx : x ∈ Subgroup.zpowers z) (hx1 : x ≠ 1) : z ∈ Subgroup.zpowers x := by
  classical
  have hz3 : z ^ 3 = 1 := by rw [← hord]; exact pow_orderOf_eq_one z
  have hxmem : x ∈ (Finset.range 3).image (z ^ ·) := by
    have h' : x ∈ (Finset.range (orderOf z)).image (z ^ ·) :=
      (IsOfFinOrder.mem_zpowers_iff_mem_range_orderOf (isOfFinOrder_of_finite z)).mp hx
    rwa [hord] at h'
  obtain ⟨k, hk, hkx⟩ := Finset.mem_image.mp hxmem
  rw [Finset.mem_range] at hk
  interval_cases k
  · rw [pow_zero] at hkx
    exact absurd hkx.symm hx1
  · rw [pow_one] at hkx
    rw [← hkx]
    exact Subgroup.mem_zpowers_iff.mpr ⟨1, zpow_one z⟩
  · rw [← hkx]
    refine Subgroup.mem_zpowers_iff.mpr ⟨(2 : ℤ), ?_⟩
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast]
    calc (z ^ 2) ^ 2 = z ^ (2 * 2) := (pow_mul z 2 2).symm
      _ = z ^ 4 := by norm_num
      _ = z := by rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_succ, hz3, one_mul]

private lemma p9u5a_zpow_not_mem_range (h : UnitaryFieldData 2 1 F) (hF : Nat.card F = 4)
    (hm : 3 ≤ m) {K : Subgroup G} {φ : ↥(unitarySU 2 1 F m) →* K}
    (hφker : p9u5a_scalarKer φ) {z : G} (hz : z ∈ Subgroup.centralizer (K : Set G))
    (hz1 : z ≠ 1) : z ∉ (K.subtype.comp (φ.comp (torus h hF hm))).range := by
  rintro ⟨s, hs⟩
  have hzφ : ((φ (torus h hF hm s) : K) : G) = z := hs
  have hN : ∀ g ∈ unitarySU 2 1 F m, ∃ c : F,
      ((((torus h hF hm s : ↥(unitarySU 2 1 F m)) : GL (Fin m) F) * g *
          (((torus h hF hm s : ↥(unitarySU 2 1 F m)) : GL (Fin m) F))⁻¹ * g⁻¹ :
          GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = diagonal (fun _ => c) := by
    intro g hg
    let q : ↥(unitarySU 2 1 F m) := ⟨g, hg⟩
    have h1 : φ (torus h hF hm s * q * (torus h hF hm s)⁻¹ * q⁻¹) = 1 := by
      apply Subtype.ext
      have hq : ((φ q : K) : G) * z = z * ((φ q : K) : G) :=
        Subgroup.mem_centralizer_iff.mp hz (φ q) (φ q).2
      calc ((φ (torus h hF hm s * q * (torus h hF hm s)⁻¹ * q⁻¹) : K) : G)
          = ((φ (torus h hF hm s) : K) : G) * ((φ q : K) : G) *
              (((φ (torus h hF hm s) : K) : G))⁻¹ * (((φ q : K) : G))⁻¹ := by
            simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
        _ = z * ((φ q : K) : G) * z⁻¹ * (((φ q : K) : G))⁻¹ := by rw [hzφ]
        _ = 1 := by
            rw [hq.symm]
            group
    obtain ⟨c, hc⟩ := hφker _ h1
    exact ⟨c, by simpa [Subgroup.coe_mul, Subgroup.coe_inv] using hc⟩
  obtain ⟨c, hc⟩ := P9_U7a_eq_scalar_of_comm h hm _ hN
  have hs1 : s = 1 := torus_eq_one_of_scalar h hF hm s hc
  exact hz1 (by rw [hzφ.symm, hs1, (torus h hF hm).map_one, (φ).map_one, Subgroup.coe_one])

private lemma p9u5a_range_inf_zpowers (h : UnitaryFieldData 2 1 F) (hF : Nat.card F = 4)
    (hm : 3 ≤ m) {K : Subgroup G} {φ : ↥(unitarySU 2 1 F m) →* K}
    (hφker : p9u5a_scalarKer φ) {z : G} (hz : z ∈ Subgroup.centralizer (K : Set G))
    (hz1 : z ≠ 1) (hz3 : z ^ 3 = 1) :
    (K.subtype.comp (φ.comp (torus h hF hm))).range ⊓ Subgroup.zpowers z = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
  by_contra hxne
  exact p9u5a_zpow_not_mem_range h hF hm hφker hz hz1
    (Subgroup.zpowers_le.mpr hx1
      (p9u5a_zpow_mem_of_zpow_mem (p9u5a_orderOf_eq_three hz1 hz3) hx2 hxne))

private lemma p9u5a_comm_f_zpowers (h : UnitaryFieldData 2 1 F) (hF : Nat.card F = 4)
    (hm : 3 ≤ m) {K : Subgroup G} {φ : ↥(unitarySU 2 1 F m) →* K}
    {z : G} (hz : z ∈ Subgroup.centralizer (K : Set G))
    (s : Fin (m - 3) → Fˣ) (y : ↥(Subgroup.zpowers z)) :
    Commute ((K.subtype.comp (φ.comp (torus h hF hm))) s) (y : G) := by
  have hfK : ((K.subtype.comp (φ.comp (torus h hF hm))) s) ∈ K := (φ (torus h hF hm s)).2
  have hz' : z ∈ Subgroup.centralizer ({(K.subtype.comp (φ.comp (torus h hF hm))) s} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    rw [Set.mem_singleton_iff] at hb
    subst hb
    exact Subgroup.mem_centralizer_iff.mp hz _ hfK
  exact Subgroup.mem_centralizer_iff.mp (Subgroup.zpowers_le.mpr hz' y.2) _ (Set.mem_singleton _)

private noncomputable def p9u5a_Ehom (h : UnitaryFieldData 2 1 F) (hF : Nat.card F = 4)
    (hm : 3 ≤ m) {K : Subgroup G} (φ : ↥(unitarySU 2 1 F m) →* K) (z : G)
    (hz : z ∈ Subgroup.centralizer (K : Set G)) :
    ((Fin (m - 3) → Fˣ) × ↥(Subgroup.zpowers z)) →* G :=
  MonoidHom.noncommCoprod (K.subtype.comp (φ.comp (torus h hF hm)))
    (Subgroup.subtype (Subgroup.zpowers z))
    (fun s y => p9u5a_comm_f_zpowers h hF hm hz s y)

private lemma p9u5a_Ehom_injective (h : UnitaryFieldData 2 1 F) (hF : Nat.card F = 4)
    (hm : 3 ≤ m) {K : Subgroup G} {φ : ↥(unitarySU 2 1 F m) →* K}
    (hφker : p9u5a_scalarKer φ) {z : G} (hz : z ∈ Subgroup.centralizer (K : Set G))
    (hz1 : z ≠ 1) (hz3 : z ^ 3 = 1) :
    Function.Injective (p9u5a_Ehom h hF hm φ z hz) := by
  rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
  rintro ⟨s, y⟩ hmem
  have h1 : (K.subtype.comp (φ.comp (torus h hF hm))) s * (y : G) = 1 := by
    have happ : (p9u5a_Ehom h hF hm φ z hz) (s, y) =
        (K.subtype.comp (φ.comp (torus h hF hm))) s * (y : G) := rfl
    have hmem' : (p9u5a_Ehom h hF hm φ z hz) (s, y) = 1 := MonoidHom.mem_ker.mp hmem
    rwa [happ] at hmem'
  have hfs : (K.subtype.comp (φ.comp (torus h hF hm))) s ∈
      (K.subtype.comp (φ.comp (torus h hF hm))).range :=
    MonoidHom.mem_range.mpr ⟨s, rfl⟩
  have hfy : (K.subtype.comp (φ.comp (torus h hF hm))) s ∈ Subgroup.zpowers z := by
    rw [show (K.subtype.comp (φ.comp (torus h hF hm))) s = ((y : ↥(Subgroup.zpowers z)) : G)⁻¹ from
      eq_inv_of_mul_eq_one_left h1]
    exact Subgroup.inv_mem _ y.2
  have hbot : (K.subtype.comp (φ.comp (torus h hF hm))) s = 1 := by
    rw [← Subgroup.mem_bot, ← p9u5a_range_inf_zpowers h hF hm hφker hz hz1 hz3]
    exact Subgroup.mem_inf.mpr ⟨hfs, hfy⟩
  have hy1 : ((y : ↥(Subgroup.zpowers z)) : G) = 1 := by
    rw [hbot, one_mul] at h1
    exact h1
  refine Prod.ext ?_ ?_
  · have hφ1 : φ (torus h hF hm s) = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_one]
      exact hbot
    have hst : φ (torus h hF hm s) = φ (torus h hF hm 1) := by
      rw [hφ1, (torus h hF hm).map_one, (φ).map_one]
    exact p9u5a_torus_eq_of_phi_eq h hF hm hφker hst
  · exact Subtype.ext (by simpa using hy1)

private lemma p9u5a_Ehom_card (h : UnitaryFieldData 2 1 F) (hF : Nat.card F = 4)
    (hm : 3 ≤ m) {K : Subgroup G} {φ : ↥(unitarySU 2 1 F m) →* K}
    (hφker : p9u5a_scalarKer φ) {z : G} (hz : z ∈ Subgroup.centralizer (K : Set G))
    (hz1 : z ≠ 1) (hz3 : z ^ 3 = 1) :
    Nat.card (p9u5a_Ehom h hF hm φ z hz).range = 3 ^ (m - 2) := by
  rw [← Nat.card_congr (MonoidHom.ofInjective
    (p9u5a_Ehom_injective h hF hm hφker hz hz1 hz3)).toEquiv]
  have hunits : Nat.card Fˣ = 3 := by rw [Nat.card_units, hF]
  rw [Nat.card_prod, Nat.card_fun, Nat.card_fin, Nat.card_zpowers,
    p9u5a_orderOf_eq_three hz1 hz3, hunits]
  rw [show m - 2 = (m - 3) + 1 by omega, pow_succ]

private lemma p9u5a_Ehom_elemAbelian (h : UnitaryFieldData 2 1 F) (hF : Nat.card F = 4)
    (hm : 3 ≤ m) {K : Subgroup G} {φ : ↥(unitarySU 2 1 F m) →* K}
    {z : G} (hz : z ∈ Subgroup.centralizer (K : Set G)) (hz1 : z ≠ 1) (hz3 : z ^ 3 = 1) :
    IsElemAbelian 3 (p9u5a_Ehom h hF hm φ z hz).range := by
  refine ⟨?_, ?_⟩
  · haveI : IsMulCommutative (Fin (m - 3) → Fˣ) :=
      ⟨⟨fun a b => funext fun i => mul_comm (a i) (b i)⟩⟩
    exact Subgroup.range_isMulCommutative (p9u5a_Ehom h hF hm φ z hz)
  · intro x hx
    obtain ⟨⟨s, y⟩, rfl⟩ := MonoidHom.mem_range.mp hx
    rw [show (p9u5a_Ehom h hF hm φ z hz) (s, y) =
        (K.subtype.comp (φ.comp (torus h hF hm))) s * (y : G) from rfl]
    have hτ3 : torus h hF hm s ^ 3 = 1 := torus_pow_three h hF hm s
    have hf3 : ((K.subtype.comp (φ.comp (torus h hF hm))) s) ^ 3 = 1 := by
      have h1 : φ (torus h hF hm s) ^ 3 = 1 := by
        rw [← map_pow, hτ3, map_one]
      simpa using congrArg (fun t : K => (t : G)) h1
    have hy3 : ((y : ↥(Subgroup.zpowers z)) : G) ^ 3 = 1 := by
      have hdvd : orderOf ((y : ↥(Subgroup.zpowers z)) : G) ∣ orderOf z :=
        orderOf_dvd_of_mem_zpowers y.2
      rw [p9u5a_orderOf_eq_three hz1 hz3] at hdvd
      exact orderOf_dvd_iff_pow_eq_one.mp hdvd
    rw [(p9u5a_comm_f_zpowers h hF hm hz s y).mul_pow, hf3, hy3, one_mul]

private lemma p9u5a_Ehom_le_normalizer (h : UnitaryFieldData 2 1 F) (hF : Nat.card F = 4)
    (hm : 3 ≤ m) {K : Subgroup G} {φ : ↥(unitarySU 2 1 F m) →* K}
    {z : G} (hz : z ∈ Subgroup.centralizer (K : Set G)) :
    (p9u5a_Ehom h hF hm φ z hz).range ≤ Subgroup.normalizer
      (Subgroup.zpowers ((φ (swap h hm) : K) : G) : Set G) := by
  let a : G := ((φ (swap h hm) : K) : G)
  have hsub : (p9u5a_Ehom h hF hm φ z hz).range ≤
      Subgroup.centralizer (Subgroup.zpowers a : Set G) := by
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨⟨s, y⟩, rfl⟩ := MonoidHom.mem_range.mp he
    let e' : G := (K.subtype.comp (φ.comp (torus h hF hm))) s * (y : G)
    have happ : (p9u5a_Ehom h hF hm φ z hz) (s, y) = e' := rfl
    rw [happ]
    have hKeq : φ (torus h hF hm s) * φ (swap h hm) =
        φ (swap h hm) * φ (torus h hF hm s) := by
      rw [← map_mul, ← map_mul]
      exact congrArg φ (torus_comm_swap h hF hm s)
    have hfa : Commute ((K.subtype.comp (φ.comp (torus h hF hm))) s) a :=
      congrArg (fun t : K => (t : G)) hKeq
    have hza : z ∈ Subgroup.centralizer ({a} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hz _ (φ (swap h hm)).2).symm
    have hya : Commute ((y : ↥(Subgroup.zpowers z)) : G) a :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.zpowers_le.mpr hza y.2)
    have hae : a ∈ Subgroup.centralizer ({e'} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hfa.mul_left hya).symm
    have hxe := Subgroup.zpowers_le.mpr hae hx
    exact Subgroup.mem_centralizer_singleton_iff.mp hxe
  exact hsub.trans (Subgroup.centralizer_le_normalizer (Subgroup.zpowers a : Set G))

private theorem p9u5a_witness (h : UnitaryFieldData 2 1 F) (hF : Nat.card F = 4)
    {G : Type} [Group G] [Finite G] {K : Subgroup G}
    {φ : ↥(unitarySU 2 1 F m) →* K} (hφker : p9u5a_scalarKer φ) (hm : 3 ≤ m)
    {z : G} (hz : z ∈ Subgroup.centralizer (K : Set G)) (hz1 : z ≠ 1) (hz3 : z ^ 3 = 1) :
    ∃ E X : Subgroup G, X ≠ ⊥ ∧ IsPGroup 2 X ∧ IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ (m - 2) ∧ E ≤ Subgroup.normalizer (X : Set G) := by
  have ha1 : ((φ (swap h hm) : K) : G) ≠ 1 := by
    intro h1
    obtain ⟨c, hc⟩ := hφker _ (Subtype.ext h1)
    exact swap_not_scalar h hm ⟨c, hc⟩
  have ha2 : (((φ (swap h hm) : K) : G)) ^ 2 = 1 := by
    have h1 : (φ (swap h hm)) ^ 2 = 1 := by
      rw [pow_two, ← map_mul, P9U5.swap_mul_self, map_one]
    simpa using congrArg (fun t : K => (t : G)) h1
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨(p9u5a_Ehom h hF hm φ z hz).range,
    Subgroup.zpowers ((φ (swap h hm) : K) : G), ?_, ?_,
    p9u5a_Ehom_elemAbelian h hF hm hz hz1 hz3,
    p9u5a_Ehom_card h hF hm hφker hz hz1 hz3,
    p9u5a_Ehom_le_normalizer h hF hm hz⟩
  · rw [Ne, Subgroup.zpowers_eq_bot]
    exact ha1
  · refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, orderOf_eq_prime ha2 ha1, pow_one]

theorem P9_U5a_sub_two_le {G : Type} [Group G] [Finite G] [Finite F] (hF : Nat.card F = 4)
    {K : Subgroup G} {φ : ↥(unitarySU 2 1 F m) →* K}
    (hφker : ∀ g : ↥(unitarySU 2 1 F m), φ g = 1 →
      ∃ c : F, ((g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = diagonal (fun _ => c))
    {z : G} (hz : z ∈ Subgroup.centralizer (K : Set G)) (hz1 : z ≠ 1) (hz3 : z ^ 3 = 1) :
    m - 2 ≤ CFSG.Open.twoLocalPrimeRank 3 G := by
  classical
  by_cases hm : 3 ≤ m
  · have h : UnitaryFieldData 2 1 F := ⟨Nat.prime_two, le_rfl, by rw [hF]; norm_num⟩
    obtain ⟨E, X, hX, hX2, hE, hEcard, hXE⟩ :=
      p9u5a_witness h hF hφker hm hz hz1 hz3
    exact CFSG.LocalAnalysis.GLTheoremA.le_twoLocalPrimeRank_of_normalizer Nat.prime_three
      hX hX2 hE hEcard hXE
  · have h0 : m - 2 = 0 := by omega
    rw [h0]
    exact Nat.zero_le _

theorem P9_U5a_sub_two_le_of_cover
    {G : Type} [Group G] [Finite G] [Finite F]
    (hF : Nat.card F = 4) (hm : 5 ≤ m) (hm6 : m ≠ 6) {K : Subgroup G}
    {ψ : K →* LargeEvenProj (unitarySU 2 1 F m)} (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center K) (hperf : commutator K = ⊤)
    {z : G} (hz : z ∈ Subgroup.centralizer (K : Set G)) (hz1 : z ≠ 1) (hz3 : z ^ 3 = 1) :
    m - 2 ≤ CFSG.Open.twoLocalPrimeRank 3 G := by
  have hK4 : Nat.card F = (2 ^ 1) ^ 2 := by rw [hF]; norm_num
  have hcov : UnitaryCoverAt 1 m F := unitaryCoverAt hK4 hm (by rintro ⟨h, -⟩; omega)
  obtain ⟨φ, hφ⟩ := hcov.2 K ψ hψ hker hperf
  refine P9_U5a_sub_two_le hF (φ := φ) (fun g hg => ?_) hz hz1 hz3
  have h1 : LargeEvenProjMk (unitarySU 2 1 F m) g = 1 := by
    rw [← hφ g, hg, map_one]
  have h2 : (g : GL (Fin m) F) ∈ LargeEvenScalars (Fin m) F := by
    have h3 : g ∈ (LargeEvenProjMk (unitarySU 2 1 F m)).ker := h1
    rw [QuotientGroup.ker_mk'] at h3
    exact Subgroup.mem_subgroupOf.mp h3
  rw [largeEvenScalars_def] at h2
  obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp h2
  refine ⟨(u : F), ?_⟩
  rw [← hu, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]

end CFSG.StandardType.FrameRoute

end
