module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight8xK85
import CFSG.LocalAnalysis.SteinbergBQInvolutionHullStructure
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight65X0CardTypes
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneElevenEleven
public import CFSG.GroupTheory.ConjActionModPCore

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.UniquenessCase.UC22
  (Data DataExt Bar2 IsSpor IsSp4 IsG2 UniqueMax pRank_bar2_eq_of_odd)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F08 (IsSU5 R869 IsA6Z3)
open CFSG.LocalAnalysis.UniquenessCase.UC6S846 (SigmaStd)
open scoped commutatorElement

private theorem k86_disjoint {G : Type} [Group G] [Finite G] {L A : Subgroup G}
    (_hAL : A ≤ L) (hA : IsPGroup 3 A) :
    Disjoint (A.subgroupOf L) (CFSG.pCore 2 ↥L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact IsPGroup.disjoint_of_ne 3 2 (by norm_num) _ _ hA.comap_subtype
    (CFSG.pCore_isPGroup (p := 2) (G := ↥L))

private theorem k86_card {G : Type} [Group G] [Finite G] {L A : Subgroup G}
    (hAL : A ≤ L) (hA : IsPGroup 3 A) :
    Nat.card (imBar2 L A) = Nat.card A := by
  have hdisj := k86_disjoint hAL hA
  have h1 : Nat.card ((A.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) =
      Nat.card (A.subgroupOf L) := by
    apply CFSG.LocalAnalysis.UniquenessCase.UC6S846.card_map_of_disjoint_ker
    simpa only [QuotientGroup.ker_mk'] using hdisj
  rw [imBar2, h1]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv

private theorem k86_inj {G : Type} [Group G] [Finite G] {L Q A B : Subgroup G}
    (hQL : Q ≤ L) (hQ : IsPGroup 3 Q)
    (hAQ : A ≤ Q) (hBQ : B ≤ Q) (h : imBar2 L A = imBar2 L B) : A = B := by
  have hdisjQ : Disjoint (Q.subgroupOf L) (CFSG.pCore 2 ↥L) := k86_disjoint hQL hQ
  have key : ∀ a ∈ A, a ∈ B := by
    intro a ha
    have haL : a ∈ L := hQL (hAQ ha)
    let aL : ↥L := ⟨a, haL⟩
    have hπa : QuotientGroup.mk' (CFSG.pCore 2 ↥L) aL ∈ imBar2 L B := by
      rw [← h, imBar2]
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr ha)
    rw [imBar2] at hπa
    obtain ⟨b, hb, hbπ⟩ := Subgroup.mem_map.mp hπa
    have hbB : (b : G) ∈ B := Subgroup.mem_subgroupOf.mp hb
    have hbQ : (b : G) ∈ Q := hBQ hbB
    have hbQinv : (b : G) * a⁻¹ ∈ Q := Q.mul_mem hbQ (Q.inv_mem (hAQ ha))
    have hker : b * aL⁻¹ ∈ (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hbπ]
      exact mul_inv_cancel _
    have hmem : b * aL⁻¹ ∈ Q.subgroupOf L ⊓ CFSG.pCore 2 ↥L := by
      refine ⟨?_, ?_⟩
      · exact Subgroup.mem_subgroupOf.mpr hbQinv
      · rwa [QuotientGroup.ker_mk'] at hker
    have hone : b * aL⁻¹ = 1 := Subgroup.disjoint_def.mp hdisjQ hmem.1 hmem.2
    have hbeq : b = aL := mul_inv_eq_one.mp hone
    have hval : (b : G) = a := by rw [hbeq]
    simpa [hval] using hbB
  exact le_antisymm key (by
    intro b hb
    have hbL : b ∈ L := hQL (hBQ hb)
    let bL : ↥L := ⟨b, hbL⟩
    have hπb : QuotientGroup.mk' (CFSG.pCore 2 ↥L) bL ∈ imBar2 L A := by
      rw [h, imBar2]
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hb)
    rw [imBar2] at hπb
    obtain ⟨a, ha, haπ⟩ := Subgroup.mem_map.mp hπb
    have haA : (a : G) ∈ A := Subgroup.mem_subgroupOf.mp ha
    have haQ : (a : G) ∈ Q := hAQ haA
    have haQinv : (a : G) * b⁻¹ ∈ Q := Q.mul_mem haQ (Q.inv_mem (hBQ hb))
    have hker : a * bL⁻¹ ∈ (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, haπ]
      exact mul_inv_cancel _
    have hmem : a * bL⁻¹ ∈ Q.subgroupOf L ⊓ CFSG.pCore 2 ↥L := by
      refine ⟨?_, ?_⟩
      · exact Subgroup.mem_subgroupOf.mpr haQinv
      · rwa [QuotientGroup.ker_mk'] at hker
    have hone : a * bL⁻¹ = 1 := Subgroup.disjoint_def.mp hdisjQ hmem.1 hmem.2
    have haeq : a = bL := mul_inv_eq_one.mp hone
    have hval : (a : G) = b := by rw [haeq]
    simpa [hval] using haA)

private theorem k86_preimage {G : Type} [Group G] [Finite G] {L Q : Subgroup G}
    (_hQL : Q ≤ L) (Ā : Subgroup (Bar2 L)) (hĀ : Ā ≤ imBar2 L Q) :
    ∃ A : Subgroup G, A ≤ Q ∧ imBar2 L A = Ā := by
  let π := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  refine ⟨((Ā.comap π).map L.subtype) ⊓ Q, inf_le_right, ?_⟩
  ext x
  constructor
  · intro hx
    rw [imBar2] at hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    rw [← hyx]
    have hy1 : (y : G) ∈ (Ā.comap π).map L.subtype := (Subgroup.mem_subgroupOf.mp hy).1
    rw [Subgroup.mem_map] at hy1
    obtain ⟨z, hz, hzy⟩ := hy1
    have hzy' : z = y := Subtype.ext hzy
    rw [hzy'] at hz
    exact Subgroup.mem_comap.mp hz
  · intro hx
    rw [imBar2]
    have hxQ : x ∈ imBar2 L Q := hĀ hx
    rw [imBar2] at hxQ
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxQ
    refine Subgroup.mem_map.mpr ⟨y, ?_, hyx⟩
    refine Subgroup.mem_subgroupOf.mpr ?_
    refine ⟨?_, ?_⟩
    · change (y : G) ∈ (Ā.comap π).map L.subtype
      rw [Subgroup.mem_map]
      refine ⟨y, ?_, rfl⟩
      rw [Subgroup.mem_comap]
      rw [hyx]
      exact hx
    · exact Subgroup.mem_subgroupOf.mp hy

private theorem k86_zOf {G : Type} [Group G] [Finite G] {L Q : Subgroup G}
    (hQL : Q ≤ L) (hQ : IsPGroup 3 Q) :
    imBar2 L (ZOf Q) = ZOf (imBar2 L Q) := by
  let π := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  have hdisjQ : Disjoint (Q.subgroupOf L) (CFSG.pCore 2 ↥L) := k86_disjoint hQL hQ
  apply le_antisymm
  · intro x hx
    rw [imBar2] at hx
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hx
    have hzZ : (z : G) ∈ ZOf Q := Subgroup.mem_subgroupOf.mp hz
    rw [ZOf, Subgroup.mem_inf] at hzZ ⊢
    refine ⟨?_, ?_⟩
    · rw [imBar2]
      exact Subgroup.mem_map.mpr ⟨z, Subgroup.mem_subgroupOf.mpr hzZ.1, rfl⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [imBar2] at hy
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hy
      have hwQ : (w : G) ∈ Q := Subgroup.mem_subgroupOf.mp hw
      have hcomm : (w : G) * (z : G) = (z : G) * (w : G) :=
        Subgroup.mem_centralizer_iff.mp hzZ.2 (w : G) hwQ
      have hcomm' : w * z = z * w := Subtype.ext hcomm
      rw [← map_mul, ← map_mul, hcomm']
  · intro x hx
    rw [ZOf, Subgroup.mem_inf] at hx
    obtain ⟨hxQ, hxC⟩ := hx
    rw [imBar2] at hxQ
    obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hxQ
    rw [← hzx] at hxC
    rw [← hzx, imBar2]
    refine Subgroup.mem_map.mpr ⟨z, ?_, rfl⟩
    refine Subgroup.mem_subgroupOf.mpr ?_
    rw [ZOf, Subgroup.mem_inf]
    refine ⟨Subgroup.mem_subgroupOf.mp hz, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hqL : q ∈ L := hQL hq
    let qL : ↥L := ⟨q, hqL⟩
    have hqbar : π qL ∈ imBar2 L Q := by
      rw [imBar2]
      exact Subgroup.mem_map.mpr ⟨qL, Subgroup.mem_subgroupOf.mpr hq, rfl⟩
    have hcomm : π qL * π z = π z * π qL :=
      Subgroup.mem_centralizer_iff.mp hxC (π qL) hqbar
    have hker : (qL * z) * (z * qL)⁻¹ ∈ (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).ker := by
      rw [MonoidHom.mem_ker]
      have h2 : π ((qL * z) * (z * qL)⁻¹) = π qL * π z * (π z * π qL)⁻¹ := by
        simp only [map_mul, map_inv]
      rw [h2, hcomm]
      exact mul_inv_cancel _
    rw [QuotientGroup.ker_mk'] at hker
    have hmemQ : (qL * z) * (z * qL)⁻¹ ∈ Q.subgroupOf L := by
      refine (Q.subgroupOf L).mul_mem ?_ ?_
      · exact (Q.subgroupOf L).mul_mem (Subgroup.mem_subgroupOf.mpr hq) hz
      · exact (Q.subgroupOf L).inv_mem ((Q.subgroupOf L).mul_mem hz (Subgroup.mem_subgroupOf.mpr hq))
    have hmem : (qL * z) * (z * qL)⁻¹ ∈ Q.subgroupOf L ⊓ CFSG.pCore 2 ↥L := ⟨hmemQ, hker⟩
    have hone : (qL * z) * (z * qL)⁻¹ = 1 :=
      Subgroup.disjoint_def.mp hdisjQ hmem.1 hmem.2
    have hqq : qL * z = z * qL := mul_inv_eq_one.mp hone
    exact congrArg Subtype.val hqq

private theorem k86_conj {G : Type} [Group G] [Finite G] {L A M : Subgroup G}
    (hAL : A ≤ L) (hnorm : M ≤ Subgroup.normalizer (L : Set G)) {m : G} (hm : m ∈ M) :
    imBar2 L (A.map (MulAut.conj m).toMonoidHom) =
      (imBar2 L A).map
        ((CFSG.GroupTheory.conjModPCore 2 L M hnorm ⟨m, hm⟩).toMonoidHom) := by
  let α := CFSG.GroupTheory.conjModPCore 2 L M hnorm ⟨m, hm⟩
  ext x
  constructor
  · intro hx
    rw [imBar2] at hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    have hyA : (y : G) ∈ A.map (MulAut.conj m).toMonoidHom := Subgroup.mem_subgroupOf.mp hy
    rw [Subgroup.mem_map] at hyA
    obtain ⟨a, haA, hay⟩ := hyA
    have haL : a ∈ L := hAL haA
    have hmaL : m * a * m⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hnorm hm) a).mp haL
    have hay' : m * a * m⁻¹ = (y : G) := by
      have h := hay
      change MulAut.conj m a = (y : G) at h
      rwa [MulAut.conj_apply] at h
    rw [imBar2]
    refine Subgroup.mem_map.mpr ⟨QuotientGroup.mk (⟨a, haL⟩ : ↥L), ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨⟨a, haL⟩, Subgroup.mem_subgroupOf.mpr haA, rfl⟩
    · change CFSG.GroupTheory.conjModPCore 2 L M hnorm ⟨m, hm⟩
          (QuotientGroup.mk (⟨a, haL⟩ : ↥L)) = x
      rw [CFSG.GroupTheory.conjModPCore_mk]
      have hy_eq : (⟨m * a * m⁻¹, hmaL⟩ : ↥L) = y := Subtype.ext hay'
      rw [hy_eq]
      exact hyx
  · intro hx
    obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hx
    rw [imBar2] at hz
    obtain ⟨a, ha, haz⟩ := Subgroup.mem_map.mp hz
    have haA : (a : G) ∈ A := Subgroup.mem_subgroupOf.mp ha
    have haL : (a : G) ∈ L := hAL haA
    have hmaL : m * (a : G) * m⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hnorm hm) (a : G)).mp haL
    refine Subgroup.mem_map.mpr ⟨⟨m * (a : G) * m⁻¹, hmaL⟩, ?_, ?_⟩
    · refine Subgroup.mem_subgroupOf.mpr ?_
      rw [Subgroup.mem_map]
      exact ⟨(a : G), haA, rfl⟩
    · have h1 : α z = x := hzx
      rw [← haz] at h1
      change α (QuotientGroup.mk a) = x at h1
      rw [show α (QuotientGroup.mk a) =
          QuotientGroup.mk (⟨m * (a : G) * m⁻¹, hmaL⟩ : ↥L) from
        CFSG.GroupTheory.conjModPCore_mk 2 L M hnorm ⟨m, hm⟩ a] at h1
      exact h1

private theorem k86_conj_inner {G : Type} [Group G] [Finite G] {L A : Subgroup G}
    (hAL : A ≤ L) {g : ↥L} :
    imBar2 L (A.map (MulAut.conj (g : G)).toMonoidHom) =
      (imBar2 L A).map
        (MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥L) g)).toMonoidHom := by
  have h1 := k86_conj hAL (Subgroup.le_normalizer (H := L)) g.2
  rw [h1]
  congr 1
  simpa using congrArg MulEquiv.toMonoidHom
    (CFSG.GroupTheory.conjModPCore_apply_eq_conj_mk 2 L L
      (Subgroup.le_normalizer (H := L)) g.2 g.2)

private theorem k86_lift_aux {G : Type} [Group G] [Finite G] {L A B : Subgroup G}
    (hAL : A ≤ L) (hBL : B ≤ L) (_hA : IsPGroup 3 A) (hB : IsPGroup 3 B)
    (hAcard : Nat.card A = 3) (hBcard : Nat.card B = 3)
    (h : imBar2 L A = imBar2 L B) :
    ∃ k ∈ L, B = A.map (MulAut.conj k).toMonoidHom := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOle : CFSG.Open.pCoreOf 2 L ≤ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L
  have hOpg : IsPGroup 2 (CFSG.Open.pCoreOf 2 L) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) L
  have hBnormO : B ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 L : Set G) :=
    hBL.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
  have hOinfB : CFSG.Open.pCoreOf 2 L ⊓ B = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    exact Subgroup.disjoint_def.mp
      (IsPGroup.disjoint_of_ne 2 3 (by norm_num) _ _ hOpg hB) hx.1 hx.2
  let K := B ⊔ CFSG.Open.pCoreOf 2 L
  have hBK : B ≤ K := le_sup_left
  have hKL : K ≤ L := sup_le hBL hOle
  have hKcard : Nat.card K = Nat.card (CFSG.Open.pCoreOf 2 L) * Nat.card B := by
    rw [show K = CFSG.Open.pCoreOf 2 L ⊔ B from sup_comm B (CFSG.Open.pCoreOf 2 L)]
    exact CFSG.LocalAnalysis.RankThreeTheoremC.RankOne.card_sup_of_le_normalizer_of_inf_eq_bot
      hBnormO hOinfB
  have hfac : (Nat.card K).factorization 3 = 1 := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hOpg
    rw [hKcard, hBcard, hn]
    have h1 : (2 ^ n).factorization 3 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (by
        intro hd
        have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd
        norm_num at h32)
    rw [Nat.factorization_mul (pow_ne_zero n (by norm_num)) (by norm_num), Finsupp.add_apply, h1,
      Nat.Prime.factorization_self Nat.prime_three, zero_add]
  have hAK : A ≤ K := by
    intro x hx
    have hxL : x ∈ L := hAL hx
    have hxbar : QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨x, hxL⟩ ∈ imBar2 L B := by
      rw [← h, imBar2]
      exact Subgroup.mem_map.mpr ⟨⟨x, hxL⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    rw [imBar2] at hxbar
    obtain ⟨b, hb, hbbar⟩ := Subgroup.mem_map.mp hxbar
    have hbB : (b : G) ∈ B := Subgroup.mem_subgroupOf.mp hb
    have hker : (⟨x, hxL⟩ : ↥L) * b⁻¹ ∈ (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hbbar, mul_inv_cancel]
    rw [QuotientGroup.ker_mk'] at hker
    have hmemO : x * (b : G)⁻¹ ∈ CFSG.Open.pCoreOf 2 L := by
      rw [CFSG.Open.pCoreOf, Subgroup.mem_map]
      exact ⟨(⟨x, hxL⟩ : ↥L) * b⁻¹, hker, rfl⟩
    have hxeq : x = (x * (b : G)⁻¹) * (b : G) := by group
    rw [hxeq]
    exact K.mul_mem (Subgroup.mem_sup_right hmemO) (Subgroup.mem_sup_left hbB)
  have hSylA : IsSylowOf 3 A K :=
    CFSG.ABGLocalTools.isSylowOf_of_card hAK (by rw [hAcard, hfac]; norm_num)
  have hSylB : IsSylowOf 3 B K :=
    CFSG.ABGLocalTools.isSylowOf_of_card hBK (by rw [hBcard, hfac]; norm_num)
  obtain ⟨k, hkK, hk⟩ := hSylA.exists_mem_conj hSylB
  refine ⟨k, hKL hkK, ?_⟩
  ext x
  rw [hk x]
  constructor
  · intro hx
    rw [Subgroup.mem_map]
    refine ⟨k⁻¹ * x * k, hx, ?_⟩
    change MulAut.conj k (k⁻¹ * x * k) = x
    rw [MulAut.conj_apply]
    group
  · intro hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨a, ha, hax⟩ := hx
    have hax' : MulAut.conj k a = x := hax
    have : k⁻¹ * x * k = a := by rw [← hax', MulAut.conj_apply]; group
    rw [this]
    exact ha

private theorem k86_conj_lift {G : Type} [Group G] [Finite G] {L A B : Subgroup G}
    (hAL : A ≤ L) (hBL : B ≤ L) (hA : IsPGroup 3 A) (hB : IsPGroup 3 B)
    (hAcard : Nat.card A = 3) (hBcard : Nat.card B = 3)
    (g : Bar2 L) (h : imBar2 L B = (imBar2 L A).map (MulAut.conj g).toMonoidHom) :
    ∃ k ∈ L, B = A.map (MulAut.conj k).toMonoidHom := by
  obtain ⟨g₀, hg₀⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L) g
  let A' : Subgroup G := A.map (MulAut.conj (g₀ : G)).toMonoidHom
  have hA'L : A' ≤ L := by
    intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    change MulAut.conj (g₀ : G) a ∈ L
    rw [MulAut.conj_apply]
    exact (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer (H := L) g₀.2) a).mp (hAL ha)
  have hA'pg : IsPGroup 3 A' := hA.map (MulAut.conj (g₀ : G)).toMonoidHom
  have hA'card : Nat.card A' = 3 := by
    rw [show A' = A.map (MulAut.conj (g₀ : G)).toMonoidHom from rfl,
      Subgroup.card_map_of_injective (MulAut.conj (g₀ : G)).injective, hAcard]
  have hA'bar : imBar2 L A' = imBar2 L B := by
    rw [h]
    exact (by
      rw [show A' = A.map (MulAut.conj (g₀ : G)).toMonoidHom from rfl, k86_conj_inner hAL, hg₀])
  obtain ⟨k, hkL, hk⟩ := k86_lift_aux hA'L hBL hA'pg hB hA'card hBcard hA'bar
  refine ⟨k * g₀, L.mul_mem hkL g₀.2, ?_⟩
  rw [hk]
  rw [show A' = A.map (MulAut.conj (g₀ : G)).toMonoidHom from rfl]
  rw [Subgroup.map_map]
  congr 1
  ext a
  show MulAut.conj k (MulAut.conj (g₀ : G) a) = MulAut.conj (k * (g₀ : G)) a
  rw [MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply]
  group

private theorem k86_imBar2_mono {G : Type} [Group G] {L A B : Subgroup G} (h : A ≤ B) :
    imBar2 L A ≤ imBar2 L B := by
  rw [imBar2, imBar2]
  exact Subgroup.map_mono (Subgroup.subgroupOf_mono L h)

theorem r886_of_inputs {G : Type} [Group G] [Finite G] (D : Data G) (h882 : R882 D)
    (h885 : R885 D) (hIns : List880PRankInspection) (hJ2 : J2FivePRank)
    (hCl : J2ThreeClasses) (hA6 : J2CentralizerThreeA) : R886 D := by
  intro L P hset
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hJ, -, -⟩ := h885 L P hset
  have h2L : 2 ≤ CFSG.Open.pRank 5 L := by
    have h52 := (hJ2 (Bar2 L) hJ).1
    rw [pRank_bar2_eq_of_odd Nat.prime_five (by norm_num)] at h52
    omega
  have hnorm : D.M ≤ normalizer (L : Set G) :=
    normalizer_of_set880_of_two_le_pRank D h882 hIns hset Nat.prime_five le_rfl h2L
  have hLM : L ≤ D.M := CFSG.Quasithin.A3.subnormal_le hset.mem.1
  have hQ : IsSylowOf 3 (P ⊓ L) L := hset.sylow.inf_of_le_normalizer hLM hnorm
  have hS : IsSylowOf 3 (imBar2 L (P ⊓ L)) ⊤ := isSylowOf_imBar2 hQ
  have hQpg : IsPGroup 3 ↥(P ⊓ L) := ((CFSG.ABGLocalTools.isSylowOf_iff).1 hQ).2.1
  have hQL : P ⊓ L ≤ L := inf_le_right
  have hZLe : ZOf (P ⊓ L) ≤ L := (inf_le_left : ZOf (P ⊓ L) ≤ P ⊓ L).trans hQL
  have hZpg : IsPGroup 3 (ZOf (P ⊓ L)) := hQpg.to_le inf_le_left
  have hZbar : imBar2 L (ZOf (P ⊓ L)) = ZOf (imBar2 L (P ⊓ L)) := k86_zOf hQL hQpg
  have hZcard : Nat.card (ZOf (P ⊓ L)) = 3 := by
    have h1 := (hCl (Bar2 L) hJ (imBar2 L (P ⊓ L)) hS).1
    rw [← hZbar] at h1
    rw [k86_card hZLe hZpg] at h1
    exact h1
  refine ⟨hZcard, ?_, ?_, ?_⟩
  · obtain ⟨Ā, hĀS, hĀcard, hĀnot, hall⟩ := (hCl (Bar2 L) hJ (imBar2 L (P ⊓ L)) hS).2.1
    obtain ⟨X, hXQ, hXbar⟩ := k86_preimage hQL Ā hĀS
    have hXL : X ≤ L := hXQ.trans hQL
    have hXcard : Nat.card X = 3 := by
      rw [← k86_card hXL (hQpg.to_le hXQ), hXbar, hĀcard]
    have hXnot : X ∉ MConjSet D.M (ZOf (P ⊓ L)) := by
      rintro ⟨m, hm, hmX⟩
      apply hĀnot
      rw [← hXbar, hmX, k86_conj hZLe hnorm hm, hZbar]
      exact (hCl (Bar2 L) hJ (imBar2 L (P ⊓ L)) hS).2.2.1 _
    refine ⟨X, hXL, hXcard, hXnot, ?_⟩
    intro A hAL hAcard
    have hApg : IsPGroup 3 A := by
      rw [IsPGroup.iff_card]
      exact ⟨1, by rw [hAcard]; norm_num⟩
    have hAcard' : Nat.card (imBar2 L A) = 3 := by rw [k86_card hAL hApg, hAcard]
    rcases hall (imBar2 L A) hAcard' with h1 | h1
    · left
      rcases h1 with ⟨g, -, hg⟩
      rw [← hZbar] at hg
      obtain ⟨k, hkL, hk⟩ := k86_conj_lift hZLe hAL hZpg hApg hZcard hAcard g hg
      exact ⟨k, hLM hkL, hk⟩
    · right
      rcases h1 with ⟨g, -, hg⟩
      rw [← hXbar] at hg
      obtain ⟨k, hkL, hk⟩ := k86_conj_lift hXL hAL (hQpg.to_le hXQ) hApg hXcard hAcard g hg
      exact ⟨k, hLM hkL, hk⟩
  · intro m hm hle
    have h1 : imBar2 L ((ZOf (P ⊓ L)).map (MulAut.conj m).toMonoidHom) =
        (imBar2 L (ZOf (P ⊓ L))).map
          ((CFSG.GroupTheory.conjModPCore 2 L D.M hnorm ⟨m, hm⟩).toMonoidHom) :=
      k86_conj hZLe hnorm hm
    have h2 : (imBar2 L (ZOf (P ⊓ L))).map
          ((CFSG.GroupTheory.conjModPCore 2 L D.M hnorm ⟨m, hm⟩).toMonoidHom) ≤
        imBar2 L (P ⊓ L) := by
      rw [← h1]
      exact k86_imBar2_mono hle
    have h3 : (imBar2 L (ZOf (P ⊓ L))).map
          ((CFSG.GroupTheory.conjModPCore 2 L D.M hnorm ⟨m, hm⟩).toMonoidHom) ∈
        MConjSet (⊤ : Subgroup (Bar2 L)) (ZOf (imBar2 L (P ⊓ L))) := by
      rw [hZbar]
      exact (hCl (Bar2 L) hJ (imBar2 L (P ⊓ L)) hS).2.2.1 _
    have h4 : (imBar2 L (ZOf (P ⊓ L))).map
          ((CFSG.GroupTheory.conjModPCore 2 L D.M hnorm ⟨m, hm⟩).toMonoidHom) =
        ZOf (imBar2 L (P ⊓ L)) :=
      (hCl (Bar2 L) hJ (imBar2 L (P ⊓ L)) hS).2.2.2 _ h2 h3
    have hEq : imBar2 L ((ZOf (P ⊓ L)).map (MulAut.conj m).toMonoidHom) =
        imBar2 L (ZOf (P ⊓ L)) := by rw [h1, h4, hZbar]
    exact k86_inj hQL hQpg hle inf_le_left hEq
  · change IsA6Z3 ↥(centralizer (imBar2 L (ZOf (P ⊓ L)) : Set (Bar2 L)))
    rw [hZbar]
    exact hA6 (Bar2 L) hJ (imBar2 L (P ⊓ L)) hS

private theorem k88t_zpowers_three_cases {G : Type} [Group G] {z x : G} (hz : orderOf z = 3)
    (hx : x ∈ Subgroup.zpowers z) : x = 1 ∨ x = z ∨ x = z ^ 2 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← zpow_mod_orderOf z k, hz]
  have hcases : k % (↑(3 : ℕ) : ℤ) = 0 ∨ k % (↑(3 : ℕ) : ℤ) = 1 ∨
      k % (↑(3 : ℕ) : ℤ) = 2 := by
    have h0 : 0 ≤ k % (↑(3 : ℕ) : ℤ) := Int.emod_nonneg k (by norm_num)
    have h1 : k % (↑(3 : ℕ) : ℤ) < 3 := Int.emod_lt_of_pos k (by norm_num)
    omega
  rcases hcases with h | h | h <;> rw [h] <;> simp

private theorem k88t_conj_inv_of_conj {G : Type} [Group G] {q a b : G} (hb : b * q = q * b)
    (h : q * a * q⁻¹ = b * a) : q⁻¹ * a * q = b⁻¹ * a := by
  have hqa : q * a = b * a * q := by
    have := congrArg (· * q) h
    simpa [mul_assoc] using this
  have hqb : q⁻¹ * b = b * q⁻¹ := by
    calc q⁻¹ * b = q⁻¹ * (b * q) * q⁻¹ := by group
      _ = q⁻¹ * (q * b) * q⁻¹ := by rw [hb]
      _ = b * q⁻¹ := by group
  have h2 : a = b * (q⁻¹ * a * q) := by
    calc a = q⁻¹ * (b * a * q) := by
          have := congrArg (fun x => q⁻¹ * x) hqa
          simpa [mul_assoc] using this
      _ = b * (q⁻¹ * a * q) := by
          calc q⁻¹ * (b * a * q) = (q⁻¹ * b) * a * q := by group
            _ = (b * q⁻¹) * a * q := by rw [hqb]
            _ = b * (q⁻¹ * a * q) := by group
  have h4 := congrArg (fun x => b⁻¹ * x) h2
  have h5 : b⁻¹ * (b * (q⁻¹ * a * q)) = q⁻¹ * a * q := by group
  rw [h5] at h4
  exact h4.symm

private theorem k88t_conj_odd_pow {G : Type} [Group G] {s z : G} (hs : s * z * s⁻¹ = z⁻¹) {m : ℕ} (hm : Odd m) :
    (s ^ m) * z * (s ^ m)⁻¹ = z⁻¹ := by
  obtain ⟨j, rfl⟩ := hm
  have hs2 : s ^ 2 * z * (s ^ 2)⁻¹ = z := by
    rw [pow_two]
    calc (s * s) * z * (s * s)⁻¹ = s * (s * z * s⁻¹) * s⁻¹ := by group
      _ = s * z⁻¹ * s⁻¹ := by rw [hs]
      _ = (s * z * s⁻¹)⁻¹ := by group
      _ = z := by rw [hs, inv_inv]
  have hfix : ∀ i : ℕ, (s ^ 2) ^ i * z * ((s ^ 2) ^ i)⁻¹ = z := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
        rw [pow_succ]
        calc (s ^ 2) ^ i * (s ^ 2) * z * ((s ^ 2) ^ i * (s ^ 2))⁻¹
            = (s ^ 2) ^ i * ((s ^ 2) * z * (s ^ 2)⁻¹) * ((s ^ 2) ^ i)⁻¹ := by group
          _ = (s ^ 2) ^ i * z * ((s ^ 2) ^ i)⁻¹ := by rw [hs2]
          _ = z := ih
  have hsp : s ^ (2 * j + 1) = (s ^ 2) ^ j * s := by
    rw [pow_add, pow_mul, pow_one]
  rw [hsp]
  calc ((s ^ 2) ^ j * s) * z * ((s ^ 2) ^ j * s)⁻¹
      = (s ^ 2) ^ j * (s * z * s⁻¹) * ((s ^ 2) ^ j)⁻¹ := by group
    _ = (s ^ 2) ^ j * z⁻¹ * ((s ^ 2) ^ j)⁻¹ := by rw [hs]
    _ = ((s ^ 2) ^ j * z * ((s ^ 2) ^ j)⁻¹)⁻¹ := by group
    _ = z⁻¹ := by rw [hfix]

private theorem k88t_exists_conj_ne_of_not_mem_centralizer {G : Type} [Group G] {H : Subgroup G} {z : G}
    (hz : z ∉ Subgroup.centralizer (H : Set G)) : ∃ q ∈ H, q * z * q⁻¹ ≠ z := by
  by_contra h
  apply hz
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  by_contra hne
  have hfix : q * z * q⁻¹ = z := by
    by_contra hc
    exact h ⟨q, hq, hc⟩
  exact hne (by
    have := congrArg (· * q) hfix
    simpa [mul_assoc] using this)

private theorem k88t_eq_zpowers_of_card_three {G : Type} [Group G] [Finite G] {H : Subgroup G} {z : G}
    (hzH : z ∈ H) (hcard : Nat.card H = 3) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) :
    H = Subgroup.zpowers z := by
  have hord : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  symm
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzH) ?_
  rw [Nat.card_zpowers, hord, hcard]

theorem exists_two_element_of_transvections {G : Type} [Group G] [Finite G]
    {A Q₁ Q₂ Z₁ Z₂ B₁ B₂ : Subgroup G} (hA : IsElemAbelian 3 A) (hAcard : Nat.card A = 27)
    (hQ₁ : Q₁ ≤ normalizer (A : Set G)) (hQ₂ : Q₂ ≤ normalizer (A : Set G))
    (hZ₁ : ⁅A, Q₁⁆ = Z₁) (hZ₂ : ⁅A, Q₂⁆ = Z₂)
    (hB₁ : A ⊓ centralizer (Q₁ : Set G) = B₁) (hB₂ : A ⊓ centralizer (Q₂ : Set G) = B₂)
    (hZ₁c : Nat.card Z₁ = 3) (hZ₂c : Nat.card Z₂ = 3)
    (hB₁c : Nat.card B₁ = 9) (hB₂c : Nat.card B₂ = 9)
    (hZB₁ : Z₁ ≤ B₁) (hZB₂ : Z₂ ≤ B₂) (hZ₂B₁ : ¬ Z₂ ≤ B₁) (hZ₁B₂ : ¬ Z₁ ≤ B₂) :
    ∃ t ∈ Q₁ ⊔ Q₂, (∃ k : ℕ, orderOf t = 2 ^ k) ∧
      (∀ x ∈ Z₁ ⊔ Z₂, t * x * t⁻¹ = x⁻¹) ∧
      Nat.card ↥(A ⊓ centralizer ({t} : Set G)) = 3 ∧
      A ⊓ centralizer ({t} : Set G) ≤ centralizer ((Q₁ ⊔ Q₂ : Subgroup G) : Set G) ∧
      ∀ U : Subgroup G, U ≤ A → Nat.card U = 3 → t ∈ normalizer (U : Set G) →
        U ≤ Z₁ ⊔ Z₂ ∨ U = A ⊓ centralizer ({t} : Set G) := by
  classical
  have hcommA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy => IsElemAbelian.comm hA hx hy
  have hpowA : ∀ x ∈ A, x ^ 3 = 1 := hA.2
  have hB1A : B₁ ≤ A := hB₁ ▸ inf_le_left
  have hB2A : B₂ ≤ A := hB₂ ▸ inf_le_left
  have hB1cent : B₁ ≤ Subgroup.centralizer (Q₁ : Set G) := hB₁ ▸ inf_le_right
  have hB2cent : B₂ ≤ Subgroup.centralizer (Q₂ : Set G) := hB₂ ▸ inf_le_right
  have hZ1A : Z₁ ≤ A := le_trans hZB₁ hB1A
  have hZ2A : Z₂ ≤ A := le_trans hZB₂ hB2A
  have hHnorm : Q₁ ⊔ Q₂ ≤ Subgroup.normalizer (A : Set G) := sup_le hQ₁ hQ₂
  obtain ⟨z₂, hz₂Z₂, hz₂B₁⟩ := Set.not_subset.mp hZ₂B₁
  have hz₂ne : z₂ ≠ 1 := fun h => hz₂B₁ (h ▸ B₁.one_mem)
  have hz₂A : z₂ ∈ A := hZ2A hz₂Z₂
  have hz₂B₂ : z₂ ∈ B₂ := hZB₂ hz₂Z₂
  have hz₂cent₂ : z₂ ∈ Subgroup.centralizer (Q₂ : Set G) := hB2cent hz₂B₂
  have hz₂pow : z₂ ^ 3 = 1 := hpowA z₂ hz₂A
  have hord₂ : orderOf z₂ = 3 := orderOf_eq_prime hz₂pow hz₂ne
  have hZ₂_eq : Z₂ = Subgroup.zpowers z₂ :=
    k88t_eq_zpowers_of_card_three hz₂Z₂ hZ₂c hz₂pow hz₂ne
  have hz₂notcent₁ : z₂ ∉ Subgroup.centralizer (Q₁ : Set G) := by
    intro h
    exact hz₂B₁ (hB₁ ▸ ⟨hz₂A, h⟩)
  obtain ⟨q₁, hq₁Q₁, hq₁ne⟩ := k88t_exists_conj_ne_of_not_mem_centralizer hz₂notcent₁
  let z₁ : G := ⁅q₁, z₂⁆
  have hz₁def : z₁ = ⁅q₁, z₂⁆ := rfl
  have hq₁norm : q₁ ∈ Subgroup.normalizer (A : Set G) :=
    hHnorm (Subgroup.mem_sup_left hq₁Q₁)
  have hq₁z₂A : q₁ * z₂ * q₁⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hq₁norm z₂).mp hz₂A
  have hz₁A : z₁ ∈ A := by
    rw [hz₁def, commutatorElement_def]
    exact A.mul_mem hq₁z₂A (A.inv_mem hz₂A)
  have hz₁Z₁ : z₁ ∈ Z₁ := by
    have hmem : ⁅z₂, q₁⁆ ∈ Z₁ := by
      have := Subgroup.commutator_mem_commutator (H₁ := A) (H₂ := Q₁) hz₂A hq₁Q₁
      rwa [hZ₁] at this
    rw [hz₁def, ← commutatorElement_inv z₂ q₁]
    exact Z₁.inv_mem hmem
  have hz₁ne : z₁ ≠ 1 := by
    intro h
    apply hq₁ne
    have hc : q₁ * z₂ * q₁⁻¹ * z₂⁻¹ = 1 := by
      rw [← commutatorElement_def]
      exact h
    have := congrArg (· * z₂) hc
    simpa [mul_assoc] using this
  have hz₁pow : z₁ ^ 3 = 1 := hpowA z₁ hz₁A
  have hZ₁_eq : Z₁ = Subgroup.zpowers z₁ :=
    k88t_eq_zpowers_of_card_three hz₁Z₁ hZ₁c hz₁pow hz₁ne
  have hR1 : q₁ * z₁ * q₁⁻¹ = z₁ := by
    have hmem : z₁ ∈ Subgroup.centralizer (Q₁ : Set G) := hB1cent (hZB₁ hz₁Z₁)
    have h := Subgroup.mem_centralizer_iff.mp hmem q₁ hq₁Q₁
    rw [h, mul_assoc, mul_inv_cancel, mul_one]
  have hR2 : q₁ * z₂ * q₁⁻¹ = z₁ * z₂ := by
    have hz₁eq : z₁ = q₁ * z₂ * q₁⁻¹ * z₂⁻¹ := by rw [hz₁def, commutatorElement_def]
    rw [hz₁eq]
    group
  have hz₁B₂ : z₁ ∉ B₂ := by
    intro h
    apply hZ₁B₂
    rw [hZ₁_eq]
    exact Subgroup.zpowers_le.mpr h
  have hz₁notcent₂ : z₁ ∉ Subgroup.centralizer (Q₂ : Set G) := by
    intro h
    exact hz₁B₂ (hB₂ ▸ ⟨hz₁A, h⟩)
  obtain ⟨q₂, hq₂Q₂, hq₂ne⟩ := k88t_exists_conj_ne_of_not_mem_centralizer hz₁notcent₂
  let x : G := ⁅q₂, z₁⁆
  have hxdef : x = ⁅q₂, z₁⁆ := rfl
  have hxZ₂ : x ∈ Z₂ := by
    have hmem : ⁅z₁, q₂⁆ ∈ Z₂ := by
      have := Subgroup.commutator_mem_commutator (H₁ := A) (H₂ := Q₂) hz₁A hq₂Q₂
      rwa [hZ₂] at this
    rw [hxdef, ← commutatorElement_inv z₁ q₂]
    exact Z₂.inv_mem hmem
  have hxne : x ≠ 1 := by
    intro h
    apply hq₂ne
    have hc : q₂ * z₁ * q₂⁻¹ * z₁⁻¹ = 1 := by
      rw [← commutatorElement_def]
      exact h
    have := congrArg (· * z₁) hc
    simpa [mul_assoc] using this
  have hxpow : x ^ 3 = 1 := hpowA x (hZ2A hxZ₂)
  have hordx : orderOf x = 3 := orderOf_eq_prime hxpow hxne
  have hxzp : x ∈ Subgroup.zpowers z₂ := by
    rw [← hZ₂_eq]; exact hxZ₂
  have hxcases := k88t_zpowers_three_cases hord₂ hxzp
  have hq₂cent₂ : q₂ * z₂ * q₂⁻¹ = z₂ := by
    have h := Subgroup.mem_centralizer_iff.mp hz₂cent₂ q₂ hq₂Q₂
    rw [h, mul_assoc, mul_inv_cancel, mul_one]
  have hq₂z₁ : q₂ * z₁ * q₂⁻¹ = x * z₁ := by
    have hxeq : x = q₂ * z₁ * q₂⁻¹ * z₁⁻¹ := by rw [hxdef, commutatorElement_def]
    rw [hxeq]; group
  have hR34 : ∃ q ∈ Q₂, q * z₁ * q⁻¹ = z₁ * z₂ ∧ q * z₂ * q⁻¹ = z₂ := by
    rcases hxcases with hx1 | hxz | hxz2
    · exact absurd hx1 hxne
    · refine ⟨q₂, hq₂Q₂, ?_, hq₂cent₂⟩
      rw [hq₂z₁, hxz]
      exact hcommA z₂ (hZ2A hz₂Z₂) z₁ (hZ1A hz₁Z₁)
    · refine ⟨q₂⁻¹, Q₂.inv_mem hq₂Q₂, ?_, ?_⟩
      · rw [inv_inv]
        have hxq : x * q₂ = q₂ * x :=
          (Subgroup.mem_centralizer_iff.mp (hB2cent (hZB₂ hxZ₂)) q₂ hq₂Q₂).symm
        have hinv := k88t_conj_inv_of_conj hxq hq₂z₁
        rw [hinv, hxz2]
        have hz₂sq_inv : (z₂ ^ 2)⁻¹ = z₂ := by
          have h : z₂ ^ 2 * z₂ = 1 := by
            have h3 : z₂ ^ 3 = 1 := by simpa [hord₂] using pow_orderOf_eq_one z₂
            rw [← pow_succ]
            exact h3
          exact inv_eq_of_mul_eq_one_right h
        rw [hz₂sq_inv]
        exact hcommA z₂ (hZ2A hz₂Z₂) z₁ (hZ1A hz₁Z₁)
      · rw [inv_inv]
        have h := Subgroup.mem_centralizer_iff.mp hz₂cent₂ q₂ hq₂Q₂
        calc q₂⁻¹ * z₂ * q₂ = q₂⁻¹ * (z₂ * q₂) := by group
          _ = q₂⁻¹ * (q₂ * z₂) := by rw [← h]
          _ = z₂ := by group
  obtain ⟨q₂', hq₂'Q₂, hR4, hR3⟩ := hR34
  have hq₂'inv_z₁ : q₂'⁻¹ * z₁ * q₂' = z₁ * z₂⁻¹ := by
    have hb : z₂ * q₂' = q₂' * z₂ :=
      (Subgroup.mem_centralizer_iff.mp hz₂cent₂ q₂' hq₂'Q₂).symm
    have h : q₂' * z₁ * q₂'⁻¹ = z₂ * z₁ := by
      rw [hR4]
      exact hcommA z₁ (hZ1A hz₁Z₁) z₂ (hZ2A hz₂Z₂)
    have := k88t_conj_inv_of_conj hb h
    rw [this]
    exact hcommA z₂⁻¹ (A.inv_mem (hZ2A hz₂Z₂)) z₁ (hZ1A hz₁Z₁)
  have hq₂'inv_z₂ : q₂'⁻¹ * z₂ * q₂' = z₂ := by
    have h := Subgroup.mem_centralizer_iff.mp hz₂cent₂ q₂' hq₂'Q₂
    calc q₂'⁻¹ * z₂ * q₂' = q₂'⁻¹ * (z₂ * q₂') := by group
      _ = q₂'⁻¹ * (q₂' * z₂) := by rw [← h]
      _ = z₂ := by group
  let hh : G := q₁ * q₂'⁻¹ * q₁
  have hhdef : hh = q₁ * q₂'⁻¹ * q₁ := rfl
  have hh_z₁ : hh * z₁ * hh⁻¹ = z₂⁻¹ := by
    rw [hhdef]
    calc (q₁ * q₂'⁻¹ * q₁) * z₁ * (q₁ * q₂'⁻¹ * q₁)⁻¹
        = q₁ * q₂'⁻¹ * (q₁ * z₁ * q₁⁻¹) * q₂' * q₁⁻¹ := by group
      _ = q₁ * q₂'⁻¹ * z₁ * q₂' * q₁⁻¹ := by rw [hR1]
      _ = q₁ * (q₂'⁻¹ * z₁ * q₂') * q₁⁻¹ := by group
      _ = q₁ * (z₁ * z₂⁻¹) * q₁⁻¹ := by rw [hq₂'inv_z₁]
      _ = (q₁ * z₁ * q₁⁻¹) * (q₁ * z₂⁻¹ * q₁⁻¹) := by group
      _ = z₁ * (q₁ * z₂⁻¹ * q₁⁻¹) := by rw [hR1]
      _ = z₁ * (q₁ * z₂ * q₁⁻¹)⁻¹ := by
            rw [show q₁ * z₂⁻¹ * q₁⁻¹ = (q₁ * z₂ * q₁⁻¹)⁻¹ by group]
      _ = z₁ * (z₁ * z₂)⁻¹ := by rw [hR2]
      _ = z₂⁻¹ := by
            rw [mul_inv_rev, show z₁ * (z₂⁻¹ * z₁⁻¹) = (z₁ * z₂⁻¹) * z₁⁻¹ by group,
              hcommA z₁ (hZ1A hz₁Z₁) z₂⁻¹ (A.inv_mem (hZ2A hz₂Z₂))]
            group
  have hh_z₂ : hh * z₂ * hh⁻¹ = z₁ := by
    rw [hhdef]
    calc (q₁ * q₂'⁻¹ * q₁) * z₂ * (q₁ * q₂'⁻¹ * q₁)⁻¹
        = q₁ * q₂'⁻¹ * (q₁ * z₂ * q₁⁻¹) * q₂' * q₁⁻¹ := by group
      _ = q₁ * q₂'⁻¹ * (z₁ * z₂) * q₂' * q₁⁻¹ := by rw [hR2]
      _ = q₁ * (q₂'⁻¹ * z₁ * q₂') * (q₂'⁻¹ * z₂ * q₂') * q₁⁻¹ := by group
      _ = q₁ * (z₁ * z₂⁻¹) * z₂ * q₁⁻¹ := by rw [hq₂'inv_z₁, hq₂'inv_z₂]
      _ = q₁ * z₁ * q₁⁻¹ := by group
      _ = z₁ := hR1
  let s : G := hh ^ 2
  have hsdef : s = hh ^ 2 := rfl
  have hs_z₁ : s * z₁ * s⁻¹ = z₁⁻¹ := by
    rw [hsdef, pow_two]
    calc (hh * hh) * z₁ * (hh * hh)⁻¹ = hh * (hh * z₁ * hh⁻¹) * hh⁻¹ := by group
      _ = hh * z₂⁻¹ * hh⁻¹ := by rw [hh_z₁]
      _ = (hh * z₂ * hh⁻¹)⁻¹ := by group
      _ = z₁⁻¹ := by rw [hh_z₂]
  have hs_z₂ : s * z₂ * s⁻¹ = z₂⁻¹ := by
    rw [hsdef, pow_two]
    calc (hh * hh) * z₂ * (hh * hh)⁻¹ = hh * (hh * z₂ * hh⁻¹) * hh⁻¹ := by group
      _ = hh * z₁ * hh⁻¹ := by rw [hh_z₂]
      _ = z₂⁻¹ := hh_z₁
  obtain ⟨k, m, hm_odd, hsord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos s).ne'
  let t : G := s ^ m
  have htdef : t = s ^ m := rfl
  have ht_z₁ : t * z₁ * t⁻¹ = z₁⁻¹ := by
    rw [htdef]; exact k88t_conj_odd_pow hs_z₁ hm_odd
  have ht_z₂ : t * z₂ * t⁻¹ = z₂⁻¹ := by
    rw [htdef]; exact k88t_conj_odd_pow hs_z₂ hm_odd
  have ht_order : ∃ j : ℕ, orderOf t = 2 ^ j := by
    have hpow : t ^ (2 ^ k) = 1 := by
      rw [htdef, ← pow_mul, mul_comm m (2 ^ k), ← hsord]
      exact pow_orderOf_eq_one s
    have hdvd : orderOf t ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hpow
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact ⟨j, hj⟩
  have htH : t ∈ Q₁ ⊔ Q₂ := by
    have hq₂'inv_mem : q₂'⁻¹ ∈ Q₂ := Q₂.inv_mem hq₂'Q₂
    have hhH : hh ∈ Q₁ ⊔ Q₂ := by
      rw [hhdef]
      exact (Q₁ ⊔ Q₂).mul_mem ((Q₁ ⊔ Q₂).mul_mem (Subgroup.mem_sup_left hq₁Q₁)
        (Subgroup.mem_sup_right hq₂'inv_mem)) (Subgroup.mem_sup_left hq₁Q₁)
    have hsH : s ∈ Q₁ ⊔ Q₂ := by rw [hsdef]; exact (Q₁ ⊔ Q₂).pow_mem hhH 2
    rw [htdef]; exact (Q₁ ⊔ Q₂).pow_mem hsH m
  let Am : Subgroup G :=
    { carrier := {y | y ∈ A ∧ t * y * t⁻¹ = y⁻¹}
      one_mem' := ⟨A.one_mem, by simp⟩
      mul_mem' := by
        rintro a b ⟨haA, ha⟩ ⟨hbA, hb⟩
        refine ⟨A.mul_mem haA hbA, ?_⟩
        calc t * (a * b) * t⁻¹ = (t * a * t⁻¹) * (t * b * t⁻¹) := by group
          _ = a⁻¹ * b⁻¹ := by rw [ha, hb]
          _ = (a * b)⁻¹ := by
                rw [mul_inv_rev]
                exact hcommA a⁻¹ (A.inv_mem haA) b⁻¹ (A.inv_mem hbA)
      inv_mem' := by
        rintro a ⟨haA, ha⟩
        refine ⟨A.inv_mem haA, ?_⟩
        calc t * a⁻¹ * t⁻¹ = (t * a * t⁻¹)⁻¹ := by group
          _ = (a⁻¹)⁻¹ := by rw [ha] }
  let A0 : Subgroup G :=
    { carrier := {y | y ∈ A ∧ t * y * t⁻¹ = y}
      one_mem' := ⟨A.one_mem, by simp⟩
      mul_mem' := by
        rintro a b ⟨haA, ha⟩ ⟨hbA, hb⟩
        refine ⟨A.mul_mem haA hbA, ?_⟩
        calc t * (a * b) * t⁻¹ = (t * a * t⁻¹) * (t * b * t⁻¹) := by group
          _ = a * b := by rw [ha, hb]
      inv_mem' := by
        rintro a ⟨haA, ha⟩
        refine ⟨A.inv_mem haA, ?_⟩
        calc t * a⁻¹ * t⁻¹ = (t * a * t⁻¹)⁻¹ := by group
          _ = a⁻¹ := by rw [ha] }
  have hA0_eq : A0 = A ⊓ Subgroup.centralizer ({t} : Set G) := by
    ext a
    constructor
    · rintro ⟨haA, ha⟩
      refine ⟨haA, ?_⟩
      change a ∈ Subgroup.centralizer ({t} : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      rw [Set.mem_singleton_iff] at hu
      subst hu
      calc t * a = (t * a * t⁻¹) * t := by group
        _ = a * t := by rw [ha]
    · rintro ⟨haA, ha⟩
      refine ⟨haA, ?_⟩
      change a ∈ Subgroup.centralizer ({t} : Set G) at ha
      rw [Subgroup.mem_centralizer_iff] at ha
      have h := ha t (Set.mem_singleton t)
      rw [h]
      group
  have hAmA0 : Am ⊓ A0 = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro a ha
    rw [Subgroup.mem_inf] at ha
    obtain ⟨⟨haA, hainv⟩, ⟨-, hafix⟩⟩ := ha
    rw [Subgroup.mem_bot]
    have ha2 : a ^ 2 = 1 := by
      have haeq : a = a⁻¹ := by rw [← hainv, hafix]
      rw [pow_two]
      have h := congrArg (fun x => x * a) haeq
      rw [h]
      exact inv_mul_cancel a
    calc a = a * 1 := (mul_one a).symm
      _ = a * a ^ 2 := by rw [ha2]
      _ = a ^ 3 := (pow_succ' a 2).symm
      _ = 1 := hpowA a haA
  have hAmA0norm : Am ≤ Subgroup.normalizer (A0 : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro a ha b hb
    have haA : a ∈ A := ha.1
    have hbA : b ∈ A := hb.1
    have : a * b * a⁻¹ = b := by
      rw [hcommA a haA b hbA]
      group
    rw [this]
    exact hb
  have hprod := CFSG.LocalAnalysis.SteinbergBQ.card_sup_mul_card_inf_of_normalizes hAmA0norm
  have hprod' : Nat.card ↥(Am ⊔ A0) = Nat.card Am * Nat.card A0 := by
    rw [hAmA0, Subgroup.card_bot, mul_one] at hprod
    exact hprod
  have hAmA0_le_A : Am ⊔ A0 ≤ A := sup_le (fun x hx => hx.1) (fun x hx => hx.1)
  have hcard_sup : Nat.card ↥(Am ⊔ A0) ≤ 27 := by
    have := Subgroup.card_le_of_le hAmA0_le_A
    rwa [hAcard] at this
  have hAmul : Nat.card Am * Nat.card A0 ≤ 27 := by
    rw [← hprod']; exact hcard_sup
  have hz₁Am : z₁ ∈ Am := ⟨hz₁A, ht_z₁⟩
  have hz₂Am : z₂ ∈ Am := ⟨hz₂A, ht_z₂⟩
  have hZsup_le_Am : Z₁ ⊔ Z₂ ≤ Am := by
    rw [hZ₁_eq, hZ₂_eq]
    exact sup_le (Subgroup.zpowers_le.mpr hz₁Am) (Subgroup.zpowers_le.mpr hz₂Am)
  have hZ₁neZ₂ : Z₁ ≠ Z₂ := by
    intro h
    apply hZ₁B₂
    rw [h]
    exact hZB₂
  have hcardZ : Nat.card ↥(Z₁ ⊔ Z₂) = 9 :=
    card_sup_eq_nine_of_card_three_of_ne hZ₁c hZ₂c hZ₁neZ₂
      (fun x hx y hy => hcommA x (hZ1A hx) y (hZ2A hy))
  have hAm_ge : 9 ≤ Nat.card Am := by
    rw [← hcardZ]
    exact Subgroup.card_le_of_le hZsup_le_Am
  have hB1B2norm : B₁ ≤ Subgroup.normalizer (B₂ : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro a ha b hb
    have : a * b * a⁻¹ = b := by
      rw [hcommA a (hB1A ha) b (hB2A hb)]
      group
    rw [this]; exact hb
  have hBprod := CFSG.LocalAnalysis.SteinbergBQ.card_sup_mul_card_inf_of_normalizes hB1B2norm
  have hBsup_le : Nat.card ↥(B₁ ⊔ B₂) ≤ 27 := by
    have := Subgroup.card_le_of_le (sup_le hB1A hB2A)
    rwa [hAcard] at this
  have hBinf_ge : 3 ≤ Nat.card ↥(B₁ ⊓ B₂) := by
    rw [hB₁c, hB₂c] at hBprod
    by_contra h
    have hle2 : Nat.card ↥(B₁ ⊓ B₂) ≤ 2 := by omega
    have hmul : Nat.card ↥(B₁ ⊔ B₂) * Nat.card ↥(B₁ ⊓ B₂) ≤ 27 * 2 :=
      Nat.mul_le_mul hBsup_le hle2
    omega
  have hC₁ : B₁ ⊓ B₂ ≤ Subgroup.centralizer (Q₁ : Set G) := le_trans inf_le_left hB1cent
  have hC₂ : B₁ ⊓ B₂ ≤ Subgroup.centralizer (Q₂ : Set G) := le_trans inf_le_right hB2cent
  have hq₁C : q₁ ∈ Subgroup.centralizer ((B₁ ⊓ B₂ : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (Subgroup.mem_centralizer_iff.mp (hC₁ hb) q₁ hq₁Q₁).symm
  have hq₂'C : q₂' ∈ Subgroup.centralizer ((B₁ ⊓ B₂ : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (Subgroup.mem_centralizer_iff.mp (hC₂ hb) q₂' hq₂'Q₂).symm
  have hhC : hh ∈ Subgroup.centralizer ((B₁ ⊓ B₂ : Subgroup G) : Set G) := by
    rw [hhdef]
    exact (Subgroup.centralizer _).mul_mem ((Subgroup.centralizer _).mul_mem hq₁C
      ((Subgroup.centralizer _).inv_mem hq₂'C)) hq₁C
  have hsC : s ∈ Subgroup.centralizer ((B₁ ⊓ B₂ : Subgroup G) : Set G) := by
    rw [hsdef]; exact (Subgroup.centralizer _).pow_mem hhC 2
  have htC : t ∈ Subgroup.centralizer ((B₁ ⊓ B₂ : Subgroup G) : Set G) := by
    rw [htdef]; exact (Subgroup.centralizer _).pow_mem hsC m
  have hBinf_le_A0 : B₁ ⊓ B₂ ≤ A0 := by
    intro b hb
    rw [Subgroup.mem_inf] at hb
    refine ⟨hB1A hb.1, ?_⟩
    have h := Subgroup.mem_centralizer_iff.mp htC b hb
    rw [← h, mul_assoc, mul_inv_cancel, mul_one]
  have hA0_ge : 3 ≤ Nat.card A0 :=
    le_trans hBinf_ge (Subgroup.card_le_of_le hBinf_le_A0)
  have hA0_card : Nat.card A0 = 3 := by
    have hb3 : Nat.card A0 ≤ 3 := by
      by_contra h
      have h4 : 4 ≤ Nat.card A0 := by omega
      have : 9 * 4 ≤ Nat.card Am * Nat.card A0 := Nat.mul_le_mul hAm_ge h4
      omega
    omega
  have hAm_card : Nat.card Am = 9 := by
    have : Nat.card Am * 3 ≤ 27 := by
      calc Nat.card Am * 3 ≤ Nat.card Am * Nat.card A0 := Nat.mul_le_mul_left _ (by omega)
        _ ≤ 27 := hAmul
    omega
  have hAm_eq : Am = Z₁ ⊔ Z₂ :=
    (Subgroup.eq_of_le_of_card_ge hZsup_le_Am (by rw [hcardZ, hAm_card])).symm
  have hA0_eq2 : A0 = B₁ ⊓ B₂ :=
    (Subgroup.eq_of_le_of_card_ge hBinf_le_A0 (by rw [hA0_card]; exact hBinf_ge)).symm
  have hcentral_card : Nat.card ↥(A ⊓ Subgroup.centralizer ({t} : Set G)) = 3 := by
    rw [← hA0_eq, hA0_card]
  have hcent_le : A ⊓ Subgroup.centralizer ({t} : Set G) ≤
      Subgroup.centralizer ((Q₁ ⊔ Q₂ : Subgroup G) : Set G) := by
    rw [← hA0_eq, hA0_eq2]
    intro y hy
    rw [Subgroup.mem_inf] at hy
    have hy1 : y ∈ Subgroup.centralizer (Q₁ : Set G) := hB1cent hy.1
    have hy2 : y ∈ Subgroup.centralizer (Q₂ : Set G) := hB2cent hy.2
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hsup : Q₁ ⊔ Q₂ ≤ Subgroup.centralizer ({y} : Set G) := by
      refine sup_le ?_ ?_
      · intro q hq
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        rw [Set.mem_singleton_iff] at hw
        subst hw
        exact (Subgroup.mem_centralizer_iff.mp hy1 q hq).symm
      · intro q hq
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        rw [Set.mem_singleton_iff] at hw
        subst hw
        exact (Subgroup.mem_centralizer_iff.mp hy2 q hq).symm
    have hu' := hsup hu
    rw [Subgroup.mem_centralizer_iff] at hu'
    exact (hu' y (Set.mem_singleton y)).symm
  refine ⟨t, htH, ht_order, ?_, hcentral_card, hcent_le, ?_⟩
  · intro y hy
    exact (hZsup_le_Am hy).2
  · intro U hUA hUcard htU
    have hnt : Nontrivial U := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨u, hu⟩ := @exists_ne U hnt (1 : U)
    have huU : (u : G) ∈ U := u.2
    have hune : (u : G) ≠ 1 := fun h => hu (Subtype.ext h)
    have hupow : (u : G) ^ 3 = 1 := hpowA (u : G) (hUA huU)
    have huord : orderOf (u : G) = 3 := orderOf_eq_prime hupow hune
    have hU_eq : U = Subgroup.zpowers (u : G) :=
      k88t_eq_zpowers_of_card_three huU hUcard hupow hune
    have htu_mem : t * (u : G) * t⁻¹ ∈ U := by
      rw [Subgroup.mem_normalizer_iff] at htU
      exact (htU (u : G)).mp huU
    have htu_zp : t * (u : G) * t⁻¹ ∈ Subgroup.zpowers (u : G) := by
      rw [← hU_eq]; exact htu_mem
    have htune : t * (u : G) * t⁻¹ ≠ 1 := by
      intro h
      have : (u : G) = 1 := by
        have := congrArg (fun y => t⁻¹ * y * t) h
        simpa [mul_assoc] using this
      exact hune this
    rcases k88t_zpowers_three_cases huord htu_zp with h1 | h1 | h1
    · exact absurd h1 htune
    · right
      have huA0 : (u : G) ∈ A0 := ⟨hUA huU, h1⟩
      have hle : U ≤ A0 := by rw [hU_eq]; exact Subgroup.zpowers_le.mpr huA0
      have : U = A0 := Subgroup.eq_of_le_of_card_ge hle (by rw [hA0_card, hUcard])
      rw [this, hA0_eq]
    · left
      have hu2 : (u : G) ^ 2 = (u : G)⁻¹ :=
        eq_inv_of_mul_eq_one_right (a := (u : G)) (b := (u : G) ^ 2)
          (by rw [← pow_succ']; exact hupow)
      have huAm : (u : G) ∈ Am := ⟨hUA huU, by rw [h1, hu2]⟩
      have hle : U ≤ Am := by rw [hU_eq]; exact Subgroup.zpowers_le.mpr huAm
      rw [← hAm_eq]; exact hle

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
