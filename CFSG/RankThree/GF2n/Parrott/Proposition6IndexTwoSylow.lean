module

public import TauCeti.Algebra.Group.Subgroup.ZPowers
public import CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge.NoIndexTwoMember
public import CFSG.LocalAnalysis.OddStandard.Solomon75LPlusDefs
public import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
public import CFSG.LocalAnalysis.OddStandard.Solomon75Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG.OddStandard.Solomon75

section SylowIndex

variable {G : Type*} [Group G] [Finite G] {z : G}

theorem exists_sylow_eq_of_center_le_zpowers
    (hz : orderOf z = 2) {T : Subgroup G} (hT : IsPGroup 2 T) (hzT : z ∈ T)
    (hTH : T ≤ Subgroup.centralizer ({z} : Set G))
    (hmax : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ Subgroup.centralizer ({z} : Set G) →
      Nat.card P ≤ Nat.card T)
    (hZ : ∀ t ∈ T, (∀ s ∈ T, t * s = s * t) → t ∈ Subgroup.zpowers z) :
    ∃ S : Sylow 2 G, (S : Subgroup G) = T := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hTS⟩ := hT.exists_le_sylow
  refine ⟨S, le_antisymm ?_ hTS⟩
  by_contra hST
  have hT'lt : T.subgroupOf (S : Subgroup G) < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    exact hST (Subgroup.subgroupOf_eq_top.mp htop)
  have : Group.IsNilpotent (S : Subgroup G) := S.isPGroup'.isNilpotent
  have hNlt : T.subgroupOf (S : Subgroup G) <
      Subgroup.normalizer (T.subgroupOf (S : Subgroup G) : Set (S : Subgroup G)) :=
    Group.normalizerCondition_of_isNilpotent _ hT'lt
  obtain ⟨n, hnN, hnT⟩ := SetLike.exists_of_lt hNlt
  have hnNorm : (n : G) ∈ Subgroup.normalizer (T : Set G) := by
    have hn : n ∈ (Subgroup.normalizer (T : Set G)).subgroupOf (S : Subgroup G) := by
      rw [Subgroup.subgroupOf_normalizer_eq hTS]
      exact hnN
    exact Subgroup.mem_subgroupOf.mp hn
  have hnNotT : (n : G) ∉ T := by
    intro hnT'
    exact hnT (Subgroup.mem_subgroupOf.mpr hnT')
  have hznT : (n : G) * z * (n : G)⁻¹ ∈ T :=
    (Subgroup.mem_normalizer_iff.mp hnNorm z).mp hzT
  have hznCentral : ∀ s ∈ T,
      ((n : G) * z * (n : G)⁻¹) * s = s * ((n : G) * z * (n : G)⁻¹) := by
    intro s hs
    have hinvNorm : (n : G)⁻¹ ∈ Subgroup.normalizer (T : Set G) :=
      Subgroup.inv_mem _ hnNorm
    have hs' : (n : G)⁻¹ * s * (n : G) ∈ T := by
      simpa using (Subgroup.mem_normalizer_iff.mp hinvNorm s).mp hs
    have hcomm : ((n : G)⁻¹ * s * (n : G)) * z =
        z * ((n : G)⁻¹ * s * (n : G)) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hTH hs')
    calc ((n : G) * z * (n : G)⁻¹) * s
        = (n : G) * z * ((n : G)⁻¹ * s * (n : G)) * (n : G)⁻¹ := by group
      _ = (n : G) * (((n : G)⁻¹ * s * (n : G)) * z) * (n : G)⁻¹ := by
        rw [hcomm]
        group
      _ = s * ((n : G) * z * (n : G)⁻¹) := by group
  have hznMem : (n : G) * z * (n : G)⁻¹ ∈ Subgroup.zpowers z :=
    hZ _ hznT hznCentral
  have hznOrder : orderOf ((n : G) * z * (n : G)⁻¹) = 2 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hz]
  have hznEq : (n : G) * z * (n : G)⁻¹ = z := by
    rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two hz).mp hznMem with h1 | h1
    · rw [h1, orderOf_one] at hznOrder
      omega
    · exact h1
  have hnC : (n : G) ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (n : G) * z = ((n : G) * z * (n : G)⁻¹) * (n : G) := by group
      _ = z * (n : G) := by rw [hznEq]
  let P : Subgroup G := T ⊔ Subgroup.zpowers (n : G)
  have hTP : T ≤ P := le_sup_left
  have hnP : (n : G) ∈ P := Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hP2 : IsPGroup 2 P := by
    have hPS : P ≤ (S : Subgroup G) :=
      sup_le hTS (Subgroup.zpowers_le.mpr n.2)
    exact S.isPGroup'.to_le hPS
  have hPC : P ≤ Subgroup.centralizer ({z} : Set G) :=
    sup_le hTH (Subgroup.zpowers_le.mpr hnC)
  have hlt : T < P := lt_of_le_of_ne hTP (by
    intro hEq
    exact hnNotT (hEq ▸ hnP))
  have hcardlt : Nat.card T < Nat.card P := Subgroup.card_lt_of_lt hlt
  have hmaxle : Nat.card P ≤ Nat.card T := hmax P hP2 hPC
  omega

end SylowIndex

section IndexTwo

variable {G : Type*} [Group G]

theorem le_of_index_eq_two_of_nonempty_mulEquiv_sl23 {L N : Subgroup G}
    (hL : Nonempty (↥L ≃* SL23)) (hN : N.index = 2) : L ≤ N := by
  classical
  have : N.Normal := Subgroup.normal_of_index_eq_two hN
  obtain ⟨e⟩ := hL
  let P : Subgroup ↥L := N.subgroupOf L
  have hPidx : P.index ∣ 2 := by
    change N.relIndex L ∣ 2
    rw [← hN]
    exact Subgroup.relIndex_dvd_index_of_normal N L
  have hPne : P.index ≠ 2 := by
    intro hP2
    let K : Subgroup SL23 := P.map (e : ↥L →* SL23)
    have hK : K.index = 2 := by
      rw [Subgroup.index_map_equiv (H := P) e, hP2]
    exact CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge.sl2Three_no_index_two K hK
  have hPone : P.index = 1 := by
    have hne0 : P.index ≠ 0 := by
      intro h0
      rw [h0] at hPidx
      norm_num at hPidx
    have hpos : 0 < P.index := Nat.pos_of_ne_zero hne0
    have hle : P.index ≤ 2 := Nat.le_of_dvd (by norm_num) hPidx
    omega
  have hPtop : P = ⊤ := Subgroup.index_eq_one.mp hPone
  exact Subgroup.subgroupOf_eq_top.mp hPtop

end IndexTwo

section NoIndexTwo

variable {G : Type*} [Group G] [Finite G]

theorem index_ne_two_of_sylow_le_sup_zpowers {M : Subgroup G} {z h : G}
    (T : Sylow 2 G) (hT : (T : Subgroup G) ≤ M ⊔ Subgroup.zpowers h)
    (hM : ∀ N : Subgroup G, N.index = 2 → M ≤ N) (hzM : z ∈ M)
    (hconj : ∃ g : G, g * z * g⁻¹ = h) : ∀ N : Subgroup G, N.index ≠ 2 := by
  intro N hN
  have : N.Normal := Subgroup.normal_of_index_eq_two hN
  have hMN : M ≤ N := hM N hN
  have hzN : z ∈ N := hMN hzM
  obtain ⟨g, hg⟩ := hconj
  have hhN : h ∈ N := by
    rw [← hg]
    exact Subgroup.Normal.conj_mem inferInstance z hzN g
  have hsupN : M ⊔ Subgroup.zpowers h ≤ N :=
    sup_le hMN (Subgroup.zpowers_le.mpr hhN)
  have hTN : (T : Subgroup G) ≤ N := hT.trans hsupN
  have hidx : 2 ∣ (T : Subgroup G).index := by
    have h := Subgroup.relIndex_mul_index (H := (T : Subgroup G)) (K := N) hTN
    rw [hN] at h
    exact ⟨(T : Subgroup G).relIndex N, by rw [← h, mul_comm]⟩
  exact T.not_dvd_index hidx

end NoIndexTwo

section QuaternionCore

variable {G : Type} [Group G] [Finite G]

theorem exists_sylow_le_centralizer_of_quaternion_core {z h : G}
    (hz : orderOf z = 2) {M U : Subgroup G}
    (hcard : Nat.card ↥(Subgroup.centralizer ({z} : Set G)) = 576)
    (hMn : ∀ g ∈ Subgroup.centralizer ({z} : Set G), ∀ x ∈ M, g * x * g⁻¹ ∈ M)
    (hU : ∀ x, x ∈ U ↔ x ∈ M ∧ x ^ 4 = 1) (hcardU : Nat.card U = 32) (hzU : z ∈ U)
    (hUH : U ≤ Subgroup.centralizer ({z} : Set G))
    (hhH : h ∈ Subgroup.centralizer ({z} : Set G)) (hhM : h ∉ M) (hh : h * h = 1)
    (hcen : ∀ x ∈ Subgroup.centralizer ({z} : Set G), (∀ u ∈ U, x * u = u * x) →
      x ∈ Subgroup.zpowers z) :
    ∃ T : Sylow 2 G, (T : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hhU : h ∉ U := fun hmem => hhM (((hU h).mp hmem).1)
  have hh1 : h ≠ 1 := fun h1 => hhM (h1 ▸ M.one_mem)
  have horderh : orderOf h = 2 := orderOf_eq_prime (by rwa [pow_two]) hh1
  have hcardZh : Nat.card (Subgroup.zpowers h) = 2 := by
    rw [Nat.card_zpowers, horderh]
  have hconjU : ∀ y ∈ U, h * y * h⁻¹ ∈ U := by
    intro y hy
    rw [hU]
    refine ⟨hMn h hhH y ((hU y).mp hy).1, ?_⟩
    have hy4 : y ^ 4 = 1 := ((hU y).mp hy).2
    calc (h * y * h⁻¹) ^ 4 = h * y ^ 4 * h⁻¹ := by rw [conj_pow]
      _ = h * 1 * h⁻¹ := by rw [hy4]
      _ = 1 := by rw [mul_one, mul_inv_cancel]
  have hnormU : h ∈ Subgroup.normalizer (U : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact hconjU x
    · intro hx
      have hx2 : h * (h * x * h⁻¹) * h⁻¹ ∈ U := hconjU _ hx
      have hxeq : h * (h * x * h⁻¹) * h⁻¹ = x := by
        calc h * (h * x * h⁻¹) * h⁻¹ = (h * h) * x * (h * h)⁻¹ := by group
          _ = x := by rw [hh, one_mul, inv_one, mul_one]
      rwa [hxeq] at hx2
  have hdisj : U ⊓ Subgroup.zpowers h = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two horderh).mp hx.2 with hx1 | hx1
    · exact hx1
    · exact absurd (hx1 ▸ hx.1) hhU
  let T0 : Subgroup G := U ⊔ Subgroup.zpowers h
  have hcardT0 : Nat.card T0 = 64 := by
    have hc := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      (H := Subgroup.zpowers h) (K := U) (Subgroup.zpowers_le.mpr hnormU)
    rw [inf_comm, hdisj, Subgroup.card_bot, hcardZh, hcardU] at hc
    have hsup : T0 = Subgroup.zpowers h ⊔ U := by
      dsimp [T0]
      rw [sup_comm]
    rw [hsup]
    simpa using hc
  have hT0p : IsPGroup 2 T0 :=
    IsPGroup.of_card (n := 6) (by rw [hcardT0]; norm_num)
  have hzT0 : z ∈ T0 := by
    change z ∈ U ⊔ Subgroup.zpowers h
    exact Subgroup.mem_sup_left hzU
  have hT0C : T0 ≤ Subgroup.centralizer ({z} : Set G) := by
    change U ⊔ Subgroup.zpowers h ≤ Subgroup.centralizer ({z} : Set G)
    exact sup_le hUH (Subgroup.zpowers_le.mpr hhH)
  have hmax : ∀ P : Subgroup G, IsPGroup 2 P →
      P ≤ Subgroup.centralizer ({z} : Set G) → Nat.card P ≤ Nat.card T0 := by
    intro P hP hPC
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
    have hdvd : 2 ^ k ∣ Nat.card (Subgroup.centralizer ({z} : Set G)) := by
      rw [← hk]
      exact Subgroup.card_dvd_of_le hPC
    rw [hcard] at hdvd
    have hk6 : k ≤ 6 := by
      by_contra hk7
      have h7 : 2 ^ 7 ∣ 2 ^ k := Nat.pow_dvd_pow 2 (by omega)
      have h128 : (128 : ℕ) ∣ 576 := by simpa using h7.trans hdvd
      have hnot : ¬ (128 : ℕ) ∣ 576 := by norm_num
      exact hnot h128
    rw [hk, hcardT0]
    calc 2 ^ k ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hk6
      _ = 64 := by norm_num
  have hZ : ∀ t ∈ T0, (∀ s ∈ T0, t * s = s * t) → t ∈ Subgroup.zpowers z := by
    intro t ht htc
    refine hcen t ?_ ?_
    · exact hT0C ht
    · intro u hu
      exact htc u (Subgroup.mem_sup_left hu)
  obtain ⟨S, hS⟩ :=
    exists_sylow_eq_of_center_le_zpowers (z := z) hz hT0p hzT0 hT0C hmax hZ
  refine ⟨S, ?_⟩
  rwa [hS]

end QuaternionCore

end CFSG.RankThree.GF2n.Parrott
