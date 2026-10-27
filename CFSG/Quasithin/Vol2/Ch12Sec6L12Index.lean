module

public import CFSG.Quasithin.Vol2.Ch12Sec6T2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits S126
open scoped IsMulCommutative Pointwise commutatorElement

namespace S126T2

private theorem isElemAbelian_V_of_h1222 {G : Type} [Group G] [Finite G] {T L V : Subgroup G}
    [IsMulCommutative ↥V] (h1222 : Stmt12_2_2) (hH : Hyp126 G T L V) : IsElemAbelian 2 V := by
  have hyp := hH.hyp
  rcases h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow with hAlt | h3
  · exact absurd hAlt hyp.notAlt
  obtain ⟨-, -, hall⟩ := h3 L hyp.maximal hyp.faithful hyp.quasisimple
  obtain ⟨⟨hVT, -, hred, -⟩, -, -, -⟩ := hall V hyp.irrPlus
  exact S126L1b.isElemAbelian_of_reduced (hVT.trans le_sup_right) hred

private theorem not_le_of_quasisimple_isSolvable {G : Type} [Group G] {K N : Subgroup G}
    (hq : CFSG.IsQuasisimple ↥K) (hN : Group.IsSolvable ↥N) : ¬ K ≤ N := by
  intro hKN
  haveI : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hq
  haveI : Group.IsPerfect ↥K := hq.1
  have hsolvK : Group.IsSolvable ↥K :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hKN)
      (Subgroup.inclusion_injective hKN)
  exact Group.IsPerfect.not_isSolvable ↥K hsolvK

private theorem comm_eq_bot_of_cComp_quasisimple {G : Type} [Group G] [Finite G] {X K N : Subgroup G}
    (hK : K ∈ cComp X) (hq : CFSG.IsQuasisimple ↥K) (hNX : N ≤ X) (hNs : Group.IsSolvable ↥N)
    (hKN : K ≤ Subgroup.normalizer (N : Set G)) : ⁅K, N⁆ = ⊥ := by
  have hcomm1 : ⁅K, N⁆ ≤ K := (cComp_commutator_perfectCore hK hNX hNs hKN).1
  have hcomm2 : ⁅K, N⁆ ≤ N := by
    refine Subgroup.commutator_le.mpr fun k hk n hn => ?_
    rw [commutatorElement_def]
    exact N.mul_mem ((Subgroup.mem_normalizer_iff.mp (hKN hk) n).mp hn) (N.inv_mem hn)
  have hNK : (N.subgroupOf K).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hKN
  have hDc : N.subgroupOf K ≤ Subgroup.center ↥K := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hNK with h | h
    · exfalso
      refine not_le_of_quasisimple_isSolvable hq hNs fun k hk => ?_
      have hmem : (⟨k, hk⟩ : ↥K) ∈ N.subgroupOf K := by
        rw [h]
        exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp hmem
    · exact h
  have hcenter : ∀ x ∈ N, ∀ hxK : x ∈ K, ∀ k ∈ K, k * x = x * k := by
    intro x hxN hxK k hk
    have hmem : (⟨x, hxK⟩ : ↥K) ∈ N.subgroupOf K := Subgroup.mem_subgroupOf.mpr hxN
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp (hDc hmem) ⟨k, hk⟩)
  have hcen : ⁅⁅K, N⁆, K⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    exact Subgroup.mem_centralizer_iff.mpr fun k hk => hcenter x (hcomm2 hx) (hcomm1 hx) k hk
  exact CFSG.LocalCores.perfect_double_commutator hq.1 hcen

private theorem pCoreOf_Gv_ne_bot_of_ctx {G : Type} [Group G] [Finite G] {T L V : Subgroup G}
    [IsMulCommutative ↥V] (h1222 : Stmt12_2_2) {F : Frame126 T L V} {v : G} {Kv S : Subgroup G}
    (hC : Ctx1262 F v Kv S) : pCoreOf 2 (Gv v) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hv1 : v ≠ 1 := by
    intro h
    have h1 : F.β ⟨v, hC.mem⟩ = 1 := by
      rw [show (⟨v, hC.mem⟩ : ↥V) = 1 from Subtype.ext h, map_one]
    exact S126T2.ne_one_of_nonsing S126T2.nonsing_e01 (hC.coord.symm.trans h1)
  have hv2 : v ^ 2 = 1 := (isElemAbelian_V_of_h1222 h1222 hC.hyp).2 v hC.mem
  have hvG : v ∈ Gv v := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hN : Gv v ≤ Subgroup.normalizer (Subgroup.zpowers v : Set G) := by
    intro y hy
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    exact ((Commute.zpow_left (Subgroup.mem_centralizer_singleton_iff.mp hy).symm k).symm).eq.symm
  have hzp : IsPGroup 2 (Subgroup.zpowers v) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, orderOf_eq_prime hv2 hv1]
    norm_num
  have hle : Subgroup.zpowers v ≤ pCoreOf 2 (Gv v) :=
    le_pCoreOf_of_le_normalizer 2 (Subgroup.zpowers_le.mpr hvG) hN hzp
  intro hbot
  rw [hbot, le_bot_iff, Subgroup.zpowers_eq_bot] at hle
  exact hv1 hle

theorem relIndex_Tv_S_le_two (h1222 : Stmt12_2_2) (hD2 : Lemma12_6_4_5) {G : Type} [Group G]
    [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V] {F : Frame126 T L V} {v : G}
    {Kv S : Subgroup G} (hC : Ctx1262 F v Kv S) (hq : CFSG.IsQuasisimple ↥Kv) :
    (Tv T v).relIndex S ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hidx1, hidx2, -⟩ := hD2 G T L V F v Kv S hC
  have hle4 : (Tv T v).relIndex S ≤ 4 := hidx1.trans hidx2.le
  have hO2 : pCoreOf 2 (Gv v) ≠ ⊥ := pCoreOf_Gv_ne_bot_of_ctx h1222 hC
  have hKG : Kv ≤ Gv v := le_of_mem_cComp hC.cComp
  have hNs : Group.IsSolvable ↥(pCoreOf 2 (Gv v)) := by
    haveI : Group.IsNilpotent ↥(pCoreOf 2 (Gv v)) :=
      (pCoreOf_isPGroup 2 (Gv v)).isNilpotent
    infer_instance
  have hKN : Kv ≤ Subgroup.normalizer (pCoreOf 2 (Gv v) : Set G) :=
    hKG.trans (le_normalizer_pCoreOf 2 (Gv v))
  have hcomm0 : ⁅Kv, pCoreOf 2 (Gv v)⁆ = ⊥ :=
    comm_eq_bot_of_cComp_quasisimple hC.cComp hq (pCoreOf_le 2 (Gv v)) hNs hKN
  have hKC : Kv ≤ Subgroup.centralizer (pCoreOf 2 (Gv v) : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm0
  have hEven : CFSG.Open.quasithinEvenCharacteristic G := hC.hyp.hyp.qtke.2.1
  have hne4 : (Tv T v).relIndex S ≠ 4 := by
    intro h4
    have hTvT : Tv T v ≤ T := inf_le_left
    have hcT := Subgroup.relIndex_mul_card (H := Tv T v) (K := T)
    rw [inf_eq_left.mpr hTvT, hidx2] at hcT
    have hcS := Subgroup.relIndex_mul_card (H := Tv T v) (K := S)
    rw [inf_eq_left.mpr hC.tv_le, h4] at hcS
    have hSc : Nat.card S = Nat.card T := by rw [← hcS, ← hcT]
    have hSidx : S.index = T.index := by
      have h1 := Subgroup.card_mul_index (H := S)
      have h2 := Subgroup.card_mul_index (H := T)
      rw [hSc] at h1
      exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ↥T)) (h1.trans h2.symm)
    have hS2 : ¬ 2 ∣ S.index := by
      rw [hSidx]
      exact hC.hyp.hyp.sylow.2
    let S' : Sylow 2 G := hC.sylow.2.1.toSylow hS2
    have hInH : InH (S' : Subgroup G) (Gv v) := And.intro hC.sylow.1 hO2
    have hCT : CFSG.QuasithinUnique.CharTwo (Gv v) := charTwo_of_inH hEven S' hInH
    refine not_le_of_quasisimple_isSolvable hq hNs ?_
    intro k hk
    have hk' : k ∈ Gv v ⊓ Subgroup.centralizer (pCoreOf 2 (Gv v) : Set G) :=
      ⟨hKG hk, hKC hk⟩
    exact hCT hk'
  have hdvd : (Tv T v).relIndex S ∣ Nat.card S :=
    ⟨Nat.card ↥(Tv T v ⊓ S), (Subgroup.relIndex_mul_card (H := Tv T v) (K := S)).symm⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hC.sylow.2.1
  rw [hn] at hdvd
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  by_contra hgt
  push_neg at hgt
  have hm2 : 2 ≤ m := by
    by_contra h
    push_neg at h
    interval_cases m <;> simp only [pow_zero, pow_one] at hm <;> omega
  have h4dvd : 4 ∣ (Tv T v).relIndex S := by
    have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [hm, h4]
    exact pow_dvd_pow 2 hm2
  obtain ⟨c, hc⟩ := h4dvd
  exact hne4 (by omega)

theorem relIndex_Tv_inf_Kv_le_two (h1222 : Stmt12_2_2) (hD2 : Lemma12_6_4_5) {G : Type} [Group G]
    [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V] {F : Frame126 T L V} {v : G}
    {Kv S : Subgroup G} (hC : Ctx1262 F v Kv S) (hq : CFSG.IsQuasisimple ↥Kv) :
    (Tv T v ⊓ Kv).relIndex (S ⊓ Kv) ≤ 2 := by
  have h2 := relIndex_Tv_S_le_two h1222 hD2 hC hq
  have e : (Tv T v ⊓ Kv).relIndex (S ⊓ Kv) = (Tv T v).relIndex (S ⊓ Kv) := by
    rw [← Subgroup.relIndex_inf_mul_relIndex (Tv T v) Kv (S ⊓ Kv),
      Subgroup.relIndex_eq_one.2 inf_le_right, mul_one, inf_of_le_right inf_le_right]
  rw [e]
  exact (Subgroup.relIndex_le_of_le_right inf_le_left Subgroup.index_ne_zero_of_finite).trans h2

end S126T2

end CFSG.Quasithin.H13
