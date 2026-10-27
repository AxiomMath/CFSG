module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import Mathlib.GroupTheory.Nilpotent
import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.RankThree.PartOne.TAIL

open Subgroup

theorem exists_normalizer_of_not_sylow {H : Type*} [Group H] [Finite H] {P : Subgroup H}
    (hP : IsPGroup 7 P) (h7 : 7 ∣ P.index) :
    ∃ x : H, x ∈ Subgroup.normalizer (P : Set H) ∧ x ∉ P ∧ ∃ k : ℕ, orderOf x = 7 ^ k := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨S, hPS⟩ := hP.exists_le_sylow
  have hSP : ¬ (S : Subgroup H) ≤ P := by
    intro hSP
    have hPS' : P = S := le_antisymm hPS hSP
    rw [hPS'] at h7
    exact S.not_dvd_index h7
  have hlt : P.subgroupOf (S : Subgroup H) < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => hSP ?_
    intro x hx
    have : (⟨x, hx⟩ : ↥(S : Subgroup H)) ∈ P.subgroupOf (S : Subgroup H) := by
      rw [htop]
      exact Subgroup.mem_top _
    exact this
  have : Group.IsNilpotent ↥(S : Subgroup H) := IsPGroup.isNilpotent S.isPGroup'
  obtain ⟨s, hsn, hsH⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  refine ⟨(s : H), ?_, fun hs => hsH hs, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro y
    have hsS : (s : H) ∈ (S : Subgroup H) := s.2
    constructor
    · intro hy
      have hyS : y ∈ (S : Subgroup H) := hPS hy
      have h1 : (⟨y, hyS⟩ : ↥(S : Subgroup H)) ∈ P.subgroupOf (S : Subgroup H) := hy
      exact (Subgroup.mem_normalizer_iff.mp hsn _).mp h1
    · intro hy
      have hyS : y ∈ (S : Subgroup H) := by
        have h2 : (s : H)⁻¹ * ((s : H) * y * (s : H)⁻¹) * (s : H) ∈ (S : Subgroup H) :=
          (S : Subgroup H).mul_mem ((S : Subgroup H).mul_mem ((S : Subgroup H).inv_mem hsS)
            (hPS hy)) hsS
        have h3 : (s : H)⁻¹ * ((s : H) * y * (s : H)⁻¹) * (s : H) = y := by group
        rwa [h3] at h2
      have h1 : s * (⟨y, hyS⟩ : ↥(S : Subgroup H)) * s⁻¹ ∈ P.subgroupOf (S : Subgroup H) := hy
      exact (Subgroup.mem_normalizer_iff.mp hsn _).mpr h1
  · obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp S.isPGroup') s
    refine ⟨k, ?_⟩
    rw [← Subgroup.orderOf_coe] at hk
    exact hk

theorem exists_ne_one_mem_inf_of_card {G : Type*} [Group G] [Finite G] {A B B' : Subgroup G}
    (hA : Nat.card A = 343) (hB : Nat.card B = 49) (hB' : Nat.card B' = 49) (hBA : B ≤ A)
    (hB'A : B' ≤ A) : ∃ b ∈ B ⊓ B', b ≠ 1 := by
  have h1 : B.relIndex A * Nat.card ↥(B ⊓ A) = Nat.card A := Subgroup.relIndex_mul_card B A
  have h2 : B'.relIndex A * Nat.card ↥(B' ⊓ A) = Nat.card A :=
    Subgroup.relIndex_mul_card B' A
  rw [inf_of_le_left hBA, hB, hA] at h1
  rw [inf_of_le_left hB'A, hB', hA] at h2
  have h3 : B.relIndex A = 7 := by omega
  have h4 : B'.relIndex A = 7 := by omega
  have h5 : (B ⊓ B').relIndex A ≤ 49 := by
    have := Subgroup.relIndex_inf_le (H := B) (K := B') (L := A)
    rw [h3, h4] at this
    omega
  have h6 : (B ⊓ B').relIndex A * Nat.card ↥(B ⊓ B' ⊓ A) = Nat.card A :=
    Subgroup.relIndex_mul_card (B ⊓ B') A
  rw [inf_of_le_left (inf_le_left.trans hBA), hA] at h6
  have h7 : 1 < Nat.card ↥(B ⊓ B') := by
    by_contra hle
    push Not at hle
    have : (B ⊓ B').relIndex A * Nat.card ↥(B ⊓ B') ≤ 49 * 1 :=
      Nat.mul_le_mul h5 hle
    omega
  obtain ⟨b, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 ((Subgroup.one_lt_card_iff_ne_bot _).1 h7)
  exact ⟨b, b.2, fun h => hb1 (Subtype.ext h)⟩

theorem mem_of_normalizer_of_isSylowOf {G : Type*} [Group G] [Finite G] {P K : Subgroup G}
    (hS : CFSG.ABGLocalTools.IsSylowOf 7 P K) {l : G} (hlK : l ∈ K)
    (hlN : l ∈ Subgroup.normalizer (P : Set G)) {k : ℕ} (hk : orderOf l = 7 ^ k) : l ∈ P := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hpg : IsPGroup 7 P := hS.isPGroup
  have hxN : Subgroup.zpowers l ≤ Subgroup.normalizer (P : Set G) :=
    Subgroup.zpowers_le.mpr hlN
  have hsord : IsPGroup 7 ↥(Subgroup.zpowers l) :=
    IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  have hRpg : IsPGroup 7 ↥(P ⊔ Subgroup.zpowers l) := hpg.to_sup_of_normal_left' hsord hxN
  have hPK : P ≤ K := hS.le
  have hReq := hS.eq_of_le le_sup_left (sup_le hPK (Subgroup.zpowers_le.mpr hlK)) hRpg
  have : l ∈ P ⊔ Subgroup.zpowers l :=
    (le_sup_right : Subgroup.zpowers l ≤ P ⊔ Subgroup.zpowers l) (Subgroup.mem_zpowers _)
  rwa [hReq] at this

theorem relIndex_centralizer_dvd_six {G : Type*} [Group G] [Finite G] {c : G} (hc : orderOf c = 7)
    {N : Subgroup G} (hN : N ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G)) :
    (Subgroup.centralizer ({c} : Set G) ⊓ N).relIndex N ∣ 6 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let φ : ↥N →* MulAut ↥(Subgroup.zpowers c) :=
    (Subgroup.zpowers c).normalizerMonoidHom.comp (Subgroup.inclusion hN)
  have hker : φ.ker = (Subgroup.centralizer ({c} : Set G) ⊓ N).subgroupOf N := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro h
      refine ⟨?_, g.2⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := congrArg (fun a : MulAut ↥(Subgroup.zpowers c) =>
        ((a ⟨c, Subgroup.mem_zpowers c⟩ : ↥(Subgroup.zpowers c)) : G)) h
      simp only [φ, MonoidHom.comp_apply, Subgroup.normalizerMonoidHom_apply_apply_coe,
        MulAut.one_apply] at h1
      have h2 : (g : G) * c * (g : G)⁻¹ = c := h1
      calc (g : G) * c = ((g : G) * c * (g : G)⁻¹) * g := by group
        _ = c * g := by rw [h2]
    · rintro ⟨hgc, -⟩
      have hgc' : (g : G) * c * (g : G)⁻¹ = c := by
        have := Subgroup.mem_centralizer_singleton_iff.mp hgc
        calc (g : G) * c * (g : G)⁻¹ = (c * g) * (g : G)⁻¹ := by rw [this]
          _ = c := by group
      ext ⟨y, hy⟩
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      simp only [φ, MonoidHom.comp_apply, Subgroup.normalizerMonoidHom_apply_apply_coe,
        MulAut.one_apply]
      show (g : G) * c ^ j * (g : G)⁻¹ = c ^ j
      rw [← conj_zpow, hgc']
  have hidx : (Subgroup.centralizer ({c} : Set G) ⊓ N).relIndex N = Nat.card φ.range := by
    rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
  rw [hidx]
  have hcyc : IsCyclic ↥(Subgroup.zpowers c) := inferInstance
  have hcard : Nat.card (MulAut ↥(Subgroup.zpowers c)) = 6 := by
    rw [IsCyclic.card_mulAut, Nat.card_zpowers, hc]
    exact Nat.totient_prime (by norm_num)
  rw [← hcard]
  exact Subgroup.card_subgroup_dvd_card _

end CFSG.RankThree.PartOne.TAIL
