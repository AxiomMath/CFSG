module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutionsAction
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup

section Simple

variable {S : Type*} [Group S] [Finite S]

theorem index_ne_three_of_isSimpleGroup [IsSimpleGroup S] (hS : 6 < Nat.card S)
    (B : Subgroup S) : B.index ≠ 3 := by
  intro h3
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal B.normalCore with h0 | h1
  · have hinj : Function.Injective (MulAction.toPermHom S (S ⧸ B)) := by
      rw [← MonoidHom.ker_eq_bot_iff, ← B.normalCore_eq_ker, h0]
    have hle := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_perm, ← index_eq_card, h3] at hle
    norm_num [Nat.factorial] at hle
    omega
  · have hB : B = ⊤ := eq_top_iff.mpr (h1 ▸ B.normalCore_le)
    rw [hB, index_top] at h3
    omega

theorem false_of_card_three_sixty [IsSimpleGroup S] (hS : Nat.card S = 360) {B S₂ : Subgroup S}
    {a : ℕ} (hB : Nat.card B = 2 ^ a * 60) (hS₂ : Nat.card S₂ = 8)
    (hS₂B : S₂ ≤ normalizer (B : Set S)) : False := by
  have hidx : ∀ X : Subgroup S, Nat.card X = 120 → False := fun X hX => by
    apply index_ne_three_of_isSimpleGroup (by rw [hS]; norm_num) X
    have h := X.card_mul_index
    rw [hX, hS] at h
    omega
  have hdvd : 2 ^ a * 60 ∣ 360 := hB ▸ hS ▸ card_subgroup_dvd_card B
  have ha : a ≤ 1 := by
    by_contra ha
    have h4 : 2 ^ 2 * 60 ∣ 2 ^ a * 60 := Nat.mul_dvd_mul_right (pow_dvd_pow 2 (by omega)) 60
    exact absurd (h4.trans hdvd) (by decide)
  interval_cases a
  · have h60 : 60 ∣ Nat.card (normalizer (B : Set S)) := by
      have h := card_dvd_of_le (le_normalizer : B ≤ normalizer (B : Set S))
      rwa [hB, pow_zero, one_mul] at h
    have h8 : 8 ∣ Nat.card (normalizer (B : Set S)) := hS₂ ▸ card_dvd_of_le hS₂B
    have h120 : 120 ∣ Nat.card (normalizer (B : Set S)) := by
      have h := Nat.lcm_dvd h60 h8
      rwa [show Nat.lcm 60 8 = 120 by norm_num] at h
    have h360 : Nat.card (normalizer (B : Set S)) ∣ 360 := hS ▸ card_subgroup_dvd_card _
    obtain ⟨k, hk⟩ := h120
    have hk3 : k ∣ 3 := by
      rw [hk, show (360 : ℕ) = 120 * 3 by norm_num] at h360
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h360
    rcases (Nat.dvd_prime Nat.prime_three).mp hk3 with rfl | rfl
    · exact hidx _ (by rw [hk])
    · have htop : normalizer (B : Set S) = ⊤ := eq_top_of_card_eq _ (by rw [hk, hS])
      have hBn : B.Normal := normalizer_eq_top_iff.mp htop
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal B with h0 | h1
      · rw [h0, card_bot] at hB
        norm_num at hB
      · rw [h1, card_top, hS] at hB
        norm_num at hB
  · exact hidx B (by rw [hB]; norm_num)

end Simple

section Kernel

theorem le_pCore_of_isSolvable_of_normal {K : Type*} [Group K]
    [IsSimpleGroup (K ⧸ CFSG.pCore 2 K)] (hnab : ∃ a b : K ⧸ CFSG.pCore 2 K, a * b ≠ b * a)
    (N : Subgroup K) [hN : N.Normal] [Group.IsSolvable N] : N ≤ CFSG.pCore 2 K := by
  have hmap : (N.map (QuotientGroup.mk' (CFSG.pCore 2 K))).Normal :=
    hN.map _ (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' (CFSG.pCore 2 K))) with
      h0 | h1
  · rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h0
  · exfalso
    have hs : Group.IsSolvable (K ⧸ CFSG.pCore 2 K) := by
      have hsurj : Function.Surjective
          ((QuotientGroup.mk' (CFSG.pCore 2 K)).comp N.subtype) := by
        intro z
        have hz : z ∈ N.map (QuotientGroup.mk' (CFSG.pCore 2 K)) := h1 ▸ mem_top z
        obtain ⟨n, hn, rfl⟩ := hz
        exact ⟨⟨n, hn⟩, rfl⟩
      exact Group.isSolvable_of_surjective hsurj
    obtain ⟨a, b, hab⟩ := hnab
    exact hab ((IsSimpleGroup.comm_iff_isSolvable).mpr hs a b)

theorem card_range_eq_of_ker_le_pCore {K S : Type*} [Group K] [Finite K] [Group S] (φ : K →* S)
    (hker : φ.ker ≤ CFSG.pCore 2 K) :
    Nat.card φ.range = Nat.card ((CFSG.pCore 2 K).map φ) * Nat.card (K ⧸ CFSG.pCore 2 K) := by
  set Q := CFSG.pCore 2 K
  have h1 : Nat.card φ.ker * Nat.card φ.range = Nat.card K := by
    rw [← index_ker, card_mul_index]
  set ψ := φ.comp Q.subtype
  have hψr : ψ.range = Q.map φ := by
    rw [MonoidHom.range_comp, range_subtype]
  have hψk : Nat.card ψ.ker = Nat.card φ.ker := by
    have : ψ.ker = φ.ker.subgroupOf Q := by
      ext x
      simp [ψ, mem_subgroupOf]
    rw [this]
    exact Nat.card_congr (subgroupOfEquivOfLe hker).toEquiv
  have h2 : Nat.card ψ.ker * Nat.card ψ.range = Nat.card Q := by
    rw [← index_ker, card_mul_index]
  have h3 : Nat.card K = Nat.card (K ⧸ Q) * Nat.card Q := card_eq_card_quotient_mul_card_subgroup Q
  rw [hψk, hψr] at h2
  have hpos : 0 < Nat.card φ.ker := Nat.card_pos
  have : Nat.card φ.ker * Nat.card φ.range =
      Nat.card φ.ker * (Nat.card (Q.map φ) * Nat.card (K ⧸ Q)) := by
    rw [h1, h3, ← h2]
    ring
  exact Nat.eq_of_mul_eq_mul_left hpos this

end Kernel

section Unitary

open CFSG.LinearGroups.UnitaryThreeOverNine CFSG.Assembly.LowTwoRank

theorem card_centralizer_conj {X : Type*} [Group X] (c t : X) :
    Nat.card (centralizer ({c * t * c⁻¹} : Set X)) = Nat.card (centralizer ({t} : Set X)) := by
  have h : centralizer ({c * t * c⁻¹} : Set X) =
      (centralizer ({t} : Set X)).map (MulAut.conj c).toMonoidHom := by
    ext x
    rw [mem_map_equiv, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff,
      MulAut.conj_symm_apply]
    constructor
    · intro hx
      calc c⁻¹ * x * c * t = c⁻¹ * (x * (c * t * c⁻¹)) * c := by group
        _ = c⁻¹ * (c * t * c⁻¹ * x) * c := by rw [hx]
        _ = t * (c⁻¹ * x * c) := by group
    · intro hx
      calc x * (c * t * c⁻¹) = c * (c⁻¹ * x * c * t) * c⁻¹ := by group
        _ = c * (t * (c⁻¹ * x * c)) * c⁻¹ := by rw [hx]
        _ = c * t * c⁻¹ * x := by group
  rw [h, card_map_of_injective (MulAut.conj c).injective]

theorem card_centralizer_of_orderOf_eq_two {F : Type} [Field F] (hF : Nat.card F = 9)
    {t : StatedSU 3 3 F} (ht : orderOf t = 2) :
    Nat.card (centralizer ({t} : Set (StatedSU 3 3 F))) = 96 := by
  have hU := unitaryFieldData_of_card hF
  let L₀ : NonisoLine F := ⟨F ∙ ![1, 0, 0], finrank_span_singleton e0_ne_zero,
    ⟨![1, 0, 0], Submodule.mem_span_singleton_self _, by simp [Fin.sum_univ_three]⟩⟩
  have h96 := card_centralizer_tauLine (h := hU) (hF := hF) (L₀ := L₀) rfl
  obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_of_orderOf_eq_two hF ht (tauLine hU hF L₀).2)
  rw [← hc, card_centralizer_conj] at h96
  exact h96

end Unitary

end CFSG.Quasithin.H13.NQBlock
