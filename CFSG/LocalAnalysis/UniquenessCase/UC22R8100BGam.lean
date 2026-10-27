module

public import CFSG.LocalAnalysis.UniquenessCase.UC22R8100BFrat
public import CFSG.LocalAnalysis.UniquenessCase.UC22R8100BFix
import CFSG.LocalAnalysis.UniquenessCase.UC22P22g
import CFSG.LocalAnalysis.UniquenessCase.UC6S846c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.ABGLocalTools Subgroup

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem uc22r8100b_exists_sylow_mem {q : ℕ} [Fact q.Prime] {K : Subgroup Γ} {t : Γ} (ht : t ∈ K)
    (hto : orderOf t = q) : ∃ S : Subgroup Γ, IsSylowOf q S K ∧ t ∈ S := by
  have hP : IsPGroup q (Subgroup.zpowers (⟨t, ht⟩ : K)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one, ← hto]
    exact (Subgroup.orderOf_coe (⟨t, ht⟩ : K)).symm
  obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow hP
  exact ⟨(Q : Subgroup K).map K.subtype, ⟨Q, rfl⟩, ⟨⟨t, ht⟩, hQ (Subgroup.mem_zpowers _), rfl⟩⟩

theorem uc22r8100b_centralizes {n m p q : ℕ} {K S : Subgroup Γ} (hK : IsL2 K n) (hn : n = p * m)
    (hp : p.Prime) (hp2 : p ≠ 2) (hq : q.Prime) (hqm : q ∣ 2 ^ m - 1) (hS : IsSylowOf q S K)
    {d : Γ} (hdK : d ∈ normalizer (K : Set Γ)) (hdS : d ∈ normalizer (S : Set Γ))
    (hdp : d ^ p = 1) {t : Γ} (htS : t ∈ S) (hto : orderOf t = q) : d * t = t * d := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨Q, rfl⟩ := hS
  have htK : t ∈ K := Subgroup.map_subtype_le _ htS
  have hmem : ∀ y : K, y ∈ (Q : Subgroup K) ↔ (y : Γ) ∈ (Q : Subgroup K).map K.subtype :=
    fun y => (Subgroup.mem_map_iff_mem K.subtype_injective).symm
  have htQ : (⟨t, htK⟩ : K) ∈ (Q : Subgroup K) := (hmem _).2 htS
  set ψ : MulAut K := K.normalizerMonoidHom ⟨d, hdK⟩ with hψ
  have hψapp : ∀ x : K, ((ψ x : K) : Γ) = d * x * d⁻¹ := fun x => rfl
  have hψQ : ∀ x : K, x ∈ (Q : Subgroup K) ↔ ψ x ∈ (Q : Subgroup K) := by
    intro x
    rw [hmem, hmem, hψapp]
    exact Subgroup.mem_normalizer_iff.1 hdS x
  have hψp : ψ ^ p = 1 := by
    rw [hψ, ← map_pow]
    have : (⟨d, hdK⟩ : normalizer (K : Set Γ)) ^ p = 1 := Subtype.ext hdp
    rw [this, map_one]
  have hfix := uc22r8100b_fixes_of_aut hK hn hp hp2 hqm Q ψ hψQ hψp htQ
    ((Subgroup.orderOf_coe (⟨t, htK⟩ : K)).symm.trans hto)
  exact mul_inv_eq_iff_eq_mul.1 (congrArg Subtype.val hfix)

theorem uc22r8100b_card_inf_le {K B : Subgroup Γ} {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : IsL2 K n) (hB : IsElemAbelian p B) : Nat.card (B ⊓ K : Subgroup Γ) ≤ p := by
  have h1 : IsElemAbelian p ((B ⊓ K).subgroupOf K) := (hB.mono inf_le_left).subgroupOf K
  haveI := h1.isElementaryAbelian
  have h2 := uc22p22g_rank hp hp2 hK ((B ⊓ K).subgroupOf K)
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : B ⊓ K ≤ K)).toEquiv] at h2

theorem uc22r8100b_exists_centralizing_D {K₁ K₂ A₀ : Subgroup Γ} {n m p q : ℕ} (hK₁ : IsL2 K₁ n)
    (hK₂ : IsL2 K₂ n) (hn : n = p * m) (hp : p.Prime) (hp2 : p ≠ 2) (hpn : p ∣ 2 ^ n + 1)
    (hq : q.Prime) (hqm : q ∣ 2 ^ m - 1) (hcomm : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a)
    (hA₀ : IsElemAbelian p A₀) (hA₀c : Nat.card A₀ = p ^ 4)
    (hA₀N₁ : A₀ ≤ normalizer (K₁ : Set Γ)) (hA₀N₂ : A₀ ≤ normalizer (K₂ : Set Γ)) {t₁ t₂ : Γ}
    (ht₁ : t₁ ∈ K₁) (ht₂ : t₂ ∈ K₂) (hto₁ : orderOf t₁ = q) (hto₂ : orderOf t₂ = q) :
    ∃ D : Subgroup Γ, IsElemAbelian p D ∧ Nat.card D = p ^ 2 ∧
      ∀ d ∈ D, d * t₁ = t₁ * d ∧ d * t₂ = t₂ * d := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨hq⟩
  have hqn : q ∣ 2 ^ n - 1 :=
    hqm.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 ⟨p, by rw [hn, mul_comm]⟩)
  obtain ⟨S₁, hS₁, ht₁S⟩ := uc22r8100b_exists_sylow_mem ht₁ hto₁
  obtain ⟨S₂, hS₂, ht₂S⟩ := uc22r8100b_exists_sylow_mem ht₂ hto₂
  have hKS₁ := uc22r8100b_not_dvd_normalizer_of_le hK₁ hp hp2 hpn hq hqn hS₁
  have hKS₂ := uc22r8100b_not_dvd_normalizer_of_le hK₂ hp hp2 hpn hq hqn hS₂
  have h12 : K₁ ≤ normalizer (K₂ : Set Γ) := fun a ha => Subgroup.centralizer_le_normalizer _
    (Subgroup.mem_centralizer_iff.2 fun b hb => (hcomm a ha b hb).symm)
  have h21 : K₂ ≤ normalizer (K₁ : Set Γ) := fun b hb => Subgroup.centralizer_le_normalizer _
    (Subgroup.mem_centralizer_iff.2 fun a ha => hcomm a ha b hb)
  have h2S₁ : K₂ ≤ normalizer (S₁ : Set Γ) := fun b hb => Subgroup.centralizer_le_normalizer _
    (Subgroup.mem_centralizer_iff.2 fun s hs => hcomm s (hS₁.le hs) b hb)
  obtain ⟨D₁, hD₁H, hD₁el, hD₁c⟩ := uc22r8100b_exists_elemAbelian_le_normalizer hp hq
    (K := K₁) (H := normalizer (K₁ : Set Γ) ⊓ normalizer (K₂ : Set Γ)) (S := S₁) (A := A₀)
    (le_inf Subgroup.le_normalizer h12) inf_le_left hS₁ hKS₁ hA₀ (le_inf hA₀N₁ hA₀N₂)
  have hD₁3 : p ^ 3 ≤ Nat.card D₁ := by
    have h : p * p ^ 3 ≤ p * Nat.card D₁ :=
      calc p * p ^ 3 = p ^ 4 := by ring
        _ = Nat.card (A₀ ⊓ K₁ : Subgroup Γ) * Nat.card D₁ := by rw [← hA₀c]; exact hD₁c
        _ ≤ p * Nat.card D₁ :=
          Nat.mul_le_mul_right _ (uc22r8100b_card_inf_le hp hp2 hK₁ hA₀)
    exact Nat.le_of_mul_le_mul_left h hp.pos
  obtain ⟨D₂, hD₂H, hD₂el, hD₂c⟩ := uc22r8100b_exists_elemAbelian_le_normalizer hp hq
    (K := K₂) (H := (normalizer (K₁ : Set Γ) ⊓ normalizer (K₂ : Set Γ)) ⊓ normalizer (S₁ : Set Γ))
    (S := S₂) (A := D₁) (le_inf (le_inf h21 Subgroup.le_normalizer) h2S₁)
    (inf_le_left.trans inf_le_right) hS₂ hKS₂ hD₁el hD₁H
  have hD₂2 : p ^ 2 ≤ Nat.card D₂ := by
    have h : p * p ^ 2 ≤ p * Nat.card D₂ :=
      calc p * p ^ 2 = p ^ 3 := by ring
        _ ≤ Nat.card D₁ := hD₁3
        _ = Nat.card (D₁ ⊓ K₂ : Subgroup Γ) * Nat.card D₂ := hD₂c
        _ ≤ p * Nat.card D₂ :=
          Nat.mul_le_mul_right _ (uc22r8100b_card_inf_le hp hp2 hK₂ hD₁el)
    exact Nat.le_of_mul_le_mul_left h hp.pos
  obtain ⟨D, hDD, hDel, hDc⟩ := UC6S846.exists_card_p_sq hp hD₂el hD₂2
  refine ⟨D, hDel, hDc, fun d hd => ?_⟩
  obtain ⟨⟨⟨hdK₁, hdK₂⟩, hdS₁⟩, hdS₂⟩ := hD₂H (hDD hd)
  have hdp : d ^ p = 1 := hDel.2 d hd
  exact ⟨uc22r8100b_centralizes hK₁ hn hp hp2 hq hqm hS₁ hdK₁ hdS₁ hdp ht₁S hto₁,
    uc22r8100b_centralizes hK₂ hn hp hp2 hq hqm hS₂ hdK₂ hdS₂ hdp ht₂S hto₂⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
