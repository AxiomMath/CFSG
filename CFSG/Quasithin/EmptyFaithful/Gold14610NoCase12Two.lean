module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.Quasithin.Background.F6Basic
public import CFSG.Quasithin.Background.F7Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

namespace Gold14610

namespace NC12

variable {D : Type} [Group D] [Finite D]

omit [Finite D] in
theorem twoResidual_le_of_pow_mem {N X : Subgroup D} [N.Normal]
    (h : ∀ x ∈ X, ∃ k : ℕ, x ^ 2 ^ k ∈ N) : twoResidual X ≤ N := by
  refine (twoResidual_le_of_isTwoQuotient (N := N ⊓ X) (H := X) inf_le_right ?_ ?_).trans
    inf_le_left
  · rw [← Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right,
      Subgroup.inf_subgroupOf_right]
    infer_instance
  · intro y hy
    obtain ⟨k, hk⟩ := h y hy
    exact ⟨k, hk, X.pow_mem hy _⟩

theorem isSylowTwoOf_top {D₁ D₂ : Subgroup D} (hT : IsGoldschmidtTriple D₁ D₂) :
    IsSylowTwoOf (D₁ ⊓ D₂) (⊤ : Subgroup D) := by
  obtain ⟨T, hTe⟩ := hT.sylow
  exact hTe ▸ isSylowTwoOf_top_of_sylow T

theorem card_twoResidual_eq_three {D₁ D₂ N : Subgroup D} (hT : IsGoldschmidtTriple D₁ D₂)
    (hN3 : IsPGroup 3 ↥N) (hA : twoResidual D₂ ≤ N) : Nat.card ↥(twoResidual D₂) = 3 := by
  have hS : IsSylowTwoOf (D₁ ⊓ D₂) D₂ := F7.isSylowTwoOf_mono_right (isSylowTwoOf_top hT)
    inf_le_right le_top
  have hD₂ : (D₁ ⊓ D₂) ⊔ twoResidual D₂ = D₂ := sup_twoResidual_eq hS
  have hTn : D₁ ⊓ D₂ ≤ Subgroup.normalizer (twoResidual D₂ : Set D) :=
    inf_le_right.trans (le_normalizer_twoResidual D₂)
  have hTA : twoResidual D₂ ⊓ (D₁ ⊓ D₂) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    obtain ⟨b, hb⟩ := hS.2.1 ⟨x, hx.2⟩
    obtain ⟨a, ha⟩ := hN3 ⟨x, hA hx.1⟩
    have h2 : x ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
    have h3 : x ^ 3 ^ a = 1 := by simpa using congrArg Subtype.val ha
    have := pow_gcd_eq_one.mpr ⟨h2, h3⟩
    rwa [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow b a (by norm_num)), pow_one] at this
  have h1 := Subgroup.relIndex_mul_card (H := twoResidual D₂) (K := D₂)
  rw [inf_eq_left.mpr (twoResidual_le D₂)] at h1
  have h2 : (twoResidual D₂).relIndex D₂ = (twoResidual D₂).relIndex (D₁ ⊓ D₂) := by
    calc (twoResidual D₂).relIndex D₂
        = (twoResidual D₂).relIndex ((D₁ ⊓ D₂) ⊔ twoResidual D₂) := by rw [hD₂]
      _ = (twoResidual D₂).relIndex (D₁ ⊓ D₂) := B6.relIndex_sup_eq_of_le_normalizer hTn
  have h3 := Subgroup.relIndex_mul_card (H := twoResidual D₂) (K := D₁ ⊓ D₂)
  rw [hTA, Subgroup.card_bot, mul_one] at h3
  have h4 := F6.card_right hT
  have hpos : 0 < Nat.card ↥(D₁ ⊓ D₂) := Nat.card_pos
  rw [h2, h3] at h1
  have : Nat.card ↥(D₁ ⊓ D₂) * Nat.card ↥(twoResidual D₂) = Nat.card ↥(D₁ ⊓ D₂) * 3 := by
    rw [h1, h4, mul_comm]
  exact Nat.eq_of_mul_eq_mul_left hpos this

theorem exists_normal_of_normal_three {D₁ D₂ N : Subgroup D} [hN : N.Normal]
    (hT : IsGoldschmidtTriple D₁ D₂) (hN3 : IsPGroup 3 ↥N)
    (hN2 : ∀ x : D, ∃ k : ℕ, x ^ 2 ^ k ∈ N) (hC : 3 * Nat.card ↥⁅N, N⁆ < Nat.card ↥N) :
    ∃ P : Subgroup D, P.Normal ∧ twoResidual D₂ ≤ P ∧ ¬ twoResidual D₁ ≤ P := by
  classical
  have hA₁N : twoResidual D₁ ≤ N := twoResidual_le_of_pow_mem fun x _ => hN2 x
  have hA₂N : twoResidual D₂ ≤ N := twoResidual_le_of_pow_mem fun x _ => hN2 x
  have hCn : (⁅N, N⁆ : Subgroup D).Normal := Subgroup.commutator_normal N N
  have hCnorm : ∀ g : D, g ∈ Subgroup.normalizer ((⁅N, N⁆ : Subgroup D) : Set D) := fun g => by
    rw [Subgroup.normalizer_eq_top_iff.mpr hCn]
    exact Subgroup.mem_top g
  have hS : IsSylowTwoOf (D₁ ⊓ D₂) ⊤ := isSylowTwoOf_top hT
  have hD₁ : (D₁ ⊓ D₂) ⊔ twoResidual D₁ = D₁ :=
    sup_twoResidual_eq (F7.isSylowTwoOf_mono_right hS inf_le_left le_top)
  have hD₂ : (D₁ ⊓ D₂) ⊔ twoResidual D₂ = D₂ :=
    sup_twoResidual_eq (F7.isSylowTwoOf_mono_right hS inf_le_right le_top)
  have hA₂c : Nat.card ↥(twoResidual D₂) = 3 := card_twoResidual_eq_three hT hN3 hA₂N
  obtain ⟨P, hP⟩ : ∃ P : Subgroup D, P = twoResidual D₂ ⊔ ⁅N, N⁆ := ⟨_, rfl⟩
  have hA₂P : twoResidual D₂ ≤ P := hP ▸ le_sup_left
  have hCP : (⁅N, N⁆ : Subgroup D) ≤ P := hP ▸ le_sup_right
  have hD₂n : D₂ ≤ Subgroup.normalizer (P : Set D) := by
    refine le_trans (le_of_eq hD₂.symm) (sup_le (fun t ht => ?_) (fun a ha => ?_))
    · rw [hP]
      refine Subgroup.inf_normalizer_le_normalizer_sup (twoResidual D₂) ⁅N, N⁆ ⟨?_, hCnorm t⟩
      exact le_normalizer_twoResidual D₂ (Subgroup.mem_inf.mp ht).2
    · exact Subgroup.le_normalizer (hA₂P ha)
  have hconj : ∀ b ∈ twoResidual D₁, B6.conjSub b P ≤ P := by
    intro b hb
    rw [hP, (B6.conjSub b).map_sup, B6.conjSub_eq_self (hCnorm b)]
    refine sup_le (fun x hx => ?_) le_sup_right
    rw [B6.mem_conjSub] at hx
    have hxy : x = ⁅b, b⁻¹ * x * b⁆ * (b⁻¹ * x * b) := by
      simp only [commutatorElement_def]
      group
    rw [hxy]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.commutator_mem_commutator
      (hA₁N hb) (hA₂N hx))) (Subgroup.mem_sup_left hx)
  have hD₁n : D₁ ≤ Subgroup.normalizer (P : Set D) := by
    refine le_trans (le_of_eq hD₁.symm) (sup_le (fun t ht => ?_) (fun a ha => ?_))
    · exact hD₂n ((inf_le_right : D₁ ⊓ D₂ ≤ D₂) ht)
    · exact B6.mem_normalizer_of_conjSub_le (hconj a ha)
        (hconj a⁻¹ ((twoResidual D₁).inv_mem ha))
  have hnorm : P.Normal := by
    have h : Subgroup.normalizer (P : Set D) = ⊤ := by
      refine top_le_iff.mp ?_
      rw [← hT.gen]
      exact sup_le hD₁n hD₂n
    exact Subgroup.normalizer_eq_top_iff.mp h
  refine ⟨P, hnorm, hA₂P, fun hA₁P => ?_⟩
  have hsup : (D₁ ⊓ D₂) ⊔ P = ⊤ := by
    refine top_le_iff.mp ?_
    rw [← hT.gen]
    refine sup_le ?_ ?_
    · exact le_trans (le_of_eq hD₁.symm) (sup_le le_sup_left (hA₁P.trans le_sup_right))
    · exact le_trans (le_of_eq hD₂.symm) (sup_le le_sup_left (hA₂P.trans le_sup_right))
  have hq := B6.isTwoQuotient_of_sup_eq hS.2.1 (fun g _ => by
    rw [Subgroup.normalizer_eq_top_iff.mpr hnorm]; exact Subgroup.mem_top g) hsup
  have hNP : N ≤ P := by
    intro x hx
    obtain ⟨k, hk⟩ := hq x (Subgroup.mem_top x)
    obtain ⟨m, hm⟩ := hN3 ⟨x, hx⟩
    have hm' : x ^ 3 ^ m = 1 := by simpa using congrArg Subtype.val hm
    rw [← QuotientGroup.eq_one_iff]
    have e1 : (x : D ⧸ P) ^ 2 ^ k = 1 := by
      rw [← QuotientGroup.mk_pow]
      exact (QuotientGroup.eq_one_iff _).mpr hk
    have e2 : (x : D ⧸ P) ^ 3 ^ m = 1 := by
      rw [← QuotientGroup.mk_pow, hm']
      rfl
    have := pow_gcd_eq_one.mpr ⟨e1, e2⟩
    rwa [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow k m (by norm_num)), pow_one] at this
  have hcard : Nat.card ↥N ≤ Nat.card ↥P := Subgroup.card_le_of_le hNP
  have hPcard : Nat.card ↥P ≤ 3 * Nat.card ↥⁅N, N⁆ := by
    have h1 := Subgroup.relIndex_mul_card (H := (⁅N, N⁆ : Subgroup D)) (K := P)
    rw [inf_eq_left.mpr hCP] at h1
    have h2 : (⁅N, N⁆ : Subgroup D).relIndex P =
        (⁅N, N⁆ : Subgroup D).relIndex (twoResidual D₂) := by
      rw [hP]
      exact B6.relIndex_sup_eq_of_le_normalizer (fun a _ => hCnorm a)
    have h3 := Subgroup.relIndex_mul_card (H := (⁅N, N⁆ : Subgroup D)) (K := twoResidual D₂)
    have h4 : (⁅N, N⁆ : Subgroup D).relIndex (twoResidual D₂) ≤ 3 := by
      have : 0 < Nat.card ↥((⁅N, N⁆ : Subgroup D) ⊓ twoResidual D₂) := Nat.card_pos
      calc (⁅N, N⁆ : Subgroup D).relIndex (twoResidual D₂)
          ≤ (⁅N, N⁆ : Subgroup D).relIndex (twoResidual D₂) *
            Nat.card ↥((⁅N, N⁆ : Subgroup D) ⊓ twoResidual D₂) := Nat.le_mul_of_pos_right _ this
        _ = 3 := by rw [h3, hA₂c]
    rw [← h1, h2]
    exact Nat.mul_le_mul_right _ h4
  omega

end NC12

end Gold14610

end CFSG.Quasithin
