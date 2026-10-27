module

public import CFSG.Quasithin.EmptyFaithful.S146zJFin
public import CFSG.Quasithin.EmptyFaithful.S146zLMod
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Quasithin.EmptyFaithful.S146zLSgn

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.C1Pack
  CFSG.Quasithin.CosetGeom
open scoped commutatorElement Pointwise

section Types

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem IsDecP.types_of_fix (S : Setting146 G T M) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ p) (h : IsDecP T M H p H₀ H₁ H₂ t) (φ₁ : ↥H₁ →* DihedralGroup p)
    (hker₁ : ∀ y : ↥H₁, φ₁ y = 1 ↔ (y : G) ∈ pCoreOf 2 H) {a₁ : ↥H₁}
    (ha₁ : φ₁ a₁ = DihedralGroup.r 1) (φ₂ : ↥H₂ →* DihedralGroup p)
    (hker₂ : ∀ y : ↥H₂, φ₂ y = 1 ↔ (y : G) ∈ pCoreOf 2 H) {a₂ : ↥H₂}
    (ha₂ : φ₂ a₂ = DihedralGroup.r 1) (hne : uHi T M H H₁ ≠ uHi T M H H₂) {x : G} (hxH : x ∈ H)
    (hx2 : x * x = 1) (hf₁ : conjSub x (uHi T M H H₁) = uHi T M H H₁)
    (hf₂ : conjSub x (uHi T M H H₂) = uHi T M H H₂) :
    (x * (a₁ : G) * x⁻¹ * (a₁ : G)⁻¹ ∈ pCoreOf 2 H ∨ x * (a₁ : G) * x⁻¹ * (a₁ : G) ∈ pCoreOf 2 H) ∧
      (x * (a₂ : G) * x⁻¹ * (a₂ : G)⁻¹ ∈ pCoreOf 2 H ∨
        x * (a₂ : G) * x⁻¹ * (a₂ : G) ∈ pCoreOf 2 H) := by
  have hp : p.Prime := hred.prime
  have hp2 : p ≠ 2 := hred.odd
  have hxQ : x * x ∈ pCoreOf 2 H := by
    rw [hx2]
    exact (pCoreOf 2 H).one_mem
  have hxN₁ : x ∈ Subgroup.normalizer (H₁ : Set G) := by
    rcases h.normalizer_or_swap S hred hxH with ⟨h1, -, -⟩ | ⟨h1, -⟩
    · exact h1
    · exact absurd (hf₁.symm.trans h1) hne
  have hxN₂ : x ∈ Subgroup.normalizer (H₂ : Set G) := by
    rcases h.swap.normalizer_or_swap S hred hxH with ⟨h1, -, -⟩ | ⟨h1, -⟩
    · exact h1
    · exact absurd (hf₂.symm.trans h1).symm hne
  exact ⟨h.conj_rotation_aux hp hp2 φ₁ hker₁ ha₁ hxH hxN₁ hxQ,
    h.swap.conj_rotation_aux hp hp2 φ₂ hker₂ ha₂ hxH hxN₂ hxQ⟩

omit [Finite G] in
theorem zlElemAbelian_mono {B B₀ : Subgroup G} (hB : IsElemAbelian 2 B) (hle : B₀ ≤ B) :
    IsElemAbelian 2 B₀ := CFSG.Open.IsElemAbelian.mono hB hle

end Types


theorem input14613B2In_proved : Input14613B2In := by
  intro G _ _ T M S H PQ p hred H₀ H₁ H₂ t h h8 δ δ' k sk hpos hle
  classical
  by_contra hno
  push Not at hno
  obtain ⟨hno₁, hno₂⟩ := hno
  have hH : IsHTM T M H := hred.isHTM
  have hp : p.Prime := hred.prime
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨h81, h98⟩ := S.lemma_14_5_14 (S.isHz_iff.mpr hH)
  have h91 := h98.toHypF91
  have hBab : IsElemAbelian 2 (F8.Uγ (VZ T M) H (k : G)) := h98.isElemAbelian_Uγ
  have hBH : F8.Uγ (VZ T M) H (k : G) ≤ H := h98.Uγ_le_H sk
  have hDeq := h98.Dγ_eq_inf_pCoreOf sk
  rw [hDeq] at hle
  set B := F8.Uγ (VZ T M) H (k : G) with hB
  have hUp : IsPGroup 2 B := isPGroup_of_isElemAbelian hBab
  set s := mIdx (conjClosure (VZ T M) H)
    (F8.DH (VZ T M) (quasithinOmegaOneCenter T) H (k : G)) with hs
  have hrel : (B ⊓ pCoreOf 2 H).relIndex B = 2 ^ mIdx B (B ⊓ pCoreOf 2 H) :=
    HypF98.relIndex_eq_two_pow_mIdx hUp
  have hcard₁ : Nat.card (Wsub h91 (uHi T M H H₁)) = 16 := h.card_Wsub_of_mIdx_eight S hred h91 h8
  have hcard₂ : Nat.card (Wsub h91 (uHi T M H H₂)) = 16 :=
    h.swap.card_Wsub_of_mIdx_eight S hred h91 h8
  obtain ⟨hinfW, h256⟩ := h.card_W_sup h91 hcard₁ hcard₂
  have hne : uHi T M H H₁ ≠ uHi T M H H₂ := by
    intro heq
    rw [heq, inf_idem] at hinfW
    rw [hinfW, Subgroup.card_bot] at hcard₂
    omega
  obtain ⟨φ₁, hφ₁s, hker₁⟩ := h.exists_phi_gen
  obtain ⟨a₁, ha₁⟩ := hφ₁s (DihedralGroup.r 1)
  obtain ⟨φ₂, hφ₂s, hker₂⟩ := h.swap.exists_phi_gen
  obtain ⟨a₂, ha₂⟩ := hφ₂s (DihedralGroup.r 1)
  have hx2 : ∀ x ∈ B, x * x = 1 := fun x hx => by
    have := isElemAbelian_pow_eq_one hBab hx
    simpa [pow_two] using this
  have hfix₂ : ∀ x ∈ B, conjSub x (uHi T M H H₁) = uHi T M H H₁ →
      conjSub x (uHi T M H H₂) = uHi T M H H₂ := fun x hx hf₁ => by
    rcases h.normalizer_or_swap S hred (hBH hx) with ⟨-, -, h2⟩ | ⟨h1, -⟩
    · exact h2
    · exact absurd (hf₁.symm.trans h1) hne
  obtain ⟨w, hwB, hw₁, hw₂⟩ : ∃ w ∈ B, w ∉ H₁ ∧ w ∉ H₂ := by
    obtain ⟨x, hxB, hxH₁⟩ := IsConcreteLE.not_le_iff_exists.mp hno₁
    obtain ⟨y, hyB, hyH₂⟩ := IsConcreteLE.not_le_iff_exists.mp hno₂
    by_cases hx2' : x ∈ H₂
    · by_cases hy1 : y ∈ H₁
      · refine ⟨x * y, B.mul_mem hxB hyB, fun hxy => hxH₁ ?_, fun hxy => hyH₂ ?_⟩
        · have := H₁.mul_mem hxy (H₁.inv_mem hy1)
          simpa using this
        · have := H₂.mul_mem (H₂.inv_mem hx2') hxy
          simpa using this
      · exact ⟨y, hyB, hy1, hyH₂⟩
    · exact ⟨x, hxB, hxH₁, hx2'⟩
  have hs3 : 3 ≤ s := by
    have hwH : w ∈ H := hBH hwB
    rcases h.normalizer_or_swap S hred hwH with ⟨-, hf₁, hf₂⟩ | ⟨hs₁, hs₂⟩
    · obtain ⟨t₁, t₂⟩ := h.types_of_fix S hred φ₁ hker₁ ha₁ φ₂ hker₂ ha₂ hne hwH (hx2 w hwB) hf₁ hf₂
      rcases t₁ with c₁ | i₁ <;> rcases t₂ with c₂ | i₂
      · exact absurd (h.Q₁ (h.mem_pCore_of_centralizes S hred φ₁ hker₁ ha₁ φ₂ hker₂ ha₂ hwH
          (hx2 w hwB) c₁ c₂)) hw₁
      · exact absurd (h.swap.mem_H₁_of_inv_cent S hred φ₂ hker₂ hφ₂s ha₂ φ₁ hker₁ ha₁ hwH
          (hx2 w hwB) i₂ c₁) hw₂
      · exact absurd (h.mem_H₁_of_inv_cent S hred φ₁ hker₁ hφ₁s ha₁ φ₂ hker₂ ha₂ hwH
          (hx2 w hwB) i₁ c₂) hw₁
      · exact h.three_le_of_inv S hred sk h91 hcard₁ hcard₂ φ₁ hker₁ ha₁ φ₂ hker₂ ha₂ hwB hwH
          i₁ i₂ hf₁ hf₂
    · exact h.three_le_of_swap S hred sk h91 hcard₁ hcard₂ hwB hwH hs₁ hs₂
  have hr3 : 3 ≤ mIdx B (B ⊓ pCoreOf 2 H) := hs3.trans hle
  have hpow : ∀ n : ℕ, (B ⊓ pCoreOf 2 H).relIndex B ≤ 2 ^ n → mIdx B (B ⊓ pCoreOf 2 H) ≤ n := by
    intro n hn
    rw [hrel] at hn
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hn
  by_cases hall : ∀ x ∈ B, conjSub x (uHi T M H H₁) = uHi T M H H₁
  ·
    have htypes := fun x (hx : x ∈ B) => h.types_of_fix S hred φ₁ hker₁ ha₁ φ₂ hker₂ ha₂ hne
      (hBH hx) (hx2 x hx) (hall x hx) (hfix₂ x hx (hall x hx))
    have h4 := h.relIndex_le_four S hred φ₁ hker₁ ha₁ φ₂ hker₂ ha₂ hBH hBab
      (fun x hx => (htypes x hx).1) (fun x hx => (htypes x hx).2)
    have := hpow 2 (by simpa using h4 : _ ≤ 2 ^ 2)
    omega
  · push Not at hall
    obtain ⟨σ, hσB, hσ⟩ := hall
    have hσH : σ ∈ H := hBH hσB
    obtain ⟨hσ₁, hσ₂⟩ : conjSub σ (uHi T M H H₁) = uHi T M H H₂ ∧
        conjSub σ (uHi T M H H₂) = uHi T M H H₁ := by
      rcases h.normalizer_or_swap S hred hσH with ⟨-, h1, -⟩ | ⟨h1, h2⟩
      · exact absurd h1 hσ
      · exact ⟨h1, h2⟩
    let B₀ : Subgroup G := B ⊓ Subgroup.normalizer (uHi T M H H₁ : Set G)
    have hB₀B : B₀ ≤ B := inf_le_left
    have hB₀f₁ : ∀ x ∈ B₀, conjSub x (uHi T M H H₁) = uHi T M H H₁ := fun x hx =>
      conjSub_eq_of_mem_normalizer hx.2
    have hB₀f₂ : ∀ x ∈ B₀, conjSub x (uHi T M H H₂) = uHi T M H H₂ := fun x hx =>
      hfix₂ x hx.1 (hB₀f₁ x hx)
    have hQB₀ : B ⊓ pCoreOf 2 H ≤ B₀ := fun x hx =>
      ⟨hx.1, h.le_normalizer_uHi S hred (h.Q₁ hx.2)⟩
    have hB₀Q : B₀ ⊓ pCoreOf 2 H = B ⊓ pCoreOf 2 H :=
      le_antisymm (fun x hx => ⟨hB₀B hx.1, hx.2⟩) (fun x hx => ⟨hQB₀ hx, hx.2⟩)
    have hmul := Subgroup.relIndex_mul_relIndex (B ⊓ pCoreOf 2 H) B₀ B hQB₀ hB₀B
    have hB₀idx : B₀.relIndex B ≤ 2 := by
      unfold Subgroup.relIndex
      refine index_le_two_of_forall _ (⟨σ, hσB⟩ : ↥B) fun z => ?_
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      by_cases hz : conjSub (z : G) (uHi T M H H₁) = uHi T M H H₁
      · exact Or.inl ⟨z.2, CosetGeom.mem_normalizer_of_conjSub_eq hz⟩
      · right
        have hzswap : conjSub (z : G) (uHi T M H H₁) = uHi T M H H₂ := by
          rcases h.normalizer_or_swap S hred (hBH z.2) with ⟨-, h1, -⟩ | ⟨h1, -⟩
          · exact absurd h1 hz
          · exact h1
        refine ⟨B.mul_mem (B.inv_mem hσB) z.2, CosetGeom.mem_normalizer_of_conjSub_eq ?_⟩
        show conjSub (σ⁻¹ * (z : G)) (uHi T M H H₁) = uHi T M H H₁
        rw [conjSub_mul, hzswap, ← hσ₁, conjSub_conjSub_inv]
    have hB₀types := fun x (hx : x ∈ B₀) => h.types_of_fix S hred φ₁ hker₁ ha₁ φ₂ hker₂ ha₂ hne
      (hBH (hB₀B hx)) (hx2 x (hB₀B hx)) (hB₀f₁ x hx) (hB₀f₂ x hx)
    by_cases hinv : ∃ y ∈ B₀, y * (a₂ : G) * y⁻¹ * (a₂ : G) ∈ pCoreOf 2 H
    ·
      obtain ⟨y, hyB₀, hy₂⟩ := hinv
      have hs4 := h.four_le_of_swap_inv S hred sk h91 hcard₁ hcard₂ φ₂ hker₂ ha₂ hσB hσH hσ₁ hσ₂
        (hB₀B hyB₀) (hBH (hB₀B hyB₀)) hy₂ (hB₀f₁ y hyB₀) (hB₀f₂ y hyB₀)
      have hr4 : 4 ≤ mIdx B (B ⊓ pCoreOf 2 H) := hs4.trans hle
      have h4 := h.relIndex_le_four S hred φ₁ hker₁ ha₁ φ₂ hker₂ ha₂ (hBH.trans' hB₀B) (zlElemAbelian_mono hBab hB₀B)
        (fun x hx => (hB₀types x hx).1) (fun x hx => (hB₀types x hx).2)
      rw [hB₀Q] at h4
      have h8' : (B ⊓ pCoreOf 2 H).relIndex B ≤ 8 := by
        rw [← hmul]
        calc (B ⊓ pCoreOf 2 H).relIndex B₀ * B₀.relIndex B ≤ 4 * 2 := Nat.mul_le_mul h4 hB₀idx
          _ = 8 := by norm_num
      have := hpow 3 (by simpa using h8' : _ ≤ 2 ^ 3)
      omega
    · push Not at hinv
      have hcent₂ : ∀ x ∈ B₀, x * (a₂ : G) * x⁻¹ * (a₂ : G)⁻¹ ∈ pCoreOf 2 H := fun x hx =>
        (hB₀types x hx).2.resolve_right (hinv x hx)
      have h2 := h.relIndex_le_two_of_cent S hred φ₁ hker₁ ha₁ φ₂ hker₂ ha₂ (hBH.trans' hB₀B)
        (zlElemAbelian_mono hBab hB₀B) (fun x hx => (hB₀types x hx).1) hcent₂
      rw [hB₀Q] at h2
      have h4' : (B ⊓ pCoreOf 2 H).relIndex B ≤ 4 := by
        rw [← hmul]
        calc (B ⊓ pCoreOf 2 H).relIndex B₀ * B₀.relIndex B ≤ 2 * 2 := Nat.mul_le_mul h2 hB₀idx
          _ = 4 := by norm_num
      have := hpow 2 (by simpa using h4' : _ ≤ 2 ^ 2)
      omega

theorem input14613B2P_proved : Input14613B2P :=
  input14613B2P_of_in input14613B2In_proved

end CFSG.Quasithin
