module

public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
import CFSG.LocalAnalysis.StronglyEmbedded.Normalizer
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.R8107E3

open CFSG.Open Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G]

theorem mem_of_commute_conj_of_sp {M : Subgroup G} {p : ℕ} (hsp : IsStronglyPEmbedded p M)
    {b : G} (hNb : normalizer ((zpowers b : Subgroup G) : Set G) ≤ M) {y : G} (hyM : y ∈ M)
    (hy : orderOf y = p) {w : G} (hw : y * (w * b * w⁻¹) = w * b * w⁻¹ * y) : w ∈ M := by
  by_contra hwM
  refine hsp.2.2 w hwM ?_
  have hb : (w⁻¹ * y * w) * b = b * (w⁻¹ * y * w) :=
    calc (w⁻¹ * y * w) * b = w⁻¹ * (y * (w * b * w⁻¹)) * w := by group
      _ = w⁻¹ * (w * b * w⁻¹ * y) * w := by rw [hw]
      _ = b * (w⁻¹ * y * w) := by group
  have hc : w⁻¹ * y * w ∈ centralizer ((zpowers b : Subgroup G) : Set G) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨k, rfl⟩
    exact ((Commute.zpow_right (show Commute (w⁻¹ * y * w) b from hb) k).eq).symm
  have hmem : y ∈ M ⊓ M.map (MulAut.conj w).toMonoidHom :=
    ⟨hyM, ⟨w⁻¹ * y * w, hNb (centralizer_le_normalizer _ hc), by
      change w * (w⁻¹ * y * w) * w⁻¹ = y
      group⟩⟩
  have h := orderOf_dvd_natCard (⟨y, hmem⟩ : ↥(M ⊓ M.map (MulAut.conj w).toMonoidHom))
  rwa [Subgroup.orderOf_mk, hy] at h

private theorem mul_axes {a₀ a₁ a₂ : G} (h₀₁ : a₀ * a₁ = a₁ * a₀) (h₀₂ : a₀ * a₂ = a₂ * a₀)
    (h₁₂ : a₁ * a₂ = a₂ * a₁) (i j k i' j' k' : ℕ) :
    a₀ ^ i * a₁ ^ j * a₂ ^ k * (a₀ ^ i' * a₁ ^ j' * a₂ ^ k') =
      a₀ ^ (i + i') * a₁ ^ (j + j') * a₂ ^ (k + k') := by
  have c₀₁ : Commute a₀ a₁ := h₀₁
  have c₀₂ : Commute a₀ a₂ := h₀₂
  have c₁₂ : Commute a₁ a₂ := h₁₂
  rw [((c₀₂.pow_pow i' k).symm.mul_right (c₁₂.pow_pow j' k).symm).mul_mul_mul_comm,
    (c₀₁.pow_pow i' j).symm.mul_mul_mul_comm, pow_add, pow_add, pow_add]

private theorem pow_axes {a₀ a₁ a₂ : G} (h₀₁ : a₀ * a₁ = a₁ * a₀) (h₀₂ : a₀ * a₂ = a₂ * a₀)
    (h₁₂ : a₁ * a₂ = a₂ * a₁) (i j k n : ℕ) :
    (a₀ ^ i * a₁ ^ j * a₂ ^ k) ^ n = a₀ ^ (i * n) * a₁ ^ (j * n) * a₂ ^ (k * n) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, mul_axes h₀₁ h₀₂ h₁₂, Nat.mul_succ, Nat.mul_succ, Nat.mul_succ]

private theorem commute_axes {a₀ a₁ a₂ z : G} {i j k : ℕ} (h₀ : i = 0 ∨ z * a₀ = a₀ * z)
    (h₁ : j = 0 ∨ z * a₁ = a₁ * z) (h₂ : k = 0 ∨ z * a₂ = a₂ * z) :
    z * (a₀ ^ i * a₁ ^ j * a₂ ^ k) = a₀ ^ i * a₁ ^ j * a₂ ^ k * z := by
  have c : ∀ {a : G} {n : ℕ}, (n = 0 ∨ z * a = a * z) → Commute z (a ^ n) := by
    rintro a n (rfl | h)
    · rw [pow_zero]
      exact Commute.one_right z
    · exact (show Commute z a from h).pow_right n
  exact ((c h₀).mul_right (c h₁)).mul_right (c h₂)

private theorem exists_axis_comb_fin : ∀ e₀ e₁ e₂ f₀ f₁ f₂ : Fin 3, e₀.val ≠ 0 → e₁.val ≠ 0 →
    e₂.val ≠ 0 → f₀.val ≠ 0 → f₁.val ≠ 0 → f₂.val ≠ 0 →
    ¬ (f₀.val = e₀.val ∧ f₁.val = e₁.val ∧ f₂.val = e₂.val) →
    ¬ (f₀.val = e₀.val * 2 % 3 ∧ f₁.val = e₁.val * 2 % 3 ∧ f₂.val = e₂.val * 2 % 3) →
    ∃ c : Fin 3,
      ((e₀.val + f₀.val * c.val) % 3 = 0 ∧ (e₁.val + f₁.val * c.val) % 3 = 0 ∧
        (e₂.val + f₂.val * c.val) % 3 ≠ 0) ∨
      ((e₀.val + f₀.val * c.val) % 3 = 0 ∧ (e₁.val + f₁.val * c.val) % 3 ≠ 0 ∧
        (e₂.val + f₂.val * c.val) % 3 = 0) ∨
      ((e₀.val + f₀.val * c.val) % 3 ≠ 0 ∧ (e₁.val + f₁.val * c.val) % 3 = 0 ∧
        (e₂.val + f₂.val * c.val) % 3 = 0) := by
  decide

private theorem exists_axis_comb {e₀ e₁ e₂ f₀ f₁ f₂ : ℕ} (he₀ : e₀ < 3) (he₁ : e₁ < 3)
    (he₂ : e₂ < 3) (hf₀ : f₀ < 3) (hf₁ : f₁ < 3) (hf₂ : f₂ < 3) (ne₀ : e₀ ≠ 0) (ne₁ : e₁ ≠ 0)
    (ne₂ : e₂ ≠ 0) (nf₀ : f₀ ≠ 0) (nf₁ : f₁ ≠ 0) (nf₂ : f₂ ≠ 0)
    (h₁ : ¬ (f₀ = e₀ ∧ f₁ = e₁ ∧ f₂ = e₂))
    (h₂ : ¬ (f₀ = e₀ * 2 % 3 ∧ f₁ = e₁ * 2 % 3 ∧ f₂ = e₂ * 2 % 3)) : ∃ c : ℕ,
      ((e₀ + f₀ * c) % 3 = 0 ∧ (e₁ + f₁ * c) % 3 = 0 ∧ (e₂ + f₂ * c) % 3 ≠ 0) ∨
      ((e₀ + f₀ * c) % 3 = 0 ∧ (e₁ + f₁ * c) % 3 ≠ 0 ∧ (e₂ + f₂ * c) % 3 = 0) ∨
      ((e₀ + f₀ * c) % 3 ≠ 0 ∧ (e₁ + f₁ * c) % 3 = 0 ∧ (e₂ + f₂ * c) % 3 = 0) := by
  obtain ⟨c, hc⟩ := exists_axis_comb_fin ⟨e₀, he₀⟩ ⟨e₁, he₁⟩ ⟨e₂, he₂⟩ ⟨f₀, hf₀⟩ ⟨f₁, hf₁⟩
    ⟨f₂, hf₂⟩ ne₀ ne₁ ne₂ nf₀ nf₁ nf₂ h₁ h₂
  exact ⟨c.val, hc⟩

theorem normalizer_le_of_axes {M A : Subgroup G} {p : ℕ} (hsp : IsStronglyPEmbedded p M)
    {a₀ a₁ a₂ : G} (h₀ : a₀ ^ 3 = 1) (h₁ : a₁ ^ 3 = 1) (h₂ : a₂ ^ 3 = 1)
    (h₀₁ : a₀ * a₁ = a₁ * a₀) (h₀₂ : a₀ * a₂ = a₂ * a₀) (h₁₂ : a₁ * a₂ = a₂ * a₁)
    (hn₁₂ : a₂ ∉ zpowers a₁) (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A)
    (hA : ∀ x ∈ A, ∃ i j k : ℕ, x = a₀ ^ i * a₁ ^ j * a₂ ^ k)
    (hN₁ : normalizer ((zpowers a₁ : Subgroup G) : Set G) ≤ M)
    (hN₂ : normalizer ((zpowers a₂ : Subgroup G) : Set G) ≤ M)
    (hN₀ : a₀ ≠ 1 → normalizer ((zpowers a₀ : Subgroup G) : Set G) ≤ M)
    (hy₁₂ : ∃ y ∈ M, orderOf y = p ∧ y * a₁ = a₁ * y ∧ y * a₂ = a₂ * y)
    (hy₀₁ : a₀ ≠ 1 → ∃ y ∈ M, orderOf y = p ∧ y * a₀ = a₀ * y ∧ y * a₁ = a₁ * y)
    (hy₀₂ : a₀ ≠ 1 → ∃ y ∈ M, orderOf y = p ∧ y * a₀ = a₀ * y ∧ y * a₂ = a₂ * y) :
    normalizer (A : Set G) ≤ M := by
  obtain ⟨y, hyM, hy, hy₁, hy₂⟩ := hy₁₂
  intro w hw
  by_contra hwM
  have hconj : ∀ {b : G}, b ∈ A → w * b * w⁻¹ ∈ A := fun hb => (mem_normalizer_iff.1 hw _).1 hb
  by_cases ha₀ : a₀ = 1
  · obtain ⟨i, j, k, hu⟩ := hA _ (hconj ha₁)
    refine hwM (mem_of_commute_conj_of_sp hsp hN₁ hyM hy ?_)
    rw [hu]
    exact commute_axes (Or.inr (by rw [ha₀, mul_one, one_mul])) (Or.inr hy₁) (Or.inr hy₂)
  obtain ⟨y₀₁, hy₀₁M, hy₀₁o, hy₀₁0, hy₀₁1⟩ := hy₀₁ ha₀
  obtain ⟨y₀₂, hy₀₂M, hy₀₂o, hy₀₂0, hy₀₂2⟩ := hy₀₂ ha₀
  have hA3 : ∀ x ∈ A, ∃ i < 3, ∃ j < 3, ∃ k < 3, x = a₀ ^ i * a₁ ^ j * a₂ ^ k := by
    intro x hx
    obtain ⟨i, j, k, rfl⟩ := hA x hx
    exact ⟨i % 3, Nat.mod_lt _ (by norm_num), j % 3, Nat.mod_lt _ (by norm_num), k % 3,
      Nat.mod_lt _ (by norm_num),
      by rw [← pow_eq_pow_mod i h₀, ← pow_eq_pow_mod j h₁, ← pow_eq_pow_mod k h₂]⟩
  have hnz : ∀ {b : G}, normalizer ((zpowers b : Subgroup G) : Set G) ≤ M → ∀ {i j k : ℕ},
      w * b * w⁻¹ = a₀ ^ i * a₁ ^ j * a₂ ^ k → i ≠ 0 ∧ j ≠ 0 ∧ k ≠ 0 := by
    intro b hNb i j k he
    refine ⟨fun hi => hwM (mem_of_commute_conj_of_sp hsp hNb hyM hy ?_),
      fun hj => hwM (mem_of_commute_conj_of_sp hsp hNb hy₀₂M hy₀₂o ?_),
      fun hk => hwM (mem_of_commute_conj_of_sp hsp hNb hy₀₁M hy₀₁o ?_)⟩ <;> rw [he]
    · exact commute_axes (Or.inl hi) (Or.inr hy₁) (Or.inr hy₂)
    · exact commute_axes (Or.inr hy₀₂0) (Or.inl hj) (Or.inr hy₀₂2)
    · exact commute_axes (Or.inr hy₀₁0) (Or.inr hy₀₁1) (Or.inl hk)
  obtain ⟨e₀, he₀, e₁, he₁, e₂, he₂, hu⟩ := hA3 _ (hconj ha₁)
  obtain ⟨f₀, hf₀, f₁, hf₁, f₂, hf₂, hv⟩ := hA3 _ (hconj ha₂)
  obtain ⟨ne₀, ne₁, ne₂⟩ := hnz hN₁ hu
  obtain ⟨nf₀, nf₁, nf₂⟩ := hnz hN₂ hv
  have hcancel : ∀ {b : G}, w * a₂ * w⁻¹ = w * b * w⁻¹ → a₂ = b := fun h =>
    (mul_right_inj w).1 ((mul_left_inj w⁻¹).1 h)
  have hne₁ : ¬ (f₀ = e₀ ∧ f₁ = e₁ ∧ f₂ = e₂) := by
    rintro ⟨rfl, rfl, rfl⟩
    exact hn₁₂ (hcancel (hv.trans hu.symm) ▸ mem_zpowers a₁)
  have hne₂ : ¬ (f₀ = e₀ * 2 % 3 ∧ f₁ = e₁ * 2 % 3 ∧ f₂ = e₂ * 2 % 3) := by
    rintro ⟨hf₀', hf₁', hf₂'⟩
    refine hn₁₂ (hcancel ?_ ▸ pow_mem (mem_zpowers a₁) 2)
    rw [← conj_pow, hu, pow_axes h₀₁ h₀₂ h₁₂, hv, pow_eq_pow_mod (e₀ * 2) h₀,
      pow_eq_pow_mod (e₁ * 2) h₁, pow_eq_pow_mod (e₂ * 2) h₂, hf₀', hf₁', hf₂']
  obtain ⟨c, hc⟩ := exists_axis_comb he₀ he₁ he₂ hf₀ hf₁ hf₂ ne₀ ne₁ ne₂ nf₀ nf₁ nf₂ hne₁ hne₂
  have huv : w * (a₁ * a₂ ^ c) * w⁻¹ =
      a₀ ^ ((e₀ + f₀ * c) % 3) * a₁ ^ ((e₁ + f₁ * c) % 3) * a₂ ^ ((e₂ + f₂ * c) % 3) := by
    rw [← pow_eq_pow_mod (e₀ + f₀ * c) h₀, ← pow_eq_pow_mod (e₁ + f₁ * c) h₁,
      ← pow_eq_pow_mod (e₂ + f₂ * c) h₂, ← mul_axes h₀₁ h₀₂ h₁₂, ← pow_axes h₀₁ h₀₂ h₁₂, ← hu, ← hv,
      conj_pow]
    group
  have hfin : ∀ {b : G} {n : ℕ}, b ^ 3 = 1 → n < 3 → n ≠ 0 →
      normalizer ((zpowers b : Subgroup G) : Set G) ≤ M → w * (a₁ * a₂ ^ c) * w⁻¹ = b ^ n →
        False := by
    intro b n hb3 hn3 hn0 hNb he
    have hnn : n * n % 3 = 1 := by
      rcases (show n = 1 ∨ n = 2 by omega) with rfl | rfl <;> rfl
    have hb : (b ^ n) ^ n = b := by rw [← pow_mul, pow_eq_pow_mod (n * n) hb3, hnn, pow_one]
    have h1 : w⁻¹ * b ^ n * w⁻¹⁻¹ = a₁ * a₂ ^ c := by
      rw [inv_inv, ← he]
      group
    have h3 : w⁻¹ * b * w⁻¹⁻¹ = (a₁ * a₂ ^ c) ^ n := by rw [← h1, conj_pow, hb]
    have hw' := mem_of_commute_conj_of_sp hsp hNb hyM hy (b := b) (w := w⁻¹) (by
      rw [h3]
      exact (((show Commute y a₁ from hy₁).mul_right
        ((show Commute y a₂ from hy₂).pow_right c)).pow_right n).eq)
    exact hwM (inv_inv w ▸ inv_mem hw')
  rcases hc with ⟨hz₀, hz₁, hz₂⟩ | ⟨hz₀, hz₁, hz₂⟩ | ⟨hz₀, hz₁, hz₂⟩
  · refine hfin h₂ (Nat.mod_lt _ (by norm_num)) hz₂ hN₂ ?_
    rw [huv, hz₀, hz₁, pow_zero, pow_zero, one_mul, one_mul]
  · refine hfin h₁ (Nat.mod_lt _ (by norm_num)) hz₁ hN₁ ?_
    rw [huv, hz₀, hz₂, pow_zero, pow_zero, one_mul, mul_one]
  · refine hfin h₀ (Nat.mod_lt _ (by norm_num)) hz₀ (hN₀ ha₀) ?_
    rw [huv, hz₁, hz₂, pow_zero, pow_zero, mul_one, mul_one]

variable [Finite G]

@[expose] def R847OrderThree (D : Data G) : Prop :=
  ∀ Y ∈ calC D.M, CFSG.Open.pRank 3 Y = 1 → ∀ X : Subgroup G, X ≤ Y → Nat.card X = 3 →
    ∀ p ∈ D.sig, p ≠ 3 → (F08.Thin8 Y ∨ ∃ n : ℕ, IsU3 (Bar2 Y) n) → normalizer (X : Set G) ≤ D.M

theorem normalizer_le_of_le_of_r847 {D : Data G} (hSg : UC6S846.SigmaStd D)
    (h847 : R847OrderThree D) {p : ℕ} (hp : p ∈ D.sig) (hp3 : p ≠ 3) {L X B : Subgroup G}
    (hL : L ∈ calC D.M) (r : CFSG.Open.pRank 3 L = 1)
    (hs : F08.Thin8 L ∨ ∃ n : ℕ, IsU3 (Bar2 L) n) (hXL : X ≤ L)
    (hX : Nat.card X = 3) (hXB : X ≤ B) {y : G} (hy : orderOf y = p)
    (hyB : y ∈ centralizer (B : Set G)) : normalizer (B : Set G) ≤ D.M := by
  haveI : Fact p.Prime := ⟨(D.sig_prime p hp).1⟩
  have hC : centralizer (B : Set G) ≤ D.M := (centralizer_le hXB).trans
    ((centralizer_le_normalizer _).trans (h847 L hL r X hXL hX p hp hp3 hs))
  refine (UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hL)
    hp).normalizer_le_of_centralizer_le hC ?_
  have h := orderOf_dvd_natCard (⟨y, hyB⟩ : ↥(centralizer (B : Set G)))
  rwa [Subgroup.orderOf_mk, hy] at h

end CFSG.LocalAnalysis.UniquenessCase.UC22.R8107E3

end
