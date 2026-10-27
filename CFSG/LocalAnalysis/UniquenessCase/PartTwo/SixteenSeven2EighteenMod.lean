module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsBridge

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {W : Type} [CommGroup W] [Finite W]

theorem s16c167_le_mParam (X : Subgroup (MulAut W)) {n : ℕ}
    (hinv : ∀ t ∈ X, t * t = 1 → t ≠ 1 → n ≤ rkIdx (fixV (Subgroup.zpowers t)))
    (hodd : n ≤ rk W) : n ≤ E3.mParam X := by
  unfold E3.mParam
  split_ifs with he
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h2 : 2 ∣ Nat.card X := even_iff_two_dvd.mp he
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := X) 2 h2
    have hmem : rkIdx (fixV (Subgroup.zpowers (x : MulAut W))) ∈
        {n : ℕ | ∃ t ∈ X, orderOf t = 2 ∧ n = rkIdx (fixV (Subgroup.zpowers t))} :=
      ⟨(x : MulAut W), x.2, (Subgroup.orderOf_coe x).trans hx, rfl⟩
    obtain ⟨t, htX, htord, htn⟩ := Nat.sInf_mem ⟨_, hmem⟩
    rw [htn]
    refine hinv t htX ?_ ?_
    · have hpow : t ^ 2 = 1 := by rw [← htord]; exact pow_orderOf_eq_one t
      simpa [pow_two] using hpow
    · intro h
      rw [h, orderOf_one] at htord
      exact absurd htord (by norm_num)
  · exact hodd

theorem s16c167_rk_le_rkIdx_of_inf_map_eq_bot (t : MulAut W) {I : Subgroup W}
    (h : I ⊓ I.map t.toMonoidHom = ⊥) : rk ↥I ≤ rkIdx (fixV (Subgroup.zpowers t)) := by
  have hF : fixV (Subgroup.zpowers t) ⊓ I = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    have hx1 : t x = x := (mem_fixV_zpowers t x).mp hx.1
    have hmem : x ∈ I ⊓ I.map t.toMonoidHom :=
      ⟨hx.2, Subgroup.mem_map.mpr ⟨x, hx.2, hx1⟩⟩
    rw [h, Subgroup.mem_bot] at hmem
    simpa using hmem
  have h1 := rk_sup_add_rk_inf (fixV (Subgroup.zpowers t)) I
  rw [hF, rk_bot] at h1
  have h2 : rk ↥(fixV (Subgroup.zpowers t) ⊔ I) ≤ rk W := by
    have h2' := rk_mono (G := W) (le_top : fixV (Subgroup.zpowers t) ⊔ I ≤ ⊤)
    rwa [rk_top] at h2'
  have h3 := rk_add_rkIdx (fixV (Subgroup.zpowers t))
  omega

theorem s16c167_rkIdx_fixV_split (hW : ∀ w : W, w ^ 2 = 1) (t : MulAut W) {I₁ I₂ : Subgroup W}
    (hdisj : I₁ ⊓ I₂ = ⊥) (hsup : I₁ ⊔ I₂ = ⊤) (h₁ : I₁.map t.toMonoidHom = I₁)
    (h₂ : I₂.map t.toMonoidHom = I₂) :
    rkIdx (fixV (Subgroup.zpowers t)) =
      E3.mQuot I₁ (I₁ ⊓ fixV (Subgroup.zpowers t)) +
        E3.mQuot I₂ (I₂ ⊓ fixV (Subgroup.zpowers t)) := by
  have hdec : ∀ w : W, ∃ x₁ ∈ I₁, ∃ x₂ ∈ I₂, x₁ * x₂ = w := by
    intro w
    have hw : w ∈ I₁ ⊔ I₂ := by rw [hsup]; trivial
    rwa [Subgroup.mem_sup] at hw
  have ht₁ : ∀ x ∈ I₁, t x ∈ I₁ := fun x hx => by
    have h : t x ∈ I₁.map t.toMonoidHom := Subgroup.mem_map_of_mem _ hx
    rwa [h₁] at h
  have ht₂ : ∀ x ∈ I₂, t x ∈ I₂ := fun x hx => by
    have h : t x ∈ I₂.map t.toMonoidHom := Subgroup.mem_map_of_mem _ hx
    rwa [h₂] at h
  have huniq : ∀ {a a' b b' : W}, a ∈ I₁ → a' ∈ I₁ → b ∈ I₂ → b' ∈ I₂ →
      a * b = a' * b' → a = a' ∧ b = b' := by
    intro a a' b b' ha ha' hb hb' h
    have h1 : a'⁻¹ * a = b' * b⁻¹ := by
      have h2 : a'⁻¹ * a * b = b' := by
        rw [mul_assoc, h, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [← h2, mul_assoc, mul_inv_cancel, mul_one]
    have hmem : a'⁻¹ * a ∈ I₁ ⊓ I₂ :=
      ⟨I₁.mul_mem (I₁.inv_mem ha') ha,
        by rw [h1]; exact I₂.mul_mem hb' (I₂.inv_mem hb)⟩
    rw [hdisj, Subgroup.mem_bot] at hmem
    have hb1 : b' * b⁻¹ = 1 := by rw [← h1]; exact hmem
    exact ⟨(inv_mul_eq_one.mp hmem).symm, (mul_inv_eq_one.mp hb1).symm⟩
  have hfix : ∀ x₁ ∈ I₁, ∀ x₂ ∈ I₂,
      (x₁ * x₂ ∈ fixV (Subgroup.zpowers t) ↔
        x₁ ∈ fixV (Subgroup.zpowers t) ∧ x₂ ∈ fixV (Subgroup.zpowers t)) := by
    intro x₁ hx₁ x₂ hx₂
    rw [mem_fixV_zpowers, mem_fixV_zpowers, mem_fixV_zpowers]
    constructor
    · intro h
      have h' : t x₁ * t x₂ = x₁ * x₂ := by rw [← map_mul, h]
      exact huniq (ht₁ x₁ hx₁) hx₁ (ht₂ x₂ hx₂) hx₂ h'
    · rintro ⟨h₁', h₂'⟩
      rw [map_mul, h₁', h₂']
  have hCsup : fixV (Subgroup.zpowers t) =
      (I₁ ⊓ fixV (Subgroup.zpowers t)) ⊔ (I₂ ⊓ fixV (Subgroup.zpowers t)) := by
    apply le_antisymm
    · intro w hw
      obtain ⟨x₁, hx₁, x₂, hx₂, hwx⟩ := hdec w
      rw [← hwx] at hw ⊢
      have hmem := (hfix x₁ hx₁ x₂ hx₂).mp hw
      exact Subgroup.mul_mem_sup (Subgroup.mem_inf.mpr ⟨hx₁, hmem.1⟩)
        (Subgroup.mem_inf.mpr ⟨hx₂, hmem.2⟩)
    · exact sup_le inf_le_right inf_le_right
  have hCdisj : (I₁ ⊓ fixV (Subgroup.zpowers t)) ⊓ (I₂ ⊓ fixV (Subgroup.zpowers t)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    have hxInf : x ∈ I₁ ⊓ I₂ := ⟨hx.1.1, hx.2.1⟩
    rw [hdisj, Subgroup.mem_bot] at hxInf
    simpa using hxInf
  have hdisjI : rk W = rk ↥I₁ + rk ↥I₂ := by
    have h := rk_sup_add_rk_inf I₁ I₂
    rw [hsup, rk_top, hdisj, rk_bot] at h
    omega
  have hdisjC : rk (fixV (Subgroup.zpowers t)) =
      rk ↥(I₁ ⊓ fixV (Subgroup.zpowers t)) +
        rk ↥(I₂ ⊓ fixV (Subgroup.zpowers t)) := by
    have h := rk_sup_add_rk_inf
      (I₁ ⊓ fixV (Subgroup.zpowers t)) (I₂ ⊓ fixV (Subgroup.zpowers t))
    rw [← hCsup, hCdisj, rk_bot] at h
    omega
  have hcard₁ : rk ↥I₁ = E3.mQuot I₁ (I₁ ⊓ fixV (Subgroup.zpowers t)) +
      rk ↥(I₁ ⊓ fixV (Subgroup.zpowers t)) := by
    have h := E3.card_eq_two_pow_mul ((isPGroup_two_of_sq_eq_one hW).to_subgroup I₁)
      (inf_le_left : I₁ ⊓ fixV (Subgroup.zpowers t) ≤ I₁)
    rw [card_eq_two_pow hW, card_eq_two_pow hW, ← pow_add] at h
    exact Nat.pow_right_injective (le_refl 2) h
  have hcard₂ : rk ↥I₂ = E3.mQuot I₂ (I₂ ⊓ fixV (Subgroup.zpowers t)) +
      rk ↥(I₂ ⊓ fixV (Subgroup.zpowers t)) := by
    have h := E3.card_eq_two_pow_mul ((isPGroup_two_of_sq_eq_one hW).to_subgroup I₂)
      (inf_le_left : I₂ ⊓ fixV (Subgroup.zpowers t) ≤ I₂)
    rw [card_eq_two_pow hW, card_eq_two_pow hW, ← pow_add] at h
    exact Nat.pow_right_injective (le_refl 2) h
  have hCidx := rk_add_rkIdx (fixV (Subgroup.zpowers t))
  omega

theorem s16c167_le_mParam_of_blocks (hW : ∀ w : W, w ^ 2 = 1) (X : Subgroup (MulAut W))
    {I₁ I₂ : Subgroup W} {n : ℕ} (hdisj : I₁ ⊓ I₂ = ⊥) (hsup : I₁ ⊔ I₂ = ⊤)
    (hn₁ : n ≤ rk ↥I₁) (hn₂ : n ≤ rk ↥I₂)
    (hperm : ∀ t ∈ X, t * t = 1 → ∀ I ∈ ({I₁, I₂} : Set (Subgroup W)),
      I.map t.toMonoidHom = I ∨ I ⊓ I.map t.toMonoidHom = ⊥)
    (hloc : ∀ t ∈ X, t * t = 1 → ∀ I ∈ ({I₁, I₂} : Set (Subgroup W)),
      I.map t.toMonoidHom = I → I ≤ fixV (Subgroup.zpowers t) ∨
        n ≤ E3.mQuot I (I ⊓ fixV (Subgroup.zpowers t))) :
    n ≤ E3.mParam X := by
  have hodd : n ≤ rk W := by
    have h := le_trans hn₁ (rk_mono (le_sup_left : I₁ ≤ I₁ ⊔ I₂))
    rwa [hsup, rk_top] at h
  refine s16c167_le_mParam X ?_ hodd
  intro t htX ht2 htne
  rcases hperm t htX ht2 I₁ (by simp) with h₁ | h₁
  · rcases hperm t htX ht2 I₂ (by simp) with h₂ | h₂
    · have hsplit := s16c167_rkIdx_fixV_split hW t hdisj hsup h₁ h₂
      have hloc₁ := hloc t htX ht2 I₁ (by simp) h₁
      have hloc₂ := hloc t htX ht2 I₂ (by simp) h₂
      rcases hloc₁ with hc₁ | hc₁
      · rcases hloc₂ with hc₂ | hc₂
        · exfalso
          apply htne
          ext x
          have hx : x ∈ fixV (Subgroup.zpowers t) := by
            have hx' : x ∈ I₁ ⊔ I₂ := by rw [hsup]; trivial
            rw [Subgroup.mem_sup] at hx'
            obtain ⟨y, hy, z, hz, hyz⟩ := hx'
            rw [← hyz]
            exact (fixV (Subgroup.zpowers t)).mul_mem (hc₁ hy) (hc₂ hz)
          simpa using (mem_fixV_zpowers t x).mp hx
        · omega
      · omega
    · exact le_trans hn₂ (s16c167_rk_le_rkIdx_of_inf_map_eq_bot t h₂)
  · exact le_trans hn₁ (s16c167_rk_le_rkIdx_of_inf_map_eq_bot t h₁)

theorem s16c167_perm_of_orbit {X : Subgroup (MulAut W)} {I₀ I₁ I₂ : Subgroup W}
    (hne : I₁ ≠ I₂) (hdisj : I₁ ⊓ I₂ = ⊥)
    (horb : {J | ∃ φ ∈ X, J = I₀.map φ.toMonoidHom} = {I₁, I₂}) :
    ∀ t ∈ X, ∀ I ∈ ({I₁, I₂} : Set (Subgroup W)),
      I.map t.toMonoidHom = I ∨ I ⊓ I.map t.toMonoidHom = ⊥ := by
  intro t htX I hI
  have horbI : I ∈ {J | ∃ φ ∈ X, J = I₀.map φ.toMonoidHom} := by rw [horb]; exact hI
  obtain ⟨φ, hφX, hφ⟩ := horbI
  have hmem : I.map t.toMonoidHom ∈ ({I₁, I₂} : Set (Subgroup W)) := by
    rw [← horb]
    refine ⟨t * φ, X.mul_mem htX hφX, ?_⟩
    rw [hφ, Subgroup.map_map]
    rfl
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hI
  rcases hI with hI | hI
  · subst hI
    rcases hmem with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [h]; exact hdisj)
  · subst hI
    rcases hmem with h | h
    · exact Or.inr (by rw [h, inf_comm]; exact hdisj)
    · exact Or.inl h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
