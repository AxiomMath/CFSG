module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitDkRootsWeyl

public section

namespace CFSG.StandardType

open CFSG.LieType.RootSystem CFSG.LieType.Universal.Spin

theorem eq_pm_of_ggDDot_ne_zero {k : ℕ} {ε : Fin k → ℤ}
    (hε : ∀ a, ε a = 1 ∨ ε a = -1) {γ : Fin k → ℤ} (hγ : γ ∈ ggDRootSet k)
    (h0 : ggDDot ε γ ≠ 0) : ∃ a b : Fin k, a ≠ b ∧
      (γ = Pi.single a (ε a) + Pi.single b (ε b) ∨
        γ = -(Pi.single a (ε a) + Pi.single b (ε b))) := by
  obtain ⟨a, b, s, u, hab, hs, hu, rfl⟩ := hγ
  rw [ggDDot_comm, ggDDot_single_add_single] at h0
  refine ⟨a, b, hab, ?_⟩
  rcases hε a with ha | ha <;> rcases hε b with hb | hb <;> rcases hs with rfl | rfl <;>
    rcases hu with rfl | rfl <;>
    first
    | (left; rw [ha, hb]; done)
    | (right; rw [ha, hb]; simp only [Pi.single_neg, neg_add, neg_neg]; done)
    | (rw [ha, hb] at h0; norm_num at h0)

private theorem ggDReflect_move {k : ℕ} {ε : Fin k → ℤ} (hε : ∀ a, ε a = 1 ∨ ε a = -1)
    {x y z : Fin k} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ggDReflect (Pi.single y (ε y) + Pi.single z (-ε z)) (Pi.single x (ε x) + Pi.single y (ε y)) =
      Pi.single x (ε x) + Pi.single z (ε z) := by
  have h1 : ggDDot (Pi.single x (ε x) + Pi.single y (ε y))
      (Pi.single y (ε y) + Pi.single z (-ε z)) = 1 := by
    rw [ggDDot_single_add_single, ggDPair_apply_of_ne hxy hxz, ggDPair_apply_left hyz, mul_zero,
      zero_add]
    rcases hε y with h | h <;> rw [h] <;> norm_num
  rw [ggDReflect, h1, one_smul, Pi.single_neg]
  abel

theorem ggDk_eq_top_of_signedA {k : ℕ} (hk : 4 ≤ k) {ε : Fin k → ℤ}
    (hε : ∀ a, ε a = 1 ∨ ε a = -1) {H : Subgroup (ggWeylD k)}
    (hA : ∀ (t : ggWeylD k) (γ : Fin k → ℤ), GGDReflRoot k t γ → ggDDot ε γ = 0 → t ∈ H)
    {t₀ : ggWeylD k} {η : Fin k → ℤ} (ht₀ : GGDReflRoot k t₀ η) (hη : ggDDot ε η ≠ 0)
    (ht₀H : t₀ ∈ H) : H = ⊤ := by
  have hk2 : 2 ≤ k := by omega
  have hk1 : k ≠ 1 := by omega
  have hsq : ∀ a, ε a * ε a = 1 := fun a => by rcases hε a with h | h <;> rw [h] <;> norm_num
  have hAyz : ∀ y z : Fin k, y ≠ z →
      ∃ g ∈ H, GGDReflRoot k g (Pi.single y (ε y) + Pi.single z (-ε z)) := by
    intro y z hyz
    have hz : -ε z = 1 ∨ -ε z = -1 := by rcases hε z with h | h <;> rw [h] <;> norm_num
    obtain ⟨g, hg⟩ := exists_ggDReflRoot (k := k) ⟨y, z, ε y, -ε z, hyz, hε y, hz, rfl⟩
    refine ⟨g, hA g _ hg ?_, hg⟩
    rw [ggDDot_comm, ggDDot_single_add_single, neg_mul, hsq, hsq, add_neg_cancel]
  have hstep : ∀ x y z : Fin k, x ≠ y → x ≠ z →
      (∃ t ∈ H, GGDReflRoot k t (Pi.single x (ε x) + Pi.single y (ε y))) →
      ∃ t ∈ H, GGDReflRoot k t (Pi.single x (ε x) + Pi.single z (ε z)) := by
    rintro x y z hxy hxz ⟨t, htH, ht⟩
    by_cases hyz : y = z
    · rw [← hyz]
      exact ⟨t, htH, ht⟩
    obtain ⟨g, hgH, hg⟩ := hAyz y z hyz
    refine ⟨g * t * g⁻¹, mul_mem (mul_mem hgH htH) (inv_mem hgH), ?_⟩
    rw [← ggDReflect_move hε hxy hxz hyz]
    exact ht.conj (hg.action hk2)
  have hswap : ∀ x y : Fin k,
      (∃ t ∈ H, GGDReflRoot k t (Pi.single x (ε x) + Pi.single y (ε y))) →
      ∃ t ∈ H, GGDReflRoot k t (Pi.single y (ε y) + Pi.single x (ε x)) := by
    rintro x y ⟨t, htH, ht⟩
    exact ⟨t, htH, by rwa [add_comm] at ht⟩
  obtain ⟨c, d, hcd, hηcd⟩ := eq_pm_of_ggDDot_ne_zero hε (ht₀.mem hk1) hη
  have hcd' : ∃ t ∈ H, GGDReflRoot k t (Pi.single c (ε c) + Pi.single d (ε d)) := by
    refine ⟨t₀, ht₀H, ?_⟩
    rcases hηcd with rfl | rfl
    · exact ht₀
    · simpa only [neg_neg] using ht₀.neg
  have hall : ∀ a b : Fin k, a ≠ b →
      ∃ t ∈ H, GGDReflRoot k t (Pi.single a (ε a) + Pi.single b (ε b)) := by
    intro a b hab
    by_cases hac : a = c
    · rw [hac] at hab ⊢
      exact hstep c d b hcd hab hcd'
    · exact hstep a c b hac hab (hswap c a (hstep c d a hcd (Ne.symm hac) hcd'))
  have hrefl : ∀ (t : ggWeylD k) (γ : Fin k → ℤ), GGDReflRoot k t γ → t ∈ H := by
    intro t γ ht
    by_cases h0 : ggDDot ε γ = 0
    · exact hA t γ ht h0
    obtain ⟨a, b, hab, hγ⟩ := eq_pm_of_ggDDot_ne_zero hε (ht.mem hk1) h0
    obtain ⟨t', ht'H, ht'⟩ := hall a b hab
    rw [← ht'.unique hk2 ht hγ]
    exact ht'H
  refine eq_top_iff.2 fun w _ => ?_
  exact (coxeterMatrix (isFiniteType_cartanD k)).toCoxeterSystem.simple_induction
    (p := (· ∈ H)) w (fun i => hrefl _ _ (ggDReflRoot_simple k i)) (one_mem H)
    fun _ _ => mul_mem

end CFSG.StandardType

end
