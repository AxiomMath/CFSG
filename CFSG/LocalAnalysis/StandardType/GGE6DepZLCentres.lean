module

public import CFSG.LocalAnalysis.StandardType.GGE6DepZLFinite

public section

namespace CFSG.StandardType

namespace E6Dep

namespace ZL

private lemma zlc2_two_cartan_apply : ∀ i : Fin 6, ((2 : ZMod 3) • cartanE6 i) i = 1 := by
  decide +kernel

private lemma zlc2_kappa_two_cartan :
    ∀ i : Fin 6, kappa ⬝ᵥ ((2 : ZMod 3) • cartanE6 i) = 0 := by
  decide +kernel

theorem zl_frame_centres {V : Type} [AddCommGroup V] (hexp : ∀ v : V, 3 • v = 0) {Φ : V →+ Vec6}
    {σ : Fin 6 → V →+ V} {x : V} (hΦ2 : ∀ u : Vec6, kappa ⬝ᵥ u = 0 → ∃ v, Φ v = u)
    (hΦ3 : ∀ v, Φ v = 0 ↔ v ∈ AddSubgroup.zmultiples x) (hx : x ≠ 0)
    (hσΦ : ∀ i v, Φ (σ i v) = Φ v - Φ v i • cartanE6 i) (hσx : ∀ i, σ i x = x)
    (hσσ : ∀ i v, σ i (σ i v) = v) :
    ∃ h : Fin 6 → V, (∀ i, Φ (h i) = cartanE6 i) ∧ ∀ i v, σ i v = v - (Φ v i).val • h i := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hd0 : ∀ i v, Φ v i = 0 → σ i v - v = 0 := by
    intro i v hv
    have hΦd : Φ (σ i v - v) = 0 := by
      rw [map_sub, hσΦ i v, hv, zero_smul, sub_zero, sub_self]
    obtain ⟨k, hk⟩ :=
      AddSubgroup.mem_zmultiples_iff.mp ((hΦ3 (σ i v - v)).mp hΦd)
    have hσd : σ i (σ i v - v) = -(σ i v - v) := by
      rw [map_sub, hσσ i v]
      abel
    have hσkx : σ i (k • x) = k • x := by
      rw [map_zsmul, hσx i]
    have hkeq : k • x = -(k • x) := by
      calc k • x = σ i (k • x) := hσkx.symm
        _ = σ i (σ i v - v) := by rw [hk]
        _ = -(σ i v - v) := hσd
        _ = -(k • x) := by rw [hk]
    have h2k : (2 * k) • x = 0 := by
      have h := eq_neg_iff_add_eq_zero.mp hkeq
      rw [← add_zsmul] at h
      rwa [show k + k = 2 * k from by ring] at h
    have horder : addOrderOf x = 3 := addOrderOf_eq_prime (hexp x) hx
    have h3dvd : (3 : ℤ) ∣ 2 * k := by
      have h := (addOrderOf_dvd_iff_zsmul_eq_zero (x := x) (i := 2 * k)).mpr h2k
      rw [horder] at h
      norm_num at h
      exact h
    have h3dvdk : (3 : ℤ) ∣ k :=
      Int.dvd_of_dvd_mul_right_of_gcd_one h3dvd (by decide)
    have hk0 : k • x = 0 :=
      (addOrderOf_dvd_iff_zsmul_eq_zero (x := x) (i := k)).mp (by
        rw [horder]
        norm_num
        exact h3dvdk)
    rw [← hk]
    exact hk0
  have hb : ∀ i : Fin 6, ∃ b : V, Φ b i = 1 := by
    intro i
    obtain ⟨b, hb⟩ := hΦ2 ((2 : ZMod 3) • cartanE6 i) (zlc2_kappa_two_cartan i)
    exact ⟨b, by rw [hb]; exact zlc2_two_cartan_apply i⟩
  choose b hb1 using hb
  refine ⟨fun i => b i - σ i (b i), ?_, ?_⟩
  ·
    intro i
    rw [map_sub, hσΦ i (b i), hb1 i, one_smul, sub_sub_cancel]
  ·
    intro i v
    have hv' : Φ (v - (Φ v i).val • b i) i = 0 := by
      rw [map_sub, map_nsmul]
      change Φ v i - (Φ v i).val • Φ (b i) i = 0
      rw [hb1 i, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val, sub_self]
    have hfix : σ i (v - (Φ v i).val • b i) = v - (Φ v i).val • b i :=
      sub_eq_zero.mp (hd0 i _ hv')
    calc σ i v
        = σ i ((v - (Φ v i).val • b i) + (Φ v i).val • b i) := by
          rw [sub_add_cancel]
      _ = σ i (v - (Φ v i).val • b i) + (Φ v i).val • σ i (b i) := by
          rw [map_add, map_nsmul]
      _ = (v - (Φ v i).val • b i) + (Φ v i).val • σ i (b i) := by rw [hfix]
      _ = v - (Φ v i).val • (b i - σ i (b i)) := by
          rw [smul_sub]
          abel

end ZL

end E6Dep

end CFSG.StandardType

end
