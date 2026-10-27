module

public import CFSG.Quasithin.Background.SmithB45ExcOrbit
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.Quasithin.B45Exc

open Module CFSG.QuasithinUnique.Setup.Family

section Fpf

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [Module.Finite (ZMod 2) E]

theorem orderOf_two_dvd_finrank_of_fpf {p : ℕ} [hp : Fact p.Prime] {y : E ≃ₗ[ZMod 2] E}
    (hy : y ^ p = 1) (M : Submodule (ZMod 2) E) (hyM : ∀ x ∈ M, y x ∈ M)
    (hfpf : ∀ x ∈ M, y x = x → x = 0) :
    orderOf (2 : ZMod p) ∣ finrank (ZMod 2) M := by
  classical
  set yM := restrictEquiv y M hyM with hyMdef
  have hyMp : yM ^ p = 1 := by
    ext v
    rw [restrictEquiv_pow_apply, hy]
    rfl
  have : Finite M := Module.finite_of_finite (ZMod 2)
  have hpg : IsPGroup p (Subgroup.zpowers yM) := by
    have hdvd : orderOf yM ∣ p := orderOf_dvd_of_pow_eq_one hyMp
    rcases (Nat.dvd_prime hp.out).1 hdvd with h1 | h1
    · refine IsPGroup.of_card (n := 0) ?_
      rw [Nat.card_zpowers, h1, pow_zero]
    · refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, h1, pow_one]
  have hmod := hpg.card_modEq_card_fixedPoints M
  have hfix : Nat.card (MulAction.fixedPoints (Subgroup.zpowers yM) M) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => ?_⟩, ⟨⟨0, fun g => map_zero (g : M ≃ₗ[ZMod 2] M)⟩⟩⟩
    have hz : ∀ c : MulAction.fixedPoints (Subgroup.zpowers yM) M, (c : M) = 0 := by
      intro c
      have h1 : yM (c : M) = c := c.2 ⟨yM, Subgroup.mem_zpowers yM⟩
      apply Subtype.ext
      exact hfpf _ (c : M).2 (congrArg Subtype.val h1)
    exact Subtype.ext ((hz a).trans (hz b).symm)
  rw [hfix] at hmod
  have hcard : Nat.card M = 2 ^ finrank (ZMod 2) M := by
    have : Fintype M := Fintype.ofFinite M
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
  rw [hcard] at hmod
  have h2 : ((2 ^ finrank (ZMod 2) M : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 hmod
  push_cast at h2
  exact orderOf_dvd_of_pow_eq_one h2

theorem three_le_orderOf_two {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p) :
    3 ≤ orderOf (2 : ZMod p) := by
  by_contra hlt
  push Not at hlt
  have hpos : 0 < orderOf (2 : ZMod p) := by
    refine orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2 ⟨p - 1, by omega, ?_⟩)
    refine ZMod.pow_card_sub_one_eq_one ?_
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  have h1 : (2 : ZMod p) ^ orderOf (2 : ZMod p) = 1 := pow_orderOf_eq_one _
  interval_cases h : orderOf (2 : ZMod p)
  · have h' : ((2 - 1 : ℕ) : ZMod p) = 0 := by
      rw [Nat.cast_sub (by norm_num), Nat.cast_ofNat, Nat.cast_one, sub_eq_zero]
      simpa using h1
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  · have h' : ((4 - 1 : ℕ) : ZMod p) = 0 := by
      rw [Nat.cast_sub (by norm_num), Nat.cast_one, sub_eq_zero]
      have : (2 : ZMod p) ^ 2 = 4 := by norm_num
      rw [this] at h1
      exact_mod_cast h1
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    omega

end Fpf

section Blocks

variable {K : Type*} [Field K] [Fintype K] {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  {ρ : K × K → (E ≃ₗ[ZMod 2] E)} (h : IsVAct ρ) (hodd : Odd (Fintype.card K))

include h hodd

theorem two_mul_card_le_finrank_range_sub1 [Module.Finite (ZMod 2) E]
    (hpr : (Fintype.card K).Prime) (hp5 : 5 ≤ Fintype.card K)
    (hK : ∀ k : K, ∃ n : ℕ, (n : K) = k) {s : E ≃ₗ[ZMod 2] E} (hs : s * s = 1)
    (hsρ : ∀ x, s * ρ x * s = ρ (-x)) (U : Finset (K × K)) (hU0 : ∀ u ∈ U, u ≠ 0)
    (hUind : ∀ u ∈ U, ∀ v ∈ U, u ≠ v → det2 u v ≠ 0)
    (hUne : ∀ u ∈ U, lineProj ρ u ≠ 0) :
    2 * U.card ≤ finrank (ZMod 2) (LinearMap.range (sub1 s)) := by
  classical
  have : Fact (Fintype.card K).Prime := ⟨hpr⟩
  have hs' : (s : Module.End (ZMod 2) E) * (s : Module.End (ZMod 2) E) = 1 :=
    congrArg (fun f : E ≃ₗ[ZMod 2] E => (f : E →ₗ[ZMod 2] E)) hs
  have hsop : ∀ x, (s : Module.End (ZMod 2) E) * opE ρ x =
      opE ρ (-x) * (s : Module.End (ZMod 2) E) := by
    intro x
    have e : (s : Module.End (ZMod 2) E) * opE ρ x * (s : Module.End (ZMod 2) E) = opE ρ (-x) :=
      congrArg (fun f : E ≃ₗ[ZMod 2] E => (f : E →ₗ[ZMod 2] E)) (hsρ x)
    calc (s : Module.End (ZMod 2) E) * opE ρ x
        = (s : Module.End (ZMod 2) E) * opE ρ x * ((s : Module.End (ZMod 2) E) *
            (s : Module.End (ZMod 2) E)) := by rw [hs', mul_one]
      _ = ((s : Module.End (ZMod 2) E) * opE ρ x * (s : Module.End (ZMod 2) E)) *
            (s : Module.End (ZMod 2) E) := by simp only [mul_assoc]
      _ = opE ρ (-x) * (s : Module.End (ZMod 2) E) := by rw [e]
  have hcomm : ∀ u : K × K, (s : Module.End (ZMod 2) E) * lineProj ρ u =
      lineProj ρ u * (s : Module.End (ZMod 2) E) := by
    intro u
    unfold lineProj lineSum fullSum
    rw [mul_add, add_mul, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    congr 1
    · simp_rw [hsop]
      calc ∑ k : K, opE ρ (-(k • u)) * (s : Module.End (ZMod 2) E)
          = ∑ k : K, (fun k : K => opE ρ (k • u) * (s : Module.End (ZMod 2) E)) (-k) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            simp only [neg_smul]
        _ = ∑ k : K, opE ρ (k • u) * (s : Module.End (ZMod 2) E) :=
            Equiv.sum_comp (Equiv.neg K)
              (fun k : K => opE ρ (k • u) * (s : Module.End (ZMod 2) E))
    · simp_rw [hsop]
      exact Equiv.sum_comp (Equiv.neg (K × K))
        (fun x : K × K => opE ρ x * (s : Module.End (ZMod 2) E))
  have hc : ∀ u ∈ U, 2 ≤
      finrank (ZMod 2) ((LinearMap.range (lineProj ρ u)).map (sub1 s)) := by
    intro u hu
    obtain ⟨w, hw⟩ := exists_det_ne u (hU0 u hu)
    set M := LinearMap.range (lineProj ρ u) with hM
    have hMne : M ≠ ⊥ := fun h0 => hUne u hu (LinearMap.range_eq_bot.1 h0)
    have hMpos : 1 ≤ finrank (ZMod 2) M := Submodule.one_le_finrank_iff.2 hMne
    have hm : Odd (Fintype.card (K × K)) := by
      rw [Fintype.card_prod]; exact hodd.mul hodd
    have hvm : (ρ w) ^ (Fintype.card (K × K)) = 1 := by
      rw [← map_nsmul_eq_pow h, card_nsmul_eq_zero, h.map_zero]
    have hvp : (ρ w) ^ (Fintype.card K) = 1 := by
      rw [← map_nsmul_eq_pow h]
      have : (Fintype.card K) • w = 0 := by
        rw [← Nat.cast_smul_eq_nsmul K, FiniteField.cast_card_eq_zero, zero_smul]
      rw [this, h.map_zero]
    have hsv : s * ρ w * s = (ρ w)⁻¹ := by rw [hsρ, map_neg_eq_inv h]
    have hsM : ∀ x ∈ M, s x ∈ M := by
      rintro _ ⟨y, rfl⟩
      refine ⟨s y, ?_⟩
      have := LinearMap.congr_fun (hcomm u) y
      simpa [Module.End.mul_apply] using this.symm
    have hvM : ∀ x ∈ M, (ρ w) x ∈ M := by
      rintro _ ⟨y, rfl⟩
      refine ⟨ρ w y, ?_⟩
      have := LinearMap.congr_fun (opE_mul_lineProj_comm h w u) y
      simpa [Module.End.mul_apply, opE] using this.symm
    have hfpf : ∀ x ∈ M, (ρ w) x = x → x = 0 := fun x hx hwx =>
      fpf_of_mem_range h hodd hw hK hx hwx
    have hhalf := finrank_half M hs hsv hm hvm hsM hvM hfpf
    have hdvd := orderOf_two_dvd_finrank_of_fpf hvp M hvM hfpf
    have h3 := three_le_orderOf_two (p := Fintype.card K) hp5
    have hge := Nat.le_of_dvd (by omega) hdvd
    omega
  have := sum_le_finrank_range_sub1 s U (fun u => lineProj ρ u)
    (fun u _ => lineProj_mul_self h hodd u)
    (fun u hu v hv huv => lineProj_mul_of_indep h hodd (hUind u hu v hv huv))
    (fun u _ => by simpa using hcomm u) (fun _ => 2) hc
  simpa [Finset.sum_const, mul_comm] using this

end Blocks

end CFSG.Quasithin.B45Exc
