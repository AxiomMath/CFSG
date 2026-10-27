module

public import CFSG.RankThree.PartOne.KC.OrthogonalDerivedCentralizer

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

section Semilinear

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem eq_refl_of_scalar_line {σ : K ≃+* K} {F : V ≃+ V}
    (hFσ : ∀ (c : K) (v : V), F (c • v) = σ c • F v) {c : K} (hc : c ≠ 0) {w : V} (hw : w ≠ 0)
    (hscal : ∀ t : K, F (t • w) = c • t • w) : σ = RingEquiv.refl K := by
  refine RingEquiv.ext fun t => ?_
  have h1 := hscal 1
  rw [one_smul] at h1
  have h2 := hscal t
  rw [hFσ, h1, smul_smul, smul_smul] at h2
  have h3 : (σ t * c - c * t) • w = 0 := by rw [sub_smul]; exact sub_eq_zero.mpr h2
  have h4 := (smul_eq_zero.mp h3).resolve_right hw
  have h5 : c * (σ t - t) = 0 := by linear_combination h4
  have := (mul_eq_zero.mp h5).resolve_left hc
  exact sub_eq_zero.mp this

theorem eq_smul_of_iSup_eq_top {F : V ≃+ V} {c : K} {ι : Type*} {S : ι → Submodule K V}
    (htop : ⨆ i, S i = ⊤) (h : ∀ i, ∀ v ∈ S i, F v = c • v) : ∀ v, F v = c • v := by
  intro v
  have hv : v ∈ ⨆ i, S i := htop ▸ Submodule.mem_top
  refine Submodule.iSup_induction S (motive := fun v => F v = c • v) hv (fun i v hv => h i v hv)
    (by simp) (fun a b ha hb => ?_)
  rw [map_add, ha, hb, smul_add]

theorem eq_smul_of_mem_iSup {F : V ≃+ V} {c : K} {ι : Type*} {S : ι → Submodule K V}
    (h : ∀ i, ∀ v ∈ S i, F v = c • v) {v : V} (hv : v ∈ ⨆ i, S i) : F v = c • v := by
  refine Submodule.iSup_induction S (motive := fun v => F v = c • v) hv
    (fun i v hv => h i v hv) (by simp) (fun a b ha hb => ?_)
  rw [map_add, ha, hb, smul_add]

end Semilinear

section Characters

variable {G : Type*} [Group G]

theorem exists_zpow_mul_of_card [IsMulCommutative G] {p : ℕ} (hp : p.Prime)
    (hG : Nat.card G = p ^ 2) {M : Subgroup G} (hM : Nat.card M = p) {b : G} (hb : b ∉ M)
    (y : G) : ∃ n : ℤ, ∃ m ∈ M, y = b ^ n * m := by
  have : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card (G ⧸ M) = p := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup M
    rw [hG, hM, pow_two] at h
    exact (Nat.eq_of_mul_eq_mul_right hp.pos h).symm
  have hb1 : (b : G ⧸ M) ≠ 1 := fun h => hb ((QuotientGroup.eq_one_iff b).mp h)
  have hy : (y : G ⧸ M) ∈ Subgroup.zpowers (b : G ⧸ M) :=
    mem_zpowers_of_prime_card hcard hb1
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy
  refine ⟨n, (b ^ n)⁻¹ * y, ?_, by group⟩
  rw [← QuotientGroup.eq]
  rw [← hn]
  rfl

theorem exists_zmod_char {Γ : Type*} [Group Γ] {p : ℕ} [Fact p.Prime] (ρ : G →* Γ) (b : G)
    (hbG : ∀ y : G, ∃ n : ℤ, ρ y = ρ b ^ n) (hord : orderOf (ρ b) = p) :
    ∃ k : G →* Multiplicative (ZMod p), ∀ y, ρ y = ρ b ^ (k y).toAdd.val := by
  classical
  have hpow : ∀ n : ℤ, ρ b ^ n = ρ b ^ ((n : ZMod p).val) := by
    intro n
    have h1 : ((n : ZMod p)) = (((n : ZMod p).val : ℕ) : ZMod p) := (ZMod.natCast_zmod_val _).symm
    have h2 : ((n : ℤ) : ZMod p) = ((((n : ZMod p).val : ℕ) : ℤ) : ZMod p) := by simp
    have h3 := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ p).mp h2
    have h4 : ρ b ^ ((((n : ZMod p).val : ℕ) : ℤ) - n) = 1 :=
      orderOf_dvd_iff_zpow_eq_one.mp (by rw [hord]; exact h3)
    rw [zpow_sub, mul_inv_eq_one, zpow_natCast] at h4
    exact h4.symm
  let kf : G → ZMod p := fun y => ((Classical.choose (hbG y) : ℤ) : ZMod p)
  have hkf : ∀ y, ρ y = ρ b ^ (kf y).val := fun y => by
    rw [Classical.choose_spec (hbG y), hpow]
  have hinj : ∀ a c : ℕ, ρ b ^ a = ρ b ^ c → (a : ZMod p) = c := fun a c h => by
    rw [pow_eq_pow_iff_modEq, hord] at h
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr h
  have hmul : ∀ y y' : G, Multiplicative.ofAdd (kf (y * y')) =
      Multiplicative.ofAdd (kf y) * Multiplicative.ofAdd (kf y') := by
    intro y y'
    have h1 : ρ b ^ (kf (y * y')).val = ρ b ^ ((kf y).val + (kf y').val) := by
      rw [← hkf, map_mul, hkf y, hkf y', pow_add]
    have := hinj _ _ h1
    rw [ZMod.natCast_zmod_val, Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at this
    exact congrArg Multiplicative.ofAdd this
  exact ⟨MonoidHom.mk' (fun y => Multiplicative.ofAdd (kf y)) hmul, fun y => hkf y⟩

theorem exists_ne_one_chars_eq {p : ℕ} (hp : p.Prime) (hG : Nat.card G = p ^ 2)
    (χ₁ χ₂ : G →* Multiplicative (ZMod p)) : ∃ g : G, g ≠ 1 ∧ χ₁ g = χ₂ g := by
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨g, hg1, hg⟩ := exists_ne_one_mem_ker hp hG (χ₁ * χ₂⁻¹)
  exact ⟨g, hg1, mul_inv_eq_one.mp hg⟩

theorem exists_ne_one_chars_mul_eq_one {p : ℕ} (hp : p.Prime) (hG : Nat.card G = p ^ 2)
    (χ₁ χ₂ : G →* Multiplicative (ZMod p)) : ∃ g : G, g ≠ 1 ∧ χ₁ g * χ₂ g = 1 := by
  obtain ⟨g, hg1, hg⟩ := exists_ne_one_mem_ker hp hG (χ₁ * χ₂)
  exact ⟨g, hg1, hg⟩

end Characters

end CFSG.RankThree.PartOne.KCOrthogonal
