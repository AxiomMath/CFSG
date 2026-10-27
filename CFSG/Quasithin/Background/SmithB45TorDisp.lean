module

public import CFSG.Quasithin.Background.SmithB45ExcOrbit
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X5bRank
public import Mathlib.Data.Int.Star

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.B45Tor

open Module CFSG.QuasithinUnique.Setup.Family CFSG.Quasithin.B45Exc

section Blocks

variable {p : ℕ} [hp : Fact p.Prime] {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  {ρ : ZMod p × ZMod p → (E ≃ₗ[ZMod 2] E)}

theorem odd_card_zmod (hp2 : p ≠ 2) : Odd (Fintype.card (ZMod p)) := by
  rw [ZMod.card]
  exact hp.out.odd_of_ne_two hp2

theorem zmod_exists_natCast (k : ZMod p) : ∃ n : ℕ, (n : ZMod p) = k :=
  ⟨k.val, ZMod.natCast_zmod_val k⟩

theorem pow_prime_eq_one (h : IsVAct ρ) (w : ZMod p × ZMod p) : ρ w ^ p = 1 := by
  have hw : p • w = 0 := by
    ext <;> simp [nsmul_eq_mul]
  rw [← map_nsmul_eq_pow h, hw, h.map_zero]

theorem apply_mem_block (h : IsVAct ρ) (w u : ZMod p × ZMod p) {x : E}
    (hx : x ∈ LinearMap.range (lineProj ρ u)) : ρ w x ∈ LinearMap.range (lineProj ρ u) := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨ρ w y, ?_⟩
  have := LinearMap.congr_fun (opE_mul_lineProj_comm h w u) y
  simpa [Module.End.mul_apply, opE] using this.symm

theorem block_le_range_sub1 [Module.Finite (ZMod 2) E] (h : IsVAct ρ) (hp2 : p ≠ 2)
    {u w : ZMod p × ZMod p} (hd : det2 u w ≠ 0) :
    LinearMap.range (lineProj ρ u) ≤ LinearMap.range (sub1 (ρ w)) := by
  set M := LinearMap.range (lineProj ρ u) with hM
  have hTM : ∀ x ∈ M, sub1 (ρ w) x ∈ M := fun x hx => by
    rw [sub1_apply]
    exact M.sub_mem (apply_mem_block h w u hx) hx
  have hinj : Function.Injective ((sub1 (ρ w)).restrict hTM) := by
    intro a b hab
    have h0 : sub1 (ρ w) ((a : E) - b) = 0 := by
      have := congrArg Subtype.val hab
      simp only [LinearMap.coe_restrict_apply] at this
      rw [map_sub, this, sub_self]
    have h1 : ρ w ((a : E) - b) = (a : E) - b := by
      rw [sub1_apply, sub_eq_zero] at h0
      exact h0
    have h2 : (a : E) - b = 0 :=
      fpf_of_mem_range h (odd_card_zmod hp2) hd zmod_exists_natCast (M.sub_mem a.2 b.2) h1
    exact Subtype.ext (sub_eq_zero.1 h2)
  have hsurj := LinearMap.injective_iff_surjective.1 hinj
  intro x hx
  obtain ⟨y, hy⟩ := hsurj ⟨x, hx⟩
  exact ⟨y, congrArg Subtype.val hy⟩

theorem orderOf_two_dvd_finrank_block [Module.Finite (ZMod 2) E] (h : IsVAct ρ) (hp2 : p ≠ 2)
    {u w : ZMod p × ZMod p} (hd : det2 u w ≠ 0) :
    orderOf (2 : ZMod p) ∣ finrank (ZMod 2) (LinearMap.range (lineProj ρ u)) := by
  set M := LinearMap.range (lineProj ρ u) with hM
  have hvM : ∀ x ∈ M, ρ w x ∈ M := fun x hx => apply_mem_block h w u hx
  set T := restrictEquiv (ρ w) M hvM with hT
  have hTp : T ^ p = 1 := by
    ext v
    rw [restrictEquiv_pow_apply, pow_prime_eq_one h]
    rfl
  have hdvd := orderOf_two_dvd_finrank_range_sub1 (E := M) hp2 hTp
  have hfull : LinearMap.range (sub1 T) = ⊤ := by
    rw [LinearMap.range_eq_top]
    apply LinearMap.injective_iff_surjective.1
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro v hv
    rw [LinearMap.mem_ker, sub1_apply, sub_eq_zero] at hv
    rw [Submodule.mem_bot]
    refine Subtype.ext ?_
    exact fpf_of_mem_range h (odd_card_zmod hp2) hd zmod_exists_natCast v.2
      (congrArg Subtype.val hv)
  rw [hfull, finrank_top] at hdvd
  exact hdvd

theorem inv_comm_lineProj {s : E ≃ₗ[ZMod 2] E} (hs : s * s = 1)
    (hsρ : ∀ x, s * ρ x * s = ρ (-x)) (u : ZMod p × ZMod p) :
    (s : Module.End (ZMod 2) E) * lineProj ρ u = lineProj ρ u * (s : Module.End (ZMod 2) E) := by
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
  unfold lineProj lineSum fullSum
  rw [mul_add, add_mul, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
  congr 1
  · simp_rw [hsop]
    calc ∑ k : ZMod p, opE ρ (-(k • u)) * (s : Module.End (ZMod 2) E)
        = ∑ k : ZMod p, (fun k : ZMod p => opE ρ (k • u) * (s : Module.End (ZMod 2) E)) (-k) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          simp only [neg_smul]
      _ = ∑ k : ZMod p, opE ρ (k • u) * (s : Module.End (ZMod 2) E) :=
          Equiv.sum_comp (Equiv.neg (ZMod p))
            (fun k : ZMod p => opE ρ (k • u) * (s : Module.End (ZMod 2) E))
  · simp_rw [hsop]
    exact Equiv.sum_comp (Equiv.neg (ZMod p × ZMod p))
      (fun x : ZMod p × ZMod p => opE ρ x * (s : Module.End (ZMod 2) E))

theorem finrank_block_eq_two_mul [Module.Finite (ZMod 2) E] (h : IsVAct ρ) (hp2 : p ≠ 2)
    {s : E ≃ₗ[ZMod 2] E} (hs : s * s = 1) (hsρ : ∀ x, s * ρ x * s = ρ (-x))
    {u w : ZMod p × ZMod p} (hd : det2 u w ≠ 0) :
    finrank (ZMod 2) (LinearMap.range (lineProj ρ u)) =
      2 * finrank (ZMod 2) ((LinearMap.range (lineProj ρ u)).map (sub1 s)) := by
  set M := LinearMap.range (lineProj ρ u) with hM
  have hsv : s * ρ w * s = (ρ w)⁻¹ := by rw [hsρ, map_neg_eq_inv h]
  have hsM : ∀ x ∈ M, s x ∈ M := by
    rintro _ ⟨y, rfl⟩
    refine ⟨s y, ?_⟩
    have := LinearMap.congr_fun (inv_comm_lineProj hs hsρ u) y
    simpa [Module.End.mul_apply] using this.symm
  exact finrank_half M hs hsv (hp.out.odd_of_ne_two hp2) (pow_prime_eq_one h w) hsM
    (fun x hx => apply_mem_block h w u hx)
    (fun x hx hwx => fpf_of_mem_range h (odd_card_zmod hp2) hd zmod_exists_natCast hx hwx)

theorem sum_block_le_of_inverts [Module.Finite (ZMod 2) E] (h : IsVAct ρ) (hp2 : p ≠ 2)
    {s : E ≃ₗ[ZMod 2] E} (hs : s * s = 1) (hsρ : ∀ x, s * ρ x * s = ρ (-x))
    (U : Finset (ZMod p × ZMod p)) (hU : ∀ u ∈ U, ∀ v ∈ U, u ≠ v → det2 u v ≠ 0) :
    ∑ u ∈ U, finrank (ZMod 2) ((LinearMap.range (lineProj ρ u)).map (sub1 s)) ≤
      finrank (ZMod 2) (LinearMap.range (sub1 s)) := by
  classical
  exact sum_le_finrank_range_sub1 s U (fun u => lineProj ρ u)
    (fun u _ => lineProj_mul_self h (odd_card_zmod hp2) u)
    (fun u hu v hv huv => lineProj_mul_of_indep h (odd_card_zmod hp2) (hU u hu v hv huv))
    (fun u _ => inv_comm_lineProj hs hsρ u) _ (fun _ _ => le_rfl)

theorem sum_block_le_of_det [Module.Finite (ZMod 2) E] (h : IsVAct ρ) (hp2 : p ≠ 2)
    (w : ZMod p × ZMod p) (U : Finset (ZMod p × ZMod p))
    (hU : ∀ u ∈ U, ∀ v ∈ U, u ≠ v → det2 u v ≠ 0) (hUw : ∀ u ∈ U, det2 u w ≠ 0) :
    ∑ u ∈ U, finrank (ZMod 2) (LinearMap.range (lineProj ρ u)) ≤
      finrank (ZMod 2) (LinearMap.range (sub1 (ρ w))) := by
  classical
  have hodd := odd_card_zmod hp2
  have h1 := finrank_biSup_eq_sum U (fun u => lineProj ρ u)
    (fun u _ => lineProj_mul_self h hodd u)
    (fun u hu v hv huv => lineProj_mul_of_indep h hodd (hU u hu v hv huv))
    (fun u => LinearMap.range (lineProj ρ u)) (fun u _ => le_rfl)
  rw [← h1]
  exact Submodule.finrank_mono (iSup₂_le fun u hu => block_le_range_sub1 h hp2 (hUw u hu))

end Blocks

section Param

variable {G : Type*} [Group G] {p : ℕ} [hp : Fact p.Prime]

theorem pow_val_add {r : G} (hr : r ^ p = 1) (a b : ZMod p) :
    r ^ (a + b).val = r ^ a.val * r ^ b.val := by
  rw [ZMod.val_add, ← pow_add]
  conv_rhs => rw [← Nat.div_add_mod (a.val + b.val) p, pow_add, pow_mul, hr, one_pow, one_mul]

theorem pow_val_mul {r : G} (hr : r ^ p = 1) (a b : ZMod p) :
    r ^ (a * b).val = (r ^ b.val) ^ a.val := by
  rw [ZMod.val_mul, ← pow_mul, mul_comm b.val]
  conv_rhs => rw [← Nat.div_add_mod (a.val * b.val) p, pow_add, pow_mul, hr, one_pow, one_mul]

theorem eq_zero_of_pow_val_eq_one {r : G} (hr : r ^ p = 1) (hr1 : r ≠ 1) {a : ZMod p}
    (ha : r ^ a.val = 1) : a = 0 := by
  have hord : orderOf r = p := orderOf_eq_prime hr hr1
  have hdvd : orderOf r ∣ a.val := orderOf_dvd_of_pow_eq_one ha
  rw [hord] at hdvd
  rw [← ZMod.natCast_zmod_val a, ZMod.natCast_eq_zero_iff]
  exact hdvd

theorem exists_param (R : Subgroup G) (hRc : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a)
    (hRp : ∀ r ∈ R, r ^ p = 1) (hRcard : Nat.card R = p ^ 2) :
    ∃ φ : ZMod p × ZMod p → G, (∀ x y, φ (x + y) = φ x * φ y) ∧ Function.Injective φ ∧
      (∀ x, φ x ∈ R) ∧ ∀ r ∈ R, ∃ x, φ x = r := by
  classical
  have hp1 := hp.out.one_lt
  have : Finite R := Nat.finite_of_card_ne_zero (by rw [hRcard]; positivity)
  obtain ⟨r₁, hr₁R, hr₁1⟩ : ∃ r₁ ∈ R, r₁ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : R = ⊥ := (Subgroup.eq_bot_iff_forall R).2 hcon
    rw [hbot, Subgroup.card_bot] at hRcard
    have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp1
    omega
  have hr₁p := hRp r₁ hr₁R
  have hord₁ : orderOf r₁ = p := orderOf_eq_prime hr₁p hr₁1
  have : Finite (Subgroup.zpowers r₁) :=
    Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hord₁]; exact hp.out.ne_zero)
  obtain ⟨r₂, hr₂R, hr₂Z⟩ : ∃ r₂ ∈ R, r₂ ∉ Subgroup.zpowers r₁ := by
    by_contra hcon
    push Not at hcon
    have hle : R ≤ Subgroup.zpowers r₁ := hcon
    have h1 := Subgroup.card_le_of_le hle
    rw [hRcard, Nat.card_zpowers, hord₁] at h1
    have : p < p ^ 2 := by nlinarith
    omega
  have hr₂p := hRp r₂ hr₂R
  have hc : r₁ * r₂ = r₂ * r₁ := hRc r₁ hr₁R r₂ hr₂R
  have hcpow : ∀ m n : ℕ, r₁ ^ m * r₂ ^ n = r₂ ^ n * r₁ ^ m := fun m n =>
    ((Commute.pow_pow (show Commute r₁ r₂ from hc) m n)).eq
  set φ : ZMod p × ZMod p → G := fun x => r₁ ^ x.1.val * r₂ ^ x.2.val with hφ
  have hadd : ∀ x y, φ (x + y) = φ x * φ y := by
    intro x y
    simp only [hφ, Prod.fst_add, Prod.snd_add, pow_val_add hr₁p, pow_val_add hr₂p]
    calc r₁ ^ x.1.val * r₁ ^ y.1.val * (r₂ ^ x.2.val * r₂ ^ y.2.val) =
        r₁ ^ x.1.val * (r₁ ^ y.1.val * r₂ ^ x.2.val) * r₂ ^ y.2.val := by group
      _ = r₁ ^ x.1.val * (r₂ ^ x.2.val * r₁ ^ y.1.val) * r₂ ^ y.2.val := by rw [hcpow]
      _ = _ := by group
  have hker : ∀ x, φ x = 1 → x = 0 := by
    rintro ⟨a, b⟩ hx
    simp only [hφ] at hx
    have hb : b = 0 := by
      by_contra hb
      apply hr₂Z
      have h1 : r₂ ^ b.val ∈ Subgroup.zpowers r₁ := by
        have : r₂ ^ b.val = (r₁ ^ a.val)⁻¹ := eq_inv_of_mul_eq_one_right hx
        rw [this]
        exact inv_mem (Subgroup.pow_mem _ (Subgroup.mem_zpowers r₁) _)
      have h2 : r₂ ^ (b⁻¹ * b).val ∈ Subgroup.zpowers r₁ := by
        rw [pow_val_mul hr₂p]
        exact Subgroup.pow_mem _ h1 _
      rwa [inv_mul_cancel₀ hb, ZMod.val_one, pow_one] at h2
    subst hb
    simp only [ZMod.val_zero, pow_zero, mul_one] at hx
    rw [eq_zero_of_pow_val_eq_one hr₁p hr₁1 hx]
    rfl
  have hneg : ∀ x, φ (-x) = (φ x)⁻¹ := fun x =>
    eq_inv_of_mul_eq_one_left (by rw [← hadd, neg_add_cancel]; simp [hφ])
  have hinj : Function.Injective φ := by
    intro x y hxy
    have h1 : φ (x - y) = 1 := by
      rw [sub_eq_add_neg, hadd, hneg, hxy, mul_inv_cancel]
    exact sub_eq_zero.1 (hker _ h1)
  have hmem : ∀ x, φ x ∈ R := fun x =>
    mul_mem (Subgroup.pow_mem _ hr₁R _) (Subgroup.pow_mem _ hr₂R _)
  refine ⟨φ, hadd, hinj, hmem, ?_⟩
  have : Fintype R := Fintype.ofFinite R
  let f : ZMod p × ZMod p → R := fun x => ⟨φ x, hmem x⟩
  have hf : Function.Injective f := fun x y h => hinj (congrArg Subtype.val h)
  have hcardR : Fintype.card R = p ^ 2 := by rw [← Nat.card_eq_fintype_card, hRcard]
  have hbij : Function.Bijective f := (Fintype.bijective_iff_injective_and_card f).2
    ⟨hf, by rw [Fintype.card_prod, ZMod.card, hcardR, sq]⟩
  intro r hr
  obtain ⟨x, hx⟩ := hbij.2 ⟨r, hr⟩
  exact ⟨x, congrArg Subtype.val hx⟩

variable {φ : ZMod p × ZMod p → G} (hadd : ∀ x y, φ (x + y) = φ x * φ y)
include hadd

theorem param_zero : φ 0 = 1 := by
  have h := hadd 0 0
  rw [add_zero] at h
  exact (mul_eq_left.1 h.symm)

theorem param_neg (x : ZMod p × ZMod p) : φ (-x) = (φ x)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← hadd, neg_add_cancel, param_zero hadd])

theorem param_nsmul (n : ℕ) (x : ZMod p × ZMod p) : φ (n • x) = φ x ^ n := by
  induction n with
  | zero => rw [zero_smul, param_zero hadd, pow_zero]
  | succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]

theorem param_smul (c : ZMod p) (x : ZMod p × ZMod p) : φ (c • x) = φ x ^ c.val := by
  rw [← param_nsmul hadd]
  congr 1
  conv_lhs => rw [← ZMod.natCast_zmod_val c]
  exact Nat.cast_smul_eq_nsmul (ZMod p) c.val x

theorem param_smul_mem_zpowers (c : ZMod p) (u : ZMod p × ZMod p) :
    φ (c • u) ∈ Subgroup.zpowers (φ u) := by
  rw [param_smul hadd]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _

omit hadd in
theorem exists_smul_of_det2_eq_zero {u v : ZMod p × ZMod p} (hu : u ≠ 0) (hd : det2 u v = 0) :
    ∃ c : ZMod p, v = c • u := by
  unfold det2 at hd
  by_cases h1 : u.1 = 0
  · have h2 : u.2 ≠ 0 := fun h2 => hu (Prod.ext h1 h2)
    have hv1 : v.1 = 0 := by
      rw [h1, zero_mul, zero_sub, neg_eq_zero] at hd
      exact (mul_eq_zero.1 hd).resolve_left h2
    refine ⟨v.2 * u.2⁻¹, Prod.ext ?_ ?_⟩
    · simp [h1, hv1]
    · simp [mul_assoc, inv_mul_cancel₀ h2]
  · refine ⟨v.1 * u.1⁻¹, Prod.ext ?_ ?_⟩
    · simp [mul_assoc, inv_mul_cancel₀ h1]
    · simp only [Prod.smul_snd, smul_eq_mul]
      have e : u.2 * v.1 = u.1 * v.2 := (sub_eq_zero.1 hd).symm
      calc v.2 = u.1⁻¹ * (u.1 * v.2) := by rw [← mul_assoc, inv_mul_cancel₀ h1, one_mul]
        _ = v.1 * u.1⁻¹ * u.2 := by rw [← e]; ring

omit hadd in
theorem det2_eq_zero_of_det2_eq_zero {u v w : ZMod p × ZMod p} (hw : w ≠ 0)
    (hu : det2 u w = 0) (hv : det2 v w = 0) : det2 u v = 0 := by
  unfold det2 at *
  have e1 : w.1 * (u.1 * v.2 - u.2 * v.1) = 0 := by linear_combination v.1 * hu - u.1 * hv
  have e2 : w.2 * (u.1 * v.2 - u.2 * v.1) = 0 := by linear_combination v.2 * hu - u.2 * hv
  by_cases h1 : w.1 = 0
  · have h2 : w.2 ≠ 0 := fun h2 => hw (Prod.ext h1 h2)
    exact (mul_eq_zero.1 e2).resolve_left h2
  · exact (mul_eq_zero.1 e1).resolve_left h1

theorem exists_coord_conj (hinj : Function.Injective φ) {R : Subgroup G} (hmem : ∀ x, φ x ∈ R)
    (hsurj : ∀ r ∈ R, ∃ x, φ x = r) {g : G} (hg : ∀ r ∈ R, g * r * g⁻¹ ∈ R) :
    ∃ γ : ZMod p × ZMod p → ZMod p × ZMod p, Function.Bijective γ ∧
      (∀ x y, γ (x + y) = γ x + γ y) ∧ (∀ (c : ZMod p) (x : ZMod p × ZMod p), γ (c • x) = c • γ x) ∧
      ∀ x, g * φ x * g⁻¹ = φ (γ x) := by
  choose γ hγ using fun x => hsurj _ (hg _ (hmem x))
  have hγadd : ∀ x y, γ (x + y) = γ x + γ y := by
    intro x y
    apply hinj
    rw [hγ, hadd, hadd, hγ, hγ]
    group
  have hγns : ∀ (n : ℕ) (x : ZMod p × ZMod p), γ (n • x) = n • γ x := by
    intro n x
    induction n with
    | zero =>
      apply hinj
      rw [zero_smul, zero_smul, hγ, param_zero hadd]
      group
    | succ n ih => rw [succ_nsmul, hγadd, ih, succ_nsmul]
  have hγinj : Function.Injective γ := by
    intro x y hxy
    apply hinj
    have h1 : g * φ x * g⁻¹ = g * φ y * g⁻¹ := by rw [← hγ, ← hγ, hxy]
    simpa using h1
  refine ⟨γ, Finite.injective_iff_bijective.1 hγinj, hγadd, fun c x => ?_, fun x => (hγ x).symm⟩
  have e : ∀ y : ZMod p × ZMod p, c • y = c.val • y := fun y => by
    conv_lhs => rw [← ZMod.natCast_zmod_val c]
    exact Nat.cast_smul_eq_nsmul (ZMod p) c.val y
  rw [e, e, hγns]

end Param

section Main

variable {G : Type*} [Group G] {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  [Module.Finite (ZMod 2) E] (ψ : G →* (E ≃ₗ[ZMod 2] E)) {p : ℕ} [hp : Fact p.Prime]

theorem exists_blocks (hp2 : p ≠ 2) (R : Subgroup G) (hRc : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a)
    (hRp : ∀ r ∈ R, r ^ p = 1) (hRcard : Nat.card R = p ^ 2) (hψ : ∀ r ∈ R, ψ r = 1 → r = 1)
    (N : Set G) (hN : ∀ g ∈ N, ∀ r ∈ R, g * r * g⁻¹ ∈ R) {k : ℕ}
    (horb : ∀ K : Subgroup G, K ≤ R → Nat.card K = p → ∃ S : Finset (Subgroup G),
      k ≤ S.card ∧ ∀ K' ∈ S, ∃ g ∈ N, K' = K.map (MulAut.conj g).toMonoidHom) :
    ∃ (φ : ZMod p × ZMod p → G) (U : Finset (ZMod p × ZMod p)) (n₀ : ℕ),
      (∀ x y, φ (x + y) = φ x * φ y) ∧ Function.Injective φ ∧ (∀ x, φ x ∈ R) ∧
      (∀ r ∈ R, ∃ x, φ x = r) ∧ IsVAct (fun x => ψ (φ x)) ∧ k ≤ U.card ∧
      (∀ u ∈ U, u ≠ 0) ∧ (∀ u ∈ U, ∀ v ∈ U, u ≠ v → det2 u v ≠ 0) ∧ 0 < n₀ ∧
      ∀ u ∈ U, finrank (ZMod 2) (LinearMap.range (lineProj (fun x => ψ (φ x)) u)) = n₀ := by
  classical
  obtain ⟨φ, hadd, hinj, hmem, hsurj⟩ := exists_param R hRc hRp hRcard
  set ρ : ZMod p × ZMod p → (E ≃ₗ[ZMod 2] E) := fun x => ψ (φ x) with hρ
  have hV : IsVAct ρ := ⟨by simp [hρ, param_zero hadd], fun x y => by simp [hρ, hadd]⟩
  have hodd := odd_card_zmod (p := p) hp2
  have hfaith : ∀ x, ρ x = 1 → x = 0 := by
    intro x hx
    have h1 : φ x = 1 := hψ _ (hmem x) hx
    exact hinj (h1.trans (param_zero hadd).symm)
  have hγ : ∀ g ∈ N, ∃ γ : ZMod p × ZMod p → ZMod p × ZMod p, Function.Bijective γ ∧
      (∀ (c : ZMod p) (x : ZMod p × ZMod p), γ (c • x) = c • γ x) ∧
      (∀ x, g * φ x * g⁻¹ = φ (γ x)) := by
    intro g hg
    obtain ⟨γ, hb, -, hk, hc⟩ := exists_coord_conj hadd hinj hmem hsurj (hN g hg)
    exact ⟨γ, hb, hk, hc⟩
  obtain ⟨o, ho⟩ := exists_lineProj_ne hV hodd hfaith
  set u₀ := lineRep o with hu₀
  have hu₀0 : u₀ ≠ 0 := lineRep_ne_zero o
  set n₀ := finrank (ZMod 2) (LinearMap.range (lineProj ρ u₀)) with hn₀
  have hn₀pos : 0 < n₀ := by
    rw [hn₀, Nat.pos_iff_ne_zero, Ne, Submodule.finrank_eq_zero, LinearMap.range_eq_bot]
    exact ho
  set K₀ := Subgroup.zpowers (φ u₀) with hK₀
  have hφu₀1 : φ u₀ ≠ 1 := fun h => hu₀0 (hinj (h.trans (param_zero hadd).symm))
  have hK₀R : K₀ ≤ R := (Subgroup.zpowers_le).2 (hmem u₀)
  have hφp : ∀ x, φ x ^ p = 1 := fun x => hRp _ (hmem x)
  have hcardline : ∀ x, x ≠ 0 → Nat.card (Subgroup.zpowers (φ x)) = p := by
    intro x hx
    have hx1 : φ x ≠ 1 := fun h => hx (hinj (h.trans (param_zero hadd).symm))
    rw [Nat.card_zpowers, orderOf_eq_prime (hφp x) hx1]
  obtain ⟨S, hSk, hS⟩ := horb K₀ hK₀R (hcardline u₀ hu₀0)
  choose g hgN hgK using hS
  choose γ hγb hγk hγc using hγ
  set vec : S → ZMod p × ZMod p := fun K' => γ (g K' K'.2) (hgN K' K'.2) u₀ with hvec
  have hvec_spec : ∀ K' : S, (K' : Subgroup G) = Subgroup.zpowers (φ (vec K')) ∧
      finrank (ZMod 2) (LinearMap.range (lineProj ρ (vec K'))) = n₀ ∧ vec K' ≠ 0 := by
    intro K'
    have hb := hγb (g K' K'.2) (hgN K' K'.2)
    have hk := hγk (g K' K'.2) (hgN K' K'.2)
    have hc := hγc (g K' K'.2) (hgN K' K'.2)
    refine ⟨?_, ?_, ?_⟩
    · calc (K' : Subgroup G) = K₀.map (MulAut.conj (g K' K'.2)).toMonoidHom := hgK K' K'.2
        _ = Subgroup.zpowers (g K' K'.2 * φ u₀ * (g K' K'.2)⁻¹) := by
          rw [hK₀, MonoidHom.map_zpowers]
          rfl
        _ = Subgroup.zpowers (φ (vec K')) := by rw [hc u₀]
    · have hconj := lineProj_conj (g := ψ (g K' K'.2)) (ρ := ρ) hb hk (fun x => by
        simp only [hρ, ← map_inv, ← map_mul, hc]) u₀
      change finrank (ZMod 2) (LinearMap.range (lineProj ρ (γ (g K' K'.2) (hgN K' K'.2) u₀))) = n₀
      rw [← hconj, hn₀]
      have hrange : LinearMap.range ((ψ (g K' K'.2) : E →ₗ[ZMod 2] E) * lineProj ρ u₀ *
          (((ψ (g K' K'.2))⁻¹ : E ≃ₗ[ZMod 2] E) : E →ₗ[ZMod 2] E)) =
          (LinearMap.range (lineProj ρ u₀)).map (ψ (g K' K'.2) : E →ₗ[ZMod 2] E) := by
        rw [Module.End.mul_eq_comp, LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _),
          Module.End.mul_eq_comp, LinearMap.range_comp]
      rw [hrange]
      exact LinearEquiv.finrank_map_eq _ _
    · intro h0
      apply hu₀0
      have h1 : γ (g K' K'.2) (hgN K' K'.2) u₀ = γ (g K' K'.2) (hgN K' K'.2) 0 := by
        change vec K' = _
        rw [h0]
        apply hinj
        rw [← hc, param_zero hadd]
        group
      exact hb.1 h1
  have hindep : ∀ K₁ K₂ : S, K₁ ≠ K₂ → det2 (vec K₁) (vec K₂) ≠ 0 := by
    intro K₁ K₂ hne hd
    obtain ⟨e₁, -, n₁⟩ := hvec_spec K₁
    obtain ⟨e₂, -, n₂⟩ := hvec_spec K₂
    obtain ⟨c, hc⟩ := exists_smul_of_det2_eq_zero n₁ hd
    apply hne
    have hle : (K₂ : Subgroup G) ≤ K₁ := by
      rw [e₁, e₂, Subgroup.zpowers_le, hc]
      exact param_smul_mem_zpowers hadd c _
    have : Finite (K₁ : Subgroup G) := Nat.finite_of_card_ne_zero (by
      rw [e₁, hcardline _ n₁]; exact hp.out.ne_zero)
    refine Subtype.ext (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    rw [e₁, e₂, hcardline _ n₁, hcardline _ n₂]
  have hvecinj : Function.Injective vec := by
    intro K₁ K₂ he
    by_contra hne
    apply hindep K₁ K₂ hne
    rw [he]
    unfold det2
    ring
  refine ⟨φ, S.attach.image vec, n₀, hadd, hinj, hmem, hsurj, hV, ?_, ?_, ?_, hn₀pos, ?_⟩
  · rw [Finset.card_image_of_injective _ hvecinj, Finset.card_attach]
    exact hSk
  · intro u hu
    obtain ⟨K', -, rfl⟩ := Finset.mem_image.1 hu
    exact (hvec_spec K').2.2
  · intro u hu v hv huv
    obtain ⟨K₁, -, rfl⟩ := Finset.mem_image.1 hu
    obtain ⟨K₂, -, rfl⟩ := Finset.mem_image.1 hv
    exact hindep K₁ K₂ fun h => huv (h ▸ rfl)
  · intro u hu
    obtain ⟨K', -, rfl⟩ := Finset.mem_image.1 hu
    exact (hvec_spec K').2.1

theorem le_finrank_of_inverts (hp2 : p ≠ 2) (R : Subgroup G)
    (hRc : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a) (hRp : ∀ r ∈ R, r ^ p = 1)
    (hRcard : Nat.card R = p ^ 2) (hψ : ∀ r ∈ R, ψ r = 1 → r = 1)
    (N : Set G) (hN : ∀ g ∈ N, ∀ r ∈ R, g * r * g⁻¹ ∈ R) {k : ℕ}
    (horb : ∀ K : Subgroup G, K ≤ R → Nat.card K = p → ∃ S : Finset (Subgroup G),
      k ≤ S.card ∧ ∀ K' ∈ S, ∃ g ∈ N, K' = K.map (MulAut.conj g).toMonoidHom)
    {y : G} (hy : y * y = 1) (hyR : ∀ r ∈ R, y * r * y⁻¹ = r⁻¹) {m : ℕ}
    (hm : ∀ n : ℕ, 0 < n → orderOf (2 : ZMod p) ∣ 2 * n → m ≤ n) :
    k * m ≤ finrank (ZMod 2) (LinearMap.range (sub1 (ψ y))) := by
  classical
  obtain ⟨φ, U, n₀, hadd, -, hmem, -, hV, hk, hU0, hUi, hn₀, hUn⟩ :=
    exists_blocks ψ hp2 R hRc hRp hRcard hψ N hN horb
  have hs : ψ y * ψ y = 1 := by rw [← map_mul, hy, map_one]
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have hsρ : ∀ x, ψ y * ψ (φ x) * ψ y = ψ (φ (-x)) := by
    intro x
    rw [← map_mul, ← map_mul, param_neg hadd, ← hyR _ (hmem x), hyi]
  have hsum := sum_block_le_of_inverts hV hp2 hs hsρ U hUi
  have hterm : ∀ u ∈ U, m ≤
      finrank (ZMod 2) ((LinearMap.range (lineProj (fun x => ψ (φ x)) u)).map (sub1 (ψ y))) := by
    intro u hu
    obtain ⟨w, hw⟩ := exists_det_ne u (hU0 u hu)
    have h2 := finrank_block_eq_two_mul hV hp2 hs hsρ hw
    have hd := orderOf_two_dvd_finrank_block hV hp2 hw
    rw [hUn u hu] at h2 hd
    refine hm _ ?_ (h2 ▸ hd)
    omega
  calc k * m ≤ U.card * m := Nat.mul_le_mul_right m hk
    _ = ∑ _u ∈ U, m := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ _ := Finset.sum_le_sum hterm
    _ ≤ _ := hsum

theorem le_finrank_of_mem (hp2 : p ≠ 2) (R : Subgroup G)
    (hRc : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a) (hRp : ∀ r ∈ R, r ^ p = 1)
    (hRcard : Nat.card R = p ^ 2) (hψ : ∀ r ∈ R, ψ r = 1 → r = 1)
    (N : Set G) (hN : ∀ g ∈ N, ∀ r ∈ R, g * r * g⁻¹ ∈ R) {k : ℕ}
    (horb : ∀ K : Subgroup G, K ≤ R → Nat.card K = p → ∃ S : Finset (Subgroup G),
      k ≤ S.card ∧ ∀ K' ∈ S, ∃ g ∈ N, K' = K.map (MulAut.conj g).toMonoidHom)
    {r : G} (hr : r ∈ R) (hr1 : r ≠ 1) :
    (k - 1) * orderOf (2 : ZMod p) ≤ finrank (ZMod 2) (LinearMap.range (sub1 (ψ r))) := by
  classical
  obtain ⟨φ, U, n₀, hadd, -, -, hsurj, hV, hk, hU0, hUi, hn₀, hUn⟩ :=
    exists_blocks ψ hp2 R hRc hRp hRcard hψ N hN horb
  obtain ⟨w, rfl⟩ := hsurj r hr
  have hw0 : w ≠ 0 := fun h => hr1 (by rw [h, param_zero hadd])
  set U' := U.filter fun u => det2 u w ≠ 0 with hU'
  have hcard : U.card ≤ U'.card + 1 := by
    have hsub : (U.filter fun u => det2 u w = 0).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro u hu v hv
      rw [Finset.mem_filter] at hu hv
      by_contra huv
      exact hUi u hu.1 v hv.1 huv (det2_eq_zero_of_det2_eq_zero hw0 hu.2 hv.2)
    have := Finset.card_filter_add_card_filter_not (s := U) (fun u => det2 u w ≠ 0)
    simp only [not_not] at this
    rw [← hU'] at this
    omega
  have hsum := sum_block_le_of_det hV hp2 w U' (fun u hu v hv huv =>
    hUi u (Finset.mem_filter.1 hu).1 v (Finset.mem_filter.1 hv).1 huv)
    (fun u hu => (Finset.mem_filter.1 hu).2)
  have hterm : ∀ u ∈ U', orderOf (2 : ZMod p) ≤
      finrank (ZMod 2) (LinearMap.range (lineProj (fun x => ψ (φ x)) u)) := by
    intro u hu
    have hu' := Finset.mem_filter.1 hu
    have hd := orderOf_two_dvd_finrank_block hV hp2 hu'.2
    rw [hUn u hu'.1] at hd ⊢
    exact Nat.le_of_dvd hn₀ hd
  calc (k - 1) * orderOf (2 : ZMod p) ≤ U'.card * orderOf (2 : ZMod p) :=
        Nat.mul_le_mul_right _ (by omega)
    _ = ∑ _u ∈ U', orderOf (2 : ZMod p) := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ _ := Finset.sum_le_sum hterm
    _ ≤ _ := hsum

end Main

section Group

variable {V : Type*} [CommGroup V]

noncomputable abbrev zmodTwoModule (hV : ∀ v : V, v * v = 1) :
    Module (ZMod 2) (Additive V) :=
  AddCommGroup.zmodModule (n := 2) fun x => by
    rw [two_nsmul]
    exact hV (Additive.toMul x)

variable [Module (ZMod 2) (Additive V)]

@[expose] noncomputable def linRep : MulAut V →* (Additive V ≃ₗ[ZMod 2] Additive V) where
  toFun x := (MulEquiv.toAdditive x).toLinearEquiv fun c v =>
    ZMod.map_smul (MulEquiv.toAdditive x) c v
  map_one' := by
    ext v
    rfl
  map_mul' x y := by
    ext v
    rfl

theorem linRep_apply (x : MulAut V) (v : V) :
    linRep x (Additive.ofMul v) = Additive.ofMul (x v) := rfl

theorem linRep_eq_one {x : MulAut V} (h : linRep x = 1) : x = 1 := by
  ext v
  have := congrArg (fun f : Additive V ≃ₗ[ZMod 2] Additive V => f (Additive.ofMul v)) h
  exact congrArg Additive.toMul this

theorem index_fixV_zpowers [Finite V] (x : MulAut V) :
    (fixV (Subgroup.zpowers x)).index =
      2 ^ finrank (ZMod 2) (LinearMap.range (sub1 (linRep x))) := by
  have : Module.Finite (ZMod 2) (Additive V) := Module.Finite.of_finite
  let δ : V →* V :=
    { toFun := fun v => x v * v⁻¹
      map_one' := by simp
      map_mul' := fun a b => by
        rw [map_mul, mul_inv]
        exact mul_mul_mul_comm _ _ _ _ }
  have hker : δ.ker = fixV (Subgroup.zpowers x) := by
    ext v
    rw [MonoidHom.mem_ker, CFSG.QuasithinUnique.Setup.X5.mem_fixV_zpowers]
    change x v * v⁻¹ = 1 ↔ x v = v
    exact mul_inv_eq_one
  have hrange : Nat.card δ.range = Nat.card (LinearMap.range (sub1 (linRep x))) := by
    refine Nat.card_congr
      { toFun := fun w => ⟨Additive.ofMul (w : V), ?_⟩
        invFun := fun w => ⟨Additive.toMul (w : Additive V), ?_⟩
        left_inv := fun w => rfl
        right_inv := fun w => rfl }
    · obtain ⟨v, hv⟩ := w.2
      refine ⟨Additive.ofMul v, ?_⟩
      rw [sub1_apply, linRep_apply, ← hv, sub_eq_add_neg, ← ofMul_inv, ← ofMul_mul]
      rfl
    · obtain ⟨v, hv⟩ := w.2
      refine ⟨Additive.toMul v, ?_⟩
      rw [← hv, sub1_apply, toMul_sub, div_eq_mul_inv]
      rfl
  rw [← hker, Subgroup.index_ker, hrange, Module.natCard_eq_pow_finrank (K := ZMod 2),
    Nat.card_zmod]

omit [Module (ZMod 2) (Additive V)] in
theorem index_fixV_sq_le_card [Finite V] (hV : ∀ v : V, v * v = 1) {x : MulAut V}
    (hx : x * x = 1) : (fixV (Subgroup.zpowers x)).index ^ 2 ≤ Nat.card V := by
  let δ : V →* V :=
    { toFun := fun v => x v * v⁻¹
      map_one' := by simp
      map_mul' := fun a b => by
        rw [map_mul, mul_inv]
        exact mul_mul_mul_comm _ _ _ _ }
  have hker : δ.ker = fixV (Subgroup.zpowers x) := by
    ext v
    rw [MonoidHom.mem_ker, CFSG.QuasithinUnique.Setup.X5.mem_fixV_zpowers]
    change x v * v⁻¹ = 1 ↔ x v = v
    exact mul_inv_eq_one
  have hxx : ∀ v, x (x v) = v := fun v => by rw [← MulAut.mul_apply, hx, MulAut.one_apply]
  have hle : δ.range ≤ fixV (Subgroup.zpowers x) := by
    rintro _ ⟨v, rfl⟩
    rw [CFSG.QuasithinUnique.Setup.X5.mem_fixV_zpowers]
    change x (x v * v⁻¹) = x v * v⁻¹
    have hinv : ∀ w : V, w⁻¹ = w := fun w => inv_eq_of_mul_eq_one_right (hV w)
    rw [map_mul, map_inv, hxx, hinv (x v), hinv v, mul_comm]
  have h1 := Subgroup.card_le_of_le hle
  have h2 := (fixV (Subgroup.zpowers x)).card_mul_index
  rw [← hker, Subgroup.index_ker] at h2 ⊢
  rw [sq]
  calc Nat.card δ.range * Nat.card δ.range ≤ Nat.card δ.ker * Nat.card δ.range :=
        Nat.mul_le_mul_right _ (hker ▸ h1)
    _ = Nat.card V := by rw [h2]

end Group

section Displacement

variable {V : Type*} [CommGroup V] [Finite V] (hV : ∀ v : V, v * v = 1) {p : ℕ}
  [Fact p.Prime]
include hV

theorem two_pow_le_index_fixV_of_inverts (hp2 : p ≠ 2) (R : Subgroup (MulAut V))
    (hRc : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a) (hRp : ∀ r ∈ R, r ^ p = 1)
    (hRcard : Nat.card R = p ^ 2) (N : Set (MulAut V))
    (hN : ∀ g ∈ N, ∀ r ∈ R, g * r * g⁻¹ ∈ R) {k : ℕ}
    (horb : ∀ K : Subgroup (MulAut V), K ≤ R → Nat.card K = p →
      ∃ S : Finset (Subgroup (MulAut V)), k ≤ S.card ∧
        ∀ K' ∈ S, ∃ g ∈ N, K' = K.map (MulAut.conj g).toMonoidHom)
    {y : MulAut V} (hy : y * y = 1) (hyR : ∀ r ∈ R, y * r * y⁻¹ = r⁻¹) {m : ℕ}
    (hm : ∀ n : ℕ, 0 < n → orderOf (2 : ZMod p) ∣ 2 * n → m ≤ n) :
    2 ^ (k * m) ≤ (fixV (Subgroup.zpowers y)).index := by
  let _ := zmodTwoModule hV
  have : Module.Finite (ZMod 2) (Additive V) := Module.Finite.of_finite
  have hψ : ∀ r ∈ R, (linRep r : Additive V ≃ₗ[ZMod 2] Additive V) = 1 → r = 1 :=
    fun r _ h => linRep_eq_one h
  have h := le_finrank_of_inverts (linRep (V := V)) hp2 R hRc hRp hRcard hψ N hN horb hy hyR hm
  rw [index_fixV_zpowers]
  exact Nat.pow_le_pow_right (by norm_num) h

theorem two_pow_le_index_fixV_of_mem (hp2 : p ≠ 2) (R : Subgroup (MulAut V))
    (hRc : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a) (hRp : ∀ r ∈ R, r ^ p = 1)
    (hRcard : Nat.card R = p ^ 2) (N : Set (MulAut V))
    (hN : ∀ g ∈ N, ∀ r ∈ R, g * r * g⁻¹ ∈ R) {k : ℕ}
    (horb : ∀ K : Subgroup (MulAut V), K ≤ R → Nat.card K = p →
      ∃ S : Finset (Subgroup (MulAut V)), k ≤ S.card ∧
        ∀ K' ∈ S, ∃ g ∈ N, K' = K.map (MulAut.conj g).toMonoidHom)
    {r : MulAut V} (hr : r ∈ R) (hr1 : r ≠ 1) :
    2 ^ ((k - 1) * orderOf (2 : ZMod p)) ≤ (fixV (Subgroup.zpowers r)).index := by
  let _ := zmodTwoModule hV
  have : Module.Finite (ZMod 2) (Additive V) := Module.Finite.of_finite
  have hψ : ∀ r ∈ R, (linRep r : Additive V ≃ₗ[ZMod 2] Additive V) = 1 → r = 1 :=
    fun r _ h => linRep_eq_one h
  have h := le_finrank_of_mem (linRep (V := V)) hp2 R hRc hRp hRcard hψ N hN horb hr hr1
  rw [index_fixV_zpowers]
  exact Nat.pow_le_pow_right (by norm_num) h

end Displacement

end CFSG.Quasithin.B45Tor
