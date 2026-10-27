module

public import CFSG.Quasithin.Vol2.Ch11G2Q8OffQr

public section

namespace CFSG.Quasithin.Vol2.Ch11.G2Q8

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.KGNat Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {K : Type} [Field K]

section Trace

variable [Finite K] [Algebra (ZMod 2) K]

theorem exists_trace_mul_eq (φ : K →+ ZMod 2) :
    ∃ a : K, ∀ t, φ t = Algebra.trace (ZMod 2) K (a * t) := by
  refine ⟨((Algebra.traceForm (ZMod 2) K).toDual (traceForm_nondegenerate (ZMod 2) K)).symm
    (φ.toZModLinearMap 2), fun t => ?_⟩
  have h := LinearMap.BilinForm.apply_toDual_symm_apply (B := Algebra.traceForm (ZMod 2) K)
    (hB := traceForm_nondegenerate (ZMod 2) K) (φ.toZModLinearMap 2) t
  rw [Algebra.traceForm_apply] at h
  exact h.symm

theorem exists_trace_mul_ne_zero {a : K} (ha : a ≠ 0) :
    ∃ b : K, Algebra.trace (ZMod 2) K (a * b) ≠ 0 := by
  have htr := (traceForm_nondegenerate (ZMod 2) K).1 a
  simp_rw [Algebra.traceForm_apply] at htr
  by_contra! hf
  exact ha (htr hf)

theorem exists_trace_polarQ_eq (φ : (Ix3 → K) →+ ZMod 2) :
    ∃ u : Ix3 → K, ∀ y, φ y = Algebra.trace (ZMod 2) K (polarQ u y) := by
  classical
  choose a ha using fun i : Ix3 => exists_trace_mul_eq (φ.comp (AddMonoidHom.single _ i))
  refine ⟨q6 (a (.inr 0)) (a (.inr 1)) (a (.inr 2)) (a (.inl 0)) (a (.inl 1)) (a (.inl 2)),
    fun y => ?_⟩
  have hy : φ y = ∑ i, φ (Pi.single i (y i)) := by
    conv_lhs => rw [← Finset.univ_sum_single y]
    exact map_sum φ _ _
  have hi : ∀ i, φ (Pi.single i (y i)) = Algebra.trace (ZMod 2) K (a i * y i) := fun i =>
    ha i (y i)
  rw [hy, Finset.sum_congr rfl fun i _ => hi i, ← map_sum (Algebra.trace (ZMod 2) K)]
  congr 1
  simp only [Fintype.sum_sum_type, Fin.sum_univ_three, polarQ, q6_apply_inl0, q6_apply_inl1,
    q6_apply_inl2, q6_apply_inr0, q6_apply_inr1, q6_apply_inr2]
  ring

theorem eq_of_trace_polarQ {u u' : Ix3 → K}
    (h : ∀ y, Algebra.trace (ZMod 2) K (polarQ u y) = Algebra.trace (ZMod 2) K (polarQ u' y)) :
    u = u' := by
  rw [← sub_eq_zero]
  refine eq_zero_of_polarQ fun y => ?_
  by_contra hy
  obtain ⟨b, hb⟩ := exists_trace_mul_ne_zero hy
  apply hb
  have h1 := h (b • y)
  rw [polarQ_smul_right, polarQ_smul_right, ← sub_eq_zero, ← map_sub, ← mul_sub,
    ← polarQ_sub_left] at h1
  rwa [mul_comm] at h1

end Trace

theorem eq_one_of_forall_addChar {Z : Type*} [CommGroup Z] (hZ : ∀ z : Z, z ^ 2 = 1) {z : Z}
    (h : ∀ ζ : Additive Z →+ ZMod 2, ζ (Additive.ofMul z) = 0) : z = 1 := by
  let _ : Module (ZMod 2) (Additive Z) := AddCommGroup.zmodModule fun x => by
    change Additive.ofMul (Additive.toMul x ^ 2) = 0
    rw [hZ]
    rfl
  exact (Module.forall_dual_apply_eq_zero_iff (ZMod 2) (Additive.ofMul z)).mp
    fun φ => h φ.toAddMonoidHom

variable [CharP K 2]

theorem ell_mul_self (γ : ↥(cayleyGroup K)) (y : Ix3 → K) :
    (cgE γ (zI y)).1 * (cgE γ (zI y)).1 = normQ (g2Act γ y - y) + qr γ y := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h := normQ_g2Act γ y
  have hN := normQ_add y (g2Act γ y - y)
  rw [add_sub_cancel] at hN
  have hP : polarQ y (g2Act γ y - y) = qr γ y - polarQ y y := polarQ_sub_right _ _ _
  have hyy : polarQ y y = 0 := by
    simp only [polarQ]
    linear_combination (y (.inl 0) * y (.inr 0) + y (.inl 1) * y (.inr 1) +
      y (.inl 2) * y (.inr 2)) * h2
  rw [hN, hP, hyy, sub_zero] at h
  linear_combination h - (normQ (g2Act γ y - y) + qr γ y) * h2

section Cocycle

variable {W : Type*} [CommGroup W]

@[expose] def kapW (ρ : ↥(cayleyGroup K) →* MulAut W) (σ : Multiplicative (Ix3 → K) →* W)
    (γ : ↥(cayleyGroup K)) (x : Ix3 → K) : W :=
  ρ γ (σ (Multiplicative.ofAdd x)) * (σ (Multiplicative.ofAdd (g2Act γ x)))⁻¹

variable {ρ : ↥(cayleyGroup K) →* MulAut W} {σ : Multiplicative (Ix3 → K) →* W}

theorem kapW_add (γ : ↥(cayleyGroup K)) (x y : Ix3 → K) :
    kapW ρ σ γ (x + y) = kapW ρ σ γ x * kapW ρ σ γ y := by
  simp only [kapW, ofAdd_add, map_mul, map_add, mul_inv]
  exact mul_mul_mul_comm _ _ _ _

theorem kapW_zero (γ : ↥(cayleyGroup K)) : kapW ρ σ γ 0 = 1 := by
  simp only [kapW, ofAdd_zero, map_one, map_zero, inv_one, mul_one]

variable {Z : Subgroup W} {H : Subgroup (MulAut W)} {π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥H}
  {f : W → (Ix3 → K)}

theorem kapW_mem (hf : IsCoord (lmG K) H Z π f) (hρ : ∀ γ w, f (ρ γ w) = g2Act γ (f w))
    (hσ : ∀ x, f (σ x) = Multiplicative.toAdd x) (γ : ↥(cayleyGroup K)) (x : Ix3 → K) :
    kapW ρ σ γ x ∈ Z := by
  apply (hf.ker _).mp
  rw [kapW, hf.map_mul_inv, hρ, hσ, hσ, toAdd_ofAdd, toAdd_ofAdd, sub_self]

theorem kapW_mul (hf : IsCoord (lmG K) H Z π f) (hρ : ∀ γ w, f (ρ γ w) = g2Act γ (f w))
    (hρZ : ∀ γ, ∀ z ∈ Z, ρ γ z = z) (hσ : ∀ x, f (σ x) = Multiplicative.toAdd x)
    (γ δ : ↥(cayleyGroup K)) (x : Ix3 → K) :
    kapW ρ σ (γ * δ) x = kapW ρ σ γ (g2Act δ x) * kapW ρ σ δ x := by
  have e1 : ρ δ (σ (Multiplicative.ofAdd x)) =
      kapW ρ σ δ x * σ (Multiplicative.ofAdd (g2Act δ x)) := (inv_mul_cancel_right _ _).symm
  have e2 : ρ γ (kapW ρ σ δ x) = kapW ρ σ δ x := hρZ γ _ (kapW_mem hf hρ hσ δ x)
  calc kapW ρ σ (γ * δ) x
      = ρ γ (ρ δ (σ (Multiplicative.ofAdd x))) *
          (σ (Multiplicative.ofAdd (g2Act γ (g2Act δ x))))⁻¹ := by
        rw [kapW, map_mul, MulAut.mul_apply, g2Act_mul_apply]
    _ = kapW ρ σ δ x * (ρ γ (σ (Multiplicative.ofAdd (g2Act δ x))) *
          (σ (Multiplicative.ofAdd (g2Act γ (g2Act δ x))))⁻¹) := by
        rw [e1, map_mul, e2, mul_assoc]
    _ = kapW ρ σ γ (g2Act δ x) * kapW ρ σ δ x := mul_comm _ _

theorem rhoW_mul_inv_eq (hf : IsCoord (lmG K) H Z π f) (hρZ : ∀ γ, ∀ z ∈ Z, ρ γ z = z)
    (hσ : ∀ x, f (σ x) = Multiplicative.toAdd x) (γ : ↥(cayleyGroup K)) (w : W) :
    ρ γ w * w⁻¹ =
      kapW ρ σ γ (f w) * σ (Multiplicative.ofAdd (g2Act γ (f w) - f w)) := by
  have hz : (σ (Multiplicative.ofAdd (f w)))⁻¹ * w ∈ Z := by
    apply (hf.ker _).mp
    rw [hf.map_mul, hf.map_inv, hσ, toAdd_ofAdd, neg_add_cancel]
  have hw : w = σ (Multiplicative.ofAdd (f w)) * ((σ (Multiplicative.ofAdd (f w)))⁻¹ * w) :=
    (mul_inv_cancel_left _ _).symm
  conv_lhs => rw [hw]
  rw [map_mul, hρZ γ _ hz, kapW, ofAdd_sub, map_div]
  simp only [div_eq_mul_inv, mul_inv]
  group

end Cocycle

section Formula

variable {W : Type*} [CommGroup W] {Z : Subgroup W} {H : Subgroup (MulAut W)}
  {π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥H} {f : W → (Ix3 → K)}
  {ρ : ↥(cayleyGroup K) →* MulAut W} {σ : Multiplicative (Ix3 → K) →* W}

theorem exists_kapW_formula [Finite K] [Algebra (ZMod 2) K] {n : ℕ} (hK : Nat.card K = 2 ^ n)
    (hn : 2 ≤ n) (hf : IsCoord (lmG K) H Z π f) (hρ : ∀ γ w, f (ρ γ w) = g2Act γ (f w))
    (hρZ : ∀ γ, ∀ z ∈ Z, ρ γ z = z) (hσ : ∀ x, f (σ x) = Multiplicative.toAdd x)
    (ζ : Additive ↥Z →+ ZMod 2) :
    ∃ (α : K) (m : Ix3 → K), ∀ γ y,
      ζ (Additive.ofMul ⟨kapW ρ σ γ y, kapW_mem hf hρ hσ γ y⟩) =
        Algebra.trace (ZMod 2) K (α * (cgE γ (zI y)).1) +
          Algebra.trace (ZMod 2) K (polarQ m (g2Act γ y - y)) := by
  classical
  have hκ : ∀ γ x y, (⟨kapW ρ σ γ (x + y), kapW_mem hf hρ hσ γ (x + y)⟩ : ↥Z) =
      ⟨kapW ρ σ γ x, kapW_mem hf hρ hσ γ x⟩ * ⟨kapW ρ σ γ y, kapW_mem hf hρ hσ γ y⟩ :=
    fun γ x y => Subtype.ext (kapW_add γ x y)
  let φ : ↥(cayleyGroup K) → ((Ix3 → K) →+ ZMod 2) := fun γ =>
    { toFun := fun x => ζ (Additive.ofMul ⟨kapW ρ σ γ x, kapW_mem hf hρ hσ γ x⟩)
      map_zero' := by
        rw [show (⟨kapW ρ σ γ 0, kapW_mem hf hρ hσ γ 0⟩ : ↥Z) = 1 from
          Subtype.ext (kapW_zero γ)]
        exact map_zero ζ
      map_add' := fun x y => by
        rw [hκ, ofMul_mul, map_add] }
  have hφ : ∀ γ x, φ γ x = ζ (Additive.ofMul ⟨kapW ρ σ γ x, kapW_mem hf hρ hσ γ x⟩) :=
    fun _ _ => rfl
  choose ψ hψ using fun γ => exists_trace_polarQ_eq (φ γ⁻¹)
  have hcoc : ψ ∈ Z1A (g2Act (F := K)) := by
    intro γ δ
    refine eq_of_trace_polarQ fun y => ?_
    rw [← hψ, polarQ_add_left, map_add, ← hψ]
    have e : polarQ (g2Act γ (ψ δ)) y = polarQ (ψ δ) (g2Act γ⁻¹ y) := by
      rw [← polarQ_g2Act γ⁻¹, g2Act_inv_apply]
    rw [e, ← hψ, hφ, hφ, hφ, _root_.mul_inv_rev]
    have h1 : (⟨kapW ρ σ (δ⁻¹ * γ⁻¹) y, kapW_mem hf hρ hσ _ y⟩ : ↥Z) =
        ⟨kapW ρ σ δ⁻¹ (g2Act γ⁻¹ y), kapW_mem hf hρ hσ _ _⟩ *
          ⟨kapW ρ σ γ⁻¹ y, kapW_mem hf hρ hσ _ y⟩ :=
      Subtype.ext (kapW_mul hf hρ hρZ hσ δ⁻¹ γ⁻¹ y)
    rw [h1, ofMul_mul, map_add, add_comm]
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨α, m, hm⟩ := exists_sub_fG_mem_B1A (F := K)
    (by rw [Fintype.card_eq_nat_card, hK]) (by omega : 1 < n) hcoc
  refine ⟨α, m, fun γ y => ?_⟩
  have h1 := hψ γ⁻¹ y
  rw [inv_inv, hφ] at h1
  rw [h1]
  have h3 : ψ γ⁻¹ = α • fG γ⁻¹ + (g2Act γ⁻¹ m - m) := by
    have := congrFun hm γ⁻¹
    rw [coboundaryA_apply, Pi.sub_apply, Pi.smul_apply] at this
    rw [this]
    abel
  have hfG : polarQ (fG γ⁻¹) y = (cgE γ (zI y)).1 := by
    have := bilQ_fG γ⁻¹ y
    rw [ellG, inv_inv] at this
    rw [← this]
    simp only [polarQ, bilQ]
    ring
  have hm' : polarQ (g2Act γ⁻¹ m) y = polarQ m (g2Act γ y) := by
    rw [← polarQ_g2Act γ, g2Act_apply_inv]
  rw [h3, polarQ_add_left, polarQ_smul_left, hfG, polarQ_sub_left, hm', polarQ_sub_right, map_add]

end Formula

section Comm

variable {W : Type*} [CommGroup W] {Z : Subgroup W} {H : Subgroup (MulAut W)}
  {π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥H} {f : W → (Ix3 → K)}
  {ρ : ↥(cayleyGroup K) →* MulAut W}

theorem rhoW_comm_eq [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n)
    (hf : IsCoord (lmG K) H Z π f) (hW : ∀ w : W, w ^ 2 = 1)
    (hρ : ∀ γ w, f (ρ γ w) = g2Act γ (f w)) (hρZ : ∀ γ, ∀ z ∈ Z, ρ γ z = z)
    {γ₁ γ₂ : ↥(cayleyGroup K)} {w₁ w₂ : W}
    (he : g2Act γ₁ (f w₁) - f w₁ = g2Act γ₂ (f w₂) - f w₂)
    (hq : qr γ₁ (f w₁) = qr γ₂ (f w₂)) :
    ρ γ₁ w₁ * w₁⁻¹ = ρ γ₂ w₂ * w₂⁻¹ := by
  obtain ⟨σ, hσ⟩ := hf.exists_section hW
  rw [rhoW_mul_inv_eq hf hρZ hσ γ₁ w₁, rhoW_mul_inv_eq hf hρZ hσ γ₂ w₂, he]
  congr 1
  have hℓ : (cgE γ₁ (zI (f w₁))).1 = (cgE γ₂ (zI (f w₂))).1 :=
    eq_of_mul_self_eq_charTwo (by rw [ell_mul_self, ell_mul_self, he, hq])
  have h1 : (⟨kapW ρ σ γ₁ (f w₁), kapW_mem hf hρ hσ _ _⟩ : ↥Z) *
      (⟨kapW ρ σ γ₂ (f w₂), kapW_mem hf hρ hσ _ _⟩ : ↥Z)⁻¹ = 1 := by
    refine eq_one_of_forall_addChar (fun z => Subtype.ext (by simpa using hW z)) fun ζ => ?_
    let _ : Algebra (ZMod 2) K := ZMod.algebra K 2
    obtain ⟨α, m, hαm⟩ := exists_kapW_formula hK hn hf hρ hρZ hσ ζ
    rw [ofMul_mul, ofMul_inv, map_add, map_neg, hαm, hαm, he, hℓ]
    exact add_neg_cancel _
  exact congrArg Subtype.val (mul_inv_eq_one.mp h1)

theorem rhoW_fix [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n)
    (hf : IsCoord (lmG K) H Z π f) (hW : ∀ w : W, w ^ 2 = 1)
    (hρ : ∀ γ w, f (ρ γ w) = g2Act γ (f w)) (hρZ : ∀ γ, ∀ z ∈ Z, ρ γ z = z)
    {γ : ↥(cayleyGroup K)} {w : W} (h : g2Act γ (f w) = f w) : ρ γ w = w := by
  have h1 := rhoW_comm_eq hK hn hf hW hρ hρZ (γ₁ := γ) (γ₂ := 1) (w₁ := w) (w₂ := w)
    (by rw [h, map_one, AddMonoid.End.coe_one, id_eq]) (by simp only [qr, h, map_one]; rfl)
  rw [map_one, MulAut.one_apply, mul_inv_cancel, mul_inv_eq_one] at h1
  exact h1

end Comm

section Real

variable {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)} {Z : Subgroup W}
  {π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥H} {f : W → (Ix3 → K)}

theorem rhoG_comm_eq [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n)
    (hf : IsCoord (lmG K) H Z π f) {c₀ : K} (hc0 : c₀ ≠ 0) (hc1 : c₀ ≠ 1)
    (hW : ∀ w : W, w ^ 2 = 1) (hZ : ∀ h ∈ H, ∀ z ∈ Z, h z = z)
    {γ₁ γ₂ : ↥(cayleyGroup K)} {w₁ w₂ : W}
    (he : g2Act γ₁ (f w₁) - f w₁ = g2Act γ₂ (f w₂) - f w₂)
    (hq : qr γ₁ (f w₁) = qr γ₂ (f w₂)) :
    ((rhoG hc0 hc1 π γ₁ : ↥H) : MulAut W) w₁ * w₁⁻¹ =
      ((rhoG hc0 hc1 π γ₂ : ↥H) : MulAut W) w₂ * w₂⁻¹ :=
  rhoW_comm_eq (ρ := H.subtype.comp (rhoG hc0 hc1 π)) hK hn hf hW
    (fun γ w => IsCoord.actG hf hc0 hc1 γ w) (fun γ z hz => hZ _ (rhoG hc0 hc1 π γ).2 z hz)
    he hq

theorem rhoG_fix [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n)
    (hf : IsCoord (lmG K) H Z π f) {c₀ : K} (hc0 : c₀ ≠ 0) (hc1 : c₀ ≠ 1)
    (hW : ∀ w : W, w ^ 2 = 1) (hZ : ∀ h ∈ H, ∀ z ∈ Z, h z = z) {γ : ↥(cayleyGroup K)} {w : W}
    (h : g2Act γ (f w) = f w) : ((rhoG hc0 hc1 π γ : ↥H) : MulAut W) w = w :=
  rhoW_fix (ρ := H.subtype.comp (rhoG hc0 hc1 π)) hK hn hf hW
    (fun γ w => IsCoord.actG hf hc0 hc1 γ w) (fun γ z hz => hZ _ (rhoG hc0 hc1 π γ).2 z hz) h

end Real

end CFSG.Quasithin.Vol2.Ch11.G2Q8
