module

public import CFSG.Quasithin.EmptyFaithful.S153E58C
public import CFSG.Quasithin.Background.B5Part3

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank

namespace S153E58

open Matrix

variable {W : Type} [CommGroup W]

@[expose] def TransvIn (K : Subgroup (MulAut W)) (W₁ : Subgroup W) (e : ↥W₁ ≃* V3) : Prop :=
  ∀ x φ : Fin 3 → ZMod 2, φ ⬝ᵥ x = 0 → ∃ k ∈ K, ∀ (u : ↥W₁) (hu : (k : MulAut W) (u : W) ∈ W₁),
    e ⟨(k : MulAut W) (u : W), hu⟩ =
      Multiplicative.ofAdd (Multiplicative.toAdd (e u) + (φ ⬝ᵥ Multiplicative.toAdd (e u)) • x)

theorem exists_coords_of_realizes {K : Subgroup (MulAut W)} {W₁ : Subgroup W}
    {π : ↥(StatedSL 3 (ZMod 2)) →* ↥K}
    (hπ : (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia K W₁ ⊥ π) :
    ∃ e : ↥W₁ ≃* V3, TransvIn K W₁ e ∧
      ∀ (γ : ↥(StatedSL 3 (ZMod 2))) (u : ↥W₁) (hu : (π γ : MulAut W) (u : W) ∈ W₁),
        e ⟨(π γ : MulAut W) (u : W), hu⟩ = natAct (StatedSL 3 (ZMod 2)) γ (e u) := by
  obtain ⟨e, he⟩ := B5.exists_linModel hπ
  refine ⟨e, fun x φ h => ⟨(π (transvSL x φ h) : MulAut W), (π (transvSL x φ h)).2, fun u hu => ?_⟩, he⟩
  rw [he (transvSL x φ h) u hu]
  change Multiplicative.ofAdd (((transvGL x φ h : GL (Fin 3) (ZMod 2)) :
    Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec (Multiplicative.toAdd (e u))) = _
  rw [transvGL_mulVec]

variable {K : Subgroup (MulAut W)} {W₁ : Subgroup W} {e : ↥W₁ ≃* V3}

private theorem ofAdd_toAdd_smul (z : ZMod 2) (hz : z = 1) (x v : Fin 3 → ZMod 2) :
    Multiplicative.ofAdd (v + z • x) = Multiplicative.ofAdd v * Multiplicative.ofAdd x := by
  rw [hz, one_smul]
  rfl

private theorem coords_fixed (hKW : ∀ k ∈ K, ∀ u ∈ W₁, (k : MulAut W) u ∈ W₁)
    {x φ : Fin 3 → ZMod 2} {k : MulAut W} (hkK : k ∈ K)
    (hk : ∀ (u : ↥W₁) (hu : (k : MulAut W) (u : W) ∈ W₁),
      e ⟨(k : MulAut W) (u : W), hu⟩ =
        Multiplicative.ofAdd (Multiplicative.toAdd (e u) + (φ ⬝ᵥ Multiplicative.toAdd (e u)) • x))
    (u : ↥W₁) (hφu : φ ⬝ᵥ Multiplicative.toAdd (e u) = 0) : (k : MulAut W) (u : W) = u := by
  have h1 := hk u (hKW k hkK u u.2)
  rw [hφu, zero_smul, add_zero] at h1
  have h2 : (⟨(k : MulAut W) (u : W), hKW k hkK u u.2⟩ : ↥W₁) = u := e.injective (by
    rw [h1]
    rfl)
  exact congrArg Subtype.val h2

theorem form_zero_of_transv (hT : TransvIn K W₁ e) (hKW : ∀ k ∈ K, ∀ u ∈ W₁, (k : MulAut W) u ∈ W₁)
    (f : W → W → ZMod 2) (hr : ∀ a b c, f a (b * c) = f a b + f a c)
    (hinv : ∀ k ∈ K, ∀ a ∈ W₁, ∀ b ∈ W₁, f ((k : MulAut W) a) ((k : MulAut W) b) = f a b) :
    ∀ a ∈ W₁, ∀ b ∈ W₁, f a b = 0 := by
  intro a ha b hb
  have hf1 : ∀ a, f a 1 = 0 := by
    intro a
    have := hr a 1 1
    rw [mul_one] at this
    have h2 : f a 1 + f a 1 = f a 1 + 0 := by rw [← this, add_zero]
    exact add_left_cancel h2
  by_cases hb1 : b = 1
  · rw [hb1]
    exact hf1 a
  set x : Fin 3 → ZMod 2 := Multiplicative.toAdd (e ⟨b, hb⟩) with hx
  have hx0 : x ≠ 0 := by
    intro h
    apply hb1
    have : e ⟨b, hb⟩ = 1 := by
      have := congrArg Multiplicative.ofAdd h
      simpa [hx] using this
    have h3 : (⟨b, hb⟩ : ↥W₁) = 1 := e.injective (this.trans (map_one e).symm)
    exact congrArg Subtype.val h3
  obtain ⟨φ, w, hφx, hφv, hφw⟩ := key_form (Multiplicative.toAdd (e ⟨a, ha⟩)) x hx0
  obtain ⟨k, hkK, hk⟩ := hT x φ hφx
  have hka : (k : MulAut W) a = a := coords_fixed hKW hkK hk ⟨a, ha⟩ hφv
  set c : ↥W₁ := e.symm (Multiplicative.ofAdd w) with hc
  have hec : Multiplicative.toAdd (e c) = w := by simp [hc]
  have hkc : (k : MulAut W) (c : W) = (c : W) * b := by
    have h1 := hk c (hKW k hkK c c.2)
    rw [hec, hφw] at h1
    have h2 : e ⟨(k : MulAut W) (c : W), hKW k hkK c c.2⟩ = e (c * ⟨b, hb⟩) := by
      rw [h1, map_mul, ofAdd_toAdd_smul 1 rfl]
      simp [hc]
      rfl
    have h3 := e.injective h2
    exact congrArg Subtype.val h3
  have h4 := hinv k hkK a ha c c.2
  rw [hka, hkc, hr] at h4
  have h5 : f a c + f a b = f a c + 0 := by rw [h4, add_zero]
  exact add_left_cancel h5

theorem eq_id_of_commute (hT : TransvIn K W₁ e) (hKW : ∀ k ∈ K, ∀ u ∈ W₁, (k : MulAut W) u ∈ W₁)
    {c : MulAut W} (hc : ∀ u ∈ W₁, c u ∈ W₁) (hcom : ∀ k ∈ K, c * k = k * c) :
    ∀ a ∈ W₁, c a = a := by
  intro a ha
  by_cases ha1 : a = 1
  · rw [ha1]
    exact map_one c
  set x : Fin 3 → ZMod 2 := Multiplicative.toAdd (e ⟨a, ha⟩) with hx
  have hx0 : x ≠ 0 := by
    intro h
    apply ha1
    have : e ⟨a, ha⟩ = 1 := by
      have := congrArg Multiplicative.ofAdd h
      simpa [hx] using this
    have h3 : (⟨a, ha⟩ : ↥W₁) = 1 := e.injective (this.trans (map_one e).symm)
    exact congrArg Subtype.val h3
  obtain ⟨φ, v, hφx, hφv⟩ := key_schur x hx0
  obtain ⟨k, hkK, hk⟩ := hT x φ hφx
  set b : ↥W₁ := e.symm (Multiplicative.ofAdd v) with hb
  have heb : Multiplicative.toAdd (e b) = v := by simp [hb]
  have hkb : (k : MulAut W) (b : W) = (b : W) * a := by
    have h1 := hk b (hKW k hkK b b.2)
    rw [heb, hφv] at h1
    have h2 : e ⟨(k : MulAut W) (b : W), hKW k hkK b b.2⟩ = e (b * ⟨a, ha⟩) := by
      rw [h1, map_mul, ofAdd_toAdd_smul 1 rfl]
      simp [hb]
      rfl
    exact congrArg Subtype.val (e.injective h2)
  have hcb : c (b : W) ∈ W₁ := hc b b.2
  set b' : ↥W₁ := ⟨c (b : W), hcb⟩ with hb'
  have hcomb : c ((k : MulAut W) (b : W)) = (k : MulAut W) (c (b : W)) :=
    DFunLike.congr_fun (hcom k hkK) (b : W)
  rw [hkb, map_mul] at hcomb
  by_cases h' : φ ⬝ᵥ Multiplicative.toAdd (e b') = 0
  · have hfix := coords_fixed hKW hkK hk b' h'
    rw [show (b' : W) = c (b : W) from rfl] at hfix
    rw [hfix] at hcomb
    have : c a = 1 := by
      have h3 : c (b : W) * c a = c (b : W) * 1 := by rw [mul_one]; exact hcomb
      exact mul_left_cancel h3
    exfalso
    apply ha1
    have : c a = c 1 := by rw [this, map_one]
    exact c.injective this
  · have h1' : φ ⬝ᵥ Multiplicative.toAdd (e b') = 1 := zmod_two_eq _ h'
    have h1 := hk b' (hKW k hkK b' b'.2)
    rw [h1'] at h1
    have h2 : e ⟨(k : MulAut W) (b' : W), hKW k hkK b' b'.2⟩ = e (b' * ⟨a, ha⟩) := by
      rw [h1, map_mul, ofAdd_toAdd_smul 1 rfl]
      rfl
    have h3 : (k : MulAut W) (c (b : W)) = c (b : W) * a := congrArg Subtype.val (e.injective h2)
    rw [h3] at hcomb
    exact mul_left_cancel hcomb

end S153E58

end CFSG.Quasithin
