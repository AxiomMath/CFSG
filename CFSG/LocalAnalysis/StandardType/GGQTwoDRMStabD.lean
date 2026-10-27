module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDRMStabDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoDFrameTau
import CFSG.LocalAnalysis.StandardType.GGQTwoDRMStabDMon

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType

private abbrev p9uRMD_J (m : ℕ) (i₀ : Fin m) := {i : Fin m // i ≠ i₀}

private lemma p9uRMD_card_J {m : ℕ} (i₀ : Fin m) :
    Fintype.card (p9uRMD_J m i₀) = m - 1 := by
  rw [Fintype.card_subtype]
  have h : (Finset.univ.filter fun i : Fin m => i ≠ i₀) = Finset.univ.erase i₀ := by
    ext i
    simp [Finset.mem_erase]
  rw [h, Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_univ, Fintype.card_fin]

private abbrev p9uRMD_A (m : ℕ) (i₀ : Fin m) :=
  {a : DVec m ≃ₗ[ZMod 3] DVec m //
    a (Pi.single i₀ 1) = Pi.single i₀ 1 ∧
      ∀ w ∈ dEvenStab m (Pi.single i₀ 1), a * w * a⁻¹ ∈ dEvenStab m (Pi.single i₀ 1)}

private lemma p9uRMD_if_decide_neg_one {x : ZMod 3} (hx : x = 1 ∨ x = -1) :
    (if decide (x = -1) = true then (-1 : ZMod 3) else 1) = x := by
  rcases hx with h | h
  · rw [h]
    decide +kernel
  · rw [h]
    decide +kernel

private noncomputable def p9uRMD_monSigma {m : ℕ} (hm : 6 ≤ m) (i₀ : Fin m)
    (a : p9uRMD_A m i₀) : Equiv.Perm (Fin m) :=
  (qtwoDRMStab_D_monomial hm i₀ a.1 a.2.1 a.2.2).choose

private noncomputable def p9uRMD_monC {m : ℕ} (hm : 6 ≤ m) (i₀ : Fin m)
    (a : p9uRMD_A m i₀) : Fin m → ZMod 3 :=
  (qtwoDRMStab_D_monomial hm i₀ a.1 a.2.1 a.2.2).choose_spec.choose

private lemma p9uRMD_monC_spec {m : ℕ} (hm : 6 ≤ m) (i₀ : Fin m) (a : p9uRMD_A m i₀) :
    (∀ i, p9uRMD_monC hm i₀ a i = 1 ∨ p9uRMD_monC hm i₀ a i = -1) ∧
      p9uRMD_monSigma hm i₀ a i₀ = i₀ ∧ p9uRMD_monC hm i₀ a i₀ = 1 ∧
      ∀ i, a.1 (dBasis m i) =
        p9uRMD_monC hm i₀ a i • dBasis m (p9uRMD_monSigma hm i₀ a i) :=
  (qtwoDRMStab_D_monomial hm i₀ a.1 a.2.1 a.2.2).choose_spec.choose_spec

private noncomputable def p9uRMD_monOf {m : ℕ} (hm : 6 ≤ m) (i₀ : Fin m)
    (a : p9uRMD_A m i₀) :
    (p9uRMD_J m i₀ → Bool) × Equiv.Perm (p9uRMD_J m i₀) :=
  let σ := p9uRMD_monSigma hm i₀ a
  let c := p9uRMD_monC hm i₀ a
  let hσ : σ i₀ = i₀ := (p9uRMD_monC_spec hm i₀ a).2.1
  (fun p => decide (c p.1 = -1),
   Equiv.subtypeEquiv σ (fun i => ⟨fun hi hc => hi (σ.injective (hc.trans hσ.symm)),
     fun hi hc => hi (by rw [hc, hσ])⟩))

private lemma p9uRMD_monOf_spec {m : ℕ} (hm : 6 ≤ m) (i₀ : Fin m)
    (a : p9uRMD_A m i₀) (p : p9uRMD_J m i₀) :
    a.1 (dBasis m p.1) =
      (if (p9uRMD_monOf hm i₀ a).1 p then (-1 : ZMod 3) else 1) •
        dBasis m ((p9uRMD_monOf hm i₀ a).2 p).1 := by
  have hc := (p9uRMD_monC_spec hm i₀ a).1
  have hact := (p9uRMD_monC_spec hm i₀ a).2.2.2
  have h1 : (p9uRMD_monOf hm i₀ a).1 p = decide (p9uRMD_monC hm i₀ a p.1 = -1) := rfl
  have h2 : ((p9uRMD_monOf hm i₀ a).2 p).1 = p9uRMD_monSigma hm i₀ a p.1 := rfl
  rw [h1, h2, hact p.1]
  exact (congrArg (fun t : ZMod 3 => t • dBasis m (p9uRMD_monSigma hm i₀ a p.1))
    (p9uRMD_if_decide_neg_one (hc p.1))).symm

private lemma p9uRMD_monOf_injective {m : ℕ} (hm : 6 ≤ m) (i₀ : Fin m) :
    Function.Injective (p9uRMD_monOf hm i₀) := by
  intro a b hab
  apply Subtype.ext
  apply (dBasis m).ext'
  intro i
  by_cases hi : i = i₀
  · rw [hi, dBasis, Pi.basisFun_apply, a.2.1, b.2.1]
  · have ha := p9uRMD_monOf_spec hm i₀ a ⟨i, hi⟩
    have hb := p9uRMD_monOf_spec hm i₀ b ⟨i, hi⟩
    rw [ha, hb, hab]

private lemma p9uRMD_u_coord {m : ℕ} (σ : Equiv.Perm (Fin m)) (c : Fin m → ZMod 3)
    (i k : Fin m) :
    (c i • dBasis m (σ i) - dBasis m i) k =
      c i * (if k = σ i then (1 : ZMod 3) else 0) - (if k = i then 1 else 0) := by
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, dBasis, Pi.basisFun_apply,
    Pi.single_apply]

private lemma p9uRMD_u_coord_eq {m : ℕ} {σ : Equiv.Perm (Fin m)} {c : Fin m → ZMod 3}
    {f : Module.Dual (ZMod 3) (DVec m)} {w : DVec m} {i : Fin m}
    (h : c i • dBasis m (σ i) - dBasis m i = -f (dBasis m i) • w) (k : Fin m) :
    c i * (if k = σ i then (1 : ZMod 3) else 0) - (if k = i then 1 else 0) =
      -f (dBasis m i) * w k := by
  have hh := congrFun h k
  rwa [p9uRMD_u_coord, Pi.smul_apply, smul_eq_mul] at hh

theorem qtwoDRMStab_D_oddSign {m : ℕ} (a : DVec m ≃ₗ[ZMod 3] DVec m) (hrefl : dIsRefl a)
    {σ : Equiv.Perm (Fin m)} {c : Fin m → ZMod 3}
    (hc : ∀ i, c i = 1 ∨ c i = -1) (hact : ∀ i, a (dBasis m i) = c i • dBasis m (σ i))
    (hprod : ¬ ∏ i, c i = 1) : ∃ i, a = dNeg m i := by
  classical
  obtain ⟨w, f, -, ha⟩ := hrefl
  have hco : ∀ i k : Fin m, c i * (if k = σ i then (1 : ZMod 3) else 0) -
      (if k = i then 1 else 0) = -f (dBasis m i) * w k := fun i k =>
    p9uRMD_u_coord_eq (by rw [← hact i, ha (dBasis m i), neg_smul]; abel) k
  have hσ : ∀ i, σ i = i := by
    by_contra hne
    obtain ⟨i, hi⟩ := not_forall.mp hne
    have h1 := hco i i
    rw [if_neg (fun h => hi h.symm), if_pos rfl] at h1
    have h2 := hco i (σ i)
    rw [if_pos rfl, if_neg hi] at h2
    have hoff : ∀ j, j ≠ i → j ≠ σ i → σ j = j ∧ c j = 1 := by
      intro j hji hjs
      have h3 := hco i j
      rw [if_neg hjs, if_neg hji] at h3
      have h4 := hco j j
      rw [if_pos rfl] at h4
      have hwj : w j = 0 := by
        simp only [mul_zero, zero_sub, sub_zero] at h1 h3
        revert h1 h3
        generalize f (dBasis m i) = x
        generalize w i = y
        generalize w j = z
        revert x y z
        decide
      rw [hwj] at h4
      by_cases hsj : j = σ j
      · rw [if_pos hsj, mul_one, mul_zero, sub_eq_zero] at h4
        exact ⟨hsj.symm, h4⟩
      · rw [if_neg hsj, mul_zero, mul_zero, zero_sub] at h4
        exact absurd h4 (by decide)
    have hσσ : σ (σ i) = i := by
      by_contra h
      have hsi : σ (σ i) ≠ σ i := fun h' => hi (σ.injective h')
      exact hsi (σ.injective (hoff (σ (σ i)) h hsi).1)
    have h5 := hco (σ i) i
    rw [if_pos hσσ.symm, if_neg (fun h => hi h.symm)] at h5
    have h6 := hco (σ i) (σ i)
    rw [hσσ, if_neg hi, if_pos rfl] at h6
    have hcc : c i * c (σ i) = 1 := by
      simp only [mul_zero, mul_one, zero_sub, sub_zero] at h1 h2 h5 h6
      revert h1 h2 h5 h6
      generalize f (dBasis m i) = x₁
      generalize f (dBasis m (σ i)) = x₂
      generalize w i = y₁
      generalize w (σ i) = y₂
      generalize c i = c₁
      generalize c (σ i) = c₂
      revert x₁ x₂ y₁ y₂ c₁ c₂
      decide
    apply hprod
    rw [← Finset.mul_prod_erase Finset.univ c (Finset.mem_univ i),
      ← Finset.mul_prod_erase (Finset.univ.erase i) c
        (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ _⟩),
      Finset.prod_eq_one (fun j hj => ?_), mul_one, hcc]
    obtain ⟨hjs, hj⟩ := Finset.mem_erase.mp hj
    exact (hoff j (Finset.mem_erase.mp hj).1 hjs).2
  obtain ⟨p, hp⟩ : ∃ p, c p ≠ 1 := by
    by_contra h
    exact hprod (Finset.prod_eq_one fun j _ => by
      by_contra hj
      exact h ⟨j, hj⟩)
  have hp' : c p = -1 := (hc p).resolve_left hp
  have hother : ∀ j, j ≠ p → c j = 1 := by
    intro j hjp
    by_contra hj
    have hj' : c j = -1 := (hc j).resolve_left hj
    have h1 := hco p p
    rw [hσ p, if_pos rfl, hp'] at h1
    have h2 := hco j p
    rw [hσ j, if_neg (Ne.symm hjp)] at h2
    have h3 := hco j j
    rw [hσ j, if_pos rfl, hj'] at h3
    simp only [mul_zero, mul_one, sub_zero] at h1 h2 h3
    revert h1 h2 h3
    generalize f (dBasis m p) = x₁
    generalize f (dBasis m j) = x₂
    generalize w p = y₁
    generalize w j = y₂
    revert x₁ x₂ y₁ y₂
    decide
  refine ⟨p, (dBasis m).ext' fun i => ?_⟩
  rw [hact i, hσ i, dNeg_basis]
  by_cases hip : i = p
  · rw [if_pos hip, hip, hp']
  · rw [if_neg hip, hother i hip]

theorem qtwoDRMStab_D {m : ℕ} (hm : 6 ≤ m) (i₀ : Fin m) :
    Nat.card {a : DVec m ≃ₗ[ZMod 3] DVec m //
        a (Pi.single i₀ 1) = Pi.single i₀ 1 ∧
          ∀ w ∈ dEvenStab m (Pi.single i₀ 1), a * w * a⁻¹ ∈ dEvenStab m (Pi.single i₀ 1)} ≤
      2 ^ (m - 1) * (m - 1).factorial ∧
    ∀ a : DVec m ≃ₗ[ZMod 3] DVec m, a (Pi.single i₀ 1) = Pi.single i₀ 1 →
      (∀ w ∈ dEvenStab m (Pi.single i₀ 1), a * w * a⁻¹ ∈ dEvenStab m (Pi.single i₀ 1)) →
        dIsRefl a → a ∈ dEvenStab m (Pi.single i₀ 1) ∨ ∃ i, a = dNeg m i := by
  classical
  haveI : Fintype (DVec m ≃ₗ[ZMod 3] DVec m) :=
    Fintype.ofInjective (fun e : DVec m ≃ₗ[ZMod 3] DVec m => (e : DVec m → DVec m))
      (fun _ _ h => LinearEquiv.ext (congrFun h))
  haveI : Fintype (p9uRMD_A m i₀) :=
    Fintype.ofInjective (Subtype.val : p9uRMD_A m i₀ → DVec m ≃ₗ[ZMod 3] DVec m)
      Subtype.val_injective
  constructor
  · have hcard := Fintype.card_le_of_injective (p9uRMD_monOf hm i₀)
      (p9uRMD_monOf_injective hm i₀)
    rw [Nat.card_eq_fintype_card]
    calc Fintype.card (p9uRMD_A m i₀)
        ≤ Fintype.card ((p9uRMD_J m i₀ → Bool) × Equiv.Perm (p9uRMD_J m i₀)) := hcard
      _ = 2 ^ (m - 1) * (m - 1).factorial := by
          rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_perm,
            p9uRMD_card_J]
  · intro a hfix hnorm hrefl
    obtain ⟨σ, c, hc, hσ0, hc0, hact⟩ := qtwoDRMStab_D_monomial hm i₀ a hfix hnorm
    by_cases hprod : ∏ i, c i = 1
    · exact Or.inl ⟨⟨σ, c, hc, hprod, hact⟩, hfix⟩
    · exact Or.inr (qtwoDRMStab_D_oddSign a hrefl hc hact hprod)

end CFSG.StandardType.QTwo

end
