module

public import Mathlib.GroupTheory.RegularWreathProduct
public import Mathlib.GroupTheory.NoncommCoprod

public section

namespace CFSG.Quasithin.S14110

section Aux

variable {G D : Type*} [Group G] [Group D]

private def e2 : Multiplicative (ZMod 2) := Multiplicative.ofAdd 1

private theorem e2_ne_one : e2 ≠ 1 := by decide

private theorem e2_mul_e2 : e2 * e2 = 1 := by decide

private theorem e2_inv : e2⁻¹ = e2 := by decide

private theorem q_cases (q : Multiplicative (ZMod 2)) : q = 1 ∨ q = e2 := by
  revert q; decide

private def basePart (ι₁ ι₂ : D →* G) (hc : ∀ a b, Commute (ι₁ a) (ι₂ b)) :
    (Multiplicative (ZMod 2) → D) →* G :=
  (ι₁.noncommCoprod ι₂ hc).comp
    ((Pi.evalMonoidHom (fun _ => D) 1).prod (Pi.evalMonoidHom (fun _ => D) e2))

private theorem basePart_apply (ι₁ ι₂ : D →* G) (hc : ∀ a b, Commute (ι₁ a) (ι₂ b))
    (f : Multiplicative (ZMod 2) → D) : basePart ι₁ ι₂ hc f = ι₁ (f 1) * ι₂ (f e2) := rfl

private def invol (s : G) (hs : s * s = 1) : Multiplicative (ZMod 2) →* G where
  toFun q := if q = 1 then 1 else s
  map_one' := by simp
  map_mul' q r := by
    rcases q_cases q with rfl | rfl <;> rcases q_cases r with rfl | rfl <;>
      simp [e2_ne_one, e2_mul_e2, hs]

private theorem invol_e2 (s : G) (hs : s * s = 1) : invol s hs e2 = s := by
  simp [invol, e2_ne_one]

private theorem invol_mul_basePart (ι₁ ι₂ : D →* G) (hc : ∀ a b, Commute (ι₁ a) (ι₂ b)) (s : G)
    (hs : s * s = 1) (h₁ : ∀ d, s * ι₁ d = ι₂ d * s) (h₂ : ∀ d, s * ι₂ d = ι₁ d * s)
    (q : Multiplicative (ZMod 2)) (g : Multiplicative (ZMod 2) → D) :
    invol s hs q * basePart ι₁ ι₂ hc g =
      basePart ι₁ ι₂ hc (fun x => g (q⁻¹ * x)) * invol s hs q := by
  rcases q_cases q with rfl | rfl
  · simp
  · rw [invol_e2, basePart_apply, basePart_apply]
    simp only [e2_inv, mul_one, e2_mul_e2]
    calc s * (ι₁ (g 1) * ι₂ (g e2)) = (s * ι₁ (g 1)) * ι₂ (g e2) := (mul_assoc _ _ _).symm
      _ = (ι₂ (g 1) * s) * ι₂ (g e2) := by rw [h₁]
      _ = ι₂ (g 1) * (s * ι₂ (g e2)) := mul_assoc _ _ _
      _ = ι₂ (g 1) * (ι₁ (g e2) * s) := by rw [h₂]
      _ = (ι₂ (g 1) * ι₁ (g e2)) * s := (mul_assoc _ _ _).symm
      _ = (ι₁ (g e2) * ι₂ (g 1)) * s := by rw [(hc (g e2) (g 1)).eq]

private def wreathHom (ι₁ ι₂ : D →* G) (hc : ∀ a b, Commute (ι₁ a) (ι₂ b)) (s : G)
    (hs : s * s = 1) (h₁ : ∀ d, s * ι₁ d = ι₂ d * s) (h₂ : ∀ d, s * ι₂ d = ι₁ d * s) :
    D ≀ᵣ Multiplicative (ZMod 2) →* G where
  toFun x := basePart ι₁ ι₂ hc x.left * invol s hs x.right
  map_one' := by simp
  map_mul' x y := by
    simp only [RegularWreathProduct.mul_left, RegularWreathProduct.mul_right, map_mul]
    have key := invol_mul_basePart ι₁ ι₂ hc s hs h₁ h₂ x.right y.left
    calc basePart ι₁ ι₂ hc x.left *
          basePart ι₁ ι₂ hc (fun z => y.left (x.right⁻¹ * z)) *
          (invol s hs x.right * invol s hs y.right)
        = basePart ι₁ ι₂ hc x.left *
          (basePart ι₁ ι₂ hc (fun z => y.left (x.right⁻¹ * z)) * invol s hs x.right) *
          invol s hs y.right := by simp only [mul_assoc]
      _ = basePart ι₁ ι₂ hc x.left * (invol s hs x.right * basePart ι₁ ι₂ hc y.left) *
          invol s hs y.right := by rw [key]
      _ = basePart ι₁ ι₂ hc x.left * invol s hs x.right *
          (basePart ι₁ ι₂ hc y.left * invol s hs y.right) := by simp only [mul_assoc]

private theorem wreathHom_apply (ι₁ ι₂ : D →* G) (hc : ∀ a b, Commute (ι₁ a) (ι₂ b)) (s : G)
    (hs : s * s = 1) (h₁ : ∀ d, s * ι₁ d = ι₂ d * s) (h₂ : ∀ d, s * ι₂ d = ι₁ d * s)
    (x : D ≀ᵣ Multiplicative (ZMod 2)) :
    wreathHom ι₁ ι₂ hc s hs h₁ h₂ x = basePart ι₁ ι₂ hc x.left * invol s hs x.right := rfl

end Aux

theorem nonempty_mulEquiv_wreath {G D : Type*} [Group G] [Group D] (M N M₁ M₂ : Subgroup G) (s : G)
    (hNM : N ≤ M) (hsM : s ∈ M) (h₁N : M₁ ≤ N) (h₂N : M₂ ≤ N)
    (hcomm : ∀ a ∈ M₁, ∀ b ∈ M₂, a * b = b * a)
    (hdisj : ∀ x ∈ M₁, x ∈ M₂ → x = 1)
    (hs2 : s * s = 1) (hsN : s ∉ N)
    (hcosets : ∀ m ∈ M, m ∈ N ∨ m * s⁻¹ ∈ N)
    (hfact : ∀ n ∈ N, ∃ a ∈ M₁, ∃ b ∈ M₂, n = a * b)
    (hs₁ : ∀ a ∈ M₁, s * a * s⁻¹ ∈ M₂) (hs₂ : ∀ b ∈ M₂, s * b * s⁻¹ ∈ M₁)
    (φ : M₁ ≃* D) :
    Nonempty (M ≃* D ≀ᵣ Multiplicative (ZMod 2)) := by
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  obtain ⟨ι₁, hι₁M, hι₁inj, hι₁surj⟩ : ∃ ι₁ : D →* G, (∀ d, ι₁ d ∈ M₁) ∧ Function.Injective ι₁ ∧
      ∀ a ∈ M₁, ∃ d, ι₁ d = a :=
    ⟨M₁.subtype.comp φ.symm.toMonoidHom, fun d => (φ.symm d).2,
      fun a b h => φ.symm.injective (Subtype.ext h), fun a ha => ⟨φ ⟨a, ha⟩, by simp⟩⟩
  obtain ⟨ι₂, hι₂⟩ : ∃ ι₂ : D →* G, ∀ d, ι₂ d = s * ι₁ d * s⁻¹ :=
    ⟨(MulAut.conj s).toMonoidHom.comp ι₁, fun d => rfl⟩
  have hι₂M : ∀ d, ι₂ d ∈ M₂ := fun d => by rw [hι₂]; exact hs₁ _ (hι₁M d)
  have hι₂inj : Function.Injective ι₂ := by
    intro a b h
    rw [hι₂, hι₂] at h
    exact hι₁inj (mul_left_cancel (mul_right_cancel h))
  have hι₂surj : ∀ b ∈ M₂, ∃ d, ι₂ d = b := by
    intro b hb
    obtain ⟨d, hd⟩ := hι₁surj _ (hs₂ b hb)
    refine ⟨d, ?_⟩
    rw [hι₂, hd, hsinv]
    calc s * (s * b * s) * s = (s * s) * b * (s * s) := by simp only [mul_assoc]
      _ = b := by rw [hs2]; simp
  have hc : ∀ a b, Commute (ι₁ a) (ι₂ b) := fun a b => hcomm _ (hι₁M a) _ (hι₂M b)
  have h₁ : ∀ d, s * ι₁ d = ι₂ d * s := fun d => by rw [hι₂]; simp
  have h₂ : ∀ d, s * ι₂ d = ι₁ d * s := fun d => by
    rw [hι₂, hsinv, ← mul_assoc, ← mul_assoc, hs2, one_mul]
  have hbase_mem : ∀ f, basePart ι₁ ι₂ hc f ∈ N := fun f =>
    mul_mem (h₁N (hι₁M _)) (h₂N (hι₂M _))
  have hinvol_mem : ∀ q, invol s hs2 q ∈ M := by
    intro q
    rcases q_cases q with rfl | rfl
    · rw [map_one]; exact one_mem M
    · rw [invol_e2]; exact hsM
  have hmem : ∀ x, wreathHom ι₁ ι₂ hc s hs2 h₁ h₂ x ∈ M := fun x =>
    mul_mem (hNM (hbase_mem _)) (hinvol_mem _)
  have hinj : Function.Injective (wreathHom ι₁ ι₂ hc s hs2 h₁ h₂) := by
    rw [injective_iff_map_eq_one]
    rintro ⟨f, q⟩ hx
    rw [wreathHom_apply] at hx
    rcases q_cases q with rfl | rfl
    · rw [map_one, mul_one, basePart_apply] at hx
      have h1 : ι₁ (f 1) = 1 := by
        refine hdisj _ (hι₁M _) ?_
        have : ι₁ (f 1) = (ι₂ (f e2))⁻¹ := eq_inv_of_mul_eq_one_left hx
        rw [this]
        exact inv_mem (hι₂M _)
      have h2 : ι₂ (f e2) = 1 := by rwa [h1, one_mul] at hx
      have hf : f = 1 := by
        funext x
        rcases q_cases x with rfl | rfl
        · exact hι₁inj (by rw [h1]; simp)
        · exact hι₂inj (by rw [h2]; simp)
      exact RegularWreathProduct.ext hf rfl
    · exfalso
      rw [invol_e2] at hx
      apply hsN
      have : s = (basePart ι₁ ι₂ hc f)⁻¹ := eq_inv_of_mul_eq_one_right hx
      rw [this]
      exact inv_mem (hbase_mem _)
  have hexists : ∀ n ∈ N, ∃ f, basePart ι₁ ι₂ hc f = n := by
    intro n hn
    obtain ⟨a, ha, b, hb, rfl⟩ := hfact n hn
    obtain ⟨d₁, hd₁⟩ := hι₁surj a ha
    obtain ⟨d₂, hd₂⟩ := hι₂surj b hb
    refine ⟨fun x => if x = 1 then d₁ else d₂, ?_⟩
    rw [basePart_apply]
    simp [e2_ne_one, hd₁, hd₂]
  have hsurj : ∀ m ∈ M, ∃ x, wreathHom ι₁ ι₂ hc s hs2 h₁ h₂ x = m := by
    intro m hm
    rcases hcosets m hm with h | h
    · obtain ⟨f, hf⟩ := hexists m h
      exact ⟨⟨f, 1⟩, by rw [wreathHom_apply]; simp [hf]⟩
    · obtain ⟨f, hf⟩ := hexists _ h
      refine ⟨⟨f, e2⟩, ?_⟩
      rw [wreathHom_apply]
      simp only
      rw [invol_e2, hf, mul_assoc, hsinv, hs2, mul_one]
  let Ψ : D ≀ᵣ Multiplicative (ZMod 2) →* M :=
    (wreathHom ι₁ ι₂ hc s hs2 h₁ h₂).codRestrict M hmem
  have hΨ : Function.Bijective Ψ := by
    refine ⟨fun x y h => hinj (congrArg Subtype.val h), ?_⟩
    rintro ⟨m, hm⟩
    obtain ⟨x, hx⟩ := hsurj m hm
    exact ⟨x, Subtype.ext hx⟩
  exact ⟨(MulEquiv.ofBijective Ψ hΨ).symm⟩

end CFSG.Quasithin.S14110
