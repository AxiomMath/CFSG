module

public import CFSG.LocalAnalysis.StandardType.GGL45TGFrame

public section

namespace CFSG.StandardType.GGL45TG

open CFSG CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA Matrix
open GGL45TA (diagGL coe_diagGL scalar_mem_center not_two_cols_in_row)
open GGL45TA.LinSetting (exists_not_mem_of_card)

namespace GSetting

variable {d : ℕ} {k : Type} [Field k] [Finite k] {K : Type} [Group K] {D : GData d k} {p q₀ : ℕ}
  {ψ : MulAut K} {E : Subgroup (MulAut K)}

theorem exists_lift_of_diag_three (S : GSetting p q₀ d k D K ψ E) {P : GL (Fin d) k}
    (hP : ∀ x, S.IsLift x → ∀ i j, i ≠ j →
      ((P * x * P⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k) i j = 0)
    (hd : d = 3) (s : Fin d → kˣ) (hs : ∀ i, s i ^ p = 1) :
    ∃ y, S.IsLift y ∧ P * y * P⁻¹ = diagGL d s := by
  classical
  haveI : NeZero p := ⟨S.hp.ne_zero⟩
  have ht : ∀ x : {x : GL (Fin d) k // S.IsLift x}, ∃ t : Fin d → kˣ,
      (∀ i, t i ^ p = 1) ∧ P * x.1 * P⁻¹ = diagGL d t := fun x => S.frame_eq_diagGL hP x.2
  choose t htp ht using ht
  let f : {x : GL (Fin d) k // S.IsLift x} → (Fin d → rootsOfUnity p k) := fun x i =>
    ⟨t x i, (mem_rootsOfUnity p _).mpr (htp x i)⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have h1 : t x = t y := funext fun i => congrArg Subtype.val (congrFun hxy i)
    have h2 : P * x.1 * P⁻¹ = P * y.1 * P⁻¹ := by rw [ht, ht, h1]
    exact Subtype.ext (by simpa using h2)
  have hcard : Nat.card (Fin d → rootsOfUnity p k) ≤ Nat.card {x : GL (Fin d) k // S.IsLift x} := by
    rw [Nat.card_fun, Nat.card_fin]
    calc Nat.card (rootsOfUnity p k) ^ d ≤ p ^ d := Nat.pow_le_pow_left (card_rootsOfUnity k p) d
      _ = p * p ^ 2 := by rw [hd]; ring
      _ ≤ p * Nat.card E := Nat.mul_le_mul_left p S.card_E
      _ = Nat.card E * p := mul_comm _ _
      _ ≤ _ := S.card_E_mul_le
  obtain ⟨y, hy⟩ := (hf.bijective_of_nat_card_le hcard).2 fun i =>
    ⟨s i, (mem_rootsOfUnity p _).mpr (hs i)⟩
  refine ⟨y.1, y.2, ?_⟩
  rw [ht]
  congr 1
  funext i
  have := congrArg Subtype.val (congrFun hy i)
  exact this

theorem commute_of_comm_scalar (S : GSetting p q₀ d k D K ψ E) {g : GL (Fin d) k}
    (hg : ∀ x, S.IsLift x → g * x * g⁻¹ * x⁻¹ ∈ LargeEvenScalars (Fin d) k) {x : GL (Fin d) k}
    (hx : S.IsLift x) : g * x = x * g := by
  classical
  obtain ⟨P, hPτ, hP, hPH⟩ := S.exists_diag_frame
  obtain ⟨ω, hω⟩ := S.exists_primitive
  have hω1 : ω ≠ 1 := hω.ne_one S.hp.one_lt
  have hωinv : ω⁻¹ ≠ ω := by
    intro h
    have h2 : ω ^ 2 = 1 := by rw [sq]; nth_rewrite 1 [← h]; exact inv_mul_cancel ω
    have := Nat.le_of_dvd (by norm_num) ((hω.pow_eq_one_iff_dvd 2).mp h2)
    exact S.hp2 (le_antisymm this S.hp.two_le)
  have hd3 := S.three_le
  set Mg : GL (Fin d) k := P * g * P⁻¹ with hMg
  clear_value Mg
  have hrel : ∀ y, S.IsLift y → ∀ s : Fin d → kˣ, P * y * P⁻¹ = diagGL d s →
      ∃ c : kˣ, ∀ a b, (Mg : Matrix (Fin d) (Fin d) k) a b * (s b : k) =
        (c : k) * (s a : k) * (Mg : Matrix (Fin d) (Fin d) k) a b := by
    intro y hy s hs
    obtain ⟨c, hc⟩ := hg y hy
    refine ⟨c, fun a b => ?_⟩
    have hcen := Subgroup.mem_center_iff.mp (scalar_mem_center (d := d) (k := k) ⟨c, rfl⟩)
    have hgy : g * y = Matrix.GeneralLinearGroup.scalar (Fin d) c * y * g := by rw [hc]; group
    have h1 : Mg * diagGL d s = Matrix.GeneralLinearGroup.scalar (Fin d) c * diagGL d s * Mg := by
      rw [hMg, ← hs]
      calc P * g * P⁻¹ * (P * y * P⁻¹) = P * (g * y) * P⁻¹ := by group
        _ = P * (Matrix.GeneralLinearGroup.scalar (Fin d) c * y * g) * P⁻¹ := by rw [hgy]
        _ = P * Matrix.GeneralLinearGroup.scalar (Fin d) c * P⁻¹ * (P * y * P⁻¹) *
              (P * g * P⁻¹) := by group
        _ = Matrix.GeneralLinearGroup.scalar (Fin d) c * (P * y * P⁻¹) * (P * g * P⁻¹) := by
            rw [hcen P, mul_inv_cancel_right]
    have h2 := congrArg (fun z : GL (Fin d) k => (z : Matrix (Fin d) (Fin d) k) a b) h1
    simp only [Units.val_mul, coe_diagGL, Matrix.GeneralLinearGroup.coe_scalar, scalar_apply,
      mul_diagonal, diagonal_mul_diagonal, diagonal_mul] at h2
    exact h2
  have hkey : ∀ a b, a ≠ b → ∀ (y : GL (Fin d) k) (s : Fin d → kˣ), S.IsLift y →
      P * y * P⁻¹ = diagGL d s → s a = ω → s b = 1 → (∀ a', s a' = ω → a' = a) →
      ∀ b₂, b₂ ≠ b → s b₂ = 1 → (Mg : Matrix (Fin d) (Fin d) k) a b = 0 := by
    intro a b hab y s hy hys hsa hsb hsω b₂ hb₂ hsb₂
    by_contra hne
    obtain ⟨c, hc⟩ := hrel y hy s hys
    have hcω : (c : k) * ω = 1 := by
      have := hc a b
      rw [hsa, hsb, Units.val_one, mul_one] at this
      have h3 : ((c : k) * ω - 1) * (Mg : Matrix (Fin d) (Fin d) k) a b = 0 := by
        linear_combination -this
      exact sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_right hne)
    have hsupp : ∀ b', s b' = 1 → ∀ a', a' ≠ a → (Mg : Matrix (Fin d) (Fin d) k) a' b' = 0 := by
      intro b' hb' a' ha'
      by_contra hne'
      have := hc a' b'
      rw [hb', Units.val_one, mul_one] at this
      have h3 : (1 : k) = c * s a' := by
        have h5 : ((c : k) * s a' - 1) * (Mg : Matrix (Fin d) (Fin d) k) a' b' = 0 := by
          linear_combination -this
        exact (sub_eq_zero.mp ((mul_eq_zero.mp h5).resolve_right hne')).symm
      have h4 : (s a' : k) = ω := by
        have hc0 : (c : k) ≠ 0 := c.ne_zero
        calc (s a' : k) = (ω : k) * ((c : k) * s a') := by
              rw [← mul_assoc, mul_comm (ω : k), hcω, one_mul]
          _ = ω := by rw [← h3, mul_one]
      exact ha' (hsω a' (Units.ext h4))
    exact not_two_cols_in_row Mg (Ne.symm hb₂) (hsupp b hsb) (hsupp b₂ hsb₂)
  have hMdiag : ∀ a b, a ≠ b → (Mg : Matrix (Fin d) (Fin d) k) a b = 0 := by
    intro a b hab
    rcases Nat.lt_or_ge d 4 with hd4 | hd4
    ·
      have hd : d = 3 := by omega
      obtain ⟨y, hy, hys⟩ := S.exists_lift_of_diag_three hP hd (Pi.mulSingle a ω) fun i => by
        by_cases hi : i = a
        · subst hi; rw [Pi.mulSingle_eq_same (M := fun _ => kˣ), hω.pow_eq_one]
        · rw [Pi.mulSingle_eq_of_ne (M := fun _ => kˣ) hi, one_pow]
      obtain ⟨b₂, hb₂⟩ := exists_not_mem_of_card ({a, b} : Finset (Fin d)) (by
        have := Finset.card_le_two (a := a) (b := b); omega)
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb₂
      have h1 : (Pi.mulSingle a ω : Fin d → kˣ) a = ω :=
        Pi.mulSingle_eq_same (M := fun _ => kˣ) a ω
      have h2 : (Pi.mulSingle a ω : Fin d → kˣ) b = 1 :=
        Pi.mulSingle_eq_of_ne (M := fun _ => kˣ) (Ne.symm hab) ω
      have h3 : (Pi.mulSingle a ω : Fin d → kˣ) b₂ = 1 :=
        Pi.mulSingle_eq_of_ne (M := fun _ => kˣ) hb₂.1 ω
      refine hkey a b hab y _ hy hys h1 h2 (fun a' ha' => ?_) b₂ hb₂.2 h3
      by_contra hne
      rw [Pi.mulSingle_eq_of_ne (M := fun _ => kˣ) hne] at ha'
      exact hω1 ha'.symm
    ·
      obtain ⟨e, he⟩ := exists_not_mem_of_card ({a, b} : Finset (Fin d)) (by
        have := Finset.card_le_two (a := a) (b := b); omega)
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at he
      obtain ⟨b₂, hb₂⟩ := exists_not_mem_of_card ({a, b, e} : Finset (Fin d)) (by
        have := Finset.card_le_three (a := a) (b := b) (c := e); omega)
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb₂
      set s := NbrLangTypeA.torusVec a e ω with hs
      have hsv : ∀ l, s l = (if l = a then ω else 1) * (if l = e then ω⁻¹ else 1) := fun l =>
        NbrLangTypeA.torusVec_apply a e ω l
      have htp : ∀ l, s l ^ p = 1 := fun l => by
        rw [hsv, mul_pow]
        split_ifs <;> simp [hω.pow_eq_one]
      have hy := S.torus_isLift hPτ hP hPH htp (NbrLangTypeA.prod_torusVec a e ω)
      have hys : P * (P⁻¹ * diagGL d s * P) * P⁻¹ = diagGL d s := by group
      have hea : e ≠ a := he.1
      refine hkey a b hab _ s hy hys ?_ ?_ (fun a' ha' => ?_) b₂ hb₂.2.1 ?_
      · rw [hsv]; simp [Ne.symm hea]
      · rw [hsv]; simp [Ne.symm hab, Ne.symm he.2]
      · rw [hsv] at ha'
        by_contra hne
        by_cases hae : a' = e
        · subst hae
          simp only [hne, if_false, one_mul, if_true] at ha'
          exact hωinv ha'
        · simp only [hne, hae, if_false, mul_one] at ha'
          exact hω1 ha'.symm
      · rw [hsv]; simp [hb₂.1, hb₂.2.2]
  obtain ⟨t, -, hxt⟩ := S.frame_eq_diagGL hP hx
  have hMd : (Mg : Matrix (Fin d) (Fin d) k) =
      diagonal fun i => (Mg : Matrix (Fin d) (Fin d) k) i i := by
    ext i j
    by_cases hij : i = j
    · subst hij; rw [diagonal_apply_eq]
    · rw [diagonal_apply_ne _ hij]; exact hMdiag i j hij
  have hcomm' : (Mg : Matrix (Fin d) (Fin d) k) * diagonal (fun i => (t i : k)) =
      diagonal (fun i => (t i : k)) * (Mg : Matrix (Fin d) (Fin d) k) := by
    rw [hMd, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  have hcomm : Mg * diagGL d t = diagGL d t * Mg := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_diagGL]
    exact hcomm'
  rw [← hxt, hMg] at hcomm
  have h1 : P * (g * x) * P⁻¹ = P * (x * g) * P⁻¹ := by
    calc P * (g * x) * P⁻¹ = P * g * P⁻¹ * (P * x * P⁻¹) := by group
      _ = P * x * P⁻¹ * (P * g * P⁻¹) := hcomm
      _ = P * (x * g) * P⁻¹ := by group
  simpa using h1

end GSetting

end CFSG.StandardType.GGL45TG
