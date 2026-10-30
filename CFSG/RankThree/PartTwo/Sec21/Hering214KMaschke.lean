module

public import CFSG.RankThree.PartTwo.Sec21.Hering214L3Std
public import CFSG.RankThree.PartTwo.Sec21.Hering214Reduce
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214

open CFSG.Assembly (IsElemAbelian)

section Algebra

variable {M : Type*} [CommGroup M]

theorem eigen_identity (hsq : ∀ x : M, x * x = 1) (σ τ : M →* M)
    (hσ3 : ∀ x, σ (σ (σ x)) = x) (hτ3 : ∀ x, τ (τ (τ x)) = x)
    (hcomm : ∀ x, σ (τ x) = τ (σ x)) {d : M} (hd : d * σ d * σ (σ d) = 1) :
    τ (τ (τ d * σ (σ d)) * σ (τ d * σ (σ d))) * (τ (τ d * σ (σ d)) * σ (τ d * σ (σ d))) = 1 := by
  have h1 : τ d * τ (σ d) * τ (σ (σ d)) = 1 := by
    have := congrArg τ hd
    simpa only [map_mul, map_one] using this
  have h2 : τ (τ d) * τ (τ (σ d)) * τ (τ (σ (σ d))) = 1 := by
    have := congrArg τ h1
    simpa only [map_mul, map_one] using this
  have e : τ (τ (τ d * σ (σ d)) * σ (τ d * σ (σ d))) * (τ (τ d * σ (σ d)) * σ (τ d * σ (σ d))) =
      (d * d) * (τ d * τ (σ d) * τ (σ (σ d))) *
        (τ (τ d) * τ (τ (σ d)) * τ (τ (σ (σ d)))) := by
    simp only [map_mul, hcomm, hσ3, hτ3]
    ac_rfl
  rw [e, h1, h2, hsq d]
  simp

theorem exists_eigenvector (hsq : ∀ x : M, x * x = 1) (σ τ : M →* M)
    (hσ3 : ∀ x, σ (σ (σ x)) = x) (hτ3 : ∀ x, τ (τ (τ x)) = x)
    (hcomm : ∀ x, σ (τ x) = τ (σ x)) {d : M} (hd : d * σ d * σ (σ d) = 1) (hd1 : d ≠ 1) :
    ∃ s : M, s ≠ 1 ∧ s * σ s * σ (σ s) = 1 ∧
      (τ s = s ∨ τ s = σ s ∨ τ s = σ (σ s)) := by
  have hN : ∀ x : M, x * σ x * σ (σ x) = 1 → (τ x) * σ (τ x) * σ (σ (τ x)) = 1 := by
    intro x hx
    have := congrArg τ hx
    simpa only [map_mul, map_one, hcomm] using this
  have hNmul : ∀ x y : M, x * σ x * σ (σ x) = 1 → y * σ y * σ (σ y) = 1 →
      (x * y) * σ (x * y) * σ (σ (x * y)) = 1 := by
    intro x y hx hy
    have e : (x * y) * σ (x * y) * σ (σ (x * y)) =
        (x * σ x * σ (σ x)) * (y * σ y * σ (σ y)) := by
      simp only [map_mul]
      ac_rfl
    rw [e, hx, hy, one_mul]
  have hNσ : ∀ x : M, x * σ x * σ (σ x) = 1 → σ x * σ (σ x) * σ (σ (σ x)) = 1 := by
    intro x hx
    have := congrArg σ hx
    simpa only [map_mul, map_one] using this
  obtain ⟨m2, hm2⟩ : ∃ m2 : M, m2 = τ d * σ (σ d) := ⟨_, rfl⟩
  obtain ⟨m1, hm1⟩ : ∃ m1 : M, m1 = τ m2 * σ m2 := ⟨_, rfl⟩
  have hNd1 : τ d * σ (τ d) * σ (σ (τ d)) = 1 := hN d hd
  have hNm2 : m2 * σ m2 * σ (σ m2) = 1 := by
    rw [hm2]
    exact hNmul _ _ hNd1 (hNσ (σ d) (hNσ d hd))
  have hNm1 : m1 * σ m1 * σ (σ m1) = 1 := by
    rw [hm1]
    exact hNmul _ _ (hN m2 hNm2) (hNσ m2 hNm2)
  by_cases hm2one : m2 = 1
  · refine ⟨d, hd1, hd, Or.inr (Or.inr ?_)⟩
    have h : τ d * σ (σ d) = 1 := by rw [← hm2]; exact hm2one
    have hs2 : σ (σ d) * σ (σ d) = 1 := hsq _
    calc τ d = τ d * (σ (σ d) * σ (σ d)) := by rw [hs2, mul_one]
      _ = (τ d * σ (σ d)) * σ (σ d) := by rw [mul_assoc]
      _ = σ (σ d) := by rw [h, one_mul]
  · by_cases hm1one : m1 = 1
    · refine ⟨m2, hm2one, hNm2, Or.inr (Or.inl ?_)⟩
      have h : τ m2 * σ m2 = 1 := by rw [← hm1]; exact hm1one
      have hs : σ m2 * σ m2 = 1 := hsq _
      calc τ m2 = τ m2 * (σ m2 * σ m2) := by rw [hs, mul_one]
        _ = (τ m2 * σ m2) * σ m2 := by rw [mul_assoc]
        _ = σ m2 := by rw [h, one_mul]
    · refine ⟨m1, hm1one, hNm1, Or.inl ?_⟩
      have h : τ m1 * m1 = 1 := by
        rw [hm1, hm2]
        exact eigen_identity hsq σ τ hσ3 hτ3 hcomm hd
      calc τ m1 = τ m1 * (m1 * m1) := by rw [hsq m1, mul_one]
        _ = (τ m1 * m1) * m1 := by rw [mul_assoc]
        _ = m1 := by rw [h, one_mul]

end Algebra

section Lift

variable {X : Type} [Group X]

theorem apply_apply_apply_of_pow_three {ρ : MulAut X} (h : ρ ^ 3 = 1) (x : X) :
    ρ (ρ (ρ x)) = x := by
  have := congrArg (fun f : MulAut X => f x) h
  simpa [pow_succ, MulAut.mul_apply] using this

theorem closure_pair_eq_of_card_nine {Ē : Subgroup (MulAut X)} (hE3 : IsElemAbelian 3 Ē)
    (hE9 : Nat.card Ē = 9) {σ τ : MulAut X} (hσ : σ ∈ Ē) (hτ : τ ∈ Ē) (hσ1 : σ ≠ 1)
    (hτσ : τ ∉ Subgroup.zpowers σ) : Subgroup.closure ({σ, τ} : Set (MulAut X)) = Ē := by
  have hσ3 : σ ^ 3 = 1 := hE3.2 σ hσ
  have hord : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ1
  set H : Subgroup (MulAut X) := Subgroup.closure ({σ, τ} : Set (MulAut X)) with hH
  have hHE : H ≤ Ē := by
    rw [hH, Subgroup.closure_le]
    rintro x (rfl | hx)
    · exact hσ
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hτ
  have hσH : σ ∈ H := Subgroup.subset_closure (Set.mem_insert _ _)
  have hτH : τ ∈ H := Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hzH : Subgroup.zpowers σ ≤ H := (Subgroup.zpowers_le).2 hσH
  have hzcard : Nat.card (Subgroup.zpowers σ) = 3 := by rw [Nat.card_zpowers, hord]
  have hdvd9 : Nat.card H ∣ 9 := hE9 ▸ Subgroup.card_dvd_of_le hHE
  have hdvd3 : 3 ∣ Nat.card H := hzcard ▸ Subgroup.card_dvd_of_le hzH
  have hne3 : Nat.card H ≠ 3 := by
    intro h3
    have hfin : Finite H := Nat.finite_of_card_ne_zero (by omega)
    have heq : Subgroup.zpowers σ = H :=
      Subgroup.eq_of_le_of_card_ge hzH (by rw [hzcard, h3])
    exact hτσ (heq ▸ hτH)
  have h9 : Nat.card H = 9 := by
    obtain ⟨i, hi, hHi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1
      (show Nat.card H ∣ 3 ^ 2 by simpa using hdvd9)
    interval_cases i
    · rw [pow_zero] at hHi
      rw [hHi] at hdvd3
      omega
    · rw [pow_one] at hHi
      exact absurd hHi hne3
    · rw [hHi]
      norm_num
  have hfin : Finite Ē := Nat.finite_of_card_ne_zero (by omega)
  exact Subgroup.eq_of_le_of_card_ge hHE (by rw [hE9, h9])

theorem eInvFour_of_elemAbelian_two {Ē : Subgroup (MulAut X)} (hE3 : IsElemAbelian 3 Ē)
    (hE9 : Nat.card Ē = 9) {R : Subgroup X} (hR : IsElemAbelian 2 R)
    (hinv : ∀ σ ∈ Ē, ∀ r ∈ R, σ r ∈ R) (hnt : ∃ σ ∈ Ē, ∃ r ∈ R, σ r ≠ r) :
    EInvFour X Ē := by
  classical
  obtain ⟨σ, hσE, r, hrR, hσr⟩ := hnt
  have hσ3 : σ ^ 3 = 1 := hE3.2 σ hσE
  have hσ1 : σ ≠ 1 := fun h => hσr (by rw [h]; rfl)
  obtain ⟨τ, hτE, hτσ⟩ : ∃ τ ∈ Ē, τ ∉ Subgroup.zpowers σ := by
    by_contra hcon
    push Not at hcon
    have hle : Ē ≤ Subgroup.zpowers σ := fun x hx => hcon x hx
    have hord : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ1
    have hzcard : Nat.card (Subgroup.zpowers σ) = 3 := by rw [Nat.card_zpowers, hord]
    have hfin : Finite (Subgroup.zpowers σ) := Nat.finite_of_card_ne_zero (by omega)
    have := Subgroup.card_le_of_le hle
    omega
  have hτ3 : τ ^ 3 = 1 := hE3.2 τ hτE
  have hστ : σ * τ = τ * σ := by
    have := hE3.1.is_comm.comm ⟨σ, hσE⟩ ⟨τ, hτE⟩
    exact congrArg Subtype.val this
  have hgen : Subgroup.closure ({σ, τ} : Set (MulAut X)) = Ē :=
    closure_pair_eq_of_card_nine hE3 hE9 hσE hτE hσ1 hτσ
  letI : CommGroup R := { (inferInstance : Group R) with mul_comm := hR.1.is_comm.comm }
  have mk : ∀ ρ ∈ Ē, ∃ f : R →* R, ∀ x : R, (f x : X) = ρ x := fun ρ hρ =>
    ⟨(ρ.toMonoidHom.comp R.subtype).codRestrict R (fun x => hinv ρ hρ x x.2), fun x => rfl⟩
  obtain ⟨σR, hσR⟩ := mk σ hσE
  obtain ⟨τR, hτR⟩ := mk τ hτE
  have hsqR : ∀ x : R, x * x = 1 := fun x => by
    apply Subtype.ext
    have := hR.2 x x.2
    simpa [pow_two] using this
  have hσ3R : ∀ x : R, σR (σR (σR x)) = x := fun x => by
    apply Subtype.ext
    rw [hσR, hσR, hσR]
    exact apply_apply_apply_of_pow_three hσ3 x
  have hτ3R : ∀ x : R, τR (τR (τR x)) = x := fun x => by
    apply Subtype.ext
    rw [hτR, hτR, hτR]
    exact apply_apply_apply_of_pow_three hτ3 x
  have hcommR : ∀ x : R, σR (τR x) = τR (σR x) := fun x => by
    apply Subtype.ext
    rw [hσR, hτR, hτR, hσR]
    have := congrArg (fun f : MulAut X => f x) hστ
    simpa [MulAut.mul_apply] using this
  set a : R := ⟨r, hrR⟩ with ha
  have hσa : σR a ≠ a := fun h => hσr (by
    have := congrArg Subtype.val h
    rw [hσR] at this
    exact this)
  have hdN : (a * σR a) * σR (a * σR a) * σR (σR (a * σR a)) = 1 := by
    have e : (a * σR a) * σR (a * σR a) * σR (σR (a * σR a)) =
        (a * a) * (σR a * σR a) * (σR (σR a) * σR (σR a)) := by
      simp only [map_mul, hσ3R]
      ac_rfl
    rw [e, hsqR a, hsqR (σR a), hsqR (σR (σR a))]
    simp
  have hd1 : a * σR a ≠ 1 := by
    intro h
    apply hσa
    have : σR a = a⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this]
    exact inv_eq_of_mul_eq_one_left (hsqR a)
  obtain ⟨s, hs1, hsN, hτs⟩ := exists_eigenvector hsqR σR τR hσ3R hτ3R hcommR hdN hd1
  have hσs : σR s ≠ s := by
    intro h
    apply hs1
    have : s * σR s * σR (σR s) = s := by
      rw [h, h, hsqR s, one_mul]
    rw [← this, hsN]
  set u : X := (s : X) with hu
  set v : X := σ u with hv
  have hvR : v = ((σR s : R) : X) := by rw [hσR]
  have huu : u * u = 1 := congrArg Subtype.val (hsqR s)
  have hvv : v * v = 1 := by
    rw [hvR]
    exact congrArg Subtype.val (hsqR (σR s))
  have huv : u * v = v * u := by
    rw [hvR]
    exact congrArg Subtype.val (mul_comm s (σR s))
  have hu1 : u ≠ 1 := fun h => hs1 (Subtype.ext h)
  have hv1 : v ≠ 1 := fun h => hu1 (by
    have : σ u = σ 1 := by rw [← hv, h, map_one]
    exact σ.injective this)
  have huv' : u ≠ v := fun h => hσs (Subtype.ext (by rw [← hvR]; exact h.symm))
  have hσv : σ v = u * v := by
    have h3 : u * v * σ v = 1 := by
      have := congrArg Subtype.val hsN
      simpa [hσR, hvR] using this
    have h4 : (u * v) * (u * v) = 1 := by
      calc (u * v) * (u * v) = u * (v * u) * v := by simp only [mul_assoc]
        _ = u * (u * v) * v := by rw [← huv]
        _ = (u * u) * (v * v) := by simp only [mul_assoc]
        _ = 1 := by rw [huu, hvv, one_mul]
    have h5 : σ v = (u * v)⁻¹ := eq_inv_of_mul_eq_one_right h3
    rw [h5]
    exact (inv_eq_of_mul_eq_one_left h4)
  set W : Subgroup X := Subgroup.closure ({u, v} : Set X) with hW
  have huW : u ∈ W := Subgroup.subset_closure (Set.mem_insert _ _)
  have hvW : v ∈ W := Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hstab : ∀ ρ : MulAut X, ρ u ∈ W → ρ v ∈ W → ∀ w ∈ W, ρ w ∈ W := by
    intro ρ h1 h2 w hw
    have hle : W.map ρ.toMonoidHom ≤ W := by
      rw [hW, MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨x, hx, rfl⟩
      rcases hx with rfl | hx
      · exact h1
      · rw [Set.mem_singleton_iff] at hx
        subst hx
        exact h2
    exact hle ⟨w, hw, rfl⟩
  have hσW : ∀ w ∈ W, σ w ∈ W :=
    hstab σ (by rw [← hv]; exact hvW) (by rw [hσv]; exact W.mul_mem huW hvW)
  have hτuW : τ u ∈ W := by
    rcases hτs with h | h | h
    · have : τ u = u := by rw [← hτR]; exact congrArg Subtype.val h
      rw [this]; exact huW
    · have : τ u = v := by rw [← hτR, h, hvR]
      rw [this]; exact hvW
    · have : τ u = σ v := by
        rw [← hτR, h, hv, hσR, hσR]
      rw [this, hσv]; exact W.mul_mem huW hvW
  have hτvW : τ v ∈ W := by
    have : τ v = σ (τ u) := by
      have := congrArg (fun f : MulAut X => f u) hστ
      simp only [MulAut.mul_apply] at this
      rw [hv]
      exact this.symm
    rw [this]
    exact hσW _ hτuW
  have hτW : ∀ w ∈ W, τ w ∈ W := hstab τ hτuW hτvW
  have hĒW : ∀ ρ ∈ Ē, ∀ w ∈ W, ρ w ∈ W := by
    intro ρ hρ
    rw [← hgen] at hρ
    induction hρ using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | hx
      · exact hσW
      · rw [Set.mem_singleton_iff] at hx
        subst hx
        exact hτW
    | one => intro w hw; simpa using hw
    | mul x y hx' hy' hx hy =>
      intro w hw
      have := hx _ (hy w hw)
      simpa [MulAut.mul_apply] using this
    | inv x hx' hx =>
      intro w hw
      have hxE : x ∈ Ē := by rw [← hgen]; exact hx'
      have hx3 : x ^ 3 = 1 := hE3.2 x hxE
      have hxinv : x⁻¹ = x * x := by
        apply inv_eq_of_mul_eq_one_right
        calc x * (x * x) = x * x * x := (mul_assoc _ _ _).symm
          _ = x ^ 3 := by simp [pow_succ]
          _ = 1 := hx3
      rw [hxinv]
      have := hx _ (hx w hw)
      simpa [MulAut.mul_apply] using this
  refine ⟨W, isElemAbelian_closure_pair huu hvv huv, card_closure_pair huu hvv huv hu1 hv1 huv',
    hĒW, σ, hσE, u, huW, ?_⟩
  intro h
  apply huv'
  rw [hv]
  exact h.symm

end Lift

end CFSG.RankThree.PartTwo.Sec21.Hering214
