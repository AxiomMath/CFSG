module

public import CFSG.ClassicalInvolution.Uniform.U5Util

public section

namespace CFSG.RankThree.PartTwo.Sec17.J2CoverE8

open CFSG.Open

variable {X Q : Type} [Group X] [Group Q]

@[expose] def liftCent (π : X →* Q) (x : X) : Subgroup X :=
  (Subgroup.centralizer ({π x} : Set Q)).comap π

theorem mem_liftCent {π : X →* Q} {x y : X} :
    y ∈ liftCent π x ↔ π x * π y = π y * π x := by
  rw [liftCent, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

theorem commutator_mem_ker {π : X →* Q} {x y : X} (h : π x * π y = π y * π x) :
    x * y * x⁻¹ * y⁻¹ ∈ π.ker := by
  rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, h]
  group

@[expose] def commHom (π : X →* Q) (hker : π.ker ≤ Subgroup.center X) (x : X) :
    liftCent π x →* Subgroup.center X :=
  MonoidHom.mk' (fun y => ⟨x * y * x⁻¹ * (y : X)⁻¹,
      hker (commutator_mem_ker (mem_liftCent.mp y.2))⟩) fun y y' => by
    apply Subtype.ext
    set c' : X := x * (y' : X) * x⁻¹ * (y' : X)⁻¹ with hc'
    have hc'Z : c' ∈ Subgroup.center X := hker (commutator_mem_ker (mem_liftCent.mp y'.2))
    have hcomm : ∀ g : X, g * c' = c' * g := fun g => (Subgroup.mem_center_iff.mp hc'Z g)
    show x * ((y : X) * y') * x⁻¹ * ((y : X) * y')⁻¹ = x * y * x⁻¹ * (y : X)⁻¹ * c'
    have h1 : (y' : X) * x⁻¹ * (y' : X)⁻¹ = x⁻¹ * c' := by rw [hc']; group
    calc x * ((y : X) * y') * x⁻¹ * ((y : X) * y')⁻¹
        = x * y * ((y' : X) * x⁻¹ * (y' : X)⁻¹) * (y : X)⁻¹ := by group
      _ = x * y * (x⁻¹ * c') * (y : X)⁻¹ := by rw [h1]
      _ = x * y * x⁻¹ * ((y : X)⁻¹ * c') := by rw [hcomm (y : X)⁻¹]; group
      _ = x * y * x⁻¹ * (y : X)⁻¹ * c' := by group

theorem commHom_apply (π : X →* Q) (hker : π.ker ≤ Subgroup.center X) (x : X)
    (y : liftCent π x) : (commHom π hker x y : X) = x * y * x⁻¹ * (y : X)⁻¹ := rfl

theorem commHom_ker (π : X →* Q) (hker : π.ker ≤ Subgroup.center X) (x : X)
    (w : liftCent π x) (hw : (w : X) ∈ π.ker) : commHom π hker x w = 1 := by
  apply Subtype.ext
  rw [commHom_apply]
  have := Subgroup.mem_center_iff.mp (hker hw) x
  rw [Subgroup.coe_one, this]
  group

theorem center_comm (a b : Subgroup.center X) : a * b = b * a :=
  Subtype.ext (Subgroup.mem_center_iff.mp b.2 a)

theorem commute_lifts (π : X →* Q) (hker : π.ker ≤ Subgroup.center X) {x t u₁ u₂ : X}
    (hxt : π x * π t = π t * π x) (hx1 : π x * π u₁ = π u₁ * π x)
    (hx2 : π x * π u₂ = π u₂ * π x)
    (ht1 : π t * π u₁ * (π t)⁻¹ = π u₂) (ht2 : π t * π u₂ * (π t)⁻¹ = π u₁ * π u₂) :
    x * u₁ = u₁ * x ∧ x * u₂ = u₂ * x := by
  set f := commHom π hker x with hf
  set T : liftCent π x := ⟨t, mem_liftCent.mpr hxt⟩
  set U₁ : liftCent π x := ⟨u₁, mem_liftCent.mpr hx1⟩
  set U₂ : liftCent π x := ⟨u₂, mem_liftCent.mpr hx2⟩
  have hkerH : ∀ w : liftCent π x, (w : X) ∈ π.ker → f w = 1 := commHom_ker π hker x
  have hw₁ : ((T * U₁ * T⁻¹ * U₂⁻¹ : liftCent π x) : X) ∈ π.ker := by
    rw [MonoidHom.mem_ker]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, T, U₁, U₂]
    rw [ht1, mul_inv_cancel]
  have hw₂ : ((T * U₂ * T⁻¹ * (U₁ * U₂)⁻¹ : liftCent π x) : X) ∈ π.ker := by
    rw [MonoidHom.mem_ker]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, T, U₁, U₂]
    rw [ht2, mul_inv_rev, ← mul_assoc, mul_inv_cancel_right, mul_inv_cancel]
  have e₁ := hkerH _ hw₁
  have e₂ := hkerH _ hw₂
  simp only [map_mul, map_inv] at e₁ e₂
  have h₂ : f U₂ = f U₁ := by
    have : f T * f U₁ * (f T)⁻¹ * (f U₂)⁻¹ = 1 := e₁
    rw [center_comm (f T), mul_inv_cancel_right, mul_inv_eq_one] at this
    exact this.symm
  have h₁ : f U₁ = 1 := by
    have : f T * f U₂ * (f T)⁻¹ * (f U₁ * f U₂)⁻¹ = 1 := e₂
    rw [center_comm (f T), mul_inv_cancel_right, mul_inv_eq_one, h₂] at this
    have h' : f U₁ * f U₁ = f U₁ * 1 := by rw [mul_one]; exact this.symm
    exact mul_left_cancel h'
  have hu₁ : x * u₁ * x⁻¹ * u₁⁻¹ = 1 := by
    have := congrArg Subtype.val h₁
    rwa [commHom_apply] at this
  have hu₂ : x * u₂ * x⁻¹ * u₂⁻¹ = 1 := by
    have := congrArg Subtype.val (h₂.trans h₁)
    rwa [commHom_apply] at this
  constructor
  · rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hu₁
    exact hu₁
  · rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hu₂
    exact hu₂

theorem sq_eq_one_of_card_le_two [Finite X] {K : Subgroup X} (hK : Nat.card K ≤ 2) {k : X}
    (hk : k ∈ K) : k ^ 2 = 1 := by
  have hd : orderOf k ∣ Nat.card K := by
    rw [← Subgroup.orderOf_mk k hk]
    exact orderOf_dvd_natCard _
  have hpos : 0 < Nat.card K := Nat.card_pos
  have h2 : orderOf k ∣ 2 := by
    interval_cases h : Nat.card K
    · exact hd.trans (one_dvd 2)
    · exact hd
  exact orderOf_dvd_iff_pow_eq_one.mp h2

theorem eq_of_card_le_two [Finite X] {K : Subgroup X} (hK : Nat.card K ≤ 2) {k k' : X}
    (hk : k ∈ K) (hk' : k' ∈ K) (h1 : k ≠ 1) (h1' : k' ≠ 1) : k = k' := by
  by_contra hne
  let f : Fin 3 → K := ![1, ⟨k, hk⟩, ⟨k', hk'⟩]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f, Subtype.ext_iff, eq_comm]
  have := Nat.card_le_card_of_injective f hf
  simp at this
  omega

theorem lift_four_group [Finite X] (π : X →* Q) (hker : π.ker ≤ Subgroup.center X)
    (hcard : Nat.card π.ker ≤ 2) {v₁ v₂ s : X} (hv : π v₁ ^ 2 = 1)
    (hs₁ : π s * π v₁ * (π s)⁻¹ = π v₂) (hs₂ : π s * π v₂ * (π s)⁻¹ = π v₁ * π v₂) :
    v₁ ^ 2 ∈ π.ker ∧ v₂ ^ 2 = v₁ ^ 2 ∧ v₁ * v₂ = v₁ ^ 2 * (v₂ * v₁) := by
  have hε : v₁ ^ 2 ∈ π.ker := by rw [MonoidHom.mem_ker, map_pow, hv]
  set ε := v₁ ^ 2 with hεdef
  have hεc : ∀ g : X, g * ε = ε * g := fun g => Subgroup.mem_center_iff.mp (hker hε) g
  have hε2 : ε ^ 2 = 1 := sq_eq_one_of_card_le_two hcard hε
  have hsq : ∀ {a b : X}, π s * π a * (π s)⁻¹ = π b → a ^ 2 = ε → b ^ 2 = ε := by
    intro a b hab ha
    set k := (s * a * s⁻¹)⁻¹ * b with hk
    have hkK : k ∈ π.ker := by
      rw [MonoidHom.mem_ker, hk, map_mul, map_inv, map_mul, map_mul, map_inv, hab, inv_mul_cancel]
    have hkc : Commute (s * a * s⁻¹) k := (Subgroup.mem_center_iff.mp (hker hkK) _)
    have hk2 : k ^ 2 = 1 := sq_eq_one_of_card_le_two hcard hkK
    have hb : b = s * a * s⁻¹ * k := by rw [hk]; group
    rw [hb, hkc.mul_pow, hk2, mul_one, conj_pow, ha, hεc, mul_inv_cancel_right]
  have hv₂ : v₂ ^ 2 = ε := hsq hs₁ rfl
  have hv₁₂ : (v₁ * v₂) ^ 2 = ε := hsq (b := v₁ * v₂) (by rw [map_mul]; exact hs₂) hv₂
  refine ⟨hε, hv₂, ?_⟩
  have hi : ∀ {w : X}, w ^ 2 = ε → w⁻¹ = ε * w := by
    intro w hw
    rw [inv_eq_iff_mul_eq_one, ← mul_assoc, hεc w, mul_assoc, ← sq, hw, ← sq, hε2]
  have e1 : v₁ * v₂ = ε * (v₂⁻¹ * v₁⁻¹) := by
    have : v₁ * v₂ * (v₁ * v₂) = ε := by rw [← sq]; exact hv₁₂
    calc v₁ * v₂ = v₁ * v₂ * (v₁ * v₂) * (v₂⁻¹ * v₁⁻¹) := by group
      _ = ε * (v₂⁻¹ * v₁⁻¹) := by rw [this]
  rw [e1, hi hv₂, hi rfl]
  have hεε : ε * ε = 1 := by rw [← sq]; exact hε2
  calc ε * (ε * v₂ * (ε * v₁)) = ε * ε * (v₂ * ε) * v₁ := by simp only [mul_assoc]
    _ = ε * ε * (ε * v₂) * v₁ := by rw [hεc v₂]
    _ = ε * ε * ε * (v₂ * v₁) := by simp only [mul_assoc]
    _ = ε * (v₂ * v₁) := by rw [hεε, one_mul]

theorem exists_elemAbelian_eight_of_lifts [Finite X] (π : X →* Q)
    (hker : π.ker ≤ Subgroup.center X) (hcard : Nat.card π.ker ≤ 2) {v₁ v₂ s u₁ u₂ t : X}
    (hv : π v₁ ^ 2 = 1) (hs₁ : π s * π v₁ * (π s)⁻¹ = π v₂)
    (hs₂ : π s * π v₂ * (π s)⁻¹ = π v₁ * π v₂)
    (hu : π u₁ ^ 2 = 1) (ht₁ : π t * π u₁ * (π t)⁻¹ = π u₂)
    (ht₂ : π t * π u₂ * (π t)⁻¹ = π u₁ * π u₂)
    (h11 : π v₁ * π u₁ = π u₁ * π v₁) (h12 : π v₁ * π u₂ = π u₂ * π v₁)
    (h21 : π v₂ * π u₁ = π u₁ * π v₂) (h22 : π v₂ * π u₂ = π u₂ * π v₂)
    (h1t : π v₁ * π t = π t * π v₁) (h2t : π v₂ * π t = π t * π v₂)
    (hd : π v₁ ≠ 1 ∧ π v₂ ≠ 1 ∧ π v₂ ≠ π v₁ ∧ π v₁ * π v₂ ≠ 1 ∧
      π u₁ ≠ 1 ∧ π u₂ ≠ 1 ∧ π u₂ ≠ π u₁ ∧ π u₁ * π u₂ ≠ 1 ∧
      π u₁ ≠ π v₁ ∧ π u₁ ≠ π v₂ ∧ π u₁ ≠ π v₁ * π v₂ ∧
      π v₁ * π u₁ ≠ 1 ∧ π v₂ * π u₂ ≠ 1 ∧ π v₂ * π u₂ ≠ π v₁ * π u₁ ∧
      π v₁ * π u₁ * (π v₂ * π u₂) ≠ 1) :
    ∃ E : Subgroup X, IsElemAbelian 2 E ∧ Nat.card E = 8 := by
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15⟩ := hd
  obtain ⟨hεK, hv₂, hv₁₂⟩ := lift_four_group π hker hcard hv hs₁ hs₂
  obtain ⟨hε'K, hu₂, hu₁₂⟩ := lift_four_group π hker hcard hu ht₁ ht₂
  set ε := v₁ ^ 2 with hε
  set ε' := u₁ ^ 2 with hε'
  obtain ⟨c11, c12⟩ := commute_lifts π hker h1t h11 h12 ht₁ ht₂
  obtain ⟨c21, c22⟩ := commute_lifts π hker h2t h21 h22 ht₁ ht₂
  have hcen : ∀ {k : X}, k ∈ π.ker → ∀ g : X, g * k = k * g :=
    fun hk g => Subgroup.mem_center_iff.mp (hker hk) g
  have hsq : ∀ {k : X}, k ∈ π.ker → k * k = 1 := fun hk => by
    rw [← sq]; exact sq_eq_one_of_card_le_two hcard hk
  have hne : ∀ {a b : X}, π a ≠ π b → a ≠ b := fun h hab => h (by rw [hab])
  have hne1 : ∀ {a : X}, π a ≠ 1 → a ≠ 1 := fun h ha => h (by rw [ha, map_one])
  have hπk : ∀ {k : X}, k ∈ π.ker → π k = 1 := fun hk => (MonoidHom.mem_ker).mp hk
  by_cases hε1 : ε = 1 <;> by_cases hε'1 : ε' = 1
  ·
    have hv₁ : v₁ * v₁ = 1 := by rw [← sq]; exact hε1
    have hv₂' : v₂ * v₂ = 1 := by rw [← sq, hv₂]; exact hε1
    have hu₁ : u₁ * u₁ = 1 := by rw [← sq]; exact hε'1
    have c12' : v₁ * v₂ = v₂ * v₁ := by rw [hv₁₂, hε1, one_mul]
    exact CFSG.ClassicalInvolution.Uniform.exists_isElemAbelian_card_eight hv₁ hv₂' hu₁ c12' c11
      c21 (hne1 d1) (hne1 d2) (hne1 d5) (hne d3) (hne d9) (hne d10)
      (hne (by rw [map_mul]; exact d11))
  ·
    have hv₁ : v₁ * v₁ = 1 := by rw [← sq]; exact hε1
    have hv₂' : v₂ * v₂ = 1 := by rw [← sq, hv₂]; exact hε1
    have c12' : v₁ * v₂ = v₂ * v₁ := by rw [hv₁₂, hε1, one_mul]
    refine CFSG.ClassicalInvolution.Uniform.exists_isElemAbelian_card_eight hv₁ hv₂'
      (hsq hε'K) c12' (hcen hε'K v₁) (hcen hε'K v₂) (hne1 d1) (hne1 d2) hε'1 (hne d3)
      (hne ?_) (hne ?_) (hne ?_)
    · rw [hπk hε'K]; exact d1.symm
    · rw [hπk hε'K]; exact d2.symm
    · rw [hπk hε'K, map_mul]; exact d4.symm
  ·
    have hu₁ : u₁ * u₁ = 1 := by rw [← sq]; exact hε'1
    have hu₂' : u₂ * u₂ = 1 := by rw [← sq, hu₂]; exact hε'1
    have c12' : u₁ * u₂ = u₂ * u₁ := by rw [hu₁₂, hε'1, one_mul]
    refine CFSG.ClassicalInvolution.Uniform.exists_isElemAbelian_card_eight hu₁ hu₂'
      (hsq hεK) c12' (hcen hεK u₁) (hcen hεK u₂) (hne1 d5) (hne1 d6) hε1 (hne d7)
      (hne ?_) (hne ?_) (hne ?_)
    · rw [hπk hεK]; exact d5.symm
    · rw [hπk hεK]; exact d6.symm
    · rw [hπk hεK, map_mul]; exact d8.symm
  ·
    have hee : ε = ε' := eq_of_card_le_two hcard hεK hε'K hε1 hε'1
    have hεε : ε * ε = 1 := hsq hεK
    have hx : v₁ * u₁ * (v₁ * u₁) = 1 := by
      calc v₁ * u₁ * (v₁ * u₁) = v₁ * (u₁ * v₁) * u₁ := by group
        _ = v₁ * (v₁ * u₁) * u₁ := by rw [c11]
        _ = v₁ ^ 2 * u₁ ^ 2 := by rw [sq, sq]; group
        _ = 1 := by rw [← hε, ← hε', ← hee, hεε]
    have hy : v₂ * u₂ * (v₂ * u₂) = 1 := by
      calc v₂ * u₂ * (v₂ * u₂) = v₂ * (u₂ * v₂) * u₂ := by group
        _ = v₂ * (v₂ * u₂) * u₂ := by rw [c22]
        _ = v₂ ^ 2 * u₂ ^ 2 := by rw [sq, sq]; group
        _ = 1 := by rw [hv₂, hu₂, ← hee, hεε]
    have hxy : v₁ * u₁ * (v₂ * u₂) = v₂ * u₂ * (v₁ * u₁) := by
      calc v₁ * u₁ * (v₂ * u₂) = v₁ * (u₁ * v₂) * u₂ := by group
        _ = v₁ * (v₂ * u₁) * u₂ := by rw [c21]
        _ = v₁ * v₂ * (u₁ * u₂) := by group
        _ = ε * (v₂ * v₁) * (ε' * (u₂ * u₁)) := by rw [hv₁₂, hu₁₂]
        _ = ε * (v₂ * v₁ * ε) * (u₂ * u₁) := by rw [← hee]; simp only [mul_assoc]
        _ = ε * (ε * (v₂ * v₁)) * (u₂ * u₁) := by rw [hcen hεK (v₂ * v₁)]
        _ = ε * ε * (v₂ * v₁ * (u₂ * u₁)) := by simp only [mul_assoc]
        _ = v₂ * (v₁ * u₂) * u₁ := by rw [hεε, one_mul]; group
        _ = v₂ * (u₂ * v₁) * u₁ := by rw [c12]
        _ = v₂ * u₂ * (v₁ * u₁) := by group
    refine CFSG.ClassicalInvolution.Uniform.exists_isElemAbelian_card_eight hx hy (hsq hεK) hxy
      (hcen hεK _) (hcen hεK _) (hne1 (by rw [map_mul]; exact d12))
      (hne1 (by rw [map_mul]; exact d13)) hε1 (hne (by rw [map_mul, map_mul]; exact d14))
      (hne ?_) (hne ?_) (hne ?_)
    · rw [hπk hεK, map_mul]; exact d12.symm
    · rw [hπk hεK, map_mul]; exact d13.symm
    · rw [hπk hεK, map_mul, map_mul, map_mul]; exact d15.symm

end CFSG.RankThree.PartTwo.Sec17.J2CoverE8

end
