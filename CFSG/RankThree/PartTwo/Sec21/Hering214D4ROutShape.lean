module

public import CFSG.RankThree.PartTwo.Sec21.Hering214D4RLine
public import CFSG.RankThree.PartTwo.Sec21.Hering214D4RRefl
public import CFSG.RankThree.PartTwo.Sec4.E27.D4Shape
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityAB

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214

open CFSG.Assembly (IsElemAbelian)
open CFSG.RankThree.PartTwo.Sec19
open CFSG.ComponentClassification
open scoped commutatorElement

section OutShape


variable {n : ℕ} {F : Type} [Field F] [Finite F] {σ : F ≃+* F}

theorem outer_reflection_shape (P : D4Par n F σ) {Ē : Subgroup (MulAut (C0 σ))}
    (hE3 : IsElemAbelian 3 Ē) (hE9 : Nat.card Ē = 9)
    (hout : ¬ Ē ≤ (MulAut.conj : C0 σ →* MulAut (C0 σ)).range) (hR : ReflectsE (C0 σ) Ē) :
    ∃ (β : MulAut (C0 σ)) (g x : C0 σ), β ∈ Ē ∧ MulAut.conj g ∈ Ē ∧ β ≠ 1 ∧ β ^ 3 = 1 ∧
      β ∉ (MulAut.conj : C0 σ →* MulAut (C0 σ)).range ∧ g ≠ 1 ∧ g ^ 3 = 1 ∧
      MulAut.conj g ∉ Subgroup.zpowers β ∧ β g = g ∧ β x = x ∧ x * g * x⁻¹ = g⁻¹ := by
  classical
  have hn1 := P.one_le
  obtain ⟨x, ε₁, hε₁, ε₂, hε₂, h1, h2, hnorm, hfix, hinv⟩ := hR
  haveI : IsMulCommutative ↥Ē := hE3.1
  haveI : Finite ↥Ē := Nat.finite_of_card_ne_zero (by rw [hE9]; norm_num)
  have hinj := conj_injective_C0 σ n hn1 P.card P.frob
  have hε₁3 : ε₁ ^ 3 = 1 := hE3.2 ε₁ hε₁
  have hε₂3 : ε₂ ^ 3 = 1 := hE3.2 ε₂ hε₂
  have hε₂₁ : ε₂ ∉ Subgroup.zpowers ε₁ := not_mem_zpowers_of_inverts hfix hinv hε₂3 h2
  have hgen := closure_pair_eq_of_card_nine hE3 hE9 hε₁ hε₂ h1 hε₂₁
  obtain ⟨Θ, hΘ, hker, -⟩ := Sec4.E27.exists_theta σ n hn1 P.card P.frob
  have hΘc : ∀ y : C0 σ, Θ (MulAut.conj y) = 1 := fun y => by
    have : MulAut.conj y ∈ Θ.ker := by rw [hker]; exact ⟨y, rfl⟩
    exact this
  obtain ⟨c, hc⟩ : ∃ c : MulAut (C0 σ), c = MulAut.conj x := ⟨_, rfl⟩
  rw [← hc] at hnorm hfix hinv
  have hΘc' : Θ c = 1 := by rw [hc]; exact hΘc x
  let φ₀ : ↥Ē →* ↥Ē :=
    { toFun := fun e => ⟨c * e * c⁻¹, hnorm e e.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        show c * ((a : MulAut (C0 σ)) * b) * c⁻¹ = (c * a * c⁻¹) * (c * b * c⁻¹)
        group) }
  have hφ₀inj : Function.Injective φ₀ := by
    intro a b hab
    have := congrArg Subtype.val hab
    have h' : c * (a : MulAut (C0 σ)) * c⁻¹ = c * b * c⁻¹ := this
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h'))
  let φ : MulAut ↥Ē :=
    MulEquiv.ofBijective φ₀ ⟨hφ₀inj, Finite.injective_iff_surjective.mp hφ₀inj⟩
  have hφapp : ∀ e : ↥Ē, ((φ e : ↥Ē) : MulAut (C0 σ)) = c * e * c⁻¹ := fun e => rfl
  have hcc : Ē ≤ Subgroup.centralizer ({c * c} : Set (MulAut (C0 σ))) := by
    rw [← hgen, Subgroup.closure_le]
    rintro y (rfl | hy)
    · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      have e2 : c * c * y * (c * c)⁻¹ = y := by
        calc c * c * y * (c * c)⁻¹ = c * (c * y * c⁻¹) * c⁻¹ := by group
          _ = y := by rw [hfix, hfix]
      exact (mul_inv_eq_iff_eq_mul.mp e2).symm
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      have e2 : c * c * y * (c * c)⁻¹ = y := by
        calc c * c * y * (c * c)⁻¹ = c * (c * y * c⁻¹) * c⁻¹ := by group
          _ = c * y⁻¹ * c⁻¹ := by rw [hinv]
          _ = (c * y * c⁻¹)⁻¹ := by group
          _ = y := by rw [hinv, inv_inv]
      exact (mul_inv_eq_iff_eq_mul.mp e2).symm
  have hφ2 : φ * φ = 1 := by
    refine MulEquiv.ext fun e => Subtype.ext ?_
    show c * (c * (e : MulAut (C0 σ)) * c⁻¹) * c⁻¹ = e
    have h' : (c * c) * (e : MulAut (C0 σ)) = e * (c * c) :=
      Subgroup.mem_centralizer_iff.mp (hcc e.2) (c * c) rfl
    calc c * (c * (e : MulAut (C0 σ)) * c⁻¹) * c⁻¹ = (c * c) * e * (c * c)⁻¹ := by group
      _ = e := by rw [h']; group
  have hφ1 : φ ≠ 1 := by
    intro hφ
    have h' := congrArg (fun f : MulAut ↥Ē => ((f ⟨ε₂, hε₂⟩ : ↥Ē) : MulAut (C0 σ))) hφ
    simp only [hφapp, MulAut.one_apply] at h'
    rw [hinv] at h'
    apply h2
    have h3 : ε₂ * ε₂ = 1 := by
      have := congrArg (fun y => ε₂ * y) h'
      simpa using this.symm
    calc ε₂ = ε₂ ^ 3 * (ε₂ * ε₂)⁻¹ := by group
      _ = 1 := by rw [hε₂3, h3]; simp
  let Θ' : ↥Ē →* (F ≃+* F) := Θ.comp Ē.subtype
  let ℓ : Subgroup ↥Ē := Θ'.ker
  have hℓmem : ∀ e : ↥Ē, e ∈ ℓ ↔ Θ (e : MulAut (C0 σ)) = 1 := fun e => MonoidHom.mem_ker
  have hσ3 : σ ^ 3 = 1 := nf1_sigma_pow_three σ n P.card P.frob
  have hσ1 : σ ≠ 1 := nf1_sigma_ne_one σ n hn1 P.card P.frob
  have hle : Θ'.range ≤ Subgroup.zpowers σ := by
    rintro _ ⟨e, rfl⟩
    have hψ : Θ (e : MulAut (C0 σ)) ^ 3 = 1 := by rw [← map_pow, hE3.2 e e.2, map_one]
    show Θ (e : MulAut (C0 σ)) ∈ Subgroup.zpowers σ
    rcases Sec4.E27.gal_cube_cases σ n hn1 P.card P.frob _ hψ with h | h | h
    · rw [h]; exact one_mem _
    · rw [h]; exact Subgroup.mem_zpowers σ
    · rw [h]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers σ) 2
  have hrange_ne : Θ'.range ≠ ⊥ := by
    obtain ⟨a, haE, haI⟩ := SetLike.not_le_iff_exists.mp hout
    intro hbot
    apply haI
    have : Θ a = 1 := by
      have ha : Θ' ⟨a, haE⟩ ∈ Θ'.range := ⟨_, rfl⟩
      rw [hbot, Subgroup.mem_bot] at ha
      exact ha
    have hmem : a ∈ Θ.ker := this
    rw [hker] at hmem
    exact hmem
  have hzc : Nat.card (Subgroup.zpowers σ) = 3 := by rw [Nat.card_zpowers, orderOf_eq_prime hσ3 hσ1]
  have hrange3 : Nat.card Θ'.range = 3 := by
    have hdvd : Nat.card Θ'.range ∣ Nat.card (Subgroup.zpowers σ) :=
      Subgroup.card_dvd_of_le hle
    rw [hzc] at hdvd
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (Subgroup.card_eq_one.mp h) hrange_ne
    · exact h
  have hℓ3 : Nat.card ℓ = 3 := by
    show Nat.card Θ'.ker = 3
    have := Subgroup.card_ker_mul_card_range Θ'
    rw [hrange3, hE9] at this
    omega
  have hφℓ : ∀ l ∈ ℓ, φ l ∈ ℓ := by
    intro l hl
    rw [hℓmem] at hl ⊢
    show Θ (c * (l : MulAut (C0 σ)) * c⁻¹) = 1
    simp [map_mul, map_inv, hl, hΘc']
  have hquot : ∀ e : ↥Ē, φ e * e⁻¹ ∈ ℓ := by
    intro e
    rw [hℓmem]
    show Θ (c * (e : MulAut (C0 σ)) * c⁻¹ * (e : MulAut (C0 σ))⁻¹) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hΘc', one_mul, inv_one, mul_one,
      mul_inv_cancel]
  letI : CommGroup ↥Ē := ElementaryAbelianModule.subgroupCommGroup Ē hE3.1
  have hE3' : ∀ e : ↥Ē, e ^ 3 = 1 := fun e => Subtype.ext (by simpa using hE3.2 e e.2)
  obtain ⟨hlinv, e, heℓ, hφe⟩ := reflection_shape hE3' hE9 φ hφ2 hφ1 ℓ hℓ3 hφℓ hquot
  obtain ⟨l, hlℓ, hl1⟩ : ∃ l ∈ ℓ, l ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : ℓ = ⊥ := (Subgroup.eq_bot_iff_forall ℓ).mpr hcon
    rw [hbot, Subgroup.card_bot] at hℓ3
    omega
  obtain ⟨g, hg⟩ : ∃ g : C0 σ, MulAut.conj g = (l : MulAut (C0 σ)) := by
    have : (l : MulAut (C0 σ)) ∈ Θ.ker := (hℓmem l).mp hlℓ
    rw [hker] at this
    exact this
  have hlmem : MulAut.conj g ∈ Ē := hg ▸ l.2
  have hg1 : g ≠ 1 := by
    rintro rfl
    apply hl1
    exact Subtype.ext (by rw [← hg, map_one]; rfl)
  have hg3 : g ^ 3 = 1 := hinj (by rw [map_pow, hg, map_one]; exact hE3.2 _ l.2)
  have hxg : x * g * x⁻¹ = g⁻¹ := by
    apply hinj
    have h' := congrArg Subtype.val (hlinv l hlℓ)
    rw [hφapp] at h'
    rw [map_mul, map_mul, map_inv, map_inv, ← hc, hg]
    exact h'
  have hβ3 : (e : MulAut (C0 σ)) ^ 3 = 1 := hE3.2 _ e.2
  have hβΘ : Θ (e : MulAut (C0 σ)) ≠ 1 := fun h => heℓ ((hℓmem e).mpr h)
  have hβ1 : (e : MulAut (C0 σ)) ≠ 1 := fun h => hβΘ (by rw [h, map_one])
  have hβout : (e : MulAut (C0 σ)) ∉ (MulAut.conj : C0 σ →* MulAut (C0 σ)).range := by
    intro hr
    apply hβΘ
    have : (e : MulAut (C0 σ)) ∈ Θ.ker := by rw [hker]; exact hr
    exact this
  have hel : (e : MulAut (C0 σ)) * l = l * e := congrArg Subtype.val (mul_comm' e l)
  have hβg : (e : MulAut (C0 σ)) g = g := by
    apply hinj
    rw [← mulAut_mul_conj_mul_inv, hg, hel]
    group
  have hφe' : c * (e : MulAut (C0 σ)) * c⁻¹ = e := congrArg Subtype.val hφe
  have hβx : (e : MulAut (C0 σ)) x = x := by
    apply hinj
    have hce : c * (e : MulAut (C0 σ)) = e * c := mul_inv_eq_iff_eq_mul.mp hφe'
    rw [← mulAut_mul_conj_mul_inv, ← hc, ← hce]
    group
  have hnot : MulAut.conj g ∉ Subgroup.zpowers (e : MulAut (C0 σ)) := by
    rintro ⟨k, hk0⟩
    have hk : (e : MulAut (C0 σ)) ^ k = MulAut.conj g := hk0
    have hΘ3 : Θ (e : MulAut (C0 σ)) ^ 3 = 1 := by rw [← map_pow, hβ3, map_one]
    have hord : orderOf (Θ (e : MulAut (C0 σ))) = 3 := orderOf_eq_prime hΘ3 hβΘ
    have hΘk : Θ (e : MulAut (C0 σ)) ^ k = 1 := by
      rw [← map_zpow, hk]
      exact hΘc g
    have hdvd : ((3 : ℕ) : ℤ) ∣ k := by
      rw [← hord]
      exact orderOf_dvd_iff_zpow_eq_one.mpr hΘk
    obtain ⟨m, rfl⟩ := hdvd
    have hone : (e : MulAut (C0 σ)) ^ ((3 : ℕ) * m : ℤ) = 1 := by
      rw [zpow_mul, zpow_natCast, hβ3, one_zpow]
    rw [hone] at hk
    exact hg1 (hinj (by rw [← hk, map_one]))
  exact ⟨e, g, x, e.2, hlmem, hβ1, hβ3, hβout, hg1, hg3, hnot, hβg, hβx, hxg⟩

end OutShape

end CFSG.RankThree.PartTwo.Sec21.Hering214
