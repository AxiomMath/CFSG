module

public import CFSG.RankThree.PartTwo.Sec12.Coordinates
public import CFSG.RankThree.PartTwo.Sec21.Notation

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

abbrev V2 := Fin 2 → ZMod 3

theorem fixed_of_order_three : ∀ a b c d : ZMod 3,
    !![a, b; c, d] * !![a, b; c, d] * !![a, b; c, d] = 1 → !![a, b; c, d] ≠ 1 →
    ∃ x y : ZMod 3, (x ≠ 0 ∨ y ≠ 0) ∧ a * x + b * y = x ∧ c * x + d * y = y := by
  decide +kernel

theorem eigen_of_involution : ∀ a b c d : ZMod 3, !![a, b; c, d] * !![a, b; c, d] = 1 →
    ∃ x y : ZMod 3, (x ≠ 0 ∨ y ≠ 0) ∧ ∃ e : ZMod 3,
      a * x + b * y = e * x ∧ c * x + d * y = e * y := by
  decide +kernel

theorem toMatrix'_eq_V2 (g : V2 →ₗ[ZMod 3] V2) :
    LinearMap.toMatrix' g = !![g (Pi.single 0 1) 0, g (Pi.single 1 1) 0;
      g (Pi.single 0 1) 1, g (Pi.single 1 1) 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [LinearMap.toMatrix'_apply]

theorem apply_eq_V2 (g : V2 →ₗ[ZMod 3] V2) (x y : ZMod 3) :
    g ![x, y] = ![g (Pi.single 0 1) 0 * x + g (Pi.single 1 1) 0 * y,
      g (Pi.single 0 1) 1 * x + g (Pi.single 1 1) 1 * y] := by
  have h : (![x, y] : V2) = x • Pi.single 0 1 + y • Pi.single 1 1 := by
    ext i
    fin_cases i <;> simp
  rw [h, map_add, map_smul, map_smul]
  ext i
  fin_cases i <;> simp [mul_comm]

theorem card_V2_equiv : Nat.card (V2 ≃ₗ[ZMod 3] V2) = 48 := by
  rw [← Nat.card_congr (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 3) V2).toEquiv,
    ← Nat.card_congr (Matrix.GeneralLinearGroup.toLin (n := Fin 2) (R := ZMod 3)).toEquiv,
    Matrix.card_GL_field, Fin.prod_univ_two, ZMod.card]
  norm_num

theorem toMatrix'_pow_V2 (g : V2 ≃ₗ[ZMod 3] V2) (k : ℕ) :
    LinearMap.toMatrix' ((g ^ k : V2 ≃ₗ[ZMod 3] V2) : V2 →ₗ[ZMod 3] V2) =
      LinearMap.toMatrix' (g : V2 →ₗ[ZMod 3] V2) ^ k := by
  induction k with
  | zero => simp [LinearMap.toMatrix'_id]
  | succ k ih =>
    rw [pow_succ, pow_succ, ← ih, ← LinearMap.toMatrix'_mul]
    rfl


theorem toMatrix'_pow_eq_one_V2 {g : V2 ≃ₗ[ZMod 3] V2} {k : ℕ} (hg : g ^ k = 1) :
    LinearMap.toMatrix' (g : V2 →ₗ[ZMod 3] V2) ^ k = 1 := by
  rw [← toMatrix'_pow_V2, hg]
  exact LinearMap.toMatrix'_id

theorem exists_fixed_V2 {g : V2 ≃ₗ[ZMod 3] V2} (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1) :
    ∃ v : V2, v ≠ 0 ∧ g v = v := by
  have hM := toMatrix'_pow_eq_one_V2 hg3
  rw [toMatrix'_eq_V2, pow_succ, pow_two] at hM
  have hM1 : !![(g : V2 →ₗ[ZMod 3] V2) (Pi.single 0 1) 0, (g : V2 →ₗ[ZMod 3] V2) (Pi.single 1 1) 0;
      (g : V2 →ₗ[ZMod 3] V2) (Pi.single 0 1) 1, (g : V2 →ₗ[ZMod 3] V2) (Pi.single 1 1) 1] ≠ 1 := by
    intro h
    apply hg1
    have h1 : LinearMap.toMatrix' (g : V2 →ₗ[ZMod 3] V2) = LinearMap.toMatrix' LinearMap.id := by
      rw [toMatrix'_eq_V2, h, LinearMap.toMatrix'_id]
    have h2 := LinearMap.toMatrix'.injective h1
    exact LinearEquiv.ext fun v => by
      have := congrArg (fun φ : V2 →ₗ[ZMod 3] V2 => φ v) h2
      simpa using this
  obtain ⟨x, y, hxy, h1, h2⟩ := fixed_of_order_three _ _ _ _ hM hM1
  refine ⟨![x, y], fun h => ?_, ?_⟩
  · have hx : x = 0 := congrFun h 0
    have hy : y = 0 := congrFun h 1
    rcases hxy with hxy | hxy
    · exact hxy hx
    · exact hxy hy
  · have := apply_eq_V2 (g : V2 →ₗ[ZMod 3] V2) x y
    simp only [LinearEquiv.coe_coe] at this h1 h2
    rw [this, h1, h2]

theorem exists_eigen_V2 {g : V2 ≃ₗ[ZMod 3] V2} (hg2 : g ^ 2 = 1) :
    ∃ v : V2, v ≠ 0 ∧ ∃ e : ZMod 3, g v = e • v := by
  have hM := toMatrix'_pow_eq_one_V2 hg2
  rw [toMatrix'_eq_V2, pow_two] at hM
  obtain ⟨x, y, hxy, e, h1, h2⟩ := eigen_of_involution _ _ _ _ hM
  refine ⟨![x, y], fun h => ?_, e, ?_⟩
  · have hx : x = 0 := congrFun h 0
    have hy : y = 0 := congrFun h 1
    rcases hxy with hxy | hxy
    · exact hxy hx
    · exact hxy hy
  · have := apply_eq_V2 (g : V2 →ₗ[ZMod 3] V2) x y
    simp only [LinearEquiv.coe_coe] at this h1 h2
    rw [this, h1, h2]
    ext i
    fin_cases i <;> simp

variable {G : Type*} [Group G]


omit [Group G] in
theorem map_eq_of_mem_zpowers {B : Type*} [Group B] [Finite B] {B₁ : Subgroup B}
    {t : MulAut B} (ht : ∀ x ∈ B₁, t x ∈ B₁) {φ : MulAut B} (hφ : φ ∈ Subgroup.zpowers t) :
    B₁.map φ.toMonoidHom = B₁ := by
  have hnat : ∀ n : ℕ, ∀ x ∈ B₁, (t ^ n) x ∈ B₁ := by
    intro n
    induction n with
    | zero => intro x hx; simpa using hx
    | succ n ih =>
      intro x hx
      rw [pow_succ, MulAut.mul_apply]
      exact ih _ (ht x hx)
  have hfin : IsOfFinOrder t := isOfFinOrder_of_finite t
  rw [← hfin.mem_powers_iff_mem_zpowers] at hφ
  obtain ⟨n, rfl⟩ := hφ
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨x, hx, rfl⟩
    exact hnat n x hx
  · rw [Subgroup.card_map_of_injective (t ^ n).injective]

theorem four_dvd_card_of_isIrreducibleOn {B : Subgroup G} [Finite B]
    (hB : CFSG.Assembly.IsElemAbelian 3 B) (h9 : Nat.card B = 9) {T : Subgroup (MulAut B)}
    (hT : Sec21.IsIrreducibleOn T) : 4 ∣ Nat.card T := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨f⟩ := Sec12.exists_coords hB (n := 2) (by rw [h9]; norm_num)
  set ρ := Sec12.coordHom f with hρdef
  have hρ : Function.Injective ρ := Sec12.coordHom_injective f
  have hdvd : Nat.card T ∣ 48 := by
    have h1 := Subgroup.card_subgroup_dvd_card (T.map ρ)
    rwa [card_V2_equiv, Subgroup.card_map_of_injective hρ] at h1
  by_contra h4
  suffices hex : ∃ B₁ : Subgroup B, B₁ ≠ ⊥ ∧ B₁ ≠ ⊤ ∧ ∀ φ ∈ T, B₁.map φ.toMonoidHom = B₁ by
    obtain ⟨B₁, h1, h2, h3⟩ := hex
    rcases hT B₁ h3 with h | h
    · exact h1 h
    · exact h2 h
  have hcases : Nat.card T = 1 ∨ Nat.card T = 2 ∨ Nat.card T = 3 ∨ Nat.card T = 6 := by
    have hmem : Nat.card T ∈ Nat.divisors 48 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
    rw [show Nat.divisors 48 = {1, 2, 3, 4, 6, 8, 12, 16, 24, 48} by decide] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h | h | h | h | h | h | h | h <;> rw [h] at h4 ⊢ <;> omega
  have hline : ∀ v : V2, v ≠ 0 → (Subgroup.zpowers (f (Multiplicative.ofAdd v))) ≠ ⊥ ∧
      Subgroup.zpowers (f (Multiplicative.ofAdd v)) ≠ ⊤ := by
    intro v hv
    have hx1 : f (Multiplicative.ofAdd v) ≠ 1 := by
      intro h
      apply hv
      have := congrArg (fun z => Multiplicative.toAdd (f.symm z)) h
      simpa using this
    have hx3 : orderOf (f (Multiplicative.ofAdd v)) = 3 := by
      refine orderOf_eq_prime ?_ hx1
      exact Subtype.ext (by simpa using hB.2 _ (f (Multiplicative.ofAdd v)).2)
    refine ⟨fun h => hx1 ?_, fun h => ?_⟩
    · have : f (Multiplicative.ofAdd v) ∈ Subgroup.zpowers (f (Multiplicative.ofAdd v)) :=
        Subgroup.mem_zpowers _
      rw [h, Subgroup.mem_bot] at this
      exact this
    · have h1 := congrArg (fun H : Subgroup B => Nat.card H) h
      simp only [Nat.card_zpowers, hx3, Subgroup.card_top, h9] at h1
      omega
  have hρapp : ∀ (σ : MulAut B) (v : V2),
      σ (f (Multiplicative.ofAdd v)) = f (Multiplicative.ofAdd (ρ σ v)) := by
    intro σ v
    rw [hρdef, Sec12.coordHom_apply]
    simp
  have hthree : ∀ u : T, orderOf u = 3 → (Subgroup.zpowers u).Normal →
      ∃ B₁ : Subgroup B, B₁ ≠ ⊥ ∧ B₁ ≠ ⊤ ∧ ∀ φ ∈ T, B₁.map φ.toMonoidHom = B₁ := by
    intro u hu hU
    have hu1 : (u : MulAut B) ≠ 1 := by
      intro h
      have : u = 1 := Subtype.ext h
      rw [this, orderOf_one] at hu
      exact absurd hu (by norm_num)
    have hu3' : u ^ 3 = 1 := by
      rw [← hu]
      exact pow_orderOf_eq_one u
    have hu3 : ρ (u : MulAut B) ^ 3 = 1 := by
      rw [← map_pow, ← Subgroup.coe_pow, hu3', Subgroup.coe_one, map_one]
    have hρu1 : ρ (u : MulAut B) ≠ 1 := fun h => hu1 (hρ (h.trans (map_one ρ).symm))
    obtain ⟨v, hv, hfix⟩ := exists_fixed_V2 hu3 hρu1
    set B₁ : Subgroup B := (u : MulAut B).toMonoidHom.eqLocus (MonoidHom.id B) with hB₁
    have hx₀ : f (Multiplicative.ofAdd v) ∈ B₁ := by
      show (u : MulAut B) (f (Multiplicative.ofAdd v)) = f (Multiplicative.ofAdd v)
      rw [hρapp, hfix]
    refine ⟨B₁, fun h => ?_, fun h => ?_, fun φ hφ => ?_⟩
    · rw [h, Subgroup.mem_bot] at hx₀
      apply hv
      have := congrArg (fun z => Multiplicative.toAdd (f.symm z)) hx₀
      simpa using this
    · apply hu1
      exact MulEquiv.ext fun x => (show x ∈ B₁ by rw [h]; exact Subgroup.mem_top x)
    ·
      have hconj := hU.conj_mem u (Subgroup.mem_zpowers u) (⟨φ, hφ⟩ : T)⁻¹
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hconj
      have hj' : φ⁻¹ * (u : MulAut B) * φ = (u : MulAut B) ^ j := by
        have := congrArg Subtype.val hj
        simp only [Subgroup.coe_zpow, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv] at this
        exact this.symm
      apply Subgroup.eq_of_le_of_card_ge
      · rintro _ ⟨x, hx, rfl⟩
        show (u : MulAut B) (φ x) = φ x
        have hxj : ((u : MulAut B) ^ j) x = x :=
          MulAction.mem_fixedBy_zpow (show x ∈ MulAction.fixedBy B (u : MulAut B) from hx) j
        rw [← hj'] at hxj
        have h1 : φ⁻¹ ((u : MulAut B) (φ x)) = x := hxj
        have h2 := congrArg φ h1
        rwa [MulAut.apply_inv_self] at h2
      · rw [Subgroup.card_map_of_injective φ.injective]
  rcases hcases with h1 | h2 | h3 | h6
  ·
    refine ⟨Subgroup.zpowers (f (Multiplicative.ofAdd (Pi.single 0 1))),
      (hline _ (by simp)).1, (hline _ (by simp)).2, fun φ hφ => ?_⟩
    have : φ = 1 := by
      have hT1 : T = ⊥ := (Subgroup.card_eq_one).mp h1
      rw [hT1] at hφ
      exact hφ
    subst this
    ext x
    simp
  ·
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := T) 2 (by rw [h2])
    have ht2' : t ^ 2 = 1 := by
      rw [← ht]
      exact pow_orderOf_eq_one t
    have ht2 : ρ (t : MulAut B) ^ 2 = 1 := by
      rw [← map_pow, ← Subgroup.coe_pow, ht2', Subgroup.coe_one, map_one]
    obtain ⟨v, hv, e, hve⟩ := exists_eigen_V2 ht2
    set x₀ := f (Multiplicative.ofAdd v) with hx₀
    refine ⟨Subgroup.zpowers x₀, (hline v hv).1, (hline v hv).2, fun φ hφ => ?_⟩
    have hzp : Subgroup.zpowers t = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, ht, h2])
    have hφ' : (⟨φ, hφ⟩ : T) ∈ Subgroup.zpowers t := by
      rw [hzp]
      exact Subgroup.mem_top _
    have hφt : φ ∈ Subgroup.zpowers (t : MulAut B) := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hφ'
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, by rw [← Subgroup.coe_zpow, hk]⟩
    refine map_eq_of_mem_zpowers (fun y hy => ?_) hφt
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [map_zpow]
    refine Subgroup.zpow_mem _ ?_ k
    rw [hρapp, hve, ← ZMod.natCast_zmod_val e, Nat.cast_smul_eq_nsmul, ofAdd_nsmul, map_pow]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  ·
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := T) 3 (by rw [h3])
    have hU : (Subgroup.zpowers u).Normal := by
      have htop : Subgroup.zpowers u = ⊤ :=
        Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, hu, h3])
      rw [htop]
      infer_instance
    exact hthree u hu hU
  ·
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := T) 3 (by rw [h6]; norm_num)
    have hU : (Subgroup.zpowers u).Normal := by
      apply Subgroup.normal_of_index_eq_two
      have h1 := (Subgroup.zpowers u).index_mul_card
      rw [Nat.card_zpowers, hu, h6] at h1
      omega
    exact hthree u hu hU


theorem card_autIn_dvd_of_le {K A B₀ : Subgroup G} (hB₀A : B₀ ≤ A)
    (hKA : K ≤ Subgroup.normalizer (A : Set G)) (hKB : K ≤ Subgroup.normalizer (B₀ : Set G)) :
    Nat.card (Sec4.autIn K B₀) ∣ Nat.card (Sec4.autIn K A) := by
  set φA : K →* MulAut A := A.normalizerMonoidHom.comp (Subgroup.inclusion hKA) with hφA
  set φB : K →* MulAut B₀ := B₀.normalizerMonoidHom.comp (Subgroup.inclusion hKB) with hφB
  have hA : Sec4.autIn K A = φA.range := by
    ext σ
    rw [Sec4.mem_autIn_iff, MonoidHom.mem_range]
    constructor
    · rintro ⟨h, hN, hK, rfl⟩
      exact ⟨⟨h, hK⟩, rfl⟩
    · rintro ⟨⟨h, hK⟩, rfl⟩
      exact ⟨h, hKA hK, hK, rfl⟩
  have hB : Sec4.autIn K B₀ = φB.range := by
    ext σ
    rw [Sec4.mem_autIn_iff, MonoidHom.mem_range]
    constructor
    · rintro ⟨h, hN, hK, rfl⟩
      exact ⟨⟨h, hK⟩, rfl⟩
    · rintro ⟨⟨h, hK⟩, rfl⟩
      exact ⟨h, hKB hK, hK, rfl⟩
  have hker : φA.ker ≤ φB.ker := by
    intro k hk
    rw [MonoidHom.mem_ker] at hk ⊢
    ext x
    have h1 := congrArg (fun σ : MulAut A => ((σ ⟨x, hB₀A x.2⟩ : A) : G)) hk
    simp only [hφA, MonoidHom.comp_apply, MulAut.one_apply] at h1
    show (k : G) * x * (k : G)⁻¹ = x
    exact h1
  rw [hA, hB, ← Subgroup.index_ker, ← Subgroup.index_ker]
  exact Subgroup.index_dvd_of_le hker

theorem four_dvd_card_of_irreducible_plane {K A B₀ : Subgroup G} [Finite B₀]
    {S : Subgroup (MulAut A)} (hB₀ : CFSG.Assembly.IsElemAbelian 3 B₀) (h9 : Nat.card B₀ = 9)
    (hB₀A : B₀ ≤ A)
    (hKA : K ≤ Subgroup.normalizer (A : Set G)) (hKB : K ≤ Subgroup.normalizer (B₀ : Set G))
    (hirr : Sec21.IsIrreducibleOn (Sec4.autIn K B₀)) (hS : Sec4.autIn K A ≤ S) [Finite A] :
    4 ∣ Nat.card S :=
  ((four_dvd_card_of_isIrreducibleOn hB₀ h9 hirr).trans (card_autIn_dvd_of_le hB₀A hKA hKB)).trans
    (Subgroup.card_dvd_of_le hS)

end CFSG.RankThree.PartTwo.KFacts
