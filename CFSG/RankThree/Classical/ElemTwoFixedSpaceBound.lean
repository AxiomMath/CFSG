module

public import CFSG.RankThree.Classical.SteinbergBJCharacterSpaces
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.RankThree.Classical

open Module

theorem finrank_biSup_eq_sum {F : Type*} [Field F] {M : Type*} [AddCommGroup M] [Module F M]
    [FiniteDimensional F M] {ι : Type*} [DecidableEq ι] {p : ι → Submodule F M}
    (hp : iSupIndep p) (S : Finset ι) :
    finrank F ↥(⨆ i ∈ S, p i) = ∑ i ∈ S, finrank F (p i) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.iSup_insert, Finset.sum_insert ha, ← ih]
    have hdis : Disjoint (p a) (⨆ i ∈ S, p i) := by
      have := hp.disjoint_biSup (y := (S : Set ι)) (by simpa using ha)
      simpa using this
    have h := Submodule.finrank_sup_add_finrank_inf_eq (p a) (⨆ i ∈ S, p i)
    rw [hdis.eq_bot, finrank_bot, add_zero] at h
    exact h

section FixedSpace

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]
variable {Γ : Type*} [CommGroup Γ] [Fintype Γ]

theorem isPrimitiveRoot_neg_one_two (h2 : (2 : F) ≠ 0) : IsPrimitiveRoot (-1 : F) 2 := by
  refine ⟨by norm_num, fun l hl => ?_⟩
  rcases Nat.even_or_odd l with hle | hlo
  · exact even_iff_two_dvd.mp hle
  · rw [hlo.neg_one_pow] at hl
    exact absurd (by linear_combination -hl : (2 : F) = 0) h2

theorem card_ne_zero_of_exp_two (h2 : (2 : F) ≠ 0) (hexp : ∀ g : Γ, g ^ 2 = 1) :
    (Fintype.card Γ : F) ≠ 0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpg : IsPGroup 2 Γ := fun g => ⟨1, by rw [pow_one]; exact hexp g⟩
  obtain ⟨k, hk⟩ := hpg.exists_card_eq
  rw [← Nat.card_eq_fintype_card, hk, Nat.cast_pow, Nat.cast_ofNat]
  exact pow_ne_zero k h2

theorem charIdem_mul_eq_mul_charIdem {p : ℕ} (ρ : Γ →* Module.End F V) (ζ : F)
    (χ : Additive Γ →+ ZMod p) (h : Γ) : charIdem ρ ζ χ * ρ h = ρ h * charIdem ρ ζ χ := by
  simp only [charIdem, smul_mul_assoc, mul_smul_comm, Finset.sum_mul, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← map_mul, ← map_mul, mul_comm k h]

theorem finrank_ker_sub_one_eq_sum [Fintype (Additive Γ →+ ZMod 2)] [FiniteDimensional F V]
    (h2 : (2 : F) ≠ 0) (hexp : ∀ g : Γ, g ^ 2 = 1) (ρ : Γ →* Module.End F V) (g : Γ) :
    finrank F (LinearMap.ker (ρ g - 1)) =
      ∑ χ ∈ Finset.univ.filter (fun χ : Additive Γ →+ ZMod 2 => χ (Additive.ofMul g) = 0),
        finrank F (charSpace ρ (-1) χ) := by
  classical
  have hζ := isPrimitiveRoot_neg_one_two h2
  have hΓ := card_ne_zero_of_exp_two h2 hexp
  rw [← finrank_biSup_eq_sum (iSupIndep_charSpace hζ hΓ)]
  suffices hEq : LinearMap.ker (ρ g - 1) = ⨆ χ ∈ Finset.univ.filter
      (fun χ : Additive Γ →+ ZMod 2 => χ (Additive.ofMul g) = 0), charSpace ρ (-1) χ by
    rw [hEq]
  apply le_antisymm
  · intro v hv
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hv
    rw [eq_sum_charIdem_apply Nat.prime_two hζ hexp hΓ v]
    refine Submodule.sum_mem _ fun χ _ => ?_
    by_cases hχ : χ (Additive.ofMul g) = 0
    · exact Submodule.mem_iSup_of_mem χ (Submodule.mem_iSup_of_mem (by simp [hχ])
        (charIdem_apply_mem hζ.pow_eq_one χ v))
    · have hval : (χ (Additive.ofMul g)).val = 1 := by
        have h01 := ZMod.val_lt (χ (Additive.ofMul g))
        have hne : (χ (Additive.ofMul g)).val ≠ 0 := fun h => hχ ((ZMod.val_eq_zero _).mp h)
        omega
      have h1 : charIdem ρ (-1) χ v = -charIdem ρ (-1) χ v := by
        calc charIdem ρ (-1) χ v = charIdem ρ (-1) χ (ρ g v) := by rw [hv]
          _ = (ρ g * charIdem ρ (-1) χ) v := by
            rw [← charIdem_mul_eq_mul_charIdem, Module.End.mul_apply]
          _ = -charIdem ρ (-1) χ v := by
            rw [mul_charIdem hζ.pow_eq_one, LinearMap.smul_apply, hval, pow_one, neg_one_smul]
      have h0 : charIdem ρ (-1) χ v = 0 := by
        have h3 : (2 : F) • charIdem ρ (-1) χ v = 0 := by
          rw [two_smul]
          nth_rewrite 1 [h1]
          exact neg_add_cancel _
        exact (smul_eq_zero.mp h3).resolve_left h2
      rw [h0]
      exact zero_mem _
  · refine iSup₂_le fun χ hχ => ?_
    intro v hv
    rw [Finset.mem_filter] at hχ
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero,
      mem_charSpace.mp hv g, hχ.2, ZMod.val_zero, pow_zero, one_smul]

end FixedSpace

section Counting

variable {Γ : Type*} [CommGroup Γ] [Fintype Γ] [Fintype (Additive Γ →+ ZMod 2)]

theorem card_div_two_sub_one_le_of_sum_char (hexp : ∀ g : Γ, g ^ 2 = 1)
    (n : (Additive Γ →+ ZMod 2) → ℕ) (d : Γ → ℕ)
    (hdn : ∀ g, d g = ∑ χ ∈ Finset.univ.filter (fun χ : Additive Γ →+ ZMod 2 =>
      χ (Additive.ofMul g) = 0), n χ)
    (hc : ∀ g g', g ≠ 1 → g' ≠ 1 → d g = d g') (hnt : ∃ χ, χ ≠ 0 ∧ n χ ≠ 0) {g : Γ}
    (hg : g ≠ 1) : Fintype.card Γ / 2 - 1 ≤ d g := by
  classical
  set N := Fintype.card Γ with hN
  set D := ∑ χ, n χ with hD
  have hζ : IsPrimitiveRoot (-1 : ℚ) 2 := isPrimitiveRoot_neg_one_two (by norm_num)
  set s : (Additive Γ →+ ZMod 2) → Γ → ℚ := fun χ h => (-1 : ℚ) ^ (χ (Additive.ofMul h)).val
    with hs
  have hval : ∀ a : ZMod 2, a.val = 0 ∨ a.val = 1 := fun a => by
    have := ZMod.val_lt a
    omega
  have hs01 : ∀ χ h, (if χ (Additive.ofMul h) = 0 then (1 : ℚ) else 0) = (1 + s χ h) / 2 := by
    intro χ h
    rcases hval (χ (Additive.ofMul h)) with h0 | h1
    · have : χ (Additive.ofMul h) = 0 := (ZMod.val_eq_zero _).mp h0
      simp [hs, this]
    · have hne : χ (Additive.ofMul h) ≠ 0 := fun h' => by rw [h', ZMod.val_zero] at h1; omega
      simp only [hs, if_neg hne, h1, pow_one]
      norm_num
  have hdq : ∀ h, (2 * (d h : ℚ) - D) = ∑ χ, (n χ : ℚ) * s χ h := by
    intro h
    have e1 : (d h : ℚ) = ∑ χ, (n χ : ℚ) * (1 + s χ h) / 2 := by
      rw [hdn h, Nat.cast_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl fun χ _ => ?_
      have := hs01 χ h
      split_ifs with hχ
      · rw [if_pos hχ] at this
        rw [mul_div_assoc, ← this, mul_one]
      · rw [if_neg hχ] at this
        rw [mul_div_assoc, ← this, mul_zero]
    rw [e1, Finset.mul_sum, hD, Nat.cast_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun χ _ => ?_
    ring
  have horth : ∀ χ : Additive Γ →+ ZMod 2, ∑ h : Γ, s χ h = if χ = 0 then (N : ℚ) else 0 := by
    intro χ
    split_ifs with hχ
    · subst hχ
      simp [hs, hN]
    · exact sum_pow_val_char_eq_zero hζ hχ
  have hmul : ∀ χ ψ h, s χ h * s ψ h = s (χ + ψ) h := by
    intro χ ψ h
    simp only [hs, AddMonoidHom.add_apply]
    rw [root_pow_val_add hζ.pow_eq_one]
  have hself : ∀ χ ψ : Additive Γ →+ ZMod 2, χ + ψ = 0 ↔ χ = ψ := by
    have h01 : ∀ a b : ZMod 2, a + b = 0 ↔ a = b := by decide
    intro χ ψ
    constructor
    · intro h
      refine AddMonoidHom.ext fun x => ?_
      have hx := DFunLike.congr_fun h x
      rw [AddMonoidHom.add_apply, AddMonoidHom.zero_apply] at hx
      exact (h01 _ _).mp hx
    · rintro rfl
      refine AddMonoidHom.ext fun x => ?_
      rw [AddMonoidHom.add_apply, AddMonoidHom.zero_apply]
      exact (h01 _ _).mpr rfl
  have hfour : ∀ ψ, ∑ h : Γ, (2 * (d h : ℚ) - D) * s ψ h = N * n ψ := by
    intro ψ
    simp_rw [hdq, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [mul_assoc, hmul, ← Finset.mul_sum, horth, hself]
    simp only [mul_ite, mul_zero]
    rw [Finset.sum_ite_eq']
    simp [mul_comm]
  set c := d g with hcdef
  have hd1 : d 1 = D := by
    rw [hdn 1, hD]
    simp
  have hNpos : 0 < N := Fintype.card_pos
  have hpsi : ∀ ψ, ψ ≠ 0 → (N : ℚ) * n ψ = 2 * D - 2 * c := by
    intro ψ hψ
    rw [← hfour ψ, ← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : Γ))]
    have hrest : ∀ h ∈ Finset.univ.erase (1 : Γ), (2 * (d h : ℚ) - D) * s ψ h =
        (2 * (c : ℚ) - D) * s ψ h := by
      intro h hh
      rw [hc h g (Finset.ne_of_mem_erase hh) hg]
    rw [Finset.sum_congr rfl hrest, ← Finset.mul_sum]
    have hsum1 : ∑ h ∈ Finset.univ.erase (1 : Γ), s ψ h = -1 := by
      have := horth ψ
      rw [if_neg hψ, ← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : Γ))] at this
      have hs1 : s ψ 1 = 1 := by simp [hs]
      linarith
    have hs1 : s ψ 1 = 1 := by simp [hs]
    rw [hsum1, hs1, hd1]
    ring
  obtain ⟨ψ₀, hψ₀, hn₀⟩ := hnt
  set b := n ψ₀ with hb
  have hall : ∀ ψ, ψ ≠ 0 → n ψ = b := by
    intro ψ hψ
    have h1 := hpsi ψ hψ
    have h2 := hpsi ψ₀ hψ₀
    have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hNpos.ne'
    exact_mod_cast mul_left_cancel₀ hNq (h1.trans h2.symm)
  have hcard : Fintype.card (Additive Γ →+ ZMod 2) = N := by
    rw [← Nat.card_eq_fintype_card, natCard_char Nat.prime_two hexp, Nat.card_eq_fintype_card]
  have hDsplit : D = n 0 + (N - 1) * b := by
    rw [hD, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Additive Γ →+ ZMod 2))]
    congr 1
    rw [Finset.sum_congr rfl fun ψ hψ => hall ψ (Finset.ne_of_mem_erase hψ), Finset.sum_const,
      smul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hcard]
  have key : (N : ℚ) * b = 2 * D - 2 * c := hpsi ψ₀ hψ₀
  have hb1 : 1 ≤ b := Nat.one_le_iff_ne_zero.mpr hn₀
  have hN2 : 2 ≤ N := by
    have : 1 < N := Fintype.one_lt_card_iff_nontrivial.mpr ⟨⟨g, 1, hg⟩⟩
    omega
  have hkey : N * b + 2 * c = 2 * D := by
    have : ((N * b + 2 * c : ℕ) : ℚ) = ((2 * D : ℕ) : ℚ) := by
      push_cast
      linarith
    exact_mod_cast this
  rw [hDsplit] at hkey
  have h2c : 2 * c = 2 * n 0 + (N - 2) * b := by
    zify [show 1 ≤ N by omega, show 2 ≤ N by omega] at hkey ⊢
    linear_combination hkey
  have hb2 : N - 2 ≤ (N - 2) * b := Nat.le_mul_of_pos_right _ hb1
  omega

end Counting

theorem card_div_two_sub_one_le_finrank_ker {F : Type*} [Field F] (h2 : (2 : F) ≠ 0)
    {X : Type*} [Group X] {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : Representation F X V) {E : Subgroup X} [Finite E] (hE : Open.IsElemAbelian 2 E)
    (hρ : ∃ e ∈ E, ρ e ≠ 1)
    (hd : ∀ e ∈ E, ∀ e' ∈ E, e ≠ 1 → e' ≠ 1 →
      Module.finrank F (LinearMap.ker (ρ e - 1)) = Module.finrank F (LinearMap.ker (ρ e' - 1)))
    {e : X} (he : e ∈ E) (he1 : e ≠ 1) :
    Nat.card E / 2 - 1 ≤ Module.finrank F (LinearMap.ker (ρ e - 1)) := by
  classical
  have hcomm : ∀ a b : E, a * b = b * a := fun a b =>
    (isMulCommutative_iff_of_setLike.mp hE.1) a a.2 b b.2 |> Subtype.ext
  let : CommGroup E := { (inferInstance : Group E) with mul_comm := hcomm }
  have : Fintype E := Fintype.ofFinite E
  have : Finite (Additive E →+ ZMod 2) :=
    Finite.of_injective (fun χ : Additive E →+ ZMod 2 => (χ : Additive E → ZMod 2))
      DFunLike.coe_injective
  have : Fintype (Additive E →+ ZMod 2) := Fintype.ofFinite _
  have hexp : ∀ g : E, g ^ 2 = 1 := fun g => Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hE.2 g g.2)
  set ρE : E →* Module.End F V := ρ.comp E.subtype with hρE
  have hζ := isPrimitiveRoot_neg_one_two h2
  have hΓ := card_ne_zero_of_exp_two h2 hexp
  have key := card_div_two_sub_one_le_of_sum_char (Γ := E) hexp
    (fun χ => finrank F (charSpace ρE (-1) χ)) (fun g => finrank F (LinearMap.ker (ρE g - 1)))
    (fun g => finrank_ker_sub_one_eq_sum h2 hexp ρE g)
    (fun g g' hg hg' => hd g g.2 g' g'.2 (fun h => hg (Subtype.ext h))
      (fun h => hg' (Subtype.ext h)))
    ?_ (g := ⟨e, he⟩) (fun h => he1 (congrArg Subtype.val h))
  · rwa [← Nat.card_eq_fintype_card] at key
  ·
    by_contra hall
    push Not at hall
    obtain ⟨e₀, he₀, hne⟩ := hρ
    apply hne
    have htop : charSpace ρE (-1) (0 : Additive E →+ ZMod 2) = ⊤ := by
      rw [eq_top_iff, ← iSup_charSpace_eq_top Nat.prime_two hζ hexp hΓ]
      refine iSup_le fun χ => ?_
      by_cases hχ : χ = 0
      · rw [hχ]
      · rw [Submodule.finrank_eq_zero.mp (hall χ hχ)]
        exact bot_le
    refine LinearMap.ext fun v => ?_
    have hv : v ∈ charSpace ρE (-1) (0 : Additive E →+ ZMod 2) := htop ▸ Submodule.mem_top
    have := mem_charSpace.mp hv ⟨e₀, he₀⟩
    simpa [hρE] using this

end CFSG.RankThree.Classical
