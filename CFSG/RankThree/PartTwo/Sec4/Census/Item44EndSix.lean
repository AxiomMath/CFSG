module

public import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalSymplecticSix
public import CFSG.CharacterTheory.Burnside
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonClassification
public import Mathlib.GroupTheory.SpecificGroups.ZGroup

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open Equiv CFSG.ComponentClassification.PresentationLocal
open scoped Matrix

private theorem le_alternatingGroup_of_isPerfect {α : Type*} [Fintype α] [DecidableEq α]
    {H : Subgroup (Perm α)} (hH : Group.IsPerfect H) : H ≤ alternatingGroup α :=
  calc H = ⁅H, H⁆ := (Subgroup.isPerfect_iff.1 hH).symm
    _ ≤ ⁅⊤, ⊤⁆ := Subgroup.commutator_mono le_top le_top
    _ ≤ alternatingGroup α := alternatingGroup.commutator_perm_le

private theorem not_isSolvable_of_isPerfect_of_ne_bot {G : Type*} [Group G] {H : Subgroup G}
    (hH : Group.IsPerfect H) (hne : H ≠ ⊥) : ¬ Group.IsSolvable H := by
  have : Nontrivial H := (Subgroup.nontrivial_iff_ne_bot H).2 hne
  exact Group.IsPerfect.not_isSolvable H

private theorem isSolvable_of_card_eq_prime_pow_mul_prime_pow {G : Type*} [Group G] [Finite G]
    {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (h : Nat.card G = p ^ a * q ^ b) :
    Group.IsSolvable G := by
  have := Fintype.ofFinite G
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow hp hq hpq
    (by rw [← Nat.card_eq_fintype_card, h])

private theorem dvd_three_hundred_sixty_cases : ∀ d < 361, d ∣ 360 → 30 ∣ d ∨ ∃ a < 4, ∃ b < 3,
    d = 2 ^ a * 3 ^ b ∨ d = 2 ^ a * 5 ^ b ∨ d = 3 ^ a * 5 ^ b := by
  decide +kernel

private theorem thirty_dvd_card {G : Type*} [Group G] [Finite G] (hG : ¬ Group.IsSolvable G)
    (h : Nat.card G ∣ 360) : 30 ∣ Nat.card G := by
  rcases dvd_three_hundred_sixty_cases _ (Nat.lt_succ_of_le (Nat.le_of_dvd (by norm_num) h)) h
    with h30 | ⟨a, -, b, -, hab | hab | hab⟩
  · exact h30
  · exact absurd (isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two Nat.prime_three
      (by norm_num) hab) hG
  · exact absurd (isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two Nat.prime_five
      (by norm_num) hab) hG
  · exact absurd (isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_three Nat.prime_five
      (by norm_num) hab) hG

private theorem isSolvable_of_card_eq_thirty {G : Type*} [Group G] (h : Nat.card G = 30) :
    Group.IsSolvable G := by
  have : Finite G := Nat.finite_of_card_ne_zero (by rw [h]; norm_num)
  have h30 : Squarefree (2 * (3 * 5)) :=
    Nat.squarefree_mul_iff.2 ⟨by norm_num, Nat.prime_two.prime.squarefree,
      Nat.squarefree_mul_iff.2 ⟨by norm_num, Nat.prime_three.prime.squarefree,
        Nat.prime_five.prime.squarefree⟩⟩
  have : IsZGroup G := IsZGroup.of_squarefree (by rw [h]; exact h30)
  infer_instance

theorem perfect_perm_five {L : Subgroup (Perm (Fin 5))} (hL : Group.IsPerfect L) (hne : L ≠ ⊥) :
    L = alternatingGroup (Fin 5) := by
  have hA := le_alternatingGroup_of_isPerfect hL
  have hns := not_isSolvable_of_isPerfect_of_ne_bot hL hne
  have hcard : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]; rfl
  have hdvd : Nat.card L ∣ 60 := hcard ▸ Subgroup.card_dvd_of_le hA
  have h30 := thirty_dvd_card hns (hdvd.trans (by norm_num))
  have hne30 : Nat.card L ≠ 30 := fun h => hns (isSolvable_of_card_eq_thirty h)
  have hle := Nat.le_of_dvd (by norm_num) hdvd
  have hpos : 0 < Nat.card L := Nat.card_pos
  exact Subgroup.eq_of_le_of_card_ge hA (by omega)

private theorem card_le_sixty_of_le_alternatingGroup {K : Subgroup (Perm (Fin 6))}
    (hK : K ≤ alternatingGroup (Fin 6)) (hne : K ≠ alternatingGroup (Fin 6)) :
    Nat.card K ≤ 60 := by
  have hs : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hcard : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]; rfl
  set K' := K.subgroupOf (alternatingGroup (Fin 6))
  have hK' : K' ≠ ⊤ := fun h => hne (le_antisymm hK (Subgroup.subgroupOf_eq_top.1 h))
  have hcore : K'.normalCore = ⊥ := by
    rcases K'.normalCore_normal.eq_bot_or_eq_top with h | h
    · exact h
    · exact absurd (top_le_iff.1 (h ▸ K'.normalCore_le)) hK'
  have h1 := K'.index_normalCore_le_factorial_index
  rw [hcore, Subgroup.index_bot, hcard] at h1
  have h2 := K'.index_mul_card
  rw [hcard, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK).toEquiv] at h2
  by_contra hlt
  have h5 : K'.index ≤ 5 := by
    by_contra h6
    have := Nat.mul_le_mul (show 6 ≤ K'.index by omega) (show 61 ≤ Nat.card K by omega)
    omega
  have h120 := Nat.factorial_le h5
  have : (5 : ℕ).factorial = 120 := rfl
  omega

private theorem apply_eq_of_card_orbit_le_four {α : Type*} [Finite α] {H : Subgroup (Perm α)}
    (hH : Group.IsPerfect H) {x : α} (hx : Nat.card (MulAction.orbit H x) ≤ 4) {σ : Perm α}
    (hσ : σ ∈ H) : σ x = x := by
  let φ := MulAction.toPermHom H (MulAction.orbit H x)
  have : Group.IsSolvable (Perm (MulAction.orbit H x)) := Equiv.Perm.isSolvable hx
  have : Group.IsPerfect φ.range := Group.IsPerfect.range φ
  have : Subsingleton φ.range := by
    by_contra hnt
    rw [not_subsingleton_iff_nontrivial] at hnt
    exact Group.IsPerfect.not_isSolvable φ.range inferInstance
  have h1 : φ ⟨σ, hσ⟩ = 1 :=
    congrArg Subtype.val (Subsingleton.elim (⟨φ ⟨σ, hσ⟩, ⟨σ, hσ⟩, rfl⟩ : φ.range) 1)
  have h2 := congrArg
    (fun τ : Perm (MulAction.orbit H x) => (τ ⟨x, MulAction.mem_orbit_self x⟩ : α)) h1
  simpa [φ] using h2

private theorem exists_fixed_or_isPretransitive {H : Subgroup (Perm (Fin 6))}
    (hH : Group.IsPerfect H) : (∃ k, ∀ σ ∈ H, σ k = k) ∨ MulAction.IsPretransitive H (Fin 6) := by
  by_cases h0 : Nat.card (MulAction.orbit H (0 : Fin 6)) ≤ 4
  · exact Or.inl ⟨0, fun σ hσ => apply_eq_of_card_orbit_le_four hH h0 hσ⟩
  by_cases huniv : MulAction.orbit H (0 : Fin 6) = Set.univ
  · exact Or.inr ((MulAction.isPretransitive_iff_orbit_eq_univ 0).2 huniv)
  obtain ⟨y, hy⟩ : ∃ y, y ∉ MulAction.orbit H (0 : Fin 6) := by
    by_contra! h
    exact huniv (Set.eq_univ_of_forall h)
  refine Or.inl ⟨y, fun σ hσ => apply_eq_of_card_orbit_le_four hH ?_ hσ⟩
  have hsub : MulAction.orbit H y ⊆ (MulAction.orbit H (0 : Fin 6))ᶜ := by
    rintro z ⟨g, rfl⟩ ⟨h, hh⟩
    refine hy ⟨g⁻¹ * h, ?_⟩
    change (g⁻¹ * h) • (0 : Fin 6) = y
    change h • (0 : Fin 6) = g • y at hh
    rw [mul_smul, hh, inv_smul_smul]
  have h1 := Set.ncard_le_ncard hsub
  have h2 := Set.ncard_add_ncard_compl (MulAction.orbit H (0 : Fin 6))
  rw [Nat.card_coe_set_eq] at h0 ⊢
  rw [Nat.card_fin] at h2
  omega

theorem perfect_perm_six_of_fix {H : Subgroup (Perm (Fin 6))} (hH : Group.IsPerfect H)
    (hne : H ≠ ⊥) {k : Fin 6} (hk : ∀ σ ∈ H, σ k = k) :
    Nonempty (H ≃* alternatingGroup (Fin 5)) := by
  have hiff : ∀ σ : H, ∀ x, (σ : Perm (Fin 6)) x ≠ k ↔ x ≠ k := fun σ x =>
    not_congr ⟨fun h => (σ : Perm (Fin 6)).injective (h.trans (hk _ σ.2).symm),
      fun h => h ▸ hk _ σ.2⟩
  let φ : H →* Perm {x : Fin 6 // x ≠ k} :=
    MonoidHom.mk' (fun σ => (σ : Perm (Fin 6)).subtypePerm (hiff σ)) (fun _ _ => rfl)
  have hφ : Function.Injective φ := by
    intro σ τ h
    apply Subtype.ext
    apply Equiv.ext
    intro x
    by_cases hx : x = k
    · rw [hx, hk _ σ.2, hk _ τ.2]
    · exact congrArg Subtype.val (Equiv.congr_fun h ⟨x, hx⟩)
  have hcard : Fintype.card {x : Fin 6 // x ≠ k} = 5 := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_subtype_eq]
  let ψ : H →* Perm (Fin 5) :=
    (Equiv.permCongrHom (Fintype.equivFinOfCardEq hcard)).toMonoidHom.comp φ
  have hψ : Function.Injective ψ :=
    (Equiv.permCongrHom (Fintype.equivFinOfCardEq hcard)).injective.comp hφ
  have : Nontrivial H := (Subgroup.nontrivial_iff_ne_bot H).2 hne
  have : Nontrivial ψ.range := (MonoidHom.ofInjective hψ).injective.nontrivial
  have hrange := perfect_perm_five (Group.IsPerfect.range ψ)
    ((Subgroup.nontrivial_iff_ne_bot _).1 this)
  exact ⟨(MonoidHom.ofInjective hψ).trans (MulEquiv.subgroupCongr hrange)⟩

theorem perfect_perm_six {H : Subgroup (Perm (Fin 6))} (hH : Group.IsPerfect H) (hne : H ≠ ⊥) :
    H = alternatingGroup (Fin 6) ∨ Nonempty (H ≃* alternatingGroup (Fin 5)) := by
  by_cases hEq : H = alternatingGroup (Fin 6)
  · exact Or.inl hEq
  right
  have hA := le_alternatingGroup_of_isPerfect hH
  have hns := not_isSolvable_of_isPerfect_of_ne_bot hH hne
  have hcard : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]; rfl
  have h30 := thirty_dvd_card hns (hcard ▸ Subgroup.card_dvd_of_le hA)
  have hne30 : Nat.card H ≠ 30 := fun h => hns (isSolvable_of_card_eq_thirty h)
  have hle := card_le_sixty_of_le_alternatingGroup hA hEq
  have hpos : 0 < Nat.card H := Nat.card_pos
  have h60 : Nat.card H = 60 := by omega
  rcases exists_fixed_or_isPretransitive hH with ⟨k, hk⟩ | htr
  · exact perfect_perm_six_of_fix hH hne hk
  · exact CFSG.Glauberman.Dickson.huppert_II_8_25_transitive_degree_six_order_sixty htr
      (by simp) h60

theorem perm_six_eq_bot_of_perfect_of_pow_five {K : Subgroup (Perm (Fin 6))}
    (hK : Group.IsPerfect K) (h5 : ∀ σ ∈ K, σ ^ 5 = 1 → σ = 1) : K = ⊥ := by
  by_contra hne
  have hdvd : 5 ∣ Nat.card K := by
    rcases perfect_perm_six hK hne with h | h
    · rw [h, nat_card_alternatingGroup, Nat.card_fin]
      decide
    · obtain ⟨e⟩ := h
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      decide
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨⟨σ, hσ⟩, hord⟩ := exists_prime_orderOf_dvd_card' 5 hdvd
  rw [Subgroup.orderOf_mk] at hord
  have h1 := h5 σ hσ (by rw [← hord]; exact pow_orderOf_eq_one σ)
  rw [h1, orderOf_one] at hord
  exact absurd hord (by norm_num)

theorem sympFour_eq_bot_of_perfect_of_pow_five {H : Subgroup sympFour}
    (hH : Group.IsPerfect H) (h5 : ∀ h ∈ H, omegaPerm h ^ 5 = 1 → omegaPerm h = 1) : H = ⊥ :=
  (Subgroup.map_eq_bot_iff_of_injective H omegaPerm_injective).1
    (perm_six_eq_bot_of_perfect_of_pow_five (Group.IsPerfect.map omegaPerm) (by
      rintro _ ⟨h, hh, rfl⟩ h1
      exact h5 h hh h1))

theorem omegaPerm_eq_of_quadForm {h : sympFour} {k : Fin 6}
    (hq : ∀ v, quadForm (omegaVec k)
      (((h : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v) =
      quadForm (omegaVec k) v) : omegaPerm h k = k := by
  refine omegaVec_injective (quadForm_injective (funext fun v => ?_))
  rw [quadForm_omegaVec_omegaPerm]
  have := hq ((((h⁻¹ : sympFour) : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v)
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel,
    OneMemClass.coe_one, Units.val_one, Matrix.one_mulVec] at this
  exact this.symm

private theorem coeffTransform_add_add (g : Matrix (Fin 4) (Fin 4) (ZMod 2))
    (x y z : Fin 4 → ZMod 2) :
    coeffTransform g (x + y + z) =
      coeffTransform g x + coeffTransform g y + coeffTransform g z := by
  funext i
  simp only [coeffTransform, quadForm, Pi.add_apply]
  have h2 : ∀ x : ZMod 2, x + x = 0 := by decide
  linear_combination -h2 (g 0 i * g 3 i + g 1 i * g 2 i)

private theorem coeffTransform_add (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) (x y : Fin 4 → ZMod 2) :
    coeffTransform g x + coeffTransform g y = (x + y) ᵥ* g := by
  funext i
  simp only [coeffTransform, quadForm, Pi.add_apply, Matrix.vecMul, dotProduct,
    Fin.sum_univ_four]
  have h2 : ∀ x : ZMod 2, x + x = 0 := by decide
  linear_combination h2 (g 0 i * g 3 i + g 1 i * g 2 i)

private theorem exists_omegaVec_add_add : ∀ a : Fin 4 → ZMod 2, (∀ k, omegaVec k ≠ a) →
    ∃ i j l : Fin 6, i < j ∧ j < l ∧ omegaVec i + omegaVec j + omegaVec l = a := by
  decide

private theorem omegaVec_add_add_ne : ∀ σ : Perm (Fin 6), σ ^ 5 = 1 → σ ≠ 1 → ∀ i j l : Fin 6,
    i < j → j < l →
      omegaVec (σ i) + omegaVec (σ j) + omegaVec (σ l) ≠ omegaVec i + omegaVec j + omegaVec l := by
  decide +kernel

private theorem exists_omegaVec_add : ∀ w : Fin 4 → ZMod 2, w ≠ 0 →
    ∃ i j : Fin 6, i < j ∧ omegaVec i + omegaVec j = antidiagGram *ᵥ w := by
  decide +kernel

private theorem omegaVec_add_ne : ∀ σ : Perm (Fin 6), σ ^ 5 = 1 → σ ≠ 1 → ∀ i j : Fin 6,
    i < j → omegaVec (σ i) + omegaVec (σ j) ≠ omegaVec i + omegaVec j := by
  decide +kernel

theorem eq_bot_of_perfect_of_quadForm {a : Fin 4 → ZMod 2} (ha : a ∉ Set.range omegaVec)
    {H : Subgroup sympFour} (hH : Group.IsPerfect H)
    (hq : ∀ h ∈ H, ∀ v, quadForm a
      (((h : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v) =
      quadForm a v) : H = ⊥ := by
  obtain ⟨i, j, l, hij, hjl, hsum⟩ := exists_omegaVec_add_add a fun k hk => ha ⟨k, hk⟩
  refine sympFour_eq_bot_of_perfect_of_pow_five hH fun h hh h5 => ?_
  by_contra h1
  refine omegaVec_add_add_ne (omegaPerm h) h5 h1 i j l hij hjl ?_
  have hT : coeffTransform (((h⁻¹ : sympFour) : GL (Fin 4) (ZMod 2)) :
      Matrix (Fin 4) (Fin 4) (ZMod 2)) a = a := by
    refine quadForm_injective (funext fun v => ?_)
    rw [← quadForm_mulVec (h⁻¹ : sympFour).2]
    exact hq _ (H.inv_mem hh) v
  rw [omegaPerm_apply, omegaPerm_apply, omegaPerm_apply, omegaVec_omegaAct, omegaVec_omegaAct,
    omegaVec_omegaAct, ← coeffTransform_add_add, hsum, hT]

theorem eq_bot_of_perfect_of_fix {w : Fin 4 → ZMod 2} (hw : w ≠ 0) {H : Subgroup sympFour}
    (hH : Group.IsPerfect H)
    (hfix : ∀ h ∈ H, ((h : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ w = w) :
    H = ⊥ := by
  obtain ⟨i, j, hij, hpair⟩ := exists_omegaVec_add w hw
  refine sympFour_eq_bot_of_perfect_of_pow_five hH fun h hh h5 => ?_
  by_contra h1
  refine omegaVec_add_ne (omegaPerm h) h5 h1 i j hij ?_
  set M : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
    ((h : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) with hM
  set g : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
    (((h⁻¹ : sympFour) : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) with hg
  have hMg : M * g = 1 := by
    rw [hM, hg, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, OneMemClass.coe_one,
      Units.val_one]
  have hs : Mᵀ * antidiagGram * M = antidiagGram := h.2
  have hJ : antidiagGram * g = Mᵀ * antidiagGram :=
    calc antidiagGram * g = Mᵀ * antidiagGram * M * g := by rw [hs]
      _ = Mᵀ * antidiagGram * (M * g) := Matrix.mul_assoc _ _ _
      _ = Mᵀ * antidiagGram := by rw [hMg, Matrix.mul_one]
  have hsym : antidiagGramᵀ = antidiagGram := by decide
  calc omegaVec (omegaPerm h i) + omegaVec (omegaPerm h j)
      = coeffTransform g (omegaVec i) + coeffTransform g (omegaVec j) := by
        rw [omegaPerm_apply, omegaPerm_apply, omegaVec_omegaAct, omegaVec_omegaAct]
    _ = (omegaVec i + omegaVec j) ᵥ* g := coeffTransform_add g _ _
    _ = (w ᵥ* antidiagGram) ᵥ* g := by rw [hpair, ← Matrix.vecMul_transpose, hsym]
    _ = w ᵥ* (Mᵀ * antidiagGram) := by rw [Matrix.vecMul_vecMul, hJ]
    _ = (M *ᵥ w) ᵥ* antidiagGram := by rw [← Matrix.vecMul_vecMul, Matrix.vecMul_transpose]
    _ = omegaVec i + omegaVec j := by
        rw [hfix h hh, hpair, ← Matrix.vecMul_transpose, hsym]

end CFSG.RankThree.PartTwo.Sec4.Census
