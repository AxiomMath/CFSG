module

public import CFSG.Quasithin.Background.B4ModelsWitness

public section

namespace CFSG.Quasithin.H13

open CFSG.Quasithin

section L828H

@[expose] def alt5D_828 : ↥(alternatingGroup (Fin 5)) →* MulAut ↥(G6.coreMod 5) :=
  (G6.coreAct 5).comp (alternatingGroup (Fin 5)).subtype

theorem alt5D_828_apply (γ : ↥(alternatingGroup (Fin 5))) :
    alt5D_828 γ = G6.coreAct 5 (γ : Equiv.Perm (Fin 5)) := rfl

@[expose] def tvec828 (i : Fin 5) : Fin 5 → ZMod 2 := fun j => if j = i then 0 else 1

theorem tvec828_sum (i : Fin 5) : ∑ j, tvec828 i j = 0 := by
  revert i
  decide

@[expose] def t828 (i : Fin 5) : ↥(G6.coreMod 5) :=
  ⟨Multiplicative.ofAdd (tvec828 i), tvec828_sum i⟩

theorem coe_t828 (i : Fin 5) :
    ((t828 i : ↥(G6.coreMod 5)) : G6.PermMod 5) = Multiplicative.ofAdd (tvec828 i) := rfl

theorem t828_injective : Function.Injective t828 := by
  intro i j h
  have h1 : tvec828 i = tvec828 j := congrArg Multiplicative.toAdd (congrArg Subtype.val h)
  revert i j
  decide

theorem t828_ne_one (i : Fin 5) : t828 i ≠ 1 := by
  intro h
  have h1 : tvec828 i = 0 := congrArg Multiplicative.toAdd (congrArg Subtype.val h)
  revert i
  decide

theorem coreAct_t828 (σ : Equiv.Perm (Fin 5)) (i : Fin 5) :
    G6.coreAct 5 σ (t828 i) = t828 (σ i) := by
  apply Subtype.ext
  rw [G6.coreAct_coe, coe_t828, coe_t828]
  apply Multiplicative.toAdd.injective
  funext j
  rw [G6.permAct_apply]
  simp only [toAdd_ofAdd, tvec828, Equiv.Perm.inv_eq_iff_eq]

@[expose] def zeta828 : Equiv.Perm (Fin 5) :=
  Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 3 4

@[expose] def tau828 : Equiv.Perm (Fin 5) := Equiv.swap 1 2 * Equiv.swap 2 3

theorem zeta828_mem : zeta828 ∈ alternatingGroup (Fin 5) := by
  rw [Equiv.Perm.mem_alternatingGroup, zeta828, Equiv.Perm.sign_mul, Equiv.Perm.sign_mul,
    Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide),
    Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide)]
  decide

theorem tau828_mem : tau828 ∈ alternatingGroup (Fin 5) := by
  rw [Equiv.Perm.mem_alternatingGroup, tau828, Equiv.Perm.sign_mul,
    Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide)]
  decide

@[expose] def evec828 : Fin 5 → ZMod 2 := fun j => if j = 0 ∨ j = 1 then 1 else 0

theorem exists_weight_two_828 : ∀ v : Fin 5 → ZMod 2, ∑ j, v j = 0 → v ≠ 0 →
    (∀ i, v ≠ tvec828 i) → ∃ k : Fin 5, ∃ b : Bool,
      v = fun j => evec828 ((zeta828 ^ (k : ℕ) * (if b then tau828 else 1))⁻¹ j) := by
  decide

theorem eq_sum_tvec828 : ∀ v : Fin 5 → ZMod 2, ∑ j, v j = 0 →
    v = ∑ i ∈ Finset.univ.filter (fun i => v i = 1), tvec828 i := by
  decide

theorem zeta828_pow_zero : ∀ k : Fin 5, (zeta828 ^ (k : ℕ)) 0 = k := by
  decide

theorem exists_alt5_e828 (v : ↥(G6.coreMod 5)) (hv : v ≠ 1) (hvS : ∀ i, v ≠ t828 i) :
    ∃ γ : ↥(alternatingGroup (Fin 5)),
      v = alt5D_828 γ ⟨Multiplicative.ofAdd evec828, by
        rw [G6.mem_coreMod]
        decide⟩ := by
  have hsum : ∑ j, Multiplicative.toAdd (v : G6.PermMod 5) j = 0 := v.2
  have hv0 : Multiplicative.toAdd (v : G6.PermMod 5) ≠ 0 := fun h =>
    hv (Subtype.ext (Multiplicative.toAdd.injective h))
  have hvS' : ∀ i, Multiplicative.toAdd (v : G6.PermMod 5) ≠ tvec828 i := fun i h =>
    hvS i (Subtype.ext (Multiplicative.toAdd.injective h))
  obtain ⟨k, b, hkb⟩ := exists_weight_two_828 _ hsum hv0 hvS'
  have hmem : zeta828 ^ (k : ℕ) * (if b then tau828 else 1) ∈ alternatingGroup (Fin 5) := by
    refine Subgroup.mul_mem _ (Subgroup.pow_mem _ zeta828_mem _) ?_
    split_ifs
    · exact tau828_mem
    · exact Subgroup.one_mem _
  refine ⟨⟨_, hmem⟩, Subtype.ext (Multiplicative.toAdd.injective ?_)⟩
  rw [alt5D_828_apply, G6.coreAct_coe]
  funext j
  rw [G6.permAct_apply, hkb]
  rfl

theorem eq_one_of_fix_t828 {y : MulAut ↥(G6.coreMod 5)} (hy : ∀ i, y (t828 i) = t828 i) :
    y = 1 := by
  ext v
  have hsum : ∑ j, Multiplicative.toAdd (v : G6.PermMod 5) j = 0 := v.2
  have hv : v = ∏ i ∈ Finset.univ.filter
      (fun i => Multiplicative.toAdd (v : G6.PermMod 5) i = 1), t828 i := by
    apply Subtype.ext
    rw [show ((∏ i ∈ Finset.univ.filter
        (fun i => Multiplicative.toAdd (v : G6.PermMod 5) i = 1), t828 i : ↥(G6.coreMod 5)) :
          G6.PermMod 5) = ∏ i ∈ Finset.univ.filter
        (fun i => Multiplicative.toAdd (v : G6.PermMod 5) i = 1), ((t828 i : ↥(G6.coreMod 5)) :
          G6.PermMod 5) from map_prod (G6.coreMod 5).subtype _ _]
    apply Multiplicative.toAdd.injective
    rw [toAdd_prod]
    exact eq_sum_tvec828 _ hsum
  rw [hv, map_prod]
  simp only [hy, MulAut.one_apply]

theorem alt5D_828_injective : Function.Injective alt5D_828 := by
  rw [injective_iff_map_eq_one]
  intro γ hγ
  apply Subtype.ext
  ext i
  have h := congrArg (fun f : MulAut ↥(G6.coreMod 5) => f (t828 i)) hγ
  simp only [alt5D_828_apply, coreAct_t828, MulAut.one_apply] at h
  exact congrArg Fin.val (t828_injective h)

theorem card_range_alt5D_828 : Nat.card ↥alt5D_828.range = 60 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective alt5D_828_injective).toEquiv,
    Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  decide

theorem eq_range_alt5D_828 {Y : Subgroup (MulAut ↥(G6.coreMod 5))} (hXY : alt5D_828.range ≤ Y)
    (hperf : ⁅Y, Y⁆ = Y) (h9 : ¬ 9 ∣ Nat.card Y) : Y = alt5D_828.range := by
  classical
  have hfinA : Finite (MulAut ↥(G6.coreMod 5)) :=
    Finite.of_injective (fun f : MulAut ↥(G6.coreMod 5) => (f : ↥(G6.coreMod 5) → _))
      fun f f' h => MulEquiv.ext (congrFun h)
  by_cases hS : ∀ y ∈ Y, ∀ i : Fin 5, ∃ j : Fin 5, y (t828 i) = t828 j
  ·
    let S : SubMulAction ↥Y ↥(G6.coreMod 5) :=
      { carrier := Set.range t828
        smul_mem' := by
          rintro y _ ⟨i, rfl⟩
          obtain ⟨j, hj⟩ := hS y y.2 i
          exact ⟨j, by rw [Subgroup.smul_def, MulAut.smul_def, hj]⟩ }
    let ρ := MulAction.toPermHom ↥Y ↥S
    have hρ : Function.Injective ρ := by
      rw [injective_iff_map_eq_one]
      intro y hy
      have hfix : ∀ i, (y : MulAut ↥(G6.coreMod 5)) (t828 i) = t828 i := fun i => by
        have h := congrArg (fun f : Equiv.Perm ↥S => ((f ⟨t828 i, i, rfl⟩ : ↥S) :
          ↥(G6.coreMod 5))) hy
        simpa [ρ, Subgroup.smul_def, MulAut.smul_def] using h
      exact Subtype.ext (eq_one_of_fix_t828 hfix)
    have hsign : ∀ y : ↥Y, ρ y ∈ alternatingGroup ↥S := by
      have hYp : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.mpr hperf
      intro y
      have hker := Abelianization.commutator_subset_ker (Equiv.Perm.sign.comp ρ)
      exact hker (Group.IsPerfect.mem_commutator (G := ↥Y))
    have hcardS : Fintype.card ↥S = 5 := by
      have : Nat.card ↥S = Nat.card (Set.range t828) := rfl
      rw [← Nat.card_eq_fintype_card, this, Nat.card_range_of_injective t828_injective,
        Nat.card_eq_fintype_card, Fintype.card_fin]
    have : Nontrivial ↥S := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    have halt : Fintype.card ↥(alternatingGroup ↥S) = 60 := by
      have h2 := two_mul_card_alternatingGroup (α := ↥S)
      rw [Fintype.card_perm, hcardS] at h2
      have : Nat.factorial 5 = 120 := by decide
      omega
    have hY60 : Nat.card ↥Y ≤ 60 := by
      rw [Nat.card_congr (MonoidHom.ofInjective hρ).toEquiv]
      have hle : ρ.range ≤ alternatingGroup ↥S := by
        rintro _ ⟨y, rfl⟩
        exact hsign y
      calc Nat.card ↥ρ.range ≤ Nat.card ↥(alternatingGroup ↥S) := Subgroup.card_le_of_le hle
        _ = 60 := by rw [Nat.card_eq_fintype_card, halt]
    exact (Subgroup.eq_of_le_of_card_ge hXY (by rw [card_range_alt5D_828]; exact hY60)).symm
  ·
    exfalso
    push Not at hS
    obtain ⟨y, hy, i, hyi⟩ := hS
    apply h9
    set O := MulAction.orbit ↥Y (t828 0) with hOdef
    have hX : ∀ γ : ↥(alternatingGroup (Fin 5)), alt5D_828 γ ∈ Y := fun γ => hXY ⟨γ, rfl⟩
    have hsmul : ∀ (a : ↥Y) (w : ↥(G6.coreMod 5)), a • w = (a : MulAut _) w := fun a w => rfl
    have hT : ∀ j, t828 j ∈ O := fun j => by
      refine ⟨⟨alt5D_828 ⟨zeta828 ^ (j : ℕ), Subgroup.pow_mem _ zeta828_mem _⟩, hX _⟩, ?_⟩
      show alt5D_828 _ (t828 0) = t828 j
      rw [alt5D_828_apply, coreAct_t828]
      exact congrArg t828 (zeta828_pow_zero j)
    have hOmem : ∀ (a : MulAut ↥(G6.coreMod 5)), a ∈ Y → ∀ w ∈ O, a w ∈ O := by
      intro a ha w hw
      obtain ⟨b, rfl⟩ := hw
      refine ⟨⟨a, ha⟩ * b, ?_⟩
      show (⟨a, ha⟩ * b : ↥Y) • t828 0 = a (b • t828 0)
      rw [mul_smul]
      rfl
    have he : (⟨Multiplicative.ofAdd evec828, by rw [G6.mem_coreMod]; decide⟩ :
        ↥(G6.coreMod 5)) ∈ O := by
      have hv : y (t828 i) ∈ O := hOmem y hy _ (hT i)
      have hv1 : y (t828 i) ≠ 1 := fun h =>
        t828_ne_one i (y.injective (h.trans (map_one y).symm))
      obtain ⟨γ, hγ⟩ := exists_alt5_e828 _ hv1 hyi
      have := hOmem (alt5D_828 γ⁻¹) (hX _) _ hv
      rw [hγ, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply] at this
      exact this
    have hO : ∀ w : ↥(G6.coreMod 5), w ≠ 1 → w ∈ O := by
      intro w hw
      by_cases hwS : ∃ j, w = t828 j
      · obtain ⟨j, rfl⟩ := hwS
        exact hT j
      · push Not at hwS
        obtain ⟨γ, hγ⟩ := exists_alt5_e828 w hw hwS
        rw [hγ]
        exact hOmem _ (hX γ) _ he
    have hO1 : ∀ w ∈ O, w ≠ 1 := by
      rintro _ ⟨a, rfl⟩ h
      change a • t828 0 = 1 at h
      rw [hsmul] at h
      exact t828_ne_one 0 ((a : MulAut _).injective (h.trans (map_one _).symm))
    have hcardO : Nat.card O = 15 := by
      have hOeq : O = {w | w ≠ 1} := Set.ext fun w => ⟨hO1 w, hO w⟩
      have h16 := Explicit.card_coreMod (n := 5) (by norm_num)
      rw [hOeq, show Nat.card ↥({w | w ≠ 1} : Set ↥(G6.coreMod 5)) =
          Nat.card {w : ↥(G6.coreMod 5) // ¬ w = 1} from rfl, Nat.card_eq_fintype_card,
        Fintype.card_subtype_compl, Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card, h16]
      rfl
    have hτ0 : tau828 0 = 0 := by decide
    let s : ↥(MulAction.stabilizer ↥Y (t828 0)) :=
      ⟨⟨alt5D_828 ⟨tau828, tau828_mem⟩, hX _⟩, by
        rw [MulAction.mem_stabilizer_iff, hsmul]
        show alt5D_828 _ (t828 0) = t828 0
        rw [alt5D_828_apply, coreAct_t828, hτ0]⟩
    have hs3 : orderOf s = 3 := by
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have h1 : orderOf (alt5D_828 ⟨tau828, tau828_mem⟩) = 3 := by
        apply orderOf_eq_prime
        · rw [← map_pow]
          have : (⟨tau828, tau828_mem⟩ : ↥(alternatingGroup (Fin 5))) ^ 3 = 1 :=
            Subtype.ext (by decide)
          rw [this, map_one]
        · intro h
          have h2 := congrArg (fun f : MulAut ↥(G6.coreMod 5) => f (t828 1)) h
          simp only [alt5D_828_apply, coreAct_t828, MulAut.one_apply] at h2
          have h3 : tau828 1 = 1 := t828_injective h2
          revert h3
          decide
      rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
      exact h1
    have h3 : 3 ∣ Nat.card ↥(MulAction.stabilizer ↥Y (t828 0)) := hs3 ▸ orderOf_dvd_natCard s
    have hos := MulAction.card_orbit_mul_card_stabilizer_eq_card_group ↥Y (t828 0)
    simp only [← Nat.card_eq_fintype_card] at hos
    rw [← hOdef, hcardO] at hos
    rw [← hos]
    obtain ⟨c, hc⟩ := h3
    rw [hc]
    exact ⟨5 * c, by ring⟩

end L828H

end CFSG.Quasithin.H13
