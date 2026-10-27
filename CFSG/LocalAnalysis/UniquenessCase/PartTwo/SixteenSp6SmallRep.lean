module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8CuClosure
public import CFSG.Quasithin.Background.SmithCurtisBasic
public import CFSG.ClassicalGroups.Symplectic.SmallF2Module
public import CFSG.ClassicalGroups.Symplectic.ProjectivePerfect

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin.SmithCurtis CFSG.LocalAnalysis.UniquenessCase.PartTwo.SpCurtis

theorem s16sm_g6_perfect : Group.IsPerfect G6 := by
  have : Group.IsPerfect (CFSG.Open.StatedSp 3 (ZMod 2)) :=
    CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp 3 (ZMod 2)
      (Or.inr (Or.inr ⟨Nat.card_zmod 2, le_rfl⟩))
  exact Group.IsPerfect.ofSurjective (f := g6Equiv.symm.toMonoidHom) g6Equiv.symm.surjective

theorem s16sm_inv_le_comap {M : Type} [AddCommGroup M] [Module (ZMod 2) M]
    (ρ : Representation (ZMod 2) G6 M) :
    ∀ g, ρ.invariants ≤ ρ.invariants.comap (ρ g) := fun g x hx => by
  rw [Submodule.mem_comap, (Representation.mem_invariants ρ x).1 hx g]
  exact hx

@[expose] noncomputable def s16smQ {M : Type} [AddCommGroup M] [Module (ZMod 2) M]
    (ρ : Representation (ZMod 2) G6 M) : Representation (ZMod 2) G6 (M ⧸ ρ.invariants) :=
  ρ.quotient ρ.invariants (s16sm_inv_le_comap ρ)

theorem s16smQ_mk {M : Type} [AddCommGroup M] [Module (ZMod 2) M]
    (ρ : Representation (ZMod 2) G6 M) (g : G6) (m : M) :
    s16smQ ρ g (Submodule.Quotient.mk m) = Submodule.Quotient.mk (ρ g m) :=
  rfl

theorem s16sm_fixed_quot {M : Type} [AddCommGroup M] [Module (ZMod 2) M]
    (ρ : Representation (ZMod 2) G6 M) (x : M ⧸ ρ.invariants)
    (hx : ∀ g, s16smQ ρ g x = x) : x = 0 := by
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective ρ.invariants x
  have hmem : ∀ g, ρ g m - m ∈ ρ.invariants := by
    intro g
    have h := hx g
    rw [s16smQ_mk] at h
    exact (Submodule.Quotient.eq ρ.invariants).mp h
  have hfix : ∀ g h, ρ g (ρ h m - m) = ρ h m - m := fun g h =>
    (Representation.mem_invariants ρ (ρ h m - m)).1 (hmem h) g
  let d : G6 →* Multiplicative M :=
    { toFun := fun g => Multiplicative.ofAdd (ρ g m - m)
      map_one' := by
        apply_fun Multiplicative.toAdd
        rw [toAdd_ofAdd, toAdd_one, map_one,
          Module.End.one_apply, sub_self]
      map_mul' := fun g h => by
        apply_fun Multiplicative.toAdd
        rw [toAdd_ofAdd, toAdd_mul,
          toAdd_ofAdd, toAdd_ofAdd]
        have hsub : ρ g (ρ h m) - ρ g m = ρ h m - m := by
          rw [← map_sub]
          exact hfix g h
        have h2 : ρ g (ρ h m) = (ρ h m - m) + ρ g m := eq_add_of_sub_eq hsub
        rw [map_mul, Module.End.mul_apply, h2]
        abel }
  have hd : d = 1 := by
    apply (MonoidHom.ker_eq_top_iff (f := d)).mp
    have hker := Abelianization.commutator_subset_ker d
    rw [s16sm_g6_perfect.commutator_eq_top] at hker
    exact top_le_iff.mp hker
  have h0 : ∀ g, ρ g m - m = 0 := by
    intro g
    have h1 : d g = 1 := by simpa using DFunLike.congr_fun hd g
    exact h1
  rw [Submodule.Quotient.mk_eq_zero]
  exact (Representation.mem_invariants ρ m).2 fun g => by
    have := h0 g
    rwa [sub_eq_zero] at this

theorem s16sm_trivial_of_finrank_le_five {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [Finite V] (ρ : Representation (ZMod 2) G6 V) (h : Module.finrank (ZMod 2) V ≤ 5)
    (g : G6) (v : V) : ρ g v = v := by
  have hdim : Module.finrank (ZMod 2) V < 2 * 3 := by omega
  let σ : CFSG.Open.StatedSp 3 (ZMod 2) →* (V ≃ₗ[ZMod 2] V) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).toMonoidHom.comp
      ((Representation.asGroupHom ρ).comp g6Equiv.symm.toMonoidHom)
  have hσ : σ = 1 :=
    CFSG.ClassicalGroups.Symplectic.eq_one_of_statedSp_of_finrank_lt (m := 3)
      (by norm_num) σ hdim
  have h2 : σ (g6Equiv g) v = ρ g v := by
    show (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V)
        ((Representation.asGroupHom ρ) (g6Equiv.symm (g6Equiv g))) v = ρ g v
    rw [MulEquiv.symm_apply_apply, ← Representation.asGroupHom_apply ρ g]
    exact congrArg (fun l : V →ₗ[ZMod 2] V => l v)
      (LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap (ρ.asGroupHom g))
  rw [← h2, hσ]
  rfl

theorem s16sm_exists_simple_sub {S : Type} [AddCommGroup S] [Module (ZMod 2) S] [Finite S]
    [Nontrivial S] (ρ : Representation (ZMod 2) G6 S) :
    ∃ (T : Submodule (ZMod 2) S) (hT : ∀ g, T ≤ T.comap (ρ g)),
      T ≠ ⊥ ∧ IsSimpleRep (ρ.subrepresentation T hT) := by
  classical
  let p : ℕ → Prop := fun n => ∃ T : Submodule (ZMod 2) S,
    (∀ g, T ≤ T.comap (ρ g)) ∧ T ≠ ⊥ ∧ Nat.card T = n
  have hex : ∃ n, p n := by
    refine ⟨_, ⊤, fun g => le_top, ?_, rfl⟩
    intro hbot
    obtain ⟨x, hx⟩ : ∃ x : S, x ≠ 0 := exists_ne 0
    have hx0 : x ∈ (⊥ : Submodule (ZMod 2) S) := by
      rw [← hbot]
      exact Submodule.mem_top
    exact hx ((Submodule.mem_bot (ZMod 2)).mp hx0)
  obtain ⟨T, hT, hTne, hcard⟩ := Nat.find_spec hex
  have hmin : ∀ T' : Submodule (ZMod 2) S, (∀ g, T' ≤ T'.comap (ρ g)) → T' ≠ ⊥ →
      Nat.card T ≤ Nat.card T' := by
    intro T' hT' hne
    have := Nat.find_min' hex ⟨T', hT', hne, rfl⟩
    rwa [← hcard] at this
  refine ⟨T, hT, hTne, ?_⟩
  haveI : Nontrivial T := Submodule.nontrivial_iff_ne_bot.mpr hTne
  refine ⟨inferInstance, fun W hW => ?_⟩
  by_cases hWbot : W = ⊥
  · exact Or.inl hWbot
  · refine Or.inr ?_
    rw [eq_top_iff]
    set W' : Submodule (ZMod 2) S := W.map T.subtype with hW'def
    have hW'le : W' ≤ T := Submodule.map_subtype_le T W
    have hW'stab : ∀ g, W' ≤ W'.comap (ρ g) := by
      intro g x hx
      rw [Submodule.mem_comap]
      obtain ⟨w, hw, hwx⟩ := Submodule.mem_map.mp hx
      have hmem : (ρ.subrepresentation T hT) g w ∈ W := hW g w hw
      have hthis : ((ρ.subrepresentation T hT) g w : T).1 ∈ W' :=
        Submodule.mem_map.mpr ⟨(ρ.subrepresentation T hT) g w, hmem, rfl⟩
      rw [← hwx]
      simpa [Representation.subrepresentation_apply] using hthis
    have hW'ne : W' ≠ ⊥ := by
      intro hbot
      apply hWbot
      rw [eq_bot_iff]
      intro w hw
      have hmem : (w : S) ∈ W' := Submodule.mem_map.mpr ⟨w, hw, rfl⟩
      rw [hbot] at hmem
      exact Subtype.ext ((Submodule.mem_bot (ZMod 2)).mp hmem)
    have hcardle : Nat.card T ≤ Nat.card W' := hmin W' hW'stab hW'ne
    have hmono : Nat.card W' ≤ Nat.card T :=
      Nat.card_mono (Set.toFinite (T : Set S)) hW'le
    have hWT : W' = T := by
      refine SetLike.ext' (Set.eq_of_subset_of_ncard_le hW'le ?_)
      rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
      exact hcardle
    intro w _
    have hmem : (w : S) ∈ W' := by
      rw [hWT]
      exact w.2
    obtain ⟨w', hw', hw'eq⟩ := Submodule.mem_map.mp hmem
    have hww : w' = w := Subtype.ext hw'eq
    simpa [hww] using hw'

theorem s16sm_dual_simple {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) G6 V) (h : IsSimpleRep ρ) :
    IsSimpleRep (Representation.dual ρ) := by
  haveI : Nontrivial V := h.1
  refine ⟨inferInstance, fun T hT => ?_⟩
  have hUstab : ∀ g, ∀ w ∈ T.dualCoannihilator, ρ g w ∈ T.dualCoannihilator := by
    intro g w hw
    rw [Submodule.mem_dualCoannihilator] at hw ⊢
    intro φ hφ
    have hφ' : (Representation.dual ρ) g⁻¹ φ ∈ T := hT g⁻¹ φ hφ
    have h0 := hw ((Representation.dual ρ) g⁻¹ φ) hφ'
    rwa [Representation.dual_apply, inv_inv, Module.Dual.transpose_apply,
      LinearMap.comp_apply] at h0
  have hT' : T.dualCoannihilator.dualAnnihilator = T :=
    Subspace.dualCoannihilator_dualAnnihilator_eq
  rcases h.2 T.dualCoannihilator hUstab with hU | hU
  · right
    rw [← hT', hU, Submodule.dualAnnihilator_bot]
  · left
    rw [← hT', hU, Submodule.dualAnnihilator_top]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
