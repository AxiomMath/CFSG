module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSp6SmallQuot
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSp6SmallEight
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSp6SmallNat

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.SmithCurtis
  CFSG.LocalAnalysis.UniquenessCase.PartTwo.SpCurtis

@[expose] def S16SmSpinH1 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) G6 V), IsSimpleRep ρ → Module.finrank (ZMod 2) V = 8 →
      Module.finrank (ZMod 2) (H1 ρ) = 0

variable {M : Type} [AddCommGroup M] [Module (ZMod 2) M]

private theorem s16sm_isSimpleRep_of_invariants_eq_bot {M : Type} [AddCommGroup M]
    [Module (ZMod 2) M] [Nontrivial M] (ρ : Representation (ZMod 2) G6 M)
    (hC : ρ.invariants = ⊥) (h : IsSimpleRep (s16smQ ρ)) : IsSimpleRep ρ := by
  refine ⟨inferInstance, fun W hW => ?_⟩
  have hstab : ∀ g, ∀ s ∈ W.map (ρ.invariants).mkQ,
      s16smQ ρ g s ∈ W.map (ρ.invariants).mkQ := by
    intro g s hs
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hs
    have h1 : s16smQ ρ g ((ρ.invariants).mkQ w) = (ρ.invariants).mkQ (ρ g w) :=
      s16smQ_mk ρ g w
    rw [h1]
    exact Submodule.mem_map_of_mem (hW g w hw)
  rcases h.2 (W.map (ρ.invariants).mkQ) hstab with hbot | htop
  · left
    have hker : LinearMap.ker (ρ.invariants).mkQ = ⊥ := by rw [Submodule.ker_mkQ, hC]
    have hinj := LinearMap.map_injective hker
    exact hinj (hbot.trans (Submodule.map_bot _).symm)
  · right
    have hker : LinearMap.ker (ρ.invariants).mkQ = ⊥ := by rw [Submodule.ker_mkQ, hC]
    have hsurj : LinearMap.range (ρ.invariants).mkQ = ⊤ :=
      LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective _)
    have hsup := (LinearMap.map_eq_top_iff (f := (ρ.invariants).mkQ) hsurj).mp htop
    rwa [hker, sup_bot_eq] at hsup

private theorem s16sm_isSimpleRep_of_subrepresentation_top {S : Type} [AddCommGroup S]
    [Module (ZMod 2) S] (ρ : Representation (ZMod 2) G6 S) (T : Submodule (ZMod 2) S)
    (hT : ∀ g, T ≤ T.comap (ρ g)) (hTtop : T = ⊤)
    (h : IsSimpleRep (ρ.subrepresentation T hT)) : IsSimpleRep ρ := by
  haveI : Nontrivial T := h.1
  haveI : Nontrivial S := by
    obtain ⟨a, b, hab⟩ := exists_pair_ne T
    exact ⟨T.subtype a, T.subtype b, fun h => hab (T.subtype_injective h)⟩
  refine ⟨inferInstance, fun W hW => ?_⟩
  have hstab : ∀ g, ∀ t ∈ W.comap (T.subtype : T →ₗ[ZMod 2] S),
      (ρ.subrepresentation T hT) g t ∈ W.comap (T.subtype : T →ₗ[ZMod 2] S) := by
    intro g t ht
    rw [Submodule.mem_comap] at ht ⊢
    simpa using hW g (T.subtype t) ht
  rcases h.2 (W.comap (T.subtype : T →ₗ[ZMod 2] S)) hstab with hbot | htop
  · left
    have hself := Submodule.map_comap_eq_self (f := (T.subtype : T →ₗ[ZMod 2] S)) (q := W)
      (by rw [Submodule.range_subtype, hTtop]; exact le_top)
    rw [hbot, Submodule.map_bot] at hself
    exact hself.symm
  · right
    have hself := Submodule.map_comap_eq_self (f := (T.subtype : T →ₗ[ZMod 2] S)) (q := W)
      (by rw [Submodule.range_subtype, hTtop]; exact le_top)
    rw [htop, Submodule.map_top, Submodule.range_subtype, hTtop] at hself
    exact hself.symm

theorem s16sm_spin_case (hSpin : S16SmSpinH1) [Finite M] (ρ : Representation (ZMod 2) G6 M)
    (hperf : ∀ ψ : M →ₗ[ZMod 2] ZMod 2, (∀ g m, ψ (ρ g m) = ψ m) → ψ = 0)
    (hS : IsSimpleRep (s16smQ ρ)) (h8 : Module.finrank (ZMod 2) (M ⧸ ρ.invariants) = 8) :
    Module.finrank (ZMod 2) M = 8 ∧ ρ.invariants = ⊥ ∧ IsSimpleRep ρ := by
  classical
  haveI : Module.Finite (ZMod 2) M := Module.Finite.of_finite
  haveI : Finite (M ⧸ ρ.invariants) :=
    Finite.of_surjective (ρ.invariants).mkQ (Submodule.mkQ_surjective _)
  haveI : Module.Finite (ZMod 2) (M ⧸ ρ.invariants) := Module.Finite.of_finite
  have hq : Function.Surjective (ρ.invariants).mkQ := Submodule.mkQ_surjective _
  have hqρ : ∀ g m, (ρ.invariants).mkQ (ρ g m) = s16smQ ρ g ((ρ.invariants).mkQ m) :=
    fun g m => (s16smQ_mk ρ g m).symm
  have hZ : ∀ g m, (ρ.invariants).mkQ m = 0 → ρ g m = m := by
    intro g m hm
    exact (Representation.mem_invariants ρ m).1
      ((Submodule.Quotient.mk_eq_zero (ρ.invariants)).mp hm) g
  have hD : IsSimpleRep (Representation.dual (s16smQ ρ)) := s16sm_dual_simple (s16smQ ρ) hS
  haveI : Finite (Module.Dual (ZMod 2) (M ⧸ ρ.invariants)) :=
    Module.finite_of_finite (ZMod 2)
  have hD8 : Module.finrank (ZMod 2) (Module.Dual (ZMod 2) (M ⧸ ρ.invariants)) = 8 := by
    rw [Subspace.dual_finrank_eq, h8]
  have hH1 : Module.finrank (ZMod 2) (H1 (Representation.dual (s16smQ ρ))) = 0 :=
    hSpin (Module.Dual (ZMod 2) (M ⧸ ρ.invariants)) (Representation.dual (s16smQ ρ)) hD hD8
  have hle := finrank_ker_le_finrank_H1_dual ρ (s16smQ ρ) (ρ.invariants).mkQ hq hqρ hZ hperf
  rw [hH1] at hle
  have hkerbot : LinearMap.ker (ρ.invariants).mkQ = ⊥ :=
    (Submodule.finrank_eq_zero).mp (Nat.le_zero.mp hle)
  have hC : ρ.invariants = ⊥ := by
    rw [← Submodule.ker_mkQ (ρ.invariants)]
    exact hkerbot
  have hsum := Submodule.finrank_quotient_add_finrank (ρ.invariants)
  rw [h8, hC, finrank_bot] at hsum
  have hM8 : Module.finrank (ZMod 2) M = 8 := by omega
  haveI : Nontrivial M := Module.nontrivial_of_finrank_pos (R := ZMod 2) (M := M) (by omega)
  exact ⟨hM8, hC, s16sm_isSimpleRep_of_invariants_eq_bot ρ hC hS⟩

theorem s16sm_nat_case [Finite M] (ρ : Representation (ZMod 2) G6 M)
    (hperf : ∀ ψ : M →ₗ[ZMod 2] ZMod 2, (∀ g m, ψ (ρ g m) = ψ m) → ψ = 0)
    (β : (M ⧸ ρ.invariants) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2))
    (hβ : ∀ g s, β (s16smQ ρ g s) = natRep g (β s)) :
    Module.finrank (ZMod 2) (M ⧸ ρ.invariants) = 6 ∧
      Module.finrank (ZMod 2) ρ.invariants ≤ 1 := by
  classical
  have hq : Function.Surjective (ρ.invariants).mkQ := Submodule.mkQ_surjective _
  let q' : M →ₗ[ZMod 2] (Fin 6 → ZMod 2) := β.toLinearMap.comp (ρ.invariants).mkQ
  have hq' : Function.Surjective q' := β.surjective.comp hq
  have hq'ρ : ∀ g m, q' (ρ g m) = natRep g (q' m) := by
    intro g m
    change β ((ρ.invariants).mkQ (ρ g m)) = natRep g (β ((ρ.invariants).mkQ m))
    rw [show (ρ.invariants).mkQ (ρ g m) = s16smQ ρ g ((ρ.invariants).mkQ m) from
      (s16smQ_mk ρ g m).symm, hβ]
  have hZ' : ∀ g m, q' m = 0 → ρ g m = m := by
    intro g m hm
    have h1 : β ((ρ.invariants).mkQ m) = 0 := by simpa [q'] using hm
    have hqm : (ρ.invariants).mkQ m = 0 := β.injective (by rw [h1, map_zero])
    exact (Representation.mem_invariants ρ m).1
      ((Submodule.Quotient.mk_eq_zero (ρ.invariants)).mp hqm) g
  have hfin := s16sm_ker_le_one_nat ρ q' hq' hq'ρ hZ' hperf
  have hker : LinearMap.ker q' = LinearMap.ker (ρ.invariants).mkQ := by
    ext m
    rw [LinearMap.mem_ker, LinearMap.mem_ker]
    change β ((ρ.invariants).mkQ m) = 0 ↔ (ρ.invariants).mkQ m = 0
    constructor
    · intro h
      exact β.injective (by rw [h, map_zero])
    · intro h
      rw [h, map_zero]
  constructor
  · have hfr := β.finrank_eq
    rwa [Module.finrank_fin_fun] at hfr
  · rw [← Submodule.ker_mkQ (ρ.invariants), ← hker]
    exact hfin

theorem s16sm_main (hSpin : S16SmSpinH1) [Finite M] [Nontrivial M]
    (ρ : Representation (ZMod 2) G6 M)
    (hperf : ∀ ψ : M →ₗ[ZMod 2] ZMod 2, (∀ g m, ψ (ρ g m) = ψ m) → ψ = 0)
    (h8 : Module.finrank (ZMod 2) (M ⧸ ρ.invariants) ≤ 8) :
    (Module.finrank (ZMod 2) M = 8 ∧ ρ.invariants = ⊥ ∧ IsSimpleRep ρ) ∨
      (Module.finrank (ZMod 2) (M ⧸ ρ.invariants) = 6 ∧
        Module.finrank (ZMod 2) ρ.invariants ≤ 1) := by
  classical
  haveI : Finite (M ⧸ ρ.invariants) :=
    Finite.of_surjective (ρ.invariants).mkQ (Submodule.mkQ_surjective _)
  haveI : Module.Finite (ZMod 2) (M ⧸ ρ.invariants) := Module.Finite.of_finite
  haveI : Nontrivial (M ⧸ ρ.invariants) := s16sm_quot_nontrivial ρ hperf
  obtain ⟨T, hT, hTne, hTs⟩ := s16sm_exists_simple_sub (s16smQ ρ)
  haveI : Finite T :=
    Finite.of_injective (Subtype.val : T → M ⧸ ρ.invariants) Subtype.val_injective
  haveI : Module.Finite (ZMod 2) T := Module.Finite.of_finite
  have hTnt : ∃ g t, ((s16smQ ρ).subrepresentation T hT) g t ≠ t :=
    s16sm_sub_nontrivial_action ρ T hT hTne
  have hT8 : Module.finrank (ZMod 2) T ≤ 8 := (Submodule.finrank_le T).trans h8
  rcases s16sm_simple_small ((s16smQ ρ).subrepresentation T hT) hTs hTnt hT8 with
    hdim | ⟨β, hβ⟩
  · left
    have hTS : Module.finrank (ZMod 2) T = Module.finrank (ZMod 2) (M ⧸ ρ.invariants) :=
      le_antisymm (Submodule.finrank_le T) (by omega)
    have hTtop : T = ⊤ := Submodule.eq_top_of_finrank_eq hTS
    have hS8 : Module.finrank (ZMod 2) (M ⧸ ρ.invariants) = 8 := by omega
    exact s16sm_spin_case hSpin ρ hperf
      (s16sm_isSimpleRep_of_subrepresentation_top (s16smQ ρ) T hT hTtop hTs) hS8
  · right
    have hT6 : Module.finrank (ZMod 2) T = 6 := by
      have hfr := β.finrank_eq
      rwa [Module.finrank_fin_fun] at hfr
    have hquot : Module.finrank (ZMod 2) ((M ⧸ ρ.invariants) ⧸ T) ≤ 5 := by
      have hsum := Submodule.finrank_quotient_add_finrank T
      omega
    have hTtop : T = ⊤ := by
      by_contra hne
      obtain ⟨φ, hφne, hφ⟩ :=
        s16sm_exists_invariant_functional (s16smQ ρ) T hT hquot hne
      exact hφne (s16sm_quot_no_invariant_functional ρ hperf φ hφ)
    let e : (M ⧸ ρ.invariants) ≃ₗ[ZMod 2] T :=
      { toFun := fun s => ⟨s, by rw [hTtop]; exact Submodule.mem_top⟩
        invFun := fun t => (t : M ⧸ ρ.invariants)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        left_inv := fun _ => rfl
        right_inv := fun t => Subtype.ext rfl }
    let β' : (M ⧸ ρ.invariants) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2) := e.trans β
    have hβ' : ∀ g s, β' (s16smQ ρ g s) = natRep g (β' s) := by
      intro g s
      have h1 : e (s16smQ ρ g s) = ((s16smQ ρ).subrepresentation T hT) g (e s) :=
        Subtype.ext rfl
      change β (e (s16smQ ρ g s)) = natRep g (β (e s))
      rw [h1, hβ]
    exact s16sm_nat_case ρ hperf β' hβ'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
