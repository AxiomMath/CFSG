module

public import CFSG.RankThree.PartOne.S9.MinTwoAction.FiveActionLinearBasic
public import CFSG.RankThree.GroupTheory.SteinbergCDCentralPrimeActorField

public section

namespace CFSG.RankThree.PartOne.FiveAction.Lin

open CFSG CFSG.RankThree.GroupTheory

theorem exists_field_rep {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) (hq5 : q % 5 = 2 ∨ q % 5 = 3)
    {L : Type} [Group L] [Finite L] {b : L} (hb : b ∈ Subgroup.center L) (hbord : orderOf b = 5)
    {W : Type} [AddCommGroup W] [Module (ZMod q) W] [FiniteDimensional (ZMod q) W]
    (ρ : Representation (ZMod q) L W) (hρ : ρ.IsIrreducible) (hT : ρ b ≠ 1) :
    ∃ (E : Type) (_ : Field E) (_ : Module E W) (ρE : Representation E L W),
      (∀ g w, ρE g w = ρ g w) ∧ ρE.IsIrreducible ∧ (2 : E) ≠ 0 ∧
      ∀ g : L, Module.finrank (ZMod q) (Module.End.eigenspace (ρ g) 1) =
        4 * Module.finrank E (Module.End.eigenspace (ρE g) 1) := by
  have hq : q.Prime := Fact.out
  have : Nontrivial W := nontrivial_of_isIrreducible hρ
  let ρu : L →* LinearMap.GeneralLinearGroup (ZMod q) W := ρ.toHomUnits
  obtain ⟨E, hE⟩ : ∃ E : Subalgebra (ZMod q) (Module.End (ZMod q) W),
      E = Algebra.adjoin (ZMod q) {((ρu b : LinearMap.GeneralLinearGroup (ZMod q) W) :
        Module.End (ZMod q) W)} := ⟨_, rfl⟩
  obtain ⟨hEf, e, hEcard, -, hrest, he4⟩ := central_prime_actor_scalar_field_degree (p := 5)
    (q := q) (by norm_num) hq hb hbord ρu
    (fun U hU => eq_bot_or_eq_top_of_isIrreducible hρ U hU) (fun h => hT (congrArg Units.val h))
    E hE
  let _ : Field E := hEf.toField
  let _ : Module E W := Module.compHom W (E.val : E →+* Module.End (ZMod q) W)
  obtain ⟨hlin, hirrE, hfix⟩ := hrest
  let ρE : Representation E L W :=
    { toFun := fun g =>
        { toFun := fun w => ρ g w
          map_add' := fun v w => map_add (ρ g) v w
          map_smul' := fun c w => hlin g c w }
      map_one' := by
        refine LinearMap.ext fun w => ?_
        change ρ 1 w = w
        rw [map_one]
        rfl
      map_mul' := fun g h => by
        refine LinearMap.ext fun w => ?_
        change ρ (g * h) w = ρ g (ρ h w)
        rw [map_mul]
        rfl }
  refine ⟨E, inferInstance, inferInstance, ρE, fun g w => rfl, ?_, ?_, ?_⟩
  · exact isIrreducible_of_forall fun U hU => hirrE U fun g v hv => hU g v hv
  · intro h
    have h' : algebraMap (ZMod q) E 2 = 0 := by rw [map_ofNat]; exact h
    exact two_ne_zero_zmod hq hq2 ((algebraMap (ZMod q) E).injective (h'.trans (map_zero _).symm))
  · intro g
    obtain ⟨U, hUset, hdim⟩ := hfix g
    have h1 : Module.End.eigenspace (ρ g) 1 =
        LinearMap.ker ((ρu g : Module.End (ZMod q) W) - 1) := by
      ext w
      rw [Module.End.mem_eigenspace_iff, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero,
        one_smul]
      rfl
    have h2 : Module.End.eigenspace (ρE g) 1 = U := by
      ext w
      have hw : w ∈ U ↔ ρ g w = w := Set.ext_iff.mp hUset w
      refine (Module.End.mem_eigenspace_iff).trans (Iff.trans ?_ hw.symm)
      exact ⟨fun h => h.trans (one_smul E w), fun h => h.trans (one_smul E w).symm⟩
    rw [h1, h2, hdim, he4 rfl hq5]

end CFSG.RankThree.PartOne.FiveAction.Lin
