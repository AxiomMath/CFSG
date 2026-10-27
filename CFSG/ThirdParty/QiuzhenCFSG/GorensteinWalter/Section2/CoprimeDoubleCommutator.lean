module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.CoprimeAction
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj

namespace CFSG
end CFSG
open CFSG

/-!
# Coprime double-commutator collapse

For a coprime subgroup action, the first and second action commutators
coincide.  Thus a trivial double commutator forces the first commutator to
be trivial.
-/

open scoped Pointwise commutatorElement

namespace CFSG.GorensteinWalter

universe u

/-- If `R` acts on `W` with coprime orders and `[[W,R],R]=1`, then
`[W,R]=1`. -/
public theorem commutator_eq_bot_of_coprime_double_commutator_eq_bot
    {Q : Type u} [Group Q] [Finite Q]
    (W R : Subgroup Q)
    (hRnormW : R ≤ Subgroup.normalizer (W : Set Q))
    (hcoprime : Nat.Coprime (Nat.card R) (Nat.card W))
    (hdouble : ⁅⁅W, R⁆, R⁆ = (⊥ : Subgroup Q)) :
    ⁅W, R⁆ = (⊥ : Subgroup Q) := by
  classical
  haveI : Subgroup.Normalizes R W := ⟨hRnormW⟩
  have hcommAction2_eq_commAction :
      commutatorAction₂ (A := R) (G := W) =
        commutatorAction (A := R) (G := W) :=
    commutatorAction₂_eq_commutatorAction_of_coprime
      (G := W) (A := R) hcoprime
  have hcommAction_map :
      (commutatorAction (A := R) (G := W)).map W.subtype = ⁅W, R⁆ := by
    simpa using commutatorAction_subgroup_conj_map_eq_commutator W R hRnormW
  have hcommAction2_map_le :
      (commutatorAction₂ (A := R) (G := W)).map W.subtype ≤ ⁅⁅W, R⁆, R⁆ := by
    let C : Subgroup W := commutatorAction (A := R) (G := W)
    let S : Set W :=
      {x : W | ∃ a : R, ∃ h : W, h ∈ C ∧ x = h⁻¹ * (a • h)}
    calc
      (commutatorAction₂ (A := R) (G := W)).map W.subtype =
          (Subgroup.closure S).map W.subtype := by
        rfl
      _ = Subgroup.closure (W.subtype '' S) := by
        simpa using (MonoidHom.map_closure (f := W.subtype) S)
      _ ≤ ⁅⁅W, R⁆, R⁆ := by
        refine (Subgroup.closure_le (K := ⁅⁅W, R⁆, R⁆)).2 ?_
        rintro _ ⟨y, hy, rfl⟩
        rcases hy with ⟨a, h, hhC, rfl⟩
        have hhcomm : (h : Q) ∈ ⁅W, R⁆ := by
          rw [← hcommAction_map]
          exact Subgroup.mem_map_of_mem W.subtype hhC
        have hcomm : ⁅(h : Q)⁻¹, (a : Q)⁆ ∈ ⁅⁅W, R⁆, R⁆ :=
          Subgroup.commutator_mem_commutator
            ((⁅W, R⁆ : Subgroup Q).inv_mem hhcomm) a.2
        simpa [commutatorElement_def,
          Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe,
          hRnormW, mul_assoc] using hcomm
  have hle : ⁅W, R⁆ ≤ (⊥ : Subgroup Q) := by
    intro x hx
    have hx_commAction :
        x ∈ (commutatorAction (A := R) (G := W)).map W.subtype := by
      rwa [hcommAction_map]
    have hx_commAction2 :
        x ∈ (commutatorAction₂ (A := R) (G := W)).map W.subtype := by
      rwa [hcommAction2_eq_commAction]
    have hx_double := hcommAction2_map_le hx_commAction2
    rwa [hdouble] at hx_double
  exact le_antisymm hle bot_le

end CFSG.GorensteinWalter
