module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.O6m4L2FixFree.Defs
import CFSG.Quasithin.Background.B4ModelsIso
import CFSG.Quasithin.EmptyFaithful.SzN15Nat

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.O6m4FF

open Matrix CFSG.Open CFSG.Quasithin

theorem exists_coords_of_natOmegaMinus {W : Type} [CommGroup W] {X : Subgroup (MulAut W)}
    {I : Subgroup W} {a : ℕ} (hN : NatOmegaMinus X I ⊥ 6 a) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (b c : F), Nat.card F = 2 ^ a ∧
      (∀ s : F, s ^ 2 + b * s + c ≠ 0) ∧
      ∃ (ε : ↥X ≃* ↥(Omega6 F b c)) (ψ : ↥I ≃* Multiplicative (Idx → F)),
        ∀ (x : ↥X) (s : ↥I) (hx : (x : MulAut W) (s : W) ∈ I),
          ψ ⟨(x : MulAut W) (s : W), hx⟩ = Multiplicative.ofAdd
            (((ε x : GL Idx F) : Matrix Idx Idx F).mulVec (Multiplicative.toAdd (ψ s))) := by
  classical
  obtain ⟨-, K, hK, hKf, b, c, hK2, hpoly, π, hπ⟩ := hN
  letI := hK
  haveI : Finite K := hKf
  let Γ := StatedOmega (StatedQuadMinus 3 K b c)
  have hNR : CFSG.Quasithin.SzN15.NatReal X I ⊥ Γ π :=
    CFSG.Quasithin.SzN15.NatReal.of_realizesVia hπ
  obtain ⟨β, hβsurj, hβker, hβe⟩ := hNR.exists_β
  have hβinj : Function.Injective β := by
    intro u u' hab
    have h1 : β (u * u'⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h2 : ((u * u'⁻¹ : ↥I) : W) ∈ (⊥ : Subgroup W) := (hβker (u * u'⁻¹)).1 h1
    have h3 : u * u'⁻¹ = 1 := Subtype.ext (by simpa using Subgroup.mem_bot.1 h2)
    exact mul_inv_eq_one.1 h3
  have hπinj : Function.Injective π := by
    rw [injective_iff_map_eq_one]
    intro γ hγ
    apply natAct_faithful Γ γ
    intro m
    obtain ⟨u, rfl⟩ := hβsurj m
    have hmem : ((π γ : ↥X) : MulAut W) (u : W) ∈ I := hNR.U_inv (π γ) u u.2
    have h1 := hβe γ u hmem
    have h2 : (⟨((π γ : ↥X) : MulAut W) (u : W), hmem⟩ : ↥I) = u :=
      Subtype.ext (by simp [hγ])
    have h1' : β u = natAct Γ γ (β u) := (congrArg β h2.symm).trans h1
    rw [← h1']
    exact mul_inv_cancel _
  let πe : ↥Γ ≃* ↥X := MulEquiv.ofBijective π ⟨hπinj, hπ.1⟩
  let ψ : ↥I ≃* Multiplicative (Idx → K) := MulEquiv.ofBijective β ⟨hβinj, hβsurj⟩
  refine ⟨K, hK, hKf, b, c, hK2, hpoly, πe.symm, ψ, ?_⟩
  intro x s hx
  obtain ⟨γ, rfl⟩ : ∃ γ, πe γ = x := πe.surjective x
  rw [MulEquiv.symm_apply_apply]
  exact hβe γ s hx

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.O6m4FF
