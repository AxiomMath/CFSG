module

public import CFSG.Quasithin.AppendixH.H9.H92.OrthoCard
public import CFSG.Quasithin.AppendixH.H9.H92.CentSwap.SixDiagonalHom

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

theorem isSymNatural_swap :
    G6.IsSymNatural (Lg 5 ⊓ Subgroup.centralizer ({swapN 5} : Set (MulAut (PairN 5))))
      (commOn (fixV (Subgroup.zpowers (swapN 5)))
        (Lg 5 ⊓ Subgroup.centralizer ({swapN 5} : Set (MulAut (PairN 5))))) 6 := by
  obtain ⟨ρ, hρinj, hρorth, hρeq⟩ := exists_sixHom
  have hmem : ∀ σ : Equiv.Perm (Fin 6), pairActN 5 (ρ σ) ∈
      Lg 5 ⊓ Subgroup.centralizer ({swapN 5} : Set (MulAut (PairN 5))) :=
    fun σ => mem_inf_centralizer_swap_iff.mpr ⟨ρ σ, hρorth σ, rfl⟩
  let ρ' : Equiv.Perm (Fin 6) →*
      ↥(Lg 5 ⊓ Subgroup.centralizer ({swapN 5} : Set (MulAut (PairN 5)))) :=
    ((pairActN 5).comp ρ).codRestrict _ hmem
  have hinj : Function.Injective ρ' := fun σ τ h =>
    hρinj (pairActN_injective (congrArg Subtype.val h))
  haveI : Finite (MulAut (PairN 5)) :=
    Finite.of_injective (fun f : MulAut (PairN 5) => (f : PairN 5 → PairN 5))
      DFunLike.coe_injective
  have hperm : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  have hbij : Function.Bijective ρ' :=
    hinj.bijective_of_nat_card_le (by rw [hperm]; exact card_centralizer_swap_le)
  let θ : ↥(Lg 5 ⊓ Subgroup.centralizer ({swapN 5} : Set (MulAut (PairN 5)))) ≃*
      Equiv.Perm (Fin 6) := (MulEquiv.ofBijective ρ' hbij).symm
  unfold G6.IsSymNatural G6.IsSymModule
  refine ⟨θ, sixDiagHom, ?_, ?_, ?_⟩
  · intro x u
    obtain ⟨σ, rfl⟩ := hbij.2 x
    have hθ : θ (ρ' σ) = σ := (MulEquiv.ofBijective ρ' hbij).symm_apply_apply σ
    have hu : ∑ i, Multiplicative.toAdd (u : G6.PermMod 6) i = 0 := u.2
    have h1 := hρeq σ (Multiplicative.toAdd (u : G6.PermMod 6)) hu
    have h2 := pairActN_pairVec_of_orth (hρorth σ)
      (sixToFive (Multiplicative.toAdd (u : G6.PermMod 6)))
      (sixToFive (Multiplicative.toAdd (u : G6.PermMod 6)))
    have key : sixDiagHom (G6.coreAct 6 σ u) = pairActN 5 (ρ σ) (sixDiagHom u) :=
      (congrArg₂ pairVec h1 h1).trans h2.symm
    have hcore : G6.coreAct 6 (θ (ρ' σ)) u = G6.coreAct 6 σ u :=
      congrArg (fun τ => G6.coreAct 6 τ u) hθ
    exact (congrArg sixDiagHom hcore).trans key
  · exact range_sixDiagHom.trans commOn_fixV_swap_eq.symm
  · exact ker_sixDiagHom

end CFSG.ASVolI.ChH
