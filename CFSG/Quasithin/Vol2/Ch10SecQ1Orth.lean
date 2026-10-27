module

public import CFSG.Quasithin.Vol2.Ch10SecAFacts
public import CFSG.Quasithin.Vol2.Ch5ModulesOrth

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.OrthFour
open scoped Matrix

theorem factOrthA5_holds : FactOrthA5 := by
  intro V _ H U Z h
  obtain ⟨K, _, _, _, hK, π₀, hπ₀⟩ := h
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  have h4 := f4_pow_four hK4
  obtain ⟨ω, hω⟩ := f4_exists_omega hK4
  obtain ⟨e, he⟩ := exists_equiv_alt hω h4 hK4
  obtain ⟨θ, hθ⟩ := exists_herm_equiv (K := K) hω h4
  have hAct := FFModel.altDn_isActionModel 5
  have hD : (FFModel.altDn 5).ker.subgroupOf (FFModel.altDn 5).sec = ⊥ := by
    have h0 : Subgroup.zpowers (G6.allOnes 5) ⊓ G6.coreMod 5 = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨hx1, hx2⟩
      rcases eq_one_or_eq_of_mem_zpowers allOnes_sq hx1 with rfl | rfl
      · exact Subgroup.one_mem _
      · exfalso
        have hx2' : G6.allOnes 5 ∈ G6.coreMod 5 := hx2
        revert hx2'
        rw [G6.mem_coreMod]
        decide +kernel
    show (Subgroup.zpowers (G6.allOnes 5) ⊓ G6.coreMod 5).subgroupOf (G6.coreMod 5) = ⊥
    rw [h0, Subgroup.bot_subgroupOf]
  refine ⟨π₀.comp e.symm.toMonoidHom, realizesVia_transfer (D := FFModel.altDn 5) hπ₀ e.symm θ.symm
    (Subgroup.bot_subgroupOf _) hD hAct.ker_le hAct.sec_inv hAct.ker_inv ?_⟩
  intro (γ : ↥(alternatingGroup (Fin 5))) m' hm'
  obtain ⟨n, rfl⟩ := θ.surjective m'
  have hγ : (γ : Equiv.Perm (Fin 5)) =
      f4PermHom hω h4 ((e.symm γ : ↥(Assembly.LowTwoRank.StatedSL 2 K)) : GL (Fin 2) K) := by
    rw [← he, MulEquiv.apply_symm_apply]
  show θ.symm ⟨twistAct 1 (Assembly.LowTwoRank.StatedSL 2 K) (e.symm γ)
      ((θ n : ↥(hermSub 1 (Fin 2) K)) : Multiplicative (Matrix (Fin 2) (Fin 2) K)), hm'⟩ =
    (⟨G6.permAct 5 (γ : Equiv.Perm (Fin 5)) ((θ.symm (θ n) : ↥(G6.coreMod 5)) : G6.PermMod 5),
      hAct.sec_inv γ _ (θ.symm (θ n)).2⟩ : ↥(G6.coreMod 5))
  rw [MulEquiv.symm_apply_eq]
  simp only [MulEquiv.symm_apply_apply]
  apply Subtype.ext
  show twistAct 1 (Assembly.LowTwoRank.StatedSL 2 K) (e.symm γ)
      ((θ n : ↥(hermSub 1 (Fin 2) K)) : Multiplicative (Matrix (Fin 2) (Fin 2) K)) =
    ((θ ⟨G6.permAct 5 (γ : Equiv.Perm (Fin 5)) (n : G6.PermMod 5), hAct.sec_inv γ _ n.2⟩ :
      ↥(hermSub 1 (Fin 2) K)) : Multiplicative (Matrix (Fin 2) (Fin 2) K))
  rw [hθ n, hθ]
  show Multiplicative.ofAdd
      ((((e.symm γ : ↥(Assembly.LowTwoRank.StatedSL 2 K)) : GL (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K) * f4Theta ω (Multiplicative.toAdd (n : G6.PermMod 5)) *
        (frobPow 1 (((e.symm γ : ↥(Assembly.LowTwoRank.StatedSL 2 K)) : GL (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K))ᵀ) =
    Multiplicative.ofAdd (f4Theta ω
      (fun i => Multiplicative.toAdd (n : G6.PermMod 5) ((γ : Equiv.Perm (Fin 5))⁻¹ i)))
  rw [hγ, f4Theta_perm hω h4]
  simp only [frobPow, pow_one]

end CFSG.Quasithin.Vol2.Ch10.SecA
