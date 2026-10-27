module

public import CFSG.Quasithin.Vol2.Ch5ModulesOrth
public import CFSG.Quasithin.H13.A7FiveFixed

public section

namespace CFSG.Quasithin.H13

open scoped Matrix

namespace OrthFour

theorem binaryOrthogonalFour_one_of_alternatingNatural_five {W : Type*} [CommGroup W]
    {H : Subgroup (MulAut W)} {U Z : Subgroup W} (h : AlternatingNatural H U Z 5) :
    BinaryOrthogonalFour H U Z 1 := by
  obtain ⟨π₀, hπ₀⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK4 : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  have : CharP (GaloisField 2 2) 2 := inferInstance
  have h4 := f4_pow_four hK4
  obtain ⟨ω, hω⟩ := f4_exists_omega hK4
  obtain ⟨e, he⟩ := exists_equiv_alt hω h4 hK4
  obtain ⟨θ, hθ⟩ := exists_herm_equiv (K := GaloisField 2 2) hω h4
  have hAct := FFModel.twistTensor_isActionModel 1
    (Assembly.LowTwoRank.StatedSL 2 (GaloisField 2 2)) (by rw [hK4]; norm_num)
  have hD' : (FFModel.altDn 5).ker.subgroupOf (FFModel.altDn 5).sec = ⊥ := by
    rw [A7.altDn_five_ker_eq_bot, Subgroup.bot_subgroupOf]
  refine ⟨GaloisField 2 2, inferInstance, inferInstance, inferInstance, by rw [hK4]; norm_num,
    π₀.comp e.toMonoidHom, realizesVia_transfer
      (D := FFModel.twistTensor 1 (Assembly.LowTwoRank.StatedSL 2 (GaloisField 2 2)))
      hπ₀ e θ hD' (Subgroup.bot_subgroupOf _) hAct.ker_le hAct.sec_inv hAct.ker_inv ?_⟩
  intro (γ : ↥(Assembly.LowTwoRank.StatedSL 2 (GaloisField 2 2))) m' hm'
  have key : ∀ x : Fin 5 → ZMod 2, f4Theta ω (fun i => x ((f4PermHom hω h4
      ((γ : ↥(Assembly.LowTwoRank.StatedSL 2 (GaloisField 2 2))) : GL (Fin 2) (GaloisField 2 2)))⁻¹
        i)) =
      (((γ : ↥(Assembly.LowTwoRank.StatedSL 2 (GaloisField 2 2))) :
          GL (Fin 2) (GaloisField 2 2)) : Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) *
        f4Theta ω x *
        (frobPow 1 (((γ : ↥(Assembly.LowTwoRank.StatedSL 2 (GaloisField 2 2))) :
          GL (Fin 2) (GaloisField 2 2)) : Matrix (Fin 2) (Fin 2) (GaloisField 2 2)))ᵀ := by
    intro x
    rw [f4Theta_perm hω h4]
    simp only [frobPow, pow_one]
  apply Subtype.ext
  have h1 := hθ ⟨G6.permAct 5 ((e γ : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5))
    (show G6.PermMod 5 from m'.1), hm'⟩
  have h2 := hθ m'
  refine h1.trans ?_
  show _ = Multiplicative.ofAdd
      ((((γ : ↥(Assembly.LowTwoRank.StatedSL 2 (GaloisField 2 2))) :
          GL (Fin 2) (GaloisField 2 2)) : Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) *
        Multiplicative.toAdd ((θ m' : ↥(hermSub 1 (Fin 2) (GaloisField 2 2))) :
          Multiplicative (Matrix (Fin 2) (Fin 2) (GaloisField 2 2))) *
        (frobPow 1 (((γ : ↥(Assembly.LowTwoRank.StatedSL 2 (GaloisField 2 2))) :
          GL (Fin 2) (GaloisField 2 2)) : Matrix (Fin 2) (Fin 2) (GaloisField 2 2)))ᵀ)
  rw [h2, toAdd_ofAdd, ← key]
  congr 2
  funext i
  show Multiplicative.toAdd (show G6.PermMod 5 from m'.1)
      (((e γ : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5))⁻¹ i) = _
  rw [he γ]

end OrthFour

end CFSG.Quasithin.H13
