module

public import CFSG.Quasithin.AppendixH.H15.Vocab
public import CFSG.Quasithin.AppendixH.H16.OmegaPlus6Core

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI.H16

open CFSG.ASVolI.ChH CFSG.LargeExtraspecial CFSG.LargeExtraspecial.O62
  CFSG.RankThree.OrthogonalInvolutions CFSG.ASVolI.H16.OmegaPlus6

theorem isometryGroupG_qPlus6 :
    isometryGroupG (ZMod 2) (Fin 6) qPlus6 = TauCeti.QuadraticMap.orthogonalGroup qPlus := by
  ext g
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  change (∀ x, qPlus6 (g x) = qPlus6 x) ↔ _
  simp only [qPlus6, qPlus_apply]

theorem omegaN_qPlus6_eq :
    omegaN 6 qPlus6 = (omegaGroup qPlus qPlus_nondegenerate).map
      (linToMulAut (ZMod 2) (Fin 6 → ZMod 2)) := by
  rw [← commutator_orthogonalGroup_qPlus, ← isometryGroupG_qPlus6]
  rfl

theorem linToMulAut_injective' :
    Function.Injective (linToMulAut (ZMod 2) (Fin 6 → ZMod 2)) := by
  intro f g h
  refine LinearEquiv.ext fun x => ?_
  have := congrArg (fun a : MulAut (Multiplicative (Fin 6 → ZMod 2)) =>
    Multiplicative.toAdd (a (Multiplicative.ofAdd x))) h
  exact this

theorem exists_linToMulAut_eq (g : MulAut (Multiplicative (Fin 6 → ZMod 2))) :
    ∃ f : (Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2),
      linToMulAut (ZMod 2) (Fin 6 → ZMod 2) f = g := by
  let a : (Fin 6 → ZMod 2) ≃+ (Fin 6 → ZMod 2) := AddEquiv.toMultiplicative.symm g
  refine ⟨{ AddMonoidHom.toZModLinearMap 2 (a : (Fin 6 → ZMod 2) →+ (Fin 6 → ZMod 2)) with
    invFun := a.symm, left_inv := a.left_inv, right_inv := a.right_inv }, ?_⟩
  apply MulEquiv.ext
  intro x
  rfl

theorem eq_omegaN_qPlus6_of_card (I : Subgroup (MulAut (Multiplicative (Fin 6 → ZMod 2))))
    (hI : ∀ g ∈ I, ∀ x : Fin 6 → ZMod 2,
      qPlus6 (Multiplicative.toAdd (g (Multiplicative.ofAdd x))) = qPlus6 x)
    (hc : Nat.card I = 20160) : I = omegaN 6 qPlus6 := by
  have hrange : I ≤ (linToMulAut (ZMod 2) (Fin 6 → ZMod 2)).range := fun g _ => by
    obtain ⟨f, hf⟩ := exists_linToMulAut_eq g
    exact ⟨f, hf⟩
  have hmap := Subgroup.map_comap_eq_self hrange
  have hJc : Nat.card (I.comap (linToMulAut (ZMod 2) (Fin 6 → ZMod 2))) = 20160 := by
    have h1 : Nat.card ((I.comap (linToMulAut (ZMod 2) (Fin 6 → ZMod 2))).map
        (linToMulAut (ZMod 2) (Fin 6 → ZMod 2))) =
        Nat.card (I.comap (linToMulAut (ZMod 2) (Fin 6 → ZMod 2))) :=
      Subgroup.card_map_of_injective linToMulAut_injective'
    rw [hmap, hc] at h1
    exact h1.symm
  have hJO : I.comap (linToMulAut (ZMod 2) (Fin 6 → ZMod 2)) ≤
      TauCeti.QuadraticMap.orthogonalGroup qPlus := by
    intro f hf
    rw [← isometryGroupG_qPlus6]
    exact fun x => hI _ hf x
  have hJ := eq_omegaGroup_of_card _ hJO hJc
  rw [omegaN_qPlus6_eq, ← hJ, hmap]

end CFSG.ASVolI.H16
