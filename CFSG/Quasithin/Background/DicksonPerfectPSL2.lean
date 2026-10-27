module

public import CFSG.Quasithin.Background.DicksonPerfectBasic
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonClassification
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality

public section

namespace CFSG.Quasithin.Dickson

open CFSG.Glauberman.Dickson CFSG.GorensteinWalter
open scoped commutatorElement

theorem not_isSolvable_alt_five : ¬ Group.IsSolvable (alternatingGroup (Fin 5)) := by
  have hnc : ¬ ∀ a b : alternatingGroup (Fin 5), a * b = b * a := by decide +kernel
  exact fun h => hnc (IsSimpleGroup.comm_iff_isSolvable.2 h)

theorem card_alt_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem dickson_prime_cases {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (L : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p))) :
    Group.IsSolvable L ∨ L = ⊤ ∨
      (Nonempty (L ≃* alternatingGroup (Fin 5)) ∧ (p = 5 ∨ 5 ∣ p ^ 2 - 1)) := by
  have hF : Nat.card (ZMod p) = p ^ 1 := by rw [Nat.card_zmod, pow_one]
  rcases huppert_II_8_27_dickson_psl2_subgroup_classification hF L with
    h1 | ⟨z, -, -, hcyc⟩ | ⟨z, -, -, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨h5, ⟨e⟩⟩ |
      ⟨m, t, -, -, N, C, hN, hNel, -, hC, -, -, hsup⟩ | ⟨m, hm, hmf, ⟨e⟩⟩ | ⟨m, hm, hmf, -⟩
  · have := h1.toIsMulCommutative
    exact Or.inl inferInstance
  · exact Or.inl inferInstance
  · have := isSolvable_dihedral z
    exact Or.inl (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)
  · have := alternatingGroup.isSolvable (α := Fin 4) (by simp)
    exact Or.inl (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)
  · have := Equiv.Perm.isSolvable (α := Fin 4) (by simp)
    exact Or.inl (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)
  · exact Or.inr (Or.inr ⟨⟨e⟩, by simpa using h5⟩)
  · left
    have := hN
    have hcomm : commutator L ≤ N :=
      Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup inferInstance
    have hNs : Group.IsSolvable N := by
      have := hNel.toIsMulCommutative
      infer_instance
    have hQs : Group.IsSolvable (L ⧸ N) := by
      have : IsMulCommutative (L ⧸ N) :=
        Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcomm
      infer_instance
    exact Group.isSolvable_of_subgroup_quotient N
  · right; left
    have hm1 : m = 1 := Nat.dvd_one.mp hmf
    subst hm1
    have hK : Nat.card (GaloisField p 1) = p ^ 1 := GaloisField.card p 1 one_ne_zero
    have hodd : Odd p := hp.out.odd_of_ne_two hp2
    have hc1 := psl2_card_formula (GaloisField p 1) ⟨p, 1, hp.out, hodd, le_rfl, hK⟩
    have hc2 := psl2_card_formula (ZMod p) ⟨p, 1, hp.out, hodd, le_rfl, hF⟩
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_congr e.toEquiv, hc1, hc2, hK, hF]
  · exfalso
    have := Nat.le_of_dvd one_pos hmf
    omega

theorem perfect_subgroup_psl2_prime
    {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (L : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)))
    (hperf : ⁅L, L⁆ = L) (hne : L ≠ ⊥) :
    L = ⊤ ∨ (Nonempty (L ≃* alternatingGroup (Fin 5)) ∧ (p = 5 ∨ 5 ∣ p ^ 2 - 1)) := by
  have hLp : Group.IsPerfect L := Subgroup.isPerfect_iff.mpr hperf
  have : Nontrivial L := (Subgroup.nontrivial_iff_ne_bot L).2 hne
  rcases dickson_prime_cases hp2 L with hs | h | h
  · exact (Group.IsPerfect.not_isSolvable L hs).elim
  · exact Or.inl h
  · exact Or.inr h

theorem overgroup_alternating_five_psl2_prime
    {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {M L : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p))} (hML : M ≤ L)
    (hM : Nonempty (M ≃* alternatingGroup (Fin 5))) : L = ⊤ ∨ Nat.card L = 60 := by
  obtain ⟨eM⟩ := hM
  rcases dickson_prime_cases hp2 L with hs | h | ⟨⟨e⟩, -⟩
  · exfalso
    have hMs : Group.IsSolvable M :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hML)
        (Subgroup.inclusion_injective hML)
    exact not_isSolvable_alt_five
      (Group.isSolvable_of_isSolvable_injective (f := eM.symm.toMonoidHom) eM.symm.injective)
  · exact Or.inl h
  · right
    rw [Nat.card_congr e.toEquiv, card_alt_five]

end CFSG.Quasithin.Dickson
