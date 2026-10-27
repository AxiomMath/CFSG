module

public import CFSG.Sporadic.HNOddCore.FiveI
public import Certificates.Certificate2085
public import Certificates.Certificate2096
public import Certificates.Certificate2097
public import Certificates.Certificate2100
public import Certificates.Certificate2102
public import Certificates.Certificate2104
public import Certificates.Certificate16041
public import Certificates.Certificate2107

public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier
open CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore.Native Equiv Equiv.Perm

theorem card_Hi5_fintype : Fintype.card {i : Fin 12 // Hi5 i} = 7 := by
  rw [← Nat.card_eq_fintype_card, card_Hi5]

theorem AJ_equiv_alt :
    Nonempty (AJ ≃* alternatingGroup (Fin 7)) :=
  ⟨(MulEquiv.ofBijective ahToAJ ahToAJ_bijective).symm.trans
    ((MulEquiv.ofBijective a7Hom a7Hom_bijective).trans
      ((Subgroup.equivMapOfInjective (alternatingGroup {i : Fin 12 // Hi5 i}) Perm.ofSubtype
        Perm.ofSubtype_injective).symm.trans
        (Equiv.altCongrHom (Fintype.equivFinOfCardEq card_Hi5_fintype))))⟩

theorem gamma0_parts : ∀ j < 50, (FAData.gamma[0]!).contains j = labPos.contains j := by
  decide +kernel

theorem gamma_base
    (j : Fin 50) : gammaAdj 0 j ↔ omPt j ∈ orbit7 := by
  rw [mem_orbit7_iff, orb7_iff_labPos, ← gamma0_parts j j.2, List.contains_iff_mem]
  rfl

theorem card_fiber17 :
    Nat.card fiber17 = 6 :=
  gamma_fiber 17 (MulAction.mem_orbit_self _)

theorem ctuc_hn_five_centralizer_perfect_factor :
    (∀ a ∈ Subgroup.zpowers fJ, ∀ b ∈ IJ, a * b = b * a) ∧ Subgroup.zpowers fJ ⊓ IJ = ⊥ ∧
    Subgroup.zpowers fJ ⊔ IJ = Subgroup.centralizer {fJ} ∧ orderOf fJ = 5 ∧
    Nat.card (Subgroup.centralizer {fJ}) = 630000 ∧ Nat.card IJ = 126000 ∧ ⁅IJ, IJ⁆ = IJ ∧
    ⁅Subgroup.centralizer {fJ}, Subgroup.centralizer {fJ}⁆ = IJ ∧
    omPt 0 = x0 ∧ (∀ g ∈ IJ, ∀ x ∈ Set.range omPt, g • x ∈ Set.range omPt) ∧
    (∀ g ∈ IJ, (∀ k, g • omPt k = omPt k) → g = 1) ∧
    MulAction.orbit IJ x0 = Set.range omPt ∧ AJ ≤ IJ ∧ (∀ g ∈ IJ, g • x0 = x0 ↔ g ∈ AJ) ∧
    Nonempty (AJ ≃* alternatingGroup (Fin 7)) ∧
    Set.range omPt = MulAction.orbit AJ x0 ∪ MulAction.orbit AJ (omPt 17) ∪
      MulAction.orbit AJ (omPt 1) ∧
    (MulAction.orbit AJ x0).ncard = 1 ∧ (MulAction.orbit AJ (omPt 17)).ncard = 7 ∧
    (MulAction.orbit AJ (omPt 1)).ncard = 42 ∧
    (∀ i, ¬ gammaAdj i i) ∧ (∀ i j, gammaAdj i j → gammaAdj j i) ∧
    (∀ i, Nat.card {j // gammaAdj i j} = 7) ∧
    (∀ j, gammaAdj 0 j ↔ omPt j ∈ MulAction.orbit AJ (omPt 17)) ∧
    (∀ i, omPt i ∈ MulAction.orbit AJ (omPt 1) →
      ∃! j, gammaAdj i j ∧ omPt j ∈ MulAction.orbit AJ (omPt 17)) ∧
    (∀ j, omPt j ∈ MulAction.orbit AJ (omPt 17) →
      Nat.card {i // omPt i ∈ MulAction.orbit AJ (omPt 1) ∧ gammaAdj i j} = 6) ∧
    Function.Injective labP ∧ (∀ j, omPt j ∈ MulAction.orbit AJ (omPt 17) ↔ ∃ i, labP i = j) ∧
    (∀ h ∈ AH, ∀ i j : Fin 7, (thetaJ h : Perm (Fin 12)) (let5 i) = let5 j →
      (h : JH) • omPt (labP i) = omPt (labP j)) ∧
    gammaAdj 0 17 ∧ KF ≤ AJ ∧ (∀ g ∈ KF, g • omPt 17 = omPt 17) ∧ Nat.card fiber17 = 6 ∧
    (∀ g ∈ KF, ∀ p ∈ omPt '' fiber17, g • p ∈ omPt '' fiber17) ∧
    ∀ x y x' y' : Fin 50, x ∈ fiber17 → y ∈ fiber17 → x' ∈ fiber17 → y' ∈ fiber17 → x ≠ y →
      x' ≠ y' → ∃ g ∈ KF, g • omPt x = omPt x' ∧ g • omPt y = omPt y' :=
  ⟨zpowers_comm_IJ, zpowers_inf_IJ, CF_eq, orderOf_fJ, card_CF, card_IJ, IJ_perfect, CF_derived,
    x0_eq_pt0, fun _ hg _ hx => mem_omega_of_comm (IJ_le_CJ hg) hx,
    fun _ hg h => IJ_faithful hg h, orbit_IJ, AJ_le_IJ, fun _ hg => stab_IJ hg, AJ_equiv_alt,
    omega_eq_union, ncard_orbit1, ncard_orbit7, ncard_orbit42, gamma_loopless,
    fun _ _ h => gamma_symm h, gamma_regular, gamma_base, gamma_unique_nbr, gamma_fiber,
    labP_injective, mem_orbit7_iff', fun h hh => labelEquiv_AH ⟨h, hh⟩,
    (gamma_base 17).2 (MulAction.mem_orbit_self _), KF_le_AJ, fun _ hg => KF_fix17 hg,
    card_fiber17, fun _ hg => KF_fiber hg,
    fun _ _ _ _ hx hy hx' hy' hxy hxy' => KF_two_transitive hx hy hx' hy' hxy hxy'⟩

end CFSG.Sporadic.HNOddCore
