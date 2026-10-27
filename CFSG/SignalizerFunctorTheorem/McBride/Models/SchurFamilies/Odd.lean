module

public import CFSG.LocalAnalysis.SectionRank.OddCover.PSL2
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.PerfectOddCoverUnitary
import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryCentralCover

public section

open scoped MatrixGroups

namespace CFSG.SignalizerFunctorTheorem.McBride

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups

theorem schur_odd_psl2Three {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {J : Type*} [Group J] [Finite J]
    (hJ : Nonempty (J ≃* PSL(2, GaloisField 3 p)))
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E] (π : E →* J)
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    (hodd : Odd (Nat.card π.ker)) : π.ker = ⊥ := by
  obtain ⟨e⟩ := hJ
  have hK : Nat.card (GaloisField 3 p) = 3 ^ p := GaloisField.card 3 p hp.ne_zero
  have h9 : 3 ^ p ≠ 9 := fun h =>
    hp2 (Nat.pow_right_injective (by norm_num : 2 ≤ 3) (h.trans (by norm_num : (9 : ℕ) = 3 ^ 2)))
  let φ : E →* PSL(2, GaloisField 3 p) := e.toMonoidHom.comp π
  have hker : φ.ker = π.ker := MonoidHom.ker_comp_of_injective π e.toMonoidHom e.injective
  have h := (CFSG.SectionRank.OddCover.psl_two_perfect_odd_cover_kernel (p := 3) (f := p)
    (by norm_num) hK φ (e.surjective.comp hπ) (hker ▸ hcen) (hker ▸ hodd)).1 h9
  rwa [hker] at h

theorem schur_odd_psu3
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {J : Type*} [Group J] [Finite J]
    (hJ : Nonempty (J ≃* PSU3 2 p))
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E] (π : E →* J)
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    (hodd : Odd (Nat.card π.ker)) : Nat.card π.ker ∣ 3 := by
  obtain ⟨eJ⟩ := hJ
  have hf : 2 ≤ p := hp.two_le
  let K := FiniteField.Extension (GaloisField 2 p) 2 2
  let H := binaryQuadraticHermitian p (by omega)
  have hKcard : Nat.card K = (2 ^ p) ^ 2 := by
    rw [FiniteField.natCard_extension, GaloisField.card 2 p (by omega)]
  have hfixed : Nat.card {x : K // H.conj x = x} = 2 ^ p :=
    quadraticBinaryFrobenius_fixed_card p (by omega)
  let e : J ≃* ProjectiveSpecialUnitaryMatrixGroup H :=
    eJ.trans (CFSG.ShultStronglyClosedTI.unitaryCoverCanonicalEquiv p hf).symm
  let φ : E →* ProjectiveSpecialUnitaryMatrixGroup H := e.toMonoidHom.comp π
  have hker : φ.ker = π.ker := MonoidHom.ker_comp_of_injective π e.toMonoidHom e.injective
  obtain ⟨-, _, -, -, -, -, -, -, -, -, hdvd, -⟩ :=
    CFSG.ShultStronglyClosedTI.PerfectOddCover.perfect_odd_cover_unitary H p hf hKcard hfixed rfl φ
      (e.surjective.comp hπ) (hker ▸ hcen) (hker ▸ hodd)
  rw [hker] at hdvd
  have h3 : 3 ∣ 2 ^ p + 1 := by
    simpa using Odd.nat_add_dvd_pow_add_pow 2 1 (hp.odd_of_ne_two hp2)
  rwa [Nat.gcd_eq_left h3] at hdvd

end CFSG.SignalizerFunctorTheorem.McBride
