module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.OddIdx.Core
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3Final
public import CFSG.Quasithin.EmptyFaithful.A38c17Red
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1R925Pure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.OddIdx

open CFSG.Quasithin CFSG.Quasithin.A38c15 CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)

set_option linter.unusedSectionVars false

section Certified


theorem oddIdxProp_psu3_prime {K : Type} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hq : p % 3 = 1) (hU : LieModel K .PSU 3 p 1) : OddIdxProp K := by
  intro N Y D hN hodd hD hDY hYN hnorm hY hNK
  haveI : Fact p.Prime := ⟨hp⟩
  have hp3 : p ≠ 3 := by
    intro h
    subst h
    norm_num at hq
  have hp5 : p ≠ 5 := by
    intro h
    subst h
    norm_num at hq
  obtain ⟨-, F, hFld, hFfin, hFcard, ⟨e⟩⟩ := hU.statedClassicalModel (by decide)
  letI := hFld
  haveI := hFfin
  have h3 : ¬ 3 ∣ p + 1 := by
    intro hd
    have h0 : (p + 1) % 3 = 0 := Nat.mod_eq_zero_of_dvd hd
    omega
  have hZcard : Nat.card ((StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 (p ^ 1) F)) = 1 := by
    rw [(CFSG.LinearGroups.unitary_scalar_kernel hp hFcard (n := 3) (by norm_num)).2.2,
      pow_one, ← Nat.coprime_iff_gcd_eq_one]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
  have hZbot : (StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 (p ^ 1) F) = ⊥ :=
    Subgroup.card_eq_one.mp hZcard
  let e' : K ≃* ↥(StatedSU 3 (p ^ 1) F) :=
    e.trans ((QuotientGroup.quotientMulEquivOfEq hZbot).trans QuotientGroup.quotientBot)
  let M : Subgroup ↥(StatedSU 3 (p ^ 1) F) := N.map e'.toMonoidHom
  have hModd : Odd M.index := by
    show Odd (N.map e'.toMonoidHom).index
    rw [Subgroup.index_map_of_bijective (f := e'.toMonoidHom) e'.bijective N]
    exact hodd
  have hMne : M ≠ ⊤ := by
    intro htop
    apply hN
    have hMc : M.comap e'.toMonoidHom = N := by
      show (N.map e'.toMonoidHom).comap e'.toMonoidHom = N
      rw [Subgroup.comap_map_eq_self_of_injective e'.injective N]
    rw [htop, Subgroup.comap_top] at hMc
    exact hMc.symm
  have hF2 : Nat.card F = p ^ 2 := by rw [hFcard, pow_one]
  rcases CFSG.Quasithin.A38c17.sylowCoreSUZ_of
      (CFSG.Quasithin.A38c17.su3ReducibleOdd CFSG.Quasithin.A38c15.gl2OddIndex)
      CFSG.Quasithin.A312U3.su3OddIrr_A38c17_holds hp2 (pow_one p) hF2 M hModd hMne with
    hs | hsl | h5case
  · haveI : Group.IsSolvable ↥M := hs
    haveI : Group.IsSolvable ↥N :=
      Group.isSolvable_of_isSolvable_injective
        (f := (N.equivMapOfInjective e'.toMonoidHom e'.injective).toMonoidHom)
        (MulEquiv.injective _)
    have hYsolv : Group.IsSolvable ↥Y :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hYN)
        (Subgroup.inclusion_injective hYN)
    haveI : Group.IsPerfect ↥Y := Group.isPerfect_def.mpr hY.1
    obtain ⟨D0, hD0⟩ := hY.exists_card_three
    haveI : Nontrivial ↥D0 := by
      rw [← Finite.one_lt_card_iff_nontrivial, hD0]
      norm_num
    obtain ⟨d, hd⟩ := exists_ne (1 : ↥D0)
    haveI : Nontrivial ↥Y := ⟨⟨d.1, 1, fun h => hd (Subtype.ext h)⟩⟩
    exfalso
    exact (Group.IsPerfect.not_isSolvable ↥Y) hYsolv
  · have hcore : ↥(perfectCore N) ≃* ↥(perfectCore M) :=
      ((perfectCore N).equivMapOfInjective e'.toMonoidHom e'.injective).trans
        (MulEquiv.subgroupCongr (map_perfectCore e'.toMonoidHom N))
    have hlevi : IsLeviBlock p ↥(perfectCore N) := Or.inl (IsSL2.of_mulEquiv hcore.symm hsl)
    exact absurd (conclusion_of_levi hp hp2 hp3 hYN hY hNK hlevi).1 hp5
  · exact absurd h5case.1 hp5

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.OddIdx
