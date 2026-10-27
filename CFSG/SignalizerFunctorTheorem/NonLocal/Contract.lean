module

public import Mathlib
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalizedStatements
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.FieldLinear
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.FieldUnitary
public import CFSG.SignalizerFunctorTheorem.NonLocal.LinearMain
public import CFSG.SignalizerFunctorTheorem.NonLocal.SpMain
public import CFSG.SignalizerFunctorTheorem.NonLocal.UHeisenberg
public import CFSG.RankThree.PartOne.KC.SymplecticSubfieldFixed
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Fischer.Uniq.CompTau
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Monster.Existence.Defs
public import CFSG.Open.MonsterY443Defs
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7

public section

open CFSG.SignalizerFunctorTheorem.CatalogBridge CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.LieType.Chevalley CFSG.RankThree.Classical CFSG.ClassicalGroups.UnitaryFlag

namespace CFSG.SignalizerFunctorTheorem.NonLocal

theorem subfieldNonLocalizedPSL : SubfieldNonLocalizedPSL := by
  intro K _ _ n hn p hp hodd hpT σ hσ _
  rw [fixed_fieldAut_eq_range hn hp hodd hpT hσ]
  exact nonLocalized_linearSubfield hn _

theorem subfieldNonLocalizedPSp : SubfieldNonLocalizedPSp := by
  intro K _ _ r hr p hp hodd hpT σ hσ _
  have : NeZero r := ⟨by omega⟩
  have hσp : σ ^ p = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  have hfix : signalizerFixedSubgroup (SymplecticHigher.fieldAut r K σ) =
      (CFSG.RankThree.PartOne.KCSpComm.subfieldProj (r := r) σ).range :=
    CFSG.RankThree.PartOne.KCSpComm.spFixedGroup_fieldAut_eq_range hodd hσp
  rw [hfix]
  exact nonLocalized_spSubfield hr σ

theorem subfieldNonLocalizedPSU :
    SubfieldNonLocalizedPSU := by
  intro ℓ f K _ h n hn p hp hodd hexc hpT σ hσ _
  have : Finite K := h.finite
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact absurd hodd (by decide)
  obtain ⟨hpf, -⟩ := dvd_and_card_fixSubfield_unitary h hp hp2 hσ
  have hq : ¬(n = 3 ∧ ℓ ^ f = 2) := by
    rintro ⟨-, h2⟩
    obtain ⟨-, hf1⟩ := (Nat.Prime.pow_eq_iff Nat.prime_two).mp h2
    rw [hf1] at hpf
    exact hp.one_lt.ne' (Nat.dvd_one.mp hpf)
  obtain ⟨eP⟩ := nonempty_primeFormP_mulEquiv h (isPrimeFormGram_one (n := n))
  have hpT' : ¬ p ∣ Nat.card (unitaryPSU h n) := by
    rwa [← Nat.card_congr eP.toEquiv]
  obtain ⟨-, -, hnp, -⟩ := unitary_prime_numerics h hn hq hp hodd hpT'
  obtain ⟨-, -, -, -, hrange, -⟩ :=
    higher_unitary_prime_subfield_fixed_group_and_full_centralizer h hn hnp hp hq σ hσ
  have hq₀ : ¬(n = 3 ∧ ℓ ^ (f / p) = 2) := by
    rintro ⟨hn3, h2⟩
    obtain ⟨hℓ2, hfp⟩ := Nat.prime_two.pow_eq_iff.mp h2
    exact hexc ⟨hn3, hℓ2, by rw [← Nat.div_mul_cancel hpf, hfp, one_mul]⟩
  have hCeq : signalizerFixedSubgroup
      (primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ) = fieldFixedPSU h n σ :=
    Subgroup.ext fun x => Iff.rfl
  rw [hCeq, ← hrange]
  exact nonLocalized_unitarySubfield h (fixSubfield_unitaryFieldData h hp hp2 hσ)
    (fixSubfield_unitaryFieldData_bar h hp hp2 hσ) hn hq₀

end CFSG.SignalizerFunctorTheorem.NonLocal
