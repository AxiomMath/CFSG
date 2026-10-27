module

public import CFSG.Assembly.Defs
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.GroupTheory.FixedPointQuotientCard
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Quotient
public import CFSG.GroupTheory.SupCommute
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T2021RankHolds
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.CoverOneCore
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonSetup
public import CFSG.GroupTheory.SteinbergCBFTCores
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFInputs
public import CFSG.Holt.Centralizer
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeSL
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeSpin
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeSpinMinus
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.CommutatorFixed
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.FixedPointsTwo
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.PairSepAssembly
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.CoverCtx
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TRAssemble
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TightSep
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.AltBigVector
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.AltFixed
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.OrthModel
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SLModel
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SpModel
public import CFSG.LocalAnalysis.EvenBN.Common.CommutatorFixed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsSetup
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
public import CFSG.LocalAnalysis.GLTheoremA.S12.Bridge
public import CFSG.LocalAnalysis.GLTheoremA.S12.Prop123
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionComponent
public import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
public import CFSG.RankThree.PartTwo.Sec14.Item143N
public import CFSG.RankThree.PartTwo.Sec15.Item157
public import CFSG.RankThree.PartTwo.Sec16.Item163ProofR
public import CFSG.RankThree.PartTwo.Sec16.Item164Proof
public import CFSG.RankThree.PartTwo.Sec16.Item169HJ
public import CFSG.RankThree.PartTwo.Sec16.Item16Tail22
public import CFSG.RankThree.PartTwo.Sec17.Item1724Two
public import CFSG.RankThree.PartTwo.Sec17.Item17TailSteps
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers142
public import CFSG.RankThree.PartTwo.Sec20.Item20ResProofCases
public import CFSG.RankThree.PartTwo.Sec20.Step204RestProof
public import CFSG.RankThree.PartTwo.Sec20.Step2051Proof
public import CFSG.RankThree.PartTwo.Sec20.Step2051SylowProof
public import CFSG.RankThree.PartTwo.Sec20.Step2053Proof
public import CFSG.RankThree.PartTwo.Sec4.T444.Basic
public import CFSG.RankThree.PartTwo.Toolkit.M12Local
public import CFSG.RankThree.S4Free.SuzukiEight
public import Certificates.Certificate8166

public section

namespace CFSG.StandardType

open CFSG.Assembly

private theorem not_mem_of_centralizes_of_center_not_dvd {H : Type} [Group H] [Finite H]
    {J : Subgroup H} {z : H} (hz1 : z ≠ 1) (hz3 : z ^ 3 = 1)
    (hzJ : J ≤ Subgroup.centralizer ({z} : Set H))
    (hZJ : ¬ 3 ∣ Nat.card (Subgroup.center J)) : z ∉ J := by
  intro hzJmem
  have hzcenter : (⟨z, hzJmem⟩ : J) ∈ Subgroup.center J := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp (hzJ y.2)
  have hzpowle : Subgroup.zpowers (⟨z, hzJmem⟩ : J) ≤ Subgroup.center J :=
    Subgroup.zpowers_le.mpr hzcenter
  have hzcard : Nat.card (Subgroup.zpowers (⟨z, hzJmem⟩ : J)) = 3 := by
    rw [Nat.card_zpowers, Subgroup.orderOf_mk]
    exact orderOf_eq_prime hz3 hz1
  apply hZJ
  rw [← hzcard]
  exact Subgroup.card_dvd_of_le hzpowle

private theorem mapQuotient_center_eq_quotientAut {J : Type*} [Group J] (β : MulAut J) :
    MulAut.mapQuotient (Subgroup.center J) β = quotientAut β := by
  classical
  ext q
  induction q using QuotientGroup.induction_on with
  | H j => simpa [QuotientGroup.mk'_apply] using (quotientAut_mk β j).symm

private theorem exists_inner_of_quotient_conj {H : Type} [Group H] [Finite H]
    {J : Subgroup H} (hJ : commutator J = ⊤) {g : H} {β : MulAut J}
    (hβ : ∀ y : J, (β y : H) = g * y * g⁻¹)
    {x : J ⧸ Subgroup.center J}
    (hx : MulAut.mapQuotient (Subgroup.center J) β = MulAut.conj x) :
    ∃ x₀ ∈ J, ∀ y ∈ J, g * y * g⁻¹ = x₀ * y * x₀⁻¹ := by
  classical
  obtain ⟨x₀, hx₀⟩ := QuotientGroup.mk'_surjective (Subgroup.center J) x
  have hconjquot : MulAut.mapQuotient (Subgroup.center J) (MulAut.conj x₀) =
      MulAut.conj x := by
    ext q
    induction q using QuotientGroup.induction_on with
    | H j =>
      rw [MulAut.mapQuotient_mk]
      change (QuotientGroup.mk' (Subgroup.center J) ((MulAut.conj x₀) j)) =
        (MulAut.conj x) (QuotientGroup.mk' (Subgroup.center J) j)
      rw [MulAut.conj_apply, map_mul, map_mul, map_inv, hx₀, MulAut.conj_apply]
  have hmapmul : MulAut.mapQuotient (Subgroup.center J)
      (β * (MulAut.conj x₀)⁻¹) = 1 := by
    rw [map_mul, map_inv, hx, hconjquot, mul_inv_cancel]
  have hβeq : β = MulAut.conj x₀ := by
    have h := CFSG.LocalAnalysis.GLTheoremA.T2021.eq_one_of_mapQuotient_center_eq_one hJ
      (β * (MulAut.conj x₀)⁻¹) hmapmul
    calc β = β * (MulAut.conj x₀)⁻¹ * MulAut.conj x₀ := by group
      _ = MulAut.conj x₀ := by rw [h, one_mul]
  refine ⟨x₀, x₀.2, fun y hy => ?_⟩
  let yJ : J := ⟨y, hy⟩
  have hy' : (β yJ : H) = g * y * g⁻¹ := hβ yJ
  rw [hβeq] at hy'
  simpa [yJ, MulAut.conj_apply] using hy'.symm

private theorem exists_fixed_elemAbelian_E27 {H : Type} [Group H] [Finite H]
    {J : Subgroup H} (hZJ : ¬ 3 ∣ Nat.card (Subgroup.center J))
    {g : H} {β : MulAut J} (hβ : ∀ y : J, (β y : H) = g * y * g⁻¹)
    (hβ3 : β ^ 3 = 1)
    {A : Subgroup (J ⧸ Subgroup.center J)}
    (hAel : IsElemAbelian 3 A) (hAcard : Nat.card A = 3 ^ 3)
    (hfix : ∀ a ∈ A, quotientAut β a = a) :
    ∃ E : Subgroup H, E ≤ J ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 3 ∧
      E ≤ Subgroup.centralizer ({g} : Set H) := by
  classical
  let Z : Subgroup J := Subgroup.center J
  let C : Subgroup H := Subgroup.centralizer ({g} : Set H) ⊓ J
  let ψ : ↥C →* J ⧸ Z :=
    (QuotientGroup.mk' Z).comp (Subgroup.inclusion (inf_le_right : C ≤ J))
  have hCsub : C.subgroupOf J = autFixedSubgroup β := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_autFixedSubgroup]
    constructor
    · rintro ⟨hxcent, -⟩
      apply Subtype.ext
      have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hxcent
      rw [hβ x, ← hcomm]
      group
    · intro hx
      refine ⟨?_, x.2⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hx' : g * (x : H) * g⁻¹ = (x : H) := by
        have := congrArg Subtype.val hx
        simpa [hβ x] using this
      have hx'' : g * (x : H) = (x : H) * g := by
        have := congrArg (fun t : H => t * g) hx'
        simpa [mul_assoc] using this
      exact hx''.symm
  have hQfix : fixedPointSubgroup (Subgroup.zpowers β) (J ⧸ Z) =
      autFixedSubgroup (quotientAut β) := by
    simpa [Z] using fixedPointSubgroup_quotient_eq_autFixedSubgroup (J := J) β
  have hJfix : fixedPointSubgroup (Subgroup.zpowers β) J = autFixedSubgroup β := by
    simpa using fixedPointSubgroup_zpowers_eq_autFixedSubgroup (J := J) β
  have hcop3Z : Nat.Coprime 3 (Nat.card Z) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (by simpa [Z] using hZJ)
  have hcopA'Z : Nat.Coprime (Nat.card (Subgroup.zpowers β)) (Nat.card Z) := by
    have hdiv : Nat.card (Subgroup.zpowers β) ∣ 3 := by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one hβ3
    exact Nat.Coprime.of_dvd_left hdiv hcop3Z
  have hmapfix : fixedPointSubgroup (Subgroup.zpowers β) (J ⧸ Z) =
      (fixedPointSubgroup (Subgroup.zpowers β) J).map (QuotientGroup.mk' Z) := by
    simpa [Z] using fixedPointSubgroup_quotient_eq_map_of_isMulCommutative
      (A := Subgroup.zpowers β) (G := J) Z (isInvariant_of_characteristic Z) hcopA'Z
  have hAfixQ : A ≤ fixedPointSubgroup (Subgroup.zpowers β) (J ⧸ Z) := by
    rw [hQfix]
    intro a ha
    rw [mem_autFixedSubgroup]
    exact hfix a ha
  have hψrange : ψ.range = (C.subgroupOf J).map (QuotientGroup.mk' Z) := by
    simp [ψ, MonoidHom.range_comp, Subgroup.inclusion_range]
  have hArange : A ≤ ψ.range := by
    rw [hψrange, hCsub, ← hJfix, ← hmapfix]
    exact hAfixQ
  have hker : ψ.ker = Z.comap (Subgroup.inclusion (inf_le_right : C ≤ J)) := by
    ext x
    simp [ψ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  have hkerle : (ψ.ker).map (Subgroup.inclusion (inf_le_right : C ≤ J)) ≤ Z := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    rw [hker] at hx
    exact hx
  have hcardker : Nat.Coprime 3 (Nat.card ψ.ker) := by
    have h1 : Nat.card ψ.ker =
        Nat.card ((ψ.ker).map (Subgroup.inclusion (inf_le_right : C ≤ J))) := by
      rw [Subgroup.card_map_of_injective (Subgroup.inclusion_injective (inf_le_right : C ≤ J))]
    have h2 : Nat.card ((ψ.ker).map (Subgroup.inclusion (inf_le_right : C ≤ J))) ∣
        Nat.card Z := Subgroup.card_dvd_of_le hkerle
    rw [h1]
    exact hcop3Z.coprime_dvd_right h2
  obtain ⟨E', hE'el, hE'card⟩ :=
    CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.exists_elemAbelian_lift
      ψ hcardker hArange hAel
  refine ⟨E'.map C.subtype, ?_, hE'el.map C.subtype, ?_, ?_⟩
  · intro y hy
    obtain ⟨e, -, rfl⟩ := Subgroup.mem_map.mp hy
    exact e.2.2
  · rw [Subgroup.card_map_of_injective C.subtype_injective, hE'card, hAcard]
  · intro y hy
    obtain ⟨e, -, rfl⟩ := Subgroup.mem_map.mp hy
    exact e.2.1

private theorem exists_inner_of_fixed_E27 {H : Type} [Group H] [Finite H]
    {J : Subgroup H} (hZJ : ¬ 3 ∣ Nat.card (Subgroup.center J))
    (hrk : ∀ B : Subgroup H, IsElemAbelian 3 B → Nat.card B ≤ 3 ^ 4)
    {z g : H} (hz1 : z ≠ 1) (hz3 : z ^ 3 = 1)
    (hzJ : J ≤ Subgroup.centralizer ({z} : Set H))
    (hgz : g ∈ Subgroup.centralizer ({z} : Set H)) (hg3 : g ^ 3 = 1)
    {E : Subgroup H} (hEJ : E ≤ J) (hEel : IsElemAbelian 3 E)
    (hEcard : Nat.card E = 3 ^ 3)
    (hEg : E ≤ Subgroup.centralizer ({g} : Set H)) :
    ∃ x ∈ J, ∀ y ∈ J, g * y * g⁻¹ = x * y * x⁻¹ := by
  classical
  have hzJnot : z ∉ J := not_mem_of_centralizes_of_center_not_dvd hz1 hz3 hzJ hZJ
  have hzE : z ∉ E := fun h => hzJnot (hEJ h)
  let B₀ : Subgroup H := E ⊔ Subgroup.zpowers z
  obtain ⟨hB₀el, hB₀card₀⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.isElemAbelian_sup_zpowers_of_card (p := 3) Nat.prime_three
      (k := 3) hEel hEcard hz3 hzE
      (fun a ha => Subgroup.mem_centralizer_singleton_iff.mp (hzJ (hEJ ha)))
  have hB₀card : Nat.card B₀ = 3 ^ 4 := by
    rw [show B₀ = E ⊔ Subgroup.zpowers z from rfl, hB₀card₀]
  have hzcent : Subgroup.zpowers z ≤ Subgroup.centralizer ({g} : Set H) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_singleton_iff.mp hgz).symm
  have hB₀cent : B₀ ≤ Subgroup.centralizer ({g} : Set H) := sup_le hEg hzcent
  have hcommEz : ∀ a ∈ E, ∀ b ∈ Subgroup.zpowers z, Commute a b := by
    intro a ha b hb
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (show Commute a z from
      Subgroup.mem_centralizer_singleton_iff.mp (hzJ (hEJ ha))).zpow_right n
  by_cases hgB₀ : g ∈ B₀
  · change g ∈ E ⊔ Subgroup.zpowers z at hgB₀
    obtain ⟨a, haE, b, hbz, hab⟩ := (CFSG.mem_sup_of_commute hcommEz).mp hgB₀
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hbz
    refine ⟨a, hEJ haE, fun y hy => ?_⟩
    have hzy : Commute z y :=
      (Subgroup.mem_centralizer_singleton_iff.mp (hzJ hy)).symm
    have hzfix : z ^ n * y * (z ^ n)⁻¹ = y := by
      rw [(hzy.zpow_left n).eq, mul_assoc, mul_inv_cancel, mul_one]
    calc g * y * g⁻¹ = (a * z ^ n) * y * (a * z ^ n)⁻¹ := by rw [← hab]
      _ = a * (z ^ n * y * (z ^ n)⁻¹) * a⁻¹ := by group
      _ = a * y * a⁻¹ := by rw [hzfix]
  · have hcommB₀g : ∀ b ∈ B₀, b * g = g * b := fun b hb =>
      Subgroup.mem_centralizer_singleton_iff.mp (hB₀cent hb)
    obtain ⟨hBel, hBcard₀⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.isElemAbelian_sup_zpowers_of_card (p := 3) Nat.prime_three
        (k := 4) hB₀el hB₀card hg3 hgB₀ hcommB₀g
    have hBcard : Nat.card (B₀ ⊔ Subgroup.zpowers g : Subgroup H) = 3 ^ 5 := by
      rw [hBcard₀]
    have hle := hrk (B₀ ⊔ Subgroup.zpowers g : Subgroup H) hBel
    rw [hBcard] at hle
    norm_num at hle

theorem exists_inner_of_aut_dichotomy {H : Type} [Group H] [Finite H] {J : Subgroup H}
    (hJ : commutator J = ⊤) (hZJ : ¬ 3 ∣ Nat.card (Subgroup.center J))
    (hrk : ∀ B : Subgroup H, IsElemAbelian 3 B → Nat.card B ≤ 3 ^ 4)
    (hdich : ∀ α : MulAut (J ⧸ Subgroup.center J), α ^ 3 = 1 →
      (∃ x, α = MulAut.conj x) ∨ ∃ A : Subgroup (J ⧸ Subgroup.center J),
        IsElemAbelian 3 A ∧ Nat.card A = 3 ^ 3 ∧ ∀ a ∈ A, α a = a)
    {z : H} (hz1 : z ≠ 1) (hz3 : z ^ 3 = 1) (hzJ : J ≤ Subgroup.centralizer ({z} : Set H))
    {g : H} (hgN : g ∈ Subgroup.normalizer (J : Set H))
    (hgz : g ∈ Subgroup.centralizer ({z} : Set H)) (hg3 : g ^ 3 = 1) :
    ∃ x ∈ J, ∀ y ∈ J, g * y * g⁻¹ = x * y * x⁻¹ := by
  classical
  let β : MulAut J := Subgroup.normalizerMonoidHom J ⟨g, hgN⟩
  have hβ : ∀ y : J, (β y : H) = g * y * g⁻¹ := fun y =>
    Subgroup.normalizerMonoidHom_apply_apply_coe J ⟨g, hgN⟩ y
  have hβ3 : β ^ 3 = 1 := by
    have h3 : (⟨g, hgN⟩ : Subgroup.normalizer (J : Set H)) ^ 3 = 1 := by
      ext
      simpa using hg3
    calc β ^ 3 = Subgroup.normalizerMonoidHom J (⟨g, hgN⟩ ^ 3) := by rw [map_pow]
      _ = 1 := by rw [h3, map_one]
  let ᾱ : MulAut (J ⧸ Subgroup.center J) := MulAut.mapQuotient (Subgroup.center J) β
  have hᾱ3 : ᾱ ^ 3 = 1 := by
    calc ᾱ ^ 3 = MulAut.mapQuotient (Subgroup.center J) (β ^ 3) := by rw [map_pow]
      _ = 1 := by rw [hβ3, map_one]
  rcases hdich ᾱ hᾱ3 with ⟨x, hx⟩ | ⟨A, hAel, hAcard, hAfix⟩
  · exact exists_inner_of_quotient_conj hJ hβ hx
  · have hqaut : ᾱ = quotientAut β := mapQuotient_center_eq_quotientAut β
    have hfix : ∀ a ∈ A, quotientAut β a = a := by
      intro a ha
      rw [← hqaut]
      exact hAfix a ha
    obtain ⟨E, hEJ, hEel, hEcard, hEg⟩ :=
      exists_fixed_elemAbelian_E27 hZJ hβ hβ3 hAel hAcard hfix
    exact exists_inner_of_fixed_E27 hZJ hrk hz1 hz3 hzJ hgz hg3 hEJ hEel hEcard hEg

end CFSG.StandardType
