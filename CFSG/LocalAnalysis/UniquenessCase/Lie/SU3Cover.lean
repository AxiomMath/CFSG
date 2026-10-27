module

public import CFSG.LocalAnalysis.UniquenessCase.Lie.SU3
public import CFSG.LocalAnalysis.UniquenessCase.Lie.RankOneInput
import CFSG.LieType.Steinberg.CentralExt.SUOddClosed
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
import CFSG.LocalAnalysis.UniquenessCase.Lie.Cover
import CFSG.LinearAlgebra.LinearGroups.UnitaryScalarKernel
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.CharacterTheory.CyclicBlocks.Family
public import CFSG.CharacterTheory.Semidihedral.Principal.LargePrimeTorusSylowCentralizers
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusBlockAlignment
public import CFSG.CharacterTheory.Wreathed.FourPointInvolutionHexagon
public import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusion
public import CFSG.ClassicalGroups
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.ShortRoot
public import CFSG.Combinatorics.AperiodicCentralInvolution
public import CFSG.Combinatorics.AperiodicFiveOfSix
public import CFSG.Combinatorics.AperiodicOppositeComponents
public import CFSG.Combinatorics.AperiodicSixteenGraphDistances
public import CFSG.Combinatorics.OuterLayerPredecessors
public import CFSG.GH74.BNPair.Defs
public import CFSG.GH74.GLS.IVK.L2.F1
public import CFSG.GH74.KGroups.L3EpsNoNormalThree
public import CFSG.GH74.KGroups.L3EpsOutExp
public import CFSG.GH74.KGroups.L3EpsOuterLin
public import CFSG.LieType.SeitzGeneration.NonabHeisThreeCore
public import CFSG.LieType.SeitzGeneration.NonabHeisThreeUnitary
public import CFSG.LieType.SeitzGeneration.UnitaryBlocks
public import CFSG.LieType.SeitzGeneration.UnitaryHyperScope
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Bounded
public import CFSG.LocalAnalysis.SectionRank.QTK.EvenOrth
public import CFSG.LocalAnalysis.SectionRank.QTK.Exc
public import CFSG.LocalAnalysis.SectionRank.QTK.OddOrth
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20b
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a
public import CFSG.Mathlib.LinearAlgebra.BilinForm.Determinant
public import CFSG.Permutation.UnitaryThreeRecognition.Model
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.OddKernel.CompleteRankComparison
public import CFSG.RankThree.PartOne.KF.ClsPSL
public import CFSG.RankThree.PartOne.KF.SU5Model
public import CFSG.RankThree.PartOne.KF.SymCtxMatrix
public import CFSG.RankThree.PartOne.KF.ToralQuot
public import CFSG.RankThree.PartOne.KF.UnitaryModel
public import CFSG.RankThree.PartOne.S11c.Sec66PSL
public import CFSG.RankThree.PartOne.S11c.Sec66Sp
public import CFSG.RankThree.PartOne.S11c.SuFiveD
public import CFSG.RankThree.PartOne.S11d.OutSymplectic
public import CFSG.RankThree.PartOne.S11d.OutUnitary
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
public import CFSG.Sporadic.Recognition.JankoWongPSLNine
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Subgroup

section Push

variable {S X : Type} [Group S] [Group X]

theorem uc22pwsu3_map_normalizer_le (α : S →* X) (U : Subgroup S) :
    (normalizer (U : Set S)).map α ≤ normalizer ((U.map α : Subgroup X) : Set X) := by
  rintro _ ⟨s, hs, rfl⟩
  rw [mem_normalizer_iff]
  have hs' := mem_normalizer_iff.1 hs
  have hsi := mem_normalizer_iff.1 (inv_mem hs)
  intro x
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨s * u * s⁻¹, (hs' u).1 hu, by simp⟩
  · rintro ⟨u', hu', hx⟩
    refine ⟨s⁻¹ * u' * s, ?_, ?_⟩
    · simpa using (hsi u').1 hu'
    · rw [map_mul, map_mul, map_inv, hx]
      group

theorem uc22pwsu3_lift_pow {α : S →* X} {N M : ℕ} (hNM : Nat.Coprime N M)
    (hker : ∀ x ∈ α.ker, x ^ M = 1) {T : Subgroup S} {t' : X} (ht' : t' ∈ T.map α)
    (hN : t' ^ N = 1) : ∃ t ∈ T, α t = t' ∧ t ^ N = 1 := by
  obtain ⟨t, ht, rfl⟩ := ht'
  obtain ⟨e, he1, he2⟩ := Nat.chineseRemainder hNM 1 0
  refine ⟨t ^ e, pow_mem ht _, ?_, ?_⟩
  · rw [map_pow]
    have h1 : orderOf (α t) ∣ N := orderOf_dvd_of_pow_eq_one hN
    have h2 : e ≡ 1 [MOD orderOf (α t)] := he1.of_dvd h1
    exact (pow_eq_pow_iff_modEq.2 h2).trans (pow_one _)
  · obtain ⟨c, hc⟩ := Nat.modEq_zero_iff_dvd.1 he2
    have hk : t ^ N ∈ α.ker := by
      rw [MonoidHom.mem_ker, map_pow, hN]
    have h3 : (t ^ e) ^ N = ((t ^ N) ^ M) ^ c := by
      rw [← pow_mul, ← pow_mul, ← pow_mul, hc]
      congr 1
      ring
    rw [h3, hker _ hk, one_pow]

theorem uc22pwsu3_lift_preserves [Finite S] {α : S →* X} {M : ℕ} (hM : Odd M)
    (hker : ∀ x ∈ α.ker, x ^ M = 1) (hcent : α.ker ≤ center S) {U : Subgroup S} (hU : IsPGroup 2 U)
    {ψ : MulAut X} {ψ' : MulAut S} (hψ' : ∀ s, α (ψ' s) = ψ (α s))
    (hψ : ∀ x, x ∈ U.map α ↔ ψ x ∈ U.map α) : ∀ x, x ∈ U ↔ ψ' x ∈ U := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : ∀ x ∈ U, ψ' x ∈ U := by
    intro x hx
    have hαx : ψ (α x) ∈ U.map α := (hψ _).1 ⟨x, hx, rfl⟩
    rw [← hψ'] at hαx
    obtain ⟨u₀, hu₀, hαu⟩ := hαx
    have hk : u₀⁻¹ * ψ' x ∈ α.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hαu, inv_mul_cancel]
    have hkc : u₀⁻¹ * ψ' x ∈ center S := hcent hk
    have hxk : ψ' x = u₀ * (u₀⁻¹ * ψ' x) := by group
    obtain ⟨a, ha⟩ := IsPGroup.iff_orderOf.1 hU ⟨x, hx⟩
    obtain ⟨b, hb⟩ := IsPGroup.iff_orderOf.1 hU ⟨u₀, hu₀⟩
    have hxo : orderOf x = 2 ^ a := (Subgroup.orderOf_coe (⟨x, hx⟩ : U)).trans ha
    have huo : orderOf u₀ = 2 ^ b := (Subgroup.orderOf_coe (⟨u₀, hu₀⟩ : U)).trans hb
    have hxN : x ^ 2 ^ (a + b) = 1 :=
      orderOf_dvd_iff_pow_eq_one.1 (hxo ▸ pow_dvd_pow 2 (Nat.le_add_right a b))
    have huN : u₀ ^ 2 ^ (a + b) = 1 :=
      orderOf_dvd_iff_pow_eq_one.1 (huo ▸ pow_dvd_pow 2 (Nat.le_add_left b a))
    have hx1 : (ψ' x) ^ 2 ^ (a + b) = 1 := by rw [← map_pow, hxN, map_one]
    generalize hkdef : u₀⁻¹ * ψ' x = k at hk hkc hxk
    have hcomm : Commute u₀ k := mem_center_iff.1 hkc u₀
    have hkN : k ^ 2 ^ (a + b) = 1 := by
      have h2 : (u₀ * k) ^ 2 ^ (a + b) = u₀ ^ 2 ^ (a + b) * k ^ 2 ^ (a + b) := hcomm.mul_pow _
      rw [← hxk, hx1, huN, one_mul] at h2
      exact h2.symm
    have hcop : Nat.Coprime (2 ^ (a + b)) M := (hM.coprime_two_right.symm).pow_left _
    have hk1 : k = 1 := by
      have h3 : orderOf k ∣ Nat.gcd (2 ^ (a + b)) M :=
        Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hkN) (orderOf_dvd_of_pow_eq_one (hker k hk))
      rw [Nat.Coprime.gcd_eq_one hcop] at h3
      exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)
    rw [hxk, hk1, mul_one]
    exact hu₀
  have hle : U.map ψ'.toMonoidHom ≤ U := by
    rintro _ ⟨x, hx, rfl⟩
    exact h1 x hx
  have heq : U.map ψ'.toMonoidHom = U :=
    Subgroup.eq_of_le_of_card_ge hle (Subgroup.card_map_of_injective ψ'.injective).ge
  intro x
  refine ⟨h1 x, fun hx => ?_⟩
  have hx' : ψ' x ∈ U.map ψ'.toMonoidHom := heq.symm ▸ hx
  obtain ⟨u, hu, hux⟩ := hx'
  exact (ψ'.injective hux) ▸ hu

theorem uc22pwr1_datum_push [Finite S] {n : ℕ} (hn : 1 ≤ n) {α : S →* X}
    (hα : Function.Surjective α) (hker : ∀ x ∈ α.ker, x ^ (2 ^ n + 1) = 1)
    (hcent : α.ker ≤ center S)
    (hlift : ∀ ψ : MulAut X, ∃ ψ' : MulAut S, ∀ s, α (ψ' s) = ψ (α s))
    {U : Subgroup S} (hU : IsPGroup 2 U) (D : UC22pwR1Datum S U n) :
    UC22pwR1Datum X (U.map α) n := by
  obtain ⟨T, w, hTc, hTodd, hTN, hη, hw2, hwinv, hwgen, hfrob⟩ := D
  have hcop := uc22pwsu3_coprime_two_pow hn
  have hlt : ∀ t' ∈ T.map α, t' ^ (2 ^ n - 1) = 1 → ∃ t ∈ T, α t = t' ∧ t ^ (2 ^ n - 1) = 1 :=
    fun t' ht' h => uc22pwsu3_lift_pow hcop hker ht' h
  refine ⟨T.map α, α w, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact isCyclic_of_surjective (α.subgroupMap T) (α.subgroupMap_surjective T)
  · exact hTodd.of_dvd_nat (Subgroup.card_map_dvd T α)
  · exact (map_mono hTN).trans (uc22pwsu3_map_normalizer_le α U)
  · intro p hp hpd
    haveI := Fact.mk hp
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := T) p (hη p hp hpd)
    have hxo : orderOf (x : S) = p := (Subgroup.orderOf_coe x).trans hx
    have hne : α (x : S) ≠ 1 := by
      intro h1
      have h2 : (x : S) ^ (2 ^ n + 1) = 1 := hker _ h1
      have h3 : p ∣ 2 ^ n + 1 := hxo ▸ orderOf_dvd_of_pow_eq_one h2
      have h4 : p ∣ 2 := by
        have := Nat.dvd_sub h3 hpd
        rwa [show 2 ^ n + 1 - (2 ^ n - 1) = 2 by have := Nat.one_le_two_pow (n := n); omega] at this
      obtain rfl : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h4
      have h5 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
      have h6 := Nat.one_le_two_pow (n := n)
      generalize 2 ^ n = q at hpd h5 h6
      omega
    have h7 : orderOf (α (x : S)) = p :=
      ((Nat.dvd_prime hp).1 (hxo ▸ orderOf_map_dvd α (x : S))).resolve_left
        (fun h => hne (orderOf_eq_one_iff.1 h))
    rw [← h7]
    exact Subgroup.orderOf_dvd_natCard _ ⟨x, x.2, rfl⟩
  · rw [← map_pow, hw2, map_one]
  · intro t' ht' ht'N
    obtain ⟨t, htT, rfl, htN⟩ := hlt t' ht' ht'N
    rw [← map_mul, ← map_inv, ← map_mul, hwinv t htT htN, map_inv]
  · rw [eq_top_iff]
    intro x _
    obtain ⟨s, rfl⟩ := hα x
    have hs : s ∈ normalizer (U : Set S) ⊔ zpowers w := hwgen ▸ mem_top s
    have := Subgroup.mem_map_of_mem α hs
    rw [Subgroup.map_sup, MonoidHom.map_zpowers] at this
    exact (sup_le_sup (uc22pwsu3_map_normalizer_le α U) le_rfl) this
  · intro ψ hψ
    obtain ⟨ψ', hψ'⟩ := hlift ψ
    have hpres := uc22pwsu3_lift_preserves (uc22pwsu3_odd_two_pow_add_one hn) hker hcent hU hψ' hψ
    obtain ⟨i, hi⟩ := hfrob ψ' hpres
    refine ⟨i, fun t' ht' ht'N => ?_⟩
    obtain ⟨t, htT, rfl, htN⟩ := hlt t' ht' ht'N
    obtain ⟨u, hu, hψt⟩ := hi t htT htN
    exact ⟨α u, ⟨u, hu, rfl⟩, by rw [← hψ', hψt, map_mul, map_pow]⟩

end Push

section Cover

theorem uc22pwsu3_exists_lift {S X : Type} [Group S] [Group X] [Finite S]
    (hclosed : ∀ (E : Type) [Group E] [Finite E] (π : E →* S), Function.Surjective π →
      π.ker ≤ center E → ∃ σ : S →* E, ∀ g, π (σ g) = g)
    (hSp : commutator S = ⊤) {α : S →* X} (hα : Function.Surjective α) (hαc : α.ker ≤ center S)
    (ψ : MulAut X) : ∃ ψ' : MulAut S, ∀ s, α (ψ' s) = ψ (α s) := by
  obtain ⟨β, hβ, -, hαβ⟩ := uc22pwlie_exists_cover_of_closed_fin hclosed hSp α hα hαc
    (ψ.toMonoidHom.comp α) (ψ.surjective.comp hα) (by
      intro x hx
      apply hαc
      rw [MonoidHom.mem_ker]
      exact ψ.injective (by simpa using hx))
  exact ⟨MulEquiv.ofBijective β ⟨Finite.injective_iff_surjective.2 hβ, hβ⟩, hαβ⟩

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

theorem uc22pwsu3_closed
    (hn : 2 < n) (hF : Nat.card F = (2 ^ n) ^ 2) (E : Type) [Group E]
    [Finite E] (π : E →* SU (unitaryInvolution F 2 n) 3) (hπ : Function.Surjective π)
    (hc : π.ker ≤ center E) : ∃ s : SU (unitaryInvolution F 2 n) 3 →* E, ∀ g, π (s g) = g := by
  have hq : ((3 : ℕ), 2 ^ n) ≠ (3, 2) := by
    intro h
    have h1 : 2 ^ n = 2 := (Prod.mk.inj h).2
    have h2 : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  have hker : ((equivStatedSU hF 3).toMonoidHom.comp π).ker ≤ center E := by
    refine le_trans (fun x hx => ?_) hc
    rw [MonoidHom.mem_ker] at hx ⊢
    exact (map_eq_one_iff _ (equivStatedSU hF 3).injective).1 hx
  obtain ⟨s, hs⟩ := CFSG.LieType.Steinberg.CentralExt.SUOdd.statedSU_odd_exists_section_of_central
    (p := 2) (f := n) hF (by omega) (n := 3) le_rfl (by decide) hq
    (π := (equivStatedSU hF 3).toMonoidHom.comp π)
    ((equivStatedSU hF 3).surjective.comp hπ) hker
  refine ⟨s.comp (equivStatedSU hF 3).toMonoidHom, fun g => ?_⟩
  apply (equivStatedSU hF 3).injective
  simpa using hs ((equivStatedSU hF 3) g)

theorem uc22pwsu3_commutator_eq_top (hn : 2 < n) (hF : Nat.card F = (2 ^ n) ^ 2) :
    commutator (SU (unitaryInvolution F 2 n) 3) = ⊤ := by
  have hq : ((3 : ℕ), 2 ^ n) ≠ (3, 2) := by
    intro h
    have h1 : 2 ^ n = 2 := (Prod.mk.inj h).2
    have h2 : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  haveI := CFSG.LieType.Steinberg.CentralExt.SUOdd.isPerfect_statedSU_odd (p := 2) (f := n) hF
    (n := 3) le_rfl hq
  haveI : Group.IsPerfect (SU (unitaryInvolution F 2 n) 3) :=
    Group.IsPerfect.ofSurjective (f := (equivStatedSU hF 3).symm.toMonoidHom)
      (equivStatedSU hF 3).symm.surjective
  exact Group.IsPerfect.commutator_eq_top

theorem uc22pwsu3_scalar_mem_center {ι : Type} [Fintype ι] [DecidableEq ι] (H : Subgroup (GL ι F))
    {x : H} (hx : x ∈ (StatedScalars ι F).subgroupOf H) : x ∈ center H := by
  have hx' : (x : GL ι F) ∈ StatedScalars ι F := Subgroup.mem_subgroupOf.1 hx
  have hc : (x : GL ι F) ∈ center (GL ι F) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact hx'
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (Subgroup.mem_center_iff.1 hc g)

theorem uc22pwsu3_exists_cover
    (hn : 2 < n) (hF : Nat.card F = (2 ^ n) ^ 2) {X : Type} [Group X]
    [Finite X] (hq : CFSG.Open.IsQuasisimple X) (e : X ⧸ center X ≃* StatedProj (StatedSU 3 (2 ^ n) F)) :
    ∃ α : SU (unitaryInvolution F 2 n) 3 →* X, Function.Surjective α ∧
      α.ker ≤ center (SU (unitaryInvolution F 2 n) 3) ∧ ∀ x ∈ α.ker, x ^ (2 ^ n + 1) = 1 := by
  haveI : Finite (SU (unitaryInvolution F 2 n) 3) := inferInstance
  let ρ : SU (unitaryInvolution F 2 n) 3 →* X ⧸ center X :=
    e.symm.toMonoidHom.comp ((QuotientGroup.mk' _).comp (equivStatedSU hF 3).toMonoidHom)
  have hρ : Function.Surjective ρ :=
    e.symm.surjective.comp ((QuotientGroup.mk'_surjective _).comp (equivStatedSU hF 3).surjective)
  have hρZ : ∀ s, ρ s = 1 → equivStatedSU hF 3 s ∈
      (StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 (2 ^ n) F) := by
    intro s hs
    have h1 : e.symm (QuotientGroup.mk' ((StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 (2 ^ n) F))
        (equivStatedSU hF 3 s)) = 1 := hs
    have h2 := (map_eq_one_iff _ e.symm.injective).1 h1
    exact (QuotientGroup.eq_one_iff _).1 h2
  have hρc : ρ.ker ≤ center (SU (unitaryInvolution F 2 n) 3) := by
    intro s hs
    have hc := uc22pwsu3_scalar_mem_center _ (hρZ s hs)
    rw [Subgroup.mem_center_iff]
    intro g
    apply (equivStatedSU hF 3).injective
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.1 hc _
  obtain ⟨α, hα, hαc, hαπ⟩ := uc22pwlie_exists_cover_of_closed_fin
    (fun E _ _ π hπ hc => uc22pwsu3_closed hn hF E π hπ hc) hq.1 (QuotientGroup.mk' (center X))
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']) ρ hρ hρc
  refine ⟨α, hα, hαc, fun x hx => ?_⟩
  have hx1 : ρ x = 1 := by
    rw [← hαπ, MonoidHom.mem_ker.1 hx, map_one]
  have hZ := hρZ x hx1
  have hcard := (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hF (n := 3) (by norm_num)).2.2
  have h3 : (equivStatedSU hF 3 x) ^ Nat.card ((StatedScalars (Fin 3) F).subgroupOf
      (StatedSU 3 (2 ^ n) F)) = 1 := uc22pwr1_pow_card hZ
  rw [hcard] at h3
  have h4 : (equivStatedSU hF 3 x) ^ (2 ^ n + 1) = 1 := by
    obtain ⟨c, hc⟩ := Nat.gcd_dvd_right 3 (2 ^ n + 1)
    rw [hc, pow_mul, h3, one_pow]
  apply (equivStatedSU hF 3).injective
  rw [map_pow, h4, map_one]

end Cover

theorem uc22pwr1_concl_of_isSU3G
    {X : Type} [Group X] [Finite X] (hq : CFSG.Open.IsQuasisimple X) {n : ℕ}
    (hn : 2 < n) (hSU : IsSU3 X n) (U : Sylow 2 X) {P : Type} [Group P] (hP : IsPGroup 2 P) (ψ : P →* MulAut X)
    (hψ : ∀ (g : P) (x : X), x ∈ (U : Subgroup X) ↔ ψ g x ∈ (U : Subgroup X)) {m' : ℕ} (hm' : Odd m')
    {e : ℕ} (hnem : n = 2 ^ e * m') :
    ∃ E : Subgroup X, uc22pwlie_ConclAt uc22pwr1_shape X (U : Subgroup X) P ψ n m' E ∧
      uc22pwlie_Gal (U : Subgroup X) E ψ := by
  obtain ⟨-, hU3⟩ := hSU
  obtain ⟨-, K, hKf, hKfin, hK, ⟨e₁⟩⟩ := CFSG.Blueprint.LieModel.statedClassicalModel hU3 (by decide)
  haveI : CharP K 2 := uc22pwlie_charP_two (n := 2 * n) (by rw [hK, ← pow_mul, mul_comm])
  have hn1 : 1 ≤ n := by omega
  obtain ⟨α, hα, hαc, hαk⟩ := uc22pwsu3_exists_cover hn hK hq e₁
  have hU₀ := uc22pwsu3X_isPGroup hK
  have hD := uc22pwr1_datum_su3 hn1 hK
  have hclosed : ∀ (E : Type) [Group E] [Finite E] (π : E →* SU (unitaryInvolution K 2 n) 3),
      Function.Surjective π → π.ker ≤ center E → ∃ s : SU (unitaryInvolution K 2 n) 3 →* E,
        ∀ g, π (s g) = g := fun E _ _ π hπ hc => uc22pwsu3_closed hn hK E π hπ hc
  have hD' := uc22pwr1_datum_push hn1 hα hαk hαc
    (fun ψ => uc22pwsu3_exists_lift hclosed (uc22pwsu3_commutator_eq_top hn hK) hα hαc ψ) hU₀ hD
  have hidx : ¬ 2 ∣ ((uc22pwsu3X (unitaryInvolution_involutive hK)).map α).index :=
    fun h => uc22pwsu3X_index hn1 hK
      (h.trans (Subgroup.index_map_dvd (uc22pwsu3X (unitaryInvolution_involutive hK)) hα))
  let V : Sylow 2 X := (hU₀.map α).toSylow hidx
  have hV : (V : Subgroup X) = (uc22pwsu3X (unitaryInvolution_involutive hK)).map α :=
    IsPGroup.toSylow_coe _ _
  exact uc22pwr1_concl_of_datum_sylowG (MulEquiv.refl X) U V (by rw [hV]; exact hD') hP ψ hψ hm' hnem

theorem uc22pwCartanSU3_holds :
    uc22pwCartanSU3 := by
  intro X _ _ hq n hn hSU U P _ hP ψ hψ e m' hm' hnem
  obtain ⟨E, hE, -⟩ := uc22pwr1_concl_of_isSU3G hq hn hSU U hP ψ hψ hm' hnem
  exact uc22pwr1_literal_of_concl ⟨E, hE⟩

theorem uc22pwCartanRankOne_holds :
    uc22pwCartanRankOne :=
  uc22pwCartanRankOne_of_su3 uc22pwCartanSU3_holds

end CFSG.LocalAnalysis.UniquenessCase.UC22
