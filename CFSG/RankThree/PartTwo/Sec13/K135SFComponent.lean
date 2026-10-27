module

public import CFSG.RankThree.PartTwo.Sec13.K135SFPrime
public import CFSG.RankThree.PartTwo.Sec13.K135SFCover
import CFSG.LocalAnalysis.SectionRank.KGroupSectionClosure
import CFSG.RankThree.OddKernel.ThreeComplementQuotient
public import CFSG.RankThree.PartTwo.Sec13.K135SFDefs
public import CFSG.RankThree.PartTwo.Sec4.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec13.K135SF

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (localRank)
open scoped commutatorElement

@[expose] def SF2Statement : Prop :=
  ∀ (M : Type) [Group M] [Finite M], localRank 3 M ≤ 3 →
    ∀ (R : Subgroup M) [R.Normal], Odd (Nat.card R) →
    ∀ (X : Subgroup M) [Group.IsPerfect X] (S : Type) [Group S] [Finite S], IsSimpleGroup S →
      (∃ a b : S, a * b ≠ b * a) → ∀ π : X →* S, Function.Surjective π → Odd (Nat.card π.ker) →
      ¬ ⁅R, X⁆ ≤ (CFSG.pPrimeCore 3 R).map R.subtype → GL12Data S

theorem sectionFourHyp_or_gl12 (hLP : Item4_1LargePrime) (hTC : Item4_1ThreeCover)
    (hSF2 : SF2Statement) {M : Type} [Group M] [Finite M] (hM : SectionFourHyp M)
    (R : Subgroup M) [R.Normal] (hRodd : Odd (Nat.card R)) (J : Subgroup (M ⧸ R))
    (hJ : CFSG.IsComponent J) (hZ : Odd (Nat.card (Subgroup.center J))) :
    SectionFourHyp (J ⧸ Subgroup.center J) ∨
      (CFSG.IsKGroup (J ⧸ Subgroup.center J) ∧ GL12Data (J ⧸ Subgroup.center J)) := by
  haveI : IsSimpleGroup (J ⧸ Subgroup.center J) := hJ.1.2.1
  have hSn : ∃ a b : J ⧸ Subgroup.center J, a * b ≠ b * a := hJ.1.2.2
  haveI hJperf : Group.IsPerfect J := hJ.1.1
  obtain ⟨X, hXperf, hXJ⟩ := exists_perfect_cover R J
  haveI := hXperf
  set q := QuotientGroup.mk' R with hq
  let ψ : X →* (M ⧸ R) := q.comp X.subtype
  have hψJ : ∀ x : X, ψ x ∈ J := fun x => by
    have : ψ x ∈ X.map q := Subgroup.mem_map_of_mem _ x.2
    rwa [hXJ] at this
  let ψJ : X →* J := ψ.codRestrict J hψJ
  have hψJs : Function.Surjective ψJ := by
    intro j
    have hj : (j : M ⧸ R) ∈ X.map q := by rw [hXJ]; exact j.2
    obtain ⟨x, hx, hxj⟩ := Subgroup.mem_map.mp hj
    exact ⟨⟨x, hx⟩, Subtype.ext hxj⟩
  let π : X →* J ⧸ Subgroup.center J := (QuotientGroup.mk' (Subgroup.center J)).comp ψJ
  have hπ : Function.Surjective π :=
    (QuotientGroup.mk'_surjective _).comp hψJs
  have hπker : ∀ x : X, x ∈ π.ker ↔ ψJ x ∈ Subgroup.center J := fun x => by
    rw [MonoidHom.mem_ker]
    exact QuotientGroup.eq_one_iff _
  haveI hN₀n : ((CFSG.pPrimeCore 3 R).map R.subtype).Normal := normal_map_pPrimeCore R 3
  have hN₀3 : ¬ 3 ∣ Nat.card ((CFSG.pPrimeCore 3 R).map R.subtype) := by
    rw [Subgroup.card_map_of_injective R.subtype_injective]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (CFSG.pPrimeCore_coprime_card)
  have hπN : ∀ x : X, (x : M) ∈ (CFSG.pPrimeCore 3 R).map R.subtype → π x = 1 := by
    intro x hx
    have hxR : (x : M) ∈ R := by
      obtain ⟨r, -, hr⟩ := hx
      rw [← hr]
      exact r.2
    have : ψJ x = 1 := Subtype.ext ((QuotientGroup.eq_one_iff _).mpr hxR)
    simp [π, this]
  have hK : ⁅X, π.ker.map X.subtype⁆ ≤ R := by
    rw [Subgroup.commutator_le]
    intro g₁ h₁ g₂ h₂
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp h₂
    have hkc : ψJ k ∈ Subgroup.center J := (hπker k).mp hk
    have hcomm := (Subgroup.mem_center_iff.mp hkc) (ψJ ⟨g₁, h₁⟩)
    have hcomm' : ψ ⟨g₁, h₁⟩ * ψ k = ψ k * ψ ⟨g₁, h₁⟩ := congrArg Subtype.val hcomm
    have h1 : q ⁅g₁, X.subtype k⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm'
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hodd : Odd (Nat.card π.ker) := by
    let κ : π.ker →* J := ψJ.comp π.ker.subtype
    have hκrange : κ.range ≤ Subgroup.center J := by
      rintro _ ⟨k, rfl⟩
      exact (hπker k.1).mp k.2
    have hrange : Odd (Nat.card κ.range) :=
      Odd.of_dvd_nat hZ (Subgroup.card_dvd_of_le hκrange)
    have hkerκ : Odd (Nat.card κ.ker) := by
      let ι : κ.ker →* R := (X.subtype.comp (π.ker.subtype.comp κ.ker.subtype)).codRestrict R
        (fun y => by
          have hy : κ y.1 = 1 := y.2
          have : ψJ y.1.1 = 1 := hy
          have h2 : ψ y.1.1 = 1 := congrArg Subtype.val this
          exact (QuotientGroup.eq_one_iff _).mp h2)
      have hι : Function.Injective ι := fun a b hab => by
        have h1 : ((ι a : R) : M) = ((ι b : R) : M) := congrArg Subtype.val hab
        have h2 : (((a : π.ker) : X) : M) = (((b : π.ker) : X) : M) := h1
        exact Subtype.ext (Subtype.ext (Subtype.ext h2))
      exact Odd.of_dvd_nat hRodd (Subgroup.card_dvd_of_injective ι hι)
    exact odd_card_of_hom κ hkerκ hrange
  by_cases hL : ⁅R, X⁆ ≤ (CFSG.pPrimeCore 3 R).map R.subtype
  · left
    exact sectionFourHyp_of_perfect_cover hLP hTC hM R _ hN₀3 X inferInstance hSn π hπ hπN hK hL
  · right
    have hloc : localRank 3 M ≤ 3 :=
      (CFSG.RankThree.OddKernel.localRank_le_evenRank Nat.prime_three (by norm_num)).trans
        hM.evenRank_le
    refine ⟨?_, hSF2 M hloc R hRodd X _ inferInstance hSn π hπ hodd hL⟩
    exact CFSG.SectionRank.K_group_section_closure_inCatalog hM.kGroup X π.ker
      (QuotientGroup.quotientKerEquivOfSurjective π hπ)

end CFSG.RankThree.PartTwo.Sec13.K135SF
