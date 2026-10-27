module

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUCover
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63Two
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineL2Remainder
import CFSG.LieType.Steinberg.CentralExt.UnitaryTwoMultiplier

public section

namespace CFSG.StandardType.LineU

open CFSG.ClassicalGroups.UnitaryFlag CFSG.Assembly

theorem unitaryCoverOddAt_of_section {n d : ℕ} {K : Type} [Field K] [Finite K]
    (hperf : commutator (unitarySU 2 n K d) = ⊤)
    (hsec : ∀ (E : Type) [Group E] [Finite E] (π : E →* ↥(unitarySU 2 n K d)),
      Function.Surjective π → π.ker ≤ Subgroup.center E → Odd (Nat.card π.ker) →
        ∃ s : ↥(unitarySU 2 n K d) →* E, ∀ g, π (s g) = g) :
    Line63.UnitaryCoverOddAt n d K := by
  haveI : Finite (Matrix.GeneralLinearGroup (Fin d) K) :=
    Finite.of_injective (fun u : Matrix.GeneralLinearGroup (Fin d) K =>
      (u : Matrix (Fin d) (Fin d) K)) fun _ _ h => Units.ext h
  unfold Line63.UnitaryCoverOddAt
  refine ⟨hperf, ?_⟩
  intro L' _ _ ψ hψ hker _ hodd
  let p₁ : ↥(pullbackSub ψ) →* ↥(unitarySU 2 n K d) :=
    (MonoidHom.fst (↥(unitarySU 2 n K d)) L').comp (pullbackSub ψ).subtype
  have hp₁ : Function.Surjective p₁ := by
    intro s
    obtain ⟨l, hl⟩ := hψ (LargeEvenProjMk (unitarySU 2 n K d) s)
    exact ⟨⟨(s, l), hl.symm⟩, rfl⟩
  have hp₁c : p₁.ker ≤ Subgroup.center ↥(pullbackSub ψ) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h1 : (x : ↥(unitarySU 2 n K d) × L').1 = 1 := hx
    have h3 : LargeEvenProjMk (unitarySU 2 n K d) (x : ↥(unitarySU 2 n K d) × L').1 =
        ψ (x : ↥(unitarySU 2 n K d) × L').2 := x.2
    have h4 : (x : ↥(unitarySU 2 n K d) × L').2 ∈ Subgroup.center L' := by
      refine hker ?_
      rw [MonoidHom.mem_ker, ← h3, h1, map_one]
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    apply Prod.ext
    · show (y : ↥(unitarySU 2 n K d) × L').1 * (x : ↥(unitarySU 2 n K d) × L').1 =
        (x : ↥(unitarySU 2 n K d) × L').1 * (y : ↥(unitarySU 2 n K d) × L').1
      rw [h1, mul_one, one_mul]
    · exact Subgroup.mem_center_iff.mp h4 (y : ↥(unitarySU 2 n K d) × L').2
  have hmem : ∀ x : ↥p₁.ker, ((MonoidHom.snd (↥(unitarySU 2 n K d)) L').comp
      ((pullbackSub ψ).subtype.comp p₁.ker.subtype)) x ∈ ψ.ker := by
    rintro ⟨⟨⟨s, l⟩, hy⟩, hx⟩
    have hs : s = 1 := hx
    have hy' : LargeEvenProjMk (unitarySU 2 n K d) s = ψ l := hy
    rw [MonoidHom.mem_ker]
    show ψ l = 1
    rw [← hy', hs, map_one]
  let ι : ↥p₁.ker →* ↥ψ.ker := ((MonoidHom.snd (↥(unitarySU 2 n K d)) L').comp
    ((pullbackSub ψ).subtype.comp p₁.ker.subtype)).codRestrict ψ.ker hmem
  have hι : Function.Injective ι := by
    rintro ⟨⟨⟨s, l⟩, hy⟩, hx⟩ ⟨⟨⟨s', l'⟩, hy'⟩, hx'⟩ hxy
    have hs : s = 1 := hx
    have hs' : s' = 1 := hx'
    have hl : l = l' := congrArg Subtype.val hxy
    subst hs hs' hl
    rfl
  have hodd₁ : Odd (Nat.card p₁.ker) := hodd.of_dvd_nat (Subgroup.card_dvd_of_injective ι hι)
  obtain ⟨s, hs⟩ := hsec (pullbackSub ψ) p₁ hp₁ hp₁c hodd₁
  refine ⟨(MonoidHom.snd (↥(unitarySU 2 n K d)) L').comp ((pullbackSub ψ).subtype.comp s),
    fun g => ?_⟩
  have h1 : ((s g : ↥(pullbackSub ψ)) : ↥(unitarySU 2 n K d) × L').1 = g := hs g
  have h2 : LargeEvenProjMk (unitarySU 2 n K d)
      ((s g : ↥(pullbackSub ψ)) : ↥(unitarySU 2 n K d) × L').1 =
      ψ ((s g : ↥(pullbackSub ψ)) : ↥(unitarySU 2 n K d) × L').2 := (s g).2
  rw [h1] at h2
  exact h2.symm

section Certificates


theorem unitaryCoverOddAt_six_two (K : Type) [Field K] [Finite K] (hK : Nat.card K = 4) :
    Line63.UnitaryCoverOddAt 1 6 K := by
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 K :=
    ⟨Nat.prime_two, le_rfl, by norm_num [hK]⟩
  haveI : CharP K 2 := hU.charP
  have hF : Nat.card K = (2 ^ 1) ^ 2 := by norm_num [hK]
  refine unitaryCoverOddAt_of_section ?_ ?_
  · haveI := CFSG.LieType.Steinberg.CentralExt.SUClosed.isPerfect_statedSU hF
      (show 4 ≤ 6 by norm_num)
    exact Group.IsPerfect.commutator_eq_top
  · intro E _ _ π hπ hcen hodd
    exact CFSG.LieType.Steinberg.CentralExt.SUClosed.statedSU_exists_section_of_coprime
      (n := 6) hF ⟨3, rfl⟩ (by norm_num) E π hπ hcen (Nat.coprime_two_left.2 hodd)

theorem ggLNoInvariantLineInputOn_unitDvd63_of_h5 (h5 : Line63.GGUnitDvd63BstarRankInput) :
    GGLNoInvariantLineInputOn GGUnitDvd63Label :=
  Line63.ggLNoInvariantLineInputOn_unitDvd63_of_holds h5 fun K _ _ hK =>
    unitaryCoverOddAt_six_two K (by norm_num [hK])

theorem ggLNoInvariantLineInputOn_remainder_of_h5 (h5 : Line63.GGUnitDvd63BstarRankInput)
    (hN : GGLNoInvariantLineInputOn fun p lab =>
      Yardstones.M3f9567aba59d.GGRemainderTableBLResLine p lab ∧ ¬ GGUnitDvdLabel p lab ∧
        ¬ GGLinTwoLabel p lab) :
    GGLNoInvariantLineInputOn Yardstones.M3f9567aba59d.GGRemainderTableBLResLine :=
  ggLNoInvariantLineInputOn_remainder_of_unitDvd_linTwo
    (ggLNoInvariantLineInputOn_unitDvd63_of_h5 h5) hN

end Certificates

end CFSG.StandardType.LineU
