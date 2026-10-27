module

public import CFSG.RankThree.PartTwo.Sec15.Item15Statements
public import CFSG.RankThree.PartTwo.Sec15.Item15Tools
public import CFSG.RankThree.PartTwo.Sec13.Item13Inputs
public import CFSG.RankThree.PartTwo.Sec14.Item1411Chain
import CFSG.RankThree.PartTwo.Sec13.Item131Facts
import CFSG.RankThree.PartTwo.Sec13.Item133
import CFSG.RankThree.PartTwo.Sec13.Item133Mono
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
import CFSG.RankThree.PartTwo.Sec14.LBNatural
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec6.Item612Local
import CFSG.RankThree.PartTwo.Sec15.Item157
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Foundations
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.PartTwo.Sec14.Item145Bot
public import CFSG.RankThree.PartTwo.Sec15.HypR
public import CFSG.RankThree.PartTwo.Sec8.Pairs
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

theorem irreducibleOn_of_m22 (h131 : Item131) (hspor : SporadicModels131) (hSLC : SLTwoCenter)
    (hM22L3 : ∀ (p e : ℕ) [Fact p.Prime], ¬ Sec4.IsoLThreePi CFSG.Blueprint.NativeSporadic.M22 p e)
    (hM22M12 : IsEmpty (CFSG.Blueprint.NativeSporadic.M22 ≃* CFSG.Blueprint.NativeSporadic.M12))
    (hM22J2 : IsEmpty (CFSG.Blueprint.NativeSporadic.M22 ≃* CFSG.Blueprint.NativeSporadic.J2))
    {A L : Subgroup G} {c : G} (hD : Sec13Data G A c L)
    (hM22 : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M22)) :
    c ∉ L ∧ Nat.card ↥(A ⊓ L) = 9 ∧
      Sec21.IsIrreducibleOn (Sec4.autIn (L ⊓ Subgroup.normalizer (A : Set G)) (A ⊓ L)) := by
  obtain ⟨φ⟩ := hM22
  have hspor' := hspor
  obtain ⟨⟨hM22p, hM22z⟩, ⟨hM12p, hM12z⟩, ⟨hJ2p, hJ2z⟩⟩ := hspor'
  have hnotL3 : ¬ IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) := by
    rintro ⟨p, e, hp, -, hiso⟩
    refine hM22L3 p e ?_
    rcases hiso with ⟨hq, ⟨ψ⟩⟩ | ⟨hq, ⟨ψ⟩⟩
    · exact Or.inl ⟨hq, ⟨φ.symm.trans ψ⟩⟩
    · exact Or.inr ⟨hq, ⟨φ.symm.trans ψ⟩⟩
  rcases cases131 h131 hspor hSLC hD with ⟨hcL, h9, -, hcase⟩ | ⟨-, -, hMJ, -⟩ |
      ⟨-, hPGL, -⟩ | ⟨hcL', -⟩
  · refine ⟨hcL, h9, ?_⟩
    have hAe := hD.isElemAbelian
    have hcB : c ∉ A ⊓ L := fun h => hcL h.2
    have hAa := eq_sup_of_card_nine hD h9 hcB
    have hcase' : (True ∧ (Nonempty (Sec4.autIn L A ≃* QuaternionGroup 2) ∨
        Nonempty (Sec4.autIn L A ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)))) ∨
        (True ∧ Nonempty (Sec4.autIn L A ≃* Multiplicative (ZMod 4))) ∨
        (True ∧ Nonempty (Sec4.autIn L A ≃* QuaternionGroup 2)) := by
      rcases hcase with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
      · exact Or.inl ⟨trivial, h⟩
      · exact Or.inr (Or.inl ⟨trivial, h⟩)
      · exact Or.inr (Or.inr ⟨trivial, h⟩)
    obtain ⟨τ, hτ, h4, h2⟩ := exists_order_four_of_cases hcase'
    obtain ⟨ρ, hρ, hρ4, hρ2⟩ := exists_order_four_restrict hD hAa hτ h4 h2
    have hBe : CFSG.Assembly.IsElemAbelian 3 (A ⊓ L) :=
      ⟨⟨⟨fun x y => Subtype.ext (hD.commute x.2.1 y.2.1)⟩⟩, fun x hx => hAe.2 x hx.1⟩
    exact isIrreducibleOn_of_order_four hBe h9 hρ hρ4 hρ2
  · exfalso
    rcases hMJ with hψ | hψ
    · obtain ⟨ψ⟩ := hψ
      obtain ⟨-, -, -, ⟨χ⟩⟩ := facts_of_prod hD hM12p hM12z ψ
      exact hM22M12.false (φ.symm.trans χ)
    · obtain ⟨ψ⟩ := hψ
      obtain ⟨-, -, -, ⟨χ⟩⟩ := facts_of_prod hD hJ2p hJ2z ψ
      exact hM22J2.false (φ.symm.trans χ)
  · exact absurd (facts_of_isZ3PGLThreePi hD hPGL).1 hnotL3
  · exfalso
    have hZ : Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) = ⊥ := by
      have hmap := Subgroup.map_center_eq φ
      rw [hM22z] at hmap
      exact (Subgroup.map_eq_bot_iff_of_injective _ φ.injective).mp hmap
    exact not_mem_of_center_eq_bot hD hZ hcL'

theorem le_of_le_normalizer_of_theta {L Y : Subgroup G} (hLp : Group.IsPerfect L)
    (hLs : IsSimpleGroup (↥L ⧸ aschbacherSolvableCore 3 ↥L))
    (hLY : L ≤ Subgroup.normalizer (Y : Set G)) (h3 : 3 ∣ Nat.card ↥(L ⊓ Y)) : L ≤ Y := by
  obtain ⟨hθs, -, hθ3, -, -⟩ :=
    CFSG.RankThree.LocalRank.solvable_prime_complement_core_characterization (H := ↥L)
      Nat.prime_three
  set θ := aschbacherSolvableCore 3 ↥L with hθdef
  set N := (L ⊓ Y).subgroupOf L with hN
  have hNn : N.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
    (Late.le_normalizer_inf Subgroup.le_normalizer hLY)
  have hNcard : Nat.card N = Nat.card ↥(L ⊓ Y) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hNmap : (N.map (QuotientGroup.mk' θ)).Normal :=
    hNn.map _ (QuotientGroup.mk'_surjective θ)
  have htop : N ⊔ θ = ⊤ := by
    rcases hNmap.eq_bot_or_eq_top with h | h
    · exfalso
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
      have hdvd : Nat.card N ∣ Nat.card θ := Subgroup.card_dvd_of_le h
      exact hθ3 (h3.trans (hNcard ▸ hdvd))
    · have hcomap := Subgroup.comap_map_eq (QuotientGroup.mk' θ) N
      rw [h, Subgroup.comap_top, QuotientGroup.ker_mk'] at hcomap
      exact hcomap.symm
  have hsurj : Function.Surjective ((QuotientGroup.mk' N).comp θ.subtype) := by
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
    have hy : y ∈ N ⊔ θ := htop ▸ Subgroup.mem_top y
    rw [Subgroup.mem_sup_of_normal_left] at hy
    obtain ⟨n, hn, t, ht, rfl⟩ := hy
    refine ⟨⟨t, ht⟩, ?_⟩
    simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
      QuotientGroup.mk'_apply]
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).mpr hn, one_mul]
  have hsolv : Group.IsSolvable (↥L ⧸ N) := Group.isSolvable_of_surjective hsurj
  have hperf : Group.IsPerfect (↥L ⧸ N) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  have hsub : Subsingleton (↥L ⧸ N) := by
    by_contra hnt
    rw [not_subsingleton_iff_nontrivial] at hnt
    exact Group.IsPerfect.not_isSolvable (↥L ⧸ N) hsolv
  intro x hx
  have h1 : (QuotientGroup.mk' N ⟨x, hx⟩ : ↥L ⧸ N) = 1 := Subsingleton.elim _ _
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact (Subgroup.mem_subgroupOf.mp h1).2

@[expose] def Claim153Obs (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ Y ∈ scriptY0Star A LB,
    ∀ S ∈ scriptQPiStar A LB (Subgroup.normalizer
        (oPrimeResidualOf 3 (delta A LB (Subgroup.normalizer (Y : Set G))) : Set G)) (piOf 2),
      S ≤ Subgroup.normalizer (Y : Set G)

@[expose] def KS15M22Gen : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L →
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M22) →
    ∀ Y ∈ scriptY0Star A (lB A), Y = (L ⊓ Y) ⊔ CFSG.Open.pCoreOf 2 Y →
      ∀ T ∈ scriptQPiStar A (lB A) (Subgroup.normalizer (Subgroup.zpowers c : Set G)) (piOf 2),
        L ≤ (T ⊓ L) ⊔ (L ⊓ Y)

end CFSG.RankThree.PartTwo.Sec15
