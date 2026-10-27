module

public import CFSG.RankThree.PartTwo.Sec16.Item169StepsProof1612
public import CFSG.RankThree.PartTwo.Sec15.Item1517StepsProofY0
import CFSG.RankThree.PartTwo.Sec16.Item16Res4ProofA7
import CFSG.RankThree.PartTwo.Sec16.Item1613ResProofFix
import CFSG.RankThree.PartTwo.Sec16.Item163StepsQProofQL
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec4.Census.Lift46
import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS

@[expose] noncomputable def KS1612GenPGL : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Ctx169 G A c L → Sec8.IsZ3PGLThreePi (lBarA c L A) →
      (∃ x ∈ A, Sec4.InducesTypeOn L x 3) →
        L ≤ sSup (invariantPiSubgroups L A (piCompl 3))

namespace Proof1612Gen

variable {G : Type} [Group G] [Finite G]

open Proof163L4A7

theorem le_sSup_of_inner {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    (hAc : A = Subgroup.zpowers c ⊔ (A ⊓ L))
    (𝒲 : Set (Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)))
    (h𝒲 : ∀ W ∈ 𝒲, ¬ 3 ∣ Nat.card W ∧
      (A.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) ≤
        Subgroup.normalizer (W : Set (↥L ⧸ aschbacherSolvableCore 3 ↥L)))
    (htop : sSup 𝒲 = ⊤) : L ≤ sSup (invariantPiSubgroups L A (piCompl 3)) := by
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  set π := QuotientGroup.mk' θ with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective θ
  set T := sSup (invariantPiSubgroups L A (piCompl 3)) with hT
  set X : Subgroup ↥L := sSup ((fun W => W.comap π) '' 𝒲) ⊔ π.ker with hX
  have hXtop : X = ⊤ := by
    have hmap : Subgroup.map π X = ⊤ := by
      refine top_le_iff.mp (htop ▸ sSup_le fun W hW => ?_)
      calc W = (W.comap π).map π := (Subgroup.map_comap_eq_self_of_surjective hπs W).symm
        _ ≤ Subgroup.map π X :=
          Subgroup.map_mono (le_sup_left.trans' (le_sSup ⟨W, hW, rfl⟩))
    have h1 := Subgroup.comap_map_eq π X
    rw [hmap, Subgroup.comap_top, sup_eq_left.mpr le_sup_right] at h1
    exact h1.symm
  have hX : X ≤ T.comap L.subtype := by
    refine sup_le (sSup_le ?_) ?_
    · rintro _ ⟨W, hW, rfl⟩
      rw [← Subgroup.map_le_iff_le_comap]
      exact le_sSup (mem_invariantPiSubgroups_of_inner h hAc W (h𝒲 W hW).1 (h𝒲 W hW).2)
    · have hker : π.ker = (⊥ : Subgroup (↥L ⧸ θ)).comap π := by
        rw [MonoidHom.comap_bot]
      rw [hker, ← Subgroup.map_le_iff_le_comap]
      refine le_sSup (mem_invariantPiSubgroups_of_inner h hAc ⊥ ?_ ?_)
      · rw [Subgroup.card_bot]
        norm_num
      · rw [Subgroup.normalizer_eq_top]
        exact le_top
  intro l hl
  have hl' : (⟨l, hl⟩ : ↥L) ∈ X := hXtop ▸ Subgroup.mem_top _
  exact hX hl'

theorem facts_of_isZ3LThreeTwo
    {A : Subgroup G} {c : G} {L : Subgroup G}
    (hD : Sec13Data G A c L) {n : ℕ} (hn : IsZ3LThreeTwo A c L n) :
    c ∉ L ∧ Nat.card (A ⊓ L : Subgroup G) = 9 ∧ A = Subgroup.zpowers c ⊔ (A ⊓ L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hn1, hiso, ⟨ψ⟩⟩ := hn
  have hLc : L ∈ thetaComponentsAt 3 c := hD.mem_thetaComponentsAt
  have h9 : Nat.card (A ⊓ L : Subgroup G) = 9 := card_inf_eq_nine hD (isPerfect_lBar hD) ψ
  have hZ : Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) = ⊥ :=
    Sec15.center_eq_bot_of_types hLc (Or.inr (Or.inl ⟨2, n, inferInstance, hn1, hiso⟩))
  have hcL : c ∉ L := not_mem_of_center_eq_bot hD hZ
  refine ⟨hcL, h9, ?_⟩
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE hD.mem_partTwoE
  have hcA : Subgroup.zpowers c ≤ A := Subgroup.zpowers_le.mpr hD.mem_A
  have hle : Subgroup.zpowers c ⊔ (A ⊓ L) ≤ A := sup_le hcA inf_le_left
  have hcomm : ∀ x ∈ Subgroup.zpowers c, ∀ y ∈ A ⊓ L, x * y = y * x := fun x hx y hy =>
    hD.commute (hcA hx) hy.1
  have hdisj : Subgroup.zpowers c ⊓ (A ⊓ L) = ⊥ := by
    rw [eq_bot_iff, ← Sec4.Census.inf_zpowers_eq_bot_of_not_mem Nat.prime_three hD.orderOf_eq
      hcL]
    exact fun x hx => ⟨hx.2.2, hx.1⟩
  have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm).1
  rw [hdisj, Subgroup.card_bot, mul_one, Nat.card_zpowers, hD.orderOf_eq, h9] at hcard
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hA.2])).symm

theorem le_sSup_of_isZ3LThreeTwo
    (hK : KS1517Gen) {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec15R G A c L) {n : ℕ} (hn : IsZ3LThreeTwo A c L n)
    (hmod : ¬ (2 ^ n % 9 = 1 ∨ 2 ^ n % 9 = 8))
    (h34 : IsEmpty (lBarA c L A ≃* Multiplicative (ZMod 3) ×
      CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2))) :
    L ≤ sSup (invariantPiSubgroups L A (piCompl 3)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := h.toSec13Data
  obtain ⟨-, h9, hAc⟩ := facts_of_isZ3LThreeTwo hD hn
  obtain ⟨hn1, hiso, ⟨ψ⟩⟩ := hn
  have hLc : L ∈ thetaComponentsAt 3 c := hD.mem_thetaComponentsAt
  have hq := Sec6.isQuasisimple_of_mem_thetaComponentsAt hLc
  obtain ⟨η, -⟩ := exists_lBarEquiv hLc
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) with hπ
  set Ab := (A.subgroupOf L).map π with hAb
  have hAb9 : Nat.card Ab = 9 := by
    rw [hAb, hπ, card_map_mk_subgroupOf hD.isElemAbelian, h9]
  have hEab : CFSG.Assembly.IsElemAbelian 3 Ab :=
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 π _
      (isElemAbelian_subgroupOf hD.isElemAbelian)
  have hnot22 : ¬ Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) 2 2 := by
    rintro (⟨-, ⟨φ⟩⟩ | ⟨h3, -⟩)
    · exact h34.false (ψ.trans (MulEquiv.prodCongr (MulEquiv.refl _) (η.symm.trans φ)))
    · norm_num at h3
  have hgen := hK (↥L ⧸ aschbacherSolvableCore 3 ↥L) 2 n hn1 hiso hq.1 hmod hnot22 Ab hEab hAb9
  refine le_sSup_of_inner h hAc (invariantPiSubgroups ⊤ Ab (piCompl 3)) (fun W hW => ?_) hgen
  exact ⟨(isPiSubgroup_piCompl_iff Nat.prime_three W).mp hW.2.1, hW.2.2⟩

end Proof1612Gen

open Proof1612Gen

theorem step1612Gen_of
    (h131 : Item131) (hK : KS1517Gen) (hP : KS1612GenPGL) :
    Step1612Gen := by
  intro G _ _ A c L h h1611 hmod h34
  rcases h1611 with hPGL | ⟨n, hn⟩
  · exact hP G A c L h hPGL (Proof1613Res.exists_type_three h131 h hPGL)
  · exact le_sSup_of_isZ3LThreeTwo hK h.toSec15R hn (hmod n hn) h34

end CFSG.RankThree.PartTwo.Sec16
