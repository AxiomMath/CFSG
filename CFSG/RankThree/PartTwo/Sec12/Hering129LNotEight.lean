module

public import CFSG.RankThree.PartTwo.Sec12.Hering129HKFK
public import CFSG.RankThree.PartTwo.Sec8.Hering418ROuter
public import CFSG.RankThree.PartTwo.KFacts.K72SLPiCField
import CFSG.SignalizerFunctorTheorem.CatalogBridge.NearPSL2
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.RankThree.PartTwo.Sec12.Hering129HDefs
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.RankThree.PartTwo.Sec12

namespace Hering129L

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)

section Dickson

@[expose] def Psl28ProperSolvable : Prop :=
  ∀ H : Subgroup (projSL 2 (GaloisField 2 3)), H ≠ ⊤ → Group.IsSolvable ↥H

theorem psl28ProperSolvable_holds : Psl28ProperSolvable := by
  intro H hH
  let e := Sec4.projSLEquivPSL (GaloisField 2 3)
  have hne : H.map e.toMonoidHom ≠ ⊤ := by
    intro htop
    apply hH
    rw [eq_top_iff]
    intro y _
    have : e y ∈ H.map e.toMonoidHom := htop ▸ Subgroup.mem_top _
    obtain ⟨y', hy', hyy'⟩ := this
    have : y' = y := e.injective hyy'
    exact this ▸ hy'
  have hs := CFSG.SignalizerFunctorTheorem.CatalogBridge.proper_subgroup_solvable_psl2_even
    (p := 3) Nat.prime_three (by decide) _ hne
  have e' := H.equivMapOfInjective e.toMonoidHom e.injective
  haveI := hs
  exact Group.isSolvable_of_isSolvable_injective (f := e'.toMonoidHom) e'.injective

end Dickson

section SU2

theorem isSolvable_of_isSLThreePiAt_two {X : Type} [Group X] (h : Sec4.IsSLThreePiAt X 2) :
    Group.IsSolvable X := by
  obtain ⟨K, hKf, hKfin, h1 | h1⟩ := h
  · exact absurd h1.2.1 (by norm_num)
  · obtain ⟨hK, -, ⟨e⟩⟩ := h1
    have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 K :=
      ⟨Nat.prime_two, le_rfl, by simpa using hK⟩
    have hc : Nat.card (CFSG.Open.StatedSU 3 (2 ^ 1) K) = 216 :=
      CFSG.RankThree.CentralLiftU.card_statedSU_three_two hU rfl
    have hfin : Finite ↥(CFSG.Open.StatedSU 3 (2 ^ 1) K) :=
      Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
    have := Fintype.ofFinite ↥(CFSG.Open.StatedSU 3 (2 ^ 1) K)
    have hsolv : Group.IsSolvable ↥(CFSG.Open.StatedSU 3 (2 ^ 1) K) :=
      CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := 3) (b := 3)
        Nat.prime_two Nat.prime_three (by norm_num)
        (by rw [← Nat.card_eq_fintype_card, hc]; norm_num)
    haveI := hsolv
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

end SU2

section Main

variable {G : Type} [Group G] [Finite G]

theorem not_isSolvable_imageModTheta {Y X : Subgroup G} (hXY : X ≤ Y)
    (hq : IsQuasisimple (↥X ⧸ aschbacherSolvableCore 3 ↥X)) :
    ¬ Group.IsSolvable ↥(Sec8.imageModTheta Y X) := by
  intro hs
  set φ := Sec8.Item87Res2Proof.toQuot hXY with hφ
  have hrange : φ.range = Sec8.imageModTheta Y X := Sec8.Item87Res2Proof.range_toQuot hXY
  haveI hs' : Group.IsSolvable ↥φ.range := by rw [hrange]; exact hs
  haveI h1 : Group.IsSolvable (↥X ⧸ φ.ker) :=
    Group.isSolvable_of_isSolvable_injective (QuotientGroup.quotientKerEquivRange φ).injective
  have hker : φ.ker ≤ aschbacherSolvableCore 3 ↥X := Sec8.Item87Res2Proof.ker_toQuot_le hXY
  let ψ : (↥X ⧸ φ.ker) →* (↥X ⧸ aschbacherSolvableCore 3 ↥X) :=
    QuotientGroup.map φ.ker (aschbacherSolvableCore 3 ↥X) (MonoidHom.id _) hker
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨(x : ↥X ⧸ φ.ker), rfl⟩
  haveI h2 : Group.IsSolvable (↥X ⧸ aschbacherSolvableCore 3 ↥X) :=
    Group.isSolvable_of_surjective hψ
  haveI : Nontrivial (↥X ⧸ aschbacherSolvableCore 3 ↥X) :=
    CFSG.LocalCores.isQuasisimple_nontrivial hq
  haveI : Group.IsPerfect (↥X ⧸ aschbacherSolvableCore 3 ↥X) := hq.1
  exact Group.IsPerfect.not_isSolvable _ h2

section Cert


theorem gap129YNotEightField_of (hKK : Gap129KFKStrong) (hP8 : Psl28ProperSolvable) :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (b a : G)
      (K S : Subgroup G), Cfg129 G A c L b a K S → ∀ q : TauCeti.PrimePower,
      GTwoType129At L K q → ∀ x ∈ D129 a b, x ∉ Subgroup.zpowers b →
        ∀ Y : Subgroup G, Core129 A c x Y → resCent K x ≤ Y →
          KFacts.InducesStdKind Y b .field →
          ¬ Nonempty (Y ⧸ aschbacherSolvableCore 3 Y ≃*
            CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 2 3)) ∧
          ¬ Sec4.IsSLThreePiAt (Y ⧸ aschbacherSolvableCore 3 Y) 8 := by
  intro G _ _ A c L b a K S cfg q hq x hxD hxb Y hY hXY hfield
  obtain ⟨hYx, hAN, hAC, -⟩ := id hY
  obtain ⟨-, -, hXq, -⟩ := hKK G A c L b a K S cfg ⟨q, hq⟩ x hxD hxb
  have hstd := cfg.std
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hstd.isE27.1
  obtain ⟨hbA, haA, haL, hb1, ha1, haB, hbL, hab, haD, -⟩ := cfg.point_facts
  have hDA : D129 a b ≤ A :=
    sup_le (Subgroup.zpowers_le.mpr haA) (Subgroup.zpowers_le.mpr hbA)
  have hxA : x ∈ A := hDA hxD
  have hx1 : x ≠ 1 := fun h => hxb (h ▸ Subgroup.one_mem _)
  have hx3 : x ^ 3 = 1 := hAe.2 x hxA
  have hb3 : b ^ 3 = 1 := hAe.2 b hbA
  have hbx : b ∉ Subgroup.zpowers x := fun h =>
    hxb (mem_of_mem_zpowers_of_ne_one (orderOf_eq_prime hx3 hx1) h hb1 (Subgroup.mem_zpowers b))
  have hbN : b ∈ Subgroup.normalizer (Y : Set G) := hAN hbA
  have hKb : K ≤ Subgroup.centralizer ({b} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt cfg.hK
  have hXb : resCent K x ≤ Subgroup.centralizer ({b} : Set G) :=
    ((resCent_le K x).trans inf_le_left).trans hKb
  have hle := Sec8.Hering418.imageModTheta_le_barCentralizer_of_le hbN hb3 hXY hXb
  have hns := not_isSolvable_imageModTheta hXY hXq
  refine ⟨?_, ?_⟩
  · rintro ⟨e⟩
    have hC : Sec8.barCentralizer (Subgroup.zpowers b) Y = ⊤ := by
      by_contra hne
      set C := Sec8.barCentralizer (Subgroup.zpowers b) Y with hCdef
      have hmap : C.map e.toMonoidHom ≠ ⊤ := by
        intro htop
        apply hne
        rw [eq_top_iff]
        intro y _
        have : e y ∈ C.map e.toMonoidHom := htop ▸ Subgroup.mem_top _
        obtain ⟨y', hy', hyy'⟩ := this
        have : y' = y := e.injective hyy'
        exact this ▸ hy'
      haveI hs := hP8 _ hmap
      let eC := C.equivMapOfInjective e.toMonoidHom e.injective
      haveI hCs : Group.IsSolvable ↥C :=
        Group.isSolvable_of_isSolvable_injective (f := eC.toMonoidHom) eC.injective
      exact hns (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle))
    have hfix : ∀ y, Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨b, hbN⟩) y = y := fun y =>
      (KFacts.mem_barCentralizer_zpowers_iff hbN y).mp (hC ▸ Subgroup.mem_top y)
    have hbθ : b ∈ Sec4.thetaQuotCentralizer Y := by
      refine ⟨⟨b, hbN⟩, MonoidHom.mem_ker.mpr ?_, rfl⟩
      ext y
      exact hfix y
    have : b ∈ A ⊓ Sec4.thetaQuotCentralizer Y := ⟨hbA, hbθ⟩
    rw [hAC] at this
    exact hbx this
  · intro hSL
    have h8 : (8 : ℕ) = 2 ^ (3 * 1) := by norm_num
    rw [h8] at hSL
    have hC := KFacts.isSLThreePiAt_barCentralizer_of_field (n := 1) le_rfl hSL hb3 (Or.inl hfield)
    haveI hCs : Group.IsSolvable ↥(Sec8.barCentralizer (Subgroup.zpowers b) Y) :=
      isSolvable_of_isSLThreePiAt_two (by simpa using hC)
    exact hns (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle))

end Cert

end Main

end Hering129L

end CFSG.RankThree.PartTwo.Sec12
