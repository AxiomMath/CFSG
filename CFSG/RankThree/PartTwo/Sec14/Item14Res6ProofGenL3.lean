module

public import CFSG.RankThree.PartTwo.Sec14.Item14Res5ProofGen
public import CFSG.RankThree.PartTwo.Sec14.Item143StepsProofLThree
public import CFSG.RankThree.PartTwo.Sec15.Item1513Res3ProofCentGen
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec13.Item13SLTwo
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.Sec15.Item1423ProofTools
import CFSG.RankThree.PartTwo.Sec4.Census.Lift46
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ThetaRankThree

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projSL)

@[expose] def KS142L3HessGenNine : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p e : ℕ) [Fact p.Prime], 1 ≤ e →
    Sec4.IsoLThreePi X p e → Group.IsPerfect X → (p ^ e % 9 = 1 ∨ p ^ e % 9 = 8) →
    ¬ Sec4.IsoLThreePi X 2 3 →
    ∀ E : Subgroup X, CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 9 →
      (∀ y₀ ∈ E, y₀ ≠ 1 → ∀ y₁ ∈ E, y₁ ≠ 1 →
        ∃ w ∈ Subgroup.normalizer (E : Set X), w * y₀ * w⁻¹ = y₁) →
      sSup {Y : Subgroup X | ¬ 3 ∣ Nat.card Y ∧ E ≤ Subgroup.normalizer (Y : Set X)} = ⊤

@[expose] def KS142U38Alpha : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Sec4.IsoLThreePi X 2 3 →
    ∀ E : Subgroup X, CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 9 →
      (∀ y₀ ∈ E, y₀ ≠ 1 → ∀ y₁ ∈ E, y₁ ≠ 1 →
        ∃ w ∈ Subgroup.normalizer (E : Set X), w * y₀ * w⁻¹ = y₁) →
      ∀ Y : Subgroup (MulAut X), (MulAut.conj : X →* MulAut X).range ≤ Y →
        thetaAlpha 3 ((E.map (MulAut.conj : X →* MulAut X)).subgroupOf Y) = ⊥

@[expose] def Step142LowerGenL3PGL : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L →
    IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) →
    ¬ Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × projSL 3 (GaloisField 2 2)) →
    Sec8.IsZ3PGLThreePi (lBarA c L A) →
    Nonempty (Sec4.autIn L A ≃* Multiplicative (ZMod 3)) → (∃ x ∈ A, Sec4.InducesTypeOn L x 3) →
    sSup {X : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L) | ¬ 3 ∣ Nat.card X ∧
      ∀ σ ∈ Sec4.autThetaQuot A L, X.map σ.toMonoidHom ≤ X} = ⊤

namespace Res6GenL3

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem centralizer_le_normalizer_zpowers' (c : G) :
    Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
  refine le_trans (fun x hx => ?_) (Subgroup.centralizer_le_normalizer _)
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  exact hx

theorem autThetaQuot_eq_map_conj {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (hAc : A = Subgroup.zpowers c ⊔ (A ⊓ L)) :
    Sec4.autThetaQuot A L = (((A ⊓ L).subgroupOf L).map
      (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))).map
        (MulAut.conj : (↥L ⧸ aschbacherSolvableCore 3 ↥L) →* MulAut _) := by
  have hD := h.toSec13Data
  have hLc := hD.le_centralizer
  have hcA := hD.mem_A
  have hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy => hD.commute hx hy
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  have hconj : ∀ (g : G) (hgN : g ∈ Subgroup.normalizer (L : Set G)) (hg : g ∈ L),
      Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨g, hgN⟩) =
        MulAut.conj (QuotientGroup.mk' θ ⟨g, hg⟩) := by
    intro g hgN hg
    ext q
    induction q using QuotientGroup.induction_on with
    | H l =>
      change (((L.normalizerMonoidHom ⟨g, hgN⟩ l : L)) : ↥L ⧸ θ) =
        (QuotientGroup.mk' θ ⟨g, hg⟩) * (l : ↥L ⧸ θ) * (QuotientGroup.mk' θ ⟨g, hg⟩)⁻¹
      rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
        ← QuotientGroup.mk_mul]
      rfl
  apply le_antisymm
  · intro σ hσ
    obtain ⟨a, haN, haA, rfl⟩ := Sec4.mem_autThetaQuot_iff.mp hσ
    rw [hAc, sup_comm] at haA
    obtain ⟨β, hβ, j, rfl⟩ :=
      Res4L34.exists_eq_mul_zpow_of_mem_sup (B := A ⊓ L) (fun β hβ => hAab β hβ.1 c hcA) haA
    refine ⟨QuotientGroup.mk' θ ⟨β, hβ.2⟩,
      ⟨⟨β, hβ.2⟩, Subgroup.mem_subgroupOf.mpr hβ, rfl⟩, ?_⟩
    rw [← hconj β (L.le_normalizer hβ.2) hβ.2]
    ext q
    induction q using QuotientGroup.induction_on with
    | H l =>
      change (((L.normalizerMonoidHom ⟨β, L.le_normalizer hβ.2⟩ l : L)) : ↥L ⧸ θ) =
        (((L.normalizerMonoidHom ⟨β * c ^ j, haN⟩ l : L)) : ↥L ⧸ θ)
      congr 1
      refine Subtype.ext ?_
      have hlc : Commute (l : G) c := Subgroup.mem_centralizer_singleton_iff.mp (hLc l.2)
      change β * (l : G) * β⁻¹ = (β * c ^ j) * (l : G) * (β * c ^ j)⁻¹
      have hcj : c ^ j * (l : G) * (c ^ j)⁻¹ = l := by
        rw [((hlc.symm).zpow_left j).eq]
        group
      calc β * (l : G) * β⁻¹ = β * (c ^ j * (l : G) * (c ^ j)⁻¹) * β⁻¹ := by rw [hcj]
        _ = (β * c ^ j) * (l : G) * (β * c ^ j)⁻¹ := by group
  · rintro _ ⟨_, ⟨β, hβ, rfl⟩, rfl⟩
    have hβ' := Subgroup.mem_subgroupOf.mp hβ
    exact Sec4.mem_autThetaQuot_iff.mpr ⟨β, L.le_normalizer β.2, hβ'.1,
      hconj β (L.le_normalizer β.2) β.2⟩

theorem range_conj_le_autThetaQuot {A L : Subgroup G} {c : G} (h : Sec14Std G A c L) :
    (MulAut.conj : (↥L ⧸ aschbacherSolvableCore 3 ↥L) →* MulAut _).range ≤
      Sec4.autThetaQuot (Subgroup.normalizer (Subgroup.zpowers c : Set G)) L := by
  have hLc := h.toSec13Data.le_centralizer
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  rintro _ ⟨x, rfl⟩
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
  refine Sec4.mem_autThetaQuot_iff.mpr ⟨l, L.le_normalizer l.2,
    centralizer_le_normalizer_zpowers' c (hLc l.2), ?_⟩
  ext q
  induction q using QuotientGroup.induction_on with
  | H m =>
    change (((L.normalizerMonoidHom ⟨(l : G), L.le_normalizer l.2⟩ m : L)) : ↥L ⧸ θ) =
      (l : ↥L ⧸ θ) * (m : ↥L ⧸ θ) * (l : ↥L ⧸ θ)⁻¹
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    rfl

theorem not_isoLThreePi_two_two {A L : Subgroup G} {c : G} (hD : Sec13Data G A c L)
    (hprod : Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × Sec12.lBar c L))
    (hL34 : ¬ Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × projSL 3 (GaloisField 2 2))) :
    ¬ Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) 2 2 := by
  rintro (⟨-, ⟨ψ⟩⟩ | ⟨h42, -⟩)
  · obtain ⟨η, -⟩ := exists_lBarEquiv hD.mem_thetaComponentsAt
    obtain ⟨φ⟩ := hprod
    exact hL34 ⟨φ.trans (MulEquiv.prodCongr (MulEquiv.refl _) (η.symm.trans ψ))⟩
  · norm_num at h42

theorem invariantPiSubgroups_top_piCompl_eq {X : Type*} [Group X] (D : Subgroup X) :
    invariantPiSubgroups ⊤ D (piCompl 3) =
      {Y : Subgroup X | ¬ 3 ∣ Nat.card Y ∧ D ≤ Subgroup.normalizer (Y : Set X)} := by
  ext Y
  rw [mem_invariantPiSubgroups_piCompl_iff Nat.prime_three]
  exact ⟨fun h => ⟨h.2.1, h.2.2⟩, fun h => ⟨le_top, h.1, h.2⟩⟩

end Res6GenL3

open Res6GenL3 Res5Gen in
theorem step142LowerGenL3_of
    (h131 : Item131) (hU : Sec15.KS1517SeitzU)
    (h9 : KS142L3HessGenNine) (hU38 : KS142U38Alpha) (hPGL : Step142LowerGenL3PGL) :
    Step142LowerGenL3 := by
  intro G _ _ A c L h hL3 hL34
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := h.toSec13Data
  have hspor := Sec13.sporadicModels131
  have hLq : CFSG.IsQuasisimple (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
    Sec15.Proof1423.isQuasisimple_of_mem_thetaComponentsIn1423
      (M := Subgroup.centralizer ({c} : Set G)) hD.mem_thetaComponentsAt
  have hLp : Group.IsPerfect (↥L ⧸ aschbacherSolvableCore 3 ↥L) := hLq.1
  have : Nontrivial (↥L ⧸ aschbacherSolvableCore 3 ↥L) := LocalCores.isQuasisimple_nontrivial hLq
  have hZ := center_eq_bot_of_isLThreePi hL3 hLp
  have hcL' : c ∉ L := not_mem_of_center_eq_bot hD hZ
  rcases cases131 h131 hspor slTwoCenter hD with
      ⟨hcL, h9AL, hprod, hcase⟩ | ⟨-, -, hcase, -⟩ | ⟨-, hPGLA, hstar, hx⟩ | ⟨hcL, -⟩
  · rcases hcase with ⟨-, hQ⟩ | ⟨⟨φ⟩, -⟩ | ⟨⟨φ⟩, -⟩
    ·
      have hA : Late.IsE27 A := h.isE27'
      have hcA := hD.mem_A
      have hc3 : c ^ 3 = 1 := hD.isElemAbelian.2 c hcA
      have hLc : ∀ l ∈ L, l * c = c * l := fun l hl =>
        (Subgroup.mem_centralizer_singleton_iff.mp (hD.le_centralizer hl))
      have hAc : A = Subgroup.zpowers c ⊔ (A ⊓ L) := by
        have hcAL : Subgroup.zpowers c ≤ A := Subgroup.zpowers_le.mpr hcA
        have hle : Subgroup.zpowers c ⊔ (A ⊓ L) ≤ A := sup_le hcAL inf_le_left
        have hcomm : ∀ x ∈ Subgroup.zpowers c, ∀ y ∈ A ⊓ L, x * y = y * x := fun x hx y hy =>
          hD.commute (hcAL hx) hy.1
        have hdisj : Subgroup.zpowers c ⊓ (A ⊓ L) = ⊥ := by
          rw [eq_bot_iff, ← Sec4.Census.inf_zpowers_eq_bot_of_not_mem Nat.prime_three
            hD.orderOf_eq hcL]
          exact fun x hx => ⟨hx.2.2, hx.1⟩
        have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm).1
        rw [hdisj, Subgroup.card_bot, mul_one, Nat.card_zpowers, hD.orderOf_eq, h9AL] at hcard
        exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hA.2])).symm
      have hB : CFSG.Assembly.IsElemAbelian 3 (A ⊓ L) :=
        ⟨⟨⟨fun x y => Subtype.ext (hD.commute x.2.1 y.2.1)⟩⟩,
          fun x hx => hD.isElemAbelian.2 x hx.1⟩
      set θ := aschbacherSolvableCore 3 ↥L with hθ
      set π := QuotientGroup.mk' θ with hπ
      have hEq : (A ⊓ L).subgroupOf L = A.subgroupOf L := Subgroup.inf_subgroupOf_right A L
      set Ebar := ((A ⊓ L).subgroupOf L).map π with hEbar
      have hE9 : Nat.card Ebar = 9 := by
        rw [hEbar, hEq, card_map_mk_subgroupOf hD.isElemAbelian, h9AL]
      have hEe : CFSG.Assembly.IsElemAbelian 3 Ebar := by
        rw [hEbar, hEq]
        exact CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 π (A.subgroupOf L)
          (CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_subgroupOf 3 A L
            hD.isElemAbelian)
      have hpt : ∀ z ∈ Ebar, z ≠ 1 → ∃ y ∈ A ⊓ L, y ≠ 1 ∧ ∃ hyL : y ∈ L, π ⟨y, hyL⟩ = z := by
        rintro z ⟨y', hy', rfl⟩ hz1
        refine ⟨y', Subgroup.mem_subgroupOf.mp hy', fun hy1 => hz1 ?_, y'.2, rfl⟩
        have : y' = 1 := Subtype.ext hy1
        rw [this, map_one]
      have htrans : ∀ y₀ ∈ Ebar, y₀ ≠ 1 → ∀ y₁ ∈ Ebar, y₁ ≠ 1 →
          ∃ w ∈ Subgroup.normalizer (Ebar : Set (↥L ⧸ θ)), w * y₀ * w⁻¹ = y₁ := by
        intro z₀ hz₀ hz₀1 z₁ hz₁ hz₁1
        obtain ⟨y₀, hy₀, hy₀1, hy₀L, rfl⟩ := hpt z₀ hz₀ hz₀1
        obtain ⟨y₁, hy₁, hy₁1, hy₁L, rfl⟩ := hpt z₁ hz₁ hz₁1
        obtain ⟨w, hwL, hwN, hw⟩ :=
          exists_conj_eq_of_autIn hc3 hcL hLc hAc hB h9AL hQ hy₀ hy₁ hy₀1 hy₁1
        refine ⟨π ⟨w, hwL⟩, ?_, ?_⟩
        · have hwN' : (⟨w, hwL⟩ : ↥L) ∈ Subgroup.normalizer
              (((A ⊓ L).subgroupOf L : Subgroup ↥L) : Set ↥L) := by
            rw [Subgroup.mem_normalizer_iff]
            intro x
            rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
            exact Subgroup.mem_normalizer_iff.mp hwN (x : G)
          exact Subgroup.le_normalizer_map π ⟨_, hwN', rfl⟩
        · rw [← map_mul, ← map_inv, ← map_mul]
          congr 1
          exact Subtype.ext hw
      refine sSup_autThetaQuot_eq_top_of_inner h hAc ?_
      obtain ⟨p, e, hp, he, hiso⟩ := hL3
      by_cases hmod : p ^ e % 9 = 1 ∨ p ^ e % 9 = 8
      · by_cases hU38' : Sec4.IsoLThreePi (↥L ⧸ θ) 2 3
        ·
          exfalso
          obtain ⟨-, -, -, hα⟩ := mem_lA_iff.mp hD.mem_lA
          rw [autThetaQuot_eq_map_conj h hAc] at hα
          exact hα (hU38 _ hU38' Ebar hEe hE9 htrans _ (range_conj_le_autThetaQuot h))
        · exact h9 _ p e he hiso hLp hmod hU38' Ebar hEe hE9 htrans
      · have hL4 := not_isoLThreePi_two_two hD hprod hL34
        have hgen := Sec15.ks1517Gen_of (Sec15.ks1517CentGen_of hU) _ p e he hiso hLp hmod hL4
          Ebar hEe hE9
        rwa [invariantPiSubgroups_top_piCompl_eq] at hgen
    · exact absurd hL3 (not_isLThreePi_of_mulEquiv φ not_isoLThreePi_alternating_seven)
    · exact absurd hL3 (not_isLThreePi_of_mulEquiv φ KFacts.KS14.not_isoLThreePi_M22)
  ·
    obtain ⟨⟨hM22p, hM22z⟩, ⟨hM12p, hM12z⟩, ⟨hJ2p, hJ2z⟩⟩ := hspor
    rcases hcase with hφ | hφ
    · obtain ⟨φ⟩ := hφ
      obtain ⟨-, -, -, ⟨ψ⟩⟩ := facts_of_prod hD hM12p hM12z φ
      exact absurd hL3 (not_isLThreePi_of_mulEquiv ψ KFacts.KS14.not_isoLThreePi_M12)
    · obtain ⟨φ⟩ := hφ
      obtain ⟨-, -, -, ⟨ψ⟩⟩ := facts_of_prod hD hJ2p hJ2z φ
      exact absurd hL3 (not_isLThreePi_of_mulEquiv ψ KFacts.KS14.ks17J2NotList.1)
  ·
    exact hPGL G A c L h hL3 hL34 hPGLA hstar hx
  · exact absurd hcL hcL'

end CFSG.RankThree.PartTwo.Sec14
