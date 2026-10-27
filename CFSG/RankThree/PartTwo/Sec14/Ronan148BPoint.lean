module

public import CFSG.RankThree.PartTwo.Sec14.Item148Res7ProofPoint
public import CFSG.RankThree.PartTwo.Sec13.Item131Facts
public import CFSG.RankThree.PartTwo.Sec14.Ronan148BL3PointFacts
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec13.Item13SLTwo
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec15.Item1423ProofTools
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec13.Item13Res4ProofAlpha
public import CFSG.RankThree.PartTwo.Sec14.Item148PointProofOmega
public import CFSG.RankThree.PartTwo.Sec15.HypS

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148B

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

@[expose] def KF148PointSigF : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (A L R W Q B : Subgroup Γ) (b : Γ),
    Late.IsE27 A → b ∈ A → b ≠ 1 → L ≤ Subgroup.centralizer ({b} : Set Γ) →
    A ≤ Subgroup.normalizer (L : Set Γ) →
    Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) =
      (Subgroup.zpowers b : Set Γ) →
    (∀ x ∈ Subgroup.centralizer (A : Set Γ), x ^ 3 = 1 → x ∈ A) →
    ((b ∉ L ∧ Nat.card (A ⊓ L : Subgroup Γ) = 9 ∧
        Nonempty (lBarA b L A ≃* Multiplicative (ZMod 3) × Sec12.lBar b L) ∧
        ((IsLThreePi (L ⧸ aschbacherSolvableCore 3 L) ∧
            (Nonempty (Sec4.autIn L A ≃* QuaternionGroup 2) ∨
              Nonempty (Sec4.autIn L A ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)))) ∨
          (Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* alternatingGroup (Fin 7)) ∧
            Nonempty (Sec4.autIn L A ≃* Multiplicative (ZMod 4))) ∨
          (Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Blueprint.NativeSporadic.M22) ∧
            Nonempty (Sec4.autIn L A ≃* QuaternionGroup 2)))) ∨
      (b ∉ L ∧ Nat.card (A ⊓ L : Subgroup Γ) = 9 ∧
        (Nonempty (lBarA b L A ≃* Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.M12) ∨
          Nonempty (lBarA b L A ≃* Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.J2)) ∧
        Nonempty (Sec4.autIn L A ≃* Equiv.Perm (Fin 3))) ∨
      (b ∉ L ∧ Sec8.IsZ3PGLThreePi (lBarA b L A) ∧
        Nonempty (Sec4.autIn L A ≃* Multiplicative (ZMod 3)) ∧
        ∃ x ∈ A, Sec4.InducesTypeOn L x 3)) →
    (Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) ∨
      IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M22) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M12)) →
    (∃ (X' : Type) (_ : Group X') (_ : Finite X'), Sec4.IsList46 X' ∧
      Nonempty (X' ≃* ↥L ⧸ aschbacherSolvableCore 3 ↥L)) →
    (IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) → L3PointFacts A L b) →
    Nat.Coprime 3 (Nat.card R) → L ≤ Subgroup.normalizer (R : Set Γ) →
    R ≤ Subgroup.normalizer (L : Set Γ) → A ≤ Subgroup.normalizer (R : Set Γ) →
    W ≤ L ⊔ R → A ≤ Subgroup.normalizer (W : Set Γ) →
    IsHyperplane A B → b ∈ B → Q ≤ W ⊓ Subgroup.centralizer (B : Set Γ) →
    Q ∈ invariantPiSubgroups ⊤ A (piCompl 3) → Q = ⁅Q, A⁆ →
    (∀ H : Subgroup Γ, IsHyperplane A H → ∀ V : Subgroup Γ,
      V ≤ W ⊓ Subgroup.centralizer (H : Set Γ) → V ∈ invariantPiSubgroups ⊤ A (piCompl 3) →
      V = ⁅V, A⁆ → V ≤ pPrimeCoreOf 3 (W ⊓ Subgroup.centralizer (H : Set Γ))) →
    ¬ Q ≤ pPrimeCoreOf 3 W →
    ∃ K ∈ thetaComponentsIn W, K ≤ L ∧
      K ≤ sSup {V : Subgroup Γ | V ≤ K ∧ V ∈ invariantPiSubgroups ⊤ A (piCompl 3) ∧ V = ⁅V, A⁆}

namespace Res148BPoint

variable {G : Type} [Group G] [Finite G]

section Certs

theorem mem_of_mem_centralizer148 {A : Subgroup G} (hAF : A ∈ partTwoF G) :
    ∀ x ∈ Subgroup.centralizer (A : Set G), x ^ 3 = 1 → x ∈ A := by
  intro x hx hx3
  exact Sec15.mem_of_mem_partTwoF hAF hx3 fun e he =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hx e he)

theorem cases131_of_sec13Data (h131 : Item131) {A Lb : Subgroup G} {b : G}
    (hD : Sec13Data G A b Lb)
    (hT : Nonempty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.J2) ∨
      IsLThreePi (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb) ∨
      Nonempty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.M22) ∨
      Nonempty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.M12)) :
    (b ∉ Lb ∧ Nat.card (A ⊓ Lb : Subgroup G) = 9 ∧
        Nonempty (lBarA b Lb A ≃* Multiplicative (ZMod 3) × Sec12.lBar b Lb) ∧
        ((IsLThreePi (Lb ⧸ aschbacherSolvableCore 3 Lb) ∧
            (Nonempty (Sec4.autIn Lb A ≃* QuaternionGroup 2) ∨
              Nonempty (Sec4.autIn Lb A ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)))) ∨
          (Nonempty (Lb ⧸ aschbacherSolvableCore 3 Lb ≃* alternatingGroup (Fin 7)) ∧
            Nonempty (Sec4.autIn Lb A ≃* Multiplicative (ZMod 4))) ∨
          (Nonempty (Lb ⧸ aschbacherSolvableCore 3 Lb ≃* CFSG.Blueprint.NativeSporadic.M22) ∧
            Nonempty (Sec4.autIn Lb A ≃* QuaternionGroup 2)))) ∨
      (b ∉ Lb ∧ Nat.card (A ⊓ Lb : Subgroup G) = 9 ∧
        (Nonempty (lBarA b Lb A ≃* Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.M12) ∨
          Nonempty (lBarA b Lb A ≃* Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.J2)) ∧
        Nonempty (Sec4.autIn Lb A ≃* Equiv.Perm (Fin 3))) ∨
      (b ∉ Lb ∧ Sec8.IsZ3PGLThreePi (lBarA b Lb A) ∧
        Nonempty (Sec4.autIn Lb A ≃* Multiplicative (ZMod 3)) ∧
        ∃ x ∈ A, Sec4.InducesTypeOn Lb x 3) := by
  have hbL : b ∉ Lb :=
    not_mem_of_center_eq_bot hD (Sec15.center_eq_bot_of_types hD.mem_thetaComponentsAt hT)
  rcases cases131 h131 sporadicModels131 slTwoCenter hD with h1 | h2 | h3 | h4
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr h3)
  · exact absurd h4.1 hbL

theorem exists_of_kfF (h131 : Item131) (h46 : Sec4.Item4_6) (h41 : Sec4.Item4_1LargePrime)
    (hKF : KF148PointSigF)
    {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (h142 : Concl142 A (lB A)) {Y : Subgroup G} (hY : Y ∈ scriptY A)
    (hYB : ∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B') {B : Subgroup G}
    (hB : IsHyperplane A B) {Q : Subgroup G} (hQ : Q ∈ scriptQZero A (lB A))
    (hQY : Q ≤ Y ⊓ Subgroup.centralizer (B : Set G)) {b : G} (hb : b ∈ B)
    (hbΩ : Subgroup.zpowers b ∈ omegaA A) {Lb : Subgroup G} (hLb : Lb ∈ lA A b)
    (hQLb : Q ≤ Lb ⊔ pPrimeCoreOf 3 (Subgroup.normalizer (Subgroup.zpowers b : Set G)))
    (hQb : ¬ Q ≤ pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer ({b} : Set G))) :
    ∃ K ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({b} : Set G)), K ≤ Lb ∧
      K ≤ sSup {V : Subgroup G | V ≤ K ∧ V ∈ invariantPiSubgroups ⊤ A (piCompl 3) ∧
        V = ⁅V, A⁆} := by
  have hbA : b ∈ A := hB.1 hb
  have hb1 : b ≠ 1 := by
    intro h1
    have h3 := (zpowers_mem_omegaA_iff.mp hbΩ).2.1
    rw [h1, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at h3
    omega
  have hS : Sec14Std G A b Lb := { h with zpowers_mem_omegaA := hbΩ, mem_lA := hLb }
  have hT := (h.chosen136.2 b hbΩ Lb hLb).1
  have h3 : 3 ∣ Nat.card Lb := three_dvd_card_of_types148 hT
  have hCL : Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer (Lb : Set G) :=
    centralizer_le_normalizer_of_three_dvd hS h3
  have hLbC : Lb ≤ Subgroup.centralizer ({b} : Set G) :=
    le_centralizer_of_mem_thetaComponentsAt hLb.1
  set H := Subgroup.normalizer (Subgroup.zpowers b : Set G) with hHdef
  set R := pPrimeCoreOf 3 H with hRdef
  have hCH : Subgroup.centralizer ({b} : Set G) ≤ H := centralizer_singleton_le_normalizer_zpowers b
  have hHR : H ≤ Subgroup.normalizer (R : Set G) := le_normalizer_pPrimeCoreOf 3 H
  have hAb : A ≤ Subgroup.centralizer ({b} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr (h.toSec13Data.commute ha hbA)
  have hRLb : R ≤ Subgroup.normalizer (Lb : Set G) :=
    (pPrimeCoreOf_le 3 H).trans (Res7Point.normalizer_zpowers_le148 h hbΩ hLb h3)
  set W := (Y ⊓ Subgroup.centralizer ({b} : Set G)) ⊓ (Lb ⊔ R) with hWdef
  set C := Y ⊓ Subgroup.centralizer ({b} : Set G) with hCdef
  have hWLR : W ≤ Lb ⊔ R := inf_le_right
  have hWC : W ≤ C := inf_le_left
  have hLbR : A ≤ Subgroup.normalizer ((Lb ⊔ R : Subgroup G) : Set G) :=
    le_normalizer_sup hLb.2.1 ((hAb.trans hCH).trans hHR)
  have hAW : A ≤ Subgroup.normalizer (W : Set G) := fun a ha =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.inf_normalizer_le_normalizer_inf ⟨hY.2 ha, Subgroup.le_normalizer (hAb ha)⟩,
        hLbR ha⟩
  have hCLbR : C ≤ Subgroup.normalizer ((Lb ⊔ R : Subgroup G) : Set G) := fun y hy =>
    le_normalizer_sup (A := C) (fun z hz => hCL hz.2) (fun z hz => hHR (hCH hz.2)) hy
  have hCW : C ≤ Subgroup.normalizer (W : Set G) := fun y hy =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hy, hCLbR hy⟩
  have hQW : Q ≤ W ⊓ Subgroup.centralizer (B : Set G) := by
    have hQb' : Q ≤ Subgroup.centralizer ({b} : Set G) :=
      (hQY.trans inf_le_right).trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hb))
    exact le_inf (le_inf (le_inf (hQY.trans inf_le_left) hQb') hQLb) (hQY.trans inf_le_right)
  have hsig : ∀ H' : Subgroup G, IsHyperplane A H' → ∀ V : Subgroup G,
      V ≤ W ⊓ Subgroup.centralizer (H' : Set G) → V ∈ invariantPiSubgroups ⊤ A (piCompl 3) →
      V = ⁅V, A⁆ → V ≤ pPrimeCoreOf 3 (W ⊓ Subgroup.centralizer (H' : Set G)) := by
    intro H' hH' V hVWH hV hVA
    have hVH : V ≤ H := ((hVWH.trans inf_le_left).trans (hWC.trans inf_le_right)).trans hCH
    have hVq : V ∈ scriptQ A (lB A) :=
      Item148Point.mem_scriptQ_of_le_normalizer148 h142 hbΩ hVH hV
    have hVYH : V ≤ Y ⊓ Subgroup.centralizer (H' : Set G) :=
      le_inf (((hVWH.trans inf_le_left).trans hWC).trans inf_le_left) (hVWH.trans inf_le_right)
    have hVO : V ≤ pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer (H' : Set G)) :=
      (le_deltaZero ⟨hVq, hVA⟩ hVYH).trans (hYB H' hH')
    have hWHY : W ⊓ Subgroup.centralizer (H' : Set G) ≤ Y ⊓ Subgroup.centralizer (H' : Set G) :=
      inf_le_inf_right _ (hWC.trans inf_le_left)
    refine (le_inf hVO hVWH).trans (le_pPrimeCoreOf inf_le_right (fun g hg => ?_) ?_)
    · exact Subgroup.inf_normalizer_le_normalizer_inf
        ⟨le_normalizer_pPrimeCoreOf 3 _ (hWHY hg), Subgroup.le_normalizer hg⟩
    · exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
        (coprime_card_pPrimeCoreOf 3 _)
  have hQW' : ¬ Q ≤ pPrimeCoreOf 3 W := by
    intro hQO
    refine hQb (hQO.trans (le_pPrimeCoreOf ((pPrimeCoreOf_le 3 W).trans hWC)
      (fun g hg => normalizer_le_normalizer_pPrimeCoreOf 3 W (hCW hg))
      (coprime_card_pPrimeCoreOf 3 W)))
  have hD : Sec13Data G A b Lb := { h.toSec13Data with zpowers_mem_omegaA := hbΩ, mem_lA := hLb }
  obtain ⟨K, hK, hKLb, hKgen⟩ := hKF G A Lb R W Q B b h.isE27' hbA hb1 hLbC hLb.2.1 hLb.2.2.1
    (mem_of_mem_centralizer148 h.mem_partTwoF) (cases131_of_sec13Data h131 hD hT) hT
    (Sec13.Res4Proof.exists_isList46 h46 hD) (fun hL3 => l3PointFacts_of_std h131 h46 h41 hS hL3)
    (coprime_card_pPrimeCoreOf 3 H)
    ((hLbC.trans hCH).trans hHR) hRLb ((hAb.trans hCH).trans hHR) hWLR hAW hB hb hQW hQ.1.1 hQ.2
    hsig hQW'
  have hsub : (W.subgroupOf C).IsSubnormal :=
    Subgroup.Normal.isSubnormal ((Subgroup.normal_subgroupOf_iff_le_normalizer hWC).mpr hCW)
  exact ⟨K, Sec15.Proof1423.mem_thetaComponentsIn_of_isSubnormal hK hWC hsub, hKLb, hKgen⟩

end Certs

end Res148BPoint

section Certs

theorem step148PointOmegaGen_of_sigF (h131 : Item131) (h142 : Concl142S14) (h46 : Sec4.Item4_6)
    (h41 : Sec4.Item4_1LargePrime) (hKF : KF148PointSigF) : Step148PointOmegaGen := by
  intro G _ _ A c L h Y hY hs hYB B hB Q hQ hQY b hb hbΩ Lb hLb hQLb hQb
  exact Res148BPoint.exists_of_kfF h131 h46 h41 hKF h (h142 G A c L h) hY hYB hB hQ hQY hb hbΩ hLb
    hQLb hQb

theorem step148PointOmega_of_sigF (h131 : Item131) (hc142 : Concl142S14) (h46 : Sec4.Item4_6)
    (h41 : Sec4.Item4_1LargePrime) (hPS : KF148PointSigF) : Step148PointOmega :=
  step148PointOmega_of_gen hc142 (step148PointOmegaGen_of_sigF h131 hc142 h46 h41 hPS)

end Certs

end CFSG.RankThree.PartTwo.Sec14.Ronan148B
