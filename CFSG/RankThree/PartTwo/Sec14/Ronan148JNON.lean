module

import CFSG.RankThree.PartTwo.Sec14.Item148HJProofLB
public import CFSG.RankThree.PartTwo.Sec14.Concrete
public import CFSG.RankThree.PartTwo.Sec14.Item148HJRes2ProofInner
public import CFSG.RankThree.PartTwo.Sec14.Ronan148JTools

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148J

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS Ronan148M Main148
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem commutator_mem_centralizer_of_mem_normalizer {X : Type*} [Group X] {z r a : X}
    (hr : r ∈ Subgroup.normalizer (Subgroup.zpowers z : Set X)) (ha : a * z = z * a) :
    ⁅r, a⁆ ∈ Subgroup.centralizer ({z} : Set X) := by
  have hr' : r⁻¹ * z * r⁻¹⁻¹ ∈ Subgroup.zpowers z :=
    (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hr) z).mp (Subgroup.mem_zpowers z)
  rw [inv_inv] at hr'
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hr'
  have ham : a * z ^ m = z ^ m * a := (Commute.zpow_right ha m).eq
  rw [Subgroup.mem_centralizer_singleton_iff, commutatorElement_def]
  have key : r * a * r⁻¹ * a⁻¹ * z * (r * a * r⁻¹ * a⁻¹)⁻¹ = z := by
    have ha' : a⁻¹ * z * a = z := by
      calc a⁻¹ * z * a = a⁻¹ * (z * a) := by group
        _ = a⁻¹ * (a * z) := by rw [ha]
        _ = z := by group
    calc r * a * r⁻¹ * a⁻¹ * z * (r * a * r⁻¹ * a⁻¹)⁻¹
        = r * a * r⁻¹ * (a⁻¹ * z * a) * r * a⁻¹ * r⁻¹ := by group
      _ = r * a * (r⁻¹ * z * r) * a⁻¹ * r⁻¹ := by rw [ha']; group
      _ = r * (a * z ^ m) * a⁻¹ * r⁻¹ := by rw [← hm]; group
      _ = r * (z ^ m * a) * a⁻¹ * r⁻¹ := by rw [ham]
      _ = r * (r⁻¹ * z * r) * r⁻¹ := by rw [hm]; group
      _ = z := by group
  calc r * a * r⁻¹ * a⁻¹ * z = r * a * r⁻¹ * a⁻¹ * z * (r * a * r⁻¹ * a⁻¹)⁻¹ *
        (r * a * r⁻¹ * a⁻¹) := by group
    _ = z * (r * a * r⁻¹ * a⁻¹) := by rw [key]

theorem img148_deltaZero_le_centralizer_of_le_normalizer {A Y : Subgroup G}
    [(ker148 A Y).Normal] {LB : Subgroup G → Subgroup G} (hA : Late.IsE27 A) {d : G}
    (hd : d ∈ A)
    (hN : img148 A Y (deltaZero A LB Y) ≤
      Subgroup.normalizer (Subgroup.zpowers (alpha148 A Y d hd) : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) :
    img148 A Y (deltaZero A LB Y) ≤ Subgroup.centralizer {alpha148 A Y d hd} := by
  have hAE := img148_isE27 (Y := Y) hA
  have hAab : ∀ x ∈ img148 A Y A, ∀ y ∈ img148 A Y A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAE.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  refine img148_deltaZero_le_of_hyperplanes_of_le hA le_rfl fun E _ R hR hRE => ?_
  have hRY : R ≤ Y := hRE.trans inf_le_left
  have hRM : R ≤ Y ⊔ A := hRY.trans le_sup_left
  have hRX : img148 A Y R ≤ img148 A Y (deltaZero A LB Y) := img148_mono (le_deltaZero hR hRY)
  have hReq : img148 A Y R = ⁅img148 A Y R, img148 A Y A⁆ := by
    rw [← HJRes2.img148_commutator_eq hRM le_sup_right, ← hR.2]
  rw [hReq, Subgroup.commutator_le]
  intro r hr a ha
  exact commutator_mem_centralizer_of_mem_normalizer (hN (hRX hr))
    (hAab a ha _ (alpha148_mem_img148 hd))

section Certificates


@[expose] def Step148HJNormalInnerONCent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A), ¬ Group.IsSolvable ↥Y →
    Ind148 A (lB A) Y → ∀ B : Subgroup G, IsHyperplane A B → ¬ YBOne A (lB A) Y B →
    ∀ YB ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer (B : Set G)),
      (Sec4.IsTripleCover (↥YB ⧸ aschbacherSolvableCore 3 ↥YB) (alternatingGroup (Fin 6)) ∨
        Nonempty (↥YB ⧸ aschbacherSolvableCore 3 ↥YB ≃* alternatingGroup (Fin 5))) →
      deltaZero A (lB A) (Y ⊓ Subgroup.centralizer (B : Set G)) ≤
        pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer (B : Set G)) ⊔ YB →
      ∀ (b d : G) (Lb : Subgroup G), IsLBConfig A B b d Lb →
      YB ≤ pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) ⊔ lB A B →
      letI := ker148_normal hY.2
      ∀ J ∈ thetaComponentsIn Y, YB ≤ J → A ≤ Subgroup.normalizer (J : Set G) →
      ∀ Yd ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({d} : Set G)), YB ≤ Yd → Yd ≤ J →
        A ≤ Subgroup.normalizer (Yd : Set G) →
        YdType148 d Yd → d ∈ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y) →
        img148 A Y Yd = img148 A Y J →
        Nonempty (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd ≃* ↥(img148 A Y J)) →
        Sec4.IsTripleCover ↥(img148 A Y J) CFSG.Blueprint.NativeSporadic.ON → d ∈ Yd →
        img148 A Y (deltaZero A (lB A) Y) ≠ img148 A Y J →
        ∀ hdA : d ∈ A,
        img148 A Y (deltaZero A (lB A) Y) ≤ Subgroup.normalizer
          (Subgroup.zpowers (alpha148 A Y d hdA) : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) ∧
        ((Sec4.IsTripleCover ↥(img148 A Y (deltaZero A (lB A) Y))
              CFSG.Blueprint.NativeSporadic.ON ∨
            IsCentralProductA6Covers ↥(img148 A Y (deltaZero A (lB A) Y)) ∨
            IsA6CoverTimesA5 ↥(img148 A Y (deltaZero A (lB A) Y)) ∨
            Nonempty (↥(img148 A Y (deltaZero A (lB A) Y)) ≃*
              alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) ∨
            Nonempty (↥(img148 A Y (deltaZero A (lB A) Y)) ≃* alternatingGroup (Fin 7)) ∨
            (∃ _ : Fact (Nat.Prime 7), Nonempty (↥(img148 A Y (deltaZero A (lB A) Y)) ≃*
              CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1)))) ∨
          Case148Two A (lB A) Y)

theorem step148HJNormalInnerON_of_cent
    (hR : Step148HJNormalInnerONCent) : Step148HJNormalInnerON := by
  intro G _ _ A c L hS Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ Yd hYd
    hYBYd hYdJ hAYd hYdt hdc heq hη hJON hdYd hXJ
  let := ker148_normal hY.2
  have hA : Late.IsE27 A := hS.isE27
  obtain ⟨-, hdB, -, hd1, -⟩ := lbConfig_points hB hA.2 hc
  have hdA : d ∈ A := hB.1 hdB
  have hLb : Lb ∈ lA A b := hc.2.2.1 ▸ Set.mem_singleton Lb
  obtain ⟨hN, htype'⟩ := hR G A c L hS Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ
    hYBJ hAJ Yd hYd hYBYd hYdJ hAYd hYdt hdc heq hη hJON hdYd hXJ hdA
  rcases htype' with h3 | h2
  · exact Or.inr (Or.inl (HJRes2.case148Three_of_le_centralizer hS hY hc.2.1 hLb
      (Item148HJ.j2_of_isLBConfig hc) hdA hd1 hc.2.2.2.2
      (img148_deltaZero_le_centralizer_of_le_normalizer hA hdA hN) h3))
  · exact Or.inl h2

end Certificates

end CFSG.RankThree.PartTwo.Sec14.Ronan148J
