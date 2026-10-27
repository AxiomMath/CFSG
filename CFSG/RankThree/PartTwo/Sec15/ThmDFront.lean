module

public import CFSG.RankThree.PartTwo.Sec15.ThmDLemma10
public import CFSG.RankThree.PartTwo.Sec15.ThmDReduction
public import CFSG.RankThree.PartTwo.Sec15.ThmDDefs
public import CFSG.RankThree.PartTwo.Sec15.ThmCLemma7
public import CFSG.RankThree.PartTwo.Sec15.Item15Res6Proof159
public import CFSG.RankThree.PartTwo.Sec15.Gagen1511Point

public section

namespace CFSG.RankThree.PartTwo.Sec15.ThmD

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Late CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem commutator_zpowers_le_pPrimeCoreOf_of_dec {A Y Z : Subgroup G} {a : G} (haA : a ∈ A)
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) (hZa : Z ≤ Subgroup.centralizer ({a} : Set G))
    (hdec : Y = pPrimeCoreOf 3 Y ⊔ Z) : ⁅Y, Subgroup.zpowers a⁆ ≤ pPrimeCoreOf 3 Y := by
  set O := pPrimeCoreOf 3 Y with hO
  have hOa : a ∈ Subgroup.normalizer (O : Set G) :=
    normalizer_le_normalizer_pPrimeCoreOf 3 Y (hAY haA)
  have hZY : Z ≤ Y := by
    rw [hdec]
    exact le_sup_right
  have hZN : Z ≤ Subgroup.normalizer (O : Set G) := hZY.trans (le_normalizer_pPrimeCoreOf 3 Y)
  rw [Subgroup.commutator_le]
  intro y hy x hx
  have hxN : x ∈ Subgroup.normalizer (O : Set G) := (Subgroup.zpowers_le.mpr hOa) hx
  have hy' : y ∈ ((O : Set G) * (Z : Set G)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left O Z hZN]
    rw [← hdec]
    exact hy
  obtain ⟨o, ho, z, hz, rfl⟩ := hy'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hzc : Commute a z := (Subgroup.mem_centralizer_singleton_iff.mp (hZa hz)).symm
  have hzx : z * a ^ k = a ^ k * z := ((hzc.zpow_left k).symm).eq
  have h1 : ⁅o * z, a ^ k⁆ = o * (a ^ k * o⁻¹ * (a ^ k)⁻¹) := by
    rw [commutatorElement_def]
    calc o * z * a ^ k * (o * z)⁻¹ * (a ^ k)⁻¹ = o * (z * a ^ k) * z⁻¹ * o⁻¹ * (a ^ k)⁻¹ := by group
      _ = o * (a ^ k * z) * z⁻¹ * o⁻¹ * (a ^ k)⁻¹ := by rw [hzx]
      _ = o * (a ^ k * o⁻¹ * (a ^ k)⁻¹) := by group
  rw [h1]
  exact O.mul_mem ho ((Subgroup.mem_normalizer_iff.mp hxN _).mp (O.inv_mem ho))

section Case148


theorem cases148_split {A : Subgroup G} (h148 : Item148 A (lB A)) (hAab : IsMulCommutative A)
    {Y : Subgroup G} (hY : Y ∈ scriptY4 A (lB A)) (hYΔ : Y = deltaZero A (lB A) Y) :
    (∃ a ∈ A, a ≠ 1 ∧ ⁅Y, Subgroup.zpowers a⁆ ≤ pPrimeCoreOf 3 Y) ∨
    (Nonempty (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y ≃* alternatingGroup (Fin 10)) ∧
      (∃ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A ∧ L' ∈ lA A c' ∧
        Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* alternatingGroup (Fin 7))) ∧
      WStarS4 A) ∨
    (letI := ker148_normal hY.1.2; Case148Five A (lB A) Y) := by
  let := ker148_normal hY.1.2
  have hq := Proof1515.isQuasisimple_quot_pPrimeCore hY
  have hne := Proof1515.pPrimeCore_ne_top_of_mem_scriptY4 hY
  obtain ⟨e0⟩ : Nonempty (↥(img148 A Y (deltaZero A (lB A) Y)) ≃* ↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) := by
    rw [← hYΔ]
    exact nonempty_img148_equiv hY.1.2
  have hqX : IsQuasisimple ↥(img148 A Y (deltaZero A (lB A) Y)) :=
    CFSG.LocalCores.isQuasisimple_of_surjective hq e0.symm.toMonoidHom e0.symm.surjective
      (by rw [(MonoidHom.ker_eq_bot_iff _).mpr e0.symm.injective]; exact bot_le)
  have := Proof1515.nontrivial_alternatingGroup_five
  have := Proof1515.nontrivial_J2
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY.1.2
  have hAA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAab.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  rcases (h148 Y hY.1).2 with h1 | h2 | h3 | h4 | h5 | h6 | h7
  · exfalso
    apply hne
    rw [← hYΔ] at h1
    refine eq_top_iff.mpr fun y _ => ?_
    obtain ⟨z, hz, hzy⟩ := h1 y.2
    rwa [show z = y from Subtype.ext hzy] at hz
  · obtain ⟨c', hc', hdec, -⟩ := h2
    rw [← hYΔ] at hdec
    obtain ⟨hcA, hc3, -⟩ := zpowers_mem_omegaA_iff.mp hc'
    have hc1 : c' ≠ 1 := fun h => by
      rw [h, Subgroup.zpowers_one_eq_bot] at hc3
      simp at hc3
    refine Or.inl ⟨c', hcA, hc1, commutator_zpowers_le_pPrimeCoreOf_of_dec hcA hAY ?_ hdec⟩
    exact Proof1511Point.deltaZero_le_centralizer hAA (lB A) hcA inf_le_right
  · obtain ⟨c', d, L', hc', hL', hJ, hdA, hd1, hdc, hdec, -⟩ := h3
    rw [← hYΔ] at hdec
    refine Or.inl ⟨d, hdA, hd1, commutator_zpowers_le_pPrimeCoreOf_of_dec hdA hAY ?_ hdec⟩
    exact (deltaZero_le _).trans inf_le_right
  · obtain ⟨hφ, hL7, hW⟩ := h4
    obtain ⟨φ⟩ := hφ
    exact Or.inr (Or.inl ⟨⟨e0.symm.trans φ⟩, hL7, hW⟩)
  · exact Or.inr (Or.inr h5)
  · exfalso
    obtain ⟨hφ, -⟩ := h6
    obtain ⟨φ⟩ := hφ
    exact ((Proof1515.isEmpty_mulEquiv_prod_of_isQuasisimple hqX).false φ).elim
  · exact (false_of_case148Seven hAab hY hYΔ h7).elim

theorem not_three_dvd_card_of_isPGroup_two {P : Subgroup G} (hP : IsPGroup 2 P) :
    ¬ 3 ∣ Nat.card P := by
  intro h3
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
  rw [hn] at h3
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
    (Nat.prime_three.dvd_of_dvd_pow h3)
  omega

theorem mem_scriptQ_of_two_subgroup
    (hbot : Item145BotS14) (h148 : Item148R) (h142 : Concl142S14) (h143 : Concl143S14)
    (h146 : Item146S14)
    (hC : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec15R G A c L → ∀ Y ∈ scriptY0 A (lB A), CFSG.Open.pCoreOf 2 Y ∈ scriptQ A (lB A))
    (hP4 : Step148FourKFact) (hD3 : Step153D3) (hD4 : Step153D4) :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec15R G A c L → ∀ Y ∈ scriptY0 A (lB A), ∀ P : Subgroup G, P ≤ Y → IsPGroup 2 P →
        A ≤ Subgroup.normalizer (P : Set G) → P ∈ scriptQ A (lB A) := by
  intro G _ _ A c L hR Y hY0 P hPY hP2 hAP
  have hS := hR.toSec14Std
  have hA : IsE27 A := hS.isE27
  have hAab : IsMulCommutative A := hR.isElemAbelian.1
  have hY4 : Y ∈ scriptY4 A (lB A) := hY0.1
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY4.1.2
  have hbot' : ∃ B, IsHyperplane A B ∧ lB A B = ⊥ := hbot G A c L hS
  have hYΔ : Y = deltaZero A (lB A) Y := rank3II_15_1_lB hA hbot' hY4
  have hV := hC G A c L hR Y hY0
  have hP3 := not_three_dvd_card_of_isPGroup_two hP2
  by_cases hcen : CentralizesQuot A Y
  · obtain ⟨a, haA, ha1, hc⟩ := hcen
    exact mem_scriptQ_of_centralizes hA (h142 G A c L hS) (h143 G A c L hS) (h146 G A c L hS)
      hY4.2.2.1 hAY hV haA ha1 hc hPY hP3 hAP
  · rcases cases148_split (h148 G A c L hR) hAab hY4 hYΔ with
      ⟨a, haA, ha1, hYa⟩ | ⟨h10, hL7, hW⟩ | h5
    · exact (hcen ⟨a, haA, ha1, (ThmC.lemma7_centralizes hY0 haA hYa).1⟩).elim
    · exact hD3 G A c L hR Y hY0 hV hcen h10 (hP4 G A c L hR Y hY0 h10 hL7 hW) P hPY hP2 hAP
    · exact hD4 G A c L hR Y hY0 hYΔ hV h5 P hPY hP2 hAP

theorem step153PushCoreR_of_faithful (hobs : Claim153ObsR)
    (hbot : Item145BotS14) (h148 : Item148R) (h142 : Concl142S14) (h143 : Concl143S14)
    (h146 : Item146S14)
    (hC : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec15R G A c L → ∀ Y ∈ scriptY0 A (lB A), CFSG.Open.pCoreOf 2 Y ∈ scriptQ A (lB A))
    (hP4 : Step148FourKFact) (hD3 : Step153D3) (hD4 : Step153D4) : Step153PushCoreR := by
  refine step153PushCoreR_of_P hobs h146 fun G _ _ A c L hR Y hY S hS hSY => ?_
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T := CFSG.Open.pCoreOf 2 (Y ⊔ S) with hT
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY.prop.1.1.2
  have hAS : A ≤ Subgroup.normalizer (S : Set G) := hS.prop.1.1.1.2.2
  have hAT : A ≤ Subgroup.normalizer (T : Set G) :=
    (Sec14.le_normalizer_sup hAY hAS).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
  have hS2 : IsPGroup 2 S := isPGroup_of_mem_scriptQPi Nat.prime_two hS.prop
  have hST : S ≤ Subgroup.normalizer (T : Set G) :=
    (le_sup_right : S ≤ Y ⊔ S).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hT2 : IsPGroup 2 T := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hTS2 : IsPGroup 2 ↥(S ⊔ T) := IsPGroup.to_sup_of_normal_right' hS2 hT2 hST
  have hP2 : IsPGroup 2 ↥((T ⊔ S) ⊓ Y) := hTS2.to_le (by rw [sup_comm]; exact inf_le_left)
  have hAP : A ≤ Subgroup.normalizer (((T ⊔ S) ⊓ Y : Subgroup G) : Set G) :=
    Late.le_normalizer_inf (Sec14.le_normalizer_sup hAT hAS) hAY
  exact mem_scriptQ_of_two_subgroup hbot h148 h142 h143 h146 hC hP4 hD3 hD4 G A c L hR Y
    (scriptY0Star_subset A (lB A) hY) _ inf_le_right hP2 hAP

end Case148

end CFSG.RankThree.PartTwo.Sec15.ThmD
