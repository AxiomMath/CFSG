module

public import CFSG.RankThree.PartTwo.Sec17.RouteForms
import CFSG.RankThree.PartTwo.Sec14.Item1413Res3ProofTools
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear
public import CFSG.RankThree.PartTwo.Sec14.Concl143Std
public import CFSG.RankThree.PartTwo.Sec14.Item148HJRes2ProofImg
public import CFSG.RankThree.PartTwo.Sec14.Item148StepQuot

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148J

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

theorem commutator_le_img148_deltaZero_of_point (h142 : Concl142S14) {A L : Subgroup G} {c : G}
    (hS : Sec14Std G A c L) {Y : Subgroup G} (hY : Y ∈ scriptY A) {b : G}
    (hbΩ : Subgroup.zpowers b ∈ omegaA A) :
    letI := ker148_normal hY.2
    ∀ V : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y),
      V ≤ img148 A Y (Y ⊓ Subgroup.centralizer ({b} : Set G)) → ¬ 3 ∣ Nat.card V →
      img148 A Y A ≤ Subgroup.normalizer (V : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) →
      ⁅V, img148 A Y A⁆ ≤ img148 A Y (deltaZero A (lB A) Y) := by
  have hN : (ker148 A Y).Normal := ker148_normal hY.2
  intro V hVb hV3 hAV
  have hA : Late.IsE27 A := hS.isE27'
  have hA3' : IsPGroup 3 A := IsPGroup.of_card (n := 3) (by rw [hA.2]; norm_num)
  have hAab : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a := fun a ha a' ha' =>
    hS.toSec13Data.commute ha ha'
  have hbA : b ∈ A := (Sec13.zpowers_mem_omegaA_iff.mp hbΩ).1
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY.2
  obtain ⟨W, hW⟩ : ∃ W : Subgroup G, W =
      ((V.comap (QuotientGroup.mk' (ker148 A Y))).map (Y ⊔ A).subtype) ⊓
        (Y ⊓ Subgroup.centralizer ({b} : Set G)) := ⟨_, rfl⟩
  have hWsub : W ≤ Y ⊓ Subgroup.centralizer ({b} : Set G) := by
    rw [hW]
    exact inf_le_right
  have hWY : W ≤ Y := hWsub.trans inf_le_left
  have hWM : W ≤ Y ⊔ A := hWY.trans le_sup_left
  have hWmem : ∀ {x : G} (hx : x ∈ Y), x ∈ W ↔
      (QuotientGroup.mk' (ker148 A Y) ⟨x, Subgroup.mem_sup_left hx⟩ ∈ V ∧
        x ∈ Subgroup.centralizer ({b} : Set G)) := by
    intro x hx
    rw [hW, Subgroup.mem_inf, Subgroup.mem_inf]
    constructor
    · rintro ⟨hM, -, hC⟩
      obtain ⟨m, hm, hmx⟩ := Subgroup.mem_map.mp hM
      have hm' : m = ⟨x, Subgroup.mem_sup_left hx⟩ := Subtype.ext hmx
      subst hm'
      exact ⟨hm, hC⟩
    · rintro ⟨hV', hC⟩
      exact ⟨Subgroup.mem_map.mpr ⟨⟨x, Subgroup.mem_sup_left hx⟩, hV', rfl⟩, hx, hC⟩
  have hWV : img148 A Y W = V := by
    refine le_antisymm ?_ ?_
    · intro y hy
      obtain ⟨g, hgM, hgW, rfl⟩ := mem_img148_iff.mp hy
      exact ((hWmem (hWY hgW)).mp hgW).1
    · intro v hv
      obtain ⟨g, hgM, hgC, rfl⟩ := mem_img148_iff.mp (hVb hv)
      exact mem_img148_iff.mpr ⟨g, hgM, (hWmem hgC.1).mpr ⟨hv, hgC.2⟩, rfl⟩
  have hconj : ∀ a ∈ A, ∀ w ∈ W, a * w * a⁻¹ ∈ W := by
    intro a ha w hw
    have hwY : w ∈ Y := hWY hw
    have hcw : Commute w b := Subgroup.mem_centralizer_singleton_iff.mp (hWsub hw).2
    have hcomm : Commute a b := hAab a ha b hbA
    have hawY : a * w * a⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp (hAY ha) w).mp hwY
    have hcab : Commute (a * w * a⁻¹) b := (hcomm.mul_left hcw).mul_left hcomm.inv_left
    have hkey : QuotientGroup.mk' (ker148 A Y) ⟨a * w * a⁻¹, Subgroup.mem_sup_left hawY⟩ =
        alpha148 A Y a ha * QuotientGroup.mk' (ker148 A Y) ⟨w, Subgroup.mem_sup_left hwY⟩ *
          (alpha148 A Y a ha)⁻¹ := by
      rw [alpha148_eq_mk', ← map_inv, ← map_mul, ← map_mul] <;> rfl
    have hwV : QuotientGroup.mk' (ker148 A Y) ⟨w, Subgroup.mem_sup_left hwY⟩ ∈ V :=
      ((hWmem hwY).mp hw).1
    have hVconj :
        QuotientGroup.mk' (ker148 A Y) ⟨a * w * a⁻¹, Subgroup.mem_sup_left hawY⟩ ∈ V := by
      rw [hkey]
      exact (Subgroup.mem_normalizer_iff.mp (hAV (alpha148_mem_img148 (Y := Y) ha))
        (QuotientGroup.mk' (ker148 A Y) ⟨w, Subgroup.mem_sup_left hwY⟩)).mp hwV
    exact (hWmem hawY).mpr ⟨hVconj, Subgroup.mem_centralizer_singleton_iff.mpr hcab⟩
  have hAW : A ≤ Subgroup.normalizer (W : Set G) := fun a ha => by
    rw [Subgroup.mem_normalizer_iff]
    intro w
    refine ⟨hconj a ha w, fun hw => ?_⟩
    have h2 := hconj a⁻¹ (A.inv_mem ha) (a * w * a⁻¹) hw
    have e : a⁻¹ * (a * w * a⁻¹) * a⁻¹⁻¹ = w := by group
    rw [e] at h2
    exact h2
  have hWN : W ≤ Subgroup.normalizer (Subgroup.zpowers b : Set G) := by
    have hCN : Subgroup.centralizer ({b} : Set G) ≤
        Subgroup.normalizer (Subgroup.zpowers b : Set G) := by
      refine le_trans (fun x hx => ?_) (Subgroup.centralizer_le_normalizer _)
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      exact hx
    exact (hWsub.trans inf_le_right).trans hCN
  have hW3 : ¬ 3 ∣ Nat.card W := by
    intro h3
    obtain ⟨x, hx3⟩ := exists_prime_orderOf_dvd_card' (G := ↥W) 3 h3
    have hxW : (x : G) ∈ W := x.2
    have hxY : (x : G) ∈ Y := hWY hxW
    have hxo : orderOf (x : G) = 3 := (Subgroup.orderOf_coe x).trans hx3
    have hv : QuotientGroup.mk' (ker148 A Y) ⟨(x : G), Subgroup.mem_sup_left hxY⟩ ∈ V :=
      ((hWmem hxY).mp hxW).1
    have hg3 : orderOf (⟨(x : G), Subgroup.mem_sup_left hxY⟩ : ↥(Y ⊔ A)) = 3 :=
      (Subgroup.orderOf_coe (⟨(x : G), Subgroup.mem_sup_left hxY⟩ : ↥(Y ⊔ A))).symm.trans hxo
    have hπ3 : orderOf (QuotientGroup.mk' (ker148 A Y) ⟨(x : G), Subgroup.mem_sup_left hxY⟩)
        ∣ 3 :=
      (orderOf_map_dvd (QuotientGroup.mk' (ker148 A Y)) _).trans (dvd_of_eq hg3)
    have hπV : orderOf (QuotientGroup.mk' (ker148 A Y) ⟨(x : G), Subgroup.mem_sup_left hxY⟩)
        ∣ Nat.card V :=
      Subgroup.orderOf_dvd_natCard V hv
    have hcop : Nat.gcd 3 (Nat.card V) = 1 :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hV3
    have h1 : orderOf (QuotientGroup.mk' (ker148 A Y) ⟨(x : G), Subgroup.mem_sup_left hxY⟩)
        ∣ 1 := by
      have := Nat.dvd_gcd hπ3 hπV
      rwa [hcop] at this
    have hone : QuotientGroup.mk' (ker148 A Y) ⟨(x : G), Subgroup.mem_sup_left hxY⟩ = 1 :=
      orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1)
    have hxP : (x : G) ∈ pPrimeCoreOf 3 Y := mk'_ker148_eq_one_iff.mp hone
    have h3P : 3 ∣ Nat.card (pPrimeCoreOf 3 Y) := by
      have := Subgroup.orderOf_dvd_natCard (pPrimeCoreOf 3 Y) hxP
      rwa [hxo] at this
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (coprime_card_pPrimeCoreOf 3 Y) h3P
  have hWQ : W ∈ scriptQ A (lB A) :=
    Proof1413Res3.mem_scriptQ_of_le_normalizer h142 hS hbΩ hWN hAW hW3
  have hcommW : ⁅W, A⁆ ≤ W := Subgroup.le_normalizer_iff_commutator_le_left.mp hAW
  have hQ : ⁅W, A⁆ ∈ scriptQ A (lB A) :=
    mem_scriptQ_of_le hWQ hcommW (Subgroup.normalizer_commutator_ge_right W A)
  have hcop3 : Nat.Coprime 3 (Nat.card W) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hW3
  have hidem : ⁅⁅W, A⁆, A⁆ = ⁅W, A⁆ :=
    CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_idempotent 3 Nat.prime_three
      A W hA3' hAW hcop3
  have hQ0 : ⁅W, A⁆ ∈ scriptQZero A (lB A) := ⟨hQ, hidem.symm⟩
  have hQle : ⁅W, A⁆ ≤ deltaZero A (lB A) Y := le_deltaZero hQ0 (hcommW.trans hWY)
  calc ⁅V, img148 A Y A⁆ = ⁅img148 A Y W, img148 A Y A⁆ := by rw [hWV]
    _ = img148 A Y ⁅W, A⁆ :=
      (HJRes2.img148_commutator_eq hWM (le_sup_right : A ≤ Y ⊔ A)).symm
    _ ≤ img148 A Y (deltaZero A (lB A) Y) := img148_mono hQle

end CFSG.RankThree.PartTwo.Sec14.Ronan148J
