module

public import CFSG.RankThree.PartTwo.Sec14.Item1411Chain
public import CFSG.GroupTheory.HallHigmanPiCore
import CFSG.RankThree.PartTwo.Sec4.StepsBender
import CFSG.RankThree.PartTwo.Sec15.HypR
import CFSG.RankThree.PartTwo.Sec14.Item14Tools

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Late CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise

theorem isPSolvable_of_isSolvable {X : Type*} [Group X] {p : ℕ} (hp : p.Prime)
    (hX : Group.IsSolvable X) : CFSG.HallHigman.IsPSolvable p X := by
  intro H _ T _ hs
  have := hX
  have := hs
  have hcomm : ∀ a b : ↥H ⧸ T, a * b = b * a :=
    (IsSimpleGroup.comm_iff_isSolvable).mpr inferInstance
  have : IsMulCommutative (↥H ⧸ T) := ⟨⟨hcomm⟩⟩
  have hq : (Nat.card (↥H ⧸ T)).Prime := Group.is_simple_iff_prime_card.mp hs
  change Nat.card (↥H ⧸ T) = p ∨ Nat.Coprime p (Nat.card (↥H ⧸ T))
  by_cases h : Nat.card (↥H ⧸ T) = p
  · exact Or.inl h
  · exact Or.inr ((Nat.coprime_primes hp hq).mpr (Ne.symm h))

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isSolvable_sup_of_le_normalizer {Y A : Subgroup G} (hYs : Group.IsSolvable ↥Y)
    (hAc : IsMulCommutative A) (hAY : A ≤ Subgroup.normalizer (Y : Set G)) :
    Group.IsSolvable ↥(Y ⊔ A) := by
  have hYX : Y ≤ Y ⊔ A := le_sup_left
  have hN : (Y.subgroupOf (Y ⊔ A)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYX).mpr (sup_le Subgroup.le_normalizer hAY)
  have := hYs
  have : Group.IsSolvable ↥(Y.subgroupOf (Y ⊔ A)) :=
    Group.isSolvable_of_isSolvable_injective (f := (Subgroup.subgroupOfEquivOfLe hYX).toMonoidHom)
      (MulEquiv.injective _)
  have hrep : ∀ x : ↥(Y ⊔ A), ∃ (a : G) (ha : a ∈ A),
      (QuotientGroup.mk x : ↥(Y ⊔ A) ⧸ Y.subgroupOf (Y ⊔ A)) =
        QuotientGroup.mk ⟨a, Subgroup.mem_sup_right ha⟩ := by
    intro x
    have hx : (x : G) ∈ ((Y : Set G) * (A : Set G)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left Y A hAY]
      exact x.2
    obtain ⟨y, hy, a, ha, hya⟩ := hx
    refine ⟨a, ha, ?_⟩
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h1 : a⁻¹ * y⁻¹ * a⁻¹⁻¹ ∈ Y :=
      (Subgroup.mem_normalizer_iff.mp (hAY (inv_mem ha)) y⁻¹).mp (inv_mem hy)
    have h2 : ((x⁻¹ * ⟨a, Subgroup.mem_sup_right ha⟩ : ↥(Y ⊔ A)) : G) = a⁻¹ * y⁻¹ * a⁻¹⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, ← hya, inv_inv]
      group
    rw [h2]
    exact h1
  have : Group.IsSolvable (↥(Y ⊔ A) ⧸ Y.subgroupOf (Y ⊔ A)) := by
    apply Group.isSolvable_of_comm
    intro q₁ q₂
    obtain ⟨x₁, rfl⟩ := QuotientGroup.mk_surjective q₁
    obtain ⟨x₂, rfl⟩ := QuotientGroup.mk_surjective q₂
    obtain ⟨a₁, ha₁, h₁⟩ := hrep x₁
    obtain ⟨a₂, ha₂, h₂⟩ := hrep x₂
    rw [h₁, h₂, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    have hc : a₁ * a₂ = a₂ * a₁ := congrArg Subtype.val (hAc.is_comm.comm ⟨a₁, ha₁⟩ ⟨a₂, ha₂⟩)
    congr 1
    exact Subtype.ext hc
  exact Group.isSolvable_of_subgroup_quotient (Y.subgroupOf (Y ⊔ A))

theorem le_pPrimeCoreOf_of_isSolvable {A Y Q : Subgroup G}
    (hAe : CFSG.Assembly.IsElemAbelian 3 A)
    (hA3 : ∀ y ∈ Subgroup.centralizer (A : Set G), y ^ 3 = 1 → y ∈ A)
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) (hYs : Group.IsSolvable ↥Y) (hQY : Q ≤ Y)
    (hQ3 : ¬ 3 ∣ Nat.card Q) (hAQ : A ≤ Subgroup.normalizer (Q : Set G)) :
    Q ≤ pPrimeCoreOf 3 Y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set X := Y ⊔ A with hX
  have hXs : Group.IsSolvable ↥X := isSolvable_sup_of_le_normalizer hYs hAe.1 hAY
  have hAX : A ≤ X := le_sup_right
  have hQX : Q ≤ X := hQY.trans le_sup_left
  have hA' : CFSG.Assembly.IsElemAbelian 3 (A.subgroupOf X) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · have hc : ((a : X) : G) * ((b : X) : G) = ((b : X) : G) * ((a : X) : G) :=
        congrArg Subtype.val (hAe.1.is_comm.comm ⟨((a : X) : G), a.2⟩ ⟨((b : X) : G), b.2⟩)
      exact Subtype.ext (Subtype.ext hc)
    · apply Subtype.ext
      simpa using hAe.2 (x : G) hx
  have hA3' : ∀ y ∈ Subgroup.centralizer (A.subgroupOf X : Set ↥X), y ^ 3 = 1 →
      y ∈ A.subgroupOf X := by
    intro y hy hy3
    rw [Subgroup.mem_subgroupOf]
    refine hA3 (y : G) ?_ (by simpa using congrArg Subtype.val hy3)
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have h := Subgroup.mem_centralizer_iff.mp hy ⟨a, hAX ha⟩ (Subgroup.mem_subgroupOf.mpr ha)
    exact congrArg Subtype.val h
  have hQ3' : ¬ 3 ∣ Nat.card (Q.subgroupOf X) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQX).toEquiv]
  have hAQ' : A.subgroupOf X ≤ Subgroup.normalizer (Q.subgroupOf X : Set ↥X) := by
    intro a ha
    rw [Subgroup.mem_subgroupOf] at ha
    rw [Subgroup.mem_normalizer_iff]
    intro z
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simpa using Subgroup.mem_normalizer_iff.mp (hAQ ha) (z : G)
  have hle : Q.subgroupOf X ≤ CFSG.pPrimeCore 3 ↥X :=
    Sec4.le_pPrimeCore_of_bender (isPSolvable_of_isSolvable Nat.prime_three hXs) hA' hA3' hQ3'
      hAQ'
  set R := (CFSG.pPrimeCore 3 ↥X).map X.subtype with hR
  have hQR : Q ≤ R := by
    intro q hq
    exact ⟨⟨q, hQX hq⟩, hle (Subgroup.mem_subgroupOf.mpr hq), rfl⟩
  have hcop : Nat.Coprime 3 (Nat.card R) := by
    rw [hR, Subgroup.card_map_of_injective X.subtype_injective]
    exact CFSG.pPrimeCore_coprime_card
  have hA3g : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hAe.2 g g.2)⟩
  have hRY : R ≤ Y := by
    rintro _ ⟨z, hz, rfl⟩
    have hord : Nat.Coprime (orderOf ((z : X) : G)) 3 := by
      rw [Subgroup.orderOf_coe]
      have h1 : orderOf (⟨z, hz⟩ : ↥(CFSG.pPrimeCore 3 ↥X)) ∣
          Nat.card ↥(CFSG.pPrimeCore 3 ↥X) := orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk] at h1
      exact (Nat.Coprime.coprime_dvd_left h1
        (CFSG.pPrimeCore_coprime_card (G := ↥X) (p := 3)).symm)
    exact mem_left_of_coprime_of_isPGroup Nat.prime_three hAY hA3g z.2 hord
  have hYR : Y ≤ Subgroup.normalizer (R : Set G) := by
    have h := Subgroup.le_normalizer_map (H := CFSG.pPrimeCore 3 ↥X) X.subtype
    rw [Subgroup.normalizer_eq_top_iff.mpr CFSG.pPrimeCore_normal, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h
    exact le_sup_left.trans h
  exact hQR.trans (le_pPrimeCoreOf hRY hYR hcop)

theorem item148Solvable_of_mem_partTwoF {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    (hAF : A ∈ partTwoF G) : Item148Solvable A LB := by
  intro Y hY hYs
  refine sSup_le fun Q hQ => ?_
  have hQ3 : ¬ 3 ∣ Nat.card Q :=
    (isPiSubgroup_piCompl_iff Nat.prime_three Q).mp hQ.1.1.1.2.1
  refine le_pPrimeCoreOf_of_isSolvable hAF.1 (fun y hy hy3 => ?_) hY.2 hYs hQ.2 hQ3
    hQ.1.1.1.2.2
  exact Sec15.mem_of_mem_partTwoF hAF hy3 fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hy a ha)

variable {A L : Subgroup G} {c : G}

theorem transOn_of_isSolvable_std (h : Sec14Std G A c L) (h146 : Item146 A (lB A))
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥) {Y : Subgroup G}
    (hYΔ : Y = delta A (lB A) Y) (hY : Y ∈ scriptY A) (hYs : Group.IsSolvable ↥Y) :
    TransOn A (lB A) (xA A) Y :=
  transOn_of_isSolvable h (item148Solvable_of_mem_partTwoF h.mem_partTwoF) h146 hbot hYΔ hY hYs

theorem rank3II_14_15_std (h : Sec14Std G A c L) (h146 : Item146 A (lB A))
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥)
    (hfail : ∀ Y : Subgroup G, Y = delta A (lB A) Y → Y ∈ scriptY A →
      CFSG.Open.pCoreOf 2 Y ≠ ⊥ → inSubgroup perfectResidual Y ≠ ⊥ →
        TransOn A (lB A) (xA A) Y)
    {S T : Subgroup G} (hS : S ∈ scriptQPiStar A (lB A) ⊤ (piOf 2))
    (hT : T ∈ scriptQPiStar A (lB A) ⊤ (piOf 2)) (hST : ¬ IsConjIn (xA A) S T) : S ⊓ T = ⊥ :=
  rank3II_14_15_of h hfail (fun _ hYΔ hY hYs => transOn_of_isSolvable_std h h146 hbot hYΔ hY hYs)
    hS hT hST

theorem rank3II_14_16_false_std (h : Sec14Std G A c L) (h146 : Item146 A (lB A))
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥)
    (hfail : ∀ Y : Subgroup G, Y = delta A (lB A) Y → Y ∈ scriptY A →
      CFSG.Open.pCoreOf 2 Y ≠ ⊥ → inSubgroup perfectResidual Y ≠ ⊥ →
        TransOn A (lB A) (xA A) Y)
    {Y U₁ U₂ : Subgroup G} (hU₁ : U₁ ∈ scriptQPiStar A (lB A) Y (piOf 2))
    (hU₂ : U₂ ∈ scriptQPiStar A (lB A) Y (piOf 2)) (hne : U₁ ≠ U₂) (hmeet : U₁ ⊓ U₂ ≠ ⊥)
    (hXU : xA A ≤ Subgroup.normalizer (U₂ : Set G)) : False :=
  rank3II_14_16_false h hfail
    (fun _ hYΔ hY hYs => transOn_of_isSolvable_std h h146 hbot hYΔ hY hYs) hU₁ hU₂ hne hmeet hXU

omit [Finite G] in
theorem transOn_mono {LB : Subgroup G → Subgroup G} {V V' Y : Subgroup G} (hVV' : V ≤ V')
    (h : TransOn A LB V Y) : TransOn A LB V' Y :=
  fun S hS T hT => (h S hS T hT).mono (inf_le_inf_right _ hVV')

omit [Finite G] in
theorem transOn_of_delta {LB : Subgroup G → Subgroup G} {V Y : Subgroup G}
    (h : TransOn A LB V (delta A LB Y)) : TransOn A LB V Y := by
  intro S hS T hT
  rw [← scriptQPiStar_delta (A := A) (LB := LB) Y] at hS hT
  exact (h S hS T hT).mono (inf_le_inf_left _ (delta_le Y))

theorem claim1411Local_of_nonsolvable (h : Sec14Std G A c L) (h146 : Item146 A (lB A))
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥)
    (hW : ∀ Y : Subgroup G, Y = delta A (lB A) Y → Y ∈ scriptY A → ¬ Group.IsSolvable ↥Y →
      TransOn A (lB A) (Subgroup.normalizer (A : Set G)) Y)
    (hX : (∀ a : G, Subgroup.zpowers a ∈ omegaA A →
        TransOn A (lB A) (xA A) (Subgroup.centralizer ({a} : Set G))) →
      ∀ Y : Subgroup G, Y = delta A (lB A) Y → Y ∈ scriptY A → ¬ Group.IsSolvable ↥Y →
        TransOn A (lB A) (xA A) Y) :
    Claim1411Local A (lB A) := by
  have hXW : xA A ≤ Subgroup.normalizer (A : Set G) :=
    (pPrimeCoreOf_le 3 _).trans (Subgroup.centralizer_le_normalizer _)
  have hΔ : ∀ Y ∈ scriptY A, delta A (lB A) Y ∈ scriptY A ∧
      delta A (lB A) Y = delta A (lB A) (delta A (lB A) Y) := by
    intro Y hY
    refine ⟨⟨fun htop => hY.1 (top_le_iff.mp ?_), le_normalizer_sSup fun Q hQ => hQ.1.1.2.2⟩,
      (delta_delta Y).symm⟩
    rw [← htop]
    exact delta_le Y
  refine ⟨fun Y hY => transOn_of_delta ?_, fun hloc Y hY => transOn_of_delta ?_⟩
  · obtain ⟨hY', hYΔ⟩ := hΔ Y hY
    by_cases hs : Group.IsSolvable ↥(delta A (lB A) Y)
    · exact transOn_mono hXW (transOn_of_isSolvable_std h h146 hbot hYΔ hY' hs)
    · exact hW _ hYΔ hY' hs
  · obtain ⟨hY', hYΔ⟩ := hΔ Y hY
    by_cases hs : Group.IsSolvable ↥(delta A (lB A) Y)
    · exact transOn_of_isSolvable_std h h146 hbot hYΔ hY' hs
    · exact hX hloc _ hYΔ hY' hs

end CFSG.RankThree.PartTwo.Sec14
