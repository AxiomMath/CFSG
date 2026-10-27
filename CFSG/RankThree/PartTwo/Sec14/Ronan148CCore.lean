module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148MCore
public import CFSG.RankThree.PartTwo.Sec14.Ronan148CLift
import CFSG.RankThree.PartTwo.Sec14.Item148StepQuot

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148C

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14
open CFSG.RankThree.PartTwo.Sec4.Ronan148C
open CFSG.GH74.GLS (pPrimeCoreOf)


section Lift

variable {G : Type} [Group G] [Finite G] {A Y : Subgroup G} [(ker148 A Y).Normal]

theorem img148_le_pPrimeCoreOf_centralizer (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (hA : IsMulCommutative A) {b : G} (hb : b ∈ A) (hb3 : b ^ 3 = 1) {Q : Subgroup G}
    (hQR : Q ≤ pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer ({b} : Set G))) :
    img148 A Y Q ≤ pPrimeCoreOf 3
      (Subgroup.centralizer ({alpha148 A Y b hb} : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set R : Subgroup G := pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer ({b} : Set G)) with hR
  have hRle : R ≤ Y ⊓ Subgroup.centralizer ({b} : Set G) := Sec14.pPrimeCoreOf_le 3 _
  have hRM : R ≤ Y ⊔ A := hRle.trans (inf_le_left.trans le_sup_left)
  refine (img148_mono hQR).trans (Sec14.le_pPrimeCoreOf ?_ ?_ ?_)
  ·
    intro x hx
    obtain ⟨r, hrM, hrR, rfl⟩ := mem_img148_iff.mp hx
    rw [Subgroup.mem_centralizer_singleton_iff, alpha148_eq_mk', ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp (hRle hrR).2
  ·
    intro x hx
    have hxb : alpha148 A Y b hb * x = x * alpha148 A Y b hb :=
      (Subgroup.mem_centralizer_singleton_iff.mp hx).symm
    obtain ⟨y, a, hya, hyC, ha, rfl⟩ := Ronan148M.exists_lift_centralizer148 hAY hA hb hb3 hxb
    have hyN : y ∈ Subgroup.normalizer (R : Set G) := Sec14.le_normalizer_pPrimeCoreOf 3 _ hyC
    have haN : a ∈ Subgroup.normalizer (R : Set G) := by
      refine Sec14.normalizer_le_normalizer_pPrimeCoreOf 3 _ ?_
      have haY := Subgroup.mem_normalizer_iff.mp (hAY ha)
      have haC : a ∈ Subgroup.centralizer ({b} : Set G) :=
        Subgroup.mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (hA.is_comm.comm ⟨b, hb⟩ ⟨a, ha⟩)).symm
      have hCn := Subgroup.mem_normalizer_iff.mp
        (Subgroup.le_normalizer haC : a ∈ Subgroup.normalizer
          (Subgroup.centralizer ({b} : Set G) : Set G))
      rw [Subgroup.mem_normalizer_iff]
      intro z
      simp only [Subgroup.mem_inf]
      exact ⟨fun ⟨h1, h2⟩ => ⟨(haY z).mp h1, (hCn z).mp h2⟩,
        fun ⟨h1, h2⟩ => ⟨(haY z).mpr h1, (hCn z).mpr h2⟩⟩
    have hgN : y * a ∈ Subgroup.normalizer (R : Set G) := Subgroup.mul_mem _ hyN haN
    have key : ∀ g : G, ∀ hg : g ∈ Y ⊔ A, g ∈ Subgroup.normalizer (R : Set G) →
        ∀ z, z ∈ img148 A Y R →
          QuotientGroup.mk' (ker148 A Y) ⟨g, hg⟩ * z *
            (QuotientGroup.mk' (ker148 A Y) ⟨g, hg⟩)⁻¹ ∈ img148 A Y R := by
      intro g hg hgR z hz
      obtain ⟨r, hrM, hrR, rfl⟩ := mem_img148_iff.mp hz
      refine mem_img148_iff.mpr ⟨g * r * g⁻¹, (Y ⊔ A).mul_mem ((Y ⊔ A).mul_mem hg hrM)
        ((Y ⊔ A).inv_mem hg), (Subgroup.mem_normalizer_iff.mp hgR r).mp hrR, ?_⟩
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · exact key (y * a) hya hgN z
    · intro h
      have := key (y * a)⁻¹ ((Y ⊔ A).inv_mem hya) (Subgroup.inv_mem _ hgN) _ h
      have he : QuotientGroup.mk' (ker148 A Y) (⟨(y * a)⁻¹, (Y ⊔ A).inv_mem hya⟩ : ↥(Y ⊔ A)) =
          (QuotientGroup.mk' (ker148 A Y) ⟨y * a, hya⟩)⁻¹ := by
        rw [← map_inv]
        rfl
      rw [he, inv_inv] at this
      simpa [mul_assoc] using this
  · exact Ronan148M.coprime_card_img148 hRM (Sec14.coprime_card_pPrimeCoreOf 3 _)

end Lift

section Certs


theorem core148Layer_of_rowsS
    (R : K148RowsS) : Ronan148M.Core148Layer := by
  intro G _ _ A c L h Y hY hs hYB B hB Q hQ hQY hQb
  letI := ker148_normal hY.2
  have hA : Late.IsE27 A := h.isE27
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hA.1.2
  have hAc : IsMulCommutative A := hA.1.1
  have hY1 : Y ≠ ⊥ := by
    rintro rfl
    exact hs inferInstance
  have hMtop : Y ⊔ A ≠ ⊤ := by
    intro htop
    have : IsSimpleGroup G := h.isSimpleGroup
    have hMN : Y ⊔ A ≤ Subgroup.normalizer (Y : Set G) := sup_le Subgroup.le_normalizer hY.2
    have hYn : Y.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (htop ▸ hMN))
    rcases hYn.eq_bot_or_eq_top with hYb | hYt
    · exact hY1 hYb
    · exact hY.1 hYt
  have hH4 : SectionFourHyp ↥(Y ⊔ A) := h.toTheoremFourHyp.sectionFourHyp hMtop
  have hAH : A ≤ Y ⊔ A := le_sup_right
  have hB9 : Nat.card B = 9 := by
    have := hB.2
    rw [hA.2] at this
    omega
  have hA' : Late.IsE27 (A.subgroupOf (Y ⊔ A)) := by
    refine ⟨⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
    · apply Subtype.ext
      apply Subtype.ext
      change ((x : ↥(Y ⊔ A)) : G) * ((y : ↥(Y ⊔ A)) : G) =
        ((y : ↥(Y ⊔ A)) : G) * ((x : ↥(Y ⊔ A)) : G)
      exact congrArg Subtype.val (hAc.is_comm.comm ⟨_, x.2⟩ ⟨_, y.2⟩)
    · exact Subtype.ext (hA3 _ hx)
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv, hA.2]
  have hBA' : B.subgroupOf (Y ⊔ A) ≤ A.subgroupOf (Y ⊔ A) := Subgroup.subgroupOf_mono _ hB.1
  have hB' : Nat.card (B.subgroupOf (Y ⊔ A)) = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hB.1.trans hAH)).toEquiv, hB9]
  obtain ⟨b₀, hb₀B, hb₀1⟩ : ∃ b ∈ B, b ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hB1 : B = ⊥ := (Subgroup.eq_bot_iff_forall B).mpr hcon
    rw [hB1, Subgroup.card_bot] at hB9
    omega
  have hQC : Q ≤ Subgroup.centralizer ({b₀} : Set G) := by
    intro q hq
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp (hQY hq).2 b₀ hb₀B).symm
  have hQO := Ronan148M.pCore_le_centralizer_img148 hY.2 hAc (hB.1 hb₀B) (hA3 b₀ (hB.1 hb₀B))
    hQC (hQb b₀ hb₀B hb₀1)
  have hAQ0 : A ≤ Subgroup.normalizer (Q : Set G) := (mem_scriptQ_iff.mp hQ.1).2.1
  have hAQ : img148 A Y A ≤ Subgroup.normalizer (img148 A Y Q : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    refine (Subgroup.map_mono ?_).trans (Subgroup.le_normalizer_map _)
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro z
    rw [Subgroup.mem_subgroupOf] at hx
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mem_normalizer_iff.mp (hAQ0 hx) z
  have hQA : img148 A Y Q = ⁅img148 A Y Q, img148 A Y A⁆ := by
    have hQH : Q ≤ Y ⊔ A := fun q hq => Subgroup.mem_sup_left (hQY hq).1
    calc img148 A Y Q = (Q.subgroupOf (Y ⊔ A)).map (QuotientGroup.mk' (ker148 A Y)) := rfl
      _ = (⁅Q, A⁆.subgroupOf (Y ⊔ A)).map (QuotientGroup.mk' (ker148 A Y)) := by rw [← hQ.2]
      _ = ⁅img148 A Y Q, img148 A Y A⁆ := by
          rw [commutator_subgroupOf hQH hAH, Subgroup.map_commutator]
          rfl
  have hQB : ∀ b ∈ B.subgroupOf (Y ⊔ A), b ≠ 1 → img148 A Y Q ≤ pPrimeCoreOf 3
      (Subgroup.centralizer ({QuotientGroup.mk' (ker148 A Y) b} :
        Set (↥(Y ⊔ A) ⧸ ker148 A Y))) := by
    intro b hb hb1
    rw [Subgroup.mem_subgroupOf] at hb
    have hbA : (b : G) ∈ A := hB.1 hb
    have hb1' : (b : G) ≠ 1 := fun h1 => hb1 (Subtype.ext h1)
    have hα : QuotientGroup.mk' (ker148 A Y) b = alpha148 A Y (b : G) hbA := rfl
    rw [hα]
    exact img148_le_pPrimeCoreOf_centralizer hY.2 hAc hbA (hA3 _ hbA) (hQb _ hb hb1')
  exact layer_le_centralizer_of_sectionFourHyp R hH4 (ker148 A Y)
    (Ronan148M.ker148_eq_pPrimeCore_sup hY.2 hA3) hA' hBA' hB' hAQ hQA hQB hQO

theorem step148Core_of_rowsS
    (R : K148RowsS) : Step148Core :=
  Ronan148M.step148Core_of_layer (core148Layer_of_rowsS R)

end Certs

end CFSG.RankThree.PartTwo.Sec14.Ronan148C
