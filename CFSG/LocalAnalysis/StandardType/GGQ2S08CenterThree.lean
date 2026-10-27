module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigInputs
public import CFSG.LocalAnalysis.StandardType.GGTableBBstar

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggQ2s08_center_three_mem {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J) (c : ↥L)
    (hc : c ∈ Subgroup.center ↥L) (h3 : c ^ 3 = 1) : (c : G) ∈ Subgroup.zpowers x := by
  obtain ⟨hp, hBs, hxB, hLx, -⟩ := hS.1.1.tableB_facts
  have hSS : LargeEvenSStar 3 B x L := hS.1.1.1.2.2.2.2.2.2.1
  have hx3 : x ^ 3 = 1 := hBs.2 x hxB
  have hz3 : (c : G) ^ 3 = 1 := by
    have := congrArg (fun y : ↥L => (y : G)) h3
    simpa using this
  have hcx : (c : G) * x = x * (c : G) :=
    Subgroup.mem_centralizer_singleton_iff.mp (hLx c.2)
  have hcomm : ∀ a ∈ ({x, (c : G)} : Set G), ∀ b ∈ ({x, (c : G)} : Set G), a * b = b * a := by
    intro a ha b hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · simp only [Set.mem_singleton_iff] at hb; subst hb; exact hcx.symm
    · simp only [Set.mem_singleton_iff] at ha; subst ha; exact hcx
    · simp only [Set.mem_singleton_iff] at ha hb; subst ha; subst hb; rfl
  let E : Subgroup G := Subgroup.closure ({x, (c : G)} : Set G)
  have hP1 : ∀ a ∈ E, ∀ y ∈ ({x, (c : G)} : Set G), a * y = y * a := by
    intro a ha
    induction ha using Subgroup.closure_induction with
    | mem z hz => intro y hy; exact hcomm z hz y hy
    | one => intro y hy; simp
    | mul a b ha hb iha ihb =>
      intro y hy
      rw [mul_assoc, ihb y hy, ← mul_assoc, iha y hy, mul_assoc]
    | inv a ha iha =>
      intro y hy
      have h := iha y hy
      calc a⁻¹ * y = a⁻¹ * (y * a) * a⁻¹ := by group
        _ = a⁻¹ * (a * y) * a⁻¹ := by rw [h]
        _ = y * a⁻¹ := by group
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    induction hb using Subgroup.closure_induction with
    | mem z hz => exact hP1 a ha z hz
    | one => simp
    | mul b1 b2 hb1 hb2 ih1 ih2 =>
      rw [← mul_assoc, ih1, mul_assoc, ih2, mul_assoc]
    | inv b hb ihb =>
      have h := ihb
      calc a * b⁻¹ = b⁻¹ * (b * a) * b⁻¹ := by group
        _ = b⁻¹ * (a * b) * b⁻¹ := by rw [← h]
        _ = b⁻¹ * a := by group
  have hE3 : ∀ a ∈ E, a ^ 3 = 1 := by
    intro a ha
    induction ha using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with rfl | hy
      · exact hx3
      · simp only [Set.mem_singleton_iff] at hy; subst hy; exact hz3
    | one => exact one_pow _
    | mul a b ha hb iha ihb =>
      have hab : Commute a b := hEc a ha b hb
      rw [hab.mul_pow, iha, ihb, one_mul]
    | inv a ha iha => rw [inv_pow, iha, inv_one]
  haveI : IsMulCommutative ↥E := ⟨⟨fun a b => Subtype.ext (hEc a.1 a.2 b.1 b.2)⟩⟩
  have hEel : CFSG.Open.IsElemAbelian 3 E := ⟨this, hE3⟩
  have hxE : x ∈ E := Subgroup.subset_closure (Set.mem_insert _ _)
  have hcE : (c : G) ∈ E := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hx1 : x ≠ 1 := hSS.2.2.1
  have hcyc := hSS.2.2.2.2
  have hcentL : (c : G) ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have := congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨l, hl⟩)
    simpa using this
  have hEL := inf_centralizer_eq_zpowers_of_elemAbelian hp hEel hxE hx1 hLx hcyc
  rw [← hEL]
  exact ⟨hcE, hcentL⟩

end CFSG.StandardType

end
