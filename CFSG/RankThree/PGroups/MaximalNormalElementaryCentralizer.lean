module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.Torsion
public import CFSG.LocalAnalysis.SectionRank.SQT

public section

namespace CFSG.RankThree.PGroups

open Subgroup
open scoped commutatorElement

variable {P : Type*} [Group P] {p : ℕ}

theorem closure_normal_of_conj_mem {s : Set P} (hs : ∀ x ∈ s, ∀ g : P, g * x * g⁻¹ ∈ s) :
    (closure s).Normal := by
  constructor
  intro n hn g
  induction hn using closure_induction with
  | mem x hx => exact subset_closure (hs x hx g)
  | one => rw [mul_one, mul_inv_cancel]; exact one_mem _
  | mul a b _ _ ha hb =>
    have h := mul_mem ha hb
    rwa [show g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ by group] at h
  | inv a _ ha =>
    have h := inv_mem ha
    rwa [show (g * a * g⁻¹)⁻¹ = g * a⁻¹ * g⁻¹ by group] at h

theorem closure_pow_eq_one_eq_top {s : Set P} (hs : ∀ x ∈ s, x ^ p = 1) :
    closure {x : closure s | x ^ p = 1} = ⊤ := by
  rw [eq_top_iff, ← closure_closure_coe_preimage]
  exact closure_mono fun x hx => Subtype.ext (by rw [coe_pow, hs _ hx, coe_one])

variable [Finite P]

theorem maximal_normal_elementary_centralizer_torsion (hp : p.Prime) (hp2 : p ≠ 2)
    (hP : IsPGroup p P) {E : Subgroup P} [E.Normal] (hE : IsElementaryAbelian p E)
    (hmax : ∀ B : Subgroup P, B.Normal → IsElementaryAbelian p B → E ≤ B → B = E) :
    (omega₁ (centralizer (E : Set P)) (p := p)).map (centralizer (E : Set P)).subtype = E ∧
      ∀ x ∈ centralizer (E : Set P), x ^ p = 1 → x ∈ E := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hEc, hEp⟩ := (SectionRank.isElementaryAbelian_iff_isElemAbelian p E).1 hE
  have hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : E) ⟨y, hy⟩)
  have hmax' : ∀ B : Subgroup P, B.Normal → (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
      (∀ x ∈ B, x ^ p = 1) → E ≤ B → B = E := fun B hBn hBab hBp hEB =>
    hmax B hBn ((SectionRank.isElementaryAbelian_iff_isElemAbelian p B).2
      ⟨⟨⟨fun a b => Subtype.ext (hBab a a.2 b b.2)⟩⟩, hBp⟩) hEB
  let S : Set (Subgroup P) := {B | B.Normal ∧ (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) ∧ E ≤ B}
  obtain ⟨A, hAmax⟩ := S.toFinite.exists_maximal ⟨E, inferInstance, hEab, le_rfl⟩
  obtain ⟨hAn, hAab, hEA⟩ := hAmax.prop
  have hcenA : centralizer (A : Set P) = A :=
    SectionRank.Ccomm.maximal_abelian_normal_self_centralizing hP hAab fun B hBn hBab hAB =>
      le_antisymm (hAmax.2 ⟨hBn, hBab, hEA.trans hAB⟩ hAB) hAB
  let Ap : Subgroup P :=
    { carrier := {a | a ∈ A ∧ a ^ p = 1}
      mul_mem' := fun {a b} ha hb => ⟨A.mul_mem ha.1 hb.1, by
        rw [Commute.mul_pow (hAab a ha.1 b hb.1), ha.2, hb.2, one_mul]⟩
      one_mem' := ⟨A.one_mem, one_pow p⟩
      inv_mem' := fun {a} ha => ⟨A.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  have hApn : Ap.Normal := ⟨fun a ha g => ⟨hAn.conj_mem a ha.1 g, by
    rw [conj_pow, ha.2, mul_one, mul_inv_cancel]⟩⟩
  have hApE : Ap = E := hmax' Ap hApn (fun x hx y hy => hAab x hx.1 y hy.1) (fun x hx => hx.2)
    fun e he => ⟨hEA he, hEp e he⟩
  have hAE : ∀ a ∈ A, a ^ p = 1 → a ∈ E := fun a ha hap => by
    rw [← hApE]
    exact ⟨ha, hap⟩
  set C : Subgroup P := centralizer (E : Set P) with hC
  set X : Subgroup P := closure {x : P | x ∈ C ∧ x ^ p = 1} with hX
  have hXC : X ≤ C := (closure_le C).2 fun x hx => hx.1
  have hEC : E ≤ C := fun e he => mem_centralizer_iff.2 fun f hf => hEab f hf e he
  have hEX : E ≤ X := fun e he => subset_closure ⟨hEC he, hEp e he⟩
  have hXn : X.Normal := closure_normal_of_conj_mem fun x hx g =>
    ⟨(inferInstance : C.Normal).conj_mem x hx.1 g, by rw [conj_pow, hx.2, mul_one, mul_inv_cancel]⟩
  have hgen : ∀ x : P, x ∈ C → x ^ p = 1 → ∀ a ∈ A, a⁻¹ * (x * a * x⁻¹) ∈ E := by
    intro x hxC hxp a ha
    let : CommGroup A :=
      { (inferInstance : Group A) with mul_comm := fun a b => Subtype.ext (hAab a a.2 b b.2) }
    have hα : (MulAut.conjNormal x : MulAut A) ^ p = 1 := by
      rw [← map_pow, hxp, map_one]
    have hfix : ∀ b : A, b ^ p = 1 → MulAut.conjNormal x b = b := by
      intro b hb
      apply Subtype.ext
      have hbE : (b : P) ∈ E := hAE b b.2 (by
        have h := congrArg Subtype.val hb
        rwa [coe_pow, coe_one] at h)
      rw [MulAut.conjNormal_apply, ← mem_centralizer_iff.1 hxC _ hbE, mul_inv_cancel_right]
    have h := SectionRank.Ccomm.odd_abelian_order_p_automorphism hp2 (hP.to_subgroup A) _ hα
      hfix ⟨a, ha⟩
    refine hAE _ (A.mul_mem (A.inv_mem ha) (hAn.conj_mem a ha x)) ?_
    have h' := congrArg Subtype.val h
    rwa [coe_pow, coe_mul, coe_inv, MulAut.conjNormal_apply, coe_one] at h'
  let Y : Subgroup P :=
    { carrier := {x | ∀ a ∈ A, a⁻¹ * (x * a * x⁻¹) ∈ E}
      mul_mem' := fun {x y} hx hy a ha => by
        have h := E.mul_mem (hy a ha) (hx (y * a * y⁻¹) (hAn.conj_mem a ha y))
        rwa [show a⁻¹ * (y * a * y⁻¹) * ((y * a * y⁻¹)⁻¹ * (x * (y * a * y⁻¹) * x⁻¹)) =
          a⁻¹ * (x * y * a * (x * y)⁻¹) by group] at h
      one_mem' := fun a _ => by simp
      inv_mem' := fun {x} hx a ha => by
        have h := E.inv_mem (hx (x⁻¹ * a * x⁻¹⁻¹) (hAn.conj_mem a ha x⁻¹))
        rwa [show ((x⁻¹ * a * x⁻¹⁻¹)⁻¹ * (x * (x⁻¹ * a * x⁻¹⁻¹) * x⁻¹))⁻¹ =
          a⁻¹ * (x⁻¹ * a * x⁻¹⁻¹) by group] at h }
  have hXY : ∀ x ∈ X, ∀ a ∈ A, a⁻¹ * (x * a * x⁻¹) ∈ E := fun x hx =>
    ((closure_le Y).2 fun y hy => hgen y hy.1 hy.2) hx
  have hcommA : ∀ x ∈ X, ∀ y ∈ X, ∀ c ∈ A,
      x * (y * c * y⁻¹) * x⁻¹ = y * (x * c * x⁻¹) * y⁻¹ := by
    intro x hx y hy c hc
    obtain ⟨u, huE, hu⟩ : ∃ u ∈ E, y * c * y⁻¹ = c * u := ⟨_, hXY y hy c hc, by group⟩
    obtain ⟨v, hvE, hv⟩ : ∃ v ∈ E, x * c * x⁻¹ = c * v := ⟨_, hXY x hx c hc, by group⟩
    have hxu : x * u * x⁻¹ = u := by
      rw [← mem_centralizer_iff.1 (hXC hx) u huE, mul_inv_cancel_right]
    have hyv : y * v * y⁻¹ = v := by
      rw [← mem_centralizer_iff.1 (hXC hy) v hvE, mul_inv_cancel_right]
    calc x * (y * c * y⁻¹) * x⁻¹ = (x * c * x⁻¹) * (x * u * x⁻¹) := by rw [hu]; group
      _ = c * (v * u) := by rw [hv, hxu, mul_assoc]
      _ = c * (u * v) := by rw [hEab v hvE u huE]
      _ = (y * c * y⁻¹) * (y * v * y⁻¹) := by rw [hu, hyv, mul_assoc]
      _ = y * (x * c * x⁻¹) * y⁻¹ := by rw [hv]; group
  have hcommX : ∀ x ∈ X, ∀ y ∈ X, ⁅x, y⁆ ∈ A := by
    intro x hx y hy
    rw [← hcenA, mem_centralizer_iff]
    intro a ha
    have hb : y⁻¹ * a * y ∈ A := by simpa using hAn.conj_mem a ha y⁻¹
    have hc : x⁻¹ * (y⁻¹ * a * y) * x ∈ A := by simpa using hAn.conj_mem _ hb x⁻¹
    have h : x * (y * (x⁻¹ * (y⁻¹ * a * y) * x) * y⁻¹) * x⁻¹ = a := by
      rw [hcommA x hx y hy _ hc]
      group
    rw [commutatorElement_def]
    calc a * (x * y * x⁻¹ * y⁻¹)
        = x * (y * (x⁻¹ * (y⁻¹ * a * y) * x) * y⁻¹) * x⁻¹ * (x * y * x⁻¹ * y⁻¹) := by rw [h]
      _ = x * y * x⁻¹ * y⁻¹ * a := by group
  have hXexp : ∀ x ∈ X, x ^ p = 1 := by
    obtain ⟨-, hall⟩ := SectionRank.Ccomm.odd_torsion_generated_exponent hp2 (A.subgroupOf X)
      (fun a ha b hb => Subtype.ext (hAab _ ha _ hb))
      (by
        rw [_root_.commutator_def, commutator_le]
        intro g₁ _ g₂ _
        rw [mem_subgroupOf]
        exact hcommX _ g₁.2 _ g₂.2)
      (E.subgroupOf X)
      (fun a => by
        rw [mem_subgroupOf, mem_subgroupOf, Subtype.ext_iff, coe_pow, coe_one]
        exact ⟨fun h => ⟨hEA h, hEp _ h⟩, fun h => hAE _ h.1 h.2⟩)
      (fun e he => mem_center_iff.2 fun g => Subtype.ext
        (mem_centralizer_iff.1 (hXC g.2) _ (mem_subgroupOf.1 he)).symm)
      (by
        rw [commutator_le]
        intro a ha g _
        rw [mem_subgroupOf]
        have h := hXY g g.2 (a : P)⁻¹ (A.inv_mem (mem_subgroupOf.1 ha))
        rwa [show (a : P)⁻¹⁻¹ * ((g : P) * (a : P)⁻¹ * (g : P)⁻¹) = ((⁅a, g⁆ : X) : P) by
          simp only [commutatorElement_def, coe_mul, coe_inv, inv_inv]; group] at h)
      (closure_pow_eq_one_eq_top fun x hx => hx.2)
    intro x hx
    have h := congrArg Subtype.val (hall ⟨x, hx⟩)
    rwa [coe_pow, coe_one] at h
  have hXE : X ≤ E := by
    by_contra hXE
    have hlt : E < X := lt_of_le_not_ge hEX hXE
    obtain ⟨b, hbX, -, -, B, hBn, hEB, hBX, -, hform, -⟩ :=
      SectionRank.Ccomm.exists_central_extension hP hlt
    have hBab := SectionRank.Ccomm.comm_of_forall_eq_zpow_mul hEab (hXC hbX) hform
    exact hEB.ne (hmax' B hBn hBab (fun x hx => hXexp x (hBX hx)) hEB.le).symm
  refine ⟨?_, fun x hxC hxp => hXE (subset_closure ⟨hxC, hxp⟩)⟩
  rw [← le_antisymm hXE hEX, omega₁, omega, pow_one, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨c.2, ?_⟩
    have h := congrArg Subtype.val (show c ^ p = 1 from hc)
    rwa [coe_pow, coe_one] at h
  · rintro ⟨hxC, hxp⟩
    exact ⟨⟨x, hxC⟩, Subtype.ext (by rw [coe_pow, coe_one]; exact hxp), rfl⟩

end CFSG.RankThree.PGroups
