module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.Basic

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter1section1

open PFAppendixIII

/-!
# Peterfalvi, Part II, Chapter I, Section 1, Proposition 4(a)
-/


/-- Peterfalvi use of `H = QD`: every element of `H` has explicit `Q`-then-`D`
coordinates. -/
private theorem proposition_4_a_mem_H_decompose_QD
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t) {h : G} (hh : h ∈ H) :
    ∃ q : Q, ∃ d : D, (q : G) * (d : G) = h := by
  let QH : Subgroup H := Q.subgroupOf H
  let DH : Subgroup H := D.subgroupOf H
  haveI : QH.Normal := by
    simpa [QH] using hA1.Q_normal_in_H
  have hsupH : QH ⊔ DH = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (A := Q) (A' := D) (B := H)
        hA1.Q_le_H hA1.D_le_H]
    rw [hA1.Q_sup_D, Subgroup.subgroupOf_self]
  have hh_sup : (⟨h, hh⟩ : H) ∈ QH ⊔ DH := by
    rw [hsupH]
    trivial
  rcases (Subgroup.mem_sup_of_normal_left
      (s := QH) (t := DH) (x := (⟨h, hh⟩ : H))).1 hh_sup with
    ⟨q, hq, d, hd, hqd⟩
  refine ⟨⟨q, ?_⟩, ⟨d, ?_⟩, ?_⟩
  · simpa [QH, Subgroup.mem_subgroupOf] using hq
  · simpa [DH, Subgroup.mem_subgroupOf] using hd
  · simpa using congrArg Subtype.val hqd

private theorem proposition_4_a_rightConjugateElem_mem_rightConjugate
    {G : Type*} [Group G] {H : Subgroup G} {a t : G}
    (ha : a ∈ H) : rightConjugateElem a t ∈ rightConjugate H t := by
  rw [rightConjugate, rightConjugateElem, Subgroup.conjBy, Subgroup.mem_map]
  exact ⟨a, ha, by simp⟩

private theorem proposition_4_a_rightConjugateElem_mem_of_mem_rightConjugate
    {G : Type*} [Group G] {H : Subgroup G} {a t : G}
    (htinv : t⁻¹ = t) (ha : a ∈ rightConjugate H t) :
    rightConjugateElem a t ∈ H := by
  rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map] at ha
  rcases ha with ⟨h, hh, rfl⟩
  have hmapped :
      (MulEquiv.toMonoidHom (MulAut.conj t⁻¹)) h =
        rightConjugateElem h t := by
    simp [rightConjugateElem, htinv, mul_assoc]
  rw [hmapped]
  simpa [rightConjugateElem_rightConjugateElem (a := h) htinv] using hh

private theorem proposition_4_a_rightConjugateElem_mem_D
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t) {d : G} (hd : d ∈ D) :
    rightConjugateElem d t ∈ D := by
  have htinv : t⁻¹ = t :=
    hA1.involution_t.inv_eq_self
  rw [hA1.D_eq] at hd ⊢
  exact
    ⟨proposition_4_a_rightConjugateElem_mem_of_mem_rightConjugate
        (H := H) htinv hd.2,
      proposition_4_a_rightConjugateElem_mem_rightConjugate (H := H) hd.1⟩

/-- Peterfalvi use of normality of `Q` in `H`: the `H = QD` coordinates may be
reordered as `H = DQ`. -/
private theorem proposition_4_a_mem_H_decompose_DQ
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t) {h : G} (hh : h ∈ H) :
    ∃ d : D, ∃ q : Q, (d : G) * (q : G) = h := by
  rcases proposition_4_a_mem_H_decompose_QD H D Q t hA1 hh with ⟨q, d, hqd⟩
  let qH : H := ⟨q, hA1.Q_le_H q.property⟩
  let dH : H := ⟨d, hA1.D_le_H d.property⟩
  have hqH : qH ∈ Q.subgroupOf H := by
    simp [qH, Subgroup.mem_subgroupOf]
  have hq_conj_H :=
    hA1.Q_normal_in_H.conj_mem qH hqH dH⁻¹
  have hq_conj : (d : G)⁻¹ * (q : G) * (d : G) ∈ Q := by
    simp [qH, dH, Subgroup.mem_subgroupOf] at hq_conj_H ⊢
    exact hq_conj_H
  refine ⟨d, ⟨(d : G)⁻¹ * (q : G) * (d : G), hq_conj⟩, ?_⟩
  calc
    (d : G) * ((d : G)⁻¹ * (q : G) * (d : G)) = (q : G) * (d : G) := by
      group
    _ = h := hqd

/--
Peterfalvi: Proposition 4(a), first sentence of the proof:
`G - H = HtH = HtQ`, using double transitivity, `t` normalizing `D`, and
`H = QD`.
-/
private theorem proposition_4_a_exists
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t) :
    ∀ g : G, g ∉ H →
      ∃ p : H × Q, g = (p.1 : G) * t * (p.2 : G) := by
  intro g hg
  rcases hA1.point_stabilizer with ⟨point, hpoint⟩
  have ht_ne : t • point ≠ point := by
    intro htfix
    exact hA1.t_not_mem_H (by simpa [hpoint, MulAction.mem_stabilizer_iff] using htfix)
  have hg_ne : ∀ g : G, g ∉ H → g • point ≠ point := by
    intro g hg hgfix
    exact hg (by simpa [hpoint, MulAction.mem_stabilizer_iff] using hgfix)
  obtain ⟨x, hxt_point, hx_point⟩ :=
    (MulAction.is_two_pretransitive_iff (G := G) (α := Ω)).1
      hA1.two_transitive ht_ne (hg_ne g hg)
  have hx_mem_H : x ∈ H := by
    rw [hpoint]
    exact (MulAction.mem_stabilizer_iff (G := G) (a := point) (g := x)).2 hx_point
  have hgt_mem_H : g⁻¹ * x * t ∈ H := by
    rw [hpoint]
    rw [MulAction.mem_stabilizer_iff]
    simpa [mul_smul] using congrArg (fun z : Ω => g⁻¹ • z) hxt_point
  obtain ⟨d, q, hdq⟩ :=
    proposition_4_a_mem_H_decompose_DQ H D Q t hA1 (H.inv_mem hgt_mem_H)
  have htinv : t⁻¹ = t :=
    hA1.involution_t.inv_eq_self
  have ht2 : t * t = 1 := by
    simpa [pow_two] using hA1.involution_t.sq_eq_one
  have htd_mem_D : rightConjugateElem (d : G) t ∈ D :=
    proposition_4_a_rightConjugateElem_mem_D H D Q t hA1 d.property
  let left : H := ⟨x * rightConjugateElem (d : G) t,
    H.mul_mem hx_mem_H (hA1.D_le_H htd_mem_D)⟩
  refine ⟨(left, q), ?_⟩
  calc
    g = x * t * (g⁻¹ * x * t)⁻¹ := by
      group
    _ = x * t * ((d : G) * (q : G)) := by
      rw [hdq]
    _ = x * t * (d : G) * (q : G) := by
      group
    _ = (left : G) * t * (q : G) := by
      simp [left, rightConjugateElem, htinv, ht2, mul_assoc]

/--
Peterfalvi: Proposition 4(a), uniqueness paragraph: if
`x₁ t y₁ = x₂ t y₂`, then `H^(t y₁) = H^(t y₂)`, and the regular action of
`Q` on `Ω - {H}` gives `y₁ = y₂`, hence `x₁ = x₂`.
-/
private theorem proposition_4_a_unique
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t) :
    ∀ p₁ p₂ : H × Q,
      (p₁.1 : G) * t * (p₁.2 : G) = (p₂.1 : G) * t * (p₂.2 : G) →
        p₁ = p₂ := by
  intro p₁ p₂ heq
  have htinv : t⁻¹ = t :=
    hA1.involution_t.inv_eq_self
  let qdiff : G := (p₂.2 : G) * (p₁.2 : G)⁻¹
  have hqdiff_Q : qdiff ∈ Q := by
    exact Q.mul_mem p₂.2.property (Q.inv_mem p₁.2.property)
  have hleft_H : (p₂.1 : G)⁻¹ * (p₁.1 : G) ∈ H := by
    exact H.mul_mem (H.inv_mem p₂.1.property) p₁.1.property
  have hcalc :
      (p₂.1 : G)⁻¹ * (p₁.1 : G) = t * qdiff * t⁻¹ := by
    calc
      (p₂.1 : G)⁻¹ * (p₁.1 : G) =
          (p₂.1 : G)⁻¹ * ((p₁.1 : G) * t * (p₁.2 : G)) *
            (p₁.2 : G)⁻¹ * t⁻¹ := by
            group
      _ = (p₂.1 : G)⁻¹ * ((p₂.1 : G) * t * (p₂.2 : G)) *
            (p₁.2 : G)⁻¹ * t⁻¹ := by
            rw [heq]
      _ = t * qdiff * t⁻¹ := by
            simp [qdiff, mul_assoc]
  have hconjD : rightConjugateElem qdiff t ∈ D := by
    rw [hA1.D_eq]
    refine ⟨?_, ?_⟩
    · have hright_eq :
          rightConjugateElem qdiff t = (p₂.1 : G)⁻¹ * (p₁.1 : G) := by
        simpa [rightConjugateElem, htinv, mul_assoc] using hcalc.symm
      simpa [hright_eq] using hleft_H
    · exact
        proposition_4_a_rightConjugateElem_mem_rightConjugate
          (H := H) (hA1.Q_le_H hqdiff_Q)
  have hqdiff_D : qdiff ∈ D := by
    have hback := proposition_4_a_rightConjugateElem_mem_D H D Q t hA1 hconjD
    simpa [qdiff, rightConjugateElem_rightConjugateElem
      (a := qdiff) htinv] using hback
  have hqdiff_one : qdiff = 1 := by
    have hmem : qdiff ∈ Q ⊓ D := ⟨hqdiff_Q, hqdiff_D⟩
    have := hA1.Q_disjoint_D.le_bot hmem
    simpa using this
  have hq₂_eq_q₁ : (p₂.2 : G) = (p₁.2 : G) := by
    exact mul_inv_eq_one.mp hqdiff_one
  have hq_eq : p₁.2 = p₂.2 := by
    exact Subtype.ext hq₂_eq_q₁.symm
  have hh_eq : p₁.1 = p₂.1 := by
    have htq_eq :
        (p₁.1 : G) * t * (p₁.2 : G) =
          (p₂.1 : G) * t * (p₁.2 : G) := by
      simpa [hq₂_eq_q₁] using heq
    have ht_eq : (p₁.1 : G) * t = (p₂.1 : G) * t :=
      mul_right_cancel htq_eq
    exact Subtype.ext (mul_right_cancel ht_eq)
  exact Prod.ext hh_eq hq_eq

public theorem proposition_4_a
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t) :
    ∀ g : G, g ∉ H →
      ∃! p : H × Q, g = (p.1 : G) * t * (p.2 : G) := by
  intro g hg
  rcases proposition_4_a_exists H D Q t hA1 g hg with ⟨p, hp⟩
  refine ⟨p, hp, ?_⟩
  intro q hq
  exact proposition_4_a_unique H D Q t hA1 q p (hq.symm.trans hp)

end PFchapter1section1
end CFSG.BenderSuzuki
