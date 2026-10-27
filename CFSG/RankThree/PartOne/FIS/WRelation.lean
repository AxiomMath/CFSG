module

public import CFSG.RankThree.PartOne.FIS.VRelation
public import CFSG.RankThree.PartOne.FIS.WidthOne

public section

namespace CFSG.RankThree.PartOne.FIS

open CFSG.LocalAnalysis.GorensteinLyons (IsThreeTranspositions)
open CFSG.RankThree.PartTwo.Sec7

variable {G : Type*} [Group G] {D : Set G}

theorem wSet_noncomm {x a b : G} (ha : a ∈ wSet D x) (hb : b ∈ wSet D x) (hab : a ≠ b) :
    a * b ≠ b * a := by
  rcases wRel_ne_or_noncomm hb.1 (show WRel D a b from ha.2.trans hb.2.symm) with h | h
  · exact absurd h hab
  · exact h

theorem wSet_conj_mem (hD : IsThreeTranspositions D) {x w a : G} (hw : w ∈ wSet D x)
    (ha : a ∈ wSet D x) : w * a * w⁻¹ ∈ wSet D x := by
  refine ⟨tt_conj_mem hD ha.1 w, ?_⟩
  have key : ∀ y, w⁻¹ * y * w ∈ localSet D x ↔ y ∈ localSet D x := by
    intro y
    constructor
    · intro h
      have h' : w⁻¹ * y * w ∈ localSet D w := by rw [hw.2]; exact h
      have hc := h'.2.1
      have hww := tt_mul_self hD hw.1
      have hyw : y * w = w * y := by
        have e1 : (w⁻¹ * y * w) * w = w⁻¹ * y := by
          rw [mul_assoc, hww, mul_one]
        have e2 : w * (w⁻¹ * y * w) = y * w := by group
        rw [e1, e2] at hc
        calc y * w = w⁻¹ * y := hc.symm
          _ = w * y := by rw [tt_inv_eq hD hw.1]
      have hy : w⁻¹ * y * w = y := by
        calc w⁻¹ * y * w = w * (y * w) := by rw [tt_inv_eq hD hw.1, mul_assoc]
          _ = w * (w * y) := by rw [hyw]
          _ = (w * w) * y := by rw [mul_assoc]
          _ = y := by rw [hww, one_mul]
      rwa [hy] at h
    · intro h
      have h' : y ∈ localSet D w := by rw [hw.2]; exact h
      have hyw := h'.2.1
      have hww := tt_mul_self hD hw.1
      have hy : w⁻¹ * y * w = y := by
        calc w⁻¹ * y * w = w * (y * w) := by rw [tt_inv_eq hD hw.1, mul_assoc]
          _ = w * (w * y) := by rw [hyw]
          _ = (w * w) * y := by rw [mul_assoc]
          _ = y := by rw [hww, one_mul]
      rwa [hy]
  ext y
  rw [mem_localSet_conj hD, ha.2]
  exact key y

theorem wSet_conj_closure (hD : IsThreeTranspositions D) {x : G} :
    ∀ g ∈ Subgroup.closure (wSet D x), ∀ a ∈ wSet D x,
      g * a * g⁻¹ ∈ wSet D x ∧ g⁻¹ * a * g ∈ wSet D x := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem w hw =>
    intro a ha
    have h := wSet_conj_mem hD hw ha
    rw [tt_inv_eq hD hw.1] at h ⊢
    exact ⟨h, h⟩
  | one => intro a ha; simpa using ha
  | mul g h _ _ ihg ihh =>
    intro a ha
    constructor
    · have := (ihg _ (ihh a ha).1).1
      rwa [show g * (h * a * h⁻¹) * g⁻¹ = g * h * a * (g * h)⁻¹ by group] at this
    · have := (ihh _ (ihg a ha).2).2
      rwa [show h⁻¹ * (g⁻¹ * a * g) * h = (g * h)⁻¹ * a * (g * h) by group] at this
  | inv g _ ihg =>
    intro a ha
    exact ⟨by simpa using (ihg a ha).2, by simpa using (ihg a ha).1⟩

theorem wXgrp_isPGroup [Finite G] (hD : IsThreeTranspositions D) {x : G} (_hx : x ∈ D) :
    IsPGroup 3 (Xgrp (WRel D) D x) := by
  set S : Set G := wSet D x with hS
  let X : Subgroup G := Subgroup.closure S
  let E : Set X := Subtype.val ⁻¹' S
  have hP : IsPGroup 3 (Subgroup.closure {y : X | ∃ a ∈ E, ∃ b ∈ E, y = a * b}) := by
    refine isPGroup_three_closure_mul E ?_ ?_ ?_ ?_ ?_ ?_
    · intro e he g
      exact (wSet_conj_closure hD g.1 g.2 e he).1
    · exact Subgroup.closure_closure_coe_preimage
    · intro e he
      exact Subtype.ext (tt_mul_self hD he.1)
    · intro e he h
      exact tt_ne_one hD he.1 (congrArg Subtype.val h)
    · intro a ha b hb hab
      by_contra hne
      exact wSet_noncomm ha hb (fun h => hne (Subtype.ext h)) (congrArg Subtype.val hab)
    · intro a ha b hb
      by_cases hab : a = b
      · subst hab
        rw [Subtype.ext_iff] at *
        simp [tt_mul_self hD ha.1]
      · have hnc := wSet_noncomm ha hb (fun h => hab (Subtype.ext h))
        have := tt_cube hD ha.1 hb.1 hnc
        exact Subtype.ext (by simpa using this)
  have hmap := hP.map X.subtype
  have heq : Xgrp (WRel D) D x =
      Subgroup.map X.subtype (Subgroup.closure {y : X | ∃ a ∈ E, ∃ b ∈ E, y = a * b}) := by
    rw [MonoidHom.map_closure, Xgrp]
    congr 1
    ext s
    constructor
    · rintro ⟨a, ha, b, hb, hax, hbx, rfl⟩
      exact ⟨⟨a, Subgroup.subset_closure ⟨ha, hax⟩⟩ * ⟨b, Subgroup.subset_closure ⟨hb, hbx⟩⟩,
        ⟨⟨a, Subgroup.subset_closure ⟨ha, hax⟩⟩, ⟨ha, hax⟩,
          ⟨b, Subgroup.subset_closure ⟨hb, hbx⟩⟩, ⟨hb, hbx⟩, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩
      exact ⟨a, ha.1, b, hb.1, ha.2, hb.2, rfl⟩
  rw [heq]
  exact hmap

theorem wSet_mul_mem_pCore [Finite G] (hD : IsThreeTranspositions D) {w d : G} (hd : d ∈ D)
    (hw : w ∈ wSet D d) : w * d ∈ CFSG.pCore 3 G := by
  have hle := Xgrp_le_pCore hD (WRel D) (fun g _ _ h => WRel.conj hD g h) (fun _ _ h => h.symm)
    (fun _ _ _ h1 h2 => h1.trans h2) (fun _ => rfl)
    (fun a ha b hb hab c hc => wRel_mul_mem hD ha hb hab hc) 3
    (fun x hx => wXgrp_isPGroup hD hx) d hd
  exact hle (Subgroup.subset_closure ⟨w, hw.1, d, hd, hw.2, rfl, rfl⟩)

theorem wSet_subset_conjOrbit [Finite G] (hD : IsThreeTranspositions D) {d : G} (hd : d ∈ D) :
    wSet D d ⊆ conjOrbit (CFSG.pCore 3 G) d := by
  intro w hw
  by_cases hwd : w = d
  · exact ⟨1, one_mem _, by simp [hwd]⟩
  have hnc : w * d ≠ d * w := by
    rcases wRel_ne_or_noncomm hd hw.2 with h | h
    · exact absurd h hwd
    · exact h
  have hc := wSet_mul_mem_pCore hD hd hw
  refine ⟨(w * d)⁻¹, inv_mem hc, ?_⟩
  rw [inv_inv]
  exact (tt_conj_eq_of_noncomm hD hw.1 hd hnc).symm

theorem mem_localSet_conj_of_isPGroup_three [Finite G] (hD : IsThreeTranspositions D)
    (N : Subgroup G) [N.Normal] (hN : IsPGroup 3 N) {m d y : G} (hm : m ∈ N) (hd : d ∈ D)
    (hy : y ∈ localSet D d) : y ∈ localSet D (m * d * m⁻¹) := by
  obtain ⟨hyD, hyd, hne⟩ := hy
  have hu2 : (y * d) ^ 2 = 1 := by
    have hyy := tt_mul_self hD hyD
    have hdd := tt_mul_self hD hd
    calc (y * d) ^ 2 = y * d * (y * d) := sq _
      _ = y * (d * y) * d := by simp only [mul_assoc]
      _ = y * (y * d) * d := by rw [← hyd]
      _ = (y * y) * (d * d) := by simp only [mul_assoc]
      _ = 1 := by rw [hyy, hdd, mul_one]
  have hnotmem : y * d ∉ N := by
    intro h
    have h1 : y * d = 1 :=
      eq_one_of_mem_pGroup hN (by norm_num : Nat.Coprime 2 3) h hu2
    apply hne
    rw [← tt_inv_eq hD hd]
    exact eq_inv_of_mul_eq_one_left h1
  refine ⟨hyD, ?_, ?_⟩
  · by_contra hnc
    exact hnotmem (noncomm_imp_mem hD N hm hd hyD hyd hnc).2
  · intro h
    apply hnotmem
    rw [h]
    have : (m * d * m⁻¹) * d = m * (d * m⁻¹ * d⁻¹) := by
      rw [tt_inv_eq hD hd]
      simp only [mul_assoc]
    rw [this]
    exact mul_mem hm (Subgroup.Normal.conj_mem inferInstance _ (inv_mem hm) d)

theorem conjOrbit_subset_wSet [Finite G] (hD : IsThreeTranspositions D) {d : G} (hd : d ∈ D) :
    conjOrbit (CFSG.pCore 3 G) d ⊆ wSet D d := by
  rintro _ ⟨m, hm, rfl⟩
  have hN : IsPGroup 3 (CFSG.pCore 3 G) := CFSG.pCore_isPGroup
  have ha : m * d * m⁻¹ ∈ D := tt_conj_mem hD hd m
  refine ⟨ha, ?_⟩
  ext y
  constructor
  · intro hy
    have := mem_localSet_conj_of_isPGroup_three hD (CFSG.pCore 3 G) hN (inv_mem hm) ha hy
    rwa [show m⁻¹ * (m * d * m⁻¹) * m⁻¹⁻¹ = d by group] at this
  · intro hy
    exact mem_localSet_conj_of_isPGroup_three hD (CFSG.pCore 3 G) hN hm hd hy

theorem wSet_eq_conjOrbit [Finite G] (hD : IsThreeTranspositions D) {d : G} (hd : d ∈ D) :
    wSet D d = conjOrbit (CFSG.pCore 3 G) d :=
  Set.Subset.antisymm (wSet_subset_conjOrbit hD hd) (conjOrbit_subset_wSet hD hd)

end CFSG.RankThree.PartOne.FIS
