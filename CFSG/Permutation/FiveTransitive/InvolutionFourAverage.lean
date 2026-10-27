module

public import CFSG.Permutation.FiveTransitive.FourFixerIntersectionAverage
public import CFSG.Permutation.FiveTransitive.InvolutionFourPattern

public section

namespace CFSG

namespace FiveTransitive.InvolutionFourAverage

open Equiv MulAction

theorem exists_conjugate_four_dvd_overlap
    {X : Type*} [Fintype X] [DecidableEq X]
    (P : Subgroup (Perm X)) (h5 : IsMultiplyPretransitive P X 5)
    (s : Perm X) (hsP : s ∈ P) (hs : orderOf s = 2)
    (hm : 5 ≤ s.support.card) (hfixed : 2 ≤ (fixedBy X s).ncard) :
    ∃ t : Perm X, t ∈ P ∧ IsConj s t ∧ orderOf t = 2 ∧ t.support.card = s.support.card ∧
      4 ∣ orderOf (s * t) ∧ 2 ≤ (s.support ∩ t.support).card ∧
      (Fintype.card X - 4) * ((s.support ∩ t.support).card - 2) ≤
        (s.support.card - 4) * (s.support.card - 2) := by
  classical
  have hn : 5 ≤ Fintype.card X := hm.trans (Finset.card_le_univ _)
  let _ : IsMultiplyPretransitive P X 5 := h5
  have h4 : IsMultiplyPretransitive P X 4 := isMultiplyPretransitive_of_le
    (G := P) (α := X) (m := 4) (n := 5) (by omega)
    (by simpa only [Nat.card_eq_fintype_card] using hn)
  obtain ⟨e, hs01, hs10, hs23, hs32⟩ := InvolutionFourPattern.exists_two_swaps s hs (by omega)
  obtain ⟨k, hv0, hv3, hv1, hv2⟩ :=
    InvolutionFourPattern.exists_conjugate_pattern P h4 s e hs01 hs10 hfixed
  let v : Perm X := (k : Perm X) * s * (k : Perm X)⁻¹
  change v (e 0) = e 0 at hv0
  change v (e 3) = e 3 at hv3
  change v (e 1) = e 2 at hv1
  change v (e 2) = e 1 at hv2
  have hvP : v ∈ P := P.mul_mem (P.mul_mem k.property hsP) (P.inv_mem k.property)
  have hvm : v.support.card = s.support.card := by
    simp only [v, Perm.support_conj, Finset.card_map]
  let D : Set X := Set.range e
  have hD : D.ncard = 4 := by simp [D, Set.ncard_range_of_injective e.injective]
  have hsupp (i : Fin 4) : e i ∈ s.support := by
    rw [Perm.mem_support]
    fin_cases i
    · change s (e 0) ≠ e 0
      rw [hs01]; exact e.injective.ne (by decide)
    · change s (e 1) ≠ e 1
      rw [hs10]; exact e.injective.ne (by decide)
    · change s (e 2) ≠ e 2
      rw [hs23]; exact e.injective.ne (by decide)
    · change s (e 3) ≠ e 3
      rw [hs32]; exact e.injective.ne (by decide)
  have hDA : ∀ x ∈ D, x ∈ s.support := by rintro x ⟨i,rfl⟩; exact hsupp i
  have hAinside : (s.support.filter (fun x => x ∈ D)).card = 4 := by
    have heq : s.support.filter (fun x => x ∈ D) = Finset.univ.image e := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨fun hx => hx.2, fun hx => ⟨hDA x hx, hx⟩⟩
    rw [heq, Finset.card_image_of_injective _ e.injective]
    exact Fintype.card_fin 4
  have hBinside : (v.support.filter (fun x => x ∈ D)).card = 2 := by
    have heq : v.support.filter (fun x => x ∈ D) = {e 1,e 2} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hx,⟨i,rfl⟩⟩
        fin_cases i
        · exact ((Perm.mem_support.mp hx) hv0).elim
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact ((Perm.mem_support.mp hx) hv3).elim
      · rintro (rfl | rfl)
        · refine ⟨?_, ⟨1,rfl⟩⟩
          rw [Perm.mem_support, hv1]
          exact e.injective.ne (by decide)
        · refine ⟨?_, ⟨2,rfl⟩⟩
          rw [Perm.mem_support, hv2]
          exact e.injective.ne (by decide)
    rw [heq]
    simp [e.injective.ne (by decide : (1 : Fin 4) ≠ 2)]
  have hAout : (s.support.filter (fun x => x ∉ D)).card = s.support.card - 4 := by
    have heq := Finset.card_filter_add_card_filter_not (s := s.support) (fun x => x ∈ D)
    rw [hAinside] at heq
    omega
  have hBout : (v.support.filter (fun x => x ∉ D)).card = s.support.card - 2 := by
    have heq := Finset.card_filter_add_card_filter_not (s := v.support) (fun x => x ∈ D)
    rw [hBinside, hvm] at heq
    omega
  obtain ⟨q, hlo, havg⟩ := FourFixerIntersectionAverage.exists_fixing_intersection_le
    P h5 hn D hD s.support v.support hDA
  rw [hBinside, hAout, hBout] at havg
  rw [hBinside] at hlo
  let u : Perm X := q.val
  let t : Perm X := u * v * u⁻¹
  have hu (i : Fin 4) : u (e i) = e i :=
    (mem_fixingSubgroup_iff P).mp q.property (e i) ⟨i,rfl⟩
  have hui (i : Fin 4) : u⁻¹ (e i) = e i :=
    (mem_fixingSubgroup_iff P).mp (q⁻¹).property (e i) ⟨i,rfl⟩
  have ht0 : t (e 0) = e 0 := by simp only [t,Perm.mul_apply,hui,hv0,hu]
  have ht3 : t (e 3) = e 3 := by simp only [t,Perm.mul_apply,hui,hv3,hu]
  have ht1 : t (e 1) = e 2 := by simp only [t,Perm.mul_apply,hui,hv1,hu]
  have ht2 : t (e 2) = e 1 := by simp only [t,Perm.mul_apply,hui,hv2,hu]
  have hconjv : IsConj s v := isConj_iff.mpr ⟨k, rfl⟩
  have hconjt : IsConj v t := isConj_iff.mpr ⟨u, rfl⟩
  have hconj : IsConj s t := hconjv.trans hconjt
  have htP : t ∈ P := P.mul_mem (P.mul_mem q.val.property hvP) (P.inv_mem q.val.property)
  have hvo : orderOf v = orderOf s := (MulAut.conj (k : Perm X)).orderOf_eq s
  have hto : orderOf t = orderOf v := (MulAut.conj u).orderOf_eq v
  have htorder : orderOf t = 2 := hto.trans (hvo.trans hs)
  have htsupport : t.support = v.support.image u := by
    simp only [t,Perm.support_conj,Finset.map_eq_image,Equiv.coe_toEmbedding]
  refine ⟨t, htP, hconj, htorder, ?_, ?_, ?_, ?_⟩
  · rw [htsupport,Finset.card_image_of_injective _ u.injective,hvm]
  · apply InvolutionFourPattern.four_dvd_orderOf (s * t)
      (a := e 0) (b := e 1) (c := e 2) (d := e 3) (e.injective.ne (by decide))
    · simp only [Perm.mul_apply,ht0,hs01]
    · simp only [Perm.mul_apply,ht1,hs23]
    · simp only [Perm.mul_apply,ht3,hs32]
    · simp only [Perm.mul_apply,ht2,hs10]
  · simpa only [htsupport] using hlo
  · rw [htsupport]
    simpa only [Nat.mul_comm] using havg

end FiveTransitive.InvolutionFourAverage

end CFSG
