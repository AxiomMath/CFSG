module

public import CFSG.Quasithin.Vol2.Ch10SecQ9H38
public import CFSG.Quasithin.Vol2.Ch10SecQ9H33
public import CFSG.Quasithin.Vol2.Ch10SecQ9H37

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open Matrix

theorem comm_utSL_mem {m k : ℕ} {X : Subgroup (Matrix.SpecialLinearGroup (Fin (m + k)) (ZMod 2))}
    {l : Matrix.SpecialLinearGroup (Fin (m + k)) (ZMod 2)} (hl : l ∈ X)
    {B : Matrix (Fin m) (Fin k) (ZMod 2)}
    (hτ : utSL B ∈ Subgroup.normalizer
      (X : Set (Matrix.SpecialLinearGroup (Fin (m + k)) (ZMod 2)))) :
    l * utSL B * l⁻¹ * utSL B ∈ X := by
  have h1 : utSL B * l⁻¹ * (utSL B)⁻¹ ∈ X :=
    (Subgroup.mem_normalizer_iff.mp hτ _).mp (X.inv_mem hl)
  rw [utSL_inv] at h1
  have := X.mul_mem hl h1
  rwa [← mul_assoc, ← mul_assoc] at this

theorem utSL_mem_of_E3 {X : Subgroup (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))}
    (h3 : InvStd X 3) (htriv : ∀ x ∈ X, ∀ v, x • v + v ∈ stdE 5 3)
    (hq : Nonempty (↥X ⧸ CFSG.pCore 2 ↥X ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))
    (hU : uniSL 5 ≤ Subgroup.normalizer (X : Set (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))))
    (B : Matrix (Fin 3) (Fin 2) (ZMod 2)) : utSL B ∈ X := by
  obtain ⟨e⟩ := hq
  have hcard := card_eq_o2G_mul X e
  have hX : X ≤ stabStd 3 2 := le_stabStd_of_invStd (m := 3) (k := 2) h3
  have hbot : ∀ x : ↥(stabStd 3 2), x.1 ∈ X → botH 3 2 x = 1 := fun x hx =>
    Subtype.ext (botB_eq_one_of_triv (htriv x.1 hx))
  have himg := map_eq_top_of_sq hX (topH 3 2) (fun x hx ht =>
    sq_eq_one_of_blocks x.2 (congrArg Subtype.val ht) (congrArg Subtype.val (hbot x hx))) hcard
  have hg : a7 ∈ (X.subgroupOf (stabStd 3 2)).map (topH 3 2) := by rw [himg]; trivial
  obtain ⟨l, hl, hla⟩ := hg
  have hlX : l.1 ∈ X := Subgroup.mem_subgroupOf.mp hl
  have hc := comm_utSL_mem (m := 3) (k := 2) hlX
    (hU (utSL_mem_uniSL (m := 3) (k := 2) (m7 * B)))
  have hA : topB ((l.1 : Matrix.SpecialLinearGroup (Fin (3 + 2)) (ZMod 2)) :
      Matrix (Fin (3 + 2)) (Fin (3 + 2)) (ZMod 2)) = (a7 : Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
    congrArg Subtype.val hla
  rwa [comm_utSL_top l.2 (congrArg Subtype.val (hbot l hlX)), hA, ← Matrix.mul_assoc,
    one_add_a7_mul_m7, Matrix.one_mul] at hc

theorem utSL_mem_of_E2 {X : Subgroup (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))}
    (h2 : InvStd X 2) (htriv : ∀ x ∈ X, ∀ v ∈ stdE 5 2, x • v = v)
    (hq : Nonempty (↥X ⧸ CFSG.pCore 2 ↥X ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))
    (hU : uniSL 5 ≤ Subgroup.normalizer (X : Set (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))))
    (B : Matrix (Fin 2) (Fin 3) (ZMod 2)) : utSL B ∈ X := by
  obtain ⟨e⟩ := hq
  have hcard := card_eq_o2G_mul X e
  have hX : X ≤ stabStd 2 3 := le_stabStd_of_invStd (m := 2) (k := 3) h2
  have htop : ∀ x : ↥(stabStd 2 3), x.1 ∈ X → topH 2 3 x = 1 := fun x hx =>
    Subtype.ext (topB_eq_one_of_fix fun j => htriv x.1 hx _ (castAdd_mem_stdE (k := 3) j))
  have himg := map_eq_top_of_sq hX (botH 2 3) (fun x hx hb =>
    sq_eq_one_of_blocks x.2 (congrArg Subtype.val (htop x hx)) (congrArg Subtype.val hb)) hcard
  have hg : a7⁻¹ ∈ (X.subgroupOf (stabStd 2 3)).map (botH 2 3) := by rw [himg]; trivial
  obtain ⟨l, hl, hla⟩ := hg
  have hlX : l.1 ∈ X := Subgroup.mem_subgroupOf.mp hl
  have hc := comm_utSL_mem (m := 2) (k := 3) hlX
    (hU (utSL_mem_uniSL (m := 2) (k := 3) (B * m7)))
  have hA : botB (((l.1)⁻¹ : Matrix.SpecialLinearGroup (Fin (2 + 3)) (ZMod 2)) :
      Matrix (Fin (2 + 3)) (Fin (2 + 3)) (ZMod 2)) = (a7 : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
    have h := congrArg Subtype.val (show botH 2 3 l⁻¹ = a7 by rw [map_inv, hla, inv_inv])
    exact h
  rwa [comm_utSL_bot l.2 (congrArg Subtype.val (htop l hlX)), hA, Matrix.mul_assoc,
    m7_mul_one_add_a7, Matrix.mul_one] at hc

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
