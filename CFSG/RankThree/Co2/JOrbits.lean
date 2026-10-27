module

public import CFSG.RankThree.Co2.JClasses
public import CFSG.RankThree.Co2.JOrbitsCert

public noncomputable section

open scoped Pointwise

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.Co2

open CFSG.Monster CFSG.Monster.B.Co2 CFSG.Monster.B.Short CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Census CFSG.Monster.B.TwoA.Co2Inv

theorem card_J_class_one : Nat.card {j : subW jWords // IsConj (rep 1) (j : Cr)} = 30 := by
  rw [card_J_crConj (by norm_num), jOrbitFacts_cert.one]

theorem card_J_class_three : Nat.card {j : subW jWords // IsConj (rep 3) (j : Cr)} = 60 := by
  rw [card_J_crConj (by norm_num), jOrbitFacts_cert.three]

theorem card_J_class_four : Nat.card {j : subW jWords // IsConj (rep 4) (j : Cr)} = 360 := by
  rw [card_J_crConj (by norm_num), jOrbitFacts_cert.four]

theorem card_J_class_five : Nat.card {j : subW jWords // IsConj (rep 5) (j : Cr)} = 240 := by
  rw [card_J_crConj (by norm_num), jOrbitFacts_cert.five]

theorem card_J_class_six : Nat.card {j : subW jWords // IsConj (rep 6) (j : Cr)} = 240 := by
  rw [card_J_crConj (by norm_num), jOrbitFacts_cert.six]

theorem card_J_class_eight : Nat.card {j : subW jWords // IsConj (rep 8) (j : Cr)} = 16 := by
  rw [card_J_crConj (by norm_num), jOrbitFacts_cert.eight]

@[expose] def InOmega (y : Cr) : Prop := y = rCr ∨ IsConj (rep 2) y ∨ IsConj (rep 7) y

theorem inOmega_iff_clsA (y : Cr) : InOmega y ↔ ClsA (crMat y) := by
  rw [InOmega, ClsA, ← isConj_iff_crConj (by norm_num), ← isConj_iff_crConj (by norm_num),
    ← isConj_iff_crConj (by norm_num), isConj_rep_zero_iff]

theorem clsB_iff (y : Cr) :
    ClsB (crMat y) ↔ IsConj (rep 1) y ∨ IsConj (rep 3) y ∨ IsConj (rep 5) y := by
  rw [ClsB, ← isConj_iff_crConj (by norm_num), ← isConj_iff_crConj (by norm_num),
    ← isConj_iff_crConj (by norm_num)]

theorem clsC_iff (y : Cr) :
    ClsC (crMat y) ↔ IsConj (rep 4) y ∨ IsConj (rep 6) y ∨ IsConj (rep 8) y := by
  rw [ClsC, ← isConj_iff_crConj (by norm_num), ← isConj_iff_crConj (by norm_num),
    ← isConj_iff_crConj (by norm_num)]

theorem card_Omega :
    Nat.card {y : subW jWords // InOmega (y : Cr)} = 77 := by
  have e := Nat.card_congr (Equiv.subtypeEquivRight
    (p := fun y : subW jWords => InOmega (y : Cr))
    (q := fun y : subW jWords => ClsA (crMat (y : Cr)))
    fun y => inOmega_iff_clsA (y : Cr))
  exact (e.trans (card_subW_crMat jWords_lt42 ClsA)).trans jOrbitFacts_cert.card_A

theorem card_pairs (y : subW jWords) :
    Nat.card {t : subW jWords // InOmega (t : Cr) ∧ InOmega ((t : Cr) * y)} = nA (crMat y) := by
  have e := Nat.card_congr (Equiv.subtypeEquivRight
    (p := fun t : subW jWords => InOmega (t : Cr) ∧ InOmega ((t : Cr) * y))
    (q := fun t : subW jWords => ClsA (crMat (t : Cr)) ∧ ClsA (crMat (t : Cr) * crMat (y : Cr)))
    fun t => by rw [inOmega_iff_clsA, inOmega_iff_clsA, map_mul])
  exact e.trans (card_subW_crMat jWords_lt42 fun x => ClsA x ∧ ClsA (x * crMat (y : Cr)))

theorem card_pairs_omega (y : subW jWords) (hy : InOmega (y : Cr)) :
    Nat.card {t : subW jWords // InOmega (t : Cr) ∧ InOmega ((t : Cr) * y)} = 0 := by
  rw [card_pairs]
  exact jOrbitFacts_cert.nA_A _ (mem_J_iff_crMat.1 y.2) ((inOmega_iff_clsA _).1 hy)

theorem card_pairs_one_three_five (y : subW jWords)
    (hy : IsConj (rep 1) (y : Cr) ∨ IsConj (rep 3) (y : Cr) ∨ IsConj (rep 5) (y : Cr)) :
    Nat.card {t : subW jWords // InOmega (t : Cr) ∧ InOmega ((t : Cr) * y)} = 14 := by
  rw [card_pairs]
  exact jOrbitFacts_cert.nA_B _ (mem_J_iff_crMat.1 y.2) ((clsB_iff _).2 hy)

theorem card_pairs_four_six_eight (y : subW jWords)
    (hy : IsConj (rep 4) (y : Cr) ∨ IsConj (rep 6) (y : Cr) ∨ IsConj (rep 8) (y : Cr)) :
    Nat.card {t : subW jWords // InOmega (t : Cr) ∧ InOmega ((t : Cr) * y)} = 2 := by
  rw [card_pairs]
  exact jOrbitFacts_cert.nA_C _ (mem_J_iff_crMat.1 y.2) ((clsC_iff _).2 hy)

theorem exists_normalizer_conj_of_mem_J {x y : Cr} (hx : x ∈ subW jWords)
    (hy : y ∈ subW jWords) (hxy : IsConj x y) :
    ∃ m ∈ Subgroup.normalizer (subW jWords : Set Cr), m * x * m⁻¹ = y := by
  obtain ⟨g, rfl⟩ := isConj_iff.1 hxy
  set C : Subgroup Cr := Subgroup.centralizer {g * x * g⁻¹}
  set J₂ : Subgroup Cr := (subW jWords).map (MulAut.conj g).toMonoidHom
  have hJC : subW jWords ≤ C := fun j hj =>
    Subgroup.mem_centralizer_singleton_iff.2 (elemTwo_J.2 j hj _ hy)
  have hJ₂C : J₂ ≤ C := by
    rintro _ ⟨j, hj, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have := elemTwo_J.2 j hj x hx
    calc g * j * g⁻¹ * (g * x * g⁻¹) = g * (j * x) * g⁻¹ := by group
      _ = g * (x * j) * g⁻¹ := by rw [this]
      _ = g * x * g⁻¹ * (g * j * g⁻¹) := by group
  have hp : ∀ A : Subgroup Cr, ElemTwo A → IsPGroup 2 A := fun A hA a =>
    ⟨1, by rw [pow_one, sq]; exact Subtype.ext (hA.1 _ a.2)⟩
  have hp₁ : IsPGroup 2 ((subW jWords).subgroupOf C) :=
    ((hp _ elemTwo_J).comap_of_injective C.subtype C.subtype_injective)
  have hp₂ : IsPGroup 2 (J₂.subgroupOf C) :=
    ((hp _ (elemTwo_J.conj g)).comap_of_injective C.subtype C.subtype_injective)
  obtain ⟨P, hP⟩ := hp₁.exists_le_sylow
  obtain ⟨Q, hQ⟩ := hp₂.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C Q P
  have hcJ₂ : ∀ j ∈ J₂, (c : Cr) * j * (c : Cr)⁻¹ ∈ (P : Subgroup C).map C.subtype := by
    intro j hj
    have hjQ : (⟨j, hJ₂C hj⟩ : C) ∈ (Q : Subgroup C) := hQ (Subgroup.mem_subgroupOf.2 hj)
    have : c * ⟨j, hJ₂C hj⟩ * c⁻¹ ∈ (P : Subgroup C) := by
      rw [← hc, Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul _ (MulAut.conj c) _ hjQ
    exact ⟨_, this, rfl⟩
  have hPp : IsPGroup 2 ((P : Subgroup C).map C.subtype) := P.isPGroup'.map C.subtype
  obtain ⟨R, hR⟩ := hPp.exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq Cr R sylT
  have hRT : ∀ w ∈ (R : Subgroup Cr), k * w * k⁻¹ ∈ subW sylWords := by
    intro w hw
    rw [← coe_sylT, ← hk, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul w (MulAut.conj k) _ hw
  have hcard : ∀ h : Cr, Nat.card ((subW jWords).map (MulAut.conj h).toMonoidHom) = 1024 :=
    fun h => by rw [Subgroup.card_map_of_injective (MulAut.conj h).injective, card_J]
  have h1 : (subW jWords).map (MulAut.conj k).toMonoidHom = subW jWords := by
    apply eq_J_of_elemTwo _ (elemTwo_J.conj k) (hcard k)
    rintro _ ⟨j, hj, rfl⟩
    exact hRT j (hR ⟨⟨j, hJC hj⟩, hP (Subgroup.mem_subgroupOf.2 hj), rfl⟩)
  have h2 : (subW jWords).map (MulAut.conj (k * c * g)).toMonoidHom = subW jWords := by
    apply eq_J_of_elemTwo _ (elemTwo_J.conj _) (hcard _)
    rintro _ ⟨j, hj, rfl⟩
    have hmem := hcJ₂ (g * j * g⁻¹) ⟨j, hj, rfl⟩
    have := hRT _ (hR hmem)
    simpa [MulAut.conj_apply, mul_assoc] using this
  refine ⟨c * g, mem_normalizer_of_map_eq ?_, ?_⟩
  · have e1 : (c : Cr) * g = k⁻¹ * (k * c * g) := by group
    have e2 : (subW jWords).map (MulAut.conj ((c : Cr) * g)).toMonoidHom =
        ((subW jWords).map (MulAut.conj (k * c * g)).toMonoidHom).map
          (MulAut.conj k⁻¹).toMonoidHom := by
      rw [map_conj_mul, ← e1]
    have e3 : ((subW jWords).map (MulAut.conj k).toMonoidHom).map
        (MulAut.conj k⁻¹).toMonoidHom = subW jWords := by
      rw [map_conj_mul, inv_mul_cancel]
      ext w
      simp
    rw [e2, h2]
    rw [h1] at e3
    exact e3
  · have hcx : (c : Cr) * (g * x * g⁻¹) = (g * x * g⁻¹) * c :=
      Subgroup.mem_centralizer_singleton_iff.1 c.2
    calc (c : Cr) * g * x * ((c : Cr) * g)⁻¹ = (c : Cr) * (g * x * g⁻¹) * (c : Cr)⁻¹ := by
          group
      _ = g * x * g⁻¹ := by rw [hcx, mul_inv_cancel_right]

end CFSG.RankThree.Co2
