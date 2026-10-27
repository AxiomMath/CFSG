module

import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch11SecAKE8
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE.C10KH

open CFSG.Open CFSG.Blueprint

theorem nontrivial_of_card {V : Type*} [Group V] {k : ℕ} (h : Nat.card V = k) (hk : 1 < k) :
    Nontrivial V := by
  have : Finite V := Nat.finite_of_card_ne_zero (by omega)
  exact Finite.one_lt_card_iff_nontrivial.mp (by omega)

theorem nontrivial_of_equiv {V M : Type*} [Group V] [Group M] [Nontrivial M]
    (h : Nonempty (V ≃* M)) : Nontrivial V := by
  obtain ⟨e⟩ := h
  exact e.toEquiv.nontrivial

theorem nontrivial_of_isE2 {V : Type} [Group V] {n : ℕ} (hn : 1 ≤ n) (h : IsE2 n V) :
    Nontrivial V := by
  obtain ⟨e⟩ := (h : Nonempty (V ≃* Multiplicative (Fin n → ZMod 2)))
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact e.toEquiv.nontrivial

theorem nontrivial_of_isExtraspecial2 {V : Type} [Group V] {m : ℕ} (h : IsExtraspecial2 m V) :
    Nontrivial V :=
  nontrivial_of_card h.2 (Nat.one_lt_two_pow (by omega))

theorem nontrivial_of_isZ4StarExtra2 {V : Type} [Group V] (h : IsZ4StarExtra2 V) :
    Nontrivial V := by
  obtain ⟨Z, -, hZ, -⟩ := h
  have := nontrivial_of_card hZ (by norm_num)
  obtain ⟨a, b, hab⟩ := this
  exact ⟨⟨a, b, fun h => hab (Subtype.ext h)⟩⟩

theorem nontrivial_of_isZ4Cubed {V : Type} [Group V] (h : IsZ4Cubed V) : Nontrivial V := by
  have : Fact (1 < 4) := ⟨by norm_num⟩
  exact nontrivial_of_equiv (M := Multiplicative (Fin 3 → ZMod 4)) h

theorem nontrivial_of_isElemAbelianOfRank {V : Type} [Group V] {r : ℕ} (hr : r.Prime)
    (h : IsElemAbelianOfRank r 2 V) : Nontrivial V := by
  have : Fact (1 < r) := ⟨hr.one_lt⟩
  exact nontrivial_of_equiv (M := Multiplicative (Fin 2 → ZMod r)) h

theorem nontrivial_of_isAlt {Q : Type} [Group Q] {n : ℕ} (hn : 3 ≤ n) (h : IsAlt n Q) :
    Nontrivial Q := by
  obtain ⟨e⟩ := (h : Nonempty (Q ≃* alternatingGroup (Fin n)))
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  refine nontrivial_of_card ((Nat.card_congr e.toEquiv).trans (nat_card_alternatingGroup)) ?_
  rw [Nat.card_fin]
  have h6 : (3 : ℕ).factorial ≤ n.factorial := Nat.factorial_le hn
  rw [show (3 : ℕ).factorial = 6 from rfl] at h6
  omega

theorem nontrivial_of_isHat {Q S : Type} [Group Q] [Group S] (h : IsHat Q S) : Nontrivial Q :=
  CFSG.LocalCores.isQuasisimple_nontrivial h.1

theorem nontrivial_of_isPSL321 {Q : Type} [Group Q] (h : IsPSL 3 2 1 Q) : Nontrivial Q :=
  nontrivial_of_card (SecA.C10KH.card_of_isPSL_three_two_one h) (by norm_num)

theorem card_of_isPSL421 {Q : Type} [Group Q] (h : IsPSL 4 2 1 Q) : Nat.card Q = 20160 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_four_two h

theorem card_of_isPSL322 {Q : Type} [Group Q] (h : IsPSL 3 2 2 Q) : Nat.card Q = 20160 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_four h

theorem nontrivial_of_isPSL421 {Q : Type} [Group Q] (h : IsPSL 4 2 1 Q) : Nontrivial Q :=
  nontrivial_of_card (card_of_isPSL421 h) (by norm_num)

theorem nontrivial_of_isM24 {Q : Type} [Group Q]
    (h : IsSporadic .M24 Q) : Nontrivial Q := by
  obtain ⟨e⟩ := h
  exact nontrivial_of_card ((Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Mathieu.card_M24)
    (by norm_num)

theorem exists_center_ne_one_sl2 {q : ℕ} (hq : 2 < q) :
    ∃ z : Matrix.SpecialLinearGroup (Fin 2) (ZMod q),
      z ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod q)) ∧ z ≠ 1 := by
  let z : Matrix.SpecialLinearGroup (Fin 2) (ZMod q) :=
    ⟨-(1 : Matrix (Fin 2) (Fin 2) (ZMod q)), by
      rw [Matrix.det_neg, Matrix.det_one, Fintype.card_fin]; norm_num⟩
  refine ⟨z, ?_, ?_⟩
  · rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    change (g : Matrix (Fin 2) (Fin 2) (ZMod q)) * (-1) = (-1) * g
    simp
  · intro h
    have h1 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) (ZMod q) =>
      (A : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 0) h
    simp only [z, Matrix.SpecialLinearGroup.coe_one, Matrix.neg_apply, Matrix.one_apply_eq] at h1
    have : Fact (2 < q) := ⟨hq⟩
    exact ZMod.neg_one_ne_one h1

theorem nontrivial_of_isSL2 {Q : Type} [Group Q] {r : ℕ} (hr : 2 < r) (h : IsSL2 r Q) :
    Nontrivial Q := by
  obtain ⟨e⟩ := (h : Nonempty (Q ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod r)))
  obtain ⟨z, -, hz⟩ := exists_center_ne_one_sl2 hr
  have : Nontrivial (Matrix.SpecialLinearGroup (Fin 2) (ZMod r)) := ⟨⟨z, 1, hz⟩⟩
  exact e.toEquiv.nontrivial

theorem false_of_surj_sl2 {B : Type} [Group B] [IsSimpleGroup B] (hZ : Subgroup.center B = ⊥)
    {q : ℕ} (hq : 2 < q) (φ : B →* Matrix.SpecialLinearGroup (Fin 2) (ZMod q))
    (hφ : Function.Surjective φ) : False := by
  obtain ⟨z, hzc, hz1⟩ := exists_center_ne_one_sl2 hq
  obtain ⟨b, rfl⟩ := hφ z
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with hb | ht
  · have hinj := (MonoidHom.ker_eq_bot_iff φ).mp hb
    have hb1 : b ∈ Subgroup.center B := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply hinj
      rw [map_mul, map_mul]
      exact Subgroup.mem_center_iff.mp hzc (φ g)
    rw [hZ, Subgroup.mem_bot] at hb1
    exact hz1 (by rw [hb1, map_one])
  · exact hz1 ((MonoidHom.mem_ker).mp (ht ▸ Subgroup.mem_top b))

theorem surjective_of_sup_eq {C : Type*} [Group C] {B N : Subgroup C} [N.Normal]
    (h : B ⊔ N = ⊤) : Function.Surjective ((QuotientGroup.mk' N).comp B.subtype) := by
  intro q
  induction q using QuotientGroup.induction_on with
  | H x =>
  have hx : x ∈ ((B ⊔ N : Subgroup C) : Set C) := by rw [h]; exact Subgroup.mem_top x
  rw [Subgroup.mul_normal] at hx
  obtain ⟨b, hb, n, hn, rfl⟩ := hx
  refine ⟨⟨b, hb⟩, ?_⟩
  simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply]
  exact QuotientGroup.eq.mpr (by simpa using N.inv_mem hn)

end CFSG.Quasithin.Vol2.Ch11.SecE.C10KH
