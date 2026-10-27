module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3SFano
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3YBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

namespace GoldHyp3

variable (h : GoldHyp3 A B z V)

include h

theorem false_of_label_product {a1 a2 a3 a4 a5 b : CosetGeom (A ⊔ B) A B} (h2 : vtype a2 = false)
    (h4 : vtype a4 = false) (h12 : (graph (A ⊔ B) A B).Adj a2 a1)
    (h32 : (graph (A ⊔ B) A B).Adj a2 a3) (hb2 : (graph (A ⊔ B) A B).Adj a2 b)
    (h34 : (graph (A ⊔ B) A B).Adj a4 a3) (h54 : (graph (A ⊔ B) A B).Adj a4 a5) (n1b : a1 ≠ b)
    (n13 : a1 ≠ a3) (nb3 : b ≠ a3) (n35 : a3 ≠ a5) {c c' : D} (hc : c ∈ Zv z a1)
    (hc' : c' ∈ Zv z b) (hc1 : c ≠ 1) (hc1' : c' ≠ 1) (hs : c * c' ∈ Zv z a5) : False := by
  have t1 : vtype a1 = true := vtype_eq_true_of_adj h12 h2
  have tb : vtype b = true := vtype_eq_true_of_adj hb2 h2
  have t3 : vtype a3 = true := vtype_eq_true_of_adj h32 h2
  have t5 : vtype a5 = true := vtype_eq_true_of_adj h54 h4
  have hmem : c * c' ∈ Zv z a3 := h.mul_mem_Zv_third h2 h12 hb2 h32 n1b n13 nb3 hc hc' hc1 hc1'
  have hs1 : c * c' ≠ 1 := by
    intro e
    have hinv : c' = c⁻¹ := eq_inv_of_mul_eq_one_right e
    have hc'a : c' ∈ Zv z a1 := by
      rw [hinv]
      exact (Zv z a1).inv_mem hc
    exact n1b (h.eq_of_Zv_eq h2 h12 hb2 (h.Zv_eq_of_mem t1 tb hc'a hc' hc1'))
  exact n35 (h.eq_of_Zv_eq h4 h34 h54 (h.Zv_eq_of_mem t3 t5 hmem hs hs1))

theorem conj_pair_mul {a1 a1' a2 : CosetGeom (A ⊔ B) A B} (h2 : vtype a2 = false)
    (h12 : (graph (A ⊔ B) A B).Adj a2 a1) (h12' : (graph (A ⊔ B) A B).Adj a2 a1') {c c' : D}
    (hc : IsPair z V a1 a2 c) (hc' : IsPair z V a1' a2 c') {q : D} (hq : q ∈ ballStab 1 a2) :
    ∃ ε ∈ Vv V a2, q * (c * c') * q⁻¹ = ε * (c * c') := by
  have t1 : vtype a1 = true := vtype_eq_true_of_adj h12 h2
  have t1' : vtype a1' = true := vtype_eq_true_of_adj h12' h2
  have hq2 : q ∈ stab a2 := ballStab_le_stab 1 _ hq
  have hd : ∀ a, (graph (A ⊔ B) A B).Adj a2 a → q ∈ stab a := fun a ha =>
    ballStab_le_stab_of_dist_le (n := 1) (dist_eq_one_iff_adj.mpr ha).le hq
  let kq : ↥(A ⊔ B) := ⟨q, stab_le a2 hq2⟩
  have hk2 : kq • a2 = a2 := smul_eq_of_mem_stab hq2
  have hk1 : kq • a1 = a1 := smul_eq_of_mem_stab (hd a1 h12)
  have hk1' : kq • a1' = a1' := smul_eq_of_mem_stab (hd a1' h12')
  have p1 : IsPair z V a1 a2 (q * c * q⁻¹) := h.isPair_conj_fix hk1 hk2 hc
  have p1' : IsPair z V a1' a2 (q * c' * q⁻¹) := h.isPair_conj_fix hk1' hk2 hc'
  have hε1 : q * c * q⁻¹ * c⁻¹ ∈ Zv z a1 := h.isPair_mul_mem_Zv t1 h12.symm p1 hc.inv
  have hε3 : q * c' * q⁻¹ * c'⁻¹ ∈ Zv z a1' := h.isPair_mul_mem_Zv t1' h12'.symm p1' hc'.inv
  have hV1 : q * c * q⁻¹ * c⁻¹ ∈ Vv V a2 := h.Zv_le_Vv h12 h2 hε1
  have hV3 : q * c' * q⁻¹ * c'⁻¹ ∈ Vv V a2 := h.Zv_le_Vv h12' h2 hε3
  have hab := h.elemAbelian_Vv_B t1
  have hcV : c ∈ Vv V a1 := isPair_mem_Vv t1 hc
  have hc3 : (q * c' * q⁻¹ * c'⁻¹) * c = c * (q * c' * q⁻¹ * c'⁻¹) :=
    isElemAbelian_comm hab (Vv_le_Vv_of_adj h12 h2 hV3) hcV
  refine ⟨(q * c * q⁻¹ * c⁻¹) * (q * c' * q⁻¹ * c'⁻¹), (Vv V a2).mul_mem hV1 hV3, ?_⟩
  calc q * (c * c') * q⁻¹ = (q * c * q⁻¹ * c⁻¹ * c) * (q * c' * q⁻¹ * c'⁻¹ * c') := by group
    _ = (q * c * q⁻¹ * c⁻¹) * (c * (q * c' * q⁻¹ * c'⁻¹)) * c' := by group
    _ = (q * c * q⁻¹ * c⁻¹) * ((q * c' * q⁻¹ * c'⁻¹) * c) * c' := by rw [hc3]
    _ = (q * c * q⁻¹ * c⁻¹) * (q * c' * q⁻¹ * c'⁻¹) * (c * c') := by group

end GoldHyp3

end GoldAmL3

end F6

end CFSG.Quasithin
