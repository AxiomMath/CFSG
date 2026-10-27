module

public import CFSG.Walter.Ree.Thompson2.BaseGrp.Setup
public import CFSG.Walter.W67.JR.R123

public section

namespace CFSG.Walter.Ree.T2.BaseGrp

open CFSG.Walter.Ward

namespace Ctx

variable {G : Type} [Group G] [Finite G] {k : Type} [Field k] [CharP k 3] {σ : k ≃+* k}
variable (C : Ctx G k σ)

theorem five_lt_q : 5 < C.h.q := by
  obtain ⟨n, hn, hq⟩ := C.q_eq
  rw [hq]
  calc 5 < 3 ^ 3 := by norm_num
    _ ≤ 3 ^ (2 * n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

@[expose] noncomputable def jt₀ :
    JT.JTHyp G := C.h.toJRGroup.toJTHyp C.five_lt_q

theorem jt₀_p : C.jt₀.p = C.h.p := rfl

theorem jt₀_f : C.jt₀.f = C.h.f := rfl

include C in
theorem centralizer_sylow (S : Sylow 2 G) :
    Subgroup.centralizer ((S : Subgroup G) : Set G) = S :=
  (JT.lemma_2_1 C.jt₀ C.h.p_ne_two).2.2.2.1 S

include C in
theorem card_normalizer_sylow
    (S : Sylow 2 G) :
    Nat.card (Subgroup.normalizer ((S : Subgroup G) : Set G)) = 168 := by
  have hidx := ((JT.lemma_2_1 C.jt₀ C.h.p_ne_two).2.2.2.2.1 S).1
  rw [W67.JRGroup.card_normalizer_of_index hidx Subgroup.le_normalizer, C.h.card_sylow S]

theorem exists_conj_J :
    ∃ g : G, g * C.jt₀.t * g⁻¹ = C.J := by
  have h := (JT.lemma_2_1 C.jt₀ C.h.p_ne_two).2.2.1 C.jt₀.t C.J C.jt₀.orderOf_t C.orderOf_J
  exact isConj_iff.mp h

@[expose] noncomputable def jt :
    JT.JTHyp G := C.jt₀.conj (Classical.choose C.exists_conj_J)

theorem jt_t :
    C.jt.t = C.J := Classical.choose_spec C.exists_conj_J

theorem jt_p : C.jt.p = C.h.p := rfl

theorem jt_f : C.jt.f = C.h.f := rfl

theorem jt_q :
    C.jt.p ^ C.jt.f = C.h.q := rfl

@[expose] noncomputable def L :
    Subgroup G := C.jt.F

theorem L_le_centralizer :
    C.L ≤ Subgroup.centralizer ({C.J} : Set G) := by
  rw [← C.jt_t]; exact C.jt.le_centralizer

theorem J_not_mem_L : C.J ∉ C.L := by
  rw [← C.jt_t]; exact C.jt.t_not_mem

theorem commute_J_of_mem_L
    {x : G} (hx : x ∈ C.L) : x * C.J = C.J * x :=
  Subgroup.mem_centralizer_singleton_iff.mp (C.L_le_centralizer hx)

theorem mem_L_of_odd
    {x : G} (hx : x * C.J = C.J * x) (hodd : Odd (orderOf x)) : x ∈ C.L := by
  apply C.jt.mem_F_of_odd _ hodd
  rw [C.jt_t]
  exact Subgroup.mem_centralizer_singleton_iff.mpr hx

theorem q_mod_eight : C.h.q % 8 = 3 := by
  obtain ⟨n, -, hq⟩ := C.q_eq
  rw [hq, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

@[expose] noncomputable def Liso :
    C.L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2)
    (GaloisField C.h.p C.h.f) := C.jt.iso

theorem p_odd : Odd C.h.p := (Fact.out : C.h.p.Prime).odd_of_ne_two C.h.p_ne_two

theorem card_L :
    Nat.card C.L = C.h.q * (C.h.q ^ 2 - 1) / 2 :=
  W67.PSL2Sub.card_eq C.Liso C.p_odd C.h.f_pos

end Ctx

end CFSG.Walter.Ree.T2.BaseGrp
