module

public import CFSG.Walter.ReeOrder.JT.Section5A
public import CFSG.Walter.ReeOrder.JT.Section5
public import CFSG.Walter.ReeOrder.Ward.Order

public section

namespace CFSG.Walter.JT

open scoped IsMulCommutative Pointwise MatrixGroups
open CFSG

variable {G : Type} [Group G] [Finite G]

namespace JTHyp

variable (h : JTHyp G) (hp : h.p ≠ 2) (hp3 : h.p ≠ 3) (hS : SuzukiFourGroupTheorem)
  (hH : HuppertMetacyclicTheorem)
include hp hp3 hS hH

theorem nonempty_wardSetup
    [Fintype G] [Fintype (GaloisField h.p h.f)]
    [DecidableEq (GaloisField h.p h.f)] :
    Nonempty (Ward.WardSetup G PSL(2, GaloisField h.p h.f) h.q 1 false) := by
  have hq5 := h.lemma_4_6_c hp hp3 hS hH
  have hcard : Fintype.card (GaloisField h.p h.f) = h.q := by
    rw [Fintype.card_eq_nat_card, GaloisField.card h.p h.f h.f_pos]
    rfl
  have hchar : ringChar (GaloisField h.p h.f) ≠ 2 := by
    rw [ringChar.eq (GaloisField h.p h.f) h.p]
    exact hp
  have hq7 : 7 ≤ h.q := by
    have := h.twentyseven_le_q hp hp3 hS hH
    omega
  obtain ⟨W₀⟩ := Ward.wardLTable (GaloisField h.p h.f) h.q hcard hchar hq7 (Or.inr hq5)
  have he := h.wardSign_eq hp hp3 hS hH
  rw [he] at W₀
  obtain ⟨A, hA3, hAt, hAv, hASo, hAnc⟩ := h.exists_A hp hp3 hS hH W₀
  exact ⟨{
    W := W₀
    q_ge := h.twentyseven_le_q hp hp3 hS hH
    q_pow := ⟨h.p, h.f, Fact.out, rfl⟩
    J := h.t
    J_mul := h.t_mul_t
    J_ne := h.t_ne_one
    κ := h.κ
    κ_inj := h.κ_injective
    κ_comm := h.κ_comm
    J_not_mem := h.κ_ne_t
    centralizer := fun _ hg => h.centralizer_κ hg
    involution_conj := fun _ hx => h.isConj_t hp hx
    normalizer := fun hIV => absurd hIV (by decide)
    A := A
    orderOf_A := hA3
    A_J := hAt
    A_J' := hAv
    A_So := hASo
    A_not_comm := hAnc }⟩

theorem lemma_5_1 :
    ∃ f : ℕ, 0 < f ∧ Nat.card G = h.q ^ 3 * (h.q - 1) * f := by
  classical
  let _ : Fintype G := Fintype.ofFinite G
  let _ : Fintype (GaloisField h.p h.f) := Fintype.ofFinite _
  obtain ⟨S⟩ := h.nonempty_wardSetup hp hp3 hS hH
  obtain ⟨O⟩ := S.exists_Orbit
  have hcard := O.card_G
  have hf := O.f_pos
  have hq1 : 1 ≤ h.q := by
    have h5 := h.five_lt
    rw [← JTHyp.q_eq] at h5
    omega
  refine ⟨O.f.toNat, by omega, ?_⟩
  have : ((h.q ^ 3 * (h.q - 1) * O.f.toNat : ℕ) : ℤ) = (h.q : ℤ) ^ 3 * (h.q - 1) * O.f := by
    push_cast [Nat.cast_sub hq1, Int.toNat_of_nonneg hf.le]
    ring
  exact_mod_cast hcard.trans this.symm

theorem lemma51 :
    h.Lemma51 := fun _ => by
  obtain ⟨f, -, hf⟩ := h.lemma_5_1 hp hp3 hS hH
  exact ⟨f, hf⟩

end JTHyp

end CFSG.Walter.JT
