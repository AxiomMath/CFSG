module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sigma3Off2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedChar
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.Quasithin.Fan86.Sigma3

open CFSG.Open

structure Hyp3 (H : Type*) [Group H] [Finite H] (S : Subgroup H) (x : H) : Prop where
  sig : Sig3 H S
  ord : orderOf x = 3
  nc : ¬ ∀ q ∈ oQ H, x * q = q * x
  no : ∀ K : Subgroup H, K ≤ S → (K.subgroupOf S).Characteristic → K.Normal → K = ⊥

variable {H : Type*} [Group H] [Finite H] {S : Subgroup H} {x : H}

theorem Sig3.S_ne_bot (h : Sig3 H S) : S ≠ ⊥ := by
  intro hS
  have h1 := h.card_S
  have h2 : Nat.card S = 1 := Subgroup.card_eq_one.2 hS
  have : 0 < Nat.card (oQ H) := Nat.card_pos
  omega

theorem Sig3.invCenterIn_ne_bot (h : Sig3 H S) : invCenterIn S ≠ ⊥ := by
  obtain ⟨z, hzc, hz2, hz1⟩ :=
    CFSG.QuasithinUnique.Setup.exists_involution_centerOf h.two h.S_ne_bot
  intro hbot
  have hz : z ∈ invCenterIn S := mem_invCenterIn.2 ⟨hzc.1, by rwa [← pow_two],
    fun s hs => (Subgroup.mem_centralizer_iff.1 hzc.2 s hs).symm⟩
  rw [hbot, Subgroup.mem_bot] at hz
  exact hz1 hz

theorem Hyp3.invCenterIn_le_oneCenter (h : Hyp3 H S x) : invCenterIn S ≤ oneCenter (oQ H) := by
  intro z hz
  obtain ⟨hzS, hz2, hzc⟩ := mem_invCenterIn.1 hz
  have hzQ : z ∈ oQ H := h.sig.central_mem_Q h.ord h.nc hzS hzc
  exact mem_oneCenter.2 ⟨hzQ, hz2, fun q hq => hzc q (h.sig.Q_le_S hq)⟩

theorem Hyp3.exists_moved (h : Hyp3 H S x) : ∃ e ∈ oneCenter (oQ H), x * e * x⁻¹ ≠ e := by
  by_contra hcon
  push Not at hcon
  have hnorm : (invCenterIn S).Normal := by
    refine normal_of_gen (mul_mul_eq_one_of_orderOf h.ord) (h.sig.gen h.ord) _ ?_ ?_
    · intro s hs k hk
      have hks := (mem_invCenterIn.1 hk).2.2 s hs
      have e : s * k * s⁻¹ = k := by rw [← hks]; group
      rw [e]
      exact hk
    · intro k hk
      rw [hcon k (h.invCenterIn_le_oneCenter hk)]
      exact hk
  exact h.sig.invCenterIn_ne_bot (h.no _ invCenterIn_le invCenterIn_char hnorm)

theorem Hyp3.nQ_ne_bot (h : Hyp3 H S x) : nQ H x ≠ ⊥ := by
  obtain ⟨e, he, hne⟩ := h.exists_moved
  intro hbot
  have hmem : e * (x * e * x⁻¹) ∈ nQ H x := mem_nQ.2 ⟨e, he, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  apply hne
  rw [eq_inv_of_mul_eq_one_right hmem]
  exact inv_eq_of_mul_eq_one_right (mem_oneCenter.1 he).2.1

omit [Finite H] in
theorem elem_comm {E : Subgroup H} (hE : IsElemAbelian 2 E) {a b : H} (ha : a ∈ E) (hb : b ∈ E) :
    a * b = b * a := CFSG.Open.IsElemAbelian.comm hE ha hb

omit [Finite H] in
theorem elem_mono {E F : Subgroup H} (hFE : F ≤ E) (hE : IsElemAbelian 2 E) :
    IsElemAbelian 2 F := CFSG.Open.IsElemAbelian.mono hE hFE

omit [Finite H] in
theorem oneCenter_elem (Q : Subgroup H) : IsElemAbelian 2 (oneCenter Q) :=
  ⟨⟨⟨fun a b => Subtype.ext (oneCenter_comm _ a.2 _ b.2)⟩⟩, fun y hy => by
    rw [pow_two]
    exact (mem_oneCenter.1 hy).2.1⟩

omit [Finite H] in
theorem nQ_elem (x : H) : IsElemAbelian 2 (nQ H x) := elem_mono (nQ_le x) (oneCenter_elem _)

end CFSG.Quasithin.Fan86.Sigma3
