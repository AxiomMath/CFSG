module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sigma3Off7

public section

namespace CFSG.Quasithin.Fan86.Sigma3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique.Setup

abbrev oL (H : Type*) [Group H] : Subgroup H := oddOrderSubgroup (⊤ : Subgroup H)

variable {H : Type*} [Group H] {S : Subgroup H} {x : H}

theorem orderOf_conj' (g y : H) : orderOf (g * y * g⁻¹) = orderOf y := by
  have := (MulAut.conj g).orderOf_eq y
  simpa [MulAut.conj_apply] using this

theorem odd_mem_oL {y : H} (hy : Odd (orderOf y)) : y ∈ oL H :=
  Subgroup.subset_closure ⟨Subgroup.mem_top y, hy⟩

theorem oL_normal : (oL H).Normal := by
  refine ⟨fun n hn g => ?_⟩
  induction hn using Subgroup.closure_induction with
  | mem y hy => exact odd_mem_oL (by rw [orderOf_conj']; exact hy.2)
  | one => simp
  | mul y z _ _ hy hz =>
    have : g * (y * z) * g⁻¹ = (g * y * g⁻¹) * (g * z * g⁻¹) := by group
    rw [this]
    exact (oL H).mul_mem hy hz
  | inv y _ hy =>
    have : g * y⁻¹ * g⁻¹ = (g * y * g⁻¹)⁻¹ := by group
    rw [this]
    exact (oL H).inv_mem hy

theorem nQ_le_oL (x : H) (hx : orderOf x = 3) : nQ H x ≤ oL H := by
  intro n hn
  obtain ⟨e, he, rfl⟩ := mem_nQ.1 hn
  have hinv : e⁻¹ = e := inv_eq_of_mul_eq_one_right (mem_oneCenter.1 he).2.1
  have h1 : e * (x * e * x⁻¹) = (e * x * e⁻¹) * x⁻¹ := by rw [hinv]; group
  rw [h1]
  refine (oL H).mul_mem (odd_mem_oL ?_) (odd_mem_oL ?_)
  · rw [orderOf_conj', hx]; decide
  · rw [orderOf_inv, hx]; decide

theorem comm_mem_oL (hx : orderOf x = 3) (q : H) : x * q * x⁻¹ * q⁻¹ ∈ oL H := by
  have : x * q * x⁻¹ * q⁻¹ = x * (q * x⁻¹ * q⁻¹) := by group
  rw [this]
  refine (oL H).mul_mem (odd_mem_oL ?_) (odd_mem_oL ?_)
  · rw [hx]; decide
  · rw [orderOf_conj', orderOf_inv, hx]; decide

variable [Finite H]

theorem Hyp3.oL_inf_Q (h : Hyp3 H S x) : oL H ⊓ oQ H = nQ H x := by
  refine (Subgroup.eq_of_le_of_card_ge (le_inf (nQ_le_oL x h.ord)
    ((nQ_le x).trans oneCenter_le)) ?_).symm
  obtain ⟨j, hj⟩ :=
    (IsPGroup.to_inf_right (oQ_two (H := H)) : IsPGroup 2 ↥(oL H ⊓ oQ H)).exists_card_eq
  have hdvd := Subgroup.card_dvd_of_le (inf_le_left : oL H ⊓ oQ H ≤ oL H)
  rw [hj, h.card_oddOrder] at hdvd
  have hj2 : j ≤ 2 := by
    by_contra hj3
    have h8 : 2 ^ 3 ∣ 2 ^ j := pow_dvd_pow 2 (by omega)
    have := h8.trans hdvd
    omega
  rw [hj, h.offender.1]
  calc 2 ^ j ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hj2
    _ = 4 := by norm_num

omit [Finite H] in
theorem conj_zpowers_self {w : H} (hw : w ∈ Subgroup.zpowers x) : x * w * x⁻¹ = w := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
  have := (Commute.self_zpow x m).eq
  rw [this]
  group

theorem Hyp3.oL_eq (h : Hyp3 H S x) : oL H = nQ H x ⊔ Subgroup.zpowers x := by
  have hx3 := mul_mul_eq_one_of_orderOf h.ord
  have hle : nQ H x ⊔ Subgroup.zpowers x ≤ oL H :=
    sup_le (nQ_le_oL x h.ord) (Subgroup.zpowers_le.2 (odd_mem_oL (by rw [h.ord]; decide)))
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [h.card_oddOrder]
  let f : ↥(nQ H x) × ↥(Subgroup.zpowers x) → ↥(nQ H x ⊔ Subgroup.zpowers x) := fun p =>
    ⟨(p.1 : H) * (p.2 : H), Subgroup.mul_mem_sup p.1.2 p.2.2⟩
  have hinj : Function.Injective f := by
    rintro ⟨n, k⟩ ⟨n', k'⟩ hf
    have hf' : (n : H) * k = n' * k' := congrArg Subtype.val hf
    have hmem : (n' : H)⁻¹ * n ∈ nQ H x := (nQ H x).mul_mem ((nQ H x).inv_mem n'.2) n.2
    have hk : (n' : H)⁻¹ * n = k' * (k : H)⁻¹ := by
      calc (n' : H)⁻¹ * n = (n' : H)⁻¹ * (n * k) * (k : H)⁻¹ := by group
        _ = (n' : H)⁻¹ * (n' * k') * (k : H)⁻¹ := by rw [hf']
        _ = k' * (k : H)⁻¹ := by group
    have hkx : (k' : H) * (k : H)⁻¹ ∈ Subgroup.zpowers x :=
      (Subgroup.zpowers x).mul_mem k'.2 ((Subgroup.zpowers x).inv_mem k.2)
    have h1 : (n' : H)⁻¹ * n = 1 := by
      refine nQ_fix hx3 hmem ?_
      rw [hk]
      exact conj_zpowers_self hkx
    have hnn : (n : H) = n' := by
      have := mul_eq_one_iff_eq_inv.1 h1
      simpa using this.symm
    have hkk : (k : H) = k' := by
      rw [hnn] at hf'
      exact mul_left_cancel hf'
    exact Prod.ext (Subtype.ext hnn) (Subtype.ext hkk)
  have := Nat.card_le_card_of_injective f hinj
  rw [Nat.card_prod, Nat.card_zpowers, h.ord, h.offender.1] at this
  simpa using this

end CFSG.Quasithin.Fan86.Sigma3
