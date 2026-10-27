module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowONLineDich
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowONLinePlus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.HardMathSupport.Dickson.I271 (SevenLine mem_zpowers_symm)

variable {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime] {w : X} {F : Subgroup X}

private theorem sevenLine_inv_mod_find_g_e (h : SevenLine p w F) {a : X}
    (ha : a ∈ F) (haw : a ∉ Subgroup.zpowers w) :
    ∃ g ∈ F, ∃ e ∈ Subgroup.zpowers w, e ≠ 1 ∧ g * a * g⁻¹ = a * e := by
  have hmove : ∃ g ∈ F, g * a ≠ a * g := by
    by_contra hall
    push Not at hall
    exact haw (h.center_le ha fun q hq => (hall q hq).symm)
  obtain ⟨g, hgF, hga⟩ := hmove
  obtain ⟨e, heZ, hge⟩ := h.comm_mem hgF ha
  refine ⟨g, hgF, e, heZ, ?_, hge⟩
  intro he
  apply hga
  calc g * a = (g * a * g⁻¹) * g := by group
    _ = a * g := by rw [hge, he, mul_one]

omit [Finite X] [Fact (Nat.Prime p)] in
private theorem sevenLine_inv_mod_pow_conj (h : SevenLine p w F) {a g e : X}
    (hgF : g ∈ F) (heZ : e ∈ Subgroup.zpowers w) (hge : g * a * g⁻¹ = a * e) :
    ∀ i : ℕ, g ^ i * a * (g ^ i)⁻¹ = a * e ^ i := by
  have he_comm : Commute e g := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 heZ
    rw [← hk]
    have hwg : Commute w g := h.comm_w hgF
    exact hwg.zpow_left k
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
    have hconj : g ^ i * e * (g ^ i)⁻¹ = e :=
      ((he_comm.pow_right i).symm).mul_inv_cancel
    calc g ^ (i + 1) * a * (g ^ (i + 1))⁻¹
        = g ^ i * (g * a * g⁻¹) * (g ^ i)⁻¹ := by rw [pow_succ]; group
      _ = g ^ i * (a * e) * (g ^ i)⁻¹ := by rw [hge]
      _ = (g ^ i * a * (g ^ i)⁻¹) * (g ^ i * e * (g ^ i)⁻¹) := by rw [← conj_mul]
      _ = (g ^ i * a * (g ^ i)⁻¹) * e := by rw [hconj]
      _ = (a * e ^ i) * e := by rw [ih]
      _ = a * e ^ (i + 1) := by rw [pow_succ]; group

omit [Finite X] in
private theorem sevenLine_inv_mod_sqrt (h : SevenLine p w F) (hp2 : p ≠ 2) {c : X}
    (hcZ : c ∈ Subgroup.zpowers w) :
    ∃ d ∈ Subgroup.zpowers w, d * d = c⁻¹ := by
  have hp := (Fact.out : p.Prime)
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hcp : c ^ p = 1 := sevenLine_zpowers_pow_eq_one h hcZ
  set d : X := c ^ (p / 2) with hd
  have hm : 2 * (p / 2) = p - 1 := by
    have := Nat.two_mul_div_two_add_one_of_odd hpodd
    omega
  have hcp1 : c ^ (p - 1) = c⁻¹ := by
    have h1 : c ^ (p - 1) * c = 1 := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hp.ne_zero), hcp]
    exact mul_eq_one_iff_eq_inv.1 h1
  refine ⟨d, ?_, ?_⟩
  · rw [hd]
    exact Subgroup.pow_mem (Subgroup.zpowers w) hcZ (p / 2)
  · calc d * d = c ^ (p / 2) * c ^ (p / 2) := by rw [hd]
      _ = c ^ (p / 2 + p / 2) := (pow_add c _ _).symm
      _ = c ^ (2 * (p / 2)) := by rw [two_mul]
      _ = c ^ (p - 1) := by rw [hm]
      _ = c⁻¹ := hcp1

omit [Finite X] [Fact (Nat.Prime p)] in
private theorem sevenLine_inv_mod_final (h : SevenLine p w F) {α : MulAut X} (hαw : α w = w)
    {a c d : X} (ha : a ∈ F) (hcZ : c ∈ Subgroup.zpowers w) (hdZ : d ∈ Subgroup.zpowers w)
    (hαa : α a = c * a⁻¹) (hd2 : d * d = c⁻¹) :
    α (a * d) = (a * d)⁻¹ := by
  have hca : Commute c a := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hcZ
    rw [← hk]
    have hwa : Commute w a := h.comm_w ha
    exact hwa.zpow_left k
  have hda : Commute d a := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hdZ
    rw [← hk]
    have hwa : Commute w a := h.comm_w ha
    exact hwa.zpow_left k
  have hαd : α d = d := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hdZ
    rw [← hk, map_zpow, hαw]
  have hcd : c * d = d⁻¹ := by
    have h : c * d * d = 1 := by rw [mul_assoc, hd2]; group
    exact mul_eq_one_iff_eq_inv.1 h
  calc α (a * d) = α a * α d := by rw [map_mul]
    _ = (c * a⁻¹) * d := by rw [hαa, hαd]
    _ = a⁻¹ * (c * d) := by rw [hca.inv_right.eq, mul_assoc]
    _ = a⁻¹ * d⁻¹ := by rw [hcd]
    _ = (a * d)⁻¹ := by rw [mul_inv_rev, (hda.symm).inv_inv.eq]

theorem sevenLine_exists_conj_inv_of_inv_mod (h : SevenLine p w F) (hp2 : p ≠ 2)
    {α : MulAut X} (hαw : α w = w) (hT : ∀ f ∈ F, α f * f ∈ Subgroup.zpowers w) {a : X}
    (ha : a ∈ F) (haw : a ∉ Subgroup.zpowers w) : ∃ f ∈ F, α (f * a * f⁻¹) = (f * a * f⁻¹)⁻¹ := by
  obtain ⟨g, hgF, e, heZ, he1, hge⟩ := sevenLine_inv_mod_find_g_e h ha haw
  have heord : orderOf e = p := orderOf_eq_prime (sevenLine_zpowers_pow_eq_one h heZ) he1
  have hleZ : Subgroup.zpowers w ≤ Subgroup.zpowers e :=
    Subgroup.zpowers_le.2 (mem_zpowers_symm heord h.orderOf_w heZ)
  set c : X := α a * a with hc
  have hcZ : c ∈ Subgroup.zpowers w := by rw [hc]; exact hT a ha
  have hαa : α a = c * a⁻¹ := by rw [hc]; group
  obtain ⟨d, hdZ, hd2⟩ := sevenLine_inv_mod_sqrt h hp2 hcZ
  have hiter := sevenLine_inv_mod_pow_conj h hgF heZ hge
  have hdeZ : d ∈ Subgroup.zpowers e := hleZ hdZ
  have hdj : ∃ j : ℕ, e ^ j = d := by
    have hdp : d ∈ Submonoid.powers e :=
      (IsOfFinOrder.mem_powers_iff_mem_zpowers (isOfFinOrder_of_finite e)).2 hdeZ
    exact (Submonoid.mem_powers_iff d e).1 hdp
  obtain ⟨j, hj⟩ := hdj
  refine ⟨g ^ j, Subgroup.pow_mem F hgF j, ?_⟩
  have hfj : g ^ j * a * (g ^ j)⁻¹ = a * d := by rw [hiter j, hj]
  rw [hfj]
  exact sevenLine_inv_mod_final h hαw ha hcZ hdZ hαa hd2

theorem sevenLine_fix_or_exists_conj_inv (h : SevenLine p w F) (hp2 : p ≠ 2) {α : MulAut X}
    (hα2 : α * α = 1) (hαw : α w = w) :
    (∀ c ∈ Subgroup.centralizer ({w} : Set X), α c = c) ∨
      ∀ a ∈ F, a ∉ Subgroup.zpowers w → ∃ f ∈ F, α (f * a * f⁻¹) = (f * a * f⁻¹)⁻¹ := by
  rcases sevenLine_fix_or_inv_mod h hp2 hα2 hαw with hT | hT
  · exact Or.inl (sevenLine_fix_of_fix_mod h hp2 hα2 hαw hT)
  · exact Or.inr fun a ha haw => sevenLine_exists_conj_inv_of_inv_mod h hp2 hαw hT ha haw

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
