module

public import CFSG.Quasithin.H13.VolIAltCover

public section

namespace CFSG.Quasithin.H13.VolI

open CFSG.Quasithin Subgroup

variable {W : Type*} [CommGroup W]

theorem eq_one_of_comm_fixed_odd (hW2 : ∀ w : W, w ^ 2 = 1) {t : MulAut W} {k : ℕ}
    (hk : Odd k) (htk : t ^ k = 1) (w : W) (hfix : t (t w * w⁻¹) = t w * w⁻¹) :
    t w * w⁻¹ = 1 := by
  set c := t w * w⁻¹ with hc
  have h1 : t w = c * w := by rw [hc]; group
  have hj : ∀ j : ℕ, (t ^ j) w = c ^ j * w := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hfix, h1, ← mul_assoc, ← pow_succ]
  have hk' := hj k
  rw [htk, MulAut.one_apply] at hk'
  have hck : c ^ k = 1 := mul_right_cancel (hk'.symm.trans (one_mul w).symm)
  obtain ⟨m, rfl⟩ := hk
  rw [pow_succ, pow_mul, hW2, one_pow, one_mul] at hck
  exact hck

theorem eq_bot_of_invariant_complement {H : Subgroup (MulAut W)} {Y Z : Subgroup W}
    (hZ : Z ≤ fixV H) (hcomm : commV H = ⊤) (hY : ∀ h ∈ H, ∀ y ∈ Y, h y ∈ Y)
    (hsup : ∀ w, ∃ y ∈ Y, ∃ z ∈ Z, w = y * z) (hinf : Y ⊓ Z = ⊥) : Z = ⊥ := by
  have hYtop : Y = ⊤ := by
    rw [eq_top_iff, ← hcomm]
    refine (closure_le _).2 ?_
    rintro _ ⟨h, hh, w, rfl⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := hsup w
    have e : h (y * z) * (y * z)⁻¹ = h y * y⁻¹ := by
      rw [map_mul, hZ hz h hh]
      group
    rw [e]
    exact mul_mem (hY h hh y hy) (inv_mem hy)
  rwa [hYtop, top_inf_eq] at hinf

theorem commMap_range_inv {t h : MulAut W} (hht : h * t = t * h) {y : W}
    (hy : y ∈ (commMap t).range) : h y ∈ (commMap t).range := by
  obtain ⟨w, rfl⟩ := hy
  refine ⟨h w, ?_⟩
  rw [commMap_apply, commMap_apply, map_mul, map_inv, ← MulAut.mul_apply, ← hht,
    MulAut.mul_apply]

theorem commMap_range_complement [Finite W] (hW2 : ∀ w : W, w ^ 2 = 1) {H : Subgroup (MulAut W)}
    {Z : Subgroup W} (hZ : Z ≤ fixV H) {t : MulAut W} (htH : t ∈ H) {k : ℕ} (hk : Odd k)
    (htk : t ^ k = 1) (hfpf : ∀ w, t w = w → w ∈ Z) :
    (commMap t).range ⊓ Z = ⊥ ∧ (commMap t).range ⊔ Z = ⊤ ∧
      Nat.card Z * Nat.card (commMap t).range = Nat.card W := by
  have hker : (commMap t).ker = Z := by
    ext w
    rw [MonoidHom.mem_ker, commMap_apply, mul_inv_eq_one]
    exact ⟨hfpf w, fun hw => hZ hw t htH⟩
  have hinf : (commMap t).range ⊓ Z = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨⟨w, rfl⟩, hz⟩ := mem_inf.1 hy
    exact mem_bot.2 (eq_one_of_comm_fixed_odd hW2 hk htk w (hZ hz t htH))
  have hcard : Nat.card Z * Nat.card (commMap t).range = Nat.card W := by
    rw [← hker]
    exact card_ker_mul_card_range (commMap t)
  refine ⟨hinf, ?_, hcard⟩
  have hN : (commMap t).range ≤ normalizer (Z : Set W) := by
    rw [normalizer_eq_top]
    exact le_top
  have h := card_sup_mul_card_inf hN
  rw [hinf, card_bot, mul_one, mul_comm, hcard] at h
  exact eq_top_of_card_eq _ h

theorem exists_mul_of_sup_eq_top {Y Z : Subgroup W} (h : Y ⊔ Z = ⊤) (w : W) :
    ∃ y ∈ Y, ∃ z ∈ Z, w = y * z := by
  have hw : w ∈ Y ⊔ Z := h ▸ mem_top w
  obtain ⟨y, hy, z, hz, rfl⟩ := mem_sup.1 hw
  exact ⟨y, hy, z, hz, rfl⟩

theorem eq_bot_of_central_fpf [Finite W] (hW2 : ∀ w : W, w ^ 2 = 1) {H : Subgroup (MulAut W)}
    {Z : Subgroup W} (hZ : Z ≤ fixV H) (hcomm : commV H = ⊤) {t : MulAut W} (htH : t ∈ H)
    (htc : ∀ h ∈ H, h * t = t * h) {k : ℕ} (hk : Odd k) (htk : t ^ k = 1)
    (hfpf : ∀ w, t w = w → w ∈ Z) : Z = ⊥ := by
  obtain ⟨hinf, hsup, -⟩ := commMap_range_complement hW2 hZ htH hk htk hfpf
  exact eq_bot_of_invariant_complement hZ hcomm
    (fun h hh y hy => commMap_range_inv (htc h hh) hy) (exists_mul_of_sup_eq_top hsup) hinf

theorem eq_bot_of_two_fpf [Finite W] (hW2 : ∀ w : W, w ^ 2 = 1) {H : Subgroup (MulAut W)}
    {Z : Subgroup W} (hZ : Z ≤ fixV H) (hcomm : commV H = ⊤) {t₁ t₂ : MulAut W} (h₁H : t₁ ∈ H)
    (h₂H : t₂ ∈ H) (h₁₂ : t₁ * t₂ = t₂ * t₁) {k₁ k₂ : ℕ} (hk₁ : Odd k₁) (hk₂ : Odd k₂)
    (ht₁ : t₁ ^ k₁ = 1) (ht₂ : t₂ ^ k₂ = 1) (hfpf₁ : ∀ w, t₁ w = w → w ∈ Z)
    (hfpf₂ : ∀ w, t₂ w = w → w ∈ Z)
    (hgen : H ≤ closure {h | h * t₁ = t₁ * h ∨ h * t₂ = t₂ * h}) : Z = ⊥ := by
  obtain ⟨hinf₁, hsup₁, hc₁⟩ := commMap_range_complement hW2 hZ h₁H hk₁ ht₁ hfpf₁
  obtain ⟨-, -, hc₂⟩ := commMap_range_complement hW2 hZ h₂H hk₂ ht₂ hfpf₂
  have hle : (commMap t₂).range ≤ (commMap t₁).range := by
    rintro _ ⟨w, rfl⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := exists_mul_of_sup_eq_top hsup₁ w
    have e : commMap t₂ (y * z) = t₂ y * y⁻¹ := by
      rw [commMap_apply, map_mul, hZ hz t₂ h₂H]
      group
    rw [e]
    exact mul_mem (commMap_range_inv h₁₂.symm hy) (inv_mem hy)
  have hpos : 0 < Nat.card Z := Nat.card_pos
  have hcard : Nat.card (commMap t₂).range = Nat.card (commMap t₁).range :=
    Nat.eq_of_mul_eq_mul_left hpos (hc₂.trans hc₁.symm)
  have heq : (commMap t₂).range = (commMap t₁).range :=
    eq_of_le_of_card_ge hle hcard.symm.le
  have hinv : ∀ g ∈ closure {h : MulAut W | h * t₁ = t₁ * h ∨ h * t₂ = t₂ * h},
      ∀ y ∈ (commMap t₁).range, g y ∈ (commMap t₁).range ∧ g⁻¹ y ∈ (commMap t₁).range := by
    intro g hg
    induction hg using closure_induction with
    | mem h hh =>
      intro y hy
      have hinv' : ∀ c : MulAut W, c * h = h * c → c * h⁻¹ = h⁻¹ * c := fun c hc => by
        rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, ← hc, mul_assoc, mul_inv_cancel, mul_one]
      rcases hh with hh | hh
      · exact ⟨commMap_range_inv hh hy,
          commMap_range_inv (hinv' t₁ hh.symm).symm hy⟩
      · rw [← heq] at hy ⊢
        exact ⟨commMap_range_inv hh hy, commMap_range_inv (hinv' t₂ hh.symm).symm hy⟩
    | one => exact fun y hy => ⟨hy, by rwa [inv_one]⟩
    | mul a b _ _ ha hb =>
      intro y hy
      refine ⟨(ha _ (hb y hy).1).1, ?_⟩
      rw [mul_inv_rev, MulAut.mul_apply]
      exact (hb _ (ha y hy).2).2
    | inv a _ ha =>
      intro y hy
      exact ⟨(ha y hy).2, by rw [inv_inv]; exact (ha y hy).1⟩
  exact eq_bot_of_invariant_complement hZ hcomm (fun h hh y hy => (hinv h (hgen hh) y hy).1)
    (exists_mul_of_sup_eq_top hsup₁) hinf₁

end CFSG.Quasithin.H13.VolI
