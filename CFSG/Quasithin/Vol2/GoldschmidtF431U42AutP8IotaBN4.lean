module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8IotaBN3
public import Mathlib.Data.Finset.Prod
public import Mathlib.Algebra.Group.Subgroup.Lattice

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

variable {Δ : Type*} [Group Δ] {B P P₁ P₂ : Subgroup Δ} {s t r : Δ} {us ut U : List Δ}

namespace BNPair

theorem mulP₁ (H : BNPair B P₁ P₂ s t us ut) {g x : Δ} (hg : g ∈ P₁)
    (hx : InCells B s t x) : InCells B s t (g * x) := by
  rcases H.r1.cos g hg with hB | ⟨v, hv, b, hb, hvb⟩
  · exact hx.lmul hB
  · have hgx : g * x = v⁻¹ * (s * (b * x)) := by
      calc g * x = v⁻¹ * (v * g) * x := by group
        _ = v⁻¹ * (s * b) * x := by rw [hvb]
        _ = v⁻¹ * (s * (b * x)) := by group
    rw [hgx]
    exact (H.mul_s (hx.lmul hb)).lmul (B.inv_mem (H.r1.U_mem v hv))

theorem mulP₂ (H : BNPair B P₁ P₂ s t us ut) {g x : Δ} (hg : g ∈ P₂)
    (hx : InCells B s t x) : InCells B s t (g * x) := by
  rcases H.r2.cos g hg with hB | ⟨v, hv, b, hb, hvb⟩
  · exact hx.lmul hB
  · have hgx : g * x = v⁻¹ * (t * (b * x)) := by
      calc g * x = v⁻¹ * (v * g) * x := by group
        _ = v⁻¹ * (t * b) * x := by rw [hvb]
        _ = v⁻¹ * (t * (b * x)) := by group
    rw [hgx]
    exact (H.mul_t (hx.lmul hb)).lmul (B.inv_mem (H.r2.U_mem v hv))

theorem closure_cells (H : BNPair B P₁ P₂ s t us ut) :
    ∀ x ∈ Subgroup.closure ((P₁ : Set Δ) ∪ (P₂ : Set Δ)), InCells B s t x := by
  have key : ∀ g ∈ Subgroup.closure ((P₁ : Set Δ) ∪ (P₂ : Set Δ)),
      (∀ y, InCells B s t y → InCells B s t (g * y)) ∧
        (∀ y, InCells B s t y → InCells B s t (g⁻¹ * y)) := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      rcases hg with hg | hg
      · exact ⟨fun y hy => H.mulP₁ hg hy, fun y hy => H.mulP₁ (P₁.inv_mem hg) hy⟩
      · exact ⟨fun y hy => H.mulP₂ hg hy, fun y hy => H.mulP₂ (P₂.inv_mem hg) hy⟩
    | one => exact ⟨fun y hy => by simpa using hy, fun y hy => by simpa using hy⟩
    | mul g h _ _ hg hh =>
      refine ⟨fun y hy => ?_, fun y hy => ?_⟩
      · simpa [mul_assoc] using hg.1 _ (hh.1 y hy)
      · simpa [mul_inv_rev, mul_assoc] using hh.2 _ (hg.2 y hy)
    | inv g _ hg => exact ⟨by simpa using hg.2, by simpa using hg.1⟩
  intro x hx
  simpa using (key x hx).1 1 (inCells_one B s t)

end BNPair

@[expose] noncomputable def rcons (U : List Δ) (r : Δ) (R : Finset Δ) : Finset Δ :=
  open scoped Classical in ((U.toFinset ×ˢ R).image fun p => p.1⁻¹ * r * p.2)

theorem card_rcons_le (U : List Δ) (r : Δ) (R : Finset Δ) :
    (rcons U r R).card ≤ U.length * R.card := by
  classical
  unfold rcons
  calc _ ≤ (U.toFinset ×ˢ R).card := Finset.card_image_le
    _ = U.toFinset.card * R.card := Finset.card_product _ _
    _ ≤ U.length * R.card := Nat.mul_le_mul_right _ (List.toFinset_card_le U)

theorem RankOne.cover_word (h : RankOne B P r U) {R : Finset Δ} {w : Δ}
    (hR : ∀ b ∈ B, ∀ b' ∈ B, ∃ r' ∈ R, ∃ b'' ∈ B, b * w * b' = r' * b'') :
    ∀ b ∈ B, ∀ b' ∈ B, ∃ r' ∈ rcons U r R, ∃ b'' ∈ B, b * (r * w) * b' = r' * b'' := by
  classical
  intro b hb b' hb'
  obtain ⟨u, hu, c, hc, hbc⟩ := h.cover hb B.one_mem
  obtain ⟨r', hr', b'', hb'', hcc⟩ := hR c hc b' hb'
  refine ⟨u⁻¹ * r * r', ?_, b'', hb'', ?_⟩
  · unfold rcons
    exact Finset.mem_image.2 ⟨(u, r'), Finset.mem_product.2 ⟨List.mem_toFinset.2 hu, hr'⟩, rfl⟩
  · calc b * (r * w) * b' = (b * r * 1) * (w * b') := by group
      _ = (u⁻¹ * r * c) * (w * b') := by rw [hbc]
      _ = u⁻¹ * r * (c * w * b') := by group
      _ = u⁻¹ * r * (r' * b'') := by rw [hcc]
      _ = (u⁻¹ * r * r') * b'' := by group

theorem rcons_le {U : List Δ} {r : Δ} {R : Finset Δ} {a b : ℕ} (hU : U.length ≤ a)
    (hR : R.card ≤ b) : (rcons U r R).card ≤ a * b :=
  (card_rcons_le U r R).trans (Nat.mul_le_mul hU hR)

namespace BNPair

theorem covering (H : BNPair B P₁ P₂ s t us ut) :
    ∃ R : Finset Δ, R.card ≤ 135 ∧
      ∀ x ∈ Subgroup.closure ((P₁ : Set Δ) ∪ (P₂ : Set Δ)), ∃ r ∈ R, r⁻¹ * x ∈ B := by
  classical
  set R0 : Finset Δ := {1} with hR0
  set Rs1 := rcons us s R0 with hRs1
  set Rt1 := rcons ut t R0 with hRt1
  set Rst := rcons us s Rt1 with hRst
  set Rts := rcons ut t Rs1 with hRts
  set Rsts := rcons us s Rts with hRsts
  set Rtst := rcons ut t Rst with hRtst
  set Rstst := rcons us s Rtst with hRstst
  have c0 : R0.card ≤ 1 := by simp [hR0]
  have c1 : Rs1.card ≤ 2 * 1 := rcons_le H.us_len c0
  have c2 : Rt1.card ≤ 4 * 1 := rcons_le H.ut_len c0
  have c3 : Rst.card ≤ 2 * (4 * 1) := rcons_le H.us_len c2
  have c4 : Rts.card ≤ 4 * (2 * 1) := rcons_le H.ut_len c1
  have c5 : Rsts.card ≤ 2 * (4 * (2 * 1)) := rcons_le H.us_len c4
  have c6 : Rtst.card ≤ 4 * (2 * (4 * 1)) := rcons_le H.ut_len c3
  have c7 : Rstst.card ≤ 2 * (4 * (2 * (4 * 1))) := rcons_le H.us_len c6
  have u1 := Finset.card_union_le R0 Rs1
  have u2 := Finset.card_union_le (R0 ∪ Rs1) Rt1
  have u3 := Finset.card_union_le (R0 ∪ Rs1 ∪ Rt1) Rst
  have u4 := Finset.card_union_le (R0 ∪ Rs1 ∪ Rt1 ∪ Rst) Rts
  have u5 := Finset.card_union_le (R0 ∪ Rs1 ∪ Rt1 ∪ Rst ∪ Rts) Rsts
  have u6 := Finset.card_union_le (R0 ∪ Rs1 ∪ Rt1 ∪ Rst ∪ Rts ∪ Rsts) Rtst
  have u7 := Finset.card_union_le (R0 ∪ Rs1 ∪ Rt1 ∪ Rst ∪ Rts ∪ Rsts ∪ Rtst) Rstst
  refine ⟨R0 ∪ Rs1 ∪ Rt1 ∪ Rst ∪ Rts ∪ Rsts ∪ Rtst ∪ Rstst, by omega, ?_⟩
  have b0 : ∀ b ∈ B, ∀ b' ∈ B, ∃ r' ∈ R0, ∃ b'' ∈ B, b * 1 * b' = r' * b'' :=
    fun b hb b' hb' => ⟨1, by simp [hR0], b * b', B.mul_mem hb hb', by group⟩
  have bs1 := H.r1.cover_word b0
  have bt1 := H.r2.cover_word b0
  have bst := H.r1.cover_word bt1
  have bts := H.r2.cover_word bs1
  have bsts := H.r1.cover_word bts
  have btst := H.r2.cover_word bst
  have bstst := H.r1.cover_word btst
  have key : ∀ (n : Δ) (R : Finset Δ), R ⊆ R0 ∪ Rs1 ∪ Rt1 ∪ Rst ∪ Rts ∪ Rsts ∪ Rtst ∪ Rstst →
      (∀ b ∈ B, ∀ b' ∈ B, ∃ r' ∈ R, ∃ b'' ∈ B, b * n * b' = r' * b'') →
      ∀ x, InCell B n x → ∃ r ∈ R0 ∪ Rs1 ∪ Rt1 ∪ Rst ∪ Rts ∪ Rsts ∪ Rtst ∪ Rstst,
        r⁻¹ * x ∈ B := by
    rintro n R hsub hn x ⟨b₁, h₁, b₂, h₂, rfl⟩
    obtain ⟨r', hr', b'', hb'', h⟩ := hn b₁ h₁ b₂ h₂
    refine ⟨r', hsub hr', ?_⟩
    rw [h]
    simpa using hb''
  have conv : ∀ (n m : Δ) (R : Finset Δ),
      (∀ b ∈ B, ∀ b' ∈ B, ∃ r' ∈ R, ∃ b'' ∈ B, b * m * b' = r' * b'') → n = m →
      (∀ b ∈ B, ∀ b' ∈ B, ∃ r' ∈ R, ∃ b'' ∈ B, b * n * b' = r' * b'') := by
    intro n m R h hnm
    subst hnm
    exact h
  intro x hx
  rcases H.closure_cells x hx with h | h | h | h | h | h | h | h
  · exact key 1 R0 (by intro y hy; simp only [Finset.mem_union, hy, true_or]) b0 x h
  · exact key s Rs1 (by intro y hy; simp only [Finset.mem_union, hy, true_or, or_true])
      (conv s (s * 1) Rs1 bs1 (by group)) x h
  · exact key t Rt1 (by intro y hy; simp only [Finset.mem_union, hy, true_or, or_true])
      (conv t (t * 1) Rt1 bt1 (by group)) x h
  · exact key (s * t) Rst (by intro y hy; simp only [Finset.mem_union, hy, true_or, or_true])
      (conv (s * t) (s * (t * 1)) Rst bst (by group)) x h
  · exact key (t * s) Rts (by intro y hy; simp only [Finset.mem_union, hy, true_or, or_true])
      (conv (t * s) (t * (s * 1)) Rts bts (by group)) x h
  · exact key (s * t * s) Rsts (by intro y hy; simp only [Finset.mem_union, hy, true_or, or_true])
      (conv (s * t * s) (s * (t * (s * 1))) Rsts bsts (by group)) x h
  · exact key (t * s * t) Rtst (by intro y hy; simp only [Finset.mem_union, hy, true_or, or_true])
      (conv (t * s * t) (t * (s * (t * 1))) Rtst btst (by group)) x h
  · exact key (s * t * s * t) Rstst (by intro y hy; simp only [Finset.mem_union, hy, or_true])
      (conv (s * t * s * t) (s * (t * (s * (t * 1)))) Rstst bstst (by group)) x h

end BNPair

end CFSG.Quasithin.H13.F431.U42Aut
