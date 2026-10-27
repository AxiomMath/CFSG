module

public import CFSG.Quasithin.Background.D2Params
public import Mathlib.Data.Rat.Star

public section

namespace CFSG.Quasithin

variable {V : Type*} [CommGroup V]

theorem fixV_anti {X X' : Subgroup (MulAut V)} (h : X ≤ X') : fixV X' ≤ fixV X :=
  fun _ hv x hx => hv x (h hx)

theorem le_fixV_inf_centSub (U : Subgroup V) (A : Subgroup (MulAut V)) :
    U ≤ fixV (A ⊓ centSub U) := fun _ hu _ hg => hg.2 _ hu

theorem autSub_eq_bot_iff {A : Subgroup (MulAut V)} {U : Subgroup V} (hA : A ≤ stabSub U) :
    autSub A U = ⊥ ↔ commSub U A = ⊥ := by
  rw [commSub_eq_bot_iff]
  constructor
  · intro h u hu g hg
    have hmem : resHom U ⟨g, hA hg⟩ ∈ autSub A U := mem_autSub.mpr ⟨⟨g, hA hg⟩, hg, rfl⟩
    rw [h, Subgroup.mem_bot] at hmem
    exact congrArg (fun φ : MulAut U => ((φ ⟨u, hu⟩ : U) : V)) hmem
  · intro h
    refine (Subgroup.eq_bot_iff_forall _).mpr fun φ hφ => ?_
    obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hφ
    ext u
    exact h u.2 g hg

theorem IsA2.autSub {X A : Subgroup (MulAut V)} {U : Subgroup V} (h : IsA2 X A)
    (hA : A ≤ stabSub U) (hU : commSub U A ≠ ⊥) : IsA2 (autSub X U) (autSub A U) := by
  refine ⟨autSub_mono h.1 U, fun hbot => hU ((autSub_eq_bot_iff hA).mp hbot), ?_, ?_⟩
  · intro φ hφ ψ hψ
    obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hφ
    obtain ⟨k, hk, rfl⟩ := mem_autSub.mp hψ
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (h.2.2.1 _ hg _ hk)
  · intro φ hφ
    obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hφ
    rw [← map_pow]
    have : g ^ 2 = 1 := Subtype.ext (by simpa using h.2.2.2 _ hg)
    rw [this, map_one]

section Numerics

variable [Finite V]

theorem rk_autSub_add_rk_inf {A : Subgroup (MulAut V)} {U : Subgroup V} (hA : A ≤ stabSub U) :
    rk (autSub A U) + rk ↥(A ⊓ centSub U) = rk A := by
  have := card_autSub_mul hA
  unfold rk
  rw [← padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne', this]

theorem rkIdx_autSub_add {A : Subgroup (MulAut V)} {U : Subgroup V} (hA : A ≤ stabSub U) :
    rkIdx (fixV (autSub A U)) + rk ↥(U ⊓ fixV A) = rk U := by
  have := rk_add_rkIdx (fixV (autSub A U))
  rw [rk_fixV_autSub hA] at this
  omega

theorem rkIdx_add_le (hV : ∀ v : V, v ^ 2 = 1) {A : Subgroup (MulAut V)} {U : Subgroup V}
    (hA : A ≤ stabSub U) :
    rkIdx (fixV (A ⊓ centSub U)) + rkIdx (fixV (autSub A U)) ≤ rkIdx (fixV A) ∧
    (rkIdx (fixV (A ⊓ centSub U)) + rkIdx (fixV (autSub A U)) = rkIdx (fixV A) →
      fixV (A ⊓ centSub U) = U ⊔ fixV A) := by
  have hW : U ⊔ fixV A ≤ fixV (A ⊓ centSub U) :=
    sup_le (le_fixV_inf_centSub U A) (fixV_anti inf_le_left)
  have h1 := rk_sup_add_rk_inf U (fixV A)
  have h2 := rkIdx_autSub_add hA
  have h3 := rk_add_rkIdx (fixV A)
  have h4 := rk_add_rkIdx (fixV (A ⊓ centSub U))
  have h5 := rk_mono hW
  refine ⟨by omega, fun h => ?_⟩
  exact (eq_of_le_of_rk_le hV hW (by omega)).symm

end Numerics

section D22

variable [Finite V]

theorem D2_2 (hV : ∀ v : V, v ^ 2 = 1) {X A : Subgroup (MulAut V)} {r : ℚ}
    (hAr : A ∈ Rle X r) {U : Subgroup V} (hU : A ≤ stabSub U) (hUA : commSub U A ≠ ⊥) :
    (∃ ε : ℚ, 0 < ε ∧ autSub A U ∈ Rle (autSub X U) (r - ε)) ∨
    (∃ ε : ℚ, 0 < ε ∧ A ⊓ centSub U ∈ Rle X (r - ε)) ∨
    (A ⊓ centSub U = ⊥ ∧ rAV A = rAV (autSub A U) ∧ U ⊔ fixV A = ⊤) ∨
    (A ∈ Req X r ∧ autSub A U ∈ Req (autSub X U) r ∧ A ⊓ centSub U ∈ Req X r ∧
      fixV (A ⊓ centSub U) = U ⊔ fixV A) := by
  obtain ⟨hA2, hrA⟩ := hAr
  have hAU : IsA2 (autSub X U) (autSub A U) := hA2.autSub hU hUA
  have h1 := rk_autSub_add_rk_inf hU
  obtain ⟨hineq, hinj⟩ := rkIdx_add_le hV hU
  have hγ : 0 < rk (autSub A U) := hAU.rk_pos
  have hα : 0 < rk A := hA2.rk_pos
  have hAm := hA2.rAV_mul
  have hAUm := hAU.rAV_mul
  have h2 := rkIdx_autSub_add hU
  have h3 := rk_add_rkIdx (fixV A)
  have h5 := rk_sup_add_rk_inf U (fixV A)
  by_cases hB : A ⊓ centSub U = ⊥
  · have hβ : rk ↥(A ⊓ centSub U) = 0 := by rw [hB]; exact rk_bot
    have hαγ : rk (autSub A U) = rk A := by omega
    by_cases hW : U ⊔ fixV A = ⊤
    · refine Or.inr (Or.inr (Or.inl ⟨hB, ?_, hW⟩))
      have hrW : rk ↥(U ⊔ fixV A) = rk V := by rw [hW]; exact rk_top
      have hua : rkIdx (fixV (autSub A U)) = rkIdx (fixV A) := by omega
      unfold rAV
      rw [hαγ, hua]
    · have hrW : rk ↥(U ⊔ fixV A) < rk V := by
        have hle : rk ↥(U ⊔ fixV A) ≤ rk V := by
          have := rk_mono (le_top : U ⊔ fixV A ≤ ⊤)
          rwa [rk_top] at this
        rcases hle.lt_or_eq with hlt | heq
        · exact hlt
        · exfalso
          apply hW
          refine eq_of_le_of_rk_le hV le_top ?_
          rw [rk_top]
          omega
      have hua : rkIdx (fixV (autSub A U)) < rkIdx (fixV A) := by omega
      refine Or.inl ⟨r - rAV (autSub A U), ?_, hAU, ?_⟩
      · have : rAV (autSub A U) < rAV A := by
          unfold rAV
          rw [hαγ]
          exact div_lt_div_of_pos_right (by exact_mod_cast hua) (by exact_mod_cast hα)
        linarith
      · linarith
  · have hB2 : IsA2 X (A ⊓ centSub U) := hA2.mono inf_le_left hB
    have hβ : 0 < rk ↥(A ⊓ centSub U) := hB2.rk_pos
    have hBm := hB2.rAV_mul
    by_cases h1' : rAV (autSub A U) < r
    · exact Or.inl ⟨r - rAV (autSub A U), by linarith, hAU, by linarith⟩
    by_cases h2' : rAV (A ⊓ centSub U) < r
    · exact Or.inr (Or.inl ⟨r - rAV (A ⊓ centSub U), by linarith, hB2, by linarith⟩)
    have hr1 : r ≤ rAV (autSub A U) := not_lt.mp h1'
    have hr2 : r ≤ rAV (A ⊓ centSub U) := not_lt.mp h2'
    have hαc : (rk A : ℚ) = rk (autSub A U) + rk ↥(A ⊓ centSub U) := by exact_mod_cast h1.symm
    have hin : (rkIdx (fixV (A ⊓ centSub U)) : ℚ) + rkIdx (fixV (autSub A U)) ≤ rkIdx (fixV A) := by
      exact_mod_cast hineq
    have hγpos : (0 : ℚ) < rk (autSub A U) := by exact_mod_cast hγ
    have hβpos : (0 : ℚ) < rk ↥(A ⊓ centSub U) := by exact_mod_cast hβ
    have hαpos : (0 : ℚ) < rk A := by exact_mod_cast hα
    have ha : (rkIdx (fixV A) : ℚ) = r * rk A := by
      have e1 : rAV A * rk A ≤ r * rk A := mul_le_mul_of_nonneg_right hrA hαpos.le
      have e2 : r * rk (autSub A U) ≤ rAV (autSub A U) * rk (autSub A U) :=
        mul_le_mul_of_nonneg_right hr1 hγpos.le
      have e3 : r * rk ↥(A ⊓ centSub U) ≤ rAV (A ⊓ centSub U) * rk ↥(A ⊓ centSub U) :=
        mul_le_mul_of_nonneg_right hr2 hβpos.le
      nlinarith
    have hb : (rkIdx (fixV (A ⊓ centSub U)) : ℚ) = r * rk ↥(A ⊓ centSub U) := by
      have e1 : rAV A * rk A ≤ r * rk A := mul_le_mul_of_nonneg_right hrA hαpos.le
      have e2 : r * rk (autSub A U) ≤ rAV (autSub A U) * rk (autSub A U) :=
        mul_le_mul_of_nonneg_right hr1 hγpos.le
      have e3 : r * rk ↥(A ⊓ centSub U) ≤ rAV (A ⊓ centSub U) * rk ↥(A ⊓ centSub U) :=
        mul_le_mul_of_nonneg_right hr2 hβpos.le
      nlinarith
    have hu : (rkIdx (fixV (autSub A U)) : ℚ) = r * rk (autSub A U) := by
      have e1 : rAV A * rk A ≤ r * rk A := mul_le_mul_of_nonneg_right hrA hαpos.le
      have e2 : r * rk (autSub A U) ≤ rAV (autSub A U) * rk (autSub A U) :=
        mul_le_mul_of_nonneg_right hr1 hγpos.le
      have e3 : r * rk ↥(A ⊓ centSub U) ≤ rAV (A ⊓ centSub U) * rk ↥(A ⊓ centSub U) :=
        mul_le_mul_of_nonneg_right hr2 hβpos.le
      nlinarith
    have hsum : rkIdx (fixV (A ⊓ centSub U)) + rkIdx (fixV (autSub A U)) = rkIdx (fixV A) := by
      have : (rkIdx (fixV (A ⊓ centSub U)) : ℚ) + rkIdx (fixV (autSub A U)) =
          rkIdx (fixV A) := by rw [ha, hb, hu, hαc]; ring
      exact_mod_cast this
    have e1 : rAV A = r := by
      have := hA2.rAV_mul
      rw [ha] at this
      exact mul_right_cancel₀ hαpos.ne' this
    have e2 : rAV (autSub A U) = r := by
      rw [hu] at hAUm
      exact mul_right_cancel₀ hγpos.ne' hAUm
    have e3 : rAV (A ⊓ centSub U) = r := by
      rw [hb] at hBm
      exact mul_right_cancel₀ hβpos.ne' hBm
    exact Or.inr (Or.inr (Or.inr ⟨⟨hA2, e1⟩, ⟨hAU, e2⟩, ⟨hB2, e3⟩, hinj hsum⟩))

end D22

theorem map_commSub_autSub {A : Subgroup (MulAut V)} {U : Subgroup V} (hA : A ≤ stabSub U)
    (W : Subgroup U) :
    (commSub W (autSub A U)).map U.subtype = commSub (W.map U.subtype) A := by
  unfold commSub
  rw [MonoidHom.map_closure]
  congr 1
  ext c
  constructor
  · rintro ⟨_, ⟨φ, hφ, w, hw, rfl⟩, rfl⟩
    obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hφ
    exact ⟨g, hg, w.1, ⟨w, hw, rfl⟩, rfl⟩
  · rintro ⟨g, hg, _, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨_, ⟨resHom U ⟨g, hA hg⟩, mem_autSub.mpr ⟨⟨g, hA hg⟩, hg, rfl⟩, w, hw, rfl⟩, rfl⟩

theorem map_commIter_autSub {A : Subgroup (MulAut V)} {U : Subgroup V} (hA : A ≤ stabSub U)
    (k : ℕ) : (commIter ⊤ (autSub A U) k).map U.subtype = commIter U A k := by
  induction k with
  | zero =>
    show (⊤ : Subgroup U).map U.subtype = U
    rw [← MonoidHom.range_eq_map]
    exact U.range_subtype
  | succ k ih => simp only [commIter]; rw [map_commSub_autSub hA, ih]

theorem commSeries_autSub_eq_bot {A : Subgroup (MulAut V)} {U : Subgroup V} (hA : A ≤ stabSub U)
    {k : ℕ} (h : commSeries A k = ⊥) : commSeries (autSub A U) k = ⊥ := by
  have h1 := map_commIter_autSub hA k
  have h2 : commIter U A k ≤ commSeries A k := commIter_mono le_top le_rfl k
  rw [h] at h2
  have : (commSeries (autSub A U) k).map U.subtype = ⊥ := by
    unfold commSeries
    rw [h1]
    exact le_bot_iff.mp h2
  exact (Subgroup.map_eq_bot_iff_of_injective _ U.subtype_injective).mp this

theorem exists_le_of_le_autSub {A : Subgroup (MulAut V)} {U : Subgroup V} {B' : Subgroup (MulAut U)}
    (h : B' ≤ autSub A U) : ∃ D : Subgroup (MulAut V), D ≤ A ∧ autSub D U = B' := by
  refine ⟨A ⊓ (B'.comap (resHom U)).map (stabSub U).subtype, inf_le_left, ?_⟩
  ext φ
  rw [mem_autSub]
  constructor
  · rintro ⟨g, ⟨-, hg⟩, rfl⟩
    obtain ⟨g', hg', hgg⟩ := Subgroup.mem_map.mp hg
    have : g' = g := Subtype.ext hgg
    subst this
    exact hg'
  · intro hφ
    obtain ⟨g, hg, rfl⟩ := mem_autSub.mp (h hφ)
    exact ⟨g, ⟨hg, Subgroup.mem_map.mpr ⟨g, hφ, rfl⟩⟩, rfl⟩

section Faithful

variable [Finite V]

theorem rkIdx_autSub_eq_of_faithful {D : Subgroup (MulAut V)}
    {U : Subgroup V} (hD : D ≤ stabSub U) (hW : U ⊔ fixV D = ⊤) :
    rkIdx (fixV (autSub D U)) = rkIdx (fixV D) := by
  have h2 := rkIdx_autSub_add hD
  have h3 := rk_add_rkIdx (fixV D)
  have h5 := rk_sup_add_rk_inf U (fixV D)
  have hrW : rk ↥(U ⊔ fixV D) = rk V := by rw [hW]; exact rk_top
  omega

theorem rk_autSub_eq_of_faithful {D : Subgroup (MulAut V)} {U : Subgroup V} (hD : D ≤ stabSub U)
    (hB : D ⊓ centSub U = ⊥) : rk (autSub D U) = rk D := by
  have := rk_autSub_add_rk_inf hD
  rw [hB, rk_bot] at this
  omega

theorem rAV_autSub_eq_of_faithful {D : Subgroup (MulAut V)}
    {U : Subgroup V} (hD : D ≤ stabSub U) (hB : D ⊓ centSub U = ⊥) (hW : U ⊔ fixV D = ⊤) :
    rAV (autSub D U) = rAV D := by
  unfold rAV
  rw [rk_autSub_eq_of_faithful hD hB, rkIdx_autSub_eq_of_faithful hD hW]

end Faithful

theorem D2_3_1 {X A B : Subgroup (MulAut V)} (hA : A ∈ RPlus X) (hB : B ≠ ⊥) (hBA : B ≤ A)
    (hr : rAV A = rAV B) : B ∈ RPlus X :=
  ⟨hA.1.mono hBA hB, fun C hC hCB => hr ▸ hA.2 C hC (hCB.trans hBA)⟩

theorem D2_3_2 [Finite V] {X A : Subgroup (MulAut V)} {k : ℕ} (hA : IsA2 X A)
    (hk : commSeries A k = ⊥) (hr : (rAV A : WithTop ℚ) = kq X k) : A ∈ RPlus X := by
  refine ⟨hA, fun B hB hBA => ?_⟩
  have hB2 : IsA2 X B := hA.mono hBA hB
  have hBk : commSeries B k = ⊥ :=
    le_bot_iff.mp (hk ▸ commSeries_mono hBA k)
  exact le_kq_iff.mp hr.le B hB2 hBk

theorem autSub_bot (U : Subgroup V) : autSub (⊥ : Subgroup (MulAut V)) U = ⊥ := by
  simp [autSub]

section D24

variable [Finite V]

theorem D2_4 (hV : ∀ v : V, v ^ 2 = 1) {X A : Subgroup (MulAut V)} {r : ℚ}
    (hA : A ∈ RPlusEq X r) {U : Subgroup V} (hU : A ≤ stabSub U) (hUA : commSub U A ≠ ⊥) :
    (∃ ε : ℚ, 0 < ε ∧ autSub A U ∈ Rle (autSub X U) (r - ε) ∧ rAV (autSub A U) < rAV A) ∨
    (A ⊓ centSub U = ⊥ ∧ U ⊔ fixV A = ⊤ ∧
      (∀ D : Subgroup (MulAut V), D ≠ ⊥ → D ≤ A →
        rkIdx (fixV (autSub D U)) = rkIdx (fixV D) ∧ rAV (autSub D U) = rAV D ∧
          r ≤ rAV D) ∧
      A ∈ RPlusEq X r ∧ autSub A U ∈ RPlusEq (autSub X U) r) ∨
    (autSub A U ∈ Req (autSub X U) r ∧ A ⊓ centSub U ∈ RPlusEq X r ∧
      fixV (A ⊓ centSub U) = U ⊔ fixV A) := by
  obtain ⟨⟨hA2, hAr⟩, hAplus⟩ := hA
  have hAU : IsA2 (autSub X U) (autSub A U) := hA2.autSub hU hUA
  rcases D2_2 hV (X := X) (A := A) (r := r) ⟨hA2, hAr.le⟩ hU hUA with
    ⟨ε, hε, h1⟩ | ⟨ε, hε, h2⟩ | ⟨hB, hrr, hW⟩ | ⟨-, h4, h5, h6⟩
  · exact Or.inl ⟨ε, hε, h1, by have := h1.2; linarith⟩
  · exfalso
    have := hAplus.2 (A ⊓ centSub U) h2.1.ne_bot inf_le_left
    have := h2.2
    linarith
  · refine Or.inr (Or.inl ⟨hB, hW, ?_, ⟨⟨hA2, hAr⟩, hAplus⟩, ?_⟩)
    · intro D hD hDA
      have hDs : D ≤ stabSub U := hDA.trans hU
      have hDB : D ⊓ centSub U = ⊥ :=
        le_bot_iff.mp (hB ▸ inf_le_inf_right _ hDA)
      have hDW : U ⊔ fixV D = ⊤ :=
        top_le_iff.mp (hW ▸ sup_le_sup_left (fixV_anti hDA) U)
      exact ⟨rkIdx_autSub_eq_of_faithful hDs hDW, rAV_autSub_eq_of_faithful hDs hDB hDW,
        hAr ▸ hAplus.2 D hD hDA⟩
    · have hrAU : rAV (autSub A U) = r := hrr.symm.trans hAr
      refine ⟨⟨hAU, hrAU⟩, hAU, fun B' hB' hB'le => ?_⟩
      obtain ⟨D, hDA, rfl⟩ := exists_le_of_le_autSub hB'le
      have hD : D ≠ ⊥ := by
        rintro rfl
        exact hB' (autSub_bot U)
      have hDs : D ≤ stabSub U := hDA.trans hU
      have hDB : D ⊓ centSub U = ⊥ :=
        le_bot_iff.mp (hB ▸ inf_le_inf_right _ hDA)
      have hDW : U ⊔ fixV D = ⊤ :=
        top_le_iff.mp (hW ▸ sup_le_sup_left (fixV_anti hDA) U)
      rw [rAV_autSub_eq_of_faithful hDs hDB hDW, hrAU]
      exact hAr ▸ hAplus.2 D hD hDA
  · exact Or.inr (Or.inr ⟨h4, ⟨h5, D2_3_1 hAplus h5.1.ne_bot inf_le_left
      (by rw [hAr, h5.2])⟩, h6⟩)

theorem D2_5 (hV : ∀ v : V, v ^ 2 = 1) {X A : Subgroup (MulAut V)} {r : ℚ}
    (hA : A ∈ RPlusLe X r) {U : Subgroup V} (hU : A ≤ stabSub U) (hUA : commSub U A ≠ ⊥) :
    autSub A U ∈ Rle (autSub X U) r := by
  have hA2 : IsA2 X A := hA.1.1
  have hAU : IsA2 (autSub X U) (autSub A U) := hA2.autSub hU hUA
  refine ⟨hAU, le_trans ?_ hA.1.2⟩
  rcases D2_4 hV (X := X) (A := A) (r := rAV A) ⟨⟨hA2, rfl⟩, hA.2⟩ hU hUA with
    ⟨ε, hε, -, h1⟩ | ⟨-, -, -, -, h2⟩ | ⟨h3, -⟩
  · exact h1.le
  · exact h2.1.2.le
  · exact h3.2.le

end D24

section D26

variable [Finite V]

theorem D2_6 (hV : ∀ v : V, v ^ 2 = 1) {X A : Subgroup (MulAut V)} {k : ℕ} {r : ℚ}
    (hA : A ∈ kRPlusLe X k r) {U : Subgroup V} (hU : A ≤ stabSub U) (hUA : commSub U A ≠ ⊥)
    (hq : (r : WithTop ℚ) ≤ kq (autSub X U) k) :
    kq (autSub X U) k = (r : WithTop ℚ) ∧
    ((A ⊓ centSub U = ⊥ ∧ U ⊔ fixV A = ⊤ ∧ autSub A U ∈ RPlusEq (autSub X U) r) ∨
     (autSub A U ∈ Req (autSub X U) r ∧ A ⊓ centSub U ∈ RPlusEq X r ∧
        fixV (A ⊓ centSub U) = U ⊔ fixV A)) := by
  obtain ⟨⟨⟨hA2, hAr⟩, hAk⟩, hAplus⟩ := hA
  have hAU : IsA2 (autSub X U) (autSub A U) := hA2.autSub hU hUA
  have hAUk : commSeries (autSub A U) k = ⊥ := commSeries_autSub_eq_bot hU hAk
  have hqA : r ≤ rAV (autSub A U) :=
    WithTop.coe_le_coe.mp (hq.trans (kq_le_iff.mpr ⟨_, hAU, hAUk, le_rfl⟩))
  have hAUle : rAV (autSub A U) ≤ rAV A :=
    (D2_5 hV (X := X) (A := A) (r := rAV A) ⟨⟨hA2, le_rfl⟩, hAplus⟩ hU hUA).2
  have hρ : rAV A = r := le_antisymm hAr (hqA.trans hAUle)
  have hρ' : rAV (autSub A U) = r := le_antisymm (hAUle.trans hAr) hqA
  refine ⟨le_antisymm (kq_le_iff.mpr ⟨_, hAU, hAUk, hρ'.le⟩) hq, ?_⟩
  rcases D2_4 hV (X := X) (A := A) (r := r) ⟨⟨hA2, hρ⟩, hAplus⟩ hU hUA with
    ⟨ε, hε, -, h1⟩ | ⟨hB, hW, -, -, h5⟩ | ⟨h3, h4, h5⟩
  · exact absurd h1 (by rw [hρ, hρ']; exact lt_irrefl r)
  · exact Or.inl ⟨hB, hW, h5⟩
  · exact Or.inr ⟨h3, h4, h5⟩

end D26

section D27

variable [Finite V]

theorem D2_7 (hV : ∀ v : V, v ^ 2 = 1) {X A : Subgroup (MulAut V)} {r : ℚ}
    (hr : qhatOf X = (r : WithTop ℚ)) (hA : A ∈ QhatStar X) {U : Subgroup V}
    (hU : A ≤ stabSub U) (hUA : commSub U A ≠ ⊥) :
    A ∈ kRPlusEq X 3 r ∧
    ((∃ ε : ℚ, 0 < ε ∧ autSub A U ∈ Qhat (autSub X U) (r - ε)) ∨
      (A ⊓ centSub U = ⊥ ∧ U ⊔ fixV A = ⊤)) := by
  obtain ⟨r', hr', hr2, hAk, hmin⟩ := hA
  have hrr : r' = r := WithTop.coe_injective (hr'.symm.trans hr)
  subst hrr
  obtain ⟨⟨hA2, hAr⟩, hAk3⟩ := hAk
  have hAeq : rAV A = r' := by
    refine le_antisymm hAr ?_
    exact le_kq_iff.mp (by rw [← hr']; exact le_rfl : (r' : WithTop ℚ) ≤ kq X 3) A hA2 hAk3
  have hAplus : A ∈ RPlus X := D2_3_2 hA2 hAk3 (by rw [hAeq]; exact hr'.symm)
  have hAU : IsA2 (autSub X U) (autSub A U) := hA2.autSub hU hUA
  have hAUk : commSeries (autSub A U) 3 = ⊥ := commSeries_autSub_eq_bot hU hAk3
  have hAmem : A ∈ kRPlusEq X 3 r' := ⟨⟨⟨hA2, hAeq⟩, hAk3⟩, hAplus⟩
  refine ⟨hAmem, ?_⟩
  rcases D2_4 hV (X := X) (A := A) (r := r') ⟨⟨hA2, hAeq⟩, hAplus⟩ hU hUA with
    ⟨ε, hε, h1, -⟩ | ⟨hB, hW, -⟩ | ⟨-, h4, -⟩
  · exact Or.inl ⟨ε, hε, ⟨⟨hAU, h1.2⟩, hAUk⟩⟩
  · exact Or.inr ⟨hB, hW⟩
  · exfalso
    have hB2 : IsA2 X (A ⊓ centSub U) := h4.1.1
    have hBk : commSeries (A ⊓ centSub U) 3 = ⊥ :=
      le_bot_iff.mp (hAk3 ▸ commSeries_mono inf_le_left 3)
    have heq := hmin (A ⊓ centSub U) ⟨⟨hB2, h4.1.2.le⟩, hBk⟩ inf_le_left
    apply hUA
    rw [commSub_eq_bot_iff]
    intro u hu g hg
    have : g ∈ A ⊓ centSub U := heq.symm ▸ hg
    exact this.2 u hu

theorem D2_8 (hV : ∀ v : V, v ^ 2 = 1) {X A : Subgroup (MulAut V)} {r : ℚ}
    (hr : qhatOf X = (r : WithTop ℚ)) (hA : A ∈ QhatStar X) {U : Subgroup V}
    (hU : A ≤ stabSub U) (hUA : commSub U A ≠ ⊥)
    (hq : (r : WithTop ℚ) ≤ qhatOf (autSub X U)) :
    qhatOf (autSub X U) = (r : WithTop ℚ) ∧ A ⊓ centSub U = ⊥ ∧ U ⊔ fixV A = ⊤ ∧
      autSub A U ∈ QhatStar (autSub X U) := by
  obtain ⟨hA7, h7⟩ := D2_7 hV hr hA hU hUA
  obtain ⟨r', hr', hr2, ⟨⟨hA2, hAr⟩, hAk3⟩, hmin⟩ := hA
  have hrr : r' = r := WithTop.coe_injective (hr'.symm.trans hr)
  subst hrr
  have hAU : IsA2 (autSub X U) (autSub A U) := hA2.autSub hU hUA
  have hAUk : commSeries (autSub A U) 3 = ⊥ := commSeries_autSub_eq_bot hU hAk3
  obtain ⟨hqeq, h6⟩ := D2_6 hV (X := X) (A := A) (k := 3) (r := r')
    ⟨⟨⟨hA2, hAr⟩, hAk3⟩, hA7.2⟩ hU hUA hq
  have hfaith : A ⊓ centSub U = ⊥ ∧ U ⊔ fixV A = ⊤ ∧
      autSub A U ∈ RPlusEq (autSub X U) r' := by
    rcases h6 with h | ⟨h3, h4, -⟩
    · exact h
    · exfalso
      rcases h7 with ⟨ε, hε, hε2⟩ | ⟨hB, -⟩
      · have := hε2.1.2
        have := h3.2
        linarith
      · exact h4.1.1.ne_bot hB
  obtain ⟨hB, hW, hAUplus⟩ := hfaith
  refine ⟨hqeq, hB, hW, r', hqeq, hr2, ⟨⟨hAU, hAUplus.1.2.le⟩, hAUk⟩, ?_⟩
  rintro B' ⟨⟨hB'2, hB'r⟩, hB'k⟩ hB'le
  obtain ⟨D, hDA, rfl⟩ := exists_le_of_le_autSub hB'le
  have hD : D ≠ ⊥ := by
    rintro rfl
    exact hB'2.ne_bot (autSub_bot U)
  by_cases hDeq : D = A
  · rw [hDeq]
  · exfalso
    have hDs : D ≤ stabSub U := hDA.trans hU
    have hDB : D ⊓ centSub U = ⊥ := le_bot_iff.mp (hB ▸ inf_le_inf_right _ hDA)
    have hDW : U ⊔ fixV D = ⊤ := top_le_iff.mp (hW ▸ sup_le_sup_left (fixV_anti hDA) U)
    have hD2 : IsA2 X D := hA2.mono hDA hD
    have hDk : commSeries D 3 = ⊥ := le_bot_iff.mp (hAk3 ▸ commSeries_mono hDA 3)
    have hge : r' ≤ rAV D :=
      le_kq_iff.mp (by rw [← hr']; exact le_rfl : (r' : WithTop ℚ) ≤ kq X 3) D hD2 hDk
    have hne : rAV D ≠ r' := fun h =>
      hDeq (hmin D ⟨⟨hD2, h.le⟩, hDk⟩ hDA)
    have hlt : r' < rAV D := lt_of_le_of_ne hge (Ne.symm hne)
    have := rAV_autSub_eq_of_faithful hDs hDB hDW
    linarith

end D27

end CFSG.Quasithin
