module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Lat

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Quasithin U42F431
open scoped Pointwise

theorem eq_or_eq_of_prime_relIndex {B P K : Subgroup Y} (hBP : B ≤ P) {p : ℕ} (hp : p.Prime)
    (hidx : B.relIndex P = p) (hBK : B ≤ K) (hKP : K ≤ P) : K = B ∨ K = P := by
  have h1 := Subgroup.relIndex_mul_card (H := B) (K := P)
  rw [inf_eq_left.2 hBP, hidx] at h1
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hBK
  have hP : Nat.card K ∣ Nat.card P := Subgroup.card_dvd_of_le hKP
  rw [hm, ← h1, mul_comm p] at hP
  have hBpos : 0 < Nat.card B := Nat.card_pos
  have hmp : m ∣ p := (Nat.mul_dvd_mul_iff_left hBpos).1 hP
  rcases (Nat.dvd_prime hp).1 hmp with rfl | rfl
  · left
    exact (Subgroup.eq_of_le_of_card_ge hBK (by rw [hm]; simp)).symm
  · right
    refine (Subgroup.eq_of_le_of_card_ge hKP ?_)
    rw [hm, ← h1, mul_comm]

theorem P1_le_of {H : Subgroup Y}
    (hB : B0 ≤ H) (hD : Dj 1 ∈ H) : P1 ≤ H := by
  have hK : B0 ⊔ Subgroup.zpowers (Dj 1) ≤ P1 :=
    sup_le B0_le_P1 ((Subgroup.zpowers_le).2 D1_mem_P1)
  rcases eq_or_eq_of_prime_relIndex B0_le_P1 (p := 3) (by norm_num) relIndex_B0_P1
      le_sup_left hK with h | h
  · exfalso
    have : Dj 1 ∈ B0 := by
      rw [← h]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    exact D1_not_mem_P2 (B0_le_P2 this)
  · rw [← h]
    exact sup_le hB ((Subgroup.zpowers_le).2 hD)

theorem P2_le_of {H : Subgroup Y}
    (hB : B0 ≤ H) (hD : Dj 2 ∈ H) : P2 ≤ H := by
  have hK : B0 ⊔ Subgroup.zpowers (Dj 2) ≤ P2 :=
    sup_le B0_le_P2 ((Subgroup.zpowers_le).2 D2_mem_P2)
  rcases eq_or_eq_of_prime_relIndex B0_le_P2 (p := 5) (by norm_num) relIndex_B0_P2
      le_sup_left hK with h | h
  · exfalso
    have : Dj 2 ∈ B0 := by
      rw [← h]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    exact D2_not_mem_P1 (B0_le_P1 this)
  · rw [← h]
    exact sup_le hB ((Subgroup.zpowers_le).2 hD)

@[expose] def xY : Y := ⟨x45, x45_mem⟩

@[expose] def yY : Y := ⟨y45, y45_mem⟩

theorem closure_xy_top : Subgroup.closure ({xY, yY} : Set Y) = ⊤ := by
  apply Subgroup.map_injective (f := Xs.subtype) Xs.subtype_injective
  rw [MonoidHom.map_closure, Subgroup.map_top, Subgroup.range_subtype]
  have : (Xs.subtype : Y →* P45) '' ({xY, yY} : Set Y) = ({x45, y45} : Set P45) := by
    rw [Set.image_pair]
    rfl
  rw [this]
  rfl

@[expose] def alphaYE (a : ℕ) : Y :=
  if a < 5 then gTY a else if a == 5 then c3Y else if a == 6 then Dj 1 else Dj 2

theorem repL_alphaYE (a : ℕ) :
    RepL (alphaY a) ((alphaYE a : Y) : P45) := by
  unfold alphaY alphaYE
  split_ifs
  · exact repL_gTY a
  · exact repL_c3
  · exact repL_Dj 1
  · exact repL_Dj 2

@[expose] def wordB (w : List ℕ) : Y := (w.map alphaYE).prod

theorem repL_wordB (w : List ℕ) :
    RepL (w.foldr (fun a acc => comp (alphaY a) acc) idL) ((wordB w : Y) : P45) := by
  induction w with
  | nil => exact repL_one 45
  | cons a w ih =>
    have : ((wordB (a :: w) : Y) : P45) = ((alphaYE a : Y) : P45) * ((wordB w : Y) : P45) := by
      simp [wordB]
    rw [this]
    exact repL_mul (repL_alphaYE a) ih

theorem P1_sup_P2 : P1 ⊔ P2 = ⊤ := by
  have hx : xY ∈ P1 := by
    rw [mem_P1_iff]
    show x45 0 = 0
    apply Fin.ext
    rw [← repL_x.2 0]
    decide +kernel
  have hy : yY ∈ P1 ⊔ P2 := by
    have hw : wordB yW = yY :=
      Subtype.ext (eq_of_repL (repL_wordB yW)
        (by rw [chkLat_spec.2.2.2.2.2.2.2.2.1]; exact repL_y))
    rw [← hw]
    refine Subgroup.list_prod_mem _ ?_
    intro z hz
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hz
    unfold alphaYE
    split_ifs
    · exact Subgroup.mem_sup_left (B0_le_P1 (gTY_mem_B0 a ‹_›))
    · exact Subgroup.mem_sup_left (B0_le_P1 c3_mem_B0)
    · exact Subgroup.mem_sup_left D1_mem_P1
    · exact Subgroup.mem_sup_right D2_mem_P2
  rw [eq_top_iff, ← closure_xy_top, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact Subgroup.mem_sup_left hx
  · exact hy

theorem lattice {H : Subgroup Y}
    (hB : B0 ≤ H) : H = B0 ∨ H = P1 ∨ H = P2 ∨ H = ⊤ := by
  have hcov : ∀ g ∈ H, ∃ j < 8, Dj j ∈ H ∧ ∃ b ∈ B0, ∃ b' ∈ B0, g = b * Dj j * b' := by
    intro g hg
    obtain ⟨j, hj, b, hb, b', hb', rfl⟩ := cover_B0 g
    refine ⟨j, hj, ?_, b, hb, b', hb', rfl⟩
    have : Dj j = b⁻¹ * (b * Dj j * b') * b'⁻¹ := by simp [mul_assoc]
    rw [this]
    exact H.mul_mem (H.mul_mem (H.inv_mem (hB hb)) hg) (H.inv_mem (hB hb'))
  have hB2 : B0 ≤ P2 := B0_le_P2
  have hB1 : B0 ≤ P1 := B0_le_P1
  by_cases hfar : ∃ j, 3 ≤ j ∧ j < 8 ∧ Dj j ∈ H
  · obtain ⟨j, hj3, hj8, hjH⟩ := hfar
    obtain ⟨h1, h2⟩ := far_gen hB hj3 hj8 hjH
    right; right; right
    rw [eq_top_iff, ← P1_sup_P2]
    exact sup_le (P1_le_of hB h1) (P2_le_of hB h2)
  · have hfar' : ∀ j, 3 ≤ j → j < 8 → Dj j ∉ H := fun j h3 h8 hj => hfar ⟨j, h3, h8, hj⟩
    have hcases : ∀ g ∈ H, (g ∈ B0) ∨ (Dj 1 ∈ H ∧ g ∈ P1) ∨ (Dj 2 ∈ H ∧ g ∈ P2) := by
      intro g hg
      obtain ⟨j, hj, hjH, b, hb, b', hb', rfl⟩ := hcov g hg
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ 3 ≤ j) with rfl | rfl | rfl | h3
      · left
        rw [Dj_zero]
        simpa using B0.mul_mem hb hb'
      · right; left
        exact ⟨hjH, P1.mul_mem (P1.mul_mem (hB1 hb) D1_mem_P1) (hB1 hb')⟩
      · right; right
        exact ⟨hjH, P2.mul_mem (P2.mul_mem (hB2 hb) D2_mem_P2) (hB2 hb')⟩
      · exact absurd hjH (hfar' j h3 hj)
    by_cases h1 : Dj 1 ∈ H
    · by_cases h2 : Dj 2 ∈ H
      · right; right; right
        rw [eq_top_iff, ← P1_sup_P2]
        exact sup_le (P1_le_of hB h1) (P2_le_of hB h2)
      · right; left
        refine le_antisymm (fun g hg => ?_) (P1_le_of hB h1)
        rcases hcases g hg with hgB | ⟨-, hgP⟩ | ⟨hD2, -⟩
        · exact hB1 hgB
        · exact hgP
        · exact absurd hD2 h2
    · by_cases h2 : Dj 2 ∈ H
      · right; right; left
        refine le_antisymm (fun g hg => ?_) (P2_le_of hB h2)
        rcases hcases g hg with hgB | ⟨hD1, -⟩ | ⟨-, hgP⟩
        · exact hB2 hgB
        · exact absurd hD1 h1
        · exact hgP
      · left
        refine le_antisymm (fun g hg => ?_) hB
        rcases hcases g hg with hgB | ⟨hD1, -⟩ | ⟨hD2, -⟩
        · exact hgB
        · exact absurd hD1 h1
        · exact absurd hD2 h2

end CFSG.Quasithin.H13.F431.U42
