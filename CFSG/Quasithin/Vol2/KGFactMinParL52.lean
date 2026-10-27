module

public import CFSG.Quasithin.Vol2.KGFactMinParBase
public import CFSG.Quasithin.Vol2.KGFactMinParL52Inputs
public import CFSG.Literature.GL52Chain
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatIncl
public import Certificates.Certificate7156

public section

namespace CFSG.Quasithin.H13.KGMinPar

open CFSG.Literature.GL52 CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat

variable {X : Type} [Group X]

noncomputable def l52Mem : ℕ → Subgroup G :=
  Classical.choose Certificates.certificate7156

theorem l52_cert :
    Nat.card (l52Mem 0) = 2 ^ 10 ∧
    (∀ j < 15, l52Mem 0 ≤ l52Mem j ∧ Nat.card (l52Mem j) =
      [1, 21, 315, 3, 315, 3, 63, 3, 63, 9, 21, 21, 9, 9, 3].getD j 0 * 2 ^ 10) ∧
    (∀ i < 15, ∀ j < 15, l52Mem i ≤ l52Mem j ↔ j ∈ l52Incl.getD i []) ∧
    ∀ Z : Subgroup G, l52Mem 0 ≤ Z → Z = ⊤ ∨ ∃ j < 15, Z = l52Mem j :=
  Classical.choose_spec Certificates.certificate7156

@[expose] noncomputable def l52S : Subgroup G := l52Mem 0

theorem l52_Y_zero : l52Mem 0 = l52S := rfl

theorem l52_S_card : Nat.card l52S = 2 ^ 10 :=
  l52_cert.1

theorem l52_S_le_Y (j : ℕ) (hj : j < 15) : l52S ≤ l52Mem j :=
  (l52_cert.2.1 j hj).1

theorem l52_complete :
    ∀ Z : Subgroup G, l52S ≤ Z → ∃ j ≤ 15, Z = memberOrTop 15 l52Mem j := by
  intro Z hZ
  rcases l52_cert.2.2.2 Z hZ with rfl | ⟨j, hj, rfl⟩
  · exact ⟨15, le_rfl, by simp [memberOrTop]⟩
  · exact ⟨j, hj.le, by simp [memberOrTop, hj]⟩

@[expose] def l52Ord (j : ℕ) : ℕ :=
  #[1, 21, 315, 3, 315, 3, 63, 3, 63, 9, 21, 21, 9, 9, 3][j]! * 1024

theorem l52Ord_eq : ∀ j < 15,
    [1, 21, 315, 3, 315, 3, 63, 3, 63, 9, 21, 21, 9, 9, 3].getD j 0 * 2 ^ 10 = l52Ord j := by
  decide

theorem l52Incl_eq : ∀ i < 15, l52Incl.getD i [] = l52Incl[i]! := by
  decide

theorem l52_member_card (j : ℕ) (hj : j < 15) :
    Nat.card (l52Mem j) = l52Ord j :=
  (l52_cert.2.1 j hj).2.trans (l52Ord_eq j hj)

theorem l52_Y_le_iff {j jj : ℕ} (hj : j < 15) (hjj : jj < 15) :
    l52Mem j ≤ l52Mem jj ↔ jj ∈ l52Incl[j]! := by
  rw [l52_cert.2.2.1 j hj jj hjj, l52Incl_eq j hj]

theorem l52_S_sylow : IsSylowTwoOf l52S ⊤ := by
  refine K1.isSylowTwoOf_top_iff.mpr ⟨IsPGroup.of_card l52_S_card, ?_⟩
  have h1 := Subgroup.card_mul_index l52S
  rw [l52_S_card, card_GL52] at h1
  have h2 : l52S.index = 9765 := by omega
  rw [h2]
  norm_num

theorem l52_key [Finite X]
    {L T : Subgroup X} (hT : IsSylowTwoOf T L) (e : ↥L ≃* G) : Key T L := by
  obtain ⟨φ, hφ, hlat⟩ := exists_lat l52_S_sylow l52_S_le_Y l52_complete hT e
  set Z : ℕ → Subgroup X := fun j => (l52Mem j).map φ with hZ
  have hcard : ∀ j < 15, Nat.card (Z j) = l52Ord j := fun j hj =>
    (Subgroup.card_map_of_injective hφ).trans (l52_member_card j hj)
  have hle : ∀ i < 15, ∀ j < 15, Z i ≤ Z j ↔ j ∈ l52Incl[i]! := fun i hi j hj =>
    (Subgroup.map_le_map_iff_of_injective hφ).trans (l52_Y_le_iff hi hj)
  have hL : Nat.card L = 2 ^ 10 * 3 ^ 2 * 5 * 7 * 31 := by
    rw [Nat.card_congr e.toEquiv, card_GL52]
  have hlt : ∀ m < 15, l52Ord m < 2 ^ 10 * 3 ^ 2 * 5 * 7 * 31 := by decide
  have hnotL : ∀ m < 15, ¬ L ≤ Z m := fun m hm hLm => by
    have h1 := Subgroup.card_le_of_le hLm
    rw [hL, hcard m hm] at h1
    exact absurd (hlt m hm) (not_lt_of_ge h1)
  have hord : ∀ {a o : ℕ}, a < 15 → (∀ j < 15, l52Ord j = o → j ∈ l52Incl[a]!) →
      ∀ j < 15, Nat.card (Z j) = o → Z a ≤ Z j := fun ha h j hj hc =>
    (hle _ ha j hj).mpr (h j hj (hcard j hj ▸ hc))
  have hjoin : ∀ {a b w : ℕ}, a < 15 → b < 15 → w < 15 →
      (∀ j < 15, j ∈ l52Incl[a]! → j ∈ l52Incl[b]! → j ∈ l52Incl[w]!) →
      ∀ j < 15, Z a ≤ Z j → Z b ≤ Z j → Z w ≤ Z j := fun ha hb hw h j hj h1 h2 =>
    (hle _ hw j hj).mpr (h j hj ((hle _ ha j hj).mp h1) ((hle _ hb j hj).mp h2))
  have hc : ∀ {m : ℕ}, m < 15 → Nat.card (Z m) = l52Ord m := fun hm => hcard _ hm
  have hL6 : Nat.card L ≠ 64512 := by rw [hL]; norm_num
  have hL3 : Nat.card L ≠ 322560 := by rw [hL]; norm_num
  intro W hTW hWL h5
  rcases hlat.complete W hTW hWL with rfl | ⟨w, hw, rfl⟩
  · refine ⟨64512, 322560, hlat.case le_rfl (a := 13) (b := 1) (m₁ := 6) (m₂ := 2)
      (by norm_num) (by norm_num) (by norm_num) hL6 hL3 (hlat.le_L 13 (by norm_num))
      (hlat.le_L 1 (by norm_num)) (hord (by norm_num) (by decide))
      (hord (by norm_num) (by decide)) (hc (by norm_num)) (hc (by norm_num))
      (hnotL 6 (by norm_num)) (hnotL 2 (by norm_num)) fun j hj h1 h2 => ?_⟩
    have hv : ∀ j < 15, j ∈ l52Incl[13]! → j ∈ l52Incl[1]! → False := by decide
    exact (hv j hj ((hle 13 (by norm_num) j hj).mp h1) ((hle 1 (by norm_num) j hj).mp h2)).elim
  · have h5w : ∀ w < 15, 5 ∣ l52Ord w → w = 2 ∨ w = 4 := by decide
    rcases h5w w hw (hcard w hw ▸ h5) with rfl | rfl
    · refine ⟨322560, 64512, hlat.case (hlat.le_L 2 (by norm_num)) (a := 1) (b := 7)
        (m₁ := 4) (m₂ := 6) (by norm_num) (by norm_num) (by norm_num) hL3 hL6
        ((hle 1 (by norm_num) 2 (by norm_num)).mpr (by decide))
        ((hle 7 (by norm_num) 2 (by norm_num)).mpr (by decide))
        (hord (by norm_num) (by decide)) (hord (by norm_num) (by decide)) (hc (by norm_num))
        (hc (by norm_num)) (fun h => absurd ((hle 2 (by norm_num) 4 (by norm_num)).mp h)
          (by decide)) (fun h => absurd ((hle 2 (by norm_num) 6 (by norm_num)).mp h)
          (by decide)) (hjoin (by norm_num) (by norm_num) (by norm_num) (by decide))⟩
    · refine ⟨322560, 64512, hlat.case (hlat.le_L 4 (by norm_num)) (a := 1) (b := 14)
        (m₁ := 2) (m₂ := 6) (by norm_num) (by norm_num) (by norm_num) hL3 hL6
        ((hle 1 (by norm_num) 4 (by norm_num)).mpr (by decide))
        ((hle 14 (by norm_num) 4 (by norm_num)).mpr (by decide))
        (hord (by norm_num) (by decide)) (hord (by norm_num) (by decide)) (hc (by norm_num))
        (hc (by norm_num)) (fun h => absurd ((hle 4 (by norm_num) 2 (by norm_num)).mp h)
          (by decide)) (fun h => absurd ((hle 4 (by norm_num) 6 (by norm_num)).mp h)
          (by decide)) (hjoin (by norm_num) (by norm_num) (by norm_num) (by decide))⟩

end CFSG.Quasithin.H13.KGMinPar
