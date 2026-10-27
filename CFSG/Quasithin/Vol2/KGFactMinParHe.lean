module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHeCertificate

public import CFSG.Quasithin.Vol2.KGFactMinParBase
public import CFSG.Quasithin.Vol2.Ch8Sec3Lem8310KG
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHe
public import CFSG.Sporadic.Schreier.PairHePairs
public import CFSG.LargeExtraspecial.OutSixBasic

public section

namespace CFSG.Quasithin.H13.KGMinPar

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.Ch1.SporLat.He CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {X : Type} [Group X]

@[expose] def heOrd (j : ℕ) : ℕ := #[1, 3, 9, 135, 135, 9, 3, 21, 3, 9, 3][j]! * 1024

theorem he_key
    [Finite X] {L T : Subgroup X} (hT : IsSylowTwoOf T L)
    (e : ↥L ≃* CFSG.Sporadic.He.J) : Key T L := by
  obtain ⟨φ, hφ, hlat⟩ := exists_lat he_S_sylow (fun j _ => heCtx.S_le_Y j) he_complete hT e
  set Z : ℕ → Subgroup X := fun j => (heCtx.Y j).map φ with hZ
  have hcard : ∀ j < 11, Nat.card (Z j) = heOrd j := fun j hj =>
    (Subgroup.card_map_of_injective hφ).trans (he_member_card j hj)
  have hle : ∀ i < 11, ∀ j < 11, Z i ≤ Z j ↔ j ∈ heIncl[i]! := fun i hi j hj =>
    (Subgroup.map_le_map_iff_of_injective hφ).trans (he_Y_le_iff hi hj)
  have hL : Nat.card L = 2 ^ 10 * 3935925 := by
    rw [Nat.card_congr e.toEquiv, he_card]
  have hlt : ∀ m < 11, heOrd m < 2 ^ 10 * 3935925 := by decide
  have hnotL : ∀ m < 11, ¬ L ≤ Z m := fun m hm hLm => by
    have h1 := Subgroup.card_le_of_le hLm
    rw [hL, hcard m hm] at h1
    exact absurd (hlt m hm) (not_lt_of_ge h1)
  have hord : ∀ {a o : ℕ}, a < 11 → (∀ j < 11, heOrd j = o → j ∈ heIncl[a]!) →
      ∀ j < 11, Nat.card (Z j) = o → Z a ≤ Z j := fun ha h j hj hc =>
    (hle _ ha j hj).mpr (h j hj (hcard j hj ▸ hc))
  have hjoin : ∀ {a b w : ℕ}, a < 11 → b < 11 → w < 11 →
      (∀ j < 11, j ∈ heIncl[a]! → j ∈ heIncl[b]! → j ∈ heIncl[w]!) →
      ∀ j < 11, Z a ≤ Z j → Z b ≤ Z j → Z w ≤ Z j := fun ha hb hw h j hj h1 h2 =>
    (hle _ hw j hj).mpr (h j hj ((hle _ ha j hj).mp h1) ((hle _ hb j hj).mp h2))
  have hc : ∀ {m : ℕ}, m < 11 → Nat.card (Z m) = heOrd m := fun hm => hcard _ hm
  have hL21 : Nat.card L ≠ 21504 := by rw [hL]; norm_num
  have hL13 : Nat.card L ≠ 138240 := by rw [hL]; norm_num
  intro W hTW hWL h5
  rcases hlat.complete W hTW hWL with rfl | ⟨w, hw, rfl⟩
  · refine ⟨21504, 138240, hlat.case le_rfl (a := 7) (b := 2) (m₁ := 7) (m₂ := 3)
      (by norm_num) (by norm_num) (by norm_num) hL21 hL13 (hlat.le_L 7 (by norm_num))
      (hlat.le_L 2 (by norm_num)) (hord (by norm_num) (by decide))
      (hord (by norm_num) (by decide)) (hc (by norm_num)) (hc (by norm_num))
      (hnotL 7 (by norm_num)) (hnotL 3 (by norm_num)) fun j hj h1 h2 => ?_⟩
    have hv : ∀ j < 11, j ∈ heIncl[7]! → j ∈ heIncl[2]! → False := by decide
    exact (hv j hj ((hle 7 (by norm_num) j hj).mp h1) ((hle 2 (by norm_num) j hj).mp h2)).elim
  · have h5w : ∀ w < 11, 5 ∣ heOrd w → w = 3 ∨ w = 4 := by decide
    rcases h5w w hw (hcard w hw ▸ h5) with rfl | rfl
    · refine ⟨138240, 21504, hlat.case (hlat.le_L 3 (by norm_num)) (a := 2) (b := 8)
        (m₁ := 4) (m₂ := 7) (by norm_num) (by norm_num) (by norm_num) hL13 hL21
        ((hle 2 (by norm_num) 3 (by norm_num)).mpr (by decide))
        ((hle 8 (by norm_num) 3 (by norm_num)).mpr (by decide))
        (hord (by norm_num) (by decide)) (hord (by norm_num) (by decide)) (hc (by norm_num))
        (hc (by norm_num)) (fun h => absurd ((hle 3 (by norm_num) 4 (by norm_num)).mp h)
          (by decide)) (fun h => absurd ((hle 3 (by norm_num) 7 (by norm_num)).mp h)
          (by decide)) (hjoin (by norm_num) (by norm_num) (by norm_num) (by decide))⟩
    · refine ⟨138240, 21504, hlat.case (hlat.le_L 4 (by norm_num)) (a := 2) (b := 10)
        (m₁ := 3) (m₂ := 7) (by norm_num) (by norm_num) (by norm_num) hL13 hL21
        ((hle 2 (by norm_num) 4 (by norm_num)).mpr (by decide))
        ((hle 10 (by norm_num) 4 (by norm_num)).mpr (by decide))
        (hord (by norm_num) (by decide)) (hord (by norm_num) (by decide)) (hc (by norm_num))
        (hc (by norm_num)) (fun h => absurd ((hle 4 (by norm_num) 3 (by norm_num)).mp h)
          (by decide)) (fun h => absurd ((hle 4 (by norm_num) 7 (by norm_num)).mp h)
          (by decide)) (hjoin (by norm_num) (by norm_num) (by norm_num) (by decide))⟩

theorem he_index_dvd
    [Finite X] {L : Subgroup X}
    [L.Normal] (hC : Subgroup.centralizer (L : Set X) = ⊥)
    (e : ↥L ≃* NativeSporadic.Carrier .He) : L.index ∣ 2 := by
  have h1 := CFSG.LargeExtraspecial.S14.index_dvd_card_outer_of_mulEquiv L
    (by rw [hC]; exact bot_le) e
  have h2 : Nat.card (Outer (NativeSporadic.Carrier .He)) ≤ 2 :=
    CFSG.Sporadic.Schreier.AT_He_Schreier.1
  have : Finite (NativeSporadic.Carrier .He) := Finite.of_equiv _ e.toEquiv
  have : Finite (MulAut (NativeSporadic.Carrier .He)) :=
    Finite.of_injective (fun f : MulAut (NativeSporadic.Carrier .He) =>
      (f : NativeSporadic.Carrier .He → NativeSporadic.Carrier .He)) DFunLike.coe_injective
  have h3 : 0 < Nat.card (Outer (NativeSporadic.Carrier .He)) := Nat.card_pos
  interval_cases h : Nat.card (Outer (NativeSporadic.Carrier .He))
  · exact h1.trans (one_dvd 2)
  · exact h1

theorem kg8310MinParHe_holds
    : KG8310MinParHe := by
  intro X _ _ L S P hLn hL hC hS hP
  obtain ⟨e⟩ := hL
  have hT : IsSylowTwoOf (S ⊓ L) L :=
    B6.isSylowTwoOf_inf_normal hS le_top (by rw [Subgroup.normalizer_eq_top])
  exact not_five_dvd (he_index_dvd hC e) hS
    (he_key hT (e.trans CFSG.Sporadic.He.heEquivJ)) hP.1

end CFSG.Quasithin.H13.KGMinPar
