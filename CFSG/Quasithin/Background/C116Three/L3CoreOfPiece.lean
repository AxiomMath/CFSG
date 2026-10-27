module

import CFSG.Quasithin.Background.G64RealizeSec
public import CFSG.Quasithin.Background.B4L3Coord
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C116Three.ModuleDefs

public section

namespace CFSG.Quasithin.C116Three

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.R3c23 CFSG.Assembly.LowTwoRank

variable {V : Type} [CommGroup V]

private theorem l3core_card_of_nat {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
    {Γ : Subgroup (Matrix.GeneralLinearGroup ι F)} {L : Subgroup (MulAut V)} {U Z : Subgroup V}
    (h : (FFModel.nat Γ).Realizes L U Z) : Nat.card ↥L = Nat.card ↥Γ := by
  obtain ⟨π, hπ⟩ := h
  exact (Nat.card_congr (Equiv.ofBijective π
    ⟨G64.RealizesVia.injective_of_faithful' (FFModel.nat_faithful Γ) hπ, hπ.1⟩)).symm

private theorem l3core_card_L32 {G : Subgroup (MulAut V)} (hL : IsL32 G) :
    Nat.card ↥G = 168 := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hL
  rw [Nat.card_congr e.toEquiv]
  exact CFSG.Open.StatedAPI.card_statedSL_three_of_card_eq_two hK

private theorem l3core_q_eq_two {q : ℕ} (hq : 2 ≤ q)
    (h : 168 = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1))) : q = 2 := by
  have hq5 : q ≤ 5 := by
    by_contra hc
    have h6 : 6 ≤ q := by omega
    have h216 : 6 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left h6 3
    have h4 : 2 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
    norm_num at h216 h4
    have hpos : 0 < (q ^ 2 - 1) * (q ^ 3 - 1) := Nat.mul_pos (by omega) (by omega)
    have hle : q ^ 3 * 1 ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) :=
      Nat.mul_le_mul_left (q ^ 3) hpos
    omega
  interval_cases q <;> first | rfl | (norm_num at h)

private theorem l3core_sl2_ne {q : ℕ} (hq : 1 < q) (h : 168 = q * (q ^ 2 - 1)) : False := by
  have hq6 : q ≤ 6 := by
    by_contra hc
    have h7 : 7 ≤ q := by omega
    have h49 : 7 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left h7 2
    norm_num at h49
    have hmul : 7 * 48 ≤ q * (q ^ 2 - 1) := Nat.mul_le_mul h7 (by omega)
    omega
  interval_cases q <;> norm_num at h

private theorem l3core_not_sl2 {G : Subgroup (MulAut V)} {W C : Subgroup V} {n : ℕ}
    (hG : Nat.card ↥G = 168) (h : BinaryNaturalSL G W C 2 n) : False := by
  obtain ⟨K, _, _, _, hR⟩ := h
  have h1 := l3core_card_of_nat hR
  rw [hG, CFSG.Open.StatedAPI.card_statedSL_two K] at h1
  exact l3core_sl2_ne (Finite.one_lt_card (α := K)) h1

private theorem l3core_card_perm_five : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  decide

private theorem l3core_not_sym5 {G : Subgroup (MulAut V)} {W C : Subgroup V}
    (hG : Nat.card ↥G = 168) (h : SymmetricNatural G W C 5) : False := by
  obtain ⟨π, hπ⟩ := h
  have hle : Nat.card ↥G ≤ Nat.card (Equiv.Perm (Fin 5)) :=
    Nat.card_le_card_of_surjective (π : Equiv.Perm (Fin 5) →* ↥G) hπ.1
  rw [hG, l3core_card_perm_five] at hle
  omega

private theorem l3core_modComm_le {G : Subgroup (MulAut V)} {W : Subgroup V}
    (hinv : ∀ g ∈ G, ∀ w ∈ W, g w ∈ W) : modComm G W ≤ W :=
  XMod.commOf_le_of_isInv (fun a l hl => hinv (a : MulAut V) a.2 l hl)

private theorem l3core_modComm_le_commV {G : Subgroup (MulAut V)} (W : Subgroup V) :
    modComm G W ≤ commV G := by
  refine XMod.commOf_le_iff.mpr ?_
  intro a l _
  apply Subgroup.subset_closure
  exact ⟨(a : MulAut V), a.2, l, rfl⟩

theorem bnat_m_eq_one {G : Subgroup (MulAut V)} {U Z : Subgroup V} (hL : IsL32 G) {m : ℕ}
    (h : BinaryNaturalSL G U Z 3 m) : m = 1 := by
  obtain ⟨F, _, _, hF, hR⟩ := h
  have hG : Nat.card ↥G = 168 := l3core_card_L32 hL
  have h1 := l3core_card_of_nat hR
  rw [CFSG.Open.StatedAPI.card_statedSL_three F, hF, hG] at h1
  have hq : 2 ≤ 2 ^ m := by
    have h0 : 1 < Nat.card F := Finite.one_lt_card
    rw [hF] at h0
    omega
  have h2 : 2 ^ m = 2 := l3core_q_eq_two hq h1
  have h3 : 2 ^ m = 2 ^ 1 := by rw [pow_one]; exact h2
  exact Nat.pow_right_injective (le_refl 2) h3

theorem l3Core_of_piece {G : Subgroup (MulAut V)} {W C : Subgroup V} (hL : IsL32 G) (hCW : C ≤ W)
    (hinv : ∀ g ∈ G, ∀ w ∈ W, g w ∈ W) (h : B56Piece G W C) :
    ∃ M : Subgroup V, M ≤ W ∧ M ≤ commV G ⊔ C ∧ L3Coord G M C := by
  rcases h with ⟨hW, h⟩ | ⟨hW, m, K, hFld, hFin, hK, hd⟩ | ⟨-, -, -, -, hc⟩
  ·
    have hG : Nat.card ↥G = 168 := l3core_card_L32 hL
    rcases h with ⟨n, hn⟩ | hS | ⟨m, hm⟩
    · exact (l3core_not_sl2 hG hn).elim
    · exact (l3core_not_sym5 hG hS).elim
    · have hm1 : m = 1 := bnat_m_eq_one hL hm
      subst hm1
      exact ⟨W, le_rfl, hW.le, BinaryNaturalSL.toL3Coord hm⟩
  ·
    obtain ⟨I, π, -, -, hsum, hreal⟩ := hd
    have hI0W : I ⟨0, by norm_num⟩ ≤ W := by
      rw [← hsum]
      exact le_sup_of_le_right (le_iSup I ⟨0, by norm_num⟩)
    have hBNS : BinaryNaturalSL G (I ⟨0, by norm_num⟩) C 3 m :=
      ⟨K, hFld, hFin, hK, ⟨π, hreal ⟨0, by norm_num⟩⟩⟩
    have hm1 : m = 1 := bnat_m_eq_one hL hBNS
    subst hm1
    exact ⟨I ⟨0, by norm_num⟩, hI0W, hI0W.trans hW.le, BinaryNaturalSL.toL3Coord hBNS⟩
  ·
    exact ⟨modComm G W ⊔ C, sup_le (l3core_modComm_le hinv) hCW,
      sup_le (le_trans (l3core_modComm_le_commV W) le_sup_left) le_sup_right,
      BinaryNaturalSL.toL3Coord hc⟩

end CFSG.Quasithin.C116Three
