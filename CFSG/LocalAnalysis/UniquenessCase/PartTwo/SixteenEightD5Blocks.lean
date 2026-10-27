module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightD5Cop
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightD5Frame
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightD5Lines

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {W : Type} [CommGroup W] [Finite W]

private theorem s16e_d5_rk_sup_of_disjoint {U V : Subgroup W} (h : Disjoint U V) :
    rk ↥(U ⊔ V) = rk U + rk V := by
  have h1 := rk_sup_add_rk_inf U V
  rw [disjoint_iff.mp h, rk_bot, add_zero] at h1
  exact h1

private lemma s16e_d5_card_pi_zmod (p n : ℕ) [NeZero p] :
    Nat.card (Multiplicative (Fin n → ZMod p)) = p ^ n := by
  rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, Fintype.card_pi_const]
  simp

private lemma s16e_d5_card_elemAbelian (p n : ℕ) [NeZero p] {X : Type*} [Group X]
    (h : IsElemAbelianOfRank p n X) : Nat.card X = p ^ n := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  exact s16e_d5_card_pi_zmod p n

private lemma s16e_d5_comm_pow {p n : ℕ} {X : Type*} [Group X]
    (h : IsElemAbelianOfRank p n X) :
    (∀ a b : X, a * b = b * a) ∧ ∀ a : X, a ^ p = 1 := by
  obtain ⟨e⟩ := h
  refine ⟨fun a b => e.injective ?_, fun a => e.injective ?_⟩
  · rw [map_mul, map_mul, mul_comm]
  · rw [map_pow, map_one]
    ext i
    simp

theorem s16e_d5_Z_top (hW : ∀ w : W, w ^ 2 = 1) {K : Fin 4 → Subgroup (MulAut W)}
    (hrk8 : rk ↥(⊤ : Subgroup W) = 8) (hrk2 : ∀ i, rk ↥(fixV (K i)) = 2)
    (hind : iSupIndep (fun i => fixV (K i))) : (⨆ i, fixV (K i)) = ⊤ := by
  let S : Fin 4 → Subgroup W := fun i => fixV (K i)
  have hZrk : ∀ i, rk ↥(S i) = 2 := fun i => hrk2 i
  have hindS : iSupIndep S := hind
  have hsup : (⨆ i, S i) = S 0 ⊔ S 1 ⊔ S 2 ⊔ S 3 := by
    apply le_antisymm
    · refine iSup_le fun i => ?_
      fin_cases i
      · exact le_trans (le_trans le_sup_left le_sup_left) le_sup_left
      · exact le_trans (le_trans le_sup_right le_sup_left) le_sup_left
      · exact le_trans le_sup_right le_sup_left
      · exact le_sup_right
    · exact sup_le (sup_le (sup_le (le_iSup S 0) (le_iSup S 1)) (le_iSup S 2)) (le_iSup S 3)
  have h01 : Disjoint (S 0) (S 1) := hindS.pairwiseDisjoint (by decide)
  have h12 : Disjoint (S 0 ⊔ S 1) (S 2) := by
    have h := (iSupIndep_def.mp hindS 2).symm
    refine Disjoint.mono_left ?_ h
    refine sup_le ?_ ?_
    · exact le_iSup₂_of_le 0 (by decide) le_rfl
    · exact le_iSup₂_of_le 1 (by decide) le_rfl
  have h123 : Disjoint (S 0 ⊔ S 1 ⊔ S 2) (S 3) := by
    have h := (iSupIndep_def.mp hindS 3).symm
    refine Disjoint.mono_left ?_ h
    refine sup_le ?_ ?_
    · exact sup_le (le_iSup₂_of_le 0 (by decide) le_rfl)
        (le_iSup₂_of_le 1 (by decide) le_rfl)
    · exact le_iSup₂_of_le 2 (by decide) le_rfl
  have hrk01 : rk ↥(S 0 ⊔ S 1) = 4 := by
    rw [s16e_d5_rk_sup_of_disjoint h01, hZrk 0, hZrk 1]
  have hrk012 : rk ↥((S 0 ⊔ S 1) ⊔ S 2) = 6 := by
    rw [s16e_d5_rk_sup_of_disjoint h12, hrk01, hZrk 2]
  have hrk0123 : rk ↥(((S 0 ⊔ S 1) ⊔ S 2) ⊔ S 3) = 8 := by
    rw [s16e_d5_rk_sup_of_disjoint h123, hrk012, hZrk 3]
  have hrkiSup : rk ↥(⨆ i, S i) = 8 := by
    rw [hsup]
    exact hrk0123
  have htop : (⨆ i, S i) = ⊤ :=
    eq_of_le_of_rk_le hW le_top (by simp [hrk8, hrkiSup])
  simpa [S] using htop

theorem s16e_d5_blocks (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    (hL : IsElemAbelianOfRank 3 2 ↥L) (hWL : commSub ⊤ L = ⊤) (hrk8 : rk ↥(⊤ : Subgroup W) = 8)
    (hrk6 : ∀ x ∈ L, x ≠ 1 → rk ↥(commSub ⊤ (Subgroup.zpowers x)) = 6) :
    ∃ (K : Fin 4 → Subgroup (MulAut W)) (Z : Fin 4 → Subgroup W), s16e_d5_Frame L K Z := by
  have hcard : Nat.card ↥L = 9 := by
    rw [s16e_d5_card_elemAbelian 3 2 hL]
    norm_num
  have hcp := s16e_d5_comm_pow hL
  obtain ⟨K, hKle, hKcard, hKinj, hKall⟩ := s16e_d5_four_lines hL
  have hfixL : fixV L = ⊥ := s16e_d5_fixV_L_eq_bot hW hL hWL
  have hZindep : iSupIndep (fun i => fixV (K i)) :=
    s16e_d5_Z_indep hW hL hfixL hKle hKcard hKinj
  have hZrk : ∀ i, rk ↥(fixV (K i)) = 2 := by
    intro i
    have hKne : K i ≠ ⊥ := by
      intro hbot
      have hKi := hKcard i
      rw [hbot, Subgroup.card_bot] at hKi
      exact absurd hKi (by norm_num)
    obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hKne
    have haKi : (x : MulAut W) ∈ K i := x.2
    have haL : (x : MulAut W) ∈ L := hKle i x.2
    have ha1 : (x : MulAut W) ≠ 1 := by
      intro h
      exact hx1 (Subtype.ext (by simpa using h))
    have hx3 : (x : MulAut W) ^ 3 = 1 := by
      have h := congrArg (fun z : ↥L => (z : MulAut W)) (hcp.2 ⟨(x : MulAut W), haL⟩)
      simpa using h
    have hord : orderOf (x : MulAut W) = 3 := orderOf_eq_prime hx3 ha1
    have hzp : Subgroup.zpowers (x : MulAut W) = K i := by
      apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr haKi)
      rw [hKcard i, Nat.card_zpowers, hord]
    have h2 := s16e_d5_rk_fixV_zpowers hW hx3 hrk8 (hrk6 (x : MulAut W) haL ha1)
    rw [← hzp]
    exact h2
  refine ⟨K, fun i => fixV (K i), ?_⟩
  refine
    { sq_W := hW
      elem_L := hL
      card_L := hcard
      comm_L := fun x hx y hy => by
        have h := congrArg (fun z : ↥L => (z : MulAut W)) (hcp.1 ⟨x, hx⟩ ⟨y, hy⟩)
        simpa using h
      pow_L := fun x hx => by
        have h := congrArg (fun z : ↥L => (z : MulAut W)) (hcp.2 ⟨x, hx⟩)
        simpa using h
      fixV_L := hfixL
      K_le := hKle
      K_card := hKcard
      K_inj := hKinj
      K_all := hKall
      Z_eq := fun i => rfl
      Z_rk := hZrk
      Z_indep := hZindep
      Z_top := s16e_d5_Z_top hW hrk8 hZrk hZindep }

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
