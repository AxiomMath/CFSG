module

public import CFSG.LocalAnalysis.StandardType.GGQTwoSixGensData
public import CFSG.ClassicalInvolution.Phan.Blocks
public import CFSG.LocalAnalysis.StandardType.GGQTwoSU34Aux6

public section

namespace CFSG.StandardType.QTwo.SixPoint

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem qTwoSixWin_hs (s : Fin 3) : s.val + 4 ≤ 6 := by
  have := s.isLt
  omega

theorem qTwoSixWinEmb_val {m k i : ℕ} (h : i + k ≤ m) (a : Fin k) :
    (qTwoSixWinEmb h a).val = a.val + i :=
  rfl

@[expose] noncomputable def qTwoSixWin_left : Su K 2 1 3 →* Su K 2 1 4 :=
  blockEmb K 2 1 4 3 1 (by omega)

@[expose] noncomputable def qTwoSixWin_right : Su K 2 1 3 →* Su K 2 1 4 :=
  blockEmb K 2 1 4 3 0 (by omega)

theorem qTwoSixWin_coordBlockSU_univ (k : ℕ) :
    coordBlockSU K 2 1 (Finset.univ : Finset (Fin k)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rw [mem_coordBlockSU_iff]
  intro a b hab
  rcases hab with h | h
  · exact absurd (Finset.mem_univ a) h
  · exact absurd (Finset.mem_univ b) h

theorem qTwoSixWin_map_coordBlockSU {m k i : ℕ} (h : i + k ≤ m) (J : Finset (Fin k)) :
    (coordBlockSU K 2 1 J).map (blockEmb K 2 1 m k i h) =
      coordBlockSU K 2 1 (J.map (qTwoSixWinEmb h)) := by
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro y ⟨x, hx, rfl⟩
    have hx' := (mem_coordBlockSU_iff (K := K) (p := 2) (f := 1) (J := J)).mp hx
    refine (mem_coordBlockSU_iff (K := K) (p := 2) (f := 1)
      (J := J.map (qTwoSixWinEmb h))).mpr ?_
    intro a b hab
    rw [coe_coe_blockEmb, blockMat_apply]
    by_cases hboth : (i ≤ a.val ∧ a.val < i + k) ∧ (i ≤ b.val ∧ b.val < i + k)
    · rw [dif_pos hboth]
      have ha : qTwoSixWinEmb h ⟨a.val - i, by omega⟩ = a := by
        ext
        rw [qTwoSixWinEmb_val]
        dsimp only
        omega
      have hb : qTwoSixWinEmb h ⟨b.val - i, by omega⟩ = b := by
        ext
        rw [qTwoSixWinEmb_val]
        dsimp only
        omega
      have hp : (⟨a.val - i, by omega⟩ : Fin k) ∉ J ∨
          (⟨b.val - i, by omega⟩ : Fin k) ∉ J := by
        rcases hab with h' | h'
        · exact Or.inl fun hJ => h' (by
            rw [← ha]
            exact Finset.mem_map.mpr ⟨_, hJ, rfl⟩)
        · exact Or.inr fun hJ => h' (by
            rw [← hb]
            exact Finset.mem_map.mpr ⟨_, hJ, rfl⟩)
      have hx'' := hx' _ _ hp
      have hiff : a = b ↔
          (⟨a.val - i, by omega⟩ : Fin k) = ⟨b.val - i, by omega⟩ := by
        constructor
        · intro hab'
          apply Fin.ext
          have hval := congrArg Fin.val hab'
          dsimp only at hval ⊢
          omega
        · intro hab'
          exact ha.symm.trans ((congrArg (qTwoSixWinEmb h) hab').trans hb)
      have hif : (if (⟨a.val - i, by omega⟩ : Fin k) = ⟨b.val - i, by omega⟩ then
          (1 : K) else 0) = if a = b then 1 else 0 := by
        by_cases hEq : a = b
        · rw [if_pos hEq, if_pos (hiff.mp hEq)]
        · rw [if_neg hEq, if_neg (fun h' => hEq (hiff.mpr h'))]
      exact hx''.trans hif
    · rw [dif_neg hboth]
      exact Matrix.one_apply
  · rw [Subgroup.card_map_of_injective (blockEmb_injective h),
      qTwoS34_card_coordBlockSU, qTwoS34_card_coordBlockSU, Finset.card_map]

theorem qTwoSixWin_range {m k i : ℕ} (h : i + k ≤ m) :
    (blockEmb K 2 1 m k i h).range =
      coordBlockSU K 2 1 (Finset.univ.map (qTwoSixWinEmb h)) := by
  rw [MonoidHom.range_eq_map, ← qTwoSixWin_coordBlockSU_univ (K := K) k]
  exact qTwoSixWin_map_coordBlockSU h Finset.univ

theorem qTwoSixWin_emb_injective (s : Fin 3) :
    Function.Injective (blockEmb K 2 1 6 4 s.val (qTwoSixWin_hs s)) :=
  blockEmb_injective (qTwoSixWin_hs s)

@[expose] def qTwoSixWin_supp (s : Fin 3) (i : Fin 18) : Finset (Fin 4) :=
  Finset.univ.filter fun a => qTwoSixWinEmb (qTwoSixWin_hs s) a ∈ qTwoSixData_support i

theorem qTwoSixWin_supp_map {s : Fin 3} {i : Fin 18}
    (hin : qTwoSixData_inWindow s i) :
    (qTwoSixWin_supp s i).map (qTwoSixWinEmb (qTwoSixWin_hs s)) = qTwoSixData_support i := by
  ext a
  rw [Finset.mem_map]
  constructor
  · rintro ⟨b, hb, rfl⟩
    simpa only [qTwoSixWin_supp, Finset.mem_filter, Finset.mem_univ, true_and] using hb
  · intro ha
    have hbounds := hin a ha
    refine ⟨⟨a.val - s.val, by omega⟩, ?_, ?_⟩
    · simp only [qTwoSixWin_supp, Finset.mem_filter, Finset.mem_univ, true_and]
      have hpre : qTwoSixWinEmb (qTwoSixWin_hs s) ⟨a.val - s.val, by omega⟩ = a := by
        ext
        rw [qTwoSixWinEmb_val]
        dsimp only
        omega
      rwa [hpre]
    · ext
      rw [qTwoSixWinEmb_val]
      dsimp only
      omega

theorem qTwoSixWin_supp_card {s : Fin 3} {i : Fin 18}
    (hin : qTwoSixData_inWindow s i) :
    (qTwoSixWin_supp s i).card = (qTwoSixData_support i).card := by
  rw [← qTwoSixWin_supp_map hin, Finset.card_map]

theorem qTwoSixWin_support_subset_window {s : Fin 3} {i : Fin 18}
    (hin : qTwoSixData_inWindow s i) :
    qTwoSixData_support i ⊆ Finset.univ.map (qTwoSixWinEmb (qTwoSixWin_hs s)) := by
  intro a ha
  rw [Finset.mem_map]
  have hbounds := hin a ha
  refine ⟨⟨a.val - s.val, by omega⟩, Finset.mem_univ _, ?_⟩
  ext
  rw [qTwoSixWinEmb_val]
  dsimp only
  omega

theorem qTwoSixWin_lift_exists (hK : Nat.card K = 4) (s : Fin 3) (i : Fin 18)
    (hin : qTwoSixData_inWindow s i) :
    ∃ x : Su K 2 1 4, blockEmb K 2 1 6 4 s.val (qTwoSixWin_hs s) x = nativeSu hK i := by
  have hmem : nativeSu hK i ∈
      coordBlockSU K 2 1 (Finset.univ.map (qTwoSixWinEmb (qTwoSixWin_hs s))) :=
    qTwoS34_coordBlockSU_mono (qTwoSixWin_support_subset_window hin)
      (qTwoSixData_native_mem hK i)
  rw [← qTwoSixWin_range (qTwoSixWin_hs s)] at hmem
  exact hmem

@[expose] noncomputable def qTwoSixWin_lift (hK : Nat.card K = 4) (s : Fin 3) :
    Fin 18 → Su K 2 1 4 := fun i =>
  if hin : qTwoSixData_inWindow s i then
    Classical.choose (qTwoSixWin_lift_exists hK s i hin)
  else 1

theorem qTwoSixWin_lift_eq (hK : Nat.card K = 4) (s : Fin 3) (i : Fin 18)
    (hs : s.val + 4 ≤ 6) (hin : qTwoSixData_inWindow s i) :
    blockEmb K 2 1 6 4 s.val hs (qTwoSixWin_lift hK s i) = nativeSu hK i := by
  have h := Classical.choose_spec (qTwoSixWin_lift_exists hK s i hin)
  simp only [qTwoSixWin_lift, dif_pos hin]
  exact h

theorem qTwoSixWin_lift_mem (hK : Nat.card K = 4) (s : Fin 3) (i : Fin 18)
    (hin : qTwoSixData_inWindow s i) :
    qTwoSixWin_lift hK s i ∈ coordBlockSU K 2 1 (qTwoSixWin_supp s i) := by
  have hparent : blockEmb K 2 1 6 4 s.val (qTwoSixWin_hs s) (qTwoSixWin_lift hK s i) ∈
      (coordBlockSU K 2 1 (qTwoSixWin_supp s i)).map
        (blockEmb K 2 1 6 4 s.val (qTwoSixWin_hs s)) := by
    rw [qTwoSixWin_map_coordBlockSU, qTwoSixWin_supp_map hin]
    rw [qTwoSixWin_lift_eq hK s i (qTwoSixWin_hs s) hin]
    exact qTwoSixData_native_mem hK i
  obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp hparent
  have hyl : y = qTwoSixWin_lift hK s i :=
    blockEmb_injective (qTwoSixWin_hs s) hxy
  rwa [hyl] at hy

end CFSG.StandardType.QTwo.SixPoint

end
