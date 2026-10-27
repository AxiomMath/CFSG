module

public import CFSG.Quasithin.EmptyFaithful.SzN2Lin
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListRank2
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ParDef

public section

namespace CFSG.Quasithin.Rk2

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6 CFSG.Quasithin
open CFSG.QuasithinUnique.Vol2Native.A312L

variable {Y : Type} [Group Y] [Finite Y] {U : Subgroup Y} {P : Fin 2 → Subgroup Y}

omit [Finite Y] in
theorem Rank2Pkg.covBy (h : Rank2Pkg Y U P) (j : Fin 2) : P j ⋖ ⊤ :=
  ((h.res.2.2.1 (P j) (h.res.2.1 j)).2 ⟨j, rfl⟩)

omit [Finite Y] in
theorem Rank2Pkg.ne_top (h : Rank2Pkg Y U P) (j : Fin 2) : P j ≠ ⊤ := (h.covBy j).lt.ne

omit [Finite Y] in
theorem Rank2Pkg.le (h : Rank2Pkg Y U P) (j : Fin 2) : U ≤ P j := h.res.2.1 j

theorem Rank2Pkg.perfectCore_ne_bot (h : Rank2Pkg Y U P) (j : Fin 2) : perfectCore (P j) ≠ ⊥ := by
  intro hbot
  obtain ⟨K, hF, hFin, hCh, n, hK, hn, g, hg, -⟩ := h.levi j
  have hK4 : ∃ s : Finset K, s.card = 4 := by
    refine exists_finset_card_four ?_
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have : Group.IsSolvable ↥(perfectCore (P j)) := by rw [hbot]; infer_instance
  exact SzN2.not_isSolvable_sl2 hK4 (Group.isSolvable_of_surjective hg)

theorem Rank2Pkg.not_isSolvable_perfectCore (h : Rank2Pkg Y U P) (j : Fin 2) :
    ¬ Group.IsSolvable ↥(perfectCore (P j)) := by
  intro hs
  have h1 := (isSolvable_iff_perfectCore_eq_bot (perfectCore (P j))).1 hs
  rw [perfectCore_eq_self_of_perfect (perfectCore_perfect (P j))] at h1
  exact h.perfectCore_ne_bot j h1

theorem Rank2Pkg.not_isSolvable_of_le (h : Rank2Pkg Y U P) (j : Fin 2) {A : Subgroup Y}
    (hA : perfectCore (P j) ≤ A) : ¬ Group.IsSolvable ↥A := by
  intro hs
  have h1 := (isSolvable_iff_perfectCore_eq_bot A).1 hs
  have h2 : perfectCore (P j) ≤ perfectCore A :=
    le_perfectCore_of_perfect hA (perfectCore_perfect (P j))
  rw [h1, le_bot_iff] at h2
  exact h.perfectCore_ne_bot j h2

theorem Rank2Pkg.sup_perfectCore_eq_top (h : Rank2Pkg Y U P) :
    perfectCore (P 0) ⊔ perfectCore (P 1) ⊔ U = ⊤ := by
  by_contra hne
  set A := perfectCore (P 0) ⊔ perfectCore (P 1) ⊔ U with hA
  have hUA : U ≤ A := le_sup_right
  obtain ⟨j, hjk, -⟩ := h.res.2.2.2.2.1 A hUA hne
    (h.not_isSolvable_of_le 0 (le_sup_left.trans le_sup_left))
  have hAj : A ≤ P j := (hjk j).2 rfl
  set k : Fin 2 := j + 1 with hk
  have hkj : k ≠ j := by fin_cases j <;> decide
  have hPk : perfectCore (P k) ≤ A := by
    fin_cases j
    · exact le_sup_right.trans le_sup_left
    · exact le_sup_left.trans le_sup_left
  set M := perfectCore (P k) ⊔ U with hM
  have hMk : M ≤ P k := sup_le (perfectCore_le _) (h.le k)
  have hMA : M ≤ A := sup_le hPk hUA
  obtain ⟨l, hl, -⟩ := h.res.2.2.2.2.1 M le_sup_right (fun hT => h.ne_top k (top_le_iff.1
    (hT ▸ hMk))) (h.not_isSolvable_of_le k le_sup_left)
  have h1 : k = l := (hl k).1 hMk
  have h2 : j = l := (hl j).1 (hMA.trans hAj)
  exact hkj (h1.trans h2.symm)

end CFSG.Quasithin.Rk2
