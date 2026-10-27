module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23NeDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23AO2A
import CFSG.Quasithin.Background.E6TwentyTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23AStep

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem c23ne_lt_rParam {M V₀ V N₁ N₂ Y : Subgroup G} {k : ℕ} (hk : k ≤ 2)
    (hP : C23NePair M V₀ V N₁ N₂ Y) (hN : normalizer (V : Set G) = M) :
    (k : ℕ∞) < E3.rParam V := by
  refine lt_of_lt_of_le (b := ((k + 1 : ℕ) : ℕ∞)) ?_ ?_
  · exact_mod_cast Nat.lt_succ_self k
  · rw [E3.rParam]
    refine le_iInf₂ fun U hU => ?_
    obtain ⟨hUV, hnot⟩ := hU
    have hgoal : k + 1 ≤ E3.mQuot V U := by
      by_contra hlt
      have hmk : E3.mQuot V U ≤ k := Nat.lt_succ_iff.1 (not_le.1 hlt)
      have hm2 : E3.mQuot V U ≤ 2 := hmk.trans hk
      have hWi := E6.mQuot_inf_left_le (V := V) (U := N₁) (U' := U) hP.elem.isPGroup hP.le₁
      have hWU : E3.mQuot N₁ (N₁ ⊓ U) ≤ 2 := hWi.trans hm2
      have hsub := c23a_o2_mQuot_eq_rk_sub (V := N₁) (U := N₁ ⊓ U) inf_le_left
      have hfive : 5 ≤ rk ↥N₁ := by simpa only [mSub] using hP.rank_N₁.ge
      have hge1 : 1 ≤ rk ↥(N₁ ⊓ U) := by omega
      have hne : N₁ ⊓ U ≠ ⊥ := by
        intro hbot
        have h0 : rk ↥(N₁ ⊓ U) = 0 := by rw [hbot]; exact rk_bot
        omega
      obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
      have hwW : (a : G) ∈ N₁ := (Subgroup.mem_inf.1 a.2).1
      have hwU : (a : G) ∈ U := (Subgroup.mem_inf.1 a.2).2
      have hw1 : (a : G) ≠ 1 := fun h => ha1 (Subtype.ext h)
      have hcent : centralizer (U : Set G) ≤ M :=
        (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hwU)).trans
          (hP.cent (a : G) (Or.inl hwW) hw1)
      exact hnot (by rw [hN]; exact hcent)
    exact_mod_cast hgoal

private theorem c23ne_commElt_ne_bot {V : Subgroup G} {t : G}
    (h : ¬ V ≤ centralizer ({t} : Set G)) : commElt V t ≠ ⊥ := by
  intro hb
  apply h
  intro w hw
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 : w⁻¹ * t⁻¹ * w * t ∈ commElt V t := Subgroup.subset_closure ⟨w, hw, rfl⟩
  rw [hb, Subgroup.mem_bot] at h1
  calc w * t = (t * w) * (w⁻¹ * t⁻¹ * w * t) := by group
    _ = t * w := by rw [h1, mul_one]

theorem c23ne_lt_betaN {M V₀ V N₁ N₂ Y : Subgroup G} {k : ℕ} (hk : k ≤ 2)
    (hP : C23NePair M V₀ V N₁ N₂ Y)
    (h2 : ∀ t ∈ M, (∃ j : ℕ, orderOf t = 2 ^ j) → ¬ V ≤ centralizer ({t} : Set G) →
      mSub (commElt V t) ≤ 2 → commElt V t ≤ N₁ ∨ commElt V t ≤ N₂) :
    (k : ℕ∞) < betaN 0 M V := by
  refine lt_of_lt_of_le (b := ((k + 1 : ℕ) : ℕ∞)) ?_ ?_
  · exact_mod_cast Nat.lt_succ_self k
  · rw [betaN]
    refine le_iInf₂ fun U hU => ?_
    obtain ⟨hUV, t, ⟨htM, htC⟩, ⟨j, hj⟩, W₁, hW₁V, hmW₁, hUW₁, hW₁t, hPcomm⟩ := hU
    have hgoal : k + 1 ≤ E3.mQuot V U := by
      by_contra hlt
      have hmk : E3.mQuot V U ≤ k := Nat.lt_succ_iff.1 (not_le.1 hlt)
      have hm2 : E3.mQuot V U ≤ 2 := hmk.trans hk
      have hW₁eq : W₁ = V :=
        (E3.mQuot_eq_zero_iff hP.elem.isPGroup hW₁V).1 (Nat.le_zero.1 hmW₁)
      subst W₁
      have hUle : U ≤ V ⊓ centralizer ({t} : Set G) := fun u hu =>
        Subgroup.mem_inf.2 ⟨hUV hu, Subgroup.mem_centralizer_iff.2 (fun h hh => by
          rw [Set.mem_singleton_iff] at hh
          subst hh
          exact (Subgroup.mem_centralizer_iff.1 htC u hu).symm)⟩
      have hmVU : E3.mQuot V (V ⊓ centralizer ({t} : Set G)) ≤ 2 :=
        (E3.mQuot_mono hUle).trans hm2
      have hcomm : mSub (commElt V t) = E3.mQuot V (V ⊓ centralizer ({t} : Set G)) := by
        have hsplit := c23a_mSub_commElt_add hP.elem (hP.norm htM)
        have hquot := c23a_o2_mQuot_eq_rk_sub (V := V) (U := V ⊓ centralizer ({t} : Set G))
          inf_le_left
        simp only [mSub] at hsplit hquot ⊢
        omega
      have hmcomm : mSub (commElt V t) ≤ 2 := hcomm.trans_le hmVU
      have hside := h2 t htM ⟨j, hj⟩ hW₁t hmcomm
      have hne : commElt V t ≠ ⊥ := c23ne_commElt_ne_bot hW₁t
      obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
      have hwm : (a : G) ∈ commElt V t := a.2
      have hw1 : (a : G) ≠ 1 := fun h => ha1 (Subtype.ext h)
      have hwblock : (a : G) ∈ (N₁ : Set G) ∪ (N₂ : Set G) := by
        rcases hside with hle | hle
        · exact Or.inl (hle hwm)
        · exact Or.inr (hle hwm)
      have hcent : centralizer (commElt V t : Set G) ≤ M :=
        (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hwm)).trans
          (hP.cent (a : G) hwblock hw1)
      exact hPcomm hcent
    exact_mod_cast hgoal

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
