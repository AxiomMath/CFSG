module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BetaDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BetaCount
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBCase4Rank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

private theorem s16c13beta_fam_dParam_three : dParam 3 = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold dParam
  exact orderOf_eq_prime (by decide) (by decide)

private theorem s16c13beta_fam_dParam_seven : dParam 7 = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  unfold dParam
  exact orderOf_eq_prime (by decide) (by decide)

private theorem s16c13beta_fam_close {T : Type} [CommGroup T] [Finite T]
    (hT : ∀ t : T, t ^ 2 = 1) {X F : Subgroup (MulAut T)} {p r : ℕ} (hp : p = 3 ∨ p = 7)
    (hr : 3 < r) {ι : Type} [Fintype ι] {Y : ι → Subgroup T}
    (hrk : ∀ i, rk ↥(Y i) = dParam p) (hFX : F ≤ X) (hF : IsElemAbelian p F)
    (hFn : p ^ r ≤ Nat.card F) (hFY : ∀ f ∈ F, ∀ i, (Y i).map f.toMonoidHom = Y i)
    {a b : ι} {z : T} (hz : z ∈ Y a ⊔ Y b) :
    ∃ E : Subgroup (MulAut T), E ≤ X ∧ IsPGroup p ↥E ∧ ¬ IsCyclic ↥E ∧ ∀ e ∈ E, e z = z := by
  classical
  have hS : ({a, b} : Finset ι).card + 2 ≤ r := by
    have h2 := Finset.card_le_two (a := a) (b := b)
    omega
  obtain ⟨E, hEF, hEp, hEnc, hEfix⟩ :=
    s16c13beta_exists_noncyclic_fix hp hT hF hFn Y {a, b} (fun i _ => hrk i)
      (fun i _ f hf => hFY f hf i) hS
  refine ⟨E, hEF.trans hFX, hEp, hEnc, ?_⟩
  intro e he
  obtain ⟨y, hy, y', hy', rfl⟩ := Subgroup.mem_sup.mp hz
  rw [map_mul, hEfix a (by simp) e he y hy, hEfix b (by simp) e he y' hy']

theorem s16c13beta_fam_good {T : Type} [CommGroup T] [Finite T] (hT : ∀ t : T, t ^ 2 = 1)
    {X F : Subgroup (MulAut T)} {p k r : ℕ} (hp : p = 3 ∨ p = 7) (hr : 3 < r)
    (hk : k < dParam p) {ι : Type} [Fintype ι] {Y : ι → Subgroup T} (hind : iSupIndep Y)
    (hinj : Function.Injective Y) (hsup : ⨆ i, Y i = ⊤) (hrk : ∀ i, rk ↥(Y i) = dParam p)
    (hperm : ∀ g ∈ X, ∀ i, ∃ j, (Y i).map g.toMonoidHom = Y j) (hFX : F ≤ X)
    (hF : IsElemAbelian p F) (hFn : p ^ r ≤ Nat.card F)
    (hFY : ∀ f ∈ F, ∀ i, (Y i).map f.toMonoidHom = Y i)
    (hQ : p = 7 → ∃ Q : Subgroup (MulAut T), F ≤ Q ∧ Q ≤ X ∧ IsPGroup 7 ↥Q ∧
      (∀ φ ∈ X, Q.map (MulAut.conj φ).toMonoidHom = Q) ∧
      ∀ q ∈ Q, ∀ i, (Y i).map q.toMonoidHom = Y i) :
    s16c13betaGood X p k (k + 2) := by
  classical
  intro φ hφX h2 hC U hU hUφ
  have hC_lt : rkIdx (fixV (Subgroup.zpowers φ)) < 2 * dParam p := by
    rcases hp with hp3 | hp7
    · rw [hp3, s16c13beta_fam_dParam_three] at hk ⊢
      omega
    · rw [hp7, s16c13beta_fam_dParam_seven] at hk ⊢
      omega
  rcases s16n9b_case4_rank_moved hT hind hinj hrk (hperm φ hφX) hC_lt with
    hid | ⟨a, b, hab, hφa, hφb, -⟩
  · rcases hp with hp3 | hp7
    · have hk1 : k ≤ 1 := by
        rw [hp3, s16c13beta_fam_dParam_three] at hk
        omega
      obtain ⟨a, b, z, hz, hz1, hzab⟩ :=
        s16n9b_case4_rank_id hT hind hsup hk1 hid hU hUφ
      obtain ⟨E, hEX, hEp, hEnc, hEz⟩ :=
        s16c13beta_fam_close hT (Or.inl hp3) hr hrk hFX hF hFn hFY hzab
      exact ⟨z, hz, hz1, E, hEX, hEp, hEnc, hEz⟩
    · obtain ⟨Q, hFQ, hQX, hQp, hnorm, hQY⟩ := hQ hp7
      let C : Subgroup T := fixV (Subgroup.zpowers φ)
      set W : Subgroup T := ⨆ i : {i : ι // ¬ Y i ≤ C}, Y (i : ι) with hWdef
      set Q' : Subgroup T := ⨆ i : {i : ι // Y i ≤ C}, Y (i : ι) with hQ'def
      have hQ'C : Q' ≤ C := by
        rw [hQ'def]
        refine iSup_le ?_
        rintro i
        exact i.2
      have hWmap : W.map φ.toMonoidHom ≤ W := by
        rw [hWdef, Subgroup.map_iSup]
        refine iSup_le ?_
        rintro i
        rw [hid (i : ι)]
        exact le_iSup (fun j : {j : ι // ¬ Y j ≤ C} => Y (j : ι)) i
      have hWQ : W ⊔ Q' = ⊤ := by
        rw [eq_top_iff, ← hsup]
        refine iSup_le ?_
        intro i
        by_cases hi : Y i ≤ C
        · refine le_trans ?_ le_sup_right
          rw [hQ'def]
          exact le_iSup (fun j : {j : ι // Y j ≤ C} => Y (j : ι)) ⟨i, hi⟩
        · refine le_trans ?_ le_sup_left
          rw [hWdef]
          exact le_iSup (fun j : {j : ι // ¬ Y j ≤ C} => Y (j : ι)) ⟨i, hi⟩
      have hcomm : s16n9bCommOn U φ ≤ W := s16n9b_case4_rank_supp hWmap hQ'C hWQ U
      obtain ⟨z, hz, hz1⟩ := s16n9b_exists_commOn hUφ
      have hzW : z ∈ W := hcomm hz
      obtain ⟨E, hEF, hEp, hEnc, -⟩ :=
        s16c13beta_exists_noncyclic_fix (Or.inr hp7) hT hF hFn Y ∅ (by simp) (by simp)
          (by simp; omega)
      refine ⟨z, hz, hz1, E, hEF.trans hFX, hEp, hEnc, ?_⟩
      intro e he
      have heQ : (e : MulAut T) ∈ Q := hFQ (hEF he)
      have hWfix : W ≤ fixV (Subgroup.zpowers (e : MulAut T)) := by
        rw [hWdef]
        refine iSup_le ?_
        rintro ⟨i, hi⟩
        intro v hv
        rw [mem_fixV_zpowers_iff_apply]
        have hrki : rk ↥(Y i) = 3 := by
          rw [hrk i, hp7, s16c13beta_fam_dParam_seven]
        have hphi1 : ∃ y ∈ Y i, φ y ≠ y := by
          by_contra hcon
          apply hi
          intro y hy
          rw [mem_fixV_zpowers_iff_apply]
          by_contra hne
          exact hcon ⟨y, hy, hne⟩
        exact s16n9b_case4_aut_norm7 hT hrki hQp (fun q hq => hQY q hq i) h2 (hid i)
          (hnorm φ hφX) hphi1 e heQ v hv
      exact (mem_fixV_zpowers_iff_apply).1 (hWfix hzW)
  · obtain ⟨z, hz, hz1, hzab⟩ :=
      s16n9b_case4_rank_swap hT (hind.pairwiseDisjoint hab) (hrk a) (hrk b) hk hφa hφb hU
    obtain ⟨E, hEX, hEp, hEnc, hEz⟩ :=
      s16c13beta_fam_close hT hp hr hrk hFX hF hFn hFY hzab
    exact ⟨z, hz, hz1, E, hEX, hEp, hEnc, hEz⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
