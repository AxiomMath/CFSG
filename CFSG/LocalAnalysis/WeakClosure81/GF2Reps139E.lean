module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139F

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps139

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W] {G X D : Subgroup (MulAut W)} {s : MulAut W}
  {Y : Subgroup W} {n : ℕ}

theorem Std139.lemmaE (hw2 : ∀ w : W, w ^ 2 = 1) (S : Std139 G X D s Y n) (hn : 3 ≤ n)
    (hC : DNormComp G D) {K₁ K₂ : Subgroup (MulAut W)} (h1 : IsComponentOf K₁ G)
    (h2 : IsComponentOf K₂ G) (hK1 : ¬ K₁ ≤ Subgroup.centralizer (D : Set (MulAut W)))
    (hK2 : ¬ K₂ ≤ Subgroup.centralizer (D : Set (MulAut W))) : K₁ = K₂ := by
  classical
  by_contra hne
  obtain ⟨hF1sup, hF1inf, hF1Y, hF1axis, hF1irr⟩ :=
    Std139.lemmaF hw2 S hn hC h1 hK1
  obtain ⟨hF2sup, hF2inf, hF2Y, hF2axis, hF2irr⟩ :=
    Std139.lemmaF hw2 S hn hC h2 hK2
  have hDgt : 1 < Nat.card D := by
    rw [S.Dcard]
    have h2' : 2 ≤ n - 1 := by omega
    calc 1 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) h2'
  have hDne : D ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hDgt
    omega
  obtain ⟨⟨e, heD⟩, he1sub⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hDne
  have he1 : e ≠ 1 := fun h => he1sub (Subtype.ext h)
  have hK1K2 : ⁅K₁, K₂⁆ = ⊥ :=
    CFSG.LargeExtraspecial.S5.commute_of_isComponentOf_ne h1 h2 hne
  have hMR : ⁅K₁ ⊔ X, K₂⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    refine sup_le ?_ ?_
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hK1K2
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact Std139.component_commutes_X S h2 y hy x hx
  have hR : ⁅K₂, K₂⁆ = K₂ := by
    haveI : Group.IsPerfect ↥K₂ := ⟨h2.2.2.1⟩
    exact Subgroup.commutator_eq_self
  have hYR : StableUnder K₂ (commSub ⊤ K₁) := by
    have hK1leC : K₁ ≤ Subgroup.centralizer (K₂ : Set (MulAut W)) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hK1K2
    have hcomm : ∀ y ∈ K₁, ∀ b ∈ K₂, y * b = b * y := by
      intro y hy b hb
      exact (Subgroup.mem_centralizer_iff.mp (hK1leC hy) b hb).symm
    exact CFSG.Quasithin.B1.commSub_invariant_of_commute (Y := K₁) (B := K₂) (M := ⊤)
      hcomm (fun _ _ m _ => Subgroup.mem_top m)
  have hU1K : StableUnder K₁ (commSub ⊤ K₁) := hF1irr.2.1
  have hU1X : StableUnder X (commSub ⊤ K₁) := hF1irr.2.2.1
  have hU1ne : commSub ⊤ K₁ ≠ ⊥ := hF1irr.1
  have hmin : ∀ C : Subgroup W, StableUnder K₁ C → StableUnder X C →
      C ≤ commSub ⊤ K₁ → C = ⊥ ∨ C = commSub ⊤ K₁ := hF1irr.2.2.2
  have hfixMle : fixV (K₁ ⊔ X) ≤ fixV K₁ := by
    intro w hw
    rw [mem_fixV] at hw ⊢
    intro k hk
    exact hw k (Subgroup.mem_sup_left hk)
  have hNbot : commSub ⊤ K₁ ⊓ fixV (K₁ ⊔ X) = ⊥ := by
    apply le_bot_iff.mp
    refine (le_inf ?_ ?_).trans (le_of_eq hF1inf)
    · exact inf_le_right.trans hfixMle
    · exact inf_le_left
  have hYM : StableUnder (K₁ ⊔ X) (commSub ⊤ K₁) := by
    intro g hg
    rw [Subgroup.sup_eq_closure] at hg
    induction hg using Subgroup.closure_induction'' with
    | mem g hg =>
        rcases hg with hg | hg
        · exact hU1K g hg
        · exact hU1X g hg
    | inv_mem g hg =>
        rcases hg with hg | hg
        · exact hU1K g⁻¹ (K₁.inv_mem hg)
        · exact hU1X g⁻¹ (X.inv_mem hg)
    | one => intro v hv; exact hv
    | mul g h _ _ ihg ihh => intro v hv; exact ihg _ (ihh v hv)
  have hirr : IsIrrOn (K₁ ⊔ X) (commSub ⊤ K₁)
      (commSub ⊤ K₁ ⊓ fixV (K₁ ⊔ X)) := by
    refine ⟨?_, hYM, ?_, ?_⟩
    · rw [hNbot]
      exact bot_lt_iff_ne_bot.mpr hU1ne
    · intro m hm u hu
      refine ⟨hYM m hm u hu.1, ?_⟩
      refine mem_fixV.mpr ?_
      intro m' hm'
      rw [mem_fixV.mp hu.2 m hm]
      exact mem_fixV.mp hu.2 m' hm'
    · intro J hJM hNJ hJU
      have hJK : StableUnder K₁ J :=
        fun k hk j hj => hJM k (Subgroup.mem_sup_left hk) j hj
      have hJX : StableUnder X J :=
        fun x hx j hj => hJM x (Subgroup.mem_sup_right hx) j hj
      rcases hmin J hJK hJX hJU with hJ | hJ
      · left
        rw [hJ, hNbot]
      · exact Or.inr hJ
  have hW' : ∀ w : W, w * w = 1 := fun w => by rw [← pow_two]; exact hw2 w
  have hschur : commSub (commSub ⊤ K₁) K₂ ≤ commSub ⊤ K₁ ⊓ fixV (K₁ ⊔ X) :=
    s13_schur_perfect hW' (K₁ ⊔ X) K₂ hMR hR (commSub ⊤ K₁) hYM hYR hirr
  have hU1fixK2 : commSub ⊤ K₁ ≤ fixV K₂ := by
    have hbot : commSub (commSub ⊤ K₁) K₂ = ⊥ := by
      rw [hNbot] at hschur
      exact le_bot_iff.mp hschur
    exact commSub_eq_bot_iff.mp hbot
  have hWe1 : commSub ⊤ (Subgroup.zpowers e) ≤ commSub ⊤ K₁ :=
    (hF1axis e heD he1).trans inf_le_left
  have hWe2 : commSub ⊤ (Subgroup.zpowers e) ≤ commSub ⊤ K₂ :=
    (hF2axis e heD he1).trans inf_le_left
  have hWe_bot : commSub ⊤ (Subgroup.zpowers e) = ⊥ := by
    have h : commSub ⊤ (Subgroup.zpowers e) ≤ fixV K₂ ⊓ commSub ⊤ K₂ :=
      le_inf (hWe1.trans hU1fixK2) hWe2
    rw [hF2inf] at h
    exact le_bot_iff.mp h
  have hrk : rk ↥(commSub ⊤ (Subgroup.zpowers e)) = 2 :=
    (Std139.commSub_axis hw2 S heD he1).1
  rw [hWe_bot, rk_bot] at hrk
  omega

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps139
