module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BetaDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSpLift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenWitt

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16c13beta_centralizer_le_of_fix (D : Data G) (h61 : UC6.R6_1 D) {V₀ V : Subgroup G}
    (hV : IsElemAbelian 2 V) (h : Hyp125 D V₀ V) (h4 : Nat.card V₀ ≤ 4) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpσ : p ∈ D.sig) {Z : Subgroup G} {z : Vtil V₀ V hV}
    (hz : z ∈ imgTil V₀ V hV Z) (hz1 : z ≠ 1) {E : Subgroup (MulAut (Vtil V₀ V hV))}
    (hEX : E ≤ Mbar D.M V₀ V hV) (hEp : IsPGroup p ↥E) (hEc : ¬ IsCyclic ↥E)
    (hfix : ∀ e ∈ E, e z = z) : centralizer (Z : Set G) ≤ D.M := by
  classical
  obtain ⟨x, hxZ, hxz⟩ := (mem_imgTil V₀ V hV Z z).1 hz
  have hx0 : x.val ∉ V₀ := by
    intro hxV₀
    apply hz1
    rw [← hxz]
    exact (QuotientGroup.eq_one_iff (N := modNull V₀ V hV) x).2
      ((mem_modNull V₀ V hV x).2 hxV₀)
  have hcase : V₀ = ⊥ ∨ InCalV0 D.M V₀ V := by
    rcases h.1 with ⟨-, h0⟩ | ⟨h0, -⟩
    · exact Or.inl h0
    · exact Or.inr h0
  have hE : E ≤ ptCent (Mbar D.M V₀ V hV) (mkTil V₀ V hV x) := by
    intro e he
    refine Subgroup.mem_inf.2 ⟨hEX he, ?_⟩
    rw [MulAction.mem_stabilizer_iff, MulAut.smul_def, hxz]
    exact hfix e he
  exact (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hxZ)).trans
    (centralizer_le_of_noncyclic_bar D h61 hp hp2 hpσ hV h.pairFacts hcase h4 x hx0 hE hEp hEc)

theorem s16c13beta_betaN_lt (D : Data G) (h61 : UC6.R6_1 D) {V₀ V : Subgroup G}
    (hV : IsElemAbelian 2 V) (h : Hyp125 D V₀ V) (h4 : Nat.card V₀ ≤ 4) {p k : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpσ : p ∈ D.sig)
    (hgood : s16c13betaGood (Mbar D.M V₀ V hV) p k (k + 2)) :
    ((k + 1 : ℕ) : ℕ∞) < betaN k D.M V := by
  have hMV : D.M ≤ normalizer (V : Set G) := h.pairFacts.le_normalizer
  have hMV₀ : D.M ≤ normalizer (V₀ : Set G) := h.pairFacts.le_normalizer₀
  have hMs : D.M ≤ stabTil V₀ V := le_stabTil hMV hMV₀
  have hall : ∀ U ∈ calBn k D.M V, k + 2 ≤ E3.mQuot V U := by
    intro U hU
    obtain ⟨hUV, t, ⟨htM, htU⟩, ht2, W, hWV, hWn, hUW, hWt, hB⟩ := hU
    by_contra hlt
    have hlt' : E3.mQuot V U ≤ k + 1 := by omega
    have hUt : U ≤ V ⊓ centralizer ({t} : Set G) := by
      refine le_inf hUV fun u hu => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.1 htU u hu
    have hrank : E3.mQuot V (V ⊓ centralizer ({t} : Set G)) ≤ k + 1 :=
      (E3.mQuot_mono hUt).trans hlt'
    obtain ⟨w, hwW, hw1⟩ := s16n9b_exists_commutator_ne_one hWt
    have hwmem : w⁻¹ * t⁻¹ * w * t ∈ commElt W t := Subgroup.subset_closure ⟨w, hwW, rfl⟩
    by_cases hw0 : w⁻¹ * t⁻¹ * w * t ∈ V₀
    · exact hB (centralizer_le_M_of_mem_inf_V₀ D h hwmem hw0 hw1)
    · let g : ↥(stabTil V₀ V) := ⟨t, hMs htM⟩
      have hφM : actTil V₀ V hV g⁻¹ ∈ Mbar D.M V₀ V hV :=
        actTil_mem_barSub V₀ V hV (D.M.inv_mem htM) ((stabTil V₀ V).inv_mem g.2)
      have hφ2 : ∃ a : ℕ, orderOf (actTil V₀ V hV g⁻¹) = 2 ^ a := by
        obtain ⟨a, ha⟩ := ht2
        have hdvd : orderOf (actTil V₀ V hV g⁻¹) ∣ 2 ^ a := by
          refine (orderOf_map_dvd (actTil V₀ V hV) g⁻¹).trans ?_
          rw [orderOf_inv, ← ha]
          exact (Subgroup.orderOf_coe g).symm.dvd
        obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
        exact ⟨b, hb⟩
      have hrank' : rkIdx (fixV (Subgroup.zpowers (actTil V₀ V hV g⁻¹))) ≤ k + 2 := by
        have hle := (s16n9b_rkIdx_fixV_le V₀ V hV g).trans hrank
        omega
      have hU' : rkIdx (imgTil V₀ V hV W) ≤ k :=
        (s16n9b_rkIdx_imgTil_le V₀ V hV W).trans hWn
      have hUφ : ¬ imgTil V₀ V hV W ≤ fixV (Subgroup.zpowers (actTil V₀ V hV g⁻¹)) :=
        s16n9b_not_le_fixV_of_commutator V₀ V hV g hwW (hWV hwW) hw0
      obtain ⟨zt, hzt, hzt1, E, hEX, hEp, hEc, hfix⟩ :=
        hgood (actTil V₀ V hV g⁻¹) hφM hφ2 hrank' (imgTil V₀ V hV W) hU' hUφ
      have hzt' : zt ∈ imgTil V₀ V hV (commElt W t) :=
        s16n9b_commOn_le_imgTil V₀ V hV W g hzt
      exact hB (s16c13beta_centralizer_le_of_fix D h61 hV h h4 hp hp2 hpσ
        (Z := commElt W t) hzt' hzt1 hEX hEp hEc hfix)
  have hki : k + 1 + 1 = k + 2 := by omega
  have hle : ((k + 1 + 1 : ℕ) : ℕ∞) ≤ betaN k D.M V := by
    rw [hki]
    unfold betaN
    refine le_iInf₂ fun U hU => ?_
    exact_mod_cast hall U hU
  exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self (k + 1)) hle

theorem s16c13beta_rMV_lt (D : Data G) (h61 : UC6.R6_1 D) {V₀ V : Subgroup G}
    (hV : IsElemAbelian 2 V) (h : Hyp125 D V₀ V) (h4 : Nat.card V₀ ≤ 4) {p k : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpσ : p ∈ D.sig)
    (hpts : s16c13betaPts (Mbar D.M V₀ V hV) p (k + 1)) :
    ((k + 1 + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V := by
  have hV₀V : V₀ ≤ V := h.pairFacts.le
  have hrk : rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) + mSub V₀ = mSub V :=
    rk_top_vtil_add_mSub V₀ V hV hV₀V
  have htop : k + 2 ≤ rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) := by
    by_contra hlt
    have hlt' : rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) ≤ k + 1 := by omega
    have hidx : rkIdx (⊥ : Subgroup (Vtil V₀ V hV)) ≤ k + 1 := by
      have hbot : rkIdx (⊥ : Subgroup (Vtil V₀ V hV)) =
          rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) := by
        have h := rk_add_rkIdx (⊥ : Subgroup (Vtil V₀ V hV))
        rw [rk_bot, zero_add] at h
        rw [h, rk_top]
      rw [hbot]
      exact hlt'
    obtain ⟨z, hzbot, hz1, -⟩ := hpts (⊥ : Subgroup (Vtil V₀ V hV)) hidx
    exact hz1 (Subgroup.mem_bot.1 hzbot)
  have hbc : (rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) - (k + 2)) + (k + 2 + mSub V₀) ≤ mSub V := by
    omega
  have hb : ∀ U : Subgroup G, U ≤ V → ¬ centralizer (U : Set G) ≤ D.M →
      rk ↥(imgTil V₀ V hV U) ≤ rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) - (k + 2) := by
    intro U _ hUC
    by_contra hb'
    have hidx : rkIdx (imgTil V₀ V hV U) ≤ k + 1 := by
      have h := rk_add_rkIdx (imgTil V₀ V hV U)
      have hrt : rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) = rk (Vtil V₀ V hV) := rk_top
      have hb'' := not_le.1 hb'
      omega
    obtain ⟨z, hz, hz1, E, hEX, hEp, hEc, hfix⟩ := hpts (imgTil V₀ V hV U) hidx
    exact hUC (s16c13beta_centralizer_le_of_fix D h61 hV h h4 hp hp2 hpσ
      (Z := U) hz hz1 hEX hEp hEc hfix)
  have hle : ((k + 2 + mSub V₀ : ℕ) : ℕ∞) ≤ rMV D.M V :=
    le_rMV_of_forall_rk_imgTil_le D h hbc hb
  exact lt_of_lt_of_le (by exact_mod_cast (by omega :
    k + 1 + mSub V₀ < k + 2 + mSub V₀)) hle

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
