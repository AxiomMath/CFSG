module

public import CFSG.RankThree.GF2n.Smith81.InspKStatements
public import CFSG.RankThree.GF2n.Smith81.InspKPSLCore
public import CFSG.Timmesfeld.RootOutcome
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatTypeDet
public import CFSG.Adapters.LieModelSmallOrders

public section

namespace CFSG.RankThree.GF2n.Smith81.Insp

open CFSG CFSG.Blueprint CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Orders
  CFSG.Timmesfeld.RankOne CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg Matrix
  CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n.Smith81.Insp.KFact

theorem KFact.exists_ne_mem_rootSet_of_card {G : Type} [Group G] {D : Set G}
    (hD : IsRootInvolutionSet D) {f : ℕ} (hf : 2 ≤ f)
    (hroot : ∀ d ∈ D, Nat.card (rootGroup D d) = 2 ^ f) {d : G} (hd : d ∈ D) :
    ∃ e ∈ rootSet D d, e ≠ d := by
  by_contra hcon
  push Not at hcon
  have hle : rootGroup D d ≤ Subgroup.zpowers d := by
    rw [rootGroup, Subgroup.closure_le]
    intro e he
    rw [hcon e he]
    exact Subgroup.mem_zpowers d
  have hcard : Nat.card (Subgroup.zpowers d) = 2 := by
    rw [Nat.card_zpowers]
    exact hD.1 d hd
  have hfin : Finite (Subgroup.zpowers d) := Nat.finite_of_card_ne_zero (by omega)
  have h1 := Subgroup.card_le_of_le hle
  rw [hroot d hd, hcard] at h1
  have h2 : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  omega

section CertBound


open Subgroup in
theorem KFact.exists_surjective_of_hyp_psl {Y : Type} [Group Y] {D : Set Y} (hH : Hyp Y D) {k f : ℕ}
    (hk : 3 ≤ k) (hf : 2 ≤ f) (hL : LieModel Y .PSL k 2 f)
    (hroot : ∀ d ∈ D, Nat.card (rootGroup D d) = 2 ^ f) :
    ∃ Ψ : SpecialLinearGroup (Fin k) (GaloisField 2 f) →* Y, Function.Surjective Ψ ∧
      Ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin k) (GaloisField 2 f)) ∧
      ∃ x : SpecialLinearGroup (Fin k) (GaloisField 2 f), IsTransvection x ∧ Ψ x ∈ D := by
  classical
  obtain ⟨d₀, hd₀⟩ : D.Nonempty := by
    obtain ⟨d, hd, -⟩ := hH.nondeg
    exact ⟨d, hd⟩
  have hl : ∃ d ∈ D, ∃ e ∈ rootSet D d, e ≠ d :=
    ⟨d₀, hd₀, exists_ne_mem_rootSet_of_card hH.root hf hroot hd₀⟩
  obtain ⟨hc, hs, hm⟩ := largeClosures hH hl
  have h := arsHyp_rootClass hH hc hs hm
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hZ := h.center
  have hcardf : ∀ {f' : ℕ}, (∀ E ∈ rootClass D, Nat.card E = 2 ^ f') → f' = f := by
    intro f' hE
    have h1 := hE _ ⟨d₀, hd₀, rfl⟩
    rw [hroot d₀ hd₀] at h1
    exact (Nat.pow_right_injective (le_refl 2) h1).symm
  rcases ARS.output_of_hyp Y (rootClass D) h with ⟨m, hm2, A, B, hX, hgen⟩ |
      ⟨m, hm4, A, B, hX, hgen⟩ | ⟨A, B, hX, hgen⟩ | ⟨A, B, hX, hgen⟩ | ⟨A, B, hX, hgen⟩ | hns
  · have hm0 : 0 < m := by omega
    obtain ⟨e₀, he₀, hAe⟩ := hX.memA ⟨0, hm0⟩
    have he₀A : e₀ ∈ A ⟨0, hm0⟩ := by
      rw [hAe]
      exact rootSet_subset_rootGroup D e₀ ⟨he₀, fun _ _ => Iff.rfl⟩
    have he₀1 : e₀ ≠ 1 := by
      intro h
      have := hH.root.1 e₀ he₀
      rw [h, orderOf_one] at this
      omega
    rcases Nat.lt_or_ge m 3 with hm3 | hm3
    · obtain rfl : m = 2 := by omega
      obtain ⟨f', hf', hcard', ρ, hρ, hedge⟩ :=
        hX.exists_frame hR hiso (isRootedTree_A (by omega))
      have hf'f : f' = f := hcardf hcard'
      subst hf'f
      obtain ⟨ψ, hψ⟩ := hedge 0 1 (by decide)
      have hu : ∀ i, Set.range (fun c => ρ i (tv 0 1 c)) = (A i : Set Y) := fun i => by
        rw [← (hρ i).2.1]
        exact Linear.range_tv_upper (ρ i)
      have hv : ∀ i, Set.range (fun c => ρ i (tv 1 0 c)) = (B i : Set Y) := fun i => by
        rw [← (hρ i).2.2]
        exact Linear.range_tv_lower (ρ i)
      have hsurj : Function.Surjective ψ := by
        rw [← MonoidHom.range_eq_top, eq_top_iff, ← hgen]
        refine iSup_le fun i => sup_le ?_ ?_
        · intro a ha
          rw [← SetLike.mem_coe, ← hu] at ha
          obtain ⟨c, rfl⟩ := ha
          fin_cases i
          · exact ⟨tv 0 1 c, (hψ c).1⟩
          · exact ⟨tv 1 2 c, (hψ c).2.2.1⟩
        · intro b hb
          rw [← SetLike.mem_coe, ← hv] at hb
          obtain ⟨c, rfl⟩ := hb
          fin_cases i
          · exact ⟨tv 1 0 c, (hψ c).2.1⟩
          · exact ⟨tv 2 1 c, (hψ c).2.2.2⟩
      obtain ⟨f'', hf'', -, hL'⟩ := hX.lieModel_A_two hR hiso hZ hgen
      obtain ⟨-, hmk, hff⟩ := CFSG.SeitzReduction.LinearPilot.lieModel_PSL_two_unique hk hL hL'
      have hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin 3) (GaloisField 2 f')) := by
        have : Nontrivial Y := ⟨⟨e₀, 1, he₀1⟩⟩
        rcases CFSG.LocalCores.quasisimple_normal_subgroups
            (SpecialLinear.isQuasisimple 2 (GaloisField 2 f') le_rfl) (MonoidHom.normal_ker ψ) with
          htop | hle
        · exfalso
          apply he₀1
          obtain ⟨l, hl⟩ := hsurj e₀
          rw [← hl]
          exact MonoidHom.mem_ker.mp (htop ▸ Subgroup.mem_top l)
        · exact hle
      subst hmk
      have he₀A' : e₀ ∈ Set.range (fun c => ρ 0 (tv 0 1 c)) := by
        rw [hu]
        exact he₀A
      obtain ⟨c, hc⟩ := he₀A'
      change ρ 0 (tv 0 1 c) = e₀ at hc
      have hc0 : c ≠ 0 := by
        rintro rfl
        apply he₀1
        rw [← hc]
        simp [tv]
      refine ⟨ψ, hsurj, hker, tv 0 1 c, ?_, ?_⟩
      · rw [tv_of_ne (by decide)]
        exact isTransvection_transvection _ hc0
      · rw [(hψ c).1, hc]
        exact he₀
    · obtain ⟨f', hf', hE, Ψ, hΨA, hΨB, hsurj, hker⟩ := hX.exists_surjective_A hR hiso hm3 hgen
      obtain ⟨f'', hf'', hE'', hL'⟩ := hX.lieModel_A hR hiso hZ hm3 hgen
      obtain ⟨-, hmk, hff⟩ := CFSG.SeitzReduction.LinearPilot.lieModel_PSL_two_unique hk hL hL'
      have hf'f : f' = f := hcardf hE
      subst hmk hf'f
      obtain ⟨x, hx, hxe⟩ := Subgroup.mem_map.mp ((SetLike.ext_iff.mp (hΨA ⟨0, hm0⟩) e₀).mpr he₀A)
      have hx1 : x ≠ 1 := fun h => he₀1 (by rw [← hxe, h, map_one])
      obtain ⟨i, j, hij, c, hc, rfl⟩ :=
        CFSG.StandardType.exists_transvection_of_mem_rootGroup hx hx1
      exact ⟨Ψ, hsurj, hker, _, isTransvection_transvection hij hc, by rw [hxe]; exact he₀⟩
  · obtain ⟨f', hf', hE, hL'⟩ := hX.lieModel_D hR hiso hZ hm4 hgen
    exact absurd (CFSG.SeitzReduction.LinearPilot.lieModel_PSL_two_unique hk hL hL').1 (by simp)
  · obtain ⟨f', hf', hE, hL'⟩ := hX.lieModel_E6 hR hiso hZ hgen
    exact absurd (CFSG.SeitzReduction.LinearPilot.lieModel_PSL_two_unique hk hL hL').1 (by simp)
  · obtain ⟨f', hf', hE, hL'⟩ := hX.lieModel_E7 hR hiso hZ hgen
    exact absurd (CFSG.SeitzReduction.LinearPilot.lieModel_PSL_two_unique hk hL hL').1 (by simp)
  · obtain ⟨f', hf', hE, hL'⟩ := hX.lieModel_E8 hR hiso hZ hgen
    exact absurd (CFSG.SeitzReduction.LinearPilot.lieModel_PSL_two_unique hk hL hL').1 (by simp)
  · obtain ⟨hns, -⟩ := hns
    rcases hns with ⟨n, f', hn, hf', hL'⟩ | ⟨n, f', hn, hf', hL'⟩ | ⟨f', hf', hL'⟩ |
        ⟨f', hf', t, ht, hL'⟩ | hL'
    · exact absurd (CFSG.SeitzReduction.LinearPilot.lieModel_PSL_two_unique hk hL hL').1 (by simp)
    · exact absurd (CFSG.SeitzReduction.LinearPilot.lieModel_PSL_two_unique hk hL hL').1 (by simp)
    · exact absurd (CFSG.SeitzReduction.LinearPilot.lieModel_PSL_two_unique hk hL hL').1 (by simp)
    · exact absurd (CFSG.SeitzReduction.LinearPilot.lieModel_PSL_two_unique hk hL hL').1 (by
        simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl <;> simp)
    · exfalso
      have hcard := (card_statedClassicalModel_two (hL.statedClassicalModel (by decide))).1 rfl
      have hpr : Profile (Nat.card Y) (f * ((k - 1) * (k - 1 + 1) / 2)) (zA (k - 1) f) := by
        rw [hcard]
        exact profile_ordA (by omega) (by omega)
      obtain ⟨r, hr, hm⟩ := hpr.two
      have hN : 6 ≤ f * ((k - 1) * (k - 1 + 1) / 2) := by
        have h1 : 6 ≤ (k - 1) * (k - 1 + 1) := by
          obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
          have e1 : j + 3 - 1 = j + 2 := by omega
          rw [e1]
          nlinarith
        have h2 : 3 ≤ (k - 1) * (k - 1 + 1) / 2 := by omega
        nlinarith
      have h6 : 2 ^ 6 ∣ Nat.card Y := by
        rw [hm]
        exact Dvd.dvd.mul_right (pow_dvd_pow 2 hN) r
      rw [CFSG.Blueprint.LieModel.card_psu_three_three hL'] at h6
      norm_num at h6

theorem k2PSL_holds : K2PSLStatement2 := by
  intro Y _ D k f hH hk hf hL hroot d hd
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  obtain ⟨Ψ, hsurj, hker, x, hx, hxD⟩ := exists_surjective_of_hyp_psl hH hk hf hL hroot
  obtain ⟨e, he⟩ := exists_mulEquiv_projectiveSL hH.center_eq_bot Ψ hsurj hker
  obtain ⟨d₀, hD⟩ := hH.isClass
  have hconj : IsConj (Ψ x) d := by
    rw [hD] at hxD hd
    exact (isConj_comm.mp hxD).trans hd
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  rw [← hc, show c * Ψ x * c⁻¹ = (MulAut.conj c) (Ψ x) from rfl,
    card_pCoreOf_centralizer_mulEquiv (MulAut.conj c) (Ψ x), ← he x,
    card_pCoreOf_centralizer_mulEquiv e]
  have h1 := card_pCoreOf_centralizer_proj_transvection_le (by omega) hx
  rw [GaloisField.card 2 f (by omega)] at h1
  have h2 : 2 * (m + 1) - 3 = 2 * m - 1 := by omega
  rw [h2]
  exact h1

end CertBound

end CFSG.RankThree.GF2n.Smith81.Insp
