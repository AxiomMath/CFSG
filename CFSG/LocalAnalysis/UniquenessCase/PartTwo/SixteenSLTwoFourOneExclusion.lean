module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSLTwoEightFixedSpace
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3RowSL4A
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeKernel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenTransitiveKernel
public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitCount
public import CFSG.Quasithin.Background.SimsE214NatCoord
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL4BA1BAA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3SL24CoverCB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.Vol2 CFSG.Open Subgroup
  CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.H.Mathieu (realizes_iff)
open Matrix

variable {G : Type} [Group G] [Finite G]

private theorem s168e3_three_mem_and_mBarGT_one_of_sl2_four_realization
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hs : s15 D.M V₀ V hV L = 1)
    (hrow : s16h_H5RowSL2 (lBar V₀ V hV L)
      (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) 2)
    {K : Type} [fieldK : Field K] [finiteK : Finite K]
    (hK4 : Nat.card K = 4)
    (hreal : (FFModel.nat (StatedSL 2 K)).Realizes (lBar V₀ V hV L)
      (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L))) :
    3 ∈ D.sig ∧ MBarGT D.M V₀ V 1 := by
  classical
  let W := Vtil V₀ V hV
  let A : Subgroup (MulAut W) := Mbar D.M V₀ V hV
  let H : Subgroup (MulAut W) := lBar V₀ V hV L
  let Γ : Subgroup (GL (Fin 2) K) := StatedSL 2 K
  have hHA : H ≤ A := by
    show lBar V₀ V hV L ≤ Mbar D.M V₀ V hV
    simpa only [lBar, Mbar] using barSub_mono V₀ V hV c.setting.hyp151.le
  have hAn : A ≤ Subgroup.normalizer (H : Set (MulAut W)) := by
    intro g hg
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      (lBar_conj_eq_of_s15_eq_one hs hg)
  have hcomm : commSub ⊤ H = ⊤ := by
    show commSub ⊤ (lBar V₀ V hV L) = ⊤
    simpa only [wTil, lBar] using wTil_eq_top_of_case163_2 c.conc hs
  have hrealTop : (FFModel.nat Γ).Realizes H ⊤ (fixV H) :=
    s16g_realizes_top c.conc hs Γ hreal
  obtain ⟨π, hπ⟩ := hrealTop
  obtain ⟨f, hf⟩ := KGNat.exists_isCoord (KGNat.linModelNat Γ) hπ
  obtain ⟨ρ, hρinj, _hρcoord, _hρcomp, _hρmap, hρnorm⟩ :=
    exists_faithful_nat_hom_of_isCoord (W := W) (Γ := Γ) (A := A) (H := H)
      (π := π) (f := f) hHA hAn hf hcomm
  have hNormEq : s16gNorm Γ = natNorm Γ := s16gNorm_eq_natNorm Γ
  have h3 : 3 ∈ D.sig := by
    obtain ⟨p, hpσ⟩ := c.std.hx.sig_nonempty
    have hp : p.Prime := (D.sig_prime p hpσ).1
    have hp2 : p ≠ 2 := (D.sig_prime p hpσ).2
    by_cases hp3 : p = 3
    · exact hp3 ▸ hpσ
    · exfalso
      have h2le : 2 ≤ CFSG.Open.pRank p A := by
        simpa only [A] using c.two_le_pRank_mbar hpσ
      obtain ⟨E, hEA, hEab, hEcard⟩ :=
        CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank
          (G := MulAut W) (p := p) (hp := ⟨hp⟩) (H := A) (k := 2) h2le
      let E' : Subgroup (MulAut (StdMod (Fin 2) K)) := (E.subgroupOf A).map ρ
      have hE'card : Nat.card E' = p ^ 2 := by
        change Nat.card ↥((E.subgroupOf A).map ρ) = p ^ 2
        rw [Subgroup.card_map_of_injective hρinj,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEA).toEquiv]
        exact hEcard
      have hE'ab : IsElemAbelian p E' := by
        simpa only [E'] using (hEab.subgroupOf A).map ρ
      have hE'N : E' ≤ natNorm Γ := by
        intro y hy
        change y ∈ (E.subgroupOf A).map ρ at hy
        obtain ⟨a, -, rfl⟩ := hy
        rw [← hNormEq]
        exact hρnorm a
      have hcardle : Nat.card E' ≤ p :=
        s16h_H5_natNorm_statedSL_two_four_elemAbelian_one hK4 hp hp2 hp3 hE'N hE'ab
      have hp2le : p ^ 2 ≤ Nat.card E' := by rw [hE'card]
      have hpp : p * p ≤ p := by
        calc p * p = p ^ 2 := (pow_two p).symm
          _ ≤ Nat.card E' := hp2le
          _ ≤ p := hcardle
      nlinarith [hp.two_le]
  have hm : MBarGT D.M V₀ V 1 := by
    have hex : ∃ τ ∈ Mbar D.M V₀ V hV, τ ^ 2 = 1 ∧ τ ≠ 1 := by
      obtain ⟨t, htA, ht2, ht1, -, -⟩ := c.conc
      exact ⟨t, htA, ht2, ht1⟩
    refine s16h_e3_mbar_of_rank D c.setting.hyp16.hyp125 (n := 1) ?_ hex
    intro τ hτA hτ2 hτ1
    have hτN : τ ∈ Subgroup.normalizer (H : Set (MulAut W)) := hAn hτA
    have hτU : ∃ u ∈ commSub ⊤ H, τ u ≠ u := by
      by_contra h
      apply hτ1
      ext u
      by_contra hu
      exact h ⟨u, by rw [hcomm]; exact Subgroup.mem_top u, hu⟩
    obtain ⟨K', hK'f, hK'fin, hK'card, π', β', hπ's, hβ's, hβ'k, hβ'e⟩ :=
      s16h_sl24_cover_coord (L := lBar V₀ V hV L)
        (U := commSub ⊤ (lBar V₀ V hV L))
        (Z := commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) hrow
    let : Field K' := hK'f
    let : Finite K' := hK'fin
    obtain ⟨s, hsN, hs2, hs1, hrk⟩ :=
      s16h_sl24_cover_transfer (W := W) (L := H)
        (hW := s15_Infra_vtil_sq_eq_one V₀ V hV) hK'card hπ's hβ's hβ'k hβ'e
        hτN hτ2 hτU
    have h2s : 2 ≤ rkIdx (fixV (Subgroup.zpowers s)) :=
      s16h_sl4_natNorm_involution hK'card hsN hs2 hs1
    have h2τ : 2 ≤ rkIdx (fixV (Subgroup.zpowers τ)) := le_trans h2s hrk
    have h2rk : 2 ≤ rk (commSub ⊤ (Subgroup.zpowers τ)) := by
      calc 2 ≤ rkIdx (fixV (Subgroup.zpowers τ)) := h2τ
        _ = rk (commV (Subgroup.zpowers τ)) := rkIdx_fixV_zpowers τ
        _ = rk (commSub ⊤ (Subgroup.zpowers τ)) := by rw [commV_eq_commSub]
    have hcard : Nat.card ↥(commSub ⊤ (Subgroup.zpowers τ)) =
        2 ^ rk ↥(commSub ⊤ (Subgroup.zpowers τ)) :=
      card_eq_two_pow (s15_Infra_vtil_sq_eq_one V₀ V hV) _
    rw [hcard]
    exact Nat.pow_le_pow_right (by norm_num) h2rk
  exact ⟨h3, hm⟩

theorem s168e3_three_mem_and_mBarGT_one_of_sl2_four_of_s_eq_one
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hs : s15 D.M V₀ V hV L = 1)
    (hrow : s16h_H5RowSL2 (lBar V₀ V hV L)
      (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) 2) :
    3 ∈ D.sig ∧ MBarGT D.M V₀ V 1 := by
  have hrow' := hrow
  obtain ⟨-, K, hKf, hKfin, hKcard, hreal⟩ := hrow
  let : Field K := hKf
  let : Finite K := hKfin
  have hK4 : Nat.card K = 4 := by rw [hKcard]; norm_num
  exact s168e3_three_mem_and_mBarGT_one_of_sl2_four_realization c hs hrow' hK4 hreal

theorem s168e3_three_mem_and_fixV_eq_bot_of_sl2_four_of_s_eq_one
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hs : s15 D.M V₀ V hV L = 1)
    (hrow : s16h_H5RowSL2 (lBar V₀ V hV L)
      (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) 2) :
    3 ∈ D.sig ∧ fixV (lBar V₀ V hV L) = ⊥ := by
  have hfacts := s168e3_three_mem_and_mBarGT_one_of_sl2_four_of_s_eq_one c hs hrow
  obtain ⟨-, K, hKf, hKfin, hKcard, hreal⟩ := hrow
  let : Field K := hKf
  let : Finite K := hKfin
  have hK4 : Nat.card K = 4 := by rw [hKcard]; norm_num
  exact ⟨hfacts.1,
    fixV_lBar_eq_bot_of_field_four_at_three c hs hK4 (Or.inl hreal) hfacts.1 hfacts.2⟩

theorem s168e3_false_of_sl2_four_of_s_eq_one
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (_hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (_hthin : ∀ q : ℕ, q.Prime → q ≠ 2 →
      CFSG.Open.pRank q (lBar V₀ V hV L) ≤ 1)
    (hs : s15 D.M V₀ V hV L = 1)
    (hrow : s16h_H5RowSL2 (lBar V₀ V hV L)
      (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) 2) :
    False := by
  classical
  have hfacts := s168e3_three_mem_and_fixV_eq_bot_of_sl2_four_of_s_eq_one c hs hrow
  obtain ⟨-, K, hKf, hKfin, hKcard, hreal⟩ := hrow
  let : Field K := hKf
  let : Finite K := hKfin
  have hK4 : Nat.card K = 4 := by rw [hKcard]; norm_num
  let W := Vtil V₀ V hV
  let A : Subgroup (MulAut W) := Mbar D.M V₀ V hV
  let H : Subgroup (MulAut W) := lBar V₀ V hV L
  let Γ : Subgroup (GL (Fin 2) K) := StatedSL 2 K
  have hHA : H ≤ A := by
    show lBar V₀ V hV L ≤ Mbar D.M V₀ V hV
    simpa only [lBar, Mbar] using barSub_mono V₀ V hV c.setting.hyp151.le
  have hfix : fixV H = ⊥ := by simpa only [H] using hfacts.2
  have hrealTop : (FFModel.nat Γ).Realizes H ⊤ ⊥ := by
    have h := s16g_realizes_top c.conc hs Γ hreal
    rw [hfix] at h
    exact h
  obtain ⟨π, β, hR⟩ :=
    (realizes_iff (FFModel.nat Γ) H ⊤ ⊥).mp hrealTop
  have htrans : ∀ m ∈ (FFModel.nat Γ).sec, ∀ m' ∈ (FFModel.nat Γ).sec,
      m ∉ (FFModel.nat Γ).ker → m' ∉ (FFModel.nat Γ).ker →
      ∃ γ : (FFModel.nat Γ).Gam, ∃ k ∈ (FFModel.nat Γ).ker,
        (FFModel.nat Γ).act γ m = m' * k := by
    intro m _ m' _ hm hm'
    have hm0 : Multiplicative.toAdd (α := Fin 2 → K) m ≠ 0 := fun h => hm (by
      rw [show m = 1 from Multiplicative.toAdd.injective h]
      exact Subgroup.one_mem _)
    have hm0' : Multiplicative.toAdd (α := Fin 2 → K) m' ≠ 0 := fun h => hm' (by
      rw [show m' = 1 from Multiplicative.toAdd.injective h]
      exact Subgroup.one_mem _)
    obtain ⟨g, hg, hgm⟩ :=
      CFSG.Quasithin.SimsE2.E214N.statedSL_exists_mulVec_eq (F := K) hm0 hm0'
    refine ⟨⟨g, hg⟩, 1, Subgroup.one_mem _, ?_⟩
    rw [mul_one]
    change Multiplicative.ofAdd
      (((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ
        Multiplicative.toAdd (α := Fin 2 → K) m) = m'
    rw [hgm]
    rfl
  have htransW : ∀ u x : W, u ≠ 1 → x ≠ 1 → ∃ g ∈ A, g u = x := by
    intro u x hu hx
    obtain ⟨h, hhH, hhu⟩ :=
      CFSG.Quasithin.H13.Orbit.exists_eq_of_transitive (D := FFModel.nat Γ) hR htrans hu hx
    exact ⟨h, hHA hhH, hhu⟩
  have hWcard : Nat.card W = 16 := by
    have h1 := CFSG.Quasithin.H13.Orbit.card_eq_of_realizesBy hR
    have hker : Nat.card ↥(FFModel.nat Γ).ker = 1 := Subgroup.card_bot
    have hsec : Nat.card ↥(FFModel.nat Γ).sec = 16 := by
      change Nat.card ↥(⊤ : Subgroup (Multiplicative (Fin 2 → K))) = 16
      rw [Subgroup.card_top, Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
        Nat.card_fin, hK4]
      norm_num
    simpa [hker, hsec] using h1
  have hWsq : ∀ w : W, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one V₀ V hV
  have hAutdvd : Nat.card (MulAut W) ∣ Nat.card (GL (Fin 4) (ZMod 2)) :=
    CFSG.LocalAnalysis.UniquenessCase.UC6.N588.card_mulAut_dvd_card_GL
      (q := 2) (d := 4) (V := W) (fun a b => mul_comm a b) hWsq
      (by rw [hWcard]; norm_num)
  have hGL : Nat.card (GL (Fin 4) (ZMod 2)) = 20160 := by
    rw [Matrix.card_GL_field, ZMod.card]
    simp [Fin.prod_univ_succ]
  have hnot : ¬ 3 ^ (2 + 1) ∣ Nat.card A := by
    intro h
    have h1 : 3 ^ (2 + 1) ∣ Nat.card (MulAut W) :=
      h.trans (Subgroup.card_subgroup_dvd_card A)
    have h2 : 3 ^ (2 + 1) ∣ Nat.card (GL (Fin 4) (ZMod 2)) := h1.trans hAutdvd
    rw [hGL] at h2
    norm_num at h2
  have hrank : CFSG.Open.pRank 3 A ≤ 2 :=
    CFSG.GroupTheory.pRank_le_of_not_dvd_pow_succ (G := MulAut W) (H := A)
      (p := 3) (k := 2) Nat.prime_three hnot
  have hcop : ¬ 3 ∣ Nat.card W := by rw [hWcard]; norm_num
  have hk : S168e3Kernel A 3 :=
    s168e3_kernel_of_transitive (W := W) (p := 3) Nat.prime_three hcop hrank htransW
  exact s168e3_false_of_kernel c Nat.prime_three hfacts.1 (by simpa only [A] using hk)

theorem s168e3_concl163F_of_sl2_four_of_s_eq_one
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (_hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (_hthin : ∀ q : ℕ, q.Prime → q ≠ 2 →
      CFSG.Open.pRank q (lBar V₀ V hV L) ≤ 1)
    (hs : s15 D.M V₀ V hV L = 1)
    (hrow : s16h_H5RowSL2 (lBar V₀ V hV L)
      (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) 2) :
    Concl163F D V₀ V hV L :=
  (s168e3_false_of_sl2_four_of_s_eq_one c _hcomp _hthin hs hrow).elim

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
