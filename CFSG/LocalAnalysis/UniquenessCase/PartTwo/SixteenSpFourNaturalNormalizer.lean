module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFieldExtensionFixedKernel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenMod
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalTransitiveTI
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8Pred
public import CFSG.Quasithin.Vol2.KGNatCoord
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedL3AA
public import CFSG.Quasithin.Background.HStandard
public import CFSG.Quasithin.Background.D2Basic
public import CFSG.Open.StatedDefs
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatScalars
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CenterHopf
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16b
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Close16CoverR119
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21a
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214a
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214b
public import CFSG.Quasithin.Background.G10Local
public import CFSG.Quasithin.Background.G64ExtSq
public import CFSG.Quasithin.Background.G64NatTop
public import CFSG.Quasithin.Vol2.Ch3B513NC1Nat
public import CFSG.Sporadic.Schreier.J4SCommGenBase1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.Vol2 CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.GF2n.Stroth80

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
variable {K : Type} [Field K] [Finite K]

theorem le_rkIdx_fixV_statedSp_two_of_mem_normalizer
    {g : MulAut (StdMod (Fin 2 ⊕ Fin 2) K)}
    (hg : g ∈ s16gNorm (StatedSp 2 K)) (hg2 : g ^ 2 = 1) (hg1 : g ≠ 1) :
    (Nat.card K = 4 → 2 ≤ rkIdx (fixV (Subgroup.zpowers g))) ∧
      (Nat.card K = 8 → 3 ≤ rkIdx (fixV (Subgroup.zpowers g))) := by
  classical
  let Γ : Subgroup (GL (Fin 2 ⊕ Fin 2) K) := StatedSp 2 K
  have hΓ : AddCommutantScalar Γ := addCommutantScalar_statedSp (m := 2) (K := K)
  obtain ⟨θ, hθsem, hθker⟩ := s16g_exists_theta (Γ := Γ) hΓ
  have hsem : IsSemilinear g (θ ⟨g, hg⟩) := by
    intro c v
    have h := hθsem ⟨g, hg⟩ c (Multiplicative.ofAdd v)
    simpa [s16gSMul, toAddMap, Γ] using congrArg Multiplicative.toAdd h
  by_cases hθ : θ ⟨g, hg⟩ = 1
  · have hlin : IsSemilinear g (RingEquiv.refl K) := by
      simpa [hθ, RingAut.one_eq_refl] using hsem
    constructor
    · intro hK4
      exact le_rkIdx_fixV_of_linear (n := 2) (by rw [hK4]; norm_num) hlin hg1
    · intro hK8
      exact le_rkIdx_fixV_of_linear (n := 3) (by rw [hK8]; norm_num) hlin hg1
  · have hσ : θ ⟨g, hg⟩ ≠ RingEquiv.refl K := by
      intro h
      apply hθ
      rw [RingAut.one_eq_refl]
      exact h
    constructor
    · intro hK4
      obtain ⟨-, h2⟩ := rkIdx_fixV_of_semilinear_two (n := 2)
        (by norm_num) (by rw [hK4]; norm_num) hsem hσ hg2
      have hcardι : Fintype.card (Fin 2 ⊕ Fin 2) = 4 := by simp
      rw [hcardι] at h2
      omega
    · intro hK8
      obtain ⟨hdvd, -⟩ := rkIdx_fixV_of_semilinear_two (n := 3)
        (by norm_num) (by rw [hK8]; norm_num) hsem hσ hg2
      norm_num at hdvd


private theorem s168e3_sp4_mbarGT_of_realization_and_rank
    (c : S168e3Ctx D V₀ V L hV)
    (hs : s15 D.M V₀ V hV L = 1)
    {K : Type} [Field K] [Finite K]
    (hreal : (FFModel.nat (StatedSp 2 K)).Realizes (lBar V₀ V hV L)
      ⊤ (fixV (lBar V₀ V hV L)))
    (n : ℕ)
    (hrank : ∀ g : MulAut (StdMod (Fin 2 ⊕ Fin 2) K),
      g ∈ s16gNorm (StatedSp 2 K) → g ^ 2 = 1 → g ≠ 1 →
      n + 1 ≤ rkIdx (fixV (Subgroup.zpowers g))) :
    MBarGT D.M V₀ V n := by
  classical
  let W := Vtil V₀ V hV
  let A : Subgroup (MulAut W) := Mbar D.M V₀ V hV
  let H : Subgroup (MulAut W) := lBar V₀ V hV L
  let Γ : Subgroup (GL (Fin 2 ⊕ Fin 2) K) := StatedSp 2 K
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
  have hrealTop : (FFModel.nat Γ).Realizes H ⊤ (fixV H) := by
    simpa only [H, Γ] using hreal
  obtain ⟨π, hπ⟩ := hrealTop
  obtain ⟨f, hf⟩ := KGNat.exists_isCoord (KGNat.linModelNat Γ) hπ
  obtain ⟨ρ, hρinj, hρcoord, hρcomp, hρmap, hρnorm⟩ :=
    exists_faithful_nat_hom_of_isCoord (W := W) (Γ := Γ) (A := A) (H := H)
      (π := π) (f := f) hHA hAn hf hcomm
  have hex : ∃ τ ∈ Mbar D.M V₀ V hV, τ ^ 2 = 1 ∧ τ ≠ 1 := by
    obtain ⟨t, htA, ht2, ht1, -, -⟩ := c.conc
    exact ⟨t, htA, ht2, ht1⟩
  refine s16h_e3_mbar_of_rank D c.setting.hyp16.hyp125 (n := n) ?_ hex
  intro τ hτA hτ2 hτ1
  let a : A := ⟨τ, hτA⟩
  have ha2 : a ^ 2 = 1 := Subtype.ext hτ2
  have ha1 : a ≠ 1 := by
    intro h
    apply hτ1
    exact congrArg Subtype.val h
  let g := ρ a
  have hg2 : g ^ 2 = 1 := by
    rw [← map_pow, ha2, map_one]
  have hg1 : g ≠ 1 := by
    intro h
    apply ha1
    exact hρinj (h.trans (map_one ρ).symm)
  have hnle : n + 1 ≤ rkIdx (fixV (Subgroup.zpowers g)) :=
    hrank g (hρnorm a) hg2 hg1
  have hnrk : n + 1 ≤ rk (commSub ⊤ (Subgroup.zpowers g)) := by
    calc n + 1 ≤ rkIdx (fixV (Subgroup.zpowers g)) := hnle
      _ = rk (commV (Subgroup.zpowers g)) := rkIdx_fixV_zpowers g
      _ = rk (commSub ⊤ (Subgroup.zpowers g)) := by rw [commV_eq_commSub]
  let β : W →* Multiplicative (Fin 2 ⊕ Fin 2 → K) := hf.toHom
  have hβs : Function.Surjective β := by
    intro y
    obtain ⟨w, hw⟩ := hf.surj (Multiplicative.toAdd y)
    exact ⟨w, by
      show Multiplicative.ofAdd (f w) = y
      rw [hw]
      rfl⟩
  have hcommτ := s16_Mod_commSub_zpowers_map β hβs (t := τ) (t' := g)
    (fun w => (hρcoord a w).symm)
  have hcarddvd : Nat.card ↥((commSub ⊤ (Subgroup.zpowers τ)).map β) ∣
      Nat.card ↥(commSub ⊤ (Subgroup.zpowers τ)) :=
    Subgroup.card_map_dvd _ _
  have hrkle : rk ↥((commSub ⊤ (Subgroup.zpowers τ)).map β) ≤
      rk ↥(commSub ⊤ (Subgroup.zpowers τ)) :=
    padicValNat_two_le_of_dvd Nat.card_pos.ne' hcarddvd
  have himg : rk ↥(commSub ⊤ (Subgroup.zpowers g)) =
      rk ↥((commSub ⊤ (Subgroup.zpowers τ)).map β) := by
    rw [hcommτ]
  have hnorig : n + 1 ≤ rk ↥(commSub ⊤ (Subgroup.zpowers τ)) := by
    calc n + 1 ≤ rk ↥(commSub ⊤ (Subgroup.zpowers g)) := hnrk
      _ = rk ↥((commSub ⊤ (Subgroup.zpowers τ)).map β) := himg
      _ ≤ rk ↥(commSub ⊤ (Subgroup.zpowers τ)) := hrkle
  have hcard : Nat.card ↥(commSub ⊤ (Subgroup.zpowers τ)) =
      2 ^ rk ↥(commSub ⊤ (Subgroup.zpowers τ)) :=
    card_eq_two_pow (s15_Infra_vtil_sq_eq_one V₀ V hV) _
  rw [hcard]
  exact Nat.pow_le_pow_right (by norm_num) hnorig


theorem s168e3_sp4_four_mbarGT_one_of_s_eq_one
    (c : S168e3Ctx D V₀ V L hV)
    (hs : s15 D.M V₀ V hV L = 1)
    (hrow : NatSpn (lBar V₀ V hV L)
      (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) 4 2) :
    MBarGT D.M V₀ V 1 := by
  classical
  obtain ⟨-, K, hKf, hKfin, hKcard, hreal⟩ := hrow
  let : Field K := hKf
  let : Finite K := hKfin
  have hK4 : Nat.card K = 4 := by rw [hKcard]; norm_num
  have hrealTop : (FFModel.nat (StatedSp 2 K)).Realizes (lBar V₀ V hV L)
      ⊤ (fixV (lBar V₀ V hV L)) :=
    s16g_realizes_top c.conc hs (StatedSp 2 K) hreal
  refine s168e3_sp4_mbarGT_of_realization_and_rank c hs hrealTop 1 ?_
  intro g hg hg2 hg1
  simpa using (le_rkIdx_fixV_statedSp_two_of_mem_normalizer (K := K)
    (g := g) hg hg2 hg1).1 hK4


theorem s168e3_sp4_eight_mbarGT_two_of_s_eq_one
    (c : S168e3Ctx D V₀ V L hV)
    (hs : s15 D.M V₀ V hV L = 1)
    (hrow : NatSpn (lBar V₀ V hV L)
      (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) 4 3) :
    MBarGT D.M V₀ V 2 := by
  classical
  obtain ⟨-, K, hKf, hKfin, hKcard, hreal⟩ := hrow
  let : Field K := hKf
  let : Finite K := hKfin
  have hK8 : Nat.card K = 8 := by rw [hKcard]; norm_num
  have hrealTop : (FFModel.nat (StatedSp 2 K)).Realizes (lBar V₀ V hV L)
      ⊤ (fixV (lBar V₀ V hV L)) :=
    s16g_realizes_top c.conc hs (StatedSp 2 K) hreal
  refine s168e3_sp4_mbarGT_of_realization_and_rank c hs hrealTop 2 ?_
  intro g hg hg2 hg1
  simpa using (le_rkIdx_fixV_statedSp_two_of_mem_normalizer (K := K)
    (g := g) hg hg2 hg1).2 hK8


end CFSG.LocalAnalysis.UniquenessCase.PartTwo
