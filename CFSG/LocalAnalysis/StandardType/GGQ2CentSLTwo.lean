module

public import CFSG.LocalAnalysis.StandardType.GGQ2CentInternal
public import CFSG.LocalAnalysis.StandardType.GGLinTwoCent
public import CFSG.LocalAnalysis.StandardType.GGTableBTwoThreeTorus
public import CFSG.LocalAnalysis.StandardType.GGTableBTwoThreeRank
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMoreCl
public import CFSG.LocalAnalysis.StandardType.GGTableBRank
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoTableBReduce
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.StandardType.GGQ2CentPort

open CFSG CFSG.Assembly Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

private theorem ggQ2CentSLTwoAux_of_cent {R : Type} [Group R] {A : Subgroup (MulAut R)}
    (hcent : ∀ c : R, (∀ e ∈ A.comap MulAut.conj, c * e = e * c) → c ∈ A.comap MulAut.conj) :
    actionThree A := by
  intro r hfix _
  refine (hcent r fun e he => ?_ : r ∈ A.comap MulAut.conj)
  have h1 : MulAut.conj e r = r := hfix _ he
  rw [MulAut.conj_apply] at h1
  calc r * e = e * r * e⁻¹ * e := by rw [h1]
    _ = e * r := by group

private theorem ggQ2CentSLTwoAux_at {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J) (hperf : commutator L = ⊤)
    {d : ℕ} (hd3 : 3 ≤ d) {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    (θ' : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) K))
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hBs3 : ∀ b ∈ Bs, ∃ φ ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ,
      LargeEvenInduces θ' (fun l l' => (l' : G) = b⁻¹ * l * b) φ) :
    actionThree (ggBeta L θ' hN).range := by
  classical
  have : Finite (MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) K))) := MulEquiv.finite_left
  have hBs : IsElemAbelian 3 Bs := hS.1.1.2.1.2.1
  have hAea : IsElemAbelian 3 (ggBeta L θ' hN).range := isElemAbelian_range_ggBeta θ' hBs hN
  have hout := NbrInnerMore.ggOutdiagPrime_linear (d := d) (K := K) Nat.prime_three
    (by rw [hK]; decide) (by omega)
  have hinner : ∀ a ∈ (ggBeta L θ' hN).range, ∃ r, a = MulAut.conj r := by
    rintro a ⟨b, rfl⟩
    obtain ⟨r, hr⟩ := hout _ (ggBeta_mem L θ' hN hBs3 b) (hAea.2 _ ⟨b, rfl⟩)
    exact ⟨r, hr.symm⟩
  have hZ := ggQ2Cent_center_eq_bot hperf θ'
  have hinj : Function.Injective (MulAut.conj :
      LargeEvenProj (LargeEvenSLGroup (Fin d) K) →*
        MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) K))) :=
    fun a b hab => ggQ2Cent_eq_of_conj_eq hZ hab
  let E := (ggBeta L θ' hN).range.comap (MulAut.conj :
      LargeEvenProj (LargeEvenSLGroup (Fin d) K) →*
        MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) K)))
  have hEmap : E.map MulAut.conj = (ggBeta L θ' hN).range := by
    refine le_antisymm (Subgroup.map_comap_le _ _) ?_
    intro a ha
    obtain ⟨r, rfl⟩ := hinner a ha
    exact ⟨r, ha, rfl⟩
  have hEea : IsElemAbelian 3 E := hAea.comap hinj
  have hEcard : Nat.card E = Nat.card (ggBeta L θ' hN).range := by
    rw [← hEmap, Subgroup.card_map_of_injective hinj]
  have hSS : LargeEvenSStar 3 B x L := hS.1.1.1.2.2.2.2.2.2.1
  have hBBs : B ≤ Bs := hS.1.1.2.1.1
  have hBN : B ≤ Subgroup.normalizer (L : Set G) := hBBs.trans hN
  have hcenter : Subgroup.center (SpecialLinearGroup (Fin d) K) = ⊥ :=
    LineL2.center_eq_bot_two hK
  have hscalars : LinearFlag.scalars d K = ⊥ := by
    rw [LinearFlag.scalars_eq_center, hcenter]
  have hpinj : Function.Injective (LinearFlag.proj d K) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    rw [LinearFlag.proj_eq_one_iff, hscalars, Subgroup.mem_bot] at ha
    exact ha
  let χ : SpecialLinearGroup (Fin d) K ≃* projectiveSL d K :=
    MulEquiv.ofBijective (LinearFlag.proj d K) ⟨hpinj, LinearFlag.proj_surjective d K⟩
  let σ : LargeEvenProj (LargeEvenSLGroup (Fin d) K) ≃* SpecialLinearGroup (Fin d) K :=
    (TypeA.recipeEquiv d K).trans χ.symm
  let E₁ := E.map σ.toMonoidHom
  have hE₁ : IsElemAbelian 3 E₁ := hEea.map _
  have hE₁card : Nat.card E₁ = Nat.card E := Subgroup.card_map_of_injective σ.injective
  by_cases hd6 : 6 ≤ d
  ·
    have hlift : GGTorusLift 3 (d / 2) (LargeEvenProj (LargeEvenSLGroup (Fin d) K)) :=
      TypeA.ggTorusLift_of_mulEquiv (TypeA.recipeEquiv d K)
        (TwoThree.ggTorusLift_two hK (by omega))
    have hcard₁ : 3 ^ (d / 2) ≤ Nat.card E₁ := by
      rw [hE₁card, hEcard]
      exact le_trans (pow_le_card_range_ggBeta Nat.prime_three hSS hperf θ' hBN hlift)
        (Subgroup.card_le_of_le (range_ggBeta_le θ' hBBs hBN hN))
    have hcent₁ := LinTwoGen.cent_le_of_maxRank hK hd6 hE₁ hcard₁
    refine ggQ2CentSLTwoAux_of_cent fun c hc => ?_
    obtain ⟨c', hc', hcc'⟩ := hcent₁ (σ c) (by
      rintro _ ⟨e, he, rfl⟩
      change σ c * σ e = σ e * σ c
      rw [← map_mul, ← map_mul, hc e he])
    have hc'c : c' = c := σ.injective hcc'
    rw [← hc'c]
    exact hc'
  ·
    exfalso
    have hcardBs : Nat.card (ggBeta L θ' hN).range * 3 = Nat.card Bs :=
      card_range_ggBeta_mul_of Nat.prime_three hBs (hBBs hSS.2.1) hSS.2.2.1 hSS.2.2.2.1.1
        hSS.2.2.2.2 hperf θ' hN
    have hBcard : Nat.card B = 3 ^ LargeEvenTwoLocalRank 3 G := GGConfig.card_B_eq hS.1.1
    have hbeta : 3 ∈ LargeEvenBeta 4 G := hS.1.1.1.2.2.2.2.2.1
    have hrank : 4 ≤ LargeEvenTwoLocalRank 3 G := hbeta.2.2.2
    have hB81 : 81 ≤ Nat.card B := by
      rw [hBcard]
      calc 81 = 3 ^ 4 := by norm_num
        _ ≤ 3 ^ LargeEvenTwoLocalRank 3 G := Nat.pow_le_pow_right (by norm_num) hrank
    have hBBs' : Nat.card B ≤ Nat.card Bs := Subgroup.card_le_of_le hBBs
    let ι : SpecialLinearGroup (Fin d) K →* LinearMap.GeneralLinearGroup K (Fin d → K) :=
      (Matrix.GeneralLinearGroup.toLin : GL (Fin d) K ≃* _).toMonoidHom.comp
        Matrix.SpecialLinearGroup.toGL
    have hιinj : Function.Injective ι :=
      Matrix.GeneralLinearGroup.toLin.injective.comp Matrix.SpecialLinearGroup.toGL_injective
    let X : Subgroup (Module.End K (Fin d → K))ˣ := E₁.map ι
    have hX : IsElemAbelian 3 X := hE₁.map ι
    have hXcard : Nat.card X = Nat.card (ggBeta L θ' hN).range := by
      rw [Subgroup.card_map_of_injective hιinj, hE₁card, hEcard]
    have hsq := TwoThree.card_sq_le_top hK X (fun a ha b hb => hX.comm ha hb)
      (fun a ha => hX.2 a ha)
    rw [Module.finrank_fin_fun, hXcard] at hsq
    have h243 : 3 ^ d ≤ 243 :=
      le_trans (Nat.pow_le_pow_right (by norm_num) (by omega : d ≤ 5)) (by norm_num)
    have h27 : 27 ≤ Nat.card (ggBeta L θ' hN).range := by omega
    have h729 : 729 ≤ Nat.card (ggBeta L θ' hN).range ^ 2 := by nlinarith
    omega

theorem slTwoInput_holds :
    slTwoInput := by
  intro G _ _ p B Bs x L D J hS hon R _ θ hN
  have hp3 : p = 3 := ggQ2_pThree hS
  subst hp3
  obtain ⟨hperf, lab, hlab, hraw⟩ := hon
  obtain ⟨-, -, -, -, -, -, -, ⟨hq2, hfam⟩, -, -⟩ := largeEvenRawDatum_exists hraw
  have hn : lab.n = 1 := by
    have h1 : 1 ≤ lab.n := hlab.1
    have h2 : lab.n < 2 := hq2
    omega
  obtain ⟨d, hd3, K, _, _, hK, θ', hBs3⟩ : ∃ d : ℕ, 3 ≤ d ∧ ∃ (K : Type) (_ : Field K)
      (_ : Finite K), Nat.card K = 2 ∧
      ∃ θ' : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) K),
        ∀ b ∈ Bs, ∃ φ ∈ LargeEvenMatConjImage
          (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ,
          LargeEvenInduces θ' (fun l l' => (l' : G) = b⁻¹ * l * b) φ := by
    obtain ⟨t, r, n⟩ := lab
    dsimp only at hn hfam
    subst hn
    rcases hfam with rfl | ⟨rfl, rfl⟩
    ·
      have hr : 2 ≤ r := by
        obtain ⟨-, h1, h2⟩ : 1 ≤ 1 ∧ 1 ≤ r ∧ (r = 1 → 2 ≤ 1) := hlab
        by_contra h
        have := h2 (by omega)
        omega
      obtain ⟨K, i1, i2, hK, -, -, θ', -, -, hBs3⟩ := hraw
      exact ⟨r + 1, by omega, K, i1, i2, by rw [hK]; norm_num, θ', hBs3⟩
    ·
      obtain ⟨K, i1, i2, hK, -, -, θ', -, -, hBs3⟩ := hraw
      exact ⟨4, by norm_num, K, i1, i2, by rw [hK]; norm_num, θ', hBs3⟩
  have : CharP K 2 := charP_two_of_card (m := 1) (by rw [hK]; norm_num)
  exact actionThree_ggBeta_congr θ θ' hN (ggQ2CentSLTwoAux_at hS hperf hd3 hK θ' hN hBs3)

end CFSG.StandardType.GGQ2CentPort

end
