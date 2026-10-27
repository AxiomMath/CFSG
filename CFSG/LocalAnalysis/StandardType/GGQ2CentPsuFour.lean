module

public import CFSG.LocalAnalysis.StandardType.GGQ2CentInternal
public import CFSG.LocalAnalysis.StandardType.GGTorusGenUFourTwoCent
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestUnitaryCenter
public import CFSG.LocalAnalysis.StandardType.KGLangTorusClassicalInner
public import CFSG.LocalAnalysis.StandardType.GGTableBBstar
public import CFSG.LocalAnalysis.StandardType.GGTBJConfigFacts

public section

namespace CFSG.StandardType.GGQ2CentPort

open CFSG CFSG.Assembly

private theorem ggQ2CentPsuFourAux_at
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) (hperf : commutator L = ⊤)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4)
    (θ' : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ 1)))
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hBs3 : ∀ b ∈ Bs, ∃ φ ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin 4) K (2 ^ 1))) (LargeEvenGUSet (Fin 4) K (2 ^ 1)),
      LargeEvenInduces θ' (fun l l' => (l' : G) = b⁻¹ * l * b) φ) :
    actionThree (ggBeta L θ' hN).range := by
  classical
  have hBs : IsElemAbelian 3 Bs := hS.1.1.2.1.2.1
  have hAea : IsElemAbelian 3 (ggBeta L θ' hN).range :=
    isElemAbelian_range (fun a b => hBs.1.is_comm.comm a b)
      (fun b => Subtype.ext (hBs.2 b b.property)) (ggBeta L θ' hN)
  have hinner : ∀ a ∈ (ggBeta L θ' hN).range, ∃ r, a = MulAut.conj r := by
    rintro a ⟨b, rfl⟩
    have hI := ggBeta_mem L θ' hN hBs3 b
    obtain ⟨r, hr⟩ := kgLangC_conjImage_pow_inner_unitary (d := 4) (n := 1) (by norm_num) K
      (by rw [hK]; norm_num) _ hI
    have h3 : (ggBeta L θ' hN b) ^ 3 = 1 := hAea.2 _ ⟨b, rfl⟩
    refine ⟨r, ?_⟩
    calc ggBeta L θ' hN b = ggBeta L θ' hN b ^ 3 * ggBeta L θ' hN b := by rw [h3, one_mul]
      _ = ggBeta L θ' hN b ^ 4 := (pow_succ _ 3).symm
      _ = MulAut.conj r := hr
  have hZ := ggQ2Cent_center_eq_bot hperf θ'
  have hinj : Function.Injective (MulAut.conj :
      LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ 1)) →*
        MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ 1)))) :=
    fun a b hab => ggQ2Cent_eq_of_conj_eq hZ hab
  let E := (ggBeta L θ' hN).range.comap (MulAut.conj :
      LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ 1)) →*
        MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ 1))))
  have hEmap : E.map MulAut.conj = (ggBeta L θ' hN).range := by
    refine le_antisymm (Subgroup.map_comap_le _ _) ?_
    intro a ha
    obtain ⟨r, rfl⟩ := hinner a ha
    exact ⟨r, ha, rfl⟩
  have hEea : IsElemAbelian 3 E := hAea.comap hinj
  have hcard : 3 ^ 3 ≤ Nat.card E := by
    have hEcard : Nat.card E = Nat.card (ggBeta L θ' hN).range := by
      rw [← hEmap, Subgroup.card_map_of_injective hinj]
    rw [hEcard]
    have hSStar : LargeEvenSStar 3 B x L := hS.1.1.1.2.2.2.2.2.2.1
    have hcomp := hSStar.2.2.2.1
    have hx1 : x ≠ 1 := hSStar.2.2.1
    have hxB : x ∈ B := hSStar.2.1
    have hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (L : Set G) → IsPGroup 3 S →
        IsCyclic S := hSStar.2.2.2.2
    have hBsB : B ≤ Bs := hS.1.1.2.1.1
    have hcardBs : Nat.card (ggBeta L θ' hN).range * 3 = Nat.card Bs :=
      card_range_ggBeta_mul_of Nat.prime_three hBs (hBsB hxB) hx1 hcomp.1 hcyc hperf θ' hN
    have hBcard : Nat.card B = 3 ^ LargeEvenTwoLocalRank 3 G := GGConfig.card_B_eq hS.1.1
    have hbeta : 3 ∈ LargeEvenBeta 4 G := hS.1.1.1.2.2.2.2.2.1
    have hrank : 4 ≤ LargeEvenTwoLocalRank 3 G := hbeta.2.2.2
    have hB81 : 81 ≤ Nat.card B := by
      rw [hBcard]
      calc 81 = 3 ^ 4 := by norm_num
        _ ≤ 3 ^ LargeEvenTwoLocalRank 3 G := Nat.pow_le_pow_right (by norm_num) hrank
    have hBBs : Nat.card B ≤ Nat.card Bs := Subgroup.card_le_of_le hBsB
    have h27 : (3 : ℕ) ^ 3 = 27 := by norm_num
    rw [h27]
    omega
  have hSC : ∀ g : LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ 1)),
      (∀ e ∈ E, g * e = e * g) → g ^ 3 = 1 → g ∈ E := by
    intro g hg hg3
    let ψ : L →* LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ 1)) :=
      θ'.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
    have hψker : ψ.ker = Subgroup.center L := by
      ext l
      rw [MonoidHom.mem_ker]
      change θ' (QuotientGroup.mk l) = 1 ↔ _
      rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
    have h3Z : ¬ 3 ∣ Nat.card (Subgroup.center L) :=
      StdSubRestU.ggCenterPrime_unitary (n := 1) (d := 4) (p := 3) (K := K)
        (by rw [hK]; norm_num) le_rfl (by norm_num) (by norm_num) Nat.prime_three (by norm_num)
        (by norm_num) L ψ (θ'.surjective.comp (QuotientGroup.mk'_surjective _)) hψker.le hperf
    refine conj_mem_range_ggBeta_of_centerPrime hS θ' hN h3Z (fun a ha => ?_) hg3
    obtain ⟨r, rfl⟩ := hinner a ha
    have hrE : r ∈ E := ha
    rw [MulAut.conj_apply, ← hg r hrE, mul_inv_cancel_right]
  exact actionThree_of_torusCentSC (ggTorusCentSC_psuFourTwo hK) _ E hEea hcard hSC hEmap.le

theorem psuFourTwoInput_holds :
    psuFourTwoInput := by
  intro G _ _ p B Bs x L D J hS hon R _ θ hN
  have hp3 : p = 3 := ggQ2_pThree hS
  subst hp3
  obtain ⟨hperf, lab, hlab, hraw⟩ := hon
  obtain ⟨-, -, -, -, -, -, -, ⟨hq2, hfam⟩, -, -⟩ := largeEvenRawDatum_exists hraw
  have hn : lab.n = 1 := by
    have h1 : 1 ≤ lab.n := hlab.1
    have h2 : lab.n < 2 := hq2
    omega
  obtain ⟨K, _, _, hK, θ', hBs3⟩ : ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 4 ∧
      ∃ θ' : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ 1)),
        ∀ b ∈ Bs, ∃ φ ∈ LargeEvenMatConjImage
          (LargeEvenProjMk (LargeEvenSUGroup (Fin 4) K (2 ^ 1)))
          (LargeEvenGUSet (Fin 4) K (2 ^ 1)),
          LargeEvenInduces θ' (fun l l' => (l' : G) = b⁻¹ * l * b) φ := by
    obtain ⟨t, r, n⟩ := lab
    dsimp only at hn hfam
    subst hn
    rcases hfam with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · obtain ⟨K, i1, i2, hK, -, -, θ', -, -, hBs3⟩ := hraw
      exact ⟨K, i1, i2, by rw [hK]; norm_num, θ', hBs3⟩
  exact actionThree_ggBeta_congr θ θ' hN (ggQ2CentPsuFourAux_at hS hperf hK θ' hN hBs3)

end CFSG.StandardType.GGQ2CentPort

end
