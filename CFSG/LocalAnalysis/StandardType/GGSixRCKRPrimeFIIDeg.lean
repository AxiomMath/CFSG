module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRG
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeM3PSL
public import CFSG.LieType.Universal.SpecialLinearExtras
public import CFSG.Assembly.OrderReductions.LinearOrders
public import CFSG.RankThree.PartOne.S11c.Sec66TGroup
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenA3TypeDet
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGStep
import CFSG.LocalAnalysis.StandardType.GGSixTCPSUDualPair
import CFSG.Quasithin.EmptyFaithful.S151TBTyp
import CFSG.RankThree.PartTwo.Census.Classical.EvenLinear

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag)

theorem rckFII_PSL_degOne
    (hIRG : RCKIntrinsicRoot) {X : Type} [Group X] [Finite X] {m g : ℕ} (hg : 1 ≤ g)
    (φ : (ggU .PSL (m + 1) g).K →* X) (hφk : φ.ker ≤ Subgroup.center (ggU .PSL (m + 1) g).K)
    (S : Set (GL (Fin (m + 1)) (GaloisField 2 g))) (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s)) {e : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 g)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 g) (Units.val '' S)) e)
    {J' : Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 g))}
    (hJe : IsComponentOf J' ⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
      glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e⁆)
    {R Rm : Subgroup X} (hR : R ≤ J'.map φ) (hRm : Rm ≤ J'.map φ)
    (hpos : GGRootPosJ (J'.map φ) R Rm) (hR2 : Nat.card R = 2) :
    g = 1 ∧ blockDegree (Algebra.adjoin (GaloisField 2 g) (Units.val '' S)) e = 1 := by
  classical
  let a : ℕ := blockDegree (Algebra.adjoin (GaloisField 2 g) (Units.val '' S)) e
  have ha1 : 1 ≤ a := TableCRes.tcBlockDegree_pos he.2.2.1
  obtain ⟨k, ι, hιcent, hιrange, _hιflag⟩ := rckM3_PSL m g hg S hS hodd he hJe
  let ψ : (ggU .PSL (k + 1) (g * a)).K →* X := φ.comp ι
  have hψrange : ψ.range = J'.map φ := by
    rw [MonoidHom.range_comp, hιrange]
  have hψker : ψ.ker ≤ Subgroup.center (ggU .PSL (k + 1) (g * a)).K := by
    intro y hy
    exact hιcent y (hφk (show φ (ι y) = 1 from hy))
  have hJ'qs : CFSG.Assembly.IsQuasisimple ↥J' := hJe.2.2
  have hJ'nt : Nontrivial ↥J' := by
    have : Nontrivial (↥J' ⧸ Subgroup.center ↥J') := hJ'qs.2.toNontrivial
    exact (QuotientGroup.mk'_surjective (Subgroup.center ↥J')).nontrivial
  by_cases hga : g * a = 1
  · exact ⟨Nat.eq_one_of_mul_eq_one_right hga, Nat.eq_one_of_mul_eq_one_left hga⟩
  · have hga_pos : 0 < g * a := Nat.mul_pos (by omega) (by omega)
    have hgane : g * a ≠ 0 := Nat.pos_iff_ne_zero.mp hga_pos
    have hcard_ga : Nat.card (GaloisField 2 (g * a)) = 2 ^ (g * a) :=
      GaloisField.card (p := 2) (g * a) hgane
    obtain ⟨h2le', h22card', hPqs⟩ :=
      isQuasisimple_specialLinear_of_quasisimple_range (ρ := ι)
        (show CFSG.Assembly.IsQuasisimple ↥ι.range from by rw [hιrange]; exact hJ'qs)
    have h2le : 2 ≤ k + 1 := by simpa using h2le'
    have h22card : k + 1 ≠ 2 ∨ Nat.card (GaloisField 2 (g * a)) ≠ 2 := by
      simpa using h22card'
    have h22 : k + 1 ≠ 2 ∨ 2 ^ (g * a) ≠ 2 := by
      rcases h22card with h | h
      · exact Or.inl h
      · exact Or.inr (by rw [← hcard_ga]; exact h)
    have h23 : k + 1 ≠ 2 ∨ 2 ^ (g * a) ≠ 3 := by
      refine Or.inr ?_
      intro h3
      have hdvd : 2 ∣ 2 ^ (g * a) := dvd_pow_self 2 hgane
      rw [h3] at hdvd
      norm_num at hdvd
    have hNorm : RCKNormalizedModel .PSL (k + 1) (g * a) := by
      refine ⟨Or.inl rfl, Nat.prime_two, Nat.mul_le_mul hg ha1, h2le, ?_, ?_⟩
      · intro h
        exact h22.elim (fun h1 => h1 (Prod.ext_iff.mp h).1)
          (fun h2 => h2 (Prod.ext_iff.mp h).2)
      · intro h
        exact h23.elim (fun h1 => h1 (Prod.ext_iff.mp h).1)
          (fun h2 => h2 (Prod.ext_iff.mp h).2)
    have hPperf : Group.IsPerfect (ggU .PSL (k + 1) (g * a)).K :=
      Group.isPerfect_def.mpr hPqs.1
    have hoddP : Odd (Nat.card (Subgroup.center (ggU .PSL (k + 1) (g * a)).K)) :=
      Nat.coprime_two_right.mp (CFSG.RankThree.PartTwo.Census.coprime_card_center_SL
        (K := GaloisField 2 (g * a)) (n := k + 1) (by omega))
    have hnotker : ¬ J' ≤ φ.ker := by
      intro hle
      have hbot : J'.map φ = ⊥ := (Subgroup.map_eq_bot_iff (H := J') (f := φ)).mpr hle
      have hcard := Subgroup.card_le_of_le hR
      rw [hbot, Subgroup.card_bot] at hcard
      omega
    have hJmap : CFSG.Assembly.IsQuasisimple ↥(J'.map φ) := by
      have h := CFSG.LocalCores.isQuasisimple_map
        (CFSG.ComponentClassification.CatalogueBAlternating.quasisimple_iff_native.mpr hJ'qs) φ
        hnotker
      exact CFSG.ComponentClassification.CatalogueBAlternating.quasisimple_iff_native.mp h
    have hoddJ : Odd (Nat.card (Subgroup.center ↥(J'.map φ))) := by
      let ψ' : (ggU .PSL (k + 1) (g * a)).K →* ↥(J'.map φ) :=
        ψ.codRestrict (J'.map φ) (fun x => by
          rw [← hψrange]
          exact ⟨x, rfl⟩)
      have hψ'ker : ψ'.ker ≤ Subgroup.center (ggU .PSL (k + 1) (g * a)).K := by
        intro x hx
        exact hψker (show ψ x = 1 from congrArg Subtype.val hx)
      have hsurj' : Function.Surjective ψ' := by
        rintro ⟨y, hy⟩
        have hy' : y ∈ ψ.range := by rwa [hψrange]
        obtain ⟨x, rfl⟩ := hy'
        exact ⟨x, Subtype.ext rfl⟩
      exact hoddP.of_dvd_nat
        (CFSG.Quasithin.S151TB.Typ.card_center_dvd_of_surjective ψ' hsurj' hψ'ker)
    obtain ⟨β, u, hβroot, _hβreg, hRsub, _hRmsub⟩ :=
      (hIRG X (J'.map φ) R Rm hJmap hoddJ hpos).1 .PSL (k + 1) (g * a)
        ψ hNorm hψrange hψker
    let A : Subgroup (ggU .PSL (k + 1) (g * a)).K :=
      ((ggU .PSL (k + 1) (g * a)).D.rootGroup β).map (MulAut.conj u).toMonoidHom
    have hAroot : Nat.card ((ggU .PSL (k + 1) (g * a)).D.rootGroup β) = 2 ^ (g * a) :=
      card_rootGroup_specialLinear_galoisField (p := 2) (k := k) (q := g * a) hgane hβroot
    have hAcard : Nat.card A = 2 ^ (g * a) := by
      have h1 : Nat.card A =
          Nat.card ((ggU .PSL (k + 1) (g * a)).D.rootGroup β) :=
        Subgroup.card_map_of_injective (MulAut.conj u).injective
      rw [h1, hAroot]
    have hoddker : Odd (Nat.card ψ.ker) :=
      hoddP.of_dvd_nat (Subgroup.card_dvd_of_le hψker)
    have hcop : (Nat.card ψ.ker).Coprime (Nat.card A) := by
      rw [hAcard]
      exact (hoddker.coprime_two_right).pow_right (g * a)
    have hdj : Disjoint ψ.ker A := Subgroup.disjoint_of_coprime_natCard hcop
    have hcardmap : Nat.card (A.map ψ) = Nat.card A := by
      have hmap : (⊤ : Subgroup A).map (ψ.comp A.subtype) = A.map ψ := by
        ext y
        constructor
        · rintro ⟨x, -, rfl⟩
          exact Subgroup.mem_map_of_mem ψ x.2
        · rintro ⟨x, hx, rfl⟩
          exact ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩
      have hkerbot : (ψ.comp A.subtype).ker = ⊥ := by
        refine le_bot_iff.mp fun x hx => ?_
        have hxker : (x : (ggU .PSL (k + 1) (g * a)).K) ∈ ψ.ker := hx
        exact Subtype.ext ((Subgroup.disjoint_def.mp hdj) hxker x.2)
      have hinj : Function.Injective (ψ.comp A.subtype) :=
        (MonoidHom.ker_eq_bot_iff (f := ψ.comp A.subtype)).mp hkerbot
      have hcm := Subgroup.card_map_of_injective (K := ⊤) (f := ψ.comp A.subtype) hinj
      rw [hmap, Subgroup.card_top] at hcm
      exact hcm
    have hRcard : Nat.card R = 2 ^ (g * a) := by
      rw [hRsub]
      change Nat.card (A.map ψ) = 2 ^ (g * a)
      rw [hcardmap, hAcard]
    have hga1 : g * a = 1 := by
      have h2eq : 2 ^ (g * a) = 2 := by rw [← hRcard, hR2]
      exact Nat.pow_right_injective (a := 2) (by norm_num) (by simpa using h2eq)
    exact ⟨Nat.eq_one_of_mul_eq_one_right hga1, Nat.eq_one_of_mul_eq_one_left hga1⟩

end CFSG.StandardType.RCKRP
