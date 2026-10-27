module

public import CFSG.LocalAnalysis.StandardType.GGF4H4JBlockAux2
public import CFSG.LocalAnalysis.StandardType.GGResJLinearCubeAutomizer
public import CFSG.LocalAnalysis.StandardType.GGResLeaf
import CFSG.LocalAnalysis.StandardType.GGTypeACompatDiagRoot
import CFSG.LocalAnalysis.StandardType.GGTypeAEndNode
import CFSG.LocalAnalysis.StandardType.GGNbrBalance
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut

public section

namespace CFSG.StandardType.ResJCubicBlock

open CFSG.StandardType
open CFSG.StandardType.TypeANbrDvd
open CFSG.Assembly
open CFSG.Open
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.CatalogueBHigherLinearAction
open Matrix

theorem ggF4Ends_exists_orderOf_three_slThree
    {G : Type} [Group G] [Finite G] {J Bs : Subgroup G} {p : ℕ}
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (hBJ : Bs ≤ Subgroup.normalizer (J : Set G))
    (φ : Matrix.SpecialLinearGroup (Fin 3) K →* J)
    (hφ : Function.Surjective φ)
    (hker : ∀ g, φ g = 1 → g ∈ scalars 3 K)
    (hBs : CFSG.Open.IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hdiag : ∀ b : Bs, ∃ t : Fin 3 → K,
      TypeANbrDvd.ActsDiag φ (ggGamma J hBJ b) t)
    (h9 : 9 ≤ Nat.card (ggGamma J hBJ).range) :
    ∃ a ∈ ggAutomizer J Bs, orderOf a = 3 := by
  classical
  let π : Equiv.Perm (Fin 3) →* J := φ.comp (permSLInvHom (n := 2) (K := K))
  have hN : ∀ σ, (π σ : G) ∈ Subgroup.normalizer (Bs : Set G) := by
    intro σ
    simpa [π, permSLInvHom] using
      permSL_mem_normalizer_Bs hBJ φ hker hBs hSC hdiag σ
  let A : Subgroup (MulAut J) := (ggGamma J hBJ).range
  have hAe : CFSG.Open.IsElemAbelian p A := by
    dsimp [A]
    exact isElemAbelian_range
      (fun a b : ↥Bs => (@IsMulCommutative.is_comm ↥Bs _ hBs.1).comm a b)
      (fun b : ↥Bs => Subtype.ext (by simpa using hBs.2 b b.2))
      (ggGamma J hBJ)
  have hsc : GGTorusSelfCent p A := by
    dsimp [A]
    exact ggTorusSelfCent_ggGamma hBJ hSC
  have hdiagA : ∀ a ∈ A, ∃ t : Fin 3 → K, TypeANbrDvd.ActsDiag φ a t := by
    rintro a ⟨b, rfl⟩
    exact hdiag b
  have hNA : ∀ σ, NbrInnerWeylA.permConj φ σ ∈
      Subgroup.normalizer (A : Set (MulAut J)) :=
    fun σ => TypeANbrDvd.permConj_mem_normalizer_of_selfCent
      hφ hker hAe.2 hsc hdiagA σ
  have hnot := TypeANbrDvd.finRotate_not_mem_ker_of_nine_le_card hNA hφ hker
    (fun a => hdiagA a a.2) h9
  let ρ : Equiv.Perm (Fin 3) →* ggAutomizer J Bs := permAutActual π hN
  have hne : ρ (finRotate 3) ≠ 1 := by
    intro hσ
    have hc : (ρ (finRotate 3) : MulAut Bs) = 1 := congrArg Subtype.val hσ
    have hover : GGOverGamma hBJ (ρ (finRotate 3))
        (TypeANbrDvd.permAut φ A hNA (finRotate 3)) := by
      rw [show (ρ (finRotate 3) : MulAut Bs) = ggConjAut Bs (hN (finRotate 3)) from by
        simp [ρ]]
      rw [TypeANbrDvd.permAut_apply]
      have hNA' : ggConjAut A (hNA (finRotate 3)) =
          ggConjAut A (conj_mem_normalizer_range_ggGamma hBJ (π (finRotate 3)).2
            (hN (finRotate 3))) := by
        apply MulEquiv.ext
        intro x
        apply Subtype.ext
        rfl
      rw [hNA']
      exact ggOverGamma_conjAut (K := J) (hN := hBJ) (π (finRotate 3)).2 (hN (finRotate 3))
    have ha : TypeANbrDvd.permAut φ A hNA (finRotate 3) = 1 := by
      apply GGOverGamma.eq_one_of_one
      simpa [hc] using hover
    exact hnot ha
  have hpow : ρ (finRotate 3) ^ 3 = 1 := by
    rw [← map_pow, show (finRotate 3 : Equiv.Perm (Fin 3)) ^ 3 = 1 by decide, map_one]
  refine ⟨(ρ (finRotate 3) : MulAut Bs), (ρ (finRotate 3)).2, ?_⟩
  rw [Subgroup.orderOf_coe]
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime hpow hne

end CFSG.StandardType.ResJCubicBlock

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open Matrix


theorem ggF4Ends_exists_order_three_linear (hMp : GGInnerDiagMpInput) (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} {f : ℕ} (hH : GGResHyp p B Bs x L D J y K)
    (hInn : GGInnerDiagOn Bs L) (hM : StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 4 2 f)
    (hpf : p ∣ 2 ^ f - 1) :
    ∃ a ∈ ggAutomizer L Bs ⊓ ggAutomizer K Bs, orderOf a = 3 := by
  classical
  have hL : GGTypeALocalCfg p B Bs x L D J 3 f y K :=
    ⟨hH.1, hInn, hM, hpf, le_rfl, hH.2.2.2.2.1⟩
  have hp : p.Prime := hL.prime
  have hp2 : p ≠ 2 := hL.ne_two
  obtain ⟨φ₁, hrange, hker, hdiag, hJ⟩ := ggF4JBx_exists_lift_L_lowerBlock hMp hL
  let hBJ : Bs ≤ Subgroup.normalizer (J : Set G) := GGResHyp.Bs_le_normalizer_J hH
  have hmemJ : ∀ s, (φ₁.comp (slLowerBlockHom 3 (GaloisField 2 f))) s ∈ J := by
    intro s
    rw [← hJ]
    exact ⟨s, rfl⟩
  let φJ : Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 f) →* J :=
    (φ₁.comp (slLowerBlockHom 3 (GaloisField 2 f))).codRestrict J hmemJ
  have hφJ : Function.Surjective φJ := by
    rintro ⟨g, hg⟩
    rw [← hJ] at hg
    obtain ⟨s, rfl⟩ := hg
    exact ⟨s, rfl⟩
  have hinj : Function.Injective (φ₁.comp (slLowerBlockHom 3 (GaloisField 2 f))) :=
    injective_comp_slLowerBlockHom (n := 3) (F := GaloisField 2 f) hker
  have hkerJ : ∀ g, φJ g = 1 → g ∈ CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars 3
      (GaloisField 2 f) := by
    intro g hg
    have hg' : (φ₁.comp (slLowerBlockHom 3 (GaloisField 2 f))) g =
        (φ₁.comp (slLowerBlockHom 3 (GaloisField 2 f))) 1 := by
      rw [map_one]
      exact congrArg Subtype.val hg
    rw [hinj hg']
    exact Subgroup.one_mem _
  have hdiagJ : ∀ b : Bs, ∃ t : Fin 3 → GaloisField 2 f,
      TypeANbrDvd.ActsDiag φJ (ggGamma J hBJ b) t := by
    intro b
    obtain ⟨h, hh⟩ := hdiag b b.2
    refine ⟨fun i => (h (Fin.succ i) : GaloisField 2 f), ggDiagUnit (h ∘ Fin.succ), rfl,
      fun s => ?_⟩
    apply Subtype.ext
    rw [ggGamma_coe]
    change (b : G) * φ₁ (slLowerBlockHom 3 (GaloisField 2 f) s) * (b : G)⁻¹ =
      φ₁ (slLowerBlockHom 3 (GaloisField 2 f) (ggDiagConj (h ∘ Fin.succ) s))
    rw [hh, ggDiagConj_slLowerBlockHom]
  have h9 : 9 ≤ Nat.card (ggGamma J hBJ).range := by
    have h := GGResHyp.sq_le_card_gamma_J hH
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      omega
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left hp3 2
      _ ≤ _ := h
  obtain ⟨a, haJ, ha3⟩ := ResJCubicBlock.ggF4Ends_exists_orderOf_three_slThree hBJ φJ hφJ hkerJ
    hL.isElemAbelian hL.bs_centralizer hdiagJ h9
  have hJL : J ≤ L := by
    rw [← hJ, ← hrange]
    rintro _ ⟨s, rfl⟩
    exact ⟨slLowerBlockHom 3 (GaloisField 2 f) s, rfl⟩
  have hpJ : p ∣ Nat.card J := hJ ▸ prime_dvd_card_range_comp_slLowerBlockHom hp
    hL.dvd_natCard_units (by omega) hker
  have hJK : J ≤ K := le_of_ggNbr hLB hL.1.1 hL.1.2.2 hpJ hL.nbr
  exact ⟨a, ⟨ggAutomizer_mono Bs hJL haJ, ggAutomizer_mono Bs hJK haJ⟩, ha3⟩

end CFSG.StandardType

end
