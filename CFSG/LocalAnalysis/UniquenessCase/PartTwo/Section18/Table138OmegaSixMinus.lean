module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenFourteenK
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaSixMinusFixTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.MultNatCoords
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214Rk
public import CFSG.GroupTheory.ABGLocalTools.PStabilityQSL2
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoConfig
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscape
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrHom
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrLarge
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrXGen
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbDefs
public import CFSG.LocalAnalysis.AGLEmbedding.ZZPrimeDefs
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalFamily
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinearStrong
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16ONorm
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21a
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214a
public import CFSG.RankThree.PartOne.S8.Statements

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise commutatorElement Matrix

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mult
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.LocalAnalysis.RankThreeUC

theorem k_Table13_8_Omega6Minus_pi_holds_of (hIso : K_Omega6Minus_natIsoMod) :
    K_Table13_8_Omega6Minus_pi := by
  classical
  intro W _ _ H p n s _ hs1 hs2 hsum hp hcong v hv
  obtain ⟨I, -, hind, hsup, hN⟩ := hsum
  let i₀ : Fin s := ⟨0, hs1⟩
  let i₁ : Fin s := ⟨s - 1, by omega⟩
  obtain ⟨-, K, hK, hKf, b, c, hcard, hpoly, π0, hπ0⟩ := hN i₀
  let _ : Field K := hK
  have _ : Finite K := hKf
  have _ : CharP K 2 :=
    CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_two hcard
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · rw [hn0, pow_zero] at hcard
      have h2 : 1 < Nat.card K := Finite.one_lt_card
      omega
    · exact hnpos
  let Γ := StatedOmega (StatedQuadMinus (6 / 2) K b c)
  have _ : NeZero s := ⟨by omega⟩
  have hVia : SumOfNatVia (FFModel.nat Γ) H ⊤ ⊥ s π0 :=
    sumOfNatVia_of_isoMod (D := FFModel.nat Γ) (X := H) (I := I) hind hsup i₀ hπ0
      (fun i => hIso H (I i₀) (I i) n (hN i₀) (hN i))
  obtain ⟨-, e, -, he, -⟩ := exists_coords_of_sumOfNatVia Γ hVia
  have hpq : p ∣ Nat.card K + 1 := by
    rw [hcard]
    exact CFSG.LocalAnalysis.UniquenessCase.UC22.P2214R.dvd_of_cong hcong
  obtain ⟨g, hgΩ, hgp, hgx, hgy⟩ := exists_fix_two hpoly hcard hn1 hp hpq
    (fun i => Multiplicative.toAdd (e v) (i₀, i)) (fun i => Multiplicative.toAdd (e v) (i₁, i))
  let t : ↥H := π0 ⟨g, hgΩ⟩
  have het : ∀ w : W, e ((t : MulAut W) w) = matAut (diagGL s (g : GL _ K)) (e w) :=
    fun w => he ⟨g, hgΩ⟩ w
  have hfix : (t : MulAut W) v = v := by
    apply e.injective
    rw [het]
    apply Multiplicative.toAdd.injective
    show ((diagGL s (g : GL _ K) : GL _ K) : Matrix _ _ K) *ᵥ Multiplicative.toAdd (e v) =
      Multiplicative.toAdd (e v)
    funext q
    rw [diagGL_mulVec]
    obtain ⟨j, i⟩ := q
    have hj : j = i₀ ∨ j = i₁ := by
      rcases j with ⟨j, hj⟩
      simp only [i₀, i₁, Fin.ext_iff]
      omega
    rcases hj with rfl | rfl
    · exact congrFun hgx i
    · exact congrFun hgy i
  have : Fact p.Prime := ⟨hp⟩
  have hdvd : orderOf (t : MulAut W) ∣ p := by
    have hγ : orderOf (⟨g, hgΩ⟩ : ↥Γ) = p := by
      rw [Subgroup.orderOf_mk, hgp]
    rw [Subgroup.orderOf_coe, ← hγ]
    exact orderOf_map_dvd π0 _
  have ht1 : (t : MulAut W) ≠ 1 := by
    intro h1
    have hm : matHom (diagGL s (g : GL _ K)) = 1 := by
      ext x
      obtain ⟨w, rfl⟩ := e.surjective x
      rw [matHom_apply, ← het, h1]
      rfl
    have hg1 : (g : GL _ K) = 1 :=
      diagGL_injective s (matHom_injective (hm.trans (map_one matHom).symm) |>.trans
        (map_one (diagGL s)).symm)
    rw [hg1, orderOf_one] at hgp
    exact hp.one_lt.ne hgp
  have hord : orderOf (t : MulAut W) = p :=
    ((Nat.dvd_prime hp).mp hdvd).resolve_left fun h => ht1 (orderOf_eq_one_iff.mp h)
  have htC : (t : MulAut W) ∈ centVec H v := centVec.mem_centVec.mpr ⟨t.2, hfix⟩
  have htO : (t : MulAut W) ∈ Opp p (centVec H v) :=
    Subgroup.subset_closure ⟨htC, 1, by rw [pow_one, hord]⟩
  refine ⟨hp, ?_⟩
  have := orderOf_dvd_natCard (⟨(t : MulAut W), htO⟩ : ↥(Opp p (centVec H v)))
  rwa [Subgroup.orderOf_mk, hord] at this

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
