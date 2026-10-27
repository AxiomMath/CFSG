module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeLinDefs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeRLeaf
import CFSG.LocalAnalysis.StandardType.GGTablePThreeLinShapeLift
import CFSG.LocalAnalysis.StandardType.GGTablePThreeLinShapeSetup
import CFSG.LocalAnalysis.StandardType.GGTablePThreeLinShapeBlock
import CFSG.LocalAnalysis.StandardType.GGTablePThreeLinShapeIso
import CFSG.LocalAnalysis.StandardType.GGTablePThreeLinShapeInn
import CFSG.LocalAnalysis.StandardType.GGTablePThreeLinShapeLam
import CFSG.LocalAnalysis.StandardType.GGTablePThreeLinShapeSupp
import CFSG.LocalAnalysis.StandardType.GGTablePThreeLinShapeKer
import CFSG.LocalAnalysis.StandardType.GGTablePThreeLinShapePGL
import CFSG.LocalAnalysis.StandardType.GGTablePThreeLinShapeCards

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly
open Polynomial CFSG.RankThree.PartOne.KCPrimary CFSG.LocalAnalysis.ComponentInitial
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.RankThree.CALinearPrimary

private lemma linShape_center
    {K : Type} [Field K] [Finite K]
    {N : ℕ}
    {X : Type} [Group X] [Finite X]
    {J : Subgroup X}
    {J' : Subgroup (PSLg N K)} {E : Type} [Field E] {m j : ℕ}
    {f : Matrix.SpecialLinearGroup (Fin m) E →* ↥J'}
    (hf : Function.Surjective f)
    (hblk : m = 3 → (j = 1 ∧ 3 ∣ Nat.card K - 1 ∨ j = 2) →
      ∃ z : Matrix.SpecialLinearGroup (Fin m) E, z ∈ Subgroup.center _ ∧ f z ≠ 1)
    (hcen : Subgroup.center J = ⊥ → Subgroup.center J' = ⊥)
    (hm : m = 3) (hj : j = 1 ∧ 3 ∣ Nat.card K - 1 ∨ j = 2) :
    Subgroup.center J ≠ ⊥ := by
  obtain ⟨z, hz, hfz⟩ := hblk hm hj
  have hcent : f z ∈ Subgroup.center ↥J' := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := hf y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz x]
  intro hJbot
  have hJ'bot : Subgroup.center J' = ⊥ := hcen hJbot
  refine hfz (Subgroup.mem_bot.mp ?_)
  rw [← hJ'bot]
  exact hcent

private lemma linShape_rank
    {K : Type} [Field K] [Finite K]
    {N : ℕ}
    {X : Type} [Group X] [Finite X]
    {A : Subgroup (MulAut X)}
    {Ā : Subgroup (MulAut (PSLg N K))}
    {δ' : MulAut (PSLg N K)}
    {J' : Subgroup (PSLg N K)} (hchar : CharP K 2) (hN : 2 ≤ N)
    (hspl : 3 ∣ Nat.card K - 1 ∨ Nat.card K = 2) (hR : RDatum Ā δ' J')
    (hcardĀ : Nat.card Ā = Nat.card A)
    (hĀI : ∀ a ∈ Ā, a ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K))
      Set.univ)
    {d : GL (Fin N) K}
    (hd : LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K))
        (fun h h' => (h' : GL (Fin N) K) = d * h * d⁻¹) δ')
    (hd3 : d ^ 3 ∈ LargeEvenScalars (Fin N) K) (hdns : d ∉ LargeEvenScalars (Fin N) K)
    {h : Polynomial K} (hh : h ∈ primaryFactors (glA d : Module.End K (Fin N → K))) (hgood : IsGoodFactor d h)
    {e : PSLg N K ≃* LinearFlag.projectiveSL N K}
    (heJ : J' = Subgroup.comap e.toMonoidHom ((specialFactor d h).map (LinearFlag.proj N K)))
    {E : Type} [Field E] [Finite E] (hcharE : CharP E 2) {m j : ℕ}
    (hm : m = 2)
    (hmult : m = primaryMultiplicity (glA d : Module.End K (Fin N → K)) h)
    (hmE : 4 ≤ Nat.card E)
    {f : Matrix.SpecialLinearGroup (Fin m) E →* ↥J'}
    (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center _)
    (hj : j = h.natDegree) :
    (j = 3 → Nat.card A ≤ 3 ^ 3) ∧ (j ≠ 3 → Nat.card A < 3 ^ 3) := by
  obtain ⟨lam, g, hgraph, hgrel, hlam3⟩ := linShape_rank_lambda hR hĀI hd
  obtain ⟨hlam1, hc⟩ := linShape_rank_support hR hĀI hd hgraph hlam3 hgrel hh hgood heJ hj
  have hpgl := linShape_rank_pgl2 (E := E) hcharE hmE
  have hk := linShape_rank_kernel hchar hN hR hd hdns hgraph hlam3 hgrel hh hgood heJ hcharE hm hmult hmE hf hker hpgl
  exact linShape_rank_cards hcardĀ hc hk hlam1

theorem linShape_holds :
    ∀ (K : Type) [Field K] [Finite K], CharP K 2 → ∀ N : ℕ, 2 ≤ N →
      (IsSimpleGroup (PSLg N K) ∧ ∃ a b : PSLg N K, a * b ≠ b * a) →
      (3 ∣ Nat.card K - 1 ∨ Nat.card K = 2) →
      ∀ (X : Type) [Group X] [Finite X], commutator X = ⊤ →
        ∀ (θ : X ⧸ Subgroup.center X ≃* PSLg N K) (A : Subgroup (MulAut X)) (δ : MulAut X)
          (J : Subgroup X), GGKLocal A δ J →
          (∀ Q : Subgroup X, IsComponentOf Q (ggAutFixedSubgroup δ) → Q = J) → 3 ^ 3 ≤ Nat.card A →
          GGInducedInn A θ
            (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K)) Set.univ) →
          LinShapeConcl (Nat.card K) N A J := by
  intro K _ _ hchar N hN hsimple hspl X _ _ hperf θ A δ J hKloc huniq hcard hinn
  obtain ⟨Ā, δ', J', hR, hcardĀ, hδ', hmem, hJ', hcen⟩ :=
    leafR_holds X hperf (PSLg N K) θ A δ J hKloc huniq hcard
  have hδA : δ ∈ A := hKloc.1.2.1
  have hδ'mem : δ' ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K))
      Set.univ := by
    rw [← hδ']
    exact hinn δ hδA
  obtain ⟨d, hd, hd3, hdns⟩ := linShape_lift (K := K) (N := N) hN hR hδ'mem
  obtain ⟨h, hh, hgood, e, E, hE, hFE, hcharE, m, j, f,
      hm_eq, hj_eq, heJ, h1, h2, h3, h4, h5, h6, h8, h9, hf, hker⟩ :=
    linShape_setup (K := K) (N := N) hchar hN hspl hR.comp hd hd3
  letI : Field E := hE
  letI : Finite E := hFE
  have hperfJ : commutator J = ⊤ := by
    have hcomp : IsComponentOf J (ggAutFixedSubgroup δ) := hKloc.1.2.2.2.1
    obtain ⟨-, -, hqs⟩ := hcomp
    exact hqs.1
  have h7 : Nonempty (J ⧸ Subgroup.center J ≃* PSLg m E) :=
    linShape_iso (K := K) (N := N) hJ' hperfJ h1 h2 hf hker
  have hblk := linShape_block (K := K) (N := N) hchar hN hd3 hdns hh hgood heJ hm_eq hj_eq h5 h9 hf hker
  have h10 : (m = 3 → (j = 1 ∧ 3 ∣ Nat.card K - 1 ∨ j = 2) → Subgroup.center J ≠ ⊥) :=
    fun hm hj =>
      linShape_center (K := K) (N := N) hf hblk (fun hZ => (hcen.1 hZ).1) hm hj
  have hĀI : ∀ a ∈ Ā, a ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K))
      Set.univ :=
    linShape_induced_range (K := K) (N := N) hperf hinn hmem hcardĀ
  have h11 : (m = 2 → (j = 3 → Nat.card A ≤ 3 ^ 3) ∧ (j ≠ 3 → Nat.card A < 3 ^ 3)) :=
    fun hm =>
      linShape_rank (K := K) (N := N) hchar hN hspl hR hcardĀ hĀI hd hd3 hdns hh hgood heJ hcharE hm
        hm_eq (h2 hm) hf hker hj_eq
  exact ⟨E, hE, hFE, m, j, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

end CFSG.StandardType.TablePThreeKG

end
