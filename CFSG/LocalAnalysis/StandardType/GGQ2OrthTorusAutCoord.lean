module

public import CFSG.LocalAnalysis.StandardType.GGQ2OrthPlaneCoord
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP9SignOmega
import CFSG.RankThree.PartOne.S11d.OrthDicksonOmega
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs141d2
import CFSG.GH74.GLS.IVK.Proofs2.Lemma12hb
import CFSG.GH74.GLS.IVK.Proofs2.Lemma13d
import CFSG.GH74.GLS.IVK.Proofs2.Lemma13e
import CFSG.GH74.GLS.IVK.Proofs2.Lemma13g
import CFSG.HardMathSupport.Solomon.Coordinator.L5Conj
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.LinearFieldExport
import CFSG.LocalAnalysis.GLTheoremA.S4.PGroupCover
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.CatalogInputs
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Input319
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma123
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1313Z
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1314b
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1314c
import CFSG.LocalAnalysis.GLTheoremB.Prop95Input18
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3M11Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityKFacts
import Certificates.Certificate41501

public section

namespace CFSG.StandardType.GGQ2Frame.OrthBlocks

open Matrix CFSG.ClassicalGroups.Orthogonal Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} {t : ℕ} {δ : Fin 2}

theorem exists_moveExp_of_conj_otau (hK : Nat.card K = 2) (hζ : Function.Injective ζ)
    {Q : QuadraticForm K (Fin (t + δ.val) ⊕ Fin (t + δ.val) → K)} (hQ : ⇑Q = planeQ t δ)
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate)
    {y : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K} (hy : y ∈ omegaQ (K := K) t δ)
    {φ : PlaneRaw.V t → PlaneRaw.V t} (hφ : ∀ u, y * otau ζ t δ u * y⁻¹ = otau ζ t δ (φ u)) :
    ∃ (π : Equiv.Perm (Fin t)) (η : Fin t → Bool),
      (δ.val = 0 → Even (Finset.univ.filter fun i => η i = true).card) ∧
        φ = ChoiceTwo.moveExp π η := by
  classical
  let C : ChoiceTwoOm.OmCoord K Q (planeTorus ζ t δ) := planeCoord ζ t δ hK hζ hQ
  let g : (Fin (t + δ.val) ⊕ Fin (t + δ.val) → K) ≃ₗ[K]
      (Fin (t + δ.val) ⊕ Fin (t + δ.val) → K) := toLinEquiv _ K y
  have hconj : ∀ f, g * C.tor f * g⁻¹ = C.tor (φ f) := by
    intro f
    change (toLinEquiv _ K y) * (toLinEquiv _ K (otau ζ t δ f)) * (toLinEquiv _ K y)⁻¹ =
      toLinEquiv _ K (otau ζ t δ (φ f))
    calc (toLinEquiv _ K y) * (toLinEquiv _ K (otau ζ t δ f)) * (toLinEquiv _ K y)⁻¹
        = toLinEquiv _ K (y * otau ζ t δ f * y⁻¹) := by
          rw [map_mul, map_mul, map_inv]
      _ = toLinEquiv _ K (otau ζ t δ (φ f)) := by rw [hφ f]
  have hg : g ∈ CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hnd := by
    have h1 : y ∈ CFSG.Open.StatedOmega (planeQ (K := K) t δ) := hy
    rw [CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap hQ] at h1
    have h2 : g ∈ CFSG.RankThree.Classical2.orthDerived Q := by
      simpa [g] using (Subgroup.mem_comap.mp h1)
    exact CFSG.RankThree.PartOne.FieldFix.orthDerived_le_omegaGroup hnd h2
  by_cases hδ : δ.val = 0
  · have hW0 : C.W0 = ⊥ := planeCoord_W0_eq_bot ζ t δ hK hζ hQ hδ
    obtain ⟨π, η, hEven, hφeq⟩ :=
      (CFSG.StandardType.ChoiceTwoOm.OmCoord.exists_omega_conj_iff_of_W0_eq_bot hK hnd C hW0
        φ).mp ⟨g, hg, hconj⟩
    exact ⟨π, η, fun _ => hEven, hφeq⟩
  · have hW0 : C.W0 ≠ ⊥ := planeCoord_W0_ne_bot ζ t δ hK hζ hQ hδ
    obtain ⟨π, η, hφeq⟩ :=
      (CFSG.StandardType.ChoiceTwoOm.OmCoord.exists_omega_conj_iff_of_W0_ne_bot hnd C hW0
        φ).mp ⟨g, hg, hconj⟩
    exact ⟨π, η, fun h0 => absurd h0 hδ, hφeq⟩

private theorem otc_mem_orthDerived
    {Q : QuadraticForm K (Fin (t + δ.val) ⊕ Fin (t + δ.val) → K)}
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate) (ht : 3 ≤ t + δ.val)
    {g : (Fin (t + δ.val) ⊕ Fin (t + δ.val) → K) ≃ₗ[K] (Fin (t + δ.val) ⊕ Fin (t + δ.val) → K)}
    (hg : g ∈ CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hnd) :
    g ∈ CFSG.RankThree.Classical2.orthDerived Q := by
  have hfin : finrank K (Fin (t + δ.val) ⊕ Fin (t + δ.val) → K) = 2 * (t + δ.val) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    ring
  have h3 : 3 ≤ finrank K (Fin (t + δ.val) ⊕ Fin (t + δ.val) → K) := by
    rw [hfin]
    omega
  have hne : ¬ CFSG.RankThree.PartOne.KCOrthogonal.SmallFixedException Q := by
    rintro (⟨h3', -⟩ | ⟨⟨h4', -⟩, -⟩)
    · omega
    · omega
  exact CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs141d.omegaGroup_le_orthDerived_of_listed
    Q hnd h3 hne hg

omit [Finite K] in
private theorem otc_monoC_single {π : Equiv.Perm (Fin t)} {η : Fin t → Bool} {j : Fin t}
    (hπj : π j = j) (hηj : η j = false) (c : K × K) :
    ChoiceTwoOm.monoC π η (Pi.single j c) = Pi.single j c := by
  funext i
  rw [ChoiceTwoOm.monoC_apply]
  by_cases hij : i = j
  · subst hij
    rw [hπj, hηj, ChoiceTwoOm.sgnC_false]
  · have hπi : π i ≠ j := fun h => hij (π.injective (h.trans hπj.symm))
    rw [Pi.single_eq_of_ne hπi, map_zero, Pi.single_eq_of_ne hij]

theorem exists_omegaQ_conj_otau_moveExp (hK : Nat.card K = 2) (hζ : Function.Injective ζ)
    {Q : QuadraticForm K (Fin (t + δ.val) ⊕ Fin (t + δ.val) → K)} (hQ : ⇑Q = planeQ t δ)
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate) (ht : 3 ≤ t + δ.val)
    (π : Equiv.Perm (Fin t)) (η : Fin t → Bool)
    (hpar : δ.val = 0 → Even (Finset.univ.filter fun i => η i = true).card) :
    ∃ y ∈ omegaQ (K := K) t δ,
      (∀ u, y * otau ζ t δ u * y⁻¹ = otau ζ t δ (ChoiceTwo.moveExp π η u)) ∧
      ∀ j : Fin t, π j = j → η j = false →
        ∀ k : Fin (t + δ.val) ⊕ Fin (t + δ.val), Sum.elim id id k = Fin.castAdd δ.val j →
          (y : Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val)) (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) *ᵥ
              Pi.single k 1 = Pi.single k 1 := by
  classical
  let C : ChoiceTwoOm.OmCoord K Q (planeTorus ζ t δ) := planeCoord ζ t δ hK hζ hQ
  have hpar' : Even (Finset.univ.filter fun i => η i = true).card ∨ C.W0 ≠ ⊥ := by
    by_cases hδ : δ.val = 0
    · exact Or.inl (hpar hδ)
    · exact Or.inr (planeCoord_W0_ne_bot ζ t δ hK hζ hQ hδ)
  obtain ⟨g, hgΩ, hconj, happly⟩ :=
    CFSG.StandardType.ChoiceTwoOm.OmCoord.exists_omega_conj_moveExp_apply hnd C π η hpar'
  have hgD : g ∈ CFSG.RankThree.Classical2.orthDerived Q := otc_mem_orthDerived hnd ht hgΩ
  let y : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K := (toLinEquiv _ K).symm g
  have hy : y ∈ omegaQ (K := K) t δ := by
    have h1 : y ∈ (CFSG.RankThree.Classical2.orthDerived Q).comap
        (toLinEquiv _ K).toMonoidHom := by
      rw [Subgroup.mem_comap]
      simpa [y] using hgD
    rwa [← CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap hQ] at h1
  have hconjGL : ∀ u : PlaneRaw.V t,
      y * otau ζ t δ u * y⁻¹ = otau ζ t δ (ChoiceTwo.moveExp π η u) := by
    intro u
    apply (toLinEquiv _ K).injective
    rw [map_mul, map_mul, map_inv]; simp only [y, MulEquiv.apply_symm_apply]
    rw [← planeCoord_tor]
    exact hconj u
  refine ⟨y, hy, hconjGL, ?_⟩
  intro j hπj hηj k hk
  obtain ⟨c, hc⟩ := exists_planeCoord_Φ_eq_single ζ t δ hK hζ hQ j k hk
  have hmono := otc_monoC_single (K := K) hπj hηj c
  have hgfix : g (Pi.single k 1) = Pi.single k 1 := by
    calc g (Pi.single k 1) = g (C.Φ (Pi.single j c, 0)) := by rw [hc]
      _ = C.Φ (ChoiceTwoOm.monoC π η (Pi.single j c), 0) := happly (Pi.single j c)
      _ = C.Φ (Pi.single j c, 0) := congrArg (fun d => C.Φ (d, 0)) hmono
      _ = Pi.single k 1 := hc
  rw [← toLinEquiv_apply]; simpa [y] using hgfix

end CFSG.StandardType.GGQ2Frame.OrthBlocks
