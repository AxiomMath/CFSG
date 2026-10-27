module

public import CFSG.RankThree.PartOne.KC.SymplecticInnerEndpointMult
public import CFSG.RankThree.PartOne.KC.SymplecticInnerPlane
public import CFSG.RankThree.PartOne.KC.OrthogonalInnerPlaneProducts

public section

namespace CFSG.RankThree.PartOne

open Polynomial Module CFSG CFSG.RankThree.LocalRank CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonalModel CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

theorem symplectic_inner_plane_planeLocalCoreInner {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    {K : Type} [Field K] (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpℓ : p ≠ ℓ) {r : ℕ} (hr : 2 ≤ r) (hrq : ¬ (r = 2 ∧ ℓ ^ f = 2))
    (hfull : CommonLayerCentralizerTrivial (StatedProj (StatedSp r K)) p) :
    PlaneLocalCoreInner p (StatedProj (StatedSp r K)) (SpLiftMultiplicitiesCoprime p) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hq0 : ℓ ^ f ≠ 0 := pow_ne_zero f hℓ.ne_zero
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact hq0)
  have hp2 : p ≠ 2 := by omega
  intro B hB A hAinner hA hAcard hmult t htA ht1
  obtain ⟨-, -, hinj⟩ := spProj_facts hℓ hf hK hr hrq
  have hfinT : Finite (StatedProj (StatedSp r K)) :=
    CFSG.ClassicalGroups.Symplectic.finite_statedProj_statedSp r K
  have hfinAut : Finite (MulAut (StatedProj (StatedSp r K))) :=
    Finite.of_injective (fun f : MulAut (StatedProj (StatedSp r K)) =>
      (f : StatedProj (StatedSp r K) → _)) DFunLike.coe_injective
  set A' : Subgroup (StatedProj (StatedSp r K)) :=
    A.comap (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K)))
    with hA'
  have hmapA' : A'.map (MulAut.conj : StatedProj (StatedSp r K) →*
      MulAut (StatedProj (StatedSp r K))) = A := by
    rw [hA', Subgroup.map_comap_eq, inf_eq_right.mpr hAinner]
  have hcardA' : Nat.card A' = p ^ 2 := by
    rw [← hAcard, ← Subgroup.card_map_of_injective hinj (K := A'), hmapA']
  have hA'el : Assembly.IsElemAbelian p A' := by
    have hcomm : ∀ x ∈ A', ∀ y ∈ A', x * y = y * x := by
      intro x hx y hy
      apply hinj
      rw [map_mul, map_mul]
      have := hA.1
      exact congrArg Subtype.val (mul_comm' (⟨MulAut.conj x, hx⟩ : A) ⟨MulAut.conj y, hy⟩)
    refine ⟨⟨⟨fun x y => Subtype.ext (hcomm x x.2 y y.2)⟩⟩, ?_⟩
    intro x hx
    apply hinj
    rw [map_pow, map_one]
    exact elemPow_eq_one_of_isElementaryAbelian (MulAut.conj x) hx
  have hcent : ∀ a ∈ A, a ≠ 1 → ∀ s ∈ inSubgroup (aschbacherSolvableCore p)
      (B ⊓ Subgroup.centralizer ({a} : Set (MulAut (StatedProj (StatedSp r K))))),
      ∀ g ∈ A, g * s = s * g := by
    intro a haA ha1 s hs g hg
    obtain ⟨a₀, rfl⟩ : a ∈ (MulAut.conj : StatedProj (StatedSp r K) →*
        MulAut (StatedProj (StatedSp r K))).range := hAinner haA
    obtain ⟨g₀, rfl⟩ : g ∈ (MulAut.conj : StatedProj (StatedSp r K) →*
        MulAut (StatedProj (StatedSp r K))).range := hAinner hg
    have ha₀A' : a₀ ∈ A' := haA
    have ha₀1 : a₀ ≠ 1 := fun h => ha1 (by rw [h, map_one])
    have hord : orderOf a₀ = p := orderOf_eq_prime (hA'el.2 a₀ ha₀A') ha₀1
    obtain ⟨⟨x, ⟨hxa, hxp⟩, -⟩, -⟩ :=
      symplectic_cross_prime_primary_centralizer_blocks hℓ hf hK hp hp2 hpℓ (by omega) a₀ hord
    have hpm : ∀ h : primaryFactors (spEnd x), (h : K[X]) ≠ X - 1 →
        ¬ p ∣ primaryMultiplicity (spEnd x) (h : K[X]) := fun h hh =>
      hmult x hxp (by rw [hxa]; exact haA) (by rw [hxa]; exact ha1) h hh
    obtain ⟨-, -, -, -, -, -, h7, -⟩ := symplectic_inner_plane_below_prime_local_core_centralization
      hℓ hf hK hp hp3 hpℓ hr hrq B hB A' hA'el hcardA' a₀ ha₀A' ha₀1 x hxa hxp
    exact ((h7 hpm).2.2 g₀ hg s hs).symm
  refine sup_eq_bot_iff.mpr ⟨?_, ?_⟩
  ·
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro s hs
    exact Subgroup.mem_centralizer_iff.mpr fun g hg => hcent t htA ht1 s hs g hg
  ·
    rw [eq_bot_iff]
    intro α hα
    rw [Subgroup.mem_bot]
    have hpoint := (iInf_centralizer_layerCentralizer_eq_bot_iff B A).mp
      (hfull B hB A hAinner hA hAcard)
    refine hpoint α fun a haA ha1 d hd => ?_
    have hαa : α ∈ inSubgroup (aschbacherSolvableCore p)
        (B ⊓ Subgroup.centralizer ({a} : Set (MulAut (StatedProj (StatedSp r K))))) := by
      have := hα
      unfold autThetaT at this
      rw [Subgroup.mem_iInf] at this
      have h2 := this a
      rw [Subgroup.mem_iInf] at h2
      have h3 := h2 haA
      rw [Subgroup.mem_iInf] at h3
      exact h3 ha1
    exact commute_layerCentralizer_of_mem_core hp B a hαa hd

end CFSG.RankThree.PartOne
