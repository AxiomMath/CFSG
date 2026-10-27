module

public import CFSG.RankThree.PartOne.KC.SymplecticFullCentralizerGraph
public import CFSG.RankThree.PartOne.KC.SymplecticInnerPlane

public section

namespace CFSG.RankThree.PartOne

open Polynomial CFSG CFSG.RankThree.Classical CFSG.LocalAnalysis.ComponentInitial
  CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCSpFull CFSG.ComponentClassification
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

section Wiring

variable {r : ℕ} {K : Type} [Field K] {ℓ f p : ℕ} {Ahat : Subgroup (StatedSp r K)}

theorem centralizes_of_spListedFacts {B : Subgroup (MulAut (StatedProj (StatedSp r K)))}
    {a₀ : StatedProj (StatedSp r K)} {J : Subgroup (StatedProj (StatedSp r K))}
    (hF : SpListedFacts p B a₀ J) (hB : (MulAut.conj : StatedProj (StatedSp r K) →*
      MulAut (StatedProj (StatedSp r K))).range ≤ B)
    {α : MulAut (StatedProj (StatedSp r K))}
    (hα : ∀ L : Subgroup (MulAut (StatedProj (StatedSp r K))),
      L ≤ B ⊓ Subgroup.centralizer ({MulAut.conj a₀} : Set (MulAut (StatedProj (StatedSp r K)))) →
      IsComponent (L.subgroupOf (B ⊓ Subgroup.centralizer
        ({MulAut.conj a₀} : Set (MulAut (StatedProj (StatedSp r K)))))) →
      ∀ d ∈ L, d * α = α * d) :
    ∀ t ∈ J, α * MulAut.conj t = MulAut.conj t * α := by
  obtain ⟨hJN, -, -, hcomp, -⟩ := hF
  intro t ht
  have hL : J.map (MulAut.conj : StatedProj (StatedSp r K) →*
      MulAut (StatedProj (StatedSp r K))) ≤ B ⊓ Subgroup.centralizer
        ({MulAut.conj a₀} : Set (MulAut (StatedProj (StatedSp r K)))) := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨hB ⟨y, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subgroup.mem_centralizer_singleton_iff.mp (hJN hy)
  exact (hα _ hL hcomp (MulAut.conj t) (Subgroup.mem_map_of_mem _ ht)).symm

theorem comap_conj_plane {T : Type} [Group T]
    (hinj : Function.Injective (MulAut.conj : T →* MulAut T)) {p : ℕ}
    {A : Subgroup (MulAut T)} (hAH : A ≤ (MulAut.conj : T →* MulAut T).range)
    (hA : IsElementaryAbelian p A) (hAcard : Nat.card A = p ^ 2) :
    IsElemAbelian p (A.comap (MulAut.conj : T →* MulAut T)) ∧
      Nat.card (A.comap (MulAut.conj : T →* MulAut T)) = p ^ 2 := by
  have := hA
  have hmap : (A.comap (MulAut.conj : T →* MulAut T)).map (MulAut.conj : T →* MulAut T) = A := by
    rw [Subgroup.map_comap_eq, inf_eq_right.mpr hAH]
  have hcomm : IsMulCommutative (A.comap (MulAut.conj : T →* MulAut T)) := by
    refine ⟨⟨fun x y => Subtype.ext (hinj ?_)⟩⟩
    rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
    exact congrArg Subtype.val (mul_comm' (⟨MulAut.conj (x : T), x.2⟩ : A)
      ⟨MulAut.conj (y : T), y.2⟩)
  have hpow : ∀ x ∈ A.comap (MulAut.conj : T →* MulAut T), x ^ p = 1 := by
    intro x hx
    apply hinj
    rw [map_pow, map_one]
    exact elemPow_eq_one_of_isElementaryAbelian (MulAut.conj x) hx
  have hcard : Nat.card (A.comap (MulAut.conj : T →* MulAut T)) = p ^ 2 := by
    rw [← hAcard, ← Subgroup.card_map_of_injective hinj
      (K := A.comap (MulAut.conj : T →* MulAut T)), hmap]
  exact ⟨⟨hcomm, hpow⟩, hcard⟩

end Wiring

theorem symplectic_inner_plane_local_components_full_automorphism_centralizer
    {ℓ f p r : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type} [Field K] (hK : Nat.card K = ℓ ^ f)
    (hp : p.Prime) (hp3 : 3 < p) (hpℓ : p ≠ ℓ) (hr : 2 ≤ r) (hrq : ¬ (r = 2 ∧ ℓ ^ f = 2))
    (A : Subgroup (MulAut (StatedProj (StatedSp r K))))
    (hAH : A ≤ OuterAutomorphisms.inner (StatedProj (StatedSp r K)))
    (hA : IsElementaryAbelian p A) (hAcard : Nat.card A = p ^ 2) :
    (∀ α : MulAut (StatedProj (StatedSp r K)),
      (∀ a ∈ A, a ≠ 1 → ∀ L : Subgroup (MulAut (StatedProj (StatedSp r K))),
        L ≤ OuterAutomorphisms.inner (StatedProj (StatedSp r K)) ⊓
          Subgroup.centralizer ({a} : Set (MulAut (StatedProj (StatedSp r K)))) →
        IsComponent (L.subgroupOf (OuterAutomorphisms.inner (StatedProj (StatedSp r K)) ⊓
          Subgroup.centralizer ({a} : Set (MulAut (StatedProj (StatedSp r K)))))) →
        ∀ d ∈ L, d * α = α * d) → α = 1) ∧
    (∃! Ahat : Subgroup (StatedSp r K), IsSpPlaneLift r K p A Ahat) ∧
    ∀ Ahat : Subgroup (StatedSp r K), IsSpPlaneLift r K p A Ahat → SpPlaneDecomp p Ahat := by
  classical
  have hfin : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero f hℓ.ne_zero)
  have hr1 : 1 ≤ r := by omega
  have hp2 : p ≠ 2 := by omega
  have hinj := spConj_injective hℓ hf hK hr hrq
  have hAinn : A ≤ (MulAut.conj : StatedProj (StatedSp r K) →*
      MulAut (StatedProj (StatedSp r K))).range := hAH
  have hex := exists_unique_spPlaneLift hr1 hp hp2 hinj A hAinn hA hAcard
  have hsetup : ∀ Ahat : Subgroup (StatedSp r K), IsSpPlaneLift r K p A Ahat →
      SpPlaneSetup ℓ f p r K Ahat := fun Ahat hlift =>
    ⟨hℓ, hf, hK, hp, hp3, hpℓ, hr, hrq, hlift.1, hlift.2.1⟩
  refine ⟨?_, hex, fun Ahat hlift => (hsetup Ahat hlift).decomp⟩
  intro α hα
  obtain ⟨Ahat, hlift, -⟩ := hex
  have S := hsetup Ahat hlift
  obtain ⟨hA₀, hcard₀⟩ := comap_conj_plane hinj hAinn hA hAcard
  refine S.eq_one_of_centralizes (fun x hxA hx1 => ?_)
  have hord := S.orderOf_eq hxA hx1
  have ha : spInnerLift r K x ∈ A := hlift.2.2.1 ▸ Subgroup.mem_map_of_mem _ hxA
  have ha1 : spInnerLift r K x ≠ 1 := fun h =>
    hx1 (hlift.2.2.2 hxA (one_mem _) (h.trans (map_one _).symm))
  have hmemA₀ : proj r K x ∈ A.comap (MulAut.conj : StatedProj (StatedSp r K) →*
      MulAut (StatedProj (StatedSp r K))) := ha
  have hne₀ : proj r K x ≠ 1 := fun h => ha1 (by rw [spInnerLift_apply, h, map_one])
  have hF := symplectic_inner_plane_below_prime_local_core_centralization hℓ hf hK hp hp3 hpℓ hr
    hrq (OuterAutomorphisms.inner (StatedProj (StatedSp r K))) le_rfl _ hA₀ hcard₀ (proj r K x)
    hmemA₀ hne₀ x rfl hord
  have hα' : ∀ L : Subgroup (MulAut (StatedProj (StatedSp r K))),
      L ≤ OuterAutomorphisms.inner (StatedProj (StatedSp r K)) ⊓
        Subgroup.centralizer ({MulAut.conj (proj r K x)} :
          Set (MulAut (StatedProj (StatedSp r K)))) →
      IsComponent (L.subgroupOf (OuterAutomorphisms.inner (StatedProj (StatedSp r K)) ⊓
        Subgroup.centralizer ({MulAut.conj (proj r K x)} :
          Set (MulAut (StatedProj (StatedSp r K)))))) →
      ∀ d ∈ L, d * α = α * d := fun L hL hc d hd => hα (spInnerLift r K x) ha ha1 L hL hc d hd
  exact ⟨fun hlisted t ht => centralizes_of_spListedFacts (hF.2.1 hlisted) le_rfl hα' t ht,
    fun h hmem hh1 hm2 t ht =>
      centralizes_of_spListedFacts (hF.1 ⟨h, hmem⟩ hh1 hm2) le_rfl hα' t ht⟩

end CFSG.RankThree.PartOne
