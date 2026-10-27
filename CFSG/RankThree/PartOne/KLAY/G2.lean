module

public import CFSG.RankThree.PartOne.KLAY.Core
public import CFSG.RankThree.PartOne.KLAY.RootSL2
public import CFSG.RankThree.PartOne.KE.A1Centralizer
public import CFSG.RankThree.PartOne.KF.G2Sylow

public section

namespace CFSG.RankThree.PartOne.KLAY

open CFSG CFSG.LocalCores CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KFU CFSG.RankThree.Classical
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.UnbalancedCatalog
open scoped Pointwise

variable {p : ℕ} {K : Type} [Field K]

theorem g2_centralizer_mem (hp : p.Prime) (h5 : 5 ≤ p) {a : Fin Tag.G2.rank → Kˣ}
    (hap : a ^ p = 1) (ha1 : a ≠ 1) {θ : Fin Tag.G2.rank → ℤ} (hθ : IsRoot .G2 θ)
    (hθa : rootChar a θ = 1) {y : ModGL .G2 K} (hy : y ∈ adjointGroup .G2 K)
    (hc : y * rootDiagUnit .G2 a = rootDiagUnit .G2 a * y) :
    y ∈ (torusGroup .G2 K : Set (ModGL .G2 K)) *
      (rootRankOneGroup .G2 K θ : Set (ModGL .G2 K)) := by
  classical
  have hp3 : 3 < p := by omega
  have hX : y ∈ toralCentralizer .G2 K a :=
    mem_toralCentralizer.2 ⟨hy, by rw [← hc, mul_assoc, mul_inv_cancel, mul_one]⟩
  have heq := toralCentralizer_eq_toralRootGroup_of_le (τ := .G2) (K := K)
    (rootCharStabilizer_le_kernelReflectionGroup_G2 hp hp3 hap ha1)
  rw [heq] at hX
  have hker : rootCharKernel a ⊆ {θ, -θ} := by
    have hθmem : θ ∈ rootCharKernel a := ⟨hθ, hθa⟩
    rcases rootCharKernel_G2_cases hp hp3 hap ha1 with h0 | ⟨α, -, hαk⟩
    · rw [h0] at hθmem
      exact absurd hθmem (Set.notMem_empty _)
    · rw [hαk] at hθmem ⊢
      rcases hθmem with rfl | hθα
      · exact subset_rfl
      · rw [Set.mem_singleton_iff] at hθα
        subst hθα
        intro x hx
        rcases hx with rfl | hx
        · simp
        · rw [Set.mem_singleton_iff] at hx
          subst hx
          simp
  set Q := rootRankOneGroup .G2 K θ with hQ
  have hQsplit : Q = rootSubgroup .G2 K θ ⊔ rootSubgroup .G2 K (-θ) :=
    (exceptional_Lang_root_rank_one_torus_transport .G2 K hθ).1
  have hθQ : rootSubgroup .G2 K θ ≤ Q := by rw [hQsplit]; exact le_sup_left
  have hnθQ : rootSubgroup .G2 K (-θ) ≤ Q := by rw [hQsplit]; exact le_sup_right
  have hspan : rootSpan .G2 K {θ, -θ} ≤ Q := iSup₂_le fun α hα => by
    rcases hα with rfl | hα
    · exact hθQ
    · rw [Set.mem_singleton_iff] at hα
      subst hα
      exact hnθQ
  have hX' : y ∈ torusGroup .G2 K ⊔ Q :=
    sup_le_sup_left ((rootSpan_mono hker).trans hspan) _ hX
  rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _
    (KE.torusGroup_le_normalizer_rootRankOneGroup hθ)]
  exact hX'

section Side

@[expose] noncomputable def g2Phi (K : Type) [Field K] :
    SL2 K →* ↥(adjointGroup .G2 K) :=
  (rootSL2Map .G2 (Pi.single g2ia 1) (RingHom.id K)).codRestrict (adjointGroup .G2 K)
    (rootSL2Map_mem_adjointGroup _ _)

theorem coe_g2Phi (A : SL2 K) :
    ((g2Phi K A : ↥(adjointGroup .G2 K)) : ModGL .G2 K) =
      rootSL2Map .G2 (Pi.single g2ia 1) (RingHom.id K) A := rfl

theorem g2_SL2Torus {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ p) (h1 : 1 < p) :
    SL2Torus p (g2Phi K) (Tp p K) := by
  have hθ : IsRoot .G2 (Pi.single g2ia 1) := IsRoot.basis g2ia
  refine SL2Torus.of_rootDiag hθ (RingHom.id K) (g2Phi K) (fun A => rfl)
    (fun t ht => Tp_exp t ht) ?_ ?_ ?_
  · rintro t ⟨b, rfl⟩
    exact ⟨fun i => ((b i : rootsOfUnity p K) : Kˣ),
      rootChar (fun i => ((b i : rootsOfUnity p K) : Kˣ)) (Pi.single g2ia 1), rfl, Units.ext rfl⟩
  · intro s hs
    have hmem : ∀ j, s ^ Tag.G2.cartan g2ia j ∈ rootsOfUnity p K := fun j => by
      rw [mem_rootsOfUnity, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hs,
        one_zpow]
    refine ⟨fun j => ⟨s ^ Tag.G2.cartan g2ia j, hmem j⟩, ?_⟩
    apply Subtype.ext
    change tpHom p K _ = rootSL2Map _ _ _ (HSL s)
    rw [rootSL2Map_single_HSL]
    rfl
  · have hz : ζ ^ p = 1 := hζ.pow_eq_one
    let z : rootsOfUnity p K := ⟨ζ, (mem_rootsOfUnity p ζ).2 hz⟩
    refine ⟨tpM p K (fun j => if j = g2ia then z else 1), ⟨_, rfl⟩,
      fun i => ((if i = g2ia then z else 1 : rootsOfUnity p K) : Kˣ), ζ, rfl, ?_,
      hζ.ne_one h1⟩
    rw [rootChar_single]
    simp [z]

theorem rootSL2Map_id {τ : Tag} (θ : Fin τ.rank → ℤ) (A : SL2 K) :
    rootSL2Map τ θ (RingHom.id K) A = rootSL2 τ K θ A := by
  have h : Matrix.SpecialLinearGroup.map (RingHom.id K) A = A := by
    apply Subtype.ext
    simp
  rw [rootSL2Map_apply, h]

end Side

section Main

variable [Finite K] [CharP K 2]

theorem g2_side {f : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hf1 : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (hpq : p ∣ 2 ^ f - 1) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) :
    ∃ bM ∈ Tp p K, bM ^ p = 1 ∧ bM ≠ 1 ∧ MSide p f (Tp p K) bM := by
  classical
  obtain ⟨ζ, hζ⟩ := hζ
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one
  have hζ1 : ζ ≠ 1 := hζ.ne_one (by omega)
  have h4 : 4 ≤ Nat.card K := by
    have hpf : p ≤ 2 ^ f - 1 := Nat.le_of_dvd (by
      have := Nat.one_lt_two_pow (n := f) (by omega)
      omega) hpq
    rw [hK]
    omega
  have hθ : IsRoot .G2 (Pi.single g2ia 1) := IsRoot.basis g2ia
  let z : rootsOfUnity p K := ⟨ζ, (mem_rootsOfUnity p ζ).2 hζp⟩
  let b₀ : Fin Tag.G2.rank → rootsOfUnity p K := fun j => if j = g2ia then 1 else z
  let a₀ : Fin Tag.G2.rank → Kˣ := fun i => ((b₀ i : rootsOfUnity p K) : Kˣ)
  have hne : g2ir ≠ g2ia := by decide
  have ha₀ia : a₀ g2ia = 1 := by simp [a₀, b₀]
  have ha₀ir : a₀ g2ir = ζ := by simp [a₀, b₀, hne, z]
  have hap : a₀ ^ p = 1 := funext fun j => by
    have := (mem_rootsOfUnity p _).1 (b₀ j).2
    simpa [a₀] using this
  have ha1 : a₀ ≠ 1 := fun h => hζ1 (by rw [← ha₀ir, h]; rfl)
  have hθa : rootChar a₀ (Pi.single g2ia 1) = 1 := by rw [rootChar_single, ha₀ia]
  set bM : ↥(adjointGroup .G2 K) := tpM p K b₀ with hbM
  have hbMd : ((bM : ↥(adjointGroup .G2 K)) : ModGL .G2 K) = rootDiagUnit .G2 a₀ := rfl
  have hbMT : bM ∈ Tp p K := tpM_mem_Tp b₀
  have hbM1 : bM ≠ 1 := fun h => hζ1 (by
    have h1 : b₀ = 1 := tpM_injective (h.trans (map_one _).symm)
    have := congrFun h1 g2ir
    simpa [b₀, hne, z] using congrArg Subtype.val this)
  refine ⟨bM, hbMT, Tp_exp bM hbMT, hbM1, ?_⟩
  have hSL := g2_SL2Torus (K := K) hζ (by omega : 1 < p)
  have hD : layerD bM = (g2Phi K).range := by
    refine inSubgroup_perfectResidual_centralizer_eq (adjointGroup .G2 K) bM (torusGroup .G2 K)
      (rootRankOneGroup .G2 K (Pi.single g2ia 1)) (triangular_borel_structure.{0, 0} .G2 K).1
      (KE.torusGroup_le_normalizer_rootRankOneGroup hθ) ?_ ?_ (g2Phi K).range ?_
      (hSL.isQuasisimple_range h4).1
    · rintro _ ⟨A, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h := rootDiagUnit_conj_rootSL2 a₀ hθ A
      rw [hθa, conjSL_diagUnitOne_one] at h
      exact (mul_inv_eq_iff_eq_mul.1 h).symm
    · intro y hy
      have hc := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hy)
      exact g2_centralizer_mem hp h5 hap ha1 hθ hθa y.2 hc
    · ext x
      constructor
      · rintro ⟨_, ⟨A, rfl⟩, rfl⟩
        refine ⟨(g2Phi K A).2, ⟨A, ?_⟩⟩
        change _ = ((g2Phi K A : ↥(adjointGroup .G2 K)) : ModGL .G2 K)
        rw [coe_g2Phi, rootSL2Map_id]
      · rintro ⟨hxM, A, rfl⟩
        refine ⟨g2Phi K A, ⟨A, rfl⟩, ?_⟩
        change ((g2Phi K A : ↥(adjointGroup .G2 K)) : ModGL .G2 K) = _
        rw [coe_g2Phi, rootSL2Map_id]
  exact MSide.of_SL2Torus hSL hp ⟨ζ, hζ⟩ hK h4 hD

end Main

end CFSG.RankThree.PartOne.KLAY
