module

public import CFSG.RankThree.PartOne.KLAY.G2

public section

namespace CFSG.RankThree.PartOne.KF132

open CFSG CFSG.LocalCores CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU
  CFSG.RankThree.PartOne.KLAY CFSG.RankThree.Classical
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.UnbalancedCatalog

variable {p : ℕ} {K : Type} [Field K]

@[expose] noncomputable def g2PhiI (K : Type) [Field K] (i : Fin Tag.G2.rank) :
    SL2 K →* ↥(adjointGroup .G2 K) :=
  (rootSL2Map .G2 (Pi.single i 1) (RingHom.id K)).codRestrict (adjointGroup .G2 K)
    (rootSL2Map_mem_adjointGroup _ _)

theorem coe_g2PhiI (i : Fin Tag.G2.rank) (A : SL2 K) :
    ((g2PhiI K i A : ↥(adjointGroup .G2 K)) : ModGL .G2 K) =
      rootSL2Map .G2 (Pi.single i 1) (RingHom.id K) A := rfl

theorem g2_SL2TorusI {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ p) (h1 : 1 < p)
    (i : Fin Tag.G2.rank) : SL2Torus p (g2PhiI K i) (Tp p K) := by
  have hθ : IsRoot .G2 (Pi.single i 1) := IsRoot.basis i
  refine SL2Torus.of_rootDiag hθ (RingHom.id K) (g2PhiI K i) (fun A => rfl)
    (fun t ht => Tp_exp t ht) ?_ ?_ ?_
  · rintro t ⟨b, rfl⟩
    exact ⟨fun j => ((b j : rootsOfUnity p K) : Kˣ),
      rootChar (fun j => ((b j : rootsOfUnity p K) : Kˣ)) (Pi.single i 1), rfl, Units.ext rfl⟩
  · intro s hs
    have hmem : ∀ j, s ^ Tag.G2.cartan i j ∈ rootsOfUnity p K := fun j => by
      rw [mem_rootsOfUnity, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hs,
        one_zpow]
    refine ⟨fun j => ⟨s ^ Tag.G2.cartan i j, hmem j⟩, ?_⟩
    apply Subtype.ext
    change tpHom p K _ = rootSL2Map _ _ _ (HSL s)
    rw [rootSL2Map_single_HSL]
    rfl
  · have hz : ζ ^ p = 1 := hζ.pow_eq_one
    let z : rootsOfUnity p K := ⟨ζ, (mem_rootsOfUnity p ζ).2 hz⟩
    refine ⟨tpM p K (fun j => if j = i then z else 1), ⟨_, rfl⟩,
      fun j => ((if j = i then z else 1 : rootsOfUnity p K) : Kˣ), ζ, rfl, ?_,
      hζ.ne_one h1⟩
    rw [rootChar_single]
    simp [z]

section Layer

variable [Finite K]

theorem g2_layerD_I {f : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hK : Nat.card K = 2 ^ f)
    (hpq : p ∣ 2 ^ f - 1) (hf1 : 1 ≤ f) {z : rootsOfUnity p K} (hz : IsPrimitiveRoot (z : Kˣ) p)
    (i : Fin Tag.G2.rank) :
    layerD (tpM p K (fun j => if j = i then 1 else z)) = (g2PhiI K i).range := by
  classical
  have hζp : (z : Kˣ) ^ p = 1 := hz.pow_eq_one
  have hζ1 : (z : Kˣ) ≠ 1 := hz.ne_one (by omega)
  have h4 : 4 ≤ Nat.card K := by
    have hpf : p ≤ 2 ^ f - 1 := Nat.le_of_dvd (by
      have := Nat.one_lt_two_pow (n := f) (by omega)
      omega) hpq
    rw [hK]
    omega
  have hθ : IsRoot .G2 (Pi.single i 1) := IsRoot.basis i
  let b₀ : Fin Tag.G2.rank → rootsOfUnity p K := fun j => if j = i then 1 else z
  let a₀ : Fin Tag.G2.rank → Kˣ := fun j => ((b₀ j : rootsOfUnity p K) : Kˣ)
  have hap : a₀ ^ p = 1 := funext fun j => by
    have := (mem_rootsOfUnity p _).1 (b₀ j).2
    simpa [a₀] using this
  obtain ⟨j₀, hj₀⟩ : ∃ j₀ : Fin Tag.G2.rank, j₀ ≠ i := by
    rcases fin_G2_cases i with rfl | rfl
    · exact ⟨g2ir, by decide⟩
    · exact ⟨g2ia, by decide⟩
  have ha1 : a₀ ≠ 1 := fun h => hζ1 (by
    have := congrFun h j₀
    simpa [a₀, b₀, hj₀] using this)
  have hθa : rootChar a₀ (Pi.single i 1) = 1 := by
    rw [rootChar_single]
    simp [a₀, b₀]
  set bM : ↥(adjointGroup .G2 K) := tpM p K b₀ with hbM
  have hbMd : ((bM : ↥(adjointGroup .G2 K)) : ModGL .G2 K) = rootDiagUnit .G2 a₀ := rfl
  have hSL := g2_SL2TorusI (K := K) hz (by omega : 1 < p) i
  refine inSubgroup_perfectResidual_centralizer_eq (adjointGroup .G2 K) bM (torusGroup .G2 K)
    (rootRankOneGroup .G2 K (Pi.single i 1)) (triangular_borel_structure.{0, 0} .G2 K).1
    (KE.torusGroup_le_normalizer_rootRankOneGroup hθ) ?_ ?_ (g2PhiI K i).range ?_
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
      refine ⟨(g2PhiI K i A).2, ⟨A, ?_⟩⟩
      change _ = ((g2PhiI K i A : ↥(adjointGroup .G2 K)) : ModGL .G2 K)
      rw [coe_g2PhiI, rootSL2Map_id]
    · rintro ⟨hxM, A, rfl⟩
      refine ⟨g2PhiI K i A, ⟨A, rfl⟩, ?_⟩
      change ((g2PhiI K i A : ↥(adjointGroup .G2 K)) : ModGL .G2 K) = _
      rw [coe_g2PhiI, rootSL2Map_id]

end Layer

theorem g2vec_zero (z : rootsOfUnity p K) :
    (fun j : Fin Tag.G2.rank => if j = g2ia then (1 : rootsOfUnity p K) else z) = ![1, z] := by
  funext j
  rcases fin_G2_cases j with rfl | rfl
  · rfl
  · have : g2ir ≠ g2ia := by decide
    simp [this]
    rfl

theorem g2vec_one (z : rootsOfUnity p K) :
    (fun j : Fin Tag.G2.rank => if j = g2ir then (1 : rootsOfUnity p K) else z) = ![z, 1] := by
  funext j
  rcases fin_G2_cases j with rfl | rfl
  · have : g2ia ≠ g2ir := by decide
    simp [this]
    rfl
  · rfl

end CFSG.RankThree.PartOne.KF132
