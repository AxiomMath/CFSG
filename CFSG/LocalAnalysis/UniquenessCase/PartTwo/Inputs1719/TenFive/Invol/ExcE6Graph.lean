module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.ExcRootETwist
import CFSG.Blueprint.ChevalleyRootArtifact
public import CFSG.ClassicalInvolution.Balance.LayerGenerationShortAdjoint
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.ExcRoot
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.ExcRootE

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)
open CFSG.LieType.SeitzGeneration.ExcOuterLeOne (exists_adjData_valid_E)
open CFSG.ClassicalInvolution.Balance (rootDiagAut_xPar rootChar_single_eq)


private lemma coe_xPar_single_eq_xUnit {τ : Tag} {K : Type} [Field K] (i : Fin τ.rank) (c : K) :
    ((xPar (rootOperatorFamily τ) (Pi.single i 1) c : adjointGroup τ K) : ModGL τ K) =
      xUnit τ K i c := by
  rw [xPar_simple, RootOperatorFamily.coe_eltElement, RootOperatorFamily.eltUnit_simple]

theorem diagramMap_conj_entrywise_xPar_single (t : TwistTag) (K : Type) [Field K]
    (δ : K →+* K) (i : Fin t.tag.rank) (c : K) :
    diagramMap t K * Units.map (entrywiseHom δ)
        (xPar (rootOperatorFamily t.tag) (Pi.single i 1) c : ModGL t.tag K) *
        (diagramMap t K)⁻¹ =
      (xPar (rootOperatorFamily t.tag) (Pi.single (t.perm i) 1) (δ c) : ModGL t.tag K) := by
  rw [coe_xPar_single_eq_xUnit i c, coe_xPar_single_eq_xUnit (t.perm i) (δ c)]
  rw [← twistHom_apply, twistHom_xUnit]

theorem diagramMap_conj_xPar_single (t : TwistTag) (K : Type) [Field K] (i : Fin t.tag.rank)
    (c : K) :
    diagramMap t K * (xPar (rootOperatorFamily t.tag) (Pi.single i 1) c : ModGL t.tag K) *
        (diagramMap t K)⁻¹ =
      (xPar (rootOperatorFamily t.tag) (Pi.single (t.perm i) 1) c : ModGL t.tag K) := by
  have h := diagramMap_conj_entrywise_xPar_single t K (RingHom.id K) i c
  have h1 : ∀ g : ModGL t.tag K, Units.map (entrywiseHom (RingHom.id K)) g = g :=
    fun g => Units.ext (entrywise_id _)
  simpa only [h1, RingHom.id_apply] using h

theorem diagramMap_conj_xPar_zero_mul_five_E6 (K : Type) [Field K] (c : K) :
    diagramMap TwistTag.E6 K *
        ((xPar (rootOperatorFamily TwistTag.E6.tag) (Pi.single ⟨0, by decide⟩ 1) c *
          xPar (rootOperatorFamily TwistTag.E6.tag) (Pi.single ⟨5, by decide⟩ 1) (-c) :
            adjointGroup TwistTag.E6.tag K) : ModGL TwistTag.E6.tag K) *
        (diagramMap TwistTag.E6 K)⁻¹ =
      ((xPar (rootOperatorFamily TwistTag.E6.tag) (Pi.single ⟨0, by decide⟩ 1) c *
          xPar (rootOperatorFamily TwistTag.E6.tag) (Pi.single ⟨5, by decide⟩ 1) (-c) :
            adjointGroup TwistTag.E6.tag K) : ModGL TwistTag.E6.tag K)⁻¹ := by
  classical
  let F := rootOperatorFamily TwistTag.E6.tag
  let i0 : Fin TwistTag.E6.tag.rank := ⟨0, by decide⟩
  let i5 : Fin TwistTag.E6.tag.rank := ⟨5, by decide⟩
  let P : ModGL TwistTag.E6.tag K := diagramMap TwistTag.E6 K
  let x : adjointGroup TwistTag.E6.tag K :=
    xPar (K := K) F (Pi.single i0 1) c * xPar (K := K) F (Pi.single i5 1) (-c)
  have h0 : TwistTag.E6.perm i0 = i5 := by decide
  have h5 : TwistTag.E6.perm i5 = i0 := by decide
  have hc0 := diagramMap_conj_xPar_single TwistTag.E6 K i0 c
  have hc5 := diagramMap_conj_xPar_single TwistTag.E6 K i5 (-c)
  rw [h0] at hc0
  rw [h5] at hc5
  have hinv : (x : ModGL TwistTag.E6.tag K)⁻¹ =
      (xPar (K := K) F (Pi.single i5 1) c : ModGL TwistTag.E6.tag K) *
        (xPar (K := K) F (Pi.single i0 1) (-c) : ModGL TwistTag.E6.tag K) := by
    have hb : (xPar (K := K) F (Pi.single i5 1) (-c))⁻¹ = xPar (K := K) F (Pi.single i5 1) c := by
      rw [xPar_neg, neg_neg]
    have ha : (xPar (K := K) F (Pi.single i0 1) c)⁻¹ = xPar (K := K) F (Pi.single i0 1) (-c) :=
      xPar_neg _ _
    dsimp only [x]
    rw [Subgroup.coe_mul, mul_inv_rev, ← Subgroup.coe_inv, ← Subgroup.coe_inv, hb, ha]
  have hP : P * (x : ModGL TwistTag.E6.tag K) * P⁻¹ = (x : ModGL TwistTag.E6.tag K)⁻¹ := by
    calc P * (x : ModGL TwistTag.E6.tag K) * P⁻¹
        = (P * (xPar (K := K) F (Pi.single i0 1) c : ModGL TwistTag.E6.tag K) * P⁻¹) *
            (P * (xPar (K := K) F (Pi.single i5 1) (-c) : ModGL TwistTag.E6.tag K) * P⁻¹) := by
          dsimp only [x]
          simp only [Subgroup.coe_mul]
          group
      _ = (xPar (K := K) F (Pi.single i5 1) c : ModGL TwistTag.E6.tag K) *
            (xPar (K := K) F (Pi.single i0 1) (-c) : ModGL TwistTag.E6.tag K) := by
          rw [hc0, hc5]
      _ = (x : ModGL TwistTag.E6.tag K)⁻¹ := hinv.symm
  exact hP

theorem exists_diagramMap_inv_good_E6 {K : Type} [Field K] [Finite K] {p e : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) [CharP K p] (hK : Nat.card K = p ^ e) (h3 : 3 < p ^ e) :
    ∃ x : adjointGroup TwistTag.E6.tag K, orderOf x = p ∧
      diagramMap TwistTag.E6 K * (x : ModGL TwistTag.E6.tag K) * (diagramMap TwistTag.E6 K)⁻¹ =
        (x : ModGL TwistTag.E6.tag K)⁻¹ ∧ IsSpecialGood p x := by
  classical
  let F := rootOperatorFamily TwistTag.E6.tag
  let i0 : Fin TwistTag.E6.tag.rank := ⟨0, by decide⟩
  let i2 : Fin TwistTag.E6.tag.rank := ⟨2, by decide⟩
  let i5 : Fin TwistTag.E6.tag.rank := ⟨5, by decide⟩
  let P : ModGL TwistTag.E6.tag K := diagramMap TwistTag.E6 K
  let x : adjointGroup TwistTag.E6.tag K :=
    xPar (K := K) F (Pi.single i0 1) 1 * xPar (K := K) F (Pi.single i5 1) (-1)
  have hP : P * (x : ModGL TwistTag.E6.tag K) * P⁻¹ = (x : ModGL TwistTag.E6.tag K)⁻¹ :=
    diagramMap_conj_xPar_zero_mul_five_E6 K 1
  obtain ⟨D, hD, hτ'⟩ := exists_adjData_valid_E (τ := TwistTag.E6.tag) (Or.inl rfl)
  have hne52 : Pi.single i5 1 + Pi.single i2 1 ≠ (0 : Fin TwistTag.E6.tag.rank → ℤ) := by
    decide
  have hn52 : ¬IsRoot TwistTag.E6.tag (Pi.single i5 1 + Pi.single i2 1) :=
    fun h => absurd (isRoot_iff_mem_artifactRoots.1 h) (by decide)
  have hne50 : Pi.single i5 1 + Pi.single i0 1 ≠ (0 : Fin TwistTag.E6.tag.rank → ℤ) := by
    decide
  have hn50 : ¬IsRoot TwistTag.E6.tag (Pi.single i5 1 + Pi.single i0 1) :=
    fun h => absurd (isRoot_iff_mem_artifactRoots.1 h) (by decide)
  have hwl : ∀ s t,
      Commute (xPar (K := K) F (Pi.single i5 1) s) (xPar (K := K) F (Pi.single i2 1) t) :=
    fun s t => commute_xPar hD hτ' (isRoot_single _ i5) (isRoot_single _ i2) hne52 hn52 s t
  have hwi : ∀ s t,
      Commute (xPar (K := K) F (Pi.single i5 1) s) (xPar (K := K) F (Pi.single i0 1) t) :=
    fun s t => commute_xPar hD hτ' (isRoot_single _ i5) (isRoot_single _ i0) hne50 hn50 s t
  obtain ⟨hord, hgood⟩ := isSpecialGood_xPar_single_mul (τ := TwistTag.E6.tag)
    (Or.inr (Or.inl rfl)) hp hp2 hK h3 (i := i0) (l := i2) (by decide) (by decide)
    (w := fun s => xPar (K := K) F (Pi.single i5 1) s) (fun s t => xPar_add _ s t) hwl hwi
    (-AddMonoidHom.id K) one_ne_zero
  have hf : (-AddMonoidHom.id K) 1 = -1 := by simp
  refine ⟨x, ?_, hP, ?_⟩
  · dsimp only [x]
    simpa only [hf] using hord
  · dsimp only [x]
    simpa only [hf] using hgood

theorem rootDiag_diagramMap_conj_xPar_one_E6 {K : Type} [Field K]
    (s : Fin TwistTag.E6.tag.rank → Kˣ) (hs : s ⟨1, by decide⟩ = -1) (c : K) :
    rootDiagUnit TwistTag.E6.tag s * diagramMap TwistTag.E6 K *
        (xPar (rootOperatorFamily TwistTag.E6.tag) (Pi.single ⟨1, by decide⟩ 1) c :
          ModGL TwistTag.E6.tag K) *
        (rootDiagUnit TwistTag.E6.tag s * diagramMap TwistTag.E6 K)⁻¹ =
      (xPar (rootOperatorFamily TwistTag.E6.tag) (Pi.single ⟨1, by decide⟩ 1) c :
        ModGL TwistTag.E6.tag K)⁻¹ := by
  classical
  let F := rootOperatorFamily TwistTag.E6.tag
  let i1 : Fin TwistTag.E6.tag.rank := ⟨1, by decide⟩
  let x : adjointGroup TwistTag.E6.tag K := xPar (K := K) F (Pi.single i1 1) c
  have hperm : TwistTag.E6.perm i1 = i1 := by decide
  have hPx := diagramMap_conj_xPar_single TwistTag.E6 K i1 c
  rw [hperm] at hPx
  have hP : diagramMap TwistTag.E6 K * (x : ModGL TwistTag.E6.tag K) *
      (diagramMap TwistTag.E6 K)⁻¹ = (x : ModGL TwistTag.E6.tag K) := hPx
  have hs' : s i1 = -1 := hs
  have hd_adj : rootDiagAut TwistTag.E6.tag K s x = x⁻¹ := by
    dsimp only [x]
    rw [rootDiagAut_xPar s (isRoot_single _ i1) c, rootChar_single_eq, hs']
    simp only [Units.val_neg, Units.val_one, neg_one_mul]
    exact (xPar_neg _ c).symm
  have hd : rootDiagUnit TwistTag.E6.tag s * (x : ModGL TwistTag.E6.tag K) *
      (rootDiagUnit TwistTag.E6.tag s)⁻¹ = (x : ModGL TwistTag.E6.tag K)⁻¹ := by
    have h := congrArg (fun g : adjointGroup TwistTag.E6.tag K =>
      (g : ModGL TwistTag.E6.tag K)) hd_adj
    simpa only [coe_rootDiagAut, Subgroup.coe_inv] using h
  calc rootDiagUnit TwistTag.E6.tag s * diagramMap TwistTag.E6 K *
        (x : ModGL TwistTag.E6.tag K) *
        (rootDiagUnit TwistTag.E6.tag s * diagramMap TwistTag.E6 K)⁻¹
      = rootDiagUnit TwistTag.E6.tag s *
          (diagramMap TwistTag.E6 K * (x : ModGL TwistTag.E6.tag K) *
            (diagramMap TwistTag.E6 K)⁻¹) * (rootDiagUnit TwistTag.E6.tag s)⁻¹ := by group
    _ = rootDiagUnit TwistTag.E6.tag s * (x : ModGL TwistTag.E6.tag K) *
          (rootDiagUnit TwistTag.E6.tag s)⁻¹ := by rw [hP]
    _ = (x : ModGL TwistTag.E6.tag K)⁻¹ := hd

theorem exists_rootDiag_diagramMap_inv_good_E6 {K : Type} [Field K] [Finite K] {p e : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) [CharP K p] (hK : Nat.card K = p ^ e) (h3 : 3 < p ^ e)
    (s : Fin TwistTag.E6.tag.rank → Kˣ) (hs : s ⟨1, by decide⟩ = -1) :
    ∃ x : adjointGroup TwistTag.E6.tag K, orderOf x = p ∧
      rootDiagUnit TwistTag.E6.tag s * diagramMap TwistTag.E6 K * (x : ModGL TwistTag.E6.tag K) *
          (rootDiagUnit TwistTag.E6.tag s * diagramMap TwistTag.E6 K)⁻¹ =
        (x : ModGL TwistTag.E6.tag K)⁻¹ ∧ IsSpecialGood p x :=
  ⟨_, orderOf_xPar hp (isRoot_single _ _) one_ne_zero, rootDiag_diagramMap_conj_xPar_one_E6 s hs 1,
    isSpecialGood_xPar_single (Or.inr (Or.inl rfl)) hp hp2 hK h3 _ 1⟩

theorem exists_diagramMap_entrywise_inv_good_E6 {K : Type} [Field K] [Finite K] {p e : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) [CharP K p] (hK : Nat.card K = p ^ e) (h3 : 3 < p ^ e)
    (δ : K →+* K) (hδ2 : ∀ c, δ (δ c) = c) (hδ1 : ∃ c, δ c ≠ c) :
    ∃ x : adjointGroup TwistTag.E6.tag K, orderOf x = p ∧
      diagramMap TwistTag.E6 K * Units.map (entrywiseHom δ) (x : ModGL TwistTag.E6.tag K) *
          (diagramMap TwistTag.E6 K)⁻¹ = (x : ModGL TwistTag.E6.tag K)⁻¹ ∧
        IsSpecialGood p x := by
  classical
  let F := rootOperatorFamily TwistTag.E6.tag
  let i1 : Fin TwistTag.E6.tag.rank := ⟨1, by decide⟩
  obtain ⟨c₀, hc₀⟩ := hδ1
  let θ : K := c₀ - δ c₀
  have hθ : θ ≠ 0 := by
    dsimp only [θ]
    exact sub_ne_zero.mpr (Ne.symm hc₀)
  have hδθ : δ θ = -θ := by
    dsimp only [θ]
    rw [map_sub, hδ2]
    ring
  let x : adjointGroup TwistTag.E6.tag K := xPar (K := K) F (Pi.single i1 1) θ
  have hperm : TwistTag.E6.perm i1 = i1 := by decide
  have hP := diagramMap_conj_entrywise_xPar_single TwistTag.E6 K δ i1 θ
  rw [hperm] at hP
  have hcoe : (xPar (K := K) F (Pi.single i1 1) (δ θ) : ModGL TwistTag.E6.tag K) =
      (x : ModGL TwistTag.E6.tag K)⁻¹ := by
    rw [hδθ]
    dsimp only [x]
    rw [← xPar_neg]
    rfl
  have hP' : diagramMap TwistTag.E6 K * Units.map (entrywiseHom δ)
      (x : ModGL TwistTag.E6.tag K) * (diagramMap TwistTag.E6 K)⁻¹ =
      (x : ModGL TwistTag.E6.tag K)⁻¹ := hP.trans hcoe
  exact ⟨x, orderOf_xPar hp (isRoot_single _ i1) hθ, hP',
    isSpecialGood_xPar_single (Or.inr (Or.inl rfl)) hp hp2 hK h3 i1 θ⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
