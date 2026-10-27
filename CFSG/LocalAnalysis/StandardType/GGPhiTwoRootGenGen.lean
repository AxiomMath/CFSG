module

public import CFSG.LocalAnalysis.StandardType.GGPhiTwoRootGenSL
public import CFSG.HardMathSupport.C14IdxDet
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyBruhat
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E8FourAux.Lift
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigidTools
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.GoodRoot
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeCartanAdj
public import CFSG.RankThree.PartOne.Q1327T.Item7D4W
public import CFSG.RankThree.Chevalley.SteinbergBTTrialitySplitPrimePlane
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExcD4
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompChain
public import CFSG.LocalAnalysis.StandardType.GGPhiTwoGenConj
public import CFSG.LocalAnalysis.StandardType.GGPhiTwoGenInput
public import CFSG.LocalAnalysis.StandardType.GGExcSplitRootGenDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcFldTwo
public import CFSG.LocalAnalysis.StandardType.GGL45NtExcIdxRee
public import CFSG.LocalAnalysis.StandardType.GGL45NtExcRee
public import CFSG.RankThree.PartOne.KE6.Phi3Arith
public import CFSG.RankThree.PartOne.KE6.Phi6Arith

public section

namespace CFSG.StandardType.PhiTwoRootGen

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Steinberg.Adjoint

private theorem excIsLongest_of_smul_eq_neg
    {τ : Tag} {w : WeylGroup τ}
    (hneg : ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → w • γ = -γ) : ExcIsLongest τ w := by
  intro α hα hpos i
  rw [hneg α hα]
  exact neg_nonpos.mpr (hpos i)

private theorem exists_cartan_eq_neg_one
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (i : Fin τ.rank) :
    ∃ j : Fin τ.rank, τ.cartan i j = -1 := by
  rcases hτ with rfl | rfl | rfl <;> fin_cases i <;> decide

private theorem symmetrizedCartan_apply_free
    {τ : Tag} (i j : Fin τ.rank) :
    τ.symmetrizedCartan i j = τ.symmetrizer i i * τ.cartan i j := by
  cases τ
  case G2 | F4 => fin_cases i <;> fin_cases j <;> rfl
  all_goals simp [Tag.symmetrizedCartan, Tag.symmetrizer]

private theorem iform_single_left_free
    {τ : Tag} (i : Fin τ.rank) (y : Fin τ.rank → ℤ) :
    iform (Pi.single i 1) y = τ.symmetrizer i i * ∑ j, τ.cartan i j * y j := by
  simp only [iform, Pi.single_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single i (fun b _ hb => by simp [hb]) (by simp)]
  simp only [if_true, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [symmetrizedCartan_apply_free]
  ring

private theorem iform_single_self_E
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (i : Fin τ.rank) :
    iform (Pi.single i 1) (Pi.single i 1) = 2 := by
  rw [iform_single_left_free, CFSG.StandardType.AutSt.sum_cartan_mul_single_self]
  rcases hτ with rfl | rfl | rfl <;> simp [Tag.symmetrizer]

private theorem iform_single_eq_neg_one
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {i j : Fin τ.rank}
    (hij : i ≠ j) (h : τ.cartan i j = -1) :
    iform (Pi.single i 1) (Pi.single j 1) = -1 := by
  rw [iform_single_left_free, CFSG.StandardType.AutSt.sum_cartan_mul_single]
  rcases hτ with rfl | rfl | rfl <;> simp [h, Tag.symmetrizer]

private theorem symmetrizer_E
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (i : Fin τ.rank) :
    τ.symmetrizer i i = 1 := by
  rcases hτ with rfl | rfl | rfl <;> simp [Tag.symmetrizer]

private theorem cartan_symm_E
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (i j : Fin τ.rank) :
    τ.cartan i j = τ.cartan j i := by
  rcases hτ with rfl | rfl | rfl <;> fin_cases i <;> fin_cases j <;> decide

private theorem iform_comm_E
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (x y : Fin τ.rank → ℤ) :
    iform x y = iform y x := by
  rcases hτ with rfl | rfl | rfl <;>
  ( simp only [iform, Tag.symmetrizedCartan, Tag.symmetrizer, Matrix.one_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [cartan_symm_E (by simp) i j]
    ring )

private theorem iform_single_right_E
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (x : Fin τ.rank → ℤ)
    (i : Fin τ.rank) :
    iform x (Pi.single i 1) = ∑ j, τ.cartan i j * x j := by
  rw [iform_comm_E hτ, iform_single_left_free, symmetrizer_E hτ, one_mul]

private theorem iform_add_left_free
    {τ : Tag} (x x' y : Fin τ.rank → ℤ) :
    iform (x + x') y = iform x y + iform x' y := by
  simp [iform, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private theorem iform_smul_left_free
    {τ : Tag} (c : ℤ) (x y : Fin τ.rank → ℤ) :
    iform (c • x) y = c * iform x y := by
  simp only [iform, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

private theorem iform_sub_left_free
    {τ : Tag} (x x' y : Fin τ.rank → ℤ) :
    iform (x - x') y = iform x y - iform x' y := by
  rw [sub_eq_add_neg, iform_add_left_free, ← neg_one_smul ℤ x', iform_smul_left_free]
  ring

private theorem iform_sub_right_E
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (x y y' : Fin τ.rank → ℤ) :
    iform x (y - y') = iform x y - iform x y' := by
  rw [iform_comm_E hτ x (y - y'), iform_sub_left_free, iform_comm_E hτ y x,
    iform_comm_E hτ y' x]

private theorem iform_smul_right_E
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (c : ℤ)
    (x y : Fin τ.rank → ℤ) : iform x (c • y) = c * iform x y := by
  rw [iform_comm_E hτ x (c • y), iform_smul_left_free, iform_comm_E hτ y x]

private theorem iform_reflect_E
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (i : Fin τ.rank)
    (x y : Fin τ.rank → ℤ) :
    iform (reflect τ i x) (reflect τ i y) = iform x y := by
  have hx : reflect τ i x = x - (∑ j, τ.cartan i j * x j) • Pi.single i 1 := rfl
  have hy : reflect τ i y = y - (∑ j, τ.cartan i j * y j) • Pi.single i 1 := rfl
  rw [hx, hy, iform_sub_left_free, iform_sub_right_E hτ, iform_sub_right_E hτ,
    iform_smul_left_free, iform_smul_left_free, iform_smul_right_E hτ, iform_smul_right_E hτ,
    iform_single_self_E hτ i, iform_single_right_E hτ, iform_single_left_free,
    symmetrizer_E hτ]
  ring

private theorem iform_smul_free_E
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (w : WeylGroup τ)
    (x y : Fin τ.rank → ℤ) : iform (w • x) (w • y) = iform x y := by
  induction w using (coxeterSystem τ).simple_induction_left generalizing x y with
  | one => simp
  | mul_simple_left w i ih =>
    rw [mul_smul, mul_smul, simple_smul, simple_smul,
      iform_reflect_E hτ i (w • x) (w • y), ih]

private theorem corootPair_smul_single_E
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (w : WeylGroup τ)
    (j : Fin τ.rank) (v : Fin τ.rank → ℤ) :
    corootPair (w • (Pi.single j 1 : Fin τ.rank → ℤ)) v =
      ∑ k, τ.cartan j k * (w⁻¹ • v) k := by
  have e1 : iform (w • (Pi.single j 1 : Fin τ.rank → ℤ))
      (w • (Pi.single j 1 : Fin τ.rank → ℤ)) = 2 * τ.symmetrizer j j := by
    rw [iform_smul_free_E hτ, iform_single_self_E hτ, symmetrizer_E hτ]
    norm_num
  have e2 : iform (w • (Pi.single j 1 : Fin τ.rank → ℤ)) v =
      τ.symmetrizer j j * ∑ k, τ.cartan j k * (w⁻¹ • v) k := by
    rw [← smul_inv_smul w v, iform_smul_free_E hτ, iform_single_left_free, inv_smul_smul]
  rw [corootPair, e1, e2, symmetrizer_E hτ]
  simp only [one_mul, mul_one]
  exact Int.mul_ediv_cancel_left _ (by norm_num)

private theorem rootReflection_smul_E
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (v : Fin τ.rank → ℤ) :
    rootReflection β • v = v - corootPair β v • β := by
  have hspec := Classical.choose_spec (Classical.choose_spec (isRoot_iff_exists_smul_single.1 hβ))
  simp only [rootReflection, hβ, ↓reduceDIte]
  rw [smul_conj_simple, ← corootPair_smul_single_E hτ, hspec]

private theorem eq_or_eq_neg_of_excRefl_eq
    {τ : Tag} {p : ℕ} {γ δ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) (hδ : IsRoot τ δ)
    (hfixset : ∀ α : Fin τ.rank → ℤ, IsRoot τ α →
      ∀ t, ExcSplitRootGen.excRefl (p := p) α t = t ↔
        ∑ j, (α j : ZMod p) * t j = 0)
    (hroot : ∀ α β, IsRoot τ α → IsRoot τ β → (∀ t : Fin τ.rank → ZMod p,
      ∑ j, (α j : ZMod p) * t j = 0 → ∑ j, (β j : ZMod p) * t j = 0) → β = α ∨ β = -α)
    (h : ExcSplitRootGen.excRefl (p := p) γ = ExcSplitRootGen.excRefl (p := p) δ) :
    γ = δ ∨ γ = -δ := by
  refine hroot δ γ hδ hγ fun t ht => ?_
  rw [← hfixset γ hγ t, h]
  exact (hfixset δ hδ t).2 ht

theorem map_conj_phiTwoComp
    {τ : Tag} {K : Type} [Field K]
    {g0 : ModGL τ (AlgebraicClosure K)} {v : WeylGroup τ}
    {n : adjointGroup τ K}
    (hn : baseChangeGL (algebraMap K (AlgebraicClosure K)) ((n : adjointGroup τ K) : ModGL τ K) =
      g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) v * g0⁻¹)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    (phiTwoComp g0 γ).map (MulAut.conj n).toMonoidHom = phiTwoComp g0 (v • γ) := by
  ext x
  rw [Subgroup.mem_map_equiv, mem_phiTwoComp_iff, mem_phiTwoComp_iff]
  have hmap : (rootSpan τ (AlgebraicClosure K) {γ, -γ}).map
      (MulAut.conj (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) v)).toMonoidHom =
      rootSpan τ (AlgebraicClosure K) {v • γ, -(v • γ)} := by
    rw [← CFSG.HardMathSupport.Timmesfeld.LangTorus.rootRankOneGroup_eq_rootSpan_pair hγ,
      ← CFSG.HardMathSupport.Timmesfeld.LangTorus.rootRankOneGroup_eq_rootSpan_pair
        (IsRoot.smul hγ v)]
    exact CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.map_range_rootSL2_canonicalRep v hγ
  have hkey : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (((MulAut.conj n).symm x : adjointGroup τ K) : ModGL τ K) * g0 =
      (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) v)⁻¹ *
        (g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) * g0) *
        canonicalRep (coxeterSystem τ) (AlgebraicClosure K) v := by
    rw [MulAut.conj_symm_apply]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
    rw [hn]
    group
  rw [hkey, ← hmap, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem iSup_phiTwoComp_eq_top
    {τ : Tag} {K : Type} [Field K]
    (hGen : PhiTwoGenAt τ) [Finite K]
    [CharP K 2] (hK4 : 4 ≤ Nat.card K) {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (_hrat : ∀ X : Subgroup (ModGL τ (AlgebraicClosure K)), Finite X →
      X ≤ adjointGroup τ (AlgebraicClosure K) → (∀ x ∈ X, Units.map (entrywiseHom Fr) x = x) →
        X ≤ (adjointGroup τ K).map (baseChangeGL (algebraMap K (AlgebraicClosure K))))
    {w : WeylGroup τ} (_hcent : ∀ v : WeylGroup τ, v * w = w * v)
    (hneg : ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → w • γ = -γ)
    {g0 : ModGL τ (AlgebraicClosure K)} (hg0C : g0 ∈ adjointGroup τ (AlgebraicClosure K))
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w) :
    (⨆ γ : {γ : Fin τ.rank → ℤ // IsRoot τ γ}, phiTwoComp g0 γ.1) = ⊤ := by
  have hlong : ExcIsLongest τ w := excIsLongest_of_smul_eq_neg hneg
  exact hGen K hK4 w Fr g0 hlong hFr hg0C hg0

theorem exists_isRoot_smul_ne
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {δ : Fin τ.rank → ℤ} (hδ : IsRoot τ δ) :
    ∃ ε : Fin τ.rank → ℤ, IsRoot τ ε ∧ ε ≠ δ ∧ ε ≠ -δ ∧ rootReflection ε • δ ≠ δ ∧
      rootReflection ε • δ ≠ -δ := by
  obtain ⟨u, i, rfl⟩ := isRoot_iff_exists_smul_single.1 hδ
  let δ : Fin τ.rank → ℤ := u • (Pi.single i (1 : ℤ) : Fin τ.rank → ℤ)
  change ∃ ε : Fin τ.rank → ℤ, IsRoot τ ε ∧ ε ≠ δ ∧ ε ≠ -δ ∧
    rootReflection ε • δ ≠ δ ∧ rootReflection ε • δ ≠ -δ
  obtain ⟨j, hcart⟩ := exists_cartan_eq_neg_one hτ i
  have hdiag : τ.cartan i i = 2 := Tag.cartan_self τ i
  have hji : j ≠ i := by
    rintro rfl
    rw [hdiag] at hcart
    norm_num at hcart
  let ε : Fin τ.rank → ℤ := u • (Pi.single j (1 : ℤ) : Fin τ.rank → ℤ)
  have hε : IsRoot τ ε := by
    dsimp [ε]
    exact IsRoot.smul (isRoot_single τ j) u
  have hifδδ : iform δ δ = 2 := by
    dsimp [δ]
    rw [iform_smul_free_E hτ, iform_single_self_E hτ]
  have hifεε : iform ε ε = 2 := by
    dsimp [ε]
    rw [iform_smul_free_E hτ, iform_single_self_E hτ]
  have hife : iform δ ε = -1 := by
    dsimp [δ, ε]
    rw [iform_smul_free_E hτ, iform_single_eq_neg_one hτ hji.symm hcart]
  have hifεδ : iform ε δ = -1 := by
    rw [iform_comm_E hτ]
    exact hife
  have hεneδ : ε ≠ δ := by
    intro h
    have h' : iform δ δ = -1 := by
      have := hife
      rwa [h] at this
    rw [hifδδ] at h'
    norm_num at h'
  have hnegδ : iform δ (-δ) = -iform δ δ := by
    rw [show -δ = (-1 : ℤ) • δ from by simp, iform_smul_right_E hτ, neg_one_mul]
  have hεnenδ : ε ≠ -δ := by
    intro h
    have h' : iform δ (-δ) = -1 := by
      have := hife
      rwa [h] at this
    rw [hnegδ, hifδδ] at h'
    norm_num at h'
  have hcontr : rootReflection ε • δ = δ + ε := by
    have h1 := rootReflection_smul_E hτ hε δ
    have h2 : corootPair ε δ = -1 := by
      rw [corootPair, hifεδ, hifεε]
      norm_num
    rw [h1, h2]
    simp
  refine ⟨ε, hε, hεneδ, hεnenδ, ?_, ?_⟩
  · rw [hcontr]
    intro h
    have hε0 : ε = 0 := by
      have h' : δ + ε = δ + 0 := by simpa using h
      exact add_left_cancel h'
    have hzero : (2 : ℤ) = 0 := by
      rw [← hifεε, hε0]
      simp [iform]
    norm_num at hzero
  · rw [hcontr]
    intro h
    have hεeq : ε = (-2 : ℤ) • δ := by
      rw [eq_neg_add_of_add_eq h]
      simp only [neg_smul, two_smul, neg_add]
    have h8 : iform ε ε = 8 := by
      rw [hεeq, iform_smul_left_free, iform_smul_right_E hτ, hifδδ]
      norm_num
    rw [h8] at hifεε
    norm_num at hifεε

theorem iSup_phiTwoComp_ne
    {τ : Tag} {K : Type} [Field K] {p : ℕ}
    (hGen : PhiTwoGenAt τ) (hτ : τ = .E7 ∨ τ = .E8) [Finite K]
    [CharP K 2] (hK4 : 4 ≤ Nat.card K) {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (hrat : ∀ X : Subgroup (ModGL τ (AlgebraicClosure K)), Finite X →
      X ≤ adjointGroup τ (AlgebraicClosure K) → (∀ x ∈ X, Units.map (entrywiseHom Fr) x = x) →
        X ≤ (adjointGroup τ K).map (baseChangeGL (algebraMap K (AlgebraicClosure K))))
    {w : WeylGroup τ} (hcent : ∀ v : WeylGroup τ, v * w = w * v)
    (hneg : ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → w • γ = -γ)
    {g0 : ModGL τ (AlgebraicClosure K)} (hg0C : g0 ∈ adjointGroup τ (AlgebraicClosure K))
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
    (hfixset : ∀ α : Fin τ.rank → ℤ, IsRoot τ α →
      ∀ t, ExcSplitRootGen.excRefl (p := p) α t = t ↔ ∑ j, (α j : ZMod p) * t j = 0)
    (hroot : ∀ α β, IsRoot τ α → IsRoot τ β → (∀ t : Fin τ.rank → ZMod p,
      ∑ j, (α j : ZMod p) * t j = 0 → ∑ j, (β j : ZMod p) * t j = 0) → β = α ∨ β = -α)
    (j : {α : Fin τ.rank → ℤ // IsRoot τ α}) :
    (⨆ (i : {α : Fin τ.rank → ℤ // IsRoot τ α})
        (_ : ExcSplitRootGen.excRefl (p := p) i.1 ≠ ExcSplitRootGen.excRefl j.1),
      phiTwoComp g0 i.1) = ⊤ := by
  let M : Subgroup (adjointGroup τ K) :=
    ⨆ γ : {γ : Fin τ.rank → ℤ // IsRoot τ γ}, phiTwoComp g0 γ.1
  let Mj : Subgroup (adjointGroup τ K) :=
    ⨆ (i : {α : Fin τ.rank → ℤ // IsRoot τ α})
      (_ : ExcSplitRootGen.excRefl (p := p) i.1 ≠ ExcSplitRootGen.excRefl (p := p) j.1),
      phiTwoComp g0 i.1
  have hM : M = ⊤ := by
    dsimp [M]
    exact iSup_phiTwoComp_eq_top hGen hK4 hFr hrat hcent hneg hg0C hg0
  have hJδ : phiTwoComp g0 j.1 ≤ Mj := by
    obtain ⟨ε, hεroot, hεneδ, hεnenδ, hrεδ_ne, hrεδ_ne_neg⟩ :=
      exists_isRoot_smul_ne (Or.inr hτ) j.2
    have hδ'root : IsRoot τ (rootReflection ε • j.1) :=
      IsRoot.smul j.2 (rootReflection ε)
    have hεexc : ExcSplitRootGen.excRefl (p := p) ε ≠
        ExcSplitRootGen.excRefl (p := p) j.1 := by
      intro h
      rcases eq_or_eq_neg_of_excRefl_eq hεroot j.2 hfixset hroot h with h' | h'
      exacts [hεneδ h', hεnenδ h']
    have hδ'exc : ExcSplitRootGen.excRefl (p := p) (rootReflection ε • j.1) ≠
        ExcSplitRootGen.excRefl (p := p) j.1 := by
      intro h
      rcases eq_or_eq_neg_of_excRefl_eq hδ'root j.2 hfixset hroot h with h' | h'
      exacts [hrεδ_ne h', hrεδ_ne_neg h']
    have hJε : phiTwoComp g0 ε ≤ Mj := le_iSup₂_of_le ⟨ε, hεroot⟩ hεexc le_rfl
    have hJδ' : phiTwoComp g0 (rootReflection ε • j.1) ≤ Mj :=
      le_iSup₂_of_le ⟨rootReflection ε • j.1, hδ'root⟩ hδ'exc le_rfl
    obtain ⟨n, hnmem, hnbase⟩ := exists_phiTwoWeyl hrat hcent hg0C hg0 hεroot
    have hmap := map_conj_phiTwoComp (g0 := g0) (v := rootReflection ε) (n := n)
      hnbase hδ'root
    have hsmul : rootReflection ε • (rootReflection ε • j.1) = j.1 := by
      rw [← mul_smul, rootReflection_mul_self hεroot, one_smul]
    rw [hsmul] at hmap
    rw [← hmap]
    rintro x ⟨y, hy, rfl⟩
    change (MulAut.conj n) y ∈ Mj
    simpa only [MulAut.conj_apply] using
      Mj.mul_mem (Mj.mul_mem (hJε hnmem) (hJδ' hy)) (Mj.inv_mem (hJε hnmem))
  have hMle : M ≤ Mj := by
    dsimp [M, Mj]
    refine iSup_le fun γ => ?_
    by_cases hsame : ExcSplitRootGen.excRefl (p := p) γ.1 =
        ExcSplitRootGen.excRefl (p := p) j.1
    · have hpm := eq_or_eq_neg_of_excRefl_eq γ.2 j.2 hfixset hroot hsame
      have hJeq : phiTwoComp g0 γ.1 = phiTwoComp g0 j.1 := by
        rcases hpm with hEq | hEq
        · rw [hEq]
        · rw [hEq, phiTwoComp_neg]
      rw [hJeq]
      exact hJδ
    · exact le_iSup₂_of_le γ hsame le_rfl
  have htop : ⊤ ≤ Mj := by
    rw [← hM]
    exact hMle
  exact top_le_iff.mp htop

end CFSG.StandardType.PhiTwoRootGen

end
