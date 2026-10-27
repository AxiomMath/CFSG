module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNIRestr
public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNISpSemilin
public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNISpFixedCoord
public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNISpPairCoord
public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNISpSelfDualCoord
public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNISpBlockMark
public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNISpUnitaryMark
import CFSG.LocalAnalysis.StandardType.GGNbrLangFNIOrthogonalBlocks
import CFSG.LocalAnalysis.StandardType.GGClassicalBlockSpDecomp
import CFSG.LocalAnalysis.StandardType.GGCentInnerDiagBlocks
import CFSG.LocalAnalysis.StandardType.TableC.POmegaBlockDeg
import CFSG.GroupTheory.IsComponentOfMap

public section

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.Open (StatedSp)
open CFSG.StandardType.ClassicalPosition CFSG.StandardType.ClassicalBlocks


theorem kgfniSp_fixedBlock_negMarking {K : Type} [Field K] [Fintype K] [CharP K 2] {n : ℕ}
    (u : GL (Fin n ⊕ Fin n) K) (hu : u ∈ StatedSp n K) (hodd : Odd (orderOf u))
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    (hε : IsPrimAdjIdemIn (RingHom.id K)
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
      (Algebra.adjoin K (Units.val '' ({u} : Set (GL (Fin n ⊕ Fin n) K)))) ε)
    (h1 : (u : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε = ε)
    {σ : K ≃+* K} (hσ : σ ≠ 1) (hσu : Matrix.GeneralLinearGroup.map (σ : K →+* K) u = u)
    {C : Subgroup ↥(StatedSp n K)}
    (hC : IsComponentOf C (glBlockCentralizer (StatedSp n K).subtype {u} ε))
    {X : Type} [Group X] (θ : X ≃* ↥C) (fX : MulAut X) (fC : MulAut ↥C)
    (hθ : ∀ x : X, θ (fX x) = fC (θ x))
    (hsq : ∀ c : ↥C, ((fC c : StatedSp n K) : GL (Fin n ⊕ Fin n) K) =
      Matrix.GeneralLinearGroup.map (σ : K →+* K) ((c : StatedSp n K) : GL (Fin n ⊕ Fin n) K)) :
    GGMarkingAll (K := X) fun _ _ _ I _ θ' => kgInducedAut θ' fX ∉ I := by
  obtain ⟨n₁, eG, B, hB, hsqG⟩ := kgfniSp_fixedBlock_coord u hu hodd hε h1 hσu
  exact kgfniSp_spBlock_negMarking_congr eG hC θ fX fC hθ B hB σ hσ
    (fun c => hsqG ⟨c, hC.1 c.2⟩ ⟨fC c, hC.1 (fC c).2⟩ (hsq c))

theorem kgfniSp_pairBlock_negMarking {K : Type} [Field K] [Fintype K] [CharP K 2] {n p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (u : GL (Fin n ⊕ Fin n) K) (hu : u ∈ StatedSp n K) (hodd : Odd (orderOf u))
    (hup : u ^ p = 1)
    {ε e e' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    (hε : IsPrimAdjIdemIn (RingHom.id K)
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
      (Algebra.adjoin K (Units.val '' ({u} : Set (GL (Fin n ⊕ Fin n) K)))) ε)
    (he : IsPrimIdemIn (Algebra.adjoin K (Units.val '' ({u} : Set (GL (Fin n ⊕ Fin n) K)))) e)
    (he' : IsPrimIdemIn (Algebra.adjoin K (Units.val '' ({u} : Set (GL (Fin n ⊕ Fin n) K)))) e')
    (hne : e ≠ e') (hεe : ε = e + e')
    {σ : K ≃+* K} (hσ : σ ≠ 1) (hσp : σ ^ p = 1)
    (hσu : Matrix.GeneralLinearGroup.map (σ : K →+* K) u = u)
    {C : Subgroup ↥(StatedSp n K)}
    (hC : IsComponentOf C (glBlockCentralizer (StatedSp n K).subtype {u} ε))
    {X : Type} [Group X] (θ : X ≃* ↥C) (fX : MulAut X) (fC : MulAut ↥C)
    (hθ : ∀ x : X, θ (fX x) = fC (θ x))
    (hsq : ∀ c : ↥C, ((fC c : StatedSp n K) : GL (Fin n ⊕ Fin n) K) =
      Matrix.GeneralLinearGroup.map (σ : K →+* K) ((c : StatedSp n K) : GL (Fin n ⊕ Fin n) K)) :
    GGMarkingAll (K := X) fun _ _ _ I _ θ' => kgInducedAut θ' fX ∉ I := by
  obtain ⟨m, E, _, _, _, eG, B, τ, hτ, hsqG⟩ :=
    kgfniSp_pairBlock_coord hp hp2 u hu hodd hup hε he he' hne hεe hσ hσp hσu
  exact ClassicalBlocks.kgFieldRestriction_linearBlock_of_semilinear_congr eG hC θ fX fC hθ B τ hτ
    (fun c => hsqG ⟨c, hC.1 c.2⟩ ⟨fC c, hC.1 (fC c).2⟩ (hsq c))

theorem kgfniSp_selfDualBlock_negMarking {K : Type} [Field K] [Fintype K] [CharP K 2] {n p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (u : GL (Fin n ⊕ Fin n) K) (hu : u ∈ StatedSp n K) (hodd : Odd (orderOf u))
    (hup : u ^ p = 1)
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    (hε : IsPrimAdjIdemIn (RingHom.id K)
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
      (Algebra.adjoin K (Units.val '' ({u} : Set (GL (Fin n ⊕ Fin n) K)))) ε)
    (heprim : IsPrimIdemIn (Algebra.adjoin K
      (Units.val '' ({u} : Set (GL (Fin n ⊕ Fin n) K)))) ε)
    (h1 : (u : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε ≠ ε)
    {σ : K ≃+* K} (hσ : σ ≠ 1) (hσp : σ ^ p = 1)
    (hσu : Matrix.GeneralLinearGroup.map (σ : K →+* K) u = u)
    {C : Subgroup ↥(StatedSp n K)}
    (hC : IsComponentOf C (glBlockCentralizer (StatedSp n K).subtype {u} ε))
    {X : Type} [Group X] (θ : X ≃* ↥C) (fX : MulAut X) (fC : MulAut ↥C)
    (hθ : ∀ x : X, θ (fX x) = fC (θ x))
    (hsq : ∀ c : ↥C, ((fC c : StatedSp n K) : GL (Fin n ⊕ Fin n) K) =
      Matrix.GeneralLinearGroup.map (σ : K →+* K) ((c : StatedSp n K) : GL (Fin n ⊕ Fin n) K)) :
    GGMarkingAll (K := X) fun _ _ _ I _ θ' => kgInducedAut θ' fX ∉ I := by
  obtain ⟨m, Q, E, _, _, _, hE, eG, B, τ, hB, hτ, hτodd, hsqG⟩ :=
    kgfniSp_selfDualBlock_coord hp hp2 u hu hodd hup hε heprim h1 hσ hσp hσu
  exact kgfniSp_unitaryBlock_negMarking_congr hE eG hC θ fX fC hθ B hB τ hτ hτodd
    (fun c => hsqG ⟨c, hC.1 c.2⟩ ⟨fC c, hC.1 (fC c).2⟩ (hsq c))

theorem kgfniSp_block_negMarking {K : Type} [Field K] [Fintype K] [CharP K 2] {n p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (u : GL (Fin n ⊕ Fin n) K) (hu : u ∈ StatedSp n K) (hodd : Odd (orderOf u))
    (hup : u ^ p = 1)
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    (hε : IsPrimAdjIdemIn (RingHom.id K)
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
      (Algebra.adjoin K (Units.val '' ({u} : Set (GL (Fin n ⊕ Fin n) K)))) ε)
    {σ : K ≃+* K} (hσ : σ ≠ 1) (hσp : σ ^ p = 1)
    (hσu : Matrix.GeneralLinearGroup.map (σ : K →+* K) u = u)
    {C : Subgroup ↥(StatedSp n K)}
    (hC : IsComponentOf C (glBlockCentralizer (StatedSp n K).subtype {u} ε))
    {X : Type} [Group X] (θ : X ≃* ↥C) (fX : MulAut X) (fC : MulAut ↥C)
    (hθ : ∀ x : X, θ (fX x) = fC (θ x))
    (hsq : ∀ c : ↥C, ((fC c : StatedSp n K) : GL (Fin n ⊕ Fin n) K) =
      Matrix.GeneralLinearGroup.map (σ : K →+* K) ((c : StatedSp n K) : GL (Fin n ⊕ Fin n) K)) :
    GGMarkingAll (K := X) fun _ _ _ I _ θ' => kgInducedAut θ' fX ∉ I := by
  classical
  have hneg : (-1 : Matrix (Fin n) (Fin n) K) = 1 := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h, CharTwo.neg_eq]
  have hG : IsUnit (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K).det := by
    have hJ : (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
        Matrix.J (Fin n) K := by
      rw [Matrix.J, Matrix.fromBlocks_inj]
      exact ⟨rfl, hneg.symm, hneg, rfl⟩
    rw [hJ]
    exact Matrix.isUnit_det_J (Fin n) K
  have hGt : Matrix.transpose (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = Matrix.fromBlocks 0 1 (-1) 0 := by
    rw [Matrix.fromBlocks_transpose, Matrix.transpose_zero, Matrix.transpose_one,
      Matrix.transpose_neg (1 : Matrix (Fin n) (Fin n) K), Matrix.transpose_one,
      Matrix.fromBlocks_inj]
    exact ⟨rfl, hneg, hneg.symm, rfl⟩
  have hS : ∀ s ∈ ({u} : Set (GL (Fin n ⊕ Fin n) K)),
      ∀ s' ∈ ({u} : Set (GL (Fin n ⊕ Fin n) K)), Commute s s' := by
    intro s hs s' hs'
    rw [Set.mem_singleton_iff] at hs hs'
    rw [hs, hs']
  have hSU : ∀ s ∈ ({u} : Set (GL (Fin n ⊕ Fin n) K)),
      Matrix.transpose (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *
        (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = Matrix.fromBlocks 0 1 (-1) 0 := by
    intro s hs
    rw [Set.mem_singleton_iff] at hs
    subst hs
    exact CFSG.Open.StatedAPI.mem_statedSp_iff.mp hu
  have hSUmap : ∀ s ∈ ({u} : Set (GL (Fin n ⊕ Fin n) K)),
      Matrix.transpose ((s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K).map (RingHom.id K)) *
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *
        (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = Matrix.fromBlocks 0 1 (-1) 0 := by
    intro s hs
    simpa [Matrix.map_id] using hSU s hs
  obtain ⟨e, he, heε, -⟩ := exists_isPrimIdemIn_of_isPrimAdjIdemIn (RingHom.id K)
    (fun _ => rfl) hG (by simpa [Matrix.map_id] using hGt) hS hSUmap hε
  rcases TableC.isPrimIdemIn_cases hG hGt hS hSU hε he heε with heq | ⟨-, e', he', hne', hεe⟩
  · have heprim : IsPrimIdemIn (Algebra.adjoin K
        (Units.val '' ({u} : Set (GL (Fin n ⊕ Fin n) K)))) ε := heq ▸ he
    by_cases h1 : (u : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * ε = ε
    · exact kgfniSp_fixedBlock_negMarking u hu hodd hε h1 hσ hσu hC θ fX fC hθ hsq
    · exact kgfniSp_selfDualBlock_negMarking hp hp2 u hu hodd hup hε heprim h1 hσ hσp hσu hC
        θ fX fC hθ hsq
  · exact kgfniSp_pairBlock_negMarking hp hp2 u hu hodd hup hε he he' hne' hεe hσ hσp hσu hC
      θ fX fC hθ hsq

theorem kgFieldRestrictionCont_symplectic {K : Type} [Field K] [Finite K] [CharP K 2]
    {r p : ℕ} [NeZero r] (hp : p.Prime) (hp2 : p ≠ 2) :
    KGFieldRestrictionCont p (LargeEvenProj (LargeEvenSpGroup K r))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K r)) (LargeEvenGSpSet K r))
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSpGroup K r))) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  intro f hf hord h hh hhp hcomm J₀ hJ₀ f' hf'
  obtain ⟨σ, u, hσ1, hσp, hup, hσu, hhu, hfσ⟩ :=
    RecipeFieldSp.exists_semilinear_representatives hp hf hord hh hhp hcomm
  generalize (TableBSymp.spProjEquivSp :
    LargeEvenProj (LargeEvenSpGroup K r) ≃* ↥(LargeEvenSpGroup K r)) = e at hhu hfσ
  have hJ₁ : IsComponentOf (J₀.map e.toMonoidHom)
      ((Subgroup.centralizer {(u : GL (Fin r ⊕ Fin r) K)}).comap (StatedSp r K).subtype) := by
    have hmap := isComponentOf_iff_open.mpr
      (CFSG.isComponentOf_map_mulEquiv e (isComponentOf_iff_open.mp hJ₀))
    convert hmap using 1
    ext y
    rw [Subgroup.mem_map, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hy
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      change h (e.symm y) = e.symm y
      apply e.injective
      rw [hhu, e.apply_symm_apply]
      apply Subtype.ext
      have hy' : (y : GL (Fin r ⊕ Fin r) K) * (u : GL (Fin r ⊕ Fin r) K) =
          (u : GL (Fin r ⊕ Fin r) K) * (y : GL (Fin r ⊕ Fin r) K) := hy
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← hy', mul_inv_cancel_right]
    · rintro ⟨x, hx, rfl⟩
      have hx' : h x = x := hx
      have hux := hhu x
      rw [hx'] at hux
      have hcoe := congrArg (fun z : ↥(LargeEvenSpGroup K r) =>
        (z : GL (Fin r ⊕ Fin r) K) * (u : GL (Fin r ⊕ Fin r) K)) hux
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_cancel_right] at hcoe
      exact hcoe
  have hodd : Odd (orderOf (u : GL (Fin r ⊕ Fin r) K)) := by
    rw [Subgroup.orderOf_coe]
    exact Odd.of_dvd_nat (hp.odd_of_ne_two hp2) (orderOf_dvd_of_pow_eq_one hup)
  have hupGL : (u : GL (Fin r ⊕ Fin r) K) ^ p = 1 := by
    rw [← Subgroup.coe_pow, hup, Subgroup.coe_one]
  obtain ⟨P, hP, -, -, hc, hsup, -⟩ :=
    centralizer_block_decomp_Sp (u : GL (Fin r ⊕ Fin r) K) u.2 hodd
  rw [← hsup] at hJ₁
  obtain ⟨ε, hε, hJ₁ε⟩ := exists_isComponentOf_block P _ hc hJ₁
  let θ : ↥J₀ ≃* ↥(J₀.map e.toMonoidHom) :=
    Subgroup.equivMapOfInjective J₀ e.toMonoidHom e.injective
  have hθe : ∀ j : ↥J₀, ((θ j : ↥(J₀.map e.toMonoidHom)) : ↥(LargeEvenSpGroup K r)) =
      e (j : LargeEvenProj (LargeEvenSpGroup K r)) :=
    fun j => Subgroup.coe_equivMapOfInjective_apply J₀ e.toMonoidHom e.injective j
  let fC : MulAut ↥(J₀.map e.toMonoidHom) := θ.symm.trans (f'.trans θ)
  have hθ : ∀ x : ↥J₀, θ (f' x) = fC (θ x) := by
    intro x
    simp only [fC, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  have hsq : ∀ c : ↥(J₀.map e.toMonoidHom),
      ((fC c : StatedSp r K) : GL (Fin r ⊕ Fin r) K) =
        Matrix.GeneralLinearGroup.map (σ : K →+* K)
          ((c : StatedSp r K) : GL (Fin r ⊕ Fin r) K) := by
    intro c
    have hc : e ((θ.symm c : ↥J₀) : LargeEvenProj (LargeEvenSpGroup K r)) =
        (c : ↥(LargeEvenSpGroup K r)) := by
      rw [← hθe, MulEquiv.apply_symm_apply]
    have hfc : ((fC c : ↥(J₀.map e.toMonoidHom)) : ↥(LargeEvenSpGroup K r)) =
        e (f ((θ.symm c : ↥J₀) : LargeEvenProj (LargeEvenSpGroup K r))) := by
      show ((θ (f' (θ.symm c)) : ↥(J₀.map e.toMonoidHom)) : ↥(LargeEvenSpGroup K r)) = _
      rw [hθe, hf']
    rw [hfc, hfσ, hc]
  exact kgfniSp_block_negMarking hp hp2 (u : GL (Fin r ⊕ Fin r) K) u.2 hodd hupGL (hP ε hε)
    hσ1 hσp hσu hJ₁ε θ f' fC hθ hsq

theorem kgFieldRestrictionOn_symplectic : KGFieldRestrictionOn (kgfniRow .symplectic) := by
  intro p lab hp hp2 hlab _ht3 hrow
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, -⟩ := hrow
  change t = .B ∨ t = .C at htag
  have hl2 : 2 ≤ l := by
    rcases htag with rfl | rfl <;> exact hlab.2.1
  haveI : NeZero l := ⟨by omega⟩
  intro Q hQ
  rcases htag with rfl | rfl
  all_goals
    dsimp only [LargeEvenRawDatum, LargeEvenRecipeSymplectic] at hQ ⊢
    obtain ⟨K, i1, i2, hK, hq⟩ := hQ
    haveI : CharP K 2 := charP_two_of_card hK
    exact ⟨K, i1, i2, hK, hq, kgFieldRestrictionCont_symplectic hp hp2⟩

end CFSG.StandardType
