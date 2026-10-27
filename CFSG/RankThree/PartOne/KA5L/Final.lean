module

public import CFSG.RankThree.PartOne.KA5L.Core
public import CFSG.RankThree.PartOne.KE.SLnDescended
public import CFSG.RankThree.PartOne.KA5L.Lift

public noncomputable section

namespace CFSG.RankThree.PartOne.KA5L

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.RankThree.PartOne.KE CFSG.RankThree.Classical CFSG.RankThree.Classical2
  CFSG.SectionRank.OddCover CFSG.ClassicalInvolution.WeakCT
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ClassicalInvolution.Phan (blockMat blockMat_apply)

open scoped MatrixGroups commutatorElement

section Field

variable {L : Type} [Field L] [IsAlgClosed L] {ℓ : ℕ} [Fact ℓ.Prime] [CharP L ℓ]

theorem exists_isAlgClosure_subfield {f : ℕ} (hf : 1 ≤ f)
    (hΩ : letI := ZMod.algebra L ℓ; Algebra.IsAlgebraic (ZMod ℓ) L) :
    ∃ (k : Type) (_ : Field k) (_ : Algebra k L), IsAlgClosure k L ∧ Nat.card k = ℓ ^ f := by
  let k : Subfield L := (iterateFrobenius L ℓ f).eqLocusField (RingHom.id L)
  have hmem : ∀ c : L, c ∈ k ↔ c ^ ℓ ^ f = c := fun c => by
    rw [RingHom.mem_eqLocusField, iterateFrobenius_def, RingHom.id_apply]
  have hcard : Nat.card k = ℓ ^ f := by
    rw [← natCard_setOf_pow_eq_self (Ω := L) (ℓ := ℓ) (e := f) (by omega)]
    exact Nat.card_congr (Equiv.subtypeEquivRight hmem)
  refine ⟨k, inferInstance, inferInstance, ?_, hcard⟩
  let _ : Algebra (ZMod ℓ) L := ZMod.algebra L ℓ
  have : CharP k ℓ := RingHom.charP (algebraMap k L) (algebraMap k L).injective ℓ
  have hAlg : Algebra.IsAlgebraic k L := by
    refine ⟨fun x => ?_⟩
    obtain ⟨p, hp0, hpx⟩ := hΩ.isAlgebraic x
    let φ : ZMod ℓ →+* k := ZMod.castHom (dvd_refl ℓ) k
    refine ⟨p.map φ, (Polynomial.map_ne_zero_iff φ.injective).2 hp0, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map,
      show (algebraMap k L).comp φ = algebraMap (ZMod ℓ) L from RingHom.ext_zmod _ _]
    rwa [Polynomial.aeval_def] at hpx
  exact ⟨inferInstance, hAlg⟩

end Field

section Block

variable {L : Type} [Field L]

theorem flag_blockSL_eq (B : SL(2, L)) :
    LinearFlag.blockSL L 2 4 B = blockSL2 L 5 0 B := by
  apply Subtype.ext
  rw [LinearFlag.coe_blockSL, LinearFlag.coe_blockGL_eq_diagBlock, blockSL2, coe_blockSL]
  ext a b
  rw [LinearFlag.diagBlock, Matrix.reindex_apply, Matrix.submatrix_apply, blockMat_apply]
  refine Fin.addCases (fun x => ?_) (fun y => ?_) a <;>
    refine Fin.addCases (fun x' => ?_) (fun y' => ?_) b
  · have := x.isLt
    have := x'.isLt
    rw [finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_castAdd,
      Matrix.fromBlocks_apply₁₁, dite_eq_left (by simp [Fin.val_castAdd]; omega)]
    rfl
  · have := x.isLt
    have := y'.isLt
    rw [finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
      Matrix.fromBlocks_apply₁₂, dite_eq_right (by simp [Fin.val_natAdd]; omega)]
    simp [Matrix.one_apply, Fin.ext_iff]
    omega
  · have := y.isLt
    have := x'.isLt
    rw [finSumFinEquiv_symm_apply_natAdd, finSumFinEquiv_symm_apply_castAdd,
      Matrix.fromBlocks_apply₂₁, dite_eq_right (by simp [Fin.val_natAdd]; omega)]
    simp [Matrix.one_apply, Fin.ext_iff]
    omega
  · have := y.isLt
    have := y'.isLt
    rw [finSumFinEquiv_symm_apply_natAdd, finSumFinEquiv_symm_apply_natAdd,
      Matrix.fromBlocks_apply₂₂, dite_eq_right (by simp [Fin.val_natAdd]; omega)]
    simp [Matrix.one_apply, Fin.ext_iff]

@[expose] def cyc : Equiv.Perm (Fin 6) := Equiv.swap 0 1 * Equiv.swap 1 2

theorem sign_cyc : Equiv.Perm.sign cyc = 1 := by decide

theorem det_permGL_cyc : ((permGL cyc : GL (Fin 6) L) : Matrix (Fin 6) (Fin 6) L).det = 1 := by
  rw [MonoidHom.coe_toHomUnits, Matrix.permMatrixHom_apply, Matrix.det_permutation,
    Equiv.Perm.sign_inv, sign_cyc]
  simp

@[expose] def shiftSL : SL(6, L) := ⟨(permGL cyc : GL (Fin 6) L), det_permGL_cyc⟩

theorem toGL_shiftSL : Matrix.SpecialLinearGroup.toGL (shiftSL : SL(6, L)) = permGL cyc :=
  Units.ext rfl

theorem conjSLn_toGL {n : ℕ} (S X : SL(n, L)) :
    conjSLn (Matrix.SpecialLinearGroup.toGL S) X = S * X * S⁻¹ := by
  apply Subtype.ext
  rw [coe_conjSLn, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    ← Matrix.SpecialLinearGroup.coe_GL_coe_matrix, ← map_inv,
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
  rfl

theorem transvection_congr {n : ℕ} {i j i' j' : Fin n} (hij : i ≠ j) (hij' : i' ≠ j')
    (hi : i = i') (hj : j = j') (t : L) :
    Matrix.SpecialLinearGroup.transvection hij t =
      Matrix.SpecialLinearGroup.transvection hij' t := by
  subst hi
  subst hj
  rfl

theorem blockSL2_one_eq (A : SL(2, L)) :
    blockSL2 L 5 1 A = shiftSL * blockSL2 L 5 0 A * shiftSL⁻¹ := by
  have h : blockSL2 L 5 1 = (conjSLn (permGL cyc : GL (Fin 6) L)).comp (blockSL2 L 5 0) := by
    refine MonoidHom.eq_of_eqOn_dense CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower ?_
    rintro _ (⟨t, rfl⟩ | ⟨t, rfl⟩)
    · rw [MonoidHom.comp_apply, show sl2Upper L t = uSL t from rfl, blockSL2_uSL, blockSL2_uSL,
        conjSLn_perm_transvection]
      exact transvection_congr _ _ (by decide) (by decide) t
    · rw [MonoidHom.comp_apply, show sl2Lower L t = vSL t from rfl, blockSL2_vSL, blockSL2_vSL,
        conjSLn_perm_transvection]
      exact transvection_congr _ _ (by decide) (by decide) t
  rw [DFunLike.congr_fun h A, MonoidHom.comp_apply, ← toGL_shiftSL, conjSLn_toGL]

theorem exists_conj_simpleRootSL2_mem (Φ' : SL(6, L) ≃* SL(6, L)) {k : Type} [Field k]
    [Algebra k L] (J : SL(6, L))
    (hJ : ∀ Y : SL(2, k), J * LinearFlag.blockSL L 2 4
      (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) * J⁻¹ ∈ fixSubgroup Φ')
    (m : Fin Tag.E7.rank) (hm : m.val = 3) :
    ∃ h₀ : ModGL Tag.E7 L, ∀ Y : SL(2, k),
      h₀ * simpleRootSL2 Tag.E7 L m (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) * h₀⁻¹ ∈
        (fixSubgroup Φ').map (a5Frame L) := by
  have hmc : m = a5chain 1 := Fin.ext (by
    rw [hm]
    rfl)
  refine ⟨a5Frame L (J * shiftSL⁻¹), fun Y => ?_⟩
  set B := Matrix.SpecialLinearGroup.map (algebraMap k L) Y with hB
  refine ⟨J * LinearFlag.blockSL L 2 4 B * J⁻¹, hJ Y, ?_⟩
  have h1 : J * LinearFlag.blockSL L 2 4 B * J⁻¹ =
      (J * shiftSL⁻¹) * blockSL2 L 5 1 B * (J * shiftSL⁻¹)⁻¹ := by
    rw [flag_blockSL_eq, blockSL2_one_eq B]
    group
  rw [h1, map_mul, map_mul, map_inv, hmc, ← a5Frame_comp_blockSL2 L 1, MonoidHom.comp_apply]

end Block

theorem a5Layer_E7 : A5Layer .E7 := by
  intro L _ _ ℓ f _ _ hf hΩ ε hε _ n hn _ hact Γ P hΓ hP
  obtain ⟨k, _, _, hkc, hk⟩ := exists_isAlgClosure_subfield (L := L) (ℓ := ℓ) hf hΩ
  have hℓ : ℓ.Prime := Fact.out
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ ℓ ^ f := fun c => iterateFrobenius_def ℓ f c
  have hFrbij : Function.Bijective Fr := ⟨Fr.injective, fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y (pow_pos hℓ.pos f)
    exact ⟨x, by rw [hFr, hx]⟩⟩
  obtain ⟨u, hu, hu'⟩ := hact
  suffices key : ∃ Φ' : SL(6, L) ≃* SL(6, L),
      (∀ X, n * Units.map (entrywiseHom Fr) (a5Frame L X) * n⁻¹ = a5Frame L (Φ' X)) ∧
      Finite (fixSubgroup Φ') ∧ CFSG.IsQuasisimple (fixSubgroup Φ') ∧
      Subgroup.centralizer (((fixSubgroup Φ').map Matrix.SpecialLinearGroup.toGL :
        Subgroup (GL (Fin 6) L)) : Set (GL (Fin 6) L)) =
          (Matrix.GeneralLinearGroup.scalar (Fin 6)).range ∧
      (∀ (k : Type) [Field k] [Algebra k L] [IsAlgClosure k L], Nat.card k = ℓ ^ f →
        ∃ J : SL(6, L), ∀ Y : SL(2, k), J * LinearFlag.blockSL L 2 4
          (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) * J⁻¹ ∈ fixSubgroup Φ') by
    obtain ⟨Φ', hΦ', hfin, hq, hz, hJ⟩ := key
    rw [hP, hΓ, commutator_Gamma Fr n Φ' hΦ' hq]
    obtain ⟨hfin', hq'⟩ := finite_quasisimple_map Φ' hq
    refine ⟨hfin', hq', a5_commutant Φ' hq hz, fun m hm k' _ _ _ hk' => ?_⟩
    obtain ⟨J, hJ'⟩ := hJ k' hk'
    exact exists_conj_simpleRootSL2_mem Φ' J hJ' m hm
  rcases hε with rfl | rfl
  ·
    obtain ⟨π, hπ⟩ := exists_perm_of_mem_parabolicWeylGroup hu
    have hπ' : ∀ a b : Fin 6, a ≠ b → weylQuotientHom Tag.E7 L ⟨n, hn⟩ • a5Root a b =
        a5Root (π a) (π b) := fun a b hab => by
      rw [hu' _ (a5Root_mem_parabolicRoots hab), one_smul, hπ]
    obtain ⟨Φ', hΦ', b, hshape⟩ := exists_aut_split Fr hFrbij n hn π hπ'
    have hshape' : ∀ (i j : Fin 6) (hij : i ≠ j) (t : L),
        ((Φ' (Matrix.SpecialLinearGroup.transvection hij t) : SL(6, L)) :
          Matrix (Fin 6) (Fin 6) L) = 1 + single (π i) (π j) ((b i j : L) * t ^ ℓ ^ f) :=
      fun i j hij t => by rw [hshape i j hij t, hFr]
    obtain ⟨-, ⟨H, hH⟩, hfin, hq, -, -⟩ :=
      sln_root_permuting_frobenius_fixed_split hℓ hf hk (by norm_num : 3 ≤ 6) π Φ' b hshape'
    exact ⟨Φ', hΦ', hfin, hq, centralizer_fix_split_n Φ' H hH, fun k' _ _ _ hk' =>
      sln_fixed_contains_block_split hℓ hf hk' (m := 4) (by norm_num) π Φ' b hshape'⟩
  ·
    obtain ⟨π, hπ⟩ := exists_perm_neg_of_mem_parabolicWeylGroup hu
    have hπ' : ∀ a b : Fin 6, a ≠ b → weylQuotientHom Tag.E7 L ⟨n, hn⟩ • a5Root a b =
        a5Root (π b) (π a) := fun a b hab => by
      rw [hu' _ (a5Root_mem_parabolicRoots hab), neg_one_zsmul, hπ]
    obtain ⟨Φ', hΦ', b, hshape⟩ := exists_aut_unitary Fr hFrbij n hn π hπ'
    have hshape' : ∀ (i j : Fin 6) (hij : i ≠ j) (t : L),
        ((Φ' (Matrix.SpecialLinearGroup.transvection hij t) : SL(6, L)) :
          Matrix (Fin 6) (Fin 6) L) = 1 + single (π j) (π i) ((b i j : L) * t ^ ℓ ^ f) :=
      fun i j hij t => by rw [hshape i j hij t, hFr]
    have hne : ((6 : ℕ), ℓ ^ f) ≠ (3, 2) := fun h => absurd (congrArg Prod.fst h) (by norm_num)
    obtain ⟨-, ⟨H, hH⟩, hfin, hbig, -⟩ :=
      sln_root_permuting_frobenius_fixed_unitary hℓ hf hk (by norm_num : 3 ≤ 6) π Φ' b hshape'
    obtain ⟨hq, -, -⟩ := hbig hne
    have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; exact (pow_pos hℓ.pos f).ne')
    exact ⟨Φ', hΦ', hfin, hq, centralizer_fix_unitary_n hk (by norm_num : 3 ≤ 6) Φ' H hH,
      fun k' _ _ _ hk' =>
        sln_fixed_contains_block_unitary hℓ hf hk' (m := 4) (by norm_num) π Φ' b hshape'⟩

end CFSG.RankThree.PartOne.KA5L
