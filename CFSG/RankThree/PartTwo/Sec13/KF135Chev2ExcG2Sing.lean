module

public import CFSG.RankThree.Chevalley.SteinbergCEG2EvenQPlusTorus
import CFSG.ClassicalInvolution.ModelFacts.G2D4G2TorusGen
import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToral
import CFSG.RankThree.PartOne.KF.QuadExt

public section

namespace CFSG.RankThree.PartTwo.Sec13.KF135Chev2Exc

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.RankThree.QuadraticSL2
  CFSG.RankThree.Classical CFSG.RankThree.Chevalley CFSG.RankThree.Chevalley.EvenG2
  CFSG.RankThree.PartOne
open scoped Pointwise

@[expose] def transvSL (k : Type) [Field k] : Matrix.SpecialLinearGroup (Fin 2) k :=
  ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩

theorem transvSL_sq (k : Type) [Field k] [CharP k 2] : transvSL k ^ 2 = 1 := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_pow, sq]
  fin_cases i <;> fin_cases j <;>
    simp [transvSL, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]

theorem exists_singular_G2_qplus {k : Type} [Field k] [Finite k] [CharP k 2] {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hpk : p ∣ Nat.card k + 1)
    {A : Subgroup ↥(adjointGroup .G2 k)} (hA : CFSG.Open.IsElemAbelian p A)
    (hAc : Nat.card A = p ^ 2) :
    ∃ b ∈ A, b ≠ 1 ∧ ∃ w : ↥(adjointGroup .G2 k), w ≠ 1 ∧ w ^ 2 = 1 ∧ b * w = w * b := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, z, hg, hzC, hzdef, ⟨hzN, hw⟩, hΓ, hinv, -, -, ⟨S₀, hS₀T⟩,
      ⟨E, hEdef, hET, hEc, -, -⟩, hroots, -, hcent⟩ :=
    even_G2_qplus_torus_and_fixed_root_centralizers k hp hp3 hpk (KFQ.Qext k)
      KFQ.finrank_qext (KFQ.frobQ k).toRingEquiv fun c => KFQ.frobQ_apply c
  have hdeg : Module.finrank k (KFQ.Qext k) = 2 := KFQ.finrank_qext
  have : Module.Finite k (KFQ.Qext k) := Module.finite_of_finrank_pos (by omega)
  have : Finite (KFQ.Qext k) := Module.finite_of_finite k
  have : CharP (KFQ.Qext k) 2 :=
    charP_of_injective_algebraMap (algebraMap k (KFQ.Qext k)).injective 2
  set ψ : ModGL .G2 k →* ModGL .G2 (KFQ.Qext k) :=
    (MulAut.conj g).toMonoidHom.comp (baseChangeGL (algebraMap k (KFQ.Qext k))) with hψ
  have hψinj : Function.Injective ψ :=
    (MulAut.conj g).injective.comp (baseChangeGL_injective (τ := .G2) (algebraMap k (KFQ.Qext k)))
  let ε : adjointGroup .G2 k ≃* conjEntrywiseImage k g :=
    (adjointGroup .G2 k).equivMapOfInjective ψ hψinj
  have hA₁p : IsPGroup p (A.map ε.toMonoidHom) := by
    refine IsPGroup.of_card (n := 2) ?_
    rw [Subgroup.card_map_of_injective ε.injective, hAc]
  obtain ⟨Q', hQ'⟩ := hA₁p.exists_le_sylow
  obtain ⟨u, hu⟩ := MulAction.exists_smul_eq (conjEntrywiseImage k g) Q' S₀
  set F : adjointGroup .G2 k →* ModGL .G2 (KFQ.Qext k) := (conjEntrywiseImage k g).subtype.comp
    ((MulAut.conj u).toMonoidHom.comp ε.toMonoidHom) with hFdef
  have hF : Function.Injective F := (conjEntrywiseImage k g).subtype_injective.comp
    ((MulAut.conj u).injective.comp ε.injective)
  have hFrange : F.range = conjEntrywiseImage k g := by
    rw [hFdef, MonoidHom.range_comp, MonoidHom.range_eq_top_of_surjective _
      ((MulAut.conj u).surjective.comp ε.surjective), ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hFAE : A.map F ≤ E := by
    rintro _ ⟨a, ha, rfl⟩
    have hua : MulAut.conj u • ε a ∈ (S₀ : Subgroup (conjEntrywiseImage k g)) := by
      have h1 : MulAut.conj u • ε a ∈ MulAut.conj u • (Q' : Subgroup (conjEntrywiseImage k g)) :=
        Subgroup.smul_mem_pointwise_smul _ _ _ (hQ' (Subgroup.mem_map_of_mem _ ha))
      rwa [← Sylow.coe_subgroup_smul, hu] at h1
    have hFT : F a ∈ torusGroup .G2 (KFQ.Qext k) ⊓ conjEntrywiseImage k g :=
      Subgroup.mem_subgroupOf.1 (hS₀T hua)
    refine (hEdef _).mpr ⟨hFT.1, ?_⟩
    rw [← map_pow, hA.2 a ha, map_one]
  have hFA : A.map F = E := Subgroup.eq_of_le_of_card_ge hFAE (by
    rw [hEc, Subgroup.card_map_of_injective hF, hAc])
  have hq2 : Nat.card (KFQ.Qext k) = Nat.card k ^ 2 := natCard_eq_sq_of_finrank_eq_two hdeg
  have hq1 : 1 ≤ Nat.card k := Nat.card_pos
  have hpk₂ : p ∣ Nat.card (KFQ.Qext k) - 1 := by
    refine hpk.trans ⟨Nat.card k - 1, ?_⟩
    rw [hq2]
    zify [hq1, Nat.one_le_pow 2 _ hq1]
    ring
  obtain ⟨ζ, hζ⟩ := exists_units_orderOf_eq_of_dvd_card_sub_one (k := KFQ.Qext k) hp hpk₂
  set a : Fin Tag.G2.rank → (KFQ.Qext k)ˣ := ![1, ζ] with ha
  have hxT : rootDiagUnit .G2 a ∈ torusGroup .G2 (KFQ.Qext k) :=
    CFSG.ClassicalInvolution.G2D4Models.g2_rootDiagUnit_mem_torusGroup a
  have hap : a ^ p = 1 := by
    funext i
    rw [Pi.pow_apply, Pi.one_apply]
    fin_cases i
    · simp [ha]
    · rw [← hζ]
      exact pow_orderOf_eq_one ζ
  have hxp : rootDiagUnit .G2 a ^ p = 1 := by
    rw [← CFSG.HardMathSupport.Timmesfeld.CrossChar.rootDiagUnit_pow', hap, rootDiagUnit_one]
  have hx1 : rootDiagUnit .G2 a ≠ 1 := by
    intro h1
    rw [← rootDiagUnit_one] at h1
    have h2 := CFSG.HardMathSupport.Timmesfeld.CrossChar.rootDiagUnit_injective h1
    have h3 : ζ = 1 := by simpa [ha] using congrFun h2 1
    rw [h3, orderOf_one] at hζ
    exact hp.one_lt.ne hζ
  have hxo : orderOf (rootDiagUnit .G2 a) = p := orderOf_eq_prime hxp hx1
  have hxE : rootDiagUnit .G2 a ∈ E := (hEdef _).mpr ⟨hxT, hxp⟩
  have hker : rootCharKernel a ≠ ∅ := by
    rw [← Set.nonempty_iff_ne_empty]
    refine ⟨Pi.single 0 1, IsRoot.basis 0, Finset.prod_eq_one fun i _ => ?_⟩
    by_cases hi : i = 0
    · subst hi
      simp [ha]
    · simp [Pi.single_eq_of_ne hi]
  obtain ⟨β, hβ, -, hcomm, -⟩ := (hcent a (hET hxE) hxo).2.1 hker
  obtain ⟨Pβ, hPβ, -⟩ := hroots β hβ
  set M : Matrix.SpecialLinearGroup (Fin 2) (KFQ.Qext k) :=
    conjSL Pβ (Matrix.SpecialLinearGroup.map (algebraMap k (KFQ.Qext k)) (transvSL k)) with hM
  set w₀ : ModGL .G2 (KFQ.Qext k) := rootSL2 .G2 (KFQ.Qext k) β M with hw₀
  have hw₀R : w₀ ∈ rootRankOneGroup .G2 (KFQ.Qext k) β ⊓ conjEntrywiseImage k g := by
    have hM' : M ∈ (Matrix.SpecialLinearGroup.map (algebraMap k (KFQ.Qext k))).range.map
        (conjSL Pβ) := ⟨_, ⟨transvSL k, rfl⟩, rfl⟩
    rw [← hPβ] at hM'
    exact hM'
  have hw₀C : w₀ ∈ conjEntrywiseImage k g ⊓ Subgroup.centralizer {rootDiagUnit .G2 a} := by
    rw [← hcomm] at hw₀R
    exact Subgroup.commutator_le.mpr (fun y hy z hz =>
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hy hz) (Subgroup.inv_mem _ hy))
        (Subgroup.inv_mem _ hz)) hw₀R
  have hw₀sq : w₀ ^ 2 = 1 := by
    rw [hw₀, ← map_pow, hM, ← map_pow, ← map_pow, transvSL_sq, map_one, map_one, map_one]
  have hw₀1 : w₀ ≠ 1 := by
    intro h1
    have h2 : M = 1 := rootSL2_injective_of_field β (h1.trans (map_one _).symm)
    set X : Matrix (Fin 2) (Fin 2) (KFQ.Qext k) :=
      ((Matrix.SpecialLinearGroup.map (algebraMap k (KFQ.Qext k)) (transvSL k) :
        Matrix.SpecialLinearGroup (Fin 2) (KFQ.Qext k)) : Matrix (Fin 2) (Fin 2) (KFQ.Qext k))
      with hX
    have h3 : (Pβ : Matrix (Fin 2) (Fin 2) (KFQ.Qext k)) * X *
        (↑Pβ⁻¹ : Matrix (Fin 2) (Fin 2) (KFQ.Qext k)) = 1 :=
      congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) (KFQ.Qext k) =>
        (A : Matrix (Fin 2) (Fin 2) (KFQ.Qext k))) h2
    have key : (↑Pβ⁻¹ : Matrix (Fin 2) (Fin 2) (KFQ.Qext k)) *
        ((Pβ : Matrix (Fin 2) (Fin 2) (KFQ.Qext k)) * X *
          (↑Pβ⁻¹ : Matrix (Fin 2) (Fin 2) (KFQ.Qext k))) * (Pβ : Matrix (Fin 2) (Fin 2) _) = X := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, Pβ.inv_mul, Matrix.mul_one, ← Matrix.mul_assoc,
        Pβ.inv_mul, Matrix.one_mul]
    rw [h3, Matrix.mul_one, Pβ.inv_mul] at key
    have h5 := congrFun (congrFun key 0) 1
    rw [hX] at h5
    change (0 : KFQ.Qext k) = algebraMap k (KFQ.Qext k) 1 at h5
    rw [map_one] at h5
    exact zero_ne_one h5
  obtain ⟨b, hbA, hbx⟩ : ∃ b ∈ A, F b = rootDiagUnit .G2 a := by
    rw [← hFA] at hxE
    exact hxE
  obtain ⟨w, hw⟩ : ∃ w, F w = w₀ := by
    have : w₀ ∈ F.range := hFrange ▸ hw₀C.1
    exact this
  refine ⟨b, hbA, fun h1 => hx1 (by rw [← hbx, h1, map_one]), w, fun h1 => hw₀1 (by
    rw [← hw, h1, map_one]), hF (by rw [map_pow, hw, hw₀sq, map_one]), hF ?_⟩
  rw [map_mul, map_mul, hbx, hw]
  exact (Subgroup.mem_centralizer_singleton_iff.mp hw₀C.2).symm

end CFSG.RankThree.PartTwo.Sec13.KF135Chev2Exc
