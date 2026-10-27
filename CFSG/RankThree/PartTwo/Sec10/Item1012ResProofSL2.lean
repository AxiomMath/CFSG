module

public import CFSG.RankThree.PartTwo.Sec4.Vocabulary
public import CFSG.LocalAnalysis.SectionRank.EvenCover.SLTwo
public import CFSG.Adapters.LinearSmallCatalog

public section

namespace CFSG.RankThree.PartTwo.Sec10.Item1012ResProof

open Matrix CFSG

theorem card_sl2_of_card_four {k : Type*} [Field k] [Finite k] (hk : Nat.card k = 4) :
    Nat.card (SpecialLinearGroup (Fin 2) k) = 60 := by
  classical
  have := Fintype.ofFinite k
  rw [Matrix.card_SL_field, Fin.prod_univ_two, Fintype.card_eq_nat_card, hk]
  norm_num

@[expose] def g3 (k : Type*) [CommRing k] : SpecialLinearGroup (Fin 2) k :=
  ⟨!![0, 1; -1, -1], by simp [Matrix.det_fin_two]⟩

theorem coe_g3 (k : Type*) [CommRing k] :
    ((g3 k : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = !![0, 1; -1, -1] :=
  rfl

theorem g3_pow_three (k : Type*) [CommRing k] : g3 k ^ 3 = 1 := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [Matrix.SpecialLinearGroup.coe_pow, coe_g3, Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two]

theorem g3_ne_one (k : Type*) [CommRing k] [Nontrivial k] : g3 k ≠ 1 := by
  intro h
  have h00 := congrArg
    (fun g : SpecialLinearGroup (Fin 2) k => (g : Matrix (Fin 2) (Fin 2) k) 0 0) h
  simp [g3] at h00

theorem eq_one_of_mem_center_sl2 {k : Type*} [Field k] [CharP k 2]
    {h : SpecialLinearGroup (Fin 2) k} (hc : h ∈ Subgroup.center (SpecialLinearGroup (Fin 2) k)) :
    h = 1 := by
  obtain ⟨r, hr2, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  rw [Fintype.card_fin] at hr2
  have h2 : (2 : k) = 0 := CharP.cast_eq_zero k 2
  have hr1 : r = 1 := by
    have hsq : (r - 1) ^ 2 = 0 := by linear_combination hr2 + (1 - r) * h2
    exact sub_eq_zero.mp (pow_eq_zero_iff (two_ne_zero) |>.mp hsq)
  have hh : (h : Matrix (Fin 2) (Fin 2) k) = 1 := by rw [← hr, hr1, map_one]
  exact Matrix.SpecialLinearGroup.ext _ _ fun i j => by
    rw [hh, Matrix.SpecialLinearGroup.coe_one]

@[expose] def blk {K : Type*} [CommRing K] (X : Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin 3) (Fin 3) K :=
  !![X 0 0, X 0 1, 0; X 1 0, X 1 1, 0; 0, 0, 1]

theorem blk_mul {K : Type*} [CommRing K] (X Y : Matrix (Fin 2) (Fin 2) K) :
    blk (X * Y) = blk X * blk Y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

theorem blk_one {K : Type*} [CommRing K] : blk (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk]

theorem det_blk {K : Type*} [CommRing K] (X : Matrix (Fin 2) (Fin 2) K) :
    (blk X).det = X.det := by
  rw [Matrix.det_fin_three, Matrix.det_fin_two]
  simp [blk]

@[expose] def blkSL (K : Type*) [CommRing K] :
    SpecialLinearGroup (Fin 2) K →* SpecialLinearGroup (Fin 3) K where
  toFun X := ⟨blk (X : Matrix (Fin 2) (Fin 2) K), (det_blk _).trans X.2⟩
  map_one' := Subtype.ext blk_one
  map_mul' X Y := Subtype.ext (blk_mul (X : Matrix (Fin 2) (Fin 2) K) Y)

theorem coe_blkSL {K : Type*} [CommRing K] (X : SpecialLinearGroup (Fin 2) K) :
    (blkSL K X : Matrix (Fin 3) (Fin 3) K) = blk (X : Matrix (Fin 2) (Fin 2) K) :=
  rfl

theorem blkSL_injective {K : Type*} [CommRing K] : Function.Injective (blkSL K) := by
  intro X Y h
  ext i j
  have h' := congrArg (fun g : SpecialLinearGroup (Fin 3) K =>
    (g : Matrix (Fin 3) (Fin 3) K) (Fin.castSucc i) (Fin.castSucc j)) h
  simp only [coe_blkSL] at h'
  fin_cases i <;> fin_cases j <;> simpa [blk] using h'

theorem eq_one_of_blkSL_mem_center {K : Type*} [Field K] {h : SpecialLinearGroup (Fin 2) K}
    (hc : blkSL K h ∈ Subgroup.center (SpecialLinearGroup (Fin 3) K)) : h = 1 := by
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  have h22 := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M 2 2) hr
  simp [coe_blkSL, blk] at h22
  have hb : (blkSL K h : Matrix (Fin 3) (Fin 3) K) = 1 := by rw [← hr, h22, map_one]
  apply blkSL_injective
  rw [map_one]
  exact Matrix.SpecialLinearGroup.ext _ _ fun i j => by
    rw [hb, Matrix.SpecialLinearGroup.coe_one]

theorem map_mem_center_of_mulEquiv {A B : Type*} [Group A] [Group B] (φ : A ≃* B) {x : A}
    (hx : x ∈ Subgroup.center A) : φ x ∈ Subgroup.center B := by
  rw [Subgroup.mem_center_iff] at hx ⊢
  intro b
  obtain ⟨a, rfl⟩ := φ.surjective b
  rw [← map_mul, ← map_mul, hx a]

@[expose] def finFiveSix : Fin 5 ≃ {x : Fin 6 // x.val < 5} where
  toFun i := ⟨⟨i.val, by omega⟩, i.2⟩
  invFun x := ⟨x.1.val, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[expose] def altFiveSix : alternatingGroup (Fin 5) →* alternatingGroup (Fin 6) :=
  ((Equiv.Perm.extendDomainHom finFiveSix).comp (alternatingGroup (Fin 5)).subtype).codRestrict
    (alternatingGroup (Fin 6)) fun σ => by
      rw [Equiv.Perm.mem_alternatingGroup, MonoidHom.comp_apply,
        Equiv.Perm.extendDomainHom_apply, Equiv.Perm.sign_extendDomain]
      exact σ.2

theorem altFiveSix_injective : Function.Injective altFiveSix := by
  intro σ τ h
  apply Subtype.ext
  apply Equiv.Perm.extendDomainHom_injective finFiveSix
  exact congrArg Subtype.val h

theorem exists_sl2_hom
    {T : Type} [Group T] [Finite T]
    (hT : Sec4.IsSLThreePiAt T 4 ∨ Sec4.IsTripleCover T (alternatingGroup (Fin 6))) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 4 ∧
      ∃ ρ : SpecialLinearGroup (Fin 2) k →* T, ρ (g3 k) ≠ 1 ∧
        ∀ h, ρ h ∈ Subgroup.center T → ρ h = 1 := by
  rcases hT with ⟨K, _, _, hK⟩ | ⟨hZ, ⟨e6⟩⟩
  · rcases hK with ⟨hK4, -, ⟨ψ⟩⟩ | ⟨-, h2, -⟩
    ·
      set e3 := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K with he3
      set φ : T ≃* SpecialLinearGroup (Fin 3) K := ψ.trans e3.symm with hφ
      set ρ : SpecialLinearGroup (Fin 2) K →* T := φ.symm.toMonoidHom.comp (blkSL K) with hρ
      have hφρ : ∀ h, φ (ρ h) = blkSL K h := fun h => φ.apply_symm_apply _
      refine ⟨K, inferInstance, inferInstance, hK4, ρ, fun h1 => g3_ne_one K ?_, fun h hc => ?_⟩
      · apply blkSL_injective
        rw [← hφρ, h1, map_one, map_one]
      · have hc' := map_mem_center_of_mulEquiv φ hc
        rw [hφρ] at hc'
        rw [eq_one_of_blkSL_mem_center hc', map_one]
    · norm_num at h2
  ·
    set k := GaloisField 2 2 with hk
    have hk4 : Nat.card k = 4 := by
      rw [hk, GaloisField.card 2 2 (by norm_num)]
      norm_num
    obtain ⟨e5⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five k
      (Or.inl hk4)
    set q : SpecialLinearGroup (Fin 2) k →* alternatingGroup (Fin 6) :=
      altFiveSix.comp (e5.toMonoidHom.comp
        ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 k).toMonoidHom.comp
          (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 2) k))))) with hq
    have hqker : ∀ h, q h = 1 → h = 1 := by
      intro h hh
      have h1 : (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 2) k))) h = 1 := by
        apply (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 k).injective
        apply e5.injective
        apply altFiveSix_injective
        rw [map_one, map_one, map_one]
        exact hh
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact eq_one_of_mem_center_sl2 h1
    set πT : T →* alternatingGroup (Fin 6) :=
      e6.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center T)) with hπT
    have hπTs : Function.Surjective πT :=
      e6.surjective.comp (QuotientGroup.mk'_surjective _)
    have hπTker : πT.ker = Subgroup.center T := by
      ext x
      rw [MonoidHom.mem_ker, hπT, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    have hcen : πT.ker ≤ Subgroup.center T := hπTker.le
    have hC : ¬ 2 ∣ Nat.card πT.ker := by
      rw [hπTker, hZ]
      norm_num
    obtain ⟨ρ, hρ, -⟩ :=
      CFSG.SectionRank.EvenCover.sl2_existsUnique_lift (p := 2) (k := k) hπTs hcen hC q
    have hρq : ∀ h, πT (ρ h) = q h := fun h => DFunLike.congr_fun hρ h
    refine ⟨k, inferInstance, inferInstance, hk4, ρ, fun h1 => g3_ne_one k ?_,
      fun h hc => ?_⟩
    · apply hqker
      rw [← hρq, h1, map_one]
    · have h1 : q h = 1 := by
        rw [← hρq]
        exact (MonoidHom.mem_ker).mp (hπTker ▸ hc)
      rw [hqker h h1, map_one]

end CFSG.RankThree.PartTwo.Sec10.Item1012ResProof
