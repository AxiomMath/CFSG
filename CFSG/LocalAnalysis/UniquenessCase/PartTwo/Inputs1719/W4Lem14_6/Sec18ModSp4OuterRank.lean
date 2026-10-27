module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18ModSp4OuterGamma

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6.Sp4Outer

open Matrix CFSG.QuasithinUnique.Setup.X7b CFSG.QuasithinUnique.Setup.X7
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.Semidihedral.Principal Representation

variable {F : Type} [Field F] [CharP F 2] [Fintype F] {f : ℕ}

theorem three_mul_le_rank_of_outer_matrix (hF : Fintype.card F = 2 ^ f) (hf : 2 ≤ f)
    (hfodd : f % 2 = 1) {ι : Type} [Fintype ι] [DecidableEq ι]
    (PF : antiSp F →* Matrix ι ι F) (hτ : matMap (frobeniusEquiv F 2 : F →+* F) PF = PF)
    (hnt : ∃ g, PF g ≠ 1) (A : Matrix ι ι F) (hAA : A * A = 1)
    (hA : ∀ g, A * PF g = PF ((minorAut F ^ f) g) * A) : 3 * f ≤ (A - 1).rank := by
  classical
  have hf1 : 1 ≤ f := by omega
  obtain ⟨A₀, hA₀, hne, hpos⟩ := exists_nonempty_label hF hf1 (antiSp_isPerfect hF hf) PF hnt
  have hiso : MatIso PF (PF.comp (minorAut F ^ f).toMonoidHom) A A := ⟨hAA, hAA, hA⟩
  obtain ⟨e⟩ := hiso.equiv
  let m : Finset ℕ → ℕ := fun B =>
    repMultiplicity (matRep PF) (matRep (tensorRepS (F := F) F B))
  have hm2 : ∀ B, B ⊆ Finset.range (2 * f) → m (shiftSet f 2 B) = m B := fun B hB =>
    mult_shift_two hF PF hτ hB
  have hm0 : ∀ B, B ⊆ Finset.range (2 * f) → m (shiftSet f (2 * f - f) B) = m B := fun B hB =>
    mult_shift_pow hF hf1 PF f (by omega) e hB
  have hinv := invariant_all_shifts hf1 m hm2 (2 * f - f) (by omega) (by omega) hm0
  have hOpos : ∀ B ∈ orbitSet f A₀, B ⊆ Finset.range (2 * f) ∧ 0 < m B := by
    intro B hB
    obtain ⟨s, -, rfl⟩ := mem_orbitSet.mp hB
    exact ⟨shiftSet_subset hf1 s A₀, by rw [hinv s A₀ hA₀]; exact hpos⟩
  let s : (ι → F) ≃ₗ[F] (ι → F) := LinearEquiv.ofLinearMap (Matrix.mulVecLin A)
    (Matrix.mulVecLin A) (by rw [← Matrix.mulVecLin_mul, hAA, Matrix.mulVecLin_one])
    (by rw [← Matrix.mulVecLin_mul, hAA, Matrix.mulVecLin_one])
  have hss : ∀ v, s (s v) = v := fun v => by
    show A.mulVec (A.mulVec v) = v
    rw [Matrix.mulVec_mulVec, hAA, Matrix.one_mulVec]
  have hs : ∀ g v, s (matRep PF g v) = matRep PF ((minorAut F ^ f) g) (s v) := fun g v => by
    show A.mulVec ((PF g).mulVec v) = (PF ((minorAut F ^ f) g)).mulVec (A.mulVec v)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hA g]
  have key := sum_weight_le_codim hF hf1 (matRep PF) s hss hs (orbitSet f A₀)
    (fun B hB => (hOpos B hB).1)
  have hlow : 3 * (2 * f) ≤ ∑ C ∈ orbitSet f A₀, 3 * C.card *
      repMultiplicity (matRep PF) (matRep (tensorRepS (F := F) F C)) := by
    have hterm : ∀ C ∈ orbitSet f A₀, 3 * A₀.card ≤ 3 * C.card *
        repMultiplicity (matRep PF) (matRep (tensorRepS (F := F) F C)) := by
      intro C hC
      rw [card_of_mem_orbitSet hA₀ hC]
      have := (hOpos C hC).2
      exact Nat.le_mul_of_pos_right _ this
    calc 3 * (2 * f) ≤ 3 * ((orbitSet f A₀).card * A₀.card) :=
          Nat.mul_le_mul_left _ (orbit_card_mul hf1 hA₀ hne)
      _ = ∑ _C ∈ orbitSet f A₀, 3 * A₀.card := by
          rw [Finset.sum_const, smul_eq_mul]
          ring
      _ ≤ _ := Finset.sum_le_sum hterm
  have hD : s.toLinearMap - 1 = Matrix.mulVecLin (A - 1) := by
    refine LinearMap.ext fun v => ?_
    simp [s, Matrix.sub_mulVec]
  have hrn := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin (A - 1))
  rw [hD] at key
  unfold Matrix.rank
  rw [Module.finrank_fintype_fun_eq_card] at *
  omega

theorem outer_involution_displacement_ge (hf : 2 ≤ f) (hfodd : f % 2 = 1)
    (hF : Fintype.card F = 2 ^ f) {M : Type} [AddCommGroup M] [Module (ZMod 2) M]
    [Module.Finite (ZMod 2) M] (π : Representation (ZMod 2) (antiSp F) M)
    (hπ : Function.Injective π) (a : M ≃ₗ[ZMod 2] M) (ha : orderOf a = 2)
    (α : MulAut (antiSp F))
    (hα : α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (antiSp F))
    (hnorm : ∀ (g : antiSp F) (w : M), a (π g (a.symm w)) = π (α g) w) :
    3 * f ≤ Module.finrank (ZMod 2) (LinearMap.range (a.toLinearMap - 1)) := by
  classical
  have haa : a * a = 1 := by
    rw [← sq]
    have := pow_orderOf_eq_one a
    rwa [ha] at this
  have hinv : ∀ w, a (a w) = w := fun w => by
    have := congrArg (fun e : M ≃ₗ[ZMod 2] M => e w) haa
    exact this
  have hnorm' : ∀ (g : antiSp F) (v : M), a (π g v) = π (α g) (a v) := fun g v => by
    have := hnorm g (a v)
    rwa [LinearEquiv.symm_apply_apply] at this
  have hstar : ∀ (g : antiSp F) (v : M), π (α g) v = a (π g (a v)) := fun g v => by
    have := hnorm' g (a v)
    rw [hinv] at this
    exact this.symm
  have hαα : α * α = 1 := by
    refine MulEquiv.ext fun g => ?_
    show α (α g) = g
    apply hπ
    refine LinearMap.ext fun w => ?_
    show π (α (α g)) w = π g w
    rw [hstar (α g) w, hstar g (a w), hinv, hinv]
  have hK : Nat.card F = 2 ^ f := by rw [Nat.card_eq_fintype_card, hF]
  obtain ⟨c, hc⟩ := outer_involution_conj hf hK α hαα hα
  set τ : MulAut (antiSp F) := minorAut F ^ f with hτ
  have hαc : ∀ g : antiSp F, α (c * g * c⁻¹) = c * τ g * c⁻¹ := fun g => by
    rw [hc]
    simp [MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_def, MulAut.conj_symm_apply]
    group
  let πc : Representation (ZMod 2) (antiSp F) M := π.comp (MulAut.conj c).toMonoidHom
  have hπc : Function.Injective πc := hπ.comp (MulAut.conj c).injective
  have hπc_apply : ∀ g, πc g = π (c * g * c⁻¹) := fun g => rfl
  have hacomm : ∀ (g : antiSp F) (v : M), a (πc g v) = πc (τ g) (a v) := fun g v => by
    rw [hπc_apply, hπc_apply, hnorm', hαc]
  have hnt : ∃ g, πc g ≠ 1 := ⟨invX F, fun h => invX_ne_one (hπc (h.trans (map_one πc).symm))⟩
  let n := Module.finrank (ZMod 2) M
  let bas : Module.Basis (Fin n) (ZMod 2) M := Module.finBasis (ZMod 2) M
  let φ : ZMod 2 →+* F := ZMod.castHom (dvd_refl 2) F
  let R₂ : antiSp F →* Matrix (Fin n) (Fin n) (ZMod 2) := toMatRep πc bas
  let PF : antiSp F →* Matrix (Fin n) (Fin n) F := matMap φ R₂
  let A₂ : Matrix (Fin n) (Fin n) (ZMod 2) := LinearMap.toMatrix bas bas a.toLinearMap
  let A : Matrix (Fin n) (Fin n) F := A₂.map φ
  have hA₂A₂ : A₂ * A₂ = 1 := by
    rw [← LinearMap.toMatrix_mul]
    have : a.toLinearMap * a.toLinearMap = 1 := LinearMap.ext hinv
    rw [this, LinearMap.toMatrix_one]
  have hAA : A * A = 1 := by
    show A₂.map φ * A₂.map φ = 1
    rw [← Matrix.map_mul, hA₂A₂, Matrix.map_one φ (map_zero φ) (map_one φ)]
  have hA₂ : ∀ g, A₂ * R₂ g = R₂ (τ g) * A₂ := fun g => by
    have h1 : a.toLinearMap * πc g = πc (τ g) * a.toLinearMap := LinearMap.ext (hacomm g)
    have h2 := congrArg (LinearMap.toMatrix bas bas) h1
    rwa [LinearMap.toMatrix_mul, LinearMap.toMatrix_mul] at h2
  have hA : ∀ g, A * PF g = PF ((minorAut F ^ f) g) * A := fun g => by
    show A₂.map φ * (R₂ g).map φ = (R₂ ((minorAut F ^ f) g)).map φ * A₂.map φ
    rw [← Matrix.map_mul, ← Matrix.map_mul, hA₂ g]
  have hφ : (frobeniusEquiv F 2 : F →+* F).comp φ = φ := RingHom.ext_zmod _ _
  have hτF : matMap (frobeniusEquiv F 2 : F →+* F) PF = PF := by
    refine MonoidHom.ext fun g => ?_
    show ((R₂ g).map φ).map (frobeniusEquiv F 2 : F →+* F) = (R₂ g).map φ
    rw [Matrix.map_map]
    congr 1
    funext x
    exact RingHom.congr_fun hφ x
  have hntF : ∃ g, PF g ≠ 1 := by
    obtain ⟨g, hg⟩ := hnt
    refine ⟨g, fun hPF => hg ?_⟩
    have h1 : (R₂ g).map φ = (1 : Matrix (Fin n) (Fin n) (ZMod 2)).map φ := by
      rw [Matrix.map_one φ (map_zero φ) (map_one φ)]
      exact hPF
    have h2 := Matrix.map_injective φ.injective h1
    have h3 : LinearMap.toMatrix bas bas (πc g) = LinearMap.toMatrix bas bas 1 := by
      rw [LinearMap.toMatrix_one]
      exact h2
    exact (LinearMap.toMatrix bas bas).injective h3
  have h4 := three_mul_le_rank_of_outer_matrix hF hf hfodd PF hτF hntF A hAA hA
  have hrank : (A - 1).rank ≤ Module.finrank (ZMod 2) (LinearMap.range (a.toLinearMap - 1)) := by
    have e1 : A - 1 = (A₂ - 1).map φ := by
      ext i j
      by_cases hij : i = j <;> simp [A, hij]
    have e2 : (A₂ - 1).rank = Module.finrank (ZMod 2) (LinearMap.range (a.toLinearMap - 1)) := by
      have e3 : A₂ - 1 = LinearMap.toMatrix bas bas (a.toLinearMap - 1) := by
        rw [map_sub, LinearMap.toMatrix_one] <;> rfl
      rw [e3, Matrix.rank_eq_finrank_range_toLin _ bas bas, Matrix.toLin_toMatrix]
    rw [← e2, e1]
    exact rank_map_ringHom_le φ _
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6.Sp4Outer
