module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.PinnedBaseChange
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.C3AlgebraicPart2

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.RationalC3

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType
  CFSG.LieType.Chevalley CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Universal.Symplectic CFSG.Timmesfeld.LieEmbed
  CFSG.SeitzReduction.F4Pilot
  CFSG.StandardType.F4ExplicitPos.BaseChange CFSG.StandardType.F4ExplicitPos.RootBaseChange
  CFSG.StandardType.F4ExplicitPos.PinnedBaseChange
  CFSG.HardMathSupport.Timmesfeld.LangTorus

open scoped Matrix

section RangeDescent

theorem statedSpMap_comp' {K L M : Type} [Field K] [Field L] [Field M]
    (g : L →+* M) (f : K →+* L) (n : ℕ) (x : ↥(StatedSp n K)) :
    statedSpMap g n (statedSpMap f n x) = statedSpMap (g.comp f) n x := by
  apply Subtype.ext
  simp only [coe_statedSpMap]
  exact congrArg (fun h : GL (Fin n ⊕ Fin n) K →* GL (Fin n ⊕ Fin n) M => h x)
    (Matrix.GeneralLinearGroup.map_comp (n := Fin n ⊕ Fin n) f g).symm

theorem statedSpMap_range_eq_eqLocus {K Ω : Type} [Field K] [Finite K] [Field Ω] [Algebra K Ω]
    (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ Nat.card K) (n : ℕ) :
    (statedSpMap (algebraMap K Ω) n).range =
      (statedSpMap Fr n).eqLocus (MonoidHom.id _) := by
  apply le_antisymm
  · rintro x ⟨g, rfl⟩
    change statedSpMap Fr n (statedSpMap (algebraMap K Ω) n g) =
      statedSpMap (algebraMap K Ω) n g
    rw [statedSpMap_comp', frobenius_comp_algebraMap Fr hFr]
  · intro g hg
    classical
    change statedSpMap Fr n g = g at hg
    let M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) Ω := (g : GL (Fin n ⊕ Fin n) Ω)
    let M' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) Ω :=
      ((g⁻¹ : ↥(StatedSp n Ω)) : GL (Fin n ⊕ Fin n) Ω)
    have hGL : Matrix.GeneralLinearGroup.map Fr (g : GL (Fin n ⊕ Fin n) Ω) =
        (g : GL (Fin n ⊕ Fin n) Ω) := by
      have h' := congrArg (fun x : ↥(StatedSp n Ω) => (x : GL (Fin n ⊕ Fin n) Ω)) hg
      simpa only [coe_statedSpMap] using h'
    have hGL' : Matrix.GeneralLinearGroup.map Fr
        ((g⁻¹ : ↥(StatedSp n Ω)) : GL (Fin n ⊕ Fin n) Ω) =
        ((g⁻¹ : ↥(StatedSp n Ω)) : GL (Fin n ⊕ Fin n) Ω) := by
      have hg' : statedSpMap Fr n g⁻¹ = g⁻¹ := by rw [map_inv, hg]
      have h' := congrArg (fun x : ↥(StatedSp n Ω) => (x : GL (Fin n ⊕ Fin n) Ω)) hg'
      simpa only [coe_statedSpMap] using h'
    have hM : M.map Fr = M := by
      have h' := congrArg (fun A : GL (Fin n ⊕ Fin n) Ω =>
        (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) Ω)) hGL
      simpa only [M, coe_map_GL] using h'
    have hM' : M'.map Fr = M' := by
      have h' := congrArg (fun A : GL (Fin n ⊕ Fin n) Ω =>
        (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) Ω)) hGL'
      simpa only [M', coe_map_GL] using h'
    have hentry : ∀ i j, Fr (M i j) = M i j := by
      intro i j
      have h' := congrArg (fun A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) Ω => A i j) hM
      simpa only [Matrix.map_apply] using h'
    have hentry' : ∀ i j, Fr (M' i j) = M' i j := by
      intro i j
      have h' := congrArg (fun A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) Ω => A i j) hM'
      simpa only [Matrix.map_apply] using h'
    choose a ha using fun i j =>
      Set.mem_range.mp (mem_range_algebraMap_of_pow_card_eq (k := K)
        ((hFr _).symm.trans (hentry i j)))
    choose b hb using fun i j =>
      Set.mem_range.mp (mem_range_algebraMap_of_pow_card_eq (k := K)
        ((hFr _).symm.trans (hentry' i j)))
    let A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K := Matrix.of a
    let B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K := Matrix.of b
    have hA : A.map (algebraMap K Ω) = M := by
      ext i j
      simpa only [A, Matrix.of_apply, Matrix.map_apply] using ha i j
    have hB : B.map (algebraMap K Ω) = M' := by
      ext i j
      simpa only [B, Matrix.of_apply, Matrix.map_apply] using hb i j
    have hinj : Function.Injective
        (fun N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K =>
          N.map (algebraMap K Ω)) := Matrix.map_injective (algebraMap K Ω).injective
    have hAB : A * B = 1 := hinj (by
      change (A * B).map (algebraMap K Ω) =
        (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K).map (algebraMap K Ω)
      rw [Matrix.map_mul, hA, hB, Matrix.map_one _ (map_zero _) (map_one _)]
      simpa only [M, M', Subgroup.coe_inv] using Units.mul_inv (g : GL (Fin n ⊕ Fin n) Ω))
    have hBA : B * A = 1 := hinj (by
      change (B * A).map (algebraMap K Ω) =
        (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K).map (algebraMap K Ω)
      rw [Matrix.map_mul, hA, hB, Matrix.map_one _ (map_zero _) (map_one _)]
      simpa only [M, M', Subgroup.coe_inv] using Units.inv_mul (g : GL (Fin n ⊕ Fin n) Ω))
    let G : GL (Fin n ⊕ Fin n) K := ⟨A, B, hAB, hBA⟩
    have hG : G ∈ StatedSp n K := by
      rw [CFSG.Open.StatedAPI.mem_statedSp_iff]
      refine (isSymplectic_map_iff (algebraMap K Ω) A).1 ?_
      rw [hA]
      simpa only [M] using ((CFSG.Open.StatedAPI.mem_statedSp_iff).1 g.2)
    refine ⟨⟨G, hG⟩, ?_⟩
    apply Subtype.ext
    apply Units.ext
    change (Matrix.GeneralLinearGroup.map (algebraMap K Ω) (G : GL (Fin n ⊕ Fin n) K) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) Ω) = M
    rw [coe_map_GL]
    exact hA

end RangeDescent

section SpQuasisimple

theorem isQuasisimple_range {K A : Type} [Field K] [Finite K] [CharP K 2] [Group A]
    (i : ↥(StatedSp 3 K) →* A) (hi : Function.Injective i) :
    CFSG.IsQuasisimple ↥(MonoidHom.range i) := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, _hf, hcard⟩ := FiniteField.card K 2
  have hcard' : Nat.card K = 2 ^ (f : ℕ) := by
    rw [Nat.card_eq_fintype_card, hcard]
  have hcase : Nat.card K = 2 ∨ 4 ≤ Nat.card K := by
    rcases lt_or_ge (f : ℕ) 2 with h | h
    · left
      have hfpos : 0 < (f : ℕ) := f.pos
      have hf1 : (f : ℕ) = 1 := by omega
      rw [hcard', hf1]; norm_num
    · right
      rw [hcard']
      exact Nat.pow_le_pow_right (by norm_num : 0 < 2) h
  have hF : (Infinite K ∨ 4 ≤ Nat.card K) ∨ (Nat.card K = 3 ∧ 2 ≤ 3) ∨
      (Nat.card K = 2 ∧ 3 ≤ 3) :=
    hcase.elim (fun h => Or.inr (Or.inr ⟨h, by norm_num⟩))
      (fun h => Or.inl (Or.inr h))
  have hsp : CFSG.IsQuasisimple ↥(StatedSp 3 K) :=
    CFSG.LieType.Universal.Symplectic.isQuasisimple (n := 3) (F := K)
      (hn := by norm_num) (hF := hF)
  exact CFSG.IsQuasisimple.of_mulEquiv (MonoidHom.ofInjective hi).symm hsp

end SpQuasisimple

section Naturality

theorem hom_ext_x3_alg {K H : Type} [Field K] [CharP K 2] [Group H]
    {Ψ Ψ' : ↥(StatedSp 3 K) →* H}
    (h : ∀ γ c, Ψ (Sp.x 3 K γ c) = Ψ' (Sp.x 3 K γ c)) : Ψ = Ψ' := by
  ext g
  change g ∈ MonoidHom.eqLocus Ψ Ψ'
  have hg : g ∈ ⨆ γ ∈ roots (isFiniteType_cartanC 3) ∅,
      CFSG.StandardType.F4ExplicitPos.C3Range.c3RootSubgroup (K := K) γ := by
    rw [CFSG.StandardType.F4ExplicitPos.C3Algebraic.iSup_c3RootSubgroup_eq_top_alg (K := K)]
    exact Subgroup.mem_top g
  have hle : (⨆ γ ∈ roots (isFiniteType_cartanC 3) ∅,
      CFSG.StandardType.F4ExplicitPos.C3Range.c3RootSubgroup (K := K) γ) ≤ MonoidHom.eqLocus Ψ Ψ' :=
    iSup₂_le fun γ _hγ => by
      rw [CFSG.StandardType.F4ExplicitPos.C3Range.c3RootSubgroup, Subgroup.closure_le]
      rintro _ ⟨c, rfl⟩
      exact h γ c
  exact hle hg

theorem iOmega_natural
    (Ω : Type) [Field Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω]
    [Algebra.IsAlgebraic (ZMod 2) Ω] (Fr : Ω →+* Ω) :
    (j (τ := .F4) Fr).comp (CFSG.StandardType.F4ExplicitPos.C3Algebraic.iOmega Ω) =
      (CFSG.StandardType.F4ExplicitPos.C3Algebraic.iOmega Ω).comp (statedSpMap Fr 3) := by
  apply hom_ext_x3_alg (K := Ω)
  intro γ c
  simp only [MonoidHom.comp_apply]
  rw [CFSG.StandardType.F4ExplicitPos.C3Algebraic.iOmega_x, statedSpMap_x,
    CFSG.StandardType.F4ExplicitPos.C3Algebraic.iOmega_x]
  exact map_j_xPar (τ := .F4) Fr (rootOperatorFamily .F4) (c3ToF4 γ) c

theorem iOmega_natural_apply
    (Ω : Type) [Field Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω]
    [Algebra.IsAlgebraic (ZMod 2) Ω] (Fr : Ω →+* Ω) (g : ↥(StatedSp 3 Ω)) :
    j (τ := .F4) Fr (CFSG.StandardType.F4ExplicitPos.C3Algebraic.iOmega Ω g) =
      CFSG.StandardType.F4ExplicitPos.C3Algebraic.iOmega Ω (statedSpMap Fr 3 g) :=
  DFunLike.congr_fun (iOmega_natural Ω Fr) g

noncomputable def conjIM
    (Ω : Type) [Field Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω]
    [Algebra.IsAlgebraic (ZMod 2) Ω] (n : ModGL .F4 Ω) : ↥(StatedSp 3 Ω) →* ModGL .F4 Ω :=
  (MulAut.conj n).toMonoidHom.comp
    ((adjointGroup .F4 Ω).subtype.comp (CFSG.StandardType.F4ExplicitPos.C3Algebraic.iOmega Ω))

theorem conjIM_apply
    (Ω : Type) [Field Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω]
    [Algebra.IsAlgebraic (ZMod 2) Ω] (n : ModGL .F4 Ω) (g : ↥(StatedSp 3 Ω)) :
    conjIM Ω n g = n * (C3Algebraic.iOmega Ω g : ModGL .F4 Ω) * n⁻¹ := by
  change MulAut.conj n
      ((adjointGroup .F4 Ω).subtype (CFSG.StandardType.F4ExplicitPos.C3Algebraic.iOmega Ω g)) =
    n * (CFSG.StandardType.F4ExplicitPos.C3Algebraic.iOmega Ω g : ModGL .F4 Ω) * n⁻¹
  rw [MulAut.conj_apply]
  rfl

theorem conjIM_injective
    (Ω : Type) [Field Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω]
    [Algebra.IsAlgebraic (ZMod 2) Ω] (n : ModGL .F4 Ω) :
    Function.Injective (conjIM Ω n) :=
  (MulAut.conj n).injective.comp
    ((adjointGroup .F4 Ω).subtype_injective.comp
      (CFSG.StandardType.F4ExplicitPos.C3Algebraic.iOmega_injective Ω))

theorem conjIM_x
    (Ω : Type) [Field Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω]
    [Algebra.IsAlgebraic (ZMod 2) Ω] (n : ModGL .F4 Ω) (γ : Fin 3 → ℤ) (c : Ω) :
    conjIM Ω n (Sp.x 3 Ω γ c) =
      n * (Adjoint.f4Par Ω (c3ToF4 γ) c : ModGL .F4 Ω) * n⁻¹ := by
  rw [conjIM_apply, CFSG.StandardType.F4ExplicitPos.C3Algebraic.iOmega_x]

theorem conjIM_x_pinned
    (Ω : Type) [Field Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω]
    [Algebra.IsAlgebraic (ZMod 2) Ω] (n : ModGL .F4 Ω) {γ : Fin 3 → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartanC 3) ∅) (c : Ω) :
    conjIM Ω n (Sp.x 3 Ω γ c) =
      n * pinnedX .F4 Ω (c3ToF4 γ)
        (((rootOperatorFamily .F4).pinnedFamilySign (c3ToF4 γ) : Ω) * c) * n⁻¹ := by
  rw [conjIM_x,
    CFSG.StandardType.F4ExplicitPos.C3Algebraic.f4Par_coe_eq_pinnedX_alg (isRoot_c3ToF4 hγ)]

theorem Phi_x_pinned
    (Ω : Type) [Field Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω]
    [Algebra.IsAlgebraic (ZMod 2) Ω] {K : Type} [Field K] [Algebra K Ω]
    (n z : ModGL .F4 Ω) {γ : Fin 3 → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanC 3) ∅)
    (c : K) :
    (((MulAut.conj z).toMonoidHom.comp (conjIM Ω n)).comp
        (statedSpMap (algebraMap K Ω) 3)) (Sp.x 3 K γ c) =
      z * n * pinnedX .F4 Ω (c3ToF4 γ)
        (((rootOperatorFamily .F4).pinnedFamilySign (c3ToF4 γ) : Ω) * algebraMap K Ω c)
        * n⁻¹ * z⁻¹ := by
  change MulAut.conj z
    (conjIM Ω n (statedSpMap (algebraMap K Ω) 3 (Sp.x 3 K γ c))) = _
  rw [statedSpMap_x]
  rw [conjIM_x_pinned (hγ := hγ) (c := algebraMap K Ω c), MulAut.conj_apply]
  group

noncomputable def finitePinnedRoot
    (Ω : Type) [Field Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω]
    [Algebra.IsAlgebraic (ZMod 2) Ω] {K : Type} [Field K] [Algebra K Ω]
    (γ : Fin 3 → ℤ) : Subgroup (ModGL .F4 Ω) :=
  Subgroup.closure (Set.range (fun c : K =>
    pinnedX .F4 Ω (c3ToF4 γ)
      (((rootOperatorFamily .F4).pinnedFamilySign (c3ToF4 γ) : Ω) * algebraMap K Ω c)))

end Naturality
end CFSG.StandardType.F4ExplicitPos.RationalC3
end

end
