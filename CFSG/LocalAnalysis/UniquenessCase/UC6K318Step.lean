module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K318Red

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.UC6.K318

open Module Subgroup
open scoped Matrix

section Quotients

variable {P : Type} [Group P] [Finite P]

theorem not_isSolvable_of_simple [Group.IsPerfect P] {R : Subgroup P} [R.Normal]
    (hs : IsSimpleGroup (P ⧸ R)) : ¬ Group.IsSolvable P := by
  intro h
  haveI := h
  have : Nontrivial (P ⧸ R) := IsSimpleGroup.toNontrivial
  exact Group.IsPerfect.not_isSolvable (P ⧸ R) inferInstance

theorem not_comm_of_simple [Group.IsPerfect P] {R : Subgroup P} [R.Normal]
    (hs : IsSimpleGroup (P ⧸ R)) : ¬ ∀ a b : P, a * b = b * a := fun h =>
  not_isSolvable_of_simple hs (isSolvable_of_comm h)

theorem eq_of_simple_quotients [Group.IsPerfect P] {R N : Subgroup P} [R.Normal] [N.Normal]
    (hRs : Group.IsSolvable R) (hR : IsSimpleGroup (P ⧸ R)) (hN : IsSimpleGroup (P ⧸ N)) :
    R = N := by
  have hNR : N ≤ R := by
    rcases le_or_eq_top_of_normal hRs hR N with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := (IsSimpleGroup.toNontrivial : Nontrivial (P ⧸ N)).exists_pair_ne
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
      exact hab (QuotientGroup.eq.2 (h ▸ mem_top _))
  refine le_antisymm ?_ hNR
  haveI : (R.map (QuotientGroup.mk' N)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective N)
  rcases hN.eq_bot_or_eq_top_of_normal (R.map (QuotientGroup.mk' N)) with h | h
  · intro x hx
    have hx' : QuotientGroup.mk' N x ∈ R.map (QuotientGroup.mk' N) := mem_map_of_mem _ hx
    rw [h, mem_bot] at hx'
    exact (QuotientGroup.eq_one_iff x).1 hx'
  · exfalso
    have hsurj : Function.Surjective ((QuotientGroup.mk' N).comp R.subtype) := by
      intro z
      have hz : z ∈ R.map (QuotientGroup.mk' N) := h ▸ mem_top z
      obtain ⟨y, hy, rfl⟩ := mem_map.1 hz
      exact ⟨⟨y, hy⟩, rfl⟩
    haveI := hRs
    have hsolv : Group.IsSolvable (P ⧸ N) := solvable_of_surjective hsurj
    have : Nontrivial (P ⧸ N) := IsSimpleGroup.toNontrivial
    exact Group.IsPerfect.not_isSolvable (P ⧸ N) hsolv

end Quotients

theorem exists_range_quotient_equiv {L G : Type*} [Group L] [Group G] (φ : L →* G)
    (Y : Subgroup L) [Y.Normal] (hφ : φ.ker ≤ Y) :
    ∃ _ : (Y.map φ.rangeRestrict).Normal,
      Nonempty (φ.range ⧸ Y.map φ.rangeRestrict ≃* L ⧸ Y) := by
  haveI hR : (Y.map φ.rangeRestrict).Normal :=
    Subgroup.Normal.map inferInstance _ φ.rangeRestrict_surjective
  set f : L →* φ.range ⧸ Y.map φ.rangeRestrict :=
    (QuotientGroup.mk' (Y.map φ.rangeRestrict)).comp φ.rangeRestrict with hf
  have hsurj : Function.Surjective f :=
    (QuotientGroup.mk'_surjective _).comp φ.rangeRestrict_surjective
  have hker : f.ker = Y := by
    rw [hf, ← MonoidHom.comap_ker, QuotientGroup.ker_mk', comap_map_eq,
      MonoidHom.ker_rangeRestrict, sup_eq_left.2 hφ]
  exact ⟨hR, ⟨((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hsurj)).symm⟩⟩

section Reducible

variable {F : Type*} [Field F] {L : Type*} [Group L] {d : ℕ}

@[expose] noncomputable def subRep (φ : L →* GL (Fin d) F) (W : Submodule F (Fin d → F))
    (hW : ∀ g, ∀ w ∈ W, (φ g : Matrix (Fin d) (Fin d) F) *ᵥ w ∈ W) : L →* Module.End F W where
  toFun g := (Matrix.toLin' (φ g : Matrix (Fin d) (Fin d) F)).restrict fun w hw => hW g w hw
  map_one' := LinearMap.ext fun w => Subtype.ext (by simp)
  map_mul' g h := LinearMap.ext fun w => Subtype.ext (by
    show (φ (g * h) : Matrix (Fin d) (Fin d) F) *ᵥ (w : Fin d → F) =
      (φ g : Matrix (Fin d) (Fin d) F) *ᵥ ((φ h : Matrix (Fin d) (Fin d) F) *ᵥ (w : Fin d → F))
    rw [map_mul, Units.val_mul, Matrix.mulVec_mulVec])

@[expose] noncomputable def quotRep (φ : L →* GL (Fin d) F) (W : Submodule F (Fin d → F))
    (hW : ∀ g, ∀ w ∈ W, (φ g : Matrix (Fin d) (Fin d) F) *ᵥ w ∈ W) :
    L →* Module.End F ((Fin d → F) ⧸ W) where
  toFun g := W.mapQ W (Matrix.toLin' (φ g : Matrix (Fin d) (Fin d) F)) fun w hw => hW g w hw
  map_one' := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective W v
    simp
  map_mul' g h := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective W v
    show Submodule.Quotient.mk ((φ (g * h) : Matrix (Fin d) (Fin d) F) *ᵥ v) =
      Submodule.Quotient.mk ((φ g : Matrix (Fin d) (Fin d) F) *ᵥ
        ((φ h : Matrix (Fin d) (Fin d) F) *ᵥ v))
    rw [map_mul, Units.val_mul, Matrix.mulVec_mulVec]

@[expose] noncomputable def glOf {M : Type*} [AddCommGroup M] [Module F M]
    [FiniteDimensional F M] (ρ : L →* Module.End F M) : L →* GL (Fin (finrank F M)) F :=
  (Units.map (LinearMap.toMatrixAlgEquiv (Module.finBasis F M)).toRingEquiv.toMonoidHom).comp
    ρ.toHomUnits

theorem glOf_eq_one_iff {M : Type*} [AddCommGroup M] [Module F M] [FiniteDimensional F M]
    (ρ : L →* Module.End F M) (g : L) : glOf ρ g = 1 ↔ ρ g = 1 := by
  constructor
  · intro h
    have h1 := congrArg Units.val h
    simp only [glOf, MonoidHom.coe_comp, Function.comp_apply, Units.coe_map,
      MonoidHom.coe_toHomUnits, Units.val_one] at h1
    apply (LinearMap.toMatrixAlgEquiv (Module.finBasis F M)).injective
    rw [map_one]
    exact h1
  · intro h
    apply Units.ext
    simp [glOf, h]

theorem one_add_pow_of_sq_eq_zero {A : Type*} [Ring A] {N : A} (hN : N * N = 0) (k : ℕ) :
    (1 + N) ^ k = 1 + k • N := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, add_mul, one_mul, mul_add, mul_one, smul_mul_assoc, hN, smul_zero,
      add_zero, succ_nsmul]
    abel

theorem pow_eq_one_of_unipotent {q : ℕ} [Fact q.Prime] {g : GL (Fin d) (ZMod q)}
    {W : Submodule (ZMod q) (Fin d → ZMod q)}
    (h1 : ∀ w ∈ W, (g : Matrix (Fin d) (Fin d) (ZMod q)) *ᵥ w = w)
    (h2 : ∀ v, (g : Matrix (Fin d) (Fin d) (ZMod q)) *ᵥ v - v ∈ W) : g ^ q = 1 := by
  set N : Matrix (Fin d) (Fin d) (ZMod q) := (g : Matrix (Fin d) (Fin d) (ZMod q)) - 1 with hN
  have hNv : ∀ v, N *ᵥ v = (g : Matrix (Fin d) (Fin d) (ZMod q)) *ᵥ v - v := fun v => by
    rw [hN, Matrix.sub_mulVec, Matrix.one_mulVec]
  have hNN : N * N = 0 := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    rw [map_zero, LinearMap.zero_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, hNv v,
      hNv, h1 _ (h2 v), sub_self]
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  have hg : (g : Matrix (Fin d) (Fin d) (ZMod q)) = 1 + N := by rw [hN]; abel
  rw [hg, one_add_pow_of_sq_eq_zero hNN, ← Nat.cast_smul_eq_nsmul (ZMod q), ZMod.natCast_self,
    zero_smul, add_zero]

theorem exists_lower_of_reducible {L : Type} [Group L] [Finite L] [Group.IsPerfect L] {q : ℕ}
    [Fact q.Prime]
    {Y : Subgroup L} [Y.Normal] (hYs : Group.IsSolvable Y) (hs : IsSimpleGroup (L ⧸ Y))
    (φ : L →* GL (Fin d) (ZMod q)) (hφ : φ.ker ≤ Y) (W : Submodule (ZMod q) (Fin d → ZMod q))
    (hW : ∀ g, ∀ w ∈ W, (φ g : Matrix (Fin d) (Fin d) (ZMod q)) *ᵥ w ∈ W) (hW0 : W ≠ ⊥)
    (hWt : W ≠ ⊤) : ∃ d' < d, ∃ ψ : L →* GL (Fin d') (ZMod q), ψ.ker ≤ Y := by
  classical
  have hdim : finrank (ZMod q) ((Fin d → ZMod q) ⧸ W) + finrank (ZMod q) W = d := by
    rw [Submodule.finrank_quotient_add_finrank, Module.finrank_fin_fun]
  have hW1 : finrank (ZMod q) W < d := by
    have := Submodule.finrank_lt hWt
    rwa [Module.finrank_fin_fun] at this
  have hWpos : 0 < finrank (ZMod q) W :=
    Nat.pos_of_ne_zero fun h => hW0 (Submodule.finrank_eq_zero.1 h)
  rcases le_or_eq_top_of_normal hYs hs (glOf (subRep φ W hW)).ker with h1 | h1
  · exact ⟨_, hW1, _, h1⟩
  rcases le_or_eq_top_of_normal hYs hs (glOf (quotRep φ W hW)).ker with h2 | h2
  · exact ⟨_, by omega, _, h2⟩
  exfalso
  have hpow : ∀ g, φ g ^ q = 1 := by
    intro g
    have hg1 : subRep φ W hW g = 1 :=
      (glOf_eq_one_iff _ g).1 (MonoidHom.mem_ker.1 (h1 ▸ mem_top g))
    have hg2 : quotRep φ W hW g = 1 :=
      (glOf_eq_one_iff _ g).1 (MonoidHom.mem_ker.1 (h2 ▸ mem_top g))
    refine pow_eq_one_of_unipotent (W := W) (fun w hw => ?_) (fun v => ?_)
    · have := congrArg (fun T : Module.End (ZMod q) W => ((T ⟨w, hw⟩ : W) : Fin d → ZMod q)) hg1
      exact this
    · have := congrArg (fun T : Module.End (ZMod q) ((Fin d → ZMod q) ⧸ W) =>
        T (Submodule.Quotient.mk v)) hg2
      simp only [quotRep, MonoidHom.coe_mk, OneHom.coe_mk, Submodule.mapQ_apply,
        Matrix.toLin'_apply, Module.End.one_apply] at this
      exact (Submodule.Quotient.eq W).1 this
  have hpg : IsPGroup q φ.range := by
    rintro ⟨_, g, rfl⟩
    exact ⟨1, Subtype.ext (by simpa using hpow g)⟩
  have : Group.IsPerfect φ.range := Group.IsPerfect.range φ
  have hbot : φ.range = ⊥ := by
    by_contra hne
    have : Nontrivial φ.range := (nontrivial_iff_ne_bot _).2 hne
    exact Group.IsPerfect.not_isNilpotent φ.range hpg.isNilpotent
  apply not_isSolvable_of_simple hs
  have hYt : Y = ⊤ := by
    rw [eq_top_iff]
    intro g _
    apply hφ
    rw [MonoidHom.mem_ker]
    have : φ g ∈ φ.range := ⟨g, rfl⟩
    rwa [hbot, mem_bot] at this
  haveI := hYs
  exact solvable_of_surjective (f := Y.subtype) fun g => ⟨⟨g, hYt ▸ mem_top g⟩, rfl⟩

end Reducible

end CFSG.LocalAnalysis.UniquenessCase.UC6.K318
