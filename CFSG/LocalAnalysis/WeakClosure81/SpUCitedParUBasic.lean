module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearSchreier
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

private theorem spUCited_norm_mul_mem_traceZero (h : UnitaryFieldData p f K) (μ : K) {c : K}
    (hc : c ∈ h.traceZero) : h.norm μ * c ∈ h.traceZero := by
  rw [UnitaryFieldData.mem_traceZero, UnitaryFieldData.trace] at hc ⊢
  rw [map_mul, (UnitaryFieldData.mem_fixedField h).mp (h.norm_mem_fixedField μ), ← mul_add, hc,
    mul_zero]

private theorem spUCited_exists_hypForm_eq_one (h : UnitaryFieldData p f K)
    {v : HypIndex r ε → K} (hv0 : v ≠ 0) : ∃ x, hypForm h r ε v x = 1 := by
  obtain ⟨y, hy⟩ : ∃ y, hypForm h r ε v y ≠ 0 := by
    by_contra hz
    have hz' : ∀ y, hypForm h r ε v y = 0 := fun y => not_not.mp (not_exists.mp hz y)
    exact hv0 ((hypForm_separatingLeft h) v hz')
  exact ⟨(hypForm h r ε v y)⁻¹ • y, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hy]⟩

private theorem spUCited_exists_mem_hypSU_hermTransvection (h : UnitaryFieldData p f K)
    {v : HypIndex r ε → K} (hv : hypForm h r ε v v = 0) {c : K} (hc : c ∈ h.traceZero) :
    ∃ g : hypSU h r ε,
      mulVecLin (((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K)) =
        hermTransvection (hypForm h r ε) v c := by
  set T := hermTransvection (hypForm h r ε) v c
  set M : Matrix (HypIndex r ε) (HypIndex r ε) K := LinearMap.toMatrix' T
  have hMT : mulVecLin M = T := by
    rw [← Matrix.toLin'_apply', Matrix.toLin'_toMatrix']
  have hdet : M.det = 1 := by
    rw [← LinearMap.det_toLin', Matrix.toLin'_toMatrix']
    exact det_hermTransvection _ hv c
  let A : GL (HypIndex r ε) K :=
    GeneralLinearGroup.mkOfDetNeZero M (by rw [hdet]; exact one_ne_zero)
  have hc' : c + h.bar c = 0 := (h.mem_traceZero).mp hc
  have hA : A ∈ hypSU h r ε := by
    refine (mem_gramSU_iff_isometry (h := h) (G := hypGram r ε K)).mpr ⟨?_, hdet⟩
    intro x y
    have hx : (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ x = T x := by
      rw [← hMT]; rfl
    have hy : (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ y = T y := by
      rw [← hMT]; rfl
    rw [hx, hy]
    exact hermTransvection_isometry (hypForm_isSymm h) hv hc' x y
  exact ⟨⟨A, hA⟩, hMT⟩

private theorem spUCited_hypSU_ext_mulVecLin {h : UnitaryFieldData p f K}
    {g g' : hypSU h r ε}
    (hgg : mulVecLin (((g : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K)) =
      mulVecLin (((g' : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K))) : g = g' :=
  Subtype.ext (Units.ext (Matrix.toLin'.injective (by
    rw [Matrix.toLin'_apply', Matrix.toLin'_apply', hgg])))

private theorem spUCited_mulVecLin_conj (h : UnitaryFieldData p f K) (g z : ↥(hypSU h r ε))
    {v : HypIndex r ε → K} {c : K}
    (hz : mulVecLin ((z : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
      hermTransvection (hypForm h r ε) v c) :
    mulVecLin (((g * z * g⁻¹ : ↥(hypSU h r ε)) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) =
      hermTransvection (hypForm h r ε)
        (((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ v) c := by
  have hIso : ∀ x y, hypForm h r ε
      (((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ x)
      (((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ y) =
      hypForm h r ε x y :=
    ((mem_gramSU_iff_isometry (h := h) (G := hypGram r ε K)).mp g.2).1
  have hMul : ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *
      (((g⁻¹ : ↥(hypSU h r ε)) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) = 1 := by
    rw [← Units.val_mul, Subgroup.coe_inv, mul_inv_cancel, Units.val_one]
  have hcoe : ((g * z * g⁻¹ : ↥(hypSU h r ε)) : GL (HypIndex r ε) K) =
      (g : GL (HypIndex r ε) K) * (z : GL (HypIndex r ε) K) *
        ((g⁻¹ : ↥(hypSU h r ε)) : GL (HypIndex r ε) K) := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  apply LinearMap.ext
  intro x
  rw [Matrix.mulVecLin_apply, hermTransvection_apply, hcoe, Units.val_mul, Units.val_mul,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [show ((z : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ
        ((((g⁻¹ : ↥(hypSU h r ε)) : GL (HypIndex r ε) K) :
          Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ x) =
      hermTransvection (hypForm h r ε) v c
        ((((g⁻¹ : ↥(hypSU h r ε)) : GL (HypIndex r ε) K) :
          Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ x) by
    rw [← Matrix.mulVecLin_apply, hz]]
  rw [hermTransvection_apply, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
    hMul, Matrix.one_mulVec]
  rw [show hypForm h r ε v
        ((((g⁻¹ : ↥(hypSU h r ε)) : GL (HypIndex r ε) K) :
          Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ x) =
      hypForm h r ε (((g : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ v) x by
    have hI := hIso v ((((g⁻¹ : ↥(hypSU h r ε)) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ x)
    rw [show ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ
          ((((g⁻¹ : ↥(hypSU h r ε)) : GL (HypIndex r ε) K) :
            Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ x) = x by
      rw [Matrix.mulVec_mulVec, hMul, Matrix.one_mulVec]] at hI
    exact hI.symm]

@[expose] noncomputable def uCitedRoot (h : UnitaryFieldData p f K) (r ε : ℕ)
    (v : HypIndex r ε → K) : Subgroup ↥(hypSU h r ε) :=
  Subgroup.closure {g | ∃ c ∈ h.traceZero,
    mulVecLin ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
      hermTransvection (hypForm h r ε) v c}

theorem hypForm_single_inl_self (h : UnitaryFieldData p f K) (i : Fin r) :
    hypForm h r ε (Pi.single (Sum.inl i) (1 : K) : HypIndex r ε → K)
      (Pi.single (Sum.inl i) (1 : K)) = 0 := by
  rw [hypForm_single_inl]
  simp

theorem mem_uCitedRoot (h : UnitaryFieldData p f K) {v : HypIndex r ε → K}
    (hv : hypForm h r ε v v = 0) {x : ↥(hypSU h r ε)} :
    x ∈ uCitedRoot h r ε v ↔ ∃ c ∈ h.traceZero,
      mulVecLin ((x : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
        hermTransvection (hypForm h r ε) v c := by
  constructor
  · intro hx
    unfold uCitedRoot at hx
    refine Subgroup.closure_induction (k := {g : ↥(hypSU h r ε) |
        ∃ c ∈ h.traceZero,
          mulVecLin ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
            hermTransvection (hypForm h r ε) v c})
      (p := fun x _ => ∃ c ∈ h.traceZero,
        mulVecLin ((x : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
          hermTransvection (hypForm h r ε) v c) ?_ ?_ ?_ ?_ hx
    · rintro y ⟨c, hc, hyc⟩
      exact ⟨c, hc, hyc⟩
    · exact ⟨0, h.traceZero.zero_mem, by
        rw [Subgroup.coe_one, Units.val_one, Matrix.mulVecLin_one, hermTransvection_zero]⟩
    · rintro y z hy hz ⟨c, hc, hyc⟩ ⟨d, hd, hyd⟩
      exact ⟨c + d, h.traceZero.add_mem hc hd, by
        rw [Subgroup.coe_mul, Units.val_mul, Matrix.mulVecLin_mul, hyc, hyd,
          hermTransvection_comp _ hv c d]⟩
    · rintro y hy ⟨c, hc, hyc⟩
      obtain ⟨y', hy'⟩ := spUCited_exists_mem_hypSU_hermTransvection h hv (h.traceZero.neg_mem hc)
      refine ⟨-c, h.traceZero.neg_mem hc, ?_⟩
      have hxy : y * y' = 1 := spUCited_hypSU_ext_mulVecLin (g := y * y') (g' := 1) (by
        rw [Subgroup.coe_mul, Units.val_mul, Matrix.mulVecLin_mul, hyc, hy',
          hermTransvection_comp _ hv c (-c), add_neg_cancel, hermTransvection_zero,
          Subgroup.coe_one, Units.val_one, Matrix.mulVecLin_one])
      rw [inv_eq_of_mul_eq_one_right hxy]
      exact hy'
  · rintro ⟨c, hc, hxc⟩
    exact Subgroup.subset_closure ⟨c, hc, hxc⟩

theorem uCitedRoot_smul (h : UnitaryFieldData p f K) {v : HypIndex r ε → K}
    (hv : hypForm h r ε v v = 0) {μ : K} (hμ : μ ≠ 0) :
    uCitedRoot h r ε (μ • v) = uCitedRoot h r ε v := by
  have htrans := (hermitian_unitary_transvection h (hypForm_isSymm h) hv).2.2.2.2.2
  have hNμ : h.norm μ ≠ 0 := by
    rw [UnitaryFieldData.norm]
    exact mul_ne_zero hμ (mt (h.bar_eq_zero_iff).mp hμ)
  apply le_antisymm
  · rw [uCitedRoot, Subgroup.closure_le]
    rintro x ⟨c, hc, hxc⟩
    exact Subgroup.subset_closure
      ⟨h.norm μ * c, spUCited_norm_mul_mem_traceZero h μ hc, by rw [hxc, htrans c hc μ]⟩
  · rw [uCitedRoot, Subgroup.closure_le]
    rintro x ⟨c, hc, hxc⟩
    refine Subgroup.subset_closure ⟨(h.norm μ)⁻¹ * c, ?_, ?_⟩
    · rw [← norm_inv_eq h μ]
      exact spUCited_norm_mul_mem_traceZero h μ⁻¹ hc
    · rw [hxc, htrans ((h.norm μ)⁻¹ * c)
        (by rw [← norm_inv_eq h μ]; exact spUCited_norm_mul_mem_traceZero h μ⁻¹ hc) μ,
        ← mul_assoc, mul_inv_cancel₀ hNμ, one_mul]

theorem exists_smul_of_uCitedRoot_eq (h : UnitaryFieldData p f K) {v w : HypIndex r ε → K}
    (hv0 : v ≠ 0) (hw0 : w ≠ 0) (hv : hypForm h r ε v v = 0) (hw : hypForm h r ε w w = 0)
    (hvw : uCitedRoot h r ε v = uCitedRoot h r ε w) : ∃ μ : K, w = μ • v := by
  obtain ⟨τ, hτ, hτ0⟩ := h.exists_mem_traceZero_ne_zero
  obtain ⟨xw, hxw⟩ := spUCited_exists_mem_hypSU_hermTransvection h hw hτ
  have hxw_mem : xw ∈ uCitedRoot h r ε w := (mem_uCitedRoot h hw).mpr ⟨τ, hτ, hxw⟩
  have hxw_mem_v : xw ∈ uCitedRoot h r ε v := by rw [hvw]; exact hxw_mem
  obtain ⟨d, hd, hxd⟩ := (mem_uCitedRoot h hv).mp hxw_mem_v
  have htrans : hermTransvection (hypForm h r ε) w τ =
      hermTransvection (hypForm h r ε) v d := by rw [← hxw, hxd]
  obtain ⟨x, hx⟩ := spUCited_exists_hypForm_eq_one h hw0
  have h1 := LinearMap.congr_fun htrans x
  rw [hermTransvection_apply, hermTransvection_apply, hx, mul_one] at h1
  have h2 : τ • w = (d * hypForm h r ε v x) • v := add_left_cancel h1
  have hw_eq : w = τ⁻¹ • (τ • w) := by rw [smul_smul, inv_mul_cancel₀ hτ0, one_smul]
  refine ⟨τ⁻¹ * (d * hypForm h r ε v x), ?_⟩
  rw [hw_eq, h2, smul_smul]

theorem map_conj_uCitedRoot (h : UnitaryFieldData p f K) (g : ↥(hypSU h r ε))
    {v : HypIndex r ε → K} (hv : hypForm h r ε v v = 0) :
    (uCitedRoot h r ε v).map (MulAut.conj g).toMonoidHom =
      uCitedRoot h r ε
        (((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ v) := by
  set gv : HypIndex r ε → K :=
    (((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ v) with hgv
  rw [uCitedRoot, MonoidHom.map_closure, uCitedRoot]
  congr 1
  ext y
  constructor
  · rintro ⟨z, hzmem, hzy⟩
    obtain ⟨c, hc, hz⟩ := hzmem
    refine ⟨c, hc, ?_⟩
    rw [← hzy, show (MulAut.conj g).toMonoidHom z = g * z * g⁻¹ from MulAut.conj_apply g z]
    exact spUCited_mulVecLin_conj h g z hz
  · rintro ⟨c, hc, hy⟩
    refine ⟨g⁻¹ * y * g, ⟨c, hc, ?_⟩, ?_⟩
    · have hvback : (((g⁻¹ : ↥(hypSU h r ε)) : GL (HypIndex r ε) K) :
          Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ gv = v := by
        rw [hgv, Matrix.mulVec_mulVec]
        have h1 : (((g⁻¹ : ↥(hypSU h r ε)) : GL (HypIndex r ε) K) :
              Matrix (HypIndex r ε) (HypIndex r ε) K) *
            ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) = 1 := by
          rw [← Units.val_mul, Subgroup.coe_inv, inv_mul_cancel, Units.val_one]
        rw [h1, Matrix.one_mulVec]
      have hz := spUCited_mulVecLin_conj h g⁻¹ y (v := gv) (c := c) hy
      rw [hvback] at hz
      simpa only [inv_inv] using hz
    · change MulAut.conj g (g⁻¹ * y * g) = y
      rw [MulAut.conj_apply]
      group

theorem card_uCitedRoot (h : UnitaryFieldData p f K) {v : HypIndex r ε → K} (hv0 : v ≠ 0)
    (hv : hypForm h r ε v v = 0) :
    Nat.card (uCitedRoot h r ε v) = Nat.card h.traceZero := by
  let f : h.traceZero → uCitedRoot h r ε v := fun c =>
    ⟨Classical.choose (spUCited_exists_mem_hypSU_hermTransvection h hv c.2),
      (mem_uCitedRoot h hv).mpr ⟨(c : K), c.2,
        Classical.choose_spec (spUCited_exists_mem_hypSU_hermTransvection h hv c.2)⟩⟩
  have hf_inj : Function.Injective f := by
    intro c d hcd
    have hcd' : Classical.choose (spUCited_exists_mem_hypSU_hermTransvection h hv c.2) =
        Classical.choose (spUCited_exists_mem_hypSU_hermTransvection h hv d.2) :=
      congrArg Subtype.val hcd
    have hlin : hermTransvection (hypForm h r ε) v (c : K) =
        hermTransvection (hypForm h r ε) v (d : K) := by
      rw [← Classical.choose_spec (spUCited_exists_mem_hypSU_hermTransvection h hv c.2),
        ← Classical.choose_spec (spUCited_exists_mem_hypSU_hermTransvection h hv d.2), hcd']
    obtain ⟨x, hx⟩ := spUCited_exists_hypForm_eq_one h hv0
    have h1 := LinearMap.congr_fun hlin x
    rw [hermTransvection_apply, hermTransvection_apply, hx, mul_one, mul_one] at h1
    have h2 : (c : K) • v = (d : K) • v := add_left_cancel h1
    have hcd0 : (c - d : K) • v = 0 := by rw [sub_smul, h2, sub_self]
    have hcdz : (c : K) - d = 0 := by
      rcases smul_eq_zero.mp hcd0 with h0 | h0
      · exact h0
      · exact absurd h0 hv0
    exact Subtype.ext (sub_eq_zero.mp hcdz)
  have hf_surj : Function.Surjective f := by
    intro y
    obtain ⟨c, hc, hyc⟩ := (mem_uCitedRoot h hv).mp y.2
    refine ⟨⟨c, hc⟩, ?_⟩
    apply Subtype.ext
    apply spUCited_hypSU_ext_mulVecLin
    dsimp only [f]
    rw [Classical.choose_spec (spUCited_exists_mem_hypSU_hermTransvection h hv hc), hyc]
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩)).symm

end CFSG.LocalAnalysis.WeakClosure81

end
