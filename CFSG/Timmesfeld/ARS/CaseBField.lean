module

public import CFSG.Timmesfeld.ARS.CaseBRankOne

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement Pointwise
open CFSG.LieType.Universal Matrix

namespace CaseB

variable {G : Type} [Group G] {R : Set (Subgroup G)} {F : Type} [Field F]
  {Ψ : SpecialLinearGroup (Fin 4) F →* G}

theorem ne01 : (0 : Fin 4) ≠ 1 := by decide

theorem ne02 : (0 : Fin 4) ≠ 2 := by decide

theorem ne03 : (0 : Fin 4) ≠ 3 := by decide

theorem ne10 : (1 : Fin 4) ≠ 0 := by decide

theorem ne12 : (1 : Fin 4) ≠ 2 := by decide

theorem ne13 : (1 : Fin 4) ≠ 3 := by decide

theorem ne20 : (2 : Fin 4) ≠ 0 := by decide

theorem ne21 : (2 : Fin 4) ≠ 1 := by decide

theorem ne23 : (2 : Fin 4) ≠ 3 := by decide

theorem ne30 : (3 : Fin 4) ≠ 0 := by decide

theorem ne31 : (3 : Fin 4) ≠ 1 := by decide

theorem ne32 : (3 : Fin 4) ≠ 2 := by decide

variable (Ψ) in
noncomputable abbrev xs {a b : Fin 4} (h : a ≠ b) (s : F) : G :=
  Ψ (SpecialLinearGroup.transvection h s)

theorem xs_add {a b : Fin 4} (h : a ≠ b) (s t : F) : xs Ψ h (s + t) = xs Ψ h s * xs Ψ h t := by
  rw [xs, SpecialLinearGroup.transvection_add, map_mul]

theorem xs_zero {a b : Fin 4} (h : a ≠ b) : xs Ψ h 0 = 1 := by
  rw [xs, SpecialLinearGroup.transvection_coeff_zero, map_one]

theorem xs_mem {a b : Fin 4} (h : a ≠ b) (s : F) : xs Ψ h s ∈ xg Ψ a b :=
  ⟨_, transvection_mem_X h s, rfl⟩

theorem mem_xg_iff {a b : Fin 4} (h : a ≠ b) {g : G} : g ∈ xg Ψ a b ↔ ∃ s, xs Ψ h s = g := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨s, rfl⟩ := (mem_X h).1 hx
    exact ⟨s, rfl⟩
  · rintro ⟨s, rfl⟩
    exact xs_mem h s

theorem xs_injective (hS : Skel R Ψ) {a b : Fin 4} (h : a ≠ b) :
    Function.Injective (xs Ψ h) :=
  hS.inj.comp (SpecialLinearGroup.transvection_injective h)

@[expose] def emb2 {a b : Fin 4} (h : a ≠ b) : Fin 2 ↪ Fin 4 :=
  ⟨![a, b], fun x y hxy => by
    fin_cases x <;> fin_cases y
    · rfl
    · exact absurd hxy h
    · exact absurd hxy.symm h
    · rfl⟩

theorem emb2_zero {a b : Fin 4} (h : a ≠ b) : emb2 h 0 = a := rfl

theorem emb2_one {a b : Fin 4} (h : a ≠ b) : emb2 h 1 = b := rfl

@[expose] noncomputable def bHom {a b : Fin 4} (h : a ≠ b) :
    SpecialLinearGroup (Fin 2) F →* SpecialLinearGroup (Fin 4) F where
  toFun A := ⟨Linear.blockMat F (emb2 h) (A : Matrix (Fin 2) (Fin 2) F), by
    rw [Linear.det_blockMat]
    exact A.2⟩
  map_one' := Subtype.ext (by
    change Linear.blockMat F (emb2 h)
      ((1 : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1
    rw [Matrix.SpecialLinearGroup.coe_one, Linear.blockMat_one])
  map_mul' A B := Subtype.ext (by
    change Linear.blockMat F (emb2 h)
        ((A * B : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      Linear.blockMat F (emb2 h) (A : Matrix (Fin 2) (Fin 2) F) *
        Linear.blockMat F (emb2 h) (B : Matrix (Fin 2) (Fin 2) F)
    rw [Matrix.SpecialLinearGroup.coe_mul, Linear.blockMat_mul])

theorem coe_bHom {a b : Fin 4} (h : a ≠ b) (A : SpecialLinearGroup (Fin 2) F) :
    ((bHom h A : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      Linear.blockMat F (emb2 h) (A : Matrix (Fin 2) (Fin 2) F) := rfl

theorem bHom_injective {a b : Fin 4} (h : a ≠ b) :
    Function.Injective (bHom (F := F) h) := fun _ _ e =>
  Subtype.ext (Linear.blockMat_injective F (emb2 h) (congrArg Subtype.val e))

theorem bHom_tv {a b : Fin 4} (h : a ≠ b) {p q : Fin 2} (hpq : p ≠ q) (t : F) :
    bHom h (tv p q t) = SpecialLinearGroup.transvection ((emb2 h).injective.ne hpq) t := by
  refine Subtype.ext ?_
  rw [coe_bHom, tv_of_ne hpq]
  exact Linear.blockMat_transvection F (emb2 h) t

variable (Ψ) in
noncomputable abbrev blk {a b : Fin 4} (h : a ≠ b) : SpecialLinearGroup (Fin 2) F →* G :=
  Ψ.comp (bHom h)

theorem blk_tv01 {a b : Fin 4} (h : a ≠ b) (t : F) : blk Ψ h (tv 0 1 t) = xs Ψ h t := by
  rw [MonoidHom.comp_apply, bHom_tv h (by decide)]
  rfl

theorem blk_tv10 {a b : Fin 4} (h : a ≠ b) (t : F) : blk Ψ h (tv 1 0 t) = xs Ψ h.symm t := by
  rw [MonoidHom.comp_apply, bHom_tv h (by decide)]
  rfl

theorem blk_injective (hS : Skel R Ψ) {a b : Fin 4} (h : a ≠ b) :
    Function.Injective (blk Ψ h) :=
  hS.inj.comp (bHom_injective h)

theorem map_blk_upper {a b : Fin 4} (h : a ≠ b) : (upperUnipotent F).map (blk Ψ h) = xg Ψ a b := by
  refine SetLike.coe_injective ?_
  rw [← Linear.range_tv_upper]
  ext g
  simp only [Set.mem_range, SetLike.mem_coe, blk_tv01, mem_xg_iff h]

theorem map_blk_lower {a b : Fin 4} (h : a ≠ b) : (lowerUnipotent F).map (blk Ψ h) = xg Ψ b a := by
  refine SetLike.coe_injective ?_
  rw [← Linear.range_tv_lower]
  ext g
  simp only [Set.mem_range, SetLike.mem_coe, blk_tv10, mem_xg_iff h.symm]

theorem exists_blockIso (hS : Skel R Ψ) {a b : Fin 4} (h : a ≠ b) :
    ∃ φ : ↥(xg Ψ a b ⊔ xg Ψ b a) ≃* SpecialLinearGroup (Fin 2) F,
      ((xg Ψ a b).subgroupOf (xg Ψ a b ⊔ xg Ψ b a)).map φ.toMonoidHom = upperUnipotent F ∧
      ((xg Ψ b a).subgroupOf (xg Ψ a b ⊔ xg Ψ b a)).map φ.toMonoidHom = lowerUnipotent F ∧
      ∀ g, (φ.symm g : G) = blk Ψ h g :=
  Linear.exists_mulEquiv_of_injective (blk_injective hS h) (map_blk_upper h) (map_blk_lower h)

@[expose] def torVec {a b : Fin 4} (_h : a ≠ b) (c : Fˣ) (k : Fin 4) : F :=
  if k = a then (c : F) else if k = b then ((c⁻¹ : Fˣ) : F) else 1

theorem coe_bHom_diagElt {a b : Fin 4} (h : a ≠ b) (c : Fˣ) :
    ((bHom h (NaturalModule.diagElt c) : SpecialLinearGroup (Fin 4) F) :
      Matrix (Fin 4) (Fin 4) F) = diagonal (torVec h c) := by
  rw [coe_bHom, NaturalModule.coe_diagElt]
  refine Linear.ext_embEquiv (emb2 h) fun p q => ?_
  rw [Linear.blockMat_apply]
  rcases p with p | ⟨x, hx⟩ <;> rcases q with q | ⟨y, hy⟩
  · rw [Linear.embEquiv_inl, Linear.embEquiv_inl, Matrix.fromBlocks_apply₁₁]
    fin_cases p <;> fin_cases q <;>
      simp [emb2_zero, emb2_one, torVec, h.symm, diagonal_apply_ne _ h]
  · have hne : ∀ r, emb2 h r ≠ y := fun r e => hy ⟨r, e⟩
    rw [Linear.embEquiv_inl, Linear.embEquiv_inr, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply,
      diagonal_apply_ne _ (hne p)]
  · have hne : ∀ r, emb2 h r ≠ x := fun r e => hx ⟨r, e⟩
    rw [Linear.embEquiv_inl, Linear.embEquiv_inr, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply,
      diagonal_apply_ne _ (Ne.symm (hne q))]
  · have hxa : x ≠ a := fun e => hx ⟨0, e.symm⟩
    have hxb : x ≠ b := fun e => hx ⟨1, e.symm⟩
    rw [Linear.embEquiv_inr, Linear.embEquiv_inr, Matrix.fromBlocks_apply₂₂]
    by_cases hxy : x = y
    · subst hxy
      simp [torVec, hxa, hxb]
    · rw [diagonal_apply_ne _ hxy, Matrix.one_apply_ne (fun e => hxy (congrArg Subtype.val e))]

theorem torBlk_conj_xs {a b : Fin 4} (h : a ≠ b) (c : Fˣ) {i j : Fin 4} (hij : i ≠ j) (s : F) :
    blk Ψ h (NaturalModule.diagElt c) * xs Ψ hij s * (blk Ψ h (NaturalModule.diagElt c))⁻¹ =
      xs Ψ hij (torVec h c i * s * (torVec h c j)⁻¹) := by
  rw [xs, xs, MonoidHom.comp_apply, ← map_inv, ← map_mul, ← map_mul,
    SpecialLinear.conj_transvection_of_coe_eq_diagonal (coe_bHom_diagElt h c) hij s]

theorem torVec_ne_zero {a b : Fin 4} (h : a ≠ b) (c : Fˣ) (k : Fin 4) : torVec h c k ≠ 0 := by
  unfold torVec
  split_ifs
  exacts [c.ne_zero, (c⁻¹).ne_zero, one_ne_zero]

theorem conjSub_xg_blk {a b : Fin 4} (h : a ≠ b) (c : Fˣ) {i j : Fin 4} (hij : i ≠ j) :
    conjSub (xg Ψ i j) (blk Ψ h (NaturalModule.diagElt c)) = xg Ψ i j := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨s, rfl⟩ := (mem_xg_iff hij).1 hx
    change blk Ψ h (NaturalModule.diagElt c) * xs Ψ hij s *
      (blk Ψ h (NaturalModule.diagElt c))⁻¹ ∈ _
    rw [torBlk_conj_xs]
    exact xs_mem _ _
  · intro hg
    obtain ⟨s, rfl⟩ := (mem_xg_iff hij).1 hg
    refine ⟨xs Ψ hij ((torVec h c i)⁻¹ * s * torVec h c j), xs_mem _ _, ?_⟩
    change blk Ψ h (NaturalModule.diagElt c) * _ * (blk Ψ h (NaturalModule.diagElt c))⁻¹ = _
    rw [torBlk_conj_xs]
    congr 1
    have hi := torVec_ne_zero h c i
    have hj := torVec_ne_zero h c j
    field_simp

theorem conjSub_hidAt_blk (hR : IsRootClass R) {a b : Fin 4} (h : a ≠ b) (c : Fˣ)
    {s₁ s₂ t₁ t₂ : Fin 4} (h12 : s₁ ≠ s₂) (h34 : t₁ ≠ t₂) (h14 : s₁ ≠ t₂) (h23 : s₂ ≠ t₁) :
    conjSub (hidAt R Ψ s₁ s₂ t₁ t₂) (blk Ψ h (NaturalModule.diagElt c)) =
      hidAt R Ψ s₁ s₂ t₁ t₂ :=
  conjSub_hidAt_of hR (fun _ _ hab => conjSub_xg_blk h c hab) h12 h34 h14 h23

theorem blk_mem_sup {a b : Fin 4} (h : a ≠ b) (g : SpecialLinearGroup (Fin 2) F) :
    blk Ψ h g ∈ xg Ψ a b ⊔ xg Ψ b a := by
  have : g ∈ upperUnipotent F ⊔ lowerUnipotent F := by
    rw [NaturalModule.upperUnipotent_sup_lowerUnipotent]
    exact Subgroup.mem_top g
  rw [← map_blk_upper h, ← map_blk_lower h, ← Subgroup.map_sup]
  exact Subgroup.mem_map_of_mem _ this

theorem blk03_inv_mul_blk02 (c : Fˣ) :
    (blk Ψ ne03 (NaturalModule.diagElt c))⁻¹ *
        blk Ψ ne02 (NaturalModule.diagElt c) =
      blk Ψ ne23 (NaturalModule.diagElt c⁻¹) := by
  have e : (bHom (F := F) ne03 (NaturalModule.diagElt c))⁻¹ *
      bHom ne02 (NaturalModule.diagElt c) =
      bHom ne23 (NaturalModule.diagElt c⁻¹) := by
    rw [← map_inv, NaturalModule.diagElt_inv]
    refine Subtype.ext ?_
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_bHom_diagElt, coe_bHom_diagElt, coe_bHom_diagElt,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext k
    fin_cases k <;> simp [torVec]
  simp only [blk, MonoidHom.comp_apply]
  rw [← map_inv, ← map_mul, e]

section LinParam

variable (h : Hyp G R) {X X₀ : Subgroup G} (hX : X ∈ R) (hX₀ : X₀ ∈ omegaSet R X)
  {K : Type*} [Field K] [Finite K] [CharP K 2] {φ : ↥(X ⊔ X₀) ≃* SpecialLinearGroup (Fin 2) K}
  (hφA : (X.subgroupOf (X ⊔ X₀)).map φ.toMonoidHom = upperUnipotent K)
include h hX hX₀ hφA

theorem exists_linParam {H : Subgroup G} (hHM : H ≤ M R X) (hHX : H ⊓ X = ⊥)
    (hH : ∀ c : Kˣ, conjSub H (FrameSL3.torPar φ c) = H) :
    ∃ (e : ℕ) (ι : (Fin e → K) → G), (∀ v w, ι (v + w) = ι v * ι w) ∧
      Function.Injective ι ∧ (∀ v, ι v ∈ H) ∧ (∀ x ∈ H, ∃ v, ι v = x) ∧
      ∀ (c : Kˣ) v, FrameSL3.torPar φ c * ι v * (FrameSL3.torPar φ c)⁻¹ = ι ((c : K) • v) := by
  set V := Sec8Field.submodule h hX hX₀ φ hφA H hH
  have huniq : ∀ m₁ m₂ : ↥(M R X), (m₁ : G) ∈ H → (m₂ : G) ∈ H →
      Sec8Field.mk h hX hX₀ φ hφA m₁ = Sec8Field.mk h hX hX₀ φ hφA m₂ → m₁ = m₂ := by
    intro m₁ m₂ h1 h2 e
    have he : Sec8Field.mk h hX hX₀ φ hφA (m₁⁻¹ * m₂) = 0 := by
      rw [Sec8Field.mk_mul, Sec8Field.mk_inv, e, neg_add_cancel]
    rw [Sec8Field.mk_eq_zero_iff] at he
    have hmem : ((m₁⁻¹ * m₂ : ↥(M R X)) : G) ∈ H ⊓ X :=
      ⟨by simpa using H.mul_mem (H.inv_mem h1) h2, he⟩
    rw [hHX, Subgroup.mem_bot] at hmem
    have : m₁⁻¹ * m₂ = 1 := Subtype.ext hmem
    exact (inv_mul_eq_one.1 this)
  have hpre : ∀ v : V, ∃ m : ↥(M R X), (m : G) ∈ H ∧ Sec8Field.mk h hX hX₀ φ hφA m = v :=
    fun v => (Sec8Field.mem_submodule h hX hX₀ φ hφA).1 v.2
  choose pre hpreH hpremk using hpre
  set e := Module.finrank K V
  let b : Module.Basis (Fin e) K V := Module.finBasisOfFinrankEq K V rfl
  let ι : (Fin e → K) → G := fun x => (pre (∑ i, x i • b i) : G)
  refine ⟨e, ι, fun v w => ?_, fun v w hvw => ?_, fun v => hpreH _, fun x hx => ?_,
    fun c v => ?_⟩
  · have key := huniq (pre (∑ i, (v + w) i • b i)) (pre (∑ i, v i • b i) * pre (∑ i, w i • b i))
      (hpreH _) (H.mul_mem (hpreH _) (hpreH _))
      (by
        rw [Sec8Field.mk_mul, hpremk, hpremk, hpremk]
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, Submodule.coe_add])
    exact congrArg Subtype.val key
  · have h1 : Sec8Field.mk h hX hX₀ φ hφA (pre (∑ i, v i • b i)) =
        Sec8Field.mk h hX hX₀ φ hφA (pre (∑ i, w i • b i)) :=
      congrArg _ (Subtype.ext hvw)
    rw [hpremk, hpremk] at h1
    have h2 : (∑ i, v i • b i) = ∑ i, w i • b i := Subtype.ext h1
    have := congrArg b.repr h2
    simp only [map_sum, map_smul, Module.Basis.repr_self, Finsupp.smul_single, smul_eq_mul,
      mul_one] at this
    funext i
    have := congrArg (fun f => f i) this
    simpa [Finsupp.finsetSum_apply, Finsupp.single_apply] using this
  · have hxM := hHM hx
    let m : ↥(M R X) := ⟨x, hxM⟩
    have hv : Sec8Field.mk h hX hX₀ φ hφA m ∈ V := (Sec8Field.mem_submodule h hX hX₀ φ hφA).2
      ⟨m, hx, rfl⟩
    refine ⟨fun i => b.repr ⟨_, hv⟩ i, ?_⟩
    have e1 : (∑ i, (fun i => b.repr ⟨_, hv⟩ i) i • b i) = ⟨_, hv⟩ := b.sum_repr _
    have key := huniq (pre (∑ i, (fun i => b.repr ⟨_, hv⟩ i) i • b i)) m (hpreH _) hx
      (by rw [hpremk, e1])
    exact congrArg Subtype.val key
  · have hm : ((Sec8Field.conjM h.root hφA c (pre (∑ i, v i • b i)) : ↥(M R X)) : G) ∈ H := by
      rw [Sec8Field.coe_conjM, ← hH c]
      exact conj_mem_conjSub _ (hpreH _)
    have key := huniq (Sec8Field.conjM h.root hφA c (pre (∑ i, v i • b i)))
      (pre (∑ i, ((c : K) • v) i • b i)) hm (hpreH _)
      (by
        rw [← Sec8Field.smul_mk, hpremk, hpremk]
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, Submodule.coe_smul])
    rw [← Sec8Field.coe_conjM h.root hφA c]
    exact congrArg Subtype.val key

end LinParam

variable (R Ψ) in
@[expose] noncomputable def Qc (u : G) : F :=
  Classical.epsilon fun s : F =>
    (xs Ψ ne02 s)⁻¹ * ⁅xs Ψ ne13 1, u⁆ ∈
      hid R Ψ

variable (R Ψ) in
@[expose] noncomputable def Lc (u : G) : G :=
  (xs Ψ ne02 (Qc R Ψ u))⁻¹ * ⁅xs Ψ ne13 1, u⁆

section Commutator

variable [CharP F 2] (h : Hyp G R) (hS : Skel R Ψ)
include h hS

theorem Lc_mem {u : G} (hu : u ∈ hU R Ψ) : Lc R Ψ u ∈ hid R Ψ := by
  obtain ⟨c, hc, hn⟩ := exists_commutator_eq h hS (xs_mem (Ψ := Ψ) ne13 1) hu
  obtain ⟨s, rfl⟩ := (mem_xg_iff ne02).1 hc
  exact Classical.epsilon_spec (p := fun s : F => (xs Ψ ne02 s)⁻¹ *
    ⁅xs Ψ ne13 1, u⁆ ∈ hid R Ψ) ⟨s, hn⟩

omit [CharP F 2] h hS in
theorem commutator_eq_xs_mul_Lc (u : G) :
    ⁅xs Ψ ne13 1, u⁆ =
      xs Ψ ne02 (Qc R Ψ u) * Lc R Ψ u := by
  rw [Lc]
  group

theorem eq_Qc_of_mem {u : G} (hu : u ∈ hU R Ψ) {s : F}
    (hs : (xs Ψ ne02 s)⁻¹ * ⁅xs Ψ ne13 1, u⁆ ∈
      hid R Ψ) : s = Qc R Ψ u := by
  have hL := Lc_mem h hS hu
  rw [Lc] at hL
  have hmem : (xs Ψ ne02 (Qc R Ψ u))⁻¹ * xs Ψ ne02 s ∈
      hid R Ψ ⊓ xg Ψ 0 2 := by
    refine ⟨?_, Subgroup.mul_mem _ (Subgroup.inv_mem _ (xs_mem _ _)) (xs_mem _ _)⟩
    have e : (xs Ψ ne02 (Qc R Ψ u))⁻¹ * xs Ψ ne02 s =
        ((xs Ψ ne02 (Qc R Ψ u))⁻¹ *
          ⁅xs Ψ ne13 1, u⁆) *
          ((xs Ψ ne02 s)⁻¹ * ⁅xs Ψ ne13 1, u⁆)⁻¹ := by
      group
    rw [e]
    exact Subgroup.mul_mem _ hL (Subgroup.inv_mem _ hs)
  rw [hid_inf_02 h hS, Subgroup.mem_bot, inv_mul_eq_one] at hmem
  exact (xs_injective hS _ hmem).symm

omit [CharP F 2] h hS in
theorem blk03_conj_13 (c : Fˣ) (t : F) :
    blk Ψ ne03 (NaturalModule.diagElt c) * xs Ψ ne13 t * (blk Ψ ne03 (NaturalModule.diagElt c))⁻¹ =
      xs Ψ ne13 (t * c) := by
  rw [torBlk_conj_xs]
  congr 1
  simp [torVec]

omit [CharP F 2] h hS in
theorem blk03_conj_02 (c : Fˣ) (t : F) :
    blk Ψ ne03 (NaturalModule.diagElt c) * xs Ψ ne02 t * (blk Ψ ne03 (NaturalModule.diagElt c))⁻¹ =
      xs Ψ ne02 (c * t) := by
  rw [torBlk_conj_xs]
  congr 1
  simp [torVec]

omit [CharP F 2] h hS in
theorem blk02_conj_13 (c : Fˣ) (t : F) :
    blk Ψ ne02 (NaturalModule.diagElt c) * xs Ψ ne13 t * (blk Ψ ne02 (NaturalModule.diagElt c))⁻¹ =
      xs Ψ ne13 t := by
  rw [torBlk_conj_xs]
  congr 1
  simp [torVec]

omit [CharP F 2] h hS in
theorem blk02_conj_02 (c : Fˣ) (t : F) :
    blk Ψ ne02 (NaturalModule.diagElt c) * xs Ψ ne02 t * (blk Ψ ne02 (NaturalModule.diagElt c))⁻¹ =
      xs Ψ ne02 ((c : F) ^ 2 * t) := by
  rw [torBlk_conj_xs]
  congr 1
  simp [torVec]
  ring

theorem commute_blk03 (c : Fˣ) {u : G} (hu : u ∈ hU R Ψ) :
    Commute u (blk Ψ ne03 (NaturalModule.diagElt c)) := by
  have hle : xg Ψ 0 3 ⊔ xg Ψ 3 0 ≤ Subgroup.centralizer {u} := sup_le
    (fun x hx => Subgroup.mem_centralizer_singleton_iff.2
      (commuting_hU h hS ne03 (by decide) u hu x hx).symm)
    (fun x hx => Subgroup.mem_centralizer_singleton_iff.2
      (commuting_hU h hS ne30 (by decide) u hu x hx).symm)
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle (blk_mem_sup ne03 _))).symm

omit [CharP F 2] in
theorem blk03_conj_eq_blk02_conj (c : Fˣ) {n : G} (hn : n ∈ hid R Ψ) :
    blk Ψ ne03 (NaturalModule.diagElt c) * n * (blk Ψ ne03 (NaturalModule.diagElt c))⁻¹ =
      blk Ψ ne02 (NaturalModule.diagElt c) * n * (blk Ψ ne02 (NaturalModule.diagElt c))⁻¹ := by
  have hle : xg Ψ 2 3 ⊔ xg Ψ 3 2 ≤ Subgroup.centralizer {n} := sup_le
    (fun x hx => Subgroup.mem_centralizer_singleton_iff.2 (commuting_hid_23 n hn x hx).symm)
    (fun x hx => Subgroup.mem_centralizer_singleton_iff.2
      (commuting_hid_32 h hS n hn x hx).symm)
  have hz := Subgroup.mem_centralizer_singleton_iff.1
    (hle (blk_mem_sup ne23 (NaturalModule.diagElt c⁻¹)))
  rw [← blk03_inv_mul_blk02] at hz
  set a := blk Ψ ne03 (NaturalModule.diagElt c)
  set b := blk Ψ ne02 (NaturalModule.diagElt c)
  symm
  calc b * n * b⁻¹ = a * ((a⁻¹ * b) * n) * (a⁻¹ * b)⁻¹ * a⁻¹ := by group
    _ = a * (n * (a⁻¹ * b)) * (a⁻¹ * b)⁻¹ * a⁻¹ := by rw [hz]
    _ = a * n * a⁻¹ := by group

theorem Qc_Lc_blk02 (c : Fˣ) {u : G} (hu : u ∈ hU R Ψ) :
    Qc R Ψ (blk Ψ ne02 (NaturalModule.diagElt c) * u * (blk Ψ ne02 (NaturalModule.diagElt c))⁻¹) =
        (c : F) ^ 2 * Qc R Ψ u ∧
      Lc R Ψ (blk Ψ ne02 (NaturalModule.diagElt c) * u * (blk Ψ ne02 (NaturalModule.diagElt c))⁻¹) =
        blk Ψ ne02 (NaturalModule.diagElt c) * Lc R Ψ u *
          (blk Ψ ne02 (NaturalModule.diagElt c))⁻¹ := by
  set t := blk Ψ ne02 (NaturalModule.diagElt c) with ht
  have hu' : t * u * t⁻¹ ∈ hU R Ψ := by
    have := conj_mem_conjSub t hu
    rwa [ht, conjSub_hidAt_blk h.root ne02 c ne03 ne12 ne02 ne31] at this
  have hc' : t * xs Ψ ne13 1 * t⁻¹ = xs Ψ ne13 1 := blk02_conj_13 c 1
  have key : ⁅xs Ψ ne13 1, t * u * t⁻¹⁆ = xs Ψ ne02 ((c : F) ^ 2 * Qc R Ψ u) *
      (t * Lc R Ψ u * t⁻¹) := by
    have e1 : ⁅xs Ψ ne13 1, t * u * t⁻¹⁆ = t * ⁅xs Ψ ne13 1, u⁆ * t⁻¹ := by
      conv_lhs => rw [← hc']
      simp only [commutatorElement_def]
      group
    rw [e1, commutator_eq_xs_mul_Lc (R := R) u, ← blk02_conj_02 c, ← ht]
    group
  have hLmem : t * Lc R Ψ u * t⁻¹ ∈ hid R Ψ := by
    have := conj_mem_conjSub t (Lc_mem h hS hu)
    rwa [ht, conjSub_hidAt_blk h.root ne02 c ne01 ne23 ne03 ne12] at this
  have hQ : (c : F) ^ 2 * Qc R Ψ u = Qc R Ψ (t * u * t⁻¹) :=
    eq_Qc_of_mem h hS hu' (by rw [key]; simpa using hLmem)
  refine ⟨hQ.symm, ?_⟩
  rw [Lc, ← hQ, key]
  group

omit [CharP F 2] h hS in
theorem Qc_one (h : Hyp G R) (hS : Skel R Ψ) [CharP F 2] : Qc R Ψ (1 : G) = 0 := by
  refine (eq_Qc_of_mem h hS (Subgroup.one_mem _) (s := 0) ?_).symm
  rw [xs_zero, commutatorElement_one_right, inv_one, one_mul]
  exact Subgroup.one_mem _

theorem Qc_Lc_mul {u₁ u₂ : G} (hu₁ : u₁ ∈ hU R Ψ) (hu₂ : u₂ ∈ hU R Ψ) :
    ∃ b : F, xs Ψ ne02 b = ⁅u₁, Lc R Ψ u₂⁆ ∧
      Qc R Ψ (u₁ * u₂) = Qc R Ψ u₁ + Qc R Ψ u₂ + b ∧
      Lc R Ψ (u₁ * u₂) = Lc R Ψ u₁ * Lc R Ψ u₂ := by
  have := h.finite
  have hR := h.root
  have hL₁ := Lc_mem h hS hu₁
  have hL₂ := Lc_mem h hS hu₂
  have hcomm : ⁅u₁, Lc R Ψ u₂⁆ ∈ xg Ψ 0 2 := by
    rw [← (Q_eq_M h (hS.mem 0 2 ne02)).2.2.1]
    exact Subgroup.commutator_mem_commutator (hU_le_M_02 hu₁) (hid_le_M_02 h hS hL₂)
  obtain ⟨b, hb⟩ := (mem_xg_iff ne02).1 hcomm
  have hcen : ∀ k ∈ xg Ψ 0 2, ∀ m ∈ M R (xg Ψ 0 2), Commute k m :=
    fun k hk m hm => QD.commuting_M hR (hS.mem 0 2 ne02) k hk m hm
  have key : ⁅xs Ψ ne13 1, u₁ * u₂⁆ = xs Ψ ne02 (Qc R Ψ u₁ + Qc R Ψ u₂ + b) *
      (Lc R Ψ u₁ * Lc R Ψ u₂) := by
    have e1 : ⁅xs Ψ ne13 1, u₁ * u₂⁆ =
        ⁅xs Ψ ne13 1, u₁⁆ * (u₁ * ⁅xs Ψ ne13 1, u₂⁆ * u₁⁻¹) := by
      simp only [commutatorElement_def]
      group
    have e2 : u₁ * Lc R Ψ u₂ * u₁⁻¹ = xs Ψ ne02 b * Lc R Ψ u₂ := by
      rw [hb, commutatorElement_def]
      group
    have hu₁C : Commute u₁ (xs Ψ ne02 (Qc R Ψ u₂)) :=
      (hcen _ (xs_mem _ _) u₁ (hU_le_M_02 hu₁)).symm
    rw [e1, commutator_eq_xs_mul_Lc (R := R) u₁, commutator_eq_xs_mul_Lc (R := R) u₂]
    have e3 : u₁ * (xs Ψ ne02 (Qc R Ψ u₂) * Lc R Ψ u₂) * u₁⁻¹ =
        xs Ψ ne02 (Qc R Ψ u₂) * (xs Ψ ne02 b * Lc R Ψ u₂) := by
      rw [← e2, ← mul_assoc, hu₁C.eq]
      group
    rw [e3, xs_add, xs_add]
    have hL₁C : Commute (Lc R Ψ u₁) (xs Ψ ne02 (Qc R Ψ u₂)) :=
      (hcen _ (xs_mem _ _) _ (hid_le_M_02 h hS hL₁)).symm
    have hL₁C' : Commute (Lc R Ψ u₁) (xs Ψ ne02 b) :=
      (hcen _ (xs_mem _ _) _ (hid_le_M_02 h hS hL₁)).symm
    calc xs Ψ ne02 (Qc R Ψ u₁) * Lc R Ψ u₁ *
          (xs Ψ ne02 (Qc R Ψ u₂) * (xs Ψ ne02 b * Lc R Ψ u₂))
        = xs Ψ ne02 (Qc R Ψ u₁) * (Lc R Ψ u₁ * xs Ψ ne02 (Qc R Ψ u₂)) *
            xs Ψ ne02 b * Lc R Ψ u₂ := by group
      _ = xs Ψ ne02 (Qc R Ψ u₁) * (xs Ψ ne02 (Qc R Ψ u₂) * Lc R Ψ u₁) *
            xs Ψ ne02 b * Lc R Ψ u₂ := by rw [hL₁C.eq]
      _ = xs Ψ ne02 (Qc R Ψ u₁) * xs Ψ ne02 (Qc R Ψ u₂) * (Lc R Ψ u₁ * xs Ψ ne02 b) *
            Lc R Ψ u₂ := by group
      _ = xs Ψ ne02 (Qc R Ψ u₁) * xs Ψ ne02 (Qc R Ψ u₂) * (xs Ψ ne02 b * Lc R Ψ u₁) *
            Lc R Ψ u₂ := by rw [hL₁C'.eq]
      _ = _ := by group
  have hu : u₁ * u₂ ∈ hU R Ψ := Subgroup.mul_mem _ hu₁ hu₂
  have hQ : Qc R Ψ u₁ + Qc R Ψ u₂ + b = Qc R Ψ (u₁ * u₂) :=
    eq_Qc_of_mem h hS hu (by rw [key]; simpa using Subgroup.mul_mem _ hL₁ hL₂)
  refine ⟨b, hb, hQ.symm, ?_⟩
  rw [Lc, ← hQ, key]
  group

theorem commutator_xs13 (c : Fˣ) {u : G} (hu : u ∈ hU R Ψ) :
    ⁅xs Ψ ne13 c, u⁆ = xs Ψ ne02 (c * Qc R Ψ u) *
      Lc R Ψ (blk Ψ ne02 (NaturalModule.diagElt c) * u *
        (blk Ψ ne02 (NaturalModule.diagElt c))⁻¹) := by
  set t := blk Ψ ne03 (NaturalModule.diagElt c) with ht
  have hc : Commute u t := commute_blk03 h hS c hu
  have hut : t * u * t⁻¹ = u := by rw [← hc.eq]; group
  have e1 : xs Ψ ne13 c = t * xs Ψ ne13 1 * t⁻¹ := by rw [ht, blk03_conj_13, one_mul]
  have e2 : ⁅xs Ψ ne13 c, u⁆ = t * ⁅xs Ψ ne13 1, u⁆ * t⁻¹ := by
    rw [e1]
    conv_lhs => rw [← hut]
    simp only [commutatorElement_def]
    group
  rw [e2, commutator_eq_xs_mul_Lc (R := R) u, (Qc_Lc_blk02 h hS c hu).2,
    ← blk03_conj_eq_blk02_conj h hS c (Lc_mem h hS hu), ← blk03_conj_02 c, ← ht]
  group

end Commutator

section Anisotropic

variable [CharP F 2] (h : Hyp G R) (hS : Skel R Ψ) (hP : PtHyp R Ψ)
include h hS hP

theorem eq_one_of_Lc_eq_one {u : G} (hu : u ∈ hU R Ψ) (hL : Lc R Ψ u = 1) : u = 1 := by
  refine eq_one_of_commutator_mem h hS hP (xs_mem ne13 1) ?_ hu ?_
  · intro e
    have := xs_injective hS ne13 (e.trans (xs_zero ne13).symm)
    exact one_ne_zero this
  · rw [commutator_eq_xs_mul_Lc (R := R) u, hL, mul_one]
    exact xs_mem _ _

theorem eq_one_of_Qc_eq_zero {u : G} (hu : u ∈ hU R Ψ) (hQ : Qc R Ψ u = 0) : u = 1 := by
  have hR := h.root
  have hST := hS.perm σT
  obtain ⟨h8, Δ, hΔ, hAΔ⟩ := hP.perm hR σT
  have v0 : σT 0 = 1 := by decide
  have v1 : σT 1 = 0 := by decide
  have v2 : σT 2 = 3 := by decide
  have v3 : σT 3 = 2 := by decide
  have eOm : Om R (perm Ψ σT) = Om R Ψ := by
    rw [Om_perm, v0, v1, v2, v3]
    exact Set.inter_comm _ _
  have e02 : xg (perm Ψ σT) 0 2 = xg Ψ 1 3 := by rw [xg_perm, v0, v2]
  have e01 : xg (perm Ψ σT) 0 1 = xg Ψ 1 0 := by rw [xg_perm, v0, v1]
  have hL := Lc_mem h hS hu
  set d := u * xs Ψ ne13 1 * u⁻¹ with hd
  have hdD : d ∈ conjSub (xg Ψ 1 3) u := conj_mem_conjSub u (xs_mem ne13 1)
  have hd' : d = (Lc R Ψ u)⁻¹ * xs Ψ ne13 1 := by
    have e := commutator_eq_xs_mul_Lc (R := R) (Ψ := Ψ) u
    rw [hQ, xs_zero, one_mul, commutatorElement_def] at e
    rw [hd, ← e]
    group
  have hd1 : d ≠ 1 := by
    rw [hd]
    intro e
    have e' : xs Ψ ne13 1 = 1 := by
      calc xs Ψ ne13 1 = u⁻¹ * (u * xs Ψ ne13 1 * u⁻¹) * u := by group
        _ = 1 := by rw [e]; group
    exact one_ne_zero (xs_injective hS ne13 (e'.trans (xs_zero ne13).symm))
  have hdP : ∀ p ∈ xg (perm Ψ σT) 0 1, Commute d p := by
    intro p hp
    rw [e01] at hp
    rw [hd']
    exact ((commuting_hid_10 h hS _ hL p hp).inv_left).mul_left
      (commuting_xg (Ψ := Ψ) ne13 ne10 (by decide) (by decide) _ (xs_mem ne13 1) p hp)
  have hDom : conjSub (xg Ψ 1 3) u ∈ Om R (perm Ψ σT) := by
    rw [eOm]
    exact conjSub_mem_Om h hS hu (mem_Om_13 h hS)
  have hfix : conjSub (xg Ψ 1 3) u = xg Ψ 1 3 := by
    by_contra hne
    have hne' : conjSub (xg Ψ 1 3) u ≠ xg (perm Ψ σT) 0 2 := by
      rw [e02]
      exact hne
    exact hd1 (eq_one_of_commute_01 h hST h8 hΔ hAΔ hDom hne' hdD hdP)
  exact eq_one_of_mem_M_of_conjSub_eq h (hS.mem 3 1 ne31)
    ⟨hS.mem 1 3 ne13, hS.opp 3 1 ne31⟩ (hU_le_M_31 hu) hfix

end Anisotropic

variable (R Ψ) in
structure LinParamU (e : ℕ) (ι : (Fin e → F) → G) : Prop where
  add : ∀ v w, ι (v + w) = ι v * ι w
  inj : Function.Injective ι
  mem : ∀ v, ι v ∈ hU R Ψ
  surj : ∀ u ∈ hU R Ψ, ∃ v, ι v = u
  smul : ∀ (c : Fˣ) v, blk Ψ ne02 (NaturalModule.diagElt c) * ι v *
    (blk Ψ ne02 (NaturalModule.diagElt c))⁻¹ = ι ((c : F) • v)

theorem exists_linParamU [CharP F 2] [Finite F] (h : Hyp G R) (hS : Skel R Ψ) :
    ∃ (e : ℕ) (ι : (Fin e → F) → G), LinParamU R Ψ e ι := by
  obtain ⟨φ, hφA, -, hφ⟩ := exists_blockIso hS ne02
  have ht : ∀ c : Fˣ, FrameSL3.torPar φ c = blk Ψ ne02 (NaturalModule.diagElt c) :=
    fun c => hφ _
  have hC₀ : xg Ψ 2 0 ∈ omegaSet R (xg Ψ 0 2) := ⟨hS.mem 2 0 ne20, hS.opp 0 2 ne02⟩
  obtain ⟨e, ι, hadd, hinj, hmem, hsurj, hsc⟩ := exists_linParam h (hS.mem 0 2 ne02) hC₀ hφA
    hU_le_M_02 (hU_inf_02 h hS)
    (fun c => by rw [ht]; exact conjSub_hidAt_blk h.root ne02 c ne03 ne12 ne02 ne31)
  exact ⟨e, ι, ⟨hadd, hinj, hmem, hsurj, fun c v => by rw [← ht]; exact hsc c v⟩⟩

variable (R Ψ) in
@[expose] noncomputable def βU {e : ℕ} (ι : (Fin e → F) → G) (v w : Fin e → F) : F :=
  Qc R Ψ (ι (v + w)) - Qc R Ψ (ι v) - Qc R Ψ (ι w)

section QuadraticForm

variable [CharP F 2] (h : Hyp G R) (hS : Skel R Ψ) {e : ℕ} {ι : (Fin e → F) → G}
  (hι : LinParamU R Ψ e ι)
include h hS hι

omit [CharP F 2] h hS in
theorem LinParamU.map_zero : ι 0 = 1 := by
  have := hι.add 0 0
  rw [add_zero] at this
  exact left_eq_mul.1 this

theorem LinParamU.Qc_smul (c : F) (v : Fin e → F) :
    Qc R Ψ (ι (c • v)) = c ^ 2 * Qc R Ψ (ι v) := by
  by_cases hc : c = 0
  · subst hc
    rw [zero_smul, hι.map_zero, Qc_one h hS]
    ring
  · obtain ⟨u, rfl⟩ : ∃ u : Fˣ, (u : F) = c := ⟨Units.mk0 c hc, rfl⟩
    rw [← hι.smul, (Qc_Lc_blk02 h hS u (hι.mem v)).1]

theorem LinParamU.Lc_smul (c : Fˣ) (v : Fin e → F) :
    Lc R Ψ (ι ((c : F) • v)) = blk Ψ ne02 (NaturalModule.diagElt c) * Lc R Ψ (ι v) *
      (blk Ψ ne02 (NaturalModule.diagElt c))⁻¹ := by
  rw [← hι.smul, (Qc_Lc_blk02 h hS c (hι.mem v)).2]

theorem LinParamU.xs_βU (v w : Fin e → F) :
    xs Ψ ne02 (βU R Ψ ι v w) = ⁅ι v, Lc R Ψ (ι w)⁆ ∧
      Lc R Ψ (ι (v + w)) = Lc R Ψ (ι v) * Lc R Ψ (ι w) := by
  obtain ⟨b, hb, hQ, hL⟩ := Qc_Lc_mul h hS (hι.mem v) (hι.mem w)
  rw [← hι.add] at hQ hL
  refine ⟨?_, hL⟩
  rw [βU, hQ, show Qc R Ψ (ι v) + Qc R Ψ (ι w) + b - Qc R Ψ (ι v) - Qc R Ψ (ι w) = b by ring, hb]

omit [CharP F 2] h hS hι in
theorem LinParamU.Qc_add (v w : Fin e → F) :
    Qc R Ψ (ι (v + w)) = Qc R Ψ (ι v) + Qc R Ψ (ι w) + βU R Ψ ι v w := by
  rw [βU]
  ring

omit [CharP F 2] hι in
theorem commute_02_of_mem_M {k m : G} (hk : k ∈ xg Ψ 0 2) (hm : m ∈ M R (xg Ψ 0 2)) :
    Commute k m :=
  have := h.finite
  QD.commuting_M h.root (hS.mem 0 2 ne02) k hk m hm

theorem LinParamU.βU_add_left (v₁ v₂ w : Fin e → F) :
    βU R Ψ ι (v₁ + v₂) w = βU R Ψ ι v₁ w + βU R Ψ ι v₂ w := by
  apply xs_injective hS ne02
  rw [xs_add, (hι.xs_βU h hS _ _).1, (hι.xs_βU h hS _ _).1, (hι.xs_βU h hS _ _).1, hι.add]
  have hc : Commute (ι v₁) ⁅ι v₂, Lc R Ψ (ι w)⁆ := by
    rw [← (hι.xs_βU h hS _ _).1]
    exact (commute_02_of_mem_M h hS (xs_mem _ _) (hU_le_M_02 (hι.mem v₁))).symm
  have hc' : Commute ⁅ι v₁, Lc R Ψ (ι w)⁆ ⁅ι v₂, Lc R Ψ (ι w)⁆ := by
    rw [← (hι.xs_βU h hS v₁ w).1, ← (hι.xs_βU h hS v₂ w).1]
    exact h.root.commuting_self (hS.mem 0 2 ne02) _ (xs_mem _ _) _ (xs_mem _ _)
  calc ⁅ι v₁ * ι v₂, Lc R Ψ (ι w)⁆ =
      ι v₁ * ⁅ι v₂, Lc R Ψ (ι w)⁆ * (ι v₁)⁻¹ * ⁅ι v₁, Lc R Ψ (ι w)⁆ := by
        simp only [commutatorElement_def]
        group
    _ = ⁅ι v₂, Lc R Ψ (ι w)⁆ * ⁅ι v₁, Lc R Ψ (ι w)⁆ := by rw [hc.eq]; group
    _ = ⁅ι v₁, Lc R Ψ (ι w)⁆ * ⁅ι v₂, Lc R Ψ (ι w)⁆ := hc'.eq.symm

theorem LinParamU.βU_add_right (v w₁ w₂ : Fin e → F) :
    βU R Ψ ι v (w₁ + w₂) = βU R Ψ ι v w₁ + βU R Ψ ι v w₂ := by
  apply xs_injective hS ne02
  rw [xs_add, (hι.xs_βU h hS _ _).1, (hι.xs_βU h hS _ _).1, (hι.xs_βU h hS _ _).1,
    (hι.xs_βU h hS _ _).2]
  have hL := Lc_mem h hS (hι.mem w₁)
  have hc : Commute (Lc R Ψ (ι w₁)) ⁅ι v, Lc R Ψ (ι w₂)⁆ := by
    rw [← (hι.xs_βU h hS _ _).1]
    exact (commute_02_of_mem_M h hS (xs_mem _ _) (hid_le_M_02 h hS hL)).symm
  calc ⁅ι v, Lc R Ψ (ι w₁) * Lc R Ψ (ι w₂)⁆ =
      ⁅ι v, Lc R Ψ (ι w₁)⁆ * (Lc R Ψ (ι w₁) * ⁅ι v, Lc R Ψ (ι w₂)⁆ * (Lc R Ψ (ι w₁))⁻¹) := by
        simp only [commutatorElement_def]
        group
    _ = ⁅ι v, Lc R Ψ (ι w₁)⁆ * ⁅ι v, Lc R Ψ (ι w₂)⁆ := by rw [hc.eq]; group

theorem LinParamU.βU_smul_right (c : F) (v w : Fin e → F) :
    βU R Ψ ι v (c • w) = c * βU R Ψ ι v w := by
  by_cases hc : c = 0
  · subst hc
    have h0 : βU R Ψ ι v 0 = 0 := by
      have := hι.βU_add_right h hS v 0 0
      rw [add_zero] at this
      exact left_eq_add.1 this
    rw [zero_smul, h0, zero_mul]
  · obtain ⟨u, rfl⟩ : ∃ u : Fˣ, (u : F) = c := ⟨Units.mk0 c hc, rfl⟩
    apply xs_injective hS ne02
    rw [(hι.xs_βU h hS _ _).1, hι.Lc_smul h hS u w,
      ← blk03_conj_eq_blk02_conj h hS u (Lc_mem h hS (hι.mem w)), ← blk03_conj_02 u,
      (hι.xs_βU h hS _ _).1]
    set t := blk Ψ ne03 (NaturalModule.diagElt u)
    have hct : Commute (ι v) t := commute_blk03 h hS u (hι.mem v)
    have hvt : t * ι v * t⁻¹ = ι v := by rw [← hct.eq]; group
    conv_lhs => rw [← hvt]
    simp only [commutatorElement_def]
    group

theorem LinParamU.βU_smul_left (c : F) (v w : Fin e → F) :
    βU R Ψ ι (c • v) w = c * βU R Ψ ι v w := by
  by_cases hc : c = 0
  · subst hc
    have h0 : βU R Ψ ι 0 w = 0 := by
      have := hι.βU_add_left h hS 0 0 w
      rw [add_zero] at this
      exact left_eq_add.1 this
    rw [zero_smul, h0, zero_mul]
  · obtain ⟨u, rfl⟩ : ∃ u : Fˣ, (u : F) = c := ⟨Units.mk0 c hc, rfl⟩
    have hcc : βU R Ψ ι ((u : F) • v) ((u : F) • w) = (u : F) ^ 2 * βU R Ψ ι v w := by
      apply xs_injective hS ne02
      rw [(hι.xs_βU h hS _ _).1, hι.Lc_smul h hS u w, ← hι.smul u v, ← blk02_conj_02 u,
        (hι.xs_βU h hS _ _).1]
      simp only [commutatorElement_def]
      group
    rw [hι.βU_smul_right h hS, pow_two, mul_assoc] at hcc
    exact mul_left_cancel₀ (Units.ne_zero u) hcc

theorem LinParamU.eq_zero_of_Qc (hP : PtHyp R Ψ) {v : Fin e → F} (hv : Qc R Ψ (ι v) = 0) :
    v = 0 := by
  have h1 := eq_one_of_Qc_eq_zero h hS hP (hι.mem v) hv
  exact hι.inj (h1.trans hι.map_zero.symm)

theorem LinParamU.Qc_smul_add_of_βU (x : F) {r v : Fin e → F} (hrv : βU R Ψ ι r v = 0) :
    Qc R Ψ (ι (x • r + v)) = x ^ 2 * Qc R Ψ (ι r) + Qc R Ψ (ι v) := by
  rw [LinParamU.Qc_add, hι.Qc_smul h hS, hι.βU_smul_left h hS, hrv, mul_zero, add_zero]

theorem LinParamU.le_two [Finite F] (hP : PtHyp R Ψ) : e ≤ 2 := by
  by_contra he
  push Not at he
  set u₀ : Fin e → F := Pi.single ⟨0, by omega⟩ 1
  set u₁ : Fin e → F := Pi.single ⟨1, by omega⟩ 1
  set u₂ : Fin e → F := Pi.single ⟨2, by omega⟩ 1
  obtain ⟨r, v, hr, hrv, hind⟩ : ∃ r v : Fin e → F, r ≠ 0 ∧ βU R Ψ ι r v = 0 ∧
      ∀ x : F, x • r + v ≠ 0 := by
    by_cases hb : βU R Ψ ι u₀ u₁ = 0 ∧ βU R Ψ ι u₀ u₂ = 0
    · refine ⟨u₀, u₁, ?_, hb.1, fun x hx => ?_⟩
      · intro e0
        have := congrFun e0 ⟨0, by omega⟩
        simp [u₀] at this
      · have := congrFun hx ⟨1, by omega⟩
        simp [u₀, u₁] at this
    · refine ⟨u₀, βU R Ψ ι u₀ u₂ • u₁ - βU R Ψ ι u₀ u₁ • u₂, ?_, ?_, fun x hx => ?_⟩
      · intro e0
        have := congrFun e0 ⟨0, by omega⟩
        simp [u₀] at this
      · rw [sub_eq_add_neg, hι.βU_add_right h hS, ← neg_smul, hι.βU_smul_right h hS,
          hι.βU_smul_right h hS]
        ring
      · apply hb
        have h1 := congrFun hx ⟨1, by omega⟩
        have h2 := congrFun hx ⟨2, by omega⟩
        simp [u₀, u₁, u₂] at h1 h2
        exact ⟨by simpa using h2, h1⟩
  have hQr : Qc R Ψ (ι r) ≠ 0 := fun h0 => hr (hι.eq_zero_of_Qc h hS hP h0)
  obtain ⟨x, hx⟩ := isSquare_of_charTwo' (Qc R Ψ (ι v) / Qc R Ψ (ι r))
  apply hind x
  refine hι.eq_zero_of_Qc h hS hP ?_
  rw [hι.Qc_smul_add_of_βU h hS x hrv, pow_two, ← hx, div_mul_cancel₀ _ hQr,
    CharTwo.add_self_eq_zero]

omit hι in
theorem Lc_one : Lc R Ψ (1 : G) = 1 := by
  rw [Lc, Qc_one h hS, xs_zero, commutatorElement_one_right, inv_one, one_mul]

theorem LinParamU.commutator_xs13 (s : F) (v : Fin e → F) :
    ⁅xs Ψ ne13 s, ι v⁆ = xs Ψ ne02 (s * Qc R Ψ (ι v)) * Lc R Ψ (ι (s • v)) := by
  by_cases hs : s = 0
  · subst hs
    rw [xs_zero, commutatorElement_one_left, zero_mul, xs_zero, zero_smul, hι.map_zero,
      Lc_one h hS, mul_one]
  · obtain ⟨u, rfl⟩ : ∃ u : Fˣ, (u : F) = s := ⟨Units.mk0 s hs, rfl⟩
    rw [CaseB.commutator_xs13 h hS u (hι.mem v), hι.smul]

omit [CharP F 2] h hS in
theorem LinParamU.one_le (hU1 : hU R Ψ ≠ ⊥) : 1 ≤ e := by
  by_contra he
  push Not at he
  obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hU1
  obtain ⟨v, hv⟩ := hι.surj u u.2
  have hv0 : v = 0 := funext fun i => absurd i.2 (by omega)
  apply hu1
  rw [hv0, hι.map_zero] at hv
  exact Subtype.ext hv.symm

end QuadraticForm

end CaseB

end CFSG.Timmesfeld.ARS
