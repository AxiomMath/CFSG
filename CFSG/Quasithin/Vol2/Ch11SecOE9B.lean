module

public import CFSG.RankThree.SubgroupLists.SymplecticTransvections

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3.Sp4

open Matrix CFSG.Assembly.LowTwoRank CFSG.RankThree.SubgroupLists

variable {K : Type} [Field K]

abbrev mat (g : ↥(StatedSp 2 K)) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)

theorem mat_mul_mulVec (g h : ↥(StatedSp 2 K)) (v : Fin 2 ⊕ Fin 2 → K) :
    mat (g * h) *ᵥ v = mat g *ᵥ (mat h *ᵥ v) := by
  rw [mat, mat, mat, Subgroup.coe_mul, Units.val_mul, Matrix.mulVec_mulVec]

theorem mat_one_mulVec (v : Fin 2 ⊕ Fin 2 → K) : mat (1 : ↥(StatedSp 2 K)) *ᵥ v = v := by
  rw [mat, Subgroup.coe_one, Units.val_one, Matrix.one_mulVec]

theorem mat_inv_mulVec_mulVec (g : ↥(StatedSp 2 K)) (v : Fin 2 ⊕ Fin 2 → K) :
    mat g⁻¹ *ᵥ (mat g *ᵥ v) = v := by
  rw [← mat_mul_mulVec, inv_mul_cancel, mat_one_mulVec]

theorem mat_mulVec_inv_mulVec (g : ↥(StatedSp 2 K)) (v : Fin 2 ⊕ Fin 2 → K) :
    mat g *ᵥ (mat g⁻¹ *ᵥ v) = v := by
  rw [← mat_mul_mulVec, mul_inv_cancel, mat_one_mulVec]

@[expose] def e₀ : Fin 2 ⊕ Fin 2 → K := Pi.single (Sum.inl 0) 1

@[expose] noncomputable def xHom : Multiplicative K →* ↥(StatedSp 2 K) where
  toFun t := ⟨spTrans e₀ (Multiplicative.toAdd t), spTrans_mem_statedSp _ _⟩
  map_one' := Subtype.ext (spTrans_zero e₀)
  map_mul' _ _ := Subtype.ext (spTrans_add e₀ _ _).symm

theorem mat_xHom_mulVec (t : Multiplicative K) (v : Fin 2 ⊕ Fin 2 → K) :
    mat (xHom t) *ᵥ v = v + (Multiplicative.toAdd t * spForm 2 K v e₀) • e₀ :=
  spTrans_mulVec e₀ _ v

@[expose] noncomputable def rootX : Subgroup ↥(StatedSp 2 K) := (xHom (K := K)).range

theorem spForm_inr_e₀ : spForm 2 K (Pi.single (Sum.inr 0) 1) e₀ = -1 := by
  rw [spForm_apply]
  simp [e₀, Pi.single_apply]

theorem xHom_injective : Function.Injective (xHom (K := K)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro t ht
  have h := congrArg (fun g : ↥(StatedSp 2 K) => mat g *ᵥ Pi.single (Sum.inr 0) 1)
    (MonoidHom.mem_ker.mp ht)
  simp only [mat_xHom_mulVec, mat_one_mulVec, spForm_inr_e₀, add_eq_left] at h
  have h1 := congrFun h (Sum.inl 0)
  simp [e₀] at h1
  exact Subgroup.mem_bot.mpr h1

theorem card_rootX : Nat.card (rootX (K := K)) = Nat.card K := by
  rw [rootX, MonoidHom.range_eq_map, Subgroup.card_map_of_injective xHom_injective,
    Subgroup.card_top]
  rfl

variable [CharP K 2]

theorem isElemAbelian_rootX : CFSG.Open.IsElemAbelian 2 (rootX (K := K)) := by
  refine ⟨isMulCommutative_iff.mpr fun a b => Subtype.ext ?_, ?_⟩
  · obtain ⟨s, hs⟩ := a.2
    obtain ⟨t, ht⟩ := b.2
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hs, ← ht, ← map_mul, ← map_mul, mul_comm]
  · rintro _ ⟨t, rfl⟩
    rw [← map_pow]
    have h : t ^ 2 = 1 := by
      change Multiplicative.ofAdd (2 • Multiplicative.toAdd t) = Multiplicative.ofAdd 0
      rw [two_nsmul, CharTwo.add_self_eq_zero]
    rw [h, map_one]

@[expose] def expTwoSub (R : Subgroup ↥(StatedSp 2 K)) (m : Submodule K (Fin 2 ⊕ Fin 2 → K)) :
    Subgroup ↥(StatedSp 2 K) where
  carrier := {g | g ∈ R ∧ (∀ v, mat g *ᵥ v - v ∈ m) ∧ ∀ v ∈ m, mat g *ᵥ v = v}
  one_mem' := ⟨R.one_mem, fun v => by rw [mat_one_mulVec, sub_self]; exact m.zero_mem,
    fun v _ => mat_one_mulVec v⟩
  mul_mem' := by
    rintro g h ⟨hgR, hg1, hg2⟩ ⟨hhR, hh1, hh2⟩
    refine ⟨R.mul_mem hgR hhR, fun v => ?_, fun v hv => ?_⟩
    · rw [mat_mul_mulVec, show mat g *ᵥ (mat h *ᵥ v) - v =
        (mat g *ᵥ (mat h *ᵥ v) - mat h *ᵥ v) + (mat h *ᵥ v - v) by abel]
      exact m.add_mem (hg1 _) (hh1 v)
    · rw [mat_mul_mulVec, hh2 v hv, hg2 v hv]
  inv_mem' := by
    rintro g ⟨hgR, hg1, hg2⟩
    refine ⟨R.inv_mem hgR, fun v => ?_, fun v hv => ?_⟩
    · have h := m.neg_mem (hg1 (mat g⁻¹ *ᵥ v))
      rwa [mat_mulVec_inv_mulVec, neg_sub] at h
    · have h := congrArg (mat g⁻¹ *ᵥ ·) (hg2 v hv)
      simp only [mat_inv_mulVec_mulVec] at h
      exact h.symm

omit [CharP K 2] in
theorem expTwoSub_le (R : Subgroup ↥(StatedSp 2 K)) (m : Submodule K (Fin 2 ⊕ Fin 2 → K)) :
    expTwoSub R m ≤ R := fun _ h => h.1

omit [CharP K 2] in
theorem expTwoSub_normal {R : Subgroup ↥(StatedSp 2 K)} {m : Submodule K (Fin 2 ⊕ Fin 2 → K)}
    (hm : ∀ r ∈ R, ∀ v ∈ m, mat r *ᵥ v ∈ m) : ((expTwoSub R m).subgroupOf R).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (expTwoSub_le R m)]
  intro r hr
  rw [Subgroup.mem_normalizer_iff]
  have key : ∀ x ∈ R, ∀ g ∈ expTwoSub R m, x * g * x⁻¹ ∈ expTwoSub R m := by
    rintro x hx g ⟨hgR, hg1, hg2⟩
    refine ⟨R.mul_mem (R.mul_mem hx hgR) (R.inv_mem hx), fun v => ?_, fun v hv => ?_⟩
    · rw [mat_mul_mulVec, mat_mul_mulVec, show mat x *ᵥ (mat g *ᵥ (mat x⁻¹ *ᵥ v)) - v =
        mat x *ᵥ (mat g *ᵥ (mat x⁻¹ *ᵥ v) - mat x⁻¹ *ᵥ v) by
          rw [Matrix.mulVec_sub, mat_mulVec_inv_mulVec]]
      exact hm x hx _ (hg1 _)
    · rw [mat_mul_mulVec, mat_mul_mulVec, hg2 _ (hm _ (R.inv_mem hx) v hv),
        mat_mulVec_inv_mulVec]
  intro g
  refine ⟨key r hr g, fun h => ?_⟩
  have h1 := key r⁻¹ (R.inv_mem hr) _ h
  rwa [inv_inv, show r⁻¹ * (r * g * r⁻¹) * r = g by group] at h1

theorem mul_self_of_mem_expTwoSub {R : Subgroup ↥(StatedSp 2 K)}
    {m : Submodule K (Fin 2 ⊕ Fin 2 → K)} {g : ↥(StatedSp 2 K)} (hg : g ∈ expTwoSub R m) :
    g * g = 1 := by
  obtain ⟨-, hg1, hg2⟩ := hg
  refine Subtype.ext (gl_ext_mulVec fun v => ?_)
  change mat (g * g) *ᵥ v = mat 1 *ᵥ v
  rw [mat_mul_mulVec, mat_one_mulVec]
  have hw := hg2 _ (hg1 v)
  rw [Matrix.mulVec_sub] at hw
  have h2 : ∀ w : Fin 2 ⊕ Fin 2 → K, w + w = 0 := fun w =>
    funext fun i => CharTwo.add_self_eq_zero (w i)
  calc mat g *ᵥ (mat g *ᵥ v) = (mat g *ᵥ (mat g *ᵥ v) - mat g *ᵥ v) + mat g *ᵥ v := by abel
    _ = (mat g *ᵥ v - v) + mat g *ᵥ v := by rw [hw]
    _ = (mat g *ᵥ v + mat g *ᵥ v) - v := by abel
    _ = v := by rw [h2, zero_sub, neg_eq_of_add_eq_zero_right (h2 v)]

theorem isPGroup_expTwoSub (R : Subgroup ↥(StatedSp 2 K)) (m : Submodule K (Fin 2 ⊕ Fin 2 → K)) :
    IsPGroup 2 (expTwoSub R m) := fun g =>
  ⟨1, Subtype.ext (by rw [pow_one, sq, Subgroup.coe_mul, mul_self_of_mem_expTwoSub g.2]; rfl)⟩

theorem exists_normal_expTwo {R : Subgroup ↥(StatedSp 2 K)} (hXR : rootX ≤ R)
    (h : ∀ r ∈ R, spForm 2 K (mat r *ᵥ e₀) e₀ = 0) :
    ∃ N : Subgroup ↥(StatedSp 2 K), N ≤ R ∧ (N.subgroupOf R).Normal ∧ IsPGroup 2 N ∧
      rootX ≤ N := by
  set m : Submodule K (Fin 2 ⊕ Fin 2 → K) :=
    Submodule.span K (Set.range fun r : R => mat r *ᵥ e₀) with hmdef
  have hgen : ∀ r ∈ R, mat r *ᵥ e₀ ∈ m := fun r hr =>
    Submodule.subset_span ⟨⟨r, hr⟩, rfl⟩
  have he : e₀ ∈ m := by
    simpa [mat_one_mulVec] using hgen 1 R.one_mem
  have hm : ∀ r ∈ R, ∀ v ∈ m, mat r *ᵥ v ∈ m := by
    intro r hr v hv
    have hle : m ≤ m.comap (Matrix.toLin' (mat r)) := by
      rw [hmdef, Submodule.span_le]
      rintro _ ⟨s, rfl⟩
      change mat r *ᵥ (mat s *ᵥ e₀) ∈ m
      rw [← mat_mul_mulVec]
      exact hgen _ (R.mul_mem hr s.2)
    exact hle hv
  have horth : ∀ v ∈ m, spForm 2 K v e₀ = 0 := by
    intro v hv
    have hle : m ≤ LinearMap.ker ((spForm 2 K).flip e₀) := by
      rw [hmdef, Submodule.span_le]
      rintro _ ⟨s, rfl⟩
      exact h s s.2
    exact hle hv
  refine ⟨expTwoSub R m, expTwoSub_le R m, expTwoSub_normal hm, isPGroup_expTwoSub R m, ?_⟩
  rintro _ ⟨t, rfl⟩
  refine ⟨hXR ⟨t, rfl⟩, fun v => ?_, fun v hv => ?_⟩
  · rw [mat_xHom_mulVec, add_sub_cancel_left]
    exact m.smul_mem _ he
  · rw [mat_xHom_mulVec, horth v hv, mul_zero, zero_smul, add_zero]

end CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3.Sp4
