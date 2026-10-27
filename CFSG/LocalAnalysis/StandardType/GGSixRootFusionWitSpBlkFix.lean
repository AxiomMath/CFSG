module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitSpBlkExt
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitSpNsBlock
public import CFSG.Sporadic.Suz.Setup

public section

namespace CFSG.StandardType

namespace WitSpBlk

open Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.SeitzReduction.SymplecticPilot WitClSp WitSpNs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)

variable {K : Type} [Field K] {n : ℕ}

theorem form_span_eq_zero {s t : Set (Fin n ⊕ Fin n → K)}
    (h : ∀ a ∈ s, ∀ b ∈ t, form a b = 0) {a b : Fin n ⊕ Fin n → K}
    (ha : a ∈ Submodule.span K s) (hb : b ∈ Submodule.span K t) : form a b = 0 := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    induction hb using Submodule.span_induction with
    | mem y hy => exact h x hx y hy
    | zero => exact form_zero_right x
    | add y z _ _ h1 h2 => rw [form_add_right, h1, h2, add_zero]
    | smul c y _ h1 => rw [form_smul_right, h1, mul_zero]
  | zero => exact form_zero_left b
  | add x z _ _ h1 h2 => rw [form_add_left, h1, h2, add_zero]
  | smul c x _ h1 => rw [form_smul_left, h1, mul_zero]

theorem mem_orth_iff {T : Submodule K (Fin n ⊕ Fin n → K)} {z : Fin n ⊕ Fin n → K} :
    z ∈ (Matrix.toBilin' (Matrix.J (Fin n) K)).orthogonal T ↔ ∀ t ∈ T, form t z = 0 := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  refine forall₂_congr fun t _ => ?_
  rw [toBilin'_J_apply, neg_eq_zero]

theorem finrank_orth (T : Submodule K (Fin n ⊕ Fin n → K)) :
    Module.finrank K ((Matrix.toBilin' (Matrix.J (Fin n) K)).orthogonal T) =
      2 * n - Module.finrank K T := by
  rw [LinearMap.BilinForm.finrank_orthogonal nondegenerate_toBilin'_J, finrank_ambient]

theorem finrank_le_of_isotropic {W : Submodule K (Fin n ⊕ Fin n → K)}
    (h : ∀ a ∈ W, ∀ b ∈ W, form a b = 0) : Module.finrank K W ≤ n := by
  have hle : W ≤ (Matrix.toBilin' (Matrix.J (Fin n) K)).orthogonal W :=
    fun z hz => mem_orth_iff.mpr fun t ht => h t ht z hz
  have h1 := Submodule.finrank_mono hle
  rw [finrank_orth] at h1
  have h2 := Submodule.finrank_le W
  rw [finrank_ambient] at h2
  omega

namespace IsSpFamily

variable {m : ℕ} {u w : Fin m → Fin n ⊕ Fin n → K}

theorem zero (u w : Fin 0 → Fin n ⊕ Fin n → K) : IsSpFamily u w :=
  ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩

theorem snoc (h : IsSpFamily u w) {a b : Fin n ⊕ Fin n → K} (hab : form a b = 1)
    (ha : ∀ i, form (u i) a = 0 ∧ form (w i) a = 0)
    (hb : ∀ i, form (u i) b = 0 ∧ form (w i) b = 0) :
    IsSpFamily (Fin.snoc (α := fun _ => Fin n ⊕ Fin n → K) u a)
      (Fin.snoc (α := fun _ => Fin n ⊕ Fin n → K) w b) := by
  have hrev : ∀ {x y : Fin n ⊕ Fin n → K}, form x y = 0 → form y x = 0 := fun hxy => by
    rw [form_antisymm, hxy, neg_zero]
  refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_⟩
  · induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => simp [hab]
      | cast j =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc]
        rw [ite_eq_right (fun h' => (Fin.castSucc_ne_last j) h'.symm)]
        exact hrev (ha j).2
    | cast i =>
      induction j using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc]
        rw [ite_eq_right (Fin.castSucc_ne_last i)]
        exact (hb i).1
      | cast j =>
        simp only [Fin.snoc_castSucc, Fin.castSucc_inj]
        exact h.pair i j
  · induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => simp [form_self]
      | cast j =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc]
        exact hrev (ha j).1
    | cast i =>
      induction j using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc]
        exact (ha i).1
      | cast j =>
        simp only [Fin.snoc_castSucc]
        exact h.uu i j
  · induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => simp [form_self]
      | cast j =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc]
        exact hrev (hb j).2
    | cast i =>
      induction j using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc]
        exact (hb i).2
      | cast j =>
        simp only [Fin.snoc_castSucc]
        exact h.ww i j

theorem form_sum_u_w (h : IsSpFamily u w) (a : Fin m → K) (j : Fin m) :
    form (∑ i, a i • u i) (w j) = a j := by
  rw [form_sum_left]
  simp [form_smul_left, h.pair]

end IsSpFamily

theorem exists_fix_family (v : StatedSp n K) : ∀ d : ℕ, n + d ≤ Module.finrank K (fixSpace v) →
    ∃ x y : Fin d → Fin n ⊕ Fin n → K, IsSpFamily x y ∧ ∀ j, x j ∈ fixSpace v ∧ y j ∈ fixSpace v
  | 0, _ => ⟨Fin.elim0, Fin.elim0, IsSpFamily.zero _ _, fun j => j.elim0⟩
  | d + 1, hd => by
    classical
    obtain ⟨x, y, hxy, hmem⟩ := exists_fix_family v d (by omega)
    set B := Matrix.toBilin' (Matrix.J (Fin n) K) with hB
    set T := Submodule.span K (Set.range (Sum.elim x y)) with hT
    set Z := fixSpace v ⊓ B.orthogonal T with hZ
    have hxT : ∀ i, x i ∈ T := fun i => Submodule.subset_span ⟨Sum.inl i, rfl⟩
    have hyT : ∀ i, y i ∈ T := fun i => Submodule.subset_span ⟨Sum.inr i, rfl⟩
    have hZT : ∀ z ∈ Z, ∀ t ∈ T, form t z = 0 := fun z hz => mem_orth_iff.mp hz.2
    obtain ⟨a, ha, b, hb, hab⟩ : ∃ a ∈ Z, ∃ b ∈ Z, form a b ≠ 0 := by
      by_contra hcon
      push Not at hcon
      set X := Submodule.span K (Set.range x) with hX
      have hXT : X ≤ T := Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨Sum.inl i, rfl⟩)
      have hXiso : ∀ s ∈ X, ∀ s' ∈ X, form s s' = 0 := fun s hs s' hs' =>
        form_span_eq_zero (by rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩; exact hxy.uu i j) hs hs'
      have hZX : Z ⊓ X = ⊥ := by
        rw [eq_bot_iff]
        rintro z ⟨hzZ, hzX⟩
        obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hzX
        have hc : ∀ j, c j = 0 := fun j => by
          rw [← hxy.form_sum_u_w c j, form_antisymm, hZT _ hzZ _ (hyT j), neg_zero]
        simp [hc]
      have hiso : ∀ p ∈ Z ⊔ X, ∀ q ∈ Z ⊔ X, form p q = 0 := by
        intro p hp q hq
        obtain ⟨z, hz, s, hs, rfl⟩ := Submodule.mem_sup.mp hp
        obtain ⟨z', hz', s', hs', rfl⟩ := Submodule.mem_sup.mp hq
        rw [form_add_left, form_add_right, form_add_right, hcon z hz z' hz',
          hZT z' hz' s (hXT hs), hXiso s hs s' hs', form_antisymm, hZT z hz s' (hXT hs')]
        ring
      have h1 := finrank_le_of_isotropic hiso
      have h2 := Submodule.finrank_sup_add_finrank_inf_eq Z X
      rw [hZX, finrank_bot] at h2
      have hlin : LinearIndependent K x := hxy.linearIndependent.comp Sum.inl Sum.inl_injective
      have h3 : Module.finrank K X = d := by
        rw [hX, finrank_span_eq_card hlin, Fintype.card_fin]
      have h4 : Module.finrank K T = d + d := by
        rw [hT, finrank_span_eq_card hxy.linearIndependent, Fintype.card_sum, Fintype.card_fin]
      have h5 := Submodule.finrank_sup_add_finrank_inf_eq (fixSpace v) (B.orthogonal T)
      have h6 := Submodule.finrank_le (fixSpace v ⊔ B.orthogonal T)
      rw [finrank_orth, h4] at h5
      rw [finrank_ambient] at h6
      have h7 : 2 * d ≤ 2 * n := by
        have := Submodule.finrank_le T
        rw [h4, finrank_ambient] at this
        omega
      have h8 : Module.finrank K Z = Module.finrank K ↥(fixSpace v ⊓ B.orthogonal T) := rfl
      omega
    have hab' : form a ((form a b)⁻¹ • b) = 1 := by rw [form_smul_right, inv_mul_cancel₀ hab]
    refine ⟨Fin.snoc (α := fun _ => Fin n ⊕ Fin n → K) x a,
      Fin.snoc (α := fun _ => Fin n ⊕ Fin n → K) y ((form a b)⁻¹ • b),
      hxy.snoc hab' (fun i => ⟨hZT a ha _ (hxT i), hZT a ha _ (hyT i)⟩)
        (fun i => ⟨by rw [form_smul_right, hZT b hb _ (hxT i), mul_zero],
          by rw [form_smul_right, hZT b hb _ (hyT i), mul_zero]⟩), fun j => ?_⟩
    induction j using Fin.lastCases with
    | last =>
      simp only [Fin.snoc_last]
      exact ⟨ha.1, Submodule.smul_mem _ _ hb.1⟩
    | cast j =>
      simp only [Fin.snoc_castSucc]
      exact hmem j

theorem parClosed_union {S T : Set (Fin n ⊕ Fin n)} (hS : ParClosed S) (hT : ParClosed T) :
    ParClosed (S ∪ T) := by
  rintro a (ha | ha)
  · exact Or.inl (hS a ha)
  · exact Or.inr (hT a ha)

theorem plane_lt_of_mem_blockCoords_zero {d : ℕ} {t : Fin n ⊕ Fin n}
    (ht : t ∈ blockCoords n d 0) : (plane t : ℕ) < d := by
  have := ht.2
  simpa using this

theorem fix_of_family {v : StatedSp n K} {d : ℕ} (hdn : d ≤ n) {x y : Fin d → Fin n ⊕ Fin n → K}
    (hxy : IsSpFamily x y) (hmem : ∀ j, x j ∈ fixSpace v ∧ y j ∈ fixSpace v) :
    ∃ g : StatedSp n K, g * v * g⁻¹ ∈ suppGroup (blockCoords n d 0)ᶜ := by
  obtain ⟨A, hA⟩ := exists_sp_of_family hdn hxy
  refine ⟨A⁻¹, ?_⟩
  rw [mem_suppGroup_iff (parClosed_blockCoords n d 0).compl]
  intro t ht r
  rw [Set.mem_compl_iff, not_not] at ht
  have hlt := plane_lt_of_mem_blockCoords_zero ht
  have hcol : mat n K (A⁻¹ * v * A⁻¹⁻¹) *ᵥ Pi.single t 1 = Pi.single t 1 := by
    rw [inv_inv, map_mul, map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rcases t with k | k
    · have hk : Fin.castLE hdn ⟨k, hlt⟩ = k := Fin.ext rfl
      have h1 := (hA ⟨k, hlt⟩).1
      rw [hk] at h1
      rw [h1, mem_fixSpace.mp (hmem _).1, ← h1, mulVec_inv_mulVec]
    · have hk : Fin.castLE hdn ⟨k, hlt⟩ = k := Fin.ext rfl
      have h1 := (hA ⟨k, hlt⟩).2
      rw [hk] at h1
      rw [h1, mem_fixSpace.mp (hmem _).2, ← h1, mulVec_inv_mulVec]
  rw [mat_apply_eq_mulVec, hcol, Pi.single_apply, Matrix.one_apply]

end WitSpBlk

end CFSG.StandardType
