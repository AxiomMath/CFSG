module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.GroupTheory.GLnTwoSplitting.Transvection
public import CFSG.Open.StatedAPI

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.B5.Ln

open CFSG.Assembly.LowTwoRank Matrix Module
open scoped Matrix

variable {n : ℕ}

@[expose] def mat (g : ↥(StatedSL n (ZMod 2))) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  ((g : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))

@[simp] theorem mat_mul (g h : ↥(StatedSL n (ZMod 2))) : mat (g * h) = mat g * mat h := rfl

@[simp] theorem mat_one : mat (1 : ↥(StatedSL n (ZMod 2))) = 1 := rfl

theorem mat_inv_mul (g : ↥(StatedSL n (ZMod 2))) : mat g⁻¹ * mat g = 1 := by
  rw [← mat_mul, inv_mul_cancel, mat_one]

theorem mat_mul_inv (g : ↥(StatedSL n (ZMod 2))) : mat g * mat g⁻¹ = 1 := by
  rw [← mat_mul, mul_inv_cancel, mat_one]

theorem mat_injective : Function.Injective (mat (n := n)) := fun _ _ h =>
  Subtype.ext (Units.ext h)

theorem mulVec_inv_mulVec (g : ↥(StatedSL n (ZMod 2))) (x : Fin n → ZMod 2) :
    mat g⁻¹ *ᵥ (mat g *ᵥ x) = x := by
  rw [mulVec_mulVec, mat_inv_mul, one_mulVec]

theorem mulVec_mulVec_inv (g : ↥(StatedSL n (ZMod 2))) (x : Fin n → ZMod 2) :
    mat g *ᵥ (mat g⁻¹ *ᵥ x) = x := by
  rw [mulVec_mulVec, mat_mul_inv, one_mulVec]

theorem eq_of_mulVec_eq {g h : ↥(StatedSL n (ZMod 2))} (hgh : ∀ x, mat g *ᵥ x = mat h *ᵥ x) :
    g = h :=
  mat_injective (Matrix.toLin'.injective (LinearMap.ext hgh))

theorem mem_statedSL (M : GL (Fin n) (ZMod 2)) : M ∈ StatedSL n (ZMod 2) :=
  CFSG.Open.StatedAPI.mem_statedSL_zmod_two M

@[expose] def ofGL (M : GL (Fin n) (ZMod 2)) : ↥(StatedSL n (ZMod 2)) := ⟨M, mem_statedSL M⟩

@[simp] theorem mat_ofGL (M : GL (Fin n) (ZMod 2)) :
    mat (ofGL M) = (M : Matrix (Fin n) (Fin n) (ZMod 2)) := rfl

@[expose] def dmat (g : ↥(StatedSL n (ZMod 2))) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  (mat g⁻¹)ᵀ

theorem dmat_mul (g h : ↥(StatedSL n (ZMod 2))) : dmat (g * h) = dmat g * dmat h := by
  rw [dmat, dmat, dmat, _root_.mul_inv_rev, mat_mul, transpose_mul]

theorem dmat_one : dmat (1 : ↥(StatedSL n (ZMod 2))) = 1 := by
  simp [dmat]

theorem dmat_inv_mul (g : ↥(StatedSL n (ZMod 2))) : dmat g⁻¹ * dmat g = 1 := by
  rw [← dmat_mul, inv_mul_cancel, dmat_one]

theorem transpose_mat_mulVec_of_dmat {g : ↥(StatedSL n (ZMod 2))} {w : Fin n → ZMod 2}
    (hw : dmat g *ᵥ w = w) : (mat g)ᵀ *ᵥ w = w := by
  conv_lhs => rw [← hw]
  rw [dmat, mulVec_mulVec, ← transpose_mul, mat_inv_mul, transpose_one, one_mulVec]

@[expose] def invT (M : GL (Fin n) (ZMod 2)) : GL (Fin n) (ZMod 2) where
  val := ((M⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ
  inv := (M : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ
  val_inv := by rw [← transpose_mul, Units.mul_inv, transpose_one]
  inv_val := by rw [← transpose_mul, Units.inv_mul, transpose_one]

theorem exists_dmat_eq (M : GL (Fin n) (ZMod 2)) :
    ∃ g : ↥(StatedSL n (ZMod 2)), dmat g = (M : Matrix (Fin n) (Fin n) (ZMod 2)) :=
  ⟨ofGL (invT M), transpose_transpose _⟩

@[expose] def fixN (B : Subgroup ↥(StatedSL n (ZMod 2))) : Submodule (ZMod 2) (Fin n → ZMod 2) where
  carrier := {x | ∀ g ∈ B, mat g *ᵥ x = x}
  add_mem' := fun ha hb g hg => by rw [mulVec_add, ha g hg, hb g hg]
  zero_mem' := fun g _ => mulVec_zero _
  smul_mem' := fun c x hx g hg => by rw [mulVec_smul, hx g hg]

theorem mem_fixN {B : Subgroup ↥(StatedSL n (ZMod 2))} {x : Fin n → ZMod 2} :
    x ∈ fixN B ↔ ∀ g ∈ B, mat g *ᵥ x = x := Iff.rfl

@[expose] def commN (B : Subgroup ↥(StatedSL n (ZMod 2))) : Submodule (ZMod 2) (Fin n → ZMod 2) :=
  Submodule.span (ZMod 2) {y | ∃ g ∈ B, ∃ x, mat g *ᵥ x - x = y}

theorem sub_mem_commN {B : Subgroup ↥(StatedSL n (ZMod 2))} {g : ↥(StatedSL n (ZMod 2))}
    (hg : g ∈ B) (x : Fin n → ZMod 2) : mat g *ᵥ x - x ∈ commN B :=
  Submodule.subset_span ⟨g, hg, x, rfl⟩

@[expose] def fixD (B : Subgroup ↥(StatedSL n (ZMod 2))) : Submodule (ZMod 2) (Fin n → ZMod 2) where
  carrier := {x | ∀ g ∈ B, dmat g *ᵥ x = x}
  add_mem' := fun ha hb g hg => by rw [mulVec_add, ha g hg, hb g hg]
  zero_mem' := fun g _ => mulVec_zero _
  smul_mem' := fun c x hx g hg => by rw [mulVec_smul, hx g hg]

theorem eq_of_dotProduct_eq {v w : Fin n → ZMod 2} (h : ∀ u, v ⬝ᵥ u = w ⬝ᵥ u) : v = w := by
  funext i
  have := h (Pi.single i 1)
  simpa [dotProduct_single] using this

theorem mem_fixD_iff {B : Subgroup ↥(StatedSL n (ZMod 2))} {w : Fin n → ZMod 2} :
    w ∈ fixD B ↔ ∀ y ∈ commN B, w ⬝ᵥ y = 0 := by
  constructor
  · intro hw y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨g, hg, x, rfl⟩ := hy
      have h2 := transpose_mat_mulVec_of_dmat (hw g hg)
      rw [dotProduct_sub, dotProduct_mulVec, ← mulVec_transpose, h2, sub_self]
    | zero => exact dotProduct_zero w
    | add x y _ _ hx hy => rw [dotProduct_add, hx, hy, add_zero]
    | smul c x _ hx => rw [dotProduct_smul, hx, smul_zero]
  · intro h g hg
    apply eq_of_dotProduct_eq
    intro v
    have h1 := h _ (sub_mem_commN (B.inv_mem hg) v)
    rw [dotProduct_sub, sub_eq_zero, dotProduct_mulVec, ← mulVec_transpose] at h1
    exact h1

theorem finrank_fixD_add (B : Subgroup ↥(StatedSL n (ZMod 2))) :
    finrank (ZMod 2) (fixD B) + finrank (ZMod 2) (commN B) = n := by
  have h1 : fixD B = (commN B).dualAnnihilator.comap
      (dotProductEquiv (ZMod 2) (Fin n)).toLinearMap := by
    ext w
    rw [mem_fixD_iff, Submodule.mem_comap, Submodule.mem_dualAnnihilator]
    simp [dotProductEquiv_apply_apply]
  have h2 := Subspace.finrank_add_finrank_dualAnnihilator_eq (commN B)
  rw [Module.finrank_fin_fun (ZMod 2)] at h2
  have h3 : finrank (ZMod 2) ((commN B).dualAnnihilator.comap
      (dotProductEquiv (ZMod 2) (Fin n)).toLinearMap) =
        finrank (ZMod 2) (commN B).dualAnnihilator := by
    rw [Submodule.comap_equiv_eq_map_symm]
    exact LinearEquiv.finrank_map_eq _ _
  rw [h1, h3]
  omega

theorem card_le_two_pow_mul (B : Subgroup ↥(StatedSL n (ZMod 2))) :
    Nat.card B ≤ 2 ^ ((n - finrank (ZMod 2) (fixN B)) * finrank (ZMod 2) (commN B)) := by
  classical
  set F := fixN B
  set C := commN B
  let f : ↥B → (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) := fun g =>
    Matrix.toLin' (mat (g : ↥(StatedSL n (ZMod 2)))) - LinearMap.id
  have hfC : ∀ g : ↥B, ∀ x, f g x ∈ C := fun g x => sub_mem_commN g.2 x
  have hfF : ∀ g : ↥B, F ≤ LinearMap.ker ((f g).codRestrict C (hfC g)) := by
    intro g x hx
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    show mat (g : ↥(StatedSL n (ZMod 2))) *ᵥ x - x = 0
    rw [hx g g.2, sub_self]
  let φ : ↥B → ((Fin n → ZMod 2) ⧸ F) →ₗ[ZMod 2] ↥C := fun g =>
    F.liftQ ((f g).codRestrict C (hfC g)) (hfF g)
  have hinj : Function.Injective φ := by
    intro g h hgh
    apply Subtype.ext
    apply eq_of_mulVec_eq
    intro x
    have := congrArg (fun ψ => ((ψ (Submodule.Quotient.mk x) : ↥C) : Fin n → ZMod 2)) hgh
    simp only [φ, f, Submodule.liftQ_apply, LinearMap.codRestrict_apply, LinearMap.sub_apply,
      Matrix.toLin'_apply, LinearMap.id_apply] at this
    exact sub_left_injective this
  have : Finite (((Fin n → ZMod 2) ⧸ F) →ₗ[ZMod 2] ↥C) := Module.finite_of_finite (ZMod 2)
  have h1 := Nat.card_le_card_of_injective φ hinj
  have h2 := Submodule.finrank_quotient_add_finrank F
  rw [Module.finrank_fin_fun (ZMod 2)] at h2
  have h3 : finrank (ZMod 2) ((Fin n → ZMod 2) ⧸ F) = n - finrank (ZMod 2) F := by omega
  have h4 : Nat.card (((Fin n → ZMod 2) ⧸ F) →ₗ[ZMod 2] ↥C) =
      2 ^ ((n - finrank (ZMod 2) F) * finrank (ZMod 2) C) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Module.finrank_linearMap, Nat.card_zmod, h3]
  exact h1.trans h4.le

theorem finrank_commN_le_of_le {B : Subgroup ↥(StatedSL n (ZMod 2))} (hq : commN B ≤ fixN B) :
    finrank (ZMod 2) (commN B) ≤ finrank (ZMod 2) (fixN B) :=
  Submodule.finrank_mono hq

theorem finrank_fixN_le (B : Subgroup ↥(StatedSL n (ZMod 2))) : finrank (ZMod 2) (fixN B) ≤ n := by
  have := Submodule.finrank_le (fixN B)
  rwa [Module.finrank_fin_fun (ZMod 2)] at this

theorem exists_fixed_of_isPGroup {B : Subgroup ↥(StatedSL n (ZMod 2))} (hB : IsPGroup 2 ↥B)
    {Z : Submodule (ZMod 2) (Fin n → ZMod 2)} (hZ : ∀ g ∈ B, ∀ x ∈ Z, mat g *ᵥ x ∈ Z)
    (hZ0 : Z ≠ ⊥) : ∃ z ∈ Z, z ≠ 0 ∧ z ∈ fixN B := by
  classical
  let X := ↥({z : ↥Z | z ≠ 0} : Set ↥Z)
  have hne : ∀ (g : ↥B) (z : X), (⟨mat (g : ↥(StatedSL n (ZMod 2))) *ᵥ (z.1 : Fin n → ZMod 2),
      hZ g g.2 z.1 z.1.2⟩ : ↥Z) ≠ 0 := by
    intro g z h
    apply z.2
    apply Subtype.ext
    have h1 := congrArg (fun y : ↥Z => mat (g : ↥(StatedSL n (ZMod 2)))⁻¹ *ᵥ (y : Fin n → ZMod 2)) h
    simp only [mulVec_inv_mulVec, ZeroMemClass.coe_zero, mulVec_zero] at h1
    exact h1
  let _ : MulAction ↥B X :=
    { smul := fun g z => ⟨⟨mat (g : ↥(StatedSL n (ZMod 2))) *ᵥ (z.1 : Fin n → ZMod 2),
        hZ g g.2 z.1 z.1.2⟩, hne g z⟩
      one_smul := fun z => by
        apply Subtype.ext; apply Subtype.ext
        show mat (1 : ↥(StatedSL n (ZMod 2))) *ᵥ _ = _
        rw [mat_one, one_mulVec]
      mul_smul := fun g h z => by
        apply Subtype.ext; apply Subtype.ext
        show mat ((g * h : ↥B) : ↥(StatedSL n (ZMod 2))) *ᵥ _ = _
        rw [Subgroup.coe_mul, mat_mul, ← mulVec_mulVec]
        rfl }
  have hcard : ¬ 2 ∣ Nat.card X := by
    have hZc : Nat.card ↥Z = 2 ^ finrank (ZMod 2) Z := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    have hpos : 0 < finrank (ZMod 2) Z := by
      rw [Nat.pos_iff_ne_zero]
      intro h0
      exact hZ0 (Submodule.finrank_eq_zero.1 h0)
    have hX : Nat.card X + 1 = Nat.card ↥Z := by
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Set.card_ne_eq]
      have h3 : 0 < Fintype.card ↥Z := Fintype.card_pos
      omega
    intro hdvd
    have h4 : 2 ∣ Nat.card ↥Z := by
      rw [hZc]
      exact dvd_pow_self 2 hpos.ne'
    omega
  obtain ⟨z, hz⟩ := hB.nonempty_fixed_point_of_prime_not_dvd_card X hcard
  refine ⟨z.1, z.1.2, fun h => z.2 (Subtype.ext h), fun g hg => ?_⟩
  have := congrArg (fun y : X => ((y.1 : ↥Z) : Fin n → ZMod 2)) (hz ⟨g, hg⟩)
  exact this

theorem card_le_of_finrank_fixN_eq_one {B : Subgroup ↥(StatedSL n (ZMod 2))}
    (hcomm : ∀ g ∈ B, ∀ h ∈ B, g * h = h * g) (hB : IsPGroup 2 ↥B)
    (hfix : finrank (ZMod 2) (fixN B) = 1) : Nat.card B ≤ 2 ^ (n - 1) := by
  classical
  obtain ⟨c, hcF, hc0⟩ := (Submodule.ne_bot_iff (fixN B)).1 (fun h => by
    rw [h, finrank_bot] at hfix
    exact zero_ne_one hfix)
  have hcF' : ∀ x ∈ fixN B, x ≠ 0 → x = c := by
    intro x hx hx0
    have hcard : Nat.card ↥(fixN B) = 2 := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hfix, pow_one]
    by_contra hxc
    have h3 : 3 ≤ Nat.card ↥(fixN B) := by
      have : ({⟨0, (fixN B).zero_mem⟩, ⟨x, hx⟩, ⟨c, hcF⟩} : Finset ↥(fixN B)).card = 3 := by
        rw [Finset.card_insert_of_notMem, Finset.card_pair]
        · intro h; exact hxc (congrArg Subtype.val h)
        · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨fun h => hx0 (congrArg Subtype.val h).symm,
            fun h => hc0 (congrArg Subtype.val h).symm⟩
      rw [← this, Nat.card_eq_fintype_card]
      exact Finset.card_le_univ _
    omega
  obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
    by_contra h
    push Not at h
    exact hc0 (funext h)
  have hci : c i = 1 := by
    have : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
    exact this _ hi
  set lam : Fin n → ZMod 2 := Pi.single i 1 with hlam
  have hlc : lam ⬝ᵥ c = 1 := by rw [hlam, single_dotProduct, one_mul, hci]
  let Z : Submodule (ZMod 2) (Fin n → ZMod 2) :=
    { carrier := {x | ∀ g ∈ B, lam ⬝ᵥ (mat g *ᵥ x) = 0}
      add_mem' := fun ha hb g hg => by rw [mulVec_add, dotProduct_add, ha g hg, hb g hg, add_zero]
      zero_mem' := fun g _ => by rw [mulVec_zero, dotProduct_zero]
      smul_mem' := fun a x hx g hg => by rw [mulVec_smul, dotProduct_smul, hx g hg, smul_zero] }
  have hZinv : ∀ g ∈ B, ∀ x ∈ Z, mat g *ᵥ x ∈ Z := by
    intro g hg x hx k hk
    rw [mulVec_mulVec, ← mat_mul]
    exact hx _ (B.mul_mem hk hg)
  have hZ : Z = ⊥ := by
    by_contra hZ0
    obtain ⟨z, hzZ, hz0, hzF⟩ := exists_fixed_of_isPGroup hB hZinv hZ0
    have hzc := hcF' z hzF hz0
    have := hzZ 1 B.one_mem
    rw [mat_one, one_mulVec, hzc, hlc] at this
    exact one_ne_zero this
  let ℓ : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 := dotProductEquiv (ZMod 2) (Fin n) c
  have hℓ : ∀ μ, ℓ μ = μ ⬝ᵥ c := fun μ => by
    rw [dotProductEquiv_apply_apply, dotProduct_comm]
  let ψ : ↥B → ↥(LinearMap.ker ℓ) := fun g =>
    ⟨lam ᵥ* mat (g : ↥(StatedSL n (ZMod 2))) - lam, by
      rw [LinearMap.mem_ker, hℓ, sub_dotProduct, ← dotProduct_mulVec, hcF g g.2, hlc, sub_self]⟩
  have hψ : Function.Injective ψ := by
    intro g h hgh
    have h1 : lam ᵥ* mat (g : ↥(StatedSL n (ZMod 2))) = lam ᵥ* mat (h : ↥(StatedSL n (ZMod 2))) :=
      sub_left_injective (congrArg Subtype.val hgh)
    set f : ↥(StatedSL n (ZMod 2)) := (g : ↥(StatedSL n (ZMod 2))) * (h : ↥(StatedSL n (ZMod 2)))⁻¹
      with hf
    have hfB : f ∈ B := B.mul_mem g.2 (B.inv_mem h.2)
    have hlf : lam ᵥ* mat f = lam := by
      rw [hf, mat_mul, ← vecMul_vecMul, h1, vecMul_vecMul, mat_mul_inv, vecMul_one]
    have hfix' : ∀ x, mat f *ᵥ x - x ∈ Z := by
      intro x k hk
      rw [mulVec_sub, dotProduct_sub, mulVec_mulVec, ← mat_mul, hcomm k hk f hfB, mat_mul,
        ← mulVec_mulVec, dotProduct_mulVec, hlf, sub_self]
    have hf1 : f = 1 := by
      apply eq_of_mulVec_eq
      intro x
      have := hfix' x
      rw [hZ, Submodule.mem_bot, sub_eq_zero] at this
      rw [this, mat_one, one_mulVec]
    apply Subtype.ext
    have := congrArg (· * (h : ↥(StatedSL n (ZMod 2)))) hf1
    simpa [hf] using this
  have h1 := Nat.card_le_card_of_injective ψ hψ
  have h2 : finrank (ZMod 2) (LinearMap.ker ℓ) = n - 1 := by
    have hr := LinearMap.finrank_range_add_finrank_ker ℓ
    rw [Module.finrank_fin_fun (ZMod 2)] at hr
    have hrange : finrank (ZMod 2) (LinearMap.range ℓ) = 1 := by
      have hsurj : LinearMap.range ℓ = ⊤ := by
        rw [eq_top_iff]
        intro a _
        refine ⟨a • lam, ?_⟩
        rw [map_smul, hℓ, hlc, smul_eq_mul, mul_one]
      rw [hsurj, finrank_top, Module.finrank_self]
    omega
  have h3 : Nat.card ↥(LinearMap.ker ℓ) = 2 ^ (n - 1) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, h2]
  exact h1.trans h3.le

theorem exists_mulVec_eq {x y : Fin n → ZMod 2} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ g : ↥(StatedSL n (ZMod 2)), mat g *ᵥ x = y := by
  obtain ⟨f, d, hfd, ht⟩ := CFSG.GroupTheory.GLnTwoSplitting.exists_transvection_apply_eq hx hy
  set e := LinearEquiv.transvection hfd
  have hu : IsUnit (LinearMap.toMatrix' (e : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))) := by
    rw [Matrix.isUnit_iff_isUnit_det, LinearMap.det_toMatrix']
    exact LinearEquiv.isUnit_det' e
  refine ⟨ofGL hu.unit, ?_⟩
  rw [mat_ofGL, IsUnit.unit_spec, LinearMap.toMatrix'_mulVec]
  exact ht

theorem eq_bot_or_eq_top {W : AddSubgroup (Fin n → ZMod 2)}
    (hW : ∀ g : ↥(StatedSL n (ZMod 2)), ∀ x ∈ W, mat g *ᵥ x ∈ W) : W = ⊥ ∨ W = ⊤ := by
  by_cases h : W = ⊥
  · exact Or.inl h
  · right
    obtain ⟨⟨x, hxW⟩, hx0⟩ := AddSubgroup.ne_bot_iff_exists_ne_zero.1 h
    have hx0' : x ≠ 0 := fun h0 => hx0 (Subtype.ext h0)
    rw [eq_top_iff]
    intro y _
    by_cases hy : y = 0
    · rw [hy]
      exact W.zero_mem
    obtain ⟨g, hg⟩ := exists_mulVec_eq hx0' hy
    rw [← hg]
    exact hW g x hxW

theorem eq_bot_or_eq_top_dual {W : AddSubgroup (Fin n → ZMod 2)}
    (hW : ∀ g : ↥(StatedSL n (ZMod 2)), ∀ x ∈ W, dmat g *ᵥ x ∈ W) : W = ⊥ ∨ W = ⊤ := by
  refine eq_bot_or_eq_top fun g x hx => ?_
  obtain ⟨g', hg'⟩ := exists_dmat_eq (g : GL (Fin n) (ZMod 2))
  have := hW g' x hx
  rwa [hg'] at this

theorem exists_conj_of_intertwine {φ : (Fin n → ZMod 2) →+ (Fin n → ZMod 2)} (hφ : φ ≠ 0)
    {A B : ↥(StatedSL n (ZMod 2)) → Matrix (Fin n) (Fin n) (ZMod 2)}
    (hB : ∀ g : ↥(StatedSL n (ZMod 2)), ∃ g', B g' = mat g)
    (h : ∀ g x, φ (A g *ᵥ x) = B g *ᵥ φ x) :
    ∃ P : GL (Fin n) (ZMod 2), (∀ x, (P : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x = φ x) ∧
      ∀ g, (P : Matrix (Fin n) (Fin n) (ZMod 2)) * A g = B g * P := by
  have hR : ∀ g : ↥(StatedSL n (ZMod 2)), ∀ y ∈ φ.range, mat g *ᵥ y ∈ φ.range := by
    rintro g _ ⟨x, rfl⟩
    obtain ⟨g', hg'⟩ := hB g
    exact ⟨A g' *ᵥ x, by rw [h, hg']⟩
  have hsurj : Function.Surjective φ := by
    rcases eq_bot_or_eq_top hR with h0 | h1
    · exfalso
      apply hφ
      refine AddMonoidHom.ext fun x => ?_
      have : φ x ∈ φ.range := ⟨x, rfl⟩
      rw [h0] at this
      exact AddSubgroup.mem_bot.1 this
    · intro y
      have : y ∈ φ.range := by rw [h1]; trivial
      exact this
  have hinj : Function.Injective φ := Finite.injective_iff_surjective.2 hsurj
  set ψ := AddMonoidHom.toZModLinearMap 2 φ with hψ
  have hP₀ : ∀ x, LinearMap.toMatrix' ψ *ᵥ x = φ x := fun x => by
    rw [LinearMap.toMatrix'_mulVec]
    rfl
  have hu : IsUnit (LinearMap.toMatrix' ψ) := by
    rw [Matrix.isUnit_iff_isUnit_det, LinearMap.det_toMatrix']
    exact LinearEquiv.isUnit_det' (LinearEquiv.ofBijective ψ ⟨hinj, hsurj⟩)
  refine ⟨hu.unit, fun x => by rw [IsUnit.unit_spec, hP₀], fun g => ?_⟩
  rw [IsUnit.unit_spec]
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← mulVec_mulVec, ← mulVec_mulVec, hP₀, hP₀, h]

@[expose] def dualHom : ↥(StatedSL n (ZMod 2)) →* ↥(StatedSL n (ZMod 2)) where
  toFun g := ofGL (invT (g : GL (Fin n) (ZMod 2)))
  map_one' := mat_injective (by
    rw [mat_ofGL, mat_one]
    show ((((1 : GL (Fin n) (ZMod 2))⁻¹ : GL (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)))ᵀ = 1
    simp)
  map_mul' g h := mat_injective (by
    rw [mat_mul, mat_ofGL, mat_ofGL, mat_ofGL]
    show ((((g * h : ↥(StatedSL n (ZMod 2))) : GL (Fin n) (ZMod 2))⁻¹ : GL (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2))ᵀ = _
    rw [Subgroup.coe_mul, _root_.mul_inv_rev, Units.val_mul, transpose_mul]
    rfl)

theorem mat_dualHom (g : ↥(StatedSL n (ZMod 2))) : mat (dualHom g) = dmat g := rfl

theorem fixN_map_dualHom (B : Subgroup ↥(StatedSL n (ZMod 2))) :
    fixN (B.map dualHom) = fixD B := by
  ext x
  constructor
  · intro hx g hg
    exact hx _ ⟨g, hg, rfl⟩
  · rintro hx _ ⟨g, hg, rfl⟩
    rw [mat_dualHom]
    exact hx g hg

theorem fixD_ne_bot_of_isPGroup {B : Subgroup ↥(StatedSL n (ZMod 2))} (hB : IsPGroup 2 ↥B)
    (hn : 1 ≤ n) : fixD B ≠ ⊥ := by
  rw [← fixN_map_dualHom]
  have hB' : IsPGroup 2 ↥(B.map dualHom) := hB.map dualHom
  have htop : (⊤ : Submodule (ZMod 2) (Fin n → ZMod 2)) ≠ ⊥ := by
    intro h
    have : (Pi.single ⟨0, by omega⟩ 1 : Fin n → ZMod 2) ∈ (⊥ : Submodule (ZMod 2) _) := by
      rw [← h]; trivial
    rw [Submodule.mem_bot] at this
    have := congrFun this ⟨0, by omega⟩
    simp at this
  obtain ⟨z, -, hz0, hzF⟩ := exists_fixed_of_isPGroup hB' (Z := ⊤) (fun _ _ _ _ => trivial) htop
  intro h
  rw [h, Submodule.mem_bot] at hzF
  exact hz0 hzF

theorem fixN_ne_bot_of_isPGroup {B : Subgroup ↥(StatedSL n (ZMod 2))} (hB : IsPGroup 2 ↥B)
    (hn : 1 ≤ n) : fixN B ≠ ⊥ := by
  have htop : (⊤ : Submodule (ZMod 2) (Fin n → ZMod 2)) ≠ ⊥ := by
    intro h
    have : (Pi.single ⟨0, by omega⟩ 1 : Fin n → ZMod 2) ∈ (⊥ : Submodule (ZMod 2) _) := by
      rw [← h]; trivial
    rw [Submodule.mem_bot] at this
    have := congrFun this ⟨0, by omega⟩
    simp at this
  obtain ⟨z, -, hz0, hzF⟩ := exists_fixed_of_isPGroup hB (Z := ⊤) (fun _ _ _ _ => trivial) htop
  intro h
  rw [h, Submodule.mem_bot] at hzF
  exact hz0 hzF

theorem eq_one_of_forall_commute {z : ↥(StatedSL n (ZMod 2))}
    (hz : ∀ g, z * g = g * z) : z = 1 := by
  apply eq_of_mulVec_eq
  intro x
  rw [mat_one, one_mulVec]
  by_contra hne
  by_cases hx : x = 0
  · rw [hx, mulVec_zero] at hne
    exact hne rfl
  set y := mat z *ᵥ x with hy
  have hy0 : y ≠ 0 := by
    intro h0
    apply hx
    have := mulVec_inv_mulVec z x
    rw [← hy, h0, mulVec_zero] at this
    exact this.symm
  have hind : y ∉ (ZMod 2) ∙ x := by
    rw [CFSG.GroupTheory.GLnTwoSplitting.mem_span_singleton_iff_two]
    rintro (h | h)
    · exact hy0 h
    · exact hne h
  obtain ⟨f, hfx, hfy⟩ := CFSG.GroupTheory.GLnTwoSplitting.exists_dual_eq_one_of_notMem hind
  have hfx' : f x = 0 := hfx x (Submodule.mem_span_singleton_self x)
  let t := LinearEquiv.transvection hfx'
  have hu : IsUnit (LinearMap.toMatrix' (t : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))) := by
    rw [Matrix.isUnit_iff_isUnit_det, LinearMap.det_toMatrix']
    exact LinearEquiv.isUnit_det' t
  set g := ofGL hu.unit with hg
  have hgv : ∀ v, mat g *ᵥ v = v + f v • x := by
    intro v
    rw [hg, mat_ofGL, IsUnit.unit_spec, LinearMap.toMatrix'_mulVec]
    exact CFSG.GroupTheory.GLnTwoSplitting.transvection_apply hfx' v
  have h1 := congrArg (fun k => mat k *ᵥ x) (hz g)
  simp only [mat_mul, ← mulVec_mulVec] at h1
  rw [hgv x, hfx', zero_smul, add_zero, hgv, hfy, one_smul] at h1
  apply hx
  have := congrArg (· - y) h1
  simpa using this.symm

end CFSG.Quasithin.B5.Ln
