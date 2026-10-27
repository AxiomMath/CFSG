module

public import CFSG.LocalAnalysis.StandardType.GGWeylCartan
import CFSG.LieType.Steinberg.OfCartan
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

public section

namespace CFSG.StandardType

open CFSG.LieType.RootSystem
open CFSG.LieType.Steinberg.OfCartan

variable {ι : Type} [Fintype ι] [DecidableEq ι] {C : Matrix ι ι ℤ}

private noncomputable def ratMat (hC : TauCeti.IsFiniteType C)
    (t : (coxeterMatrix hC).Group) : Matrix ι ι ℚ :=
  (ggWeylMat hC t).map (Int.castRingHom ℚ)

private noncomputable def negKer (hC : TauCeti.IsFiniteType C)
    (t : (coxeterMatrix hC).Group) : Submodule ℚ (ι → ℚ) :=
  LinearMap.ker (Matrix.toLin' (ratMat hC t + 1))

private theorem toLin'_ratMat_toRat (hC : TauCeti.IsFiniteType C)
    (t : (coxeterMatrix hC).Group) (v : ι → ℤ) :
    Matrix.toLin' (ratMat hC t) (toRat v) = toRat (weylAction hC t v) := by
  funext k
  rw [ratMat, Matrix.toLin'_apply, toRat_apply, ggWeylMat,
    ← LinearMap.toMatrix'_mulVec (weylAction hC t) v]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, toRat_apply]
  push_cast
  rfl

private theorem mem_negKer_iff (hC : TauCeti.IsFiniteType C) (t : (coxeterMatrix hC).Group)
    (y : ι → ℚ) :
    y ∈ negKer hC t ↔ Matrix.toLin' (ratMat hC t) y = -y := by
  rw [negKer, LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.toLin'_apply]
  constructor
  · intro h; exact eq_neg_iff_add_eq_zero.mpr h
  · intro h; rw [h, neg_add_cancel]

private theorem exists_toRat_eq_smul (x : ι → ℚ) :
    ∃ N : ℕ, 0 < N ∧ ∃ z : ι → ℤ, toRat z = (N : ℚ) • x := by
  classical
  refine ⟨∏ k, (x k).den, Finset.prod_pos fun k _ => (x k).pos,
    fun k => (x k).num * ∏ l ∈ Finset.univ.erase k, ((x l).den : ℤ), funext fun k => ?_⟩
  simp only [toRat_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  rw [← Finset.mul_prod_erase Finset.univ (fun l => ((x l).den : ℚ)) (Finset.mem_univ k),
    ← Rat.mul_den_eq_num]
  ring

private theorem exists_forall_ne_zero {V κ : Type*} [AddCommGroup V] [Module ℚ V] (P : V → Prop)
    (h0 : P 0) (hP : ∀ x y (c : ℚ), P x → P y → P (x + c • y)) (f : κ → V → ℚ)
    (hf : ∀ t x y (c : ℚ), f t (x + c • y) = f t x + c * f t y) (F : Finset κ)
    (hF : ∀ t ∈ F, ∃ y, P y ∧ f t y ≠ 0) : ∃ x, P x ∧ ∀ t ∈ F, f t x ≠ 0 := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨0, h0, by simp⟩
  | insert t F ht ih =>
    obtain ⟨x, hx, hxF⟩ := ih fun s hs => hF s (Finset.mem_insert_of_mem hs)
    obtain ⟨y, hy, hty⟩ := hF t (Finset.mem_insert_self t F)
    obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset
      (insert (-(f t x) / f t y) (F.image fun s => -(f s x) / f s y))
    refine ⟨x + c • y, hP x y c hx hy, fun s hs => ?_⟩
    rw [hf]
    have key : ∀ s, c ≠ -(f s x) / f s y → f s x ≠ 0 → f s x + c * f s y ≠ 0 := by
      intro s hcs hsx h
      by_cases hsy : f s y = 0
      · rw [hsy, mul_zero, add_zero] at h
        exact hsx h
      · exact hcs (by field_simp; linarith)
    rcases Finset.mem_insert.mp hs with rfl | hs
    · intro h
      apply hc
      refine Finset.mem_insert.mpr (Or.inl ?_)
      field_simp
      linarith
    · exact key s (fun h => hc (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨s, hs, h.symm⟩)))
        (hxF s hs)

private theorem exists_dominant (hC : TauCeti.IsFiniteType C) (x : ι → ℤ) :
    ∃ u : (coxeterMatrix hC).Group, ∀ k, 0 ≤ coroot C k (weylAction hC u x) := by
  have := finite_group hC
  obtain ⟨u, hu⟩ := Finite.exists_max fun u : (coxeterMatrix hC).Group => ∑ l, weylAction hC u x l
  refine ⟨u, fun k => by_contra fun hk => ?_⟩
  push Not at hk
  have h := hu ((coxeterMatrix hC).toCoxeterSystem.simple k * u)
  rw [weylAction_mul_apply, weylAction_simple, reflection_apply_coroot] at h
  simp [Finset.sum_sub_distrib, Pi.single_apply] at h
  linarith

private theorem exists_neg_vector (hC : TauCeti.IsFiniteType C) (t : (coxeterMatrix hC).Group)
    (ht : t * t = 1) (hdim : Module.finrank ℚ
      (LinearMap.ker (Matrix.toLin' ((ggWeylMat hC t).map (Int.castRingHom ℚ) + 1))) = 1) :
    ∃ x : ι → ℤ, x ≠ 0 ∧ weylAction hC t x = -x ∧ toRat x ∈ negKer hC t ∧
      ∀ y : ι → ℚ, y ∈ negKer hC t → ∃ c : ℚ, y = c • toRat x := by
  have hdim' : Module.finrank ℚ (negKer hC t) = 1 := hdim
  have hKne : negKer hC t ≠ ⊥ := by
    intro hbot
    have h0 : Module.finrank ℚ (negKer hC t) = 0 := by rw [hbot, finrank_bot]
    omega
  obtain ⟨y, hyK, hy0⟩ := (Submodule.ne_bot_iff (negKer hC t)).mp hKne
  obtain ⟨N, hNpos, z, hz⟩ := exists_toRat_eq_smul y
  have hzK : toRat z ∈ negKer hC t := by
    rw [hz]; exact Submodule.smul_mem _ _ hyK
  have hz0 : toRat z ≠ 0 := by
    rw [hz]
    exact smul_ne_zero (by positivity) hy0
  have hzv : (⟨toRat z, hzK⟩ : negKer hC t) ≠ 0 := by
    intro h
    exact hz0 (congrArg Subtype.val h)
  have hspan0 := (finrank_eq_one_iff_of_nonzero' (K := ℚ) (V := negKer hC t)
    ⟨toRat z, hzK⟩ hzv).mp hdim'
  have hspan : ∀ w : ι → ℚ, w ∈ negKer hC t → ∃ c : ℚ, w = c • toRat z := by
    intro w hw
    obtain ⟨c, hc⟩ := hspan0 ⟨w, hw⟩
    exact ⟨c, (congrArg Subtype.val hc).symm⟩
  have htz : weylAction hC t z = -z := by
    apply toRat_injective
    have h := (mem_negKer_iff hC t (toRat z)).mp hzK
    rw [toLin'_ratMat_toRat] at h
    rw [h, map_neg]
  exact ⟨z, fun h => hz0 (by rw [h, map_zero]), htz, hzK, hspan⟩

private theorem toRat_weylAction_reflection (hC : TauCeti.IsFiniteType C)
    (t : (coxeterMatrix hC).Group) (ht : t * t = 1) (x : ι → ℤ) (hx0 : x ≠ 0)
    (htx : weylAction hC t x = -x)
    (hspan : ∀ y : ι → ℚ, y ∈ negKer hC t → ∃ c : ℚ, y = c • toRat x)
    (v : ι → ℤ) :
    toRat (weylAction hC t v) =
      toRat v - (2 * form hC (toRat x) (toRat v) / form hC (toRat x) (toRat x)) • toRat x := by
  have hx' : toRat x ≠ 0 := fun h => hx0 (toRat_injective (by rw [h, map_zero]))
  have hBxx : form hC (toRat x) (toRat x) ≠ 0 := (form_pos hC hx').ne'
  have htt : weylAction hC t (weylAction hC t v) = v := by
    rw [← weylAction_mul_apply, ht, map_one, Module.End.one_apply]
  let d : ι → ℚ := toRat v - toRat (weylAction hC t v)
  have hdK : d ∈ negKer hC t := by
    rw [mem_negKer_iff]
    change Matrix.toLin' (ratMat hC t)
      (toRat v - toRat (weylAction hC t v)) = -(toRat v - toRat (weylAction hC t v))
    rw [map_sub, toLin'_ratMat_toRat, toLin'_ratMat_toRat, htt]
    abel
  obtain ⟨c, hc⟩ := hspan d hdK
  have hpair : c * form hC (toRat x) (toRat x) = 2 * form hC (toRat x) (toRat v) := by
    have h1 : form hC (toRat x) d = c * form hC (toRat x) (toRat x) := by
      rw [hc, map_smul, smul_eq_mul]
    have htv : form hC (toRat x) (toRat (weylAction hC t v)) =
        - form hC (toRat x) (toRat v) := by
      have h := form_weylAction hC t x v
      rw [htx] at h
      simp only [map_neg, LinearMap.neg_apply] at h
      linarith
    have h3 : form hC (toRat x) d = 2 * form hC (toRat x) (toRat v) := by
      change form hC (toRat x) (toRat v - toRat (weylAction hC t v)) = _
      rw [map_sub, htv]
      ring
    linarith
  have hcval : c = 2 * form hC (toRat x) (toRat v) / form hC (toRat x) (toRat x) := by
    rw [eq_div_iff hBxx]
    exact hpair
  have hsub : toRat v - toRat (weylAction hC t v) = c • toRat x := hc
  have hfin : toRat (weylAction hC t v) = toRat v - c • toRat x := by
    rw [eq_sub_iff_add_eq, add_comm]
    exact (sub_eq_iff_eq_add.mp hsub).symm
  rw [hfin, hcval]

private theorem toRat_conj_simple (hC : TauCeti.IsFiniteType C)
    (w : (coxeterMatrix hC).Group) (i : ι) (v : ι → ℤ) :
    toRat (weylAction hC (w * (coxeterMatrix hC).toCoxeterSystem.simple i * w⁻¹) v) =
      toRat v - (coroot C i (weylAction hC w⁻¹ v) : ℚ) •
        toRat (weylAction hC w (Pi.single i 1)) := by
  rw [weylAction_conj_simple, map_sub, map_zsmul]
  simp only [Int.cast_smul_eq_zsmul]

private theorem coroot_eq_two_form_div (hC : TauCeti.IsFiniteType C)
    (w : (coxeterMatrix hC).Group) (i : ι) (v : ι → ℤ) :
    (coroot C i (weylAction hC w⁻¹ v) : ℚ) =
      2 * form hC (toRat (weylAction hC w (Pi.single i 1))) (toRat v) /
        form hC (toRat (weylAction hC w (Pi.single i 1)))
          (toRat (weylAction hC w (Pi.single i 1))) := by
  have hρ0 : toRat (weylAction hC w (Pi.single i 1)) ≠ 0 :=
    toRat_weylAction_single_ne_zero hC w i
  have hB : form hC (toRat (weylAction hC w (Pi.single i 1)))
      (toRat (weylAction hC w (Pi.single i 1))) ≠ 0 := (form_pos hC hρ0).ne'
  rw [eq_div_iff hB]
  exact coroot_mul_form_self hC w i v

private theorem eq_conj_simple_of_root_smul (hC : TauCeti.IsFiniteType C)
    (t : (coxeterMatrix hC).Group) (x : ι → ℤ) (hx0 : x ≠ 0)
    (hform : ∀ v : ι → ℤ, toRat (weylAction hC t v) =
      toRat v - (2 * form hC (toRat x) (toRat v) / form hC (toRat x) (toRat x)) • toRat x)
    (w : (coxeterMatrix hC).Group) (i : ι) (c : ℚ)
    (hρ : toRat (weylAction hC w (Pi.single i 1)) = c • toRat x) :
    t = w * (coxeterMatrix hC).toCoxeterSystem.simple i * w⁻¹ := by
  have hc0 : c ≠ 0 := by
    intro hc
    have : toRat (weylAction hC w (Pi.single i 1)) = 0 := by rw [hρ, hc, zero_smul]
    exact toRat_weylAction_single_ne_zero hC w i this
  have hx' : toRat x ≠ 0 := fun h => hx0 (toRat_injective (by rw [h, map_zero]))
  have hBxx : form hC (toRat x) (toRat x) ≠ 0 := (form_pos hC hx').ne'
  apply weylAction_injective hC
  refine LinearMap.ext fun v => ?_
  apply toRat_injective
  rw [hform v]
  have hconj := toRat_conj_simple hC w i v
  have hscalar := coroot_eq_two_form_div hC w i v
  rw [hconj, hscalar, hρ]
  have h1 : form hC (c • toRat x) (toRat v) = c * form hC (toRat x) (toRat v) := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  have h2 : form hC (c • toRat x) (c • toRat x) = c ^ 2 * form hC (toRat x) (toRat x) := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  have hcoef : (2 * form hC (c • toRat x) (toRat v) / form hC (c • toRat x) (c • toRat x)) * c =
      2 * form hC (toRat x) (toRat v) / form hC (toRat x) (toRat x) := by
    rw [h1, h2]
    field_simp
    try ring
  rw [smul_smul, hcoef]

private theorem form_neg_of_nonpos (hC : TauCeti.IsFiniteType C)
    (γ : ι → ℤ) (hγ : γ ≤ 0) (hγne : γ ≠ 0) (y : ι → ℤ)
    (hpos : ∀ l, 0 < form hC (toRat y) (toRat (Pi.single l 1))) :
    form hC (toRat y) (toRat γ) < 0 := by
  have hpos' : ∀ l, 0 < form hC (toRat y) (Pi.single l (1 : ℚ)) := fun l =>
    by simpa only [toRat_single] using hpos l
  rw [form_eq_sum]
  have hterm_le : ∀ l ∈ (Finset.univ : Finset ι),
      (toRat γ) l * form hC (toRat y) (Pi.single l (1 : ℚ)) ≤ 0 := by
    intro l _
    rw [toRat_apply]
    exact mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hγ l) (hpos' l).le
  have hterm_lt : ∃ l ∈ (Finset.univ : Finset ι),
      (toRat γ) l * form hC (toRat y) (Pi.single l (1 : ℚ)) < 0 := by
    obtain ⟨l₀, hl₀⟩ : ∃ l, γ l ≠ 0 := by
      by_contra h
      push Not at h
      exact hγne (funext h)
    refine ⟨l₀, Finset.mem_univ l₀, ?_⟩
    rw [toRat_apply]
    exact mul_neg_of_neg_of_pos (by exact_mod_cast (lt_of_le_of_ne (hγ l₀) hl₀)) (hpos' l₀)
  have hs := Finset.sum_lt_sum hterm_le hterm_lt
  simpa using hs

private theorem exists_v₀ (hC : TauCeti.IsFiniteType C) (x : ι → ℤ) (hx0 : x ≠ 0)
    (hB : ∀ (w : (coxeterMatrix hC).Group) (i : ι) (c : ℚ),
      toRat (weylAction hC w (Pi.single i 1)) ≠ c • toRat x) :
    ∃ v₀ : ι → ℤ, form hC (toRat x) (toRat v₀) = 0 ∧
      ∀ (w : (coxeterMatrix hC).Group) (i : ι),
        form hC (toRat (weylAction hC w (Pi.single i 1))) (toRat v₀) ≠ 0 := by
  classical
  have hx' : toRat x ≠ 0 := fun h => hx0 (toRat_injective (by rw [h, map_zero]))
  have hBxx : form hC (toRat x) (toRat x) ≠ 0 := (form_pos hC hx').ne'
  have hroot : ∀ ρ : ι → ℤ, ρ ∈ roots hC ∅ →
      ∃ y : ι → ℚ, form hC (toRat x) y = 0 ∧ form hC (toRat ρ) y ≠ 0 := by
    intro ρ hρ
    by_contra h
    push Not at h
    let r0 : ι → ℚ := toRat ρ -
      (form hC (toRat ρ) (toRat x) / form hC (toRat x) (toRat x)) • toRat x
    have hxr0 : form hC (toRat x) r0 = 0 := by
      dsimp only [r0]
      rw [map_sub, map_smul, form_comm hC (toRat x) (toRat ρ), smul_eq_mul]
      field_simp
      ring
    have hρr0 : form hC (toRat ρ) r0 = 0 := h r0 hxr0
    have hr0r0 : form hC r0 r0 = 0 := by
      dsimp only [r0]
      rw [map_sub, map_smul, smul_eq_mul, form_comm hC r0 (toRat ρ), hρr0,
        form_comm hC r0 (toRat x), hxr0]
      ring
    have hr0 : r0 = 0 := by
      by_contra hne
      exact (form_pos hC hne).ne' hr0r0
    have hsmul : toRat ρ =
        (form hC (toRat ρ) (toRat x) / form hC (toRat x) (toRat x)) • toRat x := by
      dsimp only [r0] at hr0
      exact sub_eq_zero.mp hr0
    rcases hρ with ⟨w, i, rfl⟩ | ⟨w, i, hi, -⟩
    · exact hB w i _ hsmul
    · exact absurd hi (by simp)
  obtain ⟨y, hyP, hyne⟩ := exists_forall_ne_zero
    (fun y : ι → ℚ => form hC (toRat x) y = 0)
    (by simp)
    (fun a b c ha hb => by simp [map_add, map_smul, ha, hb, smul_eq_mul])
    (fun ρ y => form hC (toRat ρ) y)
    (fun ρ a b c => by simp [map_add, map_smul, smul_eq_mul])
    ((finite_roots hC ∅).toFinset)
    (fun ρ hρF => hroot ρ ((finite_roots hC ∅).mem_toFinset.mp hρF))
  obtain ⟨N, hNpos, v₀, hv₀⟩ := exists_toRat_eq_smul y
  refine ⟨v₀, ?_, ?_⟩
  · rw [hv₀, map_smul, smul_eq_mul, hyP, mul_zero]
  · intro w i
    have hrootmem : weylAction hC w (Pi.single i 1) ∈ roots hC ∅ := Or.inl ⟨w, i, rfl⟩
    have hmem : weylAction hC w (Pi.single i 1) ∈ (finite_roots hC ∅).toFinset :=
      (finite_roots hC ∅).mem_toFinset.mpr hrootmem
    have hne := hyne _ hmem
    rw [hv₀, map_smul, smul_eq_mul]
    exact mul_ne_zero (by positivity) hne

private theorem false_of_no_root_smul (hC : TauCeti.IsFiniteType C)
    (t : (coxeterMatrix hC).Group) (x : ι → ℤ) (hx0 : x ≠ 0)
    (hxK : toRat x ∈ negKer hC t)
    (hspan : ∀ y : ι → ℚ, y ∈ negKer hC t → ∃ c : ℚ, y = c • toRat x)
    (htx : weylAction hC t x = -x)
    (hform : ∀ v : ι → ℤ, toRat (weylAction hC t v) =
      toRat v - (2 * form hC (toRat x) (toRat v) / form hC (toRat x) (toRat x)) • toRat x)
    (hB : ∀ (w : (coxeterMatrix hC).Group) (i : ι) (c : ℚ),
      toRat (weylAction hC w (Pi.single i 1)) ≠ c • toRat x) : False := by
  obtain ⟨v₀, hxv₀, hv₀ne⟩ := exists_v₀ hC x hx0 hB
  obtain ⟨u, hu⟩ := exists_dominant hC v₀
  have hleft : ∀ k, form hC (toRat (Pi.single k 1)) (toRat (weylAction hC u v₀)) =
      symmetrizer hC k * (coroot C k (weylAction hC u v₀) : ℚ) := by
    intro k
    rw [toRat_single, form_single_left, coroot_apply]
    push_cast
    simp only [toRat_apply]
  have hpos : ∀ k, 0 < coroot C k (weylAction hC u v₀) := by
    intro k
    have hne : form hC (toRat (Pi.single k 1)) (toRat (weylAction hC u v₀)) ≠ 0 := by
      have h1 : form hC (toRat (weylAction hC u⁻¹ (Pi.single k 1))) (toRat v₀) ≠ 0 :=
        hv₀ne u⁻¹ k
      have h2 := form_weylAction hC u (weylAction hC u⁻¹ (Pi.single k 1)) v₀
      rw [weylAction_apply_inv_apply] at h2
      rw [h2]
      exact h1
    have hc : (coroot C k (weylAction hC u v₀) : ℚ) ≠ 0 := by
      intro hc
      exact hne (by rw [hleft k, hc, mul_zero])
    have hc' : coroot C k (weylAction hC u v₀) ≠ 0 :=
      fun h => hc (by rw [h]; exact Int.cast_zero)
    exact lt_of_le_of_ne (hu k) hc'.symm
  have ht_v₀ : weylAction hC t v₀ = v₀ := by
    apply toRat_injective
    rw [hform v₀, hxv₀]
    simp
  have ht'y : weylAction hC (u * t * u⁻¹) (weylAction hC u v₀) = weylAction hC u v₀ := by
    simp only [weylAction_mul_apply, weylAction_inv_apply_apply, ht_v₀]
  have ht'ne : u * t * u⁻¹ ≠ 1 := by
    intro h
    have ht1 : t = 1 := by
      calc t = u⁻¹ * (u * t * u⁻¹) * u := by group
        _ = u⁻¹ * 1 * u := by rw [h]
        _ = 1 := by group
    have hxneg : x = -x := by
      rw [← htx, ht1, map_one, Module.End.one_apply]
    have h2 : x + x = 0 := eq_neg_iff_add_eq_zero.mp hxneg
    have hz : toRat x = 0 := by
      have h3 : (2 : ℚ) • toRat x = 0 := by
        rw [two_smul, ← map_add, h2, map_zero]
      rcases (smul_eq_zero.mp h3) with h | h
      · norm_num at h
      · exact h
    exact hx0 (toRat_injective (by rw [hz, map_zero]))
  obtain ⟨i, hi⟩ := (coxeterMatrix hC).toCoxeterSystem.exists_rightDescent_of_ne_one ht'ne
  have hγnonpos : weylAction hC (u * t * u⁻¹) (Pi.single i 1) ≤ 0 :=
    (isRightDescent_iff hC (u * t * u⁻¹) i).mp hi
  have hγne : weylAction hC (u * t * u⁻¹) (Pi.single i 1) ≠ 0 :=
    weylAction_single_ne_zero hC (u * t * u⁻¹) i
  have hposform : ∀ l, 0 < form hC (toRat (weylAction hC u v₀)) (toRat (Pi.single l 1)) := by
    intro l
    rw [form_comm, hleft l]
    exact mul_pos (symmetrizer_pos hC l) (by exact_mod_cast hpos l)
  have hsum_neg : form hC (toRat (weylAction hC u v₀))
      (toRat (weylAction hC (u * t * u⁻¹) (Pi.single i 1))) < 0 :=
    form_neg_of_nonpos hC _ hγnonpos hγne _ hposform
  have hsum_pos : 0 < form hC (toRat (weylAction hC u v₀))
      (toRat (weylAction hC (u * t * u⁻¹) (Pi.single i 1))) := by
    have h := form_weylAction hC (u * t * u⁻¹) (weylAction hC u v₀) (Pi.single i 1)
    rw [ht'y] at h
    rw [h, form_comm, hleft i]
    exact mul_pos (symmetrizer_pos hC i) (by exact_mod_cast hpos i)
  linarith

theorem ggWeyl_isReflection_of_finrank {ι : Type} [Fintype ι] [DecidableEq ι] {C : Matrix ι ι ℤ}
    (hC : TauCeti.IsFiniteType C) (t : (coxeterMatrix hC).Group) (ht : t * t = 1)
    (hdim : Module.finrank ℚ
      (LinearMap.ker (Matrix.toLin' ((ggWeylMat hC t).map (Int.castRingHom ℚ) + 1))) = 1) :
    ∃ (g : (coxeterMatrix hC).Group) (i : ι),
      t = g * (coxeterMatrix hC).toCoxeterSystem.simple i * g⁻¹ := by
  obtain ⟨x, hx0, htx, hxK, hspan⟩ := exists_neg_vector hC t ht hdim
  have hform := toRat_weylAction_reflection hC t ht x hx0 htx hspan
  by_cases hA : ∃ (w : (coxeterMatrix hC).Group) (i : ι) (c : ℚ),
      toRat (weylAction hC w (Pi.single i 1)) = c • toRat x
  · obtain ⟨w, i, c, hc⟩ := hA
    exact ⟨w, i, eq_conj_simple_of_root_smul hC t x hx0 hform w i c hc⟩
  · exact False.elim (false_of_no_root_smul hC t x hx0 hxK hspan htx hform
      (fun w i c h => hA ⟨w, i, c, h⟩))

end CFSG.StandardType
