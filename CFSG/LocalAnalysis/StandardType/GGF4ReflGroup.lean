module

public import CFSG.LocalAnalysis.StandardType.GGF4B3CoreRep
public import CFSG.LocalAnalysis.StandardType.GGF4ReflData
import CFSG.LocalAnalysis.StandardType.GGF4RankFour
import CFSG.GroupTheory.ConjClassCover
import Mathlib.Tactic.Group
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.StandardType.F4Model

private theorem M4_mul_assoc (x y z : M4) : (x.mul y).mul z = x.mul (y.mul z) := by
  apply M4.toMat_injective
  rw [M4.toMat_mul, M4.toMat_mul, M4.toMat_mul, M4.toMat_mul, mul_assoc]

private theorem M4_mul_one (x : M4) : x.mul M4.one = x := by
  apply M4.toMat_injective
  rw [M4.toMat_mul, M4.toMat_one, mul_one]

private theorem M4_one_mul (x : M4) : M4.one.mul x = x := by
  apply M4.toMat_injective
  rw [M4.toMat_mul, M4.toMat_one, one_mul]

private theorem evalW_append (l l' : List (Fin 4)) :
    evalW (l ++ l') = (evalW l).mul (evalW l') := by
  induction l with
  | nil =>
    change evalW l' = M4.one.mul (evalW l')
    exact (M4_one_mul (evalW l')).symm
  | cons i l ih =>
    change (Sm i).mul (evalW (l ++ l')) = ((Sm i).mul (evalW l)).mul (evalW l')
    rw [ih, M4_mul_assoc]

private theorem evalW_reverse_cons (i : Fin 4) (l : List (Fin 4)) :
    evalW (i :: l).reverse = (evalW l.reverse).mul (Sm i) := by
  rw [List.reverse_cons, evalW_append]
  change (evalW l.reverse).mul ((Sm i).mul M4.one) = (evalW l.reverse).mul (Sm i)
  rw [M4_mul_one]

private theorem evalW_mul_reverse (l : List (Fin 4)) :
    (evalW l).mul (evalW l.reverse) = M4.one := by
  induction l with
  | nil => exact M4_mul_one M4.one
  | cons i l ih =>
    rw [show evalW (i :: l) = (Sm i).mul (evalW l) from rfl, evalW_reverse_cons]
    calc ((Sm i).mul (evalW l)).mul ((evalW l.reverse).mul (Sm i))
        = (((Sm i).mul (evalW l)).mul (evalW l.reverse)).mul (Sm i) := by
          rw [M4_mul_assoc ((Sm i).mul (evalW l)) (evalW l.reverse) (Sm i)]
      _ = ((Sm i).mul ((evalW l).mul (evalW l.reverse))).mul (Sm i) := by
          rw [M4_mul_assoc (Sm i) (evalW l) (evalW l.reverse)]
      _ = ((Sm i).mul M4.one).mul (Sm i) := by rw [ih]
      _ = (Sm i).mul (Sm i) := by rw [M4_mul_one]
      _ = M4.one := Sm_sq i

private theorem evalW_reverse_mul (l : List (Fin 4)) :
    (evalW l.reverse).mul (evalW l) = M4.one := by
  simpa only [List.reverse_reverse] using evalW_mul_reverse l.reverse

private theorem conjW_reverse (w : List (Fin 4)) (x : M4) : conjW w.reverse (conjW w x) = x := by
  apply M4.toMat_injective
  unfold conjW
  rw [List.reverse_reverse]
  simp only [M4.toMat_mul]
  have h1 : (evalW w.reverse).toMat * (evalW w).toMat = 1 := by
    rw [← M4.toMat_mul, evalW_reverse_mul, M4.toMat_one]
  calc (evalW w.reverse).toMat *
        (((evalW w).toMat * (x.toMat * (evalW w.reverse).toMat)) * (evalW w).toMat)
      = ((evalW w.reverse).toMat * (evalW w).toMat) * x.toMat *
          ((evalW w.reverse).toMat * (evalW w).toMat) := by
        simp only [mul_assoc]
    _ = (1 : Matrix (Fin 4) (Fin 4) ℤ) * x.toMat * 1 := by rw [h1]
    _ = x.toMat := by simp

namespace F4Rep

variable {W : Type} [Group W] (R : F4Rep W)

theorem commute_of_commb {u v : W} {x y : M4} (hu : R.ρ u = x.toMat)
    (hv : R.ρ v = y.toMat) (h : commb x y = true) : Commute u v := by
  rw [commute_iff_eq]
  apply R.inj
  rw [map_mul, map_mul, hu, hv, ← M4.toMat_mul, ← M4.toMat_mul, (commb_iff x y).1 h]

theorem commb_of_commute {u v : W} {x y : M4} (hu : R.ρ u = x.toMat)
    (hv : R.ρ v = y.toMat) (h : Commute u v) : commb x y = true := by
  rw [commb_iff x y]
  apply M4.toMat_injective
  rw [M4.toMat_mul, M4.toMat_mul, ← hu, ← hv, ← map_mul, ← map_mul, h.eq]

private theorem rho_conj_s {i : Fin 4} {t : W} {x : M4} (hx : R.ρ t = x.toMat) :
    R.ρ (R.s i * t * (R.s i)⁻¹) = ((Sm i).mul (x.mul (Sm i))).toMat := by
  rw [R.s_inv i]
  exact R.rho_mul3 (R.hs i) hx (R.hs i)

noncomputable def cls (t : W) : Fin 4 := by
  classical
  exact if h : ∃ x, x < 24 ∧ R.ρ t = (Rm x).toMat then T1 h.choose else 0

theorem cls_eq {t : W} {x : ℕ} (hx : x < 24) (h : R.ρ t = (Rm x).toMat) : R.cls t = T1 x := by
  classical
  have hex : ∃ y, y < 24 ∧ R.ρ t = (Rm y).toMat := ⟨x, hx, h⟩
  have hcls : R.cls t = T1 hex.choose := by
    unfold cls
    rw [dif_pos hex]
  rw [hcls]
  congr 1
  exact Rm_inj hex.choose hex.choose_spec.1 x hx
    (M4.toMat_injective (hex.choose_spec.2.symm.trans h))

theorem exists_isRefl_of_lt {x : ℕ} (hx : x < 24) : ∃ t, R.IsRefl t ∧ R.ρ t = (Rm x).toMat := by
  obtain ⟨-, hstage⟩ := stage1 x hx
  refine ⟨R.wd (W1 x).reverse * R.s (T1 x) * (R.wd (W1 x).reverse)⁻¹,
    ⟨R.wd (W1 x).reverse, T1 x, rfl⟩, ?_⟩
  rw [R.rho_conj_wd ((W1 x).reverse) (R.hs (T1 x))]
  rw [← hstage, conjW_reverse]

theorem cls_eq_one_or_two {t : W} (ht : R.IsRefl t) : R.cls t = 1 ∨ R.cls t = 2 := by
  obtain ⟨x, hx, hxρ⟩ := R.refl_rep ht
  rw [R.cls_eq hx hxρ]
  exact (stage1 x hx).1

private theorem cls_conj_s (i : Fin 4) {t : W} (ht : R.IsRefl t) :
    R.cls (R.s i * t * (R.s i)⁻¹) = R.cls t := by
  obtain ⟨x, hx, hxρ⟩ := R.refl_rep ht
  obtain ⟨y, hy, hyρ⟩ := R.refl_rep (ht.conj (R.s i))
  rw [R.cls_eq hx hxρ, R.cls_eq hy hyρ]
  refine T1_conj_simple i x hx y hy ?_
  apply M4.toMat_injective
  rw [← hyρ, ← R.rho_conj_s hxρ]

private theorem cls_conj_aux (g : W) :
    ∀ t, R.IsRefl t → R.cls (g * t * g⁻¹) = R.cls t := by
  have hg : g ∈ Subgroup.closure (Set.range R.s) := by
    rw [R.gen]
    exact Subgroup.mem_top g
  refine Subgroup.closure_induction (p := fun g _ => ∀ t, R.IsRefl t →
    R.cls (g * t * g⁻¹) = R.cls t) ?_ ?_ ?_ ?_ hg
  · rintro g ⟨i, rfl⟩
    intro t ht
    exact cls_conj_s R i ht
  · intro t _
    simp
  · intro x y _ _ hx hy t ht
    rw [show x * y * t * (x * y)⁻¹ = x * (y * t * y⁻¹) * x⁻¹ by group]
    exact (hx (y * t * y⁻¹) (ht.conj y)).trans (hy t ht)
  · intro x _ hx t ht
    have hconj : R.IsRefl (x⁻¹ * t * x) := by simpa using ht.conj x⁻¹
    have h := hx (x⁻¹ * t * x) hconj
    rw [show x * (x⁻¹ * t * x) * x⁻¹ = t by group] at h
    simpa using h.symm

theorem cls_conj {t : W} (ht : R.IsRefl t) (g : W) : R.cls (g * t * g⁻¹) = R.cls t :=
  cls_conj_aux R g t ht

theorem exists_conj_of_cls_eq {t u : W} (ht : R.IsRefl t) (hu : R.IsRefl u)
    (h : R.cls t = R.cls u) : ∃ g : W, g * t * g⁻¹ = u := by
  obtain ⟨x, hx, hxρ⟩ := R.refl_rep ht
  obtain ⟨y, hy, hyρ⟩ := R.refl_rep hu
  have hxy : T1 x = T1 y := by
    rw [← R.cls_eq hx hxρ, ← R.cls_eq hy hyρ]
    exact h
  have hxconj : R.wd (W1 x) * t * (R.wd (W1 x))⁻¹ = R.s (T1 x) :=
    R.conj_wd_eq hxρ (R.hs (T1 x)) (stage1 x hx).2
  have hyconj : R.wd (W1 y) * u * (R.wd (W1 y))⁻¹ = R.s (T1 y) :=
    R.conj_wd_eq hyρ (R.hs (T1 y)) (stage1 y hy).2
  refine ⟨(R.wd (W1 y))⁻¹ * R.wd (W1 x), ?_⟩
  calc (R.wd (W1 y))⁻¹ * R.wd (W1 x) * t * ((R.wd (W1 y))⁻¹ * R.wd (W1 x))⁻¹
      = (R.wd (W1 y))⁻¹ * (R.wd (W1 x) * t * (R.wd (W1 x))⁻¹) * R.wd (W1 y) := by
        group
    _ = (R.wd (W1 y))⁻¹ * R.s (T1 x) * R.wd (W1 y) := by rw [hxconj]
    _ = (R.wd (W1 y))⁻¹ * R.s (T1 y) * R.wd (W1 y) := by rw [hxy]
    _ = (R.wd (W1 y))⁻¹ * (R.wd (W1 y) * u * (R.wd (W1 y))⁻¹) * R.wd (W1 y) := by
        rw [hyconj]
    _ = u := by group

theorem exists_endpoint {a₀ a₁ a₂ : W} (h₀ : R.IsRefl a₀) (h₁ : R.IsRefl a₁) (h₂ : R.IsRefl a₂)
    (h₀₁ : orderOf (a₀ * a₁) = 3) (h₀₂ : orderOf (a₀ * a₂) = 2)
    (h₁₂ : orderOf (a₁ * a₂) = 3 ∨ orderOf (a₁ * a₂) = 4) :
    ∃ t, R.IsRefl t ∧ t ≠ a₀ ∧ t ≠ a₁ ∧ t ≠ a₂ ∧ Commute t a₀ ∧ Commute t a₁ ∧
      Commute t a₂ := by
  obtain ⟨x₀, hx₀, hx₀ρ⟩ := R.refl_rep h₀
  obtain ⟨x₁, hx₁, hx₁ρ⟩ := R.refl_rep h₁
  obtain ⟨x₂, hx₂, hx₂ρ⟩ := R.refl_rep h₂
  have h₀₁' : ord3b (Rm x₀) (Rm x₁) = true := R.ord3b_of hx₀ρ hx₁ρ h₀₁
  have h₀₂' : ord2b (Rm x₀) (Rm x₂) = true := R.ord2b_of hx₀ρ hx₂ρ h₀₂
  have h₁₂' : ord3b (Rm x₁) (Rm x₂) = true ∨ ord4b (Rm x₁) (Rm x₂) = true := by
    rcases h₁₂ with h | h
    · exact Or.inl (R.ord3b_of hx₁ρ hx₂ρ h)
    · exact Or.inr (R.ord4b_of hx₁ρ hx₂ρ h)
  obtain ⟨y, hy, hok⟩ := endpoint_exists x₀ hx₀ x₁ hx₁ h₀₁' x₂ hx₂ h₀₂' h₁₂'
  obtain ⟨t, htrefl, htρ⟩ := R.exists_isRefl_of_lt hy
  simp only [endOk, Bool.and_eq_true, bne_iff_ne, and_assoc] at hok
  have hcomm₀ : Commute t a₀ := commute_of_commb R htρ hx₀ρ hok.1
  have hcomm₁ : Commute t a₁ := commute_of_commb R htρ hx₁ρ hok.2.1
  have hcomm₂ : Commute t a₂ := commute_of_commb R htρ hx₂ρ hok.2.2.1
  refine ⟨t, htrefl, ?_, ?_, ?_, hcomm₀, hcomm₁, hcomm₂⟩
  · intro heq
    have hmat : Rm y = Rm x₀ := by
      apply M4.toMat_injective
      rw [← htρ, heq, hx₀ρ]
    exact hok.2.2.2.1 (Rm_inj y hy x₀ hx₀ hmat)
  · intro heq
    have hmat : Rm y = Rm x₁ := by
      apply M4.toMat_injective
      rw [← htρ, heq, hx₁ρ]
    exact hok.2.2.2.2.1 (Rm_inj y hy x₁ hx₁ hmat)
  · intro heq
    have hmat : Rm y = Rm x₂ := by
      apply M4.toMat_injective
      rw [← htρ, heq, hx₂ρ]
    exact hok.2.2.2.2.2 (Rm_inj y hy x₂ hx₂ hmat)

private def frameSet (a : W) : Set W :=
  {u | R.IsRefl u ∧ R.cls u = R.cls a ∧ (u = a ∨ Commute u a)}

private theorem mem_frameSet_self {a : W} (ha : R.IsRefl a) : a ∈ frameSet R a :=
  ⟨ha, rfl, Or.inl rfl⟩

private theorem frame_mem_of {a b u : W} (ha : R.IsRefl a) (hb : R.IsRefl b)
    (hcls : R.cls b = R.cls a) (hab : Commute a b) (hu : R.IsRefl u)
    (hucls : R.cls u = R.cls a) (hua : u = a ∨ Commute u a) :
    u = b ∨ Commute u b := by
  obtain ⟨xa, hxa, hxaρ⟩ := R.refl_rep ha
  obtain ⟨xb, hxb, hxbρ⟩ := R.refl_rep hb
  obtain ⟨xu, hxu, hxuρ⟩ := R.refl_rep hu
  have hTb : T1 xb = T1 xa := by
    rw [← R.cls_eq hxb hxbρ, ← R.cls_eq hxa hxaρ]
    exact hcls
  have hcommab : commb (Rm xa) (Rm xb) = true := commb_of_commute R hxaρ hxbρ hab
  have hTu : T1 xu = T1 xa := by
    rw [← R.cls_eq hxu hxuρ, ← R.cls_eq hxa hxaρ]
    exact hucls
  have hua' : xu = xa ∨ commb (Rm xu) (Rm xa) = true := by
    rcases hua with rfl | hcomm
    · left
      exact Rm_inj xu hxu xa hxa (M4.toMat_injective (hxuρ.symm.trans hxaρ))
    · exact Or.inr (commb_of_commute R hxuρ hxaρ hcomm)
  rcases frame_closed xa hxa xb hxb hTb hcommab xu hxu hTu hua' with hEq | hcomm
  · left
    apply R.inj
    rw [hxuρ, hxbρ, hEq]
  · exact Or.inr (commute_of_commb R hxuρ hxbρ hcomm)

private theorem frameSet_eq {a b : W} (ha : R.IsRefl a) (hb : R.IsRefl b)
    (hcls : R.cls b = R.cls a) (hab : Commute a b) : frameSet R a = frameSet R b := by
  ext u
  constructor
  · rintro ⟨hurefl, hucls, hua⟩
    exact ⟨hurefl, by rw [hucls, ← hcls],
      frame_mem_of R ha hb hcls hab hurefl hucls hua⟩
  · rintro ⟨hurefl, hucls, hua⟩
    exact ⟨hurefl, by rw [hucls, hcls],
      frame_mem_of R hb ha hcls.symm hab.symm hurefl hucls hua⟩

private theorem mem_frameSet_conj {c g u : W}
    (hg : g ∈ Subgroup.centralizer ({c} : Set W)) (hu : u ∈ frameSet R c) :
    g * u * g⁻¹ ∈ frameSet R c := by
  obtain ⟨hurefl, hucls, huc⟩ := hu
  have hcomm : Commute g c := Subgroup.mem_centralizer_singleton_iff.mp hg
  have hgc : g * c * g⁻¹ = c := by
    rw [hcomm.eq, mul_assoc, mul_inv_cancel, mul_one]
  refine ⟨hurefl.conj g, ?_, ?_⟩
  · rw [R.cls_conj hurefl g, hucls]
  · rcases huc with rfl | huc
    · exact Or.inl hgc
    · exact Or.inr (by simpa [hgc] using huc.conj g)

private theorem centralizer_le_normalizer_frameSet (c : W) :
    Subgroup.centralizer ({c} : Set W) ≤ Subgroup.normalizer (frameSet R c) := by
  intro g hg
  rw [Subgroup.mem_set_normalizer_iff]
  intro u
  exact ⟨mem_frameSet_conj R hg, fun hu => by
    have hg' : g⁻¹ ∈ Subgroup.centralizer ({c} : Set W) :=
      (Subgroup.centralizer ({c} : Set W)).inv_mem hg
    have h := mem_frameSet_conj R hg' hu
    convert h using 1; group⟩

theorem centralizer_sup_ne_top {a b : W} (ha : R.IsRefl a) (hb : R.IsRefl b)
    (hcls : R.cls b = R.cls a) (hab : Commute a b) :
    Subgroup.centralizer ({a} : Set W) ⊔ Subgroup.centralizer ({b} : Set W) ≠ ⊤ := by
  obtain ⟨xa, hxa, hxaρ⟩ := R.refl_rep ha
  obtain ⟨r, hr, hrmove⟩ := frame_move xa hxa
  obtain ⟨s, hsrefl, hsρ⟩ := R.exists_isRefl_of_lt hr
  have huρ : R.ρ (s * a * s⁻¹) = ((Rm r).mul ((Rm xa).mul (Rm r))).toMat := by
    have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hsrefl.mul_self
    rw [hsinv]
    exact R.rho_mul3 hsρ hxaρ hsρ
  have hune : s * a * s⁻¹ ∉ frameSet R a := by
    intro hu
    obtain ⟨-, -, hua⟩ := hu
    have hcommua : Commute (s * a * s⁻¹) a := by
      rcases hua with heq | hcomm
      · rw [heq]
      · exact hcomm
    have htrue : commb ((Rm r).mul ((Rm xa).mul (Rm r))) (Rm xa) = true :=
      commb_of_commute R huρ hxaρ hcommua
    rw [hrmove] at htrue
    exact Bool.false_ne_true htrue
  have hF : frameSet R a = frameSet R b := frameSet_eq R ha hb hcls hab
  have hle : Subgroup.centralizer ({a} : Set W) ⊔ Subgroup.centralizer ({b} : Set W) ≤
      Subgroup.normalizer (frameSet R a) := by
    refine sup_le (centralizer_le_normalizer_frameSet R a) ?_
    have h := centralizer_le_normalizer_frameSet R b
    simpa [hF] using h
  intro htop
  have hpoint : s ∈ Subgroup.centralizer ({a} : Set W) ⊔
      Subgroup.centralizer ({b} : Set W) := by
    rw [htop]
    exact Subgroup.mem_top s
  have hnorm : s ∈ Subgroup.normalizer (frameSet R a) := hle hpoint
  rw [Subgroup.mem_set_normalizer_iff] at hnorm
  exact hune ((hnorm a).1 (mem_frameSet_self R ha))

theorem exists_commute_commute_not_commute {a b c : W} (ha : R.IsRefl a) (hb : R.IsRefl b)
    (hc : R.IsRefl c) (hba : R.cls b = R.cls a) (hca : R.cls c ≠ R.cls a) (hab : ¬ Commute a b) :
    ∃ s, R.IsRefl s ∧ Commute s a ∧ Commute s b ∧ ¬ Commute s c := by
  obtain ⟨xa, hxa, hxaρ⟩ := R.refl_rep ha
  obtain ⟨xb, hxb, hxbρ⟩ := R.refl_rep hb
  obtain ⟨xc, hxc, hxcρ⟩ := R.refl_rep hc
  have hTb : T1 xb = T1 xa := by
    rw [← R.cls_eq hxb hxbρ, ← R.cls_eq hxa hxaρ]
    exact hba
  have hTc : T1 xc ≠ T1 xa := by
    intro h
    exact hca (by rw [R.cls_eq hxc hxcρ, R.cls_eq hxa hxaρ, h])
  have hab' : commb (Rm xa) (Rm xb) = false := by
    have hnot : commb (Rm xa) (Rm xb) ≠ true := fun h =>
      hab (commute_of_commb R hxaρ hxbρ h)
    cases h : commb (Rm xa) (Rm xb)
    · rfl
    · exact absurd h hnot
  obtain ⟨s, hs, hsa, hsb, hsc⟩ := plane_exists xa hxa xb hxb hTb hab' xc hxc hTc
  obtain ⟨r, hrrefl, hrρ⟩ := R.exists_isRefl_of_lt hs
  refine ⟨r, hrrefl, commute_of_commb R hrρ hxaρ hsa,
    commute_of_commb R hrρ hxbρ hsb, ?_⟩
  intro hcomm
  have htrue := commb_of_commute R hrρ hxcρ hcomm
  rw [hsc] at htrue
  exact Bool.false_ne_true htrue

private theorem card_filter_T1_one :
    ((Finset.range 24).filter (fun y => T1 y = 1)).card = 12 := by
  decide +kernel

private theorem card_filter_T1_two :
    ((Finset.range 24).filter (fun y => T1 y = 2)).card = 12 := by
  decide +kernel

private theorem ncard_conjugatesOf_ge_twelve [Finite W] {t : W} (ht : R.IsRefl t)
    (c : Fin 4) (hc : c = R.cls t)
    (hcard : ((Finset.range 24).filter (fun y => T1 y = c)).card = 12) :
    12 ≤ (conjugatesOf t).ncard := by
  classical
  let Ys : Finset ℕ := (Finset.range 24).filter (fun y => T1 y = c)
  let f : ℕ → W := fun y => if h : y < 24 then (R.exists_isRefl_of_lt h).choose else 1
  have hf : ∀ y (hy : y < 24), R.IsRefl (f y) ∧ R.ρ (f y) = (Rm y).toMat := by
    intro y hy
    have h : f y = (R.exists_isRefl_of_lt hy).choose := by
      dsimp only [f]
      rw [dif_pos hy]
    rw [h]
    exact (R.exists_isRefl_of_lt hy).choose_spec
  have hfcls : ∀ y (hy : y < 24), R.cls (f y) = T1 y := by
    intro y hy
    exact R.cls_eq hy (hf y hy).2
  have hinj : Set.InjOn f ↑Ys := by
    intro y hy z hz hfyz
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hy hz
    have h1 : (Rm y).toMat = (Rm z).toMat := by
      rw [← (hf y hy.1).2, ← (hf z hz.1).2, hfyz]
    exact Rm_inj y hy.1 z hz.1 (M4.toMat_injective h1)
  have hsub : ((Ys.image f : Finset W) : Set W) ⊆ conjugatesOf t := by
    intro w hw
    rw [Finset.mem_coe, Finset.mem_image] at hw
    obtain ⟨y, hy, rfl⟩ := hw
    rw [Finset.mem_filter, Finset.mem_range] at hy
    obtain ⟨hy24, hyT⟩ := hy
    have hcls : R.cls t = R.cls (f y) := by
      rw [hfcls y hy24, hyT, hc]
    change IsConj t (f y)
    exact isConj_iff.mpr (R.exists_conj_of_cls_eq ht (hf y hy24).1 hcls)
  have hcard' : (Ys.image f).card = 12 := by
    rw [Finset.card_image_of_injOn hinj]
    simpa only [Ys] using hcard
  have hle : ((Ys.image f : Finset W) : Set W).ncard ≤ (conjugatesOf t).ncard :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  rwa [Set.ncard_coe_finset, hcard'] at hle

theorem card_centralizer_le [Finite W] (hW : Nat.card W = 1152) {t : W} (ht : R.IsRefl t) :
    Nat.card (Subgroup.centralizer ({t} : Set W)) ≤ 96 := by
  have hcard : 12 ≤ (conjugatesOf t).ncard := by
    rcases R.cls_eq_one_or_two ht with hc | hc
    · exact ncard_conjugatesOf_ge_twelve R ht 1 hc.symm card_filter_T1_one
    · exact ncard_conjugatesOf_ge_twelve R ht 2 hc.symm card_filter_T1_two
  have hmul := CFSG.GroupTheory.ncard_conjugatesOf_mul_card_centralizer t
  rw [hW] at hmul
  have hle : 12 * Nat.card (Subgroup.centralizer ({t} : Set W)) ≤ 12 * 96 := by
    calc 12 * Nat.card (Subgroup.centralizer ({t} : Set W))
        ≤ (conjugatesOf t).ncard * Nat.card (Subgroup.centralizer ({t} : Set W)) :=
          Nat.mul_le_mul_right _ hcard
      _ = 1152 := hmul
      _ = 12 * 96 := by norm_num
  exact Nat.le_of_mul_le_mul_left hle (by norm_num)

end F4Rep

end CFSG.StandardType.F4Model

end
