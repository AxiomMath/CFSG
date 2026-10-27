module

public import CFSG.Sporadic.Co1Patterson.TwistNativeElem

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Patterson.TwistNative

open Subgroup CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Schreier CFSG.LargeExtraspecial
open CFSG.Blueprint (NativeSporadic.Co1)
open CFSG.EvenSmallLie.OmegaEight (ind bNat vecK)

theorem bv_inj {a b : ℕ} (ha : a < 256) (hb : b < 256) (h : bv a = bv b) : a = b :=
  CFSG.EvenSmallLie.OmegaEight.vecK_injective ha hb (by rw [← plusCoords_bv, ← plusCoords_bv, h])

@[expose] noncomputable def enc (x : Fin 8 → ZMod 2) : ℕ := Classical.choose (exists_bv x)

theorem enc_lt (x : Fin 8 → ZMod 2) : enc x < 256 := (Classical.choose_spec (exists_bv x)).1

theorem bv_enc (x : Fin 8 → ZMod 2) : bv (enc x) = x := (Classical.choose_spec (exists_bv x)).2

theorem enc_bv {c : ℕ} (hc : c < 256) : enc (bv c) = c := bv_inj (enc_lt _) hc (bv_enc _)

theorem foldl_xor_lt (p : ℕ → Bool) (F : ℕ → ℕ) (hF : ∀ i, F i < 256) (l : List ℕ) {a : ℕ}
    (ha : a < 256) : l.foldl (fun acc i => if p i then acc ^^^ F i else acc) a < 256 := by
  induction l generalizing a with
  | nil => exact ha
  | cons i l ih =>
    simp only [List.foldl_cons]
    refine ih ?_
    by_cases hp : p i
    · rw [ite_eq_left hp]
      exact Nat.xor_lt_two_pow (n := 8) ha (hF i)
    · rw [ite_eq_right hp]
      exact ha

theorem colsApply_lt {m : List ℕ} (hm : ∀ k, m.getD k 0 < 256) (v : ℕ) : colsApply m v < 256 :=
  foldl_xor_lt _ _ hm _ (by norm_num)

@[expose] noncomputable def cols (f : (Fin 8 → ZMod 2) →ₗ[ZMod 2] (Fin 8 → ZMod 2)) : List ℕ :=
  (List.range 8).map fun k => enc (f (bv (2 ^ k)))

theorem cols_getD (f : (Fin 8 → ZMod 2) →ₗ[ZMod 2] (Fin 8 → ZMod 2)) {k : ℕ} (hk : k < 8) :
    (cols f).getD k 0 = enc (f (bv (2 ^ k))) := by
  rw [cols, List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map, List.getElem_range]

theorem cols_getD_lt (f : (Fin 8 → ZMod 2) →ₗ[ZMod 2] (Fin 8 → ZMod 2)) (k : ℕ) :
    (cols f).getD k 0 < 256 := by
  by_cases hk : k < 8
  · rw [cols_getD f hk]
    exact enc_lt _
  · rw [List.getD_eq_default _ _ (by simp [cols]; omega)]
    norm_num

theorem hasCols_cols (f : (Fin 8 → ZMod 2) →ₗ[ZMod 2] (Fin 8 → ZMod 2)) : HasCols f (cols f) :=
  fun k hk => by rw [cols_getD f hk, bv_enc]

theorem cols_getD_eq {f : (Fin 8 → ZMod 2) →ₗ[ZMod 2] (Fin 8 → ZMod 2)} {m : List ℕ}
    (h : HasCols f m) (hm : ∀ k < 8, m.getD k 0 < 256) {k : ℕ} (hk : k < 8) :
    (cols f).getD k 0 = m.getD k 0 := by
  rw [cols_getD f hk, h k hk, enc_bv (hm k hk)]

theorem polar_q₀_bv (a b : ℕ) : QuadraticMap.polar q₀ (bv a) (bv b) = ind (ZMod 2) (bNat a b) := by
  have e : ∀ x y : Fin 8 → ZMod 2, QuadraticMap.polar q₀ x y =
      QuadraticMap.polar (CFSG.LieType.Universal.Spin.quadPlus 4 (ZMod 2)) (plusCoords x)
        (plusCoords y) := fun x y => by
    rw [QuadraticMap.polar, QuadraticMap.polar, ← map_add, quadPlus_plusCoords,
      quadPlus_plusCoords, quadPlus_plusCoords]
  rw [e, plusCoords_bv, plusCoords_bv, CFSG.EvenSmallLie.OmegaEight.polar_vecK card_zmod_two]

theorem L₀_le_isometries :
    L₀ ≤ CFSG.Open.timmesfeldIsometries (q₀ : (Fin 8 → ZMod 2) → ZMod 2) :=
  closure_le _ |>.2 fun _ hg => hg.1

theorem q₀_L₀ (l : L₀) (v : Fin 8 → ZMod 2) :
    q₀ ((l : (Fin 8 → ZMod 2) ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) v) = q₀ v :=
  L₀_le_isometries l.2 v

theorem polar_L₀ (l : L₀) (u v : Fin 8 → ZMod 2) :
    QuadraticMap.polar q₀ ((l : (Fin 8 → ZMod 2) ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) u)
      ((l : (Fin 8 → ZMod 2) ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) v) = QuadraticMap.polar q₀ u v := by
  simp only [QuadraticMap.polar, ← map_add, q₀_L₀]

theorem ind_injective {a b : Bool} (h : ind (ZMod 2) a = ind (ZMod 2) b) : a = b := by
  cases a <;> cases b <;> simp_all [ind]

theorem polar_q₀_e₀ (x : Fin 8 → ZMod 2) : QuadraticMap.polar q₀ x (bv 1) = x 4 := by
  rw [← bv_enc x, polar_q₀_bv, bv_apply]
  congr 1
  simp [bNat, show Nat.testBit 1 1 = false from rfl, show Nat.testBit 1 2 = false from rfl,
    show Nat.testBit 1 3 = false from rfl, show Nat.testBit 1 4 = false from rfl,
    show Nat.testBit 1 5 = false from rfl, show Nat.testBit 1 6 = false from rfl,
    show Nat.testBit 1 7 = false from rfl]

@[expose] noncomputable def clean : (Fin 8 → ZMod 2) →ₗ[ZMod 2] (Fin 8 → ZMod 2) :=
  LinearMap.id - (LinearMap.proj (0 : Fin 8)).smulRight (bv 1)

theorem clean_apply (v : Fin 8 → ZMod 2) : clean v = v - v 0 • bv 1 := rfl

theorem bv_one_apply (i : Fin 8) : bv 1 i = if i = 0 then 1 else 0 := by
  rw [bv_apply]
  fin_cases i <;> rfl

theorem clean_bv (u : ℕ) : clean (bv u) = bv (u &&& 254) := by
  funext i
  rw [clean_apply, Pi.sub_apply, Pi.smul_apply, bv_one_apply, bv_apply, bv_apply, bv_apply,
    Nat.testBit_land]
  fin_cases i <;> simp [ind, show Nat.testBit 254 0 = false from rfl,
    show Nat.testBit 254 1 = true from rfl, show Nat.testBit 254 2 = true from rfl,
    show Nat.testBit 254 3 = true from rfl, show Nat.testBit 254 4 = true from rfl,
    show Nat.testBit 254 5 = true from rfl, show Nat.testBit 254 6 = true from rfl,
    show Nat.testBit 254 7 = true from rfl]

theorem clean_bv_one : clean (bv 1) = 0 := by
  rw [clean_bv, show (1 &&& 254 : ℕ) = 0 from rfl, bv_zero]

theorem eq_clean_add (v : Fin 8 → ZMod 2) : v = clean v + v 0 • bv 1 := by
  rw [clean_apply, sub_add_cancel]

@[expose] def W₀ : Submodule (ZMod 2) (Fin 8 → ZMod 2) where
  carrier := {x | x 0 = 0 ∧ x 4 = 0}
  add_mem' {x y} hx hy := ⟨by simp [hx.1, hy.1], by simp [hx.2, hy.2]⟩
  zero_mem' := ⟨rfl, rfl⟩
  smul_mem' c x hx := ⟨by simp [hx.1], by simp [hx.2]⟩

theorem clean_of_mem {x : Fin 8 → ZMod 2} (hx : x ∈ W₀) : clean x = x := by
  rw [clean_apply, hx.1, zero_smul, sub_zero]

theorem mem_wVecs {v : ℕ} : v ∈ wVecs ↔ v < 256 ∧ v.testBit 0 = false ∧ v.testBit 4 = false := by
  simp [wVecs]

theorem bv_mem_W₀ {v : ℕ} (hv : v ∈ wVecs) : bv v ∈ W₀ := by
  obtain ⟨-, h0, h4⟩ := mem_wVecs.1 hv
  exact ⟨by rw [bv_apply]; simp [h0, ind], by rw [bv_apply]; simp [h4, ind]⟩

theorem enc_mem_wVecs {x : Fin 8 → ZMod 2} (hx : x ∈ W₀) : enc x ∈ wVecs := by
  refine mem_wVecs.2 ⟨enc_lt x, ?_, ?_⟩
  · have h := hx.1
    rw [← bv_enc x, bv_apply, ind_eq_zero_iff] at h
    exact h
  · have h := hx.2
    rw [← bv_enc x, bv_apply, ind_eq_zero_iff] at h
    exact h

theorem bv_xorSpan_mem {F : Submodule (ZMod 2) (Fin 8 → ZMod 2)} {vs : List ℕ}
    (hvs : ∀ v ∈ vs, bv v ∈ F) : ∀ t ∈ xorSpan vs, bv t ∈ F := by
  have key : ∀ (S : List ℕ), (∀ s ∈ S, bv s ∈ F) →
      ∀ t ∈ vs.foldl (fun S v => S ++ S.map (· ^^^ v)) S, bv t ∈ F := by
    induction vs with
    | nil => exact fun S hS => hS
    | cons v vs ih =>
      intro S hS
      refine ih (fun w hw => hvs w (List.mem_cons_of_mem _ hw)) _ fun t ht => ?_
      rcases List.mem_append.1 ht with ht | ht
      · exact hS t ht
      · obtain ⟨s, hs, rfl⟩ := List.mem_map.1 ht
        rw [bv_xor]
        exact F.add_mem (hS s hs) (hvs v List.mem_cons_self)
  exact key [0] fun s hs => by
    rw [List.mem_singleton.1 hs, bv_zero]
    exact F.zero_mem

theorem irrWords_lt : ∀ w ∈ irrWords, ∀ j ∈ w, j < 2 := by decide

abbrev K₀ : Subgroup (centralizer ({aNC} : Set NativeSporadic.Co1)) :=
  centralizer ({yH 0} : Set (centralizer ({aNC} : Set NativeSporadic.Co1)))

theorem mem_K₀ {q : centralizer ({aNC} : Set NativeSporadic.Co1)} :
    q ∈ K₀ ↔ q * yH 0 = yH 0 * q :=
  Subgroup.mem_centralizer_singleton_iff

theorem yH_zero_eq : yH 0 = yprodH 1 := by
  rw [← yprodH_two_pow (show 0 < 8 by norm_num), pow_zero]

theorem phi_yH_zero : typeSystemC.φ (yH 0) = 1 :=
  (Setting.phiV₀_eq_one_iff nativeSetting coordIso nativeOmega (yH 0)).2 (yH_mem_QG 0)

theorem vec_yH_zero : typeSystemC.vec (yH 0) = bv 1 := by
  rw [yH_zero_eq, vec_yprodH]

theorem phi_e₀ {h : centralizer ({aNC} : Set NativeSporadic.Co1)} (hh : h ∈ K₀) :
    ((typeSystemC.φ h : L₀) : (Fin 8 → ZMod 2) ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) (bv 1) = bv 1 := by
  have h1 := typeSystemC.vec_conj h (yH 0) phi_yH_zero
  rw [vec_yH_zero] at h1
  have e : h * yH 0 * h⁻¹ = yH 0 := by
    rw [mem_K₀.1 hh, mul_inv_cancel_right]
  rw [e, vec_yH_zero] at h1
  exact h1.symm

theorem phi_apply_four {h : centralizer ({aNC} : Set NativeSporadic.Co1)} (hh : h ∈ K₀)
    {x : Fin 8 → ZMod 2} (hx : x ∈ W₀) :
    ((typeSystemC.φ h : L₀) : (Fin 8 → ZMod 2) ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) x 4 = 0 := by
  rw [← polar_q₀_e₀ (((typeSystemC.φ h : L₀) : (Fin 8 → ZMod 2) ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) x),
    ← phi_e₀ hh, polar_L₀, polar_q₀_e₀, hx.2]

@[expose] noncomputable def actV (h : centralizer ({aNC} : Set NativeSporadic.Co1))
    (x : Fin 8 → ZMod 2) : Fin 8 → ZMod 2 :=
  clean (((typeSystemC.φ h : L₀) : (Fin 8 → ZMod 2) ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) x)

theorem actV_mem {h : centralizer ({aNC} : Set NativeSporadic.Co1)} (hh : h ∈ K₀)
    {x : Fin 8 → ZMod 2} (hx : x ∈ W₀) : actV h x ∈ W₀ := by
  refine ⟨?_, ?_⟩
  · rw [actV, clean_apply, Pi.sub_apply, Pi.smul_apply, bv_one_apply]
    simp
  · rw [actV, clean_apply, Pi.sub_apply, Pi.smul_apply, bv_one_apply, phi_apply_four hh hx]
    simp

theorem actV_mul {h h' : centralizer ({aNC} : Set NativeSporadic.Co1)} (hh : h ∈ K₀)
    (x : Fin 8 → ZMod 2) : actV (h * h') x = actV h (actV h' x) := by
  rw [actV, actV, actV, map_mul, Subgroup.coe_mul, LinearEquiv.mul_apply]
  conv_lhs => rw [eq_clean_add (((typeSystemC.φ h' : L₀) :
    (Fin 8 → ZMod 2) ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) x)]
  rw [map_add, map_smul, phi_e₀ hh, map_add, map_smul, clean_bv_one, smul_zero, add_zero]

theorem actV_one {x : Fin 8 → ZMod 2} (hx : x ∈ W₀) : actV 1 x = x := by
  rw [actV, map_one]
  exact clean_of_mem hx

theorem actV_add (h : centralizer ({aNC} : Set NativeSporadic.Co1)) (x y : Fin 8 → ZMod 2) :
    actV h (x + y) = actV h x + actV h y := by
  rw [actV, actV, actV, map_add, map_add]

theorem actV_kH_bv {j : ℕ} (hj : j < 2) (v : ℕ) :
    actV (kH j) (bv v) = bv (actW (kCols.getD j []) v) := by
  have h1 := (hasCols_kH hj).apply v
  simp only [LinearEquiv.coe_coe] at h1
  rw [actV, h1, clean_bv]
  rfl

theorem actV_smul (h : centralizer ({aNC} : Set NativeSporadic.Co1)) (c : ZMod 2)
    (x : Fin 8 → ZMod 2) : actV h (c • x) = c • actV h x := by
  rw [actV, actV, map_smul, map_smul]

theorem actV_zero (h : centralizer ({aNC} : Set NativeSporadic.Co1)) : actV h 0 = 0 := by
  rw [actV, map_zero, map_zero]

theorem irrOK_parts : ∀ x ∈ wVecs,
    x = 0 ∨ ∀ t ∈ wVecs, t ∈ xorSpan (irrWords.map fun w => actWord w x) := by
  have h := tw_irr_check
  simp only [irrOK, List.all_eq_true, Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] at h
  exact h

theorem bv_actWord_mem {F : Submodule (ZMod 2) (Fin 8 → ZMod 2)}
    (hF : ∀ j < 2, ∀ x ∈ F, actV (kH j) x ∈ F) (w : List ℕ) (hw : ∀ j ∈ w, j < 2) {v : ℕ}
    (hv : bv v ∈ F) : bv (actWord w v) ∈ F := by
  induction w with
  | nil => exact hv
  | cons j w ih =>
    rw [actWord, List.foldr_cons, ← actWord, ← actV_kH_bv (hw j List.mem_cons_self)]
    exact hF j (hw j List.mem_cons_self) _ (ih fun i hi => hw i (List.mem_cons_of_mem _ hi))

theorem kH_mem_K₀ {j : ℕ} (hj : j < 2) : kH j ∈ K₀ := mem_K₀.2 (kH_comm hj)

theorem actV_eq_of_isPGroup {P : Subgroup (centralizer ({aNC} : Set NativeSporadic.Co1))}
    (hPK : P ≤ K₀) (hnorm : ∀ k ∈ K₀, ∀ p ∈ P, k * p * k⁻¹ ∈ P) (hP : IsPGroup 2 P) :
    ∀ p ∈ P, ∀ x ∈ W₀, actV p x = x := by
  let F : Submodule (ZMod 2) (Fin 8 → ZMod 2) :=
    { carrier := {x | ∀ p ∈ P, actV p x = x}
      add_mem' := fun {x y} hx hy p hp => by rw [actV_add, hx p hp, hy p hp]
      zero_mem' := fun p _ => actV_zero p
      smul_mem' := fun c x hx p hp => by rw [actV_smul, hx p hp] }
  have hFk : ∀ j < 2, ∀ x ∈ F, actV (kH j) x ∈ F := by
    intro j hj x hx p hp
    have hk := kH_mem_K₀ hj
    have hq : (kH j)⁻¹ * p * kH j ∈ P := by
      simpa using hnorm _ (inv_mem hk) p hp
    have e : p * kH j = kH j * ((kH j)⁻¹ * p * kH j) := by group
    have h1 : actV (p * kH j) x = actV (kH j * ((kH j)⁻¹ * p * kH j)) x := by rw [← e]
    rw [actV_mul (hPK hp), actV_mul hk, hx _ hq] at h1
    exact h1
  let _ : MulAction P W₀ :=
    { smul := fun p x => ⟨actV p x, actV_mem (hPK p.2) x.2⟩
      one_smul := fun x => Subtype.ext (actV_one x.2)
      mul_smul := fun p q x => Subtype.ext (actV_mul (hPK p.2) x.1) }
  have hfix : ∃ x : W₀, x ∈ MulAction.fixedPoints P W₀ ∧ x ≠ 0 := by
    by_contra hne
    push Not at hne
    have hFix : MulAction.fixedPoints P W₀ = {0} := by
      ext x
      refine ⟨fun hx => hne x hx, fun hx => ?_⟩
      rw [Set.mem_singleton_iff.1 hx]
      intro p
      exact Subtype.ext (actV_zero p)
    have hmod := IsPGroup.card_modEq_card_fixedPoints hP (W₀ : Type)
    have h1 : Nat.card ({0} : Set W₀) = 1 := by simp
    rw [hFix, h1] at hmod
    have he : (⟨bv 2, bv_mem_W₀ (by decide)⟩ : W₀) ≠ 0 := fun h => by
      have := congrArg Subtype.val h
      exact absurd (bv_inj (by norm_num) (by norm_num) (this.trans bv_zero.symm)) (by norm_num)
    have h2 : addOrderOf (⟨bv 2, bv_mem_W₀ (by decide)⟩ : W₀) = 2 :=
      addOrderOf_eq_prime (Subtype.ext (by rw [two_smul]; exact vec_add_self _)) he
    have hdvd := addOrderOf_dvd_natCard (⟨bv 2, bv_mem_W₀ (by decide)⟩ : W₀)
    rw [h2] at hdvd
    unfold Nat.ModEq at hmod
    omega
  obtain ⟨x₀, hx₀, hx₀0⟩ := hfix
  have hx₀F : (x₀ : Fin 8 → ZMod 2) ∈ F := fun p hp => congrArg Subtype.val (hx₀ ⟨p, hp⟩)
  have hv₀ := enc_mem_wVecs x₀.2
  have hv₀0 : enc (x₀ : Fin 8 → ZMod 2) ≠ 0 := fun h => hx₀0 (Subtype.ext (by
    rw [← bv_enc (x₀ : Fin 8 → ZMod 2), h, bv_zero]
    rfl))
  have hall : ∀ t ∈ wVecs, bv t ∈ F := by
    rcases irrOK_parts _ hv₀ with h0 | hspan
    · exact absurd h0 hv₀0
    · intro t ht
      refine bv_xorSpan_mem (fun v hv => ?_) t (hspan t ht)
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hv
      exact bv_actWord_mem hFk w (irrWords_lt w hw) (by rw [bv_enc]; exact hx₀F)
  intro p hp x hx
  have := hall _ (enc_mem_wVecs hx) p hp
  rwa [bv_enc] at this

end CFSG.Sporadic.Co1Patterson.TwistNative
