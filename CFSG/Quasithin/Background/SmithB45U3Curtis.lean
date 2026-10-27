module

public import CFSG.Quasithin.Background.SmithB45U3Group
public import CFSG.Quasithin.Background.SmithCurtisMain

public section

namespace CFSG.Quasithin.B45U3

open CFSG.QuasithinUnique.Setup.X7a CFSG.Quasithin.SmithCurtis
open scoped MatrixGroups Matrix

abbrev W1 : Type := (CoxeterMatrix.A 1).Group

abbrev cs1 : CoxeterSystem (CoxeterMatrix.A 1) W1 := (CoxeterMatrix.A 1).toCoxeterSystem

theorem W1_eq (w : W1) : w = 1 ∨ w = cs1.simple 0 := by
  refine cs1.simple_induction (p := fun w => w = 1 ∨ w = cs1.simple 0) w
    (fun i => Or.inr (by rw [Subsingleton.elim i 0])) (Or.inl rfl) ?_
  rintro w w' (rfl | rfl) (rfl | rfl)
  · exact Or.inl (one_mul 1)
  · exact Or.inr (one_mul _)
  · exact Or.inr (mul_one _)
  · exact Or.inl (cs1.simple_mul_simple_self 0)

instance : Finite W1 :=
  Finite.of_surjective (fun b : Bool => if b then cs1.simple 0 else 1) fun w => by
    rcases W1_eq w with rfl | rfl
    · exact ⟨false, rfl⟩
    · exact ⟨true, rfl⟩

theorem eq_one_of_length_simple_mul {w : W1} {i : Fin 1}
    (h : cs1.length (cs1.simple i * w) = cs1.length w + 1) : w = 1 := by
  rcases W1_eq w with rfl | rfl
  · rfl
  · rw [Subsingleton.elim i 0, cs1.simple_mul_simple_self, cs1.length_one, cs1.length_simple]
      at h
    omega

variable {K : Type} [Field K] [Finite K] [CharP K 2] {s : ℕ}

theorem wJs_liftable :
    (CoxeterMatrix.A 1).IsLiftable (fun _ : Fin 1 => (wJs : suJ K s)) := by
  intro i i'
  rw [Subsingleton.elim i' i, CoxeterMatrix.diagonal, pow_one, wJs_mul_self]

@[expose] noncomputable def nWJ : W1 →* suJ K s := cs1.lift ⟨_, wJs_liftable⟩

theorem nWJ_simple (i : Fin 1) : (nWJ (cs1.simple i) : suJ K s) = wJs :=
  cs1.lift_apply_simple wJs_liftable i

omit [CharP K 2] in
theorem one_le_s (hK : Nat.card K = (2 ^ s) ^ 2) : 1 ≤ s := by
  rcases Nat.eq_zero_or_pos s with rfl | h
  · have := Finite.one_lt_card (α := K)
    rw [hK] at this
    simp at this
  · exact h

open Classical in
@[expose] noncomputable def phiJ (hK : Nat.card K = (2 ^ s) ^ 2) (x : suJ K s) : suJ K s :=
  if h : ((x : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 0 2 = 0 then 1
  else hJ hK (Units.mk0 _ h)

theorem phiJ_of_ne (hK : Nat.card K = (2 ^ s) ^ 2) {x : suJ K s}
    (h : ((x : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 0 2 ≠ 0) :
    phiJ hK x = hJ hK (Units.mk0 _ h) := by
  simp [phiJ, h]

theorem UJ_corner_ne_zero {x : suJ K s} (hx : x ∈ UJ K s) (hx1 : x ≠ 1) :
    ((x : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 0 2 ≠ 0 := by
  obtain ⟨a, b, hab, hxe⟩ := exists_of_mem_UJ hx
  rw [hxe, up3_coe]
  simp only [upMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one]
  rintro rfl
  apply hx1
  have ha : a * a ^ 2 ^ s = 0 := by rw [← hab]; simp
  have ha0 : a = 0 := by
    rcases mul_eq_zero.mp ha with h | h
    · exact h
    · exact pow_eq_zero_iff (pow_ne_zero _ two_ne_zero) |>.mp h
  subst ha0
  refine Subtype.ext ?_
  rw [hxe, zero_pow (pow_ne_zero _ two_ne_zero), up3_zero]
  rfl

theorem UJ_mul_wJs (hK : Nat.card K = (2 ^ s) ^ 2) {x : suJ K s} (hx : x ∈ UJ K s)
    (hx1 : x ≠ 1) : ∃ l ∈ LJ K s, ∃ u ∈ UJ K s, x * wJs = l * phiJ hK x * u := by
  have hσ : ∀ c : K, (c ^ 2 ^ s) ^ 2 ^ s = c := fun c => by
    have := CFSG.LieType.BorelTits.unitaryInvolution_involutive hK c
    rwa [CFSG.LieType.BorelTits.unitaryInvolution_apply,
      CFSG.LieType.BorelTits.unitaryInvolution_apply] at this
  have h0 := UJ_corner_ne_zero hx hx1
  obtain ⟨a, b, hab, hxe⟩ := exists_of_mem_UJ hx
  have hb : b ≠ 0 := by
    have := h0
    rw [hxe, up3_coe] at this
    simpa [upMat] using this
  have hbq : b ^ 2 ^ s ≠ 0 := pow_ne_zero _ hb
  have hrel : 1 / b + (1 / b) ^ 2 ^ s = a / b * (a / b) ^ 2 ^ s := by
    rw [div_pow, div_pow, one_pow]
    field_simp
    linear_combination hab
  have hrel' : 1 / b + (1 / b) ^ 2 ^ s = a / b ^ 2 ^ s * (a / b ^ 2 ^ s) ^ 2 ^ s := by
    rw [div_pow, div_pow, one_pow, hσ]
    field_simp
    linear_combination hab
  have hl : u3 (a / b) (1 / b) ((a / b) ^ 2 ^ s) ∈ suJ K s := u3_mem_suJ hK hrel
  have hu : up3 (a / b ^ 2 ^ s) (1 / b) ((a / b ^ 2 ^ s) ^ 2 ^ s) ∈ suJ K s :=
    up3_mem_suJ hK hrel'
  refine ⟨⟨_, hl⟩, mem_lowerUni.mpr ⟨_, _, _, rfl⟩, ⟨_, hu⟩, mem_upperUni.mpr ⟨_, _, _, rfl⟩, ?_⟩
  have hentry : ((x : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 0 2 = b := by
    rw [hxe, up3_coe]
    simp [upMat]
  have hphi : phiJ hK x = hJ hK (Units.mk0 b hb) := by
    rw [phiJ_of_ne hK h0]
    congr 1
    exact Units.ext hentry
  rw [hphi]
  refine Subtype.ext ?_
  simp only [Subgroup.coe_mul, coe_wJs, coe_hJ]
  rw [hxe, up3_mul_wJ hb hab, div_pow, div_pow, hσ]

theorem wJs_UJ_wJs (hK : Nat.card K = (2 ^ s) ^ 2) {x : suJ K s} (hx : x ∈ UJ K s)
    (hx1 : x ≠ 1) : ∃ a ∈ UJ K s, ∃ u ∈ UJ K s, wJs * x * wJs = a * wJs * phiJ hK x * u := by
  obtain ⟨l, hl, u, hu, e⟩ := UJ_mul_wJs hK hx hx1
  refine ⟨wJs * l * wJs⁻¹, wJs_conj_LJ hl, u, hu, ?_⟩
  rw [mul_assoc wJs x, e]
  group

theorem LJ_bruhat (hK : Nat.card K = (2 ^ s) ^ 2) {y : suJ K s} (hy : y ∈ LJ K s)
    (hy1 : y ≠ 1) :
    ∃ h ∈ HJ K s hK, ∃ a ∈ UJ K s, ∃ c ∈ UJ K s, y = a * (h * wJs) * c := by
  set x := wJs * y * wJs⁻¹ with hxdef
  have hx : x ∈ UJ K s := wJs_conj_LJ hy
  have hx1 : x ≠ 1 := by
    intro h
    apply hy1
    have e : y = wJs⁻¹ * x * wJs := by rw [hxdef]; group
    rw [e, h, mul_one, inv_mul_cancel]
  obtain ⟨a, ha, u, hu, e⟩ := wJs_UJ_wJs hK hx hx1
  obtain ⟨r, hr⟩ : phiJ hK x ∈ HJ K s hK := by
    rw [phiJ_of_ne hK (UJ_corner_ne_zero hx hx1)]
    exact ⟨_, rfl⟩
  refine ⟨wJs * phiJ hK x * wJs⁻¹, ?_, a, ha, u, hu, ?_⟩
  · rw [← hr, wJs_conj_hJ hK]
    exact ⟨_, rfl⟩
  · have e2 : y = wJs * x * wJs := by
      rw [hxdef, wJs_inv,
        show wJs * (wJs * y * wJs) * wJs = (wJs * wJs) * y * (wJs * wJs) by group,
        wJs_mul_self, one_mul, mul_one]
    calc y = wJs * x * wJs := e2
      _ = a * wJs * phiJ hK x * u := e
      _ = a * (wJs * phiJ hK x * wJs⁻¹ * wJs) * u := by group

theorem heckeDeg_one_eq {G : Type*} [Group G] (U : Subgroup G) : heckeDeg U 1 = 1 := by
  rw [heckeDeg, map_one]
  have : U.map (1 : MulAut G).toMonoidHom = U := by
    ext g
    simp
  rw [this, Subgroup.relIndex_self]

theorem UJ_ne_bot (hK : Nat.card K = (2 ^ s) ^ 2) : UJ K s ≠ ⊥ := by
  intro h
  have h1 := card_UJ hK
  rw [h, Subgroup.card_bot] at h1
  have := one_le_s hK
  have h2 : 1 < (2 ^ s) ^ 3 := Nat.one_lt_pow (by norm_num) (Nat.one_lt_two_pow (by omega))
  omega

@[expose] noncomputable def datumJ (hK : Nat.card K = (2 ^ s) ^ 2) :
    CurtisDatum (suJ K s) cs1 2 where
  U := UJ K s
  L := LJ K s
  H := HJ K s hK
  X _ := UJ K s
  Y _ := LJ K s
  Us _ := ⊥
  Q _ := ⊥
  n _ := wJs
  nW := nWJ
  isPGroup_U := isPGroup_UJ hK
  isPGroup_L := isPGroup_LJ hK
  U_inf_L := UJ_inf_LJ
  H_comm a ha b hb := HJ_comm hK ha hb
  H_normU h hh u hu := HJ_conj_UJ hK hh hu
  H_normU' h hh u hu := by
    have := HJ_conj_UJ hK (inv_mem hh) hu
    rwa [inv_inv] at this
  H_normL h hh l hl := HJ_conj_LJ hK hh hl
  H_normX _ h hh x hx := HJ_conj_UJ hK hh hx
  H_normQ _ h hh q hq := by
    rw [Subgroup.mem_bot] at hq ⊢
    rw [hq, mul_one, mul_inv_cancel]
  X_le _ := le_rfl
  X_ne_bot _ := UJ_ne_bot hK
  U_eq _ u hu := ⟨u, hu, 1, Subgroup.one_mem _, (mul_one u).symm⟩
  Us_le _ := bot_le
  X_normUs _ x hx v hv := by
    rw [Subgroup.mem_bot] at hv ⊢
    rw [hv, mul_one, mul_inv_cancel]
  n_normUs _ v hv := by
    rw [Subgroup.mem_bot] at hv ⊢
    rw [hv, mul_one, mul_inv_cancel]
  n_normUs' _ v hv := by
    rw [Subgroup.mem_bot] at hv ⊢
    rw [hv, mul_one, inv_mul_cancel]
  Y_le _ := le_rfl
  Q_le _ := bot_le
  L_le _ := le_sup_left
  X_normQ _ x hx q hq := by
    rw [Subgroup.mem_bot] at hq ⊢
    rw [hq, mul_one, mul_inv_cancel]
  Y_normQ _ y hy q hq := by
    rw [Subgroup.mem_bot] at hq ⊢
    rw [hq, mul_one, mul_inv_cancel]
  n_normQ _ q hq := by
    rw [Subgroup.mem_bot] at hq ⊢
    rw [hq, mul_one, mul_inv_cancel]
  n_conjX _ x hx := wJs_conj_UJ hx
  n_conjY _ y hy := wJs_conj_LJ hy
  n_sq _ := by
    rw [wJs_mul_self]
    exact Subgroup.one_mem _
  n_normH _ h hh := by
    obtain ⟨r, rfl⟩ := hh
    rw [wJs_conj_hJ hK]
    exact ⟨_, rfl⟩
  phi _ := phiJ hK
  psi _ := phiJ hK
  phi_mem _ x hx hx1 := by
    rw [phiJ_of_ne hK (UJ_corner_ne_zero hx hx1)]
    exact ⟨_, rfl⟩
  psi_mem _ x hx hx1 := by
    rw [phiJ_of_ne hK (UJ_corner_ne_zero hx hx1)]
    exact ⟨_, rfl⟩
  phi_spec _ x hx hx1 := UJ_mul_wJs hK hx hx1
  psi_spec _ x hx hx1 := wJs_UJ_wJs hK hx hx1
  bruhatY _ y hy hy1 := LJ_bruhat hK hy hy1
  nW_one := map_one nWJ
  nW_simple_mul w i _ := by rw [map_mul, nWJ_simple]
  nW_conj w i h x hx := by
    rw [eq_one_of_length_simple_mul h, map_one, inv_one, one_mul, mul_one]
    exact hx
  heckeDeg_mul w i h := by
    rw [eq_one_of_length_simple_mul h, mul_one, map_one, nWJ_simple, heckeDeg_one_eq, mul_one]
  cover g := by
    rcases suJ_cover hK g with ⟨l, hl, h, hh, u, hu, e⟩ | ⟨h, hh, u, hu, e⟩
    · exact ⟨l, hl, 1, h, hh, u, hu, by rw [map_one, mul_one]; exact e⟩
    · exact ⟨1, Subgroup.one_mem _, cs1.simple 0, h, hh, u, hu, by
        rw [nWJ_simple, one_mul]; exact e⟩

theorem datumJ_X (hK : Nat.card K = (2 ^ s) ^ 2) (i : Fin 1) : (datumJ hK).X i = UJ K s := rfl

theorem datumJ_psi (hK : Nat.card K = (2 ^ s) ^ 2) (i : Fin 1) :
    (datumJ hK).psi i = phiJ hK := rfl

theorem splitOver_HJ (hK : Nat.card K = (2 ^ s) ^ 2) (k : Type*) [Field k] [Algebra K k] :
    SplitOver k (HJ K s hK) := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  have hq : 0 < Nat.card K - 1 := by
    have := Finite.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial K)
    omega
  have hprim : IsPrimitiveRoot (algebraMap K k (g : K)) (Nat.card K - 1) := by
    have h1 : IsPrimitiveRoot (g : K) (Nat.card K - 1) := by
      rw [← Nat.card_units K, ← hg, ← orderOf_units]
      exact IsPrimitiveRoot.orderOf _
    exact h1.map_of_injective (algebraMap K k).injective
  intro h hh
  refine ⟨Nat.card K - 1, ?_, (Polynomial.nthRootsFinset (Nat.card K - 1) (1 : k)).toList, ?_⟩
  · obtain ⟨r, rfl⟩ := hh
    rw [← map_pow, ← Nat.card_units K, pow_card_eq_one', map_one]
  · rw [Finset.prod_map_toList]
    exact Polynomial.X_pow_sub_one_eq_prod hq hprim

omit [CharP K 2] in
theorem odd_card_norm_fiber (hK : Nat.card K = (2 ^ s) ^ 2) {t : K} (ht : t ^ 2 ^ s = t) :
    Odd (Nat.card {a : K // a * a ^ 2 ^ s = t}) := by
  have hs := one_le_s hK
  have hq0 : 2 ^ s ≠ 0 := pow_ne_zero _ two_ne_zero
  by_cases ht0 : t = 0
  · subst ht0
    have h1 : Nat.card {a : K // a * a ^ 2 ^ s = 0} = 1 := by
      rw [Nat.card_eq_one_iff_exists]
      refine ⟨⟨0, by simp⟩, fun a => Subtype.ext ?_⟩
      rcases mul_eq_zero.mp a.2 with h | h
      · exact h
      · exact pow_eq_zero_iff hq0 |>.mp h
    rw [h1]
    exact odd_one
  · set q := 2 ^ s with hqdef
    have hq1 : 2 ≤ q := by
      have := Nat.pow_le_pow_right (by norm_num : 0 < 2) hs
      simpa [hqdef] using this
    let P : Kˣ →* Kˣ := powMonoidHom (q + 1)
    have hcardU : Nat.card Kˣ = (q - 1) * (q + 1) := by
      rw [Nat.card_units, hK]
      zify [Nat.one_le_pow 2 q (by omega), (by omega : 1 ≤ q)]
      ring
    have hker : Nat.card P.ker = q + 1 := by
      rw [IsCyclic.card_powMonoidHom_ker, hcardU, Nat.gcd_mul_left_left]
    have hrange : Nat.card P.range = q - 1 := by
      rw [IsCyclic.card_powMonoidHom_range, hcardU, Nat.gcd_mul_left_left,
        Nat.mul_div_cancel _ (by omega)]
    have hker2 : Nat.card (powMonoidHom (q - 1) : Kˣ →* Kˣ).ker = q - 1 := by
      rw [IsCyclic.card_powMonoidHom_ker, hcardU, Nat.gcd_mul_right_left]
    have hle : P.range ≤ (powMonoidHom (q - 1) : Kˣ →* Kˣ).ker := by
      rintro _ ⟨a, rfl⟩
      rw [MonoidHom.mem_ker, powMonoidHom_apply]
      show (a ^ (q + 1)) ^ (q - 1) = 1
      rw [← pow_mul, mul_comm, ← hcardU]
      exact pow_card_eq_one'
    have heq : P.range = (powMonoidHom (q - 1) : Kˣ →* Kˣ).ker :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hrange, hker2])
    set T : Kˣ := Units.mk0 t ht0 with hT
    have hTmem : T ∈ P.range := by
      rw [heq, MonoidHom.mem_ker, powMonoidHom_apply]
      refine Units.ext ?_
      rw [Units.val_pow_eq_pow_val, hT, Units.val_mk0, Units.val_one]
      have : t ^ (q - 1) * t = t := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega)]
        exact ht
      exact mul_right_cancel₀ ht0 (this.trans (one_mul t).symm)
    obtain ⟨a₀, ha₀⟩ := hTmem
    have e1 : {a : K // a * a ^ q = t} ≃ {u : Kˣ // u ^ (q + 1) = T} :=
      { toFun := fun a => ⟨Units.mk0 a.1 (fun h0 => ht0 (by rw [← a.2, h0, zero_mul])),
          Units.ext (by
            rw [Units.val_pow_eq_pow_val, Units.val_mk0, hT, Units.val_mk0, pow_succ', a.2])⟩
        invFun := fun u => ⟨u.1, by
          have h' : ((u.1 ^ (q + 1) : Kˣ) : K) = t := by rw [u.2, hT, Units.val_mk0]
          rwa [Units.val_pow_eq_pow_val, pow_succ'] at h'⟩
        left_inv := fun a => rfl
        right_inv := fun u => Subtype.ext (Units.ext rfl) }
    have e2 : {u : Kˣ // u ^ (q + 1) = T} ≃ P.ker :=
      { toFun := fun u => ⟨u.1 * a₀⁻¹, by
          rw [MonoidHom.mem_ker, powMonoidHom_apply, mul_pow, u.2, inv_pow]
          have : a₀ ^ (q + 1) = T := ha₀
          rw [this, mul_inv_cancel]⟩
        invFun := fun v => ⟨v.1 * a₀, by
          have hv : v.1 ^ (q + 1) = 1 := v.2
          have : a₀ ^ (q + 1) = T := ha₀
          rw [mul_pow, hv, one_mul, this]⟩
        left_inv := fun u => Subtype.ext (by simp)
        right_inv := fun v => Subtype.ext (by simp) }
    rw [Nat.card_congr (e1.trans e2), hker]
    have : Even q := by
      rw [hqdef]
      exact (Nat.even_pow' (by omega)).mpr even_two
    exact this.add_one

omit [Finite K] [CharP K 2] in
theorem sum_units_eq_sum [Fintype K] [Fintype Kˣ] {M : Type*} [AddCommMonoid M] (f : K → M)
    (hf : f 0 = 0) : ∑ u : Kˣ, f u = ∑ b : K, f b := by
  classical
  rw [← Finset.sum_erase Finset.univ hf]
  refine Finset.sum_bij' (fun u _ => (u : K))
    (fun b hb => Units.mk0 b (Finset.ne_of_mem_erase hb)) (fun u _ => ?_) (fun b _ => ?_)
    (fun u _ => ?_) (fun b _ => ?_) (fun u _ => rfl)
  · exact Finset.mem_erase.mpr ⟨u.ne_zero, Finset.mem_univ _⟩
  · exact Finset.mem_univ _
  · exact Units.ext rfl
  · rfl

theorem sum_UJ_corner (hK : Nat.card K = (2 ^ s) ^ 2) {k : Type*} [Field k] [CharP k 2]
    [Fintype K] {_ : Fintype (UJ K s)} (c : K → k) :
    ∑ x : UJ K s, c ((((x : suJ K s) : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 0 2) =
      ∑ b : K, c b := by
  classical
  let P := {p : K × K // p.2 + p.2 ^ 2 ^ s = p.1 * p.1 ^ 2 ^ s}
  let φ : P → UJ K s := fun p =>
    ⟨⟨up3 p.1.1 p.1.2 (p.1.1 ^ 2 ^ s), up3_mem_suJ hK p.2⟩, mem_upperUni.mpr ⟨_, _, _, rfl⟩⟩
  have hφ : Function.Bijective φ := by
    refine ⟨fun p p' h => ?_, fun u => ?_⟩
    · have h1 := up3_inj (congrArg (fun u : UJ K s => ((u : suJ K s) : SL(3, K))) h)
      exact Subtype.ext (Prod.ext h1.1 h1.2.1)
    · obtain ⟨x, y, hxy, hu⟩ := exists_of_mem_UJ u.2
      exact ⟨⟨(x, y), hxy⟩, Subtype.ext (Subtype.ext hu.symm)⟩
  have hcorner : ∀ p : P,
      ((((φ p : UJ K s) : suJ K s) : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 0 2 = p.1.2 := by
    intro p
    show (upMat p.1.1 p.1.2 (p.1.1 ^ 2 ^ s)) 0 2 = p.1.2
    simp [upMat]
  rw [← Fintype.sum_bijective φ hφ (fun p => c p.1.2) _ (fun p => by rw [hcorner])]
  let e : P ≃ Σ b : K, {a : K // a * a ^ 2 ^ s = b + b ^ 2 ^ s} :=
    { toFun := fun p => ⟨p.1.2, p.1.1, p.2.symm⟩
      invFun := fun z => ⟨(z.2.1, z.1), z.2.2.symm⟩
      left_inv := fun p => rfl
      right_inv := fun z => rfl }
  rw [← Fintype.sum_equiv e.symm (fun z => c z.1) _ (fun z => rfl), Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun b _ => ?_
  show ∑ _y : {a : K // a * a ^ 2 ^ s = b + b ^ 2 ^ s}, c b = c b
  rw [Finset.sum_const, Finset.card_univ]
  have hodd : Odd (Fintype.card {a : K // a * a ^ 2 ^ s = b + b ^ 2 ^ s}) := by
    rw [← Nat.card_eq_fintype_card]
    refine odd_card_norm_fiber hK ?_
    have hσ := CFSG.LieType.BorelTits.unitaryInvolution_involutive hK b
    rw [CFSG.LieType.BorelTits.unitaryInvolution_apply,
      CFSG.LieType.BorelTits.unitaryInvolution_apply] at hσ
    rw [add_pow_char_pow, hσ, add_comm]
  obtain ⟨m, hm⟩ := hodd
  rw [hm, add_nsmul, one_nsmul, mul_comm, mul_nsmul, two_nsmul, CharTwo.add_self_eq_zero]
  simp

theorem sum_erase_UJ_corner (hK : Nat.card K = (2 ^ s) ^ 2) {k : Type*} [Field k] [CharP k 2]
    [Fintype K] (X : Subgroup (suJ K s)) (hX : X = UJ K s) {_ : Fintype X} {_ : DecidableEq X}
    (f : X → k) (c : K → k) (hc0 : c 0 = 0)
    (hf : ∀ x : X, x ≠ 1 → f x = c ((((x : suJ K s) : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 0 2)) :
    ∑ x ∈ (Finset.univ : Finset X).erase 1, f x = ∑ b : K, c b := by
  subst hX
  rw [Finset.sum_congr rfl fun x hx => hf x (Finset.ne_of_mem_erase hx)]
  have h1 : c (((((1 : UJ K s) : suJ K s) : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 0 2) = 0 := by
    simpa using hc0
  rw [Finset.sum_subset (Finset.subset_univ _) fun x _ hx => by
    rw [show x = 1 by simpa using hx]
    exact h1]
  exact sum_UJ_corner hK c

theorem d'Scalar_datumJ (hK : Nat.card K = (2 ^ s) ^ 2) [Fintype K] [Fintype Kˣ] {k : Type*}
    [Field k] [CharP k 2] (χ : suJ K s → k) (i : Fin 1) :
    (datumJ hK).d'Scalar χ i = ∑ r : Kˣ, χ (hJ hK r) := by
  classical
  unfold CurtisDatum.d'Scalar
  dsimp only
  set c : K → k := fun b => if hb : b = 0 then 0 else χ (hJ hK (Units.mk0 b hb)) with hc
  have hterm : ∀ x : (datumJ hK).X i, x ≠ 1 →
      χ ((datumJ hK).psi i (x : suJ K s)) =
        c ((((x : suJ K s) : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 0 2) := by
    intro x hx
    have hxU : (x : suJ K s) ∈ UJ K s := x.2
    have hx1 : (x : suJ K s) ≠ 1 := fun h => hx (Subtype.ext h)
    have h0 := UJ_corner_ne_zero hxU hx1
    rw [datumJ_psi, phiJ_of_ne hK h0, hc]
    simp only [h0, ↓reduceDIte]
  rw [sum_erase_UJ_corner hK _ (datumJ_X hK i) (fun x => χ ((datumJ hK).psi i x)) c
    (by simp [hc]) hterm, ← sum_units_eq_sum c (by simp [hc])]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [hc, r.ne_zero, ↓reduceDIte]
  congr 2
  exact Units.ext rfl

theorem d'Scalar_eq_zero (hK : Nat.card K = (2 ^ s) ^ 2) {k : Type*} [Field k] [CharP k 2]
    (χ : suJ K s → k) (hmul : ∀ r r' : Kˣ, χ (hJ hK (r * r')) = χ (hJ hK r) * χ (hJ hK r'))
    (hone : χ 1 = 1) (hne : ∃ r : Kˣ, χ (hJ hK r) ≠ 1) (i : Fin 1) :
    (datumJ hK).d'Scalar χ i = 0 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  rw [d'Scalar_datumJ hK]
  let f : Kˣ →* k :=
    { toFun := fun r => χ (hJ hK r)
      map_one' := by rw [map_one]; exact hone
      map_mul' := hmul }
  have hf : f ≠ 1 := by
    obtain ⟨r, hr⟩ := hne
    intro h
    exact hr (by simpa [f] using congrArg (fun φ : Kˣ →* k => φ r) h)
  exact sum_hom_units_eq_zero f hf

end CFSG.Quasithin.B45U3
