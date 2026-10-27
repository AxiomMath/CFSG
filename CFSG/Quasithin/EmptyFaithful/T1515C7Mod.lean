module

public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod

public section

namespace CFSG.Quasithin

open scoped Pointwise

section SevenMod

variable {V : Type*} [CommGroup V]

theorem comm_apply_of {y z : MulAut V} (hyz : y * z = z * y) (u : V) : z (y u) = y (z u) :=
  (congrArg (fun φ : MulAut V => φ u) hyz).symm

theorem pow_apply_three {g : MulAut V} (hg : g ^ 3 = 1) (u : V) : g (g (g u)) = u :=
  apply_cube_c4 hg u

theorem decomp_identity (hsq : ∀ v : V, v * v = 1) {y z : MulAut V} (hz3 : z ^ 3 = 1)
    (hyz : y * z = z * y) (w : V) :
    w = normOf y (normOf z w) * normOf z w * normOf y w * normOf (y * z) w *
      normOf (y * z ^ 2) w := by
  have hc := comm_apply_of hyz
  have hz := pow_apply_three hz3
  have hz2 : z ^ 2 = z * z := pow_two z
  have key : ∀ a00 a01 a02 a10 a11 a12 a20 a21 a22 : V, a00 = a00 * a10 * a20 * (a01 * a11 * a21) *
      (a02 * a12 * a22) * (a00 * a01 * a02) * (a00 * a10 * a20) * (a00 * a11 * a22) *
      (a00 * a12 * a21) := by
    intro a00 a01 a02 a10 a11 a12 a20 a21 a22
    calc a00 = a00 * ((a10 * a10) * (a20 * a20) * (a01 * a01) * (a11 * a11) * (a21 * a21) *
          (a02 * a02) * (a12 * a12) * (a22 * a22) * (a00 * a00) * (a00 * a00)) := by
          rw [hsq a10, hsq a20, hsq a01, hsq a11, hsq a21, hsq a02, hsq a12, hsq a22, hsq a00]
          simp
      _ = _ := by ac_rfl
  simp only [normOf_apply, hz2, map_mul, MulAut.mul_apply, hc, hz]
  refine (key w (z w) (z (z w)) (y w) (y (z w)) (y (z (z w))) (y (y w)) (y (y (z w)))
    (y (y (z (z w))))).trans ?_
  ac_rfl

theorem normOf_mem_of_inv {W : Subgroup V} {g : MulAut V} (hW : ∀ w ∈ W, g w ∈ W) {w : V}
    (hw : w ∈ W) : normOf g w ∈ W := by
  rw [normOf_apply]
  exact W.mul_mem (W.mul_mem hw (hW w hw)) (hW _ (hW w hw))

theorem cube_yz {y z : MulAut V} (hy3 : y ^ 3 = 1) (hz3 : z ^ 3 = 1) (hyz : y * z = z * y) (j : ℕ) :
    (y * z ^ j) ^ 3 = 1 := by
  have hc : Commute y (z ^ j) := (show Commute y z from hyz).pow_right j
  rw [hc.mul_pow, hy3, one_mul, ← pow_mul, mul_comm, pow_mul, hz3, one_pow]

theorem normOf_cross {y z : MulAut V} (hz3 : z ^ 3 = 1)
    (hyz : y * z = z * y) {c : V} {j k : ℕ} (hj : j < 3) (hk : k < 3) (hjk : j ≠ k)
    (hc : (y * z ^ k) c = c) : normOf (y * z ^ j) c = normOf z c := by
  have hcm := comm_apply_of hyz
  have hz := pow_apply_three hz3
  have hy' : ∀ u : V, y (z u) = z (y u) := fun u => (hcm u).symm
  have hcz : ∀ u : V, z (z (z u)) = u := hz
  have hyk : (k = 0 → y c = c) ∧ (k = 1 → y c = z (z c)) ∧ (k = 2 → y c = z c) := by
    refine ⟨fun h0 => ?_, fun h1 => ?_, fun h2 => ?_⟩
    · subst h0
      simpa using hc
    · subst h1
      simp only [pow_one, MulAut.mul_apply] at hc
      have : z (z (y (z c))) = z (z c) := by rw [hc]
      rw [hy', hz] at this
      exact this
    · subst h2
      simp only [pow_two, MulAut.mul_apply] at hc
      have : z (y (z (z c))) = z c := by rw [hc]
      rw [hy', hy', hz] at this
      exact this
  have hyk' := hyk
  interval_cases k <;> interval_cases j <;> first | exact absurd rfl hjk | skip
  all_goals
    obtain ⟨h0, h1, h2⟩ := hyk'
    simp only [normOf_apply, pow_zero, pow_one, pow_two, mul_one, MulAut.mul_apply, hy', hz,
      h0, h1, h2] <;> first | rfl | ac_rfl

@[expose] def Cj (W : Subgroup V) (y z : MulAut V) (j : ℕ) : Subgroup V := W ⊓ fixOf (y * z ^ j)

theorem pow_apply_mem {W : Subgroup V} {z : MulAut V} (hWz : ∀ w ∈ W, z w ∈ W) (j : ℕ) {w : V}
    (hw : w ∈ W) : (z ^ j) w ∈ W := by
  induction j with
  | zero => simpa using hw
  | succ n ih =>
    rw [pow_succ']
    exact hWz _ ih

theorem yz_apply_mem {W : Subgroup V} {y z : MulAut V} (hWy : ∀ w ∈ W, y w ∈ W)
    (hWz : ∀ w ∈ W, z w ∈ W) (j : ℕ) {w : V} (hw : w ∈ W) : (y * z ^ j) w ∈ W :=
  hWy _ (pow_apply_mem hWz j hw)

theorem normOf_mem_Cj {W : Subgroup V} {y z : MulAut V} (hy3 : y ^ 3 = 1) (hz3 : z ^ 3 = 1)
    (hyz : y * z = z * y) (hWy : ∀ w ∈ W, y w ∈ W) (hWz : ∀ w ∈ W, z w ∈ W) (j : ℕ) {w : V}
    (hw : w ∈ W) : normOf (y * z ^ j) w ∈ Cj W y z j :=
  ⟨normOf_mem_of_inv (fun _ hu => yz_apply_mem hWy hWz j hu) hw,
    normOf_mem_fixOf (cube_yz hy3 hz3 hyz j) w⟩

theorem normOf_z_eq_one {W : Subgroup V} {z : MulAut V} (hz3 : z ^ 3 = 1)
    (hWz : ∀ w ∈ W, z w ∈ W) (hfpf : ∀ w ∈ W, z w = w → w = 1) {w : V} (hw : w ∈ W) :
    normOf z w = 1 :=
  hfpf _ (normOf_mem_of_inv hWz hw) (normOf_mem_fixOf hz3 w)

theorem exists_decomp_E (hsq : ∀ v : V, v * v = 1) {y z : MulAut V} (hz3 : z ^ 3 = 1)
    (hyz : y * z = z * y) {W : Subgroup V} (hWz : ∀ w ∈ W, z w ∈ W)
    (hfpf : ∀ w ∈ W, z w = w → w = 1) {w : V} (hw : w ∈ W) :
    w = normOf (y * z ^ 0) w * normOf (y * z ^ 1) w * normOf (y * z ^ 2) w := by
  have h := decomp_identity hsq hz3 hyz w
  have hNz := normOf_z_eq_one hz3 hWz hfpf hw
  rw [hNz, map_one, one_mul, one_mul] at h
  simpa using h

theorem normOf_self {g : MulAut V} (hsq : ∀ v : V, v * v = 1) {c : V} (hc : g c = c) :
    normOf g c = c := by
  rw [normOf_apply, hc, hc]
  calc c * c * c = (c * c) * c := rfl
    _ = c := by rw [hsq, one_mul]

theorem card_eq_prod_Cj (hsq : ∀ v : V, v * v = 1) {y z : MulAut V} (hy3 : y ^ 3 = 1)
    (hz3 : z ^ 3 = 1) (hyz : y * z = z * y) {W : Subgroup V} (hWy : ∀ w ∈ W, y w ∈ W)
    (hWz : ∀ w ∈ W, z w ∈ W) (hfpf : ∀ w ∈ W, z w = w → w = 1) :
    Nat.card W = Nat.card (Cj W y z 0) * (Nat.card (Cj W y z 1) * Nat.card (Cj W y z 2)) := by
  let ψ : ↥(Cj W y z 1) × ↥(Cj W y z 2) →* V := (Cj W y z 1).subtype.coprod (Cj W y z 2).subtype
  let φ : ↥(Cj W y z 0) × (↥(Cj W y z 1) × ↥(Cj W y z 2)) →* V :=
    (Cj W y z 0).subtype.coprod ψ
  have hφ : ∀ a b c, φ (a, (b, c)) = (a : V) * ((b : V) * (c : V)) := fun a b c => rfl
  have hcross : ∀ {j k : ℕ}, j < 3 → k < 3 → j ≠ k → ∀ {c : V}, c ∈ Cj W y z k →
      normOf (y * z ^ j) c = 1 := by
    intro j k hj hk hjk c hc
    rw [normOf_cross hz3 hyz hj hk hjk hc.2]
    exact normOf_z_eq_one hz3 hWz hfpf hc.1
  have hself : ∀ {j : ℕ}, ∀ {c : V}, c ∈ Cj W y z j → normOf (y * z ^ j) c = c := fun hc =>
    normOf_self hsq hc.2
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    rintro ⟨a, b, c⟩ h
    rw [MonoidHom.mem_ker, hφ] at h
    have e0 := congrArg (normOf (y * z ^ 0)) h
    have e1 := congrArg (normOf (y * z ^ 1)) h
    have e2 := congrArg (normOf (y * z ^ 2)) h
    simp only [map_mul, map_one] at e0 e1 e2
    rw [hself a.2, hcross (by norm_num) (by norm_num) (by norm_num) b.2,
      hcross (by norm_num) (by norm_num) (by norm_num) c.2, mul_one, mul_one] at e0
    rw [hcross (by norm_num) (by norm_num) (by norm_num) a.2, hself b.2,
      hcross (by norm_num) (by norm_num) (by norm_num) c.2, one_mul, mul_one] at e1
    rw [hcross (by norm_num) (by norm_num) (by norm_num) a.2,
      hcross (by norm_num) (by norm_num) (by norm_num) b.2, hself c.2, one_mul, one_mul] at e2
    exact Prod.ext (Subtype.ext e0) (Prod.ext (Subtype.ext e1) (Subtype.ext e2))
  have hrange : φ.range = W := by
    apply le_antisymm
    · rintro _ ⟨⟨a, b, c⟩, rfl⟩
      rw [hφ]
      exact W.mul_mem a.2.1 (W.mul_mem b.2.1 c.2.1)
    · intro w hw
      have h := exists_decomp_E hsq hz3 hyz hWz hfpf hw
      refine ⟨(⟨normOf (y * z ^ 0) w, normOf_mem_Cj hy3 hz3 hyz hWy hWz 0 hw⟩,
        (⟨normOf (y * z ^ 1) w, normOf_mem_Cj hy3 hz3 hyz hWy hWz 1 hw⟩,
        ⟨normOf (y * z ^ 2) w, normOf_mem_Cj hy3 hz3 hyz hWy hWz 2 hw⟩)), ?_⟩
      rw [hφ]
      show normOf (y * z ^ 0) w * (normOf (y * z ^ 1) w * normOf (y * z ^ 2) w) = w
      rw [← mul_assoc]
      exact h.symm
  have h1 : Nat.card (↥(Cj W y z 0) × (↥(Cj W y z 1) × ↥(Cj W y z 2))) = Nat.card φ.range :=
    Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  have h2 : Nat.card φ.range = Nat.card W := Nat.card_congr (MulEquiv.subgroupCongr hrange).toEquiv
  rw [← h2, ← h1, Nat.card_prod, Nat.card_prod]

theorem card_conj_fix {W : Subgroup V} {x g : MulAut V} (hWx : ∀ w ∈ W, x w ∈ W)
    (hWx' : ∀ w ∈ W, x⁻¹ w ∈ W) :
    Nat.card (W ⊓ fixOf (x * g * x⁻¹) : Subgroup V) = Nat.card (W ⊓ fixOf g : Subgroup V) := by
  refine Nat.card_congr
    { toFun := fun w => ⟨x⁻¹ w, hWx' w w.2.1, ?_⟩
      invFun := fun u => ⟨x u, hWx u u.2.1, ?_⟩
      left_inv := fun w => ?_
      right_inv := fun u => ?_ }
  · have h : (x * g * x⁻¹) (w : V) = w := w.2.2
    show g (x⁻¹ (w : V)) = x⁻¹ (w : V)
    have h2 : x (g (x⁻¹ (w : V))) = w := h
    calc g (x⁻¹ (w : V)) = x⁻¹ (x (g (x⁻¹ (w : V)))) := by simp
      _ = x⁻¹ (w : V) := by rw [h2]
  · have h : g (u : V) = u := u.2.2
    show (x * g * x⁻¹) (x (u : V)) = x (u : V)
    show x (g (x⁻¹ (x (u : V)))) = x (u : V)
    simp [h]
  · apply Subtype.ext
    show x (x⁻¹ (w : V)) = w
    simp
  · apply Subtype.ext
    show x⁻¹ (x (u : V)) = u
    simp

theorem inv_apply_mem_of_pow {W : Subgroup V} {x : MulAut V} (hx3 : x ^ 3 = 1)
    (hWx : ∀ w ∈ W, x w ∈ W) {w : V} (hw : w ∈ W) : x⁻¹ w ∈ W := by
  have h : x⁻¹ = x * x := by
    refine inv_eq_of_mul_eq_one_right ?_
    have : x ^ 3 = x * (x * x) := by rw [pow_succ, pow_succ, pow_one, mul_assoc]
    rwa [this] at hx3
  rw [h]
  exact hWx _ (hWx w hw)

theorem card_Cj_eq {y z x : MulAut V} (hz3 : z ^ 3 = 1) (hx3 : x ^ 3 = 1) (hxz : x * z = z * x)
    {e : ℕ} (he : e % 3 ≠ 0) (hxy : x * y * x⁻¹ = y * z ^ e) {W : Subgroup V}
    (hWx : ∀ w ∈ W, x w ∈ W) :
    Nat.card (Cj W y z 1) = Nat.card (Cj W y z 0) ∧ Nat.card (Cj W y z 2) = Nat.card (Cj W y z 0) := by
  have hWx' := fun w (hw : w ∈ W) => inv_apply_mem_of_pow hx3 hWx hw
  have h1 : Nat.card (W ⊓ fixOf (y * z ^ e) : Subgroup V) = Nat.card (W ⊓ fixOf y : Subgroup V) := by
    rw [← hxy]
    exact card_conj_fix hWx hWx'
  have hxze : x * z ^ e * x⁻¹ = z ^ e := by
    have : x * z ^ e = z ^ e * x := (Commute.pow_right (show Commute x z from hxz) e).eq
    rw [this]
    group
  have h2 : Nat.card (W ⊓ fixOf (y * (z ^ e * z ^ e)) : Subgroup V) =
      Nat.card (W ⊓ fixOf (y * z ^ e) : Subgroup V) := by
    have : x * (y * z ^ e) * x⁻¹ = y * (z ^ e * z ^ e) := by
      calc x * (y * z ^ e) * x⁻¹ = (x * y * x⁻¹) * (x * z ^ e * x⁻¹) := by group
        _ = y * (z ^ e * z ^ e) := by rw [hxy, hxze, mul_assoc]
    rw [← this]
    exact card_conj_fix hWx hWx'
  have hmod : z ^ e = z ^ (e % 3) := pow_eq_pow_mod e hz3
  have h0 : Cj W y z 0 = W ⊓ fixOf y := by simp [Cj]
  have hmod' : z ^ e * z ^ e = z ^ (2 * (e % 3) % 3) := by
    rw [← pow_add, pow_eq_pow_mod (e + e) hz3]
    congr 1
    omega
  have : e % 3 = 1 ∨ e % 3 = 2 := by omega
  rw [hmod'] at h2
  rw [hmod] at h1 h2
  rcases this with h | h
  · rw [h] at h1 h2
    simp only [pow_one, Nat.reduceMul, Nat.reduceMod] at h1 h2
    refine ⟨?_, ?_⟩
    · rw [h0]; exact h1
    · rw [h0]; rw [← h1]; exact h2
  · rw [h] at h1 h2
    simp only [Nat.reduceMul, Nat.reduceMod, pow_one] at h1 h2
    refine ⟨?_, ?_⟩
    · rw [h0, ← h1]; exact h2
    · rw [h0]; exact h1

theorem card_eq_cube (hsq : ∀ v : V, v * v = 1) {y z x : MulAut V} (hy3 : y ^ 3 = 1)
    (hz3 : z ^ 3 = 1) (hx3 : x ^ 3 = 1) (hyz : y * z = z * y) (hxz : x * z = z * x) {e : ℕ}
    (he : e % 3 ≠ 0) (hxy : x * y * x⁻¹ = y * z ^ e) {W : Subgroup V} (hWy : ∀ w ∈ W, y w ∈ W)
    (hWz : ∀ w ∈ W, z w ∈ W) (hWx : ∀ w ∈ W, x w ∈ W) (hfpf : ∀ w ∈ W, z w = w → w = 1) :
    Nat.card W = Nat.card (W ⊓ fixOf y : Subgroup V) ^ 3 := by
  obtain ⟨h1, h2⟩ := card_Cj_eq hz3 hx3 hxz he hxy hWx
  rw [card_eq_prod_Cj hsq hy3 hz3 hyz hWy hWz hfpf, h1, h2]
  have h0 : Cj W y z 0 = W ⊓ fixOf y := by simp [Cj]
  rw [h0]
  ring

theorem no_cube_four (m : ℕ) : m ^ 3 ≠ 4 := by
  intro h
  have : m ≤ 2 := by
    by_contra hlt
    have h3 : 3 ≤ m := by omega
    have := Nat.pow_le_pow_left h3 3
    norm_num at this
    omega
  interval_cases m <;> simp at h

theorem no_cube_sixteen (m : ℕ) : m ^ 3 ≠ 16 := by
  intro h
  have : m ≤ 2 := by
    by_contra hlt
    have h3 : 3 ≤ m := by omega
    have := Nat.pow_le_pow_left h3 3
    norm_num at this
    omega
  interval_cases m <;> simp at h

section Fpf

variable [Finite V]

theorem fpf_z (hsq : ∀ v : V, v * v = 1) {y z x : MulAut V} (hy3 : y ^ 3 = 1) (hz3 : z ^ 3 = 1)
    (hx3 : x ^ 3 = 1) (hyz : y * z = z * y) (hxz : x * z = z * x) {e : ℕ} (he : e % 3 ≠ 0)
    (hxy : x * y * x⁻¹ = y * z ^ e) (hV : Nat.card V = 64) (hz1 : z ≠ 1) :
    ∀ w : V, z w = w → w = 1 := by
  have hinv : ∀ a : MulAut V, a * z = z * a → ∀ w ∈ (normOf z).ker, a w ∈ (normOf z).ker :=
    fun a ha w hw => apply_mem_ker_normOf ha hw
  have hWy := hinv y hyz
  have hWz := hinv z rfl
  have hWx := hinv x hxz
  have hfpf : ∀ w ∈ (normOf z).ker, z w = w → w = 1 := by
    intro w hw hzw
    have : w ∈ fixOf z ⊓ (normOf z).ker := ⟨hzw, hw⟩
    rw [fixOf_inf_ker hsq, Subgroup.mem_bot] at this
    exact this
  have hcube := card_eq_cube hsq hy3 hz3 hx3 hyz hxz he hxy hWy hWz hWx hfpf
  have hprod := card_eq_fixOf_mul_ker hz3 hsq
  rw [hV, hcube] at hprod
  have hc3 := card_modEq_fixOf hz3
  rw [hV] at hc3
  have hcd := card_fixOf_dvd z
  rw [hV] at hcd
  have hc64 : Nat.card (fixOf z) ≠ 64 := by
    intro h64
    apply fixOf_ne_top hz1
    apply Subgroup.eq_top_of_card_eq
    rw [h64, hV]
  have hcle : Nat.card (fixOf z) ≤ 64 := Nat.le_of_dvd (by norm_num) hcd
  have hcpos : 0 < Nat.card (fixOf z) := Nat.card_pos
  unfold Nat.ModEq at hc3
  have hc1 : Nat.card (fixOf z) = 1 := by
    generalize Nat.card (fixOf z) = c at *
    set m := Nat.card (↥((normOf z).ker ⊓ fixOf y : Subgroup V)) with hm
    interval_cases c <;> first | omega | skip
    all_goals first
      | (exfalso; exact no_cube_four m (by omega))
      | (exfalso; exact no_cube_sixteen m (by omega))
  intro w hw
  have : fixOf z = ⊥ := Subgroup.card_eq_one.mp hc1
  have hw' : w ∈ fixOf z := hw
  rw [this] at hw'
  exact hw'

theorem card_fix_y (hsq : ∀ v : V, v * v = 1) {y z x : MulAut V} (hy3 : y ^ 3 = 1)
    (hz3 : z ^ 3 = 1) (hx3 : x ^ 3 = 1) (hyz : y * z = z * y) (hxz : x * z = z * x) {e : ℕ}
    (he : e % 3 ≠ 0) (hxy : x * y * x⁻¹ = y * z ^ e) (hV : Nat.card V = 64) (hz1 : z ≠ 1) :
    Nat.card (fixOf y) = 4 ∧ Nat.card (fixOf (y * z)) = 4 ∧ Nat.card (fixOf (y * z ^ 2)) = 4 := by
  have hfpf := fpf_z hsq hy3 hz3 hx3 hyz hxz he hxy hV hz1
  have hcube := card_eq_cube hsq hy3 hz3 hx3 hyz hxz he hxy (W := ⊤) (fun _ _ => trivial)
    (fun _ _ => trivial) (fun _ _ => trivial) (fun w _ h => hfpf w h)
  rw [Subgroup.card_top, hV, top_inf_eq] at hcube
  have h4 : Nat.card (fixOf y) = 4 := by
    have : Nat.card (fixOf y) ^ 3 = 4 ^ 3 := by rw [← hcube]; norm_num
    exact Nat.pow_left_injective (by norm_num : 3 ≠ 0) this
  obtain ⟨h1, h2⟩ := card_Cj_eq hz3 hx3 hxz he hxy (W := ⊤) (fun _ _ => trivial)
  have h0 : Cj ⊤ y z 0 = fixOf y := by simp [Cj]
  have e1 : Cj ⊤ y z 1 = fixOf (y * z) := by simp [Cj]
  have e2 : Cj ⊤ y z 2 = fixOf (y * z ^ 2) := by simp [Cj]
  rw [h0, e1] at h1
  rw [h0, e2] at h2
  exact ⟨h4, by rw [h1, h4], by rw [h2, h4]⟩

end Fpf

theorem apply_mem_fixOf_of_commute {x y : MulAut V} (hxy : x * y = y * x) {w : V}
    (hw : w ∈ fixOf y) : x w ∈ fixOf y := by
  have hw' : y w = w := hw
  show y (x w) = x w
  calc y (x w) = (y * x) w := rfl
    _ = (x * y) w := by rw [hxy]
    _ = x (y w) := rfl
    _ = x w := by rw [hw']

theorem commute_preserves_fix {u y z : MulAut V} (huy : u * y = y * u) (huz : u * z = z * u)
    (j : ℕ) {c : V} (hc : c ∈ fixOf (y * z ^ j)) : u c ∈ fixOf (y * z ^ j) := by
  apply apply_mem_fixOf_of_commute _ hc
  have : u * z ^ j = z ^ j * u := (Commute.pow_right (show Commute u z from huz) j).eq
  calc u * (y * z ^ j) = (u * y) * z ^ j := by group
    _ = y * (u * z ^ j) := by rw [huy]; group
    _ = y * (z ^ j * u) := by rw [this]
    _ = (y * z ^ j) * u := by group

theorem pow_eq_one_of_mod_three {x : MulAut V} (hx3 : x ^ 3 = 1) {n : ℕ} (hn : n % 3 = 0) :
    x ^ n = 1 := by
  obtain ⟨k, rfl⟩ := Nat.dvd_of_mod_eq_zero hn
  rw [pow_mul, hx3, one_pow]

end SevenMod


section Klein

variable {V : Type*} [CommGroup V] [Finite V]

theorem klein_cases {C : Subgroup V} (hC4 : Nat.card C = 4)
    {ζ : MulAut V} (hζ3 : ζ ^ 3 = 1) (hζC : ∀ c ∈ C, ζ c ∈ C)
    (hfpf : ∀ c ∈ C, ζ c = c → c = 1) {c : V} (hc : c ∈ C) (hc1 : c ≠ 1) :
    ∀ d ∈ C, d = 1 ∨ d = c ∨ d = ζ c ∨ d = ζ (ζ c) := by
  have hz := pow_apply_three hζ3
  have hζ1 : ζ c ≠ c := fun h => hc1 (hfpf c hc h)
  have hζζ : ζ (ζ c) ≠ c := by
    intro h
    apply hζ1
    have := congrArg ζ h
    rw [hz] at this
    exact this.symm
  have hζζ' : ζ (ζ c) ≠ ζ c := by
    intro h
    apply hζ1
    exact (ζ.injective h)
  have h1ζ : (1 : V) ≠ ζ c := by
    intro h
    apply hc1
    have : ζ c = ζ 1 := by rw [← h, map_one]
    exact ζ.injective this
  have h1ζζ : (1 : V) ≠ ζ (ζ c) := by
    intro h
    apply h1ζ
    have : ζ (ζ c) = ζ 1 := by rw [← h, map_one]
    rw [ζ.injective this]
  let S : Set V := {1, c, ζ c, ζ (ζ c)}
  have hS : S ⊆ (C : Set V) := by
    intro d hd
    rcases hd with rfl | rfl | rfl | rfl
    · exact C.one_mem
    · exact hc
    · exact hζC c hc
    · exact hζC _ (hζC c hc)
  have hScard : S.ncard = 4 := by
    show ({1, c, ζ c, ζ (ζ c)} : Set V).ncard = 4
    rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair hζζ'.symm]
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hζ1.symm, hζζ.symm⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hc1.symm, h1ζ, h1ζζ⟩
  have hCc : (C : Set V).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact hC4
  have hSeq : S = (C : Set V) := by
    apply Set.eq_of_subset_of_ncard_le hS
    rw [hScard, hCc]
  intro d hd
  have : d ∈ S := by rw [hSeq]; exact hd
  simpa [S] using this

theorem klein_trivial {C : Subgroup V} (hC4 : Nat.card C = 4)
    {ζ : MulAut V} (hζ3 : ζ ^ 3 = 1) (hζC : ∀ c ∈ C, ζ c ∈ C)
    (hfpf : ∀ c ∈ C, ζ c = c → c = 1) {w : MulAut V} (hwC : ∀ c ∈ C, w c ∈ C)
    (hwζ : w * ζ = ζ * w) {k : ℕ} (hwk : w ^ (2 ^ k) = 1) : ∀ c ∈ C, w c = c := by
  intro c hc
  by_cases hc1 : c = 1
  · rw [hc1, map_one]
  have hz := pow_apply_three hζ3
  have hcomm : ∀ n : ℕ, ∀ u : V, w ((ζ ^ n) u) = (ζ ^ n) (w u) := by
    intro n u
    induction n with
    | zero => simp
    | succ m ih =>
      rw [pow_succ']
      show w (ζ ((ζ ^ m) u)) = ζ ((ζ ^ m) (w u))
      have : w (ζ ((ζ ^ m) u)) = ζ (w ((ζ ^ m) u)) :=
        congrArg (fun φ : MulAut V => φ ((ζ ^ m) u)) hwζ
      rw [this, ih]
  have hwc := hwC c hc
  have hwc1 : w c ≠ 1 := by
    intro h
    apply hc1
    have : w c = w 1 := by rw [h, map_one]
    exact w.injective this
  have hcases := klein_cases hC4 hζ3 hζC hfpf hc hc1 (w c) hwc
  obtain ⟨i, hi, hwi⟩ : ∃ i : ℕ, i < 3 ∧ w c = (ζ ^ i) c := by
    rcases hcases with h | h | h | h
    · exact absurd h hwc1
    · exact ⟨0, by norm_num, by simpa using h⟩
    · exact ⟨1, by norm_num, by simpa using h⟩
    · exact ⟨2, by norm_num, by simp [pow_two, h]⟩
  have hwn : ∀ n : ℕ, (w ^ n) c = (ζ ^ (n * i)) c := by
    intro n
    induction n with
    | zero => simp
    | succ m ih =>
      have e1 : (w ^ (m + 1)) c = w ((w ^ m) c) := by rw [pow_succ']; rfl
      rw [e1, ih, hcomm, hwi]
      show (ζ ^ (m * i)) ((ζ ^ i) c) = (ζ ^ ((m + 1) * i)) c
      rw [add_mul, one_mul, pow_add]
      rfl
  have h2k := hwn (2 ^ k)
  rw [hwk] at h2k
  have h1c : (1 : MulAut V) c = c := rfl
  have hfix : (ζ ^ (2 ^ k * i)) c = c := by rw [← h2k]; rfl
  by_cases hi0 : i = 0
  · rw [hwi, hi0]; simp
  · exfalso
    have hmod : (2 ^ k * i) % 3 = 1 ∨ (2 ^ k * i) % 3 = 2 := by
      have h2 : 2 ^ k % 3 = 1 ∨ 2 ^ k % 3 = 2 := by
        rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
        · left; rw [hm, ← two_mul, pow_mul]; norm_num [Nat.pow_mod]
        · right; rw [hm, pow_succ, pow_mul]; norm_num [Nat.mul_mod, Nat.pow_mod]
      have hi' : i % 3 = 1 ∨ i % 3 = 2 := by omega
      rcases h2 with h2 | h2 <;> rcases hi' with hi' | hi' <;> simp [Nat.mul_mod, h2, hi']
    have hpow : ζ ^ (2 ^ k * i) = ζ ^ ((2 ^ k * i) % 3) := pow_eq_pow_mod _ hζ3
    rw [hpow] at hfix
    rcases hmod with hm | hm
    · rw [hm] at hfix
      simp only [pow_one] at hfix
      exact hc1 (hfpf c hc hfix)
    · rw [hm] at hfix
      have : ζ (ζ c) = c := hfix
      apply hc1
      apply hfpf c hc
      have h3 := congrArg ζ this
      rw [hz] at h3
      exact h3.symm

end Klein

end CFSG.Quasithin
