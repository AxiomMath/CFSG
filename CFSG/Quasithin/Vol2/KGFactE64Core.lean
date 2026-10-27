module

public import CFSG.Quasithin.Vol2.KGFactHeInspCore
public import CFSG.Quasithin.Vol2.KGFact3312Base

public section

namespace CFSG.Quasithin.H13.KGInsp

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13.KGH91
open CFSG.ComponentClassification.CatalogueBGraphForm (slGraphAut)
open Matrix

variable {G : Type*} [Group G]

@[expose] def conjP (y a : G) (i : ℕ) : G := y ^ i * a * (y ^ i)⁻¹

@[expose] def fA (y a : G) : G := conjP y a 3 * conjP y a 1 * a

@[expose] def fB (y b : G) : G := conjP y b 3 * conjP y b 2 * b

@[expose] def Bad (y a b : G) : Prop :=
  a ≠ 1 ∧ b ≠ 1 ∧ a * a = 1 ∧ b * b = 1 ∧ fA y a = 1 ∧ fB y b = 1 ∧
    ∀ i < 3, ∀ j < 3, conjP y a i * conjP y b j = conjP y b j * conjP y a i

theorem conjP_map {H : Type*} [Group H] (φ : G →* H) (y a : G) (i : ℕ) :
    φ (conjP y a i) = conjP (φ y) (φ a) i := by
  simp [conjP, map_mul, map_inv, map_pow]

theorem fA_map {H : Type*} [Group H] (φ : G →* H) (y a : G) : φ (fA y a) = fA (φ y) (φ a) := by
  simp only [fA, map_mul, conjP_map]

theorem fB_map {H : Type*} [Group H] (φ : G →* H) (y a : G) : φ (fB y a) = fB (φ y) (φ a) := by
  simp only [fB, map_mul, conjP_map]

theorem Bad.map {H : Type*} [Group H] {φ : G →* H} (hφ : Function.Injective φ) {y a b : G}
    (h : Bad y a b) : Bad (φ y) (φ a) (φ b) := by
  obtain ⟨ha, hb, haa, hbb, hfa, hfb, hc⟩ := h
  refine ⟨fun h1 => ha (hφ (by rw [h1, map_one])), fun h1 => hb (hφ (by rw [h1, map_one])),
    by rw [← map_mul, haa, map_one], by rw [← map_mul, hbb, map_one],
    by rw [← fA_map, hfa, map_one], by rw [← fB_map, hfb, map_one], fun i hi j hj => ?_⟩
  rw [← conjP_map, ← conjP_map, ← map_mul, ← map_mul, hc i hi j hj]

@[expose] def M0 : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 0, 1; 1, 0, 1; 0, 1, 0]

@[expose] def A0 : SpecialLinearGroup (Fin 3) (ZMod 2) :=
  ⟨M0, by rw [M0, Matrix.det_fin_three]; decide +kernel⟩

theorem coe_A0_pow (m : ℕ) :
    ((A0 ^ m : SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) = M0 ^ m :=
  Matrix.SpecialLinearGroup.coe_pow A0 m

theorem A0_pow_seven : A0 ^ 7 = 1 := by
  apply Subtype.ext
  show ((A0 ^ 7 : SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1
  rw [coe_A0_pow]
  decide +kernel

theorem A0_pow_two_pow (e : ℕ) : A0 ^ 2 ^ e = A0 ∨ A0 ^ 2 ^ e = A0 ^ 2 ∨ A0 ^ 2 ^ e = A0 ^ 4 := by
  induction e with
  | zero => left; simp
  | succ e ih =>
    rw [pow_succ, pow_mul]
    rcases ih with h | h | h <;> rw [h]
    · right; left; rfl
    · right; right; rw [← pow_mul]
    · left
      rw [← pow_mul, show 4 * 2 = 7 + 1 by norm_num, pow_add, A0_pow_seven, one_mul, pow_one]

theorem coe_slGraphAut (g : SpecialLinearGroup (Fin 3) (ZMod 2)) :
    ((slGraphAut 3 (ZMod 2) g : SpecialLinearGroup (Fin 3) (ZMod 2)) :
      Matrix (Fin 3) (Fin 3) (ZMod 2)) = ((g⁻¹ : SpecialLinearGroup (Fin 3) (ZMod 2)) :
        Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ := rfl

theorem A0_pow_inv {m : ℕ} (hm : m ≤ 7) : (A0 ^ m)⁻¹ = A0 ^ (7 - m) := by
  rw [inv_eq_iff_mul_eq_one, ← pow_add, show m + (7 - m) = 7 by omega, A0_pow_seven]

theorem cubic_of_pow {A : SpecialLinearGroup (Fin 3) (ZMod 2)}
    (hA : A = A0 ^ 1 ∨ A = A0 ^ 2 ∨ A = A0 ^ 4) :
    (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) ^ 3 + (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) + 1 = 0 ∧
      ((slGraphAut 3 (ZMod 2) A : SpecialLinearGroup (Fin 3) (ZMod 2)) :
          Matrix (Fin 3) (Fin 3) (ZMod 2)) ^ 3 +
        ((slGraphAut 3 (ZMod 2) A : SpecialLinearGroup (Fin 3) (ZMod 2)) :
          Matrix (Fin 3) (Fin 3) (ZMod 2)) ^ 2 + 1 = 0 ∧ A ≠ 1 := by
  have hne : ∀ m : ℕ, M0 ^ m ≠ 1 → A0 ^ m ≠ 1 := fun m hm h => hm (by
    rw [← coe_A0_pow, h]; rfl)
  rcases hA with rfl | rfl | rfl
  · refine ⟨by rw [coe_A0_pow]; decide +kernel, ?_, hne 1 (by decide +kernel)⟩
    rw [coe_slGraphAut, A0_pow_inv (by norm_num), coe_A0_pow]
    decide +kernel
  · refine ⟨by rw [coe_A0_pow]; decide +kernel, ?_, hne 2 (by decide +kernel)⟩
    rw [coe_slGraphAut, A0_pow_inv (by norm_num), coe_A0_pow]
    decide +kernel
  · refine ⟨by rw [coe_A0_pow]; decide +kernel, ?_, hne 4 (by decide +kernel)⟩
    rw [coe_slGraphAut, A0_pow_inv (by norm_num), coe_A0_pow]
    decide +kernel

section Module

variable {X : Type} [Group X] {Y W : Subgroup X}

theorem conjP_mem (C : NatCoord Y W 3) (y : Y) {w : X} (hw : w ∈ W) (i : ℕ) :
    conjP (y : X) w i ∈ W := by
  have h := C.conj_mem (y ^ i) hw
  simpa [conjP] using h

theorem E_conjP (C : NatCoord Y W 3) (y : Y) {w : X} (hw : w ∈ W) (i : ℕ) :
    C.E (conjP (y : X) w i) =
      ((C.ρ y : SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) ^ i *ᵥ
        C.E w := by
  have h := C.conj (y ^ i) w hw
  rw [map_pow, Matrix.SpecialLinearGroup.coe_pow] at h
  simpa [conjP] using h

theorem fA_eq_one (C : NatCoord Y W 3) (y : Y)
    (hy : ((C.ρ y : SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) ^ 3 +
      ((C.ρ y : SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) + 1 = 0)
    {w : X} (hw : w ∈ W) : fA (y : X) w = 1 := by
  have h3 := conjP_mem C y hw 3
  have h1 := conjP_mem C y hw 1
  have hm : fA (y : X) w ∈ W := W.mul_mem (W.mul_mem h3 h1) hw
  refine C.eq_one_of_E hm ?_
  rw [fA, C.map_mul _ (W.mul_mem h3 h1) _ hw, C.map_mul _ h3 _ h1, E_conjP C y hw,
    E_conjP C y hw, pow_one, ← Matrix.add_mulVec, ← Matrix.one_mulVec (C.E w),
    Matrix.mulVec_mulVec, Matrix.mul_one, ← Matrix.add_mulVec, hy, Matrix.zero_mulVec]

theorem fB_eq_one (C : NatCoord Y W 3) (y : Y)
    (hy : ((C.ρ y : SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) ^ 3 +
      ((C.ρ y : SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) ^ 2 + 1 =
        0)
    {w : X} (hw : w ∈ W) : fB (y : X) w = 1 := by
  have h3 := conjP_mem C y hw 3
  have h2 := conjP_mem C y hw 2
  have hm : fB (y : X) w ∈ W := W.mul_mem (W.mul_mem h3 h2) hw
  refine C.eq_one_of_E hm ?_
  rw [fB, C.map_mul _ (W.mul_mem h3 h2) _ hw, C.map_mul _ h3 _ h2, E_conjP C y hw,
    E_conjP C y hw, ← Matrix.add_mulVec, ← Matrix.one_mulVec (C.E w),
    Matrix.mulVec_mulVec, Matrix.mul_one, ← Matrix.add_mulVec, hy, Matrix.zero_mulVec]

theorem exists_y {W₁ W₂ : Subgroup X} (C₁ : NatCoord Y W₁ 3) (C₂ : NatCoord Y W₂ 3)
    (hK : IsPGroup 2 C₁.ρ.ker) (hdual : ∀ y, C₂.ρ y = slGraphAut 3 (ZMod 2) (C₁.ρ y)) :
    ∃ y : Y, orderOf (y : X) = 7 ∧ (∀ w ∈ W₁, fA (y : X) w = 1) ∧
      ∀ w ∈ W₂, fB (y : X) w = 1 := by
  obtain ⟨y₀, hy₀⟩ := C₁.ρ_surj A0
  have hk : y₀ ^ 7 ∈ C₁.ρ.ker := by
    rw [MonoidHom.mem_ker, map_pow, hy₀, A0_pow_seven]
  obtain ⟨e, he⟩ := hK ⟨y₀ ^ 7, hk⟩
  have he' : (y₀ ^ 7) ^ 2 ^ e = 1 := by
    have := congrArg Subtype.val he
    simpa using this
  set y : Y := y₀ ^ 2 ^ e with hy
  have hρ : C₁.ρ y = A0 ^ 2 ^ e := by rw [hy, map_pow, hy₀]
  have hA := cubic_of_pow (A := A0 ^ 2 ^ e) (by
    rcases A0_pow_two_pow e with h | h | h
    · left; rw [h, pow_one]
    · right; left; exact h
    · right; right; exact h)
  have hy7 : y ^ 7 = 1 := by rw [hy, ← pow_mul, mul_comm, pow_mul, he']
  have hy1 : y ≠ 1 := fun h => hA.2.2 (by rw [← hρ, h, map_one])
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  refine ⟨y, ?_, fun w hw => fA_eq_one C₁ y (by rw [hρ]; exact hA.1) hw,
    fun w hw => fB_eq_one C₂ y (by rw [hdual, hρ]; exact hA.2.1) hw⟩
  refine orderOf_eq_prime (by rw [← Subgroup.coe_pow, hy7]; rfl) ?_
  intro h
  exact hy1 (Subtype.ext h)

end Module

@[expose] def BadData (X : Type*) [Group X] : Prop :=
  ∃ (R N : Subgroup X) (y a b : X), IsSylowTwoOf R ⊤ ∧ R ≤ N ∧ N ≠ ⊤ ∧ y ∈ N ∧
    orderOf y = 7 ∧ a ∈ pCoreOf 2 N ∧ b ∈ pCoreOf 2 N ∧ Bad y a b

theorem badData_of_cfg {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hX : Nat.card X ≠ 168) (h : HeInspCfg X 3) : BadData X := by
  obtain ⟨Y, W₁, W₂, C₁, C₂, τ, hWY, -, hab, hK, hdual, -, -, hsyl⟩ := h
  obtain ⟨R, hR, hRN⟩ := hsyl rfl
  obtain ⟨y, hord, hfa, hfb⟩ := exists_y C₁ C₂ hK hdual
  obtain ⟨a, ha, ha1⟩ := exists_ne_one C₁
  obtain ⟨b, hb, hb1⟩ := exists_ne_one C₂
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := Subgroup.normalizer (Y : Set X) with hN
  have hsq : ∀ x ∈ W₁ ⊔ W₂, x * x = 1 := fun x hx => by rw [← sq]; exact hab.2 x hx
  have hcomm : ∀ x ∈ W₁ ⊔ W₂, ∀ z ∈ W₁ ⊔ W₂, x * z = z * x := fun x hx z hz =>
    congrArg Subtype.val (hab.1.is_comm.comm ⟨x, hx⟩ ⟨z, hz⟩)
  have hp : ∀ {W : Subgroup X}, W ≤ W₁ ⊔ W₂ → IsPGroup 2 W := fun hW x =>
    ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow, sq]; exact hsq _ (hW x.2))⟩
  have hYN : pCoreOf 2 Y ≤ pCoreOf 2 N :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 Y).trans Subgroup.le_normalizer)
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y)
  have hW : ∀ {W : Subgroup X}, W ≤ W₁ ⊔ W₂ → Y ≤ Subgroup.normalizer (W : Set X) →
      W ≤ pCoreOf 2 N := fun hW hYW =>
    (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hW.trans hWY) hYW (hp hW)).trans hYN
  refine ⟨R, N, y, a, b, hR, hRN, normalizer_ne_top hX C₁ hK, Subgroup.le_normalizer y.2, hord,
    hW le_sup_left C₁.le ha, hW le_sup_right C₂.le hb, ha1, hb1,
    hsq a (Subgroup.mem_sup_left ha), hsq b (Subgroup.mem_sup_right hb), hfa a ha, hfb b hb,
    fun i _ j _ => hcomm _ (Subgroup.mem_sup_left (conjP_mem C₁ y ha i)) _
      (Subgroup.mem_sup_right (conjP_mem C₂ y hb j))⟩

theorem BadData.map {X Γ : Type} [Group X] [Group Γ] [Finite X] (e : X ≃* Γ)
    (h : BadData X) : BadData Γ := by
  obtain ⟨R, N, y, a, b, hR, hRN, hN, hy, hord, ha, hb, hbad⟩ := h
  refine ⟨R.map e.toMonoidHom, N.map e.toMonoidHom, e y, e a, e b,
    KG3312.isSylowTwoOf_map_equiv e hR, Subgroup.map_mono hRN, fun htop => hN ?_,
    Subgroup.mem_map_of_mem _ hy, by rw [MulEquiv.orderOf_eq]; exact hord, ?_, ?_,
    hbad.map (φ := e.toMonoidHom) e.injective⟩
  · rw [eq_top_iff]
    intro x _
    have hx : e x ∈ N.map e.toMonoidHom := by rw [htop]; exact Subgroup.mem_top _
    obtain ⟨x', hx', hxx⟩ := hx
    rwa [e.injective hxx] at hx'
  · rw [CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv]
    exact Subgroup.mem_map_of_mem _ ha
  · rw [CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv]
    exact Subgroup.mem_map_of_mem _ hb

theorem BadData.conj {Γ : Type} [Group Γ] [Finite Γ] {S : Subgroup Γ} (hS : IsSylowTwoOf S ⊤)
    (h : BadData Γ) : ∃ (N : Subgroup Γ) (y a b : Γ), S ≤ N ∧ N ≠ ⊤ ∧ y ∈ N ∧
      orderOf y = 7 ∧ a ∈ pCoreOf 2 N ∧ b ∈ pCoreOf 2 N ∧ Bad y a b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, N, y, a, b, hR, hRN, hN, hy, hord, ha, hb, hbad⟩ := h
  obtain ⟨hp, hi⟩ := K1.isSylowTwoOf_top_iff.mp hR
  obtain ⟨hpS, hiS⟩ := K1.isSylowTwoOf_top_iff.mp hS
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ (hp.toSylow hi) (hpS.toSylow hiS)
  have hRS : R.map (MulAut.conj g).toMonoidHom = S := by
    have := congrArg (fun P : Sylow 2 Γ => (P : Subgroup Γ)) hg
    simp only [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at this
    exact Eq.trans rfl this
  set e : Γ ≃* Γ := MulAut.conj g with he
  refine ⟨N.map e.toMonoidHom, e y, e a, e b, hRS ▸ Subgroup.map_mono hRN, fun htop => hN ?_,
    Subgroup.mem_map_of_mem _ hy, by rw [MulEquiv.orderOf_eq]; exact hord, ?_, ?_,
    hbad.map (φ := e.toMonoidHom) e.injective⟩
  · rw [eq_top_iff]
    intro x _
    have hx : e x ∈ N.map e.toMonoidHom := by rw [htop]; exact Subgroup.mem_top _
    obtain ⟨x', hx', hxx⟩ := hx
    rwa [e.injective hxx] at hx'
  · rw [CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv]
    exact Subgroup.mem_map_of_mem _ ha
  · rw [CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv]
    exact Subgroup.mem_map_of_mem _ hb

theorem exists_conj_pow {G : Type*} [Group G] [Finite G] {N : Subgroup G}
    (h49 : ¬ 49 ∣ Nat.card N) {y y₀ : G} (hy : y ∈ N) (hy₀ : y₀ ∈ N) (ho : orderOf y = 7)
    (ho₀ : orderOf y₀ = 7) : ∃ h ∈ N, ∃ k, 1 ≤ k ∧ k ≤ 6 ∧ y = h * y₀ ^ k * h⁻¹ := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  set u : N := ⟨y, hy⟩ with hu
  set u₀ : N := ⟨y₀, hy₀⟩ with hu₀
  have hou : orderOf u = 7 := by rw [Subgroup.orderOf_mk]; exact ho
  have hou₀ : orderOf u₀ = 7 := by rw [Subgroup.orderOf_mk]; exact ho₀
  have h7 : 7 ∣ Nat.card N := hou ▸ orderOf_dvd_natCard u
  obtain ⟨m, hm⟩ := h7
  have hm7 : ¬ 7 ∣ m := fun h => h49 (by rw [hm]; exact Nat.mul_dvd_mul_left 7 h)
  have hf : (Nat.card N).factorization 7 = 1 := by
    rw [hm, Nat.factorization_mul (by norm_num) (by rintro rfl; simp at hm7),
      Finsupp.add_apply, Nat.Prime.factorization_self (by norm_num),
      Nat.factorization_eq_zero_of_not_dvd hm7]
  have hcard : ∀ v : N, orderOf v = 7 →
      Nat.card (Subgroup.zpowers v) = 7 ^ (Nat.card N).factorization 7 := fun v hv => by
    rw [Nat.card_zpowers, hv, hf, pow_one]
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq N (Sylow.ofCard _ (hcard u₀ hou₀))
    (Sylow.ofCard _ (hcard u hou))
  have hmem : u ∈ ((g • Sylow.ofCard _ (hcard u₀ hou₀) : Sylow 7 N) : Subgroup N) := by
    rw [hg, Sylow.coe_ofCard]
    exact Subgroup.mem_zpowers u
  rw [Sylow.coe_subgroup_smul, Sylow.coe_ofCard, Subgroup.mem_smul_pointwise_iff_exists] at hmem
  obtain ⟨v, hv, hvu⟩ := hmem
  obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
  set k := (z % 7).toNat with hk
  have hz : u₀ ^ z = u₀ ^ k := by
    rw [← zpow_mod_orderOf, hou₀, hk, ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _
      (by norm_num))]
    push_cast
    rfl
  have hk7 : k < 7 := by
    have := Int.emod_lt_of_pos z (by norm_num : (0 : ℤ) < 7)
    omega
  have hyu : u = g * u₀ ^ k * g⁻¹ := by
    rw [← hvu, hz, MulAut.smul_def, MulAut.conj_apply]
  have hk0 : k ≠ 0 := by
    rintro h0
    rw [h0, pow_zero, mul_one, mul_inv_cancel] at hyu
    rw [hyu, orderOf_one] at hou
    norm_num at hou
  refine ⟨g, g.2, k, by omega, by omega, ?_⟩
  have := congrArg Subtype.val hyu
  simpa using this

end CFSG.Quasithin.H13.KGInsp
