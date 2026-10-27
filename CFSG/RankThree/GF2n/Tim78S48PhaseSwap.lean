module

public import CFSG.RankThree.GF2n.Tim78S48PhaseNum

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n
open Matrix
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G]

structure IsNatCoords {B T : Subgroup G} {g : G} {F : Type} [Field F] (D : L2Coords B T g F)
    (Θ : (Fin 2 → F) → G) : Prop where
  mem : ∀ v, Θ v ∈ B ⊔ conjSubgroup g B
  mul : ∀ v v', Θ (v + v') = Θ v * Θ v'
  inj : Function.Injective Θ
  surj : ∀ w ∈ B ⊔ conjSubgroup g B, ∃ v, Θ v = w
  conj : ∀ (x : ↥(T ⊔ conjSubgroup g T)) (v : Fin 2 → F),
    (x : G) * Θ v * (x : G)⁻¹ = Θ ((D.ε x : Matrix (Fin 2) (Fin 2) F) *ᵥ v)

theorem hasNatCoords_iff {B T : Subgroup G} {g : G} {F : Type} [Field F] (D : L2Coords B T g F) :
    HasNatCoords D ↔ ∃ Θ, IsNatCoords D Θ :=
  ⟨fun ⟨Θ, h1, h2, h3, h4, h5⟩ => ⟨Θ, ⟨h1, h2, h3, h4, h5⟩⟩,
    fun ⟨Θ, h⟩ => ⟨Θ, h.mem, h.mul, h.inj, h.surj, h.conj⟩⟩

theorem IsNatCoords.zero {B T : Subgroup G} {g : G} {F : Type} [Field F] {D : L2Coords B T g F}
    {Θ : (Fin 2 → F) → G} (h : IsNatCoords D Θ) : Θ 0 = 1 := by
  have h1 := h.mul 0 0
  rw [add_zero] at h1
  exact mul_left_cancel (a := Θ 0) (by rw [mul_one]; exact h1.symm)

section MulVec

variable {F : Type} [Field F]

theorem weyl_mulVec [CharP F 2] {s : F} (hs : s ≠ 0) (x y : F) :
    ((utriElt s * ltriElt s⁻¹ * utriElt s : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ ![x, y] =
      ![s * y, s⁻¹ * x] := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hss : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  have hss' : s⁻¹ * s = 1 := inv_mul_cancel₀ hs
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, utriElt_mulVec, ltriElt_mulVec, utriElt_mulVec]
  ext i
  fin_cases i
  · show (x + s * y) + s * (s⁻¹ * (x + s * y) + y) = s * y
    linear_combination (x + s * y) * hss + (x + s * y) * h2
  · show s⁻¹ * (x + s * y) + y = s⁻¹ * x
    linear_combination y * hss' + y * h2

end MulVec

theorem relIndex_conjSubgroup (w : G) (U V : Subgroup G) :
    (conjSubgroup w U).relIndex (conjSubgroup w V) = U.relIndex V :=
  Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj w).toMonoidHom) U V
    (MulAut.conj w).injective

theorem inv_mul_mem_normalizer_of_conj_eq {x w : G} {U : Subgroup G}
    (h : conjSubgroup w U = conjSubgroup x U) : x⁻¹ * w ∈ Subgroup.normalizer (U : Set G) := by
  rw [← conjSubgroup_eq_self_iff, conjSubgroup_mul, h, ← conjSubgroup_mul, inv_mul_cancel,
    conjSubgroup_one]

theorem conjSubgroup_mul_of_mem_normalizer {x n : G} {U : Subgroup G}
    (hn : n ∈ Subgroup.normalizer (U : Set G)) : conjSubgroup (x * n) U = conjSubgroup x U := by
  rw [conjSubgroup_mul, conjSubgroup_eq_self_iff.mpr hn]

theorem conjSubgroup_mono_of_le {g : G} {A B : Subgroup G} (h : A ≤ B) :
    conjSubgroup g A ≤ conjSubgroup g B :=
  Subgroup.map_mono h

theorem mul_mul_inv_mem_conjSubgroup {U : Subgroup G} {x : G} (g : G) (hx : x ∈ U) :
    g * x * g⁻¹ ∈ conjSubgroup g U := by
  rw [mem_conjSubgroup]
  simpa [mul_assoc] using hx

theorem normalizer_conj_le [Finite G] {B T : Subgroup G} (g : G)
    (h : Subgroup.normalizer (B : Set G) ≤ Subgroup.normalizer (T : Set G)) :
    Subgroup.normalizer ((conjSubgroup g B : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((conjSubgroup g T : Subgroup G) : Set G) := by
  intro k hk
  have h1 : g⁻¹ * k * g ∈ Subgroup.normalizer (B : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun z hz => ?_
    have h2 : k * (g * z * g⁻¹) * k⁻¹ ∈ conjSubgroup g B :=
      (Subgroup.mem_normalizer_iff.mp hk _).mp (mul_mul_inv_mem_conjSubgroup g hz)
    rw [mem_conjSubgroup] at h2
    simpa [mul_assoc] using h2
  have h3 := h h1
  refine Subgroup.mem_normalizer_fintype fun z hz => ?_
  have hz' : z ∈ conjSubgroup g T := hz
  rw [mem_conjSubgroup] at hz'
  have h4 := (Subgroup.mem_normalizer_iff.mp h3 _).mp hz'
  show k * z * k⁻¹ ∈ conjSubgroup g T
  rw [mem_conjSubgroup]
  simpa [mul_assoc] using h4

theorem Core48.exists_T_not_kernel {Q B T : Subgroup G} {g : G} (C : Core48 Q B T g) :
    ∃ t ∈ T, t ∉ kernel48 B T g := by
  by_contra hcon
  refine C.T_not_cent fun t ht b hb => ?_
  have hk : t ∈ kernel48 B T g := by
    by_contra hk
    exact hcon ⟨t, ht, hk⟩
  exact (Subgroup.mem_centralizer_iff.mp hk.2 b (Subgroup.mem_sup_right hb)).symm

theorem Core48.exists_Tg_not_kernel {Q B T : Subgroup G} {g : G} (C : Core48 Q B T g) :
    ∃ t ∈ conjSubgroup g T, t ∉ kernel48 B T g := by
  by_contra hcon
  refine C.Tg_not_cent fun t ht b hb => ?_
  have hk : t ∈ kernel48 B T g := by
    by_contra hk
    exact hcon ⟨t, ht, hk⟩
  exact (Subgroup.mem_centralizer_iff.mp hk.2 b (Subgroup.mem_sup_left hb)).symm

structure WeylSwap (B T : Subgroup G) (g w : G) : Prop where
  mem_X : w ∈ T ⊔ conjSubgroup g T
  conj_B : conjSubgroup w B = conjSubgroup g B
  conj_T : conjSubgroup w T = conjSubgroup g T
  conj_Tg : conjSubgroup w (conjSubgroup g T) = T
  conj_Bg : conjSubgroup w (conjSubgroup g B) = B
  sq_mem : w * w ∈ kernel48 B T g

theorem WeylSwap.conj_S {B T : Subgroup G} {g w : G} (W₀ : WeylSwap B T g w) :
    conjSubgroup w (B ⊔ (T ⊓ conjSubgroup g T)) = conjSubgroup g B ⊔ (T ⊓ conjSubgroup g T) := by
  rw [conjSubgroup_sup_eq_sup, conjSubgroup_inf_eq_inf, W₀.conj_B, W₀.conj_T, W₀.conj_Tg,
    inf_comm]

def commSub (N S : Subgroup G) : Subgroup G where
  carrier := {h | h ∈ Subgroup.normalizer (N : Set G) ∧ ∀ a ∈ S, ⁅h, a⁆ ∈ N}
  mul_mem' {x y} hx hy := by
    refine ⟨(Subgroup.normalizer (N : Set G)).mul_mem hx.1 hy.1, fun a ha => ?_⟩
    have e : ⁅x * y, a⁆ = (x * ⁅y, a⁆ * x⁻¹) * ⁅x, a⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact N.mul_mem ((Subgroup.mem_normalizer_iff.mp hx.1 _).mp (hy.2 a ha)) (hx.2 a ha)
  one_mem' := ⟨(Subgroup.normalizer (N : Set G)).one_mem, fun a _ => by simp⟩
  inv_mem' {x} hx := by
    refine ⟨(Subgroup.normalizer (N : Set G)).inv_mem hx.1, fun a ha => ?_⟩
    have e : ⁅x⁻¹, a⁆ = x⁻¹ * ⁅x, a⁆⁻¹ * x⁻¹⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (N : Set G)).inv_mem hx.1) _).mp
      (N.inv_mem (hx.2 a ha))

theorem mem_commSub {N S : Subgroup G} {h : G} :
    h ∈ commSub N S ↔ h ∈ Subgroup.normalizer (N : Set G) ∧ ∀ a ∈ S, ⁅h, a⁆ ∈ N := Iff.rfl

namespace Hyp4

variable [Finite G] {M B Q P T : Subgroup G} (H : Hyp4 M B Q P T) {g : G}
include H

section Theta

variable {F : Type} [Field F]

theorem Θ_mem_B (h48 : Hyp48 M B T g) (hP : ¬ conjSubgroup g B ≤ P)
    (hTK : ∃ t ∈ T, t ∉ kernel48 B T g) {D : L2Coords B T g F} {Θ : (Fin 2 → F) → G}
    (N : IsNatCoords D Θ) (x : F) : Θ ![x, 0] ∈ B := by
  refine H.W_cent_T h48 hP hTK _ (N.mem _) fun t ht => ?_
  obtain ⟨s, hs⟩ := D.exists_utri ht
  have h := N.conj ⟨t, Subgroup.mem_sup_left ht⟩ ![x, 0]
  rw [hs, utriElt_mulVec] at h
  simp only [mul_zero, add_zero] at h
  calc t * Θ ![x, 0] = (t * Θ ![x, 0] * t⁻¹) * t := by group
    _ = Θ ![x, 0] * t := by rw [h]

theorem exists_Θ_B {D : L2Coords B T g F} {Θ : (Fin 2 → F) → G} (N : IsNatCoords D Θ) {b : G}
    (hb : b ∈ B) : ∃ x : F, Θ ![x, 0] = b := by
  obtain ⟨v, hv⟩ := N.surj b (Subgroup.mem_sup_left hb)
  obtain ⟨t, ht, hεt⟩ := D.exists_T (1 : F)
  have h := N.conj ⟨t, Subgroup.mem_sup_left ht⟩ v
  rw [hεt, hv] at h
  have h2 : t * b * t⁻¹ = b := by rw [H.T_comm_B ht hb]; group
  rw [h2] at h
  have h3 : v = (utriElt (1 : F) : Matrix (Fin 2) (Fin 2) F) *ᵥ v := N.inj (hv.trans h)
  have hv' : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
  rw [hv', utriElt_mulVec] at h3
  have h4 : v 1 = 0 := by
    have := congrFun h3 0
    simp at this
    exact this
  refine ⟨v 0, ?_⟩
  rw [← hv]
  congr 1
  ext i
  fin_cases i <;> simp [h4]

theorem Θ_mem_Bg (h48 : Hyp48 M B T g) (hP : ¬ conjSubgroup g B ≤ P)
    (hTgK : ∃ t ∈ conjSubgroup g T, t ∉ kernel48 B T g) {D : L2Coords B T g F}
    {Θ : (Fin 2 → F) → G} (N : IsNatCoords D Θ) (y : F) : Θ ![0, y] ∈ conjSubgroup g B := by
  refine H.W_cent_Tg h48 hP hTgK _ (N.mem _) fun t ht => ?_
  obtain ⟨s, hs⟩ := D.exists_ltri ht
  have h := N.conj ⟨t, Subgroup.mem_sup_right ht⟩ ![0, y]
  rw [hs, ltriElt_mulVec] at h
  simp only [mul_zero, zero_add] at h
  calc t * Θ ![0, y] = (t * Θ ![0, y] * t⁻¹) * t := by group
    _ = Θ ![0, y] * t := by rw [h]

theorem exists_Θ_Bg {D : L2Coords B T g F} {Θ : (Fin 2 → F) → G} (N : IsNatCoords D Θ) {b : G}
    (hb : b ∈ conjSubgroup g B) : ∃ y : F, Θ ![0, y] = b := by
  obtain ⟨v, hv⟩ := N.surj b (Subgroup.mem_sup_right hb)
  obtain ⟨t, ht, hεt⟩ := D.exists_Tg (1 : F)
  have h := N.conj ⟨t, Subgroup.mem_sup_right ht⟩ v
  rw [hεt, hv] at h
  have h2 : t * b * t⁻¹ = b := by rw [H.Tg_comm_Bg ht hb]; group
  rw [h2] at h
  have h3 : v = (ltriElt (1 : F) : Matrix (Fin 2) (Fin 2) F) *ᵥ v := N.inj (hv.trans h)
  have hv' : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
  rw [hv', ltriElt_mulVec] at h3
  have h4 : v 0 = 0 := by
    have := congrFun h3 1
    simp at this
    exact this
  refine ⟨v 1, ?_⟩
  rw [← hv]
  congr 1
  ext i
  fin_cases i <;> simp [h4]

omit H in
theorem weyl_conj_Θ [CharP F 2] {D : L2Coords B T g F} {Θ : (Fin 2 → F) → G}
    (N : IsNatCoords D Θ) {s : F} (hs : s ≠ 0) {t t' : G} (ht : t ∈ T)
    (ht' : t' ∈ conjSubgroup g T) (hεt : D.ε ⟨t, Subgroup.mem_sup_left ht⟩ = utriElt s)
    (hεt' : D.ε ⟨t', Subgroup.mem_sup_right ht'⟩ = ltriElt s⁻¹) (x y : F) :
    (t * t' * t) * Θ ![x, y] * (t * t' * t)⁻¹ = Θ ![s * y, s⁻¹ * x] := by
  have hw := N.conj (⟨t, Subgroup.mem_sup_left ht⟩ * ⟨t', Subgroup.mem_sup_right ht'⟩ *
    ⟨t, Subgroup.mem_sup_left ht⟩) ![x, y]
  have e : D.ε (⟨t, Subgroup.mem_sup_left ht⟩ * ⟨t', Subgroup.mem_sup_right ht'⟩ *
      ⟨t, Subgroup.mem_sup_left ht⟩) = utriElt s * ltriElt s⁻¹ * utriElt s := by
    rw [map_mul, map_mul, hεt, hεt']
  rw [e, weyl_mulVec hs] at hw
  exact hw

theorem weyl_swap (h48 : Hyp48 M B T g) (hP : ¬ conjSubgroup g B ≤ P) (C : Core48 Q B T g)
    [CharP F 2] {D : L2Coords B T g F} {Θ : (Fin 2 → F) → G} (N : IsNatCoords D Θ) {s : F}
    (hs : s ≠ 0) {t t' : G} (ht : t ∈ T) (ht' : t' ∈ conjSubgroup g T)
    (hεt : D.ε ⟨t, Subgroup.mem_sup_left ht⟩ = utriElt s)
    (hεt' : D.ε ⟨t', Subgroup.mem_sup_right ht'⟩ = ltriElt s⁻¹) :
    WeylSwap B T g (t * t' * t) := by
  have hTK := C.exists_T_not_kernel
  have hTgK := C.exists_Tg_not_kernel
  have hwc := weyl_conj_Θ N hs ht ht' hεt hεt'
  have hwX : t * t' * t ∈ T ⊔ conjSubgroup g T :=
    (T ⊔ conjSubgroup g T).mul_mem
      ((T ⊔ conjSubgroup g T).mul_mem (Subgroup.mem_sup_left ht) (Subgroup.mem_sup_right ht'))
      (Subgroup.mem_sup_left ht)
  have hB : conjSubgroup (t * t' * t) B = conjSubgroup g B := by
    apply le_antisymm
    · intro y hy
      rw [mem_conjSubgroup] at hy
      obtain ⟨x, hx⟩ := H.exists_Θ_B N hy
      have e : y = (t * t' * t) * Θ ![x, 0] * (t * t' * t)⁻¹ := by rw [hx]; group
      rw [e, hwc, mul_zero]
      exact H.Θ_mem_Bg h48 hP hTgK N _
    · intro y hy
      obtain ⟨z, hz⟩ := H.exists_Θ_Bg N hy
      rw [mem_conjSubgroup]
      have e : y = (t * t' * t) * Θ ![s * z, 0] * (t * t' * t)⁻¹ := by
        rw [hwc, mul_zero, inv_mul_cancel_left₀ hs, hz]
      have e2 : (t * t' * t)⁻¹ * y * (t * t' * t) = Θ ![s * z, 0] := by
        rw [e]; group
      rw [e2]
      exact H.Θ_mem_B h48 hP hTK N _
  have hww : ∀ x y : F, (t * t' * t * (t * t' * t)) * Θ ![x, y] *
      (t * t' * t * (t * t' * t))⁻¹ = Θ ![x, y] := by
    intro x y
    calc (t * t' * t * (t * t' * t)) * Θ ![x, y] * (t * t' * t * (t * t' * t))⁻¹
        = (t * t' * t) * ((t * t' * t) * Θ ![x, y] * (t * t' * t)⁻¹) * (t * t' * t)⁻¹ := by group
      _ = (t * t' * t) * Θ ![s * y, s⁻¹ * x] * (t * t' * t)⁻¹ := by rw [hwc]
      _ = Θ ![s * (s⁻¹ * x), s⁻¹ * (s * y)] := hwc _ _
      _ = Θ ![x, y] := by rw [mul_inv_cancel_left₀ hs, inv_mul_cancel_left₀ hs]
  have hsq : t * t' * t * (t * t' * t) ∈ kernel48 B T g := by
    refine ⟨(T ⊔ conjSubgroup g T).mul_mem hwX hwX, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
    obtain ⟨v, hv⟩ := N.surj z hz
    have hv' : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
    have := hww (v 0) (v 1)
    rw [← hv', hv] at this
    calc z * (t * t' * t * (t * t' * t))
        = ((t * t' * t * (t * t' * t)) * z * (t * t' * t * (t * t' * t))⁻¹) *
            (t * t' * t * (t * t' * t)) := by rw [this]
      _ = (t * t' * t * (t * t' * t)) * z := by group
  have hwM : t * t' * t * (t * t' * t) ∈ Subgroup.normalizer (B : Set G) :=
    H.M_le_normalizer_B (H.kernel_le_M hsq)
  have hwT : t * t' * t * (t * t' * t) ∈ Subgroup.normalizer (T : Set G) :=
    H.kernel_le_normalizer_T hsq
  have hT : conjSubgroup (t * t' * t) T = conjSubgroup g T := by
    obtain ⟨x, -, hxT, hxB⟩ := C.conj
    have h1 := inv_mul_mem_normalizer_of_conj_eq (hB.trans hxB)
    have h2 : x⁻¹ * (t * t' * t) ∈ Subgroup.normalizer (T : Set G) := by
      rw [H.normalizer_B] at h1
      exact H.M_le_normalizer_T h1
    rw [← mul_inv_cancel_left x (t * t' * t), conjSubgroup_mul_of_mem_normalizer h2, hxT]
  refine ⟨hwX, hB, hT, ?_, ?_, hsq⟩
  · rw [← hT, ← conjSubgroup_mul]
    exact conjSubgroup_eq_self_iff.mpr hwT
  · rw [← hB, ← conjSubgroup_mul]
    exact conjSubgroup_eq_self_iff.mpr hwM

end Theta

theorem conj_T0 (h48 : Hyp48 M B T g) {w : G} (W₀ : WeylSwap B T g w) :
    conjSubgroup w (T ⊓ kernel48 B T g) = conjSubgroup g T ⊓ kernel48 B T g := by
  rw [conjSubgroup_inf_eq_inf, W₀.conj_T,
    conjSubgroup_eq_self_iff.mpr (H.X_le_normalizer_kernel h48 W₀.mem_X)]

theorem exists_weyl {F : Type} [Field F] [CharP F 2] (h48 : Hyp48 M B T g)
    (hP : ¬ conjSubgroup g B ≤ P) (C : Core48 Q B T g) {D : L2Coords B T g F}
    {Θ : (Fin 2 → F) → G} (N : IsNatCoords D Θ) : ∃ w, WeylSwap B T g w := by
  obtain ⟨t, ht, hεt⟩ := D.exists_T (1 : F)
  obtain ⟨t', ht', hεt'⟩ := D.exists_Tg ((1 : F)⁻¹)
  exact ⟨t * t' * t, H.weyl_swap h48 hP C N one_ne_zero ht ht' hεt hεt'⟩

section Aux

variable {F : Type} [Field F]

omit H in
theorem inf_Tg_le_kernel (D : L2Coords B T g F) : T ⊓ conjSubgroup g T ≤ kernel48 B T g := by
  intro a ha
  obtain ⟨s, hs⟩ := D.exists_utri ha.1
  obtain ⟨s', hs'⟩ := D.exists_ltri ha.2
  have h : utriElt s = (ltriElt s' : SL(2, F)) := hs.symm.trans hs'
  have h01 := congrArg (fun m : SL(2, F) => (m : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simp only [utriElt_apply_01, ltriElt_apply_01] at h01
  refine (D.ker_iff ⟨a, Subgroup.mem_sup_left ha.1⟩).mp ?_
  rw [hs, h01, utriElt_zero]

omit H in
theorem inv_mul_mem_T_kernel (D : L2Coords B T g F) {t₁ t₂ : G} (h₁ : t₁ ∈ T) (h₂ : t₂ ∈ T)
    (h : D.ε ⟨t₁, Subgroup.mem_sup_left h₁⟩ = D.ε ⟨t₂, Subgroup.mem_sup_left h₂⟩) :
    t₁⁻¹ * t₂ ∈ T ⊓ kernel48 B T g := by
  refine ⟨T.mul_mem (T.inv_mem h₁) h₂, (D.ker_iff ⟨t₁⁻¹ * t₂, ?_⟩).mp ?_⟩
  · exact (T ⊔ conjSubgroup g T).mul_mem ((T ⊔ conjSubgroup g T).inv_mem
      (Subgroup.mem_sup_left h₁)) (Subgroup.mem_sup_left h₂)
  · have e : (⟨t₁⁻¹ * t₂, (T ⊔ conjSubgroup g T).mul_mem ((T ⊔ conjSubgroup g T).inv_mem
        (Subgroup.mem_sup_left h₁)) (Subgroup.mem_sup_left h₂)⟩ : ↥(T ⊔ conjSubgroup g T)) =
        (⟨t₁, Subgroup.mem_sup_left h₁⟩ : ↥(T ⊔ conjSubgroup g T))⁻¹ *
          ⟨t₂, Subgroup.mem_sup_left h₂⟩ := rfl
    rw [e, map_mul, map_inv, h, inv_mul_cancel]

end Aux

end Hyp4

end CFSG.RankThree.GF2n.Tim78
