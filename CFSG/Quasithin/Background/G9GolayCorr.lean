module

public import CFSG.Quasithin.Background.G9GolayRelabel
public import CFSG.Quasithin.Background.B4ModelsSporadic

public section

namespace CFSG.Quasithin.G11

@[expose] def GolayCorr (T : Equiv.Perm (Fin 24)) (S : Submodule (ZMod 2) GolayAmbient)
    (G : Subgroup (G6.PermMod 24)) : Prop :=
  ∀ w : GolayAmbient, w ∈ S ↔ Multiplicative.ofAdd (permAct T w) ∈ G

theorem GolayCorr.inf {T : Equiv.Perm (Fin 24)} {S₁ S₂ : Submodule (ZMod 2) GolayAmbient}
    {G₁ G₂ : Subgroup (G6.PermMod 24)} (h₁ : GolayCorr T S₁ G₁) (h₂ : GolayCorr T S₂ G₂) :
    GolayCorr T (S₁ ⊓ S₂) (G₁ ⊓ G₂) := by
  intro w
  rw [Submodule.mem_inf, Subgroup.mem_inf, h₁ w, h₂ w]

theorem GolayCorr.sup {T : Equiv.Perm (Fin 24)} {S₁ S₂ : Submodule (ZMod 2) GolayAmbient}
    {G₁ G₂ : Subgroup (G6.PermMod 24)} (h₁ : GolayCorr T S₁ G₁) (h₂ : GolayCorr T S₂ G₂) :
    GolayCorr T (S₁ ⊔ S₂) (G₁ ⊔ G₂) := by
  intro w
  constructor
  · intro hw
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hw
    rw [← hyz, golay_permAct_add, ofAdd_add]
    exact Subgroup.mul_mem_sup ((h₁ y).mp hy) ((h₂ z).mp hz)
  · intro hw
    obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup.mp hw
    set a : GolayAmbient := permAct T⁻¹ (Multiplicative.toAdd y) with ha
    set b : GolayAmbient := permAct T⁻¹ (Multiplicative.toAdd z) with hb
    have ha' : a ∈ S₁ := by
      apply (h₁ a).mpr
      rw [ha, golay_permAct_inv_cancel, ofAdd_toAdd]
      exact hy
    have hb' : b ∈ S₂ := by
      apply (h₂ b).mpr
      rw [hb, golay_permAct_inv_cancel, ofAdd_toAdd]
      exact hz
    have hab : a + b = w := by
      apply golay_permAct_injective T
      rw [golay_permAct_add, ha, hb, golay_permAct_inv_cancel, golay_permAct_inv_cancel]
      have h := congrArg Multiplicative.toAdd hyz
      rw [toAdd_mul, toAdd_ofAdd] at h
      exact h
    rw [← hab]
    exact Submodule.add_mem_sup ha' hb'

theorem golayCorr_source {T : Equiv.Perm (Fin 24)}
    (hsrc : ∀ w : GolayAmbient, w ∈ CFSG.Blueprint.EvenSource.sourceGolayCode ↔
      permAct T w ∈ CFSG.Monster.Code.C) :
    GolayCorr T CFSG.Blueprint.EvenSource.sourceGolayCode golayC := by
  intro w
  exact hsrc w

private theorem mem_zpowers_iff_eq_one_or {G : Type*} [Group G] {g x : G} (hg : g * g = 1) :
    x ∈ Subgroup.zpowers g ↔ x = 1 ∨ x = g := by
  constructor
  · intro hx
    let S : Subgroup G :=
      { carrier := {y | y = 1 ∨ y = g}
        mul_mem' := by
          rintro a b ha hb
          rcases ha with ha | ha <;> rcases hb with hb | hb
          · rw [ha, hb]; exact Or.inl (one_mul 1)
          · rw [ha, hb]; exact Or.inr (one_mul g)
          · rw [ha, hb]; exact Or.inr (mul_one g)
          · rw [ha, hb]; exact Or.inl hg
        one_mem' := Or.inl rfl
        inv_mem' := by
          rintro a ha
          rcases ha with ha | ha
          · rw [ha]; exact Or.inl inv_one
          · rw [ha]; exact Or.inr (inv_eq_of_mul_eq_one_right hg) }
    exact Subgroup.zpowers_le.mpr (show g ∈ S from Or.inr rfl) hx
  · rintro (h | h)
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact Subgroup.mem_zpowers g

private theorem golayCorr_span_singleton (T : Equiv.Perm (Fin 24)) (v v' : GolayAmbient)
    (h : permAct T v = v') :
    GolayCorr T (Submodule.span (ZMod 2) {v}) (Subgroup.zpowers (Multiplicative.ofAdd v')) := by
  intro w
  have hspan : w ∈ Submodule.span (ZMod 2) {v} ↔ w = 0 ∨ w = v := by
    rw [Submodule.mem_span_singleton]
    constructor
    · rintro ⟨a, ha⟩
      rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a with ha0 | ha1
      · left
        rw [ha0, zero_smul] at ha
        exact ha.symm
      · right
        rw [ha1, one_smul] at ha
        exact ha.symm
    · rintro (rfl | rfl)
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
  have hgg : Multiplicative.ofAdd v' * Multiplicative.ofAdd v' = 1 := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_ofAdd, toAdd_one]
    funext i
    exact CharTwo.add_self_eq_zero (v' i)
  have hzp : Multiplicative.ofAdd (permAct T w) ∈ Subgroup.zpowers (Multiplicative.ofAdd v') ↔
      permAct T w = 0 ∨ permAct T w = v' := by
    rw [mem_zpowers_iff_eq_one_or hgg]
    constructor
    · rintro (h1 | h1)
      · left
        rw [← toAdd_ofAdd (permAct T w), h1, toAdd_one]
      · right
        exact Multiplicative.ofAdd.injective h1
    · rintro (h0 | hv)
      · left
        apply Multiplicative.toAdd.injective
        rw [toAdd_ofAdd, h0, toAdd_one]
      · right
        rw [hv]
  rw [hspan, hzp]
  constructor
  · rintro (rfl | rfl)
    · left
      exact golay_permAct_zero T
    · right
      exact h
  · rintro (h0 | hv)
    · left
      exact golay_permAct_injective T (by rw [h0, golay_permAct_zero])
    · right
      exact golay_permAct_injective T (by rw [hv, h])

theorem golayCorr_constantLine (T : Equiv.Perm (Fin 24)) :
    GolayCorr T golayConstantLine (Subgroup.zpowers (G6.allOnes 24)) := by
  simpa only [golayConstantLine, G6.allOnes] using
    (golayCorr_span_singleton T (fun _ : Fin 24 => (1 : ZMod 2)) (fun _ => 1)
      (by funext i; rfl))

theorem golayCorr_permCore (T : Equiv.Perm (Fin 24)) :
    GolayCorr T (permCore 24) (G6.coreMod 24) := by
  intro w
  change (Finset.univ.sum w = 0) ↔ Multiplicative.ofAdd (permAct T w) ∈ G6.coreMod 24
  rw [G6.mem_coreMod]
  change (Finset.univ.sum w = 0) ↔
    (Finset.univ.sum fun i => Multiplicative.toAdd (Multiplicative.ofAdd (permAct T w)) i) = 0
  rw [toAdd_ofAdd]
  rw [show (Finset.univ.sum fun i => permAct T w i) = Finset.univ.sum w from
    Equiv.sum_comp T⁻¹ w]

theorem golayCorr_pairKernel {T : Equiv.Perm (Fin 24)} {x y : Fin 24} (h0 : T 0 = x)
    (h1 : T 1 = y) : GolayCorr T (golayPairKernel 0 1) (pairKer x y) := by
  intro w
  change w 0 = w 1 ↔ Multiplicative.ofAdd (permAct T w) ∈ pairKer x y
  have hx : T⁻¹ x = 0 := by
    change T.symm x = 0
    rw [Equiv.symm_apply_eq, h0]
  have hy : T⁻¹ y = 1 := by
    change T.symm y = 1
    rw [Equiv.symm_apply_eq, h1]
  have hker : Multiplicative.ofAdd (permAct T w) ∈ pairKer x y ↔
      permAct T w x + permAct T w y = 0 := by
    rw [pairKer, Multiplicative.mem_toSubgroup, toAdd_ofAdd, AddMonoidHom.mem_ker,
      AddMonoidHom.add_apply, Pi.evalAddMonoidHom_apply, Pi.evalAddMonoidHom_apply]
  rw [hker]
  have hwx : permAct T w x = w 0 := by simp only [permAct, hx]
  have hwy : permAct T w y = w 1 := by simp only [permAct, hy]
  rw [hwx, hwy]
  exact ((by decide : ∀ a b : ZMod 2, a + b = 0 ↔ a = b) (w 0) (w 1)).symm

theorem golayCorr_pairLine {T : Equiv.Perm (Fin 24)} {x y : Fin 24} (h0 : T 0 = x)
    (h1 : T 1 = y) : GolayCorr T (golayPairLine 0 1) (Subgroup.zpowers (pairVec x y)) := by
  have hact : permAct T (fun c : Fin 24 =>
        (if c = 0 then (1 : ZMod 2) else 0) + (if c = 1 then 1 else 0)) =
      (Pi.single x (1 : ZMod 2) + Pi.single y 1) := by
    funext i
    have hx : T⁻¹ i = 0 ↔ i = x := by
      change T.symm i = 0 ↔ i = x
      rw [Equiv.symm_apply_eq, h0]
    have hy : T⁻¹ i = 1 ↔ i = y := by
      change T.symm i = 1 ↔ i = y
      rw [Equiv.symm_apply_eq, h1]
    simp only [permAct, Pi.add_apply, Pi.single_apply, hx, hy]
  have hp := golayCorr_span_singleton T
    (fun c : Fin 24 => (if c = 0 then (1 : ZMod 2) else 0) + (if c = 1 then 1 else 0))
    (Pi.single x (1 : ZMod 2) + Pi.single y 1) hact
  simpa only [golayPairLine, pairVec, unitVec, ← ofAdd_add] using hp

theorem mem_AutPerm_iff_conj_preserves_source {T : Equiv.Perm (Fin 24)}
    (hsrc : ∀ w : GolayAmbient, w ∈ CFSG.Blueprint.EvenSource.sourceGolayCode ↔
      permAct T w ∈ CFSG.Monster.Code.C) (g : Equiv.Perm (Fin 24)) :
    g ∈ CFSG.Monster.Code.AutPerm ↔
      ∀ w : GolayAmbient, w ∈ CFSG.Blueprint.EvenSource.sourceGolayCode ↔
        permAct (T⁻¹ * g * T) w ∈ CFSG.Blueprint.EvenSource.sourceGolayCode := by
  have haut : (g ∈ CFSG.Monster.Code.AutPerm) ↔
      (∀ x : GolayAmbient, x ∈ CFSG.Monster.Code.C ↔
        permAct g x ∈ CFSG.Monster.Code.C) := by
    rw [CFSG.Monster.Code.mem_AutPerm_iff_permWord]
    exact Iff.rfl
  have key : ∀ w : GolayAmbient,
      permAct (T⁻¹ * g * T) w ∈ CFSG.Blueprint.EvenSource.sourceGolayCode ↔
        permAct g (permAct T w) ∈ CFSG.Monster.Code.C := by
    intro w
    rw [hsrc (permAct (T⁻¹ * g * T) w), ← golay_permAct_mul,
      show T * (T⁻¹ * g * T) = g * T by group, golay_permAct_mul]
  rw [haut]
  constructor
  · intro hg w
    rw [hsrc w, hg (permAct T w)]
    exact (key w).symm
  · intro h u
    have hw := h (permAct T⁻¹ u)
    rw [hsrc (permAct T⁻¹ u), key (permAct T⁻¹ u), golay_permAct_inv_cancel] at hw
    exact hw

theorem source_iff_permAct_mul_mem_C {T τ : Equiv.Perm (Fin 24)}
    (hsrc : ∀ w : GolayAmbient, w ∈ CFSG.Blueprint.EvenSource.sourceGolayCode ↔
      permAct T w ∈ CFSG.Monster.Code.C) (hτ : τ ∈ CFSG.Monster.Code.AutPerm) :
    ∀ w : GolayAmbient, w ∈ CFSG.Blueprint.EvenSource.sourceGolayCode ↔
      permAct (τ * T) w ∈ CFSG.Monster.Code.C := by
  intro w
  rw [hsrc w, golay_permAct_mul]
  exact (CFSG.Monster.Code.mem_AutPerm_iff_permWord.mp hτ (permAct T w))

end CFSG.Quasithin.G11
