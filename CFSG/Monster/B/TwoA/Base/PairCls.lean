module

public import CFSG.Monster.VisQuot.Monomial
public import CFSG.Monster.Griess.ShortPairs
public import CFSG.Monster.Griess.TrialityBasis.Labels
public import CFSG.Monster.VisCert.Delta

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts CFSG.Monster.Visible
  CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.SpinLattice

private theorem zmod2_cases : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide

@[expose] def sgnI (t : ZMod 2) : ℤ := 1 - 2 * bitLift t

theorem sgnI_zero : sgnI 0 = 1 := rfl

theorem sgnI_one : sgnI 1 = -1 := rfl

theorem sgnI_add : ∀ s t : ZMod 2, sgnI (s + t) = sgnI s * sgnI t := by decide

theorem sgnI_mul_self : ∀ t : ZMod 2, sgnI t * sgnI t = 1 := by decide

theorem sgnI_injective : Function.Injective sgnI := by decide

theorem sgnI_ne_zero : ∀ t : ZMod 2, sgnI t ≠ 0 := by decide

theorem sgnI_eq_one_or : ∀ t : ZMod 2, sgnI t = 1 ∨ sgnI t = -1 := by decide

@[expose] def pairVec (x y : Fin 24) (b : ZMod 2) : Fin 24 → ℤ :=
  fun m => 4 * (if m = x then 1 else 0) - sgnI b * (4 * if m = y then 1 else 0)

theorem pairVec_apply (x y : Fin 24) (b : ZMod 2) (m : Fin 24) :
    pairVec x y b m = 4 * (if m = x then 1 else 0) - sgnI b * (4 * if m = y then 1 else 0) := rfl

theorem pairVec_zero (x y : Fin 24) : pairVec x y 0 = Griess.vMinus x y := by
  funext m
  simp only [pairVec_apply, sgnI_zero, Griess.vMinus, eℤ, Pi.sub_apply, Pi.smul_apply,
    Pi.single_apply, smul_eq_mul]
  split_ifs <;> ring

theorem pairVec_one (x y : Fin 24) : pairVec x y 1 = Griess.vPlus x y := by
  funext m
  simp only [pairVec_apply, sgnI_one, Griess.vPlus, eℤ, Pi.add_apply, Pi.smul_apply,
    Pi.single_apply, smul_eq_mul]
  split_ifs <;> ring

theorem pairVec_mem {x y : Fin 24} (hxy : x ≠ y) (b : ZMod 2) : pairVec x y b ∈ minVecs := by
  rcases lt_or_gt_of_ne hxy with h | h
  · rcases zmod2_cases b with rfl | rfl
    · rw [pairVec_zero]; exact Griess.vMinus_mem h
    · rw [pairVec_one]; exact Griess.vPlus_mem h
  · rcases zmod2_cases b with rfl | rfl
    · have e : pairVec x y 0 = -Griess.vMinus y x := by
        rw [pairVec_zero, Griess.vMinus, Griess.vMinus, neg_sub]
      rw [e]
      exact neg_mem_minVecs (Griess.vMinus_mem h)
    · have e : pairVec x y 1 = Griess.vPlus y x := by
        rw [pairVec_one, Griess.vPlus, Griess.vPlus, add_comm]
      rw [e]
      exact Griess.vPlus_mem h

@[expose] def pairCls (x y : Fin 24) (b : ZMod 2) : L2 := classOf (pairVec x y b)

theorem pairCls_mem_shortSet {x y : Fin 24} (hxy : x ≠ y) (b : ZMod 2) :
    pairCls x y b ∈ VisCert.shortSet :=
  ⟨_, pairVec_mem hxy b, rfl⟩

theorem classOf_neg {u : Fin 24 → ℤ} (hu : u ∈ codeLattice C) : classOf (-u) = classOf u := by
  have hn : -u ∈ codeLattice C := (codeLatticeSubgroup allOnes_mem_C).neg_mem hu
  have e : -u = u + (2 : ℤ) • (-u) := by
    funext m
    simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    ring
  rw [e, Griess.classOf_add_two_smul hu hn]

theorem classOf_sgnI_smul {u : Fin 24 → ℤ} (hu : u ∈ codeLattice C) (t : ZMod 2) :
    classOf (sgnI t • u) = classOf u := by
  rcases zmod2_cases t with rfl | rfl
  · rw [sgnI_zero, one_smul]
  · rw [sgnI_one, neg_one_smul, classOf_neg hu]

theorem pairCls_comm {x y : Fin 24} (hxy : x ≠ y) (b : ZMod 2) : pairCls y x b = pairCls x y b := by
  have hu := (pairVec_mem hxy b).1
  have e : pairVec y x b = -(sgnI b • pairVec x y b) := by
    funext m
    simp only [pairVec_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    rcases zmod2_cases b with rfl | rfl
    · rw [sgnI_zero]; ring
    · rw [sgnI_one]; ring
  rw [pairCls, e, classOf_neg ((codeLatticeSubgroup allOnes_mem_C).zsmul_mem hu _),
    classOf_sgnI_smul hu]
  rfl

theorem pairVec_eq_smul {x y k l : Fin 24} (hxy : x ≠ y) (hkl : k ≠ l) {b c : ZMod 2} {s : ℤ}
    (hs1 : s = 1 ∨ s = -1) (hs : ∀ m, pairVec k l c m = s * pairVec x y b m) :
    ((x = k ∧ y = l) ∨ (x = l ∧ y = k)) ∧ b = c := by
  have hk := hs k
  have hl := hs l
  simp only [pairVec_apply, ite_true, ite_eq_right hkl, ite_eq_right (Ne.symm hkl)] at hk hl
  have hb := sgnI_eq_one_or b
  have hc := sgnI_eq_one_or c
  by_cases hkx : k = x
  · subst hkx
    by_cases hly : l = y
    · subst hly
      simp only [ite_eq_right hxy, ite_eq_right (Ne.symm hxy), ite_true] at hk hl
      refine ⟨.inl ⟨rfl, rfl⟩, sgnI_injective ?_⟩
      rcases hs1 with rfl | rfl <;> rcases hb with hb | hb <;> rcases hc with hc | hc <;>
        rw [hb, hc] at hl <;> rw [hb, hc] <;> omega
    · exfalso
      rw [ite_eq_right hly, ite_eq_right hkl.symm] at hl
      rcases hc with hc | hc <;> rw [hc] at hl <;> omega
  · by_cases hky : k = y
    · subst hky
      by_cases hlx : l = x
      · subst hlx
        simp only [ite_eq_right hxy, ite_eq_right (Ne.symm hxy), ite_true] at hk hl
        refine ⟨.inr ⟨rfl, rfl⟩, sgnI_injective ?_⟩
        rcases hs1 with rfl | rfl <;> rcases hb with hb | hb <;> rcases hc with hc | hc <;>
          rw [hb] at hk <;> rw [hc] at hl <;> rw [hb, hc] <;> omega
      · exfalso
        rw [ite_eq_right hlx, ite_eq_right hkl.symm] at hl
        rcases hc with hc | hc <;> rw [hc] at hl <;> omega
    · exfalso
      rw [ite_eq_right hkx, ite_eq_right hky] at hk
      omega

theorem pairCls_eq_iff {x y k l : Fin 24} (hxy : x ≠ y) (hkl : k ≠ l) (b c : ZMod 2) :
    pairCls x y b = pairCls k l c ↔ ((x = k ∧ y = l) ∨ (x = l ∧ y = k)) ∧ b = c := by
  constructor
  · intro h
    have h' := (classOf_eq_iff (pairVec_mem hxy b) (pairVec_mem hkl c)).1 h
    rcases h' with h' | h'
    · exact pairVec_eq_smul hxy hkl (.inl rfl) fun m => by rw [h', one_mul]
    · exact pairVec_eq_smul hxy hkl (.inr rfl) fun m => by rw [h', Pi.neg_apply, neg_one_mul]
  · rintro ⟨(⟨rfl, rfl⟩ | ⟨rfl, rfl⟩), rfl⟩
    · rfl
    · exact pairCls_comm hkl b

theorem signVec_apply' (a : Fin 24 → ZMod 2) (u : Fin 24 → ℤ) (i : Fin 24) :
    signVec a u i = sgnI (a i) * u i := by
  rw [signVec_apply, sgnI]
  ring

theorem signVec_pairVec_comp (a : Fin 24 → ZMod 2) (p : Equiv.Perm (Fin 24)) (x y : Fin 24)
    (b : ZMod 2) :
    signVec a (pairVec x y b) ∘ ⇑p⁻¹ = sgnI (a x) • pairVec (p x) (p y) (b + a x + a y) := by
  funext m
  have h1 : ∀ z : Fin 24, (p⁻¹ m = z) ↔ (m = p z) := fun z => by
    constructor
    · rintro rfl; simp
    · rintro rfl; simp
  simp only [Function.comp_apply, signVec_apply', Pi.smul_apply, smul_eq_mul, pairVec_apply,
    h1, sgnI_add]
  have hx2 := sgnI_mul_self (a x)
  by_cases hmx : m = p x
  · have hpx : p⁻¹ m = x := (h1 x).2 hmx
    rw [hpx]
    by_cases hmy : m = p y
    · have hxy : x = y := p.injective (hmx.symm.trans hmy)
      subst hxy
      simp only [ite_eq_left hmx]
      linear_combination (4 * sgnI b * sgnI (a x)) * hx2
    · simp only [ite_eq_left hmx, ite_eq_right hmy]
      ring
  · by_cases hmy : m = p y
    · have hpy : p⁻¹ m = y := (h1 y).2 hmy
      rw [hpy]
      simp only [ite_eq_right hmx, ite_eq_left hmy]
      linear_combination (4 * sgnI b * sgnI (a y)) * hx2
    · simp only [ite_eq_right hmx, ite_eq_right hmy]
      ring

theorem modTwoEnd_gO_mul_PO_pairCls (a : C) (p : AutPerm) {x y : Fin 24} (hxy : x ≠ y)
    (b : ZMod 2) :
    modTwoEnd (gO a * PO p) (pairCls x y b) =
      pairCls ((p : Equiv.Perm (Fin 24)) x) ((p : Equiv.Perm (Fin 24)) y)
        (b + (a : Fin 24 → ZMod 2) x + (a : Fin 24 → ZMod 2) y) := by
  have hu := (pairVec_mem hxy b).1
  have hpxy : (p : Equiv.Perm (Fin 24)) x ≠ (p : Equiv.Perm (Fin 24)) y :=
    (p : Equiv.Perm (Fin 24)).injective.ne hxy
  rw [modTwoEnd_mul, Module.End.mul_apply, pairCls, Griess.classOf_eq_cls hu, modTwoEnd_gO_cls,
    modTwoEnd_PO_cls, pairCls, ← Griess.classOf_eq_cls]
  rw [signVec_pairVec_comp, classOf_sgnI_smul (pairVec_mem hpxy _).1]

theorem twoΩCls_eq_classOf (x : Fin 24) : twoΩCls = classOf ((8 : ℤ) • eℤ x) := by
  obtain ⟨hv, hmk, -⟩ := (coordinate_frame_mod_two_fiber.2.2.2.1 ((8 : ℤ) • Pi.single x 1)).2
    ⟨x, .inl rfl⟩
  rw [twoΩCls_eq_frameClass, ← hmk]
  exact (ScalarKernel.classOf_of_mem hv).symm

theorem twoΩCls_add_pairCls {x y : Fin 24} (hxy : x ≠ y) (b : ZMod 2) :
    twoΩCls + pairCls x y b = pairCls x y (b + 1) := by
  have h8 : (8 : ℤ) • eℤ x ∈ codeLattice C := by
    have := (coordinate_frame_mod_two_fiber.2.2.2.1 ((8 : ℤ) • Pi.single x 1)).2 ⟨x, .inl rfl⟩
    exact this.1
  have hu := (pairVec_mem hxy b).1
  have hu' := (pairVec_mem hxy (b + 1)).1
  rw [twoΩCls_eq_classOf x, pairCls, ← Griess.classOf_add_of_mem h8 hu, pairCls]
  have e : (8 : ℤ) • eℤ x + pairVec x y b = pairVec x y (b + 1) + (2 : ℤ) • pairVec x y b := by
    funext m
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, pairVec_apply, sgnI_add, sgnI_one, eℤ,
      Pi.single_apply]
    split_ifs <;> ring
  rw [e, Griess.classOf_add_two_smul hu' hu]

end CFSG.Monster.B.TwoA
