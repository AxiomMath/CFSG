module

public import CFSG.Monster.Griess.Short
public import CFSG.Monster.RootlessLattice

public section

namespace CFSG.Monster.Griess

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice

@[expose] noncomputable def alphaS (c d : ShortIdx) : ℤ := hInt (uvec c) (uvec d)

theorem eight_mul_alphaS (c d : ShortIdx) :
    8 * alphaS c d = ∑ i, uvec c i * uvec d i :=
  eight_mul_hInt allOnes_mem_C weight_mod_four' (uvec_mem c).1 (uvec_mem d).1

theorem alphaS_comm (c d : ShortIdx) : alphaS c d = alphaS d c := hInt_comm _ _

theorem alphaS_self (c : ShortIdx) : alphaS c c = 4 := by
  have h := eight_mul_alphaS c c
  have h32 := (mem_minVecs_iff.1 (uvec_mem c)).2
  rw [show (∑ i, uvec c i * uvec c i) = normSq (uvec c) from rfl, h32] at h
  omega

@[expose] noncomputable def hL :
    codeLatticeSubgroup allOnes_mem_C →+ codeLatticeSubgroup allOnes_mem_C →+ ℤ :=
  AddMonoidHom.mk' (fun u => AddMonoidHom.mk' (fun v => hInt u v) fun v v' => by
      rw [hInt_comm, AddSubgroup.coe_add, hInt_add_left allOnes_mem_C weight_mod_four' v.2 v'.2 u.2,
        hInt_comm v, hInt_comm v'])
    fun u u' => AddMonoidHom.ext fun v => by
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, AddSubgroup.coe_add]
      exact hInt_add_left allOnes_mem_C weight_mod_four' u.2 u'.2 v.2

theorem hL_apply (u v : codeLatticeSubgroup allOnes_mem_C) : hL u v = hInt u v := rfl

theorem hL_symm (u v : codeLatticeSubgroup allOnes_mem_C) : hL u v = hL v u := hInt_comm _ _

theorem hL_min (w : codeLatticeSubgroup allOnes_mem_C) (hw : w ≠ 0) : 4 ≤ hL w w := by
  have h0 : (w : Fin 24 → ℤ) ≠ 0 := fun h => hw (Subtype.ext h)
  have h32 := normSq_ge w.2 h0
  have h8 := eight_mul_hInt allOnes_mem_C weight_mod_four' w.2 w.2
  rw [hL_apply]
  rw [show (∑ i, (w : Fin 24 → ℤ) i * (w : Fin 24 → ℤ) i) = normSq w from rfl] at h8
  omega

@[expose] noncomputable def uL (c : ShortIdx) : codeLatticeSubgroup allOnes_mem_C :=
  ⟨uvec c, (uvec_mem c).1⟩

theorem hL_uL (c d : ShortIdx) : hL (uL c) (uL d) = alphaS c d := rfl

theorem classOf_of_mem' {u : Fin 24 → ℤ} (hu : u ∈ codeLattice C) :
    classOf u = Submodule.Quotient.mk (⟨u, hu⟩ : codeLatticeSubgroup allOnes_mem_C) := by
  rw [classOf, dite_eq_left hu]

theorem classOf_add_of_mem {u v : Fin 24 → ℤ} (hu : u ∈ codeLattice C) (hv : v ∈ codeLattice C) :
    classOf (u + v) = classOf u + classOf v := by
  rw [classOf_of_mem' hu, classOf_of_mem' hv,
    classOf_of_mem' (add_mem_codeLattice allOnes_mem_C hu hv), ← Submodule.Quotient.mk_add]
  rfl

theorem uL_ne_of_ne {c d : ShortIdx} (hcd : c ≠ d) : uL c ≠ uL d ∧ uL c ≠ -uL d := by
  have hinj : ∀ v : Fin 24 → ℤ, v ∈ minVecs → classOf v = phi0 d.1 →
      classOf v = phi0 c.1 → False := fun v _ h1 h2 =>
    hcd (Subtype.ext (phi0Equiv.injective (h2.symm.trans h1)))
  constructor
  · intro h
    have h' : uvec c = uvec d := congrArg Subtype.val h
    exact hinj (uvec c) (uvec_mem c) (h' ▸ classOf_uvec d) (classOf_uvec c)
  · intro h
    have h' : uvec c = -uvec d := congrArg Subtype.val h
    have hcl : classOf (uvec c) = classOf (uvec d) :=
      ((classOf_eq_iff (uvec_mem d) (uvec_mem c)).2 (Or.inr h')).symm
    exact hinj (uvec c) (uvec_mem c) (hcl.trans (classOf_uvec d)) (classOf_uvec c)

theorem alphaS_mem {c d : ShortIdx} (hcd : c ≠ d) :
    alphaS c d = -2 ∨ alphaS c d = -1 ∨ alphaS c d = 0 ∨ alphaS c d = 1 ∨ alphaS c d = 2 :=
  (rootless_short_sums hL hL_symm hL_min (alphaS_self c) (alphaS_self d)
    (uL_ne_of_ne hcd).1 (uL_ne_of_ne hcd).2).1

theorem isShortCoord_iff_exists (p : C × Cocode) :
    IsShortCoord p ↔ ∃ w ∈ minVecs, classOf w = phi0 p := Iff.rfl

theorem two_smul_codeLattice {t : Fin 24 → ℤ} (ht : t ∈ codeLattice C) :
    (2 : ℤ) • t ∈ codeLattice C := (codeLatticeSubgroup allOnes_mem_C).zsmul_mem ht 2

theorem classOf_add_two_smul {w t : Fin 24 → ℤ} (hw : w ∈ codeLattice C)
    (ht : t ∈ codeLattice C) : classOf (w + (2 : ℤ) • t) = classOf w := by
  rw [classOf_add_of_mem hw (two_smul_codeLattice ht), classOf_of_mem' (two_smul_codeLattice ht)]
  rw [show (Submodule.Quotient.mk (⟨(2 : ℤ) • t, two_smul_codeLattice ht⟩ :
      codeLatticeSubgroup allOnes_mem_C) : codeLatticeModTwo C allOnes_mem_C) = 0 from
    (Submodule.Quotient.mk_eq_zero _).2 ((mem_two_range_iff allOnes_mem_C _).2 ⟨⟨t, ht⟩, rfl⟩),
    add_zero]

theorem isShortCoord_add_iff {c d : ShortIdx} (hcd : c ≠ d) :
    IsShortCoord (c.1 + d.1) ↔ alphaS c d = 2 ∨ alphaS c d = -2 := by
  obtain ⟨-, hiff, h2, hm2⟩ := rootless_short_sums hL hL_symm hL_min
    (alphaS_self c) (alphaS_self d) (uL_ne_of_ne hcd).1 (uL_ne_of_ne hcd).2
  have hcl : phi0 (c.1 + d.1) = classOf (uvec c + uvec d) := by
    rw [map_add, ← classOf_uvec, ← classOf_uvec, classOf_add_of_mem (uvec_mem c).1 (uvec_mem d).1]
  rw [← hL_uL, ← hiff]
  constructor
  · rintro ⟨w, hw, hwcl⟩
    rw [hcl, classOf_of_mem' hw.1, classOf_of_mem' (add_mem_codeLattice allOnes_mem_C
      (uvec_mem c).1 (uvec_mem d).1), Submodule.Quotient.eq, mem_two_range_iff] at hwcl
    obtain ⟨t, ht⟩ := hwcl
    refine ⟨⟨w, hw.1⟩, -t, ?_, ?_⟩
    · apply Subtype.ext
      have ht' : (2 : ℤ) • (t : Fin 24 → ℤ) = w - (uvec c + uvec d) := ht
      change uvec c + uvec d = w + (2 : ℕ) • (-(t : Fin 24 → ℤ))
      rw [two_nsmul, ← two_smul ℤ, smul_neg, ht']
      abel
    · rw [hL_apply]
      have h8 := eight_mul_hInt allOnes_mem_C weight_mod_four' hw.1 hw.1
      have h32 := (mem_minVecs_iff.1 hw).2
      rw [show (∑ i, w i * w i) = normSq w from rfl, h32] at h8
      change hInt w w = 4
      omega
  · rintro ⟨w, t, hwt, hww⟩
    refine ⟨w, ?_, ?_⟩
    · refine mem_minVecs_iff.2 ⟨w.2, ?_⟩
      have h8 := eight_mul_hInt allOnes_mem_C weight_mod_four' w.2 w.2
      rw [← hL_apply, hww] at h8
      rw [normSq]
      omega
    · rw [hcl]
      have hwt' : uvec c + uvec d = (w : Fin 24 → ℤ) + (2 : ℤ) • (t : Fin 24 → ℤ) := by
        have := congrArg Subtype.val hwt
        simp only [AddSubgroup.coe_add, two_nsmul, uL] at this
        rw [two_smul]
        exact this
      rw [hwt', classOf_add_two_smul w.2 t.2]

theorem hL_eq_four_of_mem_minVecs {w : codeLatticeSubgroup allOnes_mem_C}
    (hw : (w : Fin 24 → ℤ) ∈ minVecs) : hL w w = 4 := by
  have h8 := eight_mul_hInt allOnes_mem_C weight_mod_four' w.2 w.2
  have h32 := (mem_minVecs_iff.1 hw).2
  rw [show (∑ i, (w : Fin 24 → ℤ) i * (w : Fin 24 → ℤ) i) = normSq w from rfl, h32] at h8
  rw [hL_apply]
  omega

theorem mem_minVecs_of_hL {w : codeLatticeSubgroup allOnes_mem_C} (hw : hL w w = 4) :
    (w : Fin 24 → ℤ) ∈ minVecs := by
  refine mem_minVecs_iff.2 ⟨w.2, ?_⟩
  have h8 := eight_mul_hInt allOnes_mem_C weight_mod_four' w.2 w.2
  rw [← hL_apply, hw] at h8
  rw [normSq]
  omega

theorem alphaS_add_sq {c d : ShortIdx} (hcd : c ≠ d) (h : IsShortCoord (c.1 + d.1)) :
    alphaS c ⟨c.1 + d.1, h⟩ ^ 2 = 4 := by
  obtain ⟨-, -, h2, hm2⟩ := rootless_short_sums hL hL_symm hL_min
    (alphaS_self c) (alphaS_self d) (uL_ne_of_ne hcd).1 (uL_ne_of_ne hcd).2
  have hcl : classOf (uvec ⟨c.1 + d.1, h⟩) = classOf (uvec c + uvec d) := by
    rw [classOf_uvec, map_add, ← classOf_uvec, ← classOf_uvec,
      classOf_add_of_mem (uvec_mem c).1 (uvec_mem d).1]
  have key : ∀ w : codeLatticeSubgroup allOnes_mem_C, hL w w = 4 →
      classOf (w : Fin 24 → ℤ) = classOf (uvec c + uvec d) →
      alphaS c ⟨c.1 + d.1, h⟩ = hL (uL c) w ∨ alphaS c ⟨c.1 + d.1, h⟩ = -hL (uL c) w := by
    intro w hw hwcl
    rcases (classOf_eq_iff (mem_minVecs_of_hL hw) (uvec_mem ⟨c.1 + d.1, h⟩)).1
      (hwcl.trans hcl.symm) with he | he
    · left
      have : uL ⟨c.1 + d.1, h⟩ = w := Subtype.ext he
      rw [← hL_uL, this]
    · right
      have : uL ⟨c.1 + d.1, h⟩ = -w := Subtype.ext he
      rw [← hL_uL, this, map_neg]
  rcases (isShortCoord_add_iff hcd).1 h with hα | hα
  · obtain ⟨hw4, hwt⟩ := h2 hα
    have hwcl : classOf ((uL c - uL d : codeLatticeSubgroup allOnes_mem_C) : Fin 24 → ℤ) =
        classOf (uvec c + uvec d) := by
      have e : uvec c + uvec d = ((uL c - uL d : codeLatticeSubgroup allOnes_mem_C) : Fin 24 → ℤ) +
          (2 : ℤ) • uvec d := by
        simp only [AddSubgroup.coe_sub, uL, two_smul]
        abel
      rw [e, classOf_add_two_smul (uL c - uL d).2 (uvec_mem d).1]
    have hval : hL (uL c) (uL c - uL d) = 2 := by
      rw [map_sub, hL_uL, hL_uL, alphaS_self, hα]
      norm_num
    rcases key _ hw4 hwcl with he | he <;> rw [he, hval] <;> norm_num
  · have hw4 := hm2 hα
    have hwcl : classOf ((uL c + uL d : codeLatticeSubgroup allOnes_mem_C) : Fin 24 → ℤ) =
        classOf (uvec c + uvec d) := rfl
    have hval : hL (uL c) (uL c + uL d) = 2 := by
      rw [map_add, hL_uL, hL_uL, alphaS_self, hα]
      norm_num
    rcases key _ hw4 hwcl with he | he <;> rw [he, hval] <;> norm_num

end CFSG.Monster.Griess
