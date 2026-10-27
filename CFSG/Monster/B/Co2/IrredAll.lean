
module

public import CFSG.Monster.B.Co2.IrredAllBase

public import CFSG.Monster.B.Co2.IrredMain

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Co2

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.SpinLattice CFSG.Monster.ScalarKernel
  CFSG.Monster.Visible CFSG.Monster.VisCert CFSG.Monster.VisQuot CFSG.Certificates
  CFSG.Monster.B.Short

theorem conj_mem_Kstab' {g : OLq} {x : L2} {k : OLq} (hk : k ∈ Kstab x) :
    g⁻¹ * k * g ∈ Kstab (kOp g x) := by
  rw [Kstab_kOp]
  exact ⟨k, hk, by simp⟩

theorem conj_mem_Kstab {g : OLq} {x : L2} {k : OLq} (hk : k ∈ Kstab (kOp g x)) :
    g * k * g⁻¹ ∈ Kstab x := by
  rw [Kstab_kOp] at hk
  obtain ⟨h, hh, rfl⟩ := hk
  have : g * ((MulAut.conj g⁻¹).toMonoidHom h) * g⁻¹ = h := by
    simp [mul_assoc]
  rw [this]
  exact hh

theorem trW_wAct {g : OLq} {x : L2} (k : Kstab (kOp g x)) (w : Wv x) :
    trW g x (wAct x ⟨g * k * g⁻¹, conj_mem_Kstab k.2⟩ w) = wAct (kOp g x) k (trW g x w) := by
  induction w using Submodule.Quotient.induction_on with
  | H z =>
    rw [wAct_mk, trW_mk, trW_mk, wAct_mk]
    congr 1
    apply Subtype.ext
    change kOp g (kOp (g * k * g⁻¹) z) = kOp k (kOp g z)
    rw [← kOp_apply_mul, ← kOp_apply_mul]
    congr 1
    group

theorem trW_surjective (g : OLq) (x : L2) : Function.Surjective (trW g x) := by
  intro w
  induction w using Submodule.Quotient.induction_on with
  | H z' =>
    have hz : kOp g⁻¹ (z' : L2) ∈ vPerpL x := by
      change bL x (kOp g⁻¹ z') = 0
      rw [← bL_kOp g, kOp_apply_inv']
      exact z'.2
    refine ⟨Submodule.Quotient.mk ⟨_, hz⟩, ?_⟩
    rw [trW_mk]
    congr 1
    exact Subtype.ext (kOp_apply_inv' g z')
where
  kOp_apply_inv' (g : OLq) (y : L2) : kOp g (kOp g⁻¹ y) = y := by
    rw [← kOp_apply_mul, inv_mul_cancel, kOp_one, Module.End.one_apply]

theorem irreducible_of_conj (g : OLq) (x : L2)
    (hx : ∀ U : Submodule (ZMod 2) (Wv x),
      (∀ (k : Kstab x) (w : Wv x), w ∈ U → wAct x k w ∈ U) → U = ⊥ ∨ U = ⊤)
    (U : Submodule (ZMod 2) (Wv (kOp g x)))
    (hU : ∀ (k : Kstab (kOp g x)) (w : Wv (kOp g x)), w ∈ U → wAct (kOp g x) k w ∈ U) :
    U = ⊥ ∨ U = ⊤ := by
  have hinv : ∀ (k : Kstab x) (w : Wv x), w ∈ U.comap (trW g x) →
      wAct x k w ∈ U.comap (trW g x) := by
    intro k w hw
    let k' : Kstab (kOp g x) := ⟨g⁻¹ * k * g, conj_mem_Kstab' k.2⟩
    have e : k = ⟨g * k' * g⁻¹, conj_mem_Kstab k'.2⟩ := Subtype.ext (by
      change (k : OLq) = g * (g⁻¹ * k * g) * g⁻¹
      group)
    rw [Submodule.mem_comap, e, trW_wAct]
    exact hU k' _ hw
  rcases hx _ hinv with h | h
  · left
    rw [eq_bot_iff]
    intro u hu
    obtain ⟨w, rfl⟩ := trW_surjective g x u
    have : w ∈ U.comap (trW g x) := hu
    rw [h, Submodule.mem_bot] at this
    rw [this, map_zero]
    exact zero_mem _
  · right
    rw [eq_top_iff]
    intro u _
    obtain ⟨w, rfl⟩ := trW_surjective g x u
    have : w ∈ U.comap (trW g x) := by rw [h]; trivial
    exact this

theorem kOp_injective (g : OLq) : Function.Injective (kOp g) := fun a b h => by
  rw [← kOp_inv_apply g a, h, kOp_inv_apply]

theorem trW_injective (g : OLq) (x : L2) : Function.Injective (trW g x) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro w hw
  induction w using Submodule.Quotient.induction_on with
  | H z =>
    rw [LinearMap.mem_ker, trW_mk, Submodule.Quotient.mk_eq_zero] at hw
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
    change (z : L2) ∈ vLineL x
    have hw' : kOp g z ∈ vLineL (kOp g x) := hw
    rw [mem_vLineL] at hw' ⊢
    rcases hw' with h | h
    · left
      exact kOp_injective g (h.trans (map_zero _).symm)
    · right
      exact kOp_injective g h

theorem native_short_stabilizer_irreducible
    {u : Fin 24 → ℤ} (hu : u ∈ minVecs) :
    Function.Injective (KvAct (classOf u)) ∧ Module.finrank (ZMod 2) (Wv (classOf u)) = 22 ∧
    ∀ U : Submodule (ZMod 2) (Wv (classOf u)),
      (∀ (k : Kstab (classOf u)) (w : Wv (classOf u)), w ∈ U → wAct (classOf u) k w ∈ U) →
        U = ⊥ ∨ U = ⊤ := by
  have hfaith := lattice_short_stabilizer_22_faithful hu
  refine ⟨hfaith.2.2.2.2.2.1, hfaith.2.2.2.1, ?_⟩
  obtain ⟨p, hp⟩ := exists_Pvis_of_short (x := v0) (y := classOf u)
    ⟨_, vMinus_zero_one_mem, rfl⟩ ⟨u, hu, rfl⟩
  have key : ∀ y : L2, (∃ g : OLq, kOp g v0 = y) → ∀ U : Submodule (ZMod 2) (Wv y),
      (∀ (k : Kstab y) (w : Wv y), w ∈ U → wAct y k w ∈ U) → U = ⊥ ∨ U = ⊤ := by
    rintro y ⟨g, rfl⟩ U hU
    exact irreducible_of_conj g v0 irreducible_v0 U hU
  exact key _ ⟨QuotientGroup.mk p.1.2, hp⟩

end CFSG.Monster.B.Co2
