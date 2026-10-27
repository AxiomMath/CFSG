module

public import CFSG.Monster.VisQuot.Stabilizer

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Schur

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts CFSG.Monster.VisCert CFSG.Monster.VisQuot

private theorem bridgeQ_zero' : bridgeQ 0 = 0 := by decide

private theorem bridgeQ_one' : bridgeQ 1 = 1 := by decide

private theorem bridgeQ_inv_apply' (i : Fin 24) : bridgeQ⁻¹ (bridgeQ i) = i := by
  rw [← Equiv.Perm.mul_apply, inv_mul_cancel, Equiv.Perm.one_apply]

private theorem autPerm_maps_two' (u v : Fin 24) (huv : u ≠ v) :
    ∃ p ∈ AutPerm, p 0 = u ∧ p 1 = v := by
  obtain ⟨g, g0, g1⟩ := CFSG.Sporadic.Mathieu.exists_smul_eq_two
    CFSG.Sporadic.Mathieu.m24_hyp (by decide) (by norm_num) (bridgeQ u) (bridgeQ v)
    (bridgeQ.injective.ne huv)
  refine ⟨bridgeQ⁻¹ * (g : Equiv.Perm (Fin 24)) * bridgeQ,
    (mem_AutPerm_iff_conj _).2 ⟨g, g.2, fun i => by
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]⟩, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, bridgeQ_zero']
    have h : (g : Equiv.Perm (Fin 24)) 0 = bridgeQ u := g0
    rw [h, bridgeQ_inv_apply']
  · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, bridgeQ_one']
    have h : (g : Equiv.Perm (Fin 24)) 1 = bridgeQ v := g1
    rw [h, bridgeQ_inv_apply']


theorem exists_autPerm_apply_eq
    (i j : Fin 24) : ∃ p ∈ AutPerm, p i = j := by
  have hne : ∀ i : Fin 24, i ≠ i + 1 := by decide
  obtain ⟨p₁, hp₁, h₁, -⟩ := autPerm_maps_two' i (i + 1) (hne i)
  obtain ⟨p₂, hp₂, h₂, -⟩ := autPerm_maps_two' j (j + 1) (hne j)
  refine ⟨p₂ * p₁⁻¹, AutPerm.mul_mem hp₂ (AutPerm.inv_mem hp₁), ?_⟩
  have h3 : p₁⁻¹ i = 0 := by
    rw [Equiv.Perm.inv_eq_iff_eq]
    exact h₁.symm
  rw [Equiv.Perm.mul_apply, h3, h₂]

theorem code_fixed_of_autPerm (a : C)
    (h : ∀ p : AutPerm, permC p a = a ∨ permC p a = a + ΩC) : a = 0 ∨ a = ΩC := by
  classical
  have hΩ : ΩC ≠ 0 := fun h0 => by
    have := congrFun (congrArg Subtype.val h0) 0
    simp [ΩC, Ω] at this
  have hΩΩ : ΩC + ΩC = 0 := by
    refine Subtype.ext (funext fun i => ?_)
    show (1 : ZMod 2) + 1 = 0
    decide
  have hadd : ∀ (p : AutPerm) (x : C), permC p (x + ΩC) = permC p x + ΩC := fun p x => by
    rw [map_add, permC_ΩC]
  have hne : a + ΩC ≠ a := fun h0 => hΩ (by simpa using h0)
  have hcancel : a + ΩC + ΩC = a := by rw [add_assoc, hΩΩ, add_zero]
  let ε : AutPerm →* Multiplicative (ZMod 2) :=
    { toFun := fun p => if permC p a = a then 1 else Multiplicative.ofAdd 1
      map_one' := by simp [permC_one]
      map_mul' := fun p q => by
        have hpq : permC (p * q) a = permC p (permC q a) := permC_mul p q a
        rcases h q with hq | hq
        · rw [hpq, hq]
          simp
        · rw [hpq, hq, hadd]
          rcases h p with hp | hp
          · rw [hp]
            simp [hne]
          · rw [hp, hcancel]
            simp [hne]
            decide }
  have hε : ε = 1 := by
    rcases AutPerm_isSimpleGroup.eq_bot_or_eq_top_of_normal ε.ker with h1 | h1
    · exfalso
      have hinj : Function.Injective ε := (MonoidHom.ker_eq_bot_iff ε).1 h1
      have h2 := Nat.card_le_card_of_injective ε hinj
      rw [card_AutPerm] at h2
      have h3 : Nat.card (Multiplicative (ZMod 2)) = 2 := by simp
      omega
    · refine MonoidHom.ext fun p => ?_
      have : p ∈ ε.ker := by rw [h1]; trivial
      exact this
  have hfix : ∀ p : AutPerm, permC p a = a := by
    intro p
    by_contra hp
    have h1 : ε p = 1 := by rw [hε]; rfl
    simp only [ε, MonoidHom.coe_mk, OneHom.coe_mk, hp, ↓reduceIte] at h1
    exact absurd h1 (by decide)
  have hconst : ∀ i j : Fin 24, (a : Fin 24 → ZMod 2) i = (a : Fin 24 → ZMod 2) j := by
    intro i j
    obtain ⟨p, hp, hpi⟩ := exists_autPerm_apply_eq i j
    have h1 := hfix ⟨p, hp⟩
    have h2 : (permC ⟨p, hp⟩ a : Fin 24 → ZMod 2) j = (a : Fin 24 → ZMod 2) i := by
      rw [coe_permC, ← hpi]
      exact permWord_apply p a i
    rw [h1] at h2
    exact h2.symm
  rcases (by decide : ∀ t : ZMod 2, t = 0 ∨ t = 1) ((a : Fin 24 → ZMod 2) 0) with h0 | h0
  · left
    exact Subtype.ext (funext fun i => (hconst i 0).trans h0)
  · right
    exact Subtype.ext (funext fun i => (hconst i 0).trans h0)

theorem Evis_inf_centralizer_Nvis :
    Evis ⊓ Subgroup.centralizer (Nvis : Set GLV) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun e he => ?_
  obtain ⟨heE, hecent⟩ := he
  rw [Evis_eq_Esign, ← range_signQ] at heE
  obtain ⟨x, rfl⟩ := heE
  induction x using multQ_induction with
  | h a =>
    have hperm : ∀ p : AutPerm, permC p a = a ∨ permC p a = a + ΩC := by
      intro p
      have h1 := Subgroup.mem_centralizer_iff.1 hecent (permHom p) (permHom_mem_Nvis p)
      have h2 : permHom p * signQ (Multiplicative.ofAdd (Submodule.Quotient.mk a)) *
          (permHom p)⁻¹ = signQ (Multiplicative.ofAdd (Submodule.Quotient.mk a)) := by
        rw [h1, mul_inv_cancel_right]
      rw [signQ_mk, conj_permHom] at h2
      have h3 : signQ (Multiplicative.ofAdd (Submodule.Quotient.mk (permC p a))) =
          signQ (Multiplicative.ofAdd (Submodule.Quotient.mk a)) := by
        rw [signQ_mk, signQ_mk]
        exact h2
      have h4 := signQ_injective h3
      have h5 : (Submodule.Quotient.mk (permC p a) : C ⧸ ΩLine) = Submodule.Quotient.mk a :=
        Multiplicative.ofAdd.injective h4
      have h6 := (Submodule.Quotient.eq ΩLine).1 h5
      rcases mem_ΩLine_iff.1 h6 with h7 | h7
      · left
        exact sub_eq_zero.1 h7
      · right
        rw [← h7]
        abel
    have h8 : (Submodule.Quotient.mk a : C ⧸ ΩLine) = 0 :=
      mk_eq_zero_of_scalar (code_fixed_of_autPerm a hperm)
    rw [h8]
    exact map_one signQ

end CFSG.Monster.Schur
