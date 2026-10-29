module

public import CFSG.RankThree.PartTwo.Sec21.FF84Defs
public import CFSG.RankThree.PartTwo.Sec21.FF84S3Model

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open Equiv Equiv.Perm Subgroup
open CFSG.RankThree.PartTwo.Sec21.FF84.S3 (P8 A8s)

@[expose] def fin6e : Fin 6 ≃ {x : Fin 8 // x.val < 6} where
  toFun i := ⟨⟨i.val, by have := i.isLt; omega⟩, i.isLt⟩
  invFun x := ⟨x.1.val, x.2⟩
  left_inv i := Fin.ext rfl
  right_inv x := Subtype.ext (Fin.ext rfl)

@[expose] def ext6 : Perm (Fin 6) →* Perm (Fin 8) := Equiv.Perm.extendDomainHom fin6e

@[expose] def tau6 (σ : Perm (Fin 6)) : P8 :=
  if Equiv.Perm.sign σ = 1 then 1 else Equiv.swap 6 7

@[expose] def psi6 (σ : Perm (Fin 6)) : P8 := ext6 σ * tau6 σ

theorem ext6_fix_of_ge (σ : Perm (Fin 6)) (x : Fin 8) (hx : ¬ x.val < 6) : ext6 σ x = x :=
  Equiv.Perm.extendDomain_apply_not_subtype σ fin6e (by simpa using hx)

theorem ext6_lt_iff (σ : Perm (Fin 6)) (x : Fin 8) : (ext6 σ x).val < 6 ↔ x.val < 6 := by
  by_cases hx : x.val < 6
  · have h := Equiv.Perm.extendDomain_apply_subtype σ fin6e hx
    have h2 : (ext6 σ x).val < 6 := by
      show (Equiv.Perm.extendDomain σ fin6e x).val < 6
      rw [h]
      exact (fin6e _).2
    exact iff_of_true h2 hx
  · have h1 : ext6 σ x = x := ext6_fix_of_ge σ x hx
    rw [h1]

theorem fin_ne6 {x : Fin 8} (hx : x.val < 6) : x ≠ 6 := by
  intro h
  subst h
  exact absurd hx (by decide)

theorem fin_ne7 {x : Fin 8} (hx : x.val < 6) : x ≠ 7 := by
  intro h
  subst h
  exact absurd hx (by decide)

theorem ext6_fix6 (σ : Perm (Fin 6)) : ext6 σ 6 = 6 := ext6_fix_of_ge σ 6 (by decide)

theorem ext6_fix7 (σ : Perm (Fin 6)) : ext6 σ 7 = 7 := ext6_fix_of_ge σ 7 (by decide)

theorem ext6_comm_swap (σ : Perm (Fin 6)) :
    ext6 σ * Equiv.swap 6 7 = Equiv.swap 6 7 * ext6 σ := by
  refine Equiv.ext fun x => ?_
  simp only [Perm.mul_apply]
  by_cases hx : x.val < 6
  · have hsx : Equiv.swap (6 : Fin 8) 7 x = x :=
      Equiv.swap_apply_of_ne_of_ne (fin_ne6 hx) (fin_ne7 hx)
    have hy : (ext6 σ x).val < 6 := (ext6_lt_iff σ x).2 hx
    rw [hsx, Equiv.swap_apply_of_ne_of_ne (fin_ne6 hy) (fin_ne7 hy)]
  · have hx' : x = 6 ∨ x = 7 := by
      have : x.val = 6 ∨ x.val = 7 := by have := x.isLt; omega
      rcases this with h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Fin.ext h)
    rcases hx' with rfl | rfl
    · simp [ext6_fix6, ext6_fix7]
    · simp [ext6_fix6, ext6_fix7]

theorem tau6_mul (σ ρ : Perm (Fin 6)) : tau6 (σ * ρ) = tau6 σ * tau6 ρ := by
  unfold tau6
  rw [map_mul]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1 <;>
    rcases Int.units_eq_one_or (Equiv.Perm.sign ρ) with h2 | h2 <;> simp [h1, h2]

theorem tau6_comm (σ ρ : Perm (Fin 6)) : tau6 σ * ext6 ρ = ext6 ρ * tau6 σ := by
  unfold tau6
  split_ifs
  · simp
  · exact (ext6_comm_swap ρ).symm

theorem psi6_mul (σ ρ : Perm (Fin 6)) : psi6 (σ * ρ) = psi6 σ * psi6 ρ := by
  unfold psi6
  rw [map_mul, tau6_mul]
  have h := tau6_comm σ ρ
  calc ext6 σ * ext6 ρ * (tau6 σ * tau6 ρ) = ext6 σ * (ext6 ρ * tau6 σ) * tau6 ρ := by group
    _ = ext6 σ * (tau6 σ * ext6 ρ) * tau6 ρ := by rw [h]
    _ = ext6 σ * tau6 σ * (ext6 ρ * tau6 ρ) := by group

theorem psi6_one : psi6 1 = 1 := by
  unfold psi6 tau6
  simp

@[expose] def psiHom : Perm (Fin 6) →* P8 where
  toFun := psi6
  map_one' := psi6_one
  map_mul' := psi6_mul

theorem psi6_comm_swap (σ : Perm (Fin 6)) : psi6 σ * Equiv.swap 6 7 = Equiv.swap 6 7 * psi6 σ := by
  unfold psi6 tau6
  split_ifs
  · simp [ext6_comm_swap σ]
  · calc ext6 σ * Equiv.swap 6 7 * Equiv.swap 6 7 = ext6 σ := by
          rw [mul_assoc, Equiv.swap_mul_self, mul_one]
      _ = Equiv.swap 6 7 * (ext6 σ * Equiv.swap 6 7) := by
          rw [← mul_assoc, ← ext6_comm_swap σ, mul_assoc, Equiv.swap_mul_self, mul_one]

theorem psi6_sign (σ : Perm (Fin 6)) : Equiv.Perm.sign (psi6 σ) = 1 := by
  have hext : Equiv.Perm.sign (ext6 σ) = Equiv.Perm.sign σ := by
    show Equiv.Perm.sign (Equiv.Perm.extendDomain σ fin6e) = _
    exact Equiv.Perm.sign_extendDomain σ fin6e
  unfold psi6 tau6
  rw [map_mul, hext]
  have hs : Equiv.Perm.sign (Equiv.swap (6 : Fin 8) 7) = -1 :=
    Equiv.Perm.sign_swap (by decide)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1
  · simp [h1]
  · simp [h1, hs]

theorem psi6_mem (σ : Perm (Fin 6)) : psi6 σ ∈ Cen (Equiv.swap 6 7) ⊓ A8s := by
  refine ⟨?_, ?_⟩
  · exact mem_centralizer_singleton_iff.2 (psi6_comm_swap σ)
  · show psi6 σ ∈ alternatingGroup (Fin 8)
    exact Equiv.Perm.mem_alternatingGroup.2 (psi6_sign σ)

theorem ext6_injective : Function.Injective (ext6) :=
  Equiv.Perm.extendDomainHom_injective fin6e

theorem ext6_surj {h : P8} (h6 : h 6 = 6) (h7 : h 7 = 7) : ∃ σ : Perm (Fin 6), ext6 σ = h := by
  have hp : ∀ x : Fin 8, x.val < 6 ↔ (h x).val < 6 := by
    intro x
    by_cases hx : x.val < 6
    · have n6 : h x ≠ 6 := fun e => fin_ne6 hx (h.injective (e.trans h6.symm))
      have n7 : h x ≠ 7 := fun e => fin_ne7 hx (h.injective (e.trans h7.symm))
      have m6 : (h x).val ≠ 6 := fun e => n6 (Fin.ext e)
      have m7 : (h x).val ≠ 7 := fun e => n7 (Fin.ext e)
      have := (h x).isLt
      exact iff_of_true hx (by omega)
    · have hx' : x = 6 ∨ x = 7 := by
        have : x.val = 6 ∨ x.val = 7 := by have := x.isLt; omega
        rcases this with e | e
        · exact Or.inl (Fin.ext e)
        · exact Or.inr (Fin.ext e)
      have hxh : h x = x := by
        rcases hx' with rfl | rfl
        · exact h6
        · exact h7
      rw [hxh]
  let sp : Perm {x : Fin 8 // x.val < 6} := h.subtypePerm (fun x => (hp x).symm)
  refine ⟨fin6e.symm.permCongr sp, ?_⟩
  refine Equiv.ext fun x => ?_
  by_cases hx : x.val < 6
  · have e1 : ext6 (fin6e.symm.permCongr sp) x = fin6e ((fin6e.symm.permCongr sp) (fin6e.symm ⟨x, hx⟩)) :=
      Equiv.Perm.extendDomain_apply_subtype _ fin6e hx
    have e2 : (fin6e.symm.permCongr sp) (fin6e.symm ⟨x, hx⟩) = fin6e.symm (sp ⟨x, hx⟩) := by
      simp [Equiv.permCongr_apply]
    rw [e1, e2, Equiv.apply_symm_apply]
    try rfl
  · have hx' : x = 6 ∨ x = 7 := by
      have : x.val = 6 ∨ x.val = 7 := by have := x.isLt; omega
      rcases this with e | e
      · exact Or.inl (Fin.ext e)
      · exact Or.inr (Fin.ext e)
    rw [ext6_fix_of_ge _ x hx]
    rcases hx' with rfl | rfl
    · exact h6.symm
    · exact h7.symm

theorem ext6_sign (σ : Perm (Fin 6)) : Equiv.Perm.sign (ext6 σ) = Equiv.Perm.sign σ :=
  Equiv.Perm.sign_extendDomain σ fin6e

theorem psi6_surj (g : P8) (hg : g ∈ Cen (Equiv.swap 6 7) ⊓ A8s) : ∃ σ, psi6 σ = g := by
  obtain ⟨hc, hA⟩ := hg
  have hc' : g * Equiv.swap 6 7 = Equiv.swap 6 7 * g := mem_centralizer_singleton_iff.1 hc
  have hsign : Equiv.Perm.sign g = 1 := Equiv.Perm.mem_alternatingGroup.1 hA
  have h7 : g 7 = Equiv.swap 6 7 (g 6) := by
    have := congrArg (fun π : P8 => π 6) hc'
    simpa [Perm.mul_apply] using this
  have hcases : g 6 = 6 ∨ g 6 = 7 := by
    by_contra hne
    push Not at hne
    have h1 : Equiv.swap (6 : Fin 8) 7 (g 6) = g 6 := Equiv.swap_apply_of_ne_of_ne hne.1 hne.2
    have h2 : g 7 = g 6 := h7.trans h1
    have h3 := g.injective h2
    exact absurd h3 (by decide)
  rcases hcases with e6 | e6
  · have e7 : g 7 = 7 := by rw [h7, e6]; simp
    obtain ⟨σ, hσ⟩ := ext6_surj e6 e7
    refine ⟨σ, ?_⟩
    have hs : Equiv.Perm.sign σ = 1 := by rw [← ext6_sign σ, hσ, hsign]
    unfold psi6 tau6
    rw [if_pos hs, mul_one, hσ]
  · have e7 : g 7 = 6 := by rw [h7, e6]; simp
    obtain ⟨σ, hσ⟩ := ext6_surj (h := g * Equiv.swap 6 7)
      (by simp [Perm.mul_apply, e7]) (by simp [Perm.mul_apply, e6])
    refine ⟨σ, ?_⟩
    have hs : Equiv.Perm.sign σ = -1 := by
      rw [← ext6_sign σ, hσ, map_mul, hsign, Equiv.Perm.sign_swap (by decide : (6 : Fin 8) ≠ 7),
        one_mul]
    unfold psi6 tau6
    rw [if_neg (by simp [hs]), hσ, mul_assoc, Equiv.swap_mul_self, mul_one]

theorem psi6_inj_one (σ : Perm (Fin 6)) (h : psi6 σ = 1) : σ = 1 := by
  by_cases hs : Equiv.Perm.sign σ = 1
  · have h' : ext6 σ = 1 := by
      unfold psi6 tau6 at h
      rw [if_pos hs, mul_one] at h
      exact h
    exact ext6_injective (h'.trans (map_one ext6).symm)
  · exfalso
    unfold psi6 tau6 at h
    rw [if_neg hs] at h
    have h6 := congrArg (fun π : P8 => π 6) h
    simp [Perm.mul_apply, ext6_fix7] at h6

theorem A_cent_P_inv_S6 : Nonempty (↥(Cen (Equiv.swap 6 7) ⊓ A8s) ≃* Equiv.Perm (Fin 6)) := by
  let φ : Perm (Fin 6) →* ↥(Cen (Equiv.swap 6 7) ⊓ A8s) :=
    MonoidHom.codRestrict psiHom _ psi6_mem
  have hbij : Function.Bijective φ := by
    refine ⟨?_, fun y => ?_⟩
    · rw [injective_iff_map_eq_one]
      intro σ hσ
      exact psi6_inj_one σ (congrArg Subtype.val hσ)
    · obtain ⟨σ, hσ⟩ := psi6_surj y.1 y.2
      exact ⟨σ, Subtype.ext hσ⟩
  exact ⟨(MulEquiv.ofBijective φ hbij).symm⟩

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
