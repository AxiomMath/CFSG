module

public import CFSG.Quasithin.Vol2.Ch3Sec3A6Transport
public import CFSG.Quasithin.H13.A6S13826bK

public section

namespace CFSG.Quasithin.H13.A6

open Equiv Equiv.Perm CFSG.Quasithin.H13.A6Coc

namespace A6Hm

@[expose] def dP : Perm (Fin 6) := swap 0 1 * swap 1 2 * (swap 3 4 * swap 4 5)

theorem dP_mem : dP ∈ alternatingGroup (Fin 6) := by
  rw [Perm.mem_alternatingGroup]
  decide

@[expose] def dL : Γ := ⟨dP, dP_mem⟩

theorem three_cases_perm : ∀ x : Perm (Fin 6), sign x = 1 → x ^ 3 = 1 → x ≠ 1 →
    (∃ g : Perm (Fin 6), sign g = 1 ∧ g * aP * g⁻¹ = x) ∨
      (∃ g : Perm (Fin 6), sign g = 1 ∧ g * dP * g⁻¹ = x) :=
  A6S13826bK.three_cases_K aP dP (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem not_conj_aP_dP : ∀ g : Perm (Fin 6), g * aP * g⁻¹ ≠ dP :=
  A6S13826bK.not_conj_K aP dP (by decide +kernel) (by decide +kernel)

theorem conj_inv_perm : ∀ x : Perm (Fin 6), sign x = 1 → x ^ 3 = 1 →
    ∃ g : Perm (Fin 6), sign g = 1 ∧ g * x * g⁻¹ = x⁻¹ :=
  A6S13826bK.conj_inv_K (by decide +kernel)

theorem fixCount_conj_aP : ∀ g : Perm (Fin 6), fixCount (g * aP * g⁻¹) = 4 := by
  intro g
  rw [A6S13826bK.fixCount_conj]
  decide +kernel

theorem mem_alt_iff (x : Perm (Fin 6)) : x ∈ alternatingGroup (Fin 6) ↔ sign x = 1 :=
  Perm.mem_alternatingGroup

theorem three_cases {x : Γ} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    (∃ g : Γ, g * aL * g⁻¹ = x) ∨ ∃ g : Γ, g * dL * g⁻¹ = x := by
  have h3 : (x : Perm (Fin 6)) ^ 3 = 1 := by
    have := congrArg Subtype.val hx3
    simpa using this
  have h1 : (x : Perm (Fin 6)) ≠ 1 := fun h => hx1 (Subtype.ext h)
  rcases three_cases_perm x ((mem_alt_iff _).1 x.2) h3 h1 with ⟨g, hg, hgx⟩ | ⟨g, hg, hgx⟩
  · exact Or.inl ⟨⟨g, (mem_alt_iff _).2 hg⟩, Subtype.ext (by
      show g * aP * g⁻¹ = (x : Perm (Fin 6))
      exact hgx)⟩
  · exact Or.inr ⟨⟨g, (mem_alt_iff _).2 hg⟩, Subtype.ext (by
      show g * dP * g⁻¹ = (x : Perm (Fin 6))
      exact hgx)⟩

theorem conj_inv {x : Γ} (hx3 : x ^ 3 = 1) : ∃ g : Γ, g * x * g⁻¹ = x⁻¹ := by
  have h3 : (x : Perm (Fin 6)) ^ 3 = 1 := by
    have := congrArg Subtype.val hx3
    simpa using this
  obtain ⟨g, hg, hgx⟩ := conj_inv_perm x ((mem_alt_iff _).1 x.2) h3
  exact ⟨⟨g, (mem_alt_iff _).2 hg⟩, Subtype.ext (by simpa using hgx)⟩

theorem conj_aL_of_conj {ψ : Γ →* Γ} (hψ : Function.Injective ψ) {x : Γ} (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) (hψx : ∃ g : Γ, ψ x = g * x * g⁻¹) : ∃ g : Γ, ψ aL = g * aL * g⁻¹ := by
  have hψs : Function.Surjective ψ := Finite.injective_iff_surjective.mp hψ
  obtain ⟨g, hg⟩ := hψx
  have ha3 : (ψ aL) ^ 3 = 1 := by
    rw [← map_pow]
    have : aL ^ 3 = 1 := Subtype.ext (by decide)
    rw [this, map_one]
  have ha1 : ψ aL ≠ 1 := by
    intro h
    have : aL = 1 := hψ (by rw [h, map_one])
    exact absurd (congrArg Subtype.val this) (by decide)
  rcases three_cases hx3 hx1 with ⟨h, hh⟩ | ⟨h, hh⟩
  ·
    refine ⟨(ψ h)⁻¹ * g * h, ?_⟩
    have e1 : aL = h⁻¹ * x * h := by rw [← hh]; group
    rw [e1, map_mul, map_mul, map_inv, hg]
    group
  · rcases three_cases ha3 ha1 with ⟨k, hk⟩ | ⟨k, hk⟩
    · exact ⟨k, hk.symm⟩
    · exfalso
      obtain ⟨y, hy⟩ := hψs (k * h⁻¹ * g⁻¹)
      have e1 : ψ aL = ψ (y * x * y⁻¹) := by
        rw [map_mul, map_mul, map_inv, hy, hg, ← hk, ← hh]
        group
      have e2 : aL = y * x * y⁻¹ := hψ e1
      rw [← hh] at e2
      apply not_conj_aP_dP ((y * h : Γ) : Perm (Fin 6))⁻¹
      have e3 := congrArg Subtype.val e2
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at e3
      have e4 : (aL : Perm (Fin 6)) = aP := rfl
      have e5 : (dL : Perm (Fin 6)) = dP := rfl
      rw [e4, e5] at e3
      rw [e3]
      simp only [Subgroup.coe_mul, inv_inv]
      group

theorem exists_perm_of_conj {ψ : Γ →* Γ}
    (hψ : Function.Injective ψ) {x : Γ} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hψx : ∃ g : Γ, ψ x = g * x * g⁻¹ ∨ ψ x = g * x⁻¹ * g⁻¹) :
    ∃ σ : Perm (Fin 6), ∀ y : Γ, (ψ y : Perm (Fin 6)) = σ * y * σ⁻¹ := by
  have hψx' : ∃ g : Γ, ψ x = g * x * g⁻¹ := by
    obtain ⟨g, hg | hg⟩ := hψx
    · exact ⟨g, hg⟩
    · obtain ⟨k, hk⟩ := conj_inv hx3
      refine ⟨g * k, ?_⟩
      rw [hg, ← hk]
      group
  obtain ⟨g, hg⟩ := conj_aL_of_conj hψ hx3 hx1 hψx'
  obtain ⟨ha3, -, hb5, hab4, hab3⟩ := rels_ab
  have hrel : ∀ (y : Γ) (n : ℕ), (y : Perm (Fin 6)) ^ n = 1 →
      (ψ y : Perm (Fin 6)) ^ n = 1 := by
    intro y n hy
    have hy' : y ^ n = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hy)
    rw [← Subgroup.coe_pow, ← map_pow, hy', map_one]
    rfl
  have hfix : fixCount (ψ aL : Perm (Fin 6)) = 4 := by
    rw [hg]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact fixCount_conj_aP g
  obtain ⟨σ, hσa, hσb⟩ := Certificates.certificate7093 (ψ aL) (ψ bL)
    ⟨hrel aL 3 ha3, hfix, hrel bL 5 hb5,
      by
        have := hrel (aL * bL) 4 hab4
        rwa [map_mul, Subgroup.coe_mul] at this,
      by
        have := hrel (aL ^ 2 * bL ^ 2) 3
          (by rw [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow]; exact hab3)
        rwa [map_mul, map_pow, map_pow, Subgroup.coe_mul, Subgroup.coe_pow,
          Subgroup.coe_pow] at this⟩
  refine ⟨σ, ?_⟩
  have key : (alternatingGroup (Fin 6)).subtype.comp ψ =
      (MulAut.conj σ).toMonoidHom.comp (alternatingGroup (Fin 6)).subtype := by
    refine MonoidHom.eq_of_eqOn_dense closure_ab ?_
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · show (ψ aL : Perm (Fin 6)) = σ * aP * σ⁻¹
      exact hσa.symm
    · show (ψ bL : Perm (Fin 6)) = σ * bP * σ⁻¹
      exact hσb.symm
  intro y
  exact DFunLike.congr_fun key y

end A6Hm

end CFSG.Quasithin.H13.A6
