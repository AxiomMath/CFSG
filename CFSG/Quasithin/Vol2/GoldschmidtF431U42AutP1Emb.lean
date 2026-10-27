module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP0

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin U42F431
open CFSG.Quasithin.H13.F431.U42 (Y P45 L0S Xs Xs_eq card_Xs B0 P1 P2 card_P1 card_P2 card_B0
  mem_P1_iff mem_P2_iff)
open CFSG.ComponentClassification.CatFactsSmall.PSp43 (QA45 QP45)
open scoped Pointwise

@[expose] def incl : Y →* Ah := Subgroup.inclusion Xs_le_A

theorem incl_injective : Function.Injective incl := Subgroup.inclusion_injective _

theorem coe_incl (g : Y) : ((incl g : Ah) : P45) = (g : P45) := rfl

@[expose] def signA : Ah →* ℤˣ := Equiv.Perm.sign.comp QA45.originalSubgroup.subtype

theorem signA_apply (g : Ah) : signA g = Equiv.Perm.sign (g : P45) := by simp [signA]

theorem signA_incl (g : Y) : signA (incl g) = 1 := by
  rw [signA_apply, coe_incl]
  exact sign_of_mem_Xs (Xs_eq ▸ g.2)

theorem signA_fhatA : signA fhatA = -1 := by
  rw [signA_apply, fhatA_coe]
  exact sign_fhat

theorem mem_Yh_iff_incl (g : Ah) : g ∈ Yh ↔ ∃ y : Y, incl y = g := by
  rw [mem_Yh_iff]
  constructor
  · intro h
    rw [← Xs_eq] at h
    exact ⟨⟨g, h⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    rw [← Xs_eq]
    exact y.2

theorem Yh_eq_range : Yh = incl.range := by
  ext g
  rw [mem_Yh_iff_incl, MonoidHom.mem_range]

theorem card_Yh : Nat.card Yh = 25920 := by
  rw [Yh_eq_range, ← card_Xs]
  exact (Nat.card_congr (MonoidHom.ofInjective incl_injective).toEquiv).symm

theorem index_Yh : Yh.index = 2 := by
  have h := Subgroup.index_mul_card (H := Yh)
  rw [card_Yh, card_A] at h
  generalize Yh.index = n at h ⊢
  omega

theorem signA_eq_one_iff (g : Ah) : signA g = 1 ↔ g ∈ Yh := by
  constructor
  · intro hs
    by_contra hg
    have hf : fhatA⁻¹ ∉ Yh := fun h => fhatA_not_mem_Yh (Yh.inv_mem_iff.1 h)
    have h2 : g * fhatA⁻¹ ∈ Yh := by
      rw [Subgroup.mul_mem_iff_of_index_two index_Yh]
      exact iff_of_false hg hf
    obtain ⟨y, hy⟩ := (mem_Yh_iff_incl _).1 h2
    have h3 := signA_incl y
    rw [hy, map_mul, hs, map_inv, signA_fhatA] at h3
    exact absurd h3 (by decide)
  · intro h
    obtain ⟨y, rfl⟩ := (mem_Yh_iff_incl g).1 h
    exact signA_incl y

theorem signA_eq_neg_one_iff (g : Ah) :
    signA g = -1 ↔ g ∉ Yh := by
  rw [← signA_eq_one_iff]
  rcases Int.units_eq_one_or (signA g) with h | h <;> simp [h]

theorem card_top_units : Nat.card (⊤ : Subgroup ℤˣ) = 2 := by
  rw [Subgroup.card_top, Nat.card_eq_fintype_card]
  decide

theorem card_range_units {H : Type*} [Group H] (φ : H →* ℤˣ) (h : ∃ a, φ a = -1) :
    Nat.card φ.range = 2 := by
  obtain ⟨a, ha⟩ := h
  have : φ.range = ⊤ := by
    refine eq_top_iff.2 fun u _ => ?_
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact φ.range.one_mem
    · exact ⟨a, ha⟩
  rw [this]
  exact card_top_units

theorem card_eq_two_mul {H : Subgroup Ah} (hf : fhatA ∈ H) :
    Nat.card H = 2 * Nat.card (H.comap incl) := by
  obtain ⟨φ, hφ⟩ : ∃ φ : H →* ℤˣ, φ = signA.comp H.subtype := ⟨_, rfl⟩
  have hr : Nat.card φ.range = 2 :=
    card_range_units φ ⟨⟨fhatA, hf⟩, by simpa [hφ] using signA_fhatA⟩
  have hk : Nat.card φ.ker = Nat.card (H.comap incl) := by
    refine (Nat.card_eq_of_bijective (fun y : H.comap incl =>
      (⟨⟨incl y, y.2⟩, by simpa [hφ] using signA_incl y⟩ : φ.ker)) ⟨?_, ?_⟩).symm
    · intro a b hab
      exact Subtype.ext (incl_injective (congrArg (fun z : φ.ker => ((z : H) : Ah)) hab))
    · rintro ⟨⟨h, hH⟩, hk⟩
      have hk' : signA h = 1 := by simpa [hφ] using hk
      obtain ⟨y, rfl⟩ := (mem_Yh_iff_incl h).1 ((signA_eq_one_iff h).1 hk')
      exact ⟨⟨y, hH⟩, rfl⟩
  have h := Subgroup.card_ker_mul_card_range φ
  rw [hr, hk] at h
  exact h.symm.trans (mul_comm _ _)

theorem eq_of_comap_eq {H₁ H₂ : Subgroup Ah} (h1 : fhatA ∈ H₁)
    (h2 : fhatA ∈ H₂) (hc : H₁.comap incl = H₂.comap incl) : H₁ = H₂ := by
  have key : ∀ g : Ah, g ∈ H₁ ↔ g ∈ H₂ := by
    intro g
    by_cases hg : g ∈ Yh
    · obtain ⟨y, rfl⟩ := (mem_Yh_iff_incl g).1 hg
      have := SetLike.ext_iff.1 hc y
      simpa using this
    · have hf : fhatA⁻¹ ∉ Yh := fun h => fhatA_not_mem_Yh (Yh.inv_mem_iff.1 h)
      have h3 : g * fhatA⁻¹ ∈ Yh := by
        rw [Subgroup.mul_mem_iff_of_index_two index_Yh]
        exact iff_of_false hg hf
      obtain ⟨y, hy⟩ := (mem_Yh_iff_incl _).1 h3
      have e1 : g ∈ H₁ ↔ g * fhatA⁻¹ ∈ H₁ :=
        (Subgroup.mul_mem_cancel_right H₁ (H₁.inv_mem h1)).symm
      have e2 : g ∈ H₂ ↔ g * fhatA⁻¹ ∈ H₂ :=
        (Subgroup.mul_mem_cancel_right H₂ (H₂.inv_mem h2)).symm
      rw [e1, e2, ← hy]
      exact SetLike.ext_iff.1 hc y
  exact Subgroup.ext key

theorem comap_P1h : P1h.comap incl = P1 := by
  ext g
  rw [Subgroup.mem_comap, mem_P1h_iff, mem_P1_iff]
  rfl

theorem comap_P2h : P2h.comap incl = P2 := by
  ext g
  rw [Subgroup.mem_comap, mem_P2h_iff, mem_P2_iff]
  rfl

theorem comap_Bh : Bh.comap incl = B0 := by
  rw [Bh, Subgroup.comap_inf, comap_P1h, comap_P2h]
  rfl

theorem fhatA_mem_P1h : fhatA ∈ P1h := fhatA_mem_Bh.1

theorem fhatA_mem_P2h : fhatA ∈ P2h := fhatA_mem_Bh.2

theorem card_P1h :
    Nat.card P1h = 1152 := by
  rw [card_eq_two_mul fhatA_mem_P1h, comap_P1h, card_P1]

theorem card_P2h :
    Nat.card P2h = 1920 := by
  rw [card_eq_two_mul fhatA_mem_P2h, comap_P2h, card_P2]

theorem card_Bh :
    Nat.card Bh = 384 := by
  rw [card_eq_two_mul fhatA_mem_Bh, comap_Bh, card_B0]

end CFSG.Quasithin.H13.F431.U42Aut
