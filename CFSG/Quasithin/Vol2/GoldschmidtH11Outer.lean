module

public import CFSG.Quasithin.Vol2.GoldschmidtH11Conj
public import CFSG.Quasithin.Vol2.GoldschmidtH11OutCard

public section

open scoped Matrix MatrixGroups

namespace CFSG.Quasithin.H11

variable {F : Type} [Field F] [Finite F] [CharP F 2] {a : ℕ} {h : Nat.card F = 2 ^ (2 * a)}

theorem isElemAbelian2_mono {V : Type*} [CommGroup V] {A B : Subgroup (MulAut V)} (hBA : B ≤ A)
    (hel : IsElemAbelian2 A) : IsElemAbelian2 B :=
  ⟨fun x hx y hy => hel.1 x (hBA hx) y (hBA hy), fun x hx => hel.2 x (hBA hx)⟩

theorem fixV_le_tau {A : Subgroup (MulAut (HV F a))} (hτ : tauAut a h ∈ A) :
    fixV A ≤ fixV (Subgroup.zpowers (tauAut a h)) :=
  fun _ hv x hx => hv x (Subgroup.zpowers_le.mpr hτ hx)

theorem concl_of_tau_bot (ha : 1 < a) (h : Nat.card F = 2 ^ (2 * a))
    {M A : Subgroup (MulAut (HV F a))}
    (hMN : M ≤ Subgroup.normalizer (Lh a h : Set (MulAut (HV F a)))) (hAM : A ≤ M)
    (hel : IsElemAbelian2 A) (hτ : tauAut a h ∈ A) (hbot : A ⊓ Lh a h = ⊥) :
    H11Concl a (Lh a h) A := by
  have ha0 : 0 < a := by omega
  have h1 := rk_le_rk_inf_add_one ha0 hMN hAM hel hτ
  have h0 : rk ↥(A ⊓ Lh a h) = 0 := by rw [hbot]; exact rk_bot
  have hs := rkIdx_anti (fixV_le_tau hτ)
  rw [rkIdx_fixV_tau ha0 h] at hs
  refine ⟨by omega, ?_, fun hAL => absurd (hAL hτ) (tauAut_not_mem_Lh ha0)⟩
  by_cases h3 : 3 ≤ a
  · exact Or.inl (by omega)
  · exact Or.inr ⟨by omega, tauAut a h, hτ, rkIdx_fixV_tau ha0 h⟩

theorem concl_of_tau_U (ha : 1 < a) (h : Nat.card F = 2 ^ (2 * a))
    {M A : Subgroup (MulAut (HV F a))}
    (hMN : M ≤ Subgroup.normalizer (Lh a h : Set (MulAut (HV F a)))) (hAM : A ≤ M)
    (hel : IsElemAbelian2 A) (hτ : tauAut a h ∈ A) (hB1 : A ⊓ Lh a h ≠ ⊥)
    (hU : UType a h (A ⊓ Lh a h)) (hK : Tset a h (A ⊓ Lh a h) ⊆ ((Kf a : Subfield F) : Set F)) :
    H11Concl a (Lh a h) A := by
  have ha0 : 0 < a := by omega
  have h1 := rk_le_rk_inf_add_one ha0 hMN hAM hel hτ
  obtain ⟨hr, hs⟩ := outer_rank hU hB1 (isElemAbelian2_mono inf_le_left hel) ha0 hK
  have hle : fixV A ≤ fixV (A ⊓ Lh a h) := fun v hv x hx => hv x hx.1
  have hs' := rkIdx_anti hle
  have hsτ := rkIdx_fixV_tau ha0 h
  refine ⟨by omega, ?_, fun hAL => absurd (hAL hτ) (tauAut_not_mem_Lh ha0)⟩
  by_cases h3 : 3 ≤ a
  · exact Or.inl (by omega)
  · by_cases h4 : rk ↥(A ⊓ Lh a h) ≤ 1
    · exact Or.inl (by omega)
    · exact Or.inr ⟨by omega, tauAut a h, hτ, hsτ⟩

end CFSG.Quasithin.H11
