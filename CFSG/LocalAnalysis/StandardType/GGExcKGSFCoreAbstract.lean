module

public import CFSG.LocalAnalysis.StandardType.GGExcKGSFCoreAux

public section

namespace CFSG.StandardType.GGSFCore

open CFSG.Open

variable {A : Type*} [Group A]

theorem sf_core_abstract [Finite A] {p : ℕ} (hp : p.Prime)
    {Inn N : Subgroup A} [Inn.Normal] (hN : Inn ≤ N) (P : Sylow p N) (D : A → Prop)
    (hInn : ∀ x ∈ Inn, D x) {B : Subgroup A} (hB : IsElemAbelian p B) (hBD : ∀ b ∈ B, D b)
    {c : ℕ} (hBc : Nat.card B = c) (hBi : Nat.card B ≤ p * Nat.card ↥(B ⊓ Inn))
    (hCIa : ∀ E : Subgroup A, IsElemAbelian p E → (∀ b ∈ E, D b) → Nat.card E ≤ c)
    (hCId : Nat.card ↥(B ⊓ Inn) < Nat.card B →
      ∀ E E' : Subgroup A, IsElemAbelian p E → IsElemAbelian p E' → (∀ b ∈ E, D b) →
        (∀ b ∈ E', D b) → Nat.card E = c → Nat.card E' = c →
        ∃ κ : A, D κ ∧ E.map (MulAut.conj κ).toMonoidHom = E')
    {E : Subgroup A} (hE : IsElemAbelian p E) (h4 : p ^ 4 ≤ Nat.card E)
    (hEP : E ≤ (P : Subgroup N).map N.subtype) (hED : ∀ b ∈ E, D b)
    (huniq : ∀ E' : Subgroup A, E' ≤ (P : Subgroup N).map N.subtype → IsElemAbelian p E' →
      Nat.card E' = Nat.card E → E' = E) :
    ∃ κ : A, D κ ∧ (E.map (MulAut.conj κ).toMonoidHom = B ∨
      E.map (MulAut.conj κ).toMonoidHom = B ⊓ Inn) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨s, hs⟩ := exists_card_eq_pow hE
  have hE0s : IsElemAbelian p (B ⊓ Inn) := isElemAbelian_of_le hB inf_le_left
  obtain ⟨r, hr⟩ := exists_card_eq_pow hE0s
  obtain ⟨m, hm⟩ := exists_card_eq_pow hB
  obtain ⟨g, hgInn, hg⟩ := exists_conj_le_sylow_of_normal hN P
    (inf_le_right : B ⊓ Inn ≤ Inn) (isElemAbelian_isPGroup hE0s)
  let E0 : Subgroup A := (B ⊓ Inn).map (MulAut.conj g).toMonoidHom
  have hE0 : IsElemAbelian p E0 := isElemAbelian_map_conj hE0s g
  have hE0card : Nat.card E0 = p ^ r := (card_map_conj (B ⊓ Inn) g).trans hr
  have hE0P : E0 ≤ (P : Subgroup N).map N.subtype := hg
  have hspos : 1 ≤ s := by
    have hpow4 : p ^ 4 ≤ p ^ s := by rw [← hs]; exact h4
    have h4s : 4 ≤ s := (Nat.pow_le_pow_iff_right hp.one_lt).mp hpow4
    omega
  rcases lt_trichotomy s r with hlt | heq | hgt
  ·
    obtain ⟨X, Y, hXE0, hYE0, hXcard, hYcard, hXY⟩ :=
      exists_two_subgroups hE0 hE0card hspos hlt
    have hXP : X ≤ (P : Subgroup N).map N.subtype := hXE0.trans hE0P
    have hXA : IsElemAbelian p X := isElemAbelian_of_le hE0 hXE0
    have hXeq : X = E := huniq X hXP hXA (by rw [hXcard, hs])
    have hYP : Y ≤ (P : Subgroup N).map N.subtype := hYE0.trans hE0P
    have hYA : IsElemAbelian p Y := isElemAbelian_of_le hE0 hYE0
    have hYeq : Y = E := huniq Y hYP hYA (by rw [hYcard, hs])
    exact absurd (hXeq.trans hYeq.symm) hXY
  ·
    have hE0eqE : E0 = E := huniq E0 hE0P hE0 (by rw [hE0card, hs, heq])
    refine ⟨g⁻¹, hInn g⁻¹ (Subgroup.inv_mem Inn hgInn), Or.inr ?_⟩
    rw [← hE0eqE]
    show ((B ⊓ Inn).map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj g⁻¹).toMonoidHom = B ⊓ Inn
    rw [Subgroup.map_map]
    have hcomp : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom
        = MonoidHom.id A := by
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MonoidHom.id_apply]
      rw [MulAut.conj_apply, MulAut.conj_apply]
      group
    rw [hcomp, Subgroup.map_id]
  ·
    have hsle : s ≤ m := by
      have hle : p ^ s ≤ p ^ m := by
        calc p ^ s = Nat.card E := hs.symm
          _ ≤ c := hCIa E hE hED
          _ = Nat.card B := hBc.symm
          _ = p ^ m := hm
      exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hle
    have hmle : m ≤ r + 1 := by
      have hle : p ^ m ≤ p ^ (r + 1) := by
        calc p ^ m = Nat.card B := hm.symm
          _ ≤ p * Nat.card ↥(B ⊓ Inn) := hBi
          _ = p * p ^ r := by rw [hr]
          _ = p ^ (r + 1) := by rw [pow_succ']
      exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hle
    have hrs : r + 1 ≤ s := Nat.succ_le_of_lt hgt
    have hsm : s = m := le_antisymm hsle (hmle.trans hrs)
    have hEcard : Nat.card E = c := by
      calc Nat.card E = p ^ s := hs
        _ = p ^ m := by rw [hsm]
        _ = Nat.card B := hm.symm
        _ = c := hBc
    have hBlt : Nat.card ↥(B ⊓ Inn) < Nat.card B := by
      rw [hr, hm]
      exact Nat.pow_lt_pow_right hp.one_lt (by omega)
    obtain ⟨κ, hDκ, hmap⟩ := hCId hBlt E B hE hB hED hBD hEcard hBc
    exact ⟨κ, hDκ, Or.inl hmap⟩

end CFSG.StandardType.GGSFCore
