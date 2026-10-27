module

public import CFSG.Quasithin.Background.GoldschmidtD35CoreOff2
public import CFSG.Quasithin.Background.GoldschmidtD35CoreA6
public import CFSG.Quasithin.Background.GoldschmidtD35CoreFix

public section

namespace CFSG.Quasithin.D35Core

open CFSG.QuasithinUnique.Setup.X3 CFSG.Quasithin Equiv
open scoped Matrix LinearAlgebra.Projectivization

variable {K : Type} [Field K] [Finite K] {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 3) K)}
variable {pt : Fin 6 → ℙ K (Fin 3 → K)}

theorem axis_eq (hval : IsValentiner K Γ) {E : Subgroup Γ} (hE : OffNat Γ E) {t₀ : Γ}
    (ht₀E : t₀ ∈ E) (ht₀1 : t₀ ≠ 1) {t : Γ} (htE : t ∈ E) (ht1 : t ≠ 1) :
    fixNat Γ E = {w | ((t : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
      w = w} := by
  have hE2' : ∀ t ∈ E, t * t = 1 := fun t ht => by rw [← sq]; exact hE.2.2.1 t ht
  obtain ⟨h16, -⟩ := card_offender hval hE ht₀E ht₀1
  have hc16 := card_fix_elt hval (hE2' t htE) ht1
  rw [Nat.card_coe_set_eq] at hc16 h16
  exact Set.eq_of_subset_of_ncard_le (fixNat_subset htE) (by rw [hc16, h16]) (Set.toFinite _)

theorem exists_fixTwo_of_offender (hval : IsValentiner K Γ) (hO : IsSixOrbit (valL Γ) pt)
    {E : Subgroup Γ} (hE : OffNat Γ E) :
    ∃ a b : Fin 6, a ≠ b ∧ ∀ x : alternatingGroup (Fin 6),
      FixTwo a b x ↔ ∃ γ ∈ E, actHom hO γ = x := by
  classical
  have hE2' : ∀ t ∈ E, t * t = 1 := fun t ht => by rw [← sq]; exact hE.2.2.1 t ht
  obtain ⟨⟨t₀, ht₀E⟩, ht₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hE.1
  have ht₀1' : t₀ ≠ 1 := fun h => ht₀1 (Subtype.ext h)
  obtain ⟨-, hE4⟩ := card_offender hval hE ht₀E ht₀1'
  have hax := fun {t : Γ} (htE : t ∈ E) (ht1 : t ≠ 1) => axis_eq hval hE ht₀E ht₀1' htE ht1
  let S : Finset (Fin 6) := Finset.univ.filter fun i => (pt i).rep ∈ fixNat Γ E
  have hS : ∀ t ∈ E, t ≠ 1 → ∀ i, actPerm hO t i = i ↔ i ∈ S := fun t htE ht1 i => by
    rw [actPerm_fix_iff hval hO (hE2' t htE) i, ← hax htE ht1]
    simp [S]
  have hS2 : S.card = 2 := by
    have h := card_fixedPoints_involution (actHom hO t₀)
      (by rw [← map_mul, hE2' t₀ ht₀E, map_one])
      (fun h => actPerm_ne_one_of_sq hval hO (hE2' t₀ ht₀E) ht₀1' (congrArg Subtype.val h))
    have hfilt : S = Finset.univ.filter fun p => ((actHom hO t₀ : alternatingGroup (Fin 6)) :
        Perm (Fin 6)) p = p := by
      ext i
      have hi : i ∈ S ↔ actPerm hO t₀ i = i := (hS t₀ ht₀E ht₀1' i).symm
      refine hi.trans ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rfl
    rw [hfilt]
    exact h
  obtain ⟨a, b, hab, hSab⟩ := Finset.card_eq_two.1 hS2
  have hfix : ∀ t ∈ E, actPerm hO t a = a ∧ actPerm hO t b = b := fun t htE => by
    by_cases ht1 : t = 1
    · subst ht1
      simp [actPerm_one]
    · exact ⟨(hS t htE ht1 a).2 (by rw [hSab]; simp), (hS t htE ht1 b).2 (by rw [hSab]; simp)⟩
  have hmem : ∀ t ∈ E, FixTwo a b (actHom hO t) := fun t htE =>
    ⟨(hfix t htE).1, (hfix t htE).2, by rw [← map_mul, hE2' t htE, map_one]⟩
  have hinj : Set.InjOn (actHom hO) {t | t ∈ E} := by
    intro γ hγ γ' hγ' h
    have hz : γ⁻¹ * γ' ∈ Subgroup.center Γ := by
      rw [← ker_actHom hval hO, MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
    have hz2 : (γ⁻¹ * γ') * (γ⁻¹ * γ') = 1 := by
      have hc := hE.2.1 γ' hγ' γ⁻¹ (E.inv_mem hγ)
      calc γ⁻¹ * γ' * (γ⁻¹ * γ') = γ⁻¹ * (γ' * γ⁻¹) * γ' := by group
        _ = γ⁻¹ * (γ⁻¹ * γ') * γ' := by rw [hc]
        _ = (γ * γ)⁻¹ * (γ' * γ') := by group
        _ = 1 := by rw [hE2' γ hγ, hE2' γ' hγ']; simp
    exact inv_mul_eq_one.1 (eq_one_of_mem_center_of_sq hval hz hz2)
  have : Fintype Γ := Fintype.ofFinite Γ
  let T : Finset Γ := Finset.univ.filter fun γ => γ ∈ E
  have hT : T.card = Nat.card E := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have himg : T.image (actHom hO) ⊆ Finset.univ.filter (FixTwo a b) := by
    intro x hx
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.1 hx
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hmem γ (Finset.mem_filter.1 hγ).2⟩
  have hle : (Finset.univ.filter (FixTwo a b)).card ≤ (T.image (actHom hO)).card := by
    rw [card_fixTwo a b hab, Finset.card_image_of_injOn (by simpa [T] using hinj), hT]
    exact hE4
  have heq := Finset.eq_of_subset_of_card_le himg hle
  refine ⟨a, b, hab, fun x => ⟨fun hx => ?_, fun ⟨γ, hγ, hγx⟩ => hγx ▸ hmem γ hγ⟩⟩
  have : x ∈ Finset.univ.filter (FixTwo a b) := Finset.mem_filter.2 ⟨Finset.mem_univ _, hx⟩
  rw [← heq] at this
  obtain ⟨γ, hγ, hγx⟩ := Finset.mem_image.1 this
  exact ⟨γ, (Finset.mem_filter.1 hγ).2, hγx⟩

end CFSG.Quasithin.D35Core
