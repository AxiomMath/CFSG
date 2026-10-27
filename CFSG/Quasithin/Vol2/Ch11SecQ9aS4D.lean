module

public import CFSG.Quasithin.Vol2.Ch11SecQ9aS4B

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A

open Matrix CFSG.Quasithin CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.Open (pCoreOf)

variable (K : Type) [Field K]

@[expose] def tSa : Subgroup (Fin 2 → Kˣ) := (Pi.evalMonoidHom (fun _ : Fin 2 => Kˣ) 0).ker

@[expose] def tSb : Subgroup (Fin 2 → Kˣ) := (Pi.evalMonoidHom (fun _ : Fin 2 => Kˣ) 1).ker

@[expose] def tSc : Subgroup (Fin 2 → Kˣ) :=
  (Pi.evalMonoidHom (fun _ : Fin 2 => Kˣ) 0 * Pi.evalMonoidHom (fun _ : Fin 2 => Kˣ) 1).ker

@[expose] def tSd : Subgroup (Fin 2 → Kˣ) :=
  (Pi.evalMonoidHom (fun _ : Fin 2 => Kˣ) 0 / Pi.evalMonoidHom (fun _ : Fin 2 => Kˣ) 1).ker

variable {K}

theorem mem_tSa {t : Fin 2 → Kˣ} : t ∈ tSa K ↔ t 0 = 1 := Iff.rfl

theorem mem_tSb {t : Fin 2 → Kˣ} : t ∈ tSb K ↔ t 1 = 1 := Iff.rfl

theorem mem_tSc {t : Fin 2 → Kˣ} : t ∈ tSc K ↔ t 0 * t 1 = 1 := Iff.rfl

theorem mem_tSd {t : Fin 2 → Kˣ} : t ∈ tSd K ↔ t 0 = t 1 := by
  change t 0 / t 1 = 1 ↔ _
  exact div_eq_one

theorem eq_of_fin_two {t t' : Fin 2 → Kˣ} (h0 : t 0 = t' 0) (h1 : t 1 = t' 1) : t = t' := by
  funext i
  fin_cases i
  · exact h0
  · exact h1

theorem card_tS (S : Subgroup (Fin 2 → Kˣ)) (φ : (Fin 2 → Kˣ) → Kˣ) (ψ : Kˣ → (Fin 2 → Kˣ))
    (hψ : ∀ a, ψ a ∈ S) (hφψ : ∀ a, φ (ψ a) = a) (hψφ : ∀ t ∈ S, ψ (φ t) = t) :
    Nat.card ↥S = Nat.card Kˣ :=
  Nat.card_congr
    { toFun := fun t => φ t
      invFun := fun a => ⟨ψ a, hψ a⟩
      left_inv := fun t => Subtype.ext (hψφ t t.2)
      right_inv := hφψ }

theorem card_tSa : Nat.card ↥(tSa K) = Nat.card Kˣ :=
  card_tS _ (fun t => t 1) (fun a => ![1, a]) (fun _ => rfl) (fun _ => rfl)
    (fun _ ht => eq_of_fin_two (mem_tSa.mp ht).symm rfl)

theorem card_tSb : Nat.card ↥(tSb K) = Nat.card Kˣ :=
  card_tS _ (fun t => t 0) (fun a => ![a, 1]) (fun _ => rfl) (fun _ => rfl)
    (fun _ ht => eq_of_fin_two rfl (mem_tSb.mp ht).symm)

theorem card_tSc : Nat.card ↥(tSc K) = Nat.card Kˣ :=
  card_tS _ (fun t => t 0) (fun a => ![a, a⁻¹]) (fun a => mem_tSc.mpr (mul_inv_cancel a))
    (fun _ => rfl) (fun _ ht => eq_of_fin_two rfl (eq_inv_of_mul_eq_one_right ht).symm)

theorem card_tSd : Nat.card ↥(tSd K) = Nat.card Kˣ :=
  card_tS _ (fun t => t 0) (fun a => ![a, a]) (fun _ => mem_tSd.mpr rfl) (fun _ => rfl)
    (fun _ ht => eq_of_fin_two rfl (mem_tSd.mp ht))

theorem torus_inf_eq_map {X : Subgroup (StatedSp 2 K)} {S : Subgroup (Fin 2 → Kˣ)}
    (h : ∀ t, torusHom t ∈ X ↔ t ∈ S) : torus 2 K ⊓ X = S.map torusHom := by
  ext x
  constructor
  · rintro ⟨⟨t, rfl⟩, hx⟩
    exact ⟨t, (h t).mp hx, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨⟨t, rfl⟩, (h t).mpr ht⟩

variable [Finite K] [CharP K 2]

omit [CharP K 2] in
theorem torus_inf_N0 (hK4 : ∃ s : Finset K, s.card = 4) :
    torus 2 K ⊓ perfectCore (Q2 K 0) = (tSa K).map torusHom :=
  torus_inf_eq_map fun t => (torusHom_mem_N0_iff hK4 t).trans mem_tSa.symm

omit [CharP K 2] in
theorem torus_inf_N1 (hK4 : ∃ s : Finset K, s.card = 4) :
    torus 2 K ⊓ perfectCore (Q2 K 1) = (tSc K).map torusHom :=
  torus_inf_eq_map fun t => (torusHom_mem_N1_iff hK4 t).trans mem_tSc.symm

theorem torus_inf_sc0 (hK4 : ∃ s : Finset K, s.card = 4) :
    torus 2 K ⊓ sectionCentralizer (perfectCore (Q2 K 0)) (pCoreOf 2 (perfectCore (Q2 K 0))) =
      (tSb K).map torusHom :=
  torus_inf_eq_map fun t => (torusHom_mem_sc0_iff hK4 t).trans mem_tSb.symm

theorem torus_inf_sc1 (hK4 : ∃ s : Finset K, s.card = 4) :
    torus 2 K ⊓ sectionCentralizer (perfectCore (Q2 K 1)) (pCoreOf 2 (perfectCore (Q2 K 1))) =
      (tSd K).map torusHom :=
  torus_inf_eq_map fun t => (torusHom_mem_sc1_iff hK4 t).trans mem_tSd.symm

omit [Finite K] [CharP K 2] in
theorem torus_le_sup_ba : torus 2 K ≤ (tSb K).map torusHom ⊔ (tSa K).map torusHom := by
  rintro _ ⟨t, rfl⟩
  have e : t = ![t 0, 1] * ![1, t 1] := eq_of_fin_two (by simp) (by simp)
  rw [e, map_mul]
  exact Subgroup.mul_mem_sup ⟨_, mem_tSb.mpr rfl, rfl⟩ ⟨_, mem_tSa.mpr rfl, rfl⟩

omit [Finite K] [CharP K 2] in
theorem torus_le_sup_ac : torus 2 K ≤ (tSa K).map torusHom ⊔ (tSc K).map torusHom := by
  rintro _ ⟨t, rfl⟩
  have e : t = ![1, t 0 * t 1] * ![t 0, (t 0)⁻¹] :=
    eq_of_fin_two (by simp) (by simp [mul_comm (t 0)])
  rw [e, map_mul]
  exact Subgroup.mul_mem_sup ⟨_, mem_tSa.mpr rfl, rfl⟩
    ⟨_, mem_tSc.mpr (mul_inv_cancel (t 0)), rfl⟩

theorem torus_inf_N0_inf_sc1 (hK4 : ∃ s : Finset K, s.card = 4) :
    torus 2 K ⊓ perfectCore (Q2 K 0) ⊓
      sectionCentralizer (perfectCore (Q2 K 1)) (pCoreOf 2 (perfectCore (Q2 K 1))) = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨⟨⟨t, rfl⟩, h0⟩, h1⟩
  have h0' := (torusHom_mem_N0_iff hK4 t).mp h0
  have h1' := (torusHom_mem_sc1_iff hK4 t).mp h1
  rw [Subgroup.mem_bot]
  have ht : t = 1 := eq_of_fin_two h0' (h1'.symm.trans h0')
  rw [ht, map_one]

end CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
