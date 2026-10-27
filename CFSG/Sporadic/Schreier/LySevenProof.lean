
module

public import CFSG.Sporadic.Schreier.LySevenProofBase

public import CFSG.Sporadic.Ly.Primitive
public import CFSG.Sporadic.Schreier.LyOperator

public noncomputable section

namespace CFSG.Sporadic.LySchreier

open CFSG.Sporadic.Ly CFSG.Sporadic.Ly.Native CFSG.Sporadic.LySchreier.Native
open CFSG.Sporadic.He.Native Matrix
open CFSG.Sporadic.Th (allIn_eq_true)

@[expose] def lyG0 : Subgroup J :=
  (MulAction.stabilizer (Equiv.Perm (Fin 8835156)) (0 : Fin 8835156)).comap lyAct

theorem mem_lyG0
    {g : J} : g ∈ lyG0 ↔ g • CFSG.Sporadic.Ly.Omega.opE = CFSG.Sporadic.Ly.Omega.opE := by
  change lyAct g • (0 : Fin 8835156) = 0 ↔ _
  rw [Equiv.Perm.smul_def, lyAct_zero]

theorem lyG0_eq_stabilizer :
    lyG0 = MulAction.stabilizer J CFSG.Sporadic.Ly.Omega.opE := by
  ext g
  rw [mem_lyG0, MulAction.mem_stabilizer_iff]

theorem lyG0_eq_lyH : lyG0 = lyH := by
  rw [lyG0_eq_stabilizer]
  exact ly_certificate.2.2.1

theorem card_lyG0 : Nat.card lyG0 = 5859000000 := by
  rw [lyG0_eq_lyH]
  exact ly_certificate.2.2.2.1

theorem lyH_le_lyG0 : lyH ≤ lyG0 := lyG0_eq_lyH.ge

theorem lyt_mem_lyG0 : lyt ∈ lyG0 :=
  mem_lyG0.2 ly_certificate.2.2.2.2.2.2.1

theorem seven_space_centralizer_bound :
    lyH = (MulAction.stabilizer (Equiv.Perm (Fin 8835156)) (0 : Fin 8835156)).comap lyAct ∧
    Nat.card lyH = 5859000000 ∧
    (∀ h ∈ lyH, ∀ u ∈ LinearMap.range (Matrix.mulVecLin lyU),
      mat h *ᵥ u ∈ LinearMap.range (Matrix.mulVecLin lyU)) ∧
    (∀ h ∈ lyH, (∀ u ∈ LinearMap.range (Matrix.mulVecLin lyU), mat h *ᵥ u = u) → h = 1) ∧
    ∃ ht : lyv⁻¹ * lyz * lyv ∈ lyH, orderOf (lyv⁻¹ * lyz * lyv) = 2 ∧
      Nat.card (Subgroup.centralizer ({⟨lyv⁻¹ * lyz * lyv, ht⟩} : Set lyH)) ≤ 14400 := by
  let ψ : lyH' →* lyK := (rhoP.comp lyH'.subtype).codRestrict lyK (fun x => ⟨x, x.2, rfl⟩)
  have hψ : Function.Surjective ψ := by
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hH' : Nat.card lyH' = Nat.card lyH :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe lyH_le_stabU).toEquiv
  have hKH : Nat.card lyK ≤ Nat.card lyH := hH' ▸ Nat.card_le_card_of_surjective ψ hψ
  have hHG : Nat.card lyH ≤ Nat.card lyG0 := Subgroup.card_le_of_le lyH_le_lyG0
  have hK := card_image_ge
  have hcardH : Nat.card lyH = 5859000000 := by rw [card_lyG0] at hHG; omega
  have hHeq : lyH = lyG0 := Subgroup.eq_of_le_of_card_ge lyH_le_lyG0 (by rw [hcardH, card_lyG0])
  have hψb : Function.Bijective ψ :=
    hψ.bijective_of_nat_card_le (by rw [hH']; omega)
  have hinj : ∀ h ∈ lyH, restr7 h = 1 → h = 1 := by
    intro h hh h1
    have e : ψ ⟨⟨h, lyH_le_stabU hh⟩, Subgroup.mem_subgroupOf.2 hh⟩ = ψ 1 := by
      apply Subtype.ext
      change rhoP ⟨h, lyH_le_stabU hh⟩ = rhoP 1
      rw [map_one]
      exact rhoP_eq_one h1
    have := congrArg (fun x : lyH' => ((x : stabU) : J)) (hψb.1 e)
    simpa using this
  have hrange : ∀ u, u ∈ LinearMap.range (Matrix.mulVecLin lyU) ↔ ∃ x, lyU *ᵥ x = u := by
    intro u; rfl
  refine ⟨hHeq, hcardH, fun h hh u hu => ?_, fun h hh hfix => ?_, ?_⟩
  · obtain ⟨x, rfl⟩ := (hrange u).1 hu
    refine (hrange _).2 ⟨restr7 h *ᵥ x, ?_⟩
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← mem_stabU.1 (lyH_le_stabU hh)]
  · apply hinj h hh
    apply restr7_of_eq
    rw [Matrix.mul_one]
    ext i c
    have := hfix (lyU *ᵥ Pi.single c 1) ((hrange _).2 ⟨_, rfl⟩)
    have e := congrFun this i
    rwa [Matrix.mulVec_mulVec, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at e
  · have ht : lyv⁻¹ * lyz * lyv ∈ lyH := hHeq ▸ lyt_mem_lyG0
    refine ⟨ht, ?_, ?_⟩
    · have := MulEquiv.orderOf_eq (MulAut.conj lyv⁻¹) lyz
      rw [MulAut.conj_apply, inv_inv] at this
      rw [this]
      exact orderOf_a
    · have ht' : lyt ∈ lyH := ht
      show Nat.card (Subgroup.centralizer ({⟨lyt, ht'⟩} : Set lyH)) ≤ 14400
      have hc := card_conj_class_ge ht'
      have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (ConjAct lyH)
        (⟨lyt, ht'⟩ : lyH))
      rw [Nat.card_prod, Nat.card_congr ConjAct.toConjAct.symm.toEquiv, hcardH] at h
      have hstab : Nat.card (MulAction.stabilizer (ConjAct lyH) (⟨lyt, ht'⟩ : lyH)) =
          Nat.card (Subgroup.centralizer ({⟨lyt, ht'⟩} : Set lyH)) := by
        exact card_stabilizer_conjAct _
      rw [hstab] at h
      nlinarith

end CFSG.Sporadic.LySchreier
