module

public import CFSG.Quasithin.Vol2.KGFactC31J4M4Fac
public import CFSG.Quasithin.Vol2.KGFactC31Concl
public import CFSG.Quasithin.Vol2.KGFactC31J4OffRun

public section

namespace CFSG.Quasithin.KGC31.J4M4

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Quasithin.KGC31
open CFSG.Quasithin.KGC31.J4 CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.B5.Ln (mat dmat)
open scoped Matrix

theorem map_conj_map_conj {Γ : Type*} [Group Γ] (H : Subgroup Γ) (a b : Γ) :
    (H.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom =
      H.map (MulAut.conj (a * b)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

section Off

variable (hM : MatFacts) (hc : chkF () = true)
  (hcard : Nat.card ↥CFSG.Quasithin.KGJ4.M4 = 10239344640)
include hM hc hcard

theorem card_inf_le {X : Subgroup ↥CFSG.Quasithin.KGJ4.M4}
    (hcomm : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a) :
    Nat.card ↥((piM4 hM hc).ker ⊓ X) ≤ Nat.card {B : ↥(altMat 5) // ∀ g ∈ X.map (piM4 hM hc),
      dmat g * (B : Matrix (Fin 5) (Fin 5) (ZMod 2)) * (dmat g)ᵀ = B} := by
  have hk := ker_piM4 hM hc hcard
  have hb := fJ_basis hM hc
  have hF : ∀ y : ↥((piM4 hM hc).ker ⊓ X), ((y : ↥CFSG.Quasithin.KGJ4.M4) : G₀) ∈ F4 hM hc :=
    fun y => by
      have h1 : (y : ↥CFSG.Quasithin.KGJ4.M4) ∈ (piM4 hM hc).ker := (Subgroup.mem_inf.mp y.2).1
      have h2 : (y : ↥CFSG.Quasithin.KGJ4.M4) ∈ (F4 hM hc).subgroupOf CFSG.Quasithin.KGJ4.M4 := by
        rw [← hk]
        exact h1
      exact Subgroup.mem_subgroupOf.mp h2
  let co : ↥((piM4 hM hc).ker ⊓ X) → Fin 10 → ZMod 2 := fun y =>
    Multiplicative.toAdd (ecoords hb ⟨((y : ↥CFSG.Quasithin.KGJ4.M4) : G₀), hF y⟩)
  have hco : ∀ y, eElt fJ (co y) = ((y : ↥CFSG.Quasithin.KGJ4.M4) : G₀) := fun y =>
    eElt_ecoords hb _
  refine Nat.card_le_card_of_injective (fun y => ⟨⟨altV (co y), altV_mem _⟩, ?_⟩) ?_
  · rintro _ ⟨x, hx, rfl⟩
    show dmat (piM4 hM hc x) * altV (co y) * (dmat (piM4 hM hc x))ᵀ = altV (co y)
    rw [← altV_psiMat]
    refine congrArg altV (eElt_injective hb ?_)
    rw [← piM4_conj hM hc x, hco]
    have e0 := hcomm x hx _ (Subgroup.mem_inf.mp y.2).2
    have e : (x : G₀) * ((y : ↥CFSG.Quasithin.KGJ4.M4) : G₀) =
        ((y : ↥CFSG.Quasithin.KGJ4.M4) : G₀) * (x : G₀) := by
      rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, e0]
    rw [e, mul_inv_cancel_right]
  · intro y y' hyy
    have h1 : altV (co y) = altV (co y') := congrArg (fun B => ((B.1 : ↥(altMat 5)) :
      Matrix (Fin 5) (Fin 5) (ZMod 2))) hyy
    have h2 := altV_injective h1
    have h3 : ((y : ↥CFSG.Quasithin.KGJ4.M4) : G₀) = ((y' : ↥CFSG.Quasithin.KGJ4.M4) : G₀) := by
      rw [← hco y, ← hco y', h2]
    exact Subtype.ext (Subtype.ext h3)

theorem isOff_map {X : Subgroup ↥CFSG.Quasithin.KGJ4.M4}
    (hcomm : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a) (hsq : ∀ a ∈ X, a * a = 1)
    (hX : Nat.card X = 2 ^ 10) (hXF : ¬ X ≤ (F4 hM hc).subgroupOf CFSG.Quasithin.KGJ4.M4) :
    Off5.IsOff (X.map (piM4 hM hc)) := by
  refine ⟨fun h0 => hXF ?_, ?_, ?_, ?_⟩
  · rw [← ker_piM4 hM hc hcard]
    exact (Subgroup.map_eq_bot_iff _).mp h0
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hcomm a ha b hb]
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, hsq a ha, map_one]
  · have h1 := (piM4 hM hc).ker.relIndex_mul_card X
    rw [Subgroup.relIndex_ker, hX] at h1
    rw [← h1]
    exact Nat.mul_le_mul_left _ (card_inf_le hM hc hcard hcomm)

theorem exists_conj_stab0 {R₀ X : Subgroup ↥CFSG.Quasithin.KGJ4.M4} (hR₀ : IsPGroup 2 ↥R₀)
    (hXR : X ≤ R₀) (hcomm : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a) (hsq : ∀ a ∈ X, a * a = 1)
    (hX : Nat.card X = 2 ^ 10) (hXF : ¬ X ≤ (F4 hM hc).subgroupOf CFSG.Quasithin.KGJ4.M4) :
    ∃ m : ↥CFSG.Quasithin.KGJ4.M4, ∀ y ∈ Subgroup.normalizer (R₀ : Set ↥CFSG.Quasithin.KGJ4.M4),
      piM4 hM hc (m⁻¹ * y * m) ∈ Off5.stab0 := by
  have hE := isOff_map hM hc hcard hcomm hsq hX hXF
  obtain ⟨t, ht⟩ := Off5.exists_eq_conj_T0' hE
  obtain ⟨m, rfl⟩ := piM4_surjective hM hc t
  refine ⟨m, fun y hy => ?_⟩
  have hP : IsPGroup 2 ↥(R₀.map (piM4 hM hc)) := hR₀.map _
  have hEP : X.map (piM4 hM hc) ≤ R₀.map (piM4 hM hc) := Subgroup.map_mono hXR
  have hyP : (X.map (piM4 hM hc)).map (MulAut.conj (piM4 hM hc y)).toMonoidHom ≤
      R₀.map (piM4 hM hc) := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨y * x * y⁻¹, (Subgroup.mem_normalizer_iff.mp hy x).mp (hXR hx), ?_⟩
    simp [MulAut.conj_apply, map_mul, map_inv]
  have hEq := Off5.offender_unique' hP hyP hEP (hE.conj (piM4 hM hc y)) hE
  have e : piM4 hM hc (m⁻¹ * y * m) = (piM4 hM hc m)⁻¹ * piM4 hM hc y * piM4 hM hc m := by
    rw [map_mul, map_mul, map_inv]
  apply Off5.normalizer_T0_le
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  show Off5.T0.map (MulAut.conj (piM4 hM hc (m⁻¹ * y * m))).toMonoidHom = Off5.T0
  rw [e, ← map_conj_map_conj, ← map_conj_map_conj, ← ht, hEq, ht, Off5.map_conj_inv_map_conj]

end Off

end CFSG.Quasithin.KGC31.J4M4

end
