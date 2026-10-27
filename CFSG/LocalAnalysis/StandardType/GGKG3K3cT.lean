module

public import CFSG.LocalAnalysis.StandardType.GGKG3Coord
public import CFSG.LocalAnalysis.StandardType.GGKG3Act
public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpDefs

public section

namespace CFSG.StandardType.GGKG3

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.StandardType

theorem k3c_transport
    {L : Type} [Field L] [IsAlgClosed L] (S : LangSetup .E6 L 7) (hS : IsK3Setup S)
    (φ : MulAut ↥(S.E.subgroupOf S.Γ)) (hr : GGIsReflection 7 φ) (c : WeylGroup .E6)
    (hc : ∀ x : ↥(S.E.subgroupOf S.Γ),
      (((φ x : ↥(S.E.subgroupOf S.Γ)) : S.Γ) : ModGL .E6 L) =
        canonicalRep (coxeterSystem .E6) L c * ((x : S.Γ) : ModGL .E6 L) *
          (canonicalRep (coxeterSystem .E6) L c)⁻¹) :
    (∀ y ∈ k3Ex, k3Star c y ∈ k3Ex) ∧ (∀ y ∈ k3Ex, k3Star c (k3Star c y) = y) ∧
      {y : Fin 6 → ZMod 7 | y ∈ k3Ex ∧ k3Star c y = y}.ncard = 49 := by
  have h2 : ((2 : ℕ) : L) = 0 := by
    rw [← hS.q_eq]
    exact S.hqpow.2
  obtain ⟨ζ, hζ⟩ := k3_exists_zeta (L := L) h2
  have h7 : ζ ^ 7 = 1 := by
    rw [← hζ]
    exact pow_orderOf_eq_one ζ
  have hEΓ : S.E ≤ S.Γ := S.E_le.trans inf_le_right
  have hdiag_mem : ∀ y ∈ k3Ex, k3Diag ζ y ∈ S.E := by
    intro y hy
    exact (k3_E_eq S hS hζ (k3Diag ζ y)).2 ⟨y, hy, rfl⟩
  let ψ : ↥k3Ex → ↥(S.E.subgroupOf S.Γ) := fun y =>
    ⟨⟨k3Diag ζ (y : Fin 6 → ZMod 7), hEΓ (hdiag_mem (y : Fin 6 → ZMod 7) y.2)⟩,
      Subgroup.mem_subgroupOf.mpr (hdiag_mem (y : Fin 6 → ZMod 7) y.2)⟩
  have hψinj : Function.Injective ψ := by
    intro a b hab
    apply Subtype.ext
    apply k3Diag_injective hζ
    have h := congrArg (fun z : ↥(S.E.subgroupOf S.Γ) => ((z : S.Γ) : ModGL .E6 L)) hab
    simpa [ψ] using h
  have hψsurj : Function.Surjective ψ := by
    intro b
    have hbE : ((b : S.Γ) : ModGL .E6 L) ∈ S.E := Subgroup.mem_subgroupOf.mp b.2
    obtain ⟨y, hy, hyb⟩ := (k3_E_eq S hS hζ ((b : S.Γ) : ModGL .E6 L)).1 hbE
    refine ⟨⟨y, hy⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    simpa [ψ] using hyb.symm
  have hphi_apply : ∀ y : ↥k3Ex,
      (((φ (ψ y) : ↥(S.E.subgroupOf S.Γ)) : S.Γ) : ModGL .E6 L)
        = k3Diag ζ (k3Star c (y : Fin 6 → ZMod 7)) := by
    intro y
    rw [hc (ψ y)]
    have hψval : (((ψ y : ↥(S.E.subgroupOf S.Γ)) : S.Γ) : ModGL .E6 L)
        = k3Diag ζ (y : Fin 6 → ZMod 7) := rfl
    rw [hψval]
    exact k3_conj_diag h7 c (y : Fin 6 → ZMod 7)
  have hstar_mem : ∀ y ∈ k3Ex, k3Star c y ∈ k3Ex := by
    intro y hy
    have hmemE : k3Diag ζ (k3Star c y) ∈ S.E := by
      have h := Subgroup.mem_subgroupOf.mp (φ (ψ ⟨y, hy⟩)).2
      rwa [hphi_apply ⟨y, hy⟩] at h
    obtain ⟨y', hy', hy'eq⟩ := (k3_E_eq S hS hζ (k3Diag ζ (k3Star c y))).1 hmemE
    have hEq : k3Star c y = y' := k3Diag_injective hζ hy'eq
    simpa [hEq] using hy'
  have hphi : ∀ y : ↥k3Ex,
      φ (ψ y) = ψ ⟨k3Star c (y : Fin 6 → ZMod 7),
        hstar_mem (y : Fin 6 → ZMod 7) y.2⟩ := by
    intro y
    apply Subtype.ext
    apply Subtype.ext
    exact hphi_apply y
  have hsq : ∀ b : ↥(S.E.subgroupOf S.Γ), φ (φ b) = b := by
    intro b
    rw [← MulAut.mul_apply, ← pow_two, hr.1, MulAut.one_apply]
  have hInv : ∀ y ∈ k3Ex, k3Star c (k3Star c y) = y := by
    intro y hy
    have hy1 : k3Star c y ∈ k3Ex := hstar_mem y hy
    have hstar2 :
        ψ ⟨k3Star c (k3Star c y), hstar_mem (k3Star c y) hy1⟩ = ψ ⟨y, hy⟩ := by
      calc ψ ⟨k3Star c (k3Star c y), hstar_mem (k3Star c y) hy1⟩
          = φ (ψ ⟨k3Star c y, hy1⟩) := (hphi ⟨k3Star c y, hy1⟩).symm
        _ = φ (φ (ψ ⟨y, hy⟩)) := by rw [← hphi ⟨y, hy⟩]
        _ = ψ ⟨y, hy⟩ := hsq (ψ ⟨y, hy⟩)
    exact congrArg (fun z : ↥k3Ex => (z : Fin 6 → ZMod 7)) (hψinj hstar2)
  have hFx : {y : Fin 6 → ZMod 7 | y ∈ k3Ex ∧ k3Star c y = y}
      = Subtype.val '' {y : ↥k3Ex | k3Star c (y : Fin 6 → ZMod 7) = (y : Fin 6 → ZMod 7)} := by
    ext y
    constructor
    · rintro ⟨hy, hfix⟩
      exact ⟨⟨y, hy⟩, hfix, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.2, hz⟩
  have hcard1 : {y : Fin 6 → ZMod 7 | y ∈ k3Ex ∧ k3Star c y = y}.ncard
      = Nat.card {y : ↥k3Ex | k3Star c (y : Fin 6 → ZMod 7) = (y : Fin 6 → ZMod 7)} := by
    rw [hFx, Set.ncard_image_of_injective _ (fun a b h => Subtype.ext h)]
    exact (Nat.card_coe_set_eq _).symm
  let e : ↥k3Ex ≃ ↥(S.E.subgroupOf S.Γ) := Equiv.ofBijective ψ ⟨hψinj, hψsurj⟩
  have hpq : ∀ a : ↥k3Ex,
      (k3Star c (a : Fin 6 → ZMod 7) = (a : Fin 6 → ZMod 7)) ↔ φ (e a) = e a := by
    intro a
    have hea : e a = ψ a := rfl
    rw [hea]
    constructor
    · intro h
      have hsub : (⟨k3Star c (a : Fin 6 → ZMod 7),
          hstar_mem (a : Fin 6 → ZMod 7) a.2⟩ : ↥k3Ex) = a := Subtype.ext h
      rw [hphi a, hsub]
    · intro h
      have h2 : ψ ⟨k3Star c (a : Fin 6 → ZMod 7),
          hstar_mem (a : Fin 6 → ZMod 7) a.2⟩ = ψ a := by
        rw [← hphi a]
        exact h
      exact congrArg (fun z : ↥k3Ex => (z : Fin 6 → ZMod 7)) (hψinj h2)
  have hcard2 : Nat.card {y : ↥k3Ex | k3Star c (y : Fin 6 → ZMod 7) = (y : Fin 6 → ZMod 7)}
      = Nat.card {b : ↥(S.E.subgroupOf S.Γ) // φ b = b} :=
    Nat.card_congr (Equiv.subtypeEquiv e hpq)
  have hBcard : Nat.card ↥(S.E.subgroupOf S.Γ) = 343 := by
    have h1 : Nat.card ↥(S.E.subgroupOf S.Γ) = Nat.card ↥S.E :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEΓ).toEquiv
    rw [h1, hS.card_E]
    norm_num
  have hmul : Nat.card {b : ↥(S.E.subgroupOf S.Γ) // φ b = b} * 7 = 343 := by
    rw [hr.2, hBcard]
  refine ⟨hstar_mem, hInv, ?_⟩
  rw [hcard1, hcard2]
  exact Nat.eq_of_mul_eq_mul_right (m := 7) (by norm_num) (by rw [hmul])

end CFSG.StandardType.GGKG3
