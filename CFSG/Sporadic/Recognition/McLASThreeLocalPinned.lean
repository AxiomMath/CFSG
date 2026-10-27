module

public import CFSG.Sporadic.Recognition.McLASThreeLocalMain
public import CFSG.Sporadic.Recognition.McLASInvolutions

public section

namespace CFSG.Sporadic.Recognition.McLAS

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.Blueprint

structure ThreeLocalAut (G : Type*) [Group G] (x : G) (R T A : Subgroup G) : Prop
    extends ThreeLocal G x R T A where
  delta_iff : ∀ H : Subgroup G, IsPCentralSubgroup 3 H ↔
    ∃ g : G, H = (zpowers x).map (MulAut.conj g).toMonoidHom
  A_eq_delta : A = closure {y : G | ∃ H : Subgroup G, IsPCentralSubgroup 3 H ∧ H ≤ T ∧ y ∈ H}
  card_delta_inter : {H : Subgroup G | IsPCentralSubgroup 3 H ∧ H ≤ T}.ncard = 10
  card_normalizer_aut :
    Nat.card ↥(normalizer (zpowers (MulAut.conj x : MulAut G) : Set (MulAut G))) = 116640
  exists_inverting : ∃ σ : MulAut G, orderOf σ = 2 ∧ σ ∉ inner G ∧ ∀ a ∈ A, σ a = a⁻¹

theorem threeLocal_of_equiv
    {T : Type*} [Group T] (e : T ≃* mclP) (Φ : MulAut T ≃* mclR)
    (hΦ1 : ∀ (σ : MulAut T) (g : T), ((e (σ g) : mclP) : Equiv.Perm (Fin 275)) =
      (Φ σ : Equiv.Perm (Fin 275)) * ((e g : mclP) : Equiv.Perm (Fin 275)) *
        (Φ σ : Equiv.Perm (Fin 275))⁻¹)
    (hΦ2 : ∀ σ : MulAut T, σ ∈ inner T ↔ ((Φ σ : mclR) : Equiv.Perm (Fin 275)) ∈ mclP)
    (hΦ3 : ∀ c : T, ((Φ (MulAut.conj c) : mclR) : Equiv.Perm (Fin 275)) =
      ((e c : mclP) : Equiv.Perm (Fin 275)))
    (hrows : ThreeFacts) (hsyl : sylowThreeOK = true) (h : threeLocalCheck = true) :
    ∃ (x : T) (R T' A : Subgroup T), ThreeLocalAut T x R T' A := by
  let ι : T →* Equiv.Perm (Fin 275) := mclP.subtype.comp e.toMonoidHom
  have hι : Function.Injective ι := Subtype.val_injective.comp e.injective
  have hrange : ι.range = mclP := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.surjective,
      ← MonoidHom.range_eq_map, range_subtype]
  have hιe : ∀ g : T, ι g = ((e g : mclP) : Equiv.Perm (Fin 275)) := fun g => rfl
  obtain ⟨x, R, T', A, hxι, hAι, hL, hΔ, hA, hcount⟩ :=
    delta_of_embedding ι hι hrange hrows hsyl h
  have h' := h
  simp only [threeLocalCheck, Bool.and_eq_true] at h'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨he, hg⟩, hin⟩, -⟩, -⟩, -⟩, hAc⟩, hinvc⟩, -⟩, -⟩ := h'
  obtain ⟨hσR, hσP, hσ2, hσinv⟩ := aInvCheck_spec hrows he hin hAc hinvc
  obtain ⟨-, hcardgxh⟩ := card_gx hrows hg
  let ι' : MulAut T →* Equiv.Perm (Fin 275) := mclR.subtype.comp Φ.toMonoidHom
  have hι' : Function.Injective ι' := Subtype.val_injective.comp Φ.injective
  have hrange' : ι'.range = mclR := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr Φ.surjective,
      ← MonoidHom.range_eq_map, range_subtype]
  have hι'x : ι' (MulAut.conj x) = three₁ := by
    change ((Φ (MulAut.conj x) : mclR) : Equiv.Perm (Fin 275)) = three₁
    rw [hΦ3 x, ← hxι]
    rfl
  refine ⟨x, R, T', A, ?_⟩
  refine
    { hL with
      delta_iff := hΔ
      A_eq_delta := hA
      card_delta_inter := hcount
      card_normalizer_aut := ?_
      exists_inverting := ?_ }
  · have hmap := map_normalizer_eq_inf_of_injective hι' (zpowers (MulAut.conj x : MulAut T))
    rw [MonoidHom.map_zpowers, hι'x, hrange'] at hmap
    rw [← Subgroup.card_map_of_injective hι', hmap]
    exact hcardgxh
  · let σ : MulAut T := Φ.symm ⟨tp 275 sigmaTab, hσR⟩
    have hΦσ : ((Φ σ : mclR) : Equiv.Perm (Fin 275)) = tp 275 sigmaTab := by
      simp [σ]
    refine ⟨σ, ?_, ?_, ?_⟩
    · have hord : orderOf ((Φ σ : mclR) : Equiv.Perm (Fin 275)) = orderOf σ := by
        rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
      rw [← hord, hΦσ]
      exact hσ2
    · rw [hΦ2, hΦσ]
      exact hσP
    · intro a ha
      apply hι
      have h1 := hΦ1 σ a
      rw [hΦσ] at h1
      have haA : ι a ∈ subA3 := by rw [hAι] at ha; exact ha
      have h2 := hσinv (ι a) haA
      rw [hιe, map_inv]
      rw [h1]
      exact h2

theorem mcl_threeLocal
    (hrows : ThreeFacts) (hsyl : sylowThreeOK = true) (h : threeLocalCheck = true) :
    ∃ (x : NativeSporadic.McL) (R T A : Subgroup NativeSporadic.McL),
      ThreeLocalAut NativeSporadic.McL x R T A := by
  obtain ⟨Φ, hΦ1, hΦ2, hΦ3⟩ := exists_aut_model
  exact @threeLocal_of_equiv NativeSporadic.McL inferInstance mclPermEquiv Φ hΦ1 hΦ2 hΦ3
    hrows hsyl h

end CFSG.Sporadic.Recognition.McLAS
