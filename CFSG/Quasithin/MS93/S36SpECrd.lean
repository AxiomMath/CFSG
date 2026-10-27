module

public import CFSG.Quasithin.MS93.S6Bridge
public import CFSG.Quasithin.MS93.MSPBasic
public import CFSG.Quasithin.Background.C124BlkQuot
public import CFSG.Quasithin.Background.FFC8A

public section

namespace CFSG.Quasithin.MS93.S36E

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Matrix

variable {S : Type} [CommGroup S]

theorem coord_of_natSp4 {K : Subgroup (MulAut S)} {F : Type} [Field F]
    {π : ↥(StatedSp 2 F) →* ↥K} (hR : (FFModel.nat (StatedSp 2 F)).RealizesVia K ⊤ ⊥ π) :
    ∃ (φ : ↥K →* MSP.Sp4 F) (θ : S ≃* Multiplicative (MSP.V4 F)), ∀ (x : ↥K) (s : S),
      Multiplicative.toAdd (θ ((x : MulAut S) s)) =
        MSP.mat (φ x) *ᵥ Multiplicative.toAdd (θ s) := by
  set e := FFC.equivOfRealizes (FFModel.nat_faithful _) hR with he
  obtain ⟨-, -, -, -, -, -, -, β, hβs, hβk, hβc⟩ := id hR
  have hβi : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro u hu
    have := (hβk u).mp hu
    rw [Subgroup.mem_bot] at this ⊢
    exact Subtype.ext this
  obtain ⟨q, hq⟩ : ∃ q : ↥(FFModel.nat (StatedSp 2 F)).sec ⧸
      (FFModel.nat (StatedSp 2 F)).ker.subgroupOf (FFModel.nat (StatedSp 2 F)).sec ≃*
        Multiplicative (MSP.V4 F), ∀ m, q (QuotientGroup.mk m) = m.1 :=
    ⟨((QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf _)).trans
      QuotientGroup.quotientBot).trans Subgroup.topEquiv, fun _ => rfl⟩
  set θ : S ≃* Multiplicative (MSP.V4 F) :=
    Subgroup.topEquiv.symm.trans ((MulEquiv.ofBijective β ⟨hβi, hβs⟩).trans q) with hθ
  refine ⟨e.symm.toMonoidHom, θ, fun x s => ?_⟩
  set γ := e.symm x with hγ
  have hx : π γ = x := by
    rw [hγ]
    exact e.apply_symm_apply x
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨s, Subgroup.mem_top s⟩)
  have h1 : β ⟨((π γ : ↥K) : MulAut S) s, Subgroup.mem_top _⟩ =
      QuotientGroup.mk ⟨(FFModel.nat (StatedSp 2 F)).act γ m, Subgroup.mem_top _⟩ :=
    hβc γ ⟨s, Subgroup.mem_top s⟩ m (Subgroup.mem_top _) (Subgroup.mem_top _) hm.symm
  have hθs : θ s = q (β ⟨s, Subgroup.mem_top s⟩) := rfl
  have hθx : θ ((x : MulAut S) s) = q (β ⟨(x : MulAut S) s, Subgroup.mem_top _⟩) := rfl
  rw [hθx, hθs]
  have h2 : (⟨((π γ : ↥K) : MulAut S) s, Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup S)) =
      ⟨(x : MulAut S) s, Subgroup.mem_top _⟩ := by
    rw [hx]
  rw [← h2, h1, ← hm, hq, hq]
  rfl

theorem mem_alt6Sub_iff (γ : ↥(StatedSp 2 (ZMod 2))) :
    γ ∈ (alternatingGroup (Fin 6)).comap Sp4Inf.iotaSp.toMonoidHom ↔
      ∃ σ : ↥(alternatingGroup (Fin 6)), S6B.thetaTwo (σ : Equiv.Perm (Fin 6)) = γ := by
  constructor
  · intro hγ
    have h1 : S6B.thetaTwo.symm γ ∈ alternatingGroup (Fin 6) := by
      rw [Equiv.Perm.mem_alternatingGroup, ← S6B.sign_iotaSp_thetaTwo,
        MulEquiv.apply_symm_apply]
      exact Equiv.Perm.mem_alternatingGroup.mp hγ
    exact ⟨⟨_, h1⟩, MulEquiv.apply_symm_apply _ _⟩
  · rintro ⟨σ, rfl⟩
    show Sp4Inf.iotaSp (S6B.thetaTwo (σ : Equiv.Perm (Fin 6))) ∈ alternatingGroup (Fin 6)
    rw [Equiv.Perm.mem_alternatingGroup, S6B.sign_iotaSp_thetaTwo]
    exact Equiv.Perm.mem_alternatingGroup.mp σ.2

theorem exists_heartCoord {K : Subgroup (MulAut S)} {π : ↥(alternatingGroup (Fin 6)) →* ↥K}
    (hR : (FFModel.altDn 6).RealizesVia K ⊤ ⊥ π) :
    ∃ θ : S ≃* Multiplicative (MSP.V4 (ZMod 2)), ∀ (σ : ↥(alternatingGroup (Fin 6))) (s : S),
      Multiplicative.toAdd (θ (((π σ : ↥K) : MulAut S) s)) =
        MSP.mat (S6B.thetaTwo (σ : Equiv.Perm (Fin 6))) *ᵥ Multiplicative.toAdd (θ s) := by
  obtain ⟨-, -, -, -, -, -, -, β, hβs, hβk, hβc⟩ := hR
  let β₁ : ↥(⊤ : Subgroup S) →* (↥(G6.coreMod 6) ⧸ C124.altKer 6) := β
  have hβi : Function.Injective β₁ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro u hu
    have := (hβk u).mp hu
    rw [Subgroup.mem_bot] at this ⊢
    exact Subtype.ext this
  set c : Multiplicative (AltHeart 6) ≃* Multiplicative (MSP.V4 (ZMod 2)) :=
    MulEquiv.ofBijective S6B.crdHom S6B.crdHom_bijective with hc
  set θ : S ≃* Multiplicative (MSP.V4 (ZMod 2)) :=
    ((Subgroup.topEquiv.symm.trans (MulEquiv.ofBijective β₁ ⟨hβi, hβs⟩)).trans
      (C124.altQuotEquiv 6 (by norm_num))).trans c with hθ
  refine ⟨θ, fun σ s => ?_⟩
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨s, Subgroup.mem_top s⟩)
  have hact : (FFModel.altDn 6).act σ (m : (FFModel.altDn 6).Amb) ∈ (FFModel.altDn 6).sec :=
    G6.permAct_mem_coreMod _ m.2
  have h1 : β ⟨((π σ : ↥K) : MulAut S) s, Subgroup.mem_top _⟩ = QuotientGroup.mk ⟨_, hact⟩ :=
    hβc σ ⟨s, Subgroup.mem_top s⟩ m (Subgroup.mem_top _) hact hm.symm
  have hθs : θ s = c (C124.altHeartHom 6 m) := by
    show c (C124.altQuotEquiv 6 (by norm_num) (β₁ ⟨s, Subgroup.mem_top s⟩)) = _
    rw [show β₁ ⟨s, Subgroup.mem_top s⟩ = QuotientGroup.mk m from hm.symm]
    rfl
  have hθσ : θ (((π σ : ↥K) : MulAut S) s) = c (C124.altHeartHom 6 ⟨_, hact⟩) := by
    show c (C124.altQuotEquiv 6 (by norm_num) (β₁ ⟨_, Subgroup.mem_top _⟩)) = _
    rw [show β₁ ⟨_, Subgroup.mem_top _⟩ = QuotientGroup.mk ⟨_, hact⟩ from h1]
    rfl
  rw [hθσ, hθs]
  show S6B.heartCrd (QuotientAddGroup.mk (permWeight 6 (σ : Equiv.Perm (Fin 6))
    (Multiplicative.toAdd (C124.coreEvenEquiv 6 m)))) = _
  rw [S6B.heartCrd_perm]
  rfl

theorem coord_of_altDn {X K : Subgroup (MulAut S)}
    {π : ↥(alternatingGroup (Fin 6)) →* ↥K} (hR : (FFModel.altDn 6).RealizesVia K ⊤ ⊥ π)
    (hXK : X ≤ Subgroup.normalizer (K : Set (MulAut S))) :
    ∃ (φ : ↥X →* MSP.Sp4 (ZMod 2)) (θ : S ≃* Multiplicative (MSP.V4 (ZMod 2))),
      ∀ (x : ↥X) (s : S), Multiplicative.toAdd (θ ((x : MulAut S) s)) =
        MSP.mat (φ x) *ᵥ Multiplicative.toAdd (θ s) := by
  have hπs : Function.Surjective π := hR.1
  obtain ⟨θ, hθ⟩ := exists_heartCoord hR
  set E : GL Sp4Inf.I4 (ZMod 2) ≃* MulAut (H.StdMod Sp4Inf.I4 (ZMod 2)) :=
    MulEquiv.ofBijective H.matHom ⟨H.matHom_injective, fun a =>
      (Sp4Inf.exists_matAut_zmod_two a).imp fun A h => (H.matHom_apply A).trans h.symm⟩ with hE
  set A : ↥X →* GL Sp4Inf.I4 (ZMod 2) :=
    E.symm.toMonoidHom.comp ((MulAut.congr θ).toMonoidHom.comp X.subtype) with hA
  have hEA : ∀ x : ↥X, E (A x) = MulAut.congr θ (x : MulAut S) := fun x =>
    E.apply_symm_apply _
  have hAapp : ∀ (x : ↥X) (v : MSP.V4 (ZMod 2)),
      ((A x : GL Sp4Inf.I4 (ZMod 2)) : Matrix _ _ (ZMod 2)) *ᵥ v =
        Multiplicative.toAdd (θ ((x : MulAut S) (θ.symm (Multiplicative.ofAdd v)))) := by
    intro x v
    have h2 := congrArg (fun a : MulAut (H.StdMod Sp4Inf.I4 (ZMod 2)) =>
      Multiplicative.toAdd (a (Multiplicative.ofAdd v))) (hEA x)
    simp only [hE] at h2
    rw [← H.toAddMap_matAut]
    exact h2
  have hEθ : ∀ σ : ↥(alternatingGroup (Fin 6)),
      E ((S6B.thetaTwo (σ : Equiv.Perm (Fin 6)) : ↥(StatedSp 2 (ZMod 2))) :
        GL Sp4Inf.I4 (ZMod 2)) = MulAut.congr θ ((π σ : ↥K) : MulAut S) := by
    intro σ
    refine MulEquiv.ext fun w => Multiplicative.toAdd.injective ?_
    obtain ⟨s, rfl⟩ := θ.surjective w
    have h3 : Multiplicative.toAdd (E ((S6B.thetaTwo (σ : Equiv.Perm (Fin 6)) :
        ↥(StatedSp 2 (ZMod 2))) : GL Sp4Inf.I4 (ZMod 2)) (θ s)) =
        MSP.mat (S6B.thetaTwo (σ : Equiv.Perm (Fin 6))) *ᵥ Multiplicative.toAdd (θ s) := by
      show H.toAddMap (H.matAut _) (Multiplicative.toAdd (θ s)) = _
      rw [H.toAddMap_matAut]
    rw [h3]
    show _ = Multiplicative.toAdd (θ (((π σ : ↥K) : MulAut S) (θ.symm (θ s))))
    rw [MulEquiv.symm_apply_apply, hθ]
  set D : Subgroup ↥(StatedSp 2 (ZMod 2)) :=
    (alternatingGroup (Fin 6)).comap Sp4Inf.iotaSp.toMonoidHom with hD
  have hDalt : Sp4Inf.IsAlt6Sub D := Sp4Inf.isAlt6Sub_comap
  have hconj : ∀ (x : ↥X) (σ : ↥(alternatingGroup (Fin 6))), ∃ τ : ↥(alternatingGroup (Fin 6)),
      (x : MulAut S) * ((π σ : ↥K) : MulAut S) * (x : MulAut S)⁻¹ = ((π τ : ↥K) : MulAut S) := by
    intro x σ
    have hmem : (x : MulAut S) * ((π σ : ↥K) : MulAut S) * (x : MulAut S)⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (hXK x.2) _).mp (π σ).2
    obtain ⟨τ, hτ⟩ := hπs ⟨_, hmem⟩
    exact ⟨τ, (congrArg Subtype.val hτ).symm⟩
  have hAmat : ∀ (x : ↥X) (σ : ↥(alternatingGroup (Fin 6))), ∃ τ : ↥(alternatingGroup (Fin 6)),
      A x * ((S6B.thetaTwo (σ : Equiv.Perm (Fin 6)) : ↥(StatedSp 2 (ZMod 2))) :
        GL Sp4Inf.I4 (ZMod 2)) * (A x)⁻¹ =
      ((S6B.thetaTwo (τ : Equiv.Perm (Fin 6)) : ↥(StatedSp 2 (ZMod 2))) :
        GL Sp4Inf.I4 (ZMod 2)) := by
    intro x σ
    obtain ⟨τ, hτ⟩ := hconj x σ
    refine ⟨τ, E.injective ?_⟩
    rw [map_mul, map_mul, map_inv, hEA, hEθ, hEθ, ← map_inv, ← map_mul, ← map_mul, hτ]
  have hSp : ∀ x : ↥X, A x ∈ StatedSp 2 (ZMod 2) := by
    intro x
    have h₁ : ∀ γ ∈ D, ∃ δ ∈ D, A x * (γ : GL Sp4Inf.I4 (ZMod 2)) * (A x)⁻¹ =
        (δ : GL Sp4Inf.I4 (ZMod 2)) := by
      intro γ hγ
      obtain ⟨σ, rfl⟩ := (mem_alt6Sub_iff γ).1 hγ
      obtain ⟨τ, hτ⟩ := hAmat x σ
      exact ⟨_, (mem_alt6Sub_iff _).2 ⟨τ, rfl⟩, hτ⟩
    have h₂ : ∀ δ ∈ D, ∃ γ ∈ D, (A x)⁻¹ * (δ : GL Sp4Inf.I4 (ZMod 2)) * A x =
        (γ : GL Sp4Inf.I4 (ZMod 2)) := by
      intro δ hδ
      obtain ⟨σ, rfl⟩ := (mem_alt6Sub_iff δ).1 hδ
      obtain ⟨τ, hτ⟩ := hAmat x⁻¹ σ
      rw [map_inv, inv_inv] at hτ
      exact ⟨_, (mem_alt6Sub_iff _).2 ⟨τ, rfl⟩, hτ⟩
    obtain ⟨α, hα⟩ := Sp4Inf.mem_statedSp_of_normalizes hDalt (A x) h₁ h₂
    rw [← hα]
    exact α.2
  refine ⟨A.codRestrict (StatedSp 2 (ZMod 2)) hSp, θ, fun x s => ?_⟩
  show Multiplicative.toAdd (θ ((x : MulAut S) s)) =
    ((A x : GL Sp4Inf.I4 (ZMod 2)) : Matrix _ _ (ZMod 2)) *ᵥ Multiplicative.toAdd (θ s)
  rw [hAapp, ofAdd_toAdd, MulEquiv.symm_apply_apply]

end CFSG.Quasithin.MS93.S36E
