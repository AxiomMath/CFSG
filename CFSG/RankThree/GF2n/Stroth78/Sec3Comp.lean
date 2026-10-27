module

public import CFSG.RankThree.GF2n.Stroth78.Sec3TypeA
public import CFSG.Timmesfeld.ComponentsInvariant
public import CFSG.GroupTheory.OddOrderClosure

import CFSG.RankThree.GF2n.Stroth78.Sec2Six
import CFSG.RankThree.GF2n.Stroth78.Sec2Five
import CFSG.GroupTheory.PCore.NormalPCoreOf
import CFSG.LargeExtraspecial.AS35ZSDefs

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions Module
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

noncomputable abbrev rhoLin (S : Setting z E F) (x : Hbar z) :
    Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S) :=
  (rhoBar S x : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))

theorem rhoLin_mul (S : Setting z E F) (x y : Hbar z) :
    rhoLin S (x * y) = rhoLin S x * rhoLin S y := by
  rw [rhoLin, rhoLin, rhoLin, map_mul, Subgroup.coe_mul]

theorem rhoLin_inv (S : Setting z E F) (x : Hbar z) :
    rhoLin S x⁻¹ = (rhoLin S x)⁻¹ := by
  rw [rhoLin, rhoLin, map_inv, Subgroup.coe_inv]

theorem rhoLin_conj (S : Setting z E F) (ℓ x : Hbar z) :
    rhoLin S (ℓ * x * ℓ⁻¹) = rhoLin S ℓ * rhoLin S x * (rhoLin S ℓ)⁻¹ := by
  rw [rhoLin_mul, rhoLin_mul, rhoLin_inv]

theorem orderOf_rhoLin (S : Setting z E F) (x : Hbar z) :
    orderOf (rhoLin S x) = orderOf x :=
  orderOf_rhoBar S x

theorem rhoLin_injective (S : Setting z E F) : Function.Injective (rhoLin S) :=
  fun _ _ hxy => rhoBar_injective S (Subtype.ext hxy)

theorem commute_closure_Eset_diff_ncComp (S : Setting z E F) (a : G) {β : Hbar z}
    (hβ : β ∈ A2set S) :
    ∀ x ∈ Subgroup.closure (Eset S a \ ncComp (A2set S) β),
    ∀ y ∈ Subgroup.closure (ncComp (A2set S) β), x * y = y * x := by
  have hgen : ∀ e ∈ Eset S a \ ncComp (A2set S) β,
      e ∈ Subgroup.centralizer
        (Subgroup.closure (ncComp (A2set S) β) : Set (Hbar z)) := by
    intro e he
    have heD : e ∈ A2set S := Eset_subset_A2set S a he.1
    have hcomm := CFSG.Timmesfeld.commute_closure_ncComp (D := A2set S) hβ heD he.2
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact hcomm y hy e (Subgroup.subset_closure (CFSG.Timmesfeld.mem_ncComp_self _ e))
  have hle : Subgroup.closure (Eset S a \ ncComp (A2set S) β) ≤
      Subgroup.centralizer (Subgroup.closure (ncComp (A2set S) β) : Set (Hbar z)) := by
    rw [Subgroup.closure_le]
    exact hgen
  intro x hx y hy
  exact (Subgroup.mem_centralizer_iff.mp (hle hx) y hy).symm

theorem conj_mem_Eset_diff_ncComp (S : Setting z E F) (a : G) {β ℓ : Hbar z}
    (hℓβ : ℓ * β = β * ℓ) {x : Hbar z} (hx : x ∈ Eset S a \ ncComp (A2set S) β) :
    ℓ * x * ℓ⁻¹ ∈ Eset S a \ ncComp (A2set S) β := by
  refine ⟨Eset_conj_mem S a hx.1 ℓ, ?_⟩
  intro hconj
  have himg := CFSG.Timmesfeld.ncComp_conj (D := A2set S)
    (fun g y hy => conj_mem_A2set S g hy) ℓ β
  have hfix : ℓ * β * ℓ⁻¹ = β := by
    rw [hℓβ, mul_assoc, mul_inv_cancel, mul_one]
  rw [hfix] at himg
  have hconj' : ℓ * x * ℓ⁻¹ ∈ (fun y => ℓ * y * ℓ⁻¹) '' ncComp (A2set S) β := by
    rw [← himg]
    exact hconj
  obtain ⟨y, hy, hxy⟩ := hconj'
  apply hx.2
  have hyx : y = x := (MulAut.conj ℓ).injective (by
    simpa [MulAut.conj_apply] using hxy)
  rwa [hyx.symm]

theorem conj_mem_closure_Eset_diff_ncComp (S : Setting z E F) (a : G) {β ℓ : Hbar z}
    (hℓβ : ℓ * β = β * ℓ) {x : Hbar z}
    (hx : x ∈ Subgroup.closure (Eset S a \ ncComp (A2set S) β)) :
    ℓ * x * ℓ⁻¹ ∈ Subgroup.closure (Eset S a \ ncComp (A2set S) β) := by
  induction hx using Subgroup.closure_induction with
  | mem y hy => exact Subgroup.subset_closure (conj_mem_Eset_diff_ncComp S a hℓβ hy)
  | one => simp
  | mul x y _ _ ihx ihy =>
      have h : ℓ * (x * y) * ℓ⁻¹ = (ℓ * x * ℓ⁻¹) * (ℓ * y * ℓ⁻¹) := by group
      rw [h]
      exact Subgroup.mul_mem _ ihx ihy
  | inv x _ ihx =>
      have h : ℓ * x⁻¹ * ℓ⁻¹ = (ℓ * x * ℓ⁻¹)⁻¹ := by group
      rw [h]
      exact Subgroup.inv_mem _ ihx

theorem rhoLin_mem_commSpace_of_commute (S : Setting z E F) {β ℓ : Hbar z}
    (hℓβ : ℓ * β = β * ℓ) {w : Additive (QbarOf S)} (hw : w ∈ commSpace (rhoLin S β)) :
    rhoLin S ℓ w ∈ commSpace (rhoLin S β) := by
  have hmul : ∀ u v : Hbar z, rhoLin S (u * v) = rhoLin S u * rhoLin S v := by
    intro u v
    rw [rhoLin, rhoLin, rhoLin, map_mul, Subgroup.coe_mul]
  have hρ : rhoLin S ℓ * rhoLin S β = rhoLin S β * rhoLin S ℓ := by
    calc
      rhoLin S ℓ * rhoLin S β = rhoLin S (ℓ * β) := (hmul ℓ β).symm
      _ = rhoLin S (β * ℓ) := by rw [hℓβ]
      _ = rhoLin S β * rhoLin S ℓ := hmul β ℓ
  exact CFSG.LargeExtraspecial.AS35ZS.apply_mem_commSpace_of_commute hρ hw

theorem conj_mem_fixer_of_mapsTo (S : Setting z E F) {β y k : Hbar z}
    (hy : ∀ w ∈ commSpace (rhoLin S β), rhoLin S y w ∈ commSpace (rhoLin S β))
    (hyi : ∀ w ∈ commSpace (rhoLin S β), rhoLin S y⁻¹ w ∈ commSpace (rhoLin S β))
    (hk : ∀ w ∈ commSpace (rhoLin S β), rhoLin S k w = w) :
    ∀ w ∈ commSpace (rhoLin S β), rhoLin S (y * k * y⁻¹) w = w := by
  intro w hw
  have hconj : rhoLin S (y * k * y⁻¹) =
      rhoLin S y * rhoLin S k * rhoLin S y⁻¹ := by
    rw [rhoLin, rhoLin, rhoLin, rhoLin, map_mul, map_mul, map_inv,
      Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hconj]
  simp only [LinearEquiv.mul_apply]
  rw [hk _ (hyi w hw)]
  have hinv : rhoLin S y⁻¹ = (rhoLin S y)⁻¹ := by
    rw [rhoLin, rhoLin, map_inv, Subgroup.coe_inv]
  rw [hinv]
  simp

@[expose] noncomputable def commSpaceFixer (S : Setting z E F) (β : Hbar z) :
    Subgroup (Hbar z) where
  carrier := {x | ∀ w ∈ commSpace (rhoLin S β), rhoLin S x w = w}
  one_mem' := by
    intro w _
    simp [rhoLin]
  mul_mem' := by
    intro x y hx hy w hw
    rw [rhoLin_mul, LinearEquiv.mul_apply, hy w hw, hx w hw]
  inv_mem' := by
    intro x hx w hw
    rw [rhoLin_inv]
    calc (rhoLin S x)⁻¹ w = (rhoLin S x)⁻¹ (rhoLin S x w) := by rw [hx w hw]
      _ = w := by simp

theorem mem_commSpaceFixer (S : Setting z E F) (β : Hbar z) {x : Hbar z} :
    x ∈ commSpaceFixer S β ↔ ∀ w ∈ commSpace (rhoLin S β), rhoLin S x w = w :=
  Iff.rfl

@[expose] noncomputable def kernelTwo (S : Setting z E F) (a : G) (β : Hbar z) :
    Subgroup (Hbar z) :=
  Subgroup.closure (Eset S a \ ncComp (A2set S) β) ⊓ commSpaceFixer S β

theorem mem_kernelTwo (S : Setting z E F) (a : G) (β : Hbar z) {x : Hbar z} :
    x ∈ kernelTwo S a β ↔ x ∈ Subgroup.closure (Eset S a \ ncComp (A2set S) β) ∧
      ∀ w ∈ commSpace (rhoLin S β), rhoLin S x w = w := by
  simp [kernelTwo, mem_commSpaceFixer]

theorem rhoBar_mem_commSpace_of_mem_closure_Eset_diff (S : Setting z E F) (a : G)
    {β : Hbar z} (hβ : β ∈ A2set S) {x : Hbar z}
    (hx : x ∈ Subgroup.closure (Eset S a \ ncComp (A2set S) β))
    {w : Additive (QbarOf S)} (hw : w ∈ commSpace (rhoLin S β)) :
    rhoLin S x w ∈ commSpace (rhoLin S β) := by
  have hxβ : x * β = β * x :=
    commute_closure_Eset_diff_ncComp S a hβ x hx β
      (Subgroup.subset_closure (CFSG.Timmesfeld.mem_ncComp_self _ β))
  exact rhoLin_mem_commSpace_of_commute S hxβ hw

theorem mem_normalizer_kernelTwo_of_mem_closure_ncComp (S : Setting z E F) (a : G)
    {β : Hbar z} (hβ : β ∈ A2set S) {x : Hbar z}
    (hx : x ∈ Subgroup.closure (ncComp (A2set S) β)) :
    x ∈ Subgroup.normalizer (kernelTwo S a β : Set (Hbar z)) := by
  have hforward : ∀ y ∈ Subgroup.closure (ncComp (A2set S) β),
      ∀ k ∈ kernelTwo S a β, y * k * y⁻¹ ∈ kernelTwo S a β := by
    intro y hy k hk
    have hcomm : k * y = y * k :=
      commute_closure_Eset_diff_ncComp S a hβ k hk.1 y hy
    have hyk : y * k * y⁻¹ = k := by
      rw [← hcomm]
      simp
    rw [hyk]
    exact hk
  refine Subgroup.mem_normalizer_iff.mpr fun k => ⟨?_, ?_⟩
  · intro hk
    exact hforward x hx k hk
  · intro hk
    have h := hforward x⁻¹ (Subgroup.inv_mem _ hx) (x * k * x⁻¹) hk
    simpa [mul_assoc] using h

theorem mem_normalizer_kernelTwo_of_mem_closure_Eset_diff (S : Setting z E F) (a : G)
    {β : Hbar z} (hβ : β ∈ A2set S) {x : Hbar z}
    (hx : x ∈ Subgroup.closure (Eset S a \ ncComp (A2set S) β)) :
    x ∈ Subgroup.normalizer (kernelTwo S a β : Set (Hbar z)) := by
  have hforward : ∀ y ∈ Subgroup.closure (Eset S a \ ncComp (A2set S) β),
      ∀ k ∈ kernelTwo S a β, y * k * y⁻¹ ∈ kernelTwo S a β := by
    intro y hy k hk
    refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hy hk.1) (Subgroup.inv_mem _ hy), ?_⟩
    exact (mem_commSpaceFixer S β).mpr <| conj_mem_fixer_of_mapsTo S
      (fun w hw => rhoBar_mem_commSpace_of_mem_closure_Eset_diff S a hβ hy hw)
      (fun w hw => rhoBar_mem_commSpace_of_mem_closure_Eset_diff S a hβ
        (Subgroup.inv_mem _ hy) hw) ((mem_commSpaceFixer S β).mp hk.2)
  refine Subgroup.mem_normalizer_iff.mpr fun k => ⟨?_, ?_⟩
  · intro hk
    exact hforward x hx k hk
  · intro hk
    have h := hforward x⁻¹ (Subgroup.inv_mem _ hx) (x * k * x⁻¹) hk
    simpa [mul_assoc] using h

theorem Xsub_le_normalizer_kernelTwo (S : Setting z E F) (a : G) {β : Hbar z}
    (hβ : β ∈ A2set S) : Xsub S a ≤ Subgroup.normalizer (kernelTwo S a β : Set (Hbar z)) := by
  rw [Xsub, Subgroup.closure_le]
  intro x hxE
  by_cases hxcomp : x ∈ ncComp (A2set S) β
  · exact mem_normalizer_kernelTwo_of_mem_closure_ncComp S a hβ
      (Subgroup.subset_closure hxcomp)
  · exact mem_normalizer_kernelTwo_of_mem_closure_Eset_diff S a hβ
      (Subgroup.subset_closure ⟨hxE, hxcomp⟩)

theorem mem_normalizer_commSpaceFixer (S : Setting z E F) {β ℓ : Hbar z}
    (hℓβ : ℓ * β = β * ℓ) :
    ℓ ∈ Subgroup.normalizer (commSpaceFixer S β : Set (Hbar z)) := by
  have hℓinvβ : ℓ⁻¹ * β = β * ℓ⁻¹ := by
    have h := congrArg (fun t => ℓ⁻¹ * t * ℓ⁻¹) hℓβ
    simpa [mul_assoc] using h.symm
  have hforward : ∀ γ : Hbar z, γ * β = β * γ →
      ∀ k ∈ commSpaceFixer S β, γ * k * γ⁻¹ ∈ commSpaceFixer S β := by
    intro γ hγβ k hk
    have hγinvβ : γ⁻¹ * β = β * γ⁻¹ := by
      have h := congrArg (fun t => γ⁻¹ * t * γ⁻¹) hγβ
      simpa [mul_assoc] using h.symm
    exact (mem_commSpaceFixer S β).mpr <| conj_mem_fixer_of_mapsTo S
      (fun w hw => rhoLin_mem_commSpace_of_commute S hγβ hw)
      (fun w hw => rhoLin_mem_commSpace_of_commute S hγinvβ hw)
      ((mem_commSpaceFixer S β).mp hk)
  refine Subgroup.mem_normalizer_iff.mpr fun k => ⟨?_, ?_⟩
  · intro hk
    exact hforward ℓ hℓβ k hk
  · intro hk
    have h := hforward ℓ⁻¹ hℓinvβ (ℓ * k * ℓ⁻¹) hk
    simpa [mul_assoc] using h

theorem mem_normalizer_kernelTwo_of_commute (S : Setting z E F) (a : G) {β ℓ : Hbar z}
    (hβ : β ∈ A2set S) (hℓβ : ℓ * β = β * ℓ) :
    ℓ ∈ Subgroup.normalizer (kernelTwo S a β : Set (Hbar z)) := by
  have hℓinvβ : ℓ⁻¹ * β = β * ℓ⁻¹ := by
    have h := congrArg (fun t => ℓ⁻¹ * t * ℓ⁻¹) hℓβ
    simpa [mul_assoc] using h.symm
  have hforward : ∀ γ : Hbar z, γ * β = β * γ →
      ∀ k ∈ kernelTwo S a β, γ * k * γ⁻¹ ∈ kernelTwo S a β := by
    intro γ hγβ k hk
    exact ⟨conj_mem_closure_Eset_diff_ncComp S a hγβ hk.1,
      (Subgroup.mem_normalizer_iff.mp (mem_normalizer_commSpaceFixer S hγβ) k).mp hk.2⟩
  refine Subgroup.mem_normalizer_iff.mpr fun k => ⟨?_, ?_⟩
  · intro hk
    exact hforward ℓ hℓβ k hk
  · intro hk
    have h := hforward ℓ⁻¹ hℓinvβ (ℓ * k * ℓ⁻¹) hk
    simpa [mul_assoc] using h

theorem eq_bot_of_le_kernelTwo (S : Setting z E F) (a : G) {β : Hbar z} (hβ : β ∈ A2set S)
    (P : Subgroup (Hbar z)) (hPK : P ≤ kernelTwo S a β) (hP : IsPGroup 2 P)
    (hN : kernelTwo S a β ≤ Subgroup.normalizer (P : Set (Hbar z))) : P = ⊥ := by
  have hKX : kernelTwo S a β ≤ Xsub S a := by
    rw [kernelTwo, Xsub]
    exact inf_le_left.trans (Subgroup.closure_mono fun x hx => hx.1)
  have hPcore : P ≤ CFSG.Open.pCoreOf 2 (kernelTwo S a β) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hPK hN hP
  have hK2X : CFSG.Open.pCoreOf 2 (kernelTwo S a β) ≤
      CFSG.Open.pCoreOf 2 (Xsub S a) :=
    CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 hKX
      (Xsub_le_normalizer_kernelTwo S a hβ)
  have hXtop : CFSG.Open.pCoreOf 2 (Xsub S a) ≤
      CFSG.Open.pCoreOf 2 (⊤ : Subgroup (Hbar z)) :=
    CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 le_top
      (by rw [Subgroup.normalizer_eq_top_iff.mpr (Xsub_normal S a)])
  have htopbot : CFSG.Open.pCoreOf 2 (⊤ : Subgroup (Hbar z)) = ⊥ := by
    have h := CFSG.pCore_map_iso 2 (Subgroup.topEquiv (G := Hbar z))
    rw [pCore_two_Hbar_eq_bot S,
      Subgroup.map_eq_bot_iff_of_injective _ (MulEquiv.injective _)] at h
    simp [CFSG.Open.pCoreOf, h]
  exact eq_bot_iff.mpr (hPcore.trans (hK2X.trans (hXtop.trans (le_of_eq htopbot))))

theorem eq_bot_of_le_oddOrderClosure_kernelTwo (S : Setting z E F) (a : G) {β : Hbar z}
    (hβ : β ∈ A2set S) (P : Subgroup (Hbar z))
    (hPK : P ≤ CFSG.GroupTheory.oddOrderClosure (kernelTwo S a β)) (hP : IsPGroup 2 P)
    (hN : CFSG.GroupTheory.oddOrderClosure (kernelTwo S a β) ≤
      Subgroup.normalizer (P : Set (Hbar z))) : P = ⊥ := by
  have hKX : kernelTwo S a β ≤ Xsub S a := by
    rw [kernelTwo, Xsub]
    exact inf_le_left.trans (Subgroup.closure_mono fun x hx => hx.1)
  have hOK : CFSG.GroupTheory.oddOrderClosure (kernelTwo S a β) ≤ kernelTwo S a β :=
    CFSG.GroupTheory.oddOrderClosure_le _
  have hPcore : P ≤ CFSG.Open.pCoreOf 2
      (CFSG.GroupTheory.oddOrderClosure (kernelTwo S a β)) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hPK hN hP
  have hOX : CFSG.GroupTheory.oddOrderClosure (kernelTwo S a β) ≤ Xsub S a :=
    hOK.trans hKX
  have hXnormO : Xsub S a ≤ Subgroup.normalizer
      (CFSG.GroupTheory.oddOrderClosure (kernelTwo S a β) : Set (Hbar z)) :=
    (Xsub_le_normalizer_kernelTwo S a hβ).trans
      (CFSG.GroupTheory.normalizer_le_normalizer_oddOrderClosure (kernelTwo S a β))
  have hO2X : CFSG.Open.pCoreOf 2
      (CFSG.GroupTheory.oddOrderClosure (kernelTwo S a β)) ≤
      CFSG.Open.pCoreOf 2 (Xsub S a) :=
    CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 hOX hXnormO
  have hXtop : CFSG.Open.pCoreOf 2 (Xsub S a) ≤
      CFSG.Open.pCoreOf 2 (⊤ : Subgroup (Hbar z)) :=
    CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 le_top
      (by rw [Subgroup.normalizer_eq_top_iff.mpr (Xsub_normal S a)])
  have htopbot : CFSG.Open.pCoreOf 2 (⊤ : Subgroup (Hbar z)) = ⊥ := by
    have h := CFSG.pCore_map_iso 2 (Subgroup.topEquiv (G := Hbar z))
    rw [pCore_two_Hbar_eq_bot S,
      Subgroup.map_eq_bot_iff_of_injective _ (MulEquiv.injective _)] at h
    simp [CFSG.Open.pCoreOf, h]
  exact eq_bot_iff.mpr (hPcore.trans (hO2X.trans (hXtop.trans (le_of_eq htopbot))))

end CFSG.RankThree.GF2n.Stroth78
