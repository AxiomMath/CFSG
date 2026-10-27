module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsC
public import CFSG.Quasithin.Background.HPair

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17 (SwapsParabolics)

variable {W : Type} [CommGroup W]

@[expose] def SumOfNatIsoMod (N : Subgroup (MulAut W) → Subgroup W → Subgroup W → Prop)
    (H : Subgroup (MulAut W)) (U Z : Subgroup W) (k : ℕ) : Prop :=
  ∃ I : Fin k → Subgroup W, (∀ i, Z ≤ I i) ∧
    (∀ i, I i ⊓ (Z ⊔ ⨆ (j : Fin k) (_ : j ≠ i), I j) ≤ Z) ∧
    (Z ⊔ ⨆ i, I i) = U ∧ (∀ i, N H (I i) Z) ∧
    ∀ i j, CFSG.Quasithin.H.Pair.IsoMod H (I i) (I j)

theorem pair_isoMod_of_realizesVia_common {D : FFModel}
    {H : Subgroup (MulAut W)} {π : D.Gam →* ↥H} {U V : Subgroup W}
    (hU : D.RealizesVia H U ⊥ π) (hV : D.RealizesVia H V ⊥ π) :
    CFSG.Quasithin.H.Pair.IsoMod H U V := by
  obtain ⟨hπ, -, -, hHU, -, hsecU, -, βU, hβUs, hβUk, hβUe⟩ := hU
  obtain ⟨-, -, -, hHV, -, hsecV, -, βV, hβVs, hβVk, hβVe⟩ := hV
  have hβUi : Function.Injective βU := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have hmem : (u : W) ∈ (⊥ : Subgroup W) := (hβUk u).1 hu
    exact Subtype.ext (by simpa using hmem)
  have hβVi : Function.Injective βV := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have hmem : (u : W) ∈ (⊥ : Subgroup W) := (hβVk u).1 hu
    exact Subtype.ext (by simpa using hmem)
  let βUe : ↥U ≃* (↥D.sec ⧸ D.ker.subgroupOf D.sec) :=
    MulEquiv.ofBijective βU (show Function.Bijective ⇑βU from ⟨hβUi, hβUs⟩)
  let βVe : ↥V ≃* (↥D.sec ⧸ D.ker.subgroupOf D.sec) :=
    MulEquiv.ofBijective βV (show Function.Bijective ⇑βV from ⟨hβVi, hβVs⟩)
  let e : ↥U ≃* ↥V := βUe.trans βVe.symm
  refine ⟨e, ?_⟩
  have he : ∀ u : ↥U, βVe (e u) = βUe u := by
    intro u
    show βVe (βVe.symm (βUe u)) = βUe u
    rw [MulEquiv.apply_symm_apply]
  have he' : ∀ u : ↥U, βV (e u) = βU u := fun u => he u
  intro l hl w hw
  obtain ⟨γ, hγ⟩ := hπ ⟨l, hl⟩
  have hlval : ((π γ : ↥H) : MulAut W) = l := congrArg Subtype.val hγ
  subst hlval
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (βU w)
  have hUstep : βU ⟨((π γ : ↥H) : MulAut W) (w : W), hw⟩ =
      QuotientGroup.mk ⟨D.act γ (m : D.Amb), hsecU γ m m.2⟩ :=
    hβUe γ w m hw (hsecU γ m m.2) hm.symm
  have hVmem : ((π γ : ↥H) : MulAut W) ((e w : ↥V) : W) ∈ V := hHV (π γ) _ (e w).2
  have hVstep : βV ⟨((π γ : ↥H) : MulAut W) ((e w : ↥V) : W), hVmem⟩ =
      QuotientGroup.mk ⟨D.act γ (m : D.Amb), hsecV γ m m.2⟩ := by
    refine hβVe γ (e w) m hVmem (hsecV γ m m.2) ?_
    rw [he' w]
    exact hm.symm
  have hEq : e ⟨((π γ : ↥H) : MulAut W) (w : W), hw⟩ =
      ⟨((π γ : ↥H) : MulAut W) ((e w : ↥V) : W), hVmem⟩ := by
    apply hβVi
    show βV (e ⟨((π γ : ↥H) : MulAut W) (w : W), hw⟩) = βV _
    rw [he', hUstep, hVstep]
  exact congrArg Subtype.val hEq

theorem sumOfNatIsoMod_natSpn_of_sumOfNatVia {K : Type} [Field K] [Finite K]
    {H : Subgroup (MulAut W)} {π : ↥(StatedSp 2 K) →* ↥H} {n : ℕ}
    (hK : Nat.card K = 2 ^ n)
    (h : SumOfNatVia (FFModel.nat (StatedSp 2 K)) H ⊤ ⊥ 2 π) :
    SumOfNatIsoMod (fun H U Z => NatSpn H U Z 4 n) H ⊤ ⊥ 2 := by
  obtain ⟨I, hZ, hind, hsup, hreal⟩ := h
  refine ⟨I, hZ, hind, hsup, fun i => ?_, fun i j => ?_⟩
  · refine ⟨by decide, K, inferInstance, inferInstance, hK, ?_⟩
    exact ⟨π, hreal i⟩
  · exact pair_isoMod_of_realizesVia_common (hreal i) (hreal j)

@[expose] def K_Sp4TwoNat_noSwap : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (X Y : Subgroup (MulAut W)) (n : ℕ),
      Y ≤ Subgroup.normalizer (X : Set (MulAut W)) →
      IsSylowIn 2 (Y ⊓ X) X →
      IsSp4 ↥X n →
      SumOfNatIsoMod (fun H U Z => NatSpn H U Z 4 n) X ⊤ ⊥ 2 →
      ¬ SwapsParabolics Y X

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
