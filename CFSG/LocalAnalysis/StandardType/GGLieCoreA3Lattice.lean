module

public import CFSG.LocalAnalysis.StandardType.GGLieCoreA3DatumDefs
public import CFSG.LocalAnalysis.StandardType.GGLieCoreA3LatticeDefs
public import CFSG.LocalAnalysis.StandardType.GGLieCoreA3DictTorus

public section

namespace CFSG.StandardType.LieCore

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Open (StatedLieTag)
open Matrix

private lemma ggLieA3Lat_jointChar_ofAdd {τ : Tag} {L : Type} [Field L]
    (a₁ a₂ : Fin τ.rank → Lˣ) (γ : Fin τ.rank → ℤ) :
    jointChar a₁ a₂ (Multiplicative.ofAdd γ) = (rootChar a₁ γ, rootChar a₂ γ) := rfl
private lemma ggLieA3Lat_kernelRoots_eq {τ : Tag} {L : Type} [Field L]
    (a₁ a₂ : Fin τ.rank → Lˣ) (c₁ c₂ : Fin τ.rank → ZMod 3)
    (hd1 : ∀ γ, rootChar a₁ γ = 1 ↔ ggLiePair γ c₁ = 0)
    (hd2 : ∀ γ, rootChar a₂ γ = 1 ↔ ggLiePair γ c₂ = 0) :
    kernelRoots (jointChar a₁ a₂) = a3Ker τ c₁ c₂ := by
  ext γ
  simp only [kernelRoots, Set.mem_setOf_eq, a3Ker, ggLieA3Lat_jointChar_ofAdd,
    Prod.mk_eq_one, hd1 γ, hd2 γ]

private lemma ggLieA3Lat_mem_iff_of_eqvGen {τ : Tag} {M : Type*} [CommGroup M]
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M) {a b : Fin τ.rank → ℤ}
    (h : Relation.EqvGen (fun (u v : Fin τ.rank → ℤ) =>
        u ∈ kernelRoots χ ∧ v ∈ kernelRoots χ ∧
        u ⬝ᵥ (τ.symmetrizedCartan *ᵥ v) ≠ 0) a b) :
    a ∈ kernelRoots χ ↔ b ∈ kernelRoots χ := by
  induction h with
  | rel x y hxy => exact ⟨fun _ => hxy.2.1, fun _ => hxy.1⟩
  | refl x => exact Iff.rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

private lemma ggLieA3Lat_eqvGen_transfer_forward {τ : Tag} {M : Type*} [CommGroup M]
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M) :
    ∀ (a b : kernelRoots χ),
      Relation.EqvGen (fun (u v : kernelRoots χ) =>
        (u : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (v : Fin τ.rank → ℤ)) ≠ 0) a b →
      ∀ (hα : a.1 ∈ kernelRoots χ) (hβ : b.1 ∈ kernelRoots χ),
        Relation.EqvGen (fun (u v : Fin τ.rank → ℤ) =>
          u ∈ kernelRoots χ ∧ v ∈ kernelRoots χ ∧
          u ⬝ᵥ (τ.symmetrizedCartan *ᵥ v) ≠ 0) a.1 b.1 := by
  intro a b h
  refine Relation.EqvGen.rec (motive := fun (x y : kernelRoots χ)
      (_ : Relation.EqvGen (fun (u v : kernelRoots χ) =>
        (u : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (v : Fin τ.rank → ℤ)) ≠ 0) x y) =>
    ∀ (hα : x.1 ∈ kernelRoots χ) (hβ : y.1 ∈ kernelRoots χ),
      Relation.EqvGen (fun (u v : Fin τ.rank → ℤ) =>
        u ∈ kernelRoots χ ∧ v ∈ kernelRoots χ ∧
        u ⬝ᵥ (τ.symmetrizedCartan *ᵥ v) ≠ 0) x.1 y.1) ?_ ?_ ?_ ?_ h
  · intro x y hxy hα hβ
    exact Relation.EqvGen.rel _ _ ⟨hα, hβ, hxy⟩
  · intro x hα hβ
    exact Relation.EqvGen.refl x.1
  · intro x y hxy ih hα hβ
    exact Relation.EqvGen.symm _ _ (ih hβ hα)
  · intro x y z hxy hyz ih1 ih2 hα hβ
    exact Relation.EqvGen.trans _ _ _ (ih1 hα y.2) (ih2 y.2 hβ)

private lemma ggLieA3Lat_eqvGen_transfer_backward {τ : Tag} {M : Type*} [CommGroup M]
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M) :
    ∀ (a b : Fin τ.rank → ℤ),
      Relation.EqvGen (fun (u v : Fin τ.rank → ℤ) =>
        u ∈ kernelRoots χ ∧ v ∈ kernelRoots χ ∧
        u ⬝ᵥ (τ.symmetrizedCartan *ᵥ v) ≠ 0) a b →
      ∀ (hα : a ∈ kernelRoots χ) (hβ : b ∈ kernelRoots χ),
        Relation.EqvGen (fun (u v : kernelRoots χ) =>
          (u : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (v : Fin τ.rank → ℤ)) ≠ 0)
          ⟨a, hα⟩ ⟨b, hβ⟩ := by
  intro a b h
  refine Relation.EqvGen.rec (motive := fun (x y : Fin τ.rank → ℤ)
      (_ : Relation.EqvGen (fun (u v : Fin τ.rank → ℤ) =>
        u ∈ kernelRoots χ ∧ v ∈ kernelRoots χ ∧
        u ⬝ᵥ (τ.symmetrizedCartan *ᵥ v) ≠ 0) x y) =>
    ∀ (hα : x ∈ kernelRoots χ) (hβ : y ∈ kernelRoots χ),
      Relation.EqvGen (fun (u v : kernelRoots χ) =>
        (u : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (v : Fin τ.rank → ℤ)) ≠ 0)
        ⟨x, hα⟩ ⟨y, hβ⟩) ?_ ?_ ?_ ?_ h
  · intro x y hxy hα hβ
    exact Relation.EqvGen.rel _ _ hxy.2.2
  · intro x hα hβ
    exact Relation.EqvGen.refl _
  · intro x y hxy ih hα hβ
    exact Relation.EqvGen.symm _ _ (ih hβ hα)
  · intro x y z hxy hyz ih1 ih2 hα hβ
    have hy : y ∈ kernelRoots χ := (ggLieA3Lat_mem_iff_of_eqvGen χ hxy).1 hα
    exact Relation.EqvGen.trans _ _ _ (ih1 hα hy) (ih2 hy hβ)

private lemma ggLieA3Lat_eqvGen_transfer {τ : Tag} {M : Type*} [CommGroup M]
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M) {α β : Fin τ.rank → ℤ}
    (hα : α ∈ kernelRoots χ) (hβ : β ∈ kernelRoots χ) :
    Relation.EqvGen (fun (u v : kernelRoots χ) =>
        (u : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (v : Fin τ.rank → ℤ)) ≠ 0)
        ⟨α, hα⟩ ⟨β, hβ⟩ ↔
      Relation.EqvGen (fun (u v : Fin τ.rank → ℤ) =>
        u ∈ kernelRoots χ ∧ v ∈ kernelRoots χ ∧
        u ⬝ᵥ (τ.symmetrizedCartan *ᵥ v) ≠ 0) α β := by
  constructor
  · intro h
    exact ggLieA3Lat_eqvGen_transfer_forward χ ⟨α, hα⟩ ⟨β, hβ⟩ h hα hβ
  · intro h
    exact ggLieA3Lat_eqvGen_transfer_backward χ α β h hα hβ

private lemma ggLieA3Lat_componentRoots_eq_a3Comp {τ : Tag} {L : Type} [Field L]
    (a₁ a₂ : Fin τ.rank → Lˣ) (c₁ c₂ : Fin τ.rank → ZMod 3)
    (hK : kernelRoots (jointChar a₁ a₂) = a3Ker τ c₁ c₂)
    (i : KernelComponent (jointChar a₁ a₂)) (m : Fin τ.rank → ℤ)
    (hm : m ∈ componentRoots (jointChar a₁ a₂) i) :
    componentRoots (jointChar a₁ a₂) i = a3Comp τ c₁ c₂ m := by
  obtain ⟨hmk, hmi⟩ := hm
  ext α
  constructor
  · intro hα
    obtain ⟨hαk, hαi⟩ := hα
    have hαk' : α ∈ a3Ker τ c₁ c₂ := by rwa [hK] at hαk
    refine ⟨hαk', ?_⟩
    have hsub : (kernelRootSetoid (jointChar a₁ a₂)).r ⟨α, hαk⟩ ⟨m, hmk⟩ :=
      Quotient.exact (hαi.trans hmi.symm)
    have hamb := (ggLieA3Lat_eqvGen_transfer (jointChar a₁ a₂) hαk hmk).1 hsub
    rw [hK] at hamb
    exact Relation.EqvGen.symm _ _ hamb
  · intro hα
    obtain ⟨hαk', hEqv⟩ := hα
    have hαk : α ∈ kernelRoots (jointChar a₁ a₂) := by rwa [← hK] at hαk'
    refine ⟨hαk, ?_⟩
    have hEqv' : Relation.EqvGen (fun (u v : Fin τ.rank → ℤ) =>
        u ∈ kernelRoots (jointChar a₁ a₂) ∧ v ∈ kernelRoots (jointChar a₁ a₂) ∧
        u ⬝ᵥ (τ.symmetrizedCartan *ᵥ v) ≠ 0) α m := by
      rw [← hK] at hEqv
      exact Relation.EqvGen.symm _ _ hEqv
    exact (Quotient.sound
      ((ggLieA3Lat_eqvGen_transfer (jointChar a₁ a₂) hαk hmk).2 hEqv')).trans hmi

theorem ggLieA3LatticeNo_of_spec
    (hF : A3SpecF4) (hE : A3SpecTwE6) : GGLieA3LatticeNo := by
  intro t ht w a₁ a₂ h₃₁ h₃₂ hch₁ hch₂ hcard i hnc himg hin
  obtain ⟨c₁, c₂, hd1, hd2, hd3, hd4, hd5⟩ := ggLie_torus_dictionary a₁ a₂ h₃₁ h₃₂
  have hK : kernelRoots (jointChar a₁ a₂) = a3Ker (langTag t) c₁ c₂ :=
    ggLieA3Lat_kernelRoots_eq a₁ a₂ c₁ c₂ hd1 hd2
  have hindep : ∀ s t : ZMod 3, s • c₁ + t • c₂ = 0 → s = 0 ∧ t = 0 :=
    hd5.mp hcard
  rcases ht with rfl | rfl
  · have hne : (componentRoots (jointChar a₁ a₂) i).Nonempty :=
      Set.nonempty_of_ncard_ne_zero (by rw [hnc]; norm_num)
    obtain ⟨m, hm⟩ := hne
    have hcomp := ggLieA3Lat_componentRoots_eq_a3Comp a₁ a₂ c₁ c₂ hK i m hm
    have hmk : m ∈ a3Ker (langTag .F4) c₁ c₂ := by
      rw [← hK]
      exact hm.1
    have hF' := hF c₁ c₂ hindep m hmk
    rw [← hcomp] at hF'
    exact hF' hnc
  · have hne : (componentRoots (jointChar a₁ a₂) i).Nonempty :=
      Set.nonempty_of_ncard_ne_zero (by rw [hnc]; norm_num)
    obtain ⟨m, hm⟩ := hne
    have hcomp := ggLieA3Lat_componentRoots_eq_a3Comp a₁ a₂ c₁ c₂ hK i m hm
    have hmk : m ∈ a3Ker (langTag .twistedE6) c₁ c₂ := by
      rw [← hK]
      exact hm.1
    have hlang₁ : ∀ γ, IsRoot (langTag .twistedE6) γ →
        ggLiePair (w • ggGraphLat .twistedE6 γ) c₁ = 2 * ggLiePair γ c₁ :=
      fun γ hγ => (hd3 γ (w • ggGraphLat .twistedE6 γ)).1 (hch₁ γ hγ)
    have hlang₂ : ∀ γ, IsRoot (langTag .twistedE6) γ →
        ggLiePair (w • ggGraphLat .twistedE6 γ) c₂ = 2 * ggLiePair γ c₂ :=
      fun γ hγ => (hd4 γ (w • ggGraphLat .twistedE6 γ)).1 (hch₂ γ hγ)
    have hnc' : (a3Comp (langTag .twistedE6) c₁ c₂ m).ncard = 12 := by
      rw [← hcomp]
      exact hnc
    have himg' : (fun u => w • ggGraphLat .twistedE6 u) ''
        a3Comp (langTag .twistedE6) c₁ c₂ m = a3Comp (langTag .twistedE6) c₁ c₂ m := by
      rw [← hcomp]
      exact himg
    have hin' : twistInner (a3Comp (langTag .twistedE6) c₁ c₂ m)
        (fun u => w • ggGraphLat .twistedE6 u) := by
      rw [← hcomp]
      exact hin
    exact hE w c₁ c₂ hindep hlang₁ hlang₂ m hmk hnc' himg' hin'

end CFSG.StandardType.LieCore
