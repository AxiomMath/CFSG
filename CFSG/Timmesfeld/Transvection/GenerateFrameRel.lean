module

public import CFSG.Timmesfeld.Transvection.GenerateFrame
public import CFSG.Timmesfeld.Transvection.RankThreeNormCoords
public import CFSG.Timmesfeld.Transvection.RelBuildSU

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection.Pres
open scoped commutatorElement

variable {H : Type*} [Group H] {r : ℕ} {Δ : Set (Subgroup H)} {P Q : Fin r → Subgroup H}

namespace FrameCoords

variable {K : Type*} [Field K] (C : FrameCoords K P Q) (hF : IsFrame Δ P Q) (hΔ : IsRootClass Δ)
  {F : Type*} [Field F] {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c) {ι : K →+* F}
  {β : Fin r → Fin r → F → H}
  (hpair : ∀ i j : Fin r, i < j →
    PairRelations σ ι Δ (P i) (Q i) (P j) (Q j) (C.p i) (C.p j) (C.w i) (C.w j) (C.h i) (C.h j)
      (β i j))
include hF hΔ hσ hpair

theorem family_inl_inr_mem {i j : Fin r} (hij : i ≠ j) (s : F) :
    RelBuild.family σ β C.w (.inl j) (.inr i) s ∈ shortRootGroup Δ (Q i) (P i) (P j) (Q j) := by
  have h := C.family_mem hF hΔ hσ hpair (a := .inl j) (b := .inr i) (by simpa using hij.symm) s
  rwa [shortRootGroup_comm] at h

theorem exists_family_inl_inr_eq {i j : Fin r} (hij : i ≠ j) {g : H}
    (hg : g ∈ shortRootGroup Δ (Q i) (P i) (P j) (Q j)) :
    ∃ s, RelBuild.family σ β C.w (.inl j) (.inr i) s = g := by
  rw [shortRootGroup_comm] at hg
  exact (C.mem_shortRootGroup_iff_family hF hΔ (fun i j h => (hpair i j h).mem_iff) hσ
    (a := .inl j) (b := .inr i) (by simpa using hij.symm) g).1 hg

theorem family_inl_inl_mem {i j : Fin r} (hij : i ≠ j) (s : F) :
    RelBuild.family σ β C.w (.inl j) (.inl i) s ∈ shortRootGroup Δ (P i) (Q i) (P j) (Q j) := by
  have h := C.family_mem hF hΔ hσ hpair (a := .inl j) (b := .inl i) (by simpa using hij.symm) s
  rwa [shortRootGroup_comm] at h

end FrameCoords

open CFSG.Timmesfeld.ARS.NaturalModule CFSG.Timmesfeld.RankOne

namespace IsMaxFrame

variable [Finite H] (hfr : IsMaxFrame Δ P Q) (hΔ : IsTransvectionClass Δ)
  (hiso : NoIsolated Δ) (hpts : PointsDetermined Δ) (hml : MeetsLines Δ)
  (hq : ∀ l, 4 ≤ Nat.card (P l)) {n : ℕ} (φ : ∀ l, SL2Coords (P l) (Q l) n)
  {μ : (GaloisField 2 n)ˣ} (hμ1 : μ ≠ 1)
include hfr hΔ hiso hpts hml hq hμ1

theorem exists_spRelations_hasFrameImages {β : Fin r → Fin r → GaloisField 2 n → H}
    (hpair : ∀ i j : Fin r, i < j →
      PairRelations (RingEquiv.refl _) (RingHom.id _) Δ (P i) (Q i) (P j) (Q j)
        (fun t => (φ i).elt (lowerElt _ t)) (fun t => (φ j).elt (lowerElt _ t))
        ((φ i).elt (weylElt _)) ((φ j).elt (weylElt _)) (φ i).torusElt (φ j).torusElt
        (β i j)) :
    ∃ R : SpRelations r (GaloisField 2 n) H, R.HasFrameImages Δ P Q := by
  set C := FrameCoords.ofSL2Coords φ with hC
  have hF := hfr.toIsFrame
  have hpair' : ∀ i j : Fin r, i < j → PairRelations (RingEquiv.refl _) (RingHom.id _) Δ (P i)
      (Q i) (P j) (Q j) (C.p i) (C.p j) (C.w i) (C.w j) (C.h i) (C.h j) (β i j) := hpair
  refine C.exists_spRelations_hasFrameImages hF hΔ.root hpair' fun i j k hij hjk hik s t => ?_
  have hσ : ∀ c : GaloisField 2 n, (RingEquiv.refl _) ((RingEquiv.refl _) c) = c := fun _ => rfl
  refine hfr.exists_commutator_eq_sq_mul hΔ hiso hpts hml hq φ hμ1 (ξL := C.long)
    (fun i j hij s => C.family_inl_inr_mem hF hΔ.root hσ hpair' hij s)
    (fun i j hij g hg => C.exists_family_inl_inr_eq hF hΔ.root hσ hpair' hij hg)
    (fun i j hij s => C.family_inl_inl_mem hF hΔ.root hσ hpair' hij s)
    (fun l c => C.long_mem (.inl l) c) (fun l => C.long_injective (.inl l))
    (fun i j hij s t => ?_) hij hjk hik s t
  have h := C.shortLong_family hσ (ι := RingHom.id _) (fun c => ⟨fun _ => ⟨c, rfl⟩, fun _ => rfl⟩)
    (L := C.long) (fun _ _ => rfl) hpair' hij s t rfl
  rwa [RingEquiv.refl_apply, ← pow_two] at h

theorem exists_suRelations_hasFrameImages {F : Type*} [Field F] [Finite F] [CharP F 2]
    {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c) (hne : ∃ c, σ c ≠ c) {ι : GaloisField 2 n →+* F}
    (hι : ∀ c, σ c = c ↔ ∃ m, ι m = c) {β : Fin r → Fin r → F → H}
    (hpair : ∀ i j : Fin r, i < j →
      PairRelations σ ι Δ (P i) (Q i) (P j) (Q j)
        (fun t => (φ i).elt (lowerElt _ t)) (fun t => (φ j).elt (lowerElt _ t))
        ((φ i).elt (weylElt _)) ((φ j).elt (weylElt _)) (φ i).torusElt (φ j).torusElt
        (β i j)) :
    ∃ R : SURelations r σ H, R.HasFrameImages Δ P Q := by
  set C := FrameCoords.ofSL2Coords φ with hC
  have hF := hfr.toIsFrame
  have hpair' : ∀ i j : Fin r, i < j → PairRelations σ ι Δ (P i) (Q i) (P j) (Q j) (C.p i)
      (C.p j) (C.w i) (C.w j) (C.h i) (C.h j) (β i j) := hpair
  set L : Fin r ⊕ Fin r → F → H := fun a c => C.long a (Function.invFun ι c) with hLdef
  have hL : ∀ a m, L a (ι m) = C.long a m := fun a m => by
    simp only [hLdef, Function.leftInverse_invFun ι.injective m]
  have hinjL : ∀ (a : Fin r ⊕ Fin r) (s t : F), σ s = s → σ t = t → L a s = L a t → s = t := by
    intro a s t hs ht h
    obtain ⟨m, rfl⟩ := (hι s).1 hs
    obtain ⟨m', rfl⟩ := (hι t).1 ht
    rw [hL, hL] at h
    rw [C.long_injective a h]
  set Pre := C.toPreRelations hF hΔ.root hσ hι hL hpair' with hPre
  have hD4 := fun {i j k : Fin r} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (s t : F) =>
    hfr.exists_commutator_eq_norm_mul hΔ hiso hpts hml hq φ hμ1 hσ
      (ξ := RelBuild.family σ β C.w) (ξL := L)
      (fun i j hij s => C.family_inl_inr_mem hF hΔ.root hσ hpair' hij s)
      (fun i j hij g hg => C.exists_family_inl_inr_eq hF hΔ.root hσ hpair' hij hg)
      (fun i j hij s => C.family_inl_inl_mem hF hΔ.root hσ hpair' hij s)
      (fun l c hc => C.L_mem hι hL (.inl l) hc) (fun l => hinjL (.inl l))
      (fun i j hij s t ht => C.shortLong_family hσ hι hL hpair' hij s t ht) hij hjk hik s t
  let PreSU : PreSURelations r σ H :=
    { Pre with
      inj := fun _ _ hab => RelBuild.family_injective (fun i j h => (hpair' i j h).injective) hab
      injL := hinjL
      short := fun _ _ _ hij hjk hik s t => hD4 hij hjk hik s t
      shortSMul := fun _ _ _ hij hjk hik _ _ _ _ hc hu =>
        RankThree.shortSMul_of_torus (h := C.h) (fun c hc => (hι c).1 hc)
          (fun i j hij => Pre.map_zero (a := .inl j) (b := .inr i) (by simpa using hij.symm))
          (fun i j hij c s => C.torus_family_left hF hι hpair' hij c s)
          (fun i j hij c s => C.torus_family_right hF hι hpair' hij c s)
          (fun i j k hij hik hjk c s => C.torus_family_other hF hΔ.root hσ hpair'
            (a := .inl j) (b := .inr i) (by simpa using hij.symm) (by simpa using hjk)
            (by simpa using hik) c s)
          hij hjk hik hc hu }
  obtain ⟨R, hRL, hRξ⟩ := PreSU.exists_suRelations hσ hne
  exact ⟨R, C.hasFrameImages_of_eq hF hΔ.root hσ hι hL hpair' R hRL hRξ⟩

end IsMaxFrame

end CFSG.Timmesfeld.Transvection
