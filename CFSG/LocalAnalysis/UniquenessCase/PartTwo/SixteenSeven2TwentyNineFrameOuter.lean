module

public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsSquareProd
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierCyclicCentralFactorOuter
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyHAut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.ComponentClassification.AutL2Facts
open CFSG.EvenSporadicStandard.TwoHS

private theorem s16c167_frame_center_eq_bot {S : Type*} [Group S] (hS : SimpleCentreless S) :
    Subgroup.center S = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  exact hS.center z fun g => (Subgroup.mem_center_iff.mp hz g).symm

private theorem s16c167_frame_inner_le_presSub {S : Type*} [Group S] [Finite S] :
    inner (S × S) ≤ presSub S := by
  rintro _ ⟨g, rfl⟩
  exact ⟨fun s => by simp [MulAut.conj_apply], fun t => by simp [MulAut.conj_apply]⟩

private theorem s16c167_frame_mem_inner_of_fstHom_sndHom {S : Type*} [Group S] [Finite S]
    (φ : presSub S) (h1 : fstHom φ ∈ inner S) (h2 : sndHom φ ∈ inner S) :
    (φ : MulAut (S × S)) ∈ inner (S × S) := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  refine ⟨(a, b), MulEquiv.ext fun x => ?_⟩
  obtain ⟨s, t⟩ := x
  rw [presSub_apply, ← ha, ← hb]
  simp [MulAut.conj_apply]

private theorem s16c167_frame_isPerfect_prod {A B : Type*} [Group A] [Group B]
    (hA : Group.IsPerfect A) (hB : Group.IsPerfect B) : Group.IsPerfect (A × B) := by
  rw [Group.isPerfect_def, eq_top_iff]
  rintro ⟨a, b⟩ -
  have h1 : (a, (1 : B)) ∈ commutator (A × B) := by
    have ha : a ∈ commutator A := by rw [hA.commutator_eq_top]; exact Subgroup.mem_top a
    have := Subgroup.mem_map_of_mem (MonoidHom.inl A B) ha
    rw [_root_.commutator_def, Subgroup.map_commutator] at this
    refine (Subgroup.commutator_mono le_top le_top) this
  have h2 : ((1 : A), b) ∈ commutator (A × B) := by
    have hb : b ∈ commutator B := by rw [hB.commutator_eq_top]; exact Subgroup.mem_top b
    have := Subgroup.mem_map_of_mem (MonoidHom.inr A B) hb
    rw [_root_.commutator_def, Subgroup.map_commutator] at this
    refine (Subgroup.commutator_mono le_top le_top) this
  have := mul_mem h1 h2
  simpa using this

theorem s16c167_frame_outer_square_solvable {S : Type} [Group S] [Finite S]
    (hS : SimpleCentreless S) (hout : Group.IsSolvable (Outer S)) :
    Group.IsSolvable (Outer (S × S)) := by
  haveI : Nontrivial S := ⟨⟨hS.nontriv.choose, 1, hS.nontriv.choose_spec⟩⟩
  haveI : IsSimpleGroup S := ⟨fun N hN => hS.simple N hN⟩
  have hZ : Subgroup.center S = ⊥ := s16c167_frame_center_eq_bot hS
  haveI : Group.IsSolvable (Outer S) := hout
  let ψ : ↥(presSub S) →* Outer S × Outer S :=
    ((QuotientGroup.mk' (inner S)).comp fstHom).prod
      ((QuotientGroup.mk' (inner S)).comp sndHom)
  let θ : ↥(presSub S) →* Outer (S × S) :=
    (QuotientGroup.mk' (inner (S × S))).comp (presSub S).subtype
  have hker : ψ.ker ≤ θ.ker := by
    intro φ hφ
    rw [MonoidHom.mem_ker] at hφ ⊢
    have h1 : fstHom φ ∈ inner S := by
      have h : (QuotientGroup.mk' (inner S) (fstHom φ) : Outer S) = 1 :=
        (Prod.ext_iff.mp hφ).1
      exact (QuotientGroup.eq_one_iff (fstHom φ)).mp (by simpa [QuotientGroup.mk'_apply] using h)
    have h2 : sndHom φ ∈ inner S := by
      have h : (QuotientGroup.mk' (inner S) (sndHom φ) : Outer S) = 1 :=
        (Prod.ext_iff.mp hφ).2
      exact (QuotientGroup.eq_one_iff (sndHom φ)).mp (by simpa [QuotientGroup.mk'_apply] using h)
    have hφ' : (φ : MulAut (S × S)) ∈ inner (S × S) :=
      s16c167_frame_mem_inner_of_fstHom_sndHom φ h1 h2
    exact (QuotientGroup.eq_one_iff (φ : MulAut (S × S))).mpr hφ'
  have hker' : (ψ.rangeRestrict).ker ≤ θ.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hker
  let χ : ↥ψ.range →* Outer (S × S) :=
    (MonoidHom.liftOfSurjective ψ.rangeRestrict ψ.rangeRestrict_surjective) ⟨θ, hker'⟩
  have hχ : ∀ x : ↥(presSub S), χ (ψ.rangeRestrict x) = θ x := by
    intro x
    have h := MonoidHom.liftOfRightInverse_comp_apply
      (f := ψ.rangeRestrict)
      (f_inv := Function.surjInv ψ.rangeRestrict_surjective)
      (Function.rightInverse_surjInv ψ.rangeRestrict_surjective) ⟨θ, hker'⟩ x
    simpa [χ] using h
  have hphi : inner (S × S) ≤ (SAFyHAut.phi hZ).ker := by
    intro φ hφ
    rw [MonoidHom.mem_ker, SAFyHAut.phi_eq_one_iff hZ]
    exact (s16c167_frame_inner_le_presSub hφ).1
  let Φ : Outer (S × S) →* Multiplicative (ZMod 2) :=
    QuotientGroup.lift (inner (S × S)) (SAFyHAut.phi hZ) hphi
  haveI : Group.IsSolvable ↥ψ.range := inferInstance
  haveI : Group.IsSolvable (Multiplicative (ZMod 2)) := inferInstance
  refine Group.isSolvable_of_ker_le_range χ Φ ?_
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  obtain ⟨α, rfl⟩ := QuotientGroup.mk'_surjective (inner (S × S)) x
  have hphiα : SAFyHAut.phi hZ α = 1 := hx
  have hpres : ∀ s : S, (α (s, 1)).2 = 1 := (SAFyHAut.phi_eq_one_iff hZ).mp hphiα
  have hα : α ∈ presSub S := ⟨hpres, hS.snd_of_fst hpres⟩
  refine ⟨ψ.rangeRestrict ⟨α, hα⟩, ?_⟩
  rw [hχ ⟨α, hα⟩]
  rfl

theorem s16c167_frame_outer_cyclic_square_solvable {F S Z : Type} [Group F] [Group S] [Finite S]
    [Group Z] [IsCyclic Z] (hS : SimpleCentreless S) (hperf : Group.IsPerfect S)
    (hout : Group.IsSolvable (Outer S)) (e : F ≃* Z × S × S) :
    Group.IsSolvable (Outer F) := by
  haveI : Group.IsPerfect (S × S) := s16c167_frame_isPerfect_prod hperf hperf
  have hcenter : Subgroup.center (S × S) = ⊥ := by
    rw [Subgroup.center_prod, s16c167_frame_center_eq_bot hS, Subgroup.bot_prod_bot]
  haveI : Group.IsSolvable (Outer (S × S)) := s16c167_frame_outer_square_solvable hS hout
  haveI : Group.IsSolvable (Outer ((S × S) × Z)) :=
    CFSG.ComponentClassification.CatalogueSchreierCyclicCentralFactor.outer_solvable_of_cyclic
      (L := S × S) (Z := Z) hcenter
  exact CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_equiv
    (e.trans MulEquiv.prodComm).symm

theorem s16c167_frame_le_of_perfect {A : Type*} [Group A] {X F J : Subgroup A} (hFX : F ≤ X)
    (hJX : J ≤ X) (hFn : ∀ x ∈ X, ∀ f ∈ F, x * f * x⁻¹ ∈ F)
    (hself : ∀ y ∈ X, (∀ f ∈ F, y * f = f * y) → y ∈ F)
    (hout : Group.IsSolvable (Outer ↥F)) (hJ : Group.IsPerfect ↥J) : J ≤ F := by
  intro j hj
  have hnorm : J ≤ Subgroup.normalizer (F : Set A) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact hFn x (hJX hx) h hh
    · intro hh
      have hx' : x⁻¹ ∈ X := X.inv_mem (hJX hx)
      have hmem := hFn x⁻¹ hx' (x * h * x⁻¹) hh
      rwa [show x⁻¹ * (x * h * x⁻¹) * (x⁻¹)⁻¹ = h by group] at hmem
  haveI : Group.IsPerfect ↥J := hJ
  haveI : Group.IsSolvable (Outer ↥F) := hout
  obtain ⟨k, hk⟩ := perfect_action_inner
    ((Subgroup.normalizerMonoidHom F).comp (Subgroup.inclusion hnorm)) ⟨j, hj⟩
  have hk' : ∀ f ∈ F, j * f * j⁻¹ = (k : A) * f * (k : A)⁻¹ := by
    intro f hf
    have h := congrArg (fun α : MulAut ↥F => ((α ⟨f, hf⟩ : ↥F) : A)) hk
    simpa [Subgroup.normalizerMonoidHom_apply_apply_coe] using h
  let c : A := (k : A)⁻¹ * j
  have hcX : c ∈ X := X.mul_mem (X.inv_mem (hFX k.2)) (hJX hj)
  have hcF : c ∈ F := by
    refine hself c hcX fun f hf => ?_
    have h := hk' f hf
    change ((k : A)⁻¹ * j) * f = f * ((k : A)⁻¹ * j)
    calc ((k : A)⁻¹ * j) * f
        = (k : A)⁻¹ * (j * f * j⁻¹) * j := by group
      _ = (k : A)⁻¹ * ((k : A) * f * (k : A)⁻¹) * j := by rw [h]
      _ = f * ((k : A)⁻¹ * j) := by group
  have hjc : j = (k : A) * c := by
    change j = (k : A) * ((k : A)⁻¹ * j)
    group
  rw [hjc]
  exact F.mul_mem k.2 hcF

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
