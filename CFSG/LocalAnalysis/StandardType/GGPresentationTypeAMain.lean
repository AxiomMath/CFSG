module

public import CFSG.LocalAnalysis.StandardType.GGPresentationTypeA
public import CFSG.LieType.CurtisTits.SpecialLinear

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits SpecialLinear
  CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem two_eq_zero_of_card {F : Type} [Field F] [Finite F] {f : ℕ} (hF : Nat.card F = 2 ^ f)
    (hf : 1 ≤ f) : (2 : F) = 0 := by
  have := Fintype.ofFinite F
  have h := FiniteField.cast_card_eq_zero F
  rw [← Nat.card_eq_fintype_card, hF] at h
  push_cast at h
  exact (pow_eq_zero_iff (by omega)).mp h

theorem ggPresentation_typeA {m : ℕ} (hm : 4 ≤ m) {F : Type} [Field F] [Finite F] {f : ℕ}
    (hF : Nat.card F = 2 ^ f) (hf : 1 ≤ f) {X : Type} [Group X]
    (φ : ggSub (rootDatum m F) (ggSupp (rootDatum m F) (typeAJ₁ m)) →* X)
    {R : Subgroup X} {δ : R →* (coxeterMatrix (isFiniteType_A m)).Group}
    (hδ : Function.Surjective δ)
    (hspecial : ∀ k ∈ typeAJ₁ m, ∃ c : R, (c : X) = ggExt φ (weylRep m F k) ∧
      δ c = (coxeterMatrix (isFiniteType_A m)).toCoxeterSystem.simple k)
    (hcent : ∀ (r : R), ∀ α ∈ ggSupp (rootDatum m F) (typeAJ₁ m),
      weylAction (isFiniteType_A m) (δ r) α = α →
        ∀ z ∈ rootGroup m F α, (r : X) * ggExt φ z * (r : X)⁻¹ = ggExt φ z)
    (hnt : ∃ γ ∈ ggSupp (rootDatum m F) (typeAJ₁ m), ∃ z ∈ rootGroup m F γ, ggExt φ z ≠ 1) :
    ∃ ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* X,
      (∀ x : ggSub (rootDatum m F) (ggSupp (rootDatum m F) (typeAJ₁ m)), ψ x = φ x) ∧
      (∀ (r : R) (u : Matrix.SpecialLinearGroup (Fin (m + 1)) F),
        ψ (slWeylLift m (two_eq_zero_of_card hF hf) (δ r) * u *
          (slWeylLift m (two_eq_zero_of_card hF hf) (δ r))⁻¹) = r * ψ u * (r : X)⁻¹) ∧
      (∀ w : (coxeterMatrix (isFiniteType_A m)).Group, ∃ r : R,
        (r : X) = ψ (slWeylLift m (two_eq_zero_of_card hF hf) w) ∧ δ r = w) ∧
      ψ.range = ggClosure (rootDatum m F) (fun _ : Unit => ggSupp (rootDatum m F) (typeAJ₁ m))
        (fun _ => φ) R ∧
      ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F) ∧
      IsQuasisimple (ggClosure (rootDatum m F)
        (fun _ : Unit => ggSupp (rootDatum m F) (typeAJ₁ m)) (fun _ => φ) R) ∧
      LieModel (ggClosure (rootDatum m F) (fun _ : Unit => ggSupp (rootDatum m F) (typeAJ₁ m))
          (fun _ => φ) R ⧸ Subgroup.center (ggClosure (rootDatum m F)
            (fun _ : Unit => ggSupp (rootDatum m F) (typeAJ₁ m)) (fun _ => φ) R))
        .PSL (m + 1) 2 f := by
  have h2 : (2 : F) = 0 := two_eq_zero_of_card hF hf
  have hν : GGWeylLift (rootDatum m F) (slWeylLift m h2) := slWeylLift_spec m h2
  have hS : ∀ k : Unit, (fun _ : Unit => ggSupp (rootDatum m F) (typeAJ₁ m)) k ⊆
      (rootDatum m F).roots := fun _ γ hγ => hγ.1
  have hT : ∀ t ∈ (coxeterMatrix (isFiniteType_A m)).toCoxeterSystem.simple ''
      (typeAJ₁ m : Set (Fin m)),
      slWeylLift m h2 t ∈ ggSub (rootDatum m F) (ggSupp (rootDatum m F) (typeAJ₁ m)) := by
    rintro _ ⟨k, hk, rfl⟩
    have h := hν.simple_mem k
    exact sup_le (rootGroup_le_ggSub (single_mem_ggSupp hk))
      (rootGroup_le_ggSub (neg_single_mem_ggSupp hk)) h
  have hW₁ : ∀ v ∈ typeAW₁ m, slWeylLift m h2 v ∈
      ggSub (rootDatum m F) (ggSupp (rootDatum m F) (typeAJ₁ m)) :=
    fun v hv => ggWeylLift_mem_of_closure hT hv
  have hgen : ∀ t ∈ (coxeterMatrix (isFiniteType_A m)).toCoxeterSystem.simple ''
      (typeAJ₁ m : Set (Fin m)), ∃ c : R, (c : X) = ggExt φ (slWeylLift m h2 t) ∧ δ c = t := by
    rintro _ ⟨k, hk, rfl⟩
    rw [slWeylLift_simple]
    exact hspecial k hk
  have hall := exists_mem_R_of_closure (S := fun _ : Unit => ggSupp (rootDatum m F) (typeAJ₁ m))
    (φ := fun _ => φ) (ν := slWeylLift m h2) (δ := δ) (k := ()) hW₁ hgen
  have hC : GGActsLike (rootDatum m F) (fun _ : Unit => ggSupp (rootDatum m F) (typeAJ₁ m))
      (fun _ => φ) (slWeylLift m h2) R δ := by
    refine ggActsLike_of_transitive hν hS (fun _ _ _ _ _ _ _ => rfl) ?_
      (fun r _ α hα hfix z hz => hcent r α hα hfix z hz)
      (fun w α hα hfix z hz => slWeylLift_fix m h2 w hα hfix hz)
    intro r _ _ α hα hαr
    obtain ⟨v₂, hv₂, hv₂α⟩ := typeA_transitive m F hα hαr
    obtain ⟨c₂, hc₂, hcδ₂⟩ := hall v₂ hv₂
    obtain ⟨c₁, hc₁, hcδ₁⟩ := hall 1 (one_mem _)
    refine ⟨α, 1, v₂, c₁, c₂, hα, hα, ?_, hv₂α, hW₁ 1 (one_mem _), hc₁, hcδ₁, hW₁ v₂ hv₂, hc₂,
      hcδ₂⟩
    change weylAction (isFiniteType_A m) 1 α = α
    rw [map_one]
    rfl
  have hW : GGWeylInR (rootDatum m F) (fun _ : Unit => ggSupp (rootDatum m F) (typeAJ₁ m))
      (fun _ => φ) (slWeylLift m h2) R δ :=
    ggWeylInR_of_subgroup (fun _ => typeAW₁ m) (fun _ => hW₁)
      (fun _ => (coxeterMatrix (isFiniteType_A m)).toCoxeterSystem.simple ''
        (typeAJ₁ m : Set (Fin m))) (fun _ => rfl) (fun _ => hgen)
      (fun _ w j hj => typeA_refl_mem m F w j hj)
  have hadm : StatedLieAdmissible .PSL (m + 1) 2 f :=
    ⟨Nat.prime_two, hf, by omega, fun h => by simp at h; omega, fun h => by simp at h; omega⟩
  have hCT : CurtisTitsConclusion.{0} (rootDatum m F) .PSL (m + 1) 2 f :=
    curtisTitsConclusion_specialLinear hadm hF (by omega)
  obtain ⟨ψ, h1, h2', h3, h4, h5, h6, h7⟩ := ggPresentation hCT hν hS (fun _ => φ) hδ hC hW
    (typeA_orbit m F hm) ⟨(), hnt⟩
  exact ⟨ψ, h1 (), h2', h3, h4, h5, h6, h7⟩

end CFSG.StandardType
