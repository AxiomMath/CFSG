module

public import CFSG.Timmesfeld.ARS.SimplyLacedConfig
public import CFSG.LieType.CurtisTits.SpecialLinear

public section

namespace CFSG.Timmesfeld.ARS

open CFSG.Timmesfeld.RankOne CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg Matrix
open CFSG.Blueprint

abbrev edgeA (m : ℕ) (i j : Fin m) : Prop := j.val = i.val + 1

@[expose] def parA (m : ℕ) (k : Fin m) : Fin m := ⟨k.val - 1, by have := k.2; omega⟩

theorem isRootedTree_A {m : ℕ} (hm : 1 ≤ m) :
    IsRootedTree (edgeA m) (parA m) (fun k => k.val) ⟨0, by omega⟩ := by
  have hk0 : ∀ k : Fin m, k ≠ ⟨0, by omega⟩ → k.val ≠ 0 := fun k hk h => hk (Fin.ext h)
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun i j hij hji => ?_, fun i j hij => ?_⟩
  · have := hk0 k hk
    simp only [parA]
    omega
  · have := hk0 k hk
    left
    simp only [edgeA, parA]
    omega
  · simp only [edgeA] at hij hji
    omega
  · left
    simp only [edgeA] at hij
    refine ⟨fun h => ?_, Fin.ext ?_⟩
    · have := congrArg Fin.val h
      simp only at this
      omega
    · simp only [parA]
      omega

variable {G : Type} [Group G] {R : Set (Subgroup G)}

theorem IsConfig.lieModel_A [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
    (hZ : Subgroup.center G = ⊥) {m : ℕ} (hm : 3 ≤ m) {A B : Fin m → Subgroup G}
    (hX : IsConfig R (edgeA m) A B) (hgen : ⨆ k, (A k ⊔ B k) = ⊤) :
    ∃ f : ℕ, 1 ≤ f ∧ (∀ E ∈ R, Nat.card E = 2 ^ f) ∧ LieModel G .PSL (m + 1) 2 f := by
  obtain ⟨f, hf, hcard, ρ, hρ, hedge⟩ := hX.exists_frame hR hiso (isRootedTree_A (by omega))
  set F := GaloisField 2 f
  have hF : Nat.card F = 2 ^ f := GaloisField.card 2 f (by omega)
  refine ⟨f, hf, hcard, lieModel_of_rho (D := SpecialLinear.rootDatum m F)
    (CurtisTits.curtisTitsConclusion_specialLinear
      ⟨Nat.prime_two, hf, by omega, fun h => by injection h; omega,
        fun h => by injection h; omega⟩ hF hm)
    (leviConePresented_specialLinear m F) (simplyLacedLevis_specialLinear m F) hZ hX.nonadj ρ
    (fun k => ⟨(hρ k).2.1, (hρ k).2.2⟩) hedge hgen ?_⟩
  obtain ⟨a, ha, ha1⟩ := hR.exists_ne_one (hX.memA ⟨0, by omega⟩)
  exact ⟨(⟨0, by omega⟩ : Fin m), a, ha, ha1⟩

theorem IsConfig.exists_surjective_A [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
    {m : ℕ} (hm : 3 ≤ m) {A B : Fin m → Subgroup G} (hX : IsConfig R (edgeA m) A B)
    (hgen : ⨆ k, (A k ⊔ B k) = ⊤) :
    ∃ f : ℕ, 1 ≤ f ∧ (∀ E ∈ R, Nat.card E = 2 ^ f) ∧
      ∃ Ψ : SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f) →* G,
        (∀ k, ((SpecialLinear.rootDatum m (GaloisField 2 f)).rootGroup (sroot k)).map Ψ = A k) ∧
        (∀ k, ((SpecialLinear.rootDatum m (GaloisField 2 f)).rootGroup (-sroot k)).map Ψ =
          B k) ∧ Function.Surjective Ψ ∧ Ψ.ker ≤ Subgroup.center _ := by
  obtain ⟨f, hf, hcard, ρ, hρ, hedge⟩ := hX.exists_frame hR hiso (isRootedTree_A (by omega))
  set F := GaloisField 2 f
  have hF : Nat.card F = 2 ^ f := GaloisField.card 2 f (by omega)
  refine ⟨f, hf, hcard, exists_surjective_of_rho (D := SpecialLinear.rootDatum m F)
    (CurtisTits.curtisTitsConclusion_specialLinear
      ⟨Nat.prime_two, hf, by omega, fun h => by injection h; omega,
        fun h => by injection h; omega⟩ hF hm)
    (leviConePresented_specialLinear m F) (simplyLacedLevis_specialLinear m F) hX.nonadj ρ
    (fun k => ⟨(hρ k).2.1, (hρ k).2.2⟩) hedge hgen ?_⟩
  obtain ⟨a, ha, ha1⟩ := hR.exists_ne_one (hX.memA ⟨0, by omega⟩)
  exact ⟨(⟨0, by omega⟩ : Fin m), a, ha, ha1⟩

end CFSG.Timmesfeld.ARS
