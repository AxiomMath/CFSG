module

public import CFSG.Timmesfeld.ARS.SimplyLacedConfigA

public section

namespace CFSG.Timmesfeld.ARS

open CFSG.Timmesfeld.RankOne CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg Matrix

variable {G : Type} [Group G] {R : Set (Subgroup G)}

theorem IsConfig.exists_surjective_A_two [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
    {A B : Fin 2 → Subgroup G} (hX : IsConfig R (edgeA 2) A B) (hgen : ⨆ k, (A k ⊔ B k) = ⊤) :
    ∃ f : ℕ, 1 ≤ f ∧ (∀ E ∈ R, Nat.card E = 2 ^ f) ∧
      ∃ Ψ : SpecialLinearGroup (Fin (2 + 1)) (GaloisField 2 f) →* G,
        (∀ k : Fin 2,
          ((SpecialLinear.rootDatum 2 (GaloisField 2 f)).rootGroup (sroot k)).map Ψ = A k) ∧
        (∀ k : Fin 2,
          ((SpecialLinear.rootDatum 2 (GaloisField 2 f)).rootGroup (-sroot k)).map Ψ = B k) ∧
        Function.Surjective Ψ := by
  obtain ⟨f, hf, hcard, ρ, hρ, hedge⟩ := hX.exists_frame hR hiso (isRootedTree_A (by omega))
  set F := GaloisField 2 f
  obtain ⟨ψ₀, hψ⟩ := hedge 0 1 (by decide)
  set ψ : SpecialLinearGroup (Fin (2 + 1)) F →* G := ψ₀ with hψψ
  have hu : ∀ k, Set.range (fun c => ρ k (tv 0 1 c)) = (A k : Set G) := fun k => by
    rw [← (hρ k).2.1]
    exact Linear.range_tv_upper (ρ k)
  have hv : ∀ k, Set.range (fun c => ρ k (tv 1 0 c)) = (B k : Set G) := fun k => by
    rw [← (hρ k).2.2]
    exact Linear.range_tv_lower (ρ k)
  have mu : ∀ k c, ρ k (tv 0 1 c) ∈ A k := fun k c => by
    rw [← SetLike.mem_coe, ← hu]
    exact ⟨c, rfl⟩
  have mv : ∀ k c, ρ k (tv 1 0 c) ∈ B k := fun k c => by
    rw [← SetLike.mem_coe, ← hv]
    exact ⟨c, rfl⟩
  have hxu : ∀ (k : Fin 2) (c : F), ψ (SL.x 2 F (sroot k) c) = ρ k (tv 0 1 c) := by
    intro k c
    rw [Linear.x_sroot]
    fin_cases k
    · exact (hψ c).1
    · exact (hψ c).2.2.1
  have hxv : ∀ (k : Fin 2) (c : F), ψ (SL.x 2 F (-sroot k) c) = ρ k (tv 1 0 c) := by
    intro k c
    rw [Linear.x_neg_sroot]
    fin_cases k
    · exact (hψ c).2.1
    · exact (hψ c).2.2.2
  have hD := simplyLacedLevis_specialLinear 2 F
  have hroot : ∀ k : Fin 2, sroot k ∈ (SpecialLinear.rootDatum 2 F).roots ∧
      -sroot k ∈ (SpecialLinear.rootDatum 2 F).roots := fun k =>
    ⟨(Levi.single_mem_pairRoots (D := SpecialLinear.rootDatum 2 F) (i := k) (j := k)
      (Or.inl rfl)).1.1,
      (Levi.single_mem_pairRoots (D := SpecialLinear.rootDatum 2 F) (i := k) (j := k)
        (Or.inl rfl)).2.1⟩
  have hmap : ∀ (γ : Fin 2 → ℤ) (S : Subgroup G), γ ∈ (SpecialLinear.rootDatum 2 F).roots →
      (∀ c, ψ (SL.x 2 F γ c) ∈ S) → (∀ s ∈ S, ∃ c, ψ (SL.x 2 F γ c) = s) →
      ((SpecialLinear.rootDatum 2 F).rootGroup γ).map ψ = S := by
    intro γ S hγ h1 h2
    ext y
    constructor
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨c, rfl⟩ := hD.surj _ hγ g hg
      exact h1 c
    · intro hy
      obtain ⟨c, rfl⟩ := h2 y hy
      exact ⟨_, hD.mem _ hγ c, rfl⟩
  have hA : ∀ k : Fin 2, ((SpecialLinear.rootDatum 2 F).rootGroup (sroot k)).map ψ = A k := by
    intro k
    refine hmap _ _ (hroot k).1 (fun c => ?_) (fun s hs => ?_)
    · exact (congrArg (· ∈ A k) (hxu k c)).mpr (mu k c)
    · rw [← SetLike.mem_coe, ← hu k] at hs
      obtain ⟨c, rfl⟩ := hs
      exact ⟨c, hxu k c⟩
  have hB : ∀ k : Fin 2, ((SpecialLinear.rootDatum 2 F).rootGroup (-sroot k)).map ψ = B k := by
    intro k
    refine hmap _ _ (hroot k).2 (fun c => ?_) (fun s hs => ?_)
    · exact (congrArg (· ∈ B k) (hxv k c)).mpr (mv k c)
    · rw [← SetLike.mem_coe, ← hv k] at hs
      obtain ⟨c, rfl⟩ := hs
      exact ⟨c, hxv k c⟩
  refine ⟨f, hf, hcard, ψ, hA, hB, ?_⟩
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← hgen]
  refine iSup_le fun k => sup_le ?_ ?_
  · intro a ha
    rw [← SetLike.mem_coe, ← hu] at ha
    obtain ⟨c, rfl⟩ := ha
    exact ⟨_, hxu k c⟩
  · intro b hb
    rw [← SetLike.mem_coe, ← hv] at hb
    obtain ⟨c, rfl⟩ := hb
    exact ⟨_, hxv k c⟩

end CFSG.Timmesfeld.ARS
