module

public import CFSG.LocalAnalysis.StandardType.GGTwE6ToralInner

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Exceptional

namespace ExcFrames

section IsogenyTwE6


theorem exists_injective_factor_twistedE6 {G : Type} [Group G] {n f : ℕ} (hf : 1 ≤ f)
    (ψ : (ggU .twistedE6 n f).K →* G)
    (hker : ψ.ker ≤ Subgroup.center (ggU .twistedE6 n f).K)
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) :
    ∃ χ : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) →* G,
      Function.Injective χ ∧ χ.range = ψ.range := by
  obtain ⟨π, hπ, hkerπ, -, -⟩ := LayerSixE.exists_model_twistedE6 hf
  have hkerEq : ψ.ker = π.ker := by
    refine le_antisymm (hkerπ ▸ hker) ?_
    rw [hkerπ]
    intro z hz
    have hz' : z ∈ Subgroup.center (ggU .twistedE6 n f).K := hz
    rw [MonoidHom.mem_ker]
    have h : ψ z ∈ Subgroup.centralizer (ψ.range : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨y, rfl⟩
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz' y]
    rw [hC, Subgroup.mem_bot] at h
    exact h
  have hle : π.ker ≤ ψ.ker := hkerEq.ge
  set χ : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) →* G :=
    MonoidHom.liftOfSurjective π hπ ⟨ψ, hle⟩ with hχdef
  have hχπ : ∀ x, χ (π x) = ψ x := fun x =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ x
  refine ⟨χ, ?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro c hc
    obtain ⟨x, rfl⟩ := hπ c
    rw [hχπ] at hc
    have hx : x ∈ ψ.ker := hc
    rw [hkerEq] at hx
    exact hx
  · ext g
    constructor
    · rintro ⟨c, rfl⟩
      obtain ⟨x, rfl⟩ := hπ c
      exact ⟨x, (hχπ x).symm⟩
    · rintro ⟨x, rfl⟩
      exact ⟨π x, hχπ x⟩

theorem mem_range_of_innerDiag_twistedE6 {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {n f : ℕ} (hf : 1 ≤ f) (h3 : ¬ (p = 3 ∧ 3 ∣ 2 ^ f + 1))
    (ψ : (ggU .twistedE6 n f).K →* G)
    (hker : ψ.ker ≤ Subgroup.center (ggU .twistedE6 n f).K) (hperf : commutator ↥ψ.range = ⊤)
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {c : G}
    (hcN : c ∈ Subgroup.normalizer (ψ.range : Set G)) (hcp : c ^ p = 1)
    (hci : GGPsiInnerDiag (ggU .twistedE6 n f).D ψ c) : c ∈ ψ.range := by
  obtain ⟨π, hπ, hkerπ, -, hπval⟩ := LayerSixE.exists_model_twistedE6 hf
  have hkπ : ψ.ker ≤ π.ker := hker.trans hkerπ.ge
  obtain ⟨α, hαD, hα⟩ := LayerSixE.exists_induces_twistedE6 hf hπval ψ hker hkπ hcN hci
  have hαp : α ^ p = 1 := by
    have h1 := hα.pow hkπ hcN p
    rw [hcp] at h1
    exact LayerSixE.GGInduces.unique hπ (Subgroup.one_mem _) h1 (LayerSixE.GGInduces.one hkπ)
  exact OrdPInnerExc.mem_range_of_induces_inner hπ hkerπ.le hkπ hperf hC hcN
    (ggTwE6InndiagOrdPInnerInput_holds f p hf hp hp2 h3 α hαD hαp) hα

end IsogenyTwE6

end ExcFrames

end CFSG.StandardType
