module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutInnerExcSixE
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitExcSixE

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny

namespace ExcFrames

section IsogenyE6


theorem exists_injective_factor_E6 {G : Type} [Group G] {n f : ℕ}
    (ψ : (ggU .E6 n f).K →* G) (hker : ψ.ker ≤ Subgroup.center (ggU .E6 n f).K)
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) :
    ∃ χ : adjointGroup .E6 (GaloisField 2 f) →* G, Function.Injective χ ∧
      χ.range = ψ.range := by
  have hkerEq : ψ.ker = Subgroup.center (ggU .E6 n f).K := by
    refine le_antisymm hker fun z hz => ?_
    rw [MonoidHom.mem_ker]
    have h : ψ z ∈ Subgroup.centralizer (ψ.range : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨y, rfl⟩
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz y]
    rw [hC, Subgroup.mem_bot] at h
    exact h
  obtain ⟨χ, hχ, hval⟩ :=
    ExcNonsplit.exists_factor_e6Isogeny (k := GaloisField 2 f) (ψ := ψ) hkerEq
  refine ⟨χ, hχ, ?_⟩
  ext g
  constructor
  · rintro ⟨c, rfl⟩
    obtain ⟨y, rfl⟩ := e6Isogeny_surjective (GaloisField 2 f) c
    exact ⟨y, (hval y).symm⟩
  · rintro ⟨y, rfl⟩
    exact ⟨e6Isogeny (GaloisField 2 f) y, hval y⟩

theorem mem_range_of_innerDiag_E6 {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {n f : ℕ} (hp3 : p ≠ 3 ∨ ¬ 3 ∣ Nat.card (GaloisField 2 f) - 1) (ψ : (ggU .E6 n f).K →* G)
    (hker : ψ.ker ≤ Subgroup.center (ggU .E6 n f).K) (hperf : commutator ↥ψ.range = ⊤)
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {c : G}
    (hcN : c ∈ Subgroup.normalizer (ψ.range : Set G)) (hcp : c ^ p = 1)
    (hci : GGPsiInnerDiag (ggU .E6 n f).D ψ c) : c ∈ ψ.range := by
  have hkπ := LayerSixE.ker_le_ker_e6Isogeny hker
  obtain ⟨α, hαD, hα⟩ := LayerSixE.exists_induces_E6 ψ hker hcN hci
  have hπ := e6Isogeny_surjective (GaloisField 2 f)
  have hαp : α ^ p = 1 := by
    have h1 := hα.pow hkπ hcN p
    rw [hcp] at h1
    exact LayerSixE.GGInduces.unique hπ (Subgroup.one_mem _) h1 (LayerSixE.GGInduces.one hkπ)
  exact OrdPInnerExc.mem_range_of_induces_inner hπ
    (CFSG.ClassicalInvolution.ModelFacts.ChevAut.e6Isogeny_ker_le_center (GaloisField 2 f)) hkπ
    hperf hC hcN (OrdPInnerExc.mem_inn_of_inndiag_E6 hp hp3 hαD hαp) hα

end IsogenyE6

end ExcFrames

end CFSG.StandardType
