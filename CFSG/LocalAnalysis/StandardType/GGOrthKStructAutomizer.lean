module

public import CFSG.LocalAnalysis.StandardType.GGOrthKStructDefs
public import CFSG.LocalAnalysis.StandardType.GGHalfTorusFrame
public import CFSG.LocalAnalysis.StandardType.GGSpJoinSignedPermGen
import CFSG.LocalAnalysis.StandardType.GGOrthKStructInduces
import CFSG.LocalAnalysis.StandardType.GGOrthKStructNormalizer

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.StandardType.GGHalf CFSG.StandardType.SpJoin
  CFSG.LieType.Universal.SpecialLinear Matrix

private theorem okAut_mem_halfTorus_of_psi_mem {G : Type} [Group G] {Bs K : Subgroup G} {n : ℕ}
    {ψ : SpecialLinearGroup (Fin (n + 1)) F2 →* G}
    (hψ : GGHalfTorusFrame Bs K (halfTorus n) ψ) {x : SpecialLinearGroup (Fin (n + 1)) F2}
    (hx : ψ x ∈ Bs) : x ∈ halfTorus n := by
  obtain ⟨t, ht, hact⟩ := hψ.act (ψ x) hx
  have hcomm : ∀ y : SpecialLinearGroup (Fin (n + 1)) F2,
      (t⁻¹ * x) * y = y * (t⁻¹ * x) := by
    intro y
    have hy : ψ y ∈ K := by rw [← hψ.range]; exact ⟨y, rfl⟩
    have h := hact (ψ y) hy
    have hxy : x * y * x⁻¹ = t * y * t⁻¹ := by
      apply hψ.inj
      simpa only [map_mul, map_inv] using h
    calc t⁻¹ * x * y = t⁻¹ * (x * y * x⁻¹) * x := by group
      _ = t⁻¹ * (t * y * t⁻¹) * x := by rw [hxy]
      _ = y * (t⁻¹ * x) := by group
  have htinv : t⁻¹ * x = 1 := GGHalf.eq_one_of_commute_range hψ.inj (fun y => by
    simpa only [map_mul] using congrArg ψ (hcomm y))
  have hx_eq : x = t := by
    calc x = t * (t⁻¹ * x) := by group
      _ = t * 1 := by rw [htinv]
      _ = t := mul_one t
  rw [hx_eq]
  exact ht

theorem ggOrthKStruct_automizer {G : Type} [Group G] [Finite G] {Bs K : Subgroup G} {n : ℕ}
    {ψ : SpecialLinearGroup (Fin (n + 1)) F2 →* G}
    (hψ : GGHalfTorusFrame Bs K (halfTorus n) ψ) (hn : 7 ≤ n)
    (hprod : Bs = (halfTorus n).map ψ ⊔ (Bs ⊓ Subgroup.centralizer (K : Set G)))
    (Φ : (Fin ((n + 1) / 2) → Multiplicative (ZMod 3)) ≃* ↥(halfTorus n)) (hΦ : IsTorusCoord n Φ) :
    ∀ σ ∈ ggAutomizer K Bs, ∃ h ∈ spSignedGroup ((n + 1) / 2) 3, InducesSigned K ψ Φ σ h := by
  intro σ hσ
  unfold ggAutomizer at hσ
  refine Subgroup.closure_induction (k := ggInduced K Bs)
    (p := fun σ _ => ∃ h ∈ spSignedGroup ((n + 1) / 2) 3, InducesSigned K ψ Φ σ h)
    ?_ ?_ ?_ ?_ hσ
  ·
    rintro σ hσ
    simp only [ggInduced, Set.mem_setOf_eq] at hσ
    rcases hσ with ⟨g, hgK, hgN, hσg⟩
    have hg_range : g ∈ ψ.range := by rw [hψ.range]; exact hgK
    obtain ⟨s, rfl⟩ := hg_range
    have hs_normalizer : s ∈ Subgroup.normalizer
        ((halfTorus n : Subgroup (SpecialLinearGroup (Fin (n + 1)) F2)) :
          Set (SpecialLinearGroup (Fin (n + 1)) F2)) := by
      apply Subgroup.mem_normalizer_fintype
      intro t ht
      have hψt : ψ t ∈ Bs := hψ.torus_le (Subgroup.mem_map_of_mem ψ ht)
      have hconj : ψ s * ψ t * (ψ s)⁻¹ ∈ Bs :=
        ((Subgroup.mem_normalizer_iff.mp hgN) (ψ t)).mp hψt
      exact okAut_mem_halfTorus_of_psi_mem hψ (by simpa only [map_mul, map_inv] using hconj)
    obtain ⟨h, hh, hconj⟩ := ggOrthKStruct_normalizer hn Φ hΦ hs_normalizer
    refine ⟨h, hh, ?_⟩
    unfold InducesSigned
    intro a c hb hc
    have hcK : ψ s * c = c * ψ s :=
      (Subgroup.mem_centralizer_iff.mp hc) (ψ s) hgK
    have hcinv : c * (ψ s)⁻¹ = (ψ s)⁻¹ * c := by
      calc c * (ψ s)⁻¹ = (ψ s)⁻¹ * (ψ s * c) * (ψ s)⁻¹ := by group
        _ = (ψ s)⁻¹ * (c * ψ s) * (ψ s)⁻¹ := by rw [hcK]
        _ = (ψ s)⁻¹ * c := by group
    have hconjΦ : ψ s * ψ (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) * (ψ s)⁻¹ =
        ψ (Φ (h a) : SpecialLinearGroup (Fin (n + 1)) F2) := by
      simpa only [map_mul, map_inv] using congrArg ψ (hconj a)
    calc (((σ ⟨ψ (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) * c, hb⟩ : ↥Bs)) : G)
        = ψ s * (ψ (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) * c) * (ψ s)⁻¹ :=
          hσg ⟨ψ (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) * c, hb⟩
      _ = (ψ s * ψ (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) * (ψ s)⁻¹) * c := by
            calc ψ s * (ψ (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) * c) * (ψ s)⁻¹
                = ψ s * ψ (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) * (c * (ψ s)⁻¹) := by
                  group
              _ = ψ s * ψ (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) * ((ψ s)⁻¹ * c) := by
                    rw [hcinv]
              _ = (ψ s * ψ (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) * (ψ s)⁻¹) * c := by
                    group
      _ = ψ (Φ (h a) : SpecialLinearGroup (Fin (n + 1)) F2) * c := by rw [hconjΦ]
  · exact ⟨1, Subgroup.one_mem _, ggOrthKStruct_induces_one K ψ Φ⟩
  · rintro x y hx hy ⟨hx', hhx', hσx⟩ ⟨hy', hhy', hσy⟩
    exact ⟨hx' * hy', Subgroup.mul_mem _ hhx' hhy', ggOrthKStruct_induces_mul hσx hσy⟩
  · rintro x hx ⟨hx', hhx', hσx⟩
    exact ⟨hx'⁻¹, Subgroup.inv_mem _ hhx', ggOrthKStruct_induces_inv hψ hσx⟩

end CFSG.StandardType

end
