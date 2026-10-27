module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentDefs

import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentRoot
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentRank
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentPSLTwoElt
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentPSLNormalizer
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentPSLDiag

public section

namespace CFSG.StandardType

open Matrix CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.StandardType.KGCentPSL

private theorem conjAut_proj_conjSL {m : ℕ} {F : Type} [Field F] (A : GL (Fin (m + 1)) F)
    (u : SpecialLinearGroup (Fin (m + 1)) F) :
    conjAut (m + 1) F A (proj (m + 1) F u) = proj (m + 1) F (InnerDiagA.conjSL A u) := by
  rw [conjAut_proj]
  congr 1
  refine Subtype.ext ?_
  rw [coe_slConjugation, InnerDiagA.coe_conjSL]

theorem ggKGCentTagStmt_PSL
    (ha₀ : GGLNoncyclicInput) (hL : GGLBalanceInput) : GGKGCentTagStmt .PSL := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg _ hr X hX n f ψ hloc hstd t ht htN htD htJ
  obtain ⟨r, hrA, hrefl⟩ := hr
  have hn4 : 4 ≤ n := by
    have h := hloc.1.2.2.2
    have h' : bnRank .PSL n = n - 1 := rfl
    omega
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  change SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f) →* G at ψ
  have hm3 : 3 ≤ m + 1 := by omega
  have hm2 : 2 ≤ m := by omega
  have hDBs : D ≤ Bs := hcfg.1.1.2.2.1.1.trans hcfg.1.1.2.1.1
  have hrange : ψ.range = X := hloc.2.1.2.1
  have hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)) :=
    hloc.2.1.1
  have hBsN : Bs ≤ Subgroup.normalizer (X : Set G) := hloc.2.2.1.2.1
  obtain ⟨Φ, hΦ1, hΦ2⟩ :=
    exists_pslAutHom_of_ker_le_center (K := GaloisField 2 f) hm3 ψ hker
  have h3 : ∀ d ∈ Bs, ∃ Dd : GL (Fin (m + 1)) (GaloisField 2 f),
      ((Dd : GL (Fin (m + 1)) (GaloisField 2 f)) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)).IsDiag ∧
      ∀ u : SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f),
        d * ψ u * d⁻¹ = ψ (InnerDiagA.conjSL Dd u) :=
    fun d hd => exists_isDiag_conj_of_stdPos hm2 (F := GaloisField 2 f) ψ hker (hstd d hd)
  choose! Dm hDm1 hDm2 using h3
  have hNt : t ∈ Subgroup.normalizer (ψ.range : Set G) := by
    rw [hrange]
    exact htN
  have hNd : ∀ d ∈ Bs, d ∈ Subgroup.normalizer (ψ.range : Set G) := fun d hd => by
    rw [hrange]
    exact hBsN hd
  obtain ⟨T, hT⟩ : ∃ T : Subgroup.normalizer (ψ.range : Set G), (T : G) = t := ⟨⟨t, hNt⟩, rfl⟩
  have hΦd : ∀ d (hd : d ∈ Bs),
      Φ ⟨d, hNd d hd⟩ = conjAut (m + 1) (GaloisField 2 f) (Dm d) := by
    intro d hd
    refine MulEquiv.ext fun y => ?_
    obtain ⟨u, rfl⟩ := proj_surjective (m + 1) (GaloisField 2 f) y
    rw [conjAut_proj_conjSL]
    exact hΦ1 ⟨d, hNd d hd⟩ u _ (hDm2 d hd u).symm
  obtain ⟨k, hk⟩ := ht
  have hβpow : Φ T ^ 2 ^ k = 1 := by
    have h1 : T ^ 2 ^ k = 1 := Subtype.ext (by
      show (T : G) ^ 2 ^ k = 1
      rw [hT]
      exact hk)
    rw [← map_pow Φ T (2 ^ k), h1, map_one]
  have hcomm : ∀ i : ↥D, conjAut (m + 1) (GaloisField 2 f) (Dm i) * Φ T =
      Φ T * conjAut (m + 1) (GaloisField 2 f) (Dm i) := by
    intro i
    rw [← hΦd i (hDBs i.2), ← map_mul, ← map_mul]
    congr 1
    refine Subtype.ext ?_
    show (i : G) * (T : G) = (T : G) * (i : G)
    rw [hT]
    exact Subgroup.mem_centralizer_iff.1 htD i i.2
  have hroot_of : ∀ {i j : Fin (m + 1)} (hij : i ≠ j),
      (∀ c : GaloisField 2 f, ψ (SpecialLinearGroup.transvection hij c) ∈
        Subgroup.centralizer (D : Set G)) →
      InnerDiagA.typeARoot i j ∈ ggKGCentRoots (ggU .PSL (m + 1) f).D ψ D := by
    intro i j hij hcd
    refine ⟨InnerDiagA.typeARoot_mem_roots _ hij, ?_⟩
    intro z hz
    have hz' : z ∈ SpecialLinear.rootSubgroup m (GaloisField 2 f) hij := by
      have := InnerDiagA.rootGroup_typeARoot (m := m) (F := GaloisField 2 f) hij
      exact this ▸ hz
    obtain ⟨c', rfl⟩ := (SpecialLinear.mem_rootSubgroup hij z).1 hz'
    exact hcd c'
  have hfix : ∀ (a b : Fin (m + 1)) (hab : a ≠ b),
      (∀ i : ↥D, ((Dm i : GL (Fin (m + 1)) (GaloisField 2 f)) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) a a =
        ((Dm i : GL (Fin (m + 1)) (GaloisField 2 f)) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) b b) →
      ∀ c : GaloisField 2 f, Φ T (proj (m + 1) (GaloisField 2 f)
        (SpecialLinearGroup.transvection hab c)) =
        proj (m + 1) (GaloisField 2 f) (SpecialLinearGroup.transvection hab c) := by
    intro a b hab hdiag c
    have hcd : ∀ c' : GaloisField 2 f,
        ψ (SpecialLinearGroup.transvection hab c') ∈ Subgroup.centralizer (D : Set G) := by
      intro c' d hd
      exact (commute_transvection_iff_diag_eq ψ hker (hDm1 d (hDBs hd)) (hDm2 d (hDBs hd))
        hab).2 (hdiag ⟨d, hd⟩) c'
    have hJ := ggKGCent_rootGroup_le ha₀ hL hcfg hrA hrefl hX hloc hstd (hroot_of hab hcd)
    have hψJ : ψ (SpecialLinearGroup.transvection hab c) ∈ J := by
      refine hJ ⟨_, ?_, rfl⟩
      show _ ∈ SpecialLinear.rootGroup m (GaloisField 2 f) (InnerDiagA.typeARoot a b)
      rw [InnerDiagA.rootGroup_typeARoot]
      exact SpecialLinear.transvection_mem_rootSubgroup hab c
    refine hΦ1 T _ _ ?_
    rw [hT]
    have h := Subgroup.mem_centralizer_iff.1 htJ _ hψJ
    rw [← h, mul_inv_cancel_right]
  have hdiag_of_root : ∀ {β : Fin m → ℤ},
      β ∈ ggKGCentRoots (ggU .PSL (m + 1) f).D ψ D →
      ∀ {i j : Fin (m + 1)} (hij : i ≠ j),
        SpecialLinear.toStd m β = Pi.single i 1 - Pi.single j 1 →
        ∀ d : ↥D, ((Dm d : GL (Fin (m + 1)) (GaloisField 2 f)) :
            Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) i i =
          ((Dm d : GL (Fin (m + 1)) (GaloisField 2 f)) :
            Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) j j := by
    intro β hβ i j hij hstdβ d
    refine (commute_transvection_iff_diag_eq ψ hker (hDm1 d (hDBs d.2)) (hDm2 d (hDBs d.2))
      hij).1 (fun c => ?_)
    have hmem : SpecialLinearGroup.transvection hij c ∈
        (ggU .PSL (m + 1) f).D.rootGroup β := by
      show _ ∈ SpecialLinear.rootGroup m (GaloisField 2 f) β
      rw [SpecialLinear.rootGroup_eq m (GaloisField 2 f) hij hstdβ]
      exact SpecialLinear.transvection_mem_rootSubgroup hij c
    have hmem' : ψ (SpecialLinearGroup.transvection hij c) ∈ Subgroup.centralizer (D : Set G) :=
      hβ.2 hmem
    exact Subgroup.mem_centralizer_iff.1 hmem' d d.2
  obtain ⟨β₁, hβ₁, β₂, hβ₂, hs⟩ :=
    ggKGCent_exists_root_add ha₀ hL hcfg hrA hrefl hX hloc hstd
  obtain ⟨a, b, c, hab, hbc, hac, hcases⟩ :=
    exists_distinct_of_roots_add_mem (m := m) hβ₁.1 hβ₂.1 hs
  have e1 : ∀ d : ↥D,
      ((Dm d : GL (Fin (m + 1)) (GaloisField 2 f)) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) a a =
        ((Dm d : GL (Fin (m + 1)) (GaloisField 2 f)) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) b b ∧
      ((Dm d : GL (Fin (m + 1)) (GaloisField 2 f)) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) b b =
        ((Dm d : GL (Fin (m + 1)) (GaloisField 2 f)) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) c c := by
    intro d
    rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨hdiag_of_root hβ₁ hab h1 d, hdiag_of_root hβ₂ hbc h2 d⟩
    · exact ⟨hdiag_of_root hβ₂ hab h2 d, hdiag_of_root hβ₁ hbc h1 d⟩
  have hJ0 : 3 ≤ ({a, b, c} : Finset (Fin (m + 1))).card :=
    (Finset.card_eq_three.2 ⟨a, b, c, hab, hac, hbc, rfl⟩).ge
  have hJ0D : ∀ x ∈ ({a, b, c} : Finset (Fin (m + 1))), ∀ y ∈ ({a, b, c} : Finset (Fin (m + 1))),
      ∀ i : ↥D, ((Dm i : GL (Fin (m + 1)) (GaloisField 2 f)) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) x x =
        ((Dm i : GL (Fin (m + 1)) (GaloisField 2 f)) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) y y := by
    intro x hx y hy i
    obtain ⟨h1, h2⟩ := e1 i
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      first | rfl | exact h1 | exact h1.symm | exact h2 | exact h2.symm | exact h1.trans h2 |
        exact (h1.trans h2).symm
  have hβ1 : Φ T = 1 :=
    eq_one_of_commute_diag_fix_pairs (K := GaloisField 2 f) (n := m + 1) hm3
      (fun d : ↥D => Dm d) (fun d => hDm1 d (hDBs d.2)) hβpow hcomm hfix hJ0 hJ0D
  intro g hg h hh
  have hg' : g ∈ ψ.range := hrange ▸ hg
  have hh' : h ∈ ψ.range := hrange ▸ hh
  have h2 := hΦ2 T hβ1 g hg' h hh'
  rw [hT] at h2
  exact h2

end CFSG.StandardType

end
