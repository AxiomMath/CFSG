module

public import CFSG.LocalAnalysis.StandardType.GGWPlusPSU
public import CFSG.LocalAnalysis.StandardType.GGWPlusUnitAutModel
public import CFSG.LocalAnalysis.StandardType.GGCoverRkSemilin
public import CFSG.LocalAnalysis.StandardType.GGCoverRkDiag
public import CFSG.LocalAnalysis.StandardType.GGWPlusNarrow8Defs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB
open CFSG.ClassicalGroups.UnitaryFlag CFSG.StandardType.LineU

private theorem finite_largeEvenProj_PSU {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Finite K] (H : Subgroup (GL ι K)) : Finite (LargeEvenProj H) := by
  have : Finite H := Subtype.finite
  exact Finite.of_surjective _ (QuotientGroup.mk'_surjective _)

theorem ggCoverPTableBRk_PSU
    {d n p : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n)
    (hd : 5 ≤ d) (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hpd : p ∣ d) :
    GGCoverPTableBRk p (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n))) (d - 1) := by
  intro M _ _ L' E θ hE hP hr6 a ha
  haveI : Finite (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) :=
    finite_largeEvenProj_PSU _
  haveI : Finite (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))) :=
    Finite.of_injective
      (fun f : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) =>
        (f : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)) →
          LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))))
      DFunLike.coe_injective
  have hr : p ^ (d - 2) ≤ Nat.card (ggLAutImage L' θ E) := by
    simpa only [show d - 1 - 1 = d - 2 by omega] using
      pow_pred_le_card_ggLAutImage hP hp hr6
  have hA : IsElemAbelian p (ggLAutImage L' θ E) :=
    ggIsElemAbelian_map (ggIsElemAbelian_subgroupOf hP.2.1 _) (ggLAut L' θ)
  have hI : (ggLAutImage L' θ E : Set
        (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))))) ⊆
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n)) := by
    intro b hb
    simp only [ggLAutImage, Subgroup.mem_map] at hb
    obtain ⟨x, hx, rfl⟩ := hb
    have hxe : (⟨(x : M), hE hx⟩ : Subgroup.normalizer (L' : Set M)) = x :=
      Subtype.ext rfl
    rw [← hxe]
    exact hP.2.2.2.1 ⟨(x : M), hx⟩
  have hperf : commutator (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨l, rfl⟩ := ggQuotHom_surjective θ y
    have hl : l ∈ commutator L' := by rw [hP.1]; exact Subgroup.mem_top l
    have h1 := Subgroup.mem_map_of_mem (ggQuotHom θ) hl
    rwa [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr (ggQuotHom_surjective θ), ← commutator_def] at h1
  obtain ⟨φ, hM, hdiag⟩ :=
    exists_diagModel_PSU hK hn hd hp hpq hpd hperf hA hI hr
  have hq : ¬(d = 3 ∧ 2 ^ n = 2) := by rintro ⟨h3, _⟩; omega
  obtain ⟨g, hg, σ, m, hσ, hgact⟩ :=
    exists_semilin_through_model (d := d) (n := n) (p := p) (K := K) (by omega) hq hM ha
  obtain ⟨ρ, hρ⟩ := exists_rho_commute_diag hp (by omega) hM hσ hg hgact
  refine ⟨ρ, ?_⟩
  intro e
  have hmem : ggLAut L' θ ⟨e, hE e.2⟩ ∈ ggLAutImage L' θ E :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (show (e : M) ∈ E from e.2))
  obtain ⟨t, ht⟩ := hdiag _ hmem
  have hep : ggLAut L' θ ⟨e, hE e.2⟩ ^ p = 1 := by
    rw [← map_pow]
    have hnorm : (⟨e, hE e.2⟩ : Subgroup.normalizer (L' : Set M)) ^ p = 1 :=
      Subtype.ext (by simpa using hP.2.1.2 e e.2)
    rw [hnorm, map_one]
  exact hρ _ hep ⟨t, ht⟩

end CFSG.StandardType
