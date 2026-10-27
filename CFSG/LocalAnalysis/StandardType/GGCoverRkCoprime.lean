module

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUModelCoprime
public import CFSG.LocalAnalysis.StandardType.GGCoverRkPSU
public import CFSG.LocalAnalysis.StandardType.GGCoverRkUnitLabel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB
open CFSG.ClassicalGroups.UnitaryFlag CFSG.StandardType.LineU

theorem ggCoverPTableB_PSU_coprime
    {d n p : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n)
    (hd : 3 ≤ d) (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hpd : ¬ p ∣ d) :
    GGCoverPTableB p (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n))) := by
  intro M _ _ L' E θ hE hP a ha
  have : Finite (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) := inferInstance
  have : Finite (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))) :=
    Finite.of_injective
      (fun f : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) =>
        (f : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)) →
          LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))))
      DFunLike.coe_injective
  have hA : IsElemAbelian p (ggLAutImage L' θ E) :=
    ggIsElemAbelian_map (ggIsElemAbelian_subgroupOf hP.2.1 _) (ggLAut L' θ)
  have hI : (ggLAutImage L' θ E : Set
        (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))))) ⊆
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n)) := by
    intro b hb
    simp only [ggLAutImage] at hb
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
  obtain ⟨φ, hM, hdiag⟩ := exists_diagModel_PSU_coprime hK hn hd hp hpq hpd hperf hA hI
  have hq : ¬(d = 3 ∧ 2 ^ n = 2) := by
    rintro ⟨rfl, h2⟩
    rw [h2] at hpq
    exact hpd hpq
  obtain ⟨g, hg, σ, m, hσ, hgact⟩ :=
    exists_semilin_through_model (d := d) (n := n) (p := p) (K := K) hd hq hM ha
  obtain ⟨ρ, hρ⟩ := exists_rho_commute_diag hp hd hM hσ hg hgact
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

theorem largeEvenLabelAll_coverP_twA_coprime
    {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (htag : lab.tag = .twA) (hl : 4 ≤ lab.rank) (hpn : p ∣ 2 ^ lab.n + 1)
    (hpd : ¬ p ∣ lab.rank + 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGCoverPTableB p R I := by
  have hn : 1 ≤ lab.n := hlab.1
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hl hn hpn hpd ⊢
  subst htag
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
  exact ⟨K, i1, i2, hK, ⟨hQ', ggCoverPTableB_PSU_coprime hK hn (by omega) hp hpn hpd⟩⟩

theorem largeEvenLabelAll_coverP_uFour
    {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel} (htag : lab.tag = .twA ∨ lab.tag = .twD)
    (hl : lab.rank = 3) (hn : 1 ≤ lab.n) (hpn : p ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGCoverPTableB p R I :=
  largeEvenLabelAll_uFour_of_forall htag hl fun K _ _ hK =>
    ggCoverPTableB_PSU_coprime hK hn (by norm_num) hp hpn
      (not_dvd_four_of_dvd_two_pow_add_one hp hn hpn)

end CFSG.StandardType
