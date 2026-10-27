module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OuterRSplit
public import CFSG.Quasithin.EmptyFaithful.R3c18W
public import CFSG.LocalAnalysis.UniquenessCase.UC22P218c
public import CFSG.LieType.Chevalley.G2TorusRank
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6G2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open
open CFSG.ComponentClassification
open CFSG.Blueprint (LieModel)

theorem OuterRSplit.of_pFrame {Y C : Type} [Group Y] [Finite Y] [Group C] {r : ℕ} (hr : r.Prime)
    (F : CFSG.Quasithin.R3c18.PFrame r Y C) (h2 : 2 ≤ CFSG.pRank r Y) : OuterRSplit Y r 2 := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  rintro α ⟨k, hk⟩ hα
  obtain ⟨g, i, hi, c, hgα⟩ := F.conj_mem α k hk
  have hIn : (OuterAutomorphisms.inner Y).Normal := inferInstance
  have hcr : c ^ r = 1 := by
    apply F.fld_inter
    have hi1 : QuotientGroup.mk' (OuterAutomorphisms.inner Y) i = 1 :=
      (QuotientGroup.eq_one_iff i).2 hi
    have h1 : QuotientGroup.mk' (OuterAutomorphisms.inner Y) (F.fld c) =
        QuotientGroup.mk' (OuterAutomorphisms.inner Y) (g * α * g⁻¹) := by
      rw [hgα, map_mul, hi1, one_mul]
    have h2' : (g * α * g⁻¹) ^ r ∈ OuterAutomorphisms.inner Y := by
      rw [conj_pow]
      exact hIn.conj_mem _ hα g
    have h3 : QuotientGroup.mk' (OuterAutomorphisms.inner Y) (F.fld (c ^ r)) = 1 := by
      rw [map_pow, map_pow, h1, ← map_pow]
      exact (QuotientGroup.eq_one_iff _).2 h2'
    exact (QuotientGroup.eq_one_iff _).1 h3
  obtain ⟨E, hEcard, hE, hEfix⟩ : ∃ E : Subgroup Y, Nat.card E = r ^ 2 ∧ IsElemAbelian r E ∧
      ∀ y ∈ E, F.fld c y = y := by
    by_cases hc1 : c = 1
    · obtain ⟨E, -, hE, hEcard⟩ :=
        CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := r) (H := (⊤ : Subgroup Y))
          (k := 2) (by rwa [← CFSG.SectionRank.pRank_eq_open_pRank_top])
      exact ⟨E, hEcard, hE, fun y _ => by rw [hc1, map_one, MulAut.one_apply]⟩
    · exact F.sq h2 c (orderOf_eq_prime hcr hc1)
  refine ⟨g⁻¹ * F.fld c * g, ?_, ?_, E.map (g⁻¹ : MulAut Y).toMonoidHom, hE.map _, ?_, ?_⟩
  · have hα' : α = g⁻¹ * (i * F.fld c) * g := by rw [← hgα]; group
    have heq : g⁻¹ * F.fld c * g * α⁻¹ = g⁻¹ * i⁻¹ * g⁻¹⁻¹ := by rw [hα']; group
    rw [heq]
    exact hIn.conj_mem _ ((OuterAutomorphisms.inner Y).inv_mem hi) g⁻¹
  · have h1 : (g⁻¹ * F.fld c * g⁻¹⁻¹) ^ r = g⁻¹ * F.fld c ^ r * g⁻¹⁻¹ := conj_pow
    rw [inv_inv] at h1
    rw [h1, ← map_pow, hcr, map_one, mul_one, inv_mul_cancel]
  · rw [Subgroup.card_map_of_injective (g⁻¹ : MulAut Y).injective, hEcard]
  · rintro _ ⟨e, he, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.mul_apply, MulAut.apply_inv_self, hEfix e he]

theorem outerRSplit_two_of_sp4 {X : Type} [Group X] [Finite X] {n r : ℕ}
    (hX : LieModel X .PSp 2 2 n) (hr : r.Prime) (hr5 : 5 ≤ r) (hrn : r ∣ 2 ^ n - 1) :
    OuterRSplit X r 2 := by
  have hn1 : 1 ≤ n := hX.admissible.2.1
  obtain ⟨K, hKf, hKfin, hcard, ⟨e⟩⟩ := (hX.statedClassicalModel (by decide)).2
  letI := hKf
  letI := hKfin
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two hn1 hcard
  have hrK : r ∣ Nat.card K - 1 := by rwa [hcard]
  have h2 : 2 ≤ CFSG.pRank r (StatedProj (StatedSp 2 K)) := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top,
      UC22.uc22p218c_pRank_model hr (by omega) hrK]
  exact (OuterRSplit.of_pFrame hr (CFSG.Quasithin.R3c18.pFrameSp4 hr hr5
    CFSG.Quasithin.R3c18.sp4PRankShape_holds K hcard hn1) h2).of_mulEquiv e.symm

section G2


theorem outerRSplit_two_of_g2 {X : Type} [Group X] [Finite X] {n r : ℕ}
    (hX : LieModel X .G2 0 2 n) (hr : r.Prime) (hr5 : 5 ≤ r) (hrn : r ∣ 2 ^ n - 1) :
    OuterRSplit X r 2 := by
  obtain ⟨hn2, K, hKf, hKfin, hcp, hcard, ⟨e⟩⟩ :=
    CFSG.QuasithinUnique.Setup.X6.exists_mulEquiv_G2_model
      (hX.chevalleyExceptionalModel (by decide))
  letI := hKf
  letI := hKfin
  have := hcp
  have hrK : r ∣ Nat.card K - 1 := by rwa [hcard]
  have h2 : 2 ≤ CFSG.pRank r (CFSG.Blueprint.Chevalley.adjointGroup .G2 K) := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact CFSG.LieType.Chevalley.two_le_pRank_G2_of_dvd hr hrK
  exact (OuterRSplit.of_pFrame hr (CFSG.Quasithin.R3c18.pFrameG2 hr hr5
    CFSG.Quasithin.R3c18.g2PRankShape_holds K hcard hn2) h2).of_mulEquiv e.symm

end G2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
