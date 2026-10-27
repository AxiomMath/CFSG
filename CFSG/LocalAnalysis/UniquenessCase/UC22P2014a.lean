module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P20a
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.T3Lift
public import CFSG.Quasithin.Background.A3ComponentsAmbient

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem uc22p2014a_not_dvd_card_of_le {p : ℕ} {M H N : Subgroup G}
    (hsp : IsStronglyPEmbedded p M) (hHM : ¬ H ≤ M) (hNM : N ≤ M)
    (hHN : H ≤ normalizer (N : Set G)) : ¬ p ∣ Nat.card N := by
  obtain ⟨h, hh, hhM⟩ := Set.not_subset.1 hHM
  intro hp
  refine hsp.2.2 h hhM (hp.trans (Subgroup.card_dvd_of_le (le_inf hNM fun n hn => ?_)))
  refine ⟨h⁻¹ * n * h, hNM ((Subgroup.mem_normalizer_iff''.1 (hHN hh) n).1 hn), ?_⟩
  simp [MulAut.conj_apply, mul_assoc]

theorem uc22p2014a_solvRad_le (D : Data G) (hB : ListBNonabelian) (h1930 : H1930 D)
    {H : Subgroup G} (hH : H ∈ hSet D.T D.M) : CFSG.Quasithin.solvRad H ≤ D.M := by
  rw [CFSG.Quasithin.solvRad_eq_map_solvableRadical]
  exact uc22p20a_oinf_le D hB h1930 hH

theorem uc22p2014a_le_normalizer_solvRad (H : Subgroup G) :
    H ≤ normalizer (CFSG.Quasithin.solvRad H : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (CFSG.Quasithin.solvRad_le H)).1
    (CFSG.Quasithin.solvRad_normal H)

theorem uc22p2014a_not_dvd_card_solvRad (D : Data G) (hB : ListBNonabelian) (h1930 : H1930 D)
    {p : ℕ} (hsp : IsStronglyPEmbedded p D.M) {H : Subgroup G} (hH : H ∈ hSet D.T D.M) :
    ¬ p ∣ Nat.card (CFSG.Quasithin.solvRad H) :=
  uc22p2014a_not_dvd_card_of_le hsp hH.2.1 (uc22p2014a_solvRad_le D hB h1930 hH)
    (uc22p2014a_le_normalizer_solvRad H)

theorem uc22p2014a_pRank_le_one (D : Data G) (h66 : UC6.R6_6 D) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hsp : IsStronglyPEmbedded p D.M) {H : Subgroup G} (hH : H ∈ hSet D.T D.M) :
    CFSG.Open.pRank p H ≤ 1 := by
  obtain ⟨N, hN, hHN⟩ := uc22p20a_exists_mem_calMOf D hH
  by_contra h
  have h2 : 2 ≤ CFSG.Open.pRank p N := by
    have := CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hp hHN
    omega
  exact hH.2.1 (((h66 p hp hp2).1 (Or.inl hsp) N hN h2) ▸ hHN)

theorem uc22p2014a_mem_of_conj_mem {p : ℕ} [Fact p.Prime] {M Q : Subgroup G}
    (hsp : IsStronglyPEmbedded p M) (hQ : IsPGroup p Q) (hQM : Q ≤ M) {x g : G} (hxQ : x ∈ Q)
    (hx1 : x ≠ 1) (hgx : g * x * g⁻¹ ∈ M) : g ∈ M := by
  by_contra hg
  have hg' : g⁻¹ ∉ M := fun h => hg (by simpa using M.inv_mem h)
  refine hsp.2.2 g⁻¹ hg' ?_
  have hU : zpowers x ≠ ⊥ := by
    rw [Ne, zpowers_eq_bot]
    exact hx1
  have hpU : p ∣ Nat.card (zpowers x) := by
    rcases (hQ.to_le (zpowers_le.mpr hxQ)).card_eq_or_dvd with h | h
    · exact absurd (Subgroup.card_eq_one.mp h) hU
    · exact h
  refine hpU.trans (Subgroup.card_dvd_of_le (zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨hQM hxQ, ?_⟩)))
  exact ⟨g * x * g⁻¹, hgx, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem uc22p2014a_exists_mul_mem_centralizer {p : ℕ} (hp : p.Prime) {R : Subgroup G}
    (hR : ¬ p ∣ Nat.card R) {x z : G} (hx : orderOf x = p)
    (hxR : x ∈ normalizer (R : Set G)) (hzR : z ∈ normalizer (R : Set G)) (hxz : ⁅x, z⁆ ∈ R) :
    ∃ r ∈ R, z * r ∈ centralizer ({x} : Set G) := by
  set C : Subgroup G := normalizer (R : Set G) with hCdef
  set E : Subgroup C := R.subgroupOf C with hEdef
  haveI : E.Normal := Subgroup.normal_in_normalizer
  have hE : ¬ p ∣ Nat.card E := by
    rwa [hEdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).toEquiv]
  set x' : C := ⟨x, hxR⟩ with hx'def
  set z' : C := ⟨z, hzR⟩ with hz'def
  have hx' : orderOf x' = p := by rw [← Subgroup.orderOf_coe]; exact hx
  have hc : ((z' : C) : C ⧸ E) ∈ centralizer ({((x' : C) : C ⧸ E)} : Set (C ⧸ E)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hEdef,
      Subgroup.mem_subgroupOf]
    have e : (((x' * z')⁻¹ * (z' * x') : C) : G) = (x * z)⁻¹ * ⁅x, z⁆⁻¹ * (x * z)⁻¹⁻¹ := by
      simp only [hx'def, hz'def, Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.1 (C.inv_mem (C.mul_mem hxR hzR)) _).1 (R.inv_mem hxz)
  obtain ⟨g, hg, hgz⟩ :=
    CFSG.GH74.GLS.Stage2.Bender.Thm2.T3.exists_lift_of_mem_centralizer_quotient E hp hE hx' hc
  rw [QuotientGroup.eq, hEdef, Subgroup.mem_subgroupOf] at hgz
  refine ⟨((g⁻¹ * z' : C) : G)⁻¹, R.inv_mem hgz, ?_⟩
  have e : z * ((g⁻¹ * z' : C) : G)⁻¹ = (g : G) := by
    simp only [hz'def, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e, Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  subst hh
  have := Subgroup.mem_centralizer_iff.1 hg x' (Set.mem_singleton x')
  exact congrArg Subtype.val this

end CFSG.LocalAnalysis.UniquenessCase.UC22
