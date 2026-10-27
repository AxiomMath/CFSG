module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4V1Cex

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ClassicalGroups.Unitary
open CFSG.LieType.Universal.Unitary (SUid)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

structure s16c4v1e3_Std (D : Data G) : Prop where
  dataExt : DataExt D
  sigmaStd : UC6S846.SigmaStd D
  h1219 : ∀ V₀ V : Subgroup G, Hyp125 D V₀ V → D.sig = D.sig1
  r61 : UC6.R6_1 D
  r126 : R126 D
  w3_111 : W3Thm111 G
  r129 : R129_1 D
  r1217 : R1217 D

variable {D : Data G} {V L : Subgroup G} {hV : IsElemAbelian 2 V}

private theorem s16c4v1e3_bdh_three_dvd_orderOf {x : G} (hx1 : x ≠ 1)
    (hx3 : IsPGroup 3 (Subgroup.zpowers x)) : 3 ∣ orderOf x := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := hx3.card_eq_or_dvd
  rw [Nat.card_zpowers] at h
  rcases h with h1 | h1
  · exact absurd (orderOf_eq_one_iff.mp h1) hx1
  · exact h1

private theorem s16c4v1e3_bdh_bad_conj (S : s16c4v1_Sit D V L hV) (hstd : s16c4v1e3_Std D)
    {g : G} (hg : g ∉ D.M) {u : G} (hu : u ∈ V) (hu1 : u ≠ 1)
    (hgu : g * u * g⁻¹ ∈ V) : s16c4v1_Bad D (g * u * g⁻¹) := by
  intro hle
  obtain ⟨x, hxM, hx1, hx3, hxu⟩ := s16c4v1_exists_three_fix S hu
  have hcomm : x * u = u * x := mul_inv_eq_iff_eq_mul.mp hxu
  have hgxg : g * x * g⁻¹ ∈ Subgroup.centralizer ({g * u * g⁻¹} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (g * x * g⁻¹) * (g * u * g⁻¹) = g * (x * u) * g⁻¹ := by group
      _ = g * (u * x) * g⁻¹ := by rw [hcomm]
      _ = (g * u * g⁻¹) * (g * x * g⁻¹) := by group
  have hxconj : x ∈ conjSubgroup D.M g := by
    rw [mem_conjSubgroup_iff]
    exact hle hgxg
  have hle2 : Subgroup.zpowers x ≤ D.M ⊓ conjSubgroup D.M g :=
    Subgroup.zpowers_le.mpr ⟨hxM, hxconj⟩
  have h3dvd : 3 ∣ Nat.card ↥(D.M ⊓ conjSubgroup D.M g) := by
    have hdvd := Subgroup.card_dvd_of_le hle2
    rw [Nat.card_zpowers] at hdvd
    exact (s16c4v1e3_bdh_three_dvd_orderOf hx1 hx3).trans hdvd
  have h3sig : 3 ∈ D.sig := by
    rw [S.case4.2.2]
    exact Set.mem_singleton 3
  have h3sig1 : 3 ∈ D.sig1 := by
    rw [← hstd.h1219 ⊥ V S.sect.setting.hyp16.hyp125]
    exact h3sig
  have hse : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M :=
    hstd.sigmaStd.sig1_sp 3 h3sig1
  have hginv : g⁻¹ ∉ D.M := fun h => hg (by simpa using D.M.inv_mem h)
  exact (hse.2.2 g⁻¹ hginv) (by simpa [conjSubgroup] using h3dvd)

theorem s16c4v1e3_bad_sing (S : s16c4v1_Sit D V L hV) (hstd : s16c4v1e3_Std D) {v : G}
    (hv : v ∈ V) (hv1 : v ≠ 1) (hbad : s16c4v1_Bad D v) :
    s16c4v1_vec S v ≠ 0 ∧ herm S.F.σ (s16c4v1_vec S v) (s16c4v1_vec S v) = 0 := by
  by_contra hcon
  have h3 : 3 ∈ D.sig := by
    rw [S.case4.2.2]
    exact Set.mem_singleton 3
  have hcase : s16c4v1_vec S v = 0 ∨
      herm S.F.σ (s16c4v1_vec S v) (s16c4v1_vec S v) ≠ 0 := by
    by_cases h0 : s16c4v1_vec S v = 0
    · exact Or.inl h0
    · exact Or.inr fun hh => hcon ⟨h0, hh⟩
  obtain ⟨P, hPM, hP3, hPnc, hPv⟩ := s16c4v1_noncyclic_centralizer S hv hcase
  exact hbad (centralizer_le_of_noncyclic D hstd.r61 h3 hPM hP3 hPnc hv1
    ⟨1, by simpa using hV.2 v hv⟩ hPv)

theorem s16c4v1e3_bad_of_mem_inf (S : s16c4v1_Sit D V L hV) (hstd : s16c4v1e3_Std D) {g : G}
    (hg : g ∉ D.M) {v : G} (hv : v ∈ V) (hv1 : v ≠ 1) (hgv : g * v * g⁻¹ ∈ V) :
    s16c4v1_Bad D v ∧ s16c4v1_Bad D (g * v * g⁻¹) := by
  have he : g⁻¹ * (g * v * g⁻¹) * (g⁻¹)⁻¹ = v := by group
  have hmem : g⁻¹ * (g * v * g⁻¹) * (g⁻¹)⁻¹ ∈ V := by rw [he]; exact hv
  have hgv1 : g * v * g⁻¹ ≠ 1 := by
    intro h
    apply hv1
    calc v = g⁻¹ * (g * v * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  have hginv : g⁻¹ ∉ D.M := fun h => hg (by simpa using D.M.inv_mem h)
  exact ⟨he ▸ s16c4v1e3_bdh_bad_conj S hstd hginv hgv hgv1 hmem,
    s16c4v1e3_bdh_bad_conj S hstd hg hv hv1 hgv⟩

theorem s16c4v1e3_cex_cent_V1 (S : s16c4v1_Sit D V L hV) (hstd : s16c4v1e3_Std D) {g : G}
    (hg : s16c4v1_Cex D V g) (hg' : s16c4v1_Cex D V g⁻¹) :
    ∀ a ∈ conjSubgroup V g, ∀ x ∈ v1Sub D.M ⊥ V hV L, a * x * a⁻¹ = x := by
  intro a ha x hx
  have hVn := S.sect.setting.hyp16.hyp125.pairFacts.le_normalizer
  have hxV : x ∈ V := s16c4v1_v1_le S hx
  have hcV1 : a * x * a⁻¹ * x⁻¹ ∈ v1Sub D.M ⊥ V hV L := by
    have h1 := s16c4v1_conj_mem_v1 S (hg.1 ha) hx
    exact (v1Sub D.M ⊥ V hV L).mul_mem h1 ((v1Sub D.M ⊥ V hV L).inv_mem hx)
  have hcA : a * x * a⁻¹ * x⁻¹ ∈ conjSubgroup V g := by
    have h1 : x * a⁻¹ * x⁻¹ ∈ conjSubgroup V g :=
      s16c4v1_cxh_conj_mem_of_conj_le hVn hg'.1 hxV ((conjSubgroup V g).inv_mem ha)
    have h2 : a * (x * a⁻¹ * x⁻¹) ∈ conjSubgroup V g :=
      (conjSubgroup V g).mul_mem ha h1
    rwa [show a * (x * a⁻¹ * x⁻¹) = a * x * a⁻¹ * x⁻¹ by group] at h2
  have hc1 : a * x * a⁻¹ * x⁻¹ = 1 := by
    by_contra hne
    have hcV : a * x * a⁻¹ * x⁻¹ ∈ V := s16c4v1_v1_le S hcV1
    have hbad := (s16c4v1e3_bad_of_mem_inf S hstd (s16c4v1_cxh_not_mem S hg) hcV hne
      ((mem_conjSubgroup_iff).1 hcA)).1
    have hsing := (s16c4v1e3_bad_sing S hstd hcV hne hbad).1
    exact hsing ((s16c4v1_vec_eq_zero_iff S hcV).2 hcV1)
  exact mul_inv_eq_one.1 hc1

theorem s16c4v1e3_cex_D_sing (S : s16c4v1_Sit D V L hV) (hstd : s16c4v1e3_Std D) {g : G}
    (hg : s16c4v1_Cex D V g) (hg' : s16c4v1_Cex D V g⁻¹) :
    ∀ d ∈ ⁅V, conjSubgroup V g⁆, d ≠ 1 →
      s16c4v1_vec S d ≠ 0 ∧ herm S.F.σ (s16c4v1_vec S d) (s16c4v1_vec S d) = 0 := by
  intro d hd hd1
  have hVn := S.sect.setting.hyp16.hyp125.pairFacts.le_normalizer
  have hdle : d ∈ V ⊓ conjSubgroup V g :=
    s16c4v1_cex_comm_le hVn hg.1 hg'.1 hd
  have hdV : d ∈ V := (Subgroup.mem_inf.1 hdle).1
  have hdA : d ∈ conjSubgroup V g := (Subgroup.mem_inf.1 hdle).2
  exact s16c4v1e3_bad_sing S hstd hdV hd1
    ((s16c4v1e3_bad_of_mem_inf S hstd (s16c4v1_cxh_not_mem S hg) hdV hd1
      ((mem_conjSubgroup_iff).1 hdA)).1)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
