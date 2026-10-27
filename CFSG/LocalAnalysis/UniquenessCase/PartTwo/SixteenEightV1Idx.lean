module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightV1Card
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen21Star
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7Eseven
import CFSG.GroupTheory.NormalizerInfCentralizer
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16e_index_dvd_of_range {A B : Type*} [Group A] [Finite A] [Group B] (φ : A →* B)
    {C Y : Subgroup A} (hker : φ.ker ≤ C) (hYC : Y ≤ C) {k : ℕ}
    (hk : Nat.card φ.range ∣ k * Nat.card (Y.map φ)) : C.index ∣ k := by
  have h1 : (C.map φ).relIndex φ.range = C.index := by
    rw [MonoidHom.range_eq_map, Subgroup.relIndex_map_map, top_sup_eq,
      Subgroup.relIndex_top_right, sup_of_le_left hker]
  have h2 := Subgroup.relIndex_mul_card (H := C.map φ) (K := φ.range)
  rw [inf_of_le_left (Subgroup.map_le_range φ C), h1] at h2
  obtain ⟨t, ht⟩ : Nat.card (Y.map φ) ∣ Nat.card (C.map φ) :=
    Subgroup.card_dvd_of_le (Subgroup.map_mono hYC)
  haveI : Finite φ.range := Finite.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  haveI : Finite (Y.map φ) :=
    Finite.of_injective (Subgroup.inclusion (Subgroup.map_le_range φ Y))
      (Subgroup.inclusion_injective _)
  have hpos : 0 < Nat.card (Y.map φ) := Nat.card_pos
  rw [← h2, ht] at hk
  have h3 : Nat.card (Y.map φ) * (C.index * t) ∣ Nat.card (Y.map φ) * k := by
    have : Nat.card (Y.map φ) * (C.index * t) = C.index * (Nat.card (Y.map φ) * t) := by ring
    rw [this, mul_comm (Nat.card (Y.map φ)) k]
    exact hk
  exact (Dvd.intro t rfl).trans ((Nat.mul_dvd_mul_iff_left hpos).1 h3)

theorem s16e_relIndex_cent_v1_dvd (D : Data G) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (h : Hyp125 D V₀ V) (h0 : V₀ = ⊥) (hL : L ≤ D.M)
    (hLV₁ : ∀ x ∈ L, ∀ u ∈ v1Sub D.M V₀ V hV L, x * u = u * x) {k : ℕ}
    (hk : Nat.card (Mbar D.M V₀ V hV) ∣ k * Nat.card (lBar V₀ V hV L)) :
    (D.M ⊓ centralizer (v1Sub D.M V₀ V hV L : Set G)).relIndex D.M ∣ k := by
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.pairFacts.le_normalizer h.pairFacts.le_normalizer₀
  let φ : ↥D.M →* MulAut (Vtil V₀ V hV) :=
    (actTil V₀ V hV).comp (Subgroup.inclusion hMs)
  let C : Subgroup ↥D.M :=
    (D.M ⊓ centralizer (v1Sub D.M V₀ V hV L : Set G)).subgroupOf D.M
  let Y : Subgroup ↥D.M := L.subgroupOf D.M
  have hrange : φ.range = Mbar D.M V₀ V hV := by
    change ((actTil V₀ V hV).comp (Subgroup.inclusion hMs)).range = _
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    rfl
  have hmap : Y.map φ = lBar V₀ V hV L := by
    unfold lBar
    ext ψ
    rw [Subgroup.mem_map, mem_barSub]
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨Subgroup.inclusion hMs g,
        by simpa only [Subgroup.coe_inclusion] using (Subgroup.mem_subgroupOf.1 hg), rfl⟩
    · rintro ⟨g, hgL, rfl⟩
      exact ⟨⟨(g : G), hL hgL⟩, Subgroup.mem_subgroupOf.2 hgL, rfl⟩
  have hker : φ.ker ≤ C := by
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    have h1 : ∀ v ∈ V, (g : G) * v * (g : G)⁻¹ * v⁻¹ ∈ V₀ := by
      intro v hv
      have h2 := (actTil_eq_one_iff V₀ V hV (Subgroup.inclusion hMs g)).1 hg v hv
      simpa only [Subgroup.coe_inclusion] using h2
    refine Subgroup.mem_subgroupOf.2 ⟨g.2, ?_⟩
    exact Subgroup.mem_centralizer_iff.2 fun u hu => by
      have huV : u ∈ V := s15_Infra_v1Sub_le h hV hu
      have h3 := h1 u huV
      rw [h0, Subgroup.mem_bot] at h3
      have h4 : (g : G) * u * (g : G)⁻¹ = u := by
        rw [mul_inv_eq_one] at h3
        exact h3
      have h5 : (g : G) * u = u * (g : G) := by
        calc (g : G) * u = ((g : G) * u * (g : G)⁻¹) * (g : G) := by group
          _ = u * (g : G) := by rw [h4]
      exact h5.symm
  have hYC : Y ≤ C := by
    intro x hx
    refine Subgroup.mem_subgroupOf.2 ⟨x.2, ?_⟩
    exact Subgroup.mem_centralizer_iff.2 fun u hu =>
      (hLV₁ (x : G) (Subgroup.mem_subgroupOf.1 hx) u hu).symm
  have hk' : Nat.card φ.range ∣ k * Nat.card (Y.map φ) := by
    rw [hrange, hmap]
    exact hk
  change C.index ∣ k
  exact s16e_index_dvd_of_range φ hker hYC (k := k) hk'

theorem s16e_exists_noncyclic_inf_of_relIndex_dvd {p : ℕ} (hp : p.Prime) {M C E : Subgroup G}
    (hCM : C ≤ M) (hN : M ≤ normalizer (C : Set G)) (hEM : E ≤ M)
    (hEel : IsElemAbelian p E) (hEcard : Nat.card E = p ^ 3) {k : ℕ}
    (hk : C.relIndex M ∣ k) (hpk : ¬ p ^ 2 ∣ k) :
    IsPGroup p ↥(E ⊓ C) ∧ ¬ IsCyclic ↥(E ⊓ C) := by
  have hCsub : (C.subgroupOf M).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hCM).2 hN
  have h1 : (C.subgroupOf M).relIndex (E.subgroupOf M) ∣ (C.subgroupOf M).index :=
    Subgroup.relIndex_dvd_index_of_normal (C.subgroupOf M) (E.subgroupOf M)
  rw [Subgroup.relIndex_subgroupOf hEM] at h1
  have h3 : C.relIndex E ∣ k := h1.trans hk
  have h5 : C.relIndex E * Nat.card ↥(C ⊓ E) = p ^ 3 := by
    rw [← hEcard]
    exact Subgroup.relIndex_mul_card (H := C) (K := E)
  have hrdvd : C.relIndex E ∣ p ^ 3 := Dvd.intro _ h5
  obtain ⟨j, hj3, hj⟩ := (Nat.dvd_prime_pow hp).1 hrdvd
  have hj1 : j ≤ 1 := by
    by_contra hjn
    have hpj : p ^ j ∣ k := hj ▸ h3
    exact hpk ((pow_dvd_pow p (by omega : 2 ≤ j)).trans hpj)
  have hcard : p ^ 2 ≤ Nat.card ↥(E ⊓ C) := by
    rw [inf_comm]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hj1 with rfl | rfl
    · rw [hj, pow_zero, one_mul] at h5
      rw [h5]
      exact Nat.pow_le_pow_right hp.pos (by norm_num)
    · rw [hj, pow_one] at h5
      have : Nat.card ↥(C ⊓ E) = p ^ 2 := by
        refine Nat.eq_of_mul_eq_mul_left hp.pos ?_
        rw [h5]
        ring
      exact this.ge
  have hel : IsElemAbelian p (E ⊓ C) := hEel.mono inf_le_left
  exact ⟨hel.isPGroup, s16c7_not_isCyclic_of_elemAbelian hp hel hcard⟩

theorem s16e_exists_noncyclic_cent_of_case168_2Star (D : Data G) (hSg : UC6S846.SigmaStd D)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Hyp151 D V₀ V L) (h0 : V₀ = ⊥)
    (hc : Case168_2Star D V₀ V hV L) :
    ∃ B : Subgroup G, B ≤ D.M ∧ IsPGroup 3 B ∧ ¬ IsCyclic B ∧
      ∀ b ∈ B, ∀ u ∈ v1Sub D.M V₀ V hV L, b * u = u * b := by
  have hsig : D.sig = {3} := hc.2.2
  have h3 : 3 ∈ D.sig := by rw [hsig]; exact Set.mem_singleton 3
  obtain ⟨E, hEM, hEel, hEcard⟩ :=
    UC6S846.exists_elemAbelian_card_of_le_pRank (M := D.M) Nat.prime_three (k := 3)
      (hSg.three_le 3 h3)
  have hLV₁ : ∀ x ∈ L, ∀ u ∈ v1Sub D.M V₀ V hV L, x * u = u * x :=
    fun x hx u hu => Sixteen21.commute_of_mem_v1Sub hV hS h0 hx hu
  have hdvd : (D.M ⊓ centralizer (v1Sub D.M V₀ V hV L : Set G)).relIndex D.M ∣ 12 :=
    s16e_relIndex_cent_v1_dvd D hV hS.hyp125 h0 hS.le hLV₁
      (s16e_card_mbar_dvd D V₀ V L hV hc)
  have hN : D.M ≤ normalizer ((D.M ⊓ centralizer (v1Sub D.M V₀ V hV L : Set G) : Subgroup G) :
      Set G) := fun x hx =>
    CFSG.GroupTheory.mem_normalizer_inf_centralizer
      (s15_Infra_le_normalizer_v1Sub hS.hyp125 hV hx) (Subgroup.le_normalizer hx)
  obtain ⟨hp3, hnc⟩ := s16e_exists_noncyclic_inf_of_relIndex_dvd Nat.prime_three
    inf_le_left hN hEM hEel hEcard hdvd (by norm_num)
  refine ⟨E ⊓ (D.M ⊓ centralizer (v1Sub D.M V₀ V hV L : Set G)), ?_, hp3, hnc, ?_⟩
  · exact inf_le_right.trans inf_le_left
  · intro b hb u hu
    have hbc : b ∈ centralizer (v1Sub D.M V₀ V hV L : Set G) := hb.2.2
    exact (Subgroup.mem_centralizer_iff.1 hbc u hu).symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
