module

public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveNineExFix
public import CFSG.GH74.GLS.Stage4.T6SylG

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {M V₀ V U S H : Subgroup G}

private lemma orderOf_conj_eq {Y : Type} [Group Y] (k c : Y) :
    orderOf (k * c * k⁻¹) = orderOf c :=
  (SemiconjBy.orderOf_eq k (x := c) (y := k * c * k⁻¹)
    (by simp [SemiconjBy, mul_assoc])).symm

private lemma conj_mem_center_map_subtype {X : Type} [Group X] {N : Subgroup X} [N.Normal]
    {x : X} (hx : x ∈ (Subgroup.center ↥N).map N.subtype) (g : X) :
    g * x * g⁻¹ ∈ (Subgroup.center ↥N).map N.subtype :=
  (inferInstance : ((Subgroup.center ↥N).map N.subtype).Normal).conj_mem x hx g

private theorem odd_card_fusionOddCore (X : Type) [Group X] [Finite X] :
    Odd (Nat.card (fusionOddCore X)) := by
  have h : fusionOddCore X = CFSG.pPrimeCore 2 X := by
    unfold fusionOddCore CFSG.pPrimeCore
    congr 1
    ext K
    simp [Nat.coprime_two_left]
  rw [h]
  exact Nat.coprime_two_left.1 (CFSG.pPrimeCore_coprime_card (p := 2) (G := X))

private lemma eq_one_of_mem_of_pow_two_eq_one {X : Type} [Group X] {N : Subgroup X}
    (hodd : Odd (Nat.card N)) {x : X} (hx : x ∈ N) (k : ℕ) (h2 : x ^ 2 ^ k = 1) :
    x = 1 := by
  have h1 : orderOf (⟨x, hx⟩ : ↥N) = 1 := by
    refine Nat.eq_one_of_dvd_coprimes ((Nat.coprime_two_left.mpr hodd).pow_left k) ?_ ?_
    · rw [Subgroup.orderOf_mk]
      exact orderOf_dvd_of_pow_eq_one h2
    · exact orderOf_dvd_natCard _
  have := congrArg Subtype.val (orderOf_eq_one_iff.mp h1)
  simpa using this

namespace ExCfg

variable {X : Type} [Group X] {φ : ↥(conjClosure V H) →* X} {p : ℕ}

theorem centralizer_closure_of_map_mem_center (c : ExCfg M V₀ V U S H φ p)
    (hcen : ∀ q : ↥(conjClosure V H), Odd (orderOf q) →
      φ q ∈ (Subgroup.center ↥(fusionOddCore X)).map (fusionOddCore X).subtype →
      (q : G) ∈ centralizer (V₀ : Set G))
    {q : ↥(conjClosure V H)}
    (hq : φ q ∈ (Subgroup.center ↥(fusionOddCore X)).map (fusionOddCore X).subtype) :
    (q : G) ∈ centralizer (conjClosure V₀ (conjClosure V H) : Set G) := by
  haveI : Finite X := Finite.of_surjective φ c.bar.surjective
  obtain ⟨q2, q2', hq_eq, _, hq2_two, hq2'_odd, hq2_zp, hq2'_zp⟩ :=
    CFSG.GH74.GLS.Stage4.Rest.T6.t6_two_part_decomp q
  have hq2ZN : φ q2 ∈ (Subgroup.center ↥(fusionOddCore X)).map (fusionOddCore X).subtype := by
    have hle : Subgroup.zpowers (φ q) ≤
        (Subgroup.center ↥(fusionOddCore X)).map (fusionOddCore X).subtype :=
      Subgroup.zpowers_le.mpr hq
    have hmem : φ q2 ∈ Subgroup.zpowers (φ q) := by
      have hmem' : φ q2 ∈ (Subgroup.zpowers q).map φ :=
        Subgroup.mem_map.mpr ⟨q2, hq2_zp, rfl⟩
      rwa [MonoidHom.map_zpowers φ q] at hmem'
    exact hle hmem
  have hq2N : φ q2 ∈ fusionOddCore X :=
    Subgroup.map_subtype_le (Subgroup.center ↥(fusionOddCore X)) hq2ZN
  have hq2_eq_one : φ q2 = 1 := by
    obtain ⟨k, hk⟩ := hq2_two
    refine eq_one_of_mem_of_pow_two_eq_one (odd_card_fusionOddCore X) hq2N k ?_
    have := congrArg φ hk
    simpa using this
  have hI_le : conjClosure V₀ (conjClosure V H) ≤ iSub16 V H :=
    conjClosure_V₀_conjClosure_le_iSub16 c.five c.std c.cex c.min.1 c.not_le
  have hq2_cen : (q2 : G) ∈
      centralizer (conjClosure V₀ (conjClosure V H) : Set G) :=
    Subgroup.centralizer_le (fun _ hx => hI_le hx)
      (c.pCore_le ((c.bar.ker_iff q2).mp hq2_eq_one))
  have hq2'_cen : (q2' : G) ∈
      centralizer (conjClosure V₀ (conjClosure V H) : Set G) := by
    have hle : conjClosure V₀ (conjClosure V H) ≤
        Subgroup.centralizer ({(q2' : G)} : Set G) := by
      rw [conjClosure, Subgroup.closure_le]
      rintro x ⟨g, hg, y, hy, rfl⟩
      change g * y * g⁻¹ ∈ Subgroup.centralizer ({(q2' : G)} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      let kinv : ↥(conjClosure V H) :=
        ⟨(g : G)⁻¹, (conjClosure V H).inv_mem hg⟩
      have hodd : Odd (orderOf (kinv * q2' * kinv⁻¹)) := by
        rw [orderOf_conj_eq]
        exact hq2'_odd
      have hφq2' : φ q2' ∈
          (Subgroup.center ↥(fusionOddCore X)).map (fusionOddCore X).subtype := by
        have hle' : Subgroup.zpowers (φ q) ≤
            (Subgroup.center ↥(fusionOddCore X)).map (fusionOddCore X).subtype :=
          Subgroup.zpowers_le.mpr hq
        have hmem : φ q2' ∈ Subgroup.zpowers (φ q) := by
          have hmem' : φ q2' ∈ (Subgroup.zpowers q).map φ :=
            Subgroup.mem_map.mpr ⟨q2', hq2'_zp, rfl⟩
          rwa [MonoidHom.map_zpowers φ q] at hmem'
        exact hle' hmem
      have hφconj : φ (kinv * q2' * kinv⁻¹) ∈
          (Subgroup.center ↥(fusionOddCore X)).map (fusionOddCore X).subtype := by
        rw [map_mul, map_mul, map_inv]
        exact conj_mem_center_map_subtype hφq2' (φ kinv)
      have hmemcen : ((kinv * q2' * kinv⁻¹ : ↥(conjClosure V H)) : G) ∈
          centralizer (V₀ : Set G) :=
        hcen (kinv * q2' * kinv⁻¹) hodd hφconj
      have hz : ((kinv * q2' * kinv⁻¹ : ↥(conjClosure V H)) : G)
          = (g : G)⁻¹ * (q2' : G) * (g : G) := by
        simp [kinv, mul_assoc]
      have hcomm : y * ((g : G)⁻¹ * (q2' : G) * (g : G))
          = ((g : G)⁻¹ * (q2' : G) * (g : G)) * y := by
        rw [← hz]
        exact (Subgroup.mem_centralizer_iff.mp hmemcen) y hy
      calc (g * y * g⁻¹) * q2'
          = g * (y * ((g : G)⁻¹ * (q2' : G) * (g : G))) * (g : G)⁻¹ := by group
        _ = g * (((g : G)⁻¹ * (q2' : G) * (g : G)) * y) * (g : G)⁻¹ := by rw [hcomm]
        _ = q2' * (g * y * g⁻¹) := by group
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hx)
  have hqe : (q : G) = (q2 : G) * (q2' : G) := by
    simpa using congrArg Subtype.val hq_eq
  rw [hqe]
  exact (Subgroup.centralizer (conjClosure V₀ (conjClosure V H) : Set G)).mul_mem
    hq2_cen hq2'_cen

theorem map_mem_center_of_mem_centralizer_closure (c : ExCfg M V₀ V U S H φ p)
    {q : ↥(conjClosure V H)} (hqN : φ q ∈ fusionOddCore X)
    (hq : (q : G) ∈ centralizer (conjClosure V₀ (conjClosure V H) : Set G)) :
    φ q ∈ (Subgroup.center ↥(fusionOddCore X)).map (fusionOddCore X).subtype := by
  haveI : Finite X := Finite.of_surjective φ c.bar.surjective
  obtain ⟨q2, q2', hq_eq, _, hq2_two, hq2'_odd, hq2_zp, hq2'_zp⟩ :=
    CFSG.GH74.GLS.Stage4.Rest.T6.t6_two_part_decomp q
  have hq2N : φ q2 ∈ fusionOddCore X := by
    have hle : Subgroup.zpowers (φ q) ≤ fusionOddCore X :=
      Subgroup.zpowers_le.mpr hqN
    have hmem : φ q2 ∈ Subgroup.zpowers (φ q) := by
      have hmem' : φ q2 ∈ (Subgroup.zpowers q).map φ :=
        Subgroup.mem_map.mpr ⟨q2, hq2_zp, rfl⟩
      rwa [MonoidHom.map_zpowers φ q] at hmem'
    exact hle hmem
  have hq2'N : φ q2' ∈ fusionOddCore X := by
    have hle : Subgroup.zpowers (φ q) ≤ fusionOddCore X :=
      Subgroup.zpowers_le.mpr hqN
    have hmem : φ q2' ∈ Subgroup.zpowers (φ q) := by
      have hmem' : φ q2' ∈ (Subgroup.zpowers q).map φ :=
        Subgroup.mem_map.mpr ⟨q2', hq2'_zp, rfl⟩
      rwa [MonoidHom.map_zpowers φ q] at hmem'
    exact hle hmem
  have hq2_eq_one : φ q2 = 1 := by
    obtain ⟨k, hk⟩ := hq2_two
    refine eq_one_of_mem_of_pow_two_eq_one (odd_card_fusionOddCore X) hq2N k ?_
    have := congrArg φ hk
    simpa using this
  have hq2'_I' : (q2' : G) ∈
      centralizer (conjClosure V₀ (conjClosure V H) : Set G) := by
    have hzp : Subgroup.zpowers (q : G) ≤
        centralizer (conjClosure V₀ (conjClosure V H) : Set G) :=
      Subgroup.zpowers_le.mpr hq
    have hmem : (q2' : G) ∈ Subgroup.zpowers (q : G) := by
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hq2'_zp
      rw [Subgroup.mem_zpowers_iff]
      refine ⟨n, ?_⟩
      rw [← hn]
      exact (map_zpow (Subgroup.subtype (conjClosure V H)) q n).symm
    exact hzp hmem
  have hq2'V₀ : (q2' : G) ∈ centralizer (V₀ : Set G) :=
    Subgroup.centralizer_le
      (fun _ hx => le_conjClosure V₀ (conjClosure V H) hx) hq2'_I'
  have hφq2' : φ q2' ∈
      (Subgroup.center ↥(fusionOddCore X)).map (fusionOddCore X).subtype :=
    IsMinFam16.map_mem_center_of_mem_centralizer_V₀ c.one c.std c.cex c.min c.not_le
      c.bar c.shape c.prime c.extra c.card hq2'_odd hq2'N hq2'V₀
  have hq_eq' : φ q = φ q2' := by
    rw [hq_eq, map_mul, hq2_eq_one, one_mul]
  rwa [hq_eq']

end ExCfg

end CFSG.LocalAnalysis.WeakClosure81

end
