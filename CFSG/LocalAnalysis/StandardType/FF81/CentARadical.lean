module

public import CFSG.LocalAnalysis.StandardType.FF81.Defs
import CFSG.RankThree.PartTwo.Sec21.FF81FS79SZ

public section

namespace CFSG.StandardType.FF81.CentA

theorem exists_odd_radical {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    (hA : HypA G n b L) {z : Fin 3 → ↥L} (hloc : LocalFacts b L z) {K : ℕ → Subgroup G} {t : G}
    (hFS : FrameSystem n b L K t) {Y : Subgroup G} (hYd : YData n b L Y t) :
    ∃ R : Subgroup G, R ≤ Subgroup.centralizer (Y : Set G) ∧ Odd (Nat.card R) ∧
      Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer (L : Set G) ≤
        R ⊔ Subgroup.zpowers b := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Cb : Subgroup G := Subgroup.centralizer ({b} : Set G)
  let CL : Subgroup G := Subgroup.centralizer (L : Set G)
  let D : Subgroup G := Cb ⊓ CL
  let Z : Subgroup G := Subgroup.zpowers b
  have hbCb : b ∈ Cb := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hbCL : b ∈ CL :=
    Subgroup.mem_centralizer_iff.mpr fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mp (hA.le hx)
  have hbD : b ∈ D := ⟨hbCb, hbCL⟩
  have hZle : Z ≤ D := Subgroup.zpowers_le.mpr hbD
  have hZc : ∀ r ∈ D, ∀ z ∈ Z, r * z = z * r := by
    intro r hr z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact (Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp hr.1) k).eq
  have hZ3 : Nat.card Z = 3 := by rw [Nat.card_zpowers, hA.ord]
  have hZpg : IsPGroup 3 Z :=
    IsPGroup.of_card (n := 1) (by rw [hZ3]; norm_num)
  have hZn : (Z.subgroupOf D).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      change ((g * n * g⁻¹ : ↥D) : G) ∈ Z
      have hcomm : (g : G) * (n : G) = (n : G) * (g : G) :=
        hZc (g : G) g.2 (n : G) hn
      have hval : ((g * n * g⁻¹ : ↥D) : G) = (n : G) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [hcomm]
        group
      rw [hval]
      exact hn⟩
  haveI : (Z.subgroupOf D).Normal := hZn
  have hZpg' : IsPGroup 3 (Z.subgroupOf D) :=
    hZpg.of_equiv (Subgroup.subgroupOfEquivOfLe hZle).symm
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 3 ↥D))
  have hZP : Z.subgroupOf D ≤ (P : Subgroup ↥D) :=
    IsPGroup.le_sylow_of_normal (N := Z.subgroupOf D) hZpg' P
  have hPpg : IsPGroup 3 ((P : Subgroup ↥D).map D.subtype) :=
    P.isPGroup'.map D.subtype
  have hPmap : (P : Subgroup ↥D).map D.subtype = Z := by
    refine hloc.syl _ ?_ ?_ hPpg ?_
    · rintro _ ⟨y, -, rfl⟩
      exact y.2.2
    · rintro _ ⟨y, -, rfl⟩
      exact y.2.1
    · intro x hx
      have hxD : x ∈ D := hZle hx
      have hxP : (⟨x, hxD⟩ : ↥D) ∈ (P : Subgroup ↥D) :=
        hZP (by rw [Subgroup.mem_subgroupOf]; exact hx)
      exact ⟨⟨x, hxD⟩, hxP, rfl⟩
  have hPZ : (P : Subgroup ↥D) = Z.subgroupOf D := by
    rw [← Subgroup.map_subtype_inj (H := D)]
    rw [Subgroup.subgroupOf_map_subtype, hPmap]
    exact (inf_eq_left.mpr hZle).symm
  have hZnd : ¬ 3 ∣ (Z.subgroupOf D).index := by
    rw [← hPZ]
    exact P.not_dvd_index
  have hcop : ∀ r ∈ D, ∃ m : ℕ, Nat.Coprime 3 m ∧ r ^ m ∈ Z := by
    intro r hr
    refine ⟨(Z.subgroupOf D).index, ?_, ?_⟩
    · rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
      exact hZnd
    · have h1 : (⟨r, hr⟩ : ↥D) ^ (Z.subgroupOf D).index ∈ Z.subgroupOf D :=
        Subgroup.pow_index_mem (Z.subgroupOf D) ⟨r, hr⟩
      rw [Subgroup.mem_subgroupOf] at h1
      simpa using h1
  obtain ⟨O, hOR, -, hdec, hOc⟩ :=
    CFSG.RankThree.PartTwo.Sec21.FF81.exists_central_complement hZle hZc hZ3 hcop
  have hCLn : (CL.subgroupOf (Subgroup.normalizer (L : Set G))).Normal :=
    Subgroup.normal_subgroupOf_centralizer_normalizer (L : Set G)
  have hNle : Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (CL : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (Subgroup.centralizer_le_normalizer (L : Set G))).mp hCLn
  have hO_le_Cb : O ≤ Cb := hOR.trans inf_le_left
  have hO_ndvd : ¬ 3 ∣ Nat.card O :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hOc
  have hconj : ∀ g ∈ Cb, ∀ x ∈ O, g * x * g⁻¹ ∈ O := by
    intro g hg x hx
    have hxD : x ∈ D := hOR hx
    have hgxD : g * x * g⁻¹ ∈ D := by
      refine ⟨?_, ?_⟩
      · exact Cb.mul_mem (Cb.mul_mem hg hxD.1) (Cb.inv_mem hg)
      · exact (Subgroup.mem_normalizer_iff.mp (hNle (hA.nor hg)) x).mp hxD.2
    exact CFSG.RankThree.PartTwo.Sec21.FF81.conj_mem_complement hZc hZ3 hOR hdec hOc hx hgxD
  have hO_norm : (O.subgroupOf Cb).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hO_le_Cb]
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact hconj g hg x
    · intro hx
      have h2 := hconj g⁻¹ (Cb.inv_mem hg) (g * x * g⁻¹) hx
      have h3 : g⁻¹ * (g * x * g⁻¹) * (g⁻¹)⁻¹ = x := by group
      rwa [h3] at h2
  refine ⟨O, hYd.core O hO_le_Cb hO_norm hO_ndvd,
    hFS.odd_core O hO_le_Cb hO_norm hO_ndvd, ?_⟩
  intro r hr
  obtain ⟨z, hz, x, hx, rfl⟩ := hdec r hr
  rw [sup_comm]
  exact Subgroup.mul_mem_sup hz hx

end CFSG.StandardType.FF81.CentA

end
