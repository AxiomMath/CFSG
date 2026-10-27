module

public import CFSG.LocalAnalysis.ZStar.PrincipalBlockCandidate

public section

namespace CFSG

namespace ZStar.BrauerSylowFusion

open ZStar.Helpers ZStar

universe u v

noncomputable section

abbrev groupAlgebraEquiv {H : Type u} {K : Type v}
    [Group H] [Group K] (e : H ≃* K) :
    GroupAlgebraTwo H ≃+* GroupAlgebraTwo K :=
  MonoidAlgebra.mapDomainRingEquiv (ZMod 2) e

@[simp]
theorem groupAlgebraEquiv_single {H : Type u} {K : Type v}
    [Group H] [Group K] (e : H ≃* K) (h : H) (r : ZMod 2) :
    groupAlgebraEquiv e (MonoidAlgebra.single h r) =
      MonoidAlgebra.single (e h) r := by
  exact MonoidAlgebra.mapDomainRingEquiv_single e r h

@[simp]
theorem groupAlgebraEquiv_coeff_apply {H : Type u} {K : Type v}
    [Group H] [Group K] (e : H ≃* K)
    (x : GroupAlgebraTwo H) (h : H) :
    (groupAlgebraEquiv e x).coeff (e h) = x.coeff h := by
  rw [MonoidAlgebra.coeff_mapDomainRingEquiv]
  simp

private theorem groupAlgebraEquiv_isGroupCentral {H : Type u} {K : Type v}
    [Group H] [Group K] (e : H ≃* K)
    {x : GroupAlgebraTwo H} (hx : IsGroupCentral H x) :
    IsGroupCentral K (groupAlgebraEquiv e x) := by
  intro k
  rw [← e.apply_symm_apply k]
  rw [← groupAlgebraEquiv_single e (e.symm k) 1, ← map_mul,
    hx (e.symm k),
    map_mul, groupAlgebraEquiv_single]

private theorem augmentationHom_groupAlgebraEquiv {H : Type u} {K : Type v}
    [Group H] [Group K] (e : H ≃* K) (x : GroupAlgebraTwo H) :
    augmentationHom K (groupAlgebraEquiv e x) = augmentationHom H x := by
  have hhom :
      (augmentationHom K).toRingHom.comp
          (groupAlgebraEquiv e).toRingHom =
        (augmentationHom H).toRingHom := by
    apply MonoidAlgebra.ringHom_ext
    · intro r
      simp [augmentationHom]
    · intro h
      simp [augmentationHom]
  exact DFunLike.congr_fun hhom x

private theorem groupAlgebraEquiv_principalBlockCandidate
    {H : Type u} {K : Type v} [Group H] [Group K]
    [Fintype H] [Fintype K] (e : H ≃* K) :
    groupAlgebraEquiv e (principalBlockCandidate H) =
      principalBlockCandidate K := by
  let E := groupAlgebraEquiv e
  apply principalBlockCandidate_unique K
  · exact groupAlgebraEquiv_isGroupCentral e
      (principalBlockCandidate_central H)
  · rw [← map_mul, principalBlockCandidate_idempotent]
  · rw [augmentationHom_groupAlgebraEquiv,
      augmentationHom_apply, principalBlockCandidate_augmentation]
  · intro f hf
    let fH : GroupAlgebraTwo H := E.symm f
    have hfHcentral : IsGroupCentral H fH := by
      exact groupAlgebraEquiv_isGroupCentral e.symm hf.1
    have hfHidem : fH * fH = fH := by
      apply E.injective
      simpa [fH] using hf.2.1
    have hEf : groupAlgebraEquiv e fH = f := by
      change E fH = f
      exact E.apply_symm_apply f
    have hfHaug : augmentationHom H fH = 0 := by
      calc
        augmentationHom H fH =
            augmentationHom K (groupAlgebraEquiv e fH) :=
          (augmentationHom_groupAlgebraEquiv e fH).symm
        _ = augmentationHom K f := by rw [hEf]
        _ = 0 := hf.2.2
    have hzero := principalBlockCandidate_annihilates H fH
      ⟨hfHcentral, hfHidem, hfHaug⟩
    calc
      groupAlgebraEquiv e (principalBlockCandidate H) * f =
          groupAlgebraEquiv e (principalBlockCandidate H) *
            groupAlgebraEquiv e fH := by rw [hEf]
      _ = groupAlgebraEquiv e (principalBlockCandidate H * fH) := by
        rw [map_mul]
      _ = 0 := by rw [hzero, map_zero]

private theorem principalBlockCandidate_coeff_mulEquiv
    {H : Type u} {K : Type v} [Group H] [Group K]
    [Fintype H] [Fintype K] (e : H ≃* K) (h : H) :
    (principalBlockCandidate K).coeff (e h) =
      (principalBlockCandidate H).coeff h := by
  rw [← groupAlgebraEquiv_principalBlockCandidate e,
    groupAlgebraEquiv_coeff_apply]

universe w

variable {G : Type w} [Group G] [Fintype G]

noncomputable local instance subgroupFintype (H : Subgroup G) : Fintype H :=
  Fintype.ofFinite H

theorem principalBlockCandidate_coeff_normalizerConj
    (H : Subgroup G) (n : G)
    (hn : n ∈ Subgroup.normalizer (H : Set G)) (a : H) :
    (principalBlockCandidate H).coeff
        ((H.normalizerMonoidHom ⟨n, hn⟩) a) =
      (principalBlockCandidate H).coeff a := by
  exact principalBlockCandidate_coeff_mulEquiv
    (H.normalizerMonoidHom ⟨n, hn⟩) a

theorem principalBlockCandidate_sylowCentralizer_ambientConjInvariant
    (P : Sylow 2 G) (a b : Subgroup.centralizer (P : Set G))
    (hab : IsConj (a : G) (b : G)) :
    (principalBlockCandidate (Subgroup.centralizer (P : Set G))).coeff a =
      (principalBlockCandidate (Subgroup.centralizer (P : Set G))).coeff b := by
  let D : Subgroup G := Subgroup.centralizer (P : Set G)
  obtain ⟨g, hg⟩ := isConj_iff.mp hab
  let C : Subgroup G := Subgroup.centralizer ({(b : G)} : Set G)
  have hP : (P : Subgroup G) ≤ C := by
    intro p hp
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact b.property p hp
  have hgP : ((g • P : Sylow 2 G) : Subgroup G) ≤ C := by
    intro y hy
    let yP : (g • P : Sylow 2 G) := ⟨y, hy⟩
    obtain ⟨p, hp⟩ := (Sylow.equivSMul P g).surjective yP
    have hpy : g * (p : G) * g⁻¹ = y := by
      have hval := congrArg Subtype.val hp
      change g * (p : G) * g⁻¹ = y at hval
      exact hval
    rw [← hpy]
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hpa : (p : G) * (a : G) = (a : G) * (p : G) :=
      a.property (p : G) p.property
    calc
      (g * (p : G) * g⁻¹) * (b : G) =
          (g * (p : G) * g⁻¹) * (g * (a : G) * g⁻¹) := by rw [hg]
      _ = g * ((p : G) * (a : G)) * g⁻¹ := by group
      _ = g * ((a : G) * (p : G)) * g⁻¹ := by rw [hpa]
      _ = (b : G) * (g * (p : G) * g⁻¹) := by rw [← hg]; group
  let PC : Sylow 2 C := P.subtype hP
  let QC : Sylow 2 C := (g • P).subtype hgP
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C PC QC
  have hcP : ((c : G) • P : Sylow 2 G) = g • P := by
    apply Sylow.subtype_injective (N := C)
    change c • P.subtype hP = (g • P).subtype hgP at hc
    exact (Sylow.smul_subtype hP c).symm.trans hc
  let n : G := (c : G)⁻¹ * g
  have hnPact : n • P = P := by
    calc
      n • P = (c : G)⁻¹ • (g • P) := by
        simp only [n, mul_smul]
      _ = (c : G)⁻¹ • ((c : G) • P) := by rw [hcP]
      _ = P := by simp
  have hnP : n ∈ Subgroup.normalizer (P : Set G) :=
    Sylow.smul_eq_iff_mem_normalizer.mp hnPact
  have hcb : (c : G) * (b : G) = (b : G) * (c : G) := by
    exact Subgroup.mem_centralizer_singleton_iff.mp c.property
  have hnab : n * (a : G) * n⁻¹ = (b : G) := by
    calc
      n * (a : G) * n⁻¹ =
          (c : G)⁻¹ * (g * (a : G) * g⁻¹) * (c : G) := by
        dsimp only [n]
        group
      _ = (c : G)⁻¹ * (b : G) * (c : G) := by rw [hg]
      _ = (b : G) := by
        have hcbinv : (c : G)⁻¹ * (b : G) = (b : G) * (c : G)⁻¹ :=
          (Commute.inv_left (show Commute (c : G) (b : G) from hcb)).eq
        rw [hcbinv, mul_assoc, inv_mul_cancel, mul_one]
  have hnD : n ∈ Subgroup.normalizer (D : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hnPiff := Subgroup.mem_normalizer_iff.mp hnP
    constructor
    · intro hx
      rw [Subgroup.mem_centralizer_iff] at hx ⊢
      intro p hp
      have hp' : n⁻¹ * p * n ∈ (P : Subgroup G) := by
        apply (hnPiff (n⁻¹ * p * n)).mpr
        have heq : n * (n⁻¹ * p * n) * n⁻¹ = p := by group
        rw [heq]
        exact hp
      have hcomm := hx (n⁻¹ * p * n) hp'
      calc
        p * (n * x * n⁻¹) =
            n * ((n⁻¹ * p * n) * x) * n⁻¹ := by group
        _ = n * (x * (n⁻¹ * p * n)) * n⁻¹ := by rw [hcomm]
        _ = (n * x * n⁻¹) * p := by group
    · intro hx
      rw [Subgroup.mem_centralizer_iff] at hx ⊢
      intro p hp
      have hp' : n * p * n⁻¹ ∈ (P : Subgroup G) :=
        (hnPiff p).mp hp
      have hcomm := hx (n * p * n⁻¹) hp'
      calc
        p * x = n⁻¹ * ((n * p * n⁻¹) * (n * x * n⁻¹)) * n := by
          group
        _ = n⁻¹ * ((n * x * n⁻¹) * (n * p * n⁻¹)) * n := by
          rw [hcomm]
        _ = x * p := by group
  let phi : D ≃* D := D.normalizerMonoidHom ⟨n, hnD⟩
  have hphi : phi a = b := by
    apply Subtype.ext
    exact hnab
  have hcoeff := principalBlockCandidate_coeff_mulEquiv phi a
  rw [hphi] at hcoeff
  exact hcoeff.symm

end

end ZStar.BrauerSylowFusion

end CFSG
