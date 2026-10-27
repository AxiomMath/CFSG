module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1R925Quot

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem r925_starImg_mono {H X X' : Subgroup G} (h : X ≤ X') : starImg H X ≤ starImg H X' :=
  Subgroup.map_mono fun x hx => h hx

theorem r925_odd_index_starImg {H M : Subgroup G} (hM : Odd (M.relIndex H)) :
    Odd (starImg H M).index :=
  Odd.of_dvd_nat hM (Subgroup.index_map_dvd _ (QuotientGroup.mk'_surjective _))

theorem r925_pCoreOf_le_of_sylow {H S : Subgroup G} (hS : IsSylowIn 2 S H) :
    pCoreOf 2 H ≤ S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS' : IsPGroup 2 (S.subgroupOf H) := hS.2.1.comap_subtype
  have hQ : CFSG.pCore 2 ↥H ≤ S.subgroupOf H :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥H)).le_sylow_of_normal (hS'.toSylow hS.2.2)
  rw [pCoreOf]
  exact Subgroup.map_le_iff_le_comap.mpr hQ

theorem r925_le_of_starImg_eq_top {H M : Subgroup G} (hQ : pCoreOf 2 H ≤ M)
    (h : starImg H M = ⊤) : H ≤ M := by
  have hQ' : CFSG.pCore 2 ↥H ≤ M.subgroupOf H := Subgroup.map_le_iff_le_comap.mp hQ
  have h1 : M.subgroupOf H ⊔ CFSG.pCore 2 ↥H = ⊤ := by
    have h' := congrArg (Subgroup.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥H))) h
    rw [starImg] at h'
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] at h'
  have h2 : M.subgroupOf H = ⊤ := by
    rw [← h1, sup_eq_left.mpr hQ']
  exact Subgroup.subgroupOf_eq_top.mp h2

theorem r925_normalizer_starImg {H M : Subgroup G} (hQ : pCoreOf 2 H ≤ M)
    (hN : ∀ D : Subgroup G, D ≤ M → Nat.card D = 3 → normalizer (D : Set G) ≤ M)
    (D' : Subgroup (Bar2 H)) (hD'M : D' ≤ starImg H M) (hD' : Nat.card D' = 3) :
    normalizer (D' : Set (Bar2 H)) ≤ starImg H M := by
  have hQ' : CFSG.pCore 2 ↥H ≤ M.subgroupOf H := Subgroup.map_le_iff_le_comap.mp hQ
  have hJ : ∀ x ∈ CFSG.pCore 2 ↥H, ¬ 3 ∣ orderOf x :=
    r925_pCore_two_orderOf Nat.prime_three (by norm_num)
  obtain ⟨D₁, hD₁card, hD₁map⟩ :=
    r925_exists_lift_card_three (X := ↥H) (J := CFSG.pCore 2 ↥H) hJ hD'
  have hD₁M : D₁ ≤ M.subgroupOf H := by
    have h1 : D₁.map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) ≤
        (M.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) := by
      rw [hD₁map]; exact hD'M
    rw [Subgroup.map_le_iff_le_comap] at h1
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hQ'] at h1
  let D₁' : Subgroup G := D₁.map H.subtype
  have hD₁'M : D₁' ≤ M := by
    calc D₁' = (D₁.map H.subtype) := rfl
      _ ≤ (M.subgroupOf H).map H.subtype := Subgroup.map_mono hD₁M
      _ ≤ M := by rw [Subgroup.subgroupOf_map_subtype]; exact inf_le_left
  have hD₁'card : Nat.card D₁' = 3 := by
    rw [Subgroup.card_map_of_injective H.subtype_injective, hD₁card]
  have hD₁norm : normalizer (D₁ : Set ↥H) ≤ M.subgroupOf H := by
    intro h hh
    rw [Subgroup.mem_subgroupOf]
    exact hN D₁' hD₁'M hD₁'card
      (Subgroup.le_normalizer_map H.subtype (Subgroup.mem_map_of_mem H.subtype hh))
  have hmain := r925_normalizer_map_le (Γ := ↥H) (J := CFSG.pCore 2 ↥H) (D := D₁)
    (M := M.subgroupOf H) hJ hD₁card hD₁norm
  rwa [hD₁map] at hmain

theorem r925_commutator_perfectCore (X : Subgroup G) : commutator ↥(perfectCore X) = ⊤ := by
  apply Subgroup.map_injective (perfectCore X).subtype_injective
  rw [Subgroup.map_subtype_commutator, perfectCore_perfect, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

private lemma r925_isPGroup_of_elemAbelianOfRank_two {X : Type} [Group X]
    (h : IsElemAbelianOfRank 2 4 X) : IsPGroup 2 X := by
  obtain ⟨e⟩ := h
  refine IsPGroup.of_card (n := 4) ?_
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
    Fintype.card_fun, ZMod.card, Fintype.card_fin]

theorem r925_perfA5Cover_of_e16a5 {L Y : Subgroup G} (hYL : Y ≤ L) (hY : commutator ↥Y = ⊤)
    (hE : IsE16A5 ↥(starImg L Y)) : IsPerfA5Cover ↥Y := by
  classical
  obtain ⟨N, hNnormal, hNrank, hNalt⟩ := hE
  haveI : N.Normal := hNnormal
  let ι : ↥Y →* ↥L := Subgroup.inclusion hYL
  let φ : ↥Y →* ↥(starImg L Y) :=
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp ι).codRestrict (starImg L Y)
      (fun y => by
        have hy : ι y ∈ Y.subgroupOf L :=
          (Subgroup.mem_subgroupOf (H := Y) (K := L) (h := ι y)).mpr y.2
        exact Subgroup.mem_map_of_mem (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) hy)
  let Z : Subgroup ↥Y := N.comap φ
  have hφsurj : Function.Surjective φ := by
    intro w
    obtain ⟨a, ha, haw⟩ := Subgroup.mem_map.mp w.2
    refine ⟨⟨(a : G), Subgroup.mem_subgroupOf.mp ha⟩, ?_⟩
    apply Subtype.ext
    show (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
      (ι ⟨(a : G), Subgroup.mem_subgroupOf.mp ha⟩) = ↑w
    rw [show ι ⟨(a : G), Subgroup.mem_subgroupOf.mp ha⟩ = a from Subtype.ext rfl]
    exact haw
  have hker2 : IsPGroup 2 φ.ker := by
    let κ : ↥(φ.ker) →* ↥(CFSG.pCore 2 ↥L) :=
      { toFun := fun z => ⟨ι (z : ↥Y),
          (QuotientGroup.eq_one_iff _).mp
            (congrArg Subtype.val (MonoidHom.mem_ker.mp z.2))⟩
        map_one' := by ext; rfl
        map_mul' := by intro a b; ext; rfl }
    have hκ : Function.Injective κ := by
      intro a b hab
      exact Subtype.ext (Subgroup.inclusion_injective hYL (congrArg Subtype.val hab))
    exact (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).of_injective κ hκ
  have hNp : IsPGroup 2 ↥N := r925_isPGroup_of_elemAbelianOfRank_two hNrank
  have hZ2 : IsPGroup 2 Z := by
    intro z
    have hzN : φ (z : ↥Y) ∈ N := z.2
    obtain ⟨j, hj⟩ := hNp ⟨φ (z : ↥Y), hzN⟩
    have h1 : (φ (z : ↥Y)) ^ 2 ^ j = 1 := by
      simpa using congrArg Subtype.val hj
    have h2 : (z : ↥Y) ^ 2 ^ j ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_pow, h1]
    obtain ⟨k, hk⟩ := hker2 ⟨(z : ↥Y) ^ 2 ^ j, h2⟩
    have hk' : ((z : ↥Y) ^ 2 ^ j) ^ 2 ^ k = 1 := by
      simpa using congrArg Subtype.val hk
    refine ⟨j + k, ?_⟩
    apply Subtype.ext
    change (z : ↥Y) ^ 2 ^ (j + k) = 1
    have hpow : (z : ↥Y) ^ (2 ^ j * 2 ^ k) = 1 := by
      simpa [← pow_mul] using hk'
    rwa [← pow_add] at hpow
  have hπker : ((QuotientGroup.mk' N).comp φ).ker = Z := by
    ext y
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
    exact (QuotientGroup.eq_one_iff (φ y)).trans Subgroup.mem_comap.symm
  have hπsurj : Function.Surjective ((QuotientGroup.mk' N).comp φ) :=
    (QuotientGroup.mk'_surjective N).comp hφsurj
  have hAlt : UC22.IsAlt (↥Y ⧸ Z) 5 := by
    obtain ⟨e'⟩ := hNalt
    exact ⟨((QuotientGroup.quotientMulEquivOfEq hπker).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective ((QuotientGroup.mk' N).comp φ)
        hπsurj)).trans e'⟩
  exact ⟨hY, Z, inferInstance, hZ2, hAlt⟩

theorem r925_perfA5Cover_starImg {H Y : Subgroup G} (hYH : Y ≤ H) (h : IsPerfA5Cover ↥Y) :
    IsPerfA5Cover ↥(starImg H Y) :=
  r925_perfA5Cover_map_mk (J := CFSG.pCore 2 ↥H)
    (r925_pCore_two_orderOf Nat.prime_three (by norm_num))
    (h.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hYH).symm)

private lemma r925_map_conj_iSup_conjSubgroup {Γ : Type} [Group Γ] (S : Subgroup Γ) (g : Γ) :
    (⨆ k : Γ, conjSubgroup S k).map (MulAut.conj g).toMonoidHom = ⨆ k : Γ, conjSubgroup S k := by
  rw [Subgroup.map_iSup]
  apply le_antisymm
  · refine iSup_le fun k => ?_
    have hcomp : (MulAut.conj g).toMonoidHom.comp (MulAut.conj k⁻¹).toMonoidHom =
        (MulAut.conj (k * g⁻¹)⁻¹).toMonoidHom := by
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    have hk : (conjSubgroup S k).map (MulAut.conj g).toMonoidHom = conjSubgroup S (k * g⁻¹) := by
      show (S.map (MulAut.conj k⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom =
        S.map (MulAut.conj (k * g⁻¹)⁻¹).toMonoidHom
      rw [Subgroup.map_map, hcomp]
    rw [hk]
    exact le_iSup (fun k : Γ => conjSubgroup S k) (k * g⁻¹)
  · refine iSup_le fun k => ?_
    have hcomp : (MulAut.conj g).toMonoidHom.comp (MulAut.conj (k * g)⁻¹).toMonoidHom =
        (MulAut.conj k⁻¹).toMonoidHom := by
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    have hk : conjSubgroup S k = (conjSubgroup S (k * g)).map (MulAut.conj g).toMonoidHom := by
      show S.map (MulAut.conj k⁻¹).toMonoidHom =
        (S.map (MulAut.conj (k * g)⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom
      rw [Subgroup.map_map, hcomp]
    rw [hk]
    exact le_iSup (fun k : Γ => (conjSubgroup S k).map (MulAut.conj g).toMonoidHom) (k * g)

private lemma r925_normalClosure_eq_iSup_conjSubgroup {Γ : Type} [Group Γ] (S : Subgroup Γ) :
    Subgroup.normalClosure (S : Set Γ) = ⨆ g : Γ, conjSubgroup S g := by
  haveI : (⨆ g : Γ, conjSubgroup S g).Normal :=
    Subgroup.normal_iff_map_conj_eq.mpr (r925_map_conj_iSup_conjSubgroup S)
  refine le_antisymm (Subgroup.normalClosure_le_normal ?_) ?_
  · intro x hx
    exact le_iSup (fun g : Γ => conjSubgroup S g) 1 (by rwa [conjSubgroup_one])
  · refine iSup_le fun g => ?_
    rw [conjSubgroup]
    intro x hx
    obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp hx
    rw [← hxy]
    exact (inferInstance : (Subgroup.normalClosure (S : Set Γ)).Normal).conj_mem y
      (Subgroup.subset_normalClosure hy) g⁻¹

private lemma r925_hConj_le_self {H Y : Subgroup G} (hY : Y ≤ H) : hConj H Y ≤ H := by
  refine iSup_le fun h => ?_
  intro x hx
  rw [mem_conjSubgroup_iff] at hx
  have hmem : (h : G)⁻¹ * ((h : G) * x * (h : G)⁻¹) * (h : G) ∈ H :=
    H.mul_mem (H.mul_mem (H.inv_mem h.2) (hY hx)) h.2
  rwa [show (h : G)⁻¹ * ((h : G) * x * (h : G)⁻¹) * (h : G) = x by group] at hmem

private lemma r925_map_conjSubgroup_subgroupOf {H Y : Subgroup G} (hY : Y ≤ H) (g : ↥H) :
    (conjSubgroup (Y.subgroupOf H) g).map H.subtype = conjSubgroup Y (g : G) := by
  have hcomp : H.subtype.comp (MulAut.conj g⁻¹).toMonoidHom =
      (MulAut.conj (g : G)⁻¹).toMonoidHom.comp H.subtype := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [conjSubgroup, Subgroup.map_map, hcomp]
  conv_rhs => rw [conjSubgroup, ← Subgroup.map_subgroupOf_eq_of_le hY, Subgroup.map_map]

private lemma r925_hConj_subgroupOf {H Y : Subgroup G} (hY : Y ≤ H) :
    (hConj H Y).subgroupOf H = Subgroup.normalClosure (Y.subgroupOf H) := by
  rw [r925_normalClosure_eq_iSup_conjSubgroup]
  apply Subgroup.map_injective H.subtype_injective
  have hle : hConj H Y ≤ H := r925_hConj_le_self hY
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hle, Subgroup.map_iSup]
  unfold hConj
  apply le_antisymm
  · refine iSup_le fun h => ?_
    rw [← r925_map_conjSubgroup_subgroupOf hY h]
    exact le_iSup (fun h : ↥H => (conjSubgroup (Y.subgroupOf H) h).map H.subtype) h
  · refine iSup_le fun h => ?_
    rw [r925_map_conjSubgroup_subgroupOf hY h]
    exact le_iSup (fun h : ↥H => conjSubgroup Y (h : G)) h

theorem r925_starImg_hConj {H Y : Subgroup G} (hY : Y ≤ H) :
    starImg H (hConj H Y) = Subgroup.normalClosure (starImg H Y : Set (Bar2 H)) := by
  have h1 : starImg H (hConj H Y) =
      (Subgroup.normalClosure ((Y.subgroupOf H : Subgroup ↥H) : Set ↥H)).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) := by
    rw [starImg, r925_hConj_subgroupOf hY]
  rw [h1]
  exact Subgroup.map_normalClosure _ _ (QuotientGroup.mk'_surjective _)

theorem r925_kGroupNonab_starImg (H X : Subgroup G) {C : CFSG.KCore.Catalogue.{0}}
    (hC : CFSG.KCore.IsoInvariant C) (hX : CFSG.KCore.KGroupNonab C ↥X) :
    CFSG.KCore.KGroupNonab C ↥(starImg H X) := by
  have h1 : CFSG.KCore.KGroupNonab C ↥(X.subgroupOf H) := by
    refine CFSG.KCore.KGroupNonab.of_injective hC hX
      { toFun := fun x => ⟨(x : ↥H), (Subgroup.mem_subgroupOf.mp x.2)⟩
        map_one' := by ext; rfl
        map_mul' := by intro a b; ext; rfl } ?_
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : ↥X => (z : G)) hab
  exact CFSG.KCore.KGroupNonab.of_surjective hC h1
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥H)).subgroupMap (X.subgroupOf H))
    (MonoidHom.subgroupMap_surjective _ _)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
