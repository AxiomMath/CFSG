module

public import CFSG.Monster.B.TwoA.Amalgam.TypeFourDistStd
public import CFSG.Monster.B.TwoA.Amalgam.TypeFourDistPlanes
public import CFSG.Monster.B.TwoA.Amalgam.EightOrbitsBase

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.C2E6Std.FieldExtension
open CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.Geometry CFSG.Monster.B.E6.StdF4
open CFSG.Fischer CFSG.Monster CFSG.Monster.B CFSG.Monster.B.Short CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.B.TwoA.Unitary

theorem ncard_setOf_nbr
    {v : CVert} (iv : cgraph.neighborSet v ≃ rootClass) (P : Pts → Prop) :
    {y | ∃ hy : y ∈ cgraph.neighborSet v, P (iv ⟨y, hy⟩)}.ncard = {z : Pts | P z}.ncard := by
  have e : {y | ∃ hy : y ∈ cgraph.neighborSet v, P (iv ⟨y, hy⟩)} =
      Subtype.val '' (iv ⁻¹' {z : Pts | P z}) := by
    ext y
    constructor
    · rintro ⟨hy, h⟩
      exact ⟨⟨y, hy⟩, h, rfl⟩
    · rintro ⟨u, h, rfl⟩
      exact ⟨u.2, h⟩
  rw [e, Set.ncard_image_of_injective _ Subtype.val_injective,
    Set.ncard_preimage_of_injective_subset_range iv.injective
      (fun z _ => ⟨iv.symm z, iv.apply_symm_apply z⟩)]

theorem ncard_setOf_eq_card_filter
    (P : Pts → Prop) [DecidablePred P] :
    {z : Pts | P z}.ncard = (Finset.univ.filter P).card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext z
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]

section Base

variable {θ : Eam ⧸ Subgroup.zpowers cE' ≃* GStar} {f : Chamber ≃ C2E6Std.stdChamber}
  (hadj : ∀ (i : Fin Tag.F4.rank) (x y : Chamber), chamberCS.adj i x y ↔
    stdDistanceF4 (f x) (f y) = 1 ∨ stdDistanceF4 (f x) (f y) = (coxeterSystem .F4).simple i)
  (hfeq : ∀ (z : Chamber) (e : Eam), f (chamberMul z e⁻¹) = θ (QuotientGroup.mk e) • f z)
  (hfB : f baseChamber = c₀)
  (hx : θ (QuotientGroup.mk xhatEam) = rootStar)
  (hinj : ∀ e e' : Eam, vtx 0 (chamberOf e) = vtx 0 (chamberOf e') ↔
    (QuotientGroup.mk (e⁻¹ * xhatEam * e) : Eam ⧸ Subgroup.zpowers cE') =
      QuotientGroup.mk (e'⁻¹ * xhatEam * e'))
  (t : Shat) {k : Jhat} (hk0 : cvOf (jhatS k) ≠ cv0) (hk : ¬ cgraph.Adj cv0 (cvOf (jhatS k)))
  (hτ : psiW (labE k) = tauW)

theorem inl_ivB_nbr
    (e : Eam)
    (h : cvMul (nbr a0_mem_Ehat a0_not_mem_N1 (Quotient.mk _ e)) t ∈
      cgraph.neighborSet (cvMul cv0 t)) :
    SemidirectProduct.inl (ivB hx hinj t ⟨_, h⟩ : stdGroup) =
      θ (QuotientGroup.mk (xconj e)) := by
  rw [rootV_nbr θ hx hinj rfl e h, inl_rootPt_mk]
  rfl

theorem labelThree_iff_orderOf_ivB
    (x y : cgraph.neighborSet (cvMul cv0 t)) :
    LabelThree x y ↔ orderOf ((ivB hx hinj t x : stdGroup) * ivB hx hinj t y) = 3 := by
  have hc := orderOf_clabel_mul_of_root θ rfl (ivB hx hinj t) (inl_ivB_nbr hx hinj t) x y
  have he : orderOf ((SemidirectProduct.inl (ivB hx hinj t x : stdGroup) : GStar) *
      SemidirectProduct.inl (ivB hx hinj t y : stdGroup)) =
        orderOf ((ivB hx hinj t x : stdGroup) * ivB hx hinj t y) := by
    rw [← map_mul]
    exact orderOf_injective _ SemidirectProduct.inl_injective _
  have hmem : ∀ z : cgraph.neighborSet (cvMul cv0 t),
      (SemidirectProduct.inl (ivB hx hinj t z : stdGroup) : GStar) ∈ rootClassStar := fun z => by
    rw [mem_rootClassStar_iff]
    exact ⟨_, (ivB hx hinj t z).2, rfl⟩
  obtain ⟨i, -, ho⟩ := exists_orbSize_eq (hmem x) (hmem y)
  rw [he] at hc ho
  show (orderOf (clabel x * clabel y) = 3 ∨ orderOf (clabel x * clabel y) = 6) ↔ _
  rcases hc with h | h <;> rw [h, ho] <;> fin_cases i <;> decide

include hadj hfeq hfB in
theorem adj_iff_commute_ivB
    {x y : cgraph.neighborSet (cvMul cv0 t)} (hne : x ≠ y) :
    cgraph.Adj x y ↔ Commute (SemidirectProduct.inl (ivB hx hinj t x : stdGroup) : GStar)
      (SemidirectProduct.inl (ivB hx hinj t y : stdGroup)) := by
  rw [adj_iff_commute_rootV θ hx hinj (exists_vtx_three_iff_commute_of_quotient hadj hfeq hfB)
    rfl hne, commute_inl_iff]

theorem nbrRoot_mem_fibOrbit
    {d : Fin 5} {u : CVert} (hu : u ∈ rootSubB hx hinj t d) :
    nbrRoot (ivB hx hinj t) u ∈ fibOrbit d :=
  nbrRoot_mem_of_mem_nbrPull _ hu

include hadj hfeq hfB in
theorem ncard_nquot_preimage
    {d : Fin 5} (hd : IsMid d) {𝒯 : Set (Submodule F4 V6)}
    (h𝒯 : ∀ T ∈ 𝒯, UIso (quotDim d) T) :
    {z | z ∈ fibOrbit d ∧ nquot θ d z ∈ 𝒯}.ncard = fibUSize d * 𝒯.ncard := by
  have : Finite (Submodule F4 V6) := finite_submodule
  set ψ : fibOrbit d → {S : Submodule F4 V6 // UIso (quotDim d) S} :=
    fun y => ⟨nquot θ d y, uIso_nquot hadj hfeq hfB hd y.2⟩ with hψ
  have hfib : ∀ S, (ψ ⁻¹' {S}).ncard = fibUSize d := by
    intro S
    have e : ψ ⁻¹' {S} = {y : fibOrbit d | nquot θ d y = S} := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq, hψ]
      exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    rw [e]
    exact ncard_nquot_fibre hadj hfeq hfB hd S.2
  have h1 := ncard_preimage_of_fiber hfib {S | (S : Submodule F4 V6) ∈ 𝒯}
  have e1 : {z | z ∈ fibOrbit d ∧ nquot θ d z ∈ 𝒯} =
      Subtype.val '' (ψ ⁻¹' {S | (S : Submodule F4 V6) ∈ 𝒯}) := by
    ext z
    constructor
    · rintro ⟨hz, hz𝒯⟩
      exact ⟨⟨z, hz⟩, hz𝒯, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
  have e2 : 𝒯 = Subtype.val '' {S : {S : Submodule F4 V6 // UIso (quotDim d) S} |
      (S : Submodule F4 V6) ∈ 𝒯} := by
    ext T
    constructor
    · intro hT
      exact ⟨⟨T, h𝒯 T hT⟩, hT, rfl⟩
    · rintro ⟨S, hS, rfl⟩
      exact hS
  rw [e1, Set.ncard_image_of_injective _ Subtype.val_injective, h1]
  conv_rhs => rw [e2, Set.ncard_image_of_injective _ Subtype.val_injective]

theorem mem_omegaB_zero_iff
    {u : CVert} :
    u ∈ omegaB hx hinj t 0 ↔ u ∈ cgraph.neighborSet (cvMul cv0 t) ∧
      nbrRoot (ivB hx hinj t) u ∈ fibOrbit 1 ∧
      nquot θ 1 (nbrRoot (ivB hx hinj t) u) ∈ plOrbit 0 := by
  rw [(omegaB_eq_parts hx hinj t).1]
  constructor
  · rintro ⟨hu, hT⟩
    exact ⟨hu.fst, nbrRoot_mem_fibOrbit hx hinj t hu, hT⟩
  · rintro ⟨hu, h1, hT⟩
    exact ⟨(mem_nbrPull_iff_nbrRoot _ hu).2 h1, hT⟩

include hadj hfeq hfB in
theorem not_adj_omegaB_one_zero
    {x y : CVert} (hx1 : x ∈ omegaB hx hinj t 1)
    (hy0 : y ∈ omegaB hx hinj t 0) : ¬ cgraph.Adj x y := by
  rw [(omegaB_eq_parts hx hinj t).2.2.1] at hx1
  rw [(omegaB_eq_parts hx hinj t).1] at hy0
  obtain ⟨hxR, hxP⟩ := hx1
  obtain ⟨hyR, hyP⟩ := hy0
  intro hxy
  have hne : (⟨x, hxR.fst⟩ : cgraph.neighborSet (cvMul cv0 t)) ≠ ⟨y, hyR.fst⟩ := fun e =>
    hxy.ne (congrArg Subtype.val e)
  have hc := (adj_iff_commute_ivB hadj hfeq hfB hx hinj t hne).1 hxy
  rw [← nbrRoot_of_mem _ hxR.fst, ← nbrRoot_of_mem _ hyR.fst] at hc
  have hle := (commute_iff_nquot_le hadj hfeq hfB (nbrRoot_mem_fibOrbit hx hinj t hyR)
    (nbrRoot_mem_fibOrbit hx hinj t hxR)).1 hc.symm
  exact not_le_of_mem_ptOrbit_zero hyP hxP hle

include hadj hfeq hfB in
theorem ncard_neighborSet_inter_omegaB_zero
    {y : CVert} (hy : y ∈ omegaB hx hinj t 5) :
    (cgraph.neighborSet y ∩ omegaB hx hinj t 0).ncard = 24 := by
  rw [(omegaB_eq_parts hx hinj t).2.2.2.1] at hy
  obtain ⟨hyR, hyP⟩ := hy
  have hyv : y ∈ cgraph.neighborSet (cvMul cv0 t) := hyR.fst
  have hq := nbrRoot_mem_fibOrbit hx hinj t hyR
  have e : cgraph.neighborSet y ∩ omegaB hx hinj t 0 = nbrPull (ivB hx hinj t)
      {z | z ∈ fibOrbit 1 ∧ nquot θ 1 z ∈
        {T | T ∈ plOrbit 0 ∧ nquot θ 2 (nbrRoot (ivB hx hinj t) y) ≤ T}} := by
    ext x
    constructor
    · rintro ⟨hxy, hx0⟩
      obtain ⟨hxv, hx1, hxT⟩ := (mem_omegaB_zero_iff hx hinj t).1 hx0
      have hne : (⟨y, hyv⟩ : cgraph.neighborSet (cvMul cv0 t)) ≠ ⟨x, hxv⟩ := fun e =>
        (cgraph.adj_symm hxy).ne (congrArg Subtype.val e).symm
      have hc := (adj_iff_commute_ivB hadj hfeq hfB hx hinj t hne).1 hxy
      rw [← nbrRoot_of_mem _ hyv, ← nbrRoot_of_mem _ hxv] at hc
      have hle := (commute_iff_nquot_le hadj hfeq hfB hx1 hq).1 hc.symm
      exact (mem_nbrPull_iff_nbrRoot _ hxv).2 ⟨hx1, hxT, hle⟩
    · intro hxP
      have hxv : x ∈ cgraph.neighborSet (cvMul cv0 t) := hxP.fst
      obtain ⟨hx1, hxT, hle⟩ := nbrRoot_mem_of_mem_nbrPull _ hxP
      have hx0 : x ∈ omegaB hx hinj t 0 :=
        (mem_omegaB_zero_iff hx hinj t).2 ⟨hxv, hx1, hxT⟩
      refine ⟨?_, hx0⟩
      have hc := (commute_iff_nquot_le hadj hfeq hfB hx1 hq).2 hle
      have hne : (⟨y, hyv⟩ : cgraph.neighborSet (cvMul cv0 t)) ≠ ⟨x, hxv⟩ := by
        intro e
        have h0 : y ∈ omegaB hx hinj t 0 := by
          rw [show y = x from congrArg Subtype.val e]
          exact hx0
        have h5 : y ∈ omegaB hx hinj t 5 := by
          rw [(omegaB_eq_parts hx hinj t).2.2.2.1]
          exact ⟨hyR, hyP⟩
        obtain ⟨i, -, hi⟩ := existsUnique_mem_omegaB hadj hfeq hfB hx hinj t hyv
        exact absurd ((hi 0 h0).trans (hi 5 h5).symm) (by decide)
      refine (adj_iff_commute_ivB hadj hfeq hfB hx hinj t hne).2 ?_
      rw [← nbrRoot_of_mem _ hyv, ← nbrRoot_of_mem _ hxv]
      exact hc.symm
  have hsub : {z | z ∈ fibOrbit 1 ∧ nquot θ 1 z ∈
      {T | T ∈ plOrbit 0 ∧ nquot θ 2 (nbrRoot (ivB hx hinj t) y) ≤ T}} ⊆
        SemidirectProduct.inl '' rootClass := fun z hz => fibOrbit_subset_rootClass 1 hz.1
  have hT : ∀ T ∈ {T | T ∈ plOrbit 0 ∧ nquot θ 2 (nbrRoot (ivB hx hinj t) y) ≤ T},
      UIso (quotDim 1) T := by
    intro T hT
    obtain ⟨-, -, -, -, -, -, -, -, hplU, -⟩ := native_unitary_1408_stabilizer_point_plane_orbits
    have h : T ∈ {P | IsMaxIso P} := by
      rw [hplU]
      exact Or.inl hT.1
    exact h
  rw [e, ncard_nbrPull _ hsub, ncard_nquot_preimage hadj hfeq hfB (Or.inl rfl) hT,
    ncard_planes_through (R := nquot θ 2 (nbrRoot (ivB hx hinj t) y)) hyP]
  rfl

include hadj hfeq hfB hk0 hk hτ in
theorem ncard_labelThree_omegaB_zero
    {y : CVert} (hy : y ∈ omegaB hx hinj t 7) :
    {x | x ∈ omegaB hx hinj t 0 ∧ LabelThree x y}.ncard = 324 := by
  rw [← (rootSubB_eq_omegaB hadj hfeq hfB hx hinj t).2.2.2.2] at hy
  have hyv : y ∈ cgraph.neighborSet (cvMul cv0 t) := hy.fst
  have hy4 := nbrRoot_mem_fibOrbit hx hinj t hy
  rw [nbrRoot_of_mem _ hyv] at hy4
  have hA : midSet θ 1 0 ⊆ fibOrbit 1 := fun p hp => hp.1
  have hU : ∀ p ∈ midSet θ 1 0, conjOrbit radStar p ⊆ midSet θ 1 0 := by
    intro p hp z hz
    have hz1 : z ∈ fibOrbit 1 := conjOrbit_subset_fibOrbit radStar_le_parStar hp.1 hz
    refine ⟨hz1, ?_⟩
    rw [← (nquot_eq_iff hadj hfeq hfB (Or.inl rfl) hp.1 hz1).2 hz]
    exact hp.2
  have hcard : (midSet θ 1 0).ncard = 648 :=
    (ncard_midSet hadj hfeq hfB hk0 hk hτ (d := 1) (c := 0) (Or.inl rfl) (by norm_num)).trans rfl
  have h2 := ncard_orderOf_mul_eq_three hA hU (ivB hx hinj t ⟨y, hyv⟩).2 hy4
  have e : {x | x ∈ omegaB hx hinj t 0 ∧ LabelThree x y} = nbrPull (ivB hx hinj t)
      {p | p ∈ midSet θ 1 0 ∧ orderOf (p.left * (ivB hx hinj t ⟨y, hyv⟩ : stdGroup)) = 3} := by
    ext x
    constructor
    · rintro ⟨hx0, h3⟩
      have hx0' : x ∈ nbrPull (ivB hx hinj t) (eightSet θ 0) := hx0
      have hxv : x ∈ cgraph.neighborSet (cvMul cv0 t) := hx0'.fst
      refine ⟨hxv, ?_, ?_⟩
      · have h := nbrRoot_mem_of_mem_nbrPull _ hx0'
        rw [eightSet_eq_of_mid (i := 0) (by decide), nbrRoot_of_mem _ hxv] at h
        exact h
      · exact (labelThree_iff_orderOf_ivB hx hinj t ⟨x, hxv⟩ ⟨y, hyv⟩).1 h3
    · rintro ⟨hxv, hxA, h3⟩
      refine ⟨?_, (labelThree_iff_orderOf_ivB hx hinj t ⟨x, hxv⟩ ⟨y, hyv⟩).2 h3⟩
      show x ∈ nbrPull (ivB hx hinj t) (eightSet θ 0)
      rw [eightSet_eq_of_mid (i := 0) (by decide)]
      exact ⟨hxv, hxA⟩
  have hsub : {p | p ∈ midSet θ 1 0 ∧
      orderOf (p.left * (ivB hx hinj t ⟨y, hyv⟩ : stdGroup)) = 3} ⊆
        SemidirectProduct.inl '' rootClass := fun p hp => fibOrbit_subset_rootClass 1 hp.1.1
  rw [e, ncard_nbrPull _ hsub]
  omega

include hadj hfeq hfB hk0 hk hτ in
theorem exists_labelThree_omegaB_six
    {y : CVert} (hy : y ∈ omegaB hx hinj t 6) :
    ∃ x ∈ omegaB hx hinj t 0, LabelThree x y := by
  classical
  obtain ⟨x₀, hx₀⟩ := Set.nonempty_of_ncard_ne_zero (by
    rw [ncard_omegaB hadj hfeq hfB hx hinj t hk0 hk hτ 0]
    decide : (omegaB hx hinj t 0).ncard ≠ 0)
  have hx₀v : x₀ ∈ cgraph.neighborSet (cvMul cv0 t) := omegaB_subset hx hinj t 0 hx₀
  set p₀ : Pts := ivB hx hinj t ⟨x₀, hx₀v⟩
  have hp₀ : relIdx basePt p₀ = 1 := by
    have h := (mem_omegaB_zero_iff hx hinj t).1 hx₀
    rw [nbrRoot_of_mem _ hx₀v] at h
    exact Fin.ext ((mem_fibOrbit_iff p₀.2 1).1 h.2.1)
  have hL : ∀ z (hz : z ∈ cgraph.neighborSet (cvMul cv0 t)),
      (LabelThree x₀ z ↔ relIdx p₀ (ivB hx hinj t ⟨z, hz⟩) = 4) := fun z hz =>
    (labelThree_iff_orderOf_ivB hx hinj t ⟨x₀, hx₀v⟩ ⟨z, hz⟩).trans
      (orderOf_mul_eq_three_iff p₀ (ivB hx hinj t ⟨z, hz⟩))
  have hN : {z | ∃ hz : z ∈ cgraph.neighborSet (cvMul cv0 t),
      relIdx p₀ (ivB hx hinj t ⟨z, hz⟩) = 4}.ncard = 2097152 := by
    refine (ncard_setOf_nbr (ivB hx hinj t) (fun q => relIdx p₀ q = 4)).trans ?_
    rw [ncard_setOf_eq_card_filter, card_relIdx 4 p₀]
    rfl
  have h8 : {z | ∃ hz : z ∈ cgraph.neighborSet (cvMul cv0 t),
      relIdx basePt (ivB hx hinj t ⟨z, hz⟩) = 4 ∧
        relIdx (ivB hx hinj t ⟨z, hz⟩) p₀ = 4}.ncard = 1048576 := by
    refine (ncard_setOf_nbr (ivB hx hinj t)
      (fun q => relIdx basePt q = 4 ∧ relIdx q p₀ = 4)).trans ?_
    rw [ncard_setOf_eq_card_filter, card_filter_relIdx basePt p₀ 4 4, hp₀]
    decide +kernel
  have hR4 : ∀ z (hz : z ∈ cgraph.neighborSet (cvMul cv0 t)),
      (z ∈ omegaB hx hinj t 7 ↔ relIdx basePt (ivB hx hinj t ⟨z, hz⟩) = 4) := by
    intro z hz
    rw [← (rootSubB_eq_omegaB hadj hfeq hfB hx hinj t).2.2.2.2]
    show z ∈ nbrPull (ivB hx hinj t) (fibOrbit 4) ↔ _
    rw [mem_nbrPull_iff _ hz, mem_fibOrbit_iff (ivB hx hinj t ⟨z, hz⟩).2 4, Fin.ext_iff,
      val_relIdx]
    rfl
  by_contra hnone
  have hnone' : ∀ z ∈ omegaB hx hinj t 6, ¬ LabelThree x₀ z := by
    intro z hz h3
    obtain ⟨q, hq, rfl⟩ :
        y ∈ cvOrbit (vStab (cvMul cv0 t) ⊓ vStab (cvMul (cvOf (jhatS k)) t)) z := by
      rw [cvOrbit_omegaB hadj hfeq hfB hx hinj t hk0 hk hτ 6 hz]
      exact hy
    obtain ⟨hqv, hqw⟩ := Subgroup.mem_inf.1 hq
    refine hnone ⟨cvMul x₀ q, ?_, ?_⟩
    · rw [← cvOrbit_omegaB hadj hfeq hfB hx hinj t hk0 hk hτ 0 hx₀]
      exact ⟨q, hq, rfl⟩
    · exact (labelThree_cvMul x₀ z q).2 h3
  have hsplit : {z | ∃ hz : z ∈ cgraph.neighborSet (cvMul cv0 t),
      relIdx p₀ (ivB hx hinj t ⟨z, hz⟩) = 4} ⊆
      {z | ∃ hz : z ∈ cgraph.neighborSet (cvMul cv0 t),
        relIdx basePt (ivB hx hinj t ⟨z, hz⟩) = 4 ∧ relIdx (ivB hx hinj t ⟨z, hz⟩) p₀ = 4} ∪
      (omegaB hx hinj t 0 ∪ omegaB hx hinj t 1 ∪ omegaB hx hinj t 2 ∪ omegaB hx hinj t 3 ∪
        omegaB hx hinj t 4 ∪ omegaB hx hinj t 5) := by
    rintro z ⟨hz, h4⟩
    obtain ⟨i, hi, -⟩ := existsUnique_mem_omegaB hadj hfeq hfB hx hinj t hz
    have h6 : i ≠ 6 := by
      rintro rfl
      exact hnone' z hi ((hL z hz).2 h4)
    by_cases h7 : i = 7
    · subst h7
      exact Or.inl ⟨hz, (hR4 z hz).1 hi, by rw [relIdx_comm]; exact h4⟩
    · right
      fin_cases i
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hi))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hi))))
      · exact Or.inl (Or.inl (Or.inl (Or.inr hi)))
      · exact Or.inl (Or.inl (Or.inr hi))
      · exact Or.inl (Or.inr hi)
      · exact Or.inr hi
      · exact absurd rfl h6
      · exact absurd rfl h7
  have hle := Set.ncard_le_ncard hsplit (Set.toFinite _)
  have hu1 := Set.ncard_union_le
    {z | ∃ hz : z ∈ cgraph.neighborSet (cvMul cv0 t),
      relIdx basePt (ivB hx hinj t ⟨z, hz⟩) = 4 ∧ relIdx (ivB hx hinj t ⟨z, hz⟩) p₀ = 4}
    (omegaB hx hinj t 0 ∪ omegaB hx hinj t 1 ∪ omegaB hx hinj t 2 ∪ omegaB hx hinj t 3 ∪
      omegaB hx hinj t 4 ∪ omegaB hx hinj t 5)
  have hu2 := Set.ncard_union_le (omegaB hx hinj t 0 ∪ omegaB hx hinj t 1 ∪ omegaB hx hinj t 2 ∪
    omegaB hx hinj t 3 ∪ omegaB hx hinj t 4) (omegaB hx hinj t 5)
  have hu3 := Set.ncard_union_le (omegaB hx hinj t 0 ∪ omegaB hx hinj t 1 ∪ omegaB hx hinj t 2 ∪
    omegaB hx hinj t 3) (omegaB hx hinj t 4)
  have hu4 := Set.ncard_union_le (omegaB hx hinj t 0 ∪ omegaB hx hinj t 1 ∪ omegaB hx hinj t 2)
    (omegaB hx hinj t 3)
  have hu5 := Set.ncard_union_le (omegaB hx hinj t 0 ∪ omegaB hx hinj t 1) (omegaB hx hinj t 2)
  have hu6 := Set.ncard_union_le (omegaB hx hinj t 0) (omegaB hx hinj t 1)
  have hc := ncard_omegaB hadj hfeq hfB hx hinj t hk0 hk hτ
  have c0 : (omegaB hx hinj t 0).ncard = 648 := hc 0
  have c1 : (omegaB hx hinj t 1).ncard = 8064 := hc 1
  have c2 : (omegaB hx hinj t 2).ncard = 663552 := hc 2
  have c3 : (omegaB hx hinj t 3).ncard = 1 := hc 3
  have c4 : (omegaB hx hinj t 4).ncard = 1134 := hc 4
  have c5 : (omegaB hx hinj t 5).ncard = 36288 := hc 5
  omega

end Base

end CFSG.Monster.B.TwoA.Amalgam
