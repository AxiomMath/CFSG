module

public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeGroup

public section

namespace CFSG.RankThree.PartOne.KCUnitary

open scoped commutatorElement

variable {Γ U ι : Type*} [Group Γ] [Group U]

structure ProjSetting (ρ : U →* Γ) (B : Subgroup Γ) (t : Γ) (Hs M ZM : Subgroup U)
    (F : ι → Subgroup U) : Prop where
  ker_central : ∀ u ∈ ρ.ker, ∀ g : U, Commute u g
  D_normal : ρ.range.Normal
  H_normal : (Hs.map ρ).Normal
  H_le_B : Hs.map ρ ≤ B
  N_eq : ρ.range ⊓ Subgroup.centralizer ({t} : Set Γ) = M.map ρ
  F_le_M : ∀ i, F i ≤ M
  F_le_Hs : ∀ i, F i ≤ Hs
  F_normal : ∀ i, ∀ m ∈ M, ∀ g ∈ F i, m * g * m⁻¹ ∈ F i
  F_quasi : ∀ i, CFSG.IsQuasisimple (F i)
  M_derived : ⁅M, M⁆ = ⨆ i, F i
  ZM_le_M : ZM ≤ M
  ZM_central : ∀ y ∈ ZM, ∀ m ∈ M, y * m = m * y
  ker_le_ZM : ρ.ker ≤ ZM
  centralizes : ∀ Y ∈ M, (∀ i, ∀ g ∈ F i, ⁅Y, g⁆ = 1) → Y ∈ ZM

variable {ρ : U →* Γ} {B : Subgroup Γ} {t : Γ} {Hs M ZM : Subgroup U} {F : ι → Subgroup U}
  (S : ProjSetting ρ B t Hs M ZM F)

theorem exists_quotient_equiv (ρ : U →* Γ) (ZM : Subgroup U) :
    ∃ e : (ZM ⧸ ρ.ker.subgroupOf ZM) ≃* ↥(ZM.map ρ),
      ∀ z : ZM, ((e (QuotientGroup.mk z) : ↥(ZM.map ρ)) : Γ) = ρ z := by
  let φ : ZM →* ↥(ZM.map ρ) :=
    (ρ.comp ZM.subtype).codRestrict (ZM.map ρ) (fun z => ⟨z, z.2, rfl⟩)
  have hφ : Function.Surjective φ := by
    rintro ⟨_, z, hz, rfl⟩
    exact ⟨⟨z, hz⟩, rfl⟩
  have hker : ρ.ker.subgroupOf ZM = φ.ker := by
    ext z
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, MonoidHom.mem_ker]
    constructor
    · intro h
      exact Subtype.ext h
    · intro h
      exact congrArg Subtype.val h
  refine ⟨(QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ), fun z => ?_⟩
  rfl

namespace ProjSetting

include S in
theorem map_le_centralizer (i : ι) :
    (F i).map ρ ≤ Subgroup.centralizer ({t} : Set Γ) := by
  intro y hy
  have : y ∈ ρ.range ⊓ Subgroup.centralizer ({t} : Set Γ) :=
    S.N_eq ▸ Subgroup.map_mono (S.F_le_M i) hy
  exact this.2

include S in
theorem map_le_B (i : ι) : (F i).map ρ ≤ B :=
  (Subgroup.map_mono (S.F_le_Hs i)).trans S.H_le_B

include S in
theorem map_le_centralizerB (i : ι) :
    (F i).map ρ ≤ B ⊓ Subgroup.centralizer ({t} : Set Γ) :=
  le_inf (S.map_le_B i) (S.map_le_centralizer i)

include S in
theorem image_conj_mem (i : ι) {y : Γ} (hy : y ∈ ρ.range ⊓ Subgroup.centralizer ({t} : Set Γ))
    {j : Γ} (hj : j ∈ (F i).map ρ) : y * j * y⁻¹ ∈ (F i).map ρ := by
  rw [S.N_eq] at hy
  obtain ⟨m, hm, rfl⟩ := hy
  obtain ⟨g, hg, rfl⟩ := hj
  exact ⟨m * g * m⁻¹, S.F_normal i m hm g hg, by simp⟩

include S in
theorem isQuasisimple_image (i : ι) : CFSG.IsQuasisimple ((F i).map ρ) := by
  have hQ := S.F_quasi i
  let f : F i →* Γ := ρ.comp (F i).subtype
  have hker : f.ker ≤ Subgroup.center (F i) := by
    intro g hg
    rw [Subgroup.mem_center_iff]
    intro g'
    apply Subtype.ext
    exact (S.ker_central (g : U) hg (g' : U)).eq.symm
  have := isQuasisimple_range hQ f hker
  have hrange : f.range = (F i).map ρ := by
    ext y
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g, g.2, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, rfl⟩
  rw [hrange] at this
  exact this

include S in
theorem isComponent_image (i : ι) :
    CFSG.IsComponent (((F i).map ρ).subgroupOf (B ⊓ Subgroup.centralizer ({t} : Set Γ))) := by
  set CB := B ⊓ Subgroup.centralizer ({t} : Set Γ) with hCB
  set J := (F i).map ρ with hJ
  have hJCB : J ≤ CB := S.map_le_centralizerB i
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJCB).symm
    (S.isQuasisimple_image i), ?_⟩
  set CH := (Hs.map ρ) ⊓ Subgroup.centralizer ({t} : Set Γ) with hCH
  have hJCH : J ≤ CH := le_inf (Subgroup.map_mono (S.F_le_Hs i)) (S.map_le_centralizer i)
  have hCHN : CH ≤ ρ.range ⊓ Subgroup.centralizer ({t} : Set Γ) := by
    refine le_inf ?_ inf_le_right
    exact (inf_le_left : CH ≤ Hs.map ρ).trans (Subgroup.map_le_range ρ Hs)
  have hJnorm : (J.subgroupOf CH).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hnJ : ((n : CH) : Γ) ∈ J := hn
    have hg' : ((g : CH) : Γ) ∈ ρ.range ⊓ Subgroup.centralizer ({t} : Set Γ) := hCHN g.2
    exact S.image_conj_mem i hg' hnJ
  have hCHnorm : (CH.subgroupOf CB).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn' : ((n : CB) : Γ) ∈ CH := hn
    have hnH : ((n : CB) : Γ) ∈ Hs.map ρ := hn'.1
    have hnt : ((n : CB) : Γ) ∈ Subgroup.centralizer ({t} : Set Γ) := hn'.2
    have hgt : ((g : CB) : Γ) ∈ Subgroup.centralizer ({t} : Set Γ) := g.2.2
    have hmem : ((g : CB) : Γ) * ((n : CB) : Γ) * ((g : CB) : Γ)⁻¹ ∈
        Subgroup.centralizer ({t} : Set Γ) := mul_mem (mul_mem hgt hnt) (inv_mem hgt)
    show ((g : CB) : Γ) * ((n : CB) : Γ) * ((g : CB) : Γ)⁻¹ ∈ CH
    exact ⟨S.H_normal.conj_mem _ hnH _, hmem⟩
  exact isSubnormal_subgroupOf_of_normal_chain hJCH hJnorm hCHnorm

include S in
theorem commutator_image_eq : ⁅M.map ρ, M.map ρ⁆ = ⨆ i, (F i).map ρ := by
  rw [← Subgroup.map_commutator, S.M_derived, Subgroup.map_iSup]

include S in
theorem core_le_centralizer_derived [Finite Γ] {p : ℕ} (hp : p.Prime) :
    CFSG.inSubgroup (CFSG.RankThree.LocalRank.aschbacherSolvableCore p)
        (B ⊓ Subgroup.centralizer ({t} : Set Γ)) ≤
      Subgroup.centralizer ((⁅M.map ρ, M.map ρ⁆ : Subgroup Γ) : Set Γ) := by
  intro s hs
  rw [Subgroup.mem_centralizer_iff]
  intro j hj
  rw [S.commutator_image_eq] at hj
  refine Subgroup.iSup_induction (fun i => (F i).map ρ) (C := fun j => j * s = s * j) hj ?_ ?_ ?_
  · intro i j hj
    exact (commute_of_isComponent_core hp (S.map_le_centralizerB i) (S.isComponent_image i) hj
      hs).eq
  · simp
  · intro a b ha hb
    rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]

include S in
theorem conj_mem_N {g : Γ} (hg : g ∈ Subgroup.centralizer ({t} : Set Γ)) {n : Γ}
    (hn : n ∈ M.map ρ) : g * n * g⁻¹ ∈ M.map ρ := by
  rw [← S.N_eq] at hn ⊢
  have h1 : g * n * g⁻¹ ∈ ρ.range := S.D_normal.conj_mem _ (Subgroup.mem_inf.mp hn).1 _
  have h2 : g * n * g⁻¹ ∈ Subgroup.centralizer ({t} : Set Γ) :=
    mul_mem (mul_mem hg (Subgroup.mem_inf.mp hn).2) (inv_mem hg)
  exact Subgroup.mem_inf.mpr ⟨h1, h2⟩

include S in
theorem inf_centralizer_derived_eq :
    M.map ρ ⊓ Subgroup.centralizer ((⁅M.map ρ, M.map ρ⁆ : Subgroup Γ) : Set Γ) = ZM.map ρ := by
  apply le_antisymm
  · intro y hy
    have hyN := (Subgroup.mem_inf.mp hy).1
    have hyC := (Subgroup.mem_inf.mp hy).2
    obtain ⟨Y, hY, rfl⟩ := hyN
    refine ⟨Y, S.centralizes Y hY fun i => ?_, rfl⟩
    have hker : ∀ g ∈ F i, ⁅Y, g⁆ ∈ ρ.ker := by
      intro g hg
      have hgN' : ρ g ∈ (⁅M.map ρ, M.map ρ⁆ : Subgroup Γ) := by
        rw [S.commutator_image_eq]
        exact Subgroup.mem_iSup_of_mem i ⟨g, hg, rfl⟩
      have hcomm : ρ g * ρ Y = ρ Y * ρ g := Subgroup.mem_centralizer_iff.mp hyC _ hgN'
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_commute]
      exact hcomm.symm
    exact commutator_eq_one_of_central (F := F i) (Z := ρ.ker) Y (S.F_quasi i).1
      S.ker_central hker
  · rintro _ ⟨Z, hZ, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨⟨Z, S.ZM_le_M hZ, rfl⟩, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr fun j hj => ?_
    obtain ⟨m, hm, rfl⟩ : j ∈ M.map ρ := (commutator_self_le (M.map ρ)) hj
    rw [← map_mul, ← map_mul, S.ZM_central Z hZ m hm]

include S in
theorem center_image_eq :
    (Subgroup.center ↥(M.map ρ)).map (M.map ρ).subtype = ZM.map ρ := by
  apply le_antisymm
  · rw [← S.inf_centralizer_derived_eq]
    rintro _ ⟨n, hn, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨n.2, Subgroup.mem_centralizer_iff.mpr fun j hj => ?_⟩
    have hjN : j ∈ M.map ρ := commutator_self_le _ hj
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hn ⟨j, hjN⟩)
  · rintro _ ⟨Z, hZ, rfl⟩
    refine ⟨⟨ρ Z, ⟨Z, S.ZM_le_M hZ, rfl⟩⟩, ?_, rfl⟩
    refine Subgroup.mem_center_iff.mpr ?_
    rintro ⟨_, m, hm, rfl⟩
    apply Subtype.ext
    change ρ m * ρ Z = ρ Z * ρ m
    rw [← map_mul, ← map_mul, S.ZM_central Z hZ m hm]

include S in
theorem inf_centralizer_derived_eq_center :
    M.map ρ ⊓ Subgroup.centralizer ((⁅M.map ρ, M.map ρ⁆ : Subgroup Γ) : Set Γ) =
      (Subgroup.center ↥(M.map ρ)).map (M.map ρ).subtype := by
  rw [S.center_image_eq, S.inf_centralizer_derived_eq]

omit S in
theorem center_inf_comm {a b : Γ}
    (ha : a ∈ (Subgroup.center ↥(M.map ρ)).map (M.map ρ).subtype)
    (hb : b ∈ (Subgroup.center ↥(M.map ρ)).map (M.map ρ).subtype) : a * b = b * a := by
  obtain ⟨a', ha', rfl⟩ := ha
  obtain ⟨b', hb', rfl⟩ := hb
  exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp ha' b')).symm

include S in
theorem conj_mem_center_N {g : Γ} (hg : g ∈ Subgroup.centralizer ({t} : Set Γ)) {y : Γ}
    (hy : y ∈ (Subgroup.center ↥(M.map ρ)).map (M.map ρ).subtype) :
    g * y * g⁻¹ ∈ (Subgroup.center ↥(M.map ρ)).map (M.map ρ).subtype := by
  obtain ⟨n, hn, rfl⟩ := hy
  have hgn : g * (n : Γ) * g⁻¹ ∈ M.map ρ := S.conj_mem_N hg n.2
  refine ⟨⟨g * (n : Γ) * g⁻¹, hgn⟩, ?_, rfl⟩
  refine Subgroup.mem_center_iff.mpr ?_
  intro k
  have hk : g⁻¹ * (k : Γ) * g ∈ M.map ρ := by
    have := S.conj_mem_N (inv_mem hg) k.2
    simpa using this
  have hc := Subgroup.mem_center_iff.mp hn ⟨g⁻¹ * (k : Γ) * g, hk⟩
  apply Subtype.ext
  have hc' : (g⁻¹ * (k : Γ) * g) * (n : Γ) = (n : Γ) * (g⁻¹ * (k : Γ) * g) :=
    congrArg Subtype.val hc
  change (k : Γ) * (g * (n : Γ) * g⁻¹) = (g * (n : Γ) * g⁻¹) * (k : Γ)
  calc (k : Γ) * (g * (n : Γ) * g⁻¹) = g * ((g⁻¹ * (k : Γ) * g) * (n : Γ)) * g⁻¹ := by group
    _ = g * ((n : Γ) * (g⁻¹ * (k : Γ) * g)) * g⁻¹ := by rw [hc']
    _ = (g * (n : Γ) * g⁻¹) * (k : Γ) := by group

include S in
theorem center_inf_normal :
    ((((Subgroup.center ↥(M.map ρ)).map (M.map ρ).subtype) ⊓
      (B ⊓ Subgroup.centralizer ({t} : Set Γ))).subgroupOf
        (B ⊓ Subgroup.centralizer ({t} : Set Γ))).Normal := by
  set CB := B ⊓ Subgroup.centralizer ({t} : Set Γ) with hCB
  refine ⟨fun n hn g => ?_⟩
  have hn' := Subgroup.mem_inf.mp hn
  have hg : ((g : CB) : Γ) ∈ Subgroup.centralizer ({t} : Set Γ) := g.2.2
  show ((g : CB) : Γ) * ((n : CB) : Γ) * ((g : CB) : Γ)⁻¹ ∈
    ((Subgroup.center ↥(M.map ρ)).map (M.map ρ).subtype) ⊓ CB
  exact Subgroup.mem_inf.mpr ⟨S.conj_mem_center_N hg hn'.1,
    mul_mem (mul_mem g.2 n.2) (inv_mem g.2)⟩

end ProjSetting

end CFSG.RankThree.PartOne.KCUnitary
