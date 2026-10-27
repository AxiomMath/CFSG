module

public import CFSG.LocalAnalysis.StandardType.FF81.CentAFrame
import CFSG.LocalAnalysis.StandardType.FF81.CentAModelRootAut
import CFSG.LocalAnalysis.StandardType.FF81.RootFusionLinO2

public section

namespace CFSG.StandardType.FF81.CentA

open RootFusionLin

variable {G : Type} [Group G] [Finite G] {k : ℕ} {Y L R : Subgroup G} {b t : G}
  {φ : ↥Y ≃* GL (BlkIdx 1 (k + 2)) (ZMod 2)}

private noncomputable def caFAut_pre {k : ℕ} {Y : Subgroup G}
    (φ : ↥Y ≃* GL (BlkIdx 1 (k + 2)) (ZMod 2)) (g : ↥(lStar φ)) :
    GL (BlkIdx 1 k) (ZMod 2) :=
  (MonoidHom.ofInjective (f := embGL k) (embGL_injective k)).symm
    ⟨φ ⟨g.1, liftSub_le (φ := φ) (K := (embGL k).range) g.2⟩, by
      rcases (mem_liftSub (φ := φ) (K := (embGL k).range)).mp g.2 with ⟨hy, hmem⟩
      rcases (MonoidHom.mem_range).mp hmem with ⟨x, hx⟩
      exact (MonoidHom.mem_range).mpr ⟨x, by rw [hx]⟩⟩

private theorem caFAut_pre_spec {k : ℕ} {Y : Subgroup G}
    {φ : ↥Y ≃* GL (BlkIdx 1 (k + 2)) (ZMod 2)} (g : ↥(lStar φ)) :
    embGL k (caFAut_pre φ g) =
      φ ⟨g.1, liftSub_le (φ := φ) (K := (embGL k).range) g.2⟩ := by
  rw [caFAut_pre]
  exact MonoidHom.apply_ofInjective_symm (embGL_injective k) _

private noncomputable def caFAut_inv {k : ℕ} {Y : Subgroup G}
    (φ : ↥Y ≃* GL (BlkIdx 1 (k + 2)) (ZMod 2)) (x : GL (BlkIdx 1 k) (ZMod 2)) :
    ↥(lStar φ) :=
  ⟨((φ.symm (embGL k x) : ↥Y) : G), by
    exact Subgroup.mem_map.mpr ⟨φ.symm (embGL k x),
      Subgroup.mem_map.mpr ⟨embGL k x, MonoidHom.mem_range.mpr ⟨x, rfl⟩, rfl⟩, rfl⟩⟩

private theorem caFAut_pre_inv {k : ℕ} {Y : Subgroup G}
    {φ : ↥Y ≃* GL (BlkIdx 1 (k + 2)) (ZMod 2)} (x : GL (BlkIdx 1 k) (ZMod 2)) :
    caFAut_pre φ (caFAut_inv φ x) = x := by
  apply embGL_injective k
  rw [caFAut_pre_spec]
  exact MulEquiv.apply_symm_apply φ (embGL k x)

private noncomputable def caFAut_psiFun {k : ℕ} {Y : Subgroup G}
    (φ : ↥Y ≃* GL (BlkIdx 1 (k + 2)) (ZMod 2)) :
    ↥(lStar φ) →* GL (BlkIdx 1 k) (ZMod 2) where
  toFun := caFAut_pre φ
  map_one' := by
    apply embGL_injective k
    rw [caFAut_pre_spec]
    simp
  map_mul' g h := by
    apply embGL_injective k
    rw [caFAut_pre_spec]
    rw [map_mul, caFAut_pre_spec, caFAut_pre_spec, ← map_mul]
    congr 1

private noncomputable def caFAut_psi {k : ℕ} {Y : Subgroup G}
    (φ : ↥Y ≃* GL (BlkIdx 1 (k + 2)) (ZMod 2)) :
    ↥(lStar φ) ≃* GL (BlkIdx 1 k) (ZMod 2) :=
  MulEquiv.ofBijective (caFAut_psiFun φ) (by
    constructor
    · intro g h hgh
      apply Subtype.ext
      have h' := congrArg (embGL k) hgh
      change embGL k (caFAut_pre φ g) = embGL k (caFAut_pre φ h) at h'
      rw [caFAut_pre_spec, caFAut_pre_spec] at h'
      exact congrArg (fun y : ↥Y => (y : G)) (φ.injective h')
    · intro x
      exact ⟨caFAut_inv φ x, caFAut_pre_inv (φ := φ) x⟩)

private theorem caFAut_psi_apply {k : ℕ} {Y : Subgroup G}
    {φ : ↥Y ≃* GL (BlkIdx 1 (k + 2)) (ZMod 2)} (g : ↥(lStar φ)) :
    embGL k (caFAut_psi φ g) =
      φ ⟨g.1, liftSub_le (φ := φ) (K := (embGL k).range) g.2⟩ := by
  change embGL k (caFAut_pre φ g) =
    φ ⟨g.1, liftSub_le (φ := φ) (K := (embGL k).range) g.2⟩
  exact caFAut_pre_spec g

private theorem caFAut_embGL_mem_cent_iff {k : ℕ} (x : GL (BlkIdx 1 k) (ZMod 2)) :
    x ∈ Cent 1 k ↔ embGL k x ∈ Cent 1 (k + 2) := by
  rw [Cent, Cent, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff, ← embGL_jGL k]
  constructor
  · intro h
    rw [← map_mul, ← map_mul, h]
  · intro h
    apply embGL_injective k
    rw [map_mul, map_mul]
    exact h

private theorem caFAut_psi_t (hS : CentASetting (k + 2) Y L R b t φ) :
    caFAut_psi φ ⟨t, t_mem_lStar hS⟩ = jGL 1 k := by
  apply embGL_injective k
  rw [caFAut_psi_apply, embGL_jGL]
  have h : (⟨t, liftSub_le (φ := φ) (K := (embGL k).range) (t_mem_lStar hS)⟩ : ↥Y) =
      ⟨t, hS.t_mem⟩ := Subtype.ext rfl
  rw [h, hS.φ_t]

private theorem caFAut_mem_uStar_iff {k : ℕ} {Y : Subgroup G}
    {φ : ↥Y ≃* GL (BlkIdx 1 (k + 2)) (ZMod 2)} (g : ↥(lStar φ)) :
    g.1 ∈ uStar φ ↔ caFAut_psi φ g ∈ uSub 1 k := by
  rw [uStar, mem_liftSub]
  constructor
  · rintro ⟨hy, hmem⟩
    rcases (Subgroup.mem_map).mp hmem with ⟨x, hx, hxeq⟩
    have hxpsi : caFAut_psi φ g = x := by
      apply embGL_injective k
      rw [caFAut_psi_apply]
      have h : (⟨g.1, liftSub_le (φ := φ) (K := (embGL k).range) g.2⟩ : ↥Y) =
          ⟨g.1, hy⟩ := Subtype.ext rfl
      rw [h, ← hxeq]
    rwa [hxpsi]
  · intro hmem
    refine ⟨liftSub_le (φ := φ) (K := (embGL k).range) g.2, ?_⟩
    rw [← caFAut_psi_apply, Subgroup.mem_map_iff_mem (embGL_injective k)]
    exact hmem

private theorem caFAut_mem_cent_iff (hS : CentASetting (k + 2) Y L R b t φ)
    (g : ↥(lStar φ)) :
    g.1 * t = t * g.1 ↔ caFAut_psi φ g ∈ Cent 1 k := by
  rw [caFAut_embGL_mem_cent_iff, caFAut_psi_apply]
  constructor
  · intro h
    have hmem : g.1 ∈ liftSub φ (Cent 1 (k + 2)) := by
      rw [mem_liftSub_cent hS]
      exact ⟨liftSub_le (φ := φ) (K := (embGL k).range) g.2, h⟩
    rcases (mem_liftSub (φ := φ) (K := Cent 1 (k + 2))).mp hmem with ⟨hy, hcent⟩
    have hy' : (⟨g.1, liftSub_le (φ := φ) (K := (embGL k).range) g.2⟩ : ↥Y) =
        ⟨g.1, hy⟩ := Subtype.ext rfl
    rwa [hy']
  · intro h
    have hmem : g.1 ∈ liftSub φ (Cent 1 (k + 2)) :=
      (mem_liftSub (φ := φ) (K := Cent 1 (k + 2))).mpr
        ⟨liftSub_le (φ := φ) (K := (embGL k).range) g.2, h⟩
    rw [mem_liftSub_cent hS] at hmem
    exact hmem.2

private noncomputable def caFAut_conjOn {k : ℕ} {Y : Subgroup G}
    {φ : ↥Y ≃* GL (BlkIdx 1 (k + 2)) (ZMod 2)} (x : G)
    (hx : x ∈ Subgroup.normalizer (lStar φ : Set G)) : MulAut ↥(lStar φ) where
  toFun g := ⟨x * g.1 * x⁻¹, (Subgroup.mem_normalizer_iff.mp hx g.1).mp g.2⟩
  invFun g :=
    ⟨x⁻¹ * g.1 * (x⁻¹)⁻¹,
      (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (lStar φ : Set G)).inv_mem hx) g.1).mp g.2⟩
  left_inv g := Subtype.ext (by group)
  right_inv g := Subtype.ext (by group)
  map_mul' g h := Subtype.ext (by
    simp only [Subgroup.coe_mul]
    group)

private theorem caFAut_conjOn_coe {k : ℕ} {Y : Subgroup G}
    {φ : ↥Y ≃* GL (BlkIdx 1 (k + 2)) (ZMod 2)} (x : G)
    (hx : x ∈ Subgroup.normalizer (lStar φ : Set G)) (g : ↥(lStar φ)) :
    (caFAut_conjOn x hx g).1 = x * g.1 * x⁻¹ := rfl

private noncomputable def caFAut_alpha {k : ℕ} {Y : Subgroup G}
    {φ : ↥Y ≃* GL (BlkIdx 1 (k + 2)) (ZMod 2)} (x : G)
    (hx : x ∈ Subgroup.normalizer (lStar φ : Set G)) :
    MulAut (GL (BlkIdx 1 k) (ZMod 2)) :=
  ((caFAut_psi φ).symm.trans (caFAut_conjOn x hx)).trans (caFAut_psi φ)

private theorem caFAut_alpha_psi {k : ℕ} {Y : Subgroup G}
    {φ : ↥Y ≃* GL (BlkIdx 1 (k + 2)) (ZMod 2)} (x : G)
    (hx : x ∈ Subgroup.normalizer (lStar φ : Set G)) (g : ↥(lStar φ)) :
    caFAut_alpha x hx (caFAut_psi φ g) = caFAut_psi φ (caFAut_conjOn x hx g) := by
  rw [caFAut_alpha, MulEquiv.trans_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply]

theorem exists_mem_lStar_eq_conj (hS : CentASetting (k + 2) Y L R b t φ) {x : G}
    (hxL : x ∈ Subgroup.normalizer (lStar φ : Set G)) (hxt : x * t = t * x)
    (hc : ∀ g ∈ lStar φ, g * t = t * g → x * g * x⁻¹ * g⁻¹ ∈ uStar φ) :
    ∃ a ∈ lStar φ, ∀ g ∈ lStar φ, x * g * x⁻¹ = a * g * a⁻¹ := by
  have hk : 3 ≤ k := by
    rcases hS.m_cases with h | h <;> omega
  let α : MulAut (GL (BlkIdx 1 k) (ZMod 2)) := caFAut_alpha x hxL
  have hJ : α (jGL 1 k) = jGL 1 k := by
    rw [show jGL 1 k = caFAut_psi φ ⟨t, t_mem_lStar hS⟩ from (caFAut_psi_t hS).symm]
    rw [caFAut_alpha_psi]
    congr 1
    apply Subtype.ext
    rw [caFAut_conjOn_coe, hxt]
    group
  have hU : ∀ g' ∈ Cent 1 k, α g' * g'⁻¹ ∈ uSub 1 k := by
    intro g' hg'
    let g : ↥(lStar φ) := (caFAut_psi φ).symm g'
    have hg'eq : caFAut_psi φ g = g' := (caFAut_psi φ).apply_symm_apply g'
    have hg'cent : caFAut_psi φ g ∈ Cent 1 k := by rwa [hg'eq]
    have hcent : g.1 * t = t * g.1 := (caFAut_mem_cent_iff hS g).mpr hg'cent
    have hmem : (caFAut_conjOn x hxL g * g⁻¹).1 ∈ uStar φ := by
      change x * g.1 * x⁻¹ * g.1⁻¹ ∈ uStar φ
      exact hc g.1 g.2 hcent
    have hu : caFAut_psi φ (caFAut_conjOn x hxL g * g⁻¹) ∈ uSub 1 k :=
      (caFAut_mem_uStar_iff (caFAut_conjOn x hxL g * g⁻¹)).mp hmem
    have hα : α g' = caFAut_psi φ (caFAut_conjOn x hxL g) := by
      rw [← hg'eq]
      exact caFAut_alpha_psi x hxL g
    have hg'inv : g'⁻¹ = caFAut_psi φ g⁻¹ := by
      rw [← hg'eq, map_inv]
    rw [hα, hg'inv, ← map_mul]
    exact hu
  obtain ⟨a', ha'⟩ := exists_inner_of_fix_jGL hk α hJ hU
  refine ⟨((caFAut_psi φ).symm a').1, ((caFAut_psi φ).symm a').2, ?_⟩
  intro g hg
  let gg : ↥(lStar φ) := ⟨g, hg⟩
  have h := ha' (caFAut_psi φ gg)
  rw [caFAut_alpha_psi] at h
  have h2 : caFAut_conjOn x hxL gg =
      (caFAut_psi φ).symm a' * gg * ((caFAut_psi φ).symm a')⁻¹ := by
    calc caFAut_conjOn x hxL gg
        = (caFAut_psi φ).symm (caFAut_psi φ (caFAut_conjOn x hxL gg)) := by
          rw [MulEquiv.symm_apply_apply]
      _ = (caFAut_psi φ).symm (a' * caFAut_psi φ gg * a'⁻¹) := by rw [h]
      _ = (caFAut_psi φ).symm a' * gg * ((caFAut_psi φ).symm a')⁻¹ := by
          simp [map_mul]
  have h3 := congrArg Subtype.val h2
  rw [caFAut_conjOn_coe] at h3
  simpa using h3

theorem le_uStar_of_isPGroup_of_normal (hS : CentASetting (k + 2) Y L R b t φ) (D : Subgroup G)
    (hD : D ≤ lStar φ ⊓ Subgroup.centralizer ({t} : Set G)) (hD2 : IsPGroup 2 D)
    (hn : ∀ g ∈ lStar φ ⊓ Subgroup.centralizer ({t} : Set G), ∀ d ∈ D, g * d * g⁻¹ ∈ D) :
    D ≤ uStar φ := by
  have hDl : D ≤ lStar φ := fun d hd => (hD hd).1
  have hDt : D ≤ Subgroup.centralizer ({t} : Set G) := fun d hd => (hD hd).2
  let D' : Subgroup (GL (BlkIdx 1 k) (ZMod 2)) :=
    (D.subgroupOf (lStar φ)).map (caFAut_psi φ).toMonoidHom
  have hD'C : D' ≤ Cent 1 k := by
    rintro x hx
    rcases (Subgroup.mem_map).mp hx with ⟨g, hg, rfl⟩
    have hgt : g.1 * t = t * g.1 :=
      Subgroup.mem_centralizer_singleton_iff.mp (hDt hg)
    exact (caFAut_mem_cent_iff hS g).mp hgt
  have hD'n : ∀ c ∈ Cent 1 k, ∀ d ∈ D', c * d * c⁻¹ ∈ D' := by
    intro c hc d hd
    rcases (Subgroup.mem_map).mp hd with ⟨g, hg, rfl⟩
    obtain ⟨h, rfl⟩ : ∃ h : ↥(lStar φ), caFAut_psi φ h = c :=
      ⟨(caFAut_psi φ).symm c, (caFAut_psi φ).apply_symm_apply c⟩
    have hht : h.1 * t = t * h.1 := (caFAut_mem_cent_iff hS h).mpr hc
    have hmem : h * g * h⁻¹ ∈ D.subgroupOf (lStar φ) := by
      change h.1 * g.1 * h.1⁻¹ ∈ D
      exact hn h.1 ⟨h.2, Subgroup.mem_centralizer_singleton_iff.mpr hht⟩ g.1 hg
    have hconj : caFAut_psi φ h * caFAut_psi φ g * (caFAut_psi φ h)⁻¹ =
        caFAut_psi φ (h * g * h⁻¹) := by simp [map_mul]
    change caFAut_psi φ h * caFAut_psi φ g * (caFAut_psi φ h)⁻¹ ∈ D'
    rw [hconj]
    exact Subgroup.mem_map_of_mem _ hmem
  have hD'P : IsPGroup 2 D' := by
    have hsub : IsPGroup 2 (D.subgroupOf (lStar φ)) :=
      hD2.of_equiv (Subgroup.subgroupOfEquivOfLe hDl).symm
    exact hsub.map (caFAut_psi φ).toMonoidHom
  have hD'le : D' ≤ uSub 1 k :=
    le_uSub_of_isPGroup_of_normal 1 k D' hD'C hD'n hD'P
  intro d hd
  have hdl : d ∈ lStar φ := hDl hd
  let g : ↥(lStar φ) := ⟨d, hdl⟩
  have hg : g ∈ D.subgroupOf (lStar φ) := hd
  have hpsi : caFAut_psi φ g ∈ D' := Subgroup.mem_map_of_mem _ hg
  exact (caFAut_mem_uStar_iff g).mpr (hD'le hpsi)

theorem exists_conj_eq_of_mem_normalizer_lStar (hS : CentASetting (k + 2) Y L R b t φ) {x : G}
    (hx : x ∈ Subgroup.normalizer (lStar φ : Set G)) :
    ∃ y ∈ Y, y * t * y⁻¹ = x * t * x⁻¹ := by
  have hk : 1 ≤ k := by
    rcases hS.m_cases with h | h <;> omega
  let α : MulAut (GL (BlkIdx 1 k) (ZMod 2)) := caFAut_alpha x hx
  obtain ⟨c', hc'⟩ :=
    isConj_iff.mp (isConj_map_of_mulAut hk α (IsConj.refl (jGL 1 k)))
  refine ⟨((caFAut_psi φ).symm c').1, liftSub_le (φ := φ) (K := (embGL k).range)
    ((caFAut_psi φ).symm c').2, ?_⟩
  have ht : caFAut_psi φ ⟨t, t_mem_lStar hS⟩ = jGL 1 k := caFAut_psi_t hS
  have hαJ : α (jGL 1 k) =
      caFAut_psi φ (caFAut_conjOn x hx ⟨t, t_mem_lStar hS⟩) := by
    rw [← ht]
    exact caFAut_alpha_psi x hx ⟨t, t_mem_lStar hS⟩
  have h1 : caFAut_conjOn x hx ⟨t, t_mem_lStar hS⟩ =
      (caFAut_psi φ).symm c' * ⟨t, t_mem_lStar hS⟩ * ((caFAut_psi φ).symm c')⁻¹ := by
    calc caFAut_conjOn x hx ⟨t, t_mem_lStar hS⟩
        = (caFAut_psi φ).symm
            (caFAut_psi φ (caFAut_conjOn x hx ⟨t, t_mem_lStar hS⟩)) := by
          rw [MulEquiv.symm_apply_apply]
      _ = (caFAut_psi φ).symm (α (jGL 1 k)) := by rw [hαJ]
      _ = (caFAut_psi φ).symm (c' * jGL 1 k * c'⁻¹) := by rw [hc']
      _ = (caFAut_psi φ).symm c' * (caFAut_psi φ).symm (jGL 1 k) *
            ((caFAut_psi φ).symm c')⁻¹ := by simp
      _ = (caFAut_psi φ).symm c' * ⟨t, t_mem_lStar hS⟩ * ((caFAut_psi φ).symm c')⁻¹ := by
          rw [← ht, MulEquiv.symm_apply_apply]
  have h2 := congrArg Subtype.val h1
  rw [caFAut_conjOn_coe] at h2
  simpa using h2.symm

end CFSG.StandardType.FF81.CentA

end
