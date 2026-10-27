module

public import CFSG.Assembly.Defs
public import CFSG.GroupTheory.CentralizerSup
public import CFSG.LocalAnalysis.StandardType.GGLieBridgeHom
public import CFSG.Assembly.Subnormal
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.GroupTheory.LocalCores.Fitting

public section

namespace CFSG.StandardType.LieCore

open CFSG.Assembly

private theorem l10b2_E_le {G Y : Type} [Group G] [Group Y] {G₀ D : Subgroup G} {A : Subgroup Y}
    {θ : ↥G₀ →* Y} (h₂ : ∀ a ∈ A, ∃ d ∈ D, GGLiePartner G₀ θ d a) :
    (G₀ ⊓ Subgroup.centralizer (D : Set G)).subgroupOf G₀ ≤
      (Subgroup.centralizer (A : Set Y)).comap θ := by
  intro x hx
  rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
  intro a ha
  obtain ⟨d, hd, hp⟩ := h₂ a ha
  have hx' : (x : G) ∈ G₀ ⊓ Subgroup.centralizer (D : Set G) :=
    Subgroup.mem_subgroupOf.mp hx
  have hdx : d * (x : G) * d⁻¹ = (x : G) := by
    have hc := Subgroup.mem_centralizer_iff.mp hx'.2 d hd
    rw [hc, mul_assoc, mul_inv_cancel, mul_one]
  have hmem : d * (x : G) * d⁻¹ ∈ G₀ := by rw [hdx]; exact x.2
  have hconj : θ x = a * θ x * a⁻¹ := by
    have h := hp x hmem
    rwa [show (⟨d * (x : G) * d⁻¹, hmem⟩ : ↥G₀) = x from Subtype.ext hdx] at h
  conv_rhs => rw [hconj]
  group

private theorem l10b2_normal {G Y : Type} [Group G] [Group Y] {G₀ D : Subgroup G} {A : Subgroup Y}
    {θ : ↥G₀ →* Y} (hker : θ.ker = Subgroup.center ↥G₀)
    (hDN : D ≤ Subgroup.normalizer (G₀ : Set G))
    (h₁ : ∀ d ∈ D, ∃ a ∈ A, GGLiePartner G₀ θ d a) :
    (((G₀ ⊓ Subgroup.centralizer (D : Set G)).subgroupOf G₀).subgroupOf
      ((Subgroup.centralizer (A : Set Y)).comap θ)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hn' : (n : ↥G₀) ∈ (G₀ ⊓ Subgroup.centralizer (D : Set G)).subgroupOf G₀ :=
    Subgroup.mem_subgroupOf.mp hn
  have hmain : ∀ c y : ↥G₀, c ∈ (Subgroup.centralizer (A : Set Y)).comap θ →
      y ∈ (G₀ ⊓ Subgroup.centralizer (D : Set G)).subgroupOf G₀ →
      c * y * c⁻¹ ∈ (G₀ ⊓ Subgroup.centralizer (D : Set G)).subgroupOf G₀ := by
    intro c y hc hy
    have hyD : (y : G) ∈ Subgroup.centralizer (D : Set G) :=
      (Subgroup.mem_subgroupOf.mp hy).2
    have hcg : θ c ∈ Subgroup.centralizer (A : Set Y) := Subgroup.mem_comap.mp hc
    rw [Subgroup.mem_subgroupOf]
    refine ⟨(c * y * c⁻¹ : ↥G₀).2, ?_⟩
    change (c : G) * (y : G) * (c : G)⁻¹ ∈ Subgroup.centralizer (D : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    change d * ((c : G) * (y : G) * (c : G)⁻¹) =
      ((c : G) * (y : G) * (c : G)⁻¹) * d
    obtain ⟨a, ha, hp⟩ := h₁ d hd
    have hmem : d * (c : G) * d⁻¹ ∈ G₀ :=
      (Subgroup.mem_normalizer_iff.mp (hDN hd) (c : G)).mp c.2
    set dc : ↥G₀ := ⟨d * (c : G) * d⁻¹, hmem⟩ with hdc_def
    have hdc : θ dc = a * θ c * a⁻¹ := hp c hmem
    have hca : a * θ c = θ c * a :=
      Subgroup.mem_centralizer_iff.mp hcg a ha
    have hdc_eq : θ dc = θ c := by rw [hdc, hca, mul_assoc, mul_inv_cancel, mul_one]
    set z : ↥G₀ := c⁻¹ * dc with hz_def
    have hztheta : θ z = 1 := by rw [hz_def, map_mul, map_inv, hdc_eq, inv_mul_cancel]
    have hz_ker : z ∈ θ.ker := by rw [MonoidHom.mem_ker]; exact hztheta
    have hz_center : z ∈ Subgroup.center ↥G₀ := by rw [← hker]; exact hz_ker
    have hcz : c * z = dc := by rw [hz_def, ← mul_assoc, mul_inv_cancel, one_mul]
    have hdcG : d * (c : G) * d⁻¹ = (c : G) * (z : G) := by
      have h : (((c * z : ↥G₀)) : G) = (dc : G) := congrArg Subtype.val hcz
      simpa using h.symm
    have hyd : d * (y : G) * d⁻¹ = (y : G) := by
      have h := Subgroup.mem_centralizer_iff.mp hyD d hd
      rw [h, mul_assoc, mul_inv_cancel, mul_one]
    have hzy : (z : G) * (y : G) = (y : G) * (z : G) := by
      have h := Subgroup.mem_center_iff.mp hz_center y
      exact congrArg Subtype.val h.symm
    have hzy_eq : (z : G) * (y : G) * (z : G)⁻¹ = (y : G) := by
      rw [hzy, mul_assoc, mul_inv_cancel, mul_one]
    have hconj : d * ((c : G) * (y : G) * (c : G)⁻¹) * d⁻¹ =
        (c : G) * (y : G) * (c : G)⁻¹ := by
      calc d * ((c : G) * (y : G) * (c : G)⁻¹) * d⁻¹
          = (d * (c : G) * d⁻¹) * (d * (y : G) * d⁻¹) * (d * (c : G) * d⁻¹)⁻¹ := by
              group
        _ = ((c : G) * (z : G)) * (y : G) * ((c : G) * (z : G))⁻¹ := by rw [hdcG, hyd]
        _ = (c : G) * ((z : G) * (y : G) * (z : G)⁻¹) * (c : G)⁻¹ := by group
        _ = (c : G) * (y : G) * (c : G)⁻¹ := by rw [hzy_eq]
    calc d * ((c : G) * (y : G) * (c : G)⁻¹)
        = (d * ((c : G) * (y : G) * (c : G)⁻¹) * d⁻¹) * d := by group
      _ = ((c : G) * (y : G) * (c : G)⁻¹) * d := by rw [hconj]
  refine Subgroup.mem_subgroupOf.mpr ?_
  simpa using hmain (g : ↥G₀) (n : ↥G₀) g.2 hn'

private theorem l10b2_map {G : Type} [Group G] {Y : Type} [Group Y] {G₀ : Subgroup G}
    {Γ A : Subgroup Y} {θ : ↥G₀ →* Y} (hrange : θ.range = Γ) :
    ((Subgroup.centralizer (A : Set Y)).comap θ).map θ =
      Γ ⊓ Subgroup.centralizer (A : Set Y) := by
  rw [Subgroup.map_comap_eq, hrange]

private theorem l10b2_subnormal {G : Type} [Group G] {Y : Type} [Group Y] {G₀ D J : Subgroup G}
    {A : Subgroup Y} {θ : ↥G₀ →* Y}
    (hJ : CFSG.Assembly.IsSubnormal J (G₀ ⊓ Subgroup.centralizer (D : Set G)))
    (hle : (G₀ ⊓ Subgroup.centralizer (D : Set G)).subgroupOf G₀ ≤
      (Subgroup.centralizer (A : Set Y)).comap θ)
    (hn : (((G₀ ⊓ Subgroup.centralizer (D : Set G)).subgroupOf G₀).subgroupOf
      ((Subgroup.centralizer (A : Set Y)).comap θ)).Normal) :
    CFSG.Assembly.IsSubnormal (J.subgroupOf G₀) ((Subgroup.centralizer (A : Set Y)).comap θ) := by
  have h1 : CFSG.Assembly.IsSubnormal (J.subgroupOf G₀)
      ((G₀ ⊓ Subgroup.centralizer (D : Set G)).subgroupOf G₀) := by
    simpa only [Subgroup.comap_subtype] using hJ.comap G₀.subtype
  have h2 : CFSG.Assembly.IsSubnormal
      ((G₀ ⊓ Subgroup.centralizer (D : Set G)).subgroupOf G₀)
      ((Subgroup.centralizer (A : Set Y)).comap θ) :=
    CFSG.Assembly.IsSubnormal.step hle hn (CFSG.Assembly.IsSubnormal.refl _)
  exact h1.trans h2

private theorem l10b2_nonabelian {D : Type} [Group D] (hD : CFSG.Assembly.IsQuasisimple D) :
    ∃ a b : D ⧸ Subgroup.center D, a * b ≠ b * a := by
  haveI : IsSimpleGroup (D ⧸ Subgroup.center D) := hD.2
  by_contra hcon
  push Not at hcon
  have hle : commutator D ≤ Subgroup.center D := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [← QuotientGroup.eq_one_iff]
    have h := map_commutatorElement (QuotientGroup.mk' (Subgroup.center D)) x y
    rw [commutatorElement_eq_one_iff_mul_comm.mpr (hcon _ _)] at h
    exact h
  rw [hD.1, top_le_iff] at hle
  have htriv : Subsingleton (D ⧸ Subgroup.center D) := by
    refine ⟨fun a b => ?_⟩
    induction a using QuotientGroup.induction_on with
    | H x =>
      induction b using QuotientGroup.induction_on with
      | H y =>
        rw [QuotientGroup.eq, hle]
        exact Subgroup.mem_top _
  exact not_subsingleton _ htriv

private theorem l10b2_isQuasisimple_foundations {D : Type} [Group D]
    (hD : CFSG.Assembly.IsQuasisimple D) : CFSG.IsQuasisimple D :=
  ⟨Group.IsPerfect.mk hD.1, hD.2, l10b2_nonabelian hD⟩

private theorem l10b2_quasisimple {G : Type} [Group G] {Y : Type} [Group Y] {G₀ J : Subgroup G}
    {θ : ↥G₀ →* Y} (hJG : J ≤ G₀) (hq : CFSG.Assembly.IsQuasisimple ↥J)
    (hker : θ.ker = Subgroup.center ↥G₀) :
    CFSG.Assembly.IsQuasisimple ↥((J.subgroupOf G₀).map θ) := by
  let J' : Subgroup ↥G₀ := J.subgroupOf G₀
  have hq' : CFSG.Assembly.IsQuasisimple ↥J' :=
    CFSG.Assembly.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJG) hq
  have hne : ¬ J' ≤ θ.ker := by
    intro hle
    have hcenter : Subgroup.center ↥J' = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      have hx : (x : ↥G₀) ∈ Subgroup.center ↥G₀ := by
        rw [← hker]; exact hle x.2
      show (y : ↥G₀) * (x : ↥G₀) = (x : ↥G₀) * (y : ↥G₀)
      exact Subgroup.mem_center_iff.mp hx (y : ↥G₀)
    have hsub : Subsingleton (↥J' ⧸ Subgroup.center ↥J') := by
      refine ⟨fun a b => ?_⟩
      induction a using QuotientGroup.induction_on with
      | H x =>
        induction b using QuotientGroup.induction_on with
        | H y =>
          rw [QuotientGroup.eq, hcenter]
          exact Subgroup.mem_top _
    haveI : IsSimpleGroup (↥J' ⧸ Subgroup.center ↥J') := hq'.2
    exact not_subsingleton _ hsub
  have hqF : CFSG.IsQuasisimple ↥J' := l10b2_isQuasisimple_foundations hq'
  have hm : CFSG.IsQuasisimple ↥(J'.map θ) := CFSG.LocalCores.isQuasisimple_map hqF θ hne
  show CFSG.Assembly.IsQuasisimple ↥(J'.map θ)
  exact ⟨hm.1.commutator_eq_top, hm.2.1⟩

theorem ggLieBridge_component {G : Type} [Group G] {Y : Type} [Group Y]
    (G₀ D J : Subgroup G) (Γ A : Subgroup Y) (θ : ↥G₀ →* Y)
    (hker : θ.ker = Subgroup.center ↥G₀) (hrange : θ.range = Γ)
    (hDN : D ≤ Subgroup.normalizer (G₀ : Set G))
    (h₁ : ∀ d ∈ D, ∃ a ∈ A, GGLiePartner G₀ θ d a)
    (h₂ : ∀ a ∈ A, ∃ d ∈ D, GGLiePartner G₀ θ d a) :
    IsComponentOf J (G₀ ⊓ Subgroup.centralizer (D : Set G)) →
      IsComponentOf ((J.subgroupOf G₀).map θ) (Γ ⊓ Subgroup.centralizer (A : Set Y)) := by
  rintro ⟨hJE, hsub, hqs⟩
  have hJG : J ≤ G₀ := hJE.trans inf_le_left
  have hle := l10b2_E_le (D := D) (θ := θ) h₂
  have hn := l10b2_normal hker hDN h₁
  have hmap := (l10b2_subnormal hsub hle hn).map θ
  rw [l10b2_map hrange] at hmap
  exact ⟨hmap.le, hmap, l10b2_quasisimple hJG hqs hker⟩

theorem ggLieBridge_component_of_partner {G : Type} [Group G] {Y : Type} [Group Y]
    (G₀ J : Subgroup G) (Γ : Subgroup Y) (θ : ↥G₀ →* Y)
    (hker : θ.ker = Subgroup.center ↥G₀) (hrange : θ.range = Γ)
    {d : G} {a : Y} (hdN : d ∈ Subgroup.normalizer (G₀ : Set G))
    (hpart : GGLiePartner G₀ θ d a)
    (hJ : IsComponentOf J (G₀ ⊓ Subgroup.centralizer ({d} : Set G))) :
    IsComponentOf ((J.subgroupOf G₀).map θ)
      (Γ ⊓ Subgroup.centralizer ({a} : Set Y)) := by
  rw [← CFSG.centralizer_zpowers_eq_centralizer_singleton d] at hJ
  rw [← CFSG.centralizer_zpowers_eq_centralizer_singleton a]
  refine ggLieBridge_component G₀ (Subgroup.zpowers d) J Γ (Subgroup.zpowers a) θ
    hker hrange (Subgroup.zpowers_le.mpr hdN) ?_ ?_ hJ
  · rw [Subgroup.forall_mem_zpowers]
    intro n
    exact ⟨a ^ n, Subgroup.zpow_mem_zpowers a n, GGLiePartner.zpow hdN hpart n⟩
  · rw [Subgroup.forall_mem_zpowers]
    intro n
    exact ⟨d ^ n, Subgroup.zpow_mem_zpowers d n, GGLiePartner.zpow hdN hpart n⟩

end CFSG.StandardType.LieCore
