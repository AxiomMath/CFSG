module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.ReduceLine
public import CFSG.Quasithin.Background.D2Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NatParMax

open CFSG.Quasithin Matrix

variable {W : Type} [CommGroup W] {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem inf_normalizer_le_inf_stabSub (H S : Subgroup (MulAut W)) :
    H ⊓ Subgroup.normalizer (S : Set (MulAut W)) ≤ H ⊓ stabSub (fixV S) := by
  intro g hg
  obtain ⟨hgH, hgN⟩ := Subgroup.mem_inf.1 hg
  refine Subgroup.mem_inf.2 ⟨hgH, mem_stabSub.2 fun u => ⟨?_, ?_⟩⟩
  · intro hgu s hs
    have hgs : g * s * g⁻¹ ∈ S := (Subgroup.mem_set_normalizer_iff.1 hgN s).1 hs
    have hfix : (g * s * g⁻¹) (g u) = g u := hgu _ hgs
    have h1 : (g * s * g⁻¹) (g u) = g (s u) := by simp [MulAut.mul_apply]
    rw [h1] at hfix
    exact g.injective hfix
  · intro hu s hs
    have hgs : g⁻¹ * s * g ∈ S := (Subgroup.mem_set_normalizer_iff''.1 hgN s).1 hs
    have hfix : (g⁻¹ * s * g) u = u := hu _ hgs
    have hge : g * (g⁻¹ * s * g) = s * g := by group
    calc s (g u) = (s * g) u := rfl
      _ = (g * (g⁻¹ * s * g)) u := by rw [hge]
      _ = g ((g⁻¹ * s * g) u) := by rw [MulAut.mul_apply]
      _ = g u := by rw [hfix]

theorem normalizer_subgroupOf_eq {G : Type} [Group G] {H S : Subgroup G} (hSH : S ≤ H) :
    Subgroup.normalizer ((S.subgroupOf H : Subgroup ↥H) : Set ↥H) =
      (Subgroup.normalizer (S : Set G)).subgroupOf H := by
  ext h
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_set_normalizer_iff]
  constructor
  · intro hh y
    constructor
    · intro hy
      have h1 : (⟨y, hSH hy⟩ : ↥H) ∈ S.subgroupOf H := Subgroup.mem_subgroupOf.2 hy
      have h2 := (hh ⟨y, hSH hy⟩).1 h1
      simpa using Subgroup.mem_subgroupOf.1 h2
    · intro hy
      have hyH : y ∈ H := by
        have h1 : (h : G)⁻¹ * ((h : G) * y * (h : G)⁻¹) * (h : G) ∈ H :=
          H.mul_mem (H.mul_mem (H.inv_mem h.2) (hSH hy)) h.2
        convert h1 using 1
        group
      have h2 : h * ⟨y, hyH⟩ * h⁻¹ ∈ S.subgroupOf H := by
        rw [Subgroup.mem_subgroupOf]
        simpa using hy
      exact Subgroup.mem_subgroupOf.1 ((hh ⟨y, hyH⟩).2 h2)
  · intro hh x
    constructor
    · intro hx
      have h1 : (h : G) * (x : G) * (h : G)⁻¹ ∈ S :=
        (hh (x : G)).1 (Subgroup.mem_subgroupOf.1 hx)
      exact Subgroup.mem_subgroupOf.2 (by simpa using h1)
    · intro hx
      have h1 : (h : G) * (x : G) * (h : G)⁻¹ ∈ S := Subgroup.mem_subgroupOf.1 hx
      exact Subgroup.mem_subgroupOf.2 ((hh (x : G)).2 h1)

theorem le_normalizer_of_subgroupOf_le {G : Type} [Group G] {H S X : Subgroup G} (hSH : S ≤ H)
    (hXH : X ≤ H)
    (h : X.subgroupOf H ≤ Subgroup.normalizer ((S.subgroupOf H : Subgroup ↥H) : Set ↥H)) :
    X ≤ Subgroup.normalizer (S : Set G) := by
  rw [normalizer_subgroupOf_eq hSH] at h
  intro x hx
  have hxH : (⟨x, hXH hx⟩ : ↥H) ∈ X.subgroupOf H := Subgroup.mem_subgroupOf.2 hx
  have h1 := h hxH
  rw [Subgroup.mem_subgroupOf] at h1
  simpa using h1

private lemma mem_pointStab_iff_M01 {H S : Subgroup (MulAut W)} (hS : IsSylowIn 2 S H)
    (h : ↥H) :
    h ∈ KTabD.pointStab H hS.toSylow ↔ (h : MulAut W) ∈ stabSub (fixV S) := by
  letI : MulDistribMulAction ↥H W := MulDistribMulAction.compHom W H.subtype
  letI : MulAction ↥H W := MulAction.compHom W H.subtype
  letI : MulAction ↥H (Set W) := Set.mulActionSet
  letI : MulDistribMulAction ↥(hS.toSylow) W :=
    MulDistribMulAction.compHom W (H.subtype.comp (hS.toSylow : Subgroup ↥H).subtype)
  have hsmul : ∀ b : W, h • b = (h : MulAut W) b := fun _ => rfl
  have hfixV : ∀ x : W,
      x ∈ (CFSG.fixedPointSubgroup ↥(hS.toSylow) W : Subgroup W) ↔ x ∈ fixV S := by
    intro x
    rw [FixedPoints.mem_subgroup, mem_fixV]
    constructor
    · intro hx s hs
      have hmem : (⟨s, hS.le hs⟩ : ↥H) ∈ (hS.toSylow : Subgroup ↥H) := by
        rw [IsSylowIn.coe_toSylow]
        exact Subgroup.mem_subgroupOf.2 hs
      exact hx ⟨⟨s, hS.le hs⟩, hmem⟩
    · intro hx z
      have hzS : ((z : ↥H) : MulAut W) ∈ S := by
        have hz : (z : ↥H) ∈ (hS.toSylow : Subgroup ↥H) := z.2
        rw [IsSylowIn.coe_toSylow] at hz
        exact Subgroup.mem_subgroupOf.1 hz
      exact hx ((z : ↥H) : MulAut W) hzS
  show h ∈ MulAction.stabilizer ↥H
      ((CFSG.fixedPointSubgroup ↥(hS.toSylow) W : Subgroup W) : Set W) ↔
    (h : MulAut W) ∈ stabSub (fixV S)
  rw [MulAction.mem_stabilizer_set, mem_stabSub]
  constructor
  · intro hh u
    exact (hfixV ((h : MulAut W) u)).symm.trans ((hh u).trans (hfixV u))
  · intro hh b
    rw [hsmul]
    exact (hfixV ((h : MulAut W) b)).trans ((hh b).trans (hfixV b).symm)

theorem map_subtype_pointStab_eq_inf_stabSub {H S : Subgroup (MulAut W)} (hS : IsSylowIn 2 S H) :
    (KTabD.pointStab H hS.toSylow).map H.subtype = H ⊓ stabSub (fixV S) := by
  ext g
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact Subgroup.mem_inf.2 ⟨h.2, (mem_pointStab_iff_M01 hS h).1 hh⟩
  · intro hg
    obtain ⟨hgH, hgS⟩ := Subgroup.mem_inf.1 hg
    exact ⟨⟨g, hgH⟩, (mem_pointStab_iff_M01 hS ⟨g, hgH⟩).2 hgS, rfl⟩

theorem natParMax_of_realizes [Finite W] {Γ : Subgroup (GL ι K)} {H : Subgroup (MulAut W)}
    (hreal : (FFModel.nat Γ).Realizes H ⊤ ⊥) {e₀ : ι → K} (hline : KTabC.SylowFixedLine Γ e₀)
    (hmax : ∀ Y : Subgroup ↥Γ, KTabD.lineStab Γ e₀ ≤ Y →
      Y = KTabD.lineStab Γ e₀ ∨ Y = ⊤)
    {S X : Subgroup (MulAut W)} (hS : IsSylowIn 2 S H) (hXge : H ⊓ stabSub (fixV S) ≤ X)
    (hXlt : X < H) : X = H ⊓ stabSub (fixV S) := by
  obtain ⟨φ, hφ⟩ := KTabD.exists_mulEquiv_pointStab_eq_map hreal hline hS.toSylow
  let Y : Subgroup ↥Γ := (X.subgroupOf H).comap φ.toMonoidHom
  have hle : KTabD.lineStab Γ e₀ ≤ Y := by
    intro γ hγ
    have hmap : φ γ ∈ (KTabD.lineStab Γ e₀).map φ.toMonoidHom :=
      Subgroup.mem_map_of_mem φ.toMonoidHom hγ
    rw [← hφ] at hmap
    have hsub : ((φ γ : ↥H) : MulAut W) ∈ H ⊓ stabSub (fixV S) := by
      rw [← map_subtype_pointStab_eq_inf_stabSub hS]
      exact Subgroup.mem_map_of_mem H.subtype hmap
    exact Subgroup.mem_comap.2 (Subgroup.mem_subgroupOf.2 (hXge hsub))
  rcases hmax Y hle with hY | hY
  · have hXle : X ≤ H ⊓ stabSub (fixV S) := by
      intro g hg
      have hgH : g ∈ H := hXlt.le hg
      have hmemY : φ.symm ⟨g, hgH⟩ ∈ Y := by
        rw [Subgroup.mem_comap]
        simpa using Subgroup.mem_subgroupOf.2 hg
      rw [hY] at hmemY
      have hpts : (⟨g, hgH⟩ : ↥H) ∈ KTabD.pointStab H hS.toSylow := by
        rw [hφ]
        simpa using Subgroup.mem_map_of_mem φ.toMonoidHom hmemY
      exact Subgroup.mem_inf.2 ⟨hgH, (mem_pointStab_iff_M01 hS ⟨g, hgH⟩).1 hpts⟩
    exact le_antisymm hXle hXge
  · exfalso
    apply hXlt.2
    intro h hh
    have hmemY : φ.symm ⟨h, hh⟩ ∈ Y := by rw [hY]; exact Subgroup.mem_top _
    have hmemX : (⟨h, hh⟩ : ↥H) ∈ X.subgroupOf H := by
      have h1 := Subgroup.mem_comap.1 hmemY
      simpa using h1
    exact Subgroup.mem_subgroupOf.1 hmemX

end CFSG.LocalAnalysis.UniquenessCase.UC22.NatParMax
