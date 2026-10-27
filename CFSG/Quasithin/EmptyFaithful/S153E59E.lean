module

public import CFSG.Quasithin.EmptyFaithful.S153E59B
public import CFSG.Quasithin.Background.F9Tilde

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417 CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153E59

section Rho

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

abbrev GT (T : Subgroup G) : Type :=
  SecQuot (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G)) (quasithinOmegaOneCenter T)

abbrev UT (T M V₁ Mc : Subgroup G) : Subgroup (GT T) :=
  tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)

@[expose] noncomputable def secH (cx : Ctx15350 T Mc M V₁ V₂ t) : ↥Mc →* GT T :=
  (secMk (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G)) (quasithinOmegaOneCenter T)).comp
    (Subgroup.inclusion cx.hF.H_normalizes_V₁)

@[expose] noncomputable def toNormUT (cx : Ctx15350 T Mc M V₁ V₂ t) :
    ↥Mc →* ↥(Subgroup.normalizer (UT T M V₁ Mc : Set (GT T))) :=
  MonoidHom.codRestrict (secH cx) (Subgroup.normalizer (UT T M V₁ Mc : Set (GT T)))
    (fun h => HypF91.tilde_le_normalizer (V₁ := quasithinOmegaOneCenter T)
      (Vp := ZS153 T M V₁) (H := Mc) (le_refl Mc) (secMk_mem_secImg h.2))

@[expose] noncomputable def rho (cx : Ctx15350 T Mc M V₁ V₂ t) :
    ↥Mc →* MulAut ↥(UT T M V₁ Mc) :=
  (conjAct (UT T M V₁ Mc)).comp (toNormUT cx)

theorem rho_apply_coe (cx : Ctx15350 T Mc M V₁ V₂ t) (h : ↥Mc) (w : ↥(UT T M V₁ Mc)) :
    ((rho cx h w : ↥(UT T M V₁ Mc)) : GT T) = secH cx h * (w : GT T) * (secH cx h)⁻¹ :=
  conjAct_apply_coe' (UT T M V₁ Mc) (toNormUT cx h) w

theorem U_mem_normalizer_Z (cx : Ctx15350 T Mc M V₁ V₂ t) {u : G} (hu : u ∈ UH153 T M V₁ Mc) :
    u ∈ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
  cx.hF.H_normalizes_V₁ (U_le_Mc cx hu)

omit [Finite G] in
theorem exists_eq_secMk_of_mem_UT (w : ↥(UT T M V₁ Mc)) :
    ∃ u : ↥(Subgroup.normalizer (quasithinOmegaOneCenter T : Set G)), (u : G) ∈ UH153 T M V₁ Mc ∧
      secMk (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G)) (quasithinOmegaOneCenter T) u =
        (w : GT T) :=
  mem_secImg.mp w.2

theorem rho_eq_one_iff (cx : Ctx15350 T Mc M V₁ V₂ t) (h : ↥Mc) :
    rho cx h = 1 ↔ (h : G) ∈ pCoreOf 2 Mc := by
  constructor
  · intro h1
    rw [cx.hF.pCoreOf_eq_centralizerMod]
    refine ⟨h.2, cx.hF.H_normalizes_V₁ h.2, fun u hu => ?_⟩
    have hw : (secMk (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
        (quasithinOmegaOneCenter T) ⟨u, U_mem_normalizer_Z cx hu⟩) ∈ UT T M V₁ Mc :=
      secMk_mem_secImg hu
    have h2 := congrArg (fun φ : MulAut ↥(UT T M V₁ Mc) => ((φ ⟨_, hw⟩ : ↥(UT T M V₁ Mc)) : GT T)) h1
    simp only [MulAut.one_apply, rho_apply_coe] at h2
    have h3 : secH cx h * secMk (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
        (quasithinOmegaOneCenter T) ⟨u, U_mem_normalizer_Z cx hu⟩ =
        secMk (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
          (quasithinOmegaOneCenter T) ⟨u, U_mem_normalizer_Z cx hu⟩ * secH cx h := by
      calc _ = (secH cx h * secMk (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
          (quasithinOmegaOneCenter T) ⟨u, U_mem_normalizer_Z cx hu⟩ * (secH cx h)⁻¹) * secH cx h := by
            group
        _ = _ := by rw [h2]
    exact commutator_mem_of_secMk_commute (x := Subgroup.inclusion cx.hF.H_normalizes_V₁ h)
      (y := ⟨u, U_mem_normalizer_Z cx hu⟩) h3
  · intro hQ
    rw [cx.hF.pCoreOf_eq_centralizerMod] at hQ
    refine MulEquiv.ext fun w => Subtype.ext ?_
    obtain ⟨u, hu, hw⟩ := exists_eq_secMk_of_mem_UT w
    rw [rho_apply_coe, MulAut.one_apply, ← hw]
    have hc := secMk_comm_of_commutator_mem (A := Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
      (K := quasithinOmegaOneCenter T) (x := Subgroup.inclusion cx.hF.H_normalizes_V₁ h) (y := u)
      (hQ.2.2 u hu)
    have hc' : secH cx h * secMk (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
        (quasithinOmegaOneCenter T) u = secMk (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
        (quasithinOmegaOneCenter T) u * secH cx h := hc
    calc secH cx h * secMk _ _ u * (secH cx h)⁻¹ = (secMk _ _ u * secH cx h) * (secH cx h)⁻¹ := by
          rw [hc']
      _ = _ := by group

theorem map_rho (cx : Ctx15350 T Mc M V₁ V₂ t) {B : Subgroup G} (hB : B ≤ Mc) :
    (B.subgroupOf Mc).map (rho cx) =
      autOn (tildeOf (quasithinOmegaOneCenter T) B) (UT T M V₁ Mc) := by
  ext a
  rw [mem_autOn_iff, Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨toNormUT cx h, secMk_mem_secImg (x := Subgroup.inclusion cx.hF.H_normalizes_V₁ h)
      (Subgroup.mem_subgroupOf.mp hh), rfl⟩
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨x, hxB, hxs⟩ := mem_secImg.mp hs
    refine ⟨⟨x, hB hxB⟩, Subgroup.mem_subgroupOf.mpr hxB, ?_⟩
    have : toNormUT cx ⟨x, hB hxB⟩ = s := Subtype.ext hxs
    show (conjAct (UT T M V₁ Mc)) (toNormUT cx ⟨x, hB hxB⟩) = _
    rw [this]

theorem range_rho (cx : Ctx15350 T Mc M V₁ V₂ t) : (rho cx).range = HStar153 T M V₁ Mc := by
  have := map_rho cx (le_refl Mc)
  rw [Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map] at this
  exact this

end Rho

end S153E59

end CFSG.Quasithin
