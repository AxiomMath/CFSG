module

public import CFSG.Quasithin.Vol2.Ch3E213MP5C
public import CFSG.Quasithin.Vol2.Ch3E213MP5D
public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic

public section

namespace CFSG.Quasithin.Ch3E213M.P5

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {Y : Type*} [Group Y] {k : Type} [Field k] {K : Subgroup Y} [K.Normal]

@[expose] noncomputable def conjModel (θ : ↥K ≃* projectiveSL 3 k) (y : Y) :
    MulAut (projectiveSL 3 k) :=
  MulAut.congr θ (MulAut.conjNormal y)

theorem conjModel_apply (θ : ↥K ≃* projectiveSL 3 k) (y : Y) (x : projectiveSL 3 k) :
    conjModel θ y x = θ (MulAut.conjNormal y (θ.symm x)) := rfl

theorem map_conjModel (θ : ↥K ≃* projectiveSL 3 k) (y : Y) (X : Subgroup K) :
    (X.map θ.toMonoidHom).map (conjModel θ y).toMonoidHom =
      (X.map (MulAut.conjNormal y).toMonoidHom).map θ.toMonoidHom := by
  ext x
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, conjModel_apply]
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨_, ⟨z, hz, rfl⟩, by rw [MulEquiv.symm_apply_apply]⟩
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨θ z, ⟨z, hz, rfl⟩, by rw [MulEquiv.symm_apply_apply]⟩

theorem map_conjNormal_eq {X : Subgroup Y} {y : Y} (hy : y ∈ Subgroup.normalizer (X : Set Y)) :
    ((X ⊓ K).subgroupOf K).map (MulAut.conjNormal y).toMonoidHom = (X ⊓ K).subgroupOf K := by
  ext z
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨?_, (MulAut.conjNormal y w).2⟩
    rw [MulAut.conjNormal_apply]
    exact (Subgroup.mem_normalizer_iff.1 hy _).1 hw.1
  · intro hz
    refine ⟨MulAut.conjNormal y⁻¹ z, ?_, ?_⟩
    · rw [MulAut.conjNormal_apply]
      refine ⟨?_, (MulAut.conjNormal y⁻¹ z).2⟩
      have h := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hy) _).1 hz.1
      simpa using h
    · rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

variable [Finite k] [CharP k 2]

theorem le_pzz_of_core (hk : ∃ m : ℕ, Nat.card k = 2 ^ m) {S E : Subgroup Y}
    (θ : ↥K ≃* projectiveSL 3 k)
    (hθ : ((S ⊓ K).subgroupOf K).map θ.toMonoidHom = projUnitriangular 3 k)
    (hC : ∀ a : Y, (∀ x ∈ K, a * x = x * a) → a = 1)
    (hdiag : ∃ t ∈ S, (projStabilizer (flagSpace 3 k 1)).map (conjModel θ t).toMonoidHom ≠
      projStabilizer (flagSpace 3 k 1))
    (hES : E ≤ S) (hSE : S ≤ Subgroup.normalizer (E : Set Y)) (hE2 : ∀ x ∈ E, x * x = 1) :
    E ≤ ((pzz k).map θ.symm.toMonoidHom).map K.subtype := by
  set W := ((E ⊓ K).subgroupOf K).map θ.toMonoidHom with hWdef
  have hWU : W ≤ projUnitriangular 3 k := by
    rw [← hθ]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono _ (inf_le_inf_right K hES))
  have hW2 : ∀ x ∈ W, x * x = 1 := by
    rintro _ ⟨w, hw, rfl⟩
    rw [← map_mul]
    have h1 : w * w = 1 := Subtype.ext (by simpa using hE2 _ hw.1)
    rw [h1, map_one]
  obtain ⟨t, htS, htP⟩ := hdiag
  have htU : (projUnitriangular 3 k).map (conjModel θ t).toMonoidHom = projUnitriangular 3 k := by
    rw [← hθ, map_conjModel, map_conjNormal_eq (Subgroup.le_normalizer htS)]
  have htW : W.map (conjModel θ t).toMonoidHom = W := by
    rw [hWdef, map_conjModel, map_conjNormal_eq (hSE htS)]
  have hswap := map_pa1_eq_pa2 hk (conjModel θ t) htU htP
  have hWZ : W ≤ pzz k := by
    rw [← pa1_inf_pa2]
    rcases le_or_le_proj hWU hW2 with h | h
    · refine le_inf h ?_
      rw [← htW, ← hswap]
      exact Subgroup.map_mono h
    · refine le_inf ?_ h
      rw [← map_symm_map (conjModel θ t) W, htW, ← map_symm_map (conjModel θ t) (pa1 k), hswap]
      exact Subgroup.map_mono h
  have hEK : E ≤ K := by
    intro e he
    have hβ : ∀ u ∈ unitriangular 3 k, ∃ c : k,
        conjModel θ e (proj 3 k u) = proj 3 k (u * uu 0 0 c) := by
      intro u hu
      set s : ↥K := θ.symm (proj 3 k u) with hs
      have hsS : (s : Y) ∈ S := by
        have h1 : proj 3 k u ∈ ((S ⊓ K).subgroupOf K).map θ.toMonoidHom :=
          hθ ▸ ⟨u, hu, rfl⟩
        obtain ⟨s', hs', hs'u⟩ := h1
        have : s' = s := by rw [hs, ← hs'u]; simp
        exact this ▸ hs'.1
      have hcomm : MulAut.conjNormal e s * s⁻¹ ∈ (E ⊓ K).subgroupOf K := by
        refine ⟨?_, (MulAut.conjNormal e s * s⁻¹).2⟩
        change ((MulAut.conjNormal e s * s⁻¹ : K) : Y) ∈ E
        rw [Subgroup.coe_mul, MulAut.conjNormal_apply, Subgroup.coe_inv]
        have h2 : (s : Y) * e⁻¹ * (s : Y)⁻¹ ∈ E :=
          (Subgroup.mem_normalizer_iff.1 (hSE hsS) _).1 (E.inv_mem he)
        have h3 := E.mul_mem he h2
        rwa [show e * ((s : Y) * e⁻¹ * (s : Y)⁻¹) = e * s * e⁻¹ * (s : Y)⁻¹ by group] at h3
      obtain ⟨_, ⟨c, rfl⟩, hc⟩ := hWZ ⟨_, hcomm, rfl⟩
      obtain ⟨a, b, c', rfl⟩ := exists_eq_uu hu
      refine ⟨c, ?_⟩
      rw [conjModel_apply, ← hs]
      have h4 : θ (MulAut.conjNormal e s) = proj 3 k (uu 0 0 c) * θ s := by
        rw [hc]
        simp
      rw [h4, hs, MulEquiv.apply_symm_apply, ← map_mul, uu_comm]
    obtain ⟨x, hx⟩ := inner_of_fixes_mod_pzz (conjModel θ e) hβ
    have hcen : ∀ z ∈ K, ((θ.symm x : K) : Y) * e * z = z * (((θ.symm x : K) : Y) * e) := by
      intro z hz
      have h5 := hx (θ ⟨z, hz⟩)
      rw [conjModel_apply, MulEquiv.symm_apply_apply] at h5
      have h6 : MulAut.conjNormal e (⟨z, hz⟩ : K) = (θ.symm x)⁻¹ * ⟨z, hz⟩ * θ.symm x := by
        apply θ.injective
        rw [h5, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      have h7 := congrArg Subtype.val h6
      rw [MulAut.conjNormal_apply] at h7
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h7
      calc ((θ.symm x : K) : Y) * e * z = (θ.symm x : K) * (e * z * e⁻¹) * e := by group
        _ = z * (((θ.symm x : K) : Y) * e) := by rw [h7]; group
    have h8 := hC _ hcen
    have h9 : e = ((θ.symm x : K) : Y)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one]
      exact (mul_eq_one_iff_eq_inv.1 h8).symm ▸ by group
    rw [h9]
    exact K.inv_mem (θ.symm x).2
  intro e he
  obtain ⟨x, hx, hxe⟩ := hWZ ⟨⟨e, hEK he⟩, ⟨he, hEK he⟩, rfl⟩
  refine ⟨θ.symm (proj 3 k x), ⟨proj 3 k x, ⟨x, hx, rfl⟩, rfl⟩, ?_⟩
  simp [hxe]

end CFSG.Quasithin.Ch3E213M.P5
