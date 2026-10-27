module

public import CFSG.Quasithin.Background.RonanH44Nfs

public section

namespace CFSG.Quasithin.RonanH44

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.L3Nine CFSG.Quasithin.H.SU3 Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem nfsTr_inv_linear {F : Type} [Field F] (scalar : F →+* K)
    (hfix : ∀ c : F, bar n (scalar c) = scalar c) (y : MulAut (HMod n K))
    (hy : ∀ (c : F) (v w : HMod n K), mat w = scalar c • mat v →
      mat (y w) = scalar c • mat (y v)) :
    ∀ (c : F) (v w : HMod n K), mat w = scalar c • mat v →
      mat (y⁻¹ w) = scalar c • mat (y⁻¹ v) := by
  intro c v w hvw
  obtain ⟨u, hu⟩ : ∃ u : HMod n K, mat u = scalar c • mat (y⁻¹ v) :=
    ⟨nfsSmul scalar hfix c (y⁻¹ v), mat_nfsSmul scalar hfix c (y⁻¹ v)⟩
  have h1 : mat (y u) = mat w := by
    rw [hy c (y⁻¹ v) u hu, MulAut.apply_inv_self, hvw]
  have h2 : y u = w := mat_injective h1
  have h3 : y⁻¹ w = u := by
    rw [← h2, MulAut.inv_apply_self]
  rw [h3, hu]

theorem nfsTr_mem_map_iff (y : MulAut (HMod n K)) (S : Subgroup (HMod n K)) (v : HMod n K) :
    v ∈ S.map y.toMonoidHom ↔ y⁻¹ v ∈ S := by
  rw [Subgroup.mem_map_equiv, MulAut.inv_apply]

theorem nfsTr_conj_apply (y g : MulAut (HMod n K)) (v : HMod n K) :
    (MulAut.conj y).toMonoidHom g v = y (g (y⁻¹ v)) := by
  change (y * g * y⁻¹) v = y (g (y⁻¹ v))
  rw [MulAut.mul_apply, MulAut.mul_apply]

theorem nfs_transport {F : Type} [Field F] (scalar : F →+* K)
    (hfix : ∀ c : F, bar n (scalar c) = scalar c)
    {G : Subgroup (MulAut (HMod n K))} {U Z : Subgroup (HMod n K)} {d : ℕ}
    (y : MulAut (HMod n K))
    (hy : ∀ (c : F) (v w : HMod n K), mat w = scalar c • mat v → mat (y w) = scalar c • mat (y v))
    (h : NineFaithSec scalar G U Z d) :
    NineFaithSec scalar (G.map (MulAut.conj y).toMonoidHom) (U.map y.toMonoidHom)
      (Z.map y.toMonoidHom) d := by
  have hy' := nfsTr_inv_linear scalar hfix y hy
  unfold NineFaithSec at h ⊢
  obtain ⟨hZU, hGU, hGZ, hUs, hZs, β, hβs, hβk, hβc, action, hinj, hact⟩ := h
  obtain ⟨eU, heU⟩ : ∃ e : ↥U ≃* ↥(U.map y.toMonoidHom),
      ∀ u : ↥U, ((e u : ↥(U.map y.toMonoidHom)) : HMod n K) = y (u : HMod n K) :=
    ⟨Subgroup.equivMapOfInjective U y.toMonoidHom y.injective, fun u => rfl⟩
  obtain ⟨eG, heG⟩ : ∃ e : ↥G ≃* ↥(G.map (MulAut.conj y).toMonoidHom),
      ∀ g : ↥G, ((e g : ↥(G.map (MulAut.conj y).toMonoidHom)) : MulAut (HMod n K)) =
        (MulAut.conj y).toMonoidHom (g : MulAut (HMod n K)) :=
    ⟨Subgroup.equivMapOfInjective G (MulAut.conj y).toMonoidHom (MulAut.conj y).injective,
      fun g => rfl⟩
  have hU_symm : ∀ v : ↥(U.map y.toMonoidHom),
      ((eU.symm v : ↥U) : HMod n K) = y⁻¹ (v : HMod n K) := by
    intro v
    have h1 := heU (eU.symm v)
    rw [eU.apply_symm_apply] at h1
    rw [h1, MulAut.inv_apply_self]
  have hG_symm : ∀ (g' : ↥(G.map (MulAut.conj y).toMonoidHom)) (v : HMod n K),
      (g' : MulAut (HMod n K)) v = y (((eG.symm g' : ↥G) : MulAut (HMod n K)) (y⁻¹ v)) := by
    intro g' v
    have h1 := heG (eG.symm g')
    rw [eG.apply_symm_apply] at h1
    rw [h1, nfsTr_conj_apply]
  refine ⟨Subgroup.map_mono hZU, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro g' hg' v hv
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hg'
    rw [nfsTr_mem_map_iff] at hv ⊢
    rw [nfsTr_conj_apply, MulAut.inv_apply_self]
    exact hGU g hg _ hv
  ·
    intro g' hg' v hv
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hg'
    rw [nfsTr_mem_map_iff] at hv ⊢
    rw [nfsTr_conj_apply, MulAut.inv_apply_self]
    exact hGZ g hg _ hv
  ·
    intro c v s hv hs
    rw [nfsTr_mem_map_iff] at hv ⊢
    exact hUs c _ _ hv (hy' c v s hs)
  ·
    intro c v s hv hs
    rw [nfsTr_mem_map_iff] at hv ⊢
    exact hZs c _ _ hv (hy' c v s hs)
  · refine ⟨β.comp eU.symm.toMonoidHom, ?_, ?_, ?_, action.comp eG.symm.toMonoidHom, ?_, ?_⟩
    ·
      intro x
      obtain ⟨u, hu⟩ := hβs x
      refine ⟨eU u, ?_⟩
      show β (eU.symm (eU u)) = x
      rw [MulEquiv.symm_apply_apply]
      exact hu
    ·
      intro v
      show β (eU.symm v) = 1 ↔ (v : HMod n K) ∈ Z.map y.toMonoidHom
      rw [hβk, hU_symm, nfsTr_mem_map_iff]
    ·
      intro c v w hvw
      show Multiplicative.toAdd (β (eU.symm w)) = c • Multiplicative.toAdd (β (eU.symm v))
      apply hβc c (eU.symm v) (eU.symm w)
      rw [hU_symm, hU_symm]
      exact hy' c _ _ hvw
    ·
      intro a b hab
      exact eG.symm.injective (hinj (show action (eG.symm a) = action (eG.symm b) from hab))
    ·
      intro g' v w hw
      show Multiplicative.toAdd (β (eU.symm w)) =
        action (eG.symm g') (Multiplicative.toAdd (β (eU.symm v)))
      apply hact (eG.symm g') (eU.symm v) (eU.symm w)
      rw [hU_symm, hU_symm, hw, hG_symm g' (v : HMod n K), MulAut.inv_apply_self]

end CFSG.Quasithin.RonanH44
