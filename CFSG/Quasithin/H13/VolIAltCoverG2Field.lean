module

public import CFSG.Quasithin.H13.VolIAltCoverUniversal
public import CFSG.Quasithin.Background.P3G2Zorn

public section

noncomputable section

namespace CFSG.Quasithin.H13.VolI

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Open Subgroup
open scoped commutatorElement

section Field

variable {K K' : Type} [Field K] [Field K'] [CharP K 2] [CharP K' 2]

theorem g2Derived_le (K : Type) [Field K] [CharP K 2] :
    ⁅quasithinG2 K, quasithinG2 K⁆ ≤ cayleyGroup K := by
  rw [G11.P3G2.quasithinG2_eq_cayleyGroup]
  exact cayleyActor_le K .derived

@[expose] def g2DerivedFieldEquiv (e : K ≃+* K') :
    ↥⁅quasithinG2 K, quasithinG2 K⁆ ≃* ↥⁅quasithinG2 K', quasithinG2 K'⁆ :=
  (MulEquiv.subgroupCongr (by rw [G11.P3G2.quasithinG2_eq_cayleyGroup])).trans
    (((zornConj e).subgroupMap _).trans
      (MulEquiv.subgroupCongr ((map_cayley_commutator e).trans
        (by rw [G11.P3G2.quasithinG2_eq_cayleyGroup]))))

theorem coe_g2DerivedFieldEquiv (e : K ≃+* K') (γ : ↥⁅quasithinG2 K, quasithinG2 K⁆) :
    ((g2DerivedFieldEquiv e γ : ↥⁅quasithinG2 K', quasithinG2 K'⁆) :
      quasithinZorn K' ≃ₗ[K'] quasithinZorn K') =
      zornConj e (γ : quasithinZorn K ≃ₗ[K] quasithinZorn K) := rfl

@[expose] def zornQSecEquiv (e : K ≃+* K') :
    (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).Sec ≃*
      (FFModel.zornQ ⁅quasithinG2 K', quasithinG2 K'⁆).Sec :=
  (zornSecEquiv _).trans
    ((RingEquiv.piCongrRight fun _ : Ix3 => e).toAddEquiv.toMultiplicative.trans
      (zornSecEquiv _).symm)

theorem zP_act (γ : ↥⁅quasithinG2 K, quasithinG2 K⁆) {x : quasithinZorn K}
    (hx : x.1 + x.2.2.2 = 0) :
    zP ((γ : quasithinZorn K ≃ₗ[K] quasithinZorn K) x) =
      g2Act (inclusion (g2Derived_le K) γ) (zP x) :=
  g2_zP_apply (inclusion (g2Derived_le K) γ) x hx

theorem zornQSecEquiv_act (e : K ≃+* K') (γ : ↥⁅quasithinG2 K, quasithinG2 K⁆)
    (γ' : ↥⁅quasithinG2 K', quasithinG2 K'⁆) (hγ : g2DerivedFieldEquiv e γ = γ')
    (m : ↥(zornO0 K)) (m' : ↥(zornO0 K'))
    (h : zornQSecEquiv e (QuotientGroup.mk m) = QuotientGroup.mk m')
    (hm : zornAct _ γ m.1 ∈ zornO0 K) (hm' : zornAct _ γ' m'.1 ∈ zornO0 K') :
    zornQSecEquiv e (QuotientGroup.mk ⟨_, hm⟩) = QuotientGroup.mk ⟨_, hm'⟩ := by
  subst hγ
  apply (zornSecEquiv (F := K') ⁅quasithinG2 K', quasithinG2 K'⁆).injective
  have h1 := congrArg (zornSecEquiv (F := K') ⁅quasithinG2 K', quasithinG2 K'⁆) h
  simp only [zornQSecEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply] at h1 ⊢
  change Multiplicative.ofAdd ((RingEquiv.piCongrRight fun _ : Ix3 => e)
      (zP ((γ : quasithinZorn K ≃ₗ[K] quasithinZorn K) (Multiplicative.toAdd m.1)))) =
    Multiplicative.ofAdd (zP ((g2DerivedFieldEquiv e γ : quasithinZorn K' ≃ₗ[K'] quasithinZorn K')
      (Multiplicative.toAdd m'.1)))
  change Multiplicative.ofAdd ((RingEquiv.piCongrRight fun _ : Ix3 => e)
      (zP (Multiplicative.toAdd m.1))) = Multiplicative.ofAdd (zP (Multiplicative.toAdd m'.1)) at h1
  have h2 := congrArg Multiplicative.toAdd h1
  simp only [toAdd_ofAdd] at h2
  rw [zP_act γ m.2, zP_act (g2DerivedFieldEquiv e γ) m'.2, g2Act_zornConj, h2]
  rfl

@[expose] def ModelCover.mapZorn (e : K ≃+* K') {W : Type*} [CommGroup W]
    (C : ModelCover (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆) W) :
    ModelCover (FFModel.zornQ ⁅quasithinG2 K', quasithinG2 K'⁆) W where
  ρ := C.ρ.comp (g2DerivedFieldEquiv e).symm.toMonoidHom
  β := (zornQSecEquiv e).toMonoidHom.comp C.β
  surj := (zornQSecEquiv e).surjective.comp C.surj
  fix γ v hv := C.fix _ v ((zornQSecEquiv e).map_eq_one_iff.1 hv)
  equiv γ v m' hm' hvm' := by
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (C.β v)
    have hm0 : (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).act
        ((g2DerivedFieldEquiv e).symm γ) m.1 ∈ (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).sec :=
      zornAct_mem_O0 _ ((g2Derived_le K).trans
        (G11.P3G2.quasithinG2_eq_cayleyGroup (K := K)).symm.le) _ m.2
    have h1 := C.equiv ((g2DerivedFieldEquiv e).symm γ) v m hm0 hm.symm
    have h2 : zornQSecEquiv e (QuotientGroup.mk m) = QuotientGroup.mk m' := by
      rw [hm]
      exact hvm'
    refine (congrArg (zornQSecEquiv e) h1).trans ?_
    exact zornQSecEquiv_act e _ γ (MulEquiv.apply_symm_apply _ γ) m m' h2 hm0 hm'
  gen v := by
    refine closure_mono ?_ (C.gen v)
    rintro _ ⟨γ, w, rfl⟩
    refine ⟨g2DerivedFieldEquiv e γ, w, ?_⟩
    have h := MulEquiv.symm_apply_apply (g2DerivedFieldEquiv e) γ
    exact (congrArg (fun γ' => C.ρ γ' w * w⁻¹) h).symm

theorem ModelCover.mapZorn_ker (e : K ≃+* K') {W : Type*} [CommGroup W]
    (C : ModelCover (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆) W) :
    (C.mapZorn e).β.ker = C.β.ker := by
  ext v
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  exact (zornQSecEquiv e).map_eq_one_iff

end Field

end CFSG.Quasithin.H13.VolI
