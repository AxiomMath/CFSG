module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGAutOmFAux

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
  CFSG.StandardType.Triality CFSG.LieType.Universal.Spin CFSG.LieType.Steinberg
  CFSG.SeitzReduction.OmegaPilot
open CFSG.Open (StatedLieTag StatedLieAdmissible)

private theorem irgOF_mem_rootGroup (g : ℕ) {γ : Fin 4 → ℤ}
    (hγ : γ ∈ (Spin.plusDatum 4 (irgOF_F g) d4_three_le).roots)
    (y : spinGroup (Spin.quadPlus 4 (irgOF_F g))) :
    y ∈ (Spin.plusDatum 4 (irgOF_F g) d4_three_le).rootGroup γ ↔
      ∃ c, SpinPlus.x 4 (irgOF_F g) d4_three_le γ c = y := by
  obtain ⟨i, j, hij, s, t, h, hX⟩ :=
    Spin.exists_plusRootGroup_eq (K := irgOF_F g) d4_three_le hγ
  rw [show (Spin.plusDatum 4 (irgOF_F g) d4_three_le).rootGroup γ = _ from hX,
    MonoidHom.mem_range]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨Multiplicative.toAdd c, xr_eq_longRoot hij h (Multiplicative.toAdd c)⟩
  · rintro ⟨c, rfl⟩
    exact ⟨Multiplicative.ofAdd c, (xr_eq_longRoot hij h c).symm⟩

private theorem irgOF_normalForm_xr (g : ℕ) (x : irgOF_P g) (ρ : d4DiagramGroup)
    (σ : irgOF_F g ≃+* irgOF_F g) {γ : Fin 4 → ℤ}
    (hγ : γ ∈ (SpinPlus.Φ 4 (irgOF_F g) d4_three_le).roots) (c : irgOF_F g) :
    (MulAut.conj x * plusFourGraphAut (irgOF_F g) ρ * fieldAutHom (irgOF_F g) 4 σ)
        (spin8Equiv (irgOF_F g) (SpinPlus.x 4 (irgOF_F g) d4_three_le γ c)) =
      x * spin8Equiv (irgOF_F g)
        (SpinPlus.x 4 (irgOF_F g) d4_three_le
          (fundPerm (ρ : Equiv.Perm (Fin 4)) γ) (σ c)) * x⁻¹ := by
  rw [MulAut.mul_apply, MulAut.mul_apply, fieldAutHom_spin8Equiv_x σ hγ,
    plusFourGraphAut_x ρ hγ (σ c), MulAut.conj_apply]

private theorem irgOF_normalForm_rootGroup (g : ℕ) (x : irgOF_P g) (ρ : d4DiagramGroup)
    (σ : irgOF_F g ≃+* irgOF_F g) {γ : Fin 4 → ℤ}
    (hγ : γ ∈ (Spin.plusDatum 4 (irgOF_F g) d4_three_le).roots) :
    Subgroup.map ((MulAut.conj x * plusFourGraphAut (irgOF_F g) ρ *
        fieldAutHom (irgOF_F g) 4 σ : MulAut (irgOF_P g)).toMonoidHom)
      (Subgroup.map (spin8Equiv (irgOF_F g)).toMonoidHom
        ((Spin.plusDatum 4 (irgOF_F g) d4_three_le).rootGroup γ)) =
    Subgroup.map (MulAut.conj x).toMonoidHom
      (Subgroup.map (spin8Equiv (irgOF_F g)).toMonoidHom
        ((Spin.plusDatum 4 (irgOF_F g) d4_three_le).rootGroup
          (fundPerm (ρ : Equiv.Perm (Fin 4)) γ))) := by
  have hγ' : fundPerm (ρ : Equiv.Perm (Fin 4)) γ ∈
      (Spin.plusDatum 4 (irgOF_F g) d4_three_le).roots := fundPerm_mem_spinRoots ρ hγ
  ext y
  rw [Subgroup.mem_map, Subgroup.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [Subgroup.mem_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    obtain ⟨c, rfl⟩ := (irgOF_mem_rootGroup g hγ w).1 hw
    refine ⟨spin8Equiv (irgOF_F g) (SpinPlus.x 4 (irgOF_F g) d4_three_le
      (fundPerm (ρ : Equiv.Perm (Fin 4)) γ) (σ c)),
      Subgroup.mem_map.2 ⟨_, (irgOF_mem_rootGroup g hγ' _).2 ⟨σ c, rfl⟩, rfl⟩, ?_⟩
    exact (irgOF_normalForm_xr g x ρ σ hγ c).symm
  · rintro ⟨z, hz, rfl⟩
    rw [Subgroup.mem_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    obtain ⟨d, rfl⟩ := (irgOF_mem_rootGroup g hγ' w).1 hw
    obtain ⟨c, rfl⟩ := σ.surjective d
    refine ⟨spin8Equiv (irgOF_F g) (SpinPlus.x 4 (irgOF_F g) d4_three_le γ c),
      Subgroup.mem_map.2 ⟨_, (irgOF_mem_rootGroup g hγ _).2 ⟨c, rfl⟩, rfl⟩, ?_⟩
    exact irgOF_normalForm_xr g x ρ σ hγ c

private theorem irgOF_quotEquiv_comp_mk
    (g : ℕ) :
    (irgOF_quotEquiv (g := g)).toMonoidHom.comp
      (QuotientGroup.mk' (Subgroup.center (ggU .POmegaPlus 4 g).K)) =
    (spin8Equiv (irgOF_F g)).toMonoidHom := by
  ext x
  exact irgOF_quotEquiv_mk (g := g) x

private theorem irgOF_map_map_conj {G H : Type*} [Group G] [Group H] (S : G ≃* H) (w : G)
    (X : Subgroup G) :
    (X.map (MulAut.conj w).toMonoidHom).map S.toMonoidHom =
      (X.map S.toMonoidHom).map (MulAut.conj (S w)).toMonoidHom := by
  have h : S.toMonoidHom.comp (MulAut.conj w).toMonoidHom =
      (MulAut.conj (S w)).toMonoidHom.comp S.toMonoidHom := by
    ext z
    show S (w * z * w⁻¹) = S w * S z * (S w)⁻¹
    simp only [map_mul, map_inv]
  rw [Subgroup.map_map, Subgroup.map_map, h]

private theorem irgOF_map_conj_map {G : Type*} [Group G] (α : MulAut G) (v : G)
    (Z : Subgroup G) :
    (Z.map (MulAut.conj v).toMonoidHom).map α.toMonoidHom =
      (Z.map α.toMonoidHom).map (MulAut.conj (α v)).toMonoidHom :=
  irgOF_map_map_conj α v Z

private theorem irgOF_map_conj_conj {G : Type*} [Group G] (Z : Subgroup G) (a w : G) :
    (Z.map (MulAut.conj w).toMonoidHom).map (MulAut.conj a).toMonoidHom =
      Z.map (MulAut.conj (a * w)).toMonoidHom := by
  have h : (MulAut.conj a).toMonoidHom.comp (MulAut.conj w).toMonoidHom =
      (MulAut.conj (a * w)).toMonoidHom := by
    ext z
    show a * (w * z * w⁻¹) * a⁻¹ = a * w * z * (a * w)⁻¹
    group
  rw [Subgroup.map_map, h]

private theorem irgOF_quot_map {K Q P : Type*} [Group K] [Group Q] [Group P] (mk : K →* Q)
    (e : Q ≃* P) (S : K ≃* P) (hS : e.toMonoidHom.comp mk = S.toMonoidHom) (X : Subgroup K)
    (w : K) :
    ((X.map (MulAut.conj w).toMonoidHom).map mk).map e.toMonoidHom =
      (X.map S.toMonoidHom).map (MulAut.conj (S w)).toMonoidHom := by
  rw [Subgroup.map_map (X.map (MulAut.conj w).toMonoidHom) e.toMonoidHom mk, hS]
  exact irgOF_map_map_conj S w X

private theorem irgOF_transport {K Q P : Type*} [Group K] [Group Q] [Group P] (mk : K →* Q)
    (e : Q ≃* P) (S : K ≃* P) (hS : e.toMonoidHom.comp mk = S.toMonoidHom) (θ : MulAut Q)
    (θ' : MulAut P) (hθ : ∀ q, e (θ q) = θ' (e q)) (x : P) (X Y : Subgroup K)
    (hcore : (X.map S.toMonoidHom).map θ'.toMonoidHom =
      (Y.map S.toMonoidHom).map (MulAut.conj x).toMonoidHom) (u' : K) :
    ((X.map (MulAut.conj u').toMonoidHom).map mk).map θ.toMonoidHom =
      (Y.map (MulAut.conj (S.symm (θ' (S u') * x))).toMonoidHom).map mk := by
  refine Subgroup.map_injective (f := e.toMonoidHom) e.injective ?_
  have hcomp : e.toMonoidHom.comp θ.toMonoidHom = θ'.toMonoidHom.comp e.toMonoidHom := by
    ext q
    exact hθ q
  have hstep : ∀ R : Subgroup Q, (R.map θ.toMonoidHom).map e.toMonoidHom =
      (R.map e.toMonoidHom).map θ'.toMonoidHom := by
    intro R
    rw [Subgroup.map_map R e.toMonoidHom θ.toMonoidHom,
      Subgroup.map_map R θ'.toMonoidHom e.toMonoidHom, hcomp]
  calc (((X.map (MulAut.conj u').toMonoidHom).map mk).map θ.toMonoidHom).map e.toMonoidHom
      = (((X.map (MulAut.conj u').toMonoidHom).map mk).map e.toMonoidHom).map θ'.toMonoidHom :=
        hstep _
    _ = ((X.map S.toMonoidHom).map (MulAut.conj (S u')).toMonoidHom).map θ'.toMonoidHom := by
        rw [irgOF_quot_map mk e S hS X u']
    _ = ((X.map S.toMonoidHom).map θ'.toMonoidHom).map (MulAut.conj (θ' (S u'))).toMonoidHom :=
        irgOF_map_conj_map θ' (S u') (X.map S.toMonoidHom)
    _ = ((Y.map S.toMonoidHom).map (MulAut.conj x).toMonoidHom).map
          (MulAut.conj (θ' (S u'))).toMonoidHom := by
        rw [hcore]
    _ = (Y.map S.toMonoidHom).map (MulAut.conj (θ' (S u') * x)).toMonoidHom :=
        irgOF_map_conj_conj (Y.map S.toMonoidHom) (θ' (S u')) x
    _ = ((Y.map (MulAut.conj (S.symm (θ' (S u') * x))).toMonoidHom).map mk).map e.toMonoidHom := by
        rw [irgOF_quot_map mk e S hS Y (S.symm (θ' (S u') * x)), MulEquiv.apply_symm_apply]

theorem irgRootPairAut_POmegaPlus_four
    {g : ℕ} (hadm : StatedLieAdmissible .POmegaPlus 4 2 g) : IRGRootPairAut .POmegaPlus 4 g := by
  intro θ β' hβ' hlong u'
  let e : IRGQuot .POmegaPlus 4 g ≃* irgOF_P g := irgOF_quotEquiv (g := g)
  let S : (ggU .POmegaPlus 4 g).K ≃* irgOF_P g := spin8Equiv (irgOF_F g)
  have hS : e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center (ggU .POmegaPlus 4 g).K)) =
      S.toMonoidHom := irgOF_quotEquiv_comp_mk (g := g)
  let θ' : MulAut (irgOF_P g) := MulAut.congr e θ
  have hθ : ∀ q, e (θ q) = θ' (e q) := fun q => by
    show e (θ q) = e (θ (e.symm (e q)))
    rw [MulEquiv.symm_apply_apply]
  obtain ⟨x, ρ, σ, hθ'⟩ := irgOF_normalForm (g := g) θ'
  have hβ'D : β' ∈ (Spin.plusDatum 4 (irgOF_F g) d4_three_le).roots := hβ'
  have hnegD : (-β') ∈ (Spin.plusDatum 4 (irgOF_F g) d4_three_le).roots :=
    CFSG.LieType.Steinberg.OfCartan.neg_mem_roots
      (Spin.plusDatum 4 (irgOF_F g) d4_three_le).isFiniteType hβ'D
  have hβ : fundPerm (ρ : Equiv.Perm (Fin 4)) β' ∈
      (Spin.plusDatum 4 (irgOF_F g) d4_three_le).roots := fundPerm_mem_spinRoots ρ hβ'D
  have hlongβ : GGLongRoot (Spin.plusDatum 4 (irgOF_F g) d4_three_le)
      (fundPerm (ρ : Equiv.Perm (Fin 4)) β') :=
    ggLongRoot_of_symmetric
      (CFSG.ClassicalInvolution.ModelFacts.isIrreducible_cartanD d4_three_le)
      (fun i j => CFSG.ClassicalInvolution.ModelFacts.cartanD_symm 4 i j) rfl hβ
  have hcore := irgOF_normalForm_rootGroup (g := g) x ρ σ hβ'D
  have hcoreN := irgOF_normalForm_rootGroup (g := g) x ρ σ hnegD
  rw [← hθ'] at hcore hcoreN
  have hrg : (Spin.plusDatum 4 (irgOF_F g) d4_three_le).rootGroup
        (fundPerm (ρ : Equiv.Perm (Fin 4)) (-β')) =
      (Spin.plusDatum 4 (irgOF_F g) d4_three_le).rootGroup
        (-(fundPerm (ρ : Equiv.Perm (Fin 4)) β')) :=
    congrArg (Spin.plusDatum 4 (irgOF_F g) d4_three_le).rootGroup
      (map_neg (fundPerm (ρ : Equiv.Perm (Fin 4))) β')
  have hcoreN' : (((Spin.plusDatum 4 (irgOF_F g) d4_three_le).rootGroup (-β')).map
        S.toMonoidHom).map θ'.toMonoidHom =
      (((Spin.plusDatum 4 (irgOF_F g) d4_three_le).rootGroup
        (-(fundPerm (ρ : Equiv.Perm (Fin 4)) β'))).map S.toMonoidHom).map
        (MulAut.conj x).toMonoidHom := by
    rw [← hrg]
    exact hcoreN
  refine ⟨fundPerm (ρ : Equiv.Perm (Fin 4)) β', ⟨hβ, Or.inl hlongβ⟩,
    S.symm (θ' (S u') * x), ?_, ?_⟩
  · unfold ggRootSub
    exact irgOF_transport (QuotientGroup.mk' (Subgroup.center (ggU .POmegaPlus 4 g).K)) e S hS
      θ θ' hθ x _ _ hcore u'
  · unfold ggRootSub
    exact irgOF_transport (QuotientGroup.mk' (Subgroup.center (ggU .POmegaPlus 4 g).K)) e S hS
      θ θ' hθ x _ _ hcoreN' u'

end CFSG.StandardType.RCKRP
