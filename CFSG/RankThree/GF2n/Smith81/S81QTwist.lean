module

public import CFSG.RankThree.GF2n.Smith81.S81QGen
public import CFSG.RankThree.GF2n.Smith81.S81QStab

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.D6Spin

open CFSG.RankThree.GF2n.Smith81.E7Model CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley

section Module

variable {K K' : Type} [Field K] [Field K']

@[expose] def wMap (e : K ≃+* K') : W K ≃+ W K' := Finsupp.mapRange.addEquiv e.toAddEquiv

theorem wMap_apply (e : K ≃+* K') (w : W K) (a : Idx0) : wMap e w a = e (w a) := rfl

theorem wMap_smul (e : K ≃+* K') (c : K) (w : W K) : wMap e (c • w) = e c • wMap e w := by
  ext a
  simp [wMap_apply, map_mul]

theorem wMap_symm_apply (e : K ≃+* K') (w : W K') (a : Idx0) : (wMap e).symm w a = e.symm (w a) := by
  have : wMap e ((wMap e).symm w) = w := (wMap e).apply_symm_apply w
  have h := congrArg (fun v : W K' => v a) this
  simp only [wMap_apply] at h
  exact (e.symm_apply_eq.2 h.symm)

theorem wMap_symm_smul (e : K ≃+* K') (c : K) (w : W K') :
    (wMap e).symm (e c • w) = c • (wMap e).symm w := by
  apply (wMap e).injective
  rw [(wMap e).apply_symm_apply, wMap_smul, (wMap e).apply_symm_apply]

theorem wMap_single (e : K ≃+* K') (a : Idx0) (c : K) :
    wMap e (Finsupp.single a c) = Finsupp.single a (e c) := by
  ext b
  by_cases hb : b = a
  · subst hb
    simp [wMap_apply]
  · simp [wMap_apply, Finsupp.single_apply, Ne.symm hb]

@[expose] def conjAut (e : K ≃+* K') (g : W K ≃ₗ[K] W K) : W K' ≃ₗ[K'] W K' where
  toFun w := wMap e (g ((wMap e).symm w))
  map_add' x y := by simp [map_add]
  map_smul' c' w := by
    obtain ⟨c, rfl⟩ := e.surjective c'
    simp only [RingHom.id_apply]
    rw [wMap_symm_smul, map_smul, wMap_smul]
  invFun w := wMap e (g.symm ((wMap e).symm w))
  left_inv w := by simp
  right_inv w := by simp

theorem conjAut_apply (e : K ≃+* K') (g : W K ≃ₗ[K] W K) (w : W K') :
    conjAut e g w = wMap e (g ((wMap e).symm w)) := rfl

theorem conjAut_apply_wMap (e : K ≃+* K') (g : W K ≃ₗ[K] W K) (w : W K) :
    conjAut e g (wMap e w) = wMap e (g w) := by
  rw [conjAut_apply, AddEquiv.symm_apply_apply]

theorem wMap_symm_eq (e : K ≃+* K') : (wMap e).symm = wMap e.symm := by
  ext w a
  simp [wMap_symm_apply, wMap_apply]

theorem conjAut_symm_apply (e : K ≃+* K') (h : W K' ≃ₗ[K'] W K') (w : W K) :
    conjAut e.symm h w = (wMap e).symm (h (wMap e w)) := by
  rw [conjAut_apply, wMap_symm_eq e, show (wMap e.symm).symm = wMap e from wMap_symm_eq e.symm]

@[expose] def conjEquiv (e : K ≃+* K') : (W K ≃ₗ[K] W K) ≃* (W K' ≃ₗ[K'] W K') where
  toFun := conjAut e
  invFun := conjAut e.symm
  left_inv g := by
    apply LinearEquiv.ext
    intro w
    rw [conjAut_symm_apply, conjAut_apply_wMap, AddEquiv.symm_apply_apply]
  right_inv h := by
    apply LinearEquiv.ext
    intro w
    rw [conjAut_apply, conjAut_symm_apply, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  map_mul' g h := by
    apply LinearEquiv.ext
    intro w
    simp [conjAut_apply]

theorem conjEquiv_apply (e : K ≃+* K') (g : W K ≃ₗ[K] W K) : conjEquiv e g = conjAut e g := rfl

end Module

section Root

variable {K K' : Type} [Field K] [Field K'] [CharP K 2] [CharP K' 2]

theorem wMap_EW (e : K ≃+* K') (β : Fin (Tag.rank .E7) → ℤ) (w : W K) :
    wMap e (EW K β w) = EW K' β (wMap e w) := by
  ext b
  rw [wMap_apply, EW_apply, EW_apply]
  split_ifs
  · rfl
  · exact map_zero e

theorem conjAut_xuWUnit (e : K ≃+* K') {β : Fin (Tag.rank .E7) → ℤ} (hβ : β ∈ Perp) (c : K) :
    conjAut e (vAut0 K (xuWUnit hβ c)) = vAut0 K' (xuWUnit hβ (e c)) := by
  apply LinearEquiv.ext
  intro w'
  obtain ⟨w, rfl⟩ := (wMap e).surjective w'
  rw [conjAut_apply_wMap, vAut0_apply, vAut0_apply, xuWUnit_apply, xuWUnit_apply, map_add, wMap_smul,
    wMap_EW]

theorem conjEquiv_image_genSet0 (e : K ≃+* K') : (conjEquiv e) '' genSet0 K = genSet0 K' := by
  ext g'
  constructor
  · rintro ⟨g, ⟨β, hβ, c, rfl⟩, rfl⟩
    exact ⟨β, hβ, e c, conjAut_xuWUnit e hβ c⟩
  · rintro ⟨β, hβ, c', rfl⟩
    refine ⟨vAut0 K (xuWUnit hβ (e.symm c')), ⟨β, hβ, e.symm c', rfl⟩, ?_⟩
    rw [conjEquiv_apply, conjAut_xuWUnit, e.apply_symm_apply]

theorem map_EAut0 (e : K ≃+* K') : (EAut0 K).map (conjEquiv e).toMonoidHom = EAut0 K' := by
  rw [EAut0_eq_closure_genSet0, EAut0_eq_closure_genSet0, MonoidHom.map_closure]
  congr 1
  exact conjEquiv_image_genSet0 e

@[expose] def eAut0Congr (e : K ≃+* K') : ↥(EAut0 K) ≃* ↥(EAut0 K') :=
  ((conjEquiv e).subgroupMap (EAut0 K)).trans (MulEquiv.subgroupCongr (map_EAut0 e))

theorem coe_eAut0Congr (e : K ≃+* K') (g : ↥(EAut0 K)) :
    ((eAut0Congr e g : ↥(EAut0 K')) : W K' ≃ₗ[K'] W K') = conjAut e (g : W K ≃ₗ[K] W K) := rfl

theorem eAut0Congr_xuWUnit (e : K ≃+* K') {β : Fin (Tag.rank .E7) → ℤ} (hβ : β ∈ Perp) (c : K) :
    eAut0Congr e ⟨vAut0 K (xuWUnit hβ c), vAut0_xuWUnit_mem_EAut0 hβ c⟩ =
      ⟨vAut0 K' (xuWUnit hβ (e c)), vAut0_xuWUnit_mem_EAut0 hβ (e c)⟩ :=
  Subtype.ext (conjAut_xuWUnit e hβ c)

theorem map_rootRad0 (e : K ≃+* K') :
    ((rootRad0 K).subgroupOf (EAut0 K)).map (eAut0Congr e).toMonoidHom =
      (rootRad0 K').subgroupOf (EAut0 K') := by
  unfold rootRad0
  rw [subgroupOf_closure_eq _ _ rootSet0_subset_EAut0, subgroupOf_closure_eq _ _ rootSet0_subset_EAut0,
    MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨γ, hγ, h1, c, hxc⟩ := mem_rootSet0_iff.1 hx
    have hx' : x = ⟨vAut0 K (xuWUnit hγ c), vAut0_xuWUnit_mem_EAut0 hγ c⟩ := Subtype.ext hxc
    show ((eAut0Congr e x : ↥(EAut0 K')) : W K' ≃ₗ[K'] W K') ∈ rootSet0 K'
    rw [hx', eAut0Congr_xuWUnit e hγ c]
    exact mem_rootSet0_iff.2 ⟨γ, hγ, h1, e c, rfl⟩
  · intro hy
    obtain ⟨γ, hγ, h1, c', hyc⟩ := mem_rootSet0_iff.1 hy
    have hy' : y = ⟨vAut0 K' (xuWUnit hγ c'), vAut0_xuWUnit_mem_EAut0 hγ c'⟩ := Subtype.ext hyc
    refine ⟨⟨vAut0 K (xuWUnit hγ (e.symm c')), vAut0_xuWUnit_mem_EAut0 hγ _⟩, ?_, ?_⟩
    · exact mem_rootSet0_iff.2 ⟨γ, hγ, h1, e.symm c', rfl⟩
    · rw [hy']
      show eAut0Congr e ⟨vAut0 K (xuWUnit hγ (e.symm c')), _⟩ = _
      rw [eAut0Congr_xuWUnit, e.apply_symm_apply]

private theorem hm_single (i : Fin (Tag.rank .E7)) (c : Kˣ) (a : Fin e7Data.d) :
    (((e7Data_valid.hm K i c : ↥(e7Data_valid.minGroup K)) : (Module.End K (V K))ˣ) :
        Module.End K (V K)) (Finsupp.single a 1) =
      ((c ^ e7Data.wt a i : Kˣ) : K) • Finsupp.single a 1 := by
  change e7Data_valid.endo K (e7Data_valid.hm K i c) (Finsupp.single a 1) = _
  rw [e7Data_valid.endo_hm, e7Data.hDiag_single]

theorem d0Hom_apply_single (c : Kˣ) (a : Idx0) :
    ((d0Hom K c : ↥(EAut0 K)) : W K ≃ₗ[K] W K) (Finsupp.single a 1) =
      ((c ^ e7Data.wt (a : Fin e7Data.d) nodeQ2 : Kˣ) : K) • Finsupp.single a 1 := by
  apply emb_injective
  have hind := resV0_induces (K := K) (d0Lam K c) (Finsupp.single a 1)
  change emb K ((resV0 K (d0Lam K c) : Module.End K (W K)) (Finsupp.single a 1)) =
    emb K (((c ^ e7Data.wt (a : Fin e7Data.d) nodeQ2 : Kˣ) : K) • Finsupp.single a 1)
  change emb K ((resV0 K (d0Lam K c) : Module.End K (W K)) (Finsupp.single a 1)) = _ at hind ⊢
  rw [hind, map_smul, emb_single]
  exact hm_single nodeQ2 c a

theorem eAut0Congr_d0Hom (e : K ≃+* K') (c : Kˣ) :
    eAut0Congr e (d0Hom K c) = d0Hom K' (Units.map e.toMonoidHom c) := by
  apply Subtype.ext
  rw [coe_eAut0Congr]
  apply LinearEquiv.toLinearMap_injective
  refine (Finsupp.basisSingleOne : Module.Basis Idx0 K' (W K')).ext fun a => ?_
  rw [Finsupp.coe_basisSingleOne]
  have h1 : (wMap e).symm (Finsupp.single a (1 : K')) = Finsupp.single a 1 := by
    rw [wMap_symm_eq, wMap_single, map_one]
  change conjAut e (d0Hom K c : W K ≃ₗ[K] W K) (Finsupp.single a 1) =
    ((d0Hom K' (Units.map e.toMonoidHom c) : ↥(EAut0 K')) : W K' ≃ₗ[K'] W K') (Finsupp.single a 1)
  rw [conjAut_apply, h1, d0Hom_apply_single, d0Hom_apply_single, wMap_smul, wMap_single, map_one]
  congr 1
  simp [Units.val_zpow_eq_zpow_val, map_zpow₀]

end Root

end CFSG.RankThree.GF2n.Smith81.D6Spin
