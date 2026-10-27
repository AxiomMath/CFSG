module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelFrame

public section

namespace CFSG.StandardType.E6ThreeModel

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc.E6Three

@[expose] def FrameData.map {R R' : Type} [Group R] [Group R'] (D : FrameData R) (e : R ≃* R') :
    FrameData R' where
  H := D.H.map (MulAut.congr e).toMonoidHom
  diag := (MulAut.congr e).toMonoidHom.comp D.diag
  Tor := D.Tor.map e.toMonoidHom
  nb i := e (D.nb i)

theorem FrameData.mem_map_tor {R R' : Type} [Group R] [Group R'] (D : FrameData R)
    (e : R ≃* R') (r : R') : r ∈ (D.map e).Tor ↔ e.symm r ∈ D.Tor := by
  exact Subgroup.mem_map_equiv

private theorem frameMap_congr_conj {R R' : Type} [Group R] [Group R'] (e : R ≃* R')
    (r : R) : MulAut.congr e (MulAut.conj r) = MulAut.conj (e r) := by
  ext x
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulAut.conj_apply, map_mul, map_inv,
    MulEquiv.apply_symm_apply]

private theorem frameMap_congr_symm_congr {R R' : Type} [Group R] [Group R']
    (e : R ≃* R') (z : MulAut R) :
    (MulAut.congr e).symm (MulAut.congr e z) = z := by
  ext x
  simp only [MulAut.congr_symm_apply, MulAut.congr_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply]

private theorem frameMap_ad {R R' : Type} [Group R] [Group R'] (D : FrameData R)
    (e : R ≃* R') (x : Fin Tag.E6.rank → ZMod 3) :
    (D.map e).ad x = MulAut.congr e (D.ad x) := rfl

private theorem frameMap_nb {R R' : Type} [Group R] [Group R'] (D : FrameData R)
    (e : R ≃* R') (i : Fin 6) : (D.map e).nb i = e (D.nb i) := rfl

private theorem frameMap_symm_comp_apply {L R R' : Type} [Group L] [Group R] [Group R']
    (e : R ≃* R') (ψ : L →* R') (n : L) :
    (e.symm.toMonoidHom.comp ψ) n = e.symm (ψ n) := rfl

private theorem frameMap_congr_ad {R R' : Type} [Group R] [Group R'] (D : FrameData R)
    (e : R ≃* R') (x : Fin Tag.E6.rank → ZMod 3) :
    MulAut.congr e (D.ad x) = (D.map e).ad x := (frameMap_ad D e x).symm

private theorem frameMap_ad_apply {R R' : Type} [Group R] [Group R'] (D : FrameData R)
    (e : R ≃* R') (x : Fin Tag.E6.rank → ZMod 3) (r : R) :
    (D.map e).ad x (e r) = e (D.ad x r) := by
  simp only [frameMap_ad, MulAut.congr_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply]

private theorem frameMap_ad_apply_symm {R R' : Type} [Group R] [Group R'] (D : FrameData R)
    (e : R ≃* R') (x : Fin Tag.E6.rank → ZMod 3) (r : R') :
    (D.map e).ad x r = e (D.ad x (e.symm r)) := by
  calc
    (D.map e).ad x r = (D.map e).ad x (e (e.symm r)) := by
      rw [MulEquiv.apply_symm_apply]
    _ = e (D.ad x (e.symm r)) := frameMap_ad_apply D e x (e.symm r)

private theorem frameMap_ad_eq_iff {R R' : Type} [Group R] [Group R'] (D : FrameData R)
    (e : R ≃* R') (x : Fin Tag.E6.rank → ZMod 3) (r : R') :
    (D.map e).ad x r = r ↔ D.ad x (e.symm r) = e.symm r := by
  rw [frameMap_ad_apply_symm]
  constructor
  · intro h
    exact e.injective (by rw [h, MulEquiv.apply_symm_apply])
  · intro h
    rw [h, MulEquiv.apply_symm_apply]

private theorem frameMap_V0 {R R' : Type} [Group R] [Group R'] (D : FrameData R)
    (e : R ≃* R') : (D.map e).V0 = D.V0.map e.toMonoidHom := by
  ext r'
  rw [Subgroup.mem_map_equiv]
  constructor
  · rintro ⟨hr', v, hv, hconj⟩
    refine ⟨(FrameData.mem_map_tor D e r').mp hr', v, hv, ?_⟩
    apply (MulAut.congr e).injective
    rw [frameMap_congr_conj, MulEquiv.apply_symm_apply, hconj, frameMap_ad]
  · rintro ⟨hr, v, hv, hconj⟩
    refine ⟨(FrameData.mem_map_tor D e r').mpr hr, v, hv, ?_⟩
    rw [frameMap_ad, ← hconj, frameMap_congr_conj, MulEquiv.apply_symm_apply]

private theorem frameMap_center {R R' : Type} [Group R] [Group R'] {D : FrameData R}
    (hD : D.Good) (e : R ≃* R') : Subgroup.center R' = ⊥ := by
  rw [← Subgroup.map_center_eq e, hD.center, Subgroup.map_bot]

private theorem frameMap_faithful {R R' : Type} [Group R] [Group R'] {D : FrameData R}
    (hD : D.Good) (e : R ≃* R') : (D.map e).Faithful := by
  intro a b h
  exact hD.faithful ((MulAut.congr e).injective h)

private theorem frameMap_shape {R R' : Type} [Group R] [Group R'] {D : FrameData R}
    (hD : D.Good) (e : R ≃* R') : (D.map e).Shape := by
  intro X hX hXea hXcard
  let X' : Subgroup (MulAut R) := X.map (MulAut.congr e).symm.toMonoidHom
  have hX'H : X' ≤ D.H := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp hx
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp (hX hy)
    rw [← hxy, ← hzy]
    change (MulAut.congr e).symm ((MulAut.congr e) z) ∈ D.H
    rwa [frameMap_congr_symm_congr]
  have hX'ea : CFSG.Open.IsElemAbelian 3 X' := by
    refine ⟨?_, ?_⟩
    · exact @Subgroup.map_isMulCommutative (MulAut R') (MulAut R) _ _ X
        (MulAut.congr e).symm.toMonoidHom hXea.1
    · intro x hx
      obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp hx
      rw [← hxy, ← map_pow, hXea.2 y hy, map_one]
  have hX'card : Nat.card X' = Nat.card X :=
    Subgroup.card_map_of_injective (K := X)
      (f := (MulAut.congr e).symm.toMonoidHom) (MulAut.congr e).symm.injective
  have hcard : 3 ^ 5 ≤ Nat.card X' := by
    rw [hX'card]
    exact hXcard
  obtain ⟨γ', hγ'H, hγ'⟩ := hD.shape X' hX'H hX'ea hcard
  refine ⟨MulAut.congr e γ', Subgroup.mem_map_of_mem _ hγ'H, ?_⟩
  intro x hx
  have hx' : (MulAut.congr e).symm x ∈ X' :=
    Subgroup.mem_map_of_mem (MulAut.congr e).symm.toMonoidHom hx
  have hconj : MulAut.congr e (γ' * (MulAut.congr e).symm x * γ'⁻¹) =
      MulAut.congr e γ' * x * (MulAut.congr e γ')⁻¹ := by
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  have hmem := hγ' ((MulAut.congr e).symm x) hx'
  have hrange : (D.map e).diag.range =
      D.diag.range.map (MulAut.congr e).toMonoidHom :=
    MonoidHom.range_comp (MulAut.congr e).toMonoidHom D.diag
  rw [← hconj, hrange]
  exact Subgroup.mem_map_of_mem _ hmem

private theorem frameMap_torus {R R' : Type} [Group R] [Group R'] {D : FrameData R}
    (hD : D.Good) (e : R ≃* R') : (D.map e).TorusOK := by
  refine ⟨?_, ?_, ?_⟩
  · intro s hs t ht
    have hs' := (FrameData.mem_map_tor D e s).mp hs
    have ht' := (FrameData.mem_map_tor D e t).mp ht
    calc
      s * t = e (e.symm s) * e (e.symm t) := by
        rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
      _ = e (e.symm s * e.symm t) := (map_mul e _ _).symm
      _ = e (e.symm t * e.symm s) := by rw [hD.torus.1 (e.symm s) hs' (e.symm t) ht']
      _ = e (e.symm t) * e (e.symm s) := map_mul e _ _
      _ = t * s := by rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  · intro t ht
    rw [← MulEquiv.apply_symm_apply e t, MulEquiv.orderOf_eq e (e.symm t)]
    exact hD.torus.2.1 (e.symm t) ((FrameData.mem_map_tor D e t).mp ht)
  · intro x t ht
    rw [← MulEquiv.apply_symm_apply e t, frameMap_ad_apply,
      hD.torus.2.2 x (e.symm t) ((FrameData.mem_map_tor D e t).mp ht)]

private theorem frameMap_cent {R R' : Type} [Group R] [Group R'] {D : FrameData R}
    (hD : D.Good) (e : R ≃* R') : (D.map e).Cent := by
  intro r'
  rw [FrameData.mem_map_tor D e r']
  constructor
  · intro h
    exact (hD.cent (e.symm r')).mp fun v hv => (frameMap_ad_eq_iff D e v r').mp (h v hv)
  · intro h v hv
    exact (frameMap_ad_eq_iff D e v r').mpr ((hD.cent (e.symm r')).mpr h v hv)

private theorem frameMap_inner {R R' : Type} [Group R] [Group R'] {D : FrameData R}
    (hD : D.Good) (e : R ≃* R') : (D.map e).InnerPts := by
  intro v hv
  obtain ⟨r, hr, hr3, hconj⟩ := hD.inner v hv
  refine ⟨e r, (FrameData.mem_map_tor D e (e r)).mpr ?_, ?_, ?_⟩
  · rw [MulEquiv.symm_apply_apply]
    exact hr
  · rw [← map_pow, hr3, map_one]
  · rw [frameMap_ad, ← hconj, frameMap_congr_conj]

private theorem frameMap_weyl {R R' : Type} [Group R] [Group R'] {D : FrameData R}
    (hD : D.Good) (e : R ≃* R') : (D.map e).WeylOK := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    show e (D.nb i) * e (D.nb i) = 1
    rw [← map_mul, hD.weyl.1 i, map_one]
  · intro i t ht
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp ht
    change e (D.nb i) * e r * (e (D.nb i))⁻¹ ∈ D.Tor.map e.toMonoidHom
    simp only [← map_mul, ← map_inv]
    exact Subgroup.mem_map_of_mem e.toMonoidHom (hD.weyl.2.1 i r hr)
  · intro i x
    have h := congrArg (MulAut.congr e) (hD.weyl.2.2.1 i x)
    simpa only [frameMap_nb, map_mul, map_inv, frameMap_congr_conj,
      frameMap_congr_ad] using h
  · intro i x
    rw [frameMap_V0, frameMap_nb, frameMap_ad_apply]
    refine Subgroup.mem_map.mpr ⟨D.nb i * (D.ad x (D.nb i))⁻¹, hD.weyl.2.2.2 i x, ?_⟩
    rw [map_mul, map_inv]
    rfl

private theorem frameMap_noInvFunc {L R R' : Type} [Group L] [Group R] [Group R']
    (e : R ≃* R') (ψ : L →* R') (N : Set L) (V : Subgroup R)
    (h : GGNoInvFunc (e.symm.toMonoidHom.comp ψ) N V) :
    GGNoInvFunc ψ N (V.map e.toMonoidHom) := by
  intro f hf
  let φ : V ≃* V.map e.toMonoidHom := V.equivMapOfInjective e.toMonoidHom e.injective
  have hφcoe : ∀ x : V, (φ x : R') = e x := fun x =>
    Subgroup.coe_equivMapOfInjective_apply V e.toMonoidHom e.injective x
  let f' : V →* Multiplicative (ZMod 3) := f.comp φ.toMonoidHom
  have hf' : ∀ n ∈ N, ∀ v v' : V,
      (v' : R) = (e.symm.toMonoidHom.comp ψ) n * v * ((e.symm.toMonoidHom.comp ψ) n)⁻¹ →
      f' v' = f' v := by
    intro n hn v v' hv
    have hv' : (φ v' : R') = ψ n * (φ v) * (ψ n)⁻¹ := by
      rw [hφcoe, hφcoe, hv, frameMap_symm_comp_apply, map_mul, map_mul, map_inv,
        MulEquiv.apply_symm_apply]
    exact hf n hn (φ v) (φ v') hv'
  have hf1 : f' = 1 := h f' hf'
  ext x
  obtain ⟨v, rfl⟩ := φ.surjective x
  change f (φ v) = 1
  simpa only [f', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MonoidHom.one_apply] using
    DFunLike.congr_fun hf1 v

private theorem frameMap_noInvAlt {L R R' : Type} [Group L] [Group R] [Group R']
    (e : R ≃* R') (ψ : L →* R') (N : Set L) (V : Subgroup R)
    (h : GGNoInvAlt (e.symm.toMonoidHom.comp ψ) N V) :
    GGNoInvAlt ψ N (V.map e.toMonoidHom) := by
  intro κ hκmul hκmul' hκalt hκinv
  let φ : V ≃* V.map e.toMonoidHom := V.equivMapOfInjective e.toMonoidHom e.injective
  have hφcoe : ∀ x : V, (φ x : R') = e x := fun x =>
    Subgroup.coe_equivMapOfInjective_apply V e.toMonoidHom e.injective x
  let κ' : V → V → Multiplicative (ZMod 3) := fun x y => κ (φ x) (φ y)
  have hκ' : ∀ n ∈ N, ∀ x y x' y' : V,
      (x' : R) = (e.symm.toMonoidHom.comp ψ) n * x * ((e.symm.toMonoidHom.comp ψ) n)⁻¹ →
      (y' : R) = (e.symm.toMonoidHom.comp ψ) n * y * ((e.symm.toMonoidHom.comp ψ) n)⁻¹ →
      κ' x' y' = κ' x y := by
    intro n hn x y x' y' hx' hy'
    refine hκinv n hn (φ x) (φ y) (φ x') (φ y') ?_ ?_
    · rw [hφcoe, hφcoe, hx', frameMap_symm_comp_apply, map_mul, map_mul, map_inv,
        MulEquiv.apply_symm_apply]
    · rw [hφcoe, hφcoe, hy', frameMap_symm_comp_apply, map_mul, map_mul, map_inv,
        MulEquiv.apply_symm_apply]
  have htriv : ∀ x y : V, κ' x y = 1 := by
    refine h κ' ?_ ?_ ?_ hκ'
    · intro x y z
      show κ (φ (x * y)) (φ z) = κ (φ x) (φ z) * κ (φ y) (φ z)
      rw [map_mul]
      exact hκmul (φ x) (φ y) (φ z)
    · intro x y z
      show κ (φ x) (φ (y * z)) = κ (φ x) (φ y) * κ (φ x) (φ z)
      rw [map_mul]
      exact hκmul' (φ x) (φ y) (φ z)
    · intro x
      exact hκalt (φ x)
  intro x y
  obtain ⟨x0, rfl⟩ := φ.surjective x
  obtain ⟨y0, rfl⟩ := φ.surjective y
  exact htriv x0 y0

private theorem frameMap_modules {R R' : Type} [Group R] [Group R'] {D : FrameData R}
    (hD : D.Good) (e : R ≃* R') : (D.map e).ModuleOK := by
  intro L _ ψ N hlift
  let ψ' : L →* R := e.symm.toMonoidHom.comp ψ
  have hlift' : ∀ i, ∃ n ∈ N, ψ' n = D.nb i := by
    intro i
    obtain ⟨n, hn, hψn⟩ := hlift i
    refine ⟨n, hn, ?_⟩
    show e.symm (ψ n) = D.nb i
    rw [hψn, frameMap_nb, MulEquiv.symm_apply_apply]
  obtain ⟨h1, h2, h3⟩ := hD.modules (L := L) ψ' N hlift'
  refine ⟨?_, ?_, ?_⟩
  · exact frameMap_noInvFunc e ψ N D.Tor h1
  · exact frameMap_noInvAlt e ψ N D.Tor h2
  · rw [frameMap_V0]
    exact frameMap_noInvFunc e ψ N D.V0 h3

private theorem frameMap_norm {R R' : Type} [Group R] [Group R'] {D : FrameData R}
    (hD : D.Good) (e : R ≃* R') : (D.map e).NormOK := by
  intro r' S hS h
  have h' : ∀ x ∈ S, ∃ y ∈ S,
      MulAut.conj (e.symm r') * D.ad x * (MulAut.conj (e.symm r'))⁻¹ = D.ad y := by
    intro x hx
    obtain ⟨y, hy, hyh⟩ := h x hx
    refine ⟨y, hy, ?_⟩
    apply (MulAut.congr e).injective
    simpa only [map_mul, map_inv, frameMap_congr_conj, MulEquiv.apply_symm_apply,
      frameMap_congr_ad] using hyh
  obtain ⟨u, hu⟩ := hD.norm (e.symm r') S hS h'
  refine ⟨u, fun x hx => ?_⟩
  have hx' := congrArg (MulAut.congr e) (hu x hx)
  simpa only [map_mul, map_inv, frameMap_congr_conj, MulEquiv.apply_symm_apply,
    frameMap_congr_ad] using hx'

private theorem frameMap_aut {R R' : Type} [Group R] [Group R'] {D : FrameData R}
    (hD : D.Good) (e : R ≃* R') : (D.map e).AutOK := by
  intro α' S hS h
  have h' : ∀ x ∈ S, ∃ y ∈ S,
      (MulAut.congr e).symm α' * D.ad x * ((MulAut.congr e).symm α')⁻¹ = D.ad y := by
    intro x hx
    obtain ⟨y, hy, hyh⟩ := h x hx
    refine ⟨y, hy, ?_⟩
    apply (MulAut.congr e).injective
    simpa only [map_mul, map_inv, MulEquiv.apply_symm_apply, frameMap_congr_ad] using hyh
  obtain ⟨c, u, hc, hu⟩ := hD.aut ((MulAut.congr e).symm α') S hS h'
  refine ⟨c, u, hc, fun x hx => ?_⟩
  have hx' := congrArg (MulAut.congr e) (hu x hx)
  simpa only [map_mul, map_inv, MulEquiv.apply_symm_apply, frameMap_congr_ad] using hx'

theorem FrameData.Good.map {R R' : Type} [Group R] [Group R'] {D : FrameData R} (hD : D.Good)
    (e : R ≃* R') : (D.map e).Good where
  center := frameMap_center hD e
  faithful := frameMap_faithful hD e
  shape := frameMap_shape hD e
  torus := frameMap_torus hD e
  cent := frameMap_cent hD e
  inner := frameMap_inner hD e
  weyl := frameMap_weyl hD e
  modules := frameMap_modules hD e
  norm := frameMap_norm hD e
  aut := frameMap_aut hD e

end CFSG.StandardType.E6ThreeModel
