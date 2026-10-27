module

public import CFSG.LocalAnalysis.UniquenessCase.K340.VocabCenter
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.Campbell340

open CFSG.QuasithinUnique.Setup.Campbell

variable {G : Type} [Group G] [Finite G]

private theorem map_thompsonJ_sylow' {H T : Subgroup G} (P : Sylow 2 ↥H)
    (hP : (P : Subgroup ↥H).map H.subtype = T) :
    (thompsonJ (P : Subgroup ↥H)).map H.subtype = thompsonJ T := by
  rw [thompsonJ_eq_quasithin, map_thompsonJ_sylow P hP]

noncomputable def jEquiv {H T : Subgroup G} (P : Sylow 2 ↥H)
    (hP : (P : Subgroup ↥H).map H.subtype = T) :
    ↥(CFSG.Quasithin.thompsonJ (P : Subgroup ↥H)) ≃* ↥(thompsonJ T) :=
  (MulEquiv.subgroupCongr (thompsonJ_eq_quasithin (P : Subgroup ↥H)).symm).trans <|
    (Subgroup.equivMapOfInjective (thompsonJ (P : Subgroup ↥H)) H.subtype
      H.subtype_injective).trans <|
      MulEquiv.subgroupCongr (map_thompsonJ_sylow' P hP)

private theorem jEquiv_coe {H T : Subgroup G} (P : Sylow 2 ↥H)
    (hP : (P : Subgroup ↥H).map H.subtype = T)
    (y : ↥(CFSG.Quasithin.thompsonJ (P : Subgroup ↥H))) :
    (jEquiv P hP y : G) = H.subtype (y : ↥H) :=
  rfl

private theorem subtype_comp_jEquiv {H T : Subgroup G} (P : Sylow 2 ↥H)
    (hP : (P : Subgroup ↥H).map H.subtype = T) :
    H.subtype.comp (CFSG.Quasithin.thompsonJ (P : Subgroup ↥H)).subtype =
      (thompsonJ T).subtype.comp (jEquiv P hP).toMonoidHom := by
  ext y
  exact (jEquiv_coe P hP y).symm

private theorem normalizerMonoidHom_coe {T : Subgroup G}
    (n : ↥(Subgroup.normalizer (T : Set G))) (z : T) :
    (((T.normalizerMonoidHom n) z : T) : G) = (n : G) * (z : G) * (n : G)⁻¹ :=
  rfl

private theorem normalizerMonoidHom_subtype {T : Subgroup G}
    (n : ↥(Subgroup.normalizer (T : Set G))) :
    T.subtype.comp (T.normalizerMonoidHom n).toMonoidHom =
      (MulAut.conj (n : G)).toMonoidHom.comp T.subtype := by
  ext z
  change (((T.normalizerMonoidHom n) z : T) : G) = (MulAut.conj (n : G)) ((z : T) : G)
  rw [normalizerMonoidHom_coe n z, MulAut.conj_apply]

private theorem jEquiv_comp_congr_normalizerMonoidHom {H T : Subgroup G} (P : Sylow 2 ↥H)
    (hP : (P : Subgroup ↥H).map H.subtype = T)
    (n : ↥(Subgroup.normalizer (thompsonJ T : Set G))) :
    (jEquiv P hP).toMonoidHom.comp
        (MulAut.congr (jEquiv P hP).symm ((thompsonJ T).normalizerMonoidHom n)).toMonoidHom =
      ((thompsonJ T).normalizerMonoidHom n).toMonoidHom.comp
        (jEquiv P hP).toMonoidHom := by
  ext y
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.congr_apply,
    MulEquiv.trans_apply, MulEquiv.symm_symm, MulEquiv.apply_symm_apply]

private theorem map_subgroupOf_thompsonJ {H T : Subgroup G} (P : Sylow 2 ↥H)
    (hP : (P : Subgroup ↥H).map H.subtype = T) (Y : Subgroup ↥H) :
    (Y.subgroupOf (CFSG.Quasithin.thompsonJ (P : Subgroup ↥H))).map
        (H.subtype.comp (CFSG.Quasithin.thompsonJ (P : Subgroup ↥H)).subtype) =
      Y.map H.subtype ⊓ thompsonJ T := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨Subgroup.mem_map.mpr ⟨(y : ↥H), hy, rfl⟩, ?_⟩
    rw [← map_thompsonJ_sylow P hP]
    exact Subgroup.mem_map.mpr ⟨y, y.2, rfl⟩
  · rintro ⟨hz, hzJ⟩
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
    rw [← map_thompsonJ_sylow P hP] at hzJ
    obtain ⟨u, huS, hu⟩ := Subgroup.mem_map.mp hzJ
    have hwS : w ∈ CFSG.Quasithin.thompsonJ (P : Subgroup ↥H) := by
      have h : u = w := H.subtype_injective hu
      rw [← h]
      exact huS
    exact Subgroup.mem_map.mpr ⟨⟨w, hwS⟩, hw, rfl⟩

theorem map_aimg_lam {H T : Subgroup G} (P : Sylow 2 ↥H)
    (hP : (P : Subgroup ↥H).map H.subtype = T) {x : G}
    (hx : x ∈ Subgroup.normalizer (thompsonJ T : Set G)) (Y : Subgroup ↥H) :
    (aimg (CFSG.Quasithin.thompsonJ (P : Subgroup ↥H))
        (MulAut.congr (jEquiv P hP).symm
          ((thompsonJ T).normalizerMonoidHom ⟨x, hx⟩)) Y).map H.subtype =
      (Y.map H.subtype ⊓ thompsonJ T).map (MulAut.conj x).toMonoidHom := by
  rw [aimg, Subgroup.map_map, subtype_comp_jEquiv P hP, Subgroup.map_map, MonoidHom.comp_assoc,
    jEquiv_comp_congr_normalizerMonoidHom P hP ⟨x, hx⟩, ← MonoidHom.comp_assoc,
    normalizerMonoidHom_subtype ⟨x, hx⟩, MonoidHom.comp_assoc, ← subtype_comp_jEquiv P hP,
    ← Subgroup.map_map, map_subgroupOf_thompsonJ P hP Y]

@[expose] noncomputable def lam {H T : Subgroup G} (P : Sylow 2 ↥H)
    (hP : (P : Subgroup ↥H).map H.subtype = T) (X : Subgroup G) :
    Subgroup (MulAut ↥(CFSG.Quasithin.thompsonJ (P : Subgroup ↥H))) :=
  (X.subgroupOf (Subgroup.normalizer (thompsonJ T : Set G))).map
    ((MulAut.congr (jEquiv P hP).symm).toMonoidHom.comp (thompsonJ T).normalizerMonoidHom)

private theorem lam_inner {H T X : Subgroup G} (P : Sylow 2 ↥H)
    (hP : (P : Subgroup ↥H).map H.subtype = T) (hXJ : thompsonJ H ⊓ T ≤ X) :
    ∀ x ∈ (P : Subgroup ↥H) ⊓ Hone P, ∃ β ∈ lam P hP X,
      ∀ y : ↥(CFSG.Quasithin.thompsonJ (P : Subgroup ↥H)),
        ((β y : ↥(CFSG.Quasithin.thompsonJ (P : Subgroup ↥H))) : ↥H) = x⁻¹ * y * x := by
  rintro x ⟨hxP, hxH⟩
  have hxT : H.subtype x ∈ T := by
    rw [← hP]
    exact Subgroup.mem_map.mpr ⟨x, hxP, rfl⟩
  have hxJ : H.subtype x ∈ thompsonJ H := by
    rw [← map_Hone P hP]
    exact Subgroup.mem_map.mpr ⟨x, hxH, rfl⟩
  have hxX : H.subtype x ∈ X := hXJ ⟨hxJ, hxT⟩
  have hxN : H.subtype x ∈ Subgroup.normalizer (thompsonJ T : Set G) := by
    rw [thompsonJ_eq_quasithin T]
    exact CFSG.Quasithin.B6.le_normalizer_thompsonJ T hxT
  let n : ↥(Subgroup.normalizer (thompsonJ T : Set G)) :=
    ⟨(H.subtype x)⁻¹, Subgroup.inv_mem _ hxN⟩
  have hnX : n ∈ X.subgroupOf (Subgroup.normalizer (thompsonJ T : Set G)) := by
    show ((H.subtype x)⁻¹) ∈ X
    exact X.inv_mem hxX
  refine ⟨MulAut.congr (jEquiv P hP).symm ((thompsonJ T).normalizerMonoidHom n),
    Subgroup.mem_map.mpr ⟨n, hnX, rfl⟩, ?_⟩
  intro y
  apply H.subtype_injective
  calc
    H.subtype (MulAut.congr (jEquiv P hP).symm
        ((thompsonJ T).normalizerMonoidHom n) y)
        = (jEquiv P hP (MulAut.congr (jEquiv P hP).symm
            ((thompsonJ T).normalizerMonoidHom n) y) : G) :=
          (jEquiv_coe P hP _).symm
    _ = ((thompsonJ T).normalizerMonoidHom n (jEquiv P hP y) : G) :=
          congrArg Subtype.val (DFunLike.congr_fun
            (jEquiv_comp_congr_normalizerMonoidHom P hP n) y)
    _ = (H.subtype x)⁻¹ * (jEquiv P hP y : G) * (H.subtype x) := by
          rw [normalizerMonoidHom_coe n (jEquiv P hP y)]
          simp only [n, inv_inv]
    _ = H.subtype (x⁻¹ * y * x) := by
          rw [jEquiv_coe P hP y, map_mul, map_mul, map_inv]

private theorem lam_vmod {H L T V X : Subgroup G} {k : Type} [Field k] [Finite k]
    {ρ : ↥H →* Matrix.SpecialLinearGroup (Fin 2) k}
    {ψ : CFSG.QuasithinUnique.Setup.Campbell.Ecore ↥H →* Multiplicative (Fin 2 → k)}
    (P : Sylow 2 ↥H) (hP : (P : Subgroup ↥H).map H.subtype = T)
    (h : CFSG.QuasithinUnique.Setup.Campbell.IsSeed P ρ
      (CFSG.QuasithinUnique.Setup.Campbell.Ecore ↥H) ψ)
    (hVdef : V = ⁅L, CFSG.RankThree.PartOne.omegaOneCenterIn (CFSG.Open.pCoreOf 2 H)⁆)
    (hLdef : L = CFSG.Quasithin.opResidual 2 H)
    (hcomm : ∀ a ∈ X, ⁅V, V.map (MulAut.conj a).toMonoidHom⁆ = ⊥) :
    ∀ β ∈ lam P hP X, aimg (CFSG.Quasithin.thompsonJ (P : Subgroup ↥H)) β (Vmod ↥H) ≤
      CFSG.pCore 2 ↥H := by
  intro β hβ
  obtain ⟨n, hnX, rfl⟩ := Subgroup.mem_map.mp hβ
  have hnX' : (n : G) ∈ X := hnX
  have hmapV : (Vmod ↥H).map H.subtype = V := by
    rw [map_Vmod, ← hLdef, ← hVdef]
  have hW : (aimg (CFSG.Quasithin.thompsonJ (P : Subgroup ↥H))
      ((MulAut.congr (jEquiv P hP).symm).toMonoidHom
        ((thompsonJ T).normalizerMonoidHom n)) (Vmod ↥H)).map H.subtype =
      ((Vmod ↥H).map H.subtype ⊓ thompsonJ T).map (MulAut.conj (n : G)).toMonoidHom :=
    map_aimg_lam P hP n.2 (Vmod ↥H)
  have hcommW : ⁅(Vmod ↥H).map H.subtype,
      ((Vmod ↥H).map H.subtype ⊓ thompsonJ T).map
        (MulAut.conj (n : G)).toMonoidHom⁆ = ⊥ := by
    have hle : ⁅(Vmod ↥H).map H.subtype,
        ((Vmod ↥H).map H.subtype ⊓ thompsonJ T).map
          (MulAut.conj (n : G)).toMonoidHom⁆ ≤
        ⁅V, V.map (MulAut.conj (n : G)).toMonoidHom⁆ := by
      rw [hmapV]
      exact Subgroup.commutator_mono le_rfl (Subgroup.map_mono inf_le_left)
    exact le_bot_iff.mp (hle.trans (le_of_eq (hcomm (n : G) hnX')))
  have hbot : ⁅Vmod ↥H, aimg (CFSG.Quasithin.thompsonJ (P : Subgroup ↥H))
      ((MulAut.congr (jEquiv P hP).symm).toMonoidHom
        ((thompsonJ T).normalizerMonoidHom n)) (Vmod ↥H)⁆ = ⊥ := by
    rw [← Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective, Subgroup.map_commutator,
      hW]
    exact hcommW
  have hWle : aimg (CFSG.Quasithin.thompsonJ (P : Subgroup ↥H))
      ((MulAut.congr (jEquiv P hP).symm).toMonoidHom
        ((thompsonJ T).normalizerMonoidHom n)) (Vmod ↥H) ≤
      (P : Subgroup ↥H) ⊓ Subgroup.centralizer (Vmod ↥H : Set ↥H) := by
    intro w hw
    refine ⟨CFSG.Quasithin.B6.thompsonJ_le _ (aimg_le hw), ?_⟩
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at hbot
    exact hbot hw
  rwa [h.toIsNatBase.sylow_inf_centralizer_Vmod] at hWle

theorem lamHyp_of {H L T V X : Subgroup G} {k : Type} [Field k] [Finite k]
    {ρ : ↥H →* Matrix.SpecialLinearGroup (Fin 2) k}
    {ψ : CFSG.QuasithinUnique.Setup.Campbell.Ecore ↥H →* Multiplicative (Fin 2 → k)}
    (P : Sylow 2 ↥H) (hP : (P : Subgroup ↥H).map H.subtype = T)
    (h : CFSG.QuasithinUnique.Setup.Campbell.IsSeed P ρ
      (CFSG.QuasithinUnique.Setup.Campbell.Ecore ↥H) ψ)
    (hVdef : V = ⁅L, CFSG.RankThree.PartOne.omegaOneCenterIn (CFSG.Open.pCoreOf 2 H)⁆)
    (hLdef : L = CFSG.Quasithin.opResidual 2 H)
    (hXN : X ≤ Subgroup.normalizer (thompsonJ T : Set G)) (hXJ : thompsonJ H ⊓ T ≤ X)
    (hcomm : ∀ a ∈ X, ⁅V, V.map (MulAut.conj a).toMonoidHom⁆ = ⊥) :
    CFSG.QuasithinUnique.Setup.CampbellJ.LamHyp P (lam P hP X) :=
  ⟨lam_inner P hP hXJ, lam_vmod P hP h hVdef hLdef hcomm⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.Campbell340

end
