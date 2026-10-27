module

public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestDefs
public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestBasic
public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestCenter
public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestClosure
public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestInvariant
public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestPCore
public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestAut
public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestCentD
public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestA3
public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestA4
public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestNC1
public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestNC2
public import CFSG.Assembly.Subnormal

public section

namespace CFSG.StandardType.GGSixE6Two

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open CFSG.SeitzReduction
  CFSG.StandardType.GGHalf CFSG.Timmesfeld.LieEmbed CFSG.LieType.Steinberg.Adjoint

private lemma e6as_conj_inv_comp_conj (c : EC) :
    (MulAut.conj c⁻¹).toMonoidHom.comp (MulAut.conj c).toMonoidHom = MonoidHom.id EC := by
  apply MonoidHom.ext
  intro x
  show (MulAut.conj c⁻¹) ((MulAut.conj c) x) = x
  rw [MulAut.conj_apply, MulAut.conj_apply]
  group

private lemma e6as_map_centralizer_mulAut (σ : MulAut EC) (a : EC) :
    (Subgroup.centralizer ({a} : Set EC)).map σ.toMonoidHom =
      Subgroup.centralizer ({σ a} : Set EC) := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    show σ x * σ a = σ a * σ x
    rw [← map_mul, ← map_mul, hx]
  · intro hy
    refine ⟨σ.symm y, ?_, σ.apply_symm_apply y⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    apply σ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hy]

private lemma e6as_isComponentOf_map_mulAut (σ : MulAut EC) {L K : Subgroup EC}
    (h : CFSG.Assembly.IsComponentOf L K) :
    CFSG.Assembly.IsComponentOf (L.map σ.toMonoidHom) (K.map σ.toMonoidHom) := by
  obtain ⟨hLK, hsub, hq⟩ := h
  refine ⟨Subgroup.map_mono hLK, ?_, ?_⟩
  · exact CFSG.Assembly.isSubnormal_iff_open.mpr
      ((CFSG.Assembly.isSubnormal_iff_open.mp hsub).map σ.toMonoidHom)
  · exact CFSG.Assembly.IsQuasisimple.of_mulEquiv
      (L.equivMapOfInjective σ.toMonoidHom σ.injective).symm hq

private lemma e6as_centralizer_inv (a : EC) :
    Subgroup.centralizer ({a⁻¹} : Set EC) = Subgroup.centralizer ({a} : Set EC) := by
  ext x
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  exact Commute.inv_right_iff

private lemma e6as_zpowers_eq_of_mem_zpowers {a b : EC}
    (ha : orderOf a = 3)
    (hb : b ∈ Subgroup.zpowers a) (hne : b ≠ 1) :
    Subgroup.zpowers b = Subgroup.zpowers a := by
  have hbdvd : orderOf b ∣ orderOf a := orderOf_dvd_of_mem_zpowers hb
  rw [ha] at hbdvd
  have hb3 : orderOf b = 3 := by
    rcases Nat.Prime.eq_one_or_self_of_dvd (by norm_num : Nat.Prime 3) (orderOf b) hbdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hne
    · exact h
  haveI : Finite ↥(Subgroup.zpowers a) :=
    (isOfFinOrder_iff_pow_eq_one.mpr
      ⟨3, by norm_num, by rw [← ha]; exact pow_orderOf_eq_one a⟩).finite_zpowers
  exact Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hb)
    (by rw [Nat.card_zpowers, Nat.card_zpowers, ha, hb3])

private lemma e6as_caseB
    (g : EC) {K' : Subgroup EC} (h : EC)
    (hK : CFSG.Assembly.IsComponentOf K' (Subgroup.centralizer ({g} : Set EC)))
    (hh : h ∈ Subgroup.normalizer (rE : Set EC))
    (hcent : Subgroup.centralizer ({g} : Set EC) =
      (Subgroup.centralizer ({zE} : Set EC)).map (MulAut.conj h).toMonoidHom) :
    GGRootNormNoCentral (rE.subgroupOf K') ∧
      (GGRootNormInner (rE.subgroupOf K') ∨
        ∃ δ : ↥(Subgroup.normalizer (K' : Set EC)),
          (δ : EC) ∈ Subgroup.centralizer {g} ∧
            (δ : EC) ∈ Subgroup.normalizer (rE : Set EC) ∧
            GGRootNormInnerDiag (rE.subgroupOf K') (K'.normalizerMonoidHom δ)) := by
  have hK'' : K'.map (MulAut.conj h⁻¹).toMonoidHom = lE := by
    apply eq_lE_of_isComponentOf
    have hcomp : CFSG.Assembly.IsComponentOf
        (K'.map (MulAut.conj h⁻¹).toMonoidHom)
        ((Subgroup.centralizer ({g} : Set EC)).map (MulAut.conj h⁻¹).toMonoidHom) :=
      e6as_isComponentOf_map_mulAut (MulAut.conj h⁻¹) hK
    rwa [hcent, Subgroup.map_map, e6as_conj_inv_comp_conj h, Subgroup.map_id] at hcomp
  have hid : (MulAut.conj h).toMonoidHom.comp (MulAut.conj h⁻¹).toMonoidHom =
      MonoidHom.id EC := by
    simpa using e6as_conj_inv_comp_conj h⁻¹
  have hK' : K' = lE.map (MulAut.conj h).toMonoidHom := by
    have hmap := congrArg (fun S : Subgroup EC => S.map (MulAut.conj h).toMonoidHom) hK''
    rw [Subgroup.map_map, hid, Subgroup.map_id] at hmap
    exact hmap
  have hres := ggRootNorm_rE_conj_lE h hh
  subst hK'
  exact ⟨hres.1, Or.inl hres.2⟩

theorem rE_item1 :
    pCoreOf 2 (Subgroup.normalizer (rE : Set EC)) ⊔ j0E = ⊤ := by
  rw [pCoreOf_normalizer_rE]
  exact qE_sup_j0E

theorem rE_item4 :
    ∀ Q' : Subgroup EC, Q' = pCoreOf 2 (Subgroup.normalizer (rE : Set EC)) →
      ∀ U : Subgroup EC, (Subgroup.center ↥Q').map Q'.subtype ≤ U → U ≤ Q' →
        U ≠ (Subgroup.center ↥Q').map Q'.subtype → U ≠ Q' →
        Subgroup.normalizer (rE : Set EC) ≤ Subgroup.normalizer (U : Set EC) → jE ⊔ U = ⊤ := by
  intro Q' hQ' U hU1 hU2 hU3 hU4 hN
  rw [pCoreOf_normalizer_rE] at hQ'
  subst hQ'
  rw [center_qE] at hU1 hU3
  rcases invariant_between_z0E_qE U hU1 hU2 hN with h | h | h | h
  · exact absurd h hU3
  · exact absurd h hU4
  · rw [h]; exact jE_sup_z0E_sup_uMu1
  · rw [h]; exact jE_sup_z0E_sup_uMu2

theorem rE_item2 :
    ∀ g : EC, g ^ 3 = 1 → g ≠ 1 → g ∈ Subgroup.centralizer {zE} →
      g ∈ Subgroup.centralizer (jE : Set EC) →
      ∀ K' : Subgroup EC, jE ≤ K' → CFSG.Assembly.IsComponentOf K' (Subgroup.centralizer {g}) →
        GGRootNormNoCentral (rE.subgroupOf K') ∧
          (GGRootNormInner (rE.subgroupOf K') ∨
            ∃ δ : ↥(Subgroup.normalizer (K' : Set EC)),
              (δ : EC) ∈ Subgroup.centralizer {g} ∧
                (δ : EC) ∈ Subgroup.normalizer (rE : Set EC) ∧
                GGRootNormInnerDiag (rE.subgroupOf K') (K'.normalizerMonoidHom δ)) := by
  intro g _hg3 hgne hgz hgj K' hJ hK
  have hgd : g ∈ dE := by
    rw [← centralizer_zE_inf_centralizer_jE]
    exact ⟨hgz, hgj⟩
  by_cases hw : g ∈ Subgroup.zpowers wOmegaE
  ·
    have hzw : Subgroup.zpowers g = Subgroup.zpowers wOmegaE :=
      e6as_zpowers_eq_of_mem_zpowers orderOf_wOmegaE hw hgne
    have hcent : Subgroup.centralizer ({g} : Set EC) =
        Subgroup.centralizer ({wOmegaE} : Set EC) := by
      have h1 : Subgroup.centralizer (Subgroup.zpowers g : Set EC) =
          Subgroup.centralizer ({g} : Set EC) := by
        rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      have h2 : Subgroup.centralizer (Subgroup.zpowers wOmegaE : Set EC) =
          Subgroup.centralizer ({wOmegaE} : Set EC) := by
        rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      rw [← h1, ← h2, hzw]
    have hK' : CFSG.Assembly.IsComponentOf K' (Subgroup.centralizer ({wOmegaE} : Set EC)) :=
      hcent ▸ hK
    have hKj : K' = jE := eq_jE_of_isComponentOf_centralizer_wE hJ hK'
    subst hKj
    exact ⟨ggRootNormNoCentral_rE_jE, Or.inl ggRootNormInner_rE_jE⟩
  ·
    obtain ⟨h, hhN, hz | hz⟩ := exists_conj_zE_of_mem_dE g hgd hw
    · have hhR : h ∈ Subgroup.normalizer (rE : Set EC) := hhN.2
      have hconj : MulAut.conj h zE = g := by
        rw [MulAut.conj_apply]; exact hz
      have hcent : Subgroup.centralizer ({g} : Set EC) =
          (Subgroup.centralizer ({zE} : Set EC)).map (MulAut.conj h).toMonoidHom := by
        rw [← hconj, e6as_map_centralizer_mulAut]
      exact e6as_caseB g h hK hhR hcent
    · have hhR : h ∈ Subgroup.normalizer (rE : Set EC) := hhN.2
      have hconj : MulAut.conj h zE = g⁻¹ := by
        rw [MulAut.conj_apply]; exact hz
      have hcent : Subgroup.centralizer ({g} : Set EC) =
          (Subgroup.centralizer ({zE} : Set EC)).map (MulAut.conj h).toMonoidHom := by
        rw [← e6as_centralizer_inv g, ← hconj, e6as_map_centralizer_mulAut]
      exact e6as_caseB g h hK hhR hcent

theorem e6TwoModelRest_holds :
    E6TwoModelRest :=
  ⟨rE, j0E, rE_basic.1, rE_basic.2.1, rE_basic.2.2.1, rE_basic.2.2.2, rE_item1, rE_item4,
    rE_item3, rE_item2⟩

end CFSG.StandardType.GGSixE6Two
