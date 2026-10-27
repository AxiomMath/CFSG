module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TwE6NSyl
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TwE6NCham
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TwE6NOpp
public import CFSG.LocalAnalysis.StandardType.GGRootNormInner

public section

namespace CFSG.StandardType.LieKnownR2.Short

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Exceptional CFSG.Blueprint.Chevalley
open scoped commutatorElement

private noncomputable abbrev teNP_S3
    {k : Type} [Field k] (θ : k →+* k) : twE6W k θ :=
  (coxeterMatrix (twistedDatum k θ).isFiniteType).toCoxeterSystem.simple (nf 2)

private theorem teNP_S3_sq
    {k : Type} [Field k] (θ : k →+* k) : teNP_S3 θ * teNP_S3 θ = 1 :=
  CoxeterSystem.simple_mul_simple_self _ (nf 2)

private noncomputable abbrev teNP_N3
    {k : Type} [Field k] (θ : k →+* k) : fixedGroup k θ := nHat θ (nf 2)

private theorem teNP_F4_v3_fixes_single3 :
    wordAct (fun i : Fin (Tag.rank .F4) => (reflection (Tag.cartan .F4) i).toAddMonoidHom)
      [nf 2, nf 0, nf 1, nf 2, nf 0, nf 1, nf 2, nf 0, nf 1, nf 2]
      (Pi.single (nf 2) 1) = Pi.single (nf 2) 1 := by
  decide +kernel

private theorem teNP_single3_mem_roots
    {k : Type} [Field k] (θ : k →+* k) :
    (Pi.single (nf 2) 1 : Fin (twistedDatum k θ).rank → ℤ) ∈ (twistedDatum k θ).roots := by
  rw [twistedDatum_roots]
  exact isRoot_single .F4 (nf 2)

private theorem teNP_neg_single3_mem_roots
    {k : Type} [Field k] (θ : k →+* k) :
    (-(Pi.single (nf 2) 1 : Fin (twistedDatum k θ).rank → ℤ)) ∈ (twistedDatum k θ).roots := by
  rw [twistedDatum_roots]
  exact isRoot_neg_single .F4 (nf 2)

private theorem teNP_V3_fixes_alpha3
    {k : Type} [Field k] (θ : k →+* k) :
    weylAction (twistedDatum k θ).isFiniteType (twE6V3 k θ)
      (Pi.single (nf 2) 1 : Fin (twistedDatum k θ).rank → ℤ) =
      (Pi.single (nf 2) 1 : Fin (twistedDatum k θ).rank → ℤ) := by
  rw [show twE6V3 k θ =
      (coxeterMatrix (twistedDatum k θ).isFiniteType).toCoxeterSystem.wordProd
        [nf 2, nf 0, nf 1, nf 2, nf 0, nf 1, nf 2, nf 0, nf 1, nf 2] from rfl]
  rw [CFSG.LieType.Steinberg.OfCartan.weylAction_wordProd]
  rw [show (twistedDatum k θ).cartan = Tag.cartan .F4 from rfl]
  exact teNP_F4_v3_fixes_single3

private theorem teNP_V3_fixes_neg_alpha3
    {k : Type} [Field k] (θ : k →+* k) :
    weylAction (twistedDatum k θ).isFiniteType (twE6V3 k θ)
      (-(Pi.single (nf 2) 1 : Fin (twistedDatum k θ).rank → ℤ)) =
      -(Pi.single (nf 2) 1 : Fin (twistedDatum k θ).rank → ℤ) := by
  rw [map_neg, teNP_V3_fixes_alpha3 θ]

private theorem teNP_Nv_conj_single3
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) :
    Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (twE6N θ hθ (twE6V3 k θ))))
        ((twistedDatum k θ).rootGroup (Pi.single (nf 2) 1)) =
      (twistedDatum k θ).rootGroup (Pi.single (nf 2) 1) := by
  have h := (actsAs_nrep (twE6_hct θ hθ) (twE6V3 k θ))
    (Pi.single (nf 2) 1 : Fin (twistedDatum k θ).rank → ℤ) (teNP_single3_mem_roots θ)
  rw [show twE6N θ hθ (twE6V3 k θ) = nrep (twE6_hct θ hθ) (twE6V3 k θ) from rfl]
  rw [h, teNP_V3_fixes_alpha3 θ]

private theorem teNP_Nv_conj_neg_single3
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) :
    Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (twE6N θ hθ (twE6V3 k θ))))
        ((twistedDatum k θ).rootGroup (-(Pi.single (nf 2) 1 : Fin (twistedDatum k θ).rank → ℤ))) =
      (twistedDatum k θ).rootGroup (-(Pi.single (nf 2) 1 : Fin (twistedDatum k θ).rank → ℤ)) := by
  have h := (actsAs_nrep (twE6_hct θ hθ) (twE6V3 k θ))
    (-(Pi.single (nf 2) 1 : Fin (twistedDatum k θ).rank → ℤ)) (teNP_neg_single3_mem_roots θ)
  rw [show twE6N θ hθ (twE6V3 k θ) = nrep (twE6_hct θ hθ) (twE6V3 k θ) from rfl]
  rw [h, teNP_V3_fixes_neg_alpha3 θ]

private theorem teNP_Nv_mem_rankOne
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) {x : fixedGroup k θ}
    (hx : x ∈ rankOne (twistedDatum k θ).rootGroup (nf 2)) :
    twE6N θ hθ (twE6V3 k θ) * x * (twE6N θ hθ (twE6V3 k θ))⁻¹ ∈
      rankOne (twistedDatum k θ).rootGroup (nf 2) := by
  have h1 := teNP_Nv_conj_single3 θ hθ
  have h2 := teNP_Nv_conj_neg_single3 θ hθ
  refine conj_mem_sup (twE6N θ hθ (twE6V3 k θ)) (fun y hy => ?_) (fun y hy => ?_) x hx
  · rw [← h1]; exact ⟨y, hy, rfl⟩
  · change twE6N θ hθ (twE6V3 k θ) * y * (twE6N θ hθ (twE6V3 k θ))⁻¹ ∈
      (twistedDatum k θ).rootGroup (-(Pi.single (nf 2) 1 : Fin (twistedDatum k θ).rank → ℤ))
    rw [← h2]; exact ⟨y, hy, rfl⟩

private theorem teNP_Torus_mem_rankOne
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) {t : fixedGroup k θ}
    (ht : t ∈ (⨆ i, hHat k θ i : Subgroup (fixedGroup k θ))) {x : fixedGroup k θ}
    (hx : x ∈ rankOne (twistedDatum k θ).rootGroup (nf 2)) :
    t * x * t⁻¹ ∈ rankOne (twistedDatum k θ).rootGroup (nf 2) := by
  have h1 := iSup_le_normalizer_rootGroup (twE6_hct θ hθ) (teNP_single3_mem_roots θ) ht
  have h2 := iSup_le_normalizer_rootGroup (twE6_hct θ hθ) (teNP_neg_single3_mem_roots θ) ht
  refine conj_mem_sup t (fun y hy => ?_) (fun y hy => ?_) x hx
  · exact (Subgroup.mem_normalizer_iff.mp h1 y).1 hy
  · exact (Subgroup.mem_normalizer_iff.mp h2 y).1 hy

private theorem teNP_N3_not_mem_borel
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) :
    nHat θ (nf 2) ∉ twE6Borel θ := by
  intro h
  have h' : nrep (twE6_hct θ hθ)
      ((coxeterMatrix (twistedDatum k θ).isFiniteType).toCoxeterSystem.simple (nf 2))
      ∈ twE6Borel θ := by
    erw [nrep_simple]
    exact h
  have hw := (nrep_mem_borel_iff (hct := twE6_hct θ hθ)
    (hext := twistedDatum_steinbergExtras θ hθ)).1 h'
  exact (CoxeterSystem.simple_ne_one _ (nf 2)) hw

private theorem teNP_Nv_conj_n3
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) :
    ∃ t ∈ hHat k θ (nf 2),
      twE6N θ hθ (twE6V3 k θ) * nHat θ (nf 2) * (twE6N θ hθ (twE6V3 k θ))⁻¹ = nHat θ (nf 2) * t :=
  exists_conj_n_eq (twE6_hct θ hθ) (twistedDatum_steinbergExtras θ hθ)
    (actsAs_nrep (twE6_hct θ hθ) (twE6V3 k θ)) (teNP_V3_fixes_alpha3 θ)

private theorem teNP_Nv_conj_n3_not_mem_borel
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) :
    twE6N θ hθ (twE6V3 k θ) * nHat θ (nf 2) * (twE6N θ hθ (twE6V3 k θ))⁻¹ ∉ twE6Borel θ := by
  intro h
  obtain ⟨t, ht, he⟩ := teNP_Nv_conj_n3 θ hθ
  have h2 : nHat θ (nf 2) * t ∈ twE6Borel θ := he ▸ h
  have htB : t ∈ twE6Borel θ := iSup_le_borel (le_iSup (hHat k θ) (nf 2) ht)
  have h3 : nHat θ (nf 2) ∈ twE6Borel θ := by
    have h4 : (nHat θ (nf 2) * t) * t⁻¹ ∈ twE6Borel θ := mul_mem h2 (inv_mem htB)
    have e : (nHat θ (nf 2) * t) * t⁻¹ = nHat θ (nf 2) := by group
    rwa [e] at h4
  exact teNP_N3_not_mem_borel θ hθ h3

private theorem teNP_N0_eq_n3_mul_nv
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) :
    twE6N θ hθ (twE6W0L k θ) = teNP_N3 θ * twE6N θ hθ (twE6V3 k θ) := by
  have hnd : ¬ (coxeterMatrix (twistedDatum k θ).isFiniteType).toCoxeterSystem.IsLeftDescent
      (twE6V3 k θ) (nf 2) := by
    refine CFSG.LieType.TitsSimplicity.not_isLeftDescent_of_coord_pos (k := nf 2) ?_
    have hv := teNP_V3_fixes_alpha3 θ
    have h2 := weylAction_inv_apply_apply (twistedDatum k θ).isFiniteType (twE6V3 k θ)
      (Pi.single (nf 2) 1 : Fin (twistedDatum k θ).rank → ℤ)
    rw [hv] at h2
    rw [h2]
    erw [Pi.single_eq_same]
    norm_num
  have hw : twE6W0L k θ =
      (coxeterMatrix (twistedDatum k θ).isFiniteType).toCoxeterSystem.simple (nf 2) *
        twE6V3 k θ := by
    rw [twE6V3]
    change twE6W0L k θ = teNP_S3 θ * (teNP_S3 θ * twE6W0L k θ)
    rw [← mul_assoc, teNP_S3_sq, one_mul]
  change nrep (twE6_hct θ hθ) (twE6W0L k θ) = teNP_N3 θ * nrep (twE6_hct θ hθ) (twE6V3 k θ)
  rw [hw, nrep_simple_mul (twE6_hct θ hθ) hnd]

private theorem teNP_neg_single3_inf_borel
    {k : Type} [Field k] (θ : k →+* k) :
    (twistedDatum k θ).rootGroup (-(Pi.single (nf 2) 1 : Fin (twistedDatum k θ).rank → ℤ))
      ⊓ twE6Borel θ = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro x hx
  rw [Subgroup.mem_inf] at hx
  have hxU : x ∈ negUnipotent (twistedDatum k θ) := by
    refine rootGroup_le_negUnipotent (D := twistedDatum k θ) (teNP_neg_single3_mem_roots θ) ?_ hx.1
    rw [ht_neg, show ht (Pi.single (nf 2) 1 : Fin (twistedDatum k θ).rank → ℤ) = 1 from by
      erw [ht_single]]
    norm_num
  have hmem : x ∈ twE6Borel θ ⊓ negUnipotent (twistedDatum k θ) := ⟨hx.2, hxU⟩
  rw [(twistedDatum_bruhatExtras (k := k) θ).borel_inf_negUnipotent] at hmem
  exact hmem

private theorem teNP_Cj_mul_borel
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) {g b : fixedGroup k θ}
    (hb : b ∈ twE6Borel θ) :
    twE6Cj (g * b) (twE6PosUnip θ) = twE6Cj g (twE6PosUnip θ) := by
  have hbU : b ∈ Subgroup.normalizer ((twE6PosUnip θ : Subgroup (fixedGroup k θ)) :
      Set (fixedGroup k θ)) :=
    borel_le_normalizer_posUnipotent (twE6_hct θ hθ) hb
  have hbU' : Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj b)) (twE6PosUnip θ) = twE6PosUnip θ :=
    mem_normalizer_iff_map_conj.1 hbU
  change Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (g * b))) (twE6PosUnip θ) =
    Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj g)) (twE6PosUnip θ)
  rw [map_conj_mul, hbU']

private theorem teNP_N3_inv_conj_single3
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) :
    Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (teNP_N3 θ)⁻¹))
        ((twistedDatum k θ).rootGroup (Pi.single (nf 2) 1)) =
      (twistedDatum k θ).rootGroup
        (-(Pi.single (nf 2) 1 : Fin (twistedDatum k θ).rank → ℤ)) := by
  have h := (ActsAs.inv (actsAs_n (twE6_hct θ hθ) (nf 2)))
    (Pi.single (nf 2) 1) (teNP_single3_mem_roots θ)
  have hs : weylAction (twistedDatum k θ).isFiniteType
      ((coxeterMatrix (twistedDatum k θ).isFiniteType).toCoxeterSystem.simple (nf 2))⁻¹
      (Pi.single (nf 2) 1 : Fin (twistedDatum k θ).rank → ℤ) =
      -(Pi.single (nf 2) 1 : Fin (twistedDatum k θ).rank → ℤ) := by
    erw [CoxeterSystem.inv_simple, weylAction_simple_single]
  rw [hs] at h
  exact h

private theorem teNP_Uc_torus_conj
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) {t : fixedGroup k θ}
    (ht : t ∈ (⨆ i, hHat k θ i : Subgroup (fixedGroup k θ))) {l : fixedGroup k θ} :
    twE6Cj (t * l * t⁻¹) (twE6PosUnip θ) = twE6Cj t (twE6Cj l (twE6PosUnip θ)) := by
  have htUinv : twE6Cj t⁻¹ (twE6PosUnip θ) = twE6PosUnip θ :=
    mem_normalizer_iff_map_conj.1 (borel_le_normalizer_posUnipotent (twE6_hct θ hθ)
      (inv_mem (iSup_le_borel ht)))
  change Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (t * l * t⁻¹))) (twE6PosUnip θ) =
    Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj t))
      (Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj l)) (twE6PosUnip θ))
  rw [show t * l * t⁻¹ = (t * l) * t⁻¹ by group, map_conj_mul]
  rw [show Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj t⁻¹)) (twE6PosUnip θ) =
      twE6PosUnip θ from htUinv, map_conj_mul]

private theorem teNP_finish
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)
    {l₁ l₂ : fixedGroup k θ}
    (hl₁ : l₁ ∈ rankOne (twistedDatum k θ).rootGroup (nf 2))
    (hl₂ : l₂ ∈ rankOne (twistedDatum k θ).rootGroup (nf 2))
    (hl₁S : pCoreOf 2 (twE6NA θ) ≤ twE6Cj l₁ (twE6PosUnip θ))
    (hl₂S : pCoreOf 2 (twE6NA θ) ≤ twE6Cj l₂ (twE6PosUnip θ))
    (hnot : l₁⁻¹ * (nHat θ (nf 2) * (twE6N θ hθ (twE6V3 k θ) * l₂ *
      (twE6N θ hθ (twE6V3 k θ))⁻¹)) ∉ twE6Borel θ) :
    pCoreOf 2 (twE6NA θ) ≤ twE6Rad θ := by
  set m : fixedGroup k θ := nHat θ (nf 2) * (twE6N θ hθ (twE6V3 k θ) * l₂ *
    (twE6N θ hθ (twE6V3 k θ))⁻¹) with hm
  have hmL3 : m ∈ rankOne (twistedDatum k θ).rootGroup (nf 2) := by
    rw [hm]
    exact mul_mem ((twE6_hct θ hθ).n_mem (nf 2)) (teNP_Nv_mem_rankOne θ hθ hl₂)
  have hSfix : twE6Cj (twE6N θ hθ (twE6W0L k θ)) (pCoreOf 2 (twE6NA θ)) =
      pCoreOf 2 (twE6NA θ) :=
    mem_normalizer_iff_map_conj.1
      (GGRootNorm.le_normalizer_pCoreOf (twE6NA θ) (twE6N0_mem_normalizer_alpha θ hθ))
  have hcomp : twE6Cj (twE6N θ hθ (twE6W0L k θ)) (twE6Cj l₂ (twE6PosUnip θ)) =
      twE6Cj (m * twE6N θ hθ (twE6V3 k θ)) (twE6PosUnip θ) := by
    have h1 : twE6Cj (twE6N θ hθ (twE6W0L k θ)) (twE6Cj l₂ (twE6PosUnip θ)) =
        twE6Cj (twE6N θ hθ (twE6W0L k θ) * l₂) (twE6PosUnip θ) := by
      change Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (twE6N θ hθ (twE6W0L k θ))))
          (Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj l₂)) (twE6PosUnip θ)) =
        Subgroup.map (MulEquiv.toMonoidHom
          (MulAut.conj (twE6N θ hθ (twE6W0L k θ) * l₂))) (twE6PosUnip θ)
      rw [map_conj_mul]
    rw [h1]
    congr 1
    rw [hm, teNP_N0_eq_n3_mul_nv θ hθ]
    group
  have h2 : pCoreOf 2 (twE6NA θ) ≤ twE6Cj (m * twE6N θ hθ (twE6V3 k θ)) (twE6PosUnip θ) := by
    rw [← hcomp, ← hSfix]
    exact Subgroup.map_mono hl₂S
  have hQ := twE6_opposition θ hθ hl₁ hmL3 hnot
  rw [← hQ]
  exact le_inf hl₁S h2

private theorem teNP_core
    {k : Type} [Field k] (θ : k →+* k)
    (B L X Xm T S U Q0 : Subgroup (fixedGroup k θ)) (n3 nv : fixedGroup k θ)
    (Cj : fixedGroup k θ → Subgroup (fixedGroup k θ) → Subgroup (fixedGroup k θ))
    (hInit : ∃ l ∈ L, S ≤ Cj l U)
    (hFixT : ∀ t ∈ T, ∀ l ∈ L, S ≤ Cj l U → S ≤ Cj (t * l * t⁻¹) U)
    (hC7 : ∀ l₁ ∈ L, ∀ l₂ ∈ L, S ≤ Cj l₁ U → S ≤ Cj l₂ U →
      l₁⁻¹ * (n3 * (nv * l₂ * nv⁻¹)) ∉ B → S ≤ Q0)
    (hBruhat : ∀ l ∈ L, l ∈ B ∨ ∃ y ∈ X, ∃ b ∈ B, l = y * n3 * b)
    (hTB : T ≤ B)
    (hTX : ∀ t ∈ T, ∀ y ∈ X, t * y * t⁻¹ ∈ X)
    (hTL : ∀ t ∈ T, ∀ l ∈ L, t * l * t⁻¹ ∈ L)
    (hnvTinv : ∀ t ∈ T, nv⁻¹ * t * nv ∈ T)
    (hn3Tinv : ∀ t ∈ T, n3⁻¹ * t * n3 ∈ T)
    (hn3L : n3 ∈ L)
    (hn3_notB : n3 ∉ B)
    (hn3X : ∀ y ∈ X, n3⁻¹ * y * n3 ∈ Xm)
    (hXmB : Xm ⊓ B = ⊥)
    (hIT : ∀ y ∈ X, (∀ t ∈ T, t * y * t⁻¹ = y) → y = 1)
    (hnvLB : ∀ b ∈ L ⊓ B, nv * b * nv⁻¹ ∈ B)
    (hnv_n3_notB : nv * n3 * nv⁻¹ ∉ B) :
    S ≤ Q0 := by
  by_contra hP
  have hA : ∀ l₁ ∈ L, ∀ l₂ ∈ L, S ≤ Cj l₁ U → S ≤ Cj l₂ U →
      l₁⁻¹ * (n3 * (nv * l₂ * nv⁻¹)) ∈ B := by
    intro l₁ hl₁ l₂ hl₂ hf₁ hf₂
    by_contra h
    exact hP (hC7 l₁ hl₁ l₂ hl₂ hf₁ hf₂ h)
  obtain ⟨l, hlL, hfl⟩ := hInit
  have hStep : ∀ c ∈ T, l⁻¹ * c * l ∈ B := by
    intro c hc
    set a : fixedGroup k θ := n3⁻¹ * c * n3 with ha
    have haT : a ∈ T := by rw [ha]; exact hn3Tinv c hc
    set t : fixedGroup k θ := nv⁻¹ * a * nv with ht
    have htT : t ∈ T := by rw [ht]; exact hnvTinv a haT
    have hat : nv * t * nv⁻¹ = a := by rw [ht]; group
    have hf_t : S ≤ Cj (t * l * t⁻¹) U := hFixT t htT l hlL hfl
    have h2 := hA l hlL (t * l * t⁻¹) (hTL t htT l hlL) hfl hf_t
    have h1 := hA l hlL l hlL hfl hfl
    have hb0 : l⁻¹ * (n3 * (nv * l * nv⁻¹)) ∈ B := h1
    have hE : (l⁻¹ * (n3 * (nv * l * nv⁻¹))) * a⁻¹ ∈ B :=
      mul_mem hb0 (inv_mem (hTB haT))
    have h2' : l⁻¹ * (n3 * (a * (nv * l * nv⁻¹) * a⁻¹)) ∈ B := by
      have he : nv * (t * l * t⁻¹) * nv⁻¹ = a * (nv * l * nv⁻¹) * a⁻¹ := by
        calc nv * (t * l * t⁻¹) * nv⁻¹ =
            (nv * t * nv⁻¹) * (nv * l * nv⁻¹) * (nv * t * nv⁻¹)⁻¹ := by group
          _ = a * (nv * l * nv⁻¹) * a⁻¹ := by rw [hat]
      rwa [he] at h2
    have hD : l⁻¹ * (n3 * a * n3⁻¹) * l ∈ B := by
      have h2'' : (l⁻¹ * (n3 * a * n3⁻¹) * l) *
          ((l⁻¹ * (n3 * (nv * l * nv⁻¹))) * a⁻¹) ∈ B := by
        have he : l⁻¹ * (n3 * (a * (nv * l * nv⁻¹) * a⁻¹)) =
            (l⁻¹ * (n3 * a * n3⁻¹) * l) *
              ((l⁻¹ * (n3 * (nv * l * nv⁻¹))) * a⁻¹) := by
          rw [show n3 * (nv * l * nv⁻¹) =
              l * (l⁻¹ * (n3 * (nv * l * nv⁻¹))) from by group]
          group
        rwa [he] at h2'
      have he : l⁻¹ * (n3 * a * n3⁻¹) * l =
          ((l⁻¹ * (n3 * a * n3⁻¹) * l) *
            ((l⁻¹ * (n3 * (nv * l * nv⁻¹))) * a⁻¹)) *
            ((l⁻¹ * (n3 * (nv * l * nv⁻¹))) * a⁻¹)⁻¹ := by group
      rw [he]
      exact mul_mem h2'' (inv_mem hE)
    have hc' : n3 * a * n3⁻¹ = c := by rw [ha]; group
    rwa [hc'] at hD
  rcases hBruhat l hlL with hlB | ⟨y, hy, b, hb, hl_eq⟩
  ·
    have h1 := hA l hlL l hlL hfl hfl
    have hnl' : l * (l⁻¹ * (n3 * (nv * l * nv⁻¹))) ∈ B := mul_mem hlB h1
    have hnl'2 : n3 * (nv * l * nv⁻¹) ∈ B := by rwa [mul_inv_cancel_left] at hnl'
    have hnb : nv * l * nv⁻¹ ∈ B := hnvLB l ⟨hlL, hlB⟩
    exact hn3_notB (by
      have := mul_mem hnl'2 (inv_mem hnb)
      rwa [mul_inv_cancel_right] at this)
  ·
    have hyfix : ∀ c ∈ T, c * y * c⁻¹ = y := by
      intro c hc
      have hcl : l⁻¹ * c * l ∈ B := hStep c hc
      have hX : n3⁻¹ * y⁻¹ * c * y * n3 ∈ B := by
        have hbXb : b⁻¹ * (n3⁻¹ * y⁻¹ * c * y * n3) * b ∈ B := by
          have he : l⁻¹ * c * l = b⁻¹ * (n3⁻¹ * y⁻¹ * c * y * n3) * b := by
            rw [hl_eq]; group
          rwa [he] at hcl
        have heq : n3⁻¹ * y⁻¹ * c * y * n3 =
            b * (b⁻¹ * (n3⁻¹ * y⁻¹ * c * y * n3) * b) * b⁻¹ := by group
        rw [heq]
        exact mul_mem (mul_mem hb hbXb) (inv_mem hb)
      have hyc : c * y * c⁻¹ ∈ X := hTX c hc y hy
      have hyyc : y⁻¹ * (c * y * c⁻¹) ∈ X := mul_mem (inv_mem hy) hyc
      have hz : n3⁻¹ * (y⁻¹ * (c * y * c⁻¹)) * n3 ∈ Xm := hn3X _ hyyc
      have hzd : (n3⁻¹ * (y⁻¹ * (c * y * c⁻¹)) * n3) * (n3⁻¹ * c * n3) ∈ B := by
        have heq : (n3⁻¹ * (y⁻¹ * (c * y * c⁻¹)) * n3) * (n3⁻¹ * c * n3) =
            n3⁻¹ * y⁻¹ * c * y * n3 := by group
        rw [heq]; exact hX
      have hd : n3⁻¹ * c * n3 ∈ T := hn3Tinv c hc
      have hzB : n3⁻¹ * (y⁻¹ * (c * y * c⁻¹)) * n3 ∈ B := by
        have h1 := mul_mem hzd (inv_mem (hTB hd))
        have e : ((n3⁻¹ * (y⁻¹ * (c * y * c⁻¹)) * n3) * (n3⁻¹ * c * n3)) *
            (n3⁻¹ * c * n3)⁻¹ = n3⁻¹ * (y⁻¹ * (c * y * c⁻¹)) * n3 := by group
        rwa [e] at h1
      have hz1 : n3⁻¹ * (y⁻¹ * (c * y * c⁻¹)) * n3 = 1 := by
        have hbot : n3⁻¹ * (y⁻¹ * (c * y * c⁻¹)) * n3 ∈ Xm ⊓ B := ⟨hz, hzB⟩
        rw [hXmB] at hbot
        exact Subgroup.mem_bot.mp hbot
      have hyy : y⁻¹ * (c * y * c⁻¹) = 1 := by
        have := congrArg (fun z : fixedGroup k θ => n3 * z * n3⁻¹) hz1
        simpa [mul_assoc] using this
      have hyc_eq : c * y * c⁻¹ = y := by
        have := congrArg (fun z : fixedGroup k θ => y * z) hyy
        simpa [mul_assoc] using this
      exact hyc_eq
    have hy1 : y = 1 := hIT y hy hyfix
    have hl_n3 : l = n3 * b := by rw [hl_eq, hy1, one_mul]
    have h1 := hA l hlL l hlL hfl hfl
    have hbL : b ∈ L := by
      have h : n3⁻¹ * l ∈ L := mul_mem (inv_mem hn3L) hlL
      rw [hl_n3] at h
      rwa [inv_mul_cancel_left] at h
    have hnb : nv * b * nv⁻¹ ∈ B := hnvLB b ⟨hbL, hb⟩
    have hthetal : l⁻¹ * (n3 * (nv * l * nv⁻¹)) ∈ B := h1
    exact hnv_n3_notB (by
      have heq : l⁻¹ * (n3 * (nv * l * nv⁻¹)) =
          b⁻¹ * ((nv * n3 * nv⁻¹) * (nv * b * nv⁻¹)) := by rw [hl_n3]; group
      have hbX : b⁻¹ * ((nv * n3 * nv⁻¹) * (nv * b * nv⁻¹)) ∈ B := by rwa [← heq]
      have hmn : (nv * n3 * nv⁻¹) * (nv * b * nv⁻¹) ∈ B := by
        have := mul_mem hb hbX
        rwa [mul_inv_cancel_left] at this
      have := mul_mem hmn (inv_mem hnb)
      rwa [mul_inv_cancel_right] at this)
private noncomputable abbrev teNP_T
    {k : Type} [Field k] (θ : k →+* k) : Subgroup (fixedGroup k θ) :=
  ⨆ i : Fin (Tag.rank .F4), hHat k θ i

private noncomputable abbrev teNP_L
    {k : Type} [Field k] (θ : k →+* k) : Subgroup (fixedGroup k θ) :=
  rankOne (twistedDatum k θ).rootGroup (nf 2)

private noncomputable abbrev teNP_X
    {k : Type} [Field k] (θ : k →+* k) : Subgroup (fixedGroup k θ) :=
  (twistedDatum k θ).rootGroup (Pi.single (nf 2) 1)

private noncomputable abbrev teNP_Xm
    {k : Type} [Field k] (θ : k →+* k) : Subgroup (fixedGroup k θ) :=
  (twistedDatum k θ).rootGroup (-(Pi.single (nf 2) 1 : Fin (twistedDatum k θ).rank → ℤ))

private theorem teNP_ht_alpha3
    {k : Type} [Field k] (θ : k →+* k) :
    0 < ht (Pi.single (nf 2) 1 : Fin (twistedDatum k θ).rank → ℤ) := by
  erw [ht_single]; norm_num

private theorem teNP_n3Tinv
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) {t : fixedGroup k θ}
    (ht : t ∈ teNP_T θ) : (nHat θ (nf 2))⁻¹ * t * nHat θ (nf 2) ∈ teNP_T θ := by
  have hx : (nHat θ (nf 2))⁻¹ ∈ Subgroup.normalizer (teNP_T θ : Set (fixedGroup k θ)) :=
    inv_mem (n_mem_normalizer_iSup (D := twistedDatum k θ) (n := nHat θ) (H := hHat k θ)
      (twE6_hct θ hθ) (nf 2))
  exact (Subgroup.mem_normalizer_iff.mp hx t).1 ht

private theorem teNP_nvTinv
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) {t : fixedGroup k θ}
    (ht : t ∈ teNP_T θ) : (twE6N θ hθ (twE6V3 k θ))⁻¹ * t * twE6N θ hθ (twE6V3 k θ) ∈ teNP_T θ :=
  conj_mem_iSup_of_mem_weylN (D := twistedDatum k θ) (n := nHat θ) (H := hHat k θ)
    (twE6_hct θ hθ) (inv_mem (nrep_mem_weylN (twE6_hct θ hθ) (twE6V3 k θ))) ht

private theorem teNP_T_X
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) {t : fixedGroup k θ}
    (ht : t ∈ teNP_T θ) {y : fixedGroup k θ}
    (hy : y ∈ (twistedDatum k θ).rootGroup (Pi.single (nf 2) 1)) :
    t * y * t⁻¹ ∈ (twistedDatum k θ).rootGroup (Pi.single (nf 2) 1) :=
  (Subgroup.mem_normalizer_iff.mp
    (iSup_le_normalizer_rootGroup (twE6_hct θ hθ) (teNP_single3_mem_roots θ) ht) y).1 hy

private theorem teNP_n3X_elem
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) {y : fixedGroup k θ}
    (hy : y ∈ (twistedDatum k θ).rootGroup (Pi.single (nf 2) 1)) :
    (nHat θ (nf 2))⁻¹ * y * nHat θ (nf 2) ∈
      (twistedDatum k θ).rootGroup
        (-(Pi.single (nf 2) 1 : Fin (twistedDatum k θ).rank → ℤ)) := by
  rw [← teNP_N3_inv_conj_single3 θ hθ]
  exact ⟨y, hy, rfl⟩

private theorem teNP_Fix_T
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) {t : fixedGroup k θ}
    (ht : t ∈ teNP_T θ) {l : fixedGroup k θ}
    (hfl : pCoreOf 2 (twE6NA θ) ≤ twE6Cj l (twE6PosUnip θ)) :
    pCoreOf 2 (twE6NA θ) ≤ twE6Cj (t * l * t⁻¹) (twE6PosUnip θ) := by
  have htN : t ∈ twE6NA θ :=
    iSup_le_normalizer_rootGroup (twE6_hct θ hθ) (twE6_alpha_mem_roots θ) ht
  have htS : twE6Cj t (pCoreOf 2 (twE6NA θ)) = pCoreOf 2 (twE6NA θ) :=
    mem_normalizer_iff_map_conj.1 (GGRootNorm.le_normalizer_pCoreOf (twE6NA θ) htN)
  rw [teNP_Uc_torus_conj θ hθ ht]
  calc pCoreOf 2 (twE6NA θ) = twE6Cj t (pCoreOf 2 (twE6NA θ)) := htS.symm
    _ ≤ twE6Cj t (twE6Cj l (twE6PosUnip θ)) := Subgroup.map_mono hfl

private theorem teNP_Bruhat
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) {l : fixedGroup k θ}
    (hl : l ∈ rankOne (twistedDatum k θ).rootGroup (nf 2)) :
    l ∈ twE6Borel θ ∨ ∃ y ∈ (twistedDatum k θ).rootGroup (Pi.single (nf 2) 1),
      ∃ b ∈ twE6Borel θ, l = y * nHat θ (nf 2) * b := by
  have hXB : (twistedDatum k θ).rootGroup (Pi.single (nf 2) 1) ≤ twE6Borel θ :=
    rootGroup_le_borel (teNP_single3_mem_roots θ) (teNP_ht_alpha3 θ)
  rcases (twistedDatum_steinbergExtras θ hθ).rankOne_bruhat (nf 2) l hl with
    ⟨h, hh, u, hu, hlu⟩ | ⟨u, hu, h, hh, v, hv, hluv⟩
  · left
    rw [hlu]
    exact mul_mem (iSup_le_borel (le_iSup (hHat k θ) (nf 2) hh)) (hXB hu)
  · right
    refine ⟨u, hu, h * v, mul_mem (iSup_le_borel (le_iSup (hHat k θ) (nf 2) hh)) (hXB hv), ?_⟩
    rw [hluv]; group

private theorem teNP_nvLB
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) {b : fixedGroup k θ}
    (hb : b ∈ rankOne (twistedDatum k θ).rootGroup (nf 2) ⊓ twE6Borel θ) :
    twE6N θ hθ (twE6V3 k θ) * b * (twE6N θ hθ (twE6V3 k θ))⁻¹ ∈ twE6Borel θ := by
  have hXB : (twistedDatum k θ).rootGroup (Pi.single (nf 2) 1) ≤ twE6Borel θ :=
    rootGroup_le_borel (teNP_single3_mem_roots θ) (teNP_ht_alpha3 θ)
  rcases (twistedDatum_steinbergExtras θ hθ).rankOne_bruhat (nf 2) b hb.1 with
    ⟨h, hh, u, hu, hbu⟩ | ⟨u, hu, h, hh, v, hv, hbuv⟩
  · rw [hbu]
    have hu' : twE6N θ hθ (twE6V3 k θ) * u * (twE6N θ hθ (twE6V3 k θ))⁻¹ ∈
        (twistedDatum k θ).rootGroup (Pi.single (nf 2) 1) := by
      rw [← teNP_Nv_conj_single3 θ hθ]
      exact ⟨u, hu, rfl⟩
    have he : twE6N θ hθ (twE6V3 k θ) * (h * u) * (twE6N θ hθ (twE6V3 k θ))⁻¹ =
        (twE6N θ hθ (twE6V3 k θ) * h * (twE6N θ hθ (twE6V3 k θ))⁻¹) *
        (twE6N θ hθ (twE6V3 k θ) * u * (twE6N θ hθ (twE6V3 k θ))⁻¹) := by group
    rw [he]
    exact mul_mem
      (iSup_le_borel (conj_mem_iSup_of_mem_weylN (D := twistedDatum k θ) (n := nHat θ)
        (H := hHat k θ) (twE6_hct θ hθ) (nrep_mem_weylN (twE6_hct θ hθ) (twE6V3 k θ))
        (le_iSup (hHat k θ) (nf 2) hh)))
      (hXB hu')
  · exfalso
    have hn3B : nHat θ (nf 2) ∈ twE6Borel θ := by
      have huB : u ∈ twE6Borel θ := hXB hu
      have hvB : v ∈ twE6Borel θ := hXB hv
      have hhB : h ∈ twE6Borel θ := iSup_le_borel (le_iSup (hHat k θ) (nf 2) hh)
      have hbB : b ∈ twE6Borel θ := hb.2
      have hmem := mul_mem (mul_mem (inv_mem huB) hbB) (inv_mem (mul_mem hhB hvB))
      rw [hbuv] at hmem
      simpa [mul_assoc] using hmem
    exact teNP_N3_not_mem_borel θ hθ hn3B

theorem twE6_pCoreOf_normalizer_alpha_eq
    {k : Type} [Field k] [Finite k] [CharP k 2] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)
    (hIT : TorusRegularAlpha3 θ) :
    pCoreOf 2 (twE6NA θ) = twE6Rad θ := by
  have hct := twE6_hct θ hθ
  refine le_antisymm ?_ (twE6Rad_le_pCoreOf_normalizer θ hθ)
  obtain ⟨g, hgS, hgPsi⟩ := twE6_exists_conj_sylow θ hθ
  have hgB := twE6_mem_borel_or_panel_of_forall_le θ hθ hgPsi
  have hInit : ∃ l ∈ teNP_L θ, pCoreOf 2 (twE6NA θ) ≤ twE6Cj l (twE6PosUnip θ) := by
    rcases hgB with hgB | ⟨y, hy, b, hb, rfl⟩
    · refine ⟨1, one_mem _, ?_⟩
      have hU : twE6Cj g (twE6PosUnip θ) = twE6PosUnip θ :=
        mem_normalizer_iff_map_conj.1 (borel_le_normalizer_posUnipotent hct hgB)
      rw [hU] at hgS
      have hU1 : twE6Cj (1 : fixedGroup k θ) (twE6PosUnip θ) = twE6PosUnip θ := by
        change Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (1 : fixedGroup k θ)))
          (twE6PosUnip θ) = twE6PosUnip θ
        rw [show MulAut.conj (1 : fixedGroup k θ) = 1 from map_one MulAut.conj]
        rw [show MulEquiv.toMonoidHom (1 : MulAut (fixedGroup k θ)) = MonoidHom.id _ from rfl]
        exact Subgroup.map_id _
      rw [hU1]; exact hgS
    · refine ⟨y * nHat θ (nf 2), mul_mem (Subgroup.mem_sup_left hy) (hct.n_mem (nf 2)), ?_⟩
      rw [teNP_Cj_mul_borel θ hθ hb] at hgS
      exact hgS
  have hTB : teNP_T θ ≤ twE6Borel θ := iSup_le_borel (D := twistedDatum k θ) (H := hHat k θ)
  have hIT' : ∀ y ∈ teNP_X θ, (∀ t ∈ teNP_T θ, t * y * t⁻¹ = y) → y = 1 := hIT
  refine teNP_core θ (B := twE6Borel θ) (L := teNP_L θ) (X := teNP_X θ) (Xm := teNP_Xm θ)
    (T := teNP_T θ) (S := pCoreOf 2 (twE6NA θ)) (U := twE6PosUnip θ) (Q0 := twE6Rad θ)
    (n3 := nHat θ (nf 2)) (nv := twE6N θ hθ (twE6V3 k θ)) (Cj := twE6Cj (θ := θ))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact hInit
  · intro t ht l _ hfl; exact teNP_Fix_T θ hθ ht hfl
  · intro l₁ hl₁ l₂ hl₂ hf₁ hf₂ h; exact teNP_finish θ hθ hl₁ hl₂ hf₁ hf₂ h
  · intro l hl; exact teNP_Bruhat θ hθ hl
  · exact hTB
  · intro t ht y hy; exact teNP_T_X θ hθ ht hy
  · intro t ht l hl; exact teNP_Torus_mem_rankOne θ hθ ht hl
  · intro t ht; exact teNP_nvTinv θ hθ ht
  · intro t ht; exact teNP_n3Tinv θ hθ ht
  · exact hct.n_mem (nf 2)
  · exact teNP_N3_not_mem_borel θ hθ
  · intro y hy; exact teNP_n3X_elem θ hθ hy
  · exact teNP_neg_single3_inf_borel θ
  · exact hIT'
  · intro b hb; exact teNP_nvLB θ hθ hb
  · exact teNP_Nv_conj_n3_not_mem_borel θ hθ

end CFSG.StandardType.LieKnownR2.Short
