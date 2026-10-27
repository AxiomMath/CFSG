module

public import CFSG.LocalAnalysis.StandardType.GGTorusMaxStruct
public import CFSG.LocalAnalysis.StandardType.GGQTwoDRMStabDefs
public import CFSG.LocalAnalysis.StandardType.GGTorusMaxStructAux2
public import CFSG.LocalAnalysis.StandardType.GGAutomizerMap
public import CFSG.LocalAnalysis.StandardType.GGHdRo7ExcLin
import CFSG.CGT.Stroth77.Section223Sylow
public import Certificates.Certificate1952
import CFSG.CGT.Stroth77.AmbientSplit
import CFSG.Quasithin.H13.Sp62D3

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.Blueprint.Chevalley

theorem qtwoDB40_not_neg {m : ℕ} (hm : Even m) {c : Fin m} {w : DVec m ≃ₗ[ZMod 3] DVec m}
    (hw : w ∈ dEvenStab m (Pi.single c 1))
    (hneg : ∀ (v : DVec m) (k : Fin m), k ≠ c → w v k = -v k) : False := by
  obtain ⟨σ, c', hc', hprod, hact⟩ := hw.1
  have hsign : ∀ k : Fin m, k ≠ c → c' k = -1 := by
    intro k hk
    have h := hneg (dBasis m k) k hk
    rw [hact k] at h
    have h' : c' k * (if k = σ k then (1 : ZMod 3) else 0) = -1 := by
      simpa [dBasis, Pi.basisFun_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul] using h
    by_cases hσ : k = σ k
    · rw [if_pos hσ, mul_one] at h'
      exact h'
    · rw [if_neg hσ, mul_zero] at h'
      exact absurd h' (by decide)
  have hw2 : w (dBasis m c) = dBasis m c := by
    rw [dBasis, Pi.basisFun_apply]
    exact hw.2
  have hcc : c' c = 1 := by
    have h : c' c • dBasis m (σ c) = dBasis m c := hact c ▸ hw2
    have h' := congrFun h c
    have h'' : c' c * (if c = σ c then (1 : ZMod 3) else 0) = 1 := by
      simpa [dBasis, Pi.basisFun_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul] using h'
    by_cases hσc : c = σ c
    · rw [if_pos hσc, mul_one] at h''
      exact h''
    · rw [if_neg hσc, mul_zero] at h''
      exact absurd h'' (by decide)
  have hprod' : ∏ i : Fin m, c' i = (-1 : ZMod 3) ^ (m - 1) := by
    rw [← Finset.prod_erase_mul Finset.univ c' (Finset.mem_univ c), hcc, mul_one]
    rw [Finset.prod_eq_pow_card (fun i hi => hsign i (Finset.mem_erase.mp hi).1)]
    congr 1
    rw [Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ, Fintype.card_fin]
  have hodd : Odd (m - 1) := by
    have hle : 1 ≤ m := by
      have h := c.isLt
      omega
    exact Nat.Even.sub_odd hle hm odd_one
  have h1 : (1 : ZMod 3) = -1 := by
    calc (1 : ZMod 3) = ∏ i : Fin m, c' i := hprod.symm
      _ = (-1 : ZMod 3) ^ (m - 1) := hprod'
      _ = -1 := hodd.neg_one_pow
  exact absurd h1 (by decide)

theorem qtwoDB40_contra {Γ : Type} [Group Γ] [Finite Γ] (hΓ : Nat.card Γ ∣ 2903040)
    {H : Subgroup Γ} (hH : Nat.card H = 322560) {z : Γ} (hz : ∀ y : Γ, z * y = y * z)
    (hz2 : z ^ 2 = 1) (hzH : z ∉ H) : False := by
  have hzN : z ∈ Subgroup.normalizer (H : Set Γ) :=
    Subgroup.center_le_normalizer (H : Set Γ)
      (Subgroup.mem_center_iff.mpr fun y => (hz y).symm)
  have hzsq : z * z ∈ H := by
    rw [pow_two] at hz2
    rw [hz2]
    exact H.one_mem
  have hcard := CFSG.CGT.Stroth77.S223.card_sup_zpowers_two hzN hzsq hzH
  rw [hH] at hcard
  have hcard' : Nat.card (H ⊔ Subgroup.zpowers z : Subgroup Γ) = 645120 :=
    hcard.trans (by norm_num)
  have hdvd : 645120 ∣ Nat.card Γ := by
    rw [← hcard']
    exact Subgroup.card_subgroup_dvd_card _
  exact (by norm_num : ¬ (645120 ∣ 2903040)) (hdvd.trans hΓ)


private theorem qtwoDB40_ker_conj (L' : Type) [Group L'] :
    (MulAut.conj : L' →* MulAut L').ker = Subgroup.center L' := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
  constructor
  · intro h x
    have hx : g * x * g⁻¹ = x := by
      have := congrArg (fun f : MulAut L' => f x) h
      simpa [MulAut.conj_apply] using this
    have hthis : g * x = x * g := by
      calc g * x = g * x * g⁻¹ * g := by group
        _ = x * g := by rw [hx]
    exact hthis.symm
  · intro h
    ext x
    simp only [MulAut.conj_apply, MulAut.one_apply]
    rw [← h x]
    group

private theorem qtwoDB40_equiv_E7 {R : Type} [Group R]
    (h : GGHasLabel (⟨.E7, 0, 1⟩ : LargeEvenLabel) R) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ∧
      Nonempty (R ≃* ↥(adjointGroup .E7 K)) := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  obtain ⟨ψ⟩ := CFSG.StandardType.centerQuot_chevGroup_equiv K .E7
  have hcenK : Subgroup.center (adjointGroup .E7 K) = ⊥ :=
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
  let q₀ : CFSG.Blueprint.AdjointQuotient .E7 K ≃* ↥(adjointGroup .E7 K) :=
    (QuotientGroup.quotientMulEquivOfEq hcenK).trans QuotientGroup.quotientBot
  exact ⟨K, inferInstance, inferInstance, by simpa using hK, ⟨(e.trans ψ).trans q₀⟩⟩

private theorem qtwoDB40_ggAutomizer_subgroupOf {G : Type} [Group G] {H A : Subgroup G}
    (hA : A ≤ H) :
    ggAutomizer H A = (ggAutomizer (⊤ : Subgroup H) (A.subgroupOf H)).map
      (MulAut.congr (Subgroup.subgroupOfEquivOfLe hA)).toMonoidHom := by
  have hmap : (A.subgroupOf H).map H.subtype = A := Subgroup.map_subgroupOf_eq_of_le hA
  have h := F4AutWeyl.ggAutomizer_map_eq (f := H.subtype) H.subtype_injective
    (⊤ : Subgroup H) (A.subgroupOf H) (B' := A) hmap
  rw [Subgroup.map_top, Subgroup.range_subtype] at h
  have hψ : ((A.subgroupOf H).equivMapOfInjective H.subtype H.subtype_injective).trans
      (MulEquiv.subgroupCongr hmap) = Subgroup.subgroupOfEquivOfLe hA := by
    ext x
    rfl
  rw [hψ] at h
  exact h

private theorem qtwoDB40_frame_aut {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {E : Subgroup ↥(adjointGroup .E7 K)} (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 7) :
    Nat.card (ggAutomizer (⊤ : Subgroup ↥(adjointGroup .E7 K)) E) = 2903040 ∧
      ∃ z ∈ ggAutomizer ⊤ E, ∀ y : ↥E, z y = y⁻¹ := by
  haveI : CharP K 2 := CFSG.StandardType.charP_two_of_card (m := 1) (by simpa using hK)
  let T : Subgroup ↥(adjointGroup .E7 K) := (TableBExcTwoTB.tE K TableBExcTwo.frameE7).range
  obtain ⟨c, hc⟩ := TableBExcTwoTB.exists_conj_frame_of_card_E7 hK hE hcard.ge
  have hc' : T.map (MulAut.conj c).toMonoidHom = E := hc.symm
  have hcentT : Subgroup.centralizer (T : Set _) = T := TableBExcTwoTB.centralizer_tE_frameE7 hK
  obtain ⟨π, φ, hπs, hπk, hπi⟩ := FrameRoute.tmStruct_concrete (τ := .E7) (d := 6) (K := K)
    (Or.inl rfl) TableBExcTwo.frameE7 rfl TableBExcTwoFusion.frameE7_reflections
    TableBExc.Three.cartan_symm_E7
    (TableBExc.isUnit_det_cartan_of_eq Nat.prime_three CFSG.StandardType.det_cartan_E7
      (by norm_num)) hK (TableBExcTwoTB.centralizer_tE_frameE7 hK)
  have hAutT_eq : ggAutomizer (⊤ : Subgroup ↥(adjointGroup .E7 K)) T =
      T.normalizerMonoidHom.range := by
    ext ψ
    rw [mem_ggAutomizer_iff, MonoidHom.mem_range]
    constructor
    · rintro ⟨g, -, hgN, hgψ⟩
      exact ⟨⟨g, hgN⟩, MulEquiv.ext fun b => Subtype.ext (hgψ b).symm⟩
    · rintro ⟨g, hg⟩
      refine ⟨g, Subgroup.mem_top _, g.2, fun b => ?_⟩
      rw [← hg]
      exact CFSG.StandardType.normalizerMonoidHom_apply_coe g.2 b
  have hker : T.normalizerMonoidHom.ker =
      T.subgroupOf (Subgroup.normalizer (T : Set _)) := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hg
      have hgC : (g : ↥(adjointGroup .E7 K)) ∈ Subgroup.centralizer (T : Set _) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have h1 : (g : ↥(adjointGroup .E7 K)) * y * (g : ↥(adjointGroup .E7 K))⁻¹ = y := by
          have h := congrArg (fun f : MulAut ↥T =>
            ((f ⟨y, hy⟩ : ↥T) : ↥(adjointGroup .E7 K))) hg
          simpa [CFSG.StandardType.normalizerMonoidHom_apply_coe] using h
        have h2 : (g : ↥(adjointGroup .E7 K)) * y = y * (g : ↥(adjointGroup .E7 K)) := by
          calc (g : ↥(adjointGroup .E7 K)) * y =
                (g : ↥(adjointGroup .E7 K)) * y * (g : ↥(adjointGroup .E7 K))⁻¹ *
                  (g : ↥(adjointGroup .E7 K)) := by group
            _ = y * (g : ↥(adjointGroup .E7 K)) := by rw [h1]
        exact h2.symm
      rwa [hcentT] at hgC
    · intro hg
      refine MulEquiv.ext fun y => ?_
      apply Subtype.ext
      rw [CFSG.StandardType.normalizerMonoidHom_apply_coe]
      have hc := Subgroup.mem_centralizer_iff.mp (hcentT.ge hg)
        (y : ↥(adjointGroup .E7 K)) y.2
      rw [← hc]
      simp
  have hN : Nat.card ↥(Subgroup.normalizer (T : Set ↥(adjointGroup .E7 K))) =
      Nat.card (CFSG.LieType.Chevalley.WeylGroup Tag.E7) *
        Nat.card (T.subgroupOf (Subgroup.normalizer (T : Set ↥(adjointGroup .E7 K)))) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker
    have h2 : Nat.card (↥(Subgroup.normalizer (T : Set _)) ⧸ π.ker) =
        Nat.card (CFSG.LieType.Chevalley.WeylGroup Tag.E7) :=
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπs).toEquiv
    have h3 : Nat.card π.ker = Nat.card (T.subgroupOf (Subgroup.normalizer (T : Set _))) := by
      rw [hπk]
    rw [h1, h2, h3]
  have hAutT : Nat.card (ggAutomizer (⊤ : Subgroup ↥(adjointGroup .E7 K)) T) = 2903040 := by
    rw [hAutT_eq]
    have hcr := Subgroup.card_ker_mul_card_range T.normalizerMonoidHom
    have hcr' : Nat.card (T.normalizerMonoidHom.ker) *
        Nat.card (T.normalizerMonoidHom.range) =
        Nat.card (T.normalizerMonoidHom.ker) *
          Nat.card (CFSG.LieType.Chevalley.WeylGroup Tag.E7) := by
      rw [hcr, hN, hker, mul_comm]
    have hcancel : Nat.card (T.normalizerMonoidHom.range) =
        Nat.card (CFSG.LieType.Chevalley.WeylGroup Tag.E7) :=
      mul_left_cancel₀ (Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩) hcr'
    rw [hcancel, CFSG.StandardType.NoOffExc.card_weyl_E7]
  obtain ⟨g, hg⟩ := hπs (excW0 Tag.E7)
  have hgT : ∀ y : ↥T, T.normalizerMonoidHom g y = y⁻¹ := by
    intro y
    apply φ.injective
    rw [hπi g y, hg, torusMulAut_excW0_eq_negOne (Or.inl rfl),
      negOneMulAut_apply_mul, map_inv, ofAdd_neg, ofAdd_toAdd]
  let ψ : T ≃* E := (T.equivMapOfInjective (MulAut.conj c).toMonoidHom
    (MulAut.conj c).injective).trans (MulEquiv.subgroupCongr hc')
  have hAutTE : ggAutomizer (⊤ : Subgroup ↥(adjointGroup .E7 K)) E =
      (ggAutomizer (⊤ : Subgroup ↥(adjointGroup .E7 K)) T).map
        (MulAut.congr ψ).toMonoidHom := by
    have h := F4AutWeyl.ggAutomizer_map_eq (f := (MulAut.conj c).toMonoidHom)
      (MulAut.conj c).injective (⊤ : Subgroup ↥(adjointGroup .E7 K)) T (B' := E) hc'
    rwa [Subgroup.map_top_of_surjective (MulAut.conj c).toMonoidHom
      (MulAut.conj c).surjective] at h
  have hzE : MulAut.congr ψ (T.normalizerMonoidHom g) ∈ ggAutomizer ⊤ E := by
    rw [hAutTE]
    exact Subgroup.mem_map_of_mem _ (by rw [hAutT_eq]; exact MonoidHom.mem_range.mpr ⟨g, rfl⟩)
  have hzE_inv : ∀ y : ↥E, MulAut.congr ψ (T.normalizerMonoidHom g) y = y⁻¹ := by
    intro y
    rw [show MulAut.congr ψ (T.normalizerMonoidHom g) y =
      ψ (T.normalizerMonoidHom g (ψ.symm y)) from rfl, hgT, map_inv, ψ.apply_symm_apply]
  refine ⟨?_, ⟨MulAut.congr ψ (T.normalizerMonoidHom g), hzE, hzE_inv⟩⟩
  rw [hAutTE, Subgroup.card_map_of_injective (MulAut.congr ψ).injective, hAutT]

theorem qtwoDB40_e7_aut {L' : Type} [Group L'] [Finite L'] (hperf : commutator L' = ⊤)
    (hlab : GGHasLabel ⟨.E7, 0, 1⟩ (L' ⧸ Subgroup.center L'))
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian 3 A) (hcard : Nat.card A = 3 ^ 7)
    (hAinn : A ≤ (MulAut.conj : L' →* MulAut L').range) :
    Nat.card (ggAutomizer (MulAut.conj : L' →* MulAut L').range A) ∣ 2903040 ∧
      ∃ z ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A, ∀ y : ↥A, z y = y⁻¹ := by
  obtain ⟨K, _, _, hK2, ⟨θ⟩⟩ := qtwoDB40_equiv_E7 hlab
  let f : L' →* MulAut L' := MulAut.conj
  let Inn : Subgroup (MulAut L') := f.range
  have hker : f.ker = Subgroup.center L' := qtwoDB40_ker_conj L'
  let eInn : (L' ⧸ Subgroup.center L') ≃* Inn :=
    (QuotientGroup.quotientMulEquivOfEq
      (hker.symm.trans (MonoidHom.ker_rangeRestrict f).symm)).trans
      (QuotientGroup.quotientKerEquivOfSurjective f.rangeRestrict f.rangeRestrict_surjective)
  let e : Inn ≃* ↥(adjointGroup .E7 K) := eInn.symm.trans θ
  have hAinn' : A ≤ Inn := hAinn
  let A' : Subgroup ↥Inn := A.subgroupOf Inn
  let E : Subgroup ↥(adjointGroup .E7 K) := A'.map e.toMonoidHom
  have hEea : IsElemAbelian 3 E := (hA.subgroupOf Inn).map e.toMonoidHom
  have hEcard : Nat.card E = 3 ^ 7 := by
    rw [show E = A'.map e.toMonoidHom from rfl, Subgroup.card_map_of_injective e.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAinn').toEquiv, hcard]
  obtain ⟨hAutE, z_E, hz_E_mem, hz_E_inv⟩ := qtwoDB40_frame_aut hK2 hEea hEcard
  let ι : A' ≃* A := Subgroup.subgroupOfEquivOfLe hAinn'
  have he : A'.map e.toMonoidHom = E := rfl
  let κ : A' ≃* E := (A'.equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr he)
  have hSub : ggAutomizer Inn A = (ggAutomizer (⊤ : Subgroup ↥Inn) A').map
      (MulAut.congr ι).toMonoidHom := qtwoDB40_ggAutomizer_subgroupOf hAinn'
  have hTop : ggAutomizer (⊤ : Subgroup ↥(adjointGroup .E7 K)) E =
      (ggAutomizer (⊤ : Subgroup ↥Inn) A').map (MulAut.congr κ).toMonoidHom := by
    have h := F4AutWeyl.ggAutomizer_map_eq (f := e.toMonoidHom) e.injective
      (⊤ : Subgroup ↥Inn) A' (B' := E) he
    rwa [Subgroup.map_top_of_surjective e.toMonoidHom e.surjective] at h
  have hcardInn : Nat.card (ggAutomizer Inn A) = Nat.card (ggAutomizer ⊤ E) := by
    rw [hSub, hTop, Subgroup.card_map_of_injective (MulAut.congr ι).injective,
      Subgroup.card_map_of_injective (MulAut.congr κ).injective]
  have hcardInn' : Nat.card (ggAutomizer Inn A) = 2903040 := hcardInn.trans hAutE
  refine ⟨?_, ?_⟩
  · rw [hcardInn']
  · obtain ⟨z', hz'_mem, hz'_eq⟩ := Subgroup.mem_map.mp (hTop ▸ hz_E_mem)
    refine ⟨MulAut.congr ι z', ?_, ?_⟩
    · rw [hSub]
      exact Subgroup.mem_map_of_mem _ hz'_mem
    · intro a
      have hz'_inv : ∀ a' : ↥A', z' a' = a'⁻¹ := by
        intro a'
        apply κ.injective
        have h1 : (MulAut.congr κ z') (κ a') = κ (z' a') := by
          simp [MulAut.congr_apply]
        calc κ (z' a') = (MulAut.congr κ z') (κ a') := h1.symm
          _ = z_E (κ a') := congrArg (fun f : MulAut ↥E => f (κ a')) hz'_eq
          _ = (κ a')⁻¹ := hz_E_inv (κ a')
          _ = κ (a'⁻¹) := (map_inv κ a').symm
      rw [show MulAut.congr ι z' a = ι (z' (ι.symm a)) from rfl, hz'_inv, map_inv,
        ι.apply_symm_apply]

end CFSG.StandardType.QTwo

end
