module

public import CFSG.LocalAnalysis.Gross82.OrderThree
import CFSG.GroupTheory.ComponentCovering
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2Cover

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)

private theorem k891ggrossb_center_quotient_eq_bot {G : Type*} [Group G]
    (hq : CFSG.Open.IsQuasisimple G) : Subgroup.center (G ⧸ Subgroup.center G) = ⊥ := by
  have hsimple : IsSimpleGroup (G ⧸ Subgroup.center G) := hq.2
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (Subgroup.center (G ⧸ Subgroup.center G)) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ :=
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian G hq
    apply hab
    have ha : a ∈ Subgroup.center (G ⧸ Subgroup.center G) := h ▸ Subgroup.mem_top a
    exact (Subgroup.mem_center_iff.mp ha b).symm

open CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2 in
private noncomputable def k891ggrossb_quotAutOfHom {G : Type*} [Group G] (L : Subgroup G) :
    Subgroup.normalizer (L : Set G) →* MulAut (L ⧸ Subgroup.center L) where
  toFun u := quotAutOf L u.2
  map_one' := quotAutOf_one L
  map_mul' u v := quotAutOf_mul L u.2 v.2

open CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2 in
theorem r891g211_gross_component (hGross : Gross82.R891GrossCoreOrderThree) {J0 : Type}
    [Group J0] [Finite J0]
    (hK : CFSG.Open.IsKGroup J0) {P J : Subgroup J0} (hP : IsSylowOf 3 P ⊤)
    (hJ : IsComponentOf J ⊤) (h3 : 3 ∣ Nat.card (↥J ⧸ center ↥J)) {c : J0}
    (hcN : c ∈ normalizer (J : Set J0)) (hc3 : c ^ 3 = 1)
    (hcP : ∀ x ∈ P ⊓ J, c * x = x * c) :
    ∃ t ∈ P ⊓ J, ∀ x ∈ J, c * x * c⁻¹ = t * x * t⁻¹ := by
  classical
  have h3prime : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq : CFSG.Open.IsQuasisimple ↥J := hJ.2.2
  let Jb : Type := ↥J ⧸ Subgroup.center ↥J
  let π : ↥J →* Jb := QuotientGroup.mk' (Subgroup.center ↥J)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hsimple : IsSimpleGroup Jb := hq.2
  have hnonab : ∃ a b : Jb, a * b ≠ b * a :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian ↥J hq
  have hcenter : Subgroup.center Jb = ⊥ := k891ggrossb_center_quotient_eq_bot hq
  have hcat : IsCatalogGroup Jb := hK.isCatalogGroup_of_surjective J hnonab π hπ
  let γb : MulAut Jb := quotAutOf J hcN
  have hγb3 : γb ^ 3 = 1 := by
    have hγb : γb = k891ggrossb_quotAutOfHom J ⟨c, hcN⟩ := rfl
    rw [hγb, ← map_pow]
    have hc3' : (⟨c, hcN⟩ : Subgroup.normalizer (J : Set J0)) ^ 3 = 1 := by
      apply Subtype.ext
      simp [hc3]
    rw [hc3', map_one]
  let Pj : Subgroup ↥J := (P ⊓ J).subgroupOf J
  let Pb : Subgroup Jb := Pj.map π
  have hPj : IsSylowOf 3 (P ⊓ J) J := IsSylowOf.inf_of_isSubnormal hP hJ.2.1
  obtain ⟨Q, hQ⟩ := hPj.exists_sylow_eq_subgroupOf
  have hQ' : (Q : Subgroup ↥J) = Pj := hQ
  let PbSylow : Sylow 3 Jb := Q.mapSurjective hπ
  have hPbSylowcoe : (PbSylow : Subgroup Jb) = Pb := by
    rw [Sylow.coe_mapSurjective, hQ']
  have hPbSylow : IsSylowOf 3 Pb ⊤ := by
    rw [← hPbSylowcoe, CFSG.ABGLocalTools.isSylowOf_iff, Subgroup.relIndex_top_right]
    exact ⟨le_top, PbSylow.isPGroup', PbSylow.not_dvd_index⟩
  have hfix : ∀ x ∈ Pb, γb x = x := by
    intro x hx
    obtain ⟨y, hyPj, hyx⟩ := Subgroup.mem_map.mp hx
    rw [← hyx]
    have hconjy : conjAutOf J hcN y = y := by
      apply Subtype.ext
      rw [conjAutOf_apply, hcP (y : J0) (Subgroup.mem_subgroupOf.mp hyPj)]
      group
    change quotAutOf J hcN (π y) = π y
    rw [show π y = (y : Jb) from QuotientGroup.mk'_apply _ y]
    rw [quotAutOf_mk, hconjy]
  obtain ⟨tb, htbP, htbEq⟩ :=
    hGross Jb hsimple hcenter hcat h3 γb hγb3 Pb hPbSylow hfix
  obtain ⟨t, htPj, ht_eq⟩ := Subgroup.mem_map.mp htbP
  have ht_cast : (t : Jb) = tb := by
    rw [← QuotientGroup.mk'_apply]
    exact ht_eq
  have hconj : conjAutOf J hcN = MulAut.conj t :=
    conjAutOf_eq_of_quotAutOf J hq.1 hcN t (by rw [ht_cast]; exact htbEq)
  refine ⟨(t : J0), Subgroup.mem_subgroupOf.mp htPj, ?_⟩
  intro x hx
  have h1 := congrArg (fun f : MulAut ↥J => ((f ⟨x, hx⟩ : ↥J) : J0)) hconj
  simpa only [conjAutOf_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv,
    Subtype.coe_mk] using h1

private theorem k891ggrossc_sylow_inf_not_le_center {J0 : Type} [Group J0] [Finite J0]
    {P J : Subgroup J0} (hP : IsSylowOf 3 P ⊤) (hJsub : CFSG.Open.IsSubnormal J ⊤)
    (h3 : 3 ∣ Nat.card (↥J ⧸ center ↥J)) :
    ∃ x : J, (x : J0) ∈ P ⊓ J ∧ x ∉ center J := by
  have hSyl : IsSylowOf 3 (P ⊓ J) J := IsSylowOf.inf_of_isSubnormal hP hJsub
  obtain ⟨S, hS⟩ := hSyl.exists_sylow_eq_subgroupOf
  have hne : ((S.mapSurjective (QuotientGroup.mk'_surjective (center J)) :
      Sylow 3 (J ⧸ center J)) : Subgroup (J ⧸ center J)) ≠ ⊥ :=
    Sylow.ne_bot_of_dvd_card
      (S.mapSurjective (QuotientGroup.mk'_surjective (center J))) h3
  by_contra hcon
  have hle : (S : Subgroup J) ≤ center J := by
    intro x hx
    rw [hS] at hx
    rw [Subgroup.mem_subgroupOf] at hx
    by_contra hxc
    exact hcon ⟨x, hx, hxc⟩
  apply hne
  rw [Sylow.coe_mapSurjective, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  exact hle

theorem r891g211_gross_c_of_components {J0 : Type} [Group J0] [Finite J0] {P : Subgroup J0}
    (hP : IsSylowOf 3 P ⊤) (hO : CFSG.pPrimeCore 3 J0 = ⊥)
    (h3 : ∀ J : Subgroup J0, IsComponentOf J ⊤ → 3 ∣ Nat.card (↥J ⧸ center ↥J))
    (hGrossQS : ∀ J : Subgroup J0, IsComponentOf J ⊤ → ∀ c : J0, c ∈ normalizer (J : Set J0) →
      c ^ 3 = 1 → (∀ x ∈ P ⊓ J, c * x = x * c) →
        ∃ t ∈ P ⊓ J, ∀ x ∈ J, c * x * c⁻¹ = t * x * t⁻¹) :
    ∀ c ∈ P, c ^ 3 = 1 → (∀ u ∈ P ⊓ CFSG.generalizedFitting J0, c * u = u * c) →
      c ∈ CFSG.generalizedFitting J0 := by
  intro c hcP hc3 hcU
  have hFp : CFSG.fittingSubgroup J0 = CFSG.pCore 3 J0 := CFSG.Fitting_eq_pcore J0 3 hO
  have hF_le_P : CFSG.fittingSubgroup J0 ≤ P := by
    have hQ : IsPGroup 3 (CFSG.fittingSubgroup J0 ⊔ P : Subgroup J0) :=
      (hFp.symm ▸ CFSG.pCore_isPGroup (p := 3) (G := J0)).to_sup_of_normal_left hP.isPGroup
    exact sup_eq_right.mp (IsSylowOf.eq_of_le hP le_sup_right le_top hQ)
  have hF_le_inf : CFSG.pCore 3 J0 ≤ P ⊓ CFSG.generalizedFitting J0 := by
    refine le_inf ?_ ?_
    · intro u hu
      exact hF_le_P (hFp.symm ▸ hu)
    · intro u hu
      rw [CFSG.generalizedFitting.eq_sup]
      exact Subgroup.mem_sup_left (hFp.symm ▸ hu)
  have hcF : ∀ u ∈ CFSG.pCore 3 J0, c * u = u * c := fun u hu => hcU u (hF_le_inf hu)
  have hJ_le_layer : ∀ J : Subgroup J0, IsComponentOf J ⊤ → J ≤ CFSG.layer J0 :=
    fun J hJ => CFSG.LocalCores.component_le_layer ((CFSG.isComponent_iff_open J).mpr hJ)
  have hJ_le_Fs : ∀ J : Subgroup J0, IsComponentOf J ⊤ → J ≤ CFSG.generalizedFitting J0 := by
    intro J hJ
    rw [CFSG.generalizedFitting.eq_sup]
    exact (hJ_le_layer J hJ).trans
      (le_sup_right : CFSG.layer J0 ≤ CFSG.fittingSubgroup J0 ⊔ CFSG.layer J0)
  have hcPJ : ∀ J : Subgroup J0, IsComponentOf J ⊤ → ∀ y ∈ P ⊓ J, c * y = y * c := by
    intro J hJ y hy
    exact hcU y (le_inf inf_le_left (le_trans inf_le_right (hJ_le_Fs J hJ)) hy)
  have hcN : ∀ J : Subgroup J0, IsComponentOf J ⊤ → c ∈ normalizer (J : Set J0) := by
    intro J hJ
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    by_contra hne
    have hne' : J.map (MulAut.conj c).toMonoidHom ≠ J := by
      rw [MulEquiv.toMonoidHom_eq_coe]
      exact hne
    have hJ' : IsComponentOf (J.map (MulAut.conj c).toMonoidHom) ⊤ :=
      (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj c) J).mpr hJ
    have hcomm : ⁅J.map (MulAut.conj c).toMonoidHom, J⁆ = ⊥ :=
      CFSG.ComponentClassification.LocalComponents.commute_of_ne _ J hJ' hJ hne'
    have hJ'_cent : J.map (MulAut.conj c).toMonoidHom ≤ Subgroup.centralizer (J : Set J0) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    obtain ⟨xJ, hxJ_mem, hxJ_nc⟩ :=
      k891ggrossc_sylow_inf_not_le_center hP hJ.2.1 (h3 J hJ)
    have hxJ_cent : c * (xJ : J0) * c⁻¹ = (xJ : J0) := by
      rw [hcPJ J hJ (xJ : J0) hxJ_mem, mul_assoc, mul_inv_cancel, mul_one]
    have hxJ_in : (xJ : J0) ∈ J.map (MulAut.conj c).toMonoidHom := by
      refine Subgroup.mem_map.mpr ⟨(xJ : J0), xJ.2, ?_⟩
      change MulAut.conj c (xJ : J0) = (xJ : J0)
      rw [MulAut.conj_apply]
      exact hxJ_cent
    have hxJ_center : xJ ∈ center J := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hJ'_cent hxJ_in (g : J0) g.2)
    exact hxJ_nc hxJ_center
  have hdata : ∀ K : CFSG.LocalCores.ComponentIndex J0,
      ∃ t : K.1, (t : J0) ∈ P ⊓ K.1 ∧
        ∀ y ∈ K.1, c * y * c⁻¹ = (t : J0) * y * (t : J0)⁻¹ := by
    intro K
    have hK : IsComponentOf K.1 ⊤ := (CFSG.isComponent_iff_open K.1).mp K.2
    obtain ⟨t, ht, htx⟩ := hGrossQS K.1 hK c (hcN K.1 hK) hc3 (hcPJ K.1 hK)
    exact ⟨⟨t, ht.2⟩, ht, htx⟩
  let x : ∀ K : CFSG.LocalCores.ComponentIndex J0, K.1 := fun K => Classical.choose (hdata K)
  have hxspec : ∀ (K : CFSG.LocalCores.ComponentIndex J0) (y : J0), y ∈ K.1 →
      c * y * c⁻¹ = (x K : J0) * y * (x K : J0)⁻¹ :=
    fun K => (Classical.choose_spec (hdata K)).2
  let t := CFSG.LocalCores.layerMul J0 x
  have ht_mem : t ∈ CFSG.layer J0 := by
    rw [← CFSG.LocalCores.layerMul_range]
    exact ⟨x, rfl⟩
  have hmain : ∀ (K : CFSG.LocalCores.ComponentIndex J0) (y : J0), y ∈ K.1 →
      t * y * t⁻¹ = c * y * c⁻¹ := by
    intro K y hy
    let u := CFSG.LocalCores.layerMul J0 (Function.update x K 1)
    have hu : Commute y u := CFSG.LocalCores.commute_layerMul_update x K hy
    have hyu : u * y * u⁻¹ = y := hu.symm.mul_inv_cancel
    have ht : t = (x K : J0) * u := CFSG.LocalCores.layerMul_eq_mul_update x K
    rw [ht]
    calc ((x K : J0) * u) * y * ((x K : J0) * u)⁻¹
        = (x K : J0) * (u * y * u⁻¹) * (x K : J0)⁻¹ := by group
      _ = (x K : J0) * y * (x K : J0)⁻¹ := by rw [hyu]
      _ = c * y * c⁻¹ := (hxspec K y hy).symm
  let d := t⁻¹ * c
  have hd_comp : ∀ (K : CFSG.LocalCores.ComponentIndex J0) (y : J0), y ∈ K.1 →
      d * y * d⁻¹ = y := by
    intro K y hy
    have hcy : c * y * c⁻¹ = t * y * t⁻¹ := (hmain K y hy).symm
    show (t⁻¹ * c) * y * (t⁻¹ * c)⁻¹ = y
    calc (t⁻¹ * c) * y * (t⁻¹ * c)⁻¹
        = t⁻¹ * (c * y * c⁻¹) * t := by group
      _ = t⁻¹ * (t * y * t⁻¹) * t := by rw [hcy]
      _ = y := by group
  have hd_cent_layer : d ∈ Subgroup.centralizer (CFSG.layer J0 : Set J0) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hle : CFSG.layer J0 ≤ Subgroup.centralizer ({d} : Set J0) := by
      rw [CFSG.layer.eq_sSup]
      refine sSup_le fun K hK => ?_
      intro z hz
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (mul_inv_eq_iff_eq_mul.mp (hd_comp ⟨K, hK⟩ z hz)).symm
    have hy' : y ∈ Subgroup.centralizer ({d} : Set J0) := hle hy
    rwa [Subgroup.mem_centralizer_singleton_iff] at hy'
  have hcomm_FK : ⁅CFSG.pCore 3 J0, CFSG.layer J0⁆ = ⊥ := by
    rw [← hFp]
    exact CFSG.LocalCores.fitting_layer_commute
  have ht_cent_F : t ∈ Subgroup.centralizer (CFSG.pCore 3 J0 : Set J0) := by
    rw [Subgroup.commutator_comm] at hcomm_FK
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm_FK ht_mem
  have hd_F : d ∈ Subgroup.centralizer (CFSG.pCore 3 J0 : Set J0) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    show u * (t⁻¹ * c) = (t⁻¹ * c) * u
    have hcu : Commute u c := (hcF u hu).symm
    have htu : Commute u t := Subgroup.mem_centralizer_iff.mp ht_cent_F u hu
    exact (htu.inv_right.mul_right hcu).eq
  have hd_cent_Fs : d ∈ Subgroup.centralizer (CFSG.generalizedFitting J0 : Set J0) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hle : CFSG.generalizedFitting J0 ≤ Subgroup.centralizer ({d} : Set J0) := by
      rw [CFSG.generalizedFitting.eq_sup, hFp]
      refine sup_le ?_ ?_
      · intro u hu
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subgroup.mem_centralizer_iff.mp hd_F u hu
      · intro z hz
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subgroup.mem_centralizer_iff.mp hd_cent_layer z hz
    have hy' : y ∈ Subgroup.centralizer ({d} : Set J0) := hle hy
    rwa [Subgroup.mem_centralizer_singleton_iff] at hy'
  have hd_in_Fs : d ∈ CFSG.generalizedFitting J0 :=
    CFSG.centralizer_generalizedFitting_le J0 hd_cent_Fs
  have ht_Fs : t ∈ CFSG.generalizedFitting J0 := by
    rw [CFSG.generalizedFitting.eq_sup]
    exact Subgroup.mem_sup_right ht_mem
  have htd : t * d = c := by
    show t * (t⁻¹ * c) = c
    group
  rw [← htd]
  exact mul_mem ht_Fs hd_in_Fs

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
