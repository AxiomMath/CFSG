module

public import CFSG.Timmesfeld.Bridge.RootSetsConn3
public import CFSG.Adapters.WholeGroupLayer
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20a
public import CFSG.LocalAnalysis.WeakClosure81.EightEightDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
  (IsL2 IsSz IsL3 IsU3 IsSp4 IsU4 IsU5 IsOmega8m Is3D4 IsAlt IsSL3 Bar2 OInf Opp)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)

variable {G : Type} [Group G] [Finite G]

private theorem subsingleton_of_isPerfect_of_isSolvable {X : Type*} [Group X]
    (hperf : Group.IsPerfect X) (hsol : Group.IsSolvable X) : Subsingleton X := by
  obtain ⟨n, hn⟩ := hsol.solvable
  haveI : Group.IsPerfect X := hperf
  have htop : derivedSeries X n = ⊤ := Group.IsPerfect.derivedSeries_eq_top X n
  rw [htop] at hn
  refine ⟨fun a b => ?_⟩
  have ha : a ∈ (⊤ : Subgroup X) := Subgroup.mem_top a
  rw [hn] at ha
  have hb : b ∈ (⊤ : Subgroup X) := Subgroup.mem_top b
  rw [hn] at hb
  rw [Subgroup.mem_bot] at ha hb
  rw [ha, hb]

private theorem isPerfect_le_of_normal_isSolvable_quotient {X : Type*} [Group X] {H K : Subgroup X}
    (hK : K.Normal) (hperf : Group.IsPerfect H) (hsol : Group.IsSolvable (X ⧸ K)) : H ≤ K := by
  haveI : Group.IsSolvable (X ⧸ K) := hsol
  have hperf' : Group.IsPerfect (H.map (QuotientGroup.mk' K)) := hperf.map _
  have hsol' : Group.IsSolvable (H.map (QuotientGroup.mk' K)) :=
    Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.subtype (H.map (QuotientGroup.mk' K))) (Subgroup.subtype_injective _)
  haveI : Subsingleton (H.map (QuotientGroup.mk' K)) :=
    subsingleton_of_isPerfect_of_isSolvable hperf' hsol'
  have hbot : H.map (QuotientGroup.mk' K) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have h1 : (⟨x, hx⟩ : ↥(H.map (QuotientGroup.mk' K))) = 1 := Subsingleton.elim _ _
    simpa using congrArg Subtype.val h1
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
  exact hbot

private theorem not_isSolvable_of_isQuasisimple {X : Type*} [Group X]
    (h : CFSG.IsQuasisimple X) : ¬ Group.IsSolvable X := by
  intro hs
  obtain ⟨hperf, hsimple, -⟩ := h
  haveI : Group.IsPerfect X := hperf
  haveI : Nontrivial (X ⧸ Subgroup.center X) := hsimple.toNontrivial
  have hsub : Subsingleton X := subsingleton_of_isPerfect_of_isSolvable inferInstance hs
  haveI : Subsingleton X := hsub
  exact not_subsingleton (X ⧸ Subgroup.center X) inferInstance

private theorem isQuasisimple_map_of_ker {A B X : Type*} [Group A] [Group B] [Group X]
    {K : Subgroup A} (π : A →* B) (ψ : ↥K →* X) (hψ : Function.Surjective ψ)
    (hker : ∀ k : ↥K, ψ k = 1 ↔ π (k : A) = 1) (hX : CFSG.IsQuasisimple X) :
    CFSG.IsQuasisimple (K.map π) := by
  let πK : ↥K →* B := π.comp K.subtype
  have hrange : πK.range = K.map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hker_eq : πK.ker = ψ.ker := by
    ext k
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    exact (hker k).symm
  have h1 : CFSG.IsQuasisimple ↥πK.range :=
    CFSG.IsQuasisimple.of_mulEquiv
      ((QuotientGroup.quotientKerEquivRange πK).symm.trans
        ((QuotientGroup.quotientMulEquivOfEq hker_eq).trans
          (QuotientGroup.quotientKerEquivOfSurjective ψ hψ))) hX
  exact hrange ▸ h1

private theorem exists_isComponent_le_of_normal {X : Type*} [Group X] [Finite X]
    (hsol : CFSG.solvableRadical X = ⊥) {N : Subgroup X} (hN : N.Normal) (hN1 : N ≠ ⊥) :
    ∃ K : Subgroup X, CFSG.IsComponent K ∧ K ≤ N := by
  have hfit_le : CFSG.fittingSubgroup X ≤ CFSG.solvableRadical X :=
    CFSG.Timmesfeld.Bridge.le_solvableRadical' (inferInstance : (CFSG.fittingSubgroup X).Normal)
      (inferInstance : Group.IsSolvable (CFSG.fittingSubgroup X))
  have hfit : CFSG.fittingSubgroup X = ⊥ := le_bot_iff.mp (hfit_le.trans (le_of_eq hsol))
  have hgen : CFSG.generalizedFitting X = CFSG.layer X := by
    rw [CFSG.generalizedFitting.eq_sup, hfit, bot_sup_eq]
  have hcent : Subgroup.centralizer (CFSG.layer X : Set X) = ⊥ := by
    have hle : Subgroup.centralizer (CFSG.layer X : Set X) ≤ CFSG.fittingSubgroup X := by
      rw [← hgen]
      exact CFSG.Adapters.centralizer_generalizedFitting_le_fittingSubgroup X
    exact le_bot_iff.mp (hle.trans (le_of_eq hfit))
  haveI : (CFSG.layer X).Characteristic := CFSG.LocalCores.layer_characteristic (G := X)
  have hlayerN : (CFSG.layer X).Normal := inferInstance
  haveI : N.Normal := hN
  haveI : (CFSG.layer X).Normal := hlayerN
  have hMnormal : (N ⊓ CFSG.layer X).Normal := inferInstance
  have hMne : N ⊓ CFSG.layer X ≠ ⊥ := by
    intro hbot
    have hcomm : ⁅N, CFSG.layer X⁆ ≤ N ⊓ CFSG.layer X := Subgroup.commutator_le_inf N _
    rw [hbot] at hcomm
    have hle : N ≤ Subgroup.centralizer (CFSG.layer X : Set X) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp (le_bot_iff.mp hcomm)
    exact hN1 (le_bot_iff.mp (hle.trans (le_of_eq hcent)))
  by_contra hno
  push Not at hno
  have hcentM : CFSG.layer X ≤ Subgroup.centralizer ((N ⊓ CFSG.layer X : Subgroup X) : Set X) := by
    rw [CFSG.layer.eq_sSup]
    refine sSup_le fun K hK => ?_
    rcases CFSG.LocalCores.component_normal_subgroup hK hMnormal with h | h
    · exact absurd (h.trans inf_le_left) (hno K hK)
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
  have hcomm : ⁅CFSG.layer X, N ⊓ CFSG.layer X⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcentM
  have hcomm' : ⁅(N ⊓ CFSG.layer X : Subgroup X), CFSG.layer X⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact hcomm
  have hle : N ⊓ CFSG.layer X ≤ Subgroup.centralizer (CFSG.layer X : Set X) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm'
  exact hMne (le_bot_iff.mp (hle.trans (le_of_eq hcent)))

private theorem component_le_of_normal_of_sup_isPGroup {X : Type*} [Group X] [Finite X]
    (hsol : CFSG.solvableRadical X = ⊥) {L T N : Subgroup X} (hL : CFSG.IsComponent L)
    (hT : IsPGroup 2 T) (hsup : L ⊔ T = ⊤) (hN : N.Normal) (hN1 : N ≠ ⊥) : L ≤ N := by
  obtain ⟨K, hK, hKN⟩ := exists_isComponent_le_of_normal hsol hN hN1
  let E : Subgroup X := CFSG.Quasithin.conjClosure L ⊤
  have hLE : L ≤ E := CFSG.Quasithin.le_conjClosure L ⊤
  have hE_normal : E.Normal :=
    Subgroup.normalizer_eq_top_iff.mp
      (top_le_iff.mp (CFSG.Quasithin.le_normalizer_conjClosure L ⊤))
  have hsupE : E ⊔ T = ⊤ := eq_top_iff.mpr (by
    rw [← hsup]
    exact sup_le_sup_right hLE T)
  have hEsolv : Group.IsSolvable (X ⧸ E) := by
    haveI : Group.IsSolvable T := by
      haveI : Group.IsNilpotent T := hT.isNilpotent
      infer_instance
    let φ : T →* X ⧸ E := (QuotientGroup.mk' E).comp T.subtype
    have hφ : Function.Surjective φ := by
      intro y
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective E y
      haveI : E.Normal := hE_normal
      have hx : x ∈ E ⊔ T := hsupE ▸ Subgroup.mem_top x
      obtain ⟨e, he, t, ht, het⟩ := (Subgroup.mem_sup_of_normal_left (s := E) (t := T)).mp hx
      refine ⟨⟨t, ht⟩, ?_⟩
      have he1 : (QuotientGroup.mk' E) e = 1 := (QuotientGroup.eq_one_iff e).mpr he
      show (QuotientGroup.mk' E) t = (QuotientGroup.mk' E) x
      rw [← het, map_mul, he1, one_mul]
    exact Group.isSolvable_of_surjective hφ
  have hKE : K ≤ E :=
    isPerfect_le_of_normal_isSolvable_quotient hE_normal hK.1.1 hEsolv
  have hconj : ∃ g : X, K = L.map (MulAut.conj g).toMonoidHom := by
    have hex : ∃ g : X, K ≤ L.map (MulAut.conj g).toMonoidHom := by
      by_contra hno
      push Not at hno
      have hcomm : ∀ g : X, ⁅K, L.map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
        intro g
        have hAg : CFSG.IsComponent (L.map (MulAut.conj g).toMonoidHom) :=
          CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g) hL
        rcases CFSG.LocalCores.component_subnormal_subgroup hK hAg.2 with h | h
        · exact absurd h (hno g)
        · exact h
      have hEC : E ≤ Subgroup.centralizer (K : Set X) := by
        refine CFSG.Quasithin.conjClosure_le ?_
        intro h _ z hz
        have hAhC : L.map (MulAut.conj h).toMonoidHom ≤ Subgroup.centralizer (K : Set X) :=
          Subgroup.commutator_eq_bot_iff_le_centralizer.mp
            ((Subgroup.commutator_comm _ _).trans (hcomm h))
        exact hAhC ⟨z, hz, rfl⟩
      have hKC : K ≤ Subgroup.centralizer (E : Set X) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp
          ((Subgroup.commutator_comm K E).trans
            (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hEC))
      have hcommKK : ∀ a b : K, a * b = b * a := by
        intro a b
        have ha : (a : X) ∈ E := hKE a.2
        have hb : (b : X) ∈ Subgroup.centralizer (E : Set X) := hKC b.2
        exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hb (a : X) ha)
      haveI : IsMulCommutative K := isMulCommutative_iff.mpr hcommKK
      haveI : Nontrivial K := CFSG.LocalCores.isQuasisimple_nontrivial hK.1
      haveI : Group.IsPerfect K := hK.1.1
      exact not_subsingleton K inferInstance
    obtain ⟨g, hg⟩ := hex
    refine ⟨g, le_antisymm hg ?_⟩
    have hAg : CFSG.IsComponent (L.map (MulAut.conj g).toMonoidHom) :=
      CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g) hL
    rcases CFSG.LocalCores.component_subnormal_subgroup hAg hK.2 with h | h
    · exact h
    · exfalso
      have hKK : ⁅K, K⁆ = ⊥ := by
        refine le_bot_iff.mp ?_
        calc ⁅K, K⁆ ≤ ⁅L.map (MulAut.conj g).toMonoidHom, K⁆ := Subgroup.commutator_mono hg le_rfl
          _ = ⊥ := h
      haveI : Group.IsPerfect K := hK.1.1
      rw [Subgroup.commutator_eq_self] at hKK
      haveI : Nontrivial K := CFSG.LocalCores.isQuasisimple_nontrivial hK.1
      have hsub : Subsingleton K := by rw [hKK]; infer_instance
      exact not_subsingleton K hsub
  obtain ⟨g, hgK⟩ := hconj
  intro l hl
  have hgl : g * l * g⁻¹ ∈ K :=
    hgK.symm ▸ (⟨l, hl, rfl⟩ : g * l * g⁻¹ ∈ L.map (MulAut.conj g).toMonoidHom)
  have hglN : g * l * g⁻¹ ∈ N := hKN hgl
  have hconjN : g⁻¹ * (g * l * g⁻¹) * g ∈ N := by
    simpa using hN.conj_mem (g * l * g⁻¹) hglN g⁻¹
  simpa [mul_assoc] using hconjN

theorem oInf_eq_kerMV {V H T : Subgroup G} (hT : IsSylowIn 2 T H)
    (hN : calNIn H T = {H ⊓ normalizer (V : Set G)})
    (hL : ∃ L : Subgroup G, IsComponentModN (OInf H) H L ∧ L ⊔ T = H) :
    OInf H = kerMV V H := by
  classical
  obtain ⟨L, hLcomp, hLsup⟩ := hL
  have hPH : OInf H ≤ H := Subgroup.map_subtype_le _
  have hLH : L ≤ H := hLcomp.2.2.1
  have hPnorm : ((OInf H).subgroupOf H).Normal := hLcomp.1
  have hPn : H ≤ normalizer (OInf H : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPH).mp hPnorm
  have hTM : T ≤ normalizer (V : Set G) := by
    have hmem : H ⊓ normalizer (V : Set G) ∈ calNIn H T := by
      rw [hN]; exact Set.mem_singleton _
    exact hmem.1.trans inf_le_right
  have hHMlt : H ⊓ normalizer (V : Set G) < H := by
    have hmem : H ⊓ normalizer (V : Set G) ∈ calNIn H T := by
      rw [hN]; exact Set.mem_singleton _
    exact hmem.2.1
  have hHnotM : ¬ H ≤ normalizer (V : Set G) := fun hle =>
    absurd (le_antisymm inf_le_left (le_inf le_rfl hle)) (ne_of_lt hHMlt)
  have hPT_lt : OInf H ⊔ T < H := by
    refine lt_of_le_of_ne (sup_le hPH hT.le) ?_
    intro heq
    haveI hPTsolv : Group.IsSolvable ↥(OInf H ⊔ T) :=
      CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20a_isSolvable_sup H T hT.le hT.isPGroup
    haveI : Group.IsSolvable ↥H := heq ▸ hPTsolv
    obtain ⟨X, hXgrp, φ, hφsurj, hφker, hXq⟩ := hLcomp.2.2.2.2
    letI : Group X := hXgrp
    haveI : Group.IsSolvable ↥L :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hLH)
        (Subgroup.inclusion_injective hLH)
    haveI : Group.IsSolvable X := Group.isSolvable_of_surjective hφsurj
    exact not_isSolvable_of_isQuasisimple hXq inferInstance
  have hPM : OInf H ≤ normalizer (V : Set G) := by
    obtain ⟨Y, hY, hle⟩ :=
      exists_mem_calNIn_of_lt (H := H) (T := T) (Y := OInf H ⊔ T) le_sup_right hPT_lt
    rw [hN, Set.mem_singleton_iff] at hY
    exact (le_sup_left.trans hle).trans (hY ▸ inf_le_right)
  have hPker : OInf H ≤ kerMV V H :=
    le_kerMV_of_normal hPH (fun h hh n hn =>
      (Subgroup.mem_normalizer_iff.mp (hPn hh) n).mp hn) hPM
  have hNP : kerMV V H ≤ OInf H := by
    by_contra hnot
    let A := ↥H
    let K0 : Subgroup A := CFSG.solvableRadical A
    let Xq := A ⧸ K0
    let π : A →* Xq := QuotientGroup.mk' K0
    let K : Subgroup A := L.subgroupOf H
    let L' : Subgroup Xq := K.map π
    let T' : Subgroup Xq := (T.subgroupOf H).map π
    let N' : Subgroup Xq := ((kerMV V H).subgroupOf H).map π
    have hP' : (OInf H).subgroupOf H = K0 := by
      change (OInf H).subgroupOf H = CFSG.solvableRadical ↥H
      unfold OInf
      rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
    have hπker : π.ker = K0 := QuotientGroup.ker_mk' K0
    have hsolXq : CFSG.solvableRadical Xq = ⊥ := by
      change sSup {N : Subgroup Xq | N.Normal ∧ Group.IsSolvable N} = ⊥
      refine le_antisymm (sSup_le ?_) bot_le
      rintro S ⟨hSn, hSs⟩
      exact le_of_eq (CFSG.Timmesfeld.Bridge.eq_bot_of_normal_isSolvable_quotient
        (H := A) hSn hSs)
    obtain ⟨X, hXgrp, φ, hφsurj, hφker, hXq⟩ := hLcomp.2.2.2.2
    letI : Group X := hXgrp
    let ψ : ↥(L.subgroupOf H) →* X :=
      φ.comp (Subgroup.subgroupOfEquivOfLe hLH).toMonoidHom
    have hψ : Function.Surjective ψ :=
      hφsurj.comp (Subgroup.subgroupOfEquivOfLe hLH).surjective
    have hψker : ∀ k : ↥(L.subgroupOf H), ψ k = 1 ↔ π (k : A) = 1 := by
      intro k
      have h1 : ψ k = φ ((Subgroup.subgroupOfEquivOfLe hLH) k) := rfl
      rw [h1, hφker]
      have h2 : (((Subgroup.subgroupOfEquivOfLe hLH) k : ↥L) : G) = (k : G) := rfl
      rw [h2]
      constructor
      · intro hk
        refine (QuotientGroup.eq_one_iff (N := K0) (k : A)).mpr ?_
        rw [← hP']
        exact hk
      · intro hk
        have h2' : (k : A) ∈ K0 := (QuotientGroup.eq_one_iff (N := K0) (k : A)).mp hk
        exact Subgroup.mem_subgroupOf.mp (hP'.symm ▸ h2')
    have hL'q : CFSG.IsQuasisimple L' :=
      isQuasisimple_map_of_ker π ψ hψ hψker hXq
    have hL'sub : L'.IsSubnormal :=
      (CFSG.Open.IsSubnormal.subgroupOf hLcomp.2.2.2.1).map
        (QuotientGroup.mk'_surjective K0)
    have hL'comp : CFSG.IsComponent L' := ⟨hL'q, hL'sub⟩
    have hT'pg : IsPGroup 2 T' :=
      (IsPGroup.comap_of_injective hT.isPGroup H.subtype H.subtype_injective).map π
    have hsup' : L' ⊔ T' = ⊤ := by
      have hKsup : K ⊔ T.subgroupOf H = ⊤ := by
        rw [← Subgroup.subgroupOf_sup hLH hT.le, hLsup, Subgroup.subgroupOf_self]
      rw [← Subgroup.map_sup, hKsup, Subgroup.map_top_of_surjective π
        (QuotientGroup.mk'_surjective K0)]
    have hNnorm : ((kerMV V H).subgroupOf H).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer (kerMV_le_self V H)]
      intro g hg
      rw [Subgroup.mem_normalizer_iff]
      intro n
      constructor
      · intro hn; exact conj_mem_kerMV hg hn
      · intro hn
        have h' := conj_mem_kerMV (H.inv_mem hg) hn
        have he : g⁻¹ * (g * n * g⁻¹) * (g⁻¹)⁻¹ = n := by group
        rwa [he] at h'
    have hN'normal : N'.Normal := hNnorm.map π (QuotientGroup.mk'_surjective K0)
    have hN'ne : N' ≠ ⊥ := by
      intro hbot
      apply hnot
      have hle : (kerMV V H).subgroupOf H ≤ K0 := by
        rw [← hπker]
        exact (Subgroup.map_eq_bot_iff (H := (kerMV V H).subgroupOf H) (f := π)).mp hbot
      intro n hn
      have hn' : (⟨n, kerMV_le_self V H hn⟩ : A) ∈ K0 := hle hn
      exact Subgroup.mem_subgroupOf.mp (hP'.symm ▸ hn')
    have hLN' : L' ≤ N' :=
      component_le_of_normal_of_sup_isPGroup hsolXq hL'comp hT'pg hsup' hN'normal hN'ne
    have hLN : L ≤ kerMV V H := by
      intro l hl
      have hl' : π (⟨l, hLH hl⟩ : A) ∈ L' :=
        Subgroup.mem_map.mpr ⟨⟨l, hLH hl⟩, by change l ∈ L; exact hl, rfl⟩
      obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp (hLN' hl')
      have hyG : (y : G) ∈ kerMV V H := hy
      have hker : (⟨l, hLH hl⟩ : A) * y⁻¹ ∈ K0 := by
        rw [← hπker, MonoidHom.mem_ker]
        rw [map_mul, map_inv, hyeq, mul_inv_cancel]
      have hker' : (⟨l, hLH hl⟩ : A) * y⁻¹ ∈ (OInf H).subgroupOf H := hP'.symm ▸ hker
      have hcoe : (((⟨l, hLH hl⟩ : A) * y⁻¹ : A) : G) = l * (y : G)⁻¹ := by
        dsimp only [A]
        simp
      have hPmem : l * (y : G)⁻¹ ∈ OInf H := hcoe ▸ Subgroup.mem_subgroupOf.mp hker'
      have hre : l = (l * (y : G)⁻¹) * (y : G) := by group
      rw [hre]
      exact (kerMV V H).mul_mem (hPker hPmem) hyG
    exact hHnotM (hLsup ▸ sup_le (hLN.trans (kerMV_le_normalizer V H)) hTM)
  exact le_antisymm hPker hNP


end CFSG.LocalAnalysis.WeakClosure81

end
