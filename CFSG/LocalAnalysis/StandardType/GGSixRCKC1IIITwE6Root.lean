module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIITwE6LeviRoot
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1ShortTwE6
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIISUSurvivor
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIISUActAux
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiagTwisted
public import CFSG.LocalAnalysis.StandardType.SUCenterOdd
import CFSG.GroupTheory.PCore.PCoreOfMulEquiv

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.SeitzReduction.TwistedE6Pilot
  CFSG.StandardType.RCKK1IIISU CFSG.SeitzReduction CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Exceptional CFSG.ComponentClassification

theorem rckSU_suσ_toRingHom_apply (c : SUF) : SUσ.toRingHom c = c ^ (2 ^ 1) := by
  simpa using rckSUc_sigma_apply c

private theorem rckMap_le_centralizer_map {G H : Type*} [Group G] [Group H] (f : G →* H)
    {A X : Subgroup G} (hA : A ≤ Subgroup.centralizer (X : Set G)) :
    A.map f ≤ Subgroup.centralizer ((X.map f : Subgroup H) : Set H) := by
  rw [Subgroup.coe_map]
  exact (Subgroup.map_mono hA).trans (Subgroup.map_centralizer_le_centralizer_image _ f)

section Root


noncomputable abbrev twE6LeviMap : SUG 6 →* ModGL TwistTag.E6.tag SUF :=
  (twistedE6RootGroup SUF SUσ).subtype.comp
    (((su6Levi SUσ.toRingHom).subgroupOf (twistedE6RootGroup SUF SUσ)).subtype.comp
      (KGTwE6.su6LeviHom (f := 1) rckSU_suF_card rckSU_suσ_toRingHom_apply))

private theorem rckSU_sigma_eq_frobQ : SUσ.toRingHom = frobQ 2 1 :=
  RingHom.ext fun c => by rw [rckSU_suσ_toRingHom_apply, frobQ_apply]

private def rckLemmaHTwE6 (θ : SUF →+* SUF) : Prop :=
  ∀ x ∈ (twistedDatum SUF θ).rootGroup relRoot0121, x ≠ 1 →
    pCoreOf 2 (Subgroup.centralizer ({x} : Set (fixedGroup SUF θ))) ≤
      Subgroup.centralizer ((twistedDatum SUF θ).rootGroup relRoot0121 : Set (fixedGroup SUF θ))

private theorem rckLemmaHTwE6_frobQ : rckLemmaHTwE6 (frobQ 2 1) := by
  intro x hx hx1
  exact rckLemmaHCore_twistedE6 (m := 0) (g := 1) le_rfl
    (relRoot0121_mem_roots (frobQ 2 1)) (relRoot0121_not_long (frobQ 2 1)) x hx hx1

private theorem rckLemmaHTwE6_suσ : rckLemmaHTwE6 SUσ.toRingHom := by
  rw [rckSU_sigma_eq_frobQ]
  exact rckLemmaHTwE6_frobQ

private def rckTwE6X_sq (θ : SUF →+* SUF) : Prop :=
  ∀ x ∈ (twistedDatum SUF θ).rootGroup relRoot0121, x * x = 1

private theorem rckTwE6X_sq_frobQ : rckTwE6X_sq (frobQ 2 1) := by
  intro x hx
  exact RootDetectTwE6.twistedRootGroup_mul_self (f := 1) relRoot0121
    (relRoot0121_mem_roots (frobQ 2 1)) x hx

private theorem rckTwE6X_sq_suσ : rckTwE6X_sq SUσ.toRingHom := by
  rw [rckSU_sigma_eq_frobQ]
  exact rckTwE6X_sq_frobQ

private theorem rckTwE6_mem_ker_e6IsogenyT {C : Subgroup (ModGL TwistTag.E6.tag SUF)}
    (π : fixedGroup SUF SUσ.toRingHom →* ↥C)
    (hπval : ∀ z, ((π z : ↥C) : ModGL TwistTag.E6.tag SUF) =
      ((e6IsogenyT SUF (z : e6Data_valid.minGroup SUF) :
        adjointGroup TwistTag.E6.tag SUF) : ModGL TwistTag.E6.tag SUF))
    {x : fixedGroup SUF SUσ.toRingHom} (hx : x ∈ π.ker) :
    (x : e6Data_valid.minGroup SUF) ∈ (e6IsogenyT SUF).ker := by
  rw [MonoidHom.mem_ker] at hx ⊢
  apply Subtype.ext
  have h3 := congrArg (fun y : ↥C => (y : ModGL TwistTag.E6.tag SUF)) hx
  simp only [hπval, OneMemClass.coe_one] at h3
  exact h3

private theorem rckTwE6_odd_card_ker {C : Subgroup (ModGL TwistTag.E6.tag SUF)}
    (π : fixedGroup SUF SUσ.toRingHom →* ↥C)
    (hπval : ∀ z, ((π z : ↥C) : ModGL TwistTag.E6.tag SUF) =
      ((e6IsogenyT SUF (z : e6Data_valid.minGroup SUF) :
        adjointGroup TwistTag.E6.tag SUF) : ModGL TwistTag.E6.tag SUF)) :
    Odd (Nat.card π.ker) := by
  have hle : π.ker.map (fixedGroup SUF SUσ.toRingHom).subtype ≤ (e6IsogenyT SUF).ker := by
    rintro _ ⟨x, hx, rfl⟩
    exact rckTwE6_mem_ker_e6IsogenyT π hπval hx
  have hdvd : Nat.card π.ker ∣ Nat.card (e6IsogenyT SUF).ker := by
    rw [← Subgroup.card_subtype (fixedGroup SUF SUσ.toRingHom) π.ker]
    exact Subgroup.card_dvd_of_le hle
  have h := CFSG.ClassicalInvolution.ModelFacts.ChevAut.e6Isogeny_not_dvd_card_ker SUF (p := 2)
  have hodd : Odd (Nat.card (e6IsogenyT SUF).ker) :=
    Nat.not_even_iff_odd.mp fun he => h (even_iff_two_dvd.mp he)
  exact hodd.of_dvd_nat hdvd

private theorem rckFourLeSix : 4 ≤ 6 := by norm_num

private theorem rckOneLeOne : 1 ≤ 1 := by norm_num

theorem twE6LeviMap_range : twE6LeviMap.range = su6Levi SUσ.toRingHom := by
  have hsurj : Function.Surjective
      (KGTwE6.su6LeviHom (f := 1) rckSU_suF_card rckSU_suσ_toRingHom_apply) :=
    KGTwE6.su6LeviHom_surjective rckSU_suF_card rckSU_suσ_toRingHom_apply
  rw [twE6LeviMap, MonoidHom.range_comp, MonoidHom.range_comp,
    (KGTwE6.su6LeviHom (f := 1) rckSU_suF_card rckSU_suσ_toRingHom_apply).range_eq_top.mpr hsurj,
    Subgroup.map_top, Subgroup.range_subtype,
    Subgroup.map_subgroupOf_eq_of_le (su6Levi_le_graphFixedRootGroup SUσ.toRingHom)]

theorem twE6LeviMap_ker_le_center : twE6LeviMap.ker ≤ Subgroup.center (SUG 6) := by
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  have h1 : KGTwE6.su6LeviHom (f := 1) rckSU_suF_card rckSU_suσ_toRingHom_apply x = 1 := by
    apply (Subgroup.subtype_injective
      ((su6Levi SUσ.toRingHom).subgroupOf (twistedE6RootGroup SUF SUσ)))
    apply Subgroup.subtype_injective (twistedE6RootGroup SUF SUσ)
    show twE6LeviMap x = 1
    exact hx
  exact KGTwE6.ker_su6LeviHom_le_center rckSU_suF_card rckSU_suσ_toRingHom_apply h1

private theorem rckSU_twE6LeviMap_suR_ne_one :
    twE6LeviMap (suR (k := 6) (by norm_num)) ≠ 1 := by
  have hodd : Odd (Nat.card twE6LeviMap.ker) :=
    odd_natCard_of_le_center_SU SUσ twE6LeviMap_ker_le_center
  have hord : orderOf (suR (k := 6) (by norm_num)) = 2 :=
    orderOf_eq_prime (p := 2) (hp := ⟨Nat.prime_two⟩) (rckSU_suR_sq (by norm_num))
      (suR_ne_one (by norm_num))
  intro h
  have hmem : suR (k := 6) (by norm_num) ∈ twE6LeviMap.ker := by
    rw [MonoidHom.mem_ker]
    exact h
  have hdvd : orderOf (suR (k := 6) (by norm_num)) ∣ Nat.card twE6LeviMap.ker :=
    Subgroup.orderOf_dvd_natCard _ hmem
  rw [hord] at hdvd
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)

private theorem rckTwE6_suV_map_eq :
    (suV (k := 6) (by norm_num)).map twE6LeviMap =
      ((twistedDatum SUF SUσ.toRingHom).rootGroup relRoot0121).map
        ((twistedE6RootGroup SUF SUσ).subtype.comp
          (F4Pilot.twistedIsogenyC (f := 1) (by norm_num) rckSU_suF_card SUσ.toRingHom
            rckSU_suσ_toRingHom_apply)) := by
  have h1 : (suV (k := 6) (by norm_num)).map twE6LeviMap =
      ((suV (k := 6) (by norm_num)).map
        (((su6Levi SUσ.toRingHom).subgroupOf (twistedE6RootGroup SUF SUσ)).subtype.comp
          (KGTwE6.su6LeviHom (f := 1) rckSU_suF_card rckSU_suσ_toRingHom_apply))).map
        (twistedE6RootGroup SUF SUσ).subtype := by
    rw [twE6LeviMap, ← Subgroup.map_map]
  rw [h1, su6LeviHom_map_suV (hF := rckSU_suF_card) (hσ := rckSU_suσ_toRingHom_apply)]
  exact (Subgroup.map_map (g := (twistedE6RootGroup SUF SUσ).subtype)
    (f := F4Pilot.twistedIsogenyC (f := 1) (by norm_num) rckSU_suF_card SUσ.toRingHom
      rckSU_suσ_toRingHom_apply)
    (K := (twistedDatum SUF SUσ.toRingHom).rootGroup relRoot0121))

private noncomputable def rckTwE6LeviElt (s : SUG 6) : ↥(twistedE6RootGroup SUF SUσ) :=
  (((su6Levi SUσ.toRingHom).subgroupOf (twistedE6RootGroup SUF SUσ)).subtype.comp
    (KGTwE6.su6LeviHom (f := 1) rckSU_suF_card rckSU_suσ_toRingHom_apply)) s

private theorem rckTwE6LeviElt_coe (s : SUG 6) :
    ((rckTwE6LeviElt s : ↥(twistedE6RootGroup SUF SUσ)) : ModGL TwistTag.E6.tag SUF) =
      twE6LeviMap s := rfl

private theorem rckTwE6LeviElt_mem_map {s : SUG 6} (hs : s ∈ suV (k := 6) (by norm_num)) :
    ((rckTwE6LeviElt s : ↥(twistedE6RootGroup SUF SUσ)) : ModGL TwistTag.E6.tag SUF) ∈
      ((twistedDatum SUF SUσ.toRingHom).rootGroup relRoot0121).map
        ((twistedE6RootGroup SUF SUσ).subtype.comp
          (F4Pilot.twistedIsogenyC (f := 1) (by norm_num) rckSU_suF_card SUσ.toRingHom
            rckSU_suσ_toRingHom_apply)) := by
  have h := Subgroup.mem_map_of_mem twE6LeviMap hs
  rw [rckTwE6_suV_map_eq] at h
  exact h

private theorem rckMapK2Bound {G : Type*} [Group G] (ψ : MulAut G) {Y V : Subgroup G}
    {u' r : G} (hψu : ψ u' = r) (hV : V = Y.map ψ.toMonoidHom)
    (hcore : pCoreOf 2 (Subgroup.centralizer ({u'} : Set G)) ≤
      Subgroup.centralizer (Y : Set G)) :
    pCoreOf 2 (Subgroup.centralizer ({r} : Set G)) ≤ Subgroup.normalizer (V : Set G) := by
  have hcent : (Subgroup.centralizer ({u'} : Set G)).map ψ.toMonoidHom =
      Subgroup.centralizer ({r} : Set G) := by
    rw [CFSG.GroupTheory.map_centralizer_eq_of_mulEquiv ψ ({u'} : Set G), Set.image_singleton]
    rw [show ψ.toMonoidHom u' = r from hψu]
  have hcore' : pCoreOf 2 (Subgroup.centralizer ({r} : Set G)) =
      (pCoreOf 2 (Subgroup.centralizer ({u'} : Set G))).map ψ.toMonoidHom := by
    rw [← hcent, GGRootNorm.pCoreOf_map_mulEquiv]
  have hψY : (Subgroup.centralizer (Y : Set G)).map ψ.toMonoidHom =
      Subgroup.centralizer (V : Set G) := by
    have himg : ψ.toMonoidHom '' (Y : Set G) = (V : Set G) := by
      rw [hV]
      rfl
    rw [CFSG.GroupTheory.map_centralizer_eq_of_mulEquiv ψ (Y : Set G), himg]
  rw [hcore']
  exact (Subgroup.map_mono hcore).trans (hψY.le.trans (Subgroup.centralizer_le_normalizer _))

private theorem rckTwE6_map_pCoreOf_centralizer
    {x : ↥(fixedGroup SUF SUσ.toRingHom)} (hxord : orderOf x = 2) :
    (pCoreOf 2 (Subgroup.centralizer ({x} : Set ↥(fixedGroup SUF SUσ.toRingHom)))).map
        (F4Pilot.twistedIsogenyC (f := 1) rckOneLeOne rckSU_suF_card SUσ.toRingHom
          rckSU_suσ_toRingHom_apply) =
      pCoreOf 2 (Subgroup.centralizer
        ({(F4Pilot.twistedIsogenyC (f := 1) rckOneLeOne rckSU_suF_card SUσ.toRingHom
            rckSU_suσ_toRingHom_apply) x} : Set ↥(twistedE6RootGroup SUF SUσ))) := by
  classical
  have hsurj : Function.Surjective
      (F4Pilot.twistedIsogenyC (f := 1) rckOneLeOne rckSU_suF_card SUσ.toRingHom
        rckSU_suσ_toRingHom_apply) :=
    F4Pilot.twistedIsogenyC_surjective (f := 1) rckOneLeOne rckSU_suF_card
      SUσ.toRingHom rckSU_suσ_toRingHom_apply
  have hker : (F4Pilot.twistedIsogenyC (f := 1) rckOneLeOne rckSU_suF_card SUσ.toRingHom
      rckSU_suσ_toRingHom_apply).ker = Subgroup.center ↥(fixedGroup SUF SUσ.toRingHom) :=
    F4Pilot.ker_twistedIsogenyC (f := 1) rckOneLeOne rckSU_suF_card SUσ.toRingHom
      rckSU_suσ_toRingHom_apply
  have hodd : Odd (Nat.card (F4Pilot.twistedIsogenyC (f := 1) rckOneLeOne rckSU_suF_card
      SUσ.toRingHom rckSU_suσ_toRingHom_apply).ker) :=
    rckTwE6_odd_card_ker _
      (fun z => F4Pilot.coe_twistedIsogenyC (f := 1) rckOneLeOne rckSU_suF_card
        SUσ.toRingHom rckSU_suσ_toRingHom_apply z)
  have hcent := OddKernelInvolutions.image_centralizer
    (F4Pilot.twistedIsogenyC (f := 1) rckOneLeOne rckSU_suF_card SUσ.toRingHom
      rckSU_suσ_toRingHom_apply) hsurj hodd x hxord
  have hM : (F4Pilot.twistedIsogenyC (f := 1) rckOneLeOne rckSU_suF_card SUσ.toRingHom
      rckSU_suσ_toRingHom_apply).ker ≤
      Subgroup.centralizer ({x} : Set ↥(fixedGroup SUF SUσ.toRingHom)) :=
    hker.le.trans (Subgroup.center_le_centralizer _)
  rw [LieKnownR2.map_pCoreOf_eq_of_odd_central_ker hker.le hodd hM, hcent]

private theorem rckTwE6X_orderOf {x : ↥(fixedGroup SUF SUσ.toRingHom)}
    (hxX : x ∈ (twistedDatum SUF SUσ.toRingHom).rootGroup relRoot0121) (hx1 : x ≠ 1) :
    orderOf x = 2 :=
  orderOf_eq_prime (p := 2) (hp := ⟨Nat.prime_two⟩)
    ((pow_two x).trans (rckTwE6X_sq_suσ x hxX)) hx1

private theorem rckTwE6_pCoreOf_centralizer_le_of_mem
    (π : ↥(fixedGroup SUF SUσ.toRingHom) →* ↥(twistedE6RootGroup SUF SUσ))
    (hπ : π = F4Pilot.twistedIsogenyC (f := 1) rckOneLeOne rckSU_suF_card SUσ.toRingHom
      rckSU_suσ_toRingHom_apply)
    {x : ↥(fixedGroup SUF SUσ.toRingHom)}
    (hxX : x ∈ (twistedDatum SUF SUσ.toRingHom).rootGroup relRoot0121) (hx1 : x ≠ 1) :
    pCoreOf 2 (Subgroup.centralizer ({π x} : Set ↥(twistedE6RootGroup SUF SUσ))) ≤
      Subgroup.centralizer (((twistedDatum SUF SUσ.toRingHom).rootGroup relRoot0121).map π :
        Set ↥(twistedE6RootGroup SUF SUσ)) := by
  subst hπ
  exact (rckTwE6_map_pCoreOf_centralizer (rckTwE6X_orderOf hxX hx1)).symm.le.trans
    (rckMap_le_centralizer_map _ (rckLemmaHTwE6_suσ x hxX hx1))

private theorem rckTwE6_pCoreOf_centralizer_suR_le :
    pCoreOf 2 (Subgroup.centralizer
      ({rckTwE6LeviElt (suR (k := 6) rckFourLeSix)} :
        Set ↥(twistedE6RootGroup SUF SUσ))) ≤
      Subgroup.centralizer
        ((((twistedDatum SUF SUσ.toRingHom).rootGroup relRoot0121).map
          (F4Pilot.twistedIsogenyC (f := 1) rckOneLeOne rckSU_suF_card SUσ.toRingHom
            rckSU_suσ_toRingHom_apply) : Subgroup ↥(twistedE6RootGroup SUF SUσ)) :
          Set ↥(twistedE6RootGroup SUF SUσ)) := by
  classical
  obtain ⟨π, hπ⟩ : ∃ π : ↥(fixedGroup SUF SUσ.toRingHom) →* ↥(twistedE6RootGroup SUF SUσ),
      π = F4Pilot.twistedIsogenyC (f := 1) rckOneLeOne rckSU_suF_card SUσ.toRingHom
        rckSU_suσ_toRingHom_apply := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X : Subgroup ↥(fixedGroup SUF SUσ.toRingHom),
      X = (twistedDatum SUF SUσ.toRingHom).rootGroup relRoot0121 := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : Subgroup ↥(twistedE6RootGroup SUF SUσ), Y = X.map π := ⟨_, rfl⟩
  have hu'coe : ((rckTwE6LeviElt (suR (k := 6) rckFourLeSix) :
      ↥(twistedE6RootGroup SUF SUσ)) : ModGL TwistTag.E6.tag SUF) =
      twE6LeviMap (suR (k := 6) rckFourLeSix) := rckTwE6LeviElt_coe _
  have hu'X : ((rckTwE6LeviElt (suR (k := 6) rckFourLeSix) :
      ↥(twistedE6RootGroup SUF SUσ)) : ModGL TwistTag.E6.tag SUF) ∈ X.map
      ((twistedE6RootGroup SUF SUσ).subtype.comp π) := by
    have h := rckTwE6LeviElt_mem_map (s := suR (k := 6) rckFourLeSix)
      (suR_mem_suV rckFourLeSix)
    rw [hX, hπ]
    exact h
  obtain ⟨x, hxX, hx_eq⟩ := Subgroup.mem_map.mp hu'X
  have hxX' : x ∈ (twistedDatum SUF SUσ.toRingHom).rootGroup relRoot0121 := by
    rw [hX] at hxX
    exact hxX
  have hπx : π x = rckTwE6LeviElt (suR (k := 6) rckFourLeSix) := Subtype.ext hx_eq
  have hx1 : x ≠ 1 := by
    intro hx0
    apply rckSU_twE6LeviMap_suR_ne_one
    rw [← hu'coe, ← hπx, hx0, map_one, Subgroup.coe_one]
  have hcore := rckTwE6_pCoreOf_centralizer_le_of_mem π hπ hxX' hx1
  rw [hπx] at hcore
  rw [← hπ]
  exact hcore

private theorem rckTwE6_eq_map_of_conj
    {c : ModGL TwistTag.E6.tag SUF} (g : SUG 6)
    {V : Subgroup ↥(twistedE6RootGroup SUF SUσ)}
    (hV : V.map ((MulAut.conj c).toMonoidHom.comp (twistedE6RootGroup SUF SUσ).subtype) =
      (suV (k := 6) rckFourLeSix).map (twE6LeviMap.comp (MulAut.conj g).toMonoidHom))
    {y : ModGL TwistTag.E6.tag SUF} (hy : y = c⁻¹ * twE6LeviMap g)
    {ψ : MulAut ↥(twistedE6RootGroup SUF SUσ)}
    (hψcoe : ∀ v : ↥(twistedE6RootGroup SUF SUσ),
      ((ψ v : ↥(twistedE6RootGroup SUF SUσ)) : ModGL TwistTag.E6.tag SUF) =
        y * (v : ModGL TwistTag.E6.tag SUF) * y⁻¹) :
    V = (((twistedDatum SUF SUσ.toRingHom).rootGroup relRoot0121).map
      (F4Pilot.twistedIsogenyC (f := 1) rckOneLeOne rckSU_suF_card SUσ.toRingHom
        rckSU_suσ_toRingHom_apply)).map ψ.toMonoidHom := by
  classical
  obtain ⟨π, hπ⟩ : ∃ π : ↥(fixedGroup SUF SUσ.toRingHom) →* ↥(twistedE6RootGroup SUF SUσ),
      π = F4Pilot.twistedIsogenyC (f := 1) rckOneLeOne rckSU_suF_card SUσ.toRingHom
        rckSU_suσ_toRingHom_apply := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X : Subgroup ↥(fixedGroup SUF SUσ.toRingHom),
      X = (twistedDatum SUF SUσ.toRingHom).rootGroup relRoot0121 := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : Subgroup ↥(twistedE6RootGroup SUF SUσ), Y = X.map π := ⟨_, rfl⟩
  have hVeq : V = Y.map ψ.toMonoidHom := by
    apply le_antisymm
    · intro v hv
      have hcv : c * (v : ModGL TwistTag.E6.tag SUF) * c⁻¹ ∈
          (suV (k := 6) rckFourLeSix).map
            (twE6LeviMap.comp (MulAut.conj g).toMonoidHom) := by
        have h := Subgroup.mem_map_of_mem
          ((MulAut.conj c).toMonoidHom.comp (twistedE6RootGroup SUF SUσ).subtype) hv
        rw [hV] at h
        simpa using h
      obtain ⟨s, hs, hs_eq⟩ := Subgroup.mem_map.mp hcv
      have hgs : twE6LeviMap g * twE6LeviMap s * (twE6LeviMap g)⁻¹ =
          c * (v : ModGL TwistTag.E6.tag SUF) * c⁻¹ := by
        rw [← hs_eq]
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
          map_mul, map_inv]
      have hφs : rckTwE6LeviElt s ∈ Y := by
        rw [hY]
        obtain ⟨w, hw, hw_eq⟩ := Subgroup.mem_map.mp
          (rckTwE6LeviElt_mem_map (s := s) hs)
        rw [show rckTwE6LeviElt s = π w from
          Subtype.ext (by rw [hπ]; exact hw_eq.symm)]
        rw [← hX] at hw
        exact Subgroup.mem_map_of_mem π hw
      refine Subgroup.mem_map.mpr ⟨rckTwE6LeviElt s, hφs, ?_⟩
      apply Subtype.ext
      change ((ψ (rckTwE6LeviElt s) : ↥(twistedE6RootGroup SUF SUσ)) :
        ModGL TwistTag.E6.tag SUF) = (v : ModGL TwistTag.E6.tag SUF)
      rw [hψcoe (rckTwE6LeviElt s), rckTwE6LeviElt_coe, hy]
      calc c⁻¹ * twE6LeviMap g * twE6LeviMap s * (c⁻¹ * twE6LeviMap g)⁻¹
          = c⁻¹ * (twE6LeviMap g * twE6LeviMap s * (twE6LeviMap g)⁻¹) * c := by group
        _ = c⁻¹ * (c * (v : ModGL TwistTag.E6.tag SUF) * c⁻¹) * c := by rw [hgs]
        _ = (v : ModGL TwistTag.E6.tag SUF) := by group
    · intro v hv
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hv
      rw [hY] at hz
      obtain ⟨x', hx', hx'_eq⟩ := Subgroup.mem_map.mp hz
      have hzφ : ∃ s ∈ suV (k := 6) rckFourLeSix,
          twE6LeviMap s = (z : ModGL TwistTag.E6.tag SUF) := by
        have h : (z : ModGL TwistTag.E6.tag SUF) ∈
            (suV (k := 6) rckFourLeSix).map twE6LeviMap := by
          rw [rckTwE6_suV_map_eq, ← hx'_eq, ← hX, ← hπ, ← Subgroup.map_map]
          exact Subgroup.mem_map_of_mem (twistedE6RootGroup SUF SUσ).subtype
            (Subgroup.mem_map_of_mem π hx')
        exact Subgroup.mem_map.mp h
      obtain ⟨s, hs, hs_eq⟩ := hzφ
      have hgs : (twE6LeviMap.comp (MulAut.conj g).toMonoidHom) s =
          c * ((ψ z : ↥(twistedE6RootGroup SUF SUσ)) : ModGL TwistTag.E6.tag SUF) * c⁻¹ := by
        rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_mul,
          map_inv, hψcoe z, hy, hs_eq]
        group
      have hmem : c * ((ψ z : ↥(twistedE6RootGroup SUF SUσ)) : ModGL TwistTag.E6.tag SUF) *
          c⁻¹ ∈ V.map
            ((MulAut.conj c).toMonoidHom.comp (twistedE6RootGroup SUF SUσ).subtype) := by
        rw [hV]
        exact Subgroup.mem_map.mpr ⟨s, hs, hgs⟩
      obtain ⟨w, hw, hw_eq⟩ := Subgroup.mem_map.mp hmem
      have hwψ : (w : ModGL TwistTag.E6.tag SUF) =
          ((ψ z : ↥(twistedE6RootGroup SUF SUσ)) : ModGL TwistTag.E6.tag SUF) := by
        have h := hw_eq
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
        exact mul_left_cancel (mul_right_cancel h)
      rw [show (MulEquiv.toMonoidHom ψ) z = w from Subtype.ext hwψ.symm]
      exact hw
  rw [hY] at hVeq
  rw [← hX, ← hπ]
  exact hVeq

theorem pCoreOf_centralizer_le_normalizer_of_twE6LeviMap
    {c : ModGL TwistTag.E6.tag SUF} (hc : c ∈ twistedE6InndiagGL SUF SUσ)
    {V : Subgroup ↥(twistedE6RootGroup SUF SUσ)} {r : ↥(twistedE6RootGroup SUF SUσ)} (g : SUG 6)
    (hr : c * (r : ModGL TwistTag.E6.tag SUF) * c⁻¹ =
      twE6LeviMap (g * suR (k := 6) (by norm_num) * g⁻¹))
    (hV : V.map ((MulAut.conj c).toMonoidHom.comp (twistedE6RootGroup SUF SUσ).subtype) =
      (suV (k := 6) (by norm_num)).map (twE6LeviMap.comp (MulAut.conj g).toMonoidHom)) :
    pCoreOf 2 (Subgroup.centralizer ({r} : Set ↥(twistedE6RootGroup SUF SUσ))) ≤
      Subgroup.normalizer (V : Set ↥(twistedE6RootGroup SUF SUσ)) := by
  classical
  have hφg : twE6LeviMap g ∈ twistedE6RootGroup SUF SUσ := by
    rw [← rckTwE6LeviElt_coe g]
    exact (rckTwE6LeviElt g).2
  have hcN : c ∈
      Subgroup.normalizer (twistedE6RootGroup SUF SUσ : Set (ModGL TwistTag.E6.tag SUF)) :=
    twistedE6InndiagGL_le_normalizer SUF SUσ hc
  obtain ⟨y, hy⟩ : ∃ y : ModGL TwistTag.E6.tag SUF, y = c⁻¹ * twE6LeviMap g := ⟨_, rfl⟩
  have hyN : y ∈
      Subgroup.normalizer (twistedE6RootGroup SUF SUσ : Set (ModGL TwistTag.E6.tag SUF)) := by
    rw [hy]
    exact mul_mem (inv_mem hcN) (Subgroup.le_normalizer hφg)
  obtain ⟨ψ, hψ⟩ : ∃ ψ : MulAut ↥(twistedE6RootGroup SUF SUσ),
      ψ = (twistedE6RootGroup SUF SUσ).normalizerMonoidHom ⟨y, hyN⟩ := ⟨_, rfl⟩
  have hψcoe : ∀ v : ↥(twistedE6RootGroup SUF SUσ),
      ((ψ v : ↥(twistedE6RootGroup SUF SUσ)) : ModGL TwistTag.E6.tag SUF) =
        y * (v : ModGL TwistTag.E6.tag SUF) * y⁻¹ := by
    intro v
    rw [hψ]
    exact GGRootNorm.coe_normalizerMonoidHom hyN v
  have hψu' : ψ (rckTwE6LeviElt (suR (k := 6) rckFourLeSix)) = r := by
    apply Subtype.ext
    rw [hψcoe, rckTwE6LeviElt_coe, hy]
    have hφ : twE6LeviMap (g * suR (k := 6) rckFourLeSix * g⁻¹) =
        twE6LeviMap g * twE6LeviMap (suR (k := 6) rckFourLeSix) * (twE6LeviMap g)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    calc c⁻¹ * twE6LeviMap g * twE6LeviMap (suR (k := 6) rckFourLeSix) *
          (c⁻¹ * twE6LeviMap g)⁻¹
        = c⁻¹ * (twE6LeviMap g * twE6LeviMap (suR (k := 6) rckFourLeSix) *
            (twE6LeviMap g)⁻¹) * c := by group
      _ = c⁻¹ * twE6LeviMap (g * suR (k := 6) rckFourLeSix * g⁻¹) * c := by rw [← hφ]
      _ = c⁻¹ * (c * (r : ModGL TwistTag.E6.tag SUF) * c⁻¹) * c := by rw [← hr]
      _ = (r : ModGL TwistTag.E6.tag SUF) := by group
  exact rckMapK2Bound ψ hψu'
    (rckTwE6_eq_map_of_conj (g := g) hV hy hψcoe)
    (rckTwE6_pCoreOf_centralizer_suR_le)

end Root

end CFSG.StandardType.RCKC1
