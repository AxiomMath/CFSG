module

public import CFSG.LocalAnalysis.StandardType.GGSporKStepOne
import CFSG.GroupTheory.Fitting.LayerTopBot

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly
open scoped commutatorElement

theorem ggSporK_pPrimeCore_eq_bot_B {W : Type} [Group W] [Finite W] (ha : BSevenComp W)
    (hc : BSevenSpread W) {H E : Subgroup W} (hyp : GGHypThreeSixteenFlat 7 H E) :
    LargeEvenPPrimeCore 7 ↥H = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hEH : E ≤ H := hyp.1.2.2.2.2.1
  have hE7 : IsElemAbelian 7 E := hyp.1.2.2.1
  have hEcard : Nat.card E = 7 ^ 2 := hyp.1.2.2.2.1
  have hfus : GGControlsStrongFusion H E := hyp.1.2.2.2.2
  set N : Subgroup ↥H := LargeEvenPPrimeCore 7 ↥H with hN
  have hNn : N.Normal := inferInstance
  have hNcop : Nat.Coprime 7 (Nat.card N) := CFSG.pPrimeCore_coprime_card
  let R : Subgroup W := N.map H.subtype
  have hRcard : Nat.card R = Nat.card N :=
    (Nat.card_congr (N.equivMapOfInjective H.subtype H.subtype_injective).toEquiv).symm
  have hRcop : Nat.Coprime 7 (Nat.card R) := by rw [hRcard]; exact hNcop
  have hR : ¬ 7 ∣ Nat.card R := fun hd =>
    (Nat.Prime.one_lt (Fact.out : Nat.Prime 7)).ne' (Nat.Coprime.eq_one_of_dvd hRcop hd)
  have hRnorm : ∀ h ∈ H, ∀ r ∈ R, h * r * h⁻¹ ∈ R := by
    intro h hh r hr
    obtain ⟨n, hn, rfl⟩ := hr
    exact ⟨⟨h, hh⟩ * n * ⟨h, hh⟩⁻¹, hNn.conj_mem n hn ⟨h, hh⟩, rfl⟩
  have hER : ∀ e ∈ E, ∀ r ∈ R, e * r * e⁻¹ ∈ R := fun e he r hr => hRnorm e (hEH he) r hr
  have hkey : ∀ e ∈ E, e ≠ 1 → ∃ J : Subgroup W,
      (∀ J' : Subgroup W, IsComponentOf J' (Subgroup.centralizer {e}) → J' = J) ∧
      Nat.card ↥(J ⊓ Subgroup.centralizer (J : Set W)) = 2 ∧
      R ⊓ Subgroup.centralizer {e} ≤ J ⊓ Subgroup.centralizer (J : Set W) ∧
      (J ⊓ Subgroup.centralizer (J : Set W)).subgroupOf (Subgroup.centralizer {e}) =
        LargeEvenPPrimeCore 7 ↥(Subgroup.centralizer ({e} : Set W)) := by
    intro e he he1
    have he7 : orderOf e = 7 := orderOf_eq_prime (hE7.2 e he) he1
    obtain ⟨J, -, hJu, hJc, hJP⟩ := ha e he7
    refine ⟨J, hJu, hJc, ?_, hJP.symm⟩
    have hCH : Subgroup.centralizer ({e} : Set W) ≤ H := hfus.centralizer_le he he1
    set C : Subgroup W := Subgroup.centralizer {e} with hCdef
    have hTle : R ⊓ C ≤ C := inf_le_right
    set T' : Subgroup ↥C := (R ⊓ C).subgroupOf C with hT'
    have hT'n : T'.Normal := by
      refine ⟨fun x hx c => ?_⟩
      rw [hT', Subgroup.mem_subgroupOf] at hx ⊢
      obtain ⟨hxR, hxC⟩ := Subgroup.mem_inf.mp hx
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · simpa using hRnorm (c : W) (hCH c.2) _ hxR
      · simpa using C.mul_mem (C.mul_mem c.2 hxC) (C.inv_mem c.2)
    have hT'card : Nat.Coprime 7 (Nat.card T') := by
      have hdvd : Nat.card T' ∣ Nat.card R := by
        rw [hT', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTle).toEquiv]
        exact Subgroup.card_dvd_of_le inf_le_left
      exact Nat.Coprime.coprime_dvd_right hdvd hRcop
    have hsub : T' ≤ CFSG.pPrimeCore 7 ↥C := le_sSup ⟨hT'n, hT'card⟩
    have hsub' : T' ≤ (J ⊓ Subgroup.centralizer (J : Set W)).subgroupOf C := by
      rw [← hJP]; exact hsub
    intro x hx
    have hxT : (⟨x, hx.2⟩ : ↥C) ∈ T' := by
      rw [hT', Subgroup.mem_subgroupOf]
      exact hx
    exact Subgroup.mem_subgroupOf.mp (hsub' hxT)
  by_contra hNne
  have hRne : R ≠ ⊥ := fun h =>
    hNne ((Subgroup.map_eq_bot_iff_of_injective N H.subtype_injective).mp h)
  have hex : ∃ e₀ ∈ E, e₀ ≠ 1 ∧ R ⊓ Subgroup.centralizer {e₀} ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    exact hRne (pPrimeCore_eq_bot_of_centralizers hE7 hEcard hR hER hcon)
  obtain ⟨e₀, he₀E, he₀1, hRC0⟩ := hex
  obtain ⟨J₀, hJ₀u, hJ₀c, hRCle, hJ₀P⟩ := hkey e₀ he₀E he₀1
  obtain ⟨t, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hRC0
  have htR : (t : W) ∈ R := (Subgroup.mem_inf.mp t.2).1
  have htC : (t : W) ∈ Subgroup.centralizer ({e₀} : Set W) := (Subgroup.mem_inf.mp t.2).2
  have ht1' : (t : W) ≠ 1 := fun h => ht1 (Subtype.ext h)
  have htZ : (t : W) ∈ J₀ ⊓ Subgroup.centralizer (J₀ : Set W) := hRCle t.2
  have hZn : ((J₀ ⊓ Subgroup.centralizer (J₀ : Set W)).subgroupOf
      (Subgroup.centralizer {e₀})).Normal := by
    rw [hJ₀P]; infer_instance
  have hcentral : ∀ c ∈ Subgroup.centralizer ({e₀} : Set W), c * (t : W) * c⁻¹ = (t : W) := by
    intro c hc'
    have hmem : (⟨(t : W), htC⟩ : ↥(Subgroup.centralizer ({e₀} : Set W))) ∈
        (J₀ ⊓ Subgroup.centralizer (J₀ : Set W)).subgroupOf (Subgroup.centralizer {e₀}) :=
      Subgroup.mem_subgroupOf.mpr htZ
    have hconj := hZn.conj_mem _ hmem ⟨c, hc'⟩
    have hconjZ : c * (t : W) * c⁻¹ ∈ J₀ ⊓ Subgroup.centralizer (J₀ : Set W) := by
      simpa using Subgroup.mem_subgroupOf.mp hconj
    have h2 := (Nat.card_eq_two_iff' (1 : ↥(J₀ ⊓ Subgroup.centralizer (J₀ : Set W)))).mp hJ₀c
    have hne1 : (⟨c * (t : W) * c⁻¹, hconjZ⟩ : ↥(J₀ ⊓ Subgroup.centralizer (J₀ : Set W))) ≠ 1 := by
      intro h
      have h' : c * (t : W) * c⁻¹ = 1 := congrArg Subtype.val h
      apply ht1'
      have := congrArg (fun z => c⁻¹ * z * c) h'
      simpa [mul_assoc] using this
    have hne2 : (⟨(t : W), htZ⟩ : ↥(J₀ ⊓ Subgroup.centralizer (J₀ : Set W))) ≠ 1 := fun h =>
      ht1' (congrArg Subtype.val h)
    exact congrArg Subtype.val (h2.unique hne1 hne2)
  have hall : ∀ e ∈ E, e ≠ 1 → ∀ J : Subgroup W, IsComponentOf J (Subgroup.centralizer {e}) →
      (t : W) ∈ J ⊓ Subgroup.centralizer (J : Set W) := by
    intro e he he1 J hJ
    obtain ⟨Je, hJeu, -, hRCe, -⟩ := hkey e he he1
    have heC : e ∈ Subgroup.centralizer ({e₀} : Set W) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (congrArg Subtype.val (hE7.1.is_comm.comm ⟨e₀, he₀E⟩ ⟨e, he⟩)).symm
    have hte : (t : W) ∈ Subgroup.centralizer ({e} : Set W) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := hcentral e heC
      exact (mul_inv_eq_iff_eq_mul.mp h1).symm
    rw [hJeu J hJ]
    exact hRCe ⟨htR, hte⟩
  exact hc E hE7 (by rw [hEcard]; norm_num) ⟨t, ht1', hall⟩

private theorem gkb2_fittingSubgroup_le_pCore_sup_pPrimeCore {G : Type*} [Group G] [Finite G]
    (p : ℕ) :
    CFSG.fittingSubgroup G ≤ CFSG.pCore p G ⊔ CFSG.pPrimeCore p G := by
  rw [CFSG.LocalCores.fittingSubgroup_eq_iSup_pCore]
  refine iSup_le fun q => ?_
  have hqprime : Nat.Prime (q : ℕ) := Nat.prime_of_mem_primeFactors q.2
  by_cases hqp : (q : ℕ) = p
  · rw [hqp]
    exact le_sup_left
  · by_cases hdvd : (q : ℕ) ∣ p
    · have hpgroup : IsPGroup p (CFSG.pCore (q : ℕ) G) :=
        (CFSG.pCore_isPGroup (p := (q : ℕ)) (G := G)).mono hdvd
      have hle : CFSG.pCore (q : ℕ) G ≤ CFSG.pCore p G :=
        le_sSup (show CFSG.pCore (q : ℕ) G ∈
          {K : Subgroup G | K.Normal ∧ IsPGroup p K} from
            ⟨CFSG.pCore_normal, hpgroup⟩)
      exact hle.trans le_sup_left
    · haveI : Fact (Nat.Prime (q : ℕ)) := ⟨hqprime⟩
      have hcop : Nat.Coprime p (Nat.card (CFSG.pCore (q : ℕ) G)) := by
        obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := (q : ℕ)) (G := G)).exists_card_eq
        rw [hn]
        exact Nat.Prime.coprime_pow_of_not_dvd hqprime hdvd
      have hle : CFSG.pCore (q : ℕ) G ≤ CFSG.pPrimeCore p G :=
        le_sSup (show CFSG.pCore (q : ℕ) G ∈
          {K : Subgroup G | K.Normal ∧ Nat.Coprime p (Nat.card K)} from
            ⟨CFSG.pCore_normal, hcop⟩)
      exact hle.trans le_sup_right

theorem ggSporK_pCore_eq_bot_B {W : Type} [Group W] [Finite W] (ha : BSevenComp W)
    (h49 : (Nat.card W).factorization 7 = 2) {H E : Subgroup W}
    (hyp : GGHypThreeSixteenFlat 7 H E) (hP' : LargeEvenPPrimeCore 7 ↥H = ⊥)
    (hJ : ∃ J : Subgroup W, IsComponentOf J H) : CFSG.pCore 7 ↥H = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  by_contra hP0bot
  set P0 : Subgroup ↥H := CFSG.pCore 7 ↥H with hP0def
  have hP0ne : P0 ≠ ⊥ := by rwa [hP0def]
  have hP0normal : P0.Normal := by rw [hP0def]; exact CFSG.pCore_normal
  have hP0p : IsPGroup 7 P0 := by rw [hP0def]; exact CFSG.pCore_isPGroup
  set P0map : Subgroup W := P0.map H.subtype with hP0mapdef
  have hEH : E ≤ H := hyp.1.2.2.2.2.1
  have hHfac : (Nat.card ↥H).factorization 7 = 2 := by
    have hWne : Nat.card W ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
    have hHne : Nat.card ↥H ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
    have hdvd : Nat.card ↥H ∣ Nat.card W := Subgroup.card_subgroup_dvd_card H
    have hle := (Nat.factorization_le_iff_dvd hHne hWne).mpr hdvd 7
    rw [h49] at hle
    have hdiv : 7 ^ 2 ∣ Nat.card ↥H := by
      rw [← hyp.1.2.2.2.1]
      exact Subgroup.card_dvd_of_le hEH
    have hge : 2 ≤ (Nat.card ↥H).factorization 7 :=
      (Nat.Prime.pow_dvd_iff_le_factorization (by norm_num : Nat.Prime 7) hHne).mp hdiv
    omega
  have hcardEsub : Nat.card (E.subgroupOf H) = 7 ^ (Nat.card ↥H).factorization 7 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEH).toEquiv, hyp.1.2.2.2.1, hHfac]
  haveI : P0.Normal := hP0normal
  have hP0_le_Esub : P0 ≤ E.subgroupOf H := by
    simpa only [Sylow.coe_ofCard] using
      hP0p.le_sylow_of_normal (Sylow.ofCard (E.subgroupOf H) hcardEsub)
  have hP0map_le_E : P0map ≤ E := by
    intro x hx
    rw [hP0mapdef] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact Subgroup.mem_subgroupOf.mp (hP0_le_Esub hy)
  have hP0map_ne : P0map ≠ ⊥ := by
    rw [hP0mapdef]
    intro h
    exact hP0ne ((Subgroup.map_eq_bot_iff_of_injective P0 H.subtype_injective).mp h)
  obtain ⟨e, he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hP0map_ne
  have heP0map : (e : W) ∈ P0map := e.2
  have he1W : (e : W) ≠ 1 := fun h => he1 (Subtype.ext h)
  have heE : (e : W) ∈ E := hP0map_le_E heP0map
  have hord : orderOf (e : W) = 7 := by
    have hep : (e : W) ^ 7 = 1 := hyp.1.2.2.1.2 (e : W) heE
    have hdvd : orderOf (e : W) ∣ 7 := orderOf_dvd_iff_pow_eq_one.mpr hep
    rcases (show Nat.Prime 7 by norm_num).eq_one_or_self_of_dvd _ hdvd with h1 | h7
    · exact absurd h1 (by rw [orderOf_eq_one_iff]; exact he1W)
    · exact h7
  have hC : Subgroup.centralizer ({(e : W)} : Set W) ≤ H :=
    hyp.1.2.2.2.2.centralizer_le heE he1W
  obtain ⟨J, hJcomp⟩ := hJ
  have hJH : J ≤ H := hJcomp.1
  have hP0solv : Group.IsSolvable P0 := by
    haveI : Group.IsNilpotent P0 := hP0p.isNilpotent
    infer_instance
  have hJsubW : CFSG.Assembly.IsSubnormal (J.subgroupOf H) ⊤ :=
    CFSG.Assembly.IsSubnormal.of_mathlib
      ((CFSG.Assembly.IsSubnormal.iff_subgroupOf hJH).mp hJcomp.2.1)
  have hJqsW : CFSG.Assembly.IsQuasisimple ↥(J.subgroupOf H) :=
    CFSG.Assembly.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJH) hJcomp.2.2
  have hJcompN : CFSG.IsComponent (J.subgroupOf H) :=
    (CFSG.isComponent_iff_open (J.subgroupOf H)).mpr
      (CFSG.Assembly.isComponentOf_iff_open.mp ⟨le_top, hJsubW, hJqsW⟩)
  have hcomm : ⁅J.subgroupOf H, P0⁆ = ⊥ :=
    (CFSG.LocalCores.component_solvable_centralizer hP0solv hP0normal.isSubnormal).1
      (J.subgroupOf H) hJcompN
  have hJcentral : J ≤ Subgroup.centralizer (P0map : Set W) := by
    intro j hj
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨y', hy', rfl⟩ := hy
    have hj' : (⟨j, hJH hj⟩ : ↥H) ∈ J.subgroupOf H := by
      rw [Subgroup.mem_subgroupOf]; exact hj
    have h1 : ⁅(⟨j, hJH hj⟩ : ↥H), y'⁆ ∈ ⁅J.subgroupOf H, P0⁆ :=
      Subgroup.commutator_mem_commutator hj' hy'
    rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact (congrArg Subtype.val h1).symm
  have hJ_cent_e : J ≤ Subgroup.centralizer ({(e : W)} : Set W) := by
    intro j hj
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((Subgroup.mem_centralizer_iff.mp (hJcentral hj)) (e : W) heP0map).symm
  have hJcompC : IsComponentOf J (Subgroup.centralizer ({(e : W)} : Set W)) :=
    hJcomp.of_le_of_le hJ_cent_e hC
  obtain ⟨Je, hJeC, hJeuniq, hJecard, hJeP'⟩ := ha (e : W) hord
  have hJeq : J = Je := hJeuniq J hJcompC
  have hZJcard : Nat.card ↥(J ⊓ Subgroup.centralizer (J : Set W)) = 2 := by
    rw [hJeq]; exact hJecard
  have hZJne : J ⊓ Subgroup.centralizer (J : Set W) ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hZJcard
    norm_num at hZJcard
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZJne
  have hzJ : (z : W) ∈ J := (Subgroup.mem_inf.mp z.2).1
  have hzC : (z : W) ∈ Subgroup.centralizer (J : Set W) := (Subgroup.mem_inf.mp z.2).2
  have hz1W : (z : W) ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hzord : orderOf (z : W) = 2 := by
    have hdvd : orderOf (z : W) ∣ 2 := by
      rw [Subgroup.orderOf_coe z, ← hZJcard]
      exact orderOf_dvd_natCard z
    rcases (show Nat.Prime 2 by norm_num).eq_one_or_self_of_dvd _ hdvd with h1 | h2
    · exact absurd h1 (by rw [orderOf_eq_one_iff]; exact hz1W)
    · exact h2
  set K : Subgroup ↥H := J.subgroupOf H with hKdef
  have hzK : (⟨(z : W), hJH hzJ⟩ : ↥H) ∈ K := by
    rw [hKdef, Subgroup.mem_subgroupOf]; exact hzJ
  have hzH_center : (⟨(z : W), hJH hzJ⟩ : ↥H) ∈ (Subgroup.center ↥K).map K.subtype := by
    refine ⟨⟨⟨(z : W), hJH hzJ⟩, hzK⟩, ?_, rfl⟩
    exact Subgroup.mem_center_iff.mpr (fun y => by
      apply Subtype.ext
      apply Subtype.ext
      simpa using Subgroup.mem_centralizer_iff.mp hzC (((y : ↥K) : ↥H) : W)
        (Subgroup.mem_subgroupOf.mp y.2))
  have hz_layer : (⟨(z : W), hJH hzJ⟩ : ↥H) ∈
      (Subgroup.center (CFSG.layer ↥H)).map (CFSG.layer ↥H).subtype :=
    CFSG.LocalCores.center_component_le_center_layer hJcompN hzH_center
  have hzF : (⟨(z : W), hJH hzJ⟩ : ↥H) ∈ CFSG.fittingSubgroup ↥H :=
    CFSG.WholeGroup.center_layer_le_fittingSubgroup hz_layer
  have hzP0 : (⟨(z : W), hJH hzJ⟩ : ↥H) ∈ P0 := by
    have hle := gkb2_fittingSubgroup_le_pCore_sup_pPrimeCore (G := ↥H) 7
    rw [show CFSG.pPrimeCore 7 ↥H = ⊥ from hP', sup_bot_eq] at hle
    exact hle hzF
  let g : P0 := ⟨⟨(z : W), hJH hzJ⟩, hzP0⟩
  have hg1 : g ≠ 1 := by
    intro h
    exact hz1W (by
      have := congrArg (fun w : P0 => (((w : P0) : ↥H) : W)) h
      simpa [g] using this)
  have hgord : orderOf g = 2 := by
    rw [← Subgroup.orderOf_coe g]
    change orderOf (⟨(z : W), hJH hzJ⟩ : ↥H) = 2
    rw [← Subgroup.orderOf_coe (⟨(z : W), hJH hzJ⟩ : ↥H)]
    exact hzord
  have h7 : 7 ∣ orderOf g := hP0p.dvd_orderOf hg1
  rw [hgord] at h7
  norm_num at h7

end CFSG.StandardType.SporadicShape
