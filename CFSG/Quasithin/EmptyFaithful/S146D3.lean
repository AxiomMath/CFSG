module

public import CFSG.Quasithin.EmptyFaithful.S146D2
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.Quasithin.Background.A3Structure37KeyBase
public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.Background.F6Amalgams
public import CFSG.Quasithin.Background.F6SolvableQuotient
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.EmptyFaithful.S1417Sylow
public import CFSG.Quasithin.EmptyFaithful.S1421L246
public import CFSG.Quasithin.EmptyFaithful.S143Pre
public import CFSG.Quasithin.EmptyFaithful.S146C1
public import CFSG.Quasithin.EmptyFaithful.S146C2
public import CFSG.Quasithin.EmptyFaithful.S146G4
public import CFSG.Quasithin.EmptyFaithful.S146ThreeB
public import CFSG.Quasithin.Vol2.Ch1Faithful
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

section Trace

theorem exists_fixed_mul_of_odd_index_aux {X M : Type*} [Group X] [Finite X] [CommGroup M] [Finite M]
    [MulDistribMulAction X M] (A₀ : Subgroup M) (hM2 : ∀ m : M, m * m = 1) (P : Subgroup X)
    (hP : ¬ 2 ∣ P.index) (a : M) (hPa : ∀ p ∈ P, p • a = a)
    (hA0 : ∀ x : X, (x • a) * a⁻¹ ∈ A₀) :
    ∃ c : M, (∀ x : X, x • c = c) ∧ c * a⁻¹ ∈ A₀ := by
  classical
  have hfin : (MulAction.orbit X a).Finite := Set.toFinite _
  set S : Finset M := hfin.toFinset with hS
  have hmem : ∀ y, y ∈ S ↔ y ∈ MulAction.orbit X a := fun y => hfin.mem_toFinset
  have hcard : S.card = (MulAction.stabilizer X a).index := by
    rw [MulAction.index_stabilizer, Set.ncard_eq_toFinset_card _ hfin]
  have hPC : P ≤ MulAction.stabilizer X a := fun p hp => hPa p hp
  have hodd : Odd S.card := by
    rw [hcard]
    have := Subgroup.index_dvd_of_le hPC
    exact Nat.odd_iff.mpr (by
      rcases Nat.even_or_odd (MulAction.stabilizer X a).index with he | ho
      · exact absurd (he.two_dvd.trans this) hP
      · exact Nat.odd_iff.mp ho)
  obtain ⟨m, hm⟩ := hodd
  refine ⟨∏ y ∈ S, y, ?_, ?_⟩
  · intro x
    have h1 : x • ∏ y ∈ S, y = ∏ y ∈ S, x • y :=
      map_prod (MulDistribMulAction.toMonoidHom M x) _ _
    rw [h1]
    have himg : S.image (fun y => x • y) = S := by
      ext z
      simp only [Finset.mem_image, hmem]
      constructor
      · rintro ⟨y, hy, rfl⟩
        obtain ⟨g, rfl⟩ := hy
        exact ⟨x * g, mul_smul x g a⟩
      · intro hz
        obtain ⟨g, rfl⟩ := hz
        refine ⟨(x⁻¹ * g) • a, ⟨x⁻¹ * g, rfl⟩, ?_⟩
        rw [← mul_smul, mul_inv_cancel_left]
    have hinj : Function.Injective (fun y : M => x • y) := MulAction.injective x
    rw [← Finset.prod_image (f := fun y : M => y) (fun u _ v _ h => hinj h), himg]
  · have h1 : ∏ y ∈ S, (y * a⁻¹) = (∏ y ∈ S, y) * a⁻¹ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, hm]
      congr 1
      have : (a⁻¹) ^ 2 = 1 := by rw [sq, ← mul_inv, hM2, inv_one]
      rw [pow_succ, pow_mul, this, one_pow, one_mul]
    rw [← h1]
    refine Subgroup.prod_mem _ fun y hy => ?_
    obtain ⟨x, rfl⟩ := (hmem y).mp hy
    exact hA0 x

theorem exists_fixed_mul_of_odd_index {X : Type*} [Group X] [Finite X] (A A₀ P : Subgroup X)
    [IsMulCommutative A] (hA2 : ∀ a ∈ A, a * a = 1) (hconj : ∀ x : X, ∀ a ∈ A, x * a * x⁻¹ ∈ A)
    (hP : ¬ 2 ∣ P.index) {a : X} (ha : a ∈ A) (hPa : ∀ p ∈ P, p * a * p⁻¹ = a)
    (hA0 : ∀ x : X, x * a * x⁻¹ * a⁻¹ ∈ A₀) :
    ∃ c ∈ A, (∀ x : X, x * c * x⁻¹ = c) ∧ c * a⁻¹ ∈ A₀ := by
  let _ : CommGroup A := { (inferInstance : Group A) with mul_comm := fun a b => mul_comm' a b }
  let _ : MulDistribMulAction X A :=
    { smul := fun x b => ⟨x * b * x⁻¹, hconj x b b.2⟩
      one_smul := fun b => Subtype.ext (show (1 : X) * b * 1⁻¹ = b by simp)
      mul_smul := fun x y b => Subtype.ext
        (show (x * y) * (b : X) * (x * y)⁻¹ = x * (y * b * y⁻¹) * x⁻¹ by group)
      smul_mul := fun x b b' => Subtype.ext
        (show x * ((b : X) * b') * x⁻¹ = (x * b * x⁻¹) * (x * b' * x⁻¹) by group)
      smul_one := fun x => Subtype.ext (show x * (1 : X) * x⁻¹ = 1 by simp) }
  have hsmul : ∀ (x : X) (b : A), ((x • b : A) : X) = x * b * x⁻¹ := fun x b => rfl
  obtain ⟨c, hc1, hc2⟩ := exists_fixed_mul_of_odd_index_aux (X := X) (M := A) (A₀.subgroupOf A)
    (fun m => Subtype.ext (hA2 m m.2)) P hP ⟨a, ha⟩
    (fun p hp => Subtype.ext (by rw [hsmul]; exact hPa p hp))
    (fun x => by
      rw [Subgroup.mem_subgroupOf]
      have := hA0 x
      simpa [hsmul] using this)
  refine ⟨c, c.2, fun x => ?_, ?_⟩
  · have := congrArg Subtype.val (hc1 x)
    rw [hsmul] at this
    exact this
  · have := Subgroup.mem_subgroupOf.mp hc2
    simpa using this

end Trace

section Module

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

omit [Finite G] in
theorem inv_mul_mem_of_card_four {V Z : Subgroup G} (hZV : Z ≤ V) (hV : Nat.card V = 4)
    (hZ : Nat.card Z = 2) {a b : G} (ha : a ∈ V) (hb : b ∈ V) (haZ : a ∉ Z) (hbZ : b ∉ Z) :
    a⁻¹ * b ∈ Z := by
  have hrel : Z.relIndex V = 2 := by
    have h := Subgroup.relIndex_mul_card Z V
    rw [inf_eq_left.mpr hZV, hV, hZ] at h
    omega
  have hidx : (Z.subgroupOf V).index = 2 := hrel
  have h1 := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨a⁻¹, V.inv_mem ha⟩) (b := ⟨b, hb⟩)).mpr
    (by
      have h2 : (⟨a⁻¹, V.inv_mem ha⟩ : ↥V) ∈ Z.subgroupOf V ↔ (⟨b, hb⟩ : ↥V) ∈ Z.subgroupOf V := by
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
        simp only [inv_mem_iff]
        exact ⟨fun h => absurd h haZ, fun h => absurd h hbZ⟩
      exact h2)
  exact Subgroup.mem_subgroupOf.mp h1

theorem exists_mem_not_mem_of_card_four {V Z : Subgroup G} (hV : Nat.card V = 4)
    (hZ : Nat.card Z = 2) : ∃ v ∈ V, v ∉ Z := by
  by_contra hcon
  push Not at hcon
  have : V ≤ Z := fun v hv => hcon v hv
  have := Subgroup.card_le_of_le (G := G) (H := V) (K := Z) this
  omega

end Module

section Cover

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

omit [Finite G] in
theorem le_normalizer_iSup_commutator {H U : Subgroup G} (hHU : H ≤ Subgroup.normalizer (U : Set G)) :
    H ≤ Subgroup.normalizer ((⨆ K ∈ cComp H, ⁅U, K⁆ : Subgroup G) : Set G) := by
  have key : ∀ g ∈ H, conjSub g (⨆ K ∈ cComp H, ⁅U, K⁆) ≤ ⨆ K ∈ cComp H, ⁅U, K⁆ := by
    intro g hg
    rw [conjSub_iSup]
    refine iSup_le fun K => ?_
    rw [conjSub_iSup]
    refine iSup_le fun hK => ?_
    have hU : conjSub g U = U := A38.map_conj_eq_iff.mpr (hHU hg)
    rw [← conjSub_commutator, hU]
    exact le_iSup₂ (f := fun K (_ : K ∈ cComp H) => ⁅U, K⁆) (conjSub g K) (map_conj_mem_cComp hK hg)
  intro g hg
  apply A38.map_conj_eq_iff.mp
  apply le_antisymm (key g hg)
  have h2 := key g⁻¹ (H.inv_mem hg)
  have h3 := conjSub_mono g h2
  rwa [conjSub_inv_conjSub] at h3

omit [Finite G] in
theorem perfectCore_le_centralizerMod {H U : Subgroup G}
    (hHU : H ≤ Subgroup.normalizer (U : Set G)) (hspan : cCompSpan H = perfectCore H) :
    perfectCore H ≤ centralizerMod (⨆ K ∈ cComp H, ⁅U, K⁆) H U := by
  rw [← hspan]
  show sSup (cComp H) ≤ _
  refine sSup_le fun K hK => ?_
  intro x hx
  have hxH : x ∈ H := le_of_mem_cComp hK hx
  refine ⟨hxH, le_normalizer_iSup_commutator hHU hxH, fun u hu => ?_⟩
  have h1 : ⁅x, u⁆ ∈ ⁅K, U⁆ := Subgroup.commutator_mem_commutator hx hu
  rw [Subgroup.commutator_comm] at h1
  have h2 : ⁅U, K⁆ ≤ ⨆ K' ∈ cComp H, ⁅U, K'⁆ :=
    le_iSup₂ (f := fun K' (_ : K' ∈ cComp H) => ⁅U, K'⁆) K hK
  simpa [commutatorElement_def] using h2 h1

omit [Finite G] in
theorem secMk_mem_of_le_map {A B X : Subgroup G} [(B.subgroupOf A).Normal]
    (W : Subgroup (SecQuot A B)) (hX : X ≤ (W.comap (secMk A B)).map A.subtype) (x : A)
    (hx : (x : G) ∈ X) : secMk A B x ∈ W := by
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp (hX hx)
  have : y = x := Subtype.ext hyx
  subst this
  exact hy

local notation "Nz" => Subgroup.normalizer (quasithinOmegaOneCenter T : Set G)
local notation "Zz" => quasithinOmegaOneCenter T
local notation "Γz" => SecQuot Nz Zz

theorem conc14623_three_cover (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (S : Setting146 G T M) (hB : HypB146 T M) (c19 : Conc14619 T M) (c20 : Conc14620 T M)
    (c21 : ∀ K ∈ cComp (mcOf T), Conc14621 T K) :
    tildeOf Zz (uOfL22 T M) =
      (⨆ K ∈ cComp (mcOf T), tildeOf Zz ⁅uOfL22 T M, K⁆) ⊔
        tildeOf Zz (centralizerMod Zz (uOfL22 T M) (mcOf T)) := by
  have hHTM : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hpc : pCoreOf 2 (mcOf T) ≠ ⊥ := hHTM.1.2
  have hTH : T ≤ mcOf T := hHTM.1.1
  have hTsyl : IsSylowTwoOf T (mcOf T) := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.sylow hTH
  obtain ⟨hone1, hone2⟩ := conc14623_one_of_a3 h37 h38 S hB c19 c20 c21
  have hspan : cCompSpan (mcOf T) = perfectCore (mcOf T) :=
    lemma_1_2_1_one S.hyp.qtke S.hyp.simple S.hyp.nonabelian h39 hpc
  have hNH : Nz = mcOf T := S.normalizer_Z
  have hUN : uOfL22 T M ≤ Nz := S.conjClosure_le_normalizer_Z hHTM
  have hHU : mcOf T ≤ Subgroup.normalizer (uOfL22 T M : Set G) := le_normalizer_conjClosure _ _
  have hZT : Zz ≤ T := (quasithinOmegaOneCenter_le_center T).trans inf_le_left
  have hUel : IsElemAbelian 2 (uOfL22 T M) := S.lemma_14_5_15_two hHTM
  have hTM : T ≤ M := S.hyp.m_max.1.2
  have hVN : M = Subgroup.normalizer (VZ T M : Set G) := S.hyp1281.normalizer_VZ.symm
  have hVcard : Nat.card (VZ T M) = 4 := S.hyp.rank_two
  have hZcard : Nat.card Zz = 2 := S.card_Z
  have hZV : Zz ≤ VZ T M := le_conjClosure _ _
  have hVU : VZ T M ≤ uOfL22 T M := le_conjClosure _ _
  obtain ⟨v₀, hv₀V, hv₀Z⟩ := exists_mem_not_mem_of_card_four hVcard hZcard
  have hV2 : ∀ a ∈ VZ T M, a ∉ Zz → v₀⁻¹ * a ∈ Zz := fun a ha haZ =>
    inv_mul_mem_of_card_four hZV hVcard hZcard hv₀V ha hv₀Z haZ
  have hHN : ∀ g ∈ mcOf T, g ∈ Nz := fun g hg => by rw [hNH]; exact hg
  have hv₀U : v₀ ∈ uOfL22 T M := hVU hv₀V
  have hv₀N : v₀ ∈ Nz := hUN hv₀U
  have hTZ : ∀ t ∈ T, ∀ z ∈ Zz, t * z * t⁻¹ = z := fun t ht z hz => by
    have := Subgroup.mem_centralizer_iff.mp (le_centralizer_quasithinOmegaOneCenter T ht) z hz
    calc t * z * t⁻¹ = (t * z) * t⁻¹ := rfl
      _ = (z * t) * t⁻¹ := by rw [← this]
      _ = z := by group
  have hTV : ∀ t ∈ T, v₀⁻¹ * (t * v₀ * t⁻¹) ∈ Zz := by
    intro t ht
    have h1 : t * v₀ * t⁻¹ ∈ VZ T M := by
      have := Subgroup.mem_normalizer_iff.mp (hVN ▸ hTM ht) v₀
      exact this.mp hv₀V
    refine hV2 _ h1 fun hz => hv₀Z ?_
    have h2 := hTZ t⁻¹ (T.inv_mem ht) _ hz
    rw [inv_inv] at h2
    have h3 : v₀ = t * v₀ * t⁻¹ := by
      calc v₀ = t⁻¹ * (t * v₀ * t⁻¹) * t := by group
        _ = t * v₀ * t⁻¹ := h2
    rw [h3]
    exact hz
  have hTN : T ≤ Nz := fun t ht => hHN t (hTH ht)
  have hcommU : IsMulCommutative ↥(tildeOf Zz (uOfL22 T M)) := (isElemAbelian_secImg hUel).1
  have hA2 : ∀ a ∈ tildeOf Zz (uOfL22 T M), a * a = 1 := fun a ha => by
    have := (isElemAbelian_secImg hUel).2 a ha
    simpa [pow_two] using this
  have hconj : ∀ x : Γz, ∀ a ∈ tildeOf Zz (uOfL22 T M), x * a * x⁻¹ ∈ tildeOf Zz (uOfL22 T M) := by
    intro x a ha
    obtain ⟨g, rfl⟩ := secMk_surjective x
    obtain ⟨u, hu, rfl⟩ := mem_secImg.mp ha
    have hg : (g : G) ∈ mcOf T := hNH ▸ g.2
    refine mem_secImg.mpr ⟨g * u * g⁻¹, ?_, by simp [map_mul, map_inv]⟩
    have := (Subgroup.mem_normalizer_iff.mp (hHU hg) u).mp hu
    simpa using this
  have hP : ¬ 2 ∣ (tildeOf Zz T).index := by
    have h1 : (tildeOf Zz T).relIndex (tildeOf Zz Nz) = T.relIndex Nz :=
      relIndex_secImg_of_inf_le hTN le_rfl (inf_le_right.trans hZT)
    have h2 : tildeOf Zz Nz = ⊤ := by
      unfold tildeOf secImg
      rw [Subgroup.subgroupOf_self, Subgroup.map_top_of_surjective _ (secMk_surjective)]
    rw [h2, Subgroup.relIndex_top_right] at h1
    have h3 : T.relIndex Nz = T.relIndex (mcOf T) := by rw [hNH]
    rw [h1, h3]
    exact hTsyl.2.2
  let vN : ↥Nz := ⟨v₀, hv₀N⟩
  let vt : Γz := secMk Nz Zz vN
  have hvt : vt ∈ tildeOf Zz (uOfL22 T M) := secMk_mem_secImg (x := vN) hv₀U
  have hPa : ∀ p ∈ tildeOf Zz T, p * vt * p⁻¹ = vt := by
    intro p hp
    obtain ⟨t, ht, rfl⟩ := mem_secImg.mp hp
    rw [← map_inv, ← map_mul, ← map_mul, secMk_eq_secMk_iff]
    have := (quasithinOmegaOneCenter T).inv_mem (hTV (t : G) ht)
    simpa using this
  have hA₀le : (⨆ K ∈ cComp (mcOf T), ⁅uOfL22 T M, K⁆ : Subgroup G) ≤
      ((⨆ K ∈ cComp (mcOf T), tildeOf Zz ⁅uOfL22 T M, K⁆).comap (secMk Nz Zz)).map (Subgroup.subtype Nz) := by
    refine iSup₂_le fun K hK => ?_
    intro y hy
    have hyU : y ∈ uOfL22 T M :=
      S145.commutator_le_of_le_normalizer ((le_of_mem_cComp hK).trans hHU) hy
    refine Subgroup.mem_map.mpr ⟨⟨y, hUN hyU⟩, ?_, rfl⟩
    exact le_iSup₂ (f := fun K' (_ : K' ∈ cComp (mcOf T)) => tildeOf Zz ⁅uOfL22 T M, K'⁆) K hK
      (secMk_mem_secImg (x := ⟨y, hUN hyU⟩) hy)
  have hA0 : ∀ x : Γz, x * vt * x⁻¹ * vt⁻¹ ∈ ⨆ K ∈ cComp (mcOf T), tildeOf Zz ⁅uOfL22 T M, K⁆ := by
    intro x
    obtain ⟨g, rfl⟩ := secMk_surjective x
    have hgH : (g : G) ∈ mcOf T := hNH ▸ g.2
    have hPN : T ≤ Subgroup.normalizer (perfectCore (mcOf T) : Set G) :=
      hTH.trans (Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore (mcOf T)))
    have hgsup : (g : G) ∈ ((perfectCore (mcOf T) ⊔ T : Subgroup G) : Set G) := by
      rw [← hone2]; exact hgH
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hPN] at hgsup
    obtain ⟨a, ha, t, ht, hat⟩ := hgsup
    have haN : a ∈ Nz := hHN a (perfectCore_le _ ha)
    have htN : t ∈ Nz := hTN ht
    have hg : g = ⟨a, haN⟩ * ⟨t, htN⟩ := Subtype.ext hat.symm
    have hfix := hPa (secMk Nz Zz ⟨t, htN⟩) (secMk_mem_secImg (x := ⟨t, htN⟩) ht)
    have hcent := (perfectCore_le_centralizerMod hHU hspan ha).2.2 v₀ hv₀U
    have hmem := secMk_mem_of_le_map _ hA₀le (⟨a, haN⟩ * vN * ⟨a, haN⟩⁻¹ * vN⁻¹ : ↥Nz) hcent
    have heq : secMk Nz Zz g * vt * (secMk Nz Zz g)⁻¹ * vt⁻¹ =
        secMk Nz Zz (⟨a, haN⟩ * vN * ⟨a, haN⟩⁻¹ * vN⁻¹) := by
      calc secMk Nz Zz g * vt * (secMk Nz Zz g)⁻¹ * vt⁻¹
          = secMk Nz Zz ⟨a, haN⟩ * (secMk Nz Zz ⟨t, htN⟩ * vt * (secMk Nz Zz ⟨t, htN⟩)⁻¹) *
              (secMk Nz Zz ⟨a, haN⟩)⁻¹ * vt⁻¹ := by rw [hg, map_mul]; group
        _ = secMk Nz Zz ⟨a, haN⟩ * vt * (secMk Nz Zz ⟨a, haN⟩)⁻¹ * vt⁻¹ := by rw [hfix]
        _ = secMk Nz Zz (⟨a, haN⟩ * vN * ⟨a, haN⟩⁻¹ * vN⁻¹) := by simp [vt, map_mul, map_inv]
    rw [heq]
    exact hmem
  obtain ⟨c, hcU, hcfix, hcA⟩ := exists_fixed_mul_of_odd_index (tildeOf Zz (uOfL22 T M))
    (⨆ K ∈ cComp (mcOf T), tildeOf Zz ⁅uOfL22 T M, K⁆) (tildeOf Zz T) hA2 hconj hP hvt hPa hA0
  have hcC : c ∈ tildeOf Zz (centralizerMod Zz (uOfL22 T M) (mcOf T)) := by
    obtain ⟨u, huU, rfl⟩ := mem_secImg.mp hcU
    refine mem_secImg.mpr ⟨u, ?_, rfl⟩
    refine ⟨huU, u.2, fun h hh => ?_⟩
    have hhN : h ∈ Nz := hHN h hh
    have h1 := hcfix (secMk Nz Zz ⟨h, hhN⟩)
    rw [← map_inv, ← map_mul, ← map_mul, secMk_eq_secMk_iff] at h1
    have hz : h * (u : G)⁻¹ * h⁻¹ * u ∈ Zz := by simpa [mul_assoc] using h1
    have h2 := (Subgroup.mem_normalizer_iff.mp u.2 _).mp hz
    have h3 : (u : G) * h * (u : G)⁻¹ * h⁻¹ = u * (h * (u : G)⁻¹ * h⁻¹ * u) * (u : G)⁻¹ := by group
    rw [h3]
    exact h2
  apply le_antisymm
  · have hUle : uOfL22 T M ≤ (((⨆ K ∈ cComp (mcOf T), tildeOf Zz ⁅uOfL22 T M, K⁆) ⊔
        tildeOf Zz (centralizerMod Zz (uOfL22 T M) (mcOf T))).comap (secMk Nz Zz)).map
        (Subgroup.subtype Nz) := by
      refine conjClosure_le fun h hh v hv => ?_
      have hhN : h ∈ Nz := hHN h hh
      have hvN : v ∈ Nz := hUN (hVU hv)
      have hhvN : h * v * h⁻¹ ∈ Nz :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hhN hvN) (Subgroup.inv_mem _ hhN)
      refine Subgroup.mem_map.mpr ⟨⟨h * v * h⁻¹, hhvN⟩, ?_, rfl⟩
      rw [Subgroup.mem_comap]
      by_cases hvZ : v ∈ Zz
      · have hZc : h * v * h⁻¹ ∈ Zz := by
          have := Subgroup.mem_centralizer_iff.mp hh v hvZ
          have h4 : h * v * h⁻¹ = v := by
            calc h * v * h⁻¹ = (h * v) * h⁻¹ := rfl
              _ = (v * h) * h⁻¹ := by rw [← this]
              _ = v := by group
          rw [h4]
          exact hvZ
        rw [(secMk_eq_one_iff).mpr hZc]
        exact Subgroup.one_mem _
      · have hv1 : secMk Nz Zz ⟨v, hvN⟩ = vt := by
          rw [secMk_eq_secMk_iff]
          exact (Subgroup.inv_mem _ (hV2 v hv hvZ) |> fun h' => by simpa using h')
        have hconjeq : secMk Nz Zz ⟨h * v * h⁻¹, hhvN⟩ =
            secMk Nz Zz ⟨h, hhN⟩ * vt * (secMk Nz Zz ⟨h, hhN⟩)⁻¹ := by
          rw [← hv1, ← map_inv, ← map_mul, ← map_mul]; rfl
        rw [hconjeq]
        set x := secMk Nz Zz ⟨h, hhN⟩ with hx
        have hx1 := hA0 x
        have hc' : vt * c⁻¹ ∈ ⨆ K ∈ cComp (mcOf T), tildeOf Zz ⁅uOfL22 T M, K⁆ := by
          have := Subgroup.inv_mem _ hcA
          simpa using this
        have : x * vt * x⁻¹ = (x * vt * x⁻¹ * vt⁻¹) * (vt * c⁻¹) * c := by group
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hx1)
          (Subgroup.mem_sup_left hc')) (Subgroup.mem_sup_right hcC)
    exact (secImg_le_iff.mpr fun x hx => secMk_mem_of_le_map _ hUle x hx)
  · refine sup_le (iSup₂_le fun K hK => secImg_mono ?_) (secImg_mono (centralizerMod_le_left _ _ _))
    exact S145.commutator_le_of_le_normalizer ((le_of_mem_cComp hK).trans hHU)

end Cover

end CFSG.Quasithin
