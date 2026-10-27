module

public import CFSG.Quasithin.H13.A6S13821zz8
public import CFSG.Quasithin.H13.A6S13821zz6
public import CFSG.Quasithin.H13.A6S13821zy

public section

namespace CFSG.Quasithin.H13.A6.A6S20

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [Finite G]


omit [Finite G] in
theorem exists_secRestrict_comp {W : Type} [CommGroup W] {Y : Subgroup (MulAut W)}
    {U : Subgroup W} {C : Subgroup ↥U} (hY : Y ≤ CFSG.Quasithin.stabSub U)
    (hYC : autSub Y U ≤ CFSG.Quasithin.stabSub ⊤ ⊓ CFSG.Quasithin.stabSub C) {X : Type*}
    [Group X] (ρ : X →* ↥Y) (hρ : Function.Surjective ρ) :
    ∃ κ : X →* ↥(autSec (autSub Y U) ⊤ C), Function.Surjective κ ∧
      (∀ x, ρ x = 1 → κ x = 1) ∧
      ∀ (x : X) (u : ↥U), (κ x : MulAut (Sec (⊤ : Subgroup ↥U) C)) (InternalSec.secMk C u) =
        InternalSec.secMk C (resHom U ⟨(ρ x : MulAut W), hY (ρ x).2⟩ u) := by
  have hmem : ∀ g : ↥Y, resHomOn U hY g ∈ autSub Y U := fun g =>
    mem_autSub.mpr ⟨⟨g, hY g.2⟩, g.2, rfl⟩
  refine ⟨(Bridge.secRestrict hYC).comp (((resHomOn U hY).codRestrict _ hmem).comp ρ),
    fun y => ?_, fun x hx => by rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hx, map_one,
      map_one], fun x u => rfl⟩
  obtain ⟨⟨φ, hφ⟩, rfl⟩ := Bridge.secRestrict_surjective hYC y
  obtain ⟨g, hgY, hgφ⟩ := mem_autSub.mp hφ
  obtain ⟨x, hx⟩ := hρ ⟨(g : MulAut W), hgY⟩
  refine ⟨x, ?_⟩
  have h1 : ((resHomOn U hY).codRestrict _ hmem).comp ρ x = ⟨φ, hφ⟩ := by
    apply Subtype.ext
    show resHomOn U hY (ρ x) = φ
    rw [hx, ← hgφ]
    rfl
  rw [MonoidHom.comp_apply, h1]

omit [Finite G] in
theorem mem_normalizer_of_mem_ker {X : Type*} [Group X] [Finite X] (N : Subgroup X) [N.Normal]
    (hperf : commutator (X ⧸ N) = ⊤) (hs : IsSimpleGroup ((X ⧸ N) ⧸ Subgroup.center (X ⧸ N)))
    {T₀ : Subgroup X} (hNT : N ≤ T₀) {Y : Type*} [Group Y] [Nontrivial Y] (κ : X →* Y)
    (hκ : Function.Surjective κ) (hO : ∀ x ∈ N, κ x = 1) {x : X} (hx : x ∈ κ.ker) :
    x ∈ Subgroup.normalizer (T₀ : Set X) := by
  classical
  set π := QuotientGroup.mk' N with hπ
  have hDn : (κ.ker.map π).Normal := (MonoidHom.normal_ker κ).map π (QuotientGroup.mk'_surjective _)
  have hDt : κ.ker.map π ≠ ⊤ := by
    intro htop
    obtain ⟨a, b, hab⟩ := exists_pair_ne Y
    apply hab
    have hκ1 : ∀ y : X, κ y = 1 := by
      intro y
      have hy : π y ∈ κ.ker.map π := by rw [htop]; exact Subgroup.mem_top _
      obtain ⟨d, hd, hdy⟩ := hy
      have hdy' : d⁻¹ * y ∈ N := by
        rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hdy
        exact hdy
      have e : y = d * (d⁻¹ * y) := by group
      rw [e, map_mul, MonoidHom.mem_ker.mp hd, hO _ hdy', one_mul]
    obtain ⟨a', rfl⟩ := hκ a
    obtain ⟨b', rfl⟩ := hκ b
    rw [hκ1 a', hκ1 b']
  have hc := le_center_of_normal_ne_top hperf hs hDt
  have hxc : π x ∈ Subgroup.center (X ⧸ N) := hc ⟨x, hx, rfl⟩
  refine Subgroup.mem_normalizer_fintype fun t ht => ?_
  rw [SetLike.mem_coe] at ht ⊢
  have hcomm : x * t * x⁻¹ * t⁻¹ ∈ N := by
    have h1 : π (x * t * x⁻¹ * t⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv,
        (Subgroup.mem_center_iff.mp hxc (π t)).symm]
      group
    rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  have e : x * t * x⁻¹ = (x * t * x⁻¹ * t⁻¹) * t := by group
  rw [e]
  exact T₀.mul_mem (hNT hcomm) ht

omit [Finite G] in
theorem exists_fpf_of_kappa {W : Type} [CommGroup W] {L : Subgroup (MulAut W)} {m : ℕ}
    (hnat : BinaryNaturalSL L ⊤ ⊥ 3 m) (hm : 2 ≤ m) {X : Type} [Group X] [Finite X]
    (κ : X →* ↥L) (hκ : Function.Surjective κ) (N : Subgroup X) [N.Normal]
    (hperf : commutator (X ⧸ N) = ⊤) (hs : IsSimpleGroup ((X ⧸ N) ⧸ Subgroup.center (X ⧸ N)))
    {T₀ : Subgroup X} (hsyl : IsSylowTwoOf T₀ ⊤) (hNT : N ≤ T₀) (hO : ∀ x ∈ N, κ x = 1) :
    ∃ k ∈ Subgroup.normalizer (T₀ : Set X), ∀ w : W, ((κ k : ↥L) : MulAut W) w = w → w = 1 := by
  have hnt : Nontrivial ↥L := by
    obtain ⟨F, _, _, hFc, ⟨e⟩⟩ := hnat.exists_equiv
    have h1 : 1 < Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F) := by
      rw [Vol2.Ch10.SecA.card_statedSL, Vol2.Ch10.SecA.card_SL_three_pow hFc]
      have h2 : 2 ≤ 2 ^ (3 * m) := Nat.le_self_pow (by omega) 2
      have h3 : 1 ≤ 2 ^ (3 * m) - 1 := by omega
      have h4 : 2 ≤ 2 ^ (2 * m) := Nat.le_self_pow (by omega) 2
      have h5 : 1 ≤ 2 ^ (2 * m) - 1 := by omega
      calc 1 < 2 * (1 * 1) := by norm_num
        _ ≤ 2 ^ (3 * m) * ((2 ^ (3 * m) - 1) * (2 ^ (2 * m) - 1)) :=
          Nat.mul_le_mul h2 (Nat.mul_le_mul h3 h5)
    have : Finite ↥L := Finite.of_equiv _ e.toEquiv
    rw [Nat.card_congr e.toEquiv] at h1
    exact Finite.one_lt_card_iff_nontrivial.mp h1
  obtain ⟨k, hkN, hk⟩ := exists_fpf_of_natural_sl3 hnat hm κ hκ hsyl
    fun x hx => mem_normalizer_of_mem_ker N hperf hs hNT κ hκ hO hx
  refine ⟨k, hkN, fun w hw => ?_⟩
  have h1 := hk w (Subgroup.mem_top w) (by rw [hw, mul_inv_cancel]; exact Subgroup.one_mem _)
  exact Subgroup.mem_bot.mp h1

theorem exists_borel_fpf_sl3 {T V L V₁ Vp H K I : Subgroup G} (hF : HypF918 T V L V₁ Vp H K)
    (hV₁I : V₁ ≤ I) (hIU : I ≤ conjClosure Vp H) (hKI : K ≤ Subgroup.normalizer (I : Set G))
    [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    (hperf : commutator (↥K ⧸ CFSG.pCore 2 ↥K) = ⊤)
    (hs : IsSimpleGroup ((↥K ⧸ CFSG.pCore 2 ↥K) ⧸ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)))
    {m : ℕ}
    (hnat : BinaryNaturalSL (autSec (autSub (autIH V₁ I H K) (subM V₁ (conjClosure I H) I)) ⊤
        ((subM V₁ (conjClosure I H) I ⊓ fixV (autIH V₁ I H (conjClosure K T))).subgroupOf
          (subM V₁ (conjClosure I H) I))) ⊤ ⊥ 3 m) (hm : 2 ≤ m) {T₀ : Subgroup G}
    (hsyl : IsSylowTwoOf T₀ K) :
    ∃ k : ↥K, (k : G) ∈ Subgroup.normalizer (T₀ : Set G) ∧ ∀ i ∈ I,
      (k : G) * i * (k : G)⁻¹ * i⁻¹ ∈ centralizerMod V₁ I (conjClosure K T) →
        i ∈ centralizerMod V₁ I (conjClosure K T) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : K ≤ H := le_of_mem_cComp hF.K_cComp
  have hIHN := hF.conjClosure_le_normalizer_V₁ hIU
  obtain ⟨κ, hκs, hκ1, hκf⟩ := exists_secRestrict_comp
    (A6L32.autIH_le_stabSub_of hF hIU hV₁I hKH hKI) (autSub_le_stabSub (I := I) hF hKH)
    (toAutI hF I) (toAutI_surjective hF I)
  have hO : ∀ x ∈ CFSG.pCore 2 ↥K, κ x = 1 := fun x hx =>
    hκ1 x (toAutI_eq_one_of_mem_pCore hF hIU hx)
  have hsyl' : IsSylowTwoOf (T₀.subgroupOf K) (⊤ : Subgroup ↥K) := by
    refine ⟨le_top, ?_, ?_⟩
    · exact hsyl.2.1.of_injective (Subgroup.subgroupOfEquivOfLe hsyl.1).toMonoidHom
        (Subgroup.subgroupOfEquivOfLe hsyl.1).injective
    · have e : ((T₀.subgroupOf K).subgroupOf (⊤ : Subgroup ↥K)).index =
          (T₀.subgroupOf K).index :=
        Subgroup.index_comap_of_surjective (T₀.subgroupOf K) (f := (⊤ : Subgroup ↥K).subtype)
          (fun x => ⟨⟨x, Subgroup.mem_top x⟩, rfl⟩)
      rw [e]
      exact hsyl.2.2
  have hNT : CFSG.pCore 2 ↥K ≤ T₀.subgroupOf K := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    have hx' : (x : G) ∈ pCoreOf 2 K := ⟨x, by assumption, rfl⟩
    exact F7.isSylowTwoOf_pCoreOf_le hsyl hx'
  obtain ⟨k, hkN, hkfix⟩ := exists_fpf_of_kappa hnat hm κ hκs (CFSG.pCore 2 ↥K) hperf hs hsyl'
    hNT hO
  refine ⟨k, ?_, fun i hi hki => ?_⟩
  · refine Subgroup.mem_normalizer_fintype fun t ht => ?_
    rw [SetLike.mem_coe] at ht ⊢
    have htK : t ∈ K := hsyl.1 ht
    have h1 := (Subgroup.mem_normalizer_iff.mp hkN ⟨t, htK⟩).mp (Subgroup.mem_subgroupOf.mpr ht)
    exact Subgroup.mem_subgroupOf.mp h1
  ·
    have hki' : (k : G) * i * (k : G)⁻¹ ∈ I :=
      (Subgroup.mem_normalizer_iff.mp (hKI k.2) i).mp hi
    have e : resHom (subM V₁ (conjClosure I H) I)
        ⟨((toAutI hF I k : ↥(autIH V₁ I H K)) : MulAut ↥(tildeOf V₁ (conjClosure I H))),
          A6L32.autIH_le_stabSub_of hF hIU hV₁I hKH hKI (toAutI hF I k).2⟩
          (thetaMap hIHN hV₁I ⟨i, hi⟩) = thetaMap hIHN hV₁I ⟨_, hki'⟩ := by
      apply Subtype.ext
      rw [coe_thetaMap]
      show ((toAutI hF I k : ↥(autIH V₁ I H K)) : MulAut ↥(tildeOf V₁ (conjClosure I H)))
        (thetaMap hIHN hV₁I ⟨i, hi⟩ : ↥(tildeOf V₁ (conjClosure I H))) = _
      rw [coe_thetaMap, toAutI_coe]
      exact actH_modMk hF.H_le_normalizer_V₁ hIHN (le_normalizer_conjClosure I H)
        ⟨(k : G), hKH k.2⟩ (le_conjClosure I H hi)
    have h1 := hκf k (thetaMap hIHN hV₁I ⟨i, hi⟩)
    rw [e] at h1
    have h3 := (secMap_eq_one_iff hF hV₁I hIU (⟨_, hki'⟩ * (⟨i, hi⟩ : ↥I)⁻¹)).mpr hki
    rw [map_mul, map_inv, mul_inv_eq_one] at h3
    exact (secMap_eq_one_iff hF hV₁I hIU ⟨i, hi⟩).mp
      (hkfix (InternalSec.secMk _ (thetaMap hIHN hV₁I ⟨i, hi⟩)) (h1.trans h3))


theorem comm_mem_of_conj {T V L V₁ Vp H K I : Subgroup G} (hF : HypF918 T V L V₁ Vp H K)
    (hV₁I : V₁ ≤ I) (hIU : I ≤ conjClosure Vp H) {c : G} (hcH : c ∈ H)
    (hcK : ∀ x ∈ K, c * x * c⁻¹ * x⁻¹ ∈ pCoreOf 2 H) {k : G} (hk : k ∈ K) {i : G} (hi : i ∈ I)
    (h : c⁻¹ * k * c * i * (c⁻¹ * k * c)⁻¹ * i⁻¹ ∈ centralizerMod V₁ I (conjClosure K T)) :
    k * i * k⁻¹ * i⁻¹ ∈ centralizerMod V₁ I (conjClosure K T) := by
  have h1 := hF.toHypF98.toHypF91
  have hKH : K ≤ H := le_of_mem_cComp hF.K_cComp
  have hV₁C : V₁ ≤ centralizerMod V₁ I (conjClosure K T) :=
    le_centralizerMod hF.H_le_normalizer_V₁ hF.K₀_le_H hV₁I
  have hq : k⁻¹ * (c⁻¹ * k * c) ∈ pCoreOf 2 H := by
    have h2 := hcK k⁻¹ (K.inv_mem hk)
    have h3 := (Subgroup.mem_normalizer_iff.mp
      (le_normalizer_pCoreOf 2 H (H.inv_mem hcH)) _).mp h2
    have e : c⁻¹ * (c * k⁻¹ * c⁻¹ * k⁻¹⁻¹) * c⁻¹⁻¹ = k⁻¹ * (c⁻¹ * k * c) := by group
    rwa [e] at h3
  have hqi : k⁻¹ * (c⁻¹ * k * c) * i * (k⁻¹ * (c⁻¹ * k * c))⁻¹ * i⁻¹ ∈ V₁ := by
    rw [h1.pCoreOf_eq_centralizerMod] at hq
    exact hq.2.2 i (hIU hi)
  have hv := (Subgroup.mem_normalizer_iff.mp (hF.H_le_normalizer_V₁ (hKH hk)) _).mp hqi
  have e : k * i * k⁻¹ * i⁻¹ =
      (k * (k⁻¹ * (c⁻¹ * k * c) * i * (k⁻¹ * (c⁻¹ * k * c))⁻¹ * i⁻¹) * k⁻¹)⁻¹ *
        (c⁻¹ * k * c * i * (c⁻¹ * k * c)⁻¹ * i⁻¹) := by group
  rw [e]
  exact (centralizerMod V₁ I (conjClosure K T)).mul_mem
    ((centralizerMod V₁ I (conjClosure K T)).inv_mem (hV₁C hv)) h

theorem fixProp_sup_sl3 {T V L V₁ Vp H K I : Subgroup G} (hF : HypF918 T V L V₁ Vp H K)
    (hK₀ : conjClosure K T = K) (hV₁I : V₁ ≤ I) (hIU : I ≤ conjClosure Vp H)
    (hirr : IsIrrPlusTilde V₁ (conjClosure K T) I)
    [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure Vp H)))]
    [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    (hperf : commutator (↥K ⧸ CFSG.pCore 2 ↥K) = ⊤)
    (hs : IsSimpleGroup ((↥K ⧸ CFSG.pCore 2 ↥K) ⧸ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)))
    {m : ℕ}
    (hnat : BinaryNaturalSL (autSec (autSub (autIH V₁ I H K) (subM V₁ (conjClosure I H) I)) ⊤
        ((subM V₁ (conjClosure I H) I ⊓ fixV (autIH V₁ I H (conjClosure K T))).subgroupOf
          (subM V₁ (conjClosure I H) I))) ⊤ ⊥ 3 m) (hm : 2 ≤ m) {c : G} (hcH : c ∈ H)
    (hcK : ∀ x ∈ K, c * x * c⁻¹ * x⁻¹ ∈ pCoreOf 2 H)
    (hII : I ⊓ conjSub c I ≤ centralizerMod V₁ I K) {T₀ : Subgroup G}
    (hsyl : IsSylowTwoOf T₀ K) :
    S1565.FixProp ((actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure Vp H)).comp
        (Subgroup.inclusion (le_of_mem_cComp hF.K_cComp)))
      ((K ⊓ Subgroup.normalizer (T₀ : Set G)).subgroupOf K) ⊥
      (subM V₁ (conjClosure Vp H) (I ⊔ conjSub c I)) := by
  have hKI : K ≤ Subgroup.normalizer (I : Set G) := (le_conjClosure K T).trans hirr.1
  obtain ⟨k, hkN, hkI⟩ := exists_borel_fpf_sl3 hF hV₁I hIU hKI hperf hs hnat hm hsyl
  exact fixProp_sup_of_fpf hF hK₀ hV₁I hIU hirr hcH hII inf_le_left ⟨k.2, hkN⟩ hkI
    (fun i hi h => hkI i hi (comm_mem_of_conj hF hV₁I hIU hcH hcK k.2 hi h))

end CFSG.Quasithin.H13.A6.A6S20
