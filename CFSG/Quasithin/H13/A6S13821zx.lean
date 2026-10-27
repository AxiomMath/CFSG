module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.H13.A6S13821zu
public import CFSG.Quasithin.Vol2.Ch10SecQ3CBkA

public section

namespace CFSG.Quasithin.H13.A6.A6S20

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Assembly.LowTwoRank

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def thetaMap {V₁ H I : Subgroup G}
    (hIHN : conjClosure I H ≤ Subgroup.normalizer (V₁ : Set G)) (hV₁I : V₁ ≤ I)
    [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))] :
    ↥I →* ↥(subM V₁ (conjClosure I H) I) where
  toFun i := ⟨modMk hIHN (i : G) (le_conjClosure I H i.2),
    (modMk_mem_subM_iff hIHN hV₁I _).mpr i.2⟩
  map_one' := by
    apply Subtype.ext
    exact modMk_one hIHN
  map_mul' a b := by
    apply Subtype.ext
    exact modMk_mul hIHN (le_conjClosure I H a.2) (le_conjClosure I H b.2)

omit [Finite G] in
theorem coe_thetaMap {V₁ H I : Subgroup G}
    (hIHN : conjClosure I H ≤ Subgroup.normalizer (V₁ : Set G)) (hV₁I : V₁ ≤ I)
    [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))] (i : ↥I) :
    ((thetaMap hIHN hV₁I i : ↥(subM V₁ (conjClosure I H) I)) :
      ↥(tildeOf V₁ (conjClosure I H))) = modMk hIHN (i : G) (le_conjClosure I H i.2) := rfl

@[expose] noncomputable def secMap {V₁ H I : Subgroup G}
    (hIHN : conjClosure I H ≤ Subgroup.normalizer (V₁ : Set G)) (hV₁I : V₁ ≤ I)
    [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    (C' : Subgroup ↥(subM V₁ (conjClosure I H) I)) :
    ↥I →* Sec (⊤ : Subgroup ↥(subM V₁ (conjClosure I H) I)) C' :=
  (InternalSec.secMk C').comp (thetaMap hIHN hV₁I)

omit [Finite G] in
theorem secMap_apply {V₁ H I : Subgroup G}
    (hIHN : conjClosure I H ≤ Subgroup.normalizer (V₁ : Set G)) (hV₁I : V₁ ≤ I)
    [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    (C' : Subgroup ↥(subM V₁ (conjClosure I H) I)) (i : ↥I) :
    secMap hIHN hV₁I C' i = InternalSec.secMk C' (thetaMap hIHN hV₁I i) := rfl

omit [Finite G] in
theorem secMap_surjective {V₁ H I : Subgroup G}
    (hIHN : conjClosure I H ≤ Subgroup.normalizer (V₁ : Set G)) (hV₁I : V₁ ≤ I)
    [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    (C' : Subgroup ↥(subM V₁ (conjClosure I H) I)) :
    Function.Surjective (secMap hIHN hV₁I C') := by
  intro y
  obtain ⟨w, rfl⟩ := InternalSec.secMk_surjective C' y
  obtain ⟨a, haIH, haw⟩ := exists_mk_of_mem_tilde (w : ↥(tildeOf V₁ (conjClosure I H)))
  have haI : (a : G) ∈ I := by
    have h1 : ((w : ↥(tildeOf V₁ (conjClosure I H))) :
        SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁) ∈ tildeOf V₁ I := w.2
    rw [← haw] at h1
    exact (secMk_mem_tildeOf_iff hV₁I).mp h1
  refine ⟨⟨(a : G), haI⟩, ?_⟩
  rw [secMap_apply]
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  exact haw

theorem secMap_eq_one_iff {T V L V₁ Vp H K I : Subgroup G} (hF : HypF918 T V L V₁ Vp H K)
    (hV₁I : V₁ ≤ I) (hIU : I ≤ conjClosure Vp H)
    [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))] (z : ↥I) :
    secMap (hF.conjClosure_le_normalizer_V₁ hIU) hV₁I
        ((subM V₁ (conjClosure I H) I ⊓ fixV (autIH V₁ I H (conjClosure K T))).subgroupOf
          (subM V₁ (conjClosure I H) I)) z = 1 ↔
      (z : G) ∈ centralizerMod V₁ I (conjClosure K T) := by
  have hIHN := hF.conjClosure_le_normalizer_V₁ hIU
  have hIH := le_normalizer_conjClosure I H
  have hV₁C : V₁ ≤ centralizerMod V₁ I (conjClosure K T) :=
    le_centralizerMod hF.H_le_normalizer_V₁ hF.K₀_le_H hV₁I
  have hsubC := subM_centralizerMod hF.H_le_normalizer_V₁ hIHN hIH hF.K₀_le_H hV₁I
    (le_conjClosure I H)
  have hz := (modMk_mem_subM_iff hIHN hV₁C (le_conjClosure I H z.2)).symm
  rw [hsubC] at hz
  rw [secMap_apply, InternalSec.secMk, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  change modMk hIHN (z : G) (le_conjClosure I H z.2) ∈ _ ↔ _
  refine Iff.trans ?_ hz.symm
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun a => h2 a a.2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun γ hγ => h2 ⟨γ, hγ⟩⟩

omit [Finite G] in
theorem autSub_le_stabSub {T V L V₁ Vp H K I : Subgroup G} (hF : HypF918 T V L V₁ Vp H K)
    [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))] {X : Subgroup G} (hXH : X ≤ H) :
    autSub (autIH V₁ I H X) (subM V₁ (conjClosure I H) I) ≤
      CFSG.Quasithin.stabSub ⊤ ⊓ CFSG.Quasithin.stabSub
        ((subM V₁ (conjClosure I H) I ⊓ fixV (autIH V₁ I H (conjClosure K T))).subgroupOf
          (subM V₁ (conjClosure I H) I)) := by
  have hHN : autIH V₁ I H H ≤ Subgroup.normalizer
      ((autIH V₁ I H (conjClosure K T) : Subgroup (MulAut ↥(tildeOf V₁ (conjClosure I H)))) :
        Set _) := by
    rw [autIH_eq_map hF le_rfl, autIH_eq_map hF hF.K₀_le_H]
    exact map_le_normalizer_map_of_le_normalizer _ hF.K₀_le_H hF.K₀_normal
  intro g hg
  refine ⟨InternalSec.mem_stabSub_top g, ?_⟩
  obtain ⟨g', hg'X, rfl⟩ := mem_autSub.mp hg
  have hgN := hHN (autOn_le_autOn _ (secImg_mono hXH) hg'X)
  have hfixst : (g' : MulAut ↥(tildeOf V₁ (conjClosure I H))) ∈
      CFSG.Quasithin.stabSub (fixV (autIH V₁ I H (conjClosure K T))) := by
    refine L32A.C.mem_stabSub_fixV_of_conj (fun m hm => ?_) (fun m hm => ?_)
    · exact (Subgroup.mem_normalizer_iff.mp hgN m).mp hm
    · have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgN) m).mp hm
      simpa using h1
  intro v
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, resHom_apply]
  exact ⟨fun h => ⟨v.2, (hfixst (v : ↥(tildeOf V₁ (conjClosure I H)))).mp h.2⟩,
    fun h => ⟨(g'.2 v).mpr v.2, (hfixst (v : ↥(tildeOf V₁ (conjClosure I H)))).mpr h.2⟩⟩

theorem exists_secHom_secMap {T V L V₁ Vp H K I : Subgroup G} (hF : HypF918 T V L V₁ Vp H K)
    (hV₁I : V₁ ≤ I) (hIU : I ≤ conjClosure Vp H)
    [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))] {X : Subgroup G} (hXH : X ≤ H)
    (hXI : X ≤ Subgroup.normalizer (I : Set G)) {x : G} (hx : x ∈ X) :
    ∃ ℓ ∈ autSec (autSub (autIH V₁ I H X) (subM V₁ (conjClosure I H) I)) ⊤
        ((subM V₁ (conjClosure I H) I ⊓ fixV (autIH V₁ I H (conjClosure K T))).subgroupOf
          (subM V₁ (conjClosure I H) I)),
      ∀ (i : ↥I) (hi : x * (i : G) * x⁻¹ ∈ I),
        ℓ (secMap (hF.conjClosure_le_normalizer_V₁ hIU) hV₁I _ i) =
          secMap (hF.conjClosure_le_normalizer_V₁ hIU) hV₁I _ ⟨_, hi⟩ := by
  have hIHN := hF.conjClosure_le_normalizer_V₁ hIU
  have hIH := le_normalizer_conjClosure I H
  have hXU := A6L32.autIH_le_stabSub_of hF hIU hV₁I hXH hXI
  have hXC' := autSub_le_stabSub (I := I) hF hXH
  have hxH : x ∈ H := hXH hx
  have hψx : actH hF.H_le_normalizer_V₁ hIH ⟨x, hxH⟩ ∈ autIH V₁ I H X := by
    rw [autIH_eq_map hF hXH]
    exact ⟨⟨x, hxH⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  have hψU := hXU hψx
  have hres : resHom (subM V₁ (conjClosure I H) I) ⟨_, hψU⟩ ∈
      autSub (autIH V₁ I H X) (subM V₁ (conjClosure I H) I) :=
    mem_autSub.mpr ⟨⟨_, hψU⟩, hψx, rfl⟩
  refine ⟨Bridge.secHom ⊤ _ ⟨_, hXC' hres⟩, Bridge.secHom_mem_autSec hXC' hres, fun i hi => ?_⟩
  rw [secMap_apply, secMap_apply, InternalSec.secHom_secMk]
  congr 1

omit [Finite G] in
theorem eq_one_of_fix_natural {W : Type} [CommGroup W] {L : Subgroup (MulAut W)} {m : ℕ}
    (hnat : BinaryNaturalSL L ⊤ ⊥ 2 m) {ℓ : MulAut W} (hℓ : ℓ ∈ L) (hℓ2 : ℓ ^ 2 ≠ 1) {w : W}
    (hw : ℓ w = w) : w = 1 := by
  classical
  obtain ⟨K', _, hK'fin, hK'c, hR⟩ := hnat
  obtain ⟨π, hπ⟩ : ∃ π : ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 K') →* ↥L,
      (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 2 K')).RealizesVia L ⊤ ⊥ π := hR
  have := Fintype.ofFinite K'
  have : CharP K' 2 := charP_of_card_eq_prime_pow (f := m) (by
    rw [← Nat.card_eq_fintype_card, hK'c])
  obtain ⟨ε, hε⟩ := exists_sec_equiv_nat (CFSG.Assembly.LowTwoRank.StatedSL 2 K') hπ
  obtain ⟨γ, hγ⟩ : ∃ γ : ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 K'), π γ = ⟨ℓ, hℓ⟩ :=
    hπ.1 ⟨ℓ, hℓ⟩
  have hγℓ : ((π γ : ↥L) : MulAut W) = ℓ := by rw [hγ]
  have h1 := hε γ ⟨w, trivial⟩ trivial
  have hu' : (⟨((π γ : ↥L) : MulAut W) ((⟨w, trivial⟩ : ↥(⊤ : Subgroup W)) : W), trivial⟩ :
      ↥(⊤ : Subgroup W)) = ⟨w, trivial⟩ := by
    apply Subtype.ext
    show ((π γ : ↥L) : MulAut W) w = w
    rw [hγℓ, hw]
  replace h1 := (congrArg (fun z => ε (QuotientGroup.mk z)) hu').symm.trans h1
  set v : Fin 2 → K' := Multiplicative.toAdd (ε (QuotientGroup.mk ⟨w, trivial⟩)) with hv
  have hγv : (((γ : GL (Fin 2) K') : Matrix (Fin 2) (Fin 2) K')).mulVec v = v := by
    have h2 := congrArg Multiplicative.toAdd h1
    rw [natAct] at h2
    simp only [toAdd_ofAdd] at h2
    exact h2.symm
  by_cases hv0 : v = 0
  · have h2 : ε (QuotientGroup.mk ⟨w, trivial⟩) = 1 := by
      apply Multiplicative.toAdd.injective
      rw [← hv, hv0]
      rfl
    rw [map_eq_one_iff _ ε.injective, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      Subgroup.mem_bot] at h2
    exact h2
  · exfalso
    apply hℓ2
    set γ' := (specialLinearGroupEquivStatedSL 2 K').symm γ with hγ'
    have hγ'm : ((γ' : Matrix.SpecialLinearGroup (Fin 2) K') : Matrix (Fin 2) (Fin 2) K') =
        ((γ : GL (Fin 2) K') : Matrix (Fin 2) (Fin 2) K') := by
      have := specialLinearGroupEquivStatedSL_coe 2 K' γ'
      rw [hγ', MulEquiv.apply_symm_apply] at this
      exact this.symm
    have hsq := Vol2.Ch10.SecB.C11AmS.sq_eq_one_of_fix γ' hv0 (by rw [hγ'm]; exact hγv)
    have hγ2 : γ ^ 2 = 1 := by
      have := congrArg (specialLinearGroupEquivStatedSL 2 K') hsq
      rwa [map_pow, hγ', MulEquiv.apply_symm_apply, map_one] at this
    rw [← hγℓ, ← Subgroup.coe_pow, ← map_pow, hγ2, map_one]
    rfl

theorem mk_eq_one_of_comm {T V L V₁ Vp H K I : Subgroup G} (hF : HypF918 T V L V₁ Vp H K)
    (hK₀ : conjClosure K T = K) (hS' : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K)) (hV₁I : V₁ ≤ I)
    (hIU : I ≤ conjClosure Vp H) (hirr : IsIrrPlusTilde V₁ (conjClosure K T) I) {x : ↥K}
    (hx : ∀ i ∈ I, (x : G) * i * (x : G)⁻¹ * i⁻¹ ∈ centralizerMod V₁ I (conjClosure K T)) :
    (QuotientGroup.mk x : ↥K ⧸ CFSG.pCore 2 ↥K) = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizerMod V₁ I (conjClosure K T) with hC
  have h1 := hF.toHypF98.toHypF91
  have hKH : K ≤ H := le_of_mem_cComp hF.K_cComp
  have hHV₁ : H ≤ Subgroup.normalizer (V₁ : Set G) := hF.H_le_normalizer_V₁
  have hUH : conjClosure Vp H ≤ H := h1.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)
  have hKK₀ : K ≤ conjClosure K T := le_conjClosure K T
  have hKI : K ≤ Subgroup.normalizer (I : Set G) := hKK₀.trans hirr.1
  have hKC : K ≤ Subgroup.normalizer (C : Set G) :=
    le_normalizer_centralizerMod (hKH.trans hHV₁) hKI (by rw [hK₀]; exact Subgroup.le_normalizer)
  have hV₁C : V₁ ≤ C := le_centralizerMod hHV₁ hF.K₀_le_H hV₁I
  set D := centralizerMod C K I with hD
  have hDK : D ≤ K := centralizerMod_le_left _ _ _
  have hKD : K ≤ Subgroup.normalizer (D : Set G) :=
    le_normalizer_centralizerMod hKC (fun k hk => Subgroup.le_normalizer hk) hKI
  have hDn : (D.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDK).mpr hKD
  have hxD : (x : G) ∈ D := ⟨x.2, hKC x.2, hx⟩
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hπ
  have hnorm : ((D.subgroupOf K).map π).Normal := hDn.map π (QuotientGroup.mk'_surjective _)
  rcases hnorm.eq_bot_or_eq_top with hbot | htop
  · have : π x ∈ (D.subgroupOf K).map π := ⟨x, Subgroup.mem_subgroupOf.mpr hxD, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  · exfalso
    have hO : ∀ o : ↥K, o ∈ CFSG.pCore 2 ↥K → ∀ i ∈ I, (o : G) * i * (o : G)⁻¹ * i⁻¹ ∈ V₁ := by
      intro o ho i hi
      have ho' : (o : G) ∈ pCoreOf 2 K := ⟨o, by assumption, rfl⟩
      have hoQ := A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hF.K_cComp) ho'
      rw [h1.pCoreOf_eq_centralizerMod] at hoQ
      exact hoQ.2.2 i (hIU hi)
    have hcomm : ∀ k ∈ K, ∀ i ∈ I, k * i * k⁻¹ * i⁻¹ ∈ C := by
      intro k hk i hi
      have hk' : π ⟨k, hk⟩ ∈ (D.subgroupOf K).map π := by rw [htop]; exact Subgroup.mem_top _
      obtain ⟨d, hdD, hdk⟩ := hk'
      have hdD' : (d : G) ∈ D := Subgroup.mem_subgroupOf.mp hdD
      have ho : d⁻¹ * ⟨k, hk⟩ ∈ CFSG.pCore 2 ↥K := by
        rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hdk
        exact hdk
      have hv := hO _ ho i hi
      have hko : k = (d : G) * ((d⁻¹ * ⟨k, hk⟩ : ↥K) : G) := by simp
      set o : G := ((d⁻¹ * ⟨k, hk⟩ : ↥K) : G) with hodef
      have hdV₁ : (d : G) * (o * i * o⁻¹ * i⁻¹) * (d : G)⁻¹ ∈ C :=
        hV₁C ((Subgroup.mem_normalizer_iff.mp (hHV₁ (hKH d.2)) _).mp hv)
      have hdi := hdD'.2.2 i hi
      have e : k * i * k⁻¹ * i⁻¹ = ((d : G) * (o * i * o⁻¹ * i⁻¹) * (d : G)⁻¹) *
          ((d : G) * i * (d : G)⁻¹ * i⁻¹) := by rw [hko]; group
      rw [e]
      exact C.mul_mem hdV₁ hdi
    have hIK : ⁅I, conjClosure K T⁆ ≤ C := by
      rw [hK₀]
      refine Subgroup.commutator_le.mpr fun i hi k hk => ?_
      have h2 := C.inv_mem (hcomm k hk i hi)
      have e : (k * i * k⁻¹ * i⁻¹)⁻¹ = i * k * i⁻¹ * k⁻¹ := by group
      rw [e] at h2
      exact h2
    have hle : tildeOf V₁ I ≤ tildeOf V₁ C := hirr.2.1 ▸ secImg_mono hIK
    have hIC := le_sup_of_tildeOf_le (hIU.trans (hUH.trans hHV₁)) hle
    rw [sup_eq_left.mpr hV₁C] at hIC
    exact (not_le_of_gt hirr.2.2.1) hIC

theorem mem_of_natural {T V L V₁ Vp H K I : Subgroup G} (hF : HypF918 T V L V₁ Vp H K)
    (hK₀ : conjClosure K T = K) (hS' : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K)) (hV₁I : V₁ ≤ I)
    (hIU : I ≤ conjClosure Vp H) (hirr : IsIrrPlusTilde V₁ (conjClosure K T) I)
    [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))] {m : ℕ}
    (hnat : BinaryNaturalSL (autSec (autSub (autIH V₁ I H K) (subM V₁ (conjClosure I H) I)) ⊤
        ((subM V₁ (conjClosure I H) I ⊓ fixV (autIH V₁ I H (conjClosure K T))).subgroupOf
          (subM V₁ (conjClosure I H) I))) ⊤ ⊥ 2 m)
    {k : ↥K} (hk : (QuotientGroup.mk k : ↥K ⧸ CFSG.pCore 2 ↥K) ^ 2 ≠ 1) {i : G} (hi : i ∈ I)
    (hki : (k : G) * i * (k : G)⁻¹ * i⁻¹ ∈ centralizerMod V₁ I (conjClosure K T)) :
    i ∈ centralizerMod V₁ I (conjClosure K T) := by
  classical
  have hKH : K ≤ H := le_of_mem_cComp hF.K_cComp
  have hKI : K ≤ Subgroup.normalizer (I : Set G) := (le_conjClosure K T).trans hirr.1
  have hIk : ∀ j ∈ I, (k : G) * j * (k : G)⁻¹ ∈ I := fun j hj =>
    (Subgroup.mem_normalizer_iff.mp (hKI k.2) j).mp hj
  obtain ⟨ℓ, hℓL, hℓ⟩ := exists_secHom_secMap (K := K) hF hV₁I hIU hKH hKI k.2
  set f := secMap (hF.conjClosure_le_normalizer_V₁ hIU) hV₁I
    ((subM V₁ (conjClosure I H) I ⊓ fixV (autIH V₁ I H (conjClosure K T))).subgroupOf
      (subM V₁ (conjClosure I H) I)) with hf
  have hfeq : ∀ a b : ↥I, (a : G) * (b : G)⁻¹ ∈ centralizerMod V₁ I (conjClosure K T) →
      f a = f b := by
    intro a b hab
    have h2 : f (a * b⁻¹) = 1 := (secMap_eq_one_iff hF hV₁I hIU (a * b⁻¹)).mpr hab
    rw [map_mul, map_inv, mul_inv_eq_one] at h2
    exact h2
  have hℓ2 : ℓ ^ 2 ≠ 1 := by
    intro h2
    apply hk
    rw [← QuotientGroup.mk_pow]
    refine mk_eq_one_of_comm hF hK₀ hS' hV₁I hIU hirr fun j hj => ?_
    have hj1 := hℓ ⟨j, hj⟩ (hIk j hj)
    have hj2 := hℓ ⟨_, hIk j hj⟩ (hIk _ (hIk j hj))
    have hsq : ℓ (ℓ (f ⟨j, hj⟩)) = f ⟨j, hj⟩ := by
      rw [← MulAut.mul_apply, ← sq, h2]
      rfl
    rw [hj1, hj2] at hsq
    have h3 := (secMap_eq_one_iff hF hV₁I hIU
      (⟨_, hIk _ (hIk j hj)⟩ * (⟨j, hj⟩ : ↥I)⁻¹)).mp (by rw [map_mul, map_inv, hsq, mul_inv_cancel])
    have e : (((k ^ 2 : ↥K) : G)) * j * ((k ^ 2 : ↥K) : G)⁻¹ * j⁻¹ =
        (k : G) * ((k : G) * j * (k : G)⁻¹) * (k : G)⁻¹ * j⁻¹ := by
      rw [Subgroup.coe_pow, sq]
      group
    rw [e]
    exact h3
  have hfix : ℓ (f ⟨i, hi⟩) = f ⟨i, hi⟩ := by
    rw [hℓ ⟨i, hi⟩ (hIk i hi)]
    exact hfeq _ _ hki
  have h1 := eq_one_of_fix_natural hnat hℓL hℓ2 hfix
  exact (secMap_eq_one_iff hF hV₁I hIU ⟨i, hi⟩).mp h1

end CFSG.Quasithin.H13.A6.A6S20
