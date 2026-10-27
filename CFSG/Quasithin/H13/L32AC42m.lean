module

public import CFSG.Quasithin.H13.L32AC42l
public import CFSG.Quasithin.H13.L32AC41g
public import CFSG.Quasithin.H13.L32AC42g
public import CFSG.Quasithin.H13.L32AC42k

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open hiding StatedSL StatedSU StatedSp StatedProj StatedClassicalModel
open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique.Bridge.TypeList
open scoped IsMulCommutative MatrixGroups

namespace B42R

variable {W : Type} [CommGroup W] [Finite W] {G₁ K₁ : Subgroup (MulAut W)}

theorem eq_one_of_comm (h2 : ∀ y ∈ G₁, ∃ e : ℕ, y ^ 2 ^ e ∈ K₁)
    (hKn : ∀ y ∈ G₁, ∀ k ∈ K₁, y * k * y⁻¹ ∈ K₁) (hZ : Subgroup.center ↥K₁ = ⊥)
    (hO2 : pCoreOf 2 G₁ = ⊥) {c : MulAut W} (hc : c ∈ G₁) (hck : ∀ k ∈ K₁, c * k = k * c) :
    c = 1 := by
  have : Finite (MulAut W) := finite_mulAut
  set N : Subgroup (MulAut W) := G₁ ⊓ Subgroup.centralizer (K₁ : Set (MulAut W)) with hN
  have hcen : ∀ y ∈ K₁, y ∈ Subgroup.centralizer (K₁ : Set (MulAut W)) → y = 1 := by
    intro y hy hyc
    have : (⟨y, hy⟩ : ↥K₁) ∈ Subgroup.center ↥K₁ :=
      Subgroup.mem_center_iff.mpr fun z => Subtype.ext (Subgroup.mem_centralizer_iff.mp hyc z z.2)
    rw [hZ, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  have hNp : IsPGroup 2 ↥N := by
    rintro ⟨y, hyG, hyc⟩
    obtain ⟨e, he⟩ := h2 y hyG
    refine ⟨e, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    exact hcen _ he (Subgroup.pow_mem _ hyc _)
  have hNn : G₁ ≤ Subgroup.normalizer (N : Set (MulAut W)) := by
    intro g hg
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    refine ⟨G₁.mul_mem (G₁.mul_mem hg hy.1) (G₁.inv_mem hg),
      Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
    have hk' : g⁻¹ * k * g ∈ K₁ := by
      have := hKn g⁻¹ (G₁.inv_mem hg) k hk
      rwa [inv_inv] at this
    have h1 := Subgroup.mem_centralizer_iff.mp hy.2 _ hk'
    calc k * (g * y * g⁻¹) = g * ((g⁻¹ * k * g) * y) * g⁻¹ := by group
      _ = g * (y * (g⁻¹ * k * g)) * g⁻¹ := by rw [h1]
      _ = g * y * g⁻¹ * k := by group
  have hle := le_pCoreOf_of_le_normalizer 2 inf_le_left hNn hNp
  rw [hO2] at hle
  have : c ∈ N := ⟨hc, Subgroup.mem_centralizer_iff.mpr fun k hk => (hck k hk).symm⟩
  exact Subgroup.mem_bot.mp (hle this)

end B42R

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

theorem TopW.actS_mem_autOf {W : Subgroup G} (D : TopW T L V H W)
    [IsMulCommutative ↥(conjClosure V H)] {K : Subgroup G} {y : ↥H ⧸ CFSG.pCore 2 ↥H}
    (hy : y ∈ modO2Image H K) : D.actS y ∈ D.autOf K := by
  obtain ⟨k, hk, rfl⟩ := mem_modO2Image'.mp hy
  exact ⟨k, Subgroup.mem_subgroupOf.mpr hk, (D.actS_mk k).symm⟩

namespace Top42

variable {K I : Subgroup G} (C : Top42 T L V H K I) (D : TopW T L V H I)
include C D

variable [IsMulCommutative ↥(conjClosure V H)]

theorem nonempty_kb_equiv (h28 : Lemma14_7_28) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (h5 : Lemma14_7_5) {n : ℕ}
    (hLie : A315.IsLieChar2 n (cStar K ⧸ Subgroup.center (cStar K)))
    {x : ↥H ⧸ CFSG.pCore 2 ↥H} (hx : x ∈ modO2Image H (l1 T L V)) {Vs : Subgroup (Hat V H I)}
    (hcup : Vs ⊔ Vs.map (D.actS x).toMonoidHom = ⊤) (hKs : D.autOf K ≤ stabSub Vs) :
    Nonempty (↥(modO2Image H K) ≃* ↥(autSub (D.autOf K) Vs)) := by
  have hKa : ∀ g ∈ D.autOf K, g * D.actS x = D.actS x * g :=
    fun g hg => (D.actS_comm (C.hc hx) hg).symm
  have hinj := C.actS_injective D h28 h1222 h1332 h1334 h5 hLie
  have hmem : ∀ y : ↥(modO2Image H K), D.actS y ∈ D.autOf K := fun y => D.actS_mem_autOf y.2
  let g₁ : ↥(modO2Image H K) →* ↥(stabSub Vs) :=
    (D.actS.comp (modO2Image H K).subtype).codRestrict _ fun y => hKs (hmem y)
  let f : ↥(modO2Image H K) →* ↥(autSub (D.autOf K) Vs) :=
    ((resHom Vs).comp g₁).codRestrict _ fun y => mem_autSub.mpr ⟨g₁ y, hmem y, rfl⟩
  refine ⟨MulEquiv.ofBijective f ⟨fun y₁ y₂ h => ?_, ?_⟩⟩
  · have h1 : resHom Vs (g₁ y₁) = resHom Vs (g₁ y₂) := congrArg Subtype.val h
    have h2 := Dec.eq_of_resHom_eq hcup (hKa _ (hmem y₁)) (hKa _ (hmem y₂)) h1
    have h3 : D.actS y₁ = D.actS y₂ := congrArg Subtype.val h2
    exact Subtype.ext (hinj h3)
  · rintro ⟨φ, hφ⟩
    obtain ⟨g, hgK, rfl⟩ := mem_autSub.mp hφ
    obtain ⟨k, hk, hkg⟩ := hgK
    refine ⟨⟨QuotientGroup.mk' (CFSG.pCore 2 ↥H) k,
      mem_modO2Image'.mpr ⟨k, Subgroup.mem_subgroupOf.mp hk, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    show resHom Vs (g₁ _) = resHom Vs g
    congr 1
    apply Subtype.ext
    show D.actS (QuotientGroup.mk' (CFSG.pCore 2 ↥H) k) = g
    rw [D.actS_mk, hkg]

theorem exists_outer (h28 : Lemma14_7_28) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (h5 : Lemma14_7_5) {n : ℕ}
    (hLie : A315.IsLieChar2 n (cStar K ⧸ Subgroup.center (cStar K)))
    {x : ↥H ⧸ CFSG.pCore 2 ↥H} (hx : x ∈ modO2Image H (l1 T L V)) {Vs : Subgroup (Hat V H I)}
    (hcup : Vs ⊔ Vs.map (D.actS x).toMonoidHom = ⊤) (hKs : D.autOf K ≤ stabSub Vs)
    (hTs : D.autOf T ≤ stabSub Vs)
    (hB4 : B4Hyp (autSub (D.autOf K ⊔ D.autOf T) Vs) (autSub (D.autOf K) Vs))
    (h2 : ∀ y ∈ autSub (D.autOf K ⊔ D.autOf T) Vs, ∃ e : ℕ, y ^ 2 ^ e ∈ autSub (D.autOf K) Vs)
    (hnorm : ∀ y ∈ autSub (D.autOf K ⊔ D.autOf T) Vs, ∀ k ∈ autSub (D.autOf K) Vs,
      y * k * y⁻¹ ∈ autSub (D.autOf K) Vs)
    (hO2 : pCoreOf 2 (autSub (D.autOf K ⊔ D.autOf T) Vs) = ⊥)
    (hZ : Subgroup.center ↥(autSub (D.autOf K) Vs) = ⊥) {A : Subgroup (MulAut ↥Vs)}
    (hA : IsFFStarOffender (autSub (D.autOf K ⊔ D.autOf T) Vs) A)
    (hc5 : B42R.Case5Five (autSub (D.autOf K ⊔ D.autOf T) Vs) A) :
    Nonempty (↥(modO2Image H K) ≃* ↥(alternatingGroup (Fin 5))) ∧
      ∃ τ : ↥H ⧸ CFSG.pCore 2 ↥H, ∀ k ∈ modO2Image H K,
        ∀ r ∈ Subgroup.centralizer (modO2Image H K : Set (↥H ⧸ CFSG.pCore 2 ↥H)), τ ≠ k * r := by
  classical
  set G₁ := autSub (D.autOf K ⊔ D.autOf T) Vs with hG₁
  set K₁ := autSub (D.autOf K) Vs with hK₁
  obtain ⟨π, hπ, T', hT'sw, -, hAT⟩ := hc5
  have hexp : ∀ v : ↥Vs, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using D.hexp (v : Hat V H I))
  have hKJ : K₁ ≤ ffJ G₁ := le_ffJ_of_b4Hyp hexp hB4 hA
  have hJG : ffJ G₁ ≤ G₁ := B6.ffJ_le G₁
  have hq : CFSG.IsQuasisimple ↥K₁ := hB4.2.2.1
  have hKJn : (K₁.subgroupOf (ffJ G₁)).Normal := ⟨fun l hl g => by
    rw [Subgroup.mem_subgroupOf] at hl ⊢
    exact hnorm _ (hJG g.2) _ hl⟩
  have hq' : CFSG.IsQuasisimple ↥(K₁.subgroupOf (ffJ G₁)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKJ).symm hq
  obtain ⟨e5⟩ := perm_perfect_normal_equiv (by norm_num) π hπ.1 _ hKJn
    hq'.1.commutator_eq_top (exists_noncomm_of_quasisimple hq')
  obtain ⟨eK⟩ := C.nonempty_kb_equiv D h28 h1222 h1332 h1334 h5 hLie hx hcup hKs
  refine ⟨⟨eK.trans ((Subgroup.subgroupOfEquivOfLe hKJ).symm.trans e5.symm)⟩, ?_⟩
  have hAJ : A ≤ ffJ G₁ := le_iSup₂_of_le A hA le_rfl
  obtain ⟨σ, hσT⟩ : T'.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    rintro rfl
    apply hA.2.1
    rw [Subgroup.closure_empty, Subgroup.map_bot] at hAT
    rw [eq_bot_iff]
    intro a ha
    have : (⟨a, hAJ ha⟩ : ↥(ffJ G₁)) ∈ A.subgroupOf (ffJ G₁) := ha
    rw [hAT, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  have hπσA : ((π σ : ↥(ffJ G₁)) : MulAut ↥Vs) ∈ A := by
    have : π σ ∈ A.subgroupOf (ffJ G₁) := by
      rw [hAT]
      exact ⟨σ, Subgroup.subset_closure hσT, rfl⟩
    exact this
  have hinjπ : Function.Injective π := hπ.injective_of_faithful (G64.symDn_faithful (by norm_num))
  set f : Equiv.Perm (Fin 5) →* MulAut ↥Vs := (ffJ G₁).subtype.comp π with hf
  have hfinj : Function.Injective f := (ffJ G₁).subtype_injective.comp hinjπ
  have hfr : f.range = ffJ G₁ := by
    ext y
    constructor
    · rintro ⟨σ, rfl⟩
      exact (π σ).2
    · intro hy
      obtain ⟨σ, hσ⟩ := hπ.1 ⟨y, hy⟩
      exact ⟨σ, congrArg Subtype.val hσ⟩
  have hσK : f σ ∉ K₁ := by
    intro hσ
    set N := K₁.comap f with hN
    have hNmap : N.map f = K₁ := Subgroup.map_comap_eq_self (hfr ▸ hKJ)
    have hperf : ⁅N, N⁆ = N := by
      apply Subgroup.map_injective hfinj
      rw [Subgroup.map_commutator, hNmap]
      exact Subgroup.isPerfect_iff.mp hq.1
    have hle : N ≤ Equiv.Perm.sign.ker := by
      rw [← hperf, Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
    have h1 := hle (show σ ∈ N from hσ)
    rw [MonoidHom.mem_ker, (hT'sw σ hσT).sign_eq] at h1
    exact absurd h1 (by decide)
  obtain ⟨g, hgKT, hgσ⟩ := mem_autSub.mp (hA.1 hπσA)
  have hmap : D.autOf K ⊔ D.autOf T = (K.subgroupOf H ⊔ T.subgroupOf H).map D.act := by
    rw [Subgroup.map_sup]
    rfl
  obtain ⟨h, -, hhg⟩ := (hmap ▸ hgKT : (g : MulAut (Hat V H I)) ∈ _)
  refine ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥H) h, fun k hk r hr hkr => hσK ?_⟩
  have hkK := D.actS_mem_autOf hk
  have hrS : D.actS r = (D.actS k)⁻¹ * g := by
    have e : r = k⁻¹ * QuotientGroup.mk' (CFSG.pCore 2 ↥H) h := by rw [hkr]; group
    rw [e, map_mul, map_inv, D.actS_mk, hhg]
  have hKTs : D.autOf K ⊔ D.autOf T ≤ stabSub Vs := sup_le hKs hTs
  have hrKT : D.actS r ∈ D.autOf K ⊔ D.autOf T := by
    rw [hrS]
    exact mul_mem (inv_mem (Subgroup.mem_sup_left hkK)) hgKT
  have hc : resHom Vs ⟨D.actS r, hKTs hrKT⟩ = 1 := by
    refine B42R.eq_one_of_comm h2 hnorm hZ hO2 (mem_autSub.mpr ⟨_, hrKT, rfl⟩) fun φ hφ => ?_
    obtain ⟨k', hk', rfl⟩ := mem_autSub.mp hφ
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (D.actS_comm hr hk')
  have hge : g = ⟨D.actS k, hKs hkK⟩ * ⟨D.actS r, hKTs hrKT⟩ := by
    apply Subtype.ext
    show (g : MulAut (Hat V H I)) = D.actS k * D.actS r
    rw [hrS, mul_inv_cancel_left]
  have e : f σ = resHom Vs ⟨D.actS k, hKs hkK⟩ := by
    show ((π σ : ↥(ffJ G₁)) : MulAut ↥Vs) = _
    rw [← hgσ, hge, map_mul, hc, mul_one]
  rw [e]
  exact mem_autSub.mpr ⟨_, hkK, rfl⟩

end Top42

theorem lemma14_7_42_s5s3_of_inputs (h310 : D310) (hB42 : AsB42) (hA21 : AsA21SQTKSection)
    (hN1 : LieSylowOver3) (hN3 : LieBorelThreeInner) (hN4 : LieBorelTwoInner)
    (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (h5 : Lemma14_7_5)
    (h28 : Lemma14_7_28) (h29 : Thm14_7_29) (h30 : Lemma14_7_30) (h32 : Lemma14_7_32)
    (h34 : Lemma14_7_34) (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (hPGL : Lemma14741PGL) :
    Lemma14_7_42_S5S3 := by
  intro G _ _ T L V H S K hK hHeq n hn hLie hl1K
  classical
  obtain ⟨hq, -, -, hF918⟩ := h30 G T L V H S K hK
  have hTK := h32 G T L V H S K hK
  have hKn := le_normalizer_of_setting hA37 hA38 S hK hTK
  have hc := l1_star_le_centralizer_of hN1 hN3 h28 h29 h1222 h1332 h1334 hPGL S hK hq hKn hHeq
    hn hLie hl1K
  have C0 : Hyp42 T L V H K := ⟨S, hK, hq, hKn, hHeq, hl1K, hc⟩
  have hHeq' : conjClosure K T ⊔ (l1 T L V ⊔ T) = H := by
    rw [conjClosure_T_eq_self ((Setting147.TH' S).trans hKn)]
    exact hHeq.symm
  rw [hHeq'] at hF918
  obtain ⟨I, C⟩ := C0.exists_top42 hF918.toHypF98
  have D := C.toTopW h5 h1332 h1334
  have := D.comm
  obtain ⟨B, hB, -⟩ := hF918.F918_2
  obtain ⟨Vs, hVs, hcase⟩ := C.d310 D h310 h28 h1222 h1332 h1334 h5 hLie hB
  obtain ⟨x, hx, t, ht, hx3, hx1, htx⟩ :=
    C.exists_tC hN1 hN4 h29 h1222 h1332 h1334 h34 hn hLie
  rcases hcase with hst | h2
  swap
  · exact absurd h2 (C.not_d310Two D h28 h1222 h1332 h1334 h5 hLie hx hx1 ht htx
      ⟨le_top, hVs.1.2⟩)
  obtain ⟨hB4, h2, hnorm, hO2, A, hA, hconc⟩ :=
    C.b42 D hB42 hA21 h28 h1222 h1332 h1334 h5 hLie hx hx1 ht htx hVs hst hB
  obtain ⟨-, hcap, hcup⟩ := C.isCompl_of_stab D h28 h1222 h1332 h1334 h5 hLie hx hx1 ht htx
    ⟨le_top, hVs.1.2⟩ hst
  obtain ⟨hinv, -⟩ := mem_irrPlus_top_iff.mp (⟨le_top, hVs.1.2⟩ : Vs ∈ IrrPlus (D.autOf K) ⊤)
  have hKs : D.autOf K ≤ stabSub Vs := fun g hg =>
    B5.mem_stabSub_of_inv (hinv g hg) (hinv g⁻¹ (inv_mem hg))
  have hTs : D.autOf T ≤ stabSub Vs := fun g hg => hst g hg
  obtain ⟨eK⟩ := C.nonempty_kb_equiv D h28 h1222 h1332 h1334 h5 hLie hx hcup hKs
  have hZb := C.center_eq_bot h28 h1222 h1332 h1334 hLie
  have hZ : Subgroup.center ↥(autSub (D.autOf K) Vs) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have h1 : eK.symm z ∈ Subgroup.center ↥(modO2Image H K) :=
      (Subgroup.centerCongr eK.symm).toEquiv.toFun ⟨z, hz⟩ |>.2
    rw [hZb, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot, ← eK.apply_symm_apply z, h1, map_one]
  have hrb := C.pRank_kb h1222 h1332 h1334 h34
  have hr : CFSG.Open.pRank 3 (autSub (D.autOf K) Vs) ≤ 1 := by
    have : Finite (MulAut ↥Vs) := B42R.finite_mulAut
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup,
      ← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) eK,
      ← CFSG.SectionRank.pRank_eq_open_pRank_top, hrb]
  obtain ⟨hqX, hoddX, hLieX⟩ := kst_props hK hq hLie
  have hKG : autSub (D.autOf K) Vs ≤ autSub (D.autOf K ⊔ D.autOf T) Vs :=
    autSub_mono le_sup_left Vs
  have hfield : ∀ {F : Type} [Field F] [Finite F] {m : ℕ}, Nat.card F = 2 ^ m → 1 ≤ m :=
    fun hF => one_le_of_card_eq_pow hF
  rcases B42R.cases_of_rank hB4 hKG h2 hr hZ hconc with c1 | c2 | c5
  ·
    exfalso
    obtain ⟨-, ⟨m, hm⟩, -, -⟩ := c1
    rcases Nat.lt_or_ge m 2 with hlt | hge
    · obtain ⟨F, _, _, hF, ⟨e⟩⟩ := BinaryNaturalSL.exists_equiv hm
      have hm1 : m = 1 := by have := hfield hF; omega
      subst hm1
      have h6 : Nat.card ↥(autSub (D.autOf K) Vs) = 6 := by
        rw [← Nat.card_congr e.toEquiv,
          ← Nat.card_congr (specialLinearGroupEquivStatedSL 2 F).toEquiv,
          CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two F, hF]
        norm_num
      exact commutator_ne_top_of_card_six h6 hB4.2.2.1.1.commutator_eq_top
    · exact C.false_of_natural D hN1 h29 h28 h1222 h1332 h1334 h5 hn hLie hx hx1 ht htx hVs hst
        (Or.inl rfl) hge hm
  ·
    exfalso
    obtain ⟨-, ⟨m, hm⟩, -⟩ := c2
    rcases Nat.lt_or_ge m 2 with hlt | hge
    · obtain ⟨F, _, _, hF, ⟨e⟩⟩ := BinaryNaturalSL.exists_equiv hm
      have hm1 : m = 1 := by have := hfield hF; omega
      subst hm1
      exact false_of_equiv_sl32 hN4 hn hqX hoddX hLieX hrb (by simpa using hF)
        ((eK.trans e.symm).trans (specialLinearGroupEquivStatedSL 3 F).symm)
    · exact C.false_of_natural D hN1 h29 h28 h1222 h1332 h1334 h5 hn hLie hx hx1 ht htx hVs hst
        (Or.inr rfl) hge hm
  ·
    obtain ⟨⟨e5⟩, τ, hτ⟩ := C.exists_outer D h28 h1222 h1332 h1334 h5 hLie hx hcup hKs hTs hB4
      h2 hnorm hO2 hZ hA c5
    have := C.kbNormal
    obtain ⟨ρ, hρ⟩ := exists_bijective_s5s3 e5 (C.hc hx) ht
      (C.pow_three_of_mem h1222 h1332 h1334 hx) hx1 htx
      (fun r hr => C.mem_cent_cases h28 h1222 h1332 h1334 hLie hx hx1 ht htx hr) hτ
    refine ⟨ρ.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥H)),
      hρ.2.comp (QuotientGroup.mk'_surjective _), ?_⟩
    ext h
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← map_one ρ]
    rw [hρ.1.eq_iff, ← MonoidHom.mem_ker, QuotientGroup.ker_mk']

end CFSG.Quasithin.H13.L32A.C
