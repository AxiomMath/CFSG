module

public import CFSG.Quasithin.H13.L32AC42j
public import CFSG.Quasithin.H13.L32AC42h
public import CFSG.Quasithin.H13.L32AM50j

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open scoped IsMulCommutative

namespace Dec

variable {W : Type} [CommGroup W] [Finite W] {Vs : Subgroup W} {a : MulAut W}

theorem isSylowTwoOf_autSub (hcup : Vs ⊔ Vs.map a.toMonoidHom = ⊤) {P X : Subgroup (MulAut W)}
    (hP : IsSylowTwoOf P X) (hXs : X ≤ stabSub Vs) (hXa : ∀ g ∈ X, g * a = a * g) :
    IsSylowTwoOf (autSub P Vs) (autSub X Vs) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut W) := B42R.finite_mulAut
  have hPs : P ≤ stabSub Vs := hP.1.trans hXs
  refine ⟨autSub_mono hP.1 Vs, ?_, ?_⟩
  · exact (hP.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hPs).symm).map _
  · have h1 := (P.subgroupOf X).card_mul_index
    have h2 := ((autSub P Vs).subgroupOf (autSub X Vs)).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP.1).toEquiv] at h1
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (autSub_mono hP.1 Vs)).toEquiv,
      card_autSub hcup hPs fun g hg => hXa g (hP.1 hg), card_autSub hcup hXs hXa] at h2
    have hpos : 0 < Nat.card ↥P := Nat.card_pos
    have h3 := Nat.eq_of_mul_eq_mul_left hpos (h1.trans h2.symm)
    rw [← h3]
    exact hP.2.2

end Dec

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

namespace TopW

variable {W : Subgroup G} (D : TopW T L V H W) [IsMulCommutative ↥(conjClosure V H)]
include D

theorem isSylowTwoOf_autOf_inf {K : Subgroup G} (hKH : K ≤ H)
    (hKn : H ≤ Subgroup.normalizer (K : Set G)) : IsSylowTwoOf (D.autOf (T ⊓ K)) (D.autOf K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo D.S.hyp.fsu.sylow D.hTH
  have hKs : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hKn
  have hTK : IsSylowTwoOf (T ⊓ K) K := (show IsSylowIn 2 T H from hT).inf_normal hKH hKs
  have h := isSylowTwoOf_map_subgroupOf (D.act.comp (Subgroup.inclusion hKH)) hTK
  have e1 : ((T ⊓ K).subgroupOf K).map (D.act.comp (Subgroup.inclusion hKH)) =
      D.autOf (T ⊓ K) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨Subgroup.inclusion hKH y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hy)).2⟩, hy, rfl⟩
  have e2 : (K.subgroupOf K).map (D.act.comp (Subgroup.inclusion hKH)) = D.autOf K := by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      exact ⟨Subgroup.inclusion hKH y, Subgroup.mem_subgroupOf.mpr y.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
  rwa [e1, e2] at h

theorem act_vHat_of_trivSub {h : ↥H} (hh : (h : G) ∈ L32NSet14.trivSub V (fsuV1 T V)) :
    ∀ v ∈ vHat V H W, D.act h v = v := by
  rintro _ ⟨u, hu, rfl⟩
  rw [D.act_mk, ← mul_inv_eq_one, ← map_inv, ← map_mul, A6.A6Mod.secMk_eq_one_iff]
  apply D.hV₁W
  have := (L32NSet14.mem_trivSub.mp hh).2.2 u (Subgroup.mem_subgroupOf.mp hu)
  simpa using this

end TopW

theorem mem_trivSub_of_szB1 (hN1 : LieSylowOver3) (h29 : Thm14_7_29) (h1222 : Stmt12_2_2)
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (S : Setting147 G T L V H) {K : Subgroup G}
    (hK : K ∈ cComp H) (hq : CFSG.IsQuasisimple (cStar K))
    (hKn : H ≤ Subgroup.normalizer (K : Set G)) {n : ℕ} (hn : 1 < n)
    (hLie : A315.IsLieChar2 n (cStar K ⧸ Subgroup.center (cStar K))) (hl1K : ¬ l1 T L V ≤ K)
    {β : ↥H} (hβ : QuotientGroup.mk' (CFSG.pCore 2 ↥H) β ∈ szB1 T H K) :
    (β : G) ∈ L32NSet14.trivSub V (fsuV1 T V) := by
  classical
  have hTH : T ≤ H := Setting147.TH' S
  have hl1H : l1 T L V ≤ H := Setting147.l1H' S
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V S.hyp.hyp S.hyp.fsu).1.1
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2 S.hyp (stmt13_3_2_two_of h1332) hMod h1222
  have S14 := Hyp147.set14 S.hyp h1222 h1332 h1334 hV2
  obtain ⟨ψ, hψ⟩ := S14.exists_rep
  obtain ⟨x, hxL, hx3, hfpf⟩ := exists_l1_fpf S.hyp hMod h1222 h1332 h1334
  obtain ⟨t, htT, htL, htn⟩ := exists_TL_not_triv S.hyp h1332 S14
  have hl1 : L₁Of L (fsuV1 T V) = l1 T L V := oTwoRes_eq_oTwoUpper _
  have hx : x ∈ l1 T L V := hl1 ▸ hxL
  have hxX := S14.L1_le_X hxL
  have htX := S14.T_le_X htT
  have hψt : ψ ⟨t, htX⟩ ≠ 1 := fun h => htn ((hψ _).mp h)
  have hψt2 : ψ ⟨t, htX⟩ ^ 2 = 1 := by
    obtain ⟨k, hk⟩ := S.hyp.fsu.sylow.1 ⟨t, htT⟩
    refine L32NSet14.sl2_sq_of_two (k := k) ?_
    rw [← map_pow]
    have : (⟨t, htX⟩ : ↥(L32NSet14.nX T V)) ^ 2 ^ k = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [this, map_one]
  have hψx : ψ ⟨x, hxX⟩ ≠ 1 := by
    intro h
    have hxt := (hψ _).mp h
    have hle : V ≤ fsuV1 T V := fun v hv => hfpf v hv ((L32NSet14.mem_trivSub.mp hxt).2.2 v hv)
    have := Subgroup.card_le_of_le hle
    rw [S14.card_V, S14.card_V1] at this
    omega
  have hψx3 : ψ ⟨x, hxX⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨x, hxX⟩ : ↥(L32NSet14.nX T V)) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
    rw [this, map_one]
  have hsolv := isSolvable_szB1_l1T' hN1 h1222 h1332 h1334 S hK hq hKn hn hLie
  have hβL := mem_normalizer_L_of_solvable h29 S hsolv le_sup_right (Subgroup.mem_sup_left hβ)
  have hβX := mem_nX_of h1332 h1334 S β.2 hβL
  refine (hψ ⟨β, hβX⟩).mp ?_
  exact psi_eq_one_of_mem S S14 hψ hK hKn hl1K (oTwoUpper_le _ hx).1 hxX (hl1H hx) hψx hψx3
    htL htX (hTH htT) hψt hψt2 hβX hβL β.2 hβ.2

namespace Top42

variable {K I : Subgroup G} (C : Top42 T L V H K I) (D : TopW T L V H I)
include C D

variable [IsMulCommutative ↥(conjClosure V H)]

theorem mem_szB1_of_normalizer (h28 : Lemma14_7_28) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (h5 : Lemma14_7_5) {n : ℕ}
    (hLie : A315.IsLieChar2 n (cStar K ⧸ Subgroup.center (cStar K))) {k : ↥H} (hkK : (k : G) ∈ K)
    (hkN : D.act k ∈ Subgroup.normalizer (D.autOf (T ⊓ K) : Set (MulAut (Hat V H I)))) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥H) k ∈ szB1 T H K := by
  have : Finite (MulAut (Hat V H I)) := TopW.finite_mulAut
  have hO2T : pCoreOf 2 H ≤ T := L32A.pCoreOf_le_of_le C.S.hyp C.hTH
  have hinj := C.actS_injective D h28 h1222 h1332 h1334 h5 hLie
  show _ ∈ Subgroup.normalizer (szS1 T H K : Set (↥H ⧸ CFSG.pCore 2 ↥H)) ⊓ modO2Image H K
  refine Subgroup.mem_inf.mpr ⟨mem_normalizer_of_conj_mem_fin fun s hs => ?_,
    mem_modO2Image'.mpr ⟨k, hkK, rfl⟩⟩
  obtain ⟨⟨t, htH⟩, htT, rfl⟩ := mem_modO2Image'.mp (Subgroup.mem_inf.mp hs).1
  obtain ⟨⟨b, hbH⟩, hbK, hbt⟩ := mem_modO2Image'.mp (Subgroup.mem_inf.mp hs).2
  have hbT : b ∈ T := by
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ((⟨t, htH⟩ : ↥H)⁻¹ * ⟨b, hbH⟩) = 1 := by
      rw [map_mul, map_inv, hbt, inv_mul_cancel]
    have h2 : t⁻¹ * b ∈ T := hO2T ((mk_pCore_eq_one_iff _).mp h1)
    have e1 : b = t * (t⁻¹ * b) := by group
    rw [e1]
    exact T.mul_mem htT h2
  rw [← hbt, ← map_inv, ← map_mul, ← map_mul]
  have hbP : D.act ⟨b, hbH⟩ ∈ D.autOf (T ⊓ K) :=
    ⟨⟨b, hbH⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨hbT, hbK⟩), rfl⟩
  have h3 : D.act (k * ⟨b, hbH⟩ * k⁻¹) ∈ D.autOf (T ⊓ K) := by
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hkN _).mp hbP
  obtain ⟨b', hb', hb'e⟩ := h3
  have hb'TK := Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hb')
  have hkb : QuotientGroup.mk' (CFSG.pCore 2 ↥H) (k * ⟨b, hbH⟩ * k⁻¹) =
      QuotientGroup.mk' (CFSG.pCore 2 ↥H) b' := by
    apply hinj
    rw [D.actS_mk, D.actS_mk, hb'e]
  rw [hkb]
  exact Subgroup.mem_inf.mpr ⟨mem_modO2Image'.mpr ⟨b', hb'TK.1, rfl⟩,
    mem_modO2Image'.mpr ⟨b', hb'TK.2, rfl⟩⟩

theorem false_of_natural (hN1 : LieSylowOver3) (h29 : Thm14_7_29) (h28 : Lemma14_7_28)
    (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (h5 : Lemma14_7_5)
    {n : ℕ} (hn : 1 < n) (hLie : A315.IsLieChar2 n (cStar K ⧸ Subgroup.center (cStar K)))
    {x t : ↥H ⧸ CFSG.pCore 2 ↥H} (hx : x ∈ modO2Image H (l1 T L V)) (hx1 : x ≠ 1)
    (ht : t ∈ Subgroup.centralizer (modO2Image H K : Set (↥H ⧸ CFSG.pCore 2 ↥H)))
    (htx : t * x * t⁻¹ = x⁻¹) {Vs : Subgroup (Hat V H I)}
    (hVs : Vs ∈ IrrPlusOn (D.autOf K) (orbSup (D.autOf T) Vs) (D.autOf T))
    (hst : ∀ g ∈ D.autOf T, g ∈ stabSub Vs) {d m : ℕ} (hd : d = 2 ∨ d = 3) (hm : 2 ≤ m)
    (hnat : BinaryNaturalSL (autSub (D.autOf K) Vs) ⊤ ⊥ d m) : False := by
  classical
  have : Finite (MulAut (Hat V H I)) := TopW.finite_mulAut
  obtain ⟨-, hcap, hcup⟩ := C.isCompl_of_stab D h28 h1222 h1332 h1334 h5 hLie hx hx1 ht htx
    ⟨le_top, hVs.1.2⟩ hst
  obtain ⟨hinv, -⟩ := mem_irrPlus_top_iff.mp (⟨le_top, hVs.1.2⟩ : Vs ∈ IrrPlus (D.autOf K) ⊤)
  have hKs : D.autOf K ≤ stabSub Vs := fun g hg =>
    B5.mem_stabSub_of_inv (hinv g hg) (hinv g⁻¹ (inv_mem hg))
  have hKa : ∀ g ∈ D.autOf K, g * D.actS x = D.actS x * g :=
    fun g hg => (D.actS_comm (C.hc hx) hg).symm
  have hPK : D.autOf (T ⊓ K) ≤ D.autOf K :=
    Subgroup.map_mono fun y hy => (Subgroup.mem_inf.mp hy).2
  have hP1 := Dec.isSylowTwoOf_autSub hcup (D.isSylowTwoOf_autOf_inf C.hKH C.hKn) hKs hKa
  obtain ⟨ν, hνK, hνN, hνfix⟩ : ∃ ν ∈ autSub (D.autOf K) Vs,
      ν ∈ Subgroup.normalizer (autSub (D.autOf (T ⊓ K)) Vs : Set (MulAut ↥Vs)) ∧
        ∀ y : ↥Vs, ν y = y → y = 1 := by
    rcases hd with rfl | rfl
    · exact exists_fpf_normalizer_two hm hnat hP1
    · exact exists_fpf_normalizer_three hm hnat hP1
  obtain ⟨g, hgK, hgν⟩ := mem_autSub.mp hνK
  obtain ⟨k, hkK, hkg⟩ := id hgK
  have hkK' : ((k : ↥H) : G) ∈ K := Subgroup.mem_subgroupOf.mp hkK
  have hgN : (g : MulAut (Hat V H I)) ∈
      Subgroup.normalizer (D.autOf (T ⊓ K) : Set (MulAut (Hat V H I))) := by
    refine Subgroup.mem_normalizer_fintype fun p hp => ?_
    have hpK := hPK hp
    have hgpK : (g : MulAut (Hat V H I)) * p * (g : MulAut (Hat V H I))⁻¹ ∈ D.autOf K :=
      (D.autOf K).mul_mem ((D.autOf K).mul_mem hgK hpK) ((D.autOf K).inv_mem hgK)
    have h1 : resHom Vs ⟨_, hKs hgpK⟩ ∈ autSub (D.autOf (T ⊓ K)) Vs := by
      have e : resHom Vs ⟨_, hKs hgpK⟩ = ν * resHom Vs ⟨p, hKs hpK⟩ * ν⁻¹ := by
        rw [← hgν, ← map_inv, ← map_mul, ← map_mul]
        rfl
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp hνN _).mp (mem_autSub.mpr ⟨_, hp, rfl⟩)
    obtain ⟨p', hp'P, hp'e⟩ := mem_autSub.mp h1
    have h2 : (p' : MulAut (Hat V H I)) = (g : MulAut (Hat V H I)) * p *
        (g : MulAut (Hat V H I))⁻¹ :=
      congrArg Subtype.val (Dec.eq_of_resHom_eq hcup (hKa _ (hPK hp'P)) (hKa _ hgpK) hp'e)
    rw [← h2]
    exact hp'P
  have hkB := C.mem_szB1_of_normalizer D h28 h1222 h1332 h1334 h5 hLie hkK' (hkg ▸ hgN)
  have hkV := D.act_vHat_of_trivSub (mem_trivSub_of_szB1 hN1 h29 h1222 h1332 h1334 C.S C.hK
    C.hq C.hKn hn hLie C.hl1K hkB)
  have hcardV := D.card_vHat h1222 h1332 h1334
  obtain ⟨⟨u, huV⟩, hu1⟩ : ∃ u : ↥(vHat V H I), u ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : Nat.card ↥(vHat V H I) = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => (hcon a).trans (hcon b).symm⟩, inferInstance⟩
    omega
  obtain ⟨v, hv, w, hw, rfl⟩ := Dec.exists_eq hcup u
  have hfix := Dec.fix_parts hcap g.2 (hKa _ hgK) hv hw (by rw [← hkg]; exact hkV _ huV)
  have hv1 : (⟨v, hv⟩ : ↥Vs) = 1 :=
    hνfix _ (Subtype.ext (by rw [← hgν, resHom_apply]; exact hfix.1))
  have hw1 : (⟨w, hw⟩ : ↥Vs) = 1 :=
    hνfix _ (Subtype.ext (by rw [← hgν, resHom_apply]; exact hfix.2))
  apply hu1
  have hv1' : v = 1 := congrArg Subtype.val hv1
  have hw1' : w = 1 := congrArg Subtype.val hw1
  apply Subtype.ext
  show v * D.actS x w = 1
  rw [hv1', hw1', map_one, mul_one]

end Top42

end CFSG.Quasithin.H13.L32A.C
