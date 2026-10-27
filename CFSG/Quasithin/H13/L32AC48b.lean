module

public import CFSG.Quasithin.H13.L32AC48a
public import CFSG.Quasithin.H13.L32AC30b
public import CFSG.Quasithin.H13.L32A767n
public import CFSG.Quasithin.EmptyFaithful.S146G1
public import CFSG.Quasithin.Background.F918P1
public import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped commutatorElement

section Generic

variable {Γ : Type*} [Group Γ]

theorem mem_normalizer_of_map_conj_eq {A : Subgroup Γ} {g : Γ}
    (h : A.map (MulAut.conj g).toMonoidHom = A) : g ∈ Subgroup.normalizer (A : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hx' : g * x * g⁻¹ ∈ A.map (MulAut.conj g).toMonoidHom := ⟨x, hx, rfl⟩
    rwa [h] at hx'
  · intro hx
    rw [← h] at hx
    obtain ⟨y, hy, hye⟩ := hx
    have hyx : y = x := by
      have e : g * y * g⁻¹ = g * x * g⁻¹ := hye
      simpa using e
    rwa [← hyx]

theorem map_conj_eq_of_mem_normalizer {A : Subgroup Γ} {g : Γ}
    (hg : g ∈ Subgroup.normalizer (A : Set Γ)) : A.map (MulAut.conj g).toMonoidHom = A := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg y).mp hy
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) x).mp hx
    simpa using h1

theorem le_normalizer_commutator {A B X : Subgroup Γ}
    (hA : X ≤ Subgroup.normalizer (A : Set Γ)) (hB : X ≤ Subgroup.normalizer (B : Set Γ)) :
    X ≤ Subgroup.normalizer ((⁅A, B⁆ : Subgroup Γ) : Set Γ) := by
  intro g hg
  apply mem_normalizer_of_map_conj_eq
  rw [Subgroup.map_commutator, map_conj_eq_of_mem_normalizer (hA hg),
    map_conj_eq_of_mem_normalizer (hB hg)]

theorem map_subtype_normal_of_char {N : Subgroup Γ} [hN : N.Normal] (C : Subgroup ↥N)
    [hC : C.Characteristic] : (C.map N.subtype).Normal := by
  refine ⟨?_⟩
  rintro _ ⟨c, hc, rfl⟩ g
  let σ : MulAut ↥N := MulAut.conjNormal g
  have h1 : σ c ∈ C := by
    rw [← Subgroup.characteristic_iff_map_eq.mp hC σ]
    exact ⟨c, hc, rfl⟩
  exact ⟨σ c, h1, by simp [σ, MulAut.conjNormal_apply]⟩

end Generic

section Main

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

theorem exists_mem_cComp (h29 : Thm14_7_29) (S : Setting147 G T L V H) : ∃ K, K ∈ cComp H := by
  have hns : ¬ Group.IsSolvable ↥H := fun hs =>
    S.hz.2.2 (h29 G T L V S.hyp H S.hz.1.1 S.hz.2.1 hs)
  have hn : (H.subgroupOf H).Normal := by
    rw [Subgroup.subgroupOf_self]
    infer_instance
  obtain ⟨K, hK, -⟩ := exists_cComp_le_of_not_solvable le_rfl hn hns
  exact ⟨K, hK⟩

theorem le_commutator_l1 (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (h : Hyp147 G T L V) : V ≤ ⁅V, l1 T L V⁆ := by
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  obtain ⟨V₂, z, a, b, x, y, hV2, hz0, hz1, ha, haV, hb, hbV, hxL, hyL, hxa, hxb, hya⟩ :=
    exists_basis_l1_of h hMod h1222 h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V h.hyp h.fsu).1.1
  have S14 := h.set14 h1222 h1332 h1334 hV2
  have e : l1 T L V = L₁Of L (fsuV1 T V) := by rw [L₁Of, oTwoRes_eq_oTwoUpper]
  rw [e]
  have hcomm : ∀ {v l : G}, v ∈ V → l ∈ L₁Of L (fsuV1 T V) →
      l * v * l⁻¹ * v⁻¹ ∈ ⁅V, L₁Of L (fsuV1 T V)⁆ := by
    intro v l hv hl
    have h2 := Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator hv hl)
    rwa [commutatorElement_inv, commutatorElement_def] at h2
  have haV' : a ∈ V := hV2.2.1 ha
  have ha_mem : a ∈ ⁅V, L₁Of L (fsuV1 T V)⁆ := by
    have h2 := hcomm hb hxL
    rwa [hxb, mul_inv_cancel_right] at h2
  have hba : b * a⁻¹ ∈ ⁅V, L₁Of L (fsuV1 T V)⁆ := by
    have h2 := hcomm haV' hxL
    rwa [hxa] at h2
  have hz_mem : z ∈ ⁅V, L₁Of L (fsuV1 T V)⁆ := by
    have h2 := hcomm haV' hyL
    rwa [hya, mul_inv_cancel_right] at h2
  have hb_mem : b ∈ ⁅V, L₁Of L (fsuV1 T V)⁆ := by
    have h2 := Subgroup.mul_mem _ hba ha_mem
    rwa [inv_mul_cancel_right] at h2
  have hV1 : ∀ w ∈ fsuV1 T V, w ∈ ⁅V, L₁Of L (fsuV1 T V)⁆ := by
    intro w hw
    rcases S14.eq_of_mem_V1 hz0 hz1 hw with rfl | rfl
    · exact Subgroup.one_mem _
    · exact hz_mem
  have hV2' : ∀ w ∈ V₂, w ∈ ⁅V, L₁Of L (fsuV1 T V)⁆ := by
    intro w hw
    rcases S14.mem_V2 ha haV hw with hw1 | hw1
    · exact hV1 w hw1
    · have e2 : w = a⁻¹ * (a * w) := by group
      rw [e2]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ ha_mem) (hV1 _ hw1)
  intro v hv
  rcases S14.mem_V hb hbV hv with hv2 | hv2
  · exact hV2' v hv2
  · have e2 : v = b⁻¹ * (b * v) := by group
    rw [e2]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hb_mem) (hV2' _ hv2)

omit [Finite G] in
theorem conjClosure_eq_commutator (hVL : V ≤ ⁅V, l1 T L V⁆) {K : Subgroup G} (hKH : K ≤ H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) (hL1K : l1 T L V ≤ K) :
    conjClosure V H = ⁅conjClosure V H, K⁆ := by
  have hHU : H ≤ Subgroup.normalizer (conjClosure V H : Set G) := le_normalizer_conjClosure V H
  apply le_antisymm
  · have hN := le_normalizer_commutator hHU hHK
    refine conjClosure_le fun g hg v hv => ?_
    have hvC : v ∈ ⁅conjClosure V H, K⁆ :=
      Subgroup.commutator_mono (le_conjClosure V H) hL1K (hVL hv)
    exact (Subgroup.mem_normalizer_iff.mp (hN hg) v).mp hvC
  · rw [Subgroup.commutator_le]
    intro u hu k hk
    rw [commutatorElement_def]
    have hku : k * u⁻¹ * k⁻¹ ∈ conjClosure V H :=
      (Subgroup.mem_normalizer_iff.mp (hHU (hKH hk)) u⁻¹).mp (Subgroup.inv_mem _ hu)
    have e2 : u * k * u⁻¹ * k⁻¹ = u * (k * u⁻¹ * k⁻¹) := by group
    rw [e2]
    exact Subgroup.mul_mem _ hu hku

theorem eq_of_mem_cComp (h37 : A37ForSQTK) (S : Setting147 G T L V H)
    (hL3 : (pCoreOf 2 (l1 T L V)).relIndex (l1 T L V) = 3) {K₁ K₂ : Subgroup G}
    (h₁ : K₁ ∈ cComp H) (h₂ : K₂ ∈ cComp H) (hL₁ : l1 T L V ≤ K₁) (hL₂ : l1 T L V ≤ K₂)
    (hZ : Subgroup.center (cStar K₁) = ⊥) : K₁ = K₂ := by
  by_contra hne
  have h := S.hyp
  obtain ⟨hc, -⟩ :=
    lemma_1_2_1_two h.fsu.qtke h.fsu.simple h.fsu.nonabelian h37 S.hz.1.2 h₁ h₂ hne
  have hO : l1 T L V ≤ pCoreOf 2 K₁ := by
    intro l hl
    have hl1 : l ∈ K₁ := hL₁ hl
    have hcen : (QuotientGroup.mk (⟨l, hl1⟩ : ↥K₁) : cStar K₁) ∈ Subgroup.center (cStar K₁) := by
      rw [Subgroup.mem_center_iff]
      intro q
      obtain ⟨⟨k, hk⟩, rfl⟩ := QuotientGroup.mk_surjective q
      have hkl : ⁅k, l⁆ ∈ pCoreOf 2 K₁ :=
        (Subgroup.mem_inf.mp (hc (Subgroup.commutator_mem_commutator hk (hL₂ hl)))).1
      have hkl' : ⁅(⟨k, hk⟩ : ↥K₁), (⟨l, hl1⟩ : ↥K₁)⁆ ∈ (pCoreOf 2 K₁).subgroupOf K₁ := by
        rw [Subgroup.mem_subgroupOf]
        exact hkl
      have h1 : (QuotientGroup.mk ⁅(⟨k, hk⟩ : ↥K₁), (⟨l, hl1⟩ : ↥K₁)⁆ : cStar K₁) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr hkl'
      have h2 : ⁅(QuotientGroup.mk (⟨k, hk⟩ : ↥K₁) : cStar K₁),
          (QuotientGroup.mk (⟨l, hl1⟩ : ↥K₁) : cStar K₁)⁆ = 1 := by
        rw [← h1]
        exact (map_commutatorElement (QuotientGroup.mk' ((pCoreOf 2 K₁).subgroupOf K₁)) _ _).symm
      exact commutatorElement_eq_one_iff_mul_comm.mp h2
    rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hcen
    exact hcen
  have hp : IsPGroup 2 ↥(l1 T L V) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K₁).to_le hO
  have hle : l1 T L V ≤ pCoreOf 2 (l1 T L V) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_rfl Subgroup.le_normalizer hp
  have h1 := Subgroup.relIndex_eq_one.mpr hle
  omega

theorem cComp_top_eq {K : Subgroup G} (hK : cComp H = {K}) :
    cComp (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) = {modO2Image H K} := by
  ext K'
  constructor
  · intro hK'
    obtain ⟨K'', hK'', rfl⟩ := (modO2Image_bijOn H).surjOn hK'
    rw [hK, Set.mem_singleton_iff] at hK''
    rw [hK'']
    exact Set.mem_singleton _
  · intro h'
    rw [Set.mem_singleton_iff.mp h']
    exact modO2Image_mem_cComp (by rw [hK]; exact Set.mem_singleton K)

theorem centralizer_eq_bot (h28 : Lemma14_7_28) (S : Setting147 G T L V H) {K : Subgroup G}
    (hK : cComp H = {K}) (hL1K : l1 T L V ≤ K) (hKbn : (modO2Image H K).Normal)
    (hZ : Subgroup.center ↥(modO2Image H K) = ⊥) :
    Subgroup.centralizer (modO2Image H K : Set (↥H ⧸ CFSG.pCore 2 ↥H)) = ⊥ := by
  set Q := ↥H ⧸ CFSG.pCore 2 ↥H with hQ
  set Kb := modO2Image H K with hKb
  set C := Subgroup.centralizer (Kb : Set Q) with hCdef
  have hCK : C ⊓ Kb = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxC, hxK⟩
    have hx : (⟨x, hxK⟩ : ↥Kb) ∈ Subgroup.center ↥Kb := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC y y.2)
    rw [hZ, Subgroup.mem_bot] at hx
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hx
  have hCn : C.Normal := Subgroup.normal_centralizer
  have hKmem : K ∈ cComp H := by rw [hK]; exact Set.mem_singleton K
  have hsolv : Group.IsSolvable ↥C := by
    by_contra hns
    have hn : (C.subgroupOf ⊤).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_top]
      rw [Subgroup.normalizer_eq_top_iff.mpr hCn]
    obtain ⟨K', hK', hK'C⟩ := exists_cComp_le_of_not_solvable le_top hn hns
    rw [cComp_top_eq hK, Set.mem_singleton_iff] at hK'
    rw [hK'] at hK'C
    have hb : Kb = ⊥ := le_bot_iff.mp (hCK ▸ le_inf hK'C le_rfl)
    exact (modO2Image_mem_cComp hKmem).1 hb
  have hO2 : CFSG.pCore 2 Q = ⊥ := CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot
  have hoK : CFSG.oddCore Q ≤ Kb := by
    rcases h28 G T L V H S with h0 | h1
    · rw [h0]
      exact bot_le
    · rw [h1]
      exact Subgroup.map_mono fun x hx =>
        Subgroup.mem_subgroupOf.mpr (hL1K (Subgroup.mem_subgroupOf.mp hx))
  have hcore : ∀ p : ℕ, p.Prime → CFSG.pCore p ↥C = ⊥ := by
    intro p hp
    have : Fact p.Prime := ⟨hp⟩
    have hPn : ((CFSG.pCore p ↥C).map C.subtype).Normal := map_subtype_normal_of_char _
    have hPp : IsPGroup p ↥((CFSG.pCore p ↥C).map C.subtype) :=
      CFSG.pCore_isPGroup.map C.subtype
    have hPC : (CFSG.pCore p ↥C).map C.subtype ≤ C := Subgroup.map_subtype_le _
    have hPK : (CFSG.pCore p ↥C).map C.subtype ≤ Kb := by
      by_cases hp2 : p = 2
      · subst hp2
        have h1 : (CFSG.pCore 2 ↥C).map C.subtype ≤ CFSG.pCore 2 Q := le_sSup ⟨hPn, hPp⟩
        rw [hO2] at h1
        exact h1.trans bot_le
      · obtain ⟨k, hk⟩ := hPp.exists_card_eq
        have hodd : Odd (Nat.card ↥((CFSG.pCore p ↥C).map C.subtype)) := by
          rw [hk]
          exact (hp.odd_of_ne_two hp2).pow
        have h1 : (CFSG.pCore p ↥C).map C.subtype ≤ CFSG.oddCore Q := le_sSup ⟨hPn, hodd⟩
        exact h1.trans hoK
    have hbot : (CFSG.pCore p ↥C).map C.subtype = ⊥ := le_bot_iff.mp (hCK ▸ le_inf hPC hPK)
    exact (Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective).mp hbot
  have hF : CFSG.fittingSubgroup ↥C = ⊥ := by
    rw [CFSG.LocalCores.fittingSubgroup_eq_iSup_pCore]
    exact iSup_eq_bot.mpr fun p => hcore p (Nat.prime_of_mem_primeFactors p.2)
  have hcard := (CFSG.fitting_eq_bot_iff_card_eq_one_of_solvable ↥C).mp hF
  exact Subgroup.eq_bot_of_card_eq C hcard

theorem index_dvd_card_outer {Q : Type*} [Group Q] {Kb : Subgroup Q} [Kb.Normal]
    (hC : Subgroup.centralizer (Kb : Set Q) = ⊥) : Kb.index ∣ Nat.card (Outer ↥Kb) := by
  let φ : Q →* MulAut ↥Kb := MulAut.conjNormal
  let ψ : Q →* Outer ↥Kb := (QuotientGroup.mk' (inner ↥Kb)).comp φ
  have hker : ψ.ker = Kb := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    constructor
    · rintro ⟨k, hk⟩
      have hc : x * (k : Q)⁻¹ ∈ Subgroup.centralizer (Kb : Set Q) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hy' : (k : Q)⁻¹ * y * (k : Q) ∈ Kb :=
          Kb.mul_mem (Kb.mul_mem (Kb.inv_mem k.2) hy) k.2
        have h1 := congrArg (fun f : MulAut ↥Kb => ((f ⟨_, hy'⟩ : ↥Kb) : Q)) hk
        simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv, φ,
          MulAut.conjNormal_apply] at h1
        have h2 : y = x * ((k : Q)⁻¹ * y * (k : Q)) * x⁻¹ := by
          rw [← h1]
          group
        calc y * (x * (k : Q)⁻¹) = x * ((k : Q)⁻¹ * y * (k : Q)) * x⁻¹ * (x * (k : Q)⁻¹) := by
              rw [← h2]
          _ = x * (k : Q)⁻¹ * y := by group
      rw [hC, Subgroup.mem_bot, mul_inv_eq_one] at hc
      rw [hc]
      exact k.2
    · intro hx
      refine ⟨⟨x, hx⟩, ?_⟩
      ext y
      simp [φ, MulAut.conjNormal_apply, MulAut.conj_apply]
  have e := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivRange ψ)
  rw [Subgroup.index, Nat.card_congr e.toEquiv]
  exact Subgroup.card_subgroup_dvd_card ψ.range

theorem eq_sup_of_index (S : Setting147 G T L V H) {K : Subgroup G} (hKH : K ≤ H)
    (hKbn : (modO2Image H K).Normal) {j : ℕ} (hj : (modO2Image H K).index = 2 ^ j) :
    H = K ⊔ T := by
  have h := S.hyp
  have hTH : T ≤ H := le_sup_right.trans S.hz.1.1
  have hTsyl : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow hTH
  set Q := ↥H ⧸ CFSG.pCore 2 ↥H with hQ
  set f : ↥H →* Q := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hf
  have hfs : Function.Surjective f := QuotientGroup.mk'_surjective _
  have hOT : CFSG.pCore 2 ↥H ≤ T.subgroupOf H := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    have hx' : (x : G) ∈ pCoreOf 2 H := by
      refine ⟨x, ?_, rfl⟩
      assumption
    exact L32A.pCoreOf_le_of_le h hTH hx'
  have hTidx : (modO2Image H T).index = (T.subgroupOf H).index := by
    refine Subgroup.index_map_eq (T.subgroupOf H) hfs ?_
    rw [QuotientGroup.ker_mk']
    exact hOT
  have hsup : modO2Image H K ⊔ modO2Image H T = ⊤ := by
    have h1 : (modO2Image H K ⊔ modO2Image H T).index ∣ 2 ^ j :=
      hj ▸ Subgroup.index_dvd_of_le le_sup_left
    have h2 : (modO2Image H K ⊔ modO2Image H T).index ∣ (T.subgroupOf H).index :=
      hTidx ▸ Subgroup.index_dvd_of_le le_sup_right
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
    have hi0 : i = 0 := by
      by_contra hi0
      apply hTsyl.2.2
      have h3 : 2 ∣ (modO2Image H K ⊔ modO2Image H T).index := by
        rw [hi]
        exact dvd_pow_self 2 hi0
      exact h3.trans h2
    rw [hi0, pow_zero] at hi
    exact Subgroup.index_eq_one.mp hi
  apply le_antisymm _ (sup_le hKH hTH)
  intro x hx
  have hmem : f ⟨x, hx⟩ ∈ modO2Image H K ⊔ modO2Image H T := hsup ▸ Subgroup.mem_top _
  obtain ⟨y, ⟨k, hk, rfl⟩, z, ⟨t, ht, rfl⟩, hyz⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
  have hfeq : f (k * t) = f ⟨x, hx⟩ := by
    rw [map_mul]
    exact hyz
  have hq : (k * t)⁻¹ * ⟨x, hx⟩ ∈ CFSG.pCore 2 ↥H := by
    rw [hf, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hfeq
    exact hfeq
  have hqT : ((k * t)⁻¹ * ⟨x, hx⟩ : ↥H) ∈ T.subgroupOf H := hOT hq
  rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hk ht
  rw [Subgroup.mem_subgroupOf] at hqT
  have e : x = (k : G) * ((t : G) * (((k * t)⁻¹ * ⟨x, hx⟩ : ↥H) : G)) := by
    simp [mul_assoc]
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hk)
    (Subgroup.mul_mem _ (Subgroup.mem_sup_right ht) (Subgroup.mem_sup_right hqT))


theorem IsList47.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (h : IsList47 X) :
    IsList47 Y := by
  rcases h with ⟨n, hn⟩ | ⟨n, hn⟩ | hu
  · exact Or.inl ⟨n, isPSL_congr e hn⟩
  · exact Or.inr (Or.inl ⟨n, isAlt_congr e hn⟩)
  · exact Or.inr (Or.inr (isPSU_congr e hu))

theorem lemma14_7_48_of (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (h37 : A37ForSQTK) (h28 : Lemma14_7_28) (h29 : Thm14_7_29) (h30 : Lemma14_7_30)
    (h47 : Lemma14_7_47) : Lemma14_7_48 := by
  intro G _ _ T L V H S
  have hL3 := relIndex_l1 h1222 h1332 h1334 S.hyp
  obtain ⟨K, hK⟩ := exists_mem_cComp h29 S
  have hq : ∀ K' ∈ cComp H, CFSG.IsQuasisimple (cStar K') := fun K' hK' =>
    (h30 G T L V H S K' hK').1
  have hlist : ∀ K' ∈ cComp H, IsList47 (cStar K') := fun K' hK' =>
    (h47 G T L V H S K' hK').2
  have hl1 : ∀ K' ∈ cComp H, l1 T L V ≤ K' := fun K' hK' => (h47 G T L V H S K' hK').1
  have hZ : ∀ K' ∈ cComp H, Subgroup.center (cStar K') = ⊥ := fun K' hK' =>
    center_eq_bot_of_list47 (hq K' hK') (hlist K' hK')
  have huniq : cComp H = {K} := by
    ext K'
    rw [Set.mem_singleton_iff]
    constructor
    · intro hK'
      exact eq_of_mem_cComp h37 S hL3 hK' hK (hl1 K' hK') (hl1 K hK) (hZ K' hK')
    · rintro rfl
      exact hK
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hHK : H ≤ Subgroup.normalizer (K : Set G) := by
    intro g hg
    apply mem_normalizer_of_map_conj_eq
    have h1 := map_conj_mem_cComp hK hg
    rw [huniq, Set.mem_singleton_iff] at h1
    exact h1
  have hKn : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hHK
  have hKbn : (modO2Image H K).Normal := hKn.map _ (QuotientGroup.mk'_surjective _)
  obtain ⟨e⟩ := modO2_mulEquiv hK
  let e' : cStar K ≃* ↥(modO2Image H K) :=
    (QuotientGroup.quotientMulEquivOfEq (subgroupOf_pCoreOf_eq_pCore K)).trans e
  have hqb : CFSG.IsQuasisimple ↥(modO2Image H K) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e' (hq K hK)
  have hlb : IsList47 ↥(modO2Image H K) := (hlist K hK).of_mulEquiv e'
  have hZb := center_eq_bot_of_list47 hqb hlb
  have hC := centralizer_eq_bot h28 S huniq (hl1 K hK) hKbn hZb
  have hdvd := index_dvd_card_outer hC
  have : Finite (MulAut ↥(modO2Image H K)) :=
    Finite.of_injective (fun f : MulAut ↥(modO2Image H K) => (f : ↥(modO2Image H K) → _))
      DFunLike.coe_injective
  obtain ⟨m, hm⟩ := (isPGroup_two_outer_of_list47 hqb hlb).exists_card_eq
  rw [hm] at hdvd
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  exact ⟨K, huniq, eq_sup_of_index S hKH hKbn hj,
    conjClosure_eq_commutator (le_commutator_l1 h1222 h1332 h1334 S.hyp) hKH hHK (hl1 K hK)⟩

end Main

end CFSG.Quasithin.H13.L32A.C
