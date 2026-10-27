module

public import CFSG.Quasithin.Background.C31SporPull
public import CFSG.Foundations.SteinbergCADefinitionNodes

public section

namespace CFSG.Quasithin.C31Spor

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank C48Spor
open scoped commutatorElement

@[expose] def QuasiNoTwo (Y : Type) [Group Y] : Prop :=
  CFSG.Open.IsQuasisimple Y ∧ ∀ N : Subgroup Y, N.Normal → IsPGroup 2 ↥N → N = ⊥

theorem quasiNoTwo_of_isSimpleGroup {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup Y]
    (hp : ¬ (Nat.card Y).Prime) : QuasiNoTwo Y := by
  have hnc : ¬ ∀ a b : Y, a * b = b * a := by
    intro hab
    let _ : CommGroup Y := { (inferInstance : Group Y) with mul_comm := hab }
    exact hp (IsSimpleGroup.prime_card (α := Y))
  have hZ : Subgroup.center Y = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Y) with h | h
    · exact h
    · exact absurd (fun a b => Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a) hnc
  refine ⟨⟨?_, ?_⟩, fun N hN h2 => ?_⟩
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator Y) with h | h
    · exfalso
      refine hnc fun a b => ?_
      have : ⁅a, b⁆ ∈ commutator Y := Subgroup.commutator_mem_commutator (Subgroup.mem_top a)
        (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      exact this
    · exact h
  · exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).isSimpleGroup
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
    · exact h
    · exfalso
      have hY2 : IsPGroup 2 Y :=
        h2.of_equiv ((MulEquiv.subgroupCongr h).trans Subgroup.topEquiv)
      have : Nontrivial Y := IsSimpleGroup.toNontrivial
      exact (Subgroup.nontrivial_iff_ne_bot _).mp hY2.center_nontrivial hZ

theorem quasiNoTwo_of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : QuasiNoTwo Y') : QuasiNoTwo Y := by
  obtain ⟨hq, h2⟩ := h
  refine ⟨?_, fun N hN hp => ?_⟩
  · exact (CFSG.Foundations.SteinbergCA.quasisimple_iff Y).2.2.1.1
      (CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm
        ((CFSG.Foundations.SteinbergCA.quasisimple_iff Y').2.2.1.2 hq))
  · have h1 := h2 (N.map e.toMonoidHom) (hN.map _ e.surjective)
      (hp.map e.toMonoidHom)
    rw [eq_bot_iff] at h1 ⊢
    intro x hx
    have := h1 (Subgroup.mem_map_of_mem e.toMonoidHom hx)
    rw [Subgroup.mem_bot] at this ⊢
    exact e.injective (this.trans e.map_one.symm)

theorem quasiNoTwo_of_isPSL {n e : ℕ} {Y : Type} [Group Y] [Finite Y] (h : IsPSL n 2 e Y)
    (hp : ¬ (Nat.card Y).Prime) : QuasiNoTwo Y := by
  have := (CFSG.LieType.Simplicity.fam_PSL_simplicity Y n 2 e h).2
  exact quasiNoTwo_of_isSimpleGroup hp

theorem quasiNoTwo_L24 {Y : Type} [Group Y] [Finite Y] (h : IsPSL 2 2 2 Y) : QuasiNoTwo Y :=
  quasiNoTwo_of_isPSL h (by rw [card_of_isPSL_two_two_two h]; norm_num)

theorem quasiNoTwo_L32 {Y : Type} [Group Y] [Finite Y] (h : IsPSL 3 2 1 Y) : QuasiNoTwo Y :=
  quasiNoTwo_of_isPSL h (by rw [GoldS146R.card_of_isPSL_three_two h]; norm_num)

theorem quasiNoTwo_L42 {Y : Type} [Group Y] [Finite Y] (h : IsPSL 4 2 1 Y) : QuasiNoTwo Y :=
  quasiNoTwo_of_isPSL h (by rw [card_of_isPSL_four_two h]; norm_num)

theorem quasiNoTwo_L52 {Y : Type} [Group Y] [Finite Y] (h : IsPSL 5 2 1 Y) : QuasiNoTwo Y :=
  quasiNoTwo_of_isPSL h (by rw [card_of_isPSL_five_two h]; norm_num)

theorem quasiNoTwo_U33 {Y : Type} [Group Y] [Finite Y] (h : IsPSU 3 3 1 Y) : QuasiNoTwo Y := by
  have := (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity Y 3 3 1 h).2
  exact quasiNoTwo_of_isSimpleGroup (by rw [card_of_isPSU_three_three h]; norm_num)

theorem quasiNoTwo_alt {n : ℕ} (hn : 5 ≤ n) (hcard : ¬ (Nat.card (alternatingGroup (Fin n))).Prime)
    {Y : Type} [Group Y] (h : IsAlt n Y) : QuasiNoTwo Y := by
  obtain ⟨e⟩ := h
  have : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by simpa using hn)
  exact quasiNoTwo_of_mulEquiv e (quasiNoTwo_of_isSimpleGroup hcard)

theorem quasiNoTwo_A6 {Y : Type} [Group Y] (h : IsAlt 6 Y) : QuasiNoTwo Y :=
  quasiNoTwo_alt (by norm_num) (by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    norm_num [Nat.factorial]) h

theorem quasiNoTwo_A7 {Y : Type} [Group Y] (h : IsAlt 7 Y) : QuasiNoTwo Y :=
  quasiNoTwo_alt (by norm_num) (by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    norm_num [Nat.factorial]) h

theorem quasiNoTwo_M24 {Y : Type} [Group Y]
    (h : IsSporadic .M24 Y) : QuasiNoTwo Y := by
  obtain ⟨e⟩ := h
  obtain ⟨_, -, hs⟩ := CFSG.Sporadic.Mathieu.fam_m24_simplicity
  have e' : Y ≃* ↥CFSG.Blueprint.NativeSporadic.M24 := e
  exact quasiNoTwo_of_mulEquiv e' (quasiNoTwo_of_isSimpleGroup
    (by rw [CFSG.Sporadic.Mathieu.card_M24]; norm_num))

theorem quasiNoTwo_hatA6 {Y : Type} [Group Y] [Finite Y] (h : IsHat Y ↥(alternatingGroup (Fin 6))) :
    QuasiNoTwo Y := by
  obtain ⟨hq, hc, -⟩ := h
  have hq' : CFSG.Open.IsQuasisimple Y :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff Y).2.2.1.1 hq
  refine ⟨hq', fun N hN h2 => ?_⟩
  rcases le_center_or_eq_top_of_normal hq' hN with hZ | hT
  ·
    obtain ⟨k, hk⟩ := h2.exists_card_eq
    have hdvd : Nat.card ↥N ∣ 3 := hc ▸ Subgroup.card_dvd_of_le hZ
    rw [hk] at hdvd
    refine Subgroup.eq_bot_of_card_eq _ (hk.trans ?_)
    rcases k with _ | k
    · rfl
    · exfalso
      have : 2 ∣ 3 := (dvd_pow_self 2 (Nat.succ_ne_zero k)).trans hdvd
      omega
  ·
    exfalso
    have hY2 : IsPGroup 2 Y := h2.of_equiv ((MulEquiv.subgroupCongr hT).trans Subgroup.topEquiv)
    obtain ⟨k, hk⟩ := hY2.exists_card_eq
    have hdvd : 3 ∣ Nat.card Y := hc ▸ Subgroup.card_subgroup_dvd_card _
    rw [hk] at hdvd
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd) (by norm_num)

variable {G : Type} [Group G] [Finite G] {H R M L V K : Subgroup G}

theorem not_isPGroup_of_perfect {L₀ : Subgroup G} (hne : L₀ ≠ ⊥) (hperf : ⁅L₀, L₀⁆ = L₀) :
    ¬ IsPGroup 2 ↥L₀ := by
  intro hp
  have : Group.IsNilpotent ↥L₀ := hp.isNilpotent
  have : Nontrivial ↥L₀ := (Subgroup.nontrivial_iff_ne_bot L₀).mpr hne
  have : Group.IsPerfect ↥L₀ := by
    rw [Group.isPerfect_def, _root_.commutator_def]
    apply Subgroup.map_injective L₀.subtype_injective
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hperf]
  exact Group.IsPerfect.not_isNilpotent ↥L₀ inferInstance

omit [Finite G] in
theorem isPGroup_of_map_eq_bot {M₀ L₀ : Subgroup G} (hL₀ : L₀ ≤ M₀) {Y : Type} [Group Y]
    {ψ : ↥M₀ →* Y} (hker : IsPGroup 2 ↥ψ.ker) (h : (L₀.subgroupOf M₀).map ψ = ⊥) :
    IsPGroup 2 ↥L₀ := by
  have hle : L₀.subgroupOf M₀ ≤ ψ.ker := fun x hx =>
    (Subgroup.mem_bot.mp (h ▸ Subgroup.mem_map_of_mem ψ hx))
  exact ((hker.to_le hle).of_equiv (Subgroup.subgroupOfEquivOfLe hL₀))

theorem eq_conjClosure_of_quotient (hA3 : A3Orbits G) (h : HypC28 H R M L V) {Y : Type}
    [Group Y] (ψ : ↥(conjClosure L M) →* Y) (hψ : Function.Surjective ψ)
    (hker : IsPGroup 2 ↥ψ.ker) (hY : QuasiNoTwo Y) : L = conjClosure L M := by
  obtain ⟨T, hT, -⟩ := CFSG.QuasithinUnique.EscapingLocal.exists_isSylowTwoOf_ge
    (bot_le : (⊥ : Subgroup G) ≤ M) IsPGroup.of_bot
  obtain ⟨-, hcase, -⟩ := c2_9_one hA3 h hT
  rcases hcase with hL | ⟨L₂, -, -, heq, hLc, hL2c, hcomm, hint⟩
  · exact hL.symm
  exfalso
  obtain ⟨hq, hY2⟩ := hY
  have hLM : L ≤ conjClosure L M := heq ▸ le_sup_left
  have hL2M : L₂ ≤ conjClosure L M := heq ▸ le_sup_right
  have hOsub : (pCoreOf 2 (conjClosure L M)).subgroupOf (conjClosure L M) =
      CFSG.Open.pCore 2 ↥(conjClosure L M) :=
    Subgroup.comap_map_eq_self_of_injective (conjClosure L M).subtype_injective _
  have hkerO : ψ.ker ≤ (pCoreOf 2 (conjClosure L M)).subgroupOf (conjClosure L M) := by
    rw [hOsub]
    exact CFSG.LieType.BorelTits.le_pCore 2 (MonoidHom.normal_ker ψ) hker
  have hO : ((pCoreOf 2 (conjClosure L M)).subgroupOf (conjClosure L M)).map ψ = ⊥ := by
    refine hY2 _ ?_ ?_
    · rw [hOsub]
      exact (CFSG.LieType.BorelTits.pCore_normal 2).map ψ hψ
    · rw [hOsub]
      exact (CFSG.LieType.BorelTits.pCore_isPGroup 2).map ψ
  have hsup : (L.subgroupOf (conjClosure L M)).map ψ ⊔ (L₂.subgroupOf (conjClosure L M)).map ψ =
      ⊤ := by
    rw [← Subgroup.map_sup, ← Subgroup.subgroupOf_sup hLM hL2M]
    conv_lhs => rw [← heq]
    rw [Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr hψ]
  have hcommAB : ⁅(L.subgroupOf (conjClosure L M)).map ψ,
      (L₂.subgroupOf (conjClosure L M)).map ψ⁆ = ⊥ := by
    rw [← Subgroup.map_commutator, eq_bot_iff, ← hO]
    apply Subgroup.map_mono
    rw [← commutator_subgroupOf_of_le hLM hL2M]
    exact fun x hx => hcomm hx
  have hinf : (L.subgroupOf (conjClosure L M)).map ψ ⊓ (L₂.subgroupOf (conjClosure L M)).map ψ =
      ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyA, hyB⟩
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hyA
    obtain ⟨b, hb, hab⟩ := Subgroup.mem_map.mp hyB
    have hk : a⁻¹ * b ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hab, inv_mul_cancel]
    have hbO : (b : G) ∈ pCoreOf 2 (conjClosure L M) := by
      have h1 : (b : G) ∈ (L ⊔ pCoreOf 2 (conjClosure L M)) ⊓
          (L₂ ⊔ pCoreOf 2 (conjClosure L M)) := by
        refine ⟨?_, Subgroup.mem_sup_left hb⟩
        have := Subgroup.mul_mem _ (Subgroup.mem_sup_left (S := L)
          (T := pCoreOf 2 (conjClosure L M)) ha) (Subgroup.mem_sup_right (S := L)
          (T := pCoreOf 2 (conjClosure L M)) (hkerO hk))
        simpa using this
      rwa [hint] at h1
    have : ψ b ∈ ((pCoreOf 2 (conjClosure L M)).subgroupOf (conjClosure L M)).map ψ :=
      Subgroup.mem_map_of_mem ψ hbO
    rw [hO, hab] at this
    exact this
  have hnorm : ∀ {X Z : Subgroup Y}, X ⊔ Z = ⊤ → (∀ x ∈ X, ∀ z ∈ Z, x * z = z * x) →
      X.Normal := by
    intro X Z hXZ hxz
    have hle : X ⊔ Z ≤ Subgroup.normalizer (X : Set Y) := by
      refine sup_le Subgroup.le_normalizer fun z hz => ?_
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        rw [← hxz x hx z hz, mul_inv_cancel_right]
        exact hx
      · intro hx
        have h1 := hxz _ hx z hz
        simp only [inv_mul_cancel_right] at h1
        have h2 : x = z * x * z⁻¹ := mul_left_cancel h1
        rw [h2]
        exact hx
    rw [hXZ] at hle
    exact Subgroup.normalizer_eq_top_iff.mp (eq_top_iff.mpr hle)
  have hAB : ∀ a ∈ (L.subgroupOf (conjClosure L M)).map ψ,
      ∀ b ∈ (L₂.subgroupOf (conjClosure L M)).map ψ, a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommAB ha) b hb).symm
  have hAn := hnorm hsup hAB
  have hBn := hnorm (X := (L₂.subgroupOf (conjClosure L M)).map ψ)
    (Z := (L.subgroupOf (conjClosure L M)).map ψ) (by rw [sup_comm]; exact hsup)
    fun b hb a ha => (hAB a ha b hb).symm
  have hLp : ¬ IsPGroup 2 ↥L := not_isPGroup_of_perfect hLc.1 hLc.2.1
  have hL2p : ¬ IsPGroup 2 ↥L₂ := not_isPGroup_of_perfect hL2c.1 hL2c.2.1
  rcases le_center_or_eq_top_of_normal hq hAn with hAc | hAt
  · rcases le_center_or_eq_top_of_normal hq hBn with hBc | hBt
    ·
      have hZ : Subgroup.center Y = ⊤ := top_le_iff.mp (hsup ▸ sup_le hAc hBc)
      obtain ⟨-, hsimp⟩ := hq
      have hsub : Subsingleton (Y ⧸ Subgroup.center Y) := by
        rw [hZ]
        exact QuotientGroup.subsingleton_quotient_top
      exact (not_subsingleton _) hsub
    · apply hLp
      refine isPGroup_of_map_eq_bot hLM hker ?_
      rw [eq_bot_iff, ← hinf, hBt, inf_top_eq]
  · apply hL2p
    refine isPGroup_of_map_eq_bot hL2M hker ?_
    rw [eq_bot_iff, ← hinf, hAt, top_inf_eq]

theorem eq_conjClosure_of_isExt (hA3 : A3Orbits G) (h : HypC28 H R M L V)
    {PV PY : ∀ (V : Type) [Group V], Prop}
    (hPV : ∀ {A : Type} [Group A] [Finite A], PV A → IsPGroup 2 A)
    (hPY : ∀ {Y : Type} [Group Y] [Finite Y], PY Y → QuasiNoTwo Y)
    (hext : IsExt ↥(conjClosure L M) PV PY) : L = conjClosure L M := by
  obtain ⟨E, hE, hpv, hpy⟩ := hext
  refine eq_conjClosure_of_quotient hA3 h (QuotientGroup.mk' E) (QuotientGroup.mk'_surjective E)
    ?_ (hPY hpy)
  rw [QuotientGroup.ker_mk']
  exact hPV hpv

theorem eq_conjClosure_of_isExt_imageModCenter (hA3 : A3Orbits G) (h : HypC28 H R M L V)
    (h31 : C31Basic H R M L V K) {PV PY : ∀ (V : Type) [Group V], Prop}
    (hPV : ∀ {A : Type} [Group A] [Finite A], PV A → IsPGroup 2 A)
    (hPY : ∀ {Y : Type} [Group Y] [Finite Y], PY Y → QuasiNoTwo Y)
    (hext : IsExt ↥(imageModCenter K (conjClosure L M)) PV PY) : L = conjClosure L M := by
  obtain ⟨E, hE, hpv, hpy⟩ := hext
  set φ := toImageModCenter h31.1 with hφ
  refine eq_conjClosure_of_quotient hA3 h ((QuotientGroup.mk' E).comp φ)
    ((QuotientGroup.mk'_surjective E).comp (toImageModCenter_surjective h31.1)) ?_ (hPY hpy)
  have hEp : IsPGroup 2 ↥E := hPV hpv
  rintro ⟨m, hm⟩
  have hmE : φ m ∈ E := by
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hm
    exact hm
  obtain ⟨a, ha⟩ := hEp ⟨_, hmE⟩
  have hφa : m ^ 2 ^ a ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_pow]
    exact congrArg Subtype.val ha
  rw [mem_ker_toImageModCenter] at hφa
  have hZ : ((m ^ 2 ^ a : ↥(conjClosure L M)) : G) ∈ centerOf K :=
    ⟨h31.1 (m ^ 2 ^ a).2, hφa⟩
  obtain ⟨b, hb⟩ := h31.2.2 ⟨_, hZ⟩
  refine ⟨a + b, Subtype.ext (Subtype.ext ?_)⟩
  have := congrArg Subtype.val hb
  simp only [SubmonoidClass.mk_pow, OneMemClass.coe_one] at this ⊢
  rw [pow_add, pow_mul]
  exact this

theorem eq_of_c31Case3 (hA3 : A3Orbits G) (h : HypC28 H R M L V) (h31 : C31Basic H R M L V K)
    (h3 : C31Case3 H R M L V K) : L = conjClosure L M := by
  obtain ⟨-, he | he | he⟩ := h3
  · exact eq_conjClosure_of_isExt_imageModCenter hA3 h h31 (fun h => isPGroup_of_isE2 h)
      (fun h => quasiNoTwo_L24 h) he
  · exact eq_conjClosure_of_isExt_imageModCenter hA3 h h31 (fun h => isPGroup_of_isE2 h)
      (fun h => quasiNoTwo_A6 h) he
  · exact eq_conjClosure_of_isExt_imageModCenter hA3 h h31 (fun h => isPGroup_of_isE2 h)
      (fun h => quasiNoTwo_L32 h) he

theorem eq_of_c31Case4 (hA3 : A3Orbits G) (h : HypC28 H R M L V) (h4 : C31Case4 H R M L V K) :
    L = conjClosure L M := by
  obtain ⟨-, he | he | he⟩ := h4
  · exact eq_conjClosure_of_isExt hA3 h (fun h => isPGroup_of_isE2 h) (fun h => quasiNoTwo_L24 h) he
  · exact eq_conjClosure_of_isExt hA3 h (fun h => isPGroup_of_isE2 h) (fun h => quasiNoTwo_A7 h) he
  · exact eq_conjClosure_of_isExt hA3 h (fun h => isPGroup_of_isE2 h) (fun h => quasiNoTwo_L32 h) he

theorem eq_of_c31Case5 (hA3 : A3Orbits G) (h : HypC28 H R M L V) (h5 : C31Case5 H R M L V K) :
    L = conjClosure L M := by
  obtain ⟨-, he | he | he⟩ := h5
  · exact eq_conjClosure_of_isExt hA3 h (fun h => isPGroup_of_isE2 h)
      (fun h => quasiNoTwo_hatA6 h) he
  · exact eq_conjClosure_of_isExt hA3 h (fun h => isPGroup_of_isE2 h) (fun h => quasiNoTwo_L42 h) he
  · exact eq_conjClosure_of_isExt hA3 h (fun h => isPGroup_of_isE2 h) (fun h => quasiNoTwo_L32 h) he

theorem eq_of_c31Case6 (hA3 : A3Orbits G) (h : HypC28 H R M L V)
    (h6 : C31Case6 H R M L V K) : L = conjClosure L M := by
  obtain ⟨-, he | he | he⟩ := h6
  · exact eq_conjClosure_of_isExt hA3 h (fun h => isPGroup_of_isE2 h) (fun h => quasiNoTwo_M24 h) he
  · exact eq_conjClosure_of_isExt hA3 h (fun h => isPGroup_of_isSpecial2Group h)
      (fun h => quasiNoTwo_L32 h) he
  · exact eq_conjClosure_of_isExt hA3 h (fun h => isPGroup_of_isE2 h) (fun h => quasiNoTwo_L52 h) he

theorem eq_of_c31Case7 (hA3 : A3Orbits G) (h : HypC28 H R M L V) (h31 : C31Basic H R M L V K)
    (h7 : C31Case7 H R M L V K) : L = conjClosure L M := by
  obtain ⟨-, he | he⟩ := h7
  · exact eq_conjClosure_of_isExt_imageModCenter hA3 h h31 (fun h => isPGroup_of_isZ4Cubed h)
      (fun h => quasiNoTwo_L32 h) he
  · exact eq_conjClosure_of_isExt_imageModCenter hA3 h h31 (fun h => isPGroup_of_isE2 h)
      (fun h => quasiNoTwo_A6 h) he

theorem eq_of_c31Case8 (hA3 : A3Orbits G) (h : HypC28 H R M L V) (h8 : C31Case8 H R M L V K) :
    L = conjClosure L M :=
  eq_conjClosure_of_isExt hA3 h (fun h => isPGroup_of_isE2 h) (fun h => quasiNoTwo_hatA6 h) h8.2

theorem eq_of_c31Case9 (hA3 : A3Orbits G) (h : HypC28 H R M L V) (h31 : C31Basic H R M L V K)
    (h9 : C31Case9 H R M L V K) : L = conjClosure L M := by
  obtain ⟨-, he | he⟩ := h9
  · exact eq_conjClosure_of_isExt_imageModCenter hA3 h h31
      (fun h => isPGroup_of_isSpecial2Group h) (fun h => quasiNoTwo_L32 h) he
  · exact eq_conjClosure_of_isExt_imageModCenter hA3 h h31 (fun h => isPGroup_of_isE2 h)
      (fun h => quasiNoTwo_U33 h) he

end CFSG.Quasithin.C31Spor
