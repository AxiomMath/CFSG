module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4TA

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

abbrev titsH614 {Y : Type} [Group Y] (S₀ : Subgroup Y) : Subgroup Y :=
  Subgroup.centralizer ((Subgroup.center ↥S₀).map S₀.subtype : Set Y)

@[expose] def TitsBasicFact : Prop :=
  ∀ (Y : Type) [Group Y], IsTits Y → Finite Y ∧ CFSG.IsQuasisimple Y ∧ Subgroup.center Y = ⊥

@[expose] def TitsOver5Fact : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsTits Y → ∀ S₀ P : Subgroup Y, IsSylowTwoOf S₀ ⊤ →
    S₀ ≤ P → S₀.relIndex P = 5 → P = titsH614 S₀

@[expose] def TitsWCFact : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsTits Y → ∀ S₀ : Subgroup Y, IsSylowTwoOf S₀ ⊤ →
    ∀ Tst U : Subgroup (MulAut Y), IsPGroup 2 Tst →
      S₀.map (MulAut.conj : Y →* MulAut Y) ≤ Tst → U ≤ Tst → U ≠ ⊥ →
      (titsH614 S₀).map (MulAut.conj : Y →* MulAut Y) ≤
        Subgroup.normalizer (U : Set (MulAut Y)) →
      Tst ≤ Subgroup.normalizer (U : Set (MulAut Y)) →
      (∀ d : Y, U.map (MulAut.conj (MulAut.conj d)).toMonoidHom ≤ Tst →
        U.map (MulAut.conj (MulAut.conj d)).toMonoidHom = U) →
      (pCoreOf 2 (titsH614 S₀)).map (MulAut.conj : Y →* MulAut Y) ≤ U

variable {G : Type} [Group G] [Finite G]

theorem thompsonJ_conjSub_eq_of_le614 {T : Subgroup G} {k : G}
    (h : B6.conjSub k (thompsonJ T) ≤ T) : B6.conjSub k (thompsonJ T) = thompsonJ T := by
  rw [← B6.thompsonJ_conjSub] at h ⊢
  apply Subgroup.eq_of_le_of_card_ge
  · refine iSup₂_le fun A hA => ?_
    have hAT : A ≤ T := (B6.le_thompsonJ hA).trans h
    refine B6.le_thompsonJ ⟨hAT, hA.2.1, fun B hBT hB => ?_⟩
    have := hA.2.2 (B6.conjSub k B) ((B6.conjSub k).le_iff_le.mpr hBT)
      (B6.isElemAbelian_conjSub hB k)
    rwa [B6.card_conjSub] at this
  · rw [B6.thompsonJ_conjSub, B6.card_conjSub]

omit [Finite G] in
theorem mem_centralizerMod_of_actModO2_614 {K : Subgroup G} {y : G}
    (hy : y ∈ Subgroup.normalizer (K : Set G)) (h : actModO2_614 K ⟨y, hy⟩ = 1) :
    y ∈ centralizerMod (pCoreOf 2 K) (Subgroup.normalizer (K : Set G)) K := by
  refine ⟨hy, CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K hy, fun u hu => ?_⟩
  have h1 := congrArg (fun φ : MulAut (ModO2 K) =>
    φ ((⟨u⁻¹, K.inv_mem hu⟩ : ↥K) : ModO2 K)) h
  simp only [actModO2_614_mk, MulAut.one_apply] at h1
  rw [QuotientGroup.eq] at h1
  have h2 := mem_pCoreOf_of_mem_pCore614 h1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2
  convert h2 using 1
  group

omit [Finite G] in
theorem mem_pCore_of_actModO2_614 {K : Subgroup G} (hZ : Subgroup.center (ModO2 K) = ⊥)
    {k : G} (hk : k ∈ K) (h : actModO2_614 K ⟨k, Subgroup.le_normalizer hk⟩ = 1) :
    (⟨k, hk⟩ : ↥K) ∈ CFSG.pCore 2 ↥K := by
  rw [actModO2_614_of_mem] at h
  have hc : ((⟨k, hk⟩ : ↥K) : ModO2 K) ∈ Subgroup.center (ModO2 K) := by
    rw [Subgroup.mem_center_iff]
    intro z
    have := congrArg (fun φ : MulAut (ModO2 K) => φ z) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    exact (mul_inv_eq_iff_eq_mul.mp this).symm
  rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hc
  exact hc

omit [Finite G] in
theorem exists_pow_mul_eq614 {K T : Subgroup G} (hTK : T ≤ Subgroup.normalizer (K : Set G))
    {k t : G} (hk : k ∈ K) (ht : t ∈ T) (m : ℕ) : ∃ k' ∈ K, (k * t) ^ m = k' * t ^ m := by
  induction m with
  | zero => exact ⟨1, K.one_mem, by simp⟩
  | succ m ih =>
    obtain ⟨k', hk', e⟩ := ih
    refine ⟨k' * (t ^ m * k * (t ^ m)⁻¹), K.mul_mem hk' ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hTK (T.pow_mem ht m)) k).mp hk
    · rw [pow_succ, e, pow_succ]
      group

theorem mem_of_actModO2_614 {K T : Subgroup G} (hZ : Subgroup.center (ModO2 K) = ⊥)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) (hT : IsSylowTwoOf T (K ⊔ T)) {c : G}
    (hc : c ∈ K ⊔ T) (h : actModO2_614 K ⟨c, sup_le Subgroup.le_normalizer hTK hc⟩ = 1) :
    c ∈ T := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := Subgroup.normalizer (K : Set G) with hN
  have hKTN : K ⊔ T ≤ N := sup_le Subgroup.le_normalizer hTK
  set C : Subgroup G := ((actModO2_614 K).ker.map N.subtype) ⊓ (K ⊔ T) with hC
  have hmemC : ∀ x (hx : x ∈ K ⊔ T), actModO2_614 K ⟨x, hKTN hx⟩ = 1 → x ∈ C :=
    fun x hx h => ⟨⟨⟨x, hKTN hx⟩, h, rfl⟩, hx⟩
  have hCmem : ∀ x ∈ C, ∃ hx : x ∈ K ⊔ T, actModO2_614 K ⟨x, hKTN hx⟩ = 1 := by
    rintro x ⟨⟨⟨n, hn⟩, hnk, rfl⟩, hx⟩
    exact ⟨hx, hnk⟩
  have hconj : ∀ g ∈ K ⊔ T, ∀ x ∈ C, g * x * g⁻¹ ∈ C := by
    intro g hg x hx
    obtain ⟨hxKT, hx1⟩ := hCmem x hx
    have hm : g * x * g⁻¹ ∈ K ⊔ T := (K ⊔ T).mul_mem ((K ⊔ T).mul_mem hg hxKT)
      ((K ⊔ T).inv_mem hg)
    refine hmemC _ hm ?_
    have e : (⟨g * x * g⁻¹, hKTN hm⟩ : ↥N) =
        ⟨g, hKTN hg⟩ * ⟨x, hKTN hxKT⟩ * (⟨g, hKTN hg⟩ : ↥N)⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, hx1, mul_one, mul_inv_cancel]
  have hCn : K ⊔ T ≤ Subgroup.normalizer (C : Set G) := fun g hg =>
    B6.mem_normalizer_of_forall_mem (hconj g hg) (fun x hx => by
      simpa using hconj g⁻¹ ((K ⊔ T).inv_mem hg) x hx)
  have hC2 : IsPGroup 2 C := by
    rintro ⟨x, hx⟩
    obtain ⟨hxKT, hx1⟩ := hCmem x hx
    have hxKT' := hxKT
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left K T hTK] at hxKT'
    obtain ⟨k, hk, t, ht, rfl⟩ := hxKT'
    obtain ⟨a, ha⟩ := hT.2.1 ⟨t, ht⟩
    have ha' : t ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
    obtain ⟨k', hk', e⟩ := exists_pow_mul_eq614 hTK hk ht (2 ^ a)
    rw [ha', mul_one] at e
    have hpow : (⟨(k * t) ^ 2 ^ a, hKTN ((K ⊔ T).pow_mem hxKT _)⟩ : ↥N) =
        (⟨k * t, hKTN hxKT⟩ : ↥N) ^ 2 ^ a := Subtype.ext (by simp)
    have h1 : actModO2_614 K ⟨k', Subgroup.le_normalizer hk'⟩ = 1 := by
      have : (⟨k', Subgroup.le_normalizer hk'⟩ : ↥N) =
          (⟨(k * t) ^ 2 ^ a, hKTN ((K ⊔ T).pow_mem hxKT _)⟩ : ↥N) := Subtype.ext e.symm
      rw [this, hpow, map_pow, hx1, one_pow]
    obtain ⟨b, hb⟩ :=
      CFSG.pCore_isPGroup (p := 2) (G := ↥K) ⟨_, mem_pCore_of_actModO2_614 hZ hk' h1⟩
    have hb' : k' ^ 2 ^ b = 1 := by
      have := congrArg (fun z => ((z : ↥K) : G)) (congrArg Subtype.val hb)
      simpa using this
    refine ⟨a + b, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [pow_add, pow_mul, e, hb']
  have hCT : C ≤ T := (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right hCn
    hC2).trans (B6.pCoreOf_two_le_of_isSylowTwoOf hT)
  exact hCT (hmemC c hc h)

theorem pCoreOf_le_of_tits614 (hO5 : TitsOver5Fact) (hWC : TitsWCFact) {T K X : Subgroup G}
    (htits : IsTits (ModO2 K)) (hZ : Subgroup.center (ModO2 K) = ⊥)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) (hsyl : IsSylowTwoOf T (K ⊔ T))
    (hXK : X ≤ K) (hTX : T ≤ Subgroup.normalizer (X : Set G)) (hX5 : (X ⊓ T).relIndex X = 5)
    (hJX : X ⊔ T ≤ Subgroup.normalizer (thompsonJ T : Set G))
    (hJK : ¬ K ≤ Subgroup.normalizer (thompsonJ T : Set G)) :
    pCoreOf 2 (X ⊔ (T ⊓ K)) ≤
      thompsonJ T ⊔ centralizerMod (pCoreOf 2 K) (Subgroup.normalizer (K : Set G)) K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := Subgroup.normalizer (K : Set G) with hN
  set J := thompsonJ T with hJdef
  set Φ := actModO2_614 K with hΦ
  have hKN : K ≤ N := Subgroup.le_normalizer
  have hJT : J ≤ T := B6.thompsonJ_le T
  have hJN : J ≤ N := hJT.trans hTK
  have hKTN : K ⊔ T ≤ N := sup_le hKN hTK
  have hT2 : IsPGroup 2 T := hsyl.2.1
  have hsylK : IsSylowTwoOf (T ⊓ K) K :=
    A4.isSylowTwoOf_inf_normal hsyl le_sup_left (sup_le Subgroup.le_normalizer hTK)
  have hOK : pCoreOf 2 K ≤ T ⊓ K := B6.pCoreOf_two_le_of_isSylowTwoOf hsylK
  have hιq : ∀ k : ↥K, MulAut.conj (k : ModO2 K) = Φ ⟨k, hKN k.2⟩ :=
    fun k => (actModO2_614_of_mem K k.2).symm
  set Tst := (T.subgroupOf N).map Φ with hTst
  set U := (J.subgroupOf N).map Φ with hU
  have hNU : ∀ n : ↥N, (n : G) ∈ Subgroup.normalizer (J : Set G) →
      Φ n ∈ Subgroup.normalizer (U : Set (MulAut (ModO2 K))) := by
    intro n hn
    refine Subgroup.le_normalizer_map Φ ⟨n, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
    intro y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.mp hn y
  set S₀ := ((T ⊓ K).subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) with hS₀
  set H₀ := X ⊔ (T ⊓ K) with hH₀
  have hH₀K : H₀ ≤ K := sup_le hXK inf_le_right
  set P₀ := (H₀.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) with hP₀
  have hkerS : (QuotientGroup.mk' (CFSG.pCore 2 ↥K)).ker ≤ (T ⊓ K).subgroupOf K := by
    intro k hk
    rw [QuotientGroup.ker_mk'] at hk
    rw [Subgroup.mem_subgroupOf]
    exact hOK (mem_pCoreOf_of_mem_pCore614 hk)
  have hSH : (T ⊓ K).subgroupOf K ≤ H₀.subgroupOf K := fun k hk => by
    rw [Subgroup.mem_subgroupOf] at hk ⊢
    exact Subgroup.mem_sup_right hk
  have hSyl : IsSylowTwoOf S₀ ⊤ := by
    refine ⟨le_top, ?_, ?_⟩
    · exact (hsylK.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm).map _
    · show ¬ 2 ∣ S₀.relIndex ⊤
      rw [Subgroup.relIndex_top_right]
      intro h2
      exact hsylK.2.2 (h2.trans (Subgroup.index_map_dvd _ (QuotientGroup.mk'_surjective _)))
  have hSP : S₀ ≤ P₀ := Subgroup.map_mono hSH
  have hidx : S₀.relIndex P₀ = 5 := by
    rw [hS₀, hP₀, Subgroup.relIndex_map_map, sup_eq_left.mpr hkerS,
      sup_eq_left.mpr (hkerS.trans hSH), Subgroup.relIndex_subgroupOf hH₀K]
    have hTKX : T ⊓ K ≤ Subgroup.normalizer (X : Set G) := inf_le_left.trans hTX
    have hXT : X ⊓ (T ⊓ K) = X ⊓ T := by
      rw [inf_comm T K, ← inf_assoc, inf_eq_left.mpr hXK]
    have h1 := B6.relIndex_sup_eq_of_le_normalizer hTKX
    rw [sup_comm] at h1
    have h2 := Subgroup.relIndex_mul_relIndex _ _ _ (inf_le_left : X ⊓ (T ⊓ K) ≤ X)
      (le_sup_left : X ≤ H₀)
    have h3 := Subgroup.relIndex_mul_relIndex _ _ _ (inf_le_right : X ⊓ (T ⊓ K) ≤ T ⊓ K)
      (le_sup_right : T ⊓ K ≤ H₀)
    rw [Subgroup.inf_relIndex_right] at h3
    rw [hXT] at h2 h3
    rw [hX5, h1] at h2
    have hne : X.relIndex (T ⊓ K) ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h4 : X.relIndex (T ⊓ K) * (T ⊓ K).relIndex H₀ = X.relIndex (T ⊓ K) * 5 := by
      rw [h3, ← h2, mul_comm]
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne) h4
  have hP : P₀ = titsH614 S₀ := hO5 _ htits S₀ P₀ hSyl hSP hidx
  have hTst2 : IsPGroup 2 Tst := (hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTK).symm).map Φ
  have hST : S₀.map (MulAut.conj : ModO2 K →* MulAut (ModO2 K)) ≤ Tst := by
    rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hs
    rw [QuotientGroup.mk'_apply, hιq]
    exact ⟨⟨s, hKN s.2⟩, hs.1, rfl⟩
  have hUT : U ≤ Tst := Subgroup.map_mono fun n hn => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hJT hn
  have hU1 : U ≠ ⊥ := by
    intro hU0
    apply hJK
    have hcomm : ⁅J, K⁆ ≤ pCoreOf 2 K := commutator_le_pCoreOf_of_actModO2_614 hJN
      (fun j hj => by
        have : Φ ⟨j, hJN hj⟩ ∈ U := ⟨⟨j, hJN hj⟩, hj, rfl⟩
        rw [hU0, Subgroup.mem_bot] at this
        exact this)
    have hR₁T : J ⊔ pCoreOf 2 K ≤ T := sup_le hJT (hOK.trans inf_le_left)
    have hJR₁ : thompsonJ (J ⊔ pCoreOf 2 K) = J := B6.thompsonJ_eq_of_le le_sup_left hR₁T
    have hkR : ∀ k ∈ K, B6.conjSub k (J ⊔ pCoreOf 2 K) ≤ J ⊔ pCoreOf 2 K := by
      intro k hk
      rw [OrderIso.map_sup]
      refine sup_le ?_ ?_
      · intro x hx
        rw [B6.mem_conjSub] at hx
        have hc := hcomm (Subgroup.commutator_mem_commutator hx hk)
        have e : x = (⁅k⁻¹ * x * k, k⁆)⁻¹ * (k⁻¹ * x * k) := by
          rw [commutatorElement_def]
          group
        rw [e]
        exact (J ⊔ pCoreOf 2 K).mul_mem (Subgroup.mem_sup_right ((pCoreOf 2 K).inv_mem hc))
          (Subgroup.mem_sup_left hx)
      · rw [B6.conjSub_eq_self (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K hk)]
        exact le_sup_right
    intro k hk
    have e : B6.conjSub k (J ⊔ pCoreOf 2 K) = J ⊔ pCoreOf 2 K := B6.conjSub_eq_self
      (B6.mem_normalizer_of_conjSub_le (hkR k hk) (hkR k⁻¹ (K.inv_mem hk)))
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have := B6.thompsonJ_conjSub (J ⊔ pCoreOf 2 K) k
    rw [e, hJR₁] at this
    exact this.symm
  have hHU : (titsH614 S₀).map (MulAut.conj : ModO2 K →* MulAut (ModO2 K)) ≤
      Subgroup.normalizer (U : Set (MulAut (ModO2 K))) := by
    rw [← hP]
    rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hp
    rw [QuotientGroup.mk'_apply, hιq]
    exact hNU _ (hJX (sup_le_sup_left (inf_le_left : T ⊓ K ≤ T) X hp))
  have hTU : Tst ≤ Subgroup.normalizer (U : Set (MulAut (ModO2 K))) := by
    rintro _ ⟨t, ht, rfl⟩
    exact hNU t (hJX (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp ht)))
  have hwc : ∀ d : ModO2 K, U.map (MulAut.conj (MulAut.conj d)).toMonoidHom ≤ Tst →
      U.map (MulAut.conj (MulAut.conj d)).toMonoidHom = U := by
    intro d hd
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective d
    rw [hιq k] at hd ⊢
    have hJk : B6.conjSub (k : G) J ≤ T := by
      intro x hx
      rw [B6.mem_conjSub] at hx
      have hxe : x = k * ((k : G)⁻¹ * x * k) * (k : G)⁻¹ := by group
      have hxKT : x ∈ K ⊔ T := by
        rw [hxe]
        exact (K ⊔ T).mul_mem ((K ⊔ T).mul_mem (Subgroup.mem_sup_left k.2)
          (Subgroup.mem_sup_right (hJT hx))) ((K ⊔ T).inv_mem (Subgroup.mem_sup_left k.2))
      have hΦx : Φ ⟨x, hKTN hxKT⟩ ∈ Tst := by
        apply hd
        refine ⟨Φ ⟨_, hJN hx⟩, ⟨⟨_, hJN hx⟩, hx, rfl⟩, ?_⟩
        show Φ ⟨k, hKN k.2⟩ * Φ ⟨_, hJN hx⟩ * (Φ ⟨k, hKN k.2⟩)⁻¹ = Φ ⟨x, hKTN hxKT⟩
        rw [← map_inv, ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext hxe.symm
      obtain ⟨⟨t, htN⟩, ht, hte⟩ := hΦx
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at ht
      have hc : t⁻¹ * x ∈ K ⊔ T := (K ⊔ T).mul_mem (Subgroup.mem_sup_right (T.inv_mem ht)) hxKT
      have h1 : Φ ⟨t⁻¹ * x, hKTN hc⟩ = 1 := by
        have e : (⟨t⁻¹ * x, hKTN hc⟩ : ↥N) = (⟨t, htN⟩ : ↥N)⁻¹ * ⟨x, hKTN hxKT⟩ := rfl
        rw [e, map_mul, map_inv, hte, inv_mul_cancel]
      have h2 := mem_of_actModO2_614 hZ hTK hsyl hc h1
      have e2 : x = t * (t⁻¹ * x) := by group
      rw [e2]
      exact T.mul_mem ht h2
    have hkJ : (k : G) ∈ Subgroup.normalizer (J : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      exact thompsonJ_conjSub_eq_of_le614 hJk
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (hNU ⟨k, hKN k.2⟩ hkJ)
  have hcore := hWC _ htits S₀ hSyl Tst U hTst2 hST hUT hU1 hHU hTU hwc
  rw [← hP] at hcore
  intro y hy
  have hyH : y ∈ H₀ := CFSG.LieType.BorelTits.pCoreOf_le 2 H₀ hy
  have hyK : y ∈ K := hH₀K hyH
  have hyP : QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨y, hyK⟩ ∈ pCoreOf 2 P₀ := by
    set W := ((pCoreOf 2 H₀).subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) with hW
    have hWP : W ≤ P₀ := Subgroup.map_mono fun k hk => by
      rw [Subgroup.mem_subgroupOf] at hk ⊢
      exact CFSG.LieType.BorelTits.pCoreOf_le 2 H₀ hk
    have hPW : P₀ ≤ Subgroup.normalizer (W : Set (ModO2 K)) := by
      rintro _ ⟨h, hh, rfl⟩
      refine Subgroup.le_normalizer_map _ ⟨h, ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
      intro z
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H₀ (Subgroup.mem_subgroupOf.mp hh)) z
    have hW2 : IsPGroup 2 W :=
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H₀).of_equiv (Subgroup.subgroupOfEquivOfLe
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 H₀).trans hH₀K)).symm).map _
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hWP hPW hW2 ⟨⟨y, hyK⟩, hy, rfl⟩
  have hΦy : Φ ⟨y, hKN hyK⟩ ∈ U := by
    have := hcore ⟨_, hyP, rfl⟩
    rwa [QuotientGroup.mk'_apply, hιq] at this
  obtain ⟨⟨j, hjN⟩, hj, hje⟩ := hΦy
  rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hj
  have hm : j⁻¹ * y ∈ N := N.mul_mem (N.inv_mem hjN) (hKN hyK)
  have hc : j⁻¹ * y ∈ centralizerMod (pCoreOf 2 K) N K := by
    refine mem_centralizerMod_of_actModO2_614 hm ?_
    have e : (⟨j⁻¹ * y, hm⟩ : ↥N) = (⟨j, hjN⟩ : ↥N)⁻¹ * ⟨y, hKN hyK⟩ := rfl
    rw [e, map_mul, map_inv, hje, inv_mul_cancel]
  have e : y = j * (j⁻¹ * y) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hj) (Subgroup.mem_sup_right hc)

@[expose] def Res614TitsCore : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V M₁ K₁ X : Subgroup G),
    Hyp611 G T M L V 4 → IsOrthCh5 L V 4 → quasithinIsMaxTwoLocal M₁ →
    Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤ M₁ → M₁ ≠ M →
    K₁ ∈ cComp M₁ → IsTits (ModO2 K₁) → ¬ K₁ ≤ M →
    X ≤ L → X ≤ M₁ → X = oTwoUpper X → (X ⊓ T).relIndex X = 5 →
    ((X ⊓ T).subgroupOf X).Normal → T ≤ Subgroup.normalizer (X : Set G) →
    X ≤ K₁ → T ≤ Subgroup.normalizer (K₁ : Set G) →
    ¬ X ≤ Subgroup.normalizer ((T ⊓ K₁ : Subgroup G) : Set G) →
    pCoreOf 2 (X ⊔ (T ⊓ K₁)) ≤
      thompsonJ T ⊔ centralizerMod (pCoreOf 2 K₁) (Subgroup.normalizer (K₁ : Set G)) K₁ →
    False

theorem res614Tits_of (h331 : Stmt3_3_1) (h512 : Stmt5_1_2) (h513 : Stmt5_1_3)
    (h37 : A37ForSQTK) (hB : TitsBasicFact) (hO5 : TitsOver5Fact) (hWC : TitsWCFact)
    (hcore : Res614TitsCore) : Res614Tits := by
  intro G _ _ T M L V M₁ K₁ X h horth hM₁ hCM₁ hne hK₁ htits hK₁M hXL hXM₁ hX2 hX5 hXn hTX
    hXK₁ hXK₀ hnot
  obtain ⟨-, hK₁q, hZ⟩ := hB _ htits
  obtain ⟨hXK, hTK, hK₀, hJX, hJK₁, hTM₁, hsylM₁, -⟩ := tits614_setup h331 h512 h513 h37 h
    horth hM₁ hCM₁ hK₁ hK₁q hK₁M hXL hXM₁ hX2 hX5 hXn hTX hXK₁ hXK₀ hnot
  rw [hK₀] at hnot
  exact hcore G T M L V M₁ K₁ X h horth hM₁ hCM₁ hne hK₁ htits hK₁M hXL hXM₁ hX2 hX5 hXn hTX
    hXK hTK hnot (pCoreOf_le_of_tits614 hO5 hWC htits hZ hTK
      (B6.isSylowTwoOf_mono hsylM₁ le_sup_right (sup_le (le_of_mem_cComp hK₁) hTM₁))
      hXK hTX hX5 hJX hJK₁)

end CFSG.Quasithin.H13
