module

public import CFSG.Quasithin.Background.E1QuotParam
public import CFSG.Quasithin.EmptyFaithful.E22PL2
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A134Families
public import CFSG.Adapters.WholeGroupLayer
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSL
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsL52Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListRank2
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalStrong
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.RonanE114.P7

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native
  CFSG.QuasithinUnique.Vol2Native.A312L

theorem isPSL_sl3_two : IsPSL 3 2 1 (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
  have hK : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  have hcardK : Nat.card (ZMod 2) = 2 ^ 1 := by rw [hK]; norm_num
  refine ⟨⟨Nat.prime_two, le_rfl, by omega, ?_, ?_⟩, ZMod 2, inferInstance, inferInstance, hcardK,
    ⟨slEquivStatedProj hK 3⟩⟩
  · intro h2
    have := congrArg Prod.fst h2
    simp only at this
    omega
  · intro h2
    have := congrArg Prod.fst h2
    simp only at this
    omega

theorem exists_mulEquiv_sl3_of_isPSL {X : Type} [Group X] (h : IsPSL 3 2 1 X) :
    Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
  obtain ⟨-, K, hF, hFin, hcard, ⟨e⟩⟩ := h
  have hK : Nat.card K = 2 := by simpa using hcard
  have := Fintype.ofFinite K
  have hKc : Fintype.card K = Fintype.card (ZMod 2) := by
    rw [← Nat.card_eq_fintype_card, hK, ZMod.card]
  let σ : K ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq hKc
  exact ⟨e.trans ((slEquivStatedProj hK 3).symm.trans (L239.L52.slEquivOfRingEquiv σ 3))⟩

section Basic

variable {H : Type} [Group H] [Finite H] {K T : Subgroup H}

theorem pCore_map_subtype_normal (hK : K.Normal) :
    ((CFSG.pCore 2 ↥K).map K.subtype).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨k, hk, rfl⟩ := hn
  have h := CFSG.pCore_map_iso (p := 2) (MulAut.conjNormal (H := K) g)
  have hmem : (MulAut.conjNormal (H := K) g) k ∈ CFSG.pCore 2 ↥K := by
    rw [← h]
    exact ⟨k, hk, rfl⟩
  exact ⟨_, hmem, by simp [MulAut.conjNormal_apply]⟩

theorem le_of_normal_pGroup {N : Subgroup H} (hN : N.Normal) (hp : IsPGroup 2 ↥N)
    (hT : IsSylowTwoOf T ⊤) : N ≤ T := by
  obtain ⟨hp', hi⟩ := K1.isSylowTwoOf_top_iff.mp hT
  exact IsPGroup.le_sylow_of_normal hp (hp'.toSylow hi)

theorem exists_pow_mem_of_sup_eq_top (hK : K.Normal) (hKT : K ⊔ T = ⊤) (hT : IsPGroup 2 ↥T)
    (x : H) : ∃ a : ℕ, x ^ 2 ^ a ∈ K := by
  have hx : x ∈ ((K ⊔ T : Subgroup H) : Set H) := by rw [hKT]; trivial
  rw [Subgroup.normal_mul] at hx
  obtain ⟨k, hk, t, ht, rfl⟩ := hx
  obtain ⟨a, ha⟩ := hT ⟨t, ht⟩
  refine ⟨a, ?_⟩
  have h1 : (QuotientGroup.mk' K) ((k * t) ^ 2 ^ a) = 1 := by
    have hk1 : (QuotientGroup.mk' K) k = 1 := (QuotientGroup.eq_one_iff k).mpr hk
    have hkt : (QuotientGroup.mk' K) (k * t) = (QuotientGroup.mk' K) t := by
      rw [map_mul, hk1, one_mul]
    rw [map_pow, hkt, ← map_pow]
    have : t ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
    rw [this, map_one]
  exact (QuotientGroup.eq_one_iff _).mp h1

theorem eq_one_of_commutes {X : Type*} [Group X] [IsSimpleGroup X]
    (hnab : ∃ a b : X, a * b ≠ b * a) {x : X} (hx : ∀ n : X, n * x = x * n) : x = 1 := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · have hxc : x ∈ Subgroup.center X := Subgroup.mem_center_iff.mpr hx
    rw [h] at hxc
    exact hxc
  · obtain ⟨a, b, hab⟩ := hnab
    have ha : a ∈ Subgroup.center X := by rw [h]; trivial
    exact (hab (Subgroup.mem_center_iff.mp ha b).symm).elim

theorem centralizer_map_eq_bot (hK : K.Normal) (hKT : K ⊔ T = ⊤) (hT : IsPGroup 2 ↥T)
    (hcen : ∀ x ∈ K.map (QuotientGroup.mk' (CFSG.pCore 2 H)),
      (∀ n ∈ K.map (QuotientGroup.mk' (CFSG.pCore 2 H)), n * x = x * n) → x = 1) :
    Subgroup.centralizer ((K.map (QuotientGroup.mk' (CFSG.pCore 2 H)) :
      Subgroup (H ⧸ CFSG.pCore 2 H)) : Set (H ⧸ CFSG.pCore 2 H)) = ⊥ := by
  set Y := CFSG.pCore 2 H with hY
  set π := QuotientGroup.mk' Y with hπ
  set N := K.map π with hN
  have hNn : N.Normal := Subgroup.Normal.map hK π (QuotientGroup.mk'_surjective Y)
  set C := Subgroup.centralizer (N : Set (H ⧸ Y)) with hC
  have hCn : C.Normal := ⟨fun c hc g n hn => by
    have h1 : g⁻¹ * n * g ∈ N := by
      have := hNn.conj_mem n hn g⁻¹
      rwa [inv_inv] at this
    have h2 := Subgroup.mem_centralizer_iff.mp hc _ h1
    show n * (g * c * g⁻¹) = (g * c * g⁻¹) * n
    calc n * (g * c * g⁻¹) = g * ((g⁻¹ * n * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * n * g)) * g⁻¹ := by rw [h2]
      _ = (g * c * g⁻¹) * n := by group⟩
  set C' := C.comap π with hC'
  have hC'n : C'.Normal := hCn.comap π
  have hp : IsPGroup 2 ↥C' := by
    intro x
    obtain ⟨a, ha⟩ := exists_pow_mem_of_sup_eq_top hK hKT hT x.1
    have hyC : π (x.1 ^ 2 ^ a) ∈ C := by
      rw [map_pow]
      exact pow_mem x.2 _
    have hyN : π (x.1 ^ 2 ^ a) ∈ N := ⟨_, ha, rfl⟩
    have h1 : π (x.1 ^ 2 ^ a) = 1 :=
      hcen _ hyN fun n hn => Subgroup.mem_centralizer_iff.mp hyC n hn
    have hyY : x.1 ^ 2 ^ a ∈ Y := (QuotientGroup.eq_one_iff _).mp h1
    obtain ⟨b, hb⟩ := (CFSG.pCore_isPGroup (p := 2) (G := H)) ⟨_, hyY⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have : (x.1 ^ 2 ^ a) ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
    rw [← pow_mul, ← pow_add] at this
    simpa using this
  have hle : C' ≤ Y := le_sSup ⟨hC'n, hp⟩
  refine eq_bot_iff.mpr fun c hc => ?_
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Y c
  rw [Subgroup.mem_bot]
  exact (QuotientGroup.eq_one_iff x).mpr (hle hc)

theorem not_normal_of_quotient (hK : K.Normal) (hT : IsSylowTwoOf T ⊤)
    (f : ↥K →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (hf : Function.Surjective f)
    (hker : IsPGroup 2 f.ker) : ¬ (⊤ : Subgroup H) ≤ Subgroup.normalizer (T : Set H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK2 : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  have hnab := sl_nonabelian_of_card_two hK2 (m := 3) le_rfl
  have hS : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    sl_isSimple_of_card_two hK2 le_rfl
  have hker_eq : CFSG.pCore 2 ↥K = f.ker := pCore_two_eq_ker hnab f hf hker
  intro hN
  have hTn : T.Normal := Subgroup.normalizer_eq_top_iff.mp (eq_top_iff.mpr hN)
  have hSK : IsSylowTwoOf (T ⊓ K) K :=
    B6.isSylowTwoOf_inf_normal hT le_top (by rw [Subgroup.normalizer_eq_top_iff.mpr hK])
  have hp : IsPGroup 2 ↥((T ⊓ K).subgroupOf K) := by
    have := hSK.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hSK.1).symm
    exact this
  have hle : (T ⊓ K).subgroupOf K ≤ f.ker := by
    rw [← hker_eq]
    haveI := hTn
    haveI := hK
    haveI : ((T ⊓ K).subgroupOf K).Normal := Subgroup.Normal.subgroupOf inferInstance K
    exact le_sSup ⟨inferInstance, hp⟩
  have hdvd : f.ker.index ∣ ((T ⊓ K).subgroupOf K).index := Subgroup.index_dvd_of_le hle
  have hidx : f.ker.index = 168 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hf, Subgroup.card_top]
    exact L239.card_sl_three hK2
  rw [hidx] at hdvd
  exact hSK.2.2 ((by norm_num : 2 ∣ 168).trans hdvd)

theorem nParam_le_one_of_pgl7
    (hK : K.Normal) (hT : IsSylowTwoOf T ⊤) (hKT : K ⊔ T = ⊤)
    (hmax : IsMaxSubgroupIn (⊤ : Subgroup H) T)
    (f : ↥K →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (hf : Function.Surjective f)
    (hker : IsPGroup 2 f.ker) : E1.nParam (⊤ : Subgroup H) ≤ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK2 : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  have hnab := sl_nonabelian_of_card_two hK2 (m := 3) le_rfl
  have hS : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    sl_isSimple_of_card_two hK2 le_rfl
  have hker_eq : CFSG.pCore 2 ↥K = f.ker := pCore_two_eq_ker hnab f hf hker
  set Y := CFSG.pCore 2 H with hY
  haveI hYn : Y.Normal := CFSG.pCore_normal
  have hYT : Y ≤ T := le_of_normal_pGroup hYn CFSG.pCore_isPGroup hT
  have hmin : MinParabolic (⊤ : Subgroup H) T T :=
    ⟨hT, not_normal_of_quotient hK hT f hf hker, isUniqueMaxOver_iff.mpr
      ⟨hmax, le_rfl, fun N hN hTN => by
        rcases eq_or_lt_of_le hTN with h | h
        · exact h.symm
        · exact absurd (hmax.2 N h le_top) hN.1.ne⟩⟩
  refine (E1.nParam_top_le_quotient hmin hYT).trans ?_
  set π := QuotientGroup.mk' Y with hπ
  set N := K.map π with hN
  have hNn : N.Normal := Subgroup.Normal.map hK π (QuotientGroup.mk'_surjective Y)
  have hR : (CFSG.pCore 2 ↥K).map K.subtype ≤ Y :=
    le_sSup ⟨pCore_map_subtype_normal hK, CFSG.pCore_isPGroup.map K.subtype⟩
  have hkerπ : (π.subgroupMap K).ker = f.ker := by
    rw [← hker_eq]
    ext k
    simp only [MonoidHom.mem_ker]
    constructor
    · intro hk
      have hkY : (k : H) ∈ Y := by
        have h1 : π (k : H) = 1 := by simpa using congrArg Subtype.val hk
        exact (QuotientGroup.eq_one_iff (k : H)).mp h1
      have hp : IsPGroup 2 ↥(Y.subgroupOf K) := by
        intro g
        obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := H)) ⟨(g.1 : H), g.2⟩
        exact ⟨n, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hn))⟩
      haveI : (Y.subgroupOf K).Normal := Subgroup.Normal.subgroupOf hYn K
      exact (le_sSup ⟨inferInstance, hp⟩ : Y.subgroupOf K ≤ CFSG.pCore 2 ↥K) hkY
    · intro hk
      apply Subtype.ext
      have h1 : π (k : H) = 1 := (QuotientGroup.eq_one_iff (k : H)).mpr (hR ⟨k, hk, rfl⟩)
      simpa using h1
  have hsurj : Function.Surjective (π.subgroupMap K) := MonoidHom.subgroupMap_surjective π K
  let θ : ↥N ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
    (QuotientGroup.quotientKerEquivOfSurjective (π.subgroupMap K) hsurj).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hkerπ).trans (QuotientGroup.quotientKerEquivOfSurjective f hf))
  haveI : IsSimpleGroup ↥N := θ.isSimpleGroup
  have hncN : ∃ x y : ↥N, x * y ≠ y * x := by
    obtain ⟨a, b, hab⟩ := hnab
    refine ⟨θ.symm a, θ.symm b, fun h => hab ?_⟩
    simpa using congrArg θ h
  have hcen : ∀ x ∈ N, (∀ n ∈ N, n * x = x * n) → x = 1 := by
    intro x hx hc
    have := eq_one_of_commutes hncN (x := (⟨x, hx⟩ : ↥N)) fun n =>
      Subtype.ext (hc n.1 n.2)
    simpa using congrArg Subtype.val this
  have hC := centralizer_map_eq_bot hK hKT hT.2.1 hcen
  have hFN : CFSG.generalizedFitting (H ⧸ Y) = N :=
    CFSG.Adapters.generalizedFitting_eq_of_normal_simple_of_centralizer_eq_bot N hncN hC
  have hpsl : IsPSL 3 2 1 ↥(CFSG.generalizedFitting (H ⧸ Y)) :=
    IsPSL.of_mulEquiv (θ.symm.trans (MulEquiv.subgroupCongr hFN.symm)) isPSL_sl3_two
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact E22L2.nParam_le_one_of_psl2_prime (p := 7) (Or.inr rfl) le_rfl
    (statedClassicalModel_psl_two_seven_of_three_two hpsl)

end Basic

section Ambient

variable {G : Type} [Group G] [Finite G] {K T : Subgroup G}

theorem nParam_le_one_of_pgl7'
    (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hT : IsSylowTwoOf T (K ⊔ T))
    (hmax : ∀ M : Subgroup G, T ≤ M → M ≤ K ⊔ T → M = T ∨ M = K ⊔ T)
    (f : ↥K →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (hf : Function.Surjective f)
    (hker : IsPGroup 2 f.ker) : E1.nParam (K ⊔ T) ≤ 1 := by
  rw [E1.nParam_subgroupOf]
  set D := K ⊔ T with hD
  have hKD : K ≤ D := le_sup_left
  have hTD : T ≤ D := le_sup_right
  have hKn : (K.subgroupOf D).Normal := by
    have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hTK
    rwa [sup_comm] at this
  have hT' : IsSylowTwoOf (T.subgroupOf D) ⊤ := by
    exact K1.isSylowTwoOf_top_iff.mpr
      ⟨hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTD).symm, hT.2.2⟩
  have hKT' : K.subgroupOf D ⊔ T.subgroupOf D = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hKD hTD, ← hD, Subgroup.subgroupOf_self]
  let e : ↥(K.subgroupOf D) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKD
  let f' : ↥(K.subgroupOf D) →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
    f.comp e.toMonoidHom
  have hf' : Function.Surjective f' := hf.comp e.surjective
  have hker' : IsPGroup 2 f'.ker := by
    intro x
    have hx : f (e x.1) = 1 := MonoidHom.mem_ker.mp x.2
    obtain ⟨n, hn⟩ := hker ⟨e x.1, MonoidHom.mem_ker.mpr hx⟩
    refine ⟨n, Subtype.ext (e.injective ?_)⟩
    have := congrArg Subtype.val hn
    simpa using this
  have hmax' : IsMaxSubgroupIn (⊤ : Subgroup ↥D) (T.subgroupOf D) := by
    refine ⟨?_, fun M' hM' _ => ?_⟩
    · refine lt_of_le_of_ne le_top fun h => ?_
      have hDT : D ≤ T := fun x hx => by
        have : (⟨x, hx⟩ : ↥D) ∈ T.subgroupOf D := by rw [h]; trivial
        exact this
      have hpK : IsPGroup 2 ↥K := hT.2.1.to_le (hKD.trans hDT)
      have hpS := hpK.of_surjective f hf
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hpS
      have hK2 : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
      rw [L239.card_sl_three hK2] at hn
      have h3 : 3 ∣ 2 ^ n := by rw [← hn]; norm_num
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
      omega
    · set M := M'.map D.subtype with hM
      have hTM : T ≤ M := fun t ht => by
        have : (⟨t, hTD ht⟩ : ↥D) ∈ T.subgroupOf D := ht
        exact ⟨_, hM'.le this, rfl⟩
      have hMD : M ≤ D := Subgroup.map_subtype_le M'
      rcases hmax M hTM hMD with hMT | hMD'
      · exfalso
        have : M' ≤ T.subgroupOf D := fun x hx => by
          have : (x : G) ∈ M := ⟨x, hx, rfl⟩
          rw [hMT] at this
          exact this
        exact absurd hM' (not_lt_of_ge this)
      · refine eq_top_iff.mpr fun x _ => ?_
        have : (x : G) ∈ M := by rw [hMD']; exact x.2
        obtain ⟨y, hy, hyx⟩ := this
        have : y = x := Subtype.ext hyx
        rwa [← this]
  exact nParam_le_one_of_pgl7 hKn hT' hKT' hmax' f' hf' hker'

end Ambient


end CFSG.Quasithin.RonanE114.P7
