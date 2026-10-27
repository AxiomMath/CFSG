module

public import CFSG.Quasithin.H13.U3U33Fixed
public import CFSG.Quasithin.H13.U3Assembly
public import CFSG.Quasithin.H13.U3FrameKernel
public import CFSG.Quasithin.H13.StatementsL2
public import CFSG.Quasithin.Background.BlueprintB2Reduced

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative Pointwise

variable {G : Type} [Group G]

theorem mem_zornO0 {K : Type} [Field K] {x : Multiplicative (quasithinZorn K)} :
    x ∈ zornO0 K ↔ (Multiplicative.toAdd x).1 + (Multiplicative.toAdd x).2.2.2 = 0 :=
  Iff.rfl

theorem mem_zornR {K : Type} [Field K] {x : Multiplicative (quasithinZorn K)} :
    x ∈ zornR K ↔ ∃ c : K, Multiplicative.toAdd x = (c, 0, 0, c) :=
  Iff.rfl

theorem card_zornO0 (K : Type) [Field K] [Finite K] : Nat.card (zornO0 K) = Nat.card K ^ 7 := by
  let e : ↥(zornO0 K) ≃ K × (Fin 3 → K) × (Fin 3 → K) :=
    { toFun := fun x => ((Multiplicative.toAdd (x : Multiplicative (quasithinZorn K))).1,
        (Multiplicative.toAdd (x : Multiplicative (quasithinZorn K))).2.1,
        (Multiplicative.toAdd (x : Multiplicative (quasithinZorn K))).2.2.1)
      invFun := fun y => ⟨Multiplicative.ofAdd (y.1, y.2.1, y.2.2, -y.1),
        mem_zornO0.2 (add_neg_cancel y.1)⟩
      left_inv := fun x => by
        obtain ⟨x, hx⟩ := x
        have hx' := neg_eq_of_add_eq_zero_right (mem_zornO0.1 hx)
        apply Subtype.ext
        apply Multiplicative.toAdd.injective
        change ((Multiplicative.toAdd x).1, (Multiplicative.toAdd x).2.1,
          (Multiplicative.toAdd x).2.2.1, -(Multiplicative.toAdd x).1) = Multiplicative.toAdd x
        rw [hx']
      right_inv := fun y => rfl }
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_prod, Nat.card_fun, Nat.card_fin]
  ring

theorem card_zornR_subgroupOf (K : Type) [Field K] [Finite K] (h2 : (2 : K) = 0) :
    Nat.card ((zornR K).subgroupOf (zornO0 K)) = Nat.card K := by
  have hle : zornR K ≤ zornO0 K := by
    intro x hx
    obtain ⟨c, hc⟩ := mem_zornR.1 hx
    rw [mem_zornO0, hc]
    change c + c = 0
    rw [← two_mul, h2, zero_mul]
  let e : K ≃ ↥(zornR K) :=
    { toFun := fun c => ⟨Multiplicative.ofAdd (c, 0, 0, c), mem_zornR.2 ⟨c, rfl⟩⟩
      invFun := fun x => (Multiplicative.toAdd (x : Multiplicative (quasithinZorn K))).1
      left_inv := fun c => rfl
      right_inv := fun x => by
        obtain ⟨x, hx⟩ := x
        obtain ⟨c, hc⟩ := mem_zornR.1 hx
        apply Subtype.ext
        apply Multiplicative.toAdd.injective
        change ((Multiplicative.toAdd x).1, 0, 0, (Multiplicative.toAdd x).1) =
          Multiplicative.toAdd x
        rw [hc] }
  rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv, Nat.card_congr e.symm]

theorem card_zornQ_of_card_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    Nat.card (↥(zornO0 K) ⧸ (zornR K).subgroupOf (zornO0 K)) = 64 := by
  have h2 : (2 : K) = 0 := by
    have := Fintype.ofFinite K
    have h := FiniteField.cast_card_eq_zero K
    rw [← Nat.card_eq_fintype_card, hK] at h
    exact_mod_cast h
  have h1 := card_eq_card_quotient_mul_card_subgroup ((zornR K).subgroupOf (zornO0 K))
  rw [card_zornO0, card_zornR_subgroupOf K h2, hK] at h1
  norm_num at h1
  omega

theorem card_le_of_realizes {W : Type*} [CommGroup W] {D : FFModel} {H : Subgroup (MulAut W)}
    {U Z : Subgroup W} (h : D.Realizes H U Z) (hD : Finite D.Gam) :
    Nat.card H ≤ Nat.card D.Gam := by
  obtain ⟨π, hπ, -⟩ := h
  exact Nat.card_le_card_of_surjective π hπ

theorem card_alternatingGroup_le {n : ℕ} (hn : n ≤ 6) :
    Nat.card (alternatingGroup (Fin n)) ≤ 720 := by
  refine (card_le_card_group _).trans ?_
  rw [Nat.card_perm, Nat.card_fin]
  calc n.factorial ≤ (6 : ℕ).factorial := Nat.factorial_le hn
    _ = 720 := by decide

theorem finite_and_card_le_of_GL_three {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 3) K)) : Finite H ∧ Nat.card H ≤ 512 := by
  have hinj : Function.Injective (fun g : H =>
      (((g : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :
        Fin 3 → Fin 3 → K)) :=
    fun a b h => Subtype.ext (Units.ext h)
  refine ⟨Finite.of_injective _ hinj, (Nat.card_le_card_of_injective _ hinj).trans ?_⟩
  change Nat.card (Fin 3 → Fin 3 → K) ≤ 512
  rw [Nat.card_fun, Nat.card_fun, Nat.card_fin, hK]
  norm_num

theorem mem_reducedAggregate [Finite G] {E : Subgroup G} {v : G}
    (hv : v ∈ reducedAggregate E) :
    v ∈ pCoreOf 2 E ∧ (∀ k ∈ pCoreOf 2 E, k * v = v * k) ∧ v ^ 2 = 1 := by
  obtain ⟨r, hr, rfl⟩ := hv
  obtain ⟨-, -, hRc⟩ := primeReducedAggregate_normal_elementaryAbelian (E := ↥E) 2
  obtain ⟨h1, h2, h3⟩ := BlueprintB2.mem_centerTorsion_iff.1 (hRc hr)
  refine ⟨?_, fun k hk => ?_, ?_⟩
  · rw [← inSubgroup_pCore_eq_pCoreOf]
    exact ⟨r, h1, rfl⟩
  · rw [← inSubgroup_pCore_eq_pCoreOf] at hk
    obtain ⟨k', hk', rfl⟩ := hk
    exact congrArg Subtype.val (h2 k' hk')
  · have := congrArg Subtype.val h3
    simpa using this

theorem ker_normalizerConjOn {L V : Subgroup G} (hLV : L ≤ normalizer (V : Set G)) :
    (SteinbergBS.normalizerConjOn V L hLV).ker = (L ⊓ centralizer (V : Set G)).subgroupOf L := by
  ext l
  rw [mem_subgroupOf, mem_inf, MonoidHom.mem_ker]
  constructor
  · intro h
    refine ⟨l.2, mem_centralizer_iff.2 fun v hv => ?_⟩
    have h1 := congrArg (fun f : MulAut V => ((f ⟨v, hv⟩ : V) : G)) h
    change (l : G) * v * (l : G)⁻¹ = v at h1
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  · rintro ⟨-, hl⟩
    refine MulEquiv.ext fun v => Subtype.ext ?_
    change (l : G) * v * (l : G)⁻¹ = v
    rw [← (mem_centralizer_iff.1 hl) v v.2, mul_inv_cancel_right]

theorem inf_centralizer_subgroupOf_eq_pCore {L V : Subgroup G}
    (hs : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L)) (hLV : L ≤ normalizer (V : Set G))
    (hO : pCoreOf 2 L ≤ centralizer (V : Set G)) (hne : ¬ L ≤ centralizer (V : Set G)) :
    (L ⊓ centralizer (V : Set G)).subgroupOf L = CFSG.pCore 2 ↥L := by
  have hNn : ((L ⊓ centralizer (V : Set G)).subgroupOf L).Normal :=
    ker_normalizerConjOn hLV ▸ MonoidHom.normal_ker _
  have hPle : CFSG.pCore 2 ↥L ≤ (L ⊓ centralizer (V : Set G)).subgroupOf L := by
    intro x hx
    rw [mem_subgroupOf]
    refine ⟨x.2, hO ?_⟩
    rw [← inSubgroup_pCore_eq_pCoreOf]
    exact ⟨x, hx, rfl⟩
  have hmn := hNn.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (((L ⊓ centralizer (V : Set G)).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)))
    with h | h
  · rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    exact le_antisymm h hPle
  · exfalso
    apply hne
    intro l hl
    have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨l, hl⟩ ∈
        ((L ⊓ centralizer (V : Set G)).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) :=
      by rw [h]; exact mem_top _
    obtain ⟨y, hy, hyl⟩ := hmem
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hyl
    have h2 : (⟨l, hl⟩ : ↥L) ∈ (L ⊓ centralizer (V : Set G)).subgroupOf L := by
      have := mul_mem hy (hPle hyl)
      rwa [mul_inv_cancel_left] at this
    exact (mem_subgroupOf.1 h2).2

theorem exists_pow_two_pow_mem_of_mem_sup {L T : Subgroup G} (hT : IsPGroup 2 T)
    (hTL : T ≤ normalizer (L : Set G)) {c : G} (hc : c ∈ L ⊔ T) : ∃ k : ℕ, c ^ 2 ^ k ∈ L := by
  have hc' : c ∈ (L : Set G) * (T : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left L T hTL]
    exact hc
  obtain ⟨l, hl, t, ht, rfl⟩ := hc'
  have key : ∀ n : ℕ, ∃ l' ∈ L, (l * t) ^ n = l' * t ^ n := by
    intro n
    induction n with
    | zero => exact ⟨1, one_mem _, by simp⟩
    | succ n ih =>
      obtain ⟨l', hl', h⟩ := ih
      refine ⟨l' * (t ^ n * l * (t ^ n)⁻¹), mul_mem hl' ?_, ?_⟩
      · exact (mem_normalizer_iff.1 (hTL (pow_mem ht n)) l).1 hl
      · rw [pow_succ, h]
        group
  obtain ⟨k, hk⟩ := hT ⟨t, ht⟩
  have htk : t ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  obtain ⟨l', hl', h⟩ := key (2 ^ k)
  exact ⟨k, by rw [h, htk, mul_one]; exact hl'⟩

theorem normalizer_le_normalizer_centralizer (V : Subgroup G) :
    normalizer (V : Set G) ≤ normalizer (centralizer (V : Set G) : Set G) := by
  intro g hg
  rw [mem_normalizer_iff]
  intro x
  rw [mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · intro hx v hv
    have h1 : g⁻¹ * v * g ∈ V := by
      have := (mem_normalizer_iff.1 (inv_mem hg) v).1 hv
      rwa [inv_inv] at this
    have h2 := hx _ h1
    calc v * (g * x * g⁻¹) = g * ((g⁻¹ * v * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * v * g)) * g⁻¹ := by rw [h2]
      _ = g * x * g⁻¹ * v := by group
  · intro hx v hv
    have h1 : g * v * g⁻¹ ∈ V := (mem_normalizer_iff.1 hg v).1 hv
    have h2 := hx _ h1
    calc v * x = g⁻¹ * ((g * v * g⁻¹) * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * (g * v * g⁻¹)) * g := by rw [h2]
      _ = x * v := by group

theorem inf_centralizer_eq_pCoreOf_sup [Finite G] {T L V : Subgroup G}
    (hT : IsSylowTwoOf T (L ⊔ T)) (hTL : T ≤ normalizer (L : Set G))
    (hLV : L ≤ normalizer (V : Set G)) (hTV : T ≤ normalizer (V : Set G))
    (hVO : V ≤ centralizer (pCoreOf 2 (L ⊔ T) : Set G))
    (hCL : IsPGroup 2 ↥(L ⊓ centralizer (V : Set G))) :
    T ⊓ centralizer (V : Set G) = pCoreOf 2 (L ⊔ T) := by
  refine le_antisymm ?_ (le_inf (EscapingLocal.pCoreOf_le_of_isSylowTwoOf hT)
    (le_centralizer_iff.1 hVO))
  have hC2 : IsPGroup 2 ↥((L ⊔ T) ⊓ centralizer (V : Set G)) := by
    intro c
    obtain ⟨k, hk⟩ := exists_pow_two_pow_mem_of_mem_sup hT.2.1 hTL c.2.1
    have hkC : (c : G) ^ 2 ^ k ∈ L ⊓ centralizer (V : Set G) := ⟨hk, pow_mem c.2.2 _⟩
    obtain ⟨m, hm⟩ := hCL ⟨_, hkC⟩
    have hm' : ((c : G) ^ 2 ^ k) ^ 2 ^ m = 1 := by
      have := congrArg Subtype.val hm
      simpa using this
    refine ⟨k + m, Subtype.ext ?_⟩
    rw [SubmonoidClass.coe_pow, OneMemClass.coe_one, pow_add, pow_mul, hm']
  have hEV : L ⊔ T ≤ normalizer (V : Set G) := sup_le hLV hTV
  have hCn : (((L ⊔ T) ⊓ centralizer (V : Set G)).subgroupOf (L ⊔ T)).Normal := by
    refine (normal_subgroupOf_iff_le_normalizer inf_le_left).2 ?_
    exact (le_inf le_normalizer (hEV.trans (normalizer_le_normalizer_centralizer V))).trans
      inf_normalizer_le_normalizer_inf
  have hCO : (L ⊔ T) ⊓ centralizer (V : Set G) ≤ pCoreOf 2 (L ⊔ T) :=
    LieType.BorelTits.le_pCoreOf 2 inf_le_left hCn hC2
  exact (inf_le_inf_right _ le_sup_right).trans hCO

theorem exists_inf_centralizer_eq_zpowers
    [Finite G] {T L V : Subgroup G}
    (hU3 : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) (hTL : IsSylowTwoOf (T ⊓ L) L)
    (hT2 : IsPGroup 2 T) (hLV : L ≤ normalizer (V : Set G)) (hTV : T ≤ normalizer (V : Set G))
    (hVT : V ≤ T) (hV1 : V ≠ ⊥) (hV2 : ∀ v ∈ V, v ^ 2 = 1) (hV64 : Nat.card V = 64)
    (hO : CFSG.pCore 2 ↥L ≤ (SteinbergBS.normalizerConjOn V L hLV).ker)
    (hfix : V ⊓ centralizer (L : Set G) = ⊥) :
    ∃ z : G, V ⊓ centralizer (T : Set G) = zpowers z ∧ orderOf z = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e1⟩ := CFSG.Timmesfeld.nonempty_mulEquiv_PSU3_of_lieModel hU3
  obtain ⟨e2⟩ := u33Pres_mulEquiv_PSU3
  let e : ↥L ⧸ CFSG.pCore 2 ↥L ≃* U33G := e1.trans e2.symm
  let φ := SteinbergBS.normalizerConjOn V L hLV
  let ψ : U33G →* MulAut V :=
    (QuotientGroup.lift (CFSG.pCore 2 ↥L) φ hO).comp e.symm.toMonoidHom
  let f : ↥L →* U33G := e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hψf : ∀ l : ↥L, ψ (f l) = φ l := fun l => by
    change QuotientGroup.lift (CFSG.pCore 2 ↥L) φ hO (e.symm (e (l : ↥L ⧸ CFSG.pCore 2 ↥L))) =
      φ l
    rw [MulEquiv.symm_apply_apply, QuotientGroup.lift_mk]
  have hψfix : ∀ v : V, (∀ g, ψ g v = v) → v = 1 := by
    intro v hv
    have hvC : (v : G) ∈ V ⊓ centralizer (L : Set G) := by
      refine ⟨v.2, mem_centralizer_iff.2 fun l hl => ?_⟩
      have h1 := congrArg Subtype.val (hv (f ⟨l, hl⟩))
      rw [hψf] at h1
      change l * v * l⁻¹ = v at h1
      rw [mul_inv_eq_iff_eq_mul] at h1
      exact h1
    rw [hfix] at hvC
    exact Subtype.ext ((mem_bot).1 hvC)
  have hP1 : IsPGroup 2 ((T ⊓ L).subgroupOf L) :=
    hTL.2.1.of_equiv (subgroupOfEquivOfLe hTL.1).symm
  let P : Sylow 2 ↥L := hP1.toSylow hTL.2.2
  let S : Sylow 2 U33G := P.mapSurjective hf
  have hV2' : ∀ v : V, v * v = 1 := fun v => Subtype.ext (by
    rw [Subgroup.coe_mul, ← pow_two]
    exact hV2 v v.2)
  have hS := u33_sylow_fixed_card_two hV2' hV64 ψ hψfix S
  have hle : Nat.card (V ⊓ centralizer (T : Set G) : Subgroup G) ≤ 2 := by
    rw [← hS]
    refine Nat.card_le_card_of_injective
      (fun x : (V ⊓ centralizer (T : Set G) : Subgroup G) => ⟨⟨x, x.2.1⟩, fun s hs => ?_⟩) ?_
    · have hs' : s ∈ (S : Subgroup U33G) := hs
      rw [Sylow.coe_mapSurjective] at hs'
      obtain ⟨p, hp, rfl⟩ := hs'
      rw [hψf]
      apply Subtype.ext
      change (p : G) * x * (p : G)⁻¹ = x
      have hp' : p ∈ (T ⊓ L).subgroupOf L := hp
      have hpT : (p : G) ∈ T := (mem_subgroupOf.1 hp').1
      rw [(mem_centralizer_iff.1 x.2.2) _ hpT, mul_inv_cancel_right]
    · intro x y hxy
      apply Subtype.ext
      have := congrArg (fun w : {v : V // ∀ s ∈ S, ψ s v = v} => ((w.1 : V) : G)) hxy
      exact this
  have hne : V ⊓ centralizer (T : Set G) ≠ ⊥ := by
    have hVn : (V.subgroupOf T).Normal := (normal_subgroupOf_iff_le_normalizer hVT).2 hTV
    have hVT1 : V.subgroupOf T ≠ ⊥ := by
      intro h
      apply hV1
      rw [eq_bot_iff]
      intro v hv
      have hv' : (⟨v, hVT hv⟩ : ↥T) ∈ V.subgroupOf T := hv
      rw [h, mem_bot] at hv'
      exact (mem_bot).2 (congrArg Subtype.val hv')
    have : Group.IsNilpotent ↥T := hT2.isNilpotent
    obtain ⟨⟨x, hx⟩, hx1⟩ :=
      ne_bot_iff_exists_ne_one.1 (Group.IsNilpotent.inf_center_ne_bot_of_normal hVT1)
    rw [ne_bot_iff_exists_ne_one]
    refine ⟨⟨x, mem_subgroupOf.1 hx.1, mem_centralizer_iff.2 fun t ht => ?_⟩, ?_⟩
    · exact congrArg Subtype.val ((mem_center_iff.1 hx.2) ⟨t, ht⟩)
    · intro h
      apply hx1
      have h1 : (x : G) = 1 := congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext h1)
  obtain ⟨⟨z, hz⟩, hz1⟩ := ne_bot_iff_exists_ne_one.1 hne
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hord : orderOf z = 2 := orderOf_eq_prime (hV2 z hz.1) hz1'
  refine ⟨z, ?_, hord⟩
  symm
  refine eq_of_le_of_card_ge (zpowers_le.2 hz) ?_
  rw [Nat.card_zpowers, hord]
  exact hle

theorem u3_internal_frame_producer
    (h1332 : Stmt13_3_2) : U3InternalFrameProducer := by
  intro G _ _ T L hH hU3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := isSimpleGroup_of_lieModel_PSU hU3
  obtain ⟨-, ⟨hTL, -⟩, ⟨⟨V, hV⟩, hVall⟩, -⟩ := h1332 G T L hH L hH.faithful
  obtain ⟨hVT, hTV, -, hcomm, hmod⟩ := hVall V hV
  obtain ⟨hVR, hV1, hLV, -, hVlt, hirr, -⟩ := hV
  have hloc := hH.faithful.1
  have hTsyl : IsSylowTwoOf T (L ⊔ T) := ⟨le_sup_right, hloc.1, hloc.2.2.1⟩
  have hVf := fun v (hv : v ∈ V) => mem_reducedAggregate (hVR hv)
  have hVO : V ≤ pCoreOf 2 (L ⊔ T) := fun v hv => (hVf v hv).1
  have hVC : V ≤ centralizer (pCoreOf 2 (L ⊔ T) : Set G) :=
    fun v hv => mem_centralizer_iff.2 fun k hk => (hVf v hv).2.1 k hk
  have hV2 : ∀ v ∈ V, v ^ 2 = 1 := fun v hv => (hVf v hv).2.2
  have hVe : IsElementaryAbelian 2 V := BlueprintB2.isElementaryAbelian_iff.2
    ⟨fun a ha b hb => ((hVf a ha).2.1 b (hVO hb)).symm, hV2⟩
  have hLC : ¬ L ≤ centralizer (V : Set G) := fun h =>
    (lt_irrefl _) (lt_of_lt_of_le hVlt (le_inf le_rfl (le_centralizer_iff.1 h)))
  have hOL : pCoreOf 2 L ≤ centralizer (V : Set G) :=
    (pCoreOf_le_pCoreOf_sup hTL).trans (le_centralizer_iff.1 hVC)
  have hK1 := inf_centralizer_subgroupOf_eq_pCore hs hLV hOL hLC
  have hcardL : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 6048 := by
    obtain ⟨e1⟩ := CFSG.Timmesfeld.nonempty_mulEquiv_PSU3_of_lieModel hU3
    obtain ⟨e2⟩ := u33Pres_mulEquiv_PSU3
    rw [Nat.card_congr (e1.trans e2.symm).toEquiv]
    exact card_u33G
  have haut : Nat.card (autOn L V) = 6048 := by
    rw [card_autOn_eq_relIndex hLV, Subgroup.relIndex, hK1, index_eq_card, hcardL]
  have hcase : G2NaturalDerived (V := ↥V) (autOn L V) ⊤ ⊥ 1 ∧
      V ⊓ centralizer (L : Set G) = ⊥ := by
    rcases hmod with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, h⟩ | ⟨-, h, -⟩ | ⟨-, h, h'⟩
    · have h1 := card_le_of_realizes h (by
        change Finite ↥(alternatingGroup (Fin 5))
        infer_instance)
      have h2 : Nat.card (alternatingGroup (Fin 5)) ≤ 720 := card_alternatingGroup_le (by norm_num)
      change Nat.card (autOn L V) ≤ Nat.card (alternatingGroup (Fin 5)) at h1
      omega
    · have h1 := card_le_of_realizes h (by
        change Finite ↥(alternatingGroup (Fin 6))
        infer_instance)
      have h2 : Nat.card (alternatingGroup (Fin 6)) ≤ 720 := card_alternatingGroup_le le_rfl
      change Nat.card (autOn L V) ≤ Nat.card (alternatingGroup (Fin 6)) at h1
      omega
    · have h1 := card_le_of_realizes h (by
        change Finite ↥(alternatingGroup (Fin 6))
        infer_instance)
      have h2 : Nat.card (alternatingGroup (Fin 6)) ≤ 720 := card_alternatingGroup_le le_rfl
      change Nat.card (autOn L V) ≤ Nat.card (alternatingGroup (Fin 6)) at h1
      omega
    · obtain ⟨K, _, _, hK, hR⟩ := h
      obtain ⟨hfin, h2⟩ := finite_and_card_le_of_GL_three (hK.trans (pow_one 2)) (StatedSL 3 K)
      have h1 := card_le_of_realizes hR hfin
      change Nat.card (autOn L V) ≤ Nat.card (StatedSL 3 K) at h1
      omega
    · exact ⟨h, h'⟩
  obtain ⟨hG2, hCL0⟩ := hcase
  have hV64 : Nat.card V = 64 := by
    obtain ⟨K, _, _, hK, π, -, -, -, -, -, -, -, β, hβs, hβk, -⟩ := hG2
    have hβi : Function.Injective β := by
      rw [injective_iff_map_eq_one]
      intro u hu
      exact Subtype.ext ((mem_bot).1 ((hβk u).1 hu))
    have h1 := Nat.card_congr (Equiv.ofBijective β ⟨hβi, hβs⟩)
    rw [card_top] at h1
    rw [h1]
    exact card_zornQ_of_card_two (hK.trans (pow_one 2))
  have hirr' : ∀ W : Subgroup G, W ≤ V → (∀ l ∈ L, ∀ w ∈ W, l * w * l⁻¹ ∈ W) →
      W = ⊥ ∨ W = V := by
    intro W hWV hW
    have hLW : L ≤ normalizer (W : Set G) := fun l hl => mem_normalizer_iff.2 fun w =>
      ⟨fun hw => hW l hl w hw, fun hw => by
        have := hW l⁻¹ (inv_mem hl) _ hw
        simpa [mul_assoc] using this⟩
    rcases hirr W (by rw [hCL0]; exact bot_le) hWV hLW with h | h
    · exact Or.inl (h.trans hCL0)
    · exact Or.inr h
  have hnt : ∃ l ∈ L, ∃ v ∈ V, l * v * l⁻¹ ≠ v := by
    obtain ⟨v, hv, hvn⟩ := IsConcreteLE.exists_of_lt hVlt
    have hvC : v ∉ centralizer (L : Set G) := fun h => hvn ⟨hv, h⟩
    rw [mem_centralizer_iff] at hvC
    push Not at hvC
    obtain ⟨l, hl, hlv⟩ := hvC
    refine ⟨l, hl, v, hv, fun h => hlv ?_⟩
    rwa [mul_inv_eq_iff_eq_mul] at h
  have hCL : IsPGroup 2 ↥(L ⊓ centralizer (V : Set G)) := by
    have h := CFSG.pCore_isPGroup (p := 2) (G := ↥L)
    rw [← hK1] at h
    exact h.of_equiv (subgroupOfEquivOfLe inf_le_left)
  have hTLs : IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal hTsyl le_sup_left (sup_le le_normalizer hTL)
  have hO : CFSG.pCore 2 ↥L ≤ (SteinbergBS.normalizerConjOn V L hLV).ker := by
    rw [ker_normalizerConjOn, hK1]
  obtain ⟨z, hz, hz2⟩ :=
    exists_inf_centralizer_eq_zpowers hU3 hTLs hloc.1 hLV hTV hVT hV1 hV2 hV64 hO hCL0
  exact ⟨V, z, hTL, hVT, hVe, hV64, hVO, hVC, hLV, hTV, hirr', hnt,
    inf_centralizer_eq_pCoreOf_sup hTsyl hTL hLV hTV hVC hCL, hz, hz2⟩

end CFSG.Quasithin.H13.U3
