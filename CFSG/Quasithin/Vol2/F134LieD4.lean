module

public import CFSG.Quasithin.Vol2.F134LieD4Cells
public import CFSG.Quasithin.Vol2.F134LieD4Field
public import CFSG.Quasithin.Vol2.F134LieF4Group

public section

namespace CFSG.Quasithin.F134.LieD4

open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank
  CFSG.ABGLocalTools CFSG.LieType.BorelTits
open scoped Pointwise

theorem exists_proper_overgroup_of_not_dvd {Y : Type*} [Group Y] [Finite Y] (hBT : Holds Y 2)
    {U H : Subgroup Y} (hU : IsSylowOf 2 U ⊤) (hUH : U ≤ H)
    (hcard : ¬ Nat.card H ∣ (U.subgroupOf H).index.factorial) :
    ∃ Q : Subgroup Y, Q ≠ ⊤ ∧ H ≤ Q ∧ Subgroup.normalizer (U : Set Y) ≤ Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := (U.subgroupOf H).normalCore with hC
  have hCne : C ≠ ⊥ := by
    intro hbot
    have h := (U.subgroupOf H).index_normalCore_dvd_factorial_index
    rw [← hC, hbot, Subgroup.index_bot] at h
    exact hcard h
  set V := C.map H.subtype with hV
  have hVU : V ≤ U := by
    rintro _ ⟨c, hc, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (Subgroup.normalCore_le _ hc)
  have hVne : V ≠ ⊥ := by
    intro h
    apply hCne
    rwa [hV, Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective] at h
  have hVsub : V.subgroupOf H = C := by
    rw [hV, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  have hHV : H ≤ Subgroup.normalizer (V : Set Y) := by
    have hn : (V.subgroupOf H).Normal := by
      rw [hVsub]
      exact Subgroup.normalCore_normal _
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le C)).1 hn
  obtain ⟨S, Q, hQ, hNQ, -, -, hSQ⟩ := hBT V hVne (hU.isPGroup.to_le hVU)
  have hHQ : H ≤ Q := hHV.trans hNQ
  exact ⟨Q, hQ, hHQ, LieF4.normalizer_le_of_isSylowOf
    (LieF4.isSylowOf_of_sylow S (Subgroup.le_normalizer.trans hSQ))
    (hU.of_le (hUH.trans hHQ) le_top) hSQ⟩

section Models


theorem exists_mulEquiv_graphFixedRootGroup {X : Type} [Group X] {n : ℕ}
    (hX : ChevalleyExceptionalModel X .trialityD4 2 n) :
    1 ≤ n ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K ≃+* K),
      Nat.card K = (2 ^ n) ^ 3 ∧ (∀ c, σ c = c ^ (2 ^ n)) ∧
        Nonempty (X ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  obtain ⟨⟨-, hn, -⟩, K, _, _, hK, σ, hσc, ⟨e⟩⟩ := hX
  have hσb : Function.Bijective σ := ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩
  obtain ⟨-, -, -, -, -, -, -, ⟨f⟩⟩ :=
    even_triality_exact_automorphism_normal_form hn K hK (RingEquiv.ofBijective σ hσb) hσc
  exact ⟨hn, K, inferInstance, inferInstance, RingEquiv.ofBijective σ hσb, hK, hσc,
    ⟨e.trans f⟩⟩

theorem exists_mulEquiv_map_eq {X : Type} [Group X] [Finite X] {n : ℕ}
    (hX : ChevalleyExceptionalModel X .trialityD4 2 n) (U : Sylow 2 X) :
    1 ≤ n ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K ≃+* K),
      Nat.card K = (2 ^ n) ^ 3 ∧ (∀ c, σ c = c ^ (2 ^ n)) ∧
        ∃ e : X ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
          (U : Subgroup X).map e.toMonoidHom =
            (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
              (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  obtain ⟨hn, K, _, _, σ, hK, hσc, ⟨e₀⟩⟩ := exists_mulEquiv_graphFixedRootGroup hX
  refine ⟨hn, K, inferInstance, inferInstance, σ, hK, hσc, ?_⟩
  have hK3 : Nat.card K = 2 ^ (3 * n) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) hK3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  let S₀ : Sylow 2 (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    (isPGroup_graphFixedPosUnipotent_subgroupOf 2).toSylow
      (not_dvd_index_graphFixedPosUnipotent 2 σ.surjective)
  have hle : (S₀ : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ≤
      e₀.toMonoidHom.range := by
    rw [MonoidHom.range_eq_top.2 e₀.surjective]
    exact le_top
  have he₀ : Function.Injective e₀.toMonoidHom := e₀.injective
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq X U (S₀.comapOfInjective e₀.toMonoidHom he₀ hle)
  refine ⟨(MulAut.conj x).trans e₀, ?_⟩
  have hU : ((x • U : Sylow 2 X) : Subgroup X) =
      (U : Subgroup X).map (MulAut.conj x).toMonoidHom := by
    rw [Sylow.coe_subgroup_smul]
    rfl
  rw [show ((MulAut.conj x).trans e₀).toMonoidHom =
      e₀.toMonoidHom.comp (MulAut.conj x).toMonoidHom from rfl, ← Subgroup.map_map, ← hU, hx,
    Sylow.coe_comapOfInjective, Subgroup.map_comap_eq_self hle]
  rfl

end Models

section Models'


theorem even_and_le_normalizer_of_mul {X : Type} [Group X] [Finite X] {n : ℕ}
    (hX : ChevalleyExceptionalModel X .trialityD4 2 n) (U : Sylow 2 X) {P : Subgroup X}
    (hP : Nat.card P = 9) (hexp : ∀ x ∈ P, x ^ 3 = 1)
    (hmul : ∀ u ∈ (U : Subgroup X), ∀ x ∈ P, ∃ y ∈ P, ∃ s ∈ (U : Subgroup X), u * x = y * s) :
    Even n ∧ P ≤ Subgroup.normalizer ((U : Subgroup X) : Set X) := by
  obtain ⟨hn, K, _, _, σ, hK, hσc, e, he⟩ := exists_mulEquiv_map_eq hX U
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hUC := graphFixedPosUnipotent_le_graphFixedRootGroup TwistTag.D4 K σ.toRingHom
  set φ : X →* ModGL TwistTag.D4.tag K :=
    (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype.comp e.toMonoidHom with hφ
  have hφi : Function.Injective φ := Subtype.val_injective.comp e.injective
  have hφr : (⊤ : Subgroup X).map φ = graphFixedRootGroup TwistTag.D4 K σ.toRingHom := by
    rw [hφ, ← Subgroup.map_map, Subgroup.map_top_of_surjective _ e.surjective, Subgroup.map_top,
      Subgroup.range_subtype]
  have hφU : (U : Subgroup X).map φ = graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom := by
    rw [hφ, ← Subgroup.map_map, he, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hUC]
  have hH : Nat.card (P ⊔ (U : Subgroup X) : Subgroup X) = 9 * Nat.card (U : Subgroup X) :=
    CFSG.Quasithin.P134.card_sup_eq_of_mul hP U.isPGroup' hmul
  have hcardU : Nat.card (U : Subgroup X) = (2 ^ n) ^ 12 := by
    rw [← Subgroup.card_map_of_injective hφi, hφU,
      CFSG.Timmesfeld.ExceptionalOrders.card_graphFixedPosUnipotent σ.surjective
        (CFSG.Timmesfeld.ExceptionalOrders.card_orbitField Nat.prime_two hn hK hσc),
      CFSG.Timmesfeld.ExceptionalOrders.ncard_posRoots_twistedD4]
  have hrel : ((U : Subgroup X).subgroupOf (P ⊔ (U : Subgroup X))).index = 9 := by
    have h := Subgroup.relIndex_mul_card (U : Subgroup X) (P ⊔ (U : Subgroup X))
    rw [inf_eq_left.2 le_sup_right, hH] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  obtain ⟨Q, hQ, hHQ, hNQ⟩ := exists_proper_overgroup_of_not_dvd
    (holds_of_chevalleyExceptionalModel hX) (LieF4.isSylowOf_of_sylow U le_top) le_sup_right (by
      rw [hrel, hH, hcardU]
      intro hdvd
      have h12 : 2 ^ 12 ∣ Nat.factorial 9 := by
        refine Dvd.dvd.trans ?_ ((Dvd.intro_left 9 rfl).trans hdvd)
        rw [← pow_mul]
        exact pow_dvd_pow 2 (by nlinarith)
      norm_num [Nat.factorial] at h12)
  have hle : graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤ φ.range := by
    rw [← hφU]
    exact Subgroup.map_le_range φ _
  have hNcomap : (Subgroup.normalizer (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom :
      Set (ModGL TwistTag.D4.tag K))).comap φ = Subgroup.normalizer ((U : Subgroup X) : Set X) := by
    rw [Subgroup.comap_normalizer_eq_of_le_range hle, ← hφU,
      Subgroup.comap_map_eq_self_of_injective hφi]
  have hBQ : graphFixedRootBorel TwistTag.D4 K σ.toRingHom ≤ Q.map φ := by
    intro b hb
    rw [← graphFixedRootGroup_inf_normalizer_graphFixedPosUnipotent σ.surjective] at hb
    obtain ⟨hbC, hbN⟩ := hb
    rw [← hφr] at hbC
    obtain ⟨x, -, rfl⟩ := hbC
    refine ⟨x, hNQ ?_, rfl⟩
    rw [← hNcomap]
    exact hbN
  obtain ⟨hev, hHB⟩ := even_and_le_graphFixedRootBorel σ hn hK hσc (Q := Q.map φ)
    (H := (P ⊔ (U : Subgroup X)).map φ) (P := P.map φ) hBQ
    ((Subgroup.map_le_range φ Q).trans (by rw [MonoidHom.range_eq_map, hφr]))
    (fun h => hQ (Subgroup.map_injective hφi (by rw [h, hφr]))) (Subgroup.map_mono hHQ)
    (by rw [← hφU]; exact Subgroup.map_mono le_sup_right)
    (by rw [Subgroup.card_map_of_injective hφi, hH, ← Subgroup.card_map_of_injective hφi, hφU])
    (Subgroup.map_mono le_sup_left) (by rw [Subgroup.card_map_of_injective hφi, hP])
    (by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hexp x hx, map_one])
  refine ⟨hev, fun x hx => ?_⟩
  have hxB := hHB ⟨x, Subgroup.mem_sup_left hx, rfl⟩
  rw [← hNcomap]
  exact graphFixedRootBorel_le_normalizer_graphFixedPosUnipotent hxB

theorem exists_inv_mul_pow_mem_of_map_eq {X : Type} [Group X] [Finite X] {n : ℕ}
    (hX : ChevalleyExceptionalModel X .trialityD4 2 n) (U : Sylow 2 X) (α : MulAut X)
    (hα : (U : Subgroup X).map α.toMonoidHom = U) :
    ∃ k : ℕ, ∀ b ∈ Subgroup.normalizer ((U : Subgroup X) : Set X),
      (α b)⁻¹ * b ^ (2 ^ k) ∈ (U : Subgroup X) := by
  obtain ⟨hn, K, _, _, σ, hK, hσc, e, he⟩ := exists_mulEquiv_map_eq hX U
  have hUC := graphFixedPosUnipotent_le_graphFixedRootGroup TwistTag.D4 K σ.toRingHom
  set α' : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := (e.symm.trans α).trans e
    with hα'
  have hmapα' : ((graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map α'.toMonoidHom =
      (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
    rw [← he, hα', show ((e.symm.trans α).trans e).toMonoidHom =
      e.toMonoidHom.comp (α.toMonoidHom.comp e.symm.toMonoidHom) from rfl, ← Subgroup.map_map,
      ← Subgroup.map_map, Subgroup.map_map _ e.symm.toMonoidHom e.toMonoidHom]
    rw [show e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id X from
      MonoidHom.ext fun x => e.symm_apply_apply x, Subgroup.map_id, hα]
  obtain ⟨k, hk⟩ := exists_inv_mul_pow_mem_graphFixedPosUnipotent σ hn hK hσc α' hmapα'
  refine ⟨k, fun b hb => ?_⟩
  have hbB : ((e b : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : ModGL TwistTag.D4.tag K) ∈
      graphFixedRootBorel TwistTag.D4 K σ.toRingHom := by
    have h1 : e b ∈ Subgroup.normalizer (((graphFixedPosUnipotent TwistTag.D4 K
        σ.toRingHom).subgroupOf (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : Subgroup _) :
          Set _) := by
      rw [← he, ← Subgroup.map_equiv_normalizer_eq]
      exact ⟨b, hb, rfl⟩
    rw [← graphFixedRootGroup_inf_normalizer_graphFixedPosUnipotent σ.surjective]
    exact Subgroup.mem_inf.2 ⟨(e b).2, mem_normalizer_of_mem_normalizer_subgroupOf hUC h1⟩
  have h2 := hk (e b) hbB
  have h3 : α' (e b) = e (α b) := by
    simp only [hα', MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rw [h3] at h2
  have h4 : e ((α b)⁻¹ * b ^ (2 ^ k)) ∈ (graphFixedPosUnipotent TwistTag.D4 K
      σ.toRingHom).subgroupOf (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
    rw [Subgroup.mem_subgroupOf, map_mul, map_inv, map_pow]
    exact h2
  rw [← he] at h4
  obtain ⟨y, hy, hye⟩ := h4
  rwa [← e.injective hye]

end Models'

end CFSG.Quasithin.F134.LieD4

namespace CFSG.Quasithin.P134

open CFSG.Quasithin.F134 CFSG.Quasithin.F134.LieD4 CFSG.Assembly.LowTwoRank CFSG.Blueprint

theorem facts134E9_d4Even
    : ∀ n : ℕ,
    NoE9Config fun (X : Type) [Group X] => ChevalleyExceptionalModel X .trialityD4 2 n := by
  intro n A _ _ L P T hL hcfg
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : L.Normal := hcfg.normal
  have hS := E9Config.isSylowTwoOf_inf hcfg
  let U : Sylow 2 L :=
    (hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm).toSylow hS.2.2
  have hU : (U : Subgroup L) = (T ⊓ L).subgroupOf L := rfl
  have hP' : Nat.card (P.subgroupOf L) = 9 := by
    rw [← hcfg.card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcfg.le).toEquiv
  have hexp' : ∀ x ∈ P.subgroupOf L, x ^ 3 = 1 := fun x hx =>
    Subtype.ext (by simpa using hcfg.exp x (Subgroup.mem_subgroupOf.mp hx))
  have hmul' : ∀ u ∈ (U : Subgroup L), ∀ x ∈ P.subgroupOf L, ∃ y ∈ P.subgroupOf L,
      ∃ s ∈ (U : Subgroup L), u * x = y * s := by
    intro u hu x hx
    rw [hU] at hu
    obtain ⟨y, hy, s, hs, he⟩ := E9Config.mul_inf hcfg u (Subgroup.mem_subgroupOf.mp hu) x
      (Subgroup.mem_subgroupOf.mp hx)
    exact ⟨⟨y, hcfg.le hy⟩, Subgroup.mem_subgroupOf.mpr hy, ⟨s, hs.2⟩,
      by rw [hU]; exact Subgroup.mem_subgroupOf.mpr hs, Subtype.ext he⟩
  obtain ⟨-, hPN⟩ := even_and_le_normalizer_of_mul hL U hP' hexp' hmul'
  have hpow : ∀ t ∈ T ⊓ Subgroup.normalizer (P : Set A), ∃ k : ℕ,
      ∀ x ∈ P, t * x * t⁻¹ = x ^ (2 ^ k) := by
    intro t ht
    obtain ⟨htT, htN⟩ := Subgroup.mem_inf.1 ht
    have hαU : (U : Subgroup L).map (MulAut.conjNormal t).toMonoidHom = U := by
      refine Subgroup.eq_of_le_of_card_ge ?_ ?_
      · rintro _ ⟨y, hy, rfl⟩
        have hy' : (y : A) ∈ T ⊓ L := by
          have := SetLike.mem_coe.1 hy
          rw [hU, Subgroup.mem_subgroupOf] at this
          exact this
        rw [hU, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom, MulAut.conjNormal_apply]
        exact Subgroup.mem_inf.2 ⟨mul_mem (mul_mem htT (Subgroup.mem_inf.1 hy').1) (inv_mem htT),
          (MulAut.conjNormal t y).2⟩
      · rw [Subgroup.card_map_of_injective (MulEquiv.injective _)]
    obtain ⟨k, hk⟩ := exists_inv_mul_pow_mem_of_map_eq hL U (MulAut.conjNormal t) hαU
    refine ⟨k, fun x hx => ?_⟩
    have hx' : (⟨x, hcfg.le hx⟩ : L) ∈ P.subgroupOf L := hx
    have h1 := hk _ (hPN hx')
    have hαx : MulAut.conjNormal t (⟨x, hcfg.le hx⟩ : L) ∈ P.subgroupOf L := by
      rw [Subgroup.mem_subgroupOf, MulAut.conjNormal_apply]
      exact (Subgroup.mem_normalizer_iff.1 htN x).1 hx
    have h2 : (MulAut.conjNormal t (⟨x, hcfg.le hx⟩ : L))⁻¹ * ⟨x, hcfg.le hx⟩ ^ (2 ^ k) ∈
        P.subgroupOf L := mul_mem (inv_mem hαx) (pow_mem hx' _)
    have hdisj : (U : Subgroup L) ⊓ P.subgroupOf L = ⊥ := by
      refine disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard ?_)
      obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 U.isPGroup'
      rw [hm, hP']
      exact Nat.Coprime.pow_left m (by norm_num)
    have h3 : (MulAut.conjNormal t (⟨x, hcfg.le hx⟩ : L))⁻¹ * ⟨x, hcfg.le hx⟩ ^ (2 ^ k) = 1 := by
      have h13 : _ ∈ (U : Subgroup L) ⊓ P.subgroupOf L := ⟨h1, h2⟩
      rwa [hdisj, Subgroup.mem_bot] at h13
    have h5 := congrArg Subtype.val (inv_mul_eq_one.1 h3)
    rw [MulAut.conjNormal_apply] at h5
    simpa using h5
  obtain ⟨x₀, hx₀, hx₀1⟩ : ∃ x ∈ P, x ≠ 1 := by
    by_contra h
    have hbot : P = ⊥ := (Subgroup.eq_bot_iff_forall P).2 fun x hx => by
      by_contra hx1
      exact h ⟨x, hx, hx1⟩
    have := hcfg.card
    rw [hbot, Subgroup.card_bot] at this
    norm_num at this
  have key : ∀ t ∈ T ⊓ Subgroup.normalizer (P : Set A), ∀ y ∈ Subgroup.zpowers x₀,
      t * y * t⁻¹ ∈ Subgroup.zpowers x₀ := by
    intro t ht y hy
    obtain ⟨k, hk⟩ := hpow t ht
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [← conj_zpow, hk x₀ hx₀]
    exact zpow_mem (pow_mem (Subgroup.mem_zpowers x₀) _) m
  have hQN : T ⊓ Subgroup.normalizer (P : Set A) ≤
      Subgroup.normalizer (Subgroup.zpowers x₀ : Set A) := by
    intro t ht
    refine Subgroup.mem_normalizer_iff.2 fun y => ⟨key t ht y, fun hy => ?_⟩
    have := key t⁻¹ (inv_mem ht) _ hy
    simpa [mul_assoc] using this
  rcases hcfg.irred _ ((Subgroup.zpowers_le).2 hx₀) hQN with h | h
  · exact hx₀1 (Subgroup.zpowers_eq_bot.1 h)
  · have h1 : Nat.card (Subgroup.zpowers x₀) = 9 := by rw [h, hcfg.card]
    rw [Nat.card_zpowers] at h1
    have := orderOf_dvd_of_pow_eq_one (hcfg.exp x₀ hx₀)
    rw [h1] at this
    norm_num at this

end CFSG.Quasithin.P134
