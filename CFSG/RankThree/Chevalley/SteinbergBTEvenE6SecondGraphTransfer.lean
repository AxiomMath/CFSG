module

public import CFSG.RankThree.Chevalley.SteinbergBTEvenE6OddCoreTools
public import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizerTwisted

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification (OuterAutomorphisms.inner OuterAutomorphisms.inner_normal)
open CFSG.LieType.Chevalley.E6SecondGraphFull (SecondGraphFullCentralizer
  secondGraphFullCentralizer_adjointGroup secondGraphFullCentralizer_graphFixedRootGroup)
open CFSG.ComponentClassification.UnbalancedCatalog (EvenCatalog.le_oddCore_of_normal
  EvenCatalog.odd_card_oddCore EvenCatalog.not_mem_oddCore_of_sq_eq_one)

theorem oddCore_inf_centralizer_xi_eq_bot {G : Type*} [Group G] {C J : Subgroup G} [Finite C]
    {P t : G} {F : Type*} {act : F → MulAut J} (hSG : SecondGraphFullCentralizer C J P t act)
    (hP2 : P * P = 1) (hZJ : Subgroup.center J = ⊥) (ξ : MulAut C)
    (hξ : ∀ g : C, (ξ g : G) = t * (P * g * P⁻¹) * t⁻¹)
    (hF4 : ∀ τJ : MulAut J, (∀ x : J, (τJ x : G) = t * x * t⁻¹) →
      ∀ L : Subgroup (MulAut J), OuterAutomorphisms.inner J ≤ L →
        CFSG.oddCore ↥(L ⊓ Subgroup.centralizer {τJ}) = ⊥)
    (H : Subgroup (MulAut C)) (hIH : OuterAutomorphisms.inner C ≤ H) :
    CFSG.oddCore ↥(H ⊓ Subgroup.centralizer {ξ}) = ⊥ := by
  classical
  obtain ⟨htJ, hJC, η, hη, -, res, -, hker, hrange, -, hfixt, hinner, -⟩ := hSG
  have : Finite (MulAut C) := Finite.of_injective (fun β : MulAut C => (β : C → C))
    fun _ _ h => MulEquiv.ext (congrFun h)
  have : Finite J := Finite.of_injective (fun x : J => (⟨x, hJC x.2⟩ : C))
    fun x y h => Subtype.ext (congrArg Subtype.val h :)
  have : Finite (MulAut J) := Finite.of_injective (fun β : MulAut J => (β : J → J))
    fun _ _ h => MulEquiv.ext (congrFun h)
  have hξη : ξ = MulAut.conj (⟨t, hJC htJ⟩ : C) * η := MulEquiv.ext fun g => Subtype.ext (by
    rw [hξ, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, hη])
  subst hξη
  set τ : MulAut J := MulAut.conj (⟨t, htJ⟩ : J) with hτdef
  have hτ : ∀ x : J, (τ x : G) = t * x * t⁻¹ := fun x => rfl
  have hη2 : η * η = 1 := MulEquiv.ext fun g => Subtype.ext (by
    rw [MulAut.mul_apply, hη, hη, MulAut.one_apply]
    calc P * (P * (g : G) * P⁻¹) * P⁻¹ = (P * P) * g * (P * P)⁻¹ := by group
      _ = g := by rw [hP2, one_mul, inv_one, mul_one])
  set ZH := H ⊓ Subgroup.centralizer {MulAut.conj (⟨t, hJC htJ⟩ : C) * η} with hZH
  have hZHZ : ZH ≤ Subgroup.centralizer {MulAut.conj (⟨t, hJC htJ⟩ : C) * η} := inf_le_right
  set resH : ZH →* MulAut J := res.comp (Subgroup.inclusion hZHZ) with hresHdef
  set A := resH.range with hAdef
  have hAτ : A ≤ Subgroup.centralizer {τ} := by
    rintro _ ⟨z, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hfixt (resH z) ⟨_, rfl⟩
    have h2 := mulAut_mul_conj_mul_inv (resH z) (⟨t, htJ⟩ : J)
    rw [h1] at h2
    calc resH z * τ = (resH z * τ * (resH z)⁻¹) * resH z := by group
      _ = τ * resH z := by rw [hτdef, h2]
  have hIA : ∀ x : J, x * ⟨t, htJ⟩ = ⟨t, htJ⟩ * x → MulAut.conj x ∈ A := by
    intro x hx
    obtain ⟨hxZ, hres⟩ := hinner x hx
    refine ⟨⟨_, hIH ⟨⟨x, hJC x.2⟩, rfl⟩, hxZ⟩, ?_⟩
    rw [hresHdef, MonoidHom.comp_apply]
    exact hres
  set L := OuterAutomorphisms.inner J ⊔ A with hLdef
  have hLA : L ⊓ Subgroup.centralizer {τ} = A := by
    refine le_antisymm (fun y hy => ?_) (le_inf le_sup_right hAτ)
    obtain ⟨hyL, hyτ⟩ := Subgroup.mem_inf.1 hy
    have : (OuterAutomorphisms.inner J).Normal := OuterAutomorphisms.inner_normal J
    rw [← SetLike.mem_coe, hLdef, Subgroup.normal_mul] at hyL
    obtain ⟨i, hi, a, ha, rfl⟩ := hyL
    obtain ⟨z, rfl⟩ := hi
    have haτ := Subgroup.mem_centralizer_singleton_iff.1 (hAτ ha)
    have hyτ' := Subgroup.mem_centralizer_singleton_iff.1 hyτ
    have hzτ : τ * MulAut.conj z = MulAut.conj z * τ := by
      have h1 : τ * MulAut.conj z * a = MulAut.conj z * τ * a := by
        calc τ * MulAut.conj z * a = τ * (MulAut.conj z * a) := by group
          _ = MulAut.conj z * a * τ := hyτ'.symm
          _ = MulAut.conj z * (a * τ) := by group
          _ = MulAut.conj z * (τ * a) := by rw [haτ]
          _ = MulAut.conj z * τ * a := by group
      exact mul_right_cancel h1
    have hzt : z * ⟨t, htJ⟩ = ⟨t, htJ⟩ * z := by
      have h1 : MulAut.conj (z * ⟨t, htJ⟩ * z⁻¹) = MulAut.conj (⟨t, htJ⟩ : J) := by
        rw [map_mul, map_mul, map_inv, ← hτdef, ← hzτ]
        group
      have h2 := mulAut_conj_injective_of_center_eq_bot hZJ h1
      calc z * ⟨t, htJ⟩ = (z * ⟨t, htJ⟩ * z⁻¹) * z := by group
        _ = ⟨t, htJ⟩ * z := by rw [h2]
    exact mul_mem (hIA z hzt) ha
  have hAcore : CFSG.oddCore A = ⊥ := by
    have h := hF4 τ hτ L le_sup_left
    rwa [hLA] at h
  set R := CFSG.oddCore ZH with hRdef
  set resH' : ZH →* A := resH.rangeRestrict with hresH'def
  have hsurj : Function.Surjective resH' := resH.rangeRestrict_surjective
  have hRnorm : R.Normal := CFSG.oddCore_normal ZH
  have hRodd : Odd (Nat.card R) := EvenCatalog.odd_card_oddCore
  have hmap : R.map resH' = ⊥ := by
    have hle : R.map resH' ≤ CFSG.oddCore A := EvenCatalog.le_oddCore_of_normal
      (hRnorm.map resH' hsurj) (hRodd.of_dvd_nat (Subgroup.card_map_dvd R resH'))
    rw [hAcore] at hle
    exact le_bot_iff.1 hle
  rw [eq_bot_iff]
  intro r hr
  have hr1 : resH' r = 1 := by
    have : resH' r ∈ R.map resH' := ⟨r, hr, rfl⟩
    rwa [hmap, Subgroup.mem_bot] at this
  have hrker : ((r : ZH) : MulAut C) ∈ Subgroup.zpowers η := by
    rw [← hker]
    refine Subgroup.mem_map.2 ⟨Subgroup.inclusion hZHZ r, MonoidHom.mem_ker.2 ?_, rfl⟩
    exact congrArg Subtype.val hr1
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hrker
  have hr2 : r ^ 2 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, Nat.cast_ofNat,
      zpow_two, hη2, one_zpow, Subgroup.coe_one]
  by_contra hr1'
  exact EvenCatalog.not_mem_oddCore_of_sq_eq_one (fun h => hr1' (Subgroup.mem_bot.2 h)) hr2 hr

theorem oddCore_inf_centralizer_xi_conj_eq_bot {G : Type*} [Group G] {C J : Subgroup G}
    [Finite C] {P t : G} {F : Type*} {act : F → MulAut J}
    (hSG : SecondGraphFullCentralizer C J P t act) (hP2 : P * P = 1)
    (hZJ : Subgroup.center J = ⊥) (ξ : MulAut C)
    (hξ : ∀ g : C, (ξ g : G) = t * (P * g * P⁻¹) * t⁻¹)
    (hF4 : ∀ τJ : MulAut J, (∀ x : J, (τJ x : G) = t * x * t⁻¹) →
      ∀ L : Subgroup (MulAut J), OuterAutomorphisms.inner J ≤ L →
        CFSG.oddCore ↥(L ⊓ Subgroup.centralizer {τJ}) = ⊥)
    (H : Subgroup (MulAut C)) (hIH : OuterAutomorphisms.inner C ≤ H) :
    CFSG.oddCore ↥(H ⊓ Subgroup.centralizer {ξ}) = ⊥ ∧
      ∀ α ∈ H, (∃ φ : MulAut C, φ * α * φ⁻¹ = ξ) →
        CFSG.oddCore ↥(H ⊓ Subgroup.centralizer {α}) = ⊥ :=
  ⟨oddCore_inf_centralizer_xi_eq_bot hSG hP2 hZJ ξ hξ hF4 H hIH, fun _ _ ⟨_, hα⟩ =>
    oddCore_inf_centralizer_conj_eq_bot
      (fun H' hIH' => oddCore_inf_centralizer_xi_eq_bot hSG hP2 hZJ ξ hξ hF4 H' hIH') H hIH hα⟩

theorem center_eq_bot_of_mulEquiv_adjointGroup {G : Type*} [Group G] {J : Subgroup G}
    (k : Type) [Field k] (e : J ≃* adjointGroup Tag.F4 k) : Subgroup.center J = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have h1 : e x ∈ Subgroup.center (adjointGroup Tag.F4 k) := by
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro y
    obtain ⟨y', rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, hx]
  rw [center_adjointGroup_eq_bot_field, Subgroup.mem_bot] at h1
  rw [Subgroup.mem_bot]
  exact e.injective (h1.trans (map_one e).symm)

theorem even_E6_second_graph_transfer_from_F4 {f : ℕ} (hf : 1 ≤ f) (k : Type) [Field k]
    (hk : Nat.card k = 2 ^ f) (ξ : MulAut (adjointGroup TwistTag.E6.tag k))
    (hξ : ∀ g, (ξ g : ModGL TwistTag.E6.tag k) = pinnedX TwistTag.E6.tag k e6HighestRoot 1 *
      (diagramMap TwistTag.E6 k * g * (diagramMap TwistTag.E6 k)⁻¹) *
        (pinnedX TwistTag.E6.tag k e6HighestRoot 1)⁻¹)
    (hF4 : ∀ τJ : MulAut ((twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map
        (baseChangeGL (RingHom.id k))),
      (∀ x, (τJ x : ModGL TwistTag.E6.tag k) = pinnedX TwistTag.E6.tag k e6HighestRoot 1 * x *
        (pinnedX TwistTag.E6.tag k e6HighestRoot 1)⁻¹) →
      ∀ L, OuterAutomorphisms.inner _ ≤ L → CFSG.oddCore ↥(L ⊓ Subgroup.centralizer {τJ}) = ⊥)
    (H : Subgroup (MulAut (adjointGroup TwistTag.E6.tag k)))
    (hIH : OuterAutomorphisms.inner (adjointGroup TwistTag.E6.tag k) ≤ H) :
    CFSG.oddCore ↥(H ⊓ Subgroup.centralizer {ξ}) = ⊥ ∧
      ∀ α ∈ H, (∃ φ : MulAut (adjointGroup TwistTag.E6.tag k), φ * α * φ⁻¹ = ξ) →
        CFSG.oddCore ↥(H ⊓ Subgroup.centralizer {α}) = ⊥ := by
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have : Finite (adjointGroup TwistTag.E6.tag k) := generated_group_finite _ k
  have : Fintype k := Fintype.ofFinite k
  have hk2 : ringChar k = 2 := FiniteField.even_card_iff_char_two.2 (by
    rw [← Nat.card_eq_fintype_card, hk, ← Nat.sub_add_cancel hf, pow_succ, Nat.mul_mod_left])
  have h2 : (2 : k) = 0 := two_eq_zero_of_ringChar hk2
  have hZJ := center_eq_bot_of_mulEquiv_adjointGroup k (graphFixedImageF4Equiv (RingHom.id k) h2)
  exact oddCore_inf_centralizer_xi_conj_eq_bot (secondGraphFullCentralizer_adjointGroup hf k hk)
    diagramMap_E6_mul_self hZJ ξ hξ hF4 H hIH

theorem even_twisted_E6_second_graph_transfer_from_F4 {f : ℕ} (hf : 1 ≤ f) (k K : Type)
    [Field k] [Field K] [Algebra k K] (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    (σ : K →+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f) (ξ : MulAut (graphFixedRootGroup TwistTag.E6 K σ))
    (hξ : ∀ g, (ξ g : ModGL TwistTag.E6.tag K) = pinnedX TwistTag.E6.tag K e6HighestRoot 1 *
      (diagramMap TwistTag.E6 K * g * (diagramMap TwistTag.E6 K)⁻¹) *
        (pinnedX TwistTag.E6.tag K e6HighestRoot 1)⁻¹)
    (hF4 : ∀ τJ : MulAut ((twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map
        (baseChangeGL (algebraMap k K))),
      (∀ x, (τJ x : ModGL TwistTag.E6.tag K) = pinnedX TwistTag.E6.tag K e6HighestRoot 1 * x *
        (pinnedX TwistTag.E6.tag K e6HighestRoot 1)⁻¹) →
      ∀ L, OuterAutomorphisms.inner _ ≤ L → CFSG.oddCore ↥(L ⊓ Subgroup.centralizer {τJ}) = ⊥)
    (H : Subgroup (MulAut (graphFixedRootGroup TwistTag.E6 K σ)))
    (hIH : OuterAutomorphisms.inner (graphFixedRootGroup TwistTag.E6 K σ) ≤ H) :
    CFSG.oddCore ↥(H ⊓ Subgroup.centralizer {ξ}) = ⊥ ∧
      ∀ α ∈ H, (∃ φ : MulAut (graphFixedRootGroup TwistTag.E6 K σ), φ * α * φ⁻¹ = ξ) →
        CFSG.oddCore ↥(H ⊓ Subgroup.centralizer {α}) = ⊥ := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have : Fintype k := Fintype.ofFinite k
  have hk2 : ringChar k = 2 := FiniteField.even_card_iff_char_two.2 (by
    rw [← Nat.card_eq_fintype_card, hk, ← Nat.sub_add_cancel hf, pow_succ, Nat.mul_mod_left])
  have h2 : (2 : k) = 0 := two_eq_zero_of_ringChar hk2
  have hZJ := center_eq_bot_of_mulEquiv_adjointGroup k
    (graphFixedImageF4Equiv (algebraMap k K) h2)
  exact oddCore_inf_centralizer_xi_conj_eq_bot
    (secondGraphFullCentralizer_graphFixedRootGroup hf k K hk hK σ hσ) diagramMap_E6_mul_self hZJ
    ξ hξ hF4 H hIH

theorem even_E6_second_graph_centralizer_transfer_from_F4 (f : ℕ) (hf : 1 ≤ f) (k K : Type)
    [Field k] [Field K] [Algebra k K] (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    (σ : K →+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    (∀ ξ : MulAut (adjointGroup TwistTag.E6.tag k),
      (∀ g, (ξ g : ModGL TwistTag.E6.tag k) = pinnedX TwistTag.E6.tag k e6HighestRoot 1 *
        (diagramMap TwistTag.E6 k * g * (diagramMap TwistTag.E6 k)⁻¹) *
          (pinnedX TwistTag.E6.tag k e6HighestRoot 1)⁻¹) →
      (∀ τJ : MulAut ((twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map
          (baseChangeGL (RingHom.id k))),
        (∀ x, (τJ x : ModGL TwistTag.E6.tag k) = pinnedX TwistTag.E6.tag k e6HighestRoot 1 * x *
          (pinnedX TwistTag.E6.tag k e6HighestRoot 1)⁻¹) →
        ∀ L, OuterAutomorphisms.inner _ ≤ L → CFSG.oddCore ↥(L ⊓ Subgroup.centralizer {τJ}) = ⊥) →
      ∀ H : Subgroup (MulAut (adjointGroup TwistTag.E6.tag k)),
        OuterAutomorphisms.inner (adjointGroup TwistTag.E6.tag k) ≤ H →
        CFSG.oddCore ↥(H ⊓ Subgroup.centralizer {ξ}) = ⊥ ∧
          ∀ α ∈ H, (∃ φ : MulAut (adjointGroup TwistTag.E6.tag k), φ * α * φ⁻¹ = ξ) →
            CFSG.oddCore ↥(H ⊓ Subgroup.centralizer {α}) = ⊥) ∧
    (∀ ξ : MulAut (graphFixedRootGroup TwistTag.E6 K σ),
      (∀ g, (ξ g : ModGL TwistTag.E6.tag K) = pinnedX TwistTag.E6.tag K e6HighestRoot 1 *
        (diagramMap TwistTag.E6 K * g * (diagramMap TwistTag.E6 K)⁻¹) *
          (pinnedX TwistTag.E6.tag K e6HighestRoot 1)⁻¹) →
      (∀ τJ : MulAut ((twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map
          (baseChangeGL (algebraMap k K))),
        (∀ x, (τJ x : ModGL TwistTag.E6.tag K) = pinnedX TwistTag.E6.tag K e6HighestRoot 1 * x *
          (pinnedX TwistTag.E6.tag K e6HighestRoot 1)⁻¹) →
        ∀ L, OuterAutomorphisms.inner _ ≤ L → CFSG.oddCore ↥(L ⊓ Subgroup.centralizer {τJ}) = ⊥) →
      ∀ H : Subgroup (MulAut (graphFixedRootGroup TwistTag.E6 K σ)),
        OuterAutomorphisms.inner (graphFixedRootGroup TwistTag.E6 K σ) ≤ H →
        CFSG.oddCore ↥(H ⊓ Subgroup.centralizer {ξ}) = ⊥ ∧
          ∀ α ∈ H, (∃ φ : MulAut (graphFixedRootGroup TwistTag.E6 K σ), φ * α * φ⁻¹ = ξ) →
            CFSG.oddCore ↥(H ⊓ Subgroup.centralizer {α}) = ⊥) :=
  ⟨fun ξ hξ hF4 H hIH => even_E6_second_graph_transfer_from_F4 hf k hk ξ hξ hF4 H hIH,
    fun ξ hξ hF4 H hIH =>
      even_twisted_E6_second_graph_transfer_from_F4 hf k K hk hK σ hσ ξ hξ hF4 H hIH⟩

end CFSG.RankThree.Chevalley
