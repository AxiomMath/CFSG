module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotNeighbourStandardBasic
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotCentralizerT
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotAutD
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotAutDY

public section

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6GraphLevi CFSG.LieType.Chevalley.C2E6Std

section General

variable {M : Type*} [Group M]

theorem subgroupOf_le_centralizer_subgroupOf {Y D C : Subgroup M}
    (h : Y ≤ centralizer (D : Set M)) : Y.subgroupOf C ≤ centralizer (D.subgroupOf C : Set C) := by
  intro y hy
  rw [mem_centralizer_iff]
  intro d hd
  exact Subtype.ext (mem_centralizer_iff.1 (h (mem_subgroupOf.1 hy)) d (mem_subgroupOf.1 hd))

theorem isSimpleGroup_map_conj {D : Subgroup M} [IsSimpleGroup D] (n : M) :
    IsSimpleGroup (D.map (MulAut.conj n).toMonoidHom) :=
  (D.equivMapOfInjective (MulAut.conj n).toMonoidHom (MulAut.conj n).injective).symm.isSimpleGroup

theorem isPerfect_map_conj {D : Subgroup M} [Group.IsPerfect D] (n : M) :
    Group.IsPerfect (D.map (MulAut.conj n).toMonoidHom) :=
  Group.IsPerfect.ofSurjective (f := (D.equivMapOfInjective (MulAut.conj n).toMonoidHom
    (MulAut.conj n).injective).toMonoidHom) (MulEquiv.surjective _)

end General

section Data

variable {f : ℕ} {k K : Type} [Field k] [Field K] [Algebra k K]

theorem centralizer_thetaTorus_subgroupOf (hf2 : 2 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    centralizer ((thetaTorus (algebraMap k K)).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) :
        Set (graphFixedRootGroup TwistTag.E6 K σ)) =
      (thetaTorus (algebraMap k K)).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) ⊔
        (su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) := by
  have hf : 1 ≤ f := by omega
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  exact centralizer_subgroupOf_eq_sup (thetaTorus_le_C0 hf hk hK hσ)
    (thetaTorus_le_C0 hf hk hK hσ) (su6Levi_le_graphFixedRootGroup σ)
    (centralizer_thetaTorus_inf_eq hf2 hk hK hσ).1

theorem isQuasisimple_su6Levi_subgroupOf (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    CFSG.IsQuasisimple ((su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)) := by
  have := isSimpleGroup_su6Levi hf hk hK hσ
  have := isPerfect_su6Levi hf hk hK hσ
  exact isQuasisimple_subgroupOf (su6Levi_le_graphFixedRootGroup σ)

theorem isPerfect_omegaMinusLevi (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) : Group.IsPerfect (omegaMinusLevi σ) := by
  have := finite_of_card hK
  have := charP_two_of_card hf hK
  obtain ⟨σE, rfl⟩ := exists_ringEquiv_toRingHom_eq σ
  have hσσ : ∀ c, σE (σE c) = c := apply_apply_eq hK hσ
  obtain ⟨ω, hω⟩ := exists_apply_ne hf hK hσ
  have hP : Group.IsPerfect ↥(subsystemGroup TwistTag.E6.tag K setD ⊓
      twistedFixedGroup TwistTag.E6 K (σE : K →+* K)) := isPerfect_d4Fixed hσσ (ω := ω) hω
  exact Group.IsPerfect.ofSurjective (f := (MulEquiv.subgroupCongr
    (omegaMinusLevi_eq hσσ (ω := ω) hω).symm).toMonoidHom) (MulEquiv.surjective _)

theorem isQuasisimple_omegaMinusLevi_subgroupOf (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    CFSG.IsQuasisimple ((omegaMinusLevi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)) := by
  have := isSimpleGroup_omegaMinusLevi hf hK hσ
  have := isPerfect_omegaMinusLevi hf hK hσ
  exact isQuasisimple_subgroupOf (omegaMinusLevi_le_graphFixedRootGroup σ)

omit
  [Algebra k K] in
theorem d4CentralTorus_le_centralizer_self :
    d4CentralTorus K ≤ centralizer (d4CentralTorus K : Set (ModGL Tag.E6 K)) := by
  rintro _ ⟨p, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨p', rfl⟩
  rw [← map_mul, ← map_mul, mul_comm]

omit
  [Algebra k K] in
theorem w1Complement_le_centralizer_self (σ : K →+* K) :
    w1Complement σ ≤ centralizer (w1Complement σ : Set (ModGL TwistTag.E6.tag K)) := fun _ hy =>
  centralizer_le (fun _ hz => (inf_le_left : w1Complement σ ≤ d4CentralTorus K) hz)
    (d4CentralTorus_le_centralizer_self ((inf_le_left : w1Complement σ ≤ d4CentralTorus K) hy))

theorem centralizer_shortRootTorus_subgroupOf (hf2 : 2 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    centralizer ((shortRootTorus (algebraMap k K)).subgroupOf
        (graphFixedRootGroup TwistTag.E6 K σ) : Set (graphFixedRootGroup TwistTag.E6 K σ)) =
      (w1Complement σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) ⊔
        (omegaMinusLevi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) := by
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have hσι : ∀ c : k, σ (algebraMap k K c) = algebraMap k K c :=
    E6GraphLevi.fixed_algebraMap (sigma_eq_pow_card hk hσ)
  exact centralizer_subgroupOf_eq_sup (shortRootTorus_le_C0 hσι) (w1Complement_le_C0 σ)
    (omegaMinusLevi_le_graphFixedRootGroup σ) (centralizer_w1Torus_inf_eq hf2 hk hK hσ).1

theorem centralizer_thetaTorus_conj_subgroupOf (hf2 : 2 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (n : graphFixedRootGroup TwistTag.E6 K σ) :
    centralizer (((thetaTorus (algebraMap k K)).map
          (MulAut.conj (n : ModGL TwistTag.E6.tag K)).toMonoidHom).subgroupOf
        (graphFixedRootGroup TwistTag.E6 K σ) : Set (graphFixedRootGroup TwistTag.E6 K σ)) =
      ((thetaTorus (algebraMap k K)).map
          (MulAut.conj (n : ModGL TwistTag.E6.tag K)).toMonoidHom).subgroupOf
        (graphFixedRootGroup TwistTag.E6 K σ) ⊔
        ((su6Levi σ).map (MulAut.conj (n : ModGL TwistTag.E6.tag K)).toMonoidHom).subgroupOf
          (graphFixedRootGroup TwistTag.E6 K σ) := by
  have hf : 1 ≤ f := by omega
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  refine centralizer_subgroupOf_eq_sup (map_conj_le (thetaTorus_le_C0 hf hk hK hσ) n.2)
    (map_conj_le (thetaTorus_le_C0 hf hk hK hσ) n.2)
    (map_conj_le (su6Levi_le_graphFixedRootGroup σ) n.2) ?_
  rw [centralizer_map_conj_inf n.2, (centralizer_thetaTorus_inf_eq hf2 hk hK hσ).1,
    Subgroup.map_sup]

theorem isQuasisimple_su6Levi_conj_subgroupOf (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (n : graphFixedRootGroup TwistTag.E6 K σ) :
    CFSG.IsQuasisimple (((su6Levi σ).map
      (MulAut.conj (n : ModGL TwistTag.E6.tag K)).toMonoidHom).subgroupOf
        (graphFixedRootGroup TwistTag.E6 K σ)) := by
  have := isSimpleGroup_su6Levi hf hk hK hσ
  have := isPerfect_su6Levi hf hk hK hσ
  have := isSimpleGroup_map_conj (D := su6Levi σ) (n : ModGL TwistTag.E6.tag K)
  have := isPerfect_map_conj (D := su6Levi σ) (n : ModGL TwistTag.E6.tag K)
  exact isQuasisimple_subgroupOf (map_conj_le (su6Levi_le_graphFixedRootGroup σ) n.2)

end Data

section Layer

variable {G : Type*} [Group G] {L : Subgroup G} {f : ℕ} {k K : Type} [Field k] [Field K]
  [Algebra k K]

theorem neighbour_layer_2E6_X (hf2 : 2 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {X : Subgroup G}
    (hX : X = (((thetaTorus (algebraMap k K)).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G} (hDe : D = (((su6Levi σ).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype) :
    D = inSubgroup layer (L ⊓ centralizer (X : Set G)) ∧ CFSG.IsQuasisimple D := by
  have hf : 1 ≤ f := by omega
  subst hX hDe
  exact ⟨(F4Pilot.inSubgroup_layer_inf_centralizer_map_symm e
      (centralizer_thetaTorus_subgroupOf hf2 hk hK hσ)
      (subgroupOf_le_centralizer_subgroupOf (centralizer_thetaTorus_inf_eq hf2 hk hK hσ).2.2)
      (subgroupOf_le_centralizer_subgroupOf (thetaTorus_le_centralizer_self _))
      (isQuasisimple_su6Levi_subgroupOf hf hk hK hσ)).symm,
    isQuasisimple_map_symm e (isQuasisimple_su6Levi_subgroupOf hf hk hK hσ)⟩

theorem neighbour_layer_2E6_conj (hf2 : 2 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) (w : graphFixedRootGroup TwistTag.E6 K σ)
    {X : Subgroup G}
    (hX : X = ((((thetaTorus (algebraMap k K)).map
      (MulAut.conj (w : ModGL TwistTag.E6.tag K)).toMonoidHom).subgroupOf
        (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G}
    (hDe : D = ((((su6Levi σ).map (MulAut.conj (w : ModGL TwistTag.E6.tag K)).toMonoidHom).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype) :
    D = inSubgroup layer (L ⊓ centralizer (X : Set G)) ∧ CFSG.IsQuasisimple D := by
  have hf : 1 ≤ f := by omega
  subst hX hDe
  exact ⟨(F4Pilot.inSubgroup_layer_inf_centralizer_map_symm e
      (centralizer_thetaTorus_conj_subgroupOf hf2 hk hK hσ w)
      (subgroupOf_le_centralizer_subgroupOf (map_conj_le_centralizer_map_conj
        (centralizer_thetaTorus_inf_eq hf2 hk hK hσ).2.2 _))
      (subgroupOf_le_centralizer_subgroupOf (map_conj_le_centralizer_map_conj
        (thetaTorus_le_centralizer_self _) _))
      (isQuasisimple_su6Levi_conj_subgroupOf hf hk hK hσ w)).symm,
    isQuasisimple_map_symm e (isQuasisimple_su6Levi_conj_subgroupOf hf hk hK hσ w)⟩

theorem neighbour_layer_2E6_Y (hf2 : 2 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {X : Subgroup G}
    (hX : X = (((shortRootTorus (algebraMap k K)).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G} (hDe : D = (((omegaMinusLevi σ).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype) :
    D = inSubgroup layer (L ⊓ centralizer (X : Set G)) ∧ CFSG.IsQuasisimple D := by
  have hf : 1 ≤ f := by omega
  subst hX hDe
  exact ⟨(F4Pilot.inSubgroup_layer_inf_centralizer_map_symm e
      (centralizer_shortRootTorus_subgroupOf hf2 hk hK hσ)
      (subgroupOf_le_centralizer_subgroupOf (centralizer_w1Torus_inf_eq hf2 hk hK hσ (k := k)).2.1)
      (subgroupOf_le_centralizer_subgroupOf (w1Complement_le_centralizer_self σ))
      (isQuasisimple_omegaMinusLevi_subgroupOf hf hK hσ)).symm,
    isQuasisimple_map_symm e (isQuasisimple_omegaMinusLevi_subgroupOf hf hK hσ)⟩

theorem card_map_symm_subgroupOf {M : Type*} [Group M] {C A : Subgroup M} (hAC : A ≤ C)
    (e : L ≃* C) :
    Nat.card (((A.subgroupOf C).map e.symm.toMonoidHom).map L.subtype) = Nat.card A := by
  rw [card_map_of_injective L.subtype_injective, card_map_of_injective e.symm.injective,
    Nat.card_congr (subgroupOfEquivOfLe hAC).toEquiv]

end Layer

section Setting


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {k K : Type} [Field k]
  [Field K] [Algebra k K]

theorem neighbour_standard_2E6_X (hset : SeitzSetting G L) (hf2 : 2 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {X : Subgroup G}
    (hX : X = (((thetaTorus (algebraMap k K)).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = (((su6Levi σ).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype) :
    CFSG.Open.IsComponentOf
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))))
        (centralizer ({QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩} :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))) ∧
      (∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
        IsPGroup 2 U →
        U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
        Nat.card U ≤ 2) ∧
      standardComponentIsStandard ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) := by
  have hf : 1 ≤ f := by omega
  exact neighbour_standard_of_centralizer_eq_sup_gen hset.standardSetting.standard htC ht
    (inf_centralizer_eq_zpowers_twistedE6 hset hf hK hσ e htC ht) e
    (centralizer_thetaTorus_subgroupOf hf2 hk hK hσ)
    (subgroupOf_le_centralizer_subgroupOf (centralizer_thetaTorus_inf_eq hf2 hk hK hσ).2.2)
    (subgroupOf_le_centralizer_subgroupOf (thetaTorus_le_centralizer_self _))
    (isQuasisimple_su6Levi_subgroupOf hf hk hK hσ)
    (fun β hβX hβD n hβn => eq_one_of_fix_su6Levi hf2 hk hK hσ β
      (fun x hx => hβX x (mem_subgroupOf.2 hx)) (fun x hx => hβD x (mem_subgroupOf.2 hx)) n hβn)
    hX htX hDe

theorem neighbour_standard_2E6_conj (hset : SeitzSetting G L) (hf2 : 2 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ)
    (w : graphFixedRootGroup TwistTag.E6 K σ) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {X : Subgroup G}
    (hX : X = ((((thetaTorus (algebraMap k K)).map
      (MulAut.conj (w : ModGL TwistTag.E6.tag K)).toMonoidHom).subgroupOf
        (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((((su6Levi σ).map (MulAut.conj (w : ModGL TwistTag.E6.tag K)).toMonoidHom).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype) :
    CFSG.Open.IsComponentOf
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))))
        (centralizer ({QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩} :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))) ∧
      (∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
        IsPGroup 2 U →
        U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
        Nat.card U ≤ 2) ∧
      standardComponentIsStandard ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) := by
  have hf : 1 ≤ f := by omega
  exact neighbour_standard_of_centralizer_eq_sup_gen hset.standardSetting.standard htC ht
    (inf_centralizer_eq_zpowers_twistedE6 hset hf hK hσ e htC ht) e
    (centralizer_thetaTorus_conj_subgroupOf hf2 hk hK hσ w)
    (subgroupOf_le_centralizer_subgroupOf (map_conj_le_centralizer_map_conj
      (centralizer_thetaTorus_inf_eq hf2 hk hK hσ).2.2 _))
    (subgroupOf_le_centralizer_subgroupOf (map_conj_le_centralizer_map_conj
      (thetaTorus_le_centralizer_self _) _))
    (isQuasisimple_su6Levi_conj_subgroupOf hf hk hK hσ w)
    (fun β hβX hβD n hβn => eq_one_of_fix_su6Levi_conj hf2 hk hK hσ w β
      (fun x hx => hβX x (mem_subgroupOf.2 hx)) (fun x hx => hβD x (mem_subgroupOf.2 hx)) n hβn)
    hX htX hDe

theorem neighbour_standard_2E6_X' (hset : SeitzSetting G L) (hf2 : 2 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {X : Subgroup G}
    (hX : X = ((((thetaTorus (algebraMap k K)).map
      (MulAut.conj (twistedE6RelWeyl K relWordXPrime)).toMonoidHom).subgroupOf
        (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((((su6Levi σ).map
      (MulAut.conj (twistedE6RelWeyl K relWordXPrime)).toMonoidHom).subgroupOf
        (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype) :
    CFSG.Open.IsComponentOf
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))))
        (centralizer ({QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩} :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))) ∧
      (∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
        IsPGroup 2 U →
        U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
        Nat.card U ≤ 2) ∧
      standardComponentIsStandard ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) :=
  neighbour_standard_2E6_conj hset hf2 hk hK hσ e
    ⟨twistedE6RelWeyl K relWordXPrime, twistedE6RelWeyl_mem σ relWordXPrime⟩ htC ht hX htX hDe

theorem neighbour_standard_2E6_Y (hset : SeitzSetting G L) (hf2 : 2 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {X : Subgroup G}
    (hX : X = (((shortRootTorus (algebraMap k K)).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = (((omegaMinusLevi σ).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype) :
    CFSG.Open.IsComponentOf
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))))
        (centralizer ({QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩} :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))) ∧
      (∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
        IsPGroup 2 U →
        U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
        Nat.card U ≤ 2) ∧
      standardComponentIsStandard ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) := by
  have hf : 1 ≤ f := by omega
  exact neighbour_standard_of_centralizer_eq_sup_gen hset.standardSetting.standard htC ht
    (inf_centralizer_eq_zpowers_twistedE6 hset hf hK hσ e htC ht) e
    (centralizer_shortRootTorus_subgroupOf hf2 hk hK hσ)
    (subgroupOf_le_centralizer_subgroupOf (centralizer_w1Torus_inf_eq hf2 hk hK hσ).2.1)
    (subgroupOf_le_centralizer_subgroupOf (w1Complement_le_centralizer_self σ))
    (isQuasisimple_omegaMinusLevi_subgroupOf hf hK hσ)
    (fun β hβX hβD n hβn => eq_one_of_fix_omegaMinusLevi hf2 hk hK hσ β
      (fun x hx => hβX x (mem_subgroupOf.2 hx)) (fun x hx => hβD x (mem_subgroupOf.2 hx)) n hβn)
    hX htX hDe

theorem exists_neighbour_standard_2E6_X (hset : SeitzSetting G L) (hf2 : 2 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) :
    ∃ X D : Subgroup G,
      X = (((thetaTorus (algebraMap k K)).subgroupOf
        (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype ∧
      D = (((su6Levi σ).subgroupOf
        (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype ∧
      X ≤ L ∧ D = inSubgroup layer (L ⊓ centralizer (X : Set G)) ∧
      D ≤ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) ∧ CFSG.Open.IsQuasisimple D ∧
      LieModel D .PSU 6 2 f ∧
      ∃ htX : t ∈ centralizer (X : Set G),
        CFSG.Open.IsComponentOf
            ((D.subgroupOf (centralizer (X : Set G))).map
              (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))))
            (centralizer ({QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩} :
              Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))) ∧
          (∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
            IsPGroup 2 U →
            U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
                (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
              Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
            Nat.card U ≤ 2) ∧
          standardComponentIsStandard ((D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) := by
  have hf : 1 ≤ f := by omega
  set X : Subgroup G := (((thetaTorus (algebraMap k K)).subgroupOf
    (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype with hX
  set D : Subgroup G := (((su6Levi σ).subgroupOf
    (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype with hDe
  obtain ⟨hD, hDq⟩ := neighbour_layer_2E6_X hf2 hk hK hσ e hX hDe
  have hXL : X ≤ L := map_subtype_le _
  have hDL : D ≤ L := map_subtype_le _
  have htX : t ∈ centralizer (X : Set G) := centralizer_le hXL htC
  have hDX : D ≤ centralizer (X : Set G) := le_centralizer_iff.1
    (F4Pilot.map_le_centralizer_map _ (F4Pilot.map_le_centralizer_map _
      (subgroupOf_le_centralizer_subgroupOf (centralizer_thetaTorus_inf_eq hf2 hk hK hσ).2.2)))
  have hDt : D ≤ centralizer ({t} : Set G) := hDL.trans (le_centralizer_of_mem_centralizer htC)
  have hlie : LieModel D .PSU 6 2 f := lieModel_of_mulEquiv
    ((subgroupOfEquivOfLe (su6Levi_le_graphFixedRootGroup σ)).symm.trans
      ((((su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)).equivMapOfInjective
        e.symm.toMonoidHom e.symm.injective).trans
        ((((su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)).map
          e.symm.toMonoidHom).equivMapOfInjective L.subtype L.subtype_injective)))
    (lieModel_su6Levi hf hk hK hσ)
  exact ⟨X, D, rfl, rfl, hXL, hD, le_inf hDX hDt, ⟨hDq.1.commutator_eq_top, hDq.2.1⟩, hlie, htX,
    neighbour_standard_2E6_X hset hf2 hk hK hσ e htC ht rfl htX rfl⟩

theorem exists_neighbour_standard_2E6_Y (hset : SeitzSetting G L) (hf2 : 2 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) :
    ∃ X D : Subgroup G,
      X = (((shortRootTorus (algebraMap k K)).subgroupOf
        (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype ∧
      D = (((omegaMinusLevi σ).subgroupOf
        (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype ∧
      X ≤ L ∧ D = inSubgroup layer (L ⊓ centralizer (X : Set G)) ∧
      D ≤ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) ∧ CFSG.Open.IsQuasisimple D ∧
      LieModel D .POmegaMinus 4 2 f ∧
      ∃ htX : t ∈ centralizer (X : Set G),
        CFSG.Open.IsComponentOf
            ((D.subgroupOf (centralizer (X : Set G))).map
              (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))))
            (centralizer ({QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩} :
              Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))) ∧
          (∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
            IsPGroup 2 U →
            U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
                (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
              Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
            Nat.card U ≤ 2) ∧
          standardComponentIsStandard ((D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) := by
  have hf : 1 ≤ f := by omega
  set X : Subgroup G := (((shortRootTorus (algebraMap k K)).subgroupOf
    (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype with hX
  set D : Subgroup G := (((omegaMinusLevi σ).subgroupOf
    (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype with hDe
  obtain ⟨hD, hDq⟩ := neighbour_layer_2E6_Y hf2 hk hK hσ e hX hDe
  have hXL : X ≤ L := map_subtype_le _
  have hDL : D ≤ L := map_subtype_le _
  have htX : t ∈ centralizer (X : Set G) := centralizer_le hXL htC
  have hDX : D ≤ centralizer (X : Set G) :=
    F4Pilot.map_le_centralizer_map _ (F4Pilot.map_le_centralizer_map _ (by
      rw [centralizer_shortRootTorus_subgroupOf hf2 hk hK hσ]
      exact le_sup_right))
  have hDt : D ≤ centralizer ({t} : Set G) := hDL.trans (le_centralizer_of_mem_centralizer htC)
  have hlie : LieModel D .POmegaMinus 4 2 f := lieModel_of_mulEquiv
    ((subgroupOfEquivOfLe (omegaMinusLevi_le_graphFixedRootGroup σ)).symm.trans
      ((((omegaMinusLevi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)).equivMapOfInjective
        e.symm.toMonoidHom e.symm.injective).trans
        ((((omegaMinusLevi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)).map
          e.symm.toMonoidHom).equivMapOfInjective L.subtype L.subtype_injective)))
    (lieModel_omegaMinusLevi hf hK hσ)
  exact ⟨X, D, rfl, rfl, hXL, hD, le_inf hDX hDt, ⟨hDq.1.commutator_eq_top, hDq.2.1⟩, hlie, htX,
    neighbour_standard_2E6_Y hset hf2 hk hK hσ e htC ht rfl htX rfl⟩

end Setting

end CFSG.SeitzReduction.TwistedE6Pilot
