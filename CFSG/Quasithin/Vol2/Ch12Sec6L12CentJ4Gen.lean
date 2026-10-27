module

public import CFSG.Quasithin.Vol2.Ch12Sec6L12TwoLeavesCent
public import CFSG.Quasithin.Vol2.Ch12Sec6L12A6Num

public section

namespace CFSG.Quasithin.H13.K1262Two.CentJ4

open CFSG.Open CFSG.Blueprint
open scoped Pointwise

theorem quasithinO2QuotientIso_of_mulEquiv {G G' H : Type*} [Group G] [Group G'] [Group H]
    {L : Subgroup G} {L' : Subgroup G'} (e : ↥L ≃* ↥L') (h : quasithinO2QuotientIso L H) :
    quasithinO2QuotientIso L' H := by
  obtain ⟨φ, hs, hk⟩ := h
  refine ⟨φ.comp e.symm.toMonoidHom, hs.comp e.symm.surjective, ?_⟩
  rw [← MonoidHom.comap_ker, hk, Subgroup.comap_equiv_eq_map_symm']
  exact CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 e

theorem centralizer_map_mulEquiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') (x : G) :
    (Subgroup.centralizer ({x} : Set G)).map e.toMonoidHom =
      Subgroup.centralizer ({e x} : Set G') := by
  ext y
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hw
    rw [Subgroup.mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, ← map_mul, hw]
  · intro hy
    refine ⟨e.symm y, ?_, by simp⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hy
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    apply e.injective
    simp only [map_mul, MulEquiv.apply_symm_apply, hy]

theorem card_centralizer_conj {G : Type*} [Group G] (c x : G) :
    Nat.card (Subgroup.centralizer ({c * x * c⁻¹} : Set G)) =
      Nat.card (Subgroup.centralizer ({x} : Set G)) := by
  rw [← MulAut.conj_apply, ← centralizer_map_mulEquiv,
    Subgroup.card_map_of_injective (MulAut.conj c).injective]

@[expose] def J1Prop (G : Type*) [Group G] (z : G) : Prop :=
  ∀ x : G, orderOf x = 2 → 2 ^ 20 ∣ Nat.card (Subgroup.centralizer ({x} : Set G)) → IsConj x z

theorem conj_of_mulEquiv {X G : Type} [Group X] [Group G] (e : X ≃* G) {z : G}
    (h : J1Prop G z) : J1Prop X (e.symm z) := by
  intro x hx hc
  have h1 := h (e x) (by rw [MulEquiv.orderOf_eq]; exact hx) (by
    rw [← centralizer_map_mulEquiv, Subgroup.card_map_of_injective e.injective]
    exact hc)
  obtain ⟨c, hc'⟩ := isConj_iff.mp h1
  refine isConj_iff.mpr ⟨e.symm c, e.injective ?_⟩
  simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, hc']

theorem noA6_of_mulEquiv {X G : Type} [Group X] [Group G] (e : X ≃* G) {z : G}
    (h : ∀ Y : Subgroup G, Y ≤ Subgroup.centralizer ({z} : Set G) →
      quasithinO2QuotientIso Y ↥(alternatingGroup (Fin 6)) → False) :
    ∀ Y : Subgroup X, Y ≤ Subgroup.centralizer ({e.symm z} : Set X) →
      quasithinO2QuotientIso Y ↥(alternatingGroup (Fin 6)) → False := by
  intro Y hYC hY
  refine h (Y.map e.toMonoidHom) ?_
    (quasithinO2QuotientIso_of_mulEquiv (Y.equivMapOfInjective e.toMonoidHom e.injective) hY)
  rw [← MulEquiv.apply_symm_apply e z, ← centralizer_map_mulEquiv]
  exact Subgroup.map_mono hYC

theorem isConj_of_conj_eq {G : Type*} [Group G] {x z w g g' : G} (hg : g * x * g⁻¹ = w)
    (hg' : g' * z * g'⁻¹ = w) : IsConj x z := by
  refine isConj_iff.mpr ⟨g'⁻¹ * g, ?_⟩
  calc g'⁻¹ * g * x * (g'⁻¹ * g)⁻¹ = g'⁻¹ * (g * x * g⁻¹) * g' := by group
    _ = g'⁻¹ * (g' * z * g'⁻¹) * g' := by rw [hg, hg']
    _ = z := by group

theorem mul_ne_of_commutator_ne_one {G : Type*} [Group G] {a b c : G}
    (hc : c = a⁻¹ * b⁻¹ * a * b) (h1 : c ≠ 1) : a * b ≠ b * a := by
  intro h
  apply h1
  rw [hc, mul_assoc, h]
  group

theorem mk_mul_ne {G : Type*} [Group G] {H : Subgroup G} {a b : G} (ha : a ∈ H) (hb : b ∈ H)
    (h : a * b ≠ b * a) : (⟨a, ha⟩ : ↥H) * ⟨b, hb⟩ ≠ ⟨b, hb⟩ * ⟨a, ha⟩ := fun h' =>
  h (congrArg Subtype.val h')

theorem card_lt_of_conj_of_noA6 {X : Type} [Group X] [Finite X] (z : X) (hJ1 : J1Prop X z)
    (hL : ∀ Y : Subgroup X, Y ≤ Subgroup.centralizer ({z} : Set X) →
      quasithinO2QuotientIso Y ↥(alternatingGroup (Fin 6)) → False)
    {Y P : Subgroup X} {u : X} (hY : A6TypeCent Y u) (hP : IsPGroup 2 ↥P)
    (hPN : P ≤ Subgroup.normalizer (Y : Set X)) : Nat.card ↥P < 2 ^ 20 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hiso, hu, hu2, hc⟩ := hY
  have hu1 : u ≠ 1 := fun h => by rw [h, orderOf_one] at hu2; exact absurd hu2 (by norm_num)
  have husq : u * u = 1 := by rw [← sq, ← hu2, pow_orderOf_eq_one]
  obtain ⟨v, hvY, hv1, hv2, hvc, hvP⟩ :=
    exists_central_involution_fixed hu hu1 husq hc hP hPN
  by_contra hlt
  push Not at hlt
  have hvo : orderOf v = 2 := orderOf_eq_prime (by rw [sq]; exact hv2) hv1
  have hPC : P ≤ Subgroup.centralizer ({v} : Set X) := fun p hp =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hvP p hp)
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have h20 : 2 ^ 20 ∣ Nat.card ↥P := by
    rw [hk] at hlt ⊢
    exact Nat.pow_dvd_pow 2 ((Nat.pow_le_pow_iff_right (by norm_num)).mp hlt)
  obtain ⟨c, hcz⟩ := isConj_iff.mp
    (hJ1 v hvo (h20.trans (Subgroup.card_dvd_of_le hPC)))
  refine hL (Y.map (MulAut.conj c).toMonoidHom) ?_
    (quasithinO2QuotientIso_of_mulEquiv
      (Y.equivMapOfInjective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective) hiso)
  rintro _ ⟨y, hy, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff, ← hcz]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have := hvc y hy
  calc c * y * c⁻¹ * (c * v * c⁻¹) = c * (y * v) * c⁻¹ := by group
    _ = c * (v * y) * c⁻¹ := by rw [this]
    _ = c * v * c⁻¹ * (c * y * c⁻¹) := by group

theorem card_lt_of_mulEquiv {X G : Type} [Group X] [Finite X] [Group G] (e : X ≃* G) {z : G}
    (hJ1 : J1Prop G z)
    (hL : ∀ Y : Subgroup G, Y ≤ Subgroup.centralizer ({z} : Set G) →
      quasithinO2QuotientIso Y ↥(alternatingGroup (Fin 6)) → False)
    {Y P : Subgroup X} {u : X} (hY : A6TypeCent Y u) (hP : IsPGroup 2 ↥P)
    (hPN : P ≤ Subgroup.normalizer (Y : Set X)) : Nat.card ↥P < 2 ^ 20 :=
  card_lt_of_conj_of_noA6 (e.symm z) (conj_of_mulEquiv e hJ1) (noA6_of_mulEquiv e hL) hY hP hPN

theorem card_sylow_eq {G : Type*} [Group G] [Finite G] {p k : ℕ} [hp : Fact p.Prime]
    (P : Sylow p G) (h1 : p ^ k ∣ Nat.card G) (h2 : ¬ p ^ (k + 1) ∣ Nat.card G) :
    Nat.card P = p ^ k := by
  rw [P.card_eq_multiplicity]
  congr 1
  have hne : Nat.card G ≠ 0 := Nat.card_pos.ne'
  refine le_antisymm ?_ ((hp.out.pow_dvd_iff_le_factorization hne).mp h1)
  by_contra hlt
  push Not at hlt
  exact h2 ((hp.out.pow_dvd_iff_le_factorization hne).mpr hlt)

theorem card_center_eq_three {T : Type*} [Group T] [Finite T] (h27 : Nat.card T = 27)
    {a b : T} (hab : a * b ≠ b * a) : Nat.card (Subgroup.center T) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hT : IsPGroup 3 T := IsPGroup.of_card (n := 3) (by rw [h27]; norm_num)
  have hnt : Nontrivial T := ⟨⟨a, b, fun h => hab (by rw [h])⟩⟩
  have hZnt := hT.center_nontrivial
  obtain ⟨k, hk⟩ := (hT.to_subgroup (Subgroup.center T)).exists_card_eq
  have hdvd : 3 ^ k ∣ 3 ^ 3 := by
    rw [← hk, show (3 : ℕ) ^ 3 = 27 by norm_num, ← h27]
    exact Subgroup.card_subgroup_dvd_card _
  have hk3 : k ≤ 3 := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, Subgroup.card_eq_one] at hk
    exact (Subgroup.nontrivial_iff_ne_bot _).mp hZnt hk
  have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk0
  interval_cases k
  · simpa using hk
  · exfalso
    have hq : Nat.card (T ⧸ Subgroup.center T) = 3 := by
      have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center T)
      rw [h27, hk] at h
      omega
    have : IsCyclic (T ⧸ Subgroup.center T) := isCyclic_of_prime_card hq
    have hc := isMulCommutative_of_isCyclic_quotient_center_self T
    exact hab (hc.is_comm.comm a b)
  · exfalso
    have htop : Subgroup.center T = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (by rw [hk, h27]; norm_num)
    exact hab ((Subgroup.mem_center_iff.mp (htop ▸ Subgroup.mem_top b) a))

theorem center_le_of_normal {T : Type*} [Group T] [Finite T] {p : ℕ} [Fact p.Prime]
    (hT : IsPGroup p T) (hZ : Nat.card (Subgroup.center T) = p) {H : Subgroup T} [H.Normal]
    (hH : H ≠ ⊥) : Subgroup.center T ≤ H := by
  have : Group.IsNilpotent T := hT.isNilpotent
  have h1 := Group.IsNilpotent.inf_center_ne_bot_of_normal hH
  have : Fact (Nat.card ↥(Subgroup.center T)).Prime := by rw [hZ]; infer_instance
  rcases Subgroup.eq_bot_or_eq_top_of_prime_card
      ((H ⊓ Subgroup.center T).subgroupOf (Subgroup.center T)) with hb | ht
  · exfalso
    apply h1
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hx.2⟩ : ↥(Subgroup.center T)) ∈
        (H ⊓ Subgroup.center T).subgroupOf (Subgroup.center T) := by
      rw [Subgroup.mem_subgroupOf]; exact hx
    rw [hb, Subgroup.mem_bot] at hx'
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hx'
  · intro x hx
    have hx' : (⟨x, hx⟩ : ↥(Subgroup.center T)) ∈
        (H ⊓ Subgroup.center T).subgroupOf (Subgroup.center T) := by
      rw [ht]; exact Subgroup.mem_top _
    rw [Subgroup.mem_subgroupOf] at hx'
    exact hx'.1

theorem false_of_a6Type {C : Type} [Group C] [Finite C]
    (h27 : ∀ T : Sylow 3 C, Nat.card T = 27) {T₁ : Subgroup C} (hT₁ : IsPGroup 3 ↥T₁)
    {a b : C} (ha : a ∈ T₁) (hb : b ∈ T₁) (hab : a * b ≠ b * a)
    {N : Subgroup C} [hN : N.Normal] (h5 : ¬ 5 ∣ Nat.card N) {n : C} (hn : n ∈ N)
    (hn3 : orderOf n = 3) {Y : Subgroup C}
    (hY : quasithinO2QuotientIso Y ↥(alternatingGroup (Fin 6))) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hconj : ∀ (T T' : Sylow 3 C), ∃ g : C, ∀ x ∈ (T' : Subgroup C),
      g * x * g⁻¹ ∈ (T : Subgroup C) := by
    intro T T'
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq C T' T
    refine ⟨g, fun x hx => ?_⟩
    have hmem : MulAut.conj g • x ∈ MulAut.conj g • (T' : Subgroup C) :=
      Subgroup.smul_mem_pointwise_smul _ _ _ hx
    rw [← Sylow.coe_subgroup_smul, hg, MulAut.smul_def, MulAut.conj_apply] at hmem
    exact hmem
  obtain ⟨T₀, hT₀⟩ := hT₁.exists_le_sylow
  have hZ : ∀ T : Sylow 3 C, Nat.card (Subgroup.center ↥(T : Subgroup C)) = 3 := by
    intro T
    obtain ⟨g, hg⟩ := hconj T T₀
    refine card_center_eq_three (h27 T) (a := ⟨g * a * g⁻¹, hg a (hT₀ ha)⟩)
      (b := ⟨g * b * g⁻¹, hg b (hT₀ hb)⟩) fun h => hab ?_
    have h' := congrArg Subtype.val h
    simp only [Subgroup.coe_mul] at h'
    have e : g * (a * b) * g⁻¹ = g * (b * a) * g⁻¹ := by
      calc g * (a * b) * g⁻¹ = g * a * g⁻¹ * (g * b * g⁻¹) := by group
        _ = g * b * g⁻¹ * (g * a * g⁻¹) := h'
        _ = g * (b * a) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel e)
  obtain ⟨φ, hφs, hφk⟩ := hY
  have hYc := card_eq_pCore_mul_of_iso ⟨φ, hφs, hφk⟩
  obtain ⟨j, hj⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥Y)).exists_card_eq
  rw [hj] at hYc
  obtain ⟨R⟩ : Nonempty (Sylow 3 ↥Y) := inferInstance
  have hR9 : Nat.card R = 3 ^ 2 := by
    refine card_sylow_eq R ⟨2 ^ j * 40, by rw [hYc]; ring⟩ fun h => ?_
    rw [hYc] at h
    have h' := (Nat.Coprime.pow_right j
      (by norm_num : Nat.Coprime (3 ^ (2 + 1)) 2)).dvd_of_dvd_mul_left h
    norm_num at h'
  set R' : Subgroup C := (R : Subgroup ↥Y).map Y.subtype with hR'
  have hR'p : IsPGroup 3 ↥R' := R.isPGroup'.map Y.subtype
  have hR'c : Nat.card R' = 9 := by
    rw [hR', Subgroup.card_map_of_injective Y.subtype_injective, hR9]; norm_num
  obtain ⟨T, hRT⟩ := hR'p.exists_le_sylow
  have hT27 := h27 T
  have hTp : IsPGroup 3 ↥(T : Subgroup C) := T.isPGroup'
  have hZR : ∀ x ∈ Subgroup.center ↥(T : Subgroup C), (x : C) ∈ R' := by
    have hidx : (R'.subgroupOf (T : Subgroup C)).index = (Nat.card ↥(T : Subgroup C)).minFac := by
      have h1 := (R'.subgroupOf (T : Subgroup C)).card_mul_index
      rw [hT27, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRT).toEquiv, hR'c] at h1
      rw [hT27, show Nat.minFac 27 = 3 by norm_num]
      omega
    have : (R'.subgroupOf (T : Subgroup C)).Normal := Subgroup.normal_of_index_eq_minFac_card hidx
    have hne : R'.subgroupOf (T : Subgroup C) ≠ ⊥ := by
      intro hb
      have h1 := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRT).toEquiv
      rw [hb, Subgroup.card_bot, hR'c] at h1
      exact absurd h1 (by norm_num)
    intro x hx
    have := center_le_of_normal hTp (hZ T) hne hx
    rwa [Subgroup.mem_subgroupOf] at this
  have hZN : ∀ x ∈ Subgroup.center ↥(T : Subgroup C), (x : C) ∈ N := by
    have hnp : IsPGroup 3 ↥(Subgroup.zpowers n) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hn3, pow_one])
    obtain ⟨T', hnT'⟩ := hnp.exists_le_sylow
    obtain ⟨g, hg⟩ := hconj T T'
    have hgn : g * n * g⁻¹ ∈ (T : Subgroup C) := hg n (hnT' (Subgroup.mem_zpowers n))
    have hgnN : g * n * g⁻¹ ∈ N := hN.conj_mem n hn g
    have : (N.subgroupOf (T : Subgroup C)).Normal := hN.subgroupOf _
    have hne : N.subgroupOf (T : Subgroup C) ≠ ⊥ := by
      intro hb
      have h1 : (⟨g * n * g⁻¹, hgn⟩ : ↥(T : Subgroup C)) ∈ N.subgroupOf (T : Subgroup C) := by
        rw [Subgroup.mem_subgroupOf]; exact hgnN
      rw [hb, Subgroup.mem_bot] at h1
      have h2 : g * n * g⁻¹ = 1 := congrArg Subtype.val h1
      have h3 : n = 1 := by
        calc n = g⁻¹ * (g * n * g⁻¹) * g := by group
          _ = 1 := by rw [h2]; group
      rw [h3, orderOf_one] at hn3
      exact absurd hn3 (by norm_num)
    intro x hx
    have := center_le_of_normal hTp (hZ T) hne hx
    rwa [Subgroup.mem_subgroupOf] at this
  obtain ⟨ζ, hζ1⟩ : ∃ ζ : ↥(Subgroup.center ↥(T : Subgroup C)), ζ ≠ 1 := by
    have : Nontrivial ↥(Subgroup.center ↥(T : Subgroup C)) :=
      Finite.one_lt_card_iff_nontrivial.mp (by rw [hZ T]; norm_num)
    exact exists_ne 1
  have hζR := hZR ζ ζ.2
  have hζN := hZN ζ ζ.2
  obtain ⟨y, -, hyζ⟩ := Subgroup.mem_map.mp hζR
  have hζ1' : ((ζ : ↥(T : Subgroup C)) : C) ≠ 1 := fun h =>
    hζ1 (Subtype.ext (Subtype.ext h))
  obtain ⟨m, hm⟩ := hTp (ζ : ↥(T : Subgroup C))
  have : IsSimpleGroup ↥(alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hNY : (N.subgroupOf Y).Normal := hN.subgroupOf Y
  have := hNY.map φ hφs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N.subgroupOf Y).map φ) with hb | ht
  ·
    have hyN : y ∈ N.subgroupOf Y := by
      rw [Subgroup.mem_subgroupOf]
      have : (y : C) = ((ζ : ↥(T : Subgroup C)) : C) := hyζ
      rw [this]; exact hζN
    have hyk : y ∈ φ.ker := by
      rw [MonoidHom.mem_ker]
      have : φ y ∈ (N.subgroupOf Y).map φ := Subgroup.mem_map_of_mem φ hyN
      rwa [hb, Subgroup.mem_bot] at this
    rw [hφk] at hyk
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥Y)) ⟨y, hyk⟩
    have hy2 : y ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hζ2 : ((ζ : ↥(T : Subgroup C)) : C) ^ 2 ^ k = 1 := by
      rw [← hyζ]; simpa using congrArg Subtype.val hy2
    have hζ3 : ((ζ : ↥(T : Subgroup C)) : C) ^ 3 ^ m = 1 := by
      simpa using congrArg Subtype.val hm
    have hcop : Nat.Coprime (2 ^ k) (3 ^ m) := Nat.Coprime.pow k m (by norm_num)
    have h1 := orderOf_dvd_of_pow_eq_one hζ2
    have h2 := orderOf_dvd_of_pow_eq_one hζ3
    have h3 : orderOf ((ζ : ↥(T : Subgroup C)) : C) = 1 :=
      Nat.dvd_one.mp (by rw [← hcop.gcd_eq_one]; exact Nat.dvd_gcd h1 h2)
    exact hζ1' (orderOf_eq_one_iff.mp h3)
  ·
    apply h5
    have hA6 : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
      decide
    have h1 : Nat.card ↥(alternatingGroup (Fin 6)) ∣ Nat.card ↥(N.subgroupOf Y) := by
      rw [← Subgroup.card_top (G := ↥(alternatingGroup (Fin 6))), ← ht]
      exact Subgroup.card_map_dvd _ _
    have h2 : Nat.card ↥(N.subgroupOf Y) ∣ Nat.card N := by
      rw [← Subgroup.card_map_of_injective (f := Y.subtype) Y.subtype_injective,
        Subgroup.subgroupOf_map_subtype]
      exact Subgroup.card_dvd_of_le inf_le_left
    rw [hA6] at h1
    exact (show 5 ∣ 360 by norm_num).trans (h1.trans h2)

end CFSG.Quasithin.H13.K1262Two.CentJ4

end
