module

public import CFSG.LocalAnalysis.StandardType.GGSixLSixFiveKnownForms
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFlatIVQuot
public import CFSG.LocalAnalysis.StandardType.GGHypThreeSixteenFlatMarking
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.CoprimeHall

public section

namespace CFSG.StandardType

open CFSG.Assembly

open scoped commutatorElement

section Elementary

variable {G : Type} [Group G]

theorem ggEq_one_of_mem_odd [Finite G] {E : Subgroup G} (hE : Odd (Nat.card E)) {w : G}
    (hw : w ∈ E) {a : ℕ} (ha : w ^ 2 ^ a = 1) : w = 1 := by
  have h1 : orderOf (⟨w, hw⟩ : ↥E) ∣ Nat.card E := orderOf_dvd_natCard _
  have h2 : orderOf (⟨w, hw⟩ : ↥E) ∣ 2 ^ a := by
    apply orderOf_dvd_of_pow_eq_one
    exact Subtype.ext (by simpa using ha)
  have hcop : Nat.Coprime (2 ^ a) (Nat.card E) :=
    Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hE)
  have h3 : orderOf (⟨w, hw⟩ : ↥E) ∣ Nat.gcd (2 ^ a) (Nat.card E) := Nat.dvd_gcd h2 h1
  rw [hcop.gcd_eq_one] at h3
  have h4 : orderOf (⟨w, hw⟩ : ↥E) = 1 := Nat.dvd_one.mp h3
  have h5 : (⟨w, hw⟩ : ↥E) = 1 := orderOf_eq_one_iff.mp h4
  simpa using congrArg Subtype.val h5

theorem ggEq_one_of_mem_isPGroup_of_mem_odd [Finite G] {P E : Subgroup G} (hP : IsPGroup 2 P)
    (hE : Odd (Nat.card E)) {w : G} (hwP : w ∈ P) (hwE : w ∈ E) : w = 1 := by
  obtain ⟨a, ha⟩ := hP ⟨w, hwP⟩
  exact ggEq_one_of_mem_odd hE hwE (a := a) (by simpa using congrArg Subtype.val ha)

theorem ggMem_zpowers_of_isPGroup_two_of_odd_center [Finite G] {J P : Subgroup G} {r w z : G}
    {k : ℤ} (hrJ : r ∈ J) (hr2 : r ^ 2 = 1) (hP : IsPGroup 2 P) (hwP : w ∈ P) (hwJ : w ∈ J)
    (hz : z ∈ Subgroup.centralizer (J : Set G)) (hwz : w = r ^ k * z)
    (hZ : Odd (Nat.card (Subgroup.center ↥J))) : w ∈ Subgroup.zpowers r := by
  have hzw : z = (r ^ k)⁻¹ * w := by rw [hwz]; group
  have hzJ : z ∈ J := by
    rw [hzw]
    exact J.mul_mem (J.inv_mem (J.zpow_mem hrJ k)) hwJ
  have hrz : Commute r z := Subgroup.mem_centralizer_iff.mp hz r hrJ
  have hcomm : Commute ((r ^ k)⁻¹) w := by
    have h2 : Commute (r ^ k) z := hrz.zpow_left k
    have h3 : Commute (r ^ k) (r ^ k * z) := (Commute.refl _).mul_right h2
    rw [← hwz] at h3
    exact h3.inv_left
  obtain ⟨a, ha⟩ := hP ⟨w, hwP⟩
  have hwa : w ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
  have hrk : ((r ^ k)⁻¹) ^ 2 = 1 := by
    have : (r ^ k) ^ 2 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hr2, one_zpow]
    rw [inv_pow, this, inv_one]
  have h1 : ((r ^ k)⁻¹) ^ 2 ^ (a + 1) = 1 := by
    have e : 2 ^ (a + 1) = 2 * 2 ^ a := by ring
    rw [e, pow_mul, hrk, one_pow]
  have h2 : w ^ 2 ^ (a + 1) = 1 := by
    have e : 2 ^ (a + 1) = 2 ^ a * 2 := by ring
    rw [e, pow_mul, hwa, one_pow]
  have hz2 : z ^ 2 ^ (a + 1) = 1 := by
    rw [hzw, hcomm.mul_pow, h1, h2, one_mul]
  have hzc : z ∈ ggCenterOf J := ⟨⟨z, hzJ⟩, by
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hz g g.2), rfl⟩
  have hcard : Odd (Nat.card (ggCenterOf J)) := by
    rw [Subgroup.card_map_of_injective J.subtype_injective]
    exact hZ
  have hz1 : z = 1 := ggEq_one_of_mem_odd hcard hzc hz2
  rw [hwz, hz1, mul_one]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers r) k

theorem ggConj_mem_zpowers_of_commute {r y c : G} (hy : y * r = r * y)
    (hc : c ∈ Subgroup.zpowers r) : y * c * y⁻¹ ∈ Subgroup.zpowers r := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
  have h1 : y * r * y⁻¹ = r := by rw [hy]; group
  rw [← conj_zpow, h1]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers r) m

theorem ggCommutator_mem_zpowers_of_card_four [Finite G] {V : Subgroup G} {r a v : G}
    (hV : Nat.card V = 4) (hr2 : r ^ 2 = 1) (hrV : r ∈ V) (hr1 : r ≠ 1)
    (ha : a ∈ Subgroup.normalizer (V : Set G)) (har : a * r = r * a) (hv : v ∈ V) :
    v * a * v⁻¹ * a⁻¹ ∈ Subgroup.zpowers r := by
  have hord : orderOf r = 2 := orderOf_eq_prime hr2 hr1
  have hle : Subgroup.zpowers r ≤ V := Subgroup.zpowers_le.mpr hrV
  have hrel : (Subgroup.zpowers r).relIndex V = 2 := by
    have h1 := Subgroup.card_mul_index (Subgroup.zpowers r)
    have h2 := Subgroup.card_mul_index V
    have h3 := Subgroup.relIndex_mul_index hle
    rw [Nat.card_zpowers, hord] at h1
    rw [hV] at h2
    have hW : 0 < V.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    have h4 : (Subgroup.zpowers r).relIndex V * V.index = 2 * V.index := by
      rw [h3]; omega
    exact Nat.eq_of_mul_eq_mul_right hW h4
  have hH2 : ((Subgroup.zpowers r).subgroupOf V).index = 2 := hrel
  have hu : a * v * a⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp ha v).mp hv
  have har' : a⁻¹ * r = r * a⁻¹ := (Commute.inv_left (show Commute a r from har))
  have hconj : a * v * a⁻¹ ∈ Subgroup.zpowers r ↔ v ∈ Subgroup.zpowers r := by
    constructor
    · intro h
      have := ggConj_mem_zpowers_of_commute har' h
      simpa [mul_assoc] using this
    · intro h
      exact ggConj_mem_zpowers_of_commute har h
  have key : (⟨v, hv⟩ : V) * (⟨a * v * a⁻¹, hu⟩ : V)⁻¹ ∈
      (Subgroup.zpowers r).subgroupOf V := by
    rw [Subgroup.mul_mem_iff_of_index_two hH2]
    simp only [Subgroup.mem_subgroupOf, InvMemClass.coe_inv, inv_mem_iff]
    exact hconj.symm
  have key' := Subgroup.mem_subgroupOf.mp key
  have e : v * a * v⁻¹ * a⁻¹ = v * (a * v * a⁻¹)⁻¹ := by group
  rw [e]
  exact key'

@[expose] def ggCommModR (V : Subgroup G) (r : G) : Subgroup G where
  carrier := {y | y * r = r * y ∧ ∀ v ∈ V, v * y * v⁻¹ * y⁻¹ ∈ Subgroup.zpowers r}
  one_mem' := ⟨by simp, fun v _ => by simpa using Subgroup.one_mem _⟩
  mul_mem' := by
    rintro y y' ⟨hy, hyV⟩ ⟨hy', hyV'⟩
    refine ⟨by rw [mul_assoc, hy', ← mul_assoc, hy, mul_assoc], fun v hv => ?_⟩
    have e : v * (y * y') * v⁻¹ * (y * y')⁻¹ =
        (v * y * v⁻¹ * y⁻¹) * (y * (v * y' * v⁻¹ * y'⁻¹) * y⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ (hyV v hv) (ggConj_mem_zpowers_of_commute hy (hyV' v hv))
  inv_mem' := by
    rintro y ⟨hy, hyV⟩
    have hy' : y⁻¹ * r = r * y⁻¹ := Commute.inv_left (show Commute y r from hy)
    refine ⟨hy', fun v hv => ?_⟩
    have e : v * y⁻¹ * v⁻¹ * y⁻¹⁻¹ = y⁻¹ * (v * y * v⁻¹ * y⁻¹)⁻¹ * y⁻¹⁻¹ := by group
    rw [e]
    exact ggConj_mem_zpowers_of_commute hy' (Subgroup.inv_mem _ (hyV v hv))

theorem ggMem_zpowers_involution {r u : G} (hr2 : r ^ 2 = 1) (hu : u ∈ Subgroup.zpowers r) :
    u = 1 ∨ u = r := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  rcases Int.even_or_odd m with ⟨n, hn⟩ | ⟨n, hn⟩
  · left
    rw [hn, ← two_mul, zpow_mul]
    simp [hr2]
  · right
    rw [hn, zpow_add, zpow_mul, zpow_one]
    simp [hr2]

theorem ggNormalizer_zpowers_eq_centralizer_of_sq {r : G} (hr2 : r ^ 2 = 1) (hr1 : r ≠ 1) :
    Subgroup.normalizer (Subgroup.zpowers r : Set G) = Subgroup.centralizer {r} := by
  ext g
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h1 : g * r * g⁻¹ ∈ Subgroup.zpowers r := (h r).mp (Subgroup.mem_zpowers r)
    rcases ggMem_zpowers_involution hr2 h1 with h2 | h2
    · exfalso
      apply hr1
      calc r = g⁻¹ * (g * r * g⁻¹) * g := by group
        _ = 1 := by rw [h2]; group
    · calc g * r = (g * r * g⁻¹) * g := by group
        _ = r * g := by rw [h2]
  · intro h s
    have h' : g⁻¹ * r = r * g⁻¹ := Commute.inv_left (show Commute g r from h)
    constructor
    · intro hs
      exact ggConj_mem_zpowers_of_commute h hs
    · intro hs
      have := ggConj_mem_zpowers_of_commute h' hs
      simpa [mul_assoc] using this

theorem ggLe_of_fixed_of_commutators [Finite G] {p : ℕ} [Fact p.Prime] {D Y T : Subgroup G}
    (hp2 : p ≠ 2) (hD : IsPGroup p D) (hY : IsPGroup 2 Y)
    (hDY : D ≤ Subgroup.normalizer (Y : Set G))
    (hfix : ∀ y ∈ Y, (∀ b ∈ D, b * y * b⁻¹ = y) → y ∈ T)
    (hcom : ∀ b ∈ D, ∀ y ∈ Y, y⁻¹ * (b * y * b⁻¹) ∈ T) : Y ≤ T := by
  classical
  let : MulDistribMulAction ↥D ↥Y := MulDistribMulAction.compHom ↥Y (Subgroup.inclusion hDY)
  have hsmul : ∀ (b : ↥D) (y : ↥Y), ((b • y : ↥Y) : G) = (b : G) * y * (b : G)⁻¹ :=
    fun _ _ => rfl
  have hsolv : Group.IsSolvable ↥Y := by
    have := hY.isNilpotent
    infer_instance
  have hcop : Nat.Coprime (Nat.card ↥D) (Nat.card ↥Y) :=
    IsPGroup.coprime_card_of_ne p 2 hp2 D Y hD hY
  have htop := CFSG.fixedPointSubgroup_sup_commutatorAction_eq_top_of_solvable_coprime
    (A := ↥D) (G := ↥Y) hsolv hcop
  have hfix' : CFSG.fixedPointSubgroup ↥D ↥Y ≤ T.subgroupOf Y := by
    intro y hy
    rw [Subgroup.mem_subgroupOf]
    refine hfix y y.2 fun b hb => ?_
    have hc := congrArg Subtype.val (hy ⟨b, hb⟩)
    rwa [hsmul] at hc
  have hcom' : CFSG.commutatorAction ↥D ↥Y ≤ T.subgroupOf Y := by
    rw [CFSG.commutatorAction, CFSG.commutatorSubgroup, Subgroup.closure_le]
    rintro _ ⟨b, y, -, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.coe_mul, InvMemClass.coe_inv, hsmul]
    exact hcom b b.2 y y.2
  intro s hs
  have hmem : (⟨s, hs⟩ : ↥Y) ∈ T.subgroupOf Y :=
    sup_le hfix' hcom' (htop ▸ Subgroup.mem_top _)
  rwa [Subgroup.mem_subgroupOf] at hmem

end Elementary

section Outer

variable {G : Type} [Group G] [Finite G]

theorem ggInn_normal (K : Type) [Group K] :
    ((MulAut.conj : K →* MulAut K).range).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨k, rfl⟩ := hn
  refine ⟨g k, ?_⟩
  refine MulEquiv.ext fun z => ?_
  simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_apply, map_mul, map_inv,
    MulEquiv.apply_symm_apply]

theorem ggCentralizer_inn_eq_bot {K : Type} [Group K] (hK : commutator K = ⊤) :
    Subgroup.centralizer (((MulAut.conj : K →* MulAut K).range : Subgroup (MulAut K)) :
      Set (MulAut K)) = ⊥ := by
  rw [eq_bot_iff]
  intro α hα
  rw [Subgroup.mem_centralizer_iff] at hα
  have h1 : ∀ k z : K, α (k * z * k⁻¹) = k * α z * k⁻¹ := by
    intro k z
    have h := DFunLike.congr_fun (hα (MulAut.conj k) ⟨k, rfl⟩) z
    simpa [MulAut.mul_apply, MulAut.conj_apply] using h.symm
  have h2 : ∀ k w : K, w * (k⁻¹ * α k) = (k⁻¹ * α k) * w := by
    intro k w
    obtain ⟨z, rfl⟩ := α.surjective w
    have h3 : α k * α z = k * α z * k⁻¹ * α k := by
      have h4 := h1 k z
      simp only [map_mul, map_inv] at h4
      calc α k * α z = (α k * α z * (α k)⁻¹) * α k := by group
        _ = k * α z * k⁻¹ * α k := by rw [h4]
    calc α z * (k⁻¹ * α k) = k⁻¹ * (k * α z * k⁻¹ * α k) := by group
      _ = k⁻¹ * (α k * α z) := by rw [h3]
      _ = (k⁻¹ * α k) * α z := by group
  let φ : K →* ↥(Subgroup.center K) :=
    { toFun := fun k => ⟨k⁻¹ * α k, Subgroup.mem_center_iff.mpr (h2 k)⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro k k'
        apply Subtype.ext
        change (k * k')⁻¹ * α (k * k') = (k⁻¹ * α k) * (k'⁻¹ * α k')
        calc (k * k')⁻¹ * α (k * k') = k'⁻¹ * (k⁻¹ * α k) * α k' := by rw [map_mul]; group
          _ = (k⁻¹ * α k) * k'⁻¹ * α k' := by rw [h2 k k'⁻¹]
          _ = (k⁻¹ * α k) * (k'⁻¹ * α k') := by group }
  have hker : commutator K ≤ φ.ker := Abelianization.commutator_subset_ker φ
  rw [hK] at hker
  rw [Subgroup.mem_bot]
  refine MulEquiv.ext fun k => ?_
  have h5 : φ k = 1 := MonoidHom.mem_ker.mp (hker (Subgroup.mem_top k))
  have h6 : k⁻¹ * α k = 1 := congrArg Subtype.val h5
  have h7 : α k = k := by
    calc α k = k * (k⁻¹ * α k) := by group
      _ = k := by rw [h6, mul_one]
  simpa using h7

theorem ggOutTwoComm_apply (hK3 : GGOutTwoCommInner) {K : Subgroup G}
    (hmk : LargeEvenMarking ↥K (fun _ _ _ _ _ _ => True)) {Y : Subgroup G} (hY : IsPGroup 2 Y)
    (hYK : Y ≤ Subgroup.normalizer (K : Set G)) {δ : G}
    (hδK : δ ∈ Subgroup.normalizer (K : Set G)) (hδ : Odd (orderOf δ))
    (hδY : δ ∈ Subgroup.normalizer (Y : Set G)) {y : G} (hy : y ∈ Y) :
    ∃ k ∈ K, ∃ c ∈ Subgroup.centralizer (K : Set G), y⁻¹ * δ⁻¹ * y * δ = k * c := by
  classical
  have hperf : commutator ↥K = ⊤ := hmk.1
  haveI : Finite (MulAut ↥K) :=
    Finite.of_injective (fun f : MulAut ↥K => (f : ↥K → ↥K)) DFunLike.coe_injective
  set N : Subgroup G := Subgroup.normalizer (K : Set G) with hN
  set ρ : ↥N →* MulAut ↥K := K.normalizerMonoidHom with hρ
  have hρapp : ∀ (n : ↥N) (k : ↥K), ((ρ n k : ↥K) : G) = (n : G) * k * (n : G)⁻¹ := fun _ _ => rfl
  set Kb : Subgroup (MulAut ↥K) := (MulAut.conj : ↥K →* MulAut ↥K).range with hKb
  have hKbN : Kb.Normal := ggInn_normal ↥K
  have hC : Subgroup.centralizer (Kb : Set (MulAut ↥K)) = ⊥ := ggCentralizer_inn_eq_bot hperf
  have hmkb : LargeEvenMarking ↥Kb (fun _ _ _ _ _ _ => True) := by
    refine largeEvenMarking_true_of_surjective_ker_le_center
      (MulAut.conj : ↥K →* MulAut ↥K).rangeRestrict
      (MonoidHom.rangeRestrict_surjective _) ?_ hmk
    intro k hk
    rw [MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker] at hk
    rw [Subgroup.mem_center_iff]
    intro z
    have := DFunLike.congr_fun hk z
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc z * k = (k * z * k⁻¹) * k := by rw [this]
      _ = k * z := by group
  have hsimple : IsSimpleGroup ↥Kb := ggIsSimpleGroup_of_marking hmkb hC
  set Y' : Subgroup (MulAut ↥K) := (Y.subgroupOf N).map ρ with hY'
  have hY'2 : IsPGroup 2 Y' := (hY.comap_subtype (K := N)).map ρ
  have hY'mem : ∀ w : MulAut ↥K, w ∈ Y' ↔ ∃ x : ↥N, (x : G) ∈ Y ∧ ρ x = w := by
    intro w
    rw [hY', Subgroup.mem_map]
    simp only [Subgroup.mem_subgroupOf]
  set δ' : MulAut ↥K := ρ ⟨δ, hδK⟩ with hδ'
  have hδ'odd : Odd (orderOf δ') := by
    have h1 : orderOf δ' ∣ orderOf (⟨δ, hδK⟩ : ↥N) := orderOf_map_dvd ρ ⟨δ, hδK⟩
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat hδ h1
  have hδ'Y' : δ' ∈ Subgroup.normalizer (Y' : Set (MulAut ↥K)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro w
    rw [hY'mem, hY'mem]
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨⟨δ, hδK⟩ * x * ⟨δ, hδK⟩⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
      exact (Subgroup.mem_normalizer_iff.mp hδY (x : G)).mp hx
    · rintro ⟨x, hx, hxw⟩
      refine ⟨⟨δ, hδK⟩⁻¹ * x * ⟨δ, hδK⟩, ?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp hδY ((δ⁻¹ * (x : G) * δ))).mpr
        have e : δ * (δ⁻¹ * (x : G) * δ) * δ⁻¹ = x := by group
        rw [e] at this
        exact this hx
      · rw [map_mul, map_mul, map_inv, hxw]
        show δ'⁻¹ * (δ' * w * δ'⁻¹) * δ' = w
        group
  have hy' : ρ ⟨y, hYK hy⟩ ∈ Y' := (hY'mem _).mpr ⟨⟨y, hYK hy⟩, hy, rfl⟩
  have hres := hK3 (MulAut ↥K) Kb hKbN hC hsimple hmkb δ' hδ'odd Y' hY'2 hδ'Y' _ hy'
  set g : G := y⁻¹ * δ⁻¹ * y * δ with hg
  have hgN : g ∈ N := by
    have hy1 : y ∈ N := hYK hy
    exact N.mul_mem (N.mul_mem (N.mul_mem (N.inv_mem hy1) (N.inv_mem hδK)) hy1) hδK
  have hρg : ρ ⟨g, hgN⟩ = (ρ ⟨y, hYK hy⟩)⁻¹ * δ'⁻¹ * ρ ⟨y, hYK hy⟩ * δ' := by
    have : (⟨g, hgN⟩ : ↥N) = (⟨y, hYK hy⟩ : ↥N)⁻¹ * (⟨δ, hδK⟩ : ↥N)⁻¹ * ⟨y, hYK hy⟩ *
        ⟨δ, hδK⟩ := Subtype.ext rfl
    rw [this, map_mul, map_mul, map_mul, map_inv, map_inv]
  obtain ⟨k, hk⟩ := hres
  rw [← hρg] at hk
  refine ⟨(k : G), k.2, (k : G)⁻¹ * g, ?_, by rw [hg]; group⟩
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hz1 : (k : G) * z * (k : G)⁻¹ = g * z * g⁻¹ := by
    have := DFunLike.congr_fun hk ⟨z, hz⟩
    have h2 := congrArg Subtype.val this
    simpa [MulAut.conj_apply, hρapp] using h2
  calc z * ((k : G)⁻¹ * g) = (k : G)⁻¹ * ((k : G) * z * (k : G)⁻¹) * g := by group
    _ = (k : G)⁻¹ * (g * z * g⁻¹) * g := by rw [hz1]
    _ = ((k : G)⁻¹ * g) * z := by group

end Outer

end CFSG.StandardType
