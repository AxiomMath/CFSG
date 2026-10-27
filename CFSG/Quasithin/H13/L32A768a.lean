module

public import CFSG.Quasithin.H13.L32A767b
public import CFSG.Quasithin.H13.L32AL24

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace L32A

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem kz_le_centralizer_of_mem_u0 (h : Hyp147 G T L V) (hMod : StmtL32NModule) {u : G}
    (hu : u ∈ u0 T V) : kz T V ≤ Subgroup.centralizer ({u} : Set G) := by
  have hUe := isElemAbelian_fsuU_of h hMod
  have hw := ((mem_u0_iff h hMod).mp hu).2
  refine (Subgroup.closure_le _).mpr fun g hg => ?_
  obtain ⟨hgH, hodd⟩ := hg
  have hgK : g ∈ kz T V := Subgroup.subset_closure ⟨hgH, hodd⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  obtain ⟨v, hv⟩ : ∃ v, v = g * u * g⁻¹ * u⁻¹ := ⟨_, rfl⟩
  have hvV1 : v ∈ fsuV1 T V := by
    rw [hv]
    exact hw g hgK
  have hgv : g * v = v * g := (Subgroup.mem_centralizer_iff.mp hgH v hvV1).symm
  have hv2 : v * v = 1 := by
    rw [← pow_two]
    exact F7.isElemAbelian_pow_eq_one hUe (le_conjClosure V _ (Subgroup.mem_inf.mp hvV1).1)
  have e1 : g * u = v * u * g := by rw [hv]; group
  have hg2 : (g * g) * u = u * (g * g) := by
    calc (g * g) * u = g * (g * u) := by group
      _ = g * (v * u * g) := by rw [e1]
      _ = (g * v) * u * g := by group
      _ = (v * g) * u * g := by rw [hgv]
      _ = v * (g * u) * g := by group
      _ = v * (v * u * g) * g := by rw [e1]
      _ = (v * v) * u * (g * g) := by group
      _ = u * (g * g) := by rw [hv2, one_mul]
  obtain ⟨m, hm⟩ := hodd
  have hgm : (g * g) ^ (m + 1) = g := by
    rw [← pow_two, ← pow_mul, show 2 * (m + 1) = orderOf g + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  have hc := ((show Commute (g * g) u from hg2).pow_left (m + 1)).eq
  rwa [hgm] at hc

omit [Finite G] in
theorem pCoreOf_centralizer_ne_bot {u : G} (hu1 : u ≠ 1) (hu2 : u * u = 1) :
    pCoreOf 2 (Subgroup.centralizer ({u} : Set G)) ≠ ⊥ := by
  have hle : Subgroup.zpowers u ≤ Subgroup.centralizer ({u} : Set G) :=
    (Subgroup.zpowers_le).mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have hN : Subgroup.centralizer ({u} : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers u : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hc : Commute g u := Subgroup.mem_centralizer_singleton_iff.mp hg
    have hn : ∀ n : ℤ, g * u ^ n * g⁻¹ = u ^ n := fun n => by
      rw [(hc.zpow_right n).eq, mul_inv_cancel_right]
    constructor
    · intro hx
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact Subgroup.mem_zpowers_iff.mpr ⟨n, (hn n).symm⟩
    · intro hx
      obtain ⟨n, hxn⟩ := Subgroup.mem_zpowers_iff.mp hx
      refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
      have e : g * x * g⁻¹ = g * u ^ n * g⁻¹ := by rw [hn n]; exact hxn.symm
      simpa using e.symm
  have hp : IsPGroup 2 (Subgroup.zpowers u) := by
    have h2 : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact hu2) hu1
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, h2, pow_one]
  have hle' := le_pCoreOf_of_le_normalizer 2 hle hN hp
  intro hb
  apply hu1
  have : u ∈ pCoreOf 2 (Subgroup.centralizer ({u} : Set G)) := hle' (Subgroup.mem_zpowers u)
  rwa [hb, Subgroup.mem_bot] at this

theorem centralizer_le_hz_of_le_centralizer
    (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63) (h36 : A36ForSQTK)
    (h1434 : Lemma1434One) (h674 : Lemma14_7_67_four) {u : G} (hu : u ∈ u0 T V) (hu1 : u ≠ 1)
    (hTu : T ≤ Subgroup.centralizer ({u} : Set G)) :
    Subgroup.centralizer ({u} : Set G) ≤ hz T V := by
  have := h.fsu.simple
  have hUe := isElemAbelian_fsuU_of h hMod
  have hu2 : u * u = 1 := by
    rw [← pow_two]
    exact F7.isElemAbelian_pow_eq_one hUe (centralizerMod_le_left _ _ _ hu)
  have hK := kz_le_centralizer_of_mem_u0 h hMod hu
  have hmax := lemma14_7_67_three h h63 h36 h1434
  have hS : QuasithinUnique.IsSylowTwoOf T (Subgroup.centralizer ({u} : Set G)) :=
    isSylowTwoOf_of_le h hTu
  have hTK : T ≤ Subgroup.normalizer (kz T V : Set G) :=
    (T_le_hz h h63).trans (le_normalizer_oTwoUpper _)
  obtain ⟨-, hn⟩ := Vol2Native.normal_containing_cComp_of_le_normalizer h.fsu.nonabelian
    h.fsu.qtke (pCoreOf_centralizer_ne_bot hu1 hu2) hS hK hmax.1 hTK
  obtain ⟨-, hKn⟩ := hn hmax
  have hle := (Subgroup.normal_subgroupOf_iff_le_normalizer hK).mp hKn
  rwa [(h674 G T L V h).1] at hle

theorem conjSub_u0_eq_of_centralizer_le (h : Hyp147 G T L V) (hMod : StmtL32NModule)
    (h674 : Lemma14_7_67_four) {u : G} (hCu : Subgroup.centralizer ({u} : Set G) ≤ hz T V)
    {g : G} (hg : u ∈ conjSub g (u0 T V)) : conjSub g (u0 T V) = u0 T V := by
  rw [mem_conjSub] at hg
  have hK := kz_le_centralizer_of_mem_u0 h hMod hg
  have hKg : ∀ x ∈ kz T V, g * x * g⁻¹ ∈ hz T V := by
    intro x hx
    apply hCu
    have hc := Subgroup.mem_centralizer_singleton_iff.mp (hK hx)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * x * g⁻¹ * u = g * (x * (g⁻¹ * u * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * u * g) * x) * g⁻¹ := by rw [hc]
      _ = u * (g * x * g⁻¹) := by group
  have hKgK : ∀ x ∈ kz T V, g * x * g⁻¹ ∈ kz T V := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      refine Subgroup.subset_closure ⟨hKg x (Subgroup.subset_closure hx), ?_⟩
      have e := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at e
      rw [e]
      exact hx.2
    | one => simp
    | mul a b _ _ ha hb =>
      rw [show g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) by group]
      exact mul_mem ha hb
    | inv a _ ha =>
      rw [show g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ by group]
      exact inv_mem ha
  have hle : conjSub g (kz T V) ≤ kz T V := by
    intro y hy
    rw [mem_conjSub] at hy
    have := hKgK _ hy
    rwa [show g * (g⁻¹ * y * g) * g⁻¹ = y by group] at this
  have heq : conjSub g (kz T V) = kz T V :=
    Subgroup.eq_of_le_of_card_ge hle
      (Subgroup.card_map_of_injective (MulAut.conj g).injective).symm.le
  have hgN : g ∈ Subgroup.normalizer (kz T V : Set G) := conjSub_eq_self_iff.mp heq
  rw [(h674 G T L V h).1] at hgN
  exact conjSub_eq_self_iff.mpr (hz_le_normalizer_u0 h hMod hgN)

theorem normalizer_u0_eq (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h674 : Lemma14_7_67_four) :
    Subgroup.normalizer (u0 T V : Set G) = hz T V := by
  obtain ⟨-, hmax⟩ := (h674 G T L V h).2
  obtain ⟨-, -, -, hV1, -⟩ := hMod G T L V h.hyp h.fsu
  refine hmax _ ⟨u0 T V, ?_, ?_, rfl⟩ (hz_le_normalizer_u0 h hMod)
  · intro hb
    have hle := fsuV1_le_u0 h hMod
    rw [hb, le_bot_iff] at hle
    rw [hle, Subgroup.card_bot] at hV1
    omega
  · have hUe := isElemAbelian_fsuU_of h hMod
    have hUp : IsPGroup 2 ↥(fsuU T V) := fun u => ⟨1, Subtype.ext (by
      simpa using F7.isElemAbelian_pow_eq_one hUe u.2)⟩
    exact hUp.to_le (centralizerMod_le_left _ _ _)

omit [Finite G] in
theorem centralizer_le_hz_of_mem_V1 {z : G} (hV1 : Nat.card ↥(fsuV1 T V) = 2)
    (hzV : z ∈ fsuV1 T V) (hz1 : z ≠ 1) : Subgroup.centralizer ({z} : Set G) ≤ hz T V := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  by_cases hv1 : v = 1
  · rw [hv1, one_mul, mul_one]
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : ↥(fsuV1 T V))).mp hV1
  have h1 := hy ⟨v, hv⟩ (fun h => hv1 (congrArg Subtype.val h))
  have h2 := hy ⟨z, hzV⟩ (fun h => hz1 (congrArg Subtype.val h))
  have hvz : v = z := congrArg Subtype.val (h1.trans h2.symm)
  rw [hvz]
  exact Subgroup.mem_centralizer_iff.mp hx z rfl

theorem lemma14_7_68_of_centralizer_le (hMod : StmtL32NModule) (h674 : Lemma14_7_67_four)
    (hC : ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp147 G T L V →
      ∀ u ∈ u0 T V, u ≠ 1 → (∀ t ∈ T, t * u * t⁻¹ * u⁻¹ ∈ fsuV1 T V) →
        Subgroup.centralizer ({u} : Set G) ≤ hz T V) : Lemma14_7_68 := by
  intro G _ _ T L V h
  refine ⟨fun z hzV g hg => ?_, fun u hu hu1 hT =>
    ⟨hC G T L V h u hu hu1 hT, fun g hg =>
      conjSub_u0_eq_of_centralizer_le h hMod h674 (hC G T L V h u hu hu1 hT) hg⟩⟩
  by_cases hz1 : z = 1
  · rw [hz1, mul_one, mul_inv_cancel]
  obtain ⟨-, -, -, hV1, -⟩ := hMod G T L V h.hyp h.fsu
  have hCz := centralizer_le_hz_of_mem_V1 hV1 hzV hz1
  have hmem : z ∈ conjSub g⁻¹ (u0 T V) := by
    rw [mem_conjSub, inv_inv]
    exact hg
  have heq := conjSub_u0_eq_of_centralizer_le h hMod h674 hCz hmem
  have hgN : g⁻¹ ∈ Subgroup.normalizer (u0 T V : Set G) := conjSub_eq_self_iff.mp heq
  rw [normalizer_u0_eq h hMod h674] at hgN
  have hgH : g ∈ hz T V := by simpa using inv_mem hgN
  rw [(Subgroup.mem_centralizer_iff.mp hgH z hzV).symm, mul_inv_cancel_right]

end L32A

@[expose] def Lemma14_7_68_b : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp147 G T L V →
    ∀ u ∈ L32A.u0 T V, u ≠ 1 → (∀ t ∈ T, t * u * t⁻¹ * u⁻¹ ∈ fsuV1 T V) →
      QuasithinUnique.IsSylowTwoOf (T ⊓ Subgroup.centralizer ({u} : Set G))
        (Subgroup.centralizer ({u} : Set G)) →
      ∀ I ∈ cComp (Subgroup.centralizer ({u} : Set G)),
        (I.subgroupOf (Subgroup.centralizer ({u} : Set G))).Normal → L32A.kz T V ≤ I →
          I = L32A.kz T V

end CFSG.Quasithin.H13
