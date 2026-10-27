module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight6xBR861E
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.UniquenessCase.UC6R3
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight6xCRestDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank
public import CFSG.Quasithin.Background.F1Models
import CFSG.CGT.PushingUpLit.Transport
import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
import CFSG.RankThree.PartTwo.Sec3.TwoThreeStructure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)

open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data Bar2 pRank_bar2_eq_of_odd)

open CFSG.LocalAnalysis.UniquenessCase.UC6 (R6_9)

open CFSG.LocalAnalysis.UniquenessCase.UC6S846 (SigmaStd)

private theorem k1471r1_commutator_mem_center {H : Type} [Group H] (hH : Nat.card H = 3 ^ 3)
    (x y : H) : x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center H := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk0, hk⟩ := IsPGroup.card_center_eq_prime_pow hH (by norm_num)
  have hmul := (Subgroup.center H).card_mul_index
  rw [hk, hH] at hmul
  obtain ⟨j, hj, hjd⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
    (Dvd.intro_left _ hmul : (Subgroup.center H).index ∣ 3 ^ 3)
  rw [hjd, ← pow_add] at hmul
  have hkj : k + j = 3 := Nat.pow_right_injective (by norm_num : 2 ≤ 3) hmul
  have hQ : Nat.card (H ⧸ Subgroup.center H) = 3 ^ j := by
    rw [← Subgroup.index_eq_card, hjd]
  have hcomm : IsMulCommutative (H ⧸ Subgroup.center H) := by
    obtain rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    · have : Subsingleton (H ⧸ Subgroup.center H) :=
        (Nat.card_eq_one_iff_unique.mp (by simpa using hQ)).1
      exact ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩
    · have : IsCyclic (H ⧸ Subgroup.center H) := isCyclic_of_prime_card (p := 3) (by simpa using hQ)
      infer_instance
    · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq hQ
  have hle := Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hcomm
  refine hle ?_
  rw [commutator_eq_closure]
  exact Subgroup.subset_closure (commutator_mem_commutatorSet x y)

private theorem k1471r1_upperCentralSeries_two {K : Type} [Group K] {R : Subgroup K}
    (hcard : Nat.card R = 27) : Subgroup.upperCentralSeries ↥R 2 = ⊤ := by
  rw [eq_top_iff]
  intro g _
  rw [Subgroup.mem_upperCentralSeries_succ_iff]
  intro y
  rw [Subgroup.upperCentralSeries_one]
  exact k1471r1_commutator_mem_center (by simpa using hcard) g y

theorem not_ok69_of_nonabelian_order_27 {K : Type} [Group K] [Finite K] {R : Subgroup K} {a : K}
    (hcard : Nat.card R = 27) (ha : a ∈ R) (hanz : a ∉ (Subgroup.center ↥R).map R.subtype) :
    ¬ Ok69 a := by
  intro hok
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hR : IsPGroup 3 R := IsPGroup.of_card (n := 3) (by simpa using hcard)
  have h3 := (hok R hR (Subgroup.le_normalizer ha)).2
  rw [sup_eq_left.mpr (Subgroup.zpowers_le.mpr ha)] at h3
  exact hanz (h3 (Subgroup.mem_map.mpr
    ⟨⟨a, ha⟩, (k1471r1_upperCentralSeries_two hcard).ge (Subgroup.mem_top _), rfl⟩))

private theorem k1471r2_mem_secondCenter_iff {K : Type} [Group K] (S : Subgroup K) (s : K) :
    s ∈ secondCenterSubgroup S ↔ ∃ _ : s ∈ S, ∀ g ∈ S, ∀ h ∈ S,
      h * (s * g * s⁻¹ * g⁻¹) = (s * g * s⁻¹ * g⁻¹) * h := by
  unfold secondCenterSubgroup
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.2, fun g hg h hh => ?_⟩
    have h1 := Subgroup.mem_upperCentralSeries_succ_iff.mp hx ⟨g, hg⟩
    rw [Subgroup.upperCentralSeries_one] at h1
    have h2 := congrArg Subtype.val (Subgroup.mem_center_iff.mp h1 ⟨h, hh⟩)
    simpa [commutatorElement_def] using h2
  · rintro ⟨hs, h⟩
    refine ⟨⟨s, hs⟩, (Subgroup.mem_upperCentralSeries_succ_iff (n := 1)).mpr fun y => ?_, rfl⟩
    rw [Subgroup.upperCentralSeries_one, Subgroup.mem_center_iff]
    intro z
    apply Subtype.ext
    simpa [commutatorElement_def] using h y y.2 z z.2

private theorem k1471r2_mem_center_map {K : Type} [Group K] {S : Subgroup K} {s : K}
    (h : s ∈ (Subgroup.center ↥S).map S.subtype) : s ∈ S ∧ ∀ g ∈ S, g * s = s * g := by
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp h
  exact ⟨x.2, fun g hg => congrArg Subtype.val (Subgroup.mem_center_iff.mp hx ⟨g, hg⟩)⟩

private theorem k1471r2_inv_step {K : Type} [Group K] (x v : K)
    (hc : x * (x * v * x⁻¹ * v⁻¹) = (x * v * x⁻¹ * v⁻¹) * x) :
    x⁻¹ * v * x⁻¹⁻¹ * v⁻¹ = (x * v * x⁻¹ * v⁻¹)⁻¹ := by
  have h1 : x⁻¹ * (x * v * x⁻¹ * v⁻¹) * x = x * v * x⁻¹ * v⁻¹ := by
    calc x⁻¹ * (x * v * x⁻¹ * v⁻¹) * x = x⁻¹ * ((x * v * x⁻¹ * v⁻¹) * x) := by group
      _ = x⁻¹ * (x * (x * v * x⁻¹ * v⁻¹)) := by rw [hc]
      _ = x * v * x⁻¹ * v⁻¹ := by group
  calc x⁻¹ * v * x⁻¹⁻¹ * v⁻¹ = x⁻¹ * (v * x * v⁻¹ * x⁻¹) * x := by group
    _ = x⁻¹ * (x * v * x⁻¹ * v⁻¹)⁻¹ * x := by group
    _ = (x⁻¹ * (x * v * x⁻¹ * v⁻¹) * x)⁻¹ := by group
    _ = (x * v * x⁻¹ * v⁻¹)⁻¹ := by rw [h1]

private theorem k1471r2_conj_central {K : Type} [Group K] {Qb T V : Subgroup K} {u : K}
    (hTab : IsMulCommutative ↥T) (hV : V ≤ T) (hQeq : Qb = T ⊔ zpowers u)
    (htransv : ∀ v ∈ V, (u * v * u⁻¹ * v⁻¹) ∈ V ∧
      u * (u * v * u⁻¹ * v⁻¹) * u⁻¹ = u * v * u⁻¹ * v⁻¹) :
    ∀ g ∈ Qb, ∀ v ∈ V, g * v * g⁻¹ * v⁻¹ ∈ V ∧
      ∀ q ∈ Qb, q * (g * v * g⁻¹ * v⁻¹) = (g * v * g⁻¹ * v⁻¹) * q := by
  have hTc : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hTab.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hTQ : T ≤ Qb := hQeq ▸ le_sup_left
  have huQ : u ∈ Qb := hQeq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
  let Z0 : Subgroup K := V ⊓ Subgroup.centralizer (Qb : Set K)
  have hw : ∀ v ∈ V, u * v * u⁻¹ * v⁻¹ ∈ Z0 := by
    intro v hv
    obtain ⟨hwV, hwu⟩ := htransv v hv
    generalize u * v * u⁻¹ * v⁻¹ = w at hwV hwu ⊢
    refine ⟨hwV, Subgroup.mem_centralizer_iff.mpr fun q hq => ?_⟩
    have hle : Qb ≤ Subgroup.centralizer {w} := by
      rw [hQeq]
      refine sup_le (fun t ht => ?_) (Subgroup.zpowers_le.mpr ?_)
      · refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
        rw [Set.mem_singleton_iff] at hh
        subst hh
        exact hTc _ (hV hwV) t ht
      · refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
        rw [Set.mem_singleton_iff] at hh
        subst hh
        calc h * u = (u * h * u⁻¹) * u := by rw [hwu]
          _ = u * h := by group
    exact ((Subgroup.mem_centralizer_iff.mp (hle hq)) w rfl).symm
  have hZc : ∀ z ∈ Z0, ∀ q ∈ Qb, q * z = z * q := fun z hz q hq =>
    Subgroup.mem_centralizer_iff.mp hz.2 q hq
  have key : ∀ g ∈ Qb, ∀ v ∈ V, g * v * g⁻¹ * v⁻¹ ∈ Z0 := by
    intro g hg
    have hcl : g ∈ Subgroup.closure ((T : Set K) ∪ {u}) := by
      rw [Subgroup.closure_union, Subgroup.closure_eq, ← Subgroup.zpowers_eq_closure, ← hQeq]
      exact hg
    refine (Subgroup.closure_induction
      (p := fun g _ => g ∈ Qb ∧ ∀ v ∈ V, g * v * g⁻¹ * v⁻¹ ∈ Z0) ?_ ?_ ?_ ?_ hcl).2
    · rintro x (hx | rfl)
      · refine ⟨hTQ hx, fun v hv => ?_⟩
        have : x * v * x⁻¹ * v⁻¹ = 1 := by
          rw [hTc x hx v (hV hv)]; group
        rw [this]
        exact one_mem _
      · exact ⟨huQ, hw⟩
    · exact ⟨one_mem _, fun v _ => by simp⟩
    · rintro x y - - ⟨hxQ, hx⟩ ⟨hyQ, hy⟩
      refine ⟨mul_mem hxQ hyQ, fun v hv => ?_⟩
      have hc := hZc _ (hy v hv) x hxQ
      have e : (x * y) * v * (x * y)⁻¹ * v⁻¹ =
          (y * v * y⁻¹ * v⁻¹) * (x * v * x⁻¹ * v⁻¹) := by
        calc (x * y) * v * (x * y)⁻¹ * v⁻¹
            = (x * (y * v * y⁻¹ * v⁻¹) * x⁻¹) * (x * v * x⁻¹ * v⁻¹) := by group
          _ = (y * v * y⁻¹ * v⁻¹) * (x * v * x⁻¹ * v⁻¹) := by rw [hc]; group
      rw [e]
      exact mul_mem (hy v hv) (hx v hv)
    · rintro x - ⟨hxQ, hx⟩
      refine ⟨inv_mem hxQ, fun v hv => ?_⟩
      rw [k1471r2_inv_step x v (hZc _ (hx v hv) x hxQ)]
      exact inv_mem (hx v hv)
  exact fun g hg v hv => ⟨(key g hg v hv).1, fun q hq => hZc _ (key g hg v hv) q hq⟩

theorem torusType_inner_mem_center {K : Type} [Group K] [Finite K] {Qb T V : Subgroup K} {u a : K}
    (hQ : IsPGroup 3 Qb) (hTn : (T.subgroupOf Qb).Normal) (hTab : IsMulCommutative ↥T)
    (hV : V ≤ T) (hVel : IsElemAbelian 3 V) (hVmax : ∀ t ∈ T, t ^ 3 = 1 → t ∈ V)
    (hQeq : Qb = T ⊔ zpowers u)
    (htransv : ∀ v ∈ V, (u * v * u⁻¹ * v⁻¹) ∈ V ∧
      u * (u * v * u⁻¹ * v⁻¹) * u⁻¹ = u * v * u⁻¹ * v⁻¹)
    (houtside : ∀ g ∈ Qb, g ∉ T → ∃ v ∈ V, g * v * g⁻¹ ≠ v)
    (ha : a ∈ Qb) (ha3 : orderOf a = 3) (hok : Ok69 a) : a ∈ V ∧ u * a * u⁻¹ = a := by
  have _ := hTn
  have hcc := k1471r2_conj_central hTab hV hQeq htransv
  have hTQ : T ≤ Qb := hQeq ▸ le_sup_left
  have huQ : u ∈ Qb := hQeq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
  have hVQ : V ≤ Qb := hV.trans hTQ
  have hcomm : ∀ v ∈ V, ∀ g ∈ Qb, ∀ q ∈ Qb,
      q * (v * g * v⁻¹ * g⁻¹) = (v * g * v⁻¹ * g⁻¹) * q := by
    intro v hv g hg q hq
    have e : v * g * v⁻¹ * g⁻¹ = (g * v * g⁻¹ * v⁻¹)⁻¹ := by group
    rw [e]
    exact (Commute.inv_right (show Commute q (g * v * g⁻¹ * v⁻¹) from (hcc g hg v hv).2 q hq)).eq
  by_cases haT : a ∈ T
  · have haV : a ∈ V := hVmax a haT (by rw [← ha3]; exact pow_orderOf_eq_one a)
    refine ⟨haV, ?_⟩
    have hz : a ∈ secondCenterSubgroup Qb := (k1471r2_mem_secondCenter_iff Qb a).mpr
      ⟨ha, fun g hg h hh => hcomm a haV g hg h hh⟩
    have h3 := (hok Qb hQ (Subgroup.le_normalizer ha)).2
    rw [sup_eq_left.mpr (Subgroup.zpowers_le.mpr ha)] at h3
    have hcen := (k1471r2_mem_center_map (h3 hz)).2 u huQ
    calc u * a * u⁻¹ = a * u * u⁻¹ := by rw [hcen]
      _ = a := by group
  · exfalso
    have hVp : IsPGroup 3 V := fun g => ⟨1, Subtype.ext (by simpa using hVel.2 g.1 g.2)⟩
    have hnorm : a ∈ normalizer (V : Set K) := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        have e : a * h * a⁻¹ = (a * h * a⁻¹ * h⁻¹) * h := by group
        rw [e]
        exact mul_mem (hcc a ha h hh).1 hh
      · intro hh
        have e : (a⁻¹ * (a * h * a⁻¹) * a⁻¹⁻¹ * (a * h * a⁻¹)⁻¹) * (a * h * a⁻¹) = h := by group
        rw [← e]
        exact mul_mem (hcc a⁻¹ (inv_mem ha) (a * h * a⁻¹) hh).1 hh
    have hSQ : V ⊔ zpowers a ≤ Qb := sup_le hVQ (Subgroup.zpowers_le.mpr ha)
    have hS : ∀ v ∈ V, v ∈ secondCenterSubgroup (V ⊔ zpowers a) := fun v hv =>
      (k1471r2_mem_secondCenter_iff _ v).mpr ⟨Subgroup.mem_sup_left hv, fun g hg h hh =>
        hcomm v hv g (hSQ hg) h (hSQ hh)⟩
    have hcen := (hok V hVp hnorm).1
    obtain ⟨v, hv, hne⟩ := houtside a ha haT
    exact hne (by rw [hcen v (hS v hv)]; group)

private theorem k1471r3_lift_conj {G : Type} [Group G] {L : Subgroup G} {x : G} {l : ↥L}
    (hinner : ∀ y ∈ L, (x * y * x⁻¹) * ((l : G) * y * (l : G)⁻¹)⁻¹ ∈ pCoreOf 2 L) (y : ↥L) :
    ∃ y' : ↥L, (y' : G) = x * y * x⁻¹ ∧ (QuotientGroup.mk y' : Bar2 L) =
      QuotientGroup.mk l * QuotientGroup.mk y * (QuotientGroup.mk l)⁻¹ := by
  obtain ⟨w, hw, hwe⟩ := hinner y y.2
  refine ⟨w * (l * y * l⁻¹), ?_, ?_⟩
  · have hwe' : (w : G) = (x * y * x⁻¹) * ((l : G) * y * (l : G)⁻¹)⁻¹ := hwe
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hwe']
    group
  · rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff w).mpr hw, one_mul]
    simp

private theorem k1471r3_lift_norm {G : Type} [Group G] {L : Subgroup G} {x : G} (hx3 : x ^ 3 = 1)
    {l : ↥L} {c : ↥L → ↥L} (hc1 : ∀ y, (c y : G) = x * y * x⁻¹)
    (hc2 : ∀ y, (QuotientGroup.mk (c y) : Bar2 L) =
      QuotientGroup.mk l * QuotientGroup.mk y * (QuotientGroup.mk l)⁻¹)
    {S : Subgroup (Bar2 L)} (haS : (QuotientGroup.mk l : Bar2 L) ∈ S) :
    x ∈ normalizer (((S.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥L))).map L.subtype :
      Subgroup G) : Set G) := by
  set N := (S.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥L))).map L.subtype
  have fwd : ∀ z ∈ N, x * z * x⁻¹ ∈ N := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨c y, ?_, hc1 y⟩
    show (QuotientGroup.mk (c y) : Bar2 L) ∈ S
    rw [hc2]
    exact S.mul_mem (S.mul_mem haS hy) (S.inv_mem haS)
  rw [mem_normalizer_iff]
  intro z
  refine ⟨fwd z, fun hz => ?_⟩
  have h3 : x * (x * (x * z * x⁻¹) * x⁻¹) * x⁻¹ = z := by
    have hxxx : x * x * x = 1 := by rw [← pow_three']; exact hx3
    calc _ = (x * x * x) * z * (x * x * x)⁻¹ := by group
      _ = z := by rw [hxxx]; group
  rw [← h3]
  exact fwd _ (fwd _ hz)

private theorem k1471r3_lift_sylow {G : Type} [Group G] [Finite G] {x : G} (hx3 : x ^ 3 = 1)
    {N : Subgroup G} (hxN : x ∈ normalizer (N : Set G)) :
    ∃ T : Subgroup G, x ∈ T ∧ CFSG.ABGLocalTools.IsSylowOf 3 (T ⊓ N) N := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set H := N ⊔ zpowers x
  have hxH : x ∈ H := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hX : IsPGroup 3 (zpowers x) := by
    refine IsPGroup.of_card_dvd_pow (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one hx3
  obtain ⟨P, hP⟩ := (hX.comap_subtype (K := H)).exists_le_sylow
  have hT : CFSG.ABGLocalTools.IsSylowOf 3 ((P : Subgroup ↥H).map H.subtype) H := ⟨P, rfl⟩
  refine ⟨(P : Subgroup ↥H).map H.subtype,
    ⟨⟨x, hxH⟩, hP (Subgroup.mem_comap.mpr (Subgroup.mem_zpowers x)), rfl⟩, ?_⟩
  exact hT.inf_of_le_normalizer le_sup_left
    (sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hxN))

private theorem k1471r3_lift_map {G : Type} [Group G] [Finite G] {L : Subgroup G}
    {S : Subgroup (Bar2 L)} (hS : IsPGroup 3 S) {St : Subgroup ↥L}
    (hSyl : CFSG.ABGLocalTools.IsSylowOf 3 St (S.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥L)))) :
    St.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) = S := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  refine le_antisymm (Subgroup.map_le_iff_le_comap.mpr hSyl.le) ?_
  have hker : π.ker ≤ S.comap π := fun z hz => by
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hz]
    exact S.one_mem
  have h1 := Subgroup.relIndex_map_map π St (S.comap π)
  rw [Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _),
    sup_eq_left.mpr hker] at h1
  have h2 : (St ⊔ π.ker).relIndex (S.comap π) ∣ St.relIndex (S.comap π) :=
    Subgroup.relIndex_dvd_of_le_left _ le_sup_left
  have h3 : ¬ 3 ∣ St.relIndex (S.comap π) := (CFSG.ABGLocalTools.isSylowOf_iff.mp hSyl).2.2
  obtain ⟨n, hn⟩ := hS.index ((St.map π).subgroupOf S)
  have hn' : (St.map π).relIndex S = 3 ^ n := hn
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · exact Subgroup.relIndex_eq_one.mp (by simpa using hn')
  · exact absurd ((dvd_pow_self 3 hpos.ne').trans (hn' ▸ h1 ▸ h2)) h3

private theorem k1471r3_lift {G : Type} [Group G] [Finite G] {L : Subgroup G} {x : G}
    (hx3 : x ^ 3 = 1) {l : ↥L}
    (hinner : ∀ y ∈ L, (x * y * x⁻¹) * ((l : G) * y * (l : G)⁻¹)⁻¹ ∈ pCoreOf 2 L)
    {S : Subgroup (Bar2 L)} (hS : IsPGroup 3 S) (haS : (QuotientGroup.mk l : Bar2 L) ∈ S) :
    ∃ (St : Subgroup ↥L) (a' : ↥L), IsPGroup 3 St ∧ a' ∈ St ∧
      (QuotientGroup.mk a' : Bar2 L) = QuotientGroup.mk l ∧
      (∀ y ∈ St, (QuotientGroup.mk y : Bar2 L) = 1 → y = 1) ∧
      St.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) = S ∧
      ∀ y ∈ St, x * (y : G) * x⁻¹ = (a' : G) * (y : G) * (a' : G)⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  choose c hc1 hc2 using k1471r3_lift_conj hinner
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  set Kg : Subgroup ↥L := S.comap π
  obtain ⟨T, hxT, hTsyl⟩ := k1471r3_lift_sylow hx3 (k1471r3_lift_norm hx3 hc1 hc2 haS)
  have hmap : (T.subgroupOf L ⊓ Kg).map L.subtype = T ⊓ Kg.map L.subtype := by
    rw [Subgroup.map_inf _ _ _ L.subtype_injective, Subgroup.subgroupOf_map_subtype, inf_assoc,
      inf_eq_right.mpr (Subgroup.map_subtype_le Kg)]
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 3 (T.subgroupOf L ⊓ Kg) Kg :=
    (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff L).mp (hmap ▸ hTsyl)
  have hSt3 : IsPGroup 3 (T.subgroupOf L ⊓ Kg : Subgroup ↥L) := hSyl.isPGroup
  have hinj : ∀ y ∈ (T.subgroupOf L ⊓ Kg : Subgroup ↥L), (QuotientGroup.mk y : Bar2 L) = 1 →
      y = 1 := fun y hy hy1 =>
    Subgroup.disjoint_def.mp (IsPGroup.disjoint_of_ne 3 2 (by norm_num) _ _ hSt3
      CFSG.pCore_isPGroup) hy ((QuotientGroup.eq_one_iff y).mp hy1)
  have hSmap := k1471r3_lift_map hS hSyl
  obtain ⟨a', ha'St, ha'eq⟩ : (QuotientGroup.mk l : Bar2 L) ∈ (T.subgroupOf L ⊓ Kg).map π :=
    hSmap ▸ haS
  refine ⟨T.subgroupOf L ⊓ Kg, a', hSt3, ha'St, ha'eq, hinj, hSmap, fun y hy => ?_⟩
  have hcy : c y ∈ (T.subgroupOf L ⊓ Kg : Subgroup ↥L) := by
    refine ⟨?_, ?_⟩
    · show ((c y : ↥L) : G) ∈ T
      rw [hc1]
      exact T.mul_mem (T.mul_mem hxT hy.1) (T.inv_mem hxT)
    · show (QuotientGroup.mk (c y) : Bar2 L) ∈ S
      rw [hc2]
      exact S.mul_mem (S.mul_mem haS hy.2) (S.inv_mem haS)
  have h2 : a' * y * a'⁻¹ ∈ (T.subgroupOf L ⊓ Kg : Subgroup ↥L) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ ha'St hy) (Subgroup.inv_mem _ ha'St)
  have hq : (QuotientGroup.mk (c y * (a' * y * a'⁻¹)⁻¹) : Bar2 L) = 1 := by
    have ha'eq' : (QuotientGroup.mk a' : Bar2 L) = QuotientGroup.mk l := ha'eq
    simp [QuotientGroup.mk_mul, hc2, ha'eq']
  have hcy2 : c y = a' * y * a'⁻¹ :=
    mul_inv_eq_one.mp (hinj _ (Subgroup.mul_mem _ hcy (Subgroup.inv_mem _ h2)) hq)
  rw [← hc1, hcy2]
  rfl

private theorem k1471r3_main_sec_iff {K : Type} [Group K] (T : Subgroup K) (s : K) :
    s ∈ secondCenterSubgroup T ↔ ∃ _ : s ∈ T, ∀ g ∈ T, ∀ h ∈ T,
      h * (s * g * s⁻¹ * g⁻¹) = (s * g * s⁻¹ * g⁻¹) * h := by
  unfold secondCenterSubgroup
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨u.2, fun g hg h hh => ?_⟩
    have h1 := Subgroup.mem_upperCentralSeries_succ_iff.1 hu ⟨g, hg⟩
    rw [Subgroup.upperCentralSeries_one] at h1
    simpa [commutatorElement_def] using congrArg Subtype.val (Subgroup.mem_center_iff.1 h1 ⟨h, hh⟩)
  · rintro ⟨hs, h⟩
    refine ⟨⟨s, hs⟩, Subgroup.mem_upperCentralSeries_succ_iff.2 fun y => ?_, rfl⟩
    rw [Subgroup.upperCentralSeries_one]
    exact Subgroup.mem_center_iff.2 fun g => Subtype.ext (h y y.2 g g.2)

private theorem k1471r3_main_ctr_iff {K : Type} [Group K] (T : Subgroup K) (s : K) :
    s ∈ (Subgroup.center ↥T).map T.subtype ↔ s ∈ T ∧ ∀ h ∈ T, h * s = s * h := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨u.2, fun h hh => ?_⟩
    simpa using congrArg Subtype.val (Subgroup.mem_center_iff.1 hu ⟨h, hh⟩)
  · rintro ⟨hs, h⟩
    exact ⟨⟨s, hs⟩, Subgroup.mem_center_iff.2 fun g => Subtype.ext (h g g.2), rfl⟩

private theorem k1471r3_main_step {G : Type} [Group G] {L : Subgroup G} {x : G} {l : ↥L}
    (hinner : ∀ y ∈ L, (x * y * x⁻¹) * ((l : G) * y * (l : G)⁻¹)⁻¹ ∈ pCoreOf 2 L) (y : ↥L) :
    ∃ y' : ↥L, (y' : G) = x * y * x⁻¹ ∧ (QuotientGroup.mk y' : Bar2 L) =
      QuotientGroup.mk l * QuotientGroup.mk y * (QuotientGroup.mk l)⁻¹ := by
  obtain ⟨o, ho, hoe⟩ := hinner y y.2
  refine ⟨o * (l * y * l⁻¹), ?_, ?_⟩
  · have h1 : (o : G) = x * y * x⁻¹ * ((l : G) * y * (l : G)⁻¹)⁻¹ := hoe
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, h1]
    exact inv_mul_cancel_right _ _
  · simp [(QuotientGroup.eq_one_iff o).2 ho]

private theorem k1471r3_main_pow {G : Type} [Group G] {L : Subgroup G} {x : G} {l : ↥L}
    (hinner : ∀ y ∈ L, (x * y * x⁻¹) * ((l : G) * y * (l : G)⁻¹)⁻¹ ∈ pCoreOf 2 L) (k : ℕ)
    (y : ↥L) : ∃ y' : ↥L, (y' : G) = x ^ k * y * (x ^ k)⁻¹ ∧ (QuotientGroup.mk y' : Bar2 L) =
      (QuotientGroup.mk l) ^ k * QuotientGroup.mk y * ((QuotientGroup.mk l) ^ k)⁻¹ := by
  induction k generalizing y with
  | zero => exact ⟨y, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨y₁, h1, h2⟩ := ih y
    obtain ⟨y₂, h3, h4⟩ := k1471r3_main_step hinner y₁
    refine ⟨y₂, ?_, ?_⟩
    · rw [h3, h1, pow_succ']
      simp [mul_assoc]
    · rw [h4, h2, pow_succ']
      simp [mul_assoc]

private theorem k1471r3_main_cube {G : Type} [Group G] {L : Subgroup G} {x : G} {l : ↥L}
    (hx3 : x ^ 3 = 1) (hZ : Subgroup.center (Bar2 L) = ⊥)
    (hinner : ∀ y ∈ L, (x * y * x⁻¹) * ((l : G) * y * (l : G)⁻¹)⁻¹ ∈ pCoreOf 2 L) :
    (QuotientGroup.mk l : Bar2 L) ^ 3 = 1 := by
  have hc : (QuotientGroup.mk l : Bar2 L) ^ 3 ∈ Subgroup.center (Bar2 L) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨y', hy', hπ⟩ := k1471r3_main_pow hinner 3 y
    rw [hx3] at hy'
    have hyy : y' = y := Subtype.ext (by simpa using hy')
    rw [hyy] at hπ
    exact (eq_mul_inv_iff_mul_eq.1 hπ)
  rw [hZ] at hc
  exact hc

private theorem k1471r3_main_zpowers {K : Type} [Group K] {a : K} (h : a ^ 3 = 1) :
    IsPGroup 3 (Subgroup.zpowers a) := by
  rintro ⟨g, k, rfl⟩
  refine ⟨1, Subtype.ext ?_⟩
  simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h, one_zpow]

private theorem k1471r3_main_normalizer {K : Type} [Group K] {A : Subgroup K} {d : K}
    (hd : ∀ a ∈ A, a * d = d * a) : Subgroup.zpowers d ≤ normalizer (A : Set K) := by
  rw [Subgroup.le_normalizer_iff]
  rintro _ ⟨i, rfl⟩ k hk
  have hc : Commute d k := (hd k hk).symm
  rw [(hc.zpow_left i).mul_inv_cancel]
  exact hk

private theorem k1471r3_main_mem_sup {K : Type} [Group K] {A : Subgroup K} {d : K}
    (hd : ∀ a ∈ A, a * d = d * a) {g : K} (hg : g ∈ A ⊔ Subgroup.zpowers d) :
    ∃ a ∈ A, ∃ i : ℤ, g = a * d ^ i := by
  have hg' : g ∈ ((A ⊔ Subgroup.zpowers d : Subgroup K) : Set K) := hg
  rw [Subgroup.coe_mul_of_right_le_normalizer_left A _ (k1471r3_main_normalizer hd)] at hg'
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hg'
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
  exact ⟨a, ha, i, rfl⟩

private theorem k1471r3_main_central {K : Type} [Group K] {A : Subgroup K} {d : K}
    (hd : ∀ a ∈ A, a * d = d * a) {g : K} (hg : g ∈ A ⊔ Subgroup.zpowers d) :
    g * d = d * g := by
  obtain ⟨a, ha, i, rfl⟩ := k1471r3_main_mem_sup hd hg
  have hc : Commute a d := hd a ha
  exact (hc.mul_left (Commute.self_zpow d i).symm).eq

private theorem k1471r3_main_z2_lift {K : Type} [Group K] {A : Subgroup K} {d z : K}
    (hd : ∀ a ∈ A, a * d = d * a) (hz : z ∈ secondCenterSubgroup A) :
    z ∈ secondCenterSubgroup (A ⊔ Subgroup.zpowers d) := by
  rw [k1471r3_main_sec_iff] at hz ⊢
  obtain ⟨hzA, hz⟩ := hz
  refine ⟨Subgroup.mem_sup_left hzA, fun g hg h hh => ?_⟩
  obtain ⟨a₁, ha₁, i, rfl⟩ := k1471r3_main_mem_sup hd hg
  obtain ⟨a₂, ha₂, j, rfl⟩ := k1471r3_main_mem_sup hd hh
  have hzc : Commute z d := hd z hzA
  have hzd : Commute z (d ^ i) := hzc.zpow_right i
  have h1 : d ^ i * z⁻¹ * (d ^ i)⁻¹ = z⁻¹ := hzd.inv_left.symm.mul_inv_cancel
  have hc : z * (a₁ * d ^ i) * z⁻¹ * (a₁ * d ^ i)⁻¹ = z * a₁ * z⁻¹ * a₁⁻¹ := by
    calc z * (a₁ * d ^ i) * z⁻¹ * (a₁ * d ^ i)⁻¹
        = z * a₁ * (d ^ i * z⁻¹ * (d ^ i)⁻¹) * a₁⁻¹ := by simp only [mul_inv_rev, mul_assoc]
      _ = z * a₁ * z⁻¹ * a₁⁻¹ := by rw [h1]
  have hcA : z * a₁ * z⁻¹ * a₁⁻¹ ∈ A :=
    A.mul_mem (A.mul_mem (A.mul_mem hzA ha₁) (A.inv_mem hzA)) (A.inv_mem ha₁)
  have hcc : Commute (z * a₁ * z⁻¹ * a₁⁻¹) d := hd _ hcA
  have hcd : Commute (z * a₁ * z⁻¹ * a₁⁻¹) (d ^ j) := hcc.zpow_right j
  rw [hc]
  calc a₂ * d ^ j * (z * a₁ * z⁻¹ * a₁⁻¹) = a₂ * ((z * a₁ * z⁻¹ * a₁⁻¹) * d ^ j) := by
        rw [mul_assoc, ← hcd.eq]
    _ = (a₂ * (z * a₁ * z⁻¹ * a₁⁻¹)) * d ^ j := (mul_assoc _ _ _).symm
    _ = ((z * a₁ * z⁻¹ * a₁⁻¹) * a₂) * d ^ j := by rw [hz a₁ ha₁ a₂ ha₂]
    _ = (z * a₁ * z⁻¹ * a₁⁻¹) * (a₂ * d ^ j) := mul_assoc _ _ _

private theorem k1471r3_main_coreA {K : Type} [Group K] {A : Subgroup K} {a d x z : K}
    (hd : ∀ y ∈ A, y * d = d * y) (hx : x = a * d) (hz : z ∈ secondCenterSubgroup A)
    (h2 : ∀ y ∈ secondCenterSubgroup (A ⊔ Subgroup.zpowers d), x * y = y * x) :
    a * z = z * a := by
  obtain ⟨hzA, -⟩ := (k1471r3_main_sec_iff A z).1 hz
  have h1 := h2 z (k1471r3_main_z2_lift hd hz)
  have h3 := hd z hzA
  rw [hx] at h1
  apply mul_right_cancel (b := d)
  calc a * z * d = a * (z * d) := mul_assoc _ _ _
    _ = a * (d * z) := by rw [h3]
    _ = a * d * z := (mul_assoc _ _ _).symm
    _ = z * (a * d) := h1
    _ = z * a * d := (mul_assoc _ _ _).symm

private theorem k1471r3_main_coreB {K : Type} [Group K] {A : Subgroup K} {a d x : K}
    (hd : ∀ y ∈ A, y * d = d * y) (hx : x = a * d) (ha : a ∈ secondCenterSubgroup A)
    (h3 : x ∈ secondCenterSubgroup (A ⊔ Subgroup.zpowers d) →
      x ∈ (Subgroup.center ↥(A ⊔ Subgroup.zpowers d)).map (A ⊔ Subgroup.zpowers d).subtype) :
    ∀ y ∈ A, y * a = a * y := by
  have haP := k1471r3_main_z2_lift hd ha
  have hdP : d ∈ secondCenterSubgroup (A ⊔ Subgroup.zpowers d) := by
    rw [k1471r3_main_sec_iff]
    refine ⟨Subgroup.mem_sup_right (Subgroup.mem_zpowers d), fun g hg h hh => ?_⟩
    have : d * g * d⁻¹ * g⁻¹ = 1 := by
      rw [← k1471r3_main_central hd hg, mul_inv_cancel_right, mul_inv_cancel]
    rw [this, mul_one, one_mul]
  have hxP : x ∈ secondCenterSubgroup (A ⊔ Subgroup.zpowers d) := by
    rw [hx]
    exact Subgroup.mul_mem _ haP hdP
  obtain ⟨-, hxc⟩ := (k1471r3_main_ctr_iff _ x).1 (h3 hxP)
  intro y hy
  have h1 := hxc y (Subgroup.mem_sup_left hy)
  have h2 := hd y hy
  rw [hx] at h1
  apply mul_right_cancel (b := d)
  calc y * a * d = y * (a * d) := mul_assoc _ _ _
    _ = a * d * y := h1
    _ = a * (d * y) := mul_assoc _ _ _
    _ = a * (y * d) := by rw [h2]
    _ = a * y * d := (mul_assoc _ _ _).symm

private theorem k1471r3_main_inj {G : Type} [Group G] {L : Subgroup G} {St : Subgroup ↥L}
    (hinj : ∀ y ∈ St, (QuotientGroup.mk y : Bar2 L) = 1 → y = 1) {u v : ↥L} (hu : u ∈ St)
    (hv : v ∈ St) (h : (QuotientGroup.mk u : Bar2 L) = QuotientGroup.mk v) : u = v :=
  inv_mul_eq_one.1 (hinj (u⁻¹ * v) (St.mul_mem (St.inv_mem hu) hv) (by simp [h]))

private theorem k1471r3_main_dict {G : Type} [Group G] {L : Subgroup G} {St : Subgroup ↥L}
    {S : Subgroup (Bar2 L)} (hinj : ∀ y ∈ St, (QuotientGroup.mk y : Bar2 L) = 1 → y = 1)
    (hmap : St.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) = S) {z : ↥L} (hz : z ∈ St)
    (h : (QuotientGroup.mk z : Bar2 L) ∈ secondCenterSubgroup S) :
    z ∈ secondCenterSubgroup St := by
  rw [k1471r3_main_sec_iff] at h ⊢
  obtain ⟨-, h⟩ := h
  refine ⟨hz, fun g hg h' hh' => ?_⟩
  have hgS : (QuotientGroup.mk g : Bar2 L) ∈ S := by
    rw [← hmap]; exact Subgroup.mem_map_of_mem _ hg
  have hhS : (QuotientGroup.mk h' : Bar2 L) ∈ S := by
    rw [← hmap]; exact Subgroup.mem_map_of_mem _ hh'
  have h1 := h _ hgS _ hhS
  have hc : z * g * z⁻¹ * g⁻¹ ∈ St :=
    St.mul_mem (St.mul_mem (St.mul_mem hz hg) (St.inv_mem hz)) (St.inv_mem hg)
  refine k1471r3_main_inj hinj (St.mul_mem hh' hc) (St.mul_mem hc hh') ?_
  simpa using h1

private theorem k1471r3_main_map_sec {K K' : Type} [Group K] [Group K'] (f : K →* K')
    {T : Subgroup K} {z : K} (hz : z ∈ secondCenterSubgroup T) :
    f z ∈ secondCenterSubgroup (T.map f) := by
  rw [k1471r3_main_sec_iff] at hz ⊢
  obtain ⟨hzT, hz⟩ := hz
  refine ⟨Subgroup.mem_map_of_mem f hzT, ?_⟩
  rintro _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩
  simpa only [map_mul, map_inv] using congrArg f (hz g hg h hh)

private theorem k1471r3_main_pow_three {K : Type} [Group K] {X : Subgroup K} {x : K}
    (hX3 : Nat.card X = 3) (hx : x ∈ X) : x ^ 3 = 1 := by
  have h := pow_card_eq_one' (G := X) (x := ⟨x, hx⟩)
  rw [hX3] at h
  simpa using congrArg Subtype.val h

private theorem k1471r3_main_zpowers_eq {K : Type} [Group K] {X : Subgroup K} {x : K}
    (hX3 : Nat.card X = 3) (hx : x ∈ X) (hx1 : x ≠ 1) : Subgroup.zpowers x = X := by
  have : Finite X := Nat.finite_of_card_ne_zero (by rw [hX3]; norm_num)
  apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hx)
  rw [hX3, Nat.card_zpowers]
  rcases (Nat.dvd_prime Nat.prime_three).1
    (orderOf_dvd_of_pow_eq_one (k1471r3_main_pow_three hX3 hx)) with h | h
  · exact absurd (orderOf_eq_one_iff.1 h) hx1
  · exact h.ge

private theorem k1471r3_main_abstract {K : Type} [Group K] {A X M : Subgroup K} {x a : K}
    (h69X : ∀ P₀ : Subgroup K, P₀ ≤ M → IsPGroup 3 P₀ → X ≤ P₀ →
      (∀ y ∈ secondCenterSubgroup P₀, ∀ x' ∈ X, x' * y = y * x') ∧
        (X ≤ secondCenterSubgroup P₀ → X ≤ (Subgroup.center ↥P₀).map P₀.subtype))
    (hAM : A ≤ M) (hXM : X ≤ M) (hA3 : IsPGroup 3 A) (hX3 : IsPGroup 3 X)
    (hXz : X = Subgroup.zpowers x) (haA : a ∈ A)
    (hact : ∀ y ∈ A, x * y * x⁻¹ = a * y * a⁻¹) :
    (∀ z ∈ secondCenterSubgroup A, a * z = z * a) ∧
      (a ∈ secondCenterSubgroup A → ∀ y ∈ A, y * a = a * y) := by
  obtain ⟨d, hd⟩ : ∃ d : K, d = a⁻¹ * x := ⟨_, rfl⟩
  have hxd : x = a * d := by rw [hd, mul_inv_cancel_left]
  have hdA : ∀ y ∈ A, y * d = d * y := by
    intro y hy
    have h1 : x * y = a * y * a⁻¹ * x := mul_inv_eq_iff_eq_mul.1 (hact y hy)
    rw [hd]
    calc y * (a⁻¹ * x) = a⁻¹ * (a * y * a⁻¹ * x) := by group
      _ = a⁻¹ * (x * y) := by rw [h1]
      _ = a⁻¹ * x * y := by group
  have hxX : x ∈ X := hXz ▸ Subgroup.mem_zpowers x
  have hxP : x ∈ A ⊔ Subgroup.zpowers d := by
    rw [hxd]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left haA)
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers d))
  have hPeq : A ⊔ X = A ⊔ Subgroup.zpowers d := by
    refine le_antisymm (sup_le le_sup_left ?_) (sup_le le_sup_left ?_)
    · rw [hXz, Subgroup.zpowers_le]
      exact hxP
    · rw [Subgroup.zpowers_le, hd]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (A.inv_mem haA))
        (Subgroup.mem_sup_right hxX)
  have hnorm : X ≤ normalizer (A : Set K) := by
    rw [hXz, Subgroup.zpowers_le, hxd]
    exact Subgroup.mul_mem _ (Subgroup.le_normalizer haA)
      (k1471r3_main_normalizer hdA (Subgroup.mem_zpowers d))
  obtain ⟨h2, h3⟩ := h69X (A ⊔ X) (sup_le hAM hXM) (hA3.to_sup_of_normal_left' hX3 hnorm)
    le_sup_right
  rw [hPeq] at h2 h3
  refine ⟨fun z hz => k1471r3_main_coreA hdA hxd hz fun y hy => h2 y hy x hxX, fun ha' => ?_⟩
  refine k1471r3_main_coreB hdA hxd ha' fun hxP' => h3 ?_ hxX
  rw [hXz, Subgroup.zpowers_le]
  exact hxP'

private theorem k1471r3_main_ok {G : Type} [Group G] [Finite G] {L M X : Subgroup G} {x : G}
    {l : ↥L} (hLM : L ≤ M) (hXM : X ≤ M) (hX3 : Nat.card X = 3) (hxX : x ∈ X) (hx1 : x ≠ 1)
    (hx3 : x ^ 3 = 1)
    (h69X : ∀ P₀ : Subgroup G, P₀ ≤ M → IsPGroup 3 P₀ → X ≤ P₀ →
      (∀ y ∈ secondCenterSubgroup P₀, ∀ x' ∈ X, x' * y = y * x') ∧
        (X ≤ secondCenterSubgroup P₀ → X ≤ (Subgroup.center ↥P₀).map P₀.subtype))
    (hinner : ∀ y ∈ L, (x * y * x⁻¹) * ((l : G) * y * (l : G)⁻¹)⁻¹ ∈ pCoreOf 2 L)
    {S : Subgroup (Bar2 L)} (hS : IsPGroup 3 S) (haS : (QuotientGroup.mk l : Bar2 L) ∈ S) :
    (∀ z ∈ secondCenterSubgroup S, (QuotientGroup.mk l : Bar2 L) * z = z * QuotientGroup.mk l) ∧
      ((QuotientGroup.mk l : Bar2 L) ∈ secondCenterSubgroup S →
        (QuotientGroup.mk l : Bar2 L) ∈ (Subgroup.center ↥S).map S.subtype) := by
  obtain ⟨St, a', hSt3, ha'St, hπa', hinj, hmap, hact⟩ := k1471r3_lift hx3 hinner hS haS
  have hX3p : IsPGroup 3 X := IsPGroup.of_card (n := 1) (by rw [hX3, pow_one])
  obtain ⟨hA, hB⟩ := k1471r3_main_abstract h69X
    ((Subgroup.map_subtype_le St).trans hLM) hXM (hSt3.map L.subtype) hX3p
    (k1471r3_main_zpowers_eq hX3 hxX hx1).symm (Subgroup.mem_map_of_mem _ ha'St)
    (by rintro _ ⟨y, hy, rfl⟩; exact hact y hy)
  rw [← hπa']
  refine ⟨fun s hs => ?_, fun hs => ?_⟩
  · obtain ⟨hsS, -⟩ := (k1471r3_main_sec_iff S s).1 hs
    obtain ⟨z, hz, rfl⟩ : s ∈ St.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := hmap.symm ▸ hsS
    have h1 := hA _ (k1471r3_main_map_sec L.subtype (k1471r3_main_dict hinj hmap hz hs))
    exact congrArg (fun u : ↥L => (QuotientGroup.mk u : Bar2 L)) (Subtype.ext h1)
  · have h1 := hB (k1471r3_main_map_sec L.subtype (k1471r3_main_dict hinj hmap ha'St hs))
    rw [k1471r3_main_ctr_iff]
    refine ⟨hπa' ▸ haS, fun h hh => ?_⟩
    obtain ⟨y, hy, rfl⟩ : h ∈ St.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := hmap.symm ▸ hh
    exact congrArg (fun u : ↥L => (QuotientGroup.mk u : Bar2 L))
      (Subtype.ext (h1 _ (Subgroup.mem_map_of_mem _ hy)))

theorem ok69_of_inner_action {G : Type} [Group G] [Finite G] {D : Data G}
    (hSg : SigmaStd D) (h69 : R6_9 D) :
    ∀ L Q P : Subgroup G, Cex856 D L Q P → Subgroup.center (Bar2 L) = ⊥ →
      ∀ X : Subgroup G, X ≤ P → Nat.card X = 3 →
        ¬ normalizer (X : Set G) ≤ D.M → HasGammaE9 D X →
          ∀ x ∈ X, x ≠ 1 → ∀ l : ↥L,
            (∀ y ∈ L, (x * y * x⁻¹) * ((l : G) * y * (l : G)⁻¹)⁻¹ ∈ pCoreOf 2 L) →
              Ok69 (QuotientGroup.mk l : Bar2 L) := by
  intro L Q P hc hZbar X hXP hX3 hN hE x hx hx1 l hinner
  obtain ⟨E, hEM, hEel, hEcard, hEΓ, hEN⟩ := hE
  have hLM : L ≤ D.M := hc.mem.1.le
  have hXM : X ≤ D.M := hXP.trans hc.sylowP.le
  have hsig : D.sig ⊆ D.sig1 :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.sig_subset_sig1 hSg
      (CFSG.LocalAnalysis.UniquenessCase.UC6S846.not_solvable_of_mem_calC hc.mem)
  have hx3 : x ^ 3 = 1 := k1471r3_main_pow_three hX3 hx
  have hcube := k1471r3_main_cube hx3 hZbar hinner
  intro R hR haR
  exact k1471r3_main_ok hLM hXM hX3 hx hx1 hx3
    (fun P₀ hP₀M hP₀3 hXP₀ => (h69 hsig 3 Nat.prime_three (by norm_num) E hEM hEel hEcard hEΓ 3 X
      Nat.prime_three hXM hX3 hEN hN P₀ hP₀M hP₀3 hXP₀).2) hinner
    (hR.to_sup_of_normal_left' (k1471r3_main_zpowers hcube) (Subgroup.zpowers_le.2 haR))
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))

theorem three_le_pRank_of_lieModel_char_three
    {Y : Type} [Group Y] [Finite Y] {f : ℕ}
    (hY : LieModel Y .G2 0 3 f ∨ LieModel Y .trialityD4 0 3 f) :
    3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Y) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases hY with hY | hY
  · have hm := hY.chevalleyExceptionalModel (by decide)
    have h3 := CFSG.SectionRank.three_mul_le_pRank_of_G2Model (p := 3) (f := f) hm.2
    have hf : 1 ≤ f := hm.1.2.1
    omega
  · have hm := hY.chevalleyExceptionalModel (by decide)
    have h4 := CFSG.SectionRank.four_le_pRank_of_trialityD4Model (p := 3) (f := f) hm.1.2.1 hm.2
    omega

theorem p_ne_three_of_cex856_g2
    {G : Type} [Group G] [Finite G] {D : Data G} {L Q P : Subgroup G}
    (hc : Cex856 D L Q P) {p f : ℕ} (hK : LieModel (Bar2 L) .G2 0 p f) : p ≠ 3 := by
  rintro rfl
  have h3 := three_le_pRank_of_lieModel_char_three (Or.inl hK)
  rw [pRank_bar2_eq_of_odd (Y := L) Nat.prime_three (by norm_num), hc.rank] at h3
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
