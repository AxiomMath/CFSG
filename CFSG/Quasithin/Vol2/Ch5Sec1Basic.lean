module

public import CFSG.Quasithin.Vol2.Ch5Statements
public import CFSG.Quasithin.Vol2.Ch3Sec1Thm318
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.BlueprintB2Bridge
public import CFSG.Quasithin.Background.F1Rank
import CFSG.Adapters.LieModelSimple
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.H13.StatementsL1

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped Pointwise

@[expose] def L2RankOneSylowFact : Prop :=
  ∀ (X : Type) [Group X] (n : ℕ), 2 ≤ n → LieModel X .PSL 2 2 n → IsRankOneSylow X

section General

variable {G : Type} [Group G]

theorem isSimpleGroup_of_lieModel_PSL2 {X : Type} [Group X] {f : ℕ}
    (h : LieModel X .PSL 2 2 f) : IsSimpleGroup X :=
  CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h

theorem isQuasisimple_of_isSimpleGroup_of_isPerfect {Q : Type*} [Group Q] [hs : IsSimpleGroup Q]
    [hp : Group.IsPerfect Q] : CFSG.IsQuasisimple Q := by
  have hnc : ¬ IsMulCommutative Q := Group.IsPerfect.not_isMulCommutative Q
  have hZ : Subgroup.center Q = ⊥ := by
    rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
    · exact h
    · exact absurd (Subgroup.center_eq_top_iff.mp h) hnc
  let e : Q ⧸ Subgroup.center Q ≃* Q :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have : Nontrivial (Q ⧸ Subgroup.center Q) := e.toEquiv.nontrivial
  refine ⟨hp, IsSimpleGroup.isSimpleGroup_of_surjective e.symm.toMonoidHom e.symm.surjective, ?_⟩
  obtain ⟨a, b, hab⟩ : ∃ a b : Q, a * b ≠ b * a := by
    by_contra hall
    exact hnc ⟨⟨fun a b => by_contra fun h => hall ⟨a, b, h⟩⟩⟩
  exact ⟨e.symm a, e.symm b, fun h => hab (e.symm.injective (by rw [map_mul, map_mul]; exact h))⟩

theorem pow_mul_mem_of_mem_normalizer {L : Subgroup G} {x t : G} (hx : x ∈ L)
    (ht : t ∈ Subgroup.normalizer (L : Set G)) (m : ℕ) : ∃ x' ∈ L, (x * t) ^ m = x' * t ^ m := by
  induction m with
  | zero => exact ⟨1, L.one_mem, by simp⟩
  | succ m ih =>
    obtain ⟨x', hx', he⟩ := ih
    refine ⟨x' * (t ^ m * x * (t ^ m)⁻¹), L.mul_mem hx' ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ ht m) x).mp hx
    · rw [pow_succ, he]
      group

theorem eq_oTwoUpper_sup_of_isSylowTwoOf' [Finite G] {H T : Subgroup G}
    (hT : IsSylowTwoOf T H) : H = oTwoUpper H ⊔ T := by
  classical
  have hNH : H ≤ Subgroup.normalizer (oTwoUpper H : Set G) := le_normalizer_oTwoUpper H
  have hnorm : ((oTwoUpper H).subgroupOf H).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hNH
  have hQ : IsPGroup 2 (↥H ⧸ (oTwoUpper H).subgroupOf H) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper H x.2
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr hk
  set f : ↥H →* (↥H ⧸ (oTwoUpper H).subgroupOf H) := QuotientGroup.mk' _ with hf
  have hdvd := Subgroup.index_map_dvd (H := T.subgroupOf H) (f := f)
    (QuotientGroup.mk'_surjective _)
  obtain ⟨n, hn⟩ := hQ.index ((T.subgroupOf H).map f)
  have hodd : ¬ 2 ∣ (T.subgroupOf H).index := hT.2.2
  have h1 : ((T.subgroupOf H).map f).index = 1 := by
    rcases n with _ | n
    · simpa using hn
    · exfalso
      refine hodd ?_
      rw [hn] at hdvd
      exact (dvd_pow_self 2 (Nat.succ_ne_zero n)).trans hdvd
  rw [Subgroup.index_eq_one] at h1
  refine le_antisymm (fun x hx => ?_) (sup_le (oTwoUpper_le H) hT.1)
  have hmem : f ⟨x, hx⟩ ∈ (T.subgroupOf H).map f := by
    rw [h1]
    exact Subgroup.mem_top _
  obtain ⟨t, ht, hteq⟩ := Subgroup.mem_map.mp hmem
  have h2 : (t : ↥H)⁻¹ * ⟨x, hx⟩ ∈ (oTwoUpper H).subgroupOf H := by
    rw [← QuotientGroup.eq]
    exact hteq
  have h3 : (t : G)⁻¹ * x ∈ oTwoUpper H := Subgroup.mem_subgroupOf.mp h2
  have h4 : x = (t : G) * ((t : G)⁻¹ * x) := by group
  have h5 : x ∈ T ⊔ oTwoUpper H := by
    rw [h4]
    exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp ht) h3
  rwa [sup_comm] at h5

theorem IsCh5Module.isTwoReducedIn {T L V : Subgroup G} (hV : IsCh5Module T L V) :
    IsTwoReducedIn (L ⊔ T) V :=
  isTwoReducedIn_iff_isPrimeReduced_subgroupOf.mpr ⟨hV.1, hV.2.1⟩

end General

namespace Hyp5_0_1

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G} {n : ℕ}

theorem T_le_normalizer (h : Hyp5_0_1 G T M L n) : T ≤ Subgroup.normalizer (L : Set G) :=
  h.T_le.trans h.normal

theorem sup_le_M (h : Hyp5_0_1 G T M L n) : L ⊔ T ≤ M := sup_le h.L_le h.T_le

theorem sup_le_normalizer (h : Hyp5_0_1 G T M L n) :
    L ⊔ T ≤ Subgroup.normalizer (L : Set G) :=
  sup_le Subgroup.le_normalizer h.T_le_normalizer

theorem conjClosure_eq (h : Hyp5_0_1 G T M L n) : conjClosure L T = L := by
  apply le_antisymm
  · exact conjClosure_le fun t ht z hz =>
      (Subgroup.mem_normalizer_iff.mp (h.T_le_normalizer ht) z).mp hz
  · exact le_conjClosure L T

theorem isSylowTwoOf (h : Hyp5_0_1 G T M L n) {X : Subgroup G} (hTX : T ≤ X) :
    IsSylowTwoOf T X :=
  isSylowTwoOf_of_isSylowTwo h.sylow hTX

theorem commutator_eq (h : Hyp5_0_1 G T M L n) : ⁅L, L⁆ = L :=
  h.faithful.1.2.1.2.1

theorem isSimple (h : Hyp5_0_1 G T M L n) : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) :=
  isSimpleGroup_of_lieModel_PSL2 h.lie

theorem isQuasisimple (h : Hyp5_0_1 G T M L n) : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) := by
  have := h.isSimple
  have : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr h.commutator_eq
  exact isQuasisimple_of_isSimpleGroup_of_isPerfect

theorem le_pCoreOf_or_eq (h : Hyp5_0_1 G T M L n) {N : Subgroup G} (hNL : N ≤ L)
    (hN : L ≤ Subgroup.normalizer (N : Set G)) : N ≤ pCoreOf 2 L ∨ N = L := by
  have hsimp := h.isSimple
  have hN' : (N.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNL).mpr hN
  have hNb : ((N.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))).Normal :=
    hN'.map _ (QuotientGroup.mk'_surjective _)
  rcases hsimp.eq_bot_or_eq_top_of_normal ((N.subgroupOf L).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) with hb | ht
  · left
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hb
    intro x hx
    have hxN : (⟨x, hNL hx⟩ : ↥L) ∈ N.subgroupOf L := by
      rw [Subgroup.mem_subgroupOf]
      exact hx
    have hxP : (⟨x, hNL hx⟩ : ↥L) ∈ CFSG.Open.pCore 2 ↥L := by
      exact hb hxN
    exact ⟨_, hxP, rfl⟩
  · right
    refine h.faithful.2.1 N hNL hN' fun x hx => ?_
    have hmem : (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) ⟨x, hx⟩ ∈
        (N.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := by
      rw [ht]
      exact Subgroup.mem_top _
    obtain ⟨c, hc, hcx⟩ := hmem
    have ho' : (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) (c⁻¹ * ⟨x, hx⟩) = 1 := by
      rw [map_mul, map_inv, hcx, inv_mul_cancel]
    have ho : c⁻¹ * ⟨x, hx⟩ ∈ CFSG.pCore 2 ↥L := by
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at ho'
    obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup ⟨_, ho⟩
    have hk' : (c⁻¹ * ⟨x, hx⟩) ^ 2 ^ k = 1 := by
      simpa using congrArg Subtype.val hk
    refine ⟨k, ?_⟩
    have hσc : (QuotientGroup.mk' (N.subgroupOf L)) c = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hc
    have hσx : (QuotientGroup.mk' (N.subgroupOf L)) ⟨x, hx⟩ =
        (QuotientGroup.mk' (N.subgroupOf L)) (c⁻¹ * ⟨x, hx⟩) := by
      rw [map_mul, map_inv, hσc, inv_one, one_mul]
    have hpow : (QuotientGroup.mk' (N.subgroupOf L)) ((⟨x, hx⟩ : ↥L) ^ 2 ^ k) = 1 := by
      rw [map_pow, hσx, ← map_pow, hk', map_one]
    have hmemN' : (⟨x, hx⟩ : ↥L) ^ 2 ^ k ∈ N.subgroupOf L := by
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hpow
    rw [Subgroup.mem_subgroupOf] at hmemN'
    simpa using hmemN'

theorem inf_centralizer_le (h : Hyp5_0_1 G T M L n) (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hVL : ⁅V, L⁆ ≠ ⊥) : L ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 L := by
  have hnorm : L ≤ Subgroup.normalizer
      ((L ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro c
    have key : ∀ g ∈ L, ∀ c ∈ L ⊓ Subgroup.centralizer (V : Set G),
        g * c * g⁻¹ ∈ L ⊓ Subgroup.centralizer (V : Set G) := by
      intro g hg c hc
      refine ⟨L.mul_mem (L.mul_mem hg hc.1) (L.inv_mem hg), ?_⟩
      show g * c * g⁻¹ ∈ Subgroup.centralizer (V : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hv' : g⁻¹ * v * g ∈ V := by
        have := (Subgroup.mem_normalizer_iff.mp (hLV (L.inv_mem hg)) v).mp hv
        simpa using this
      have hcomm := Subgroup.mem_centralizer_iff.mp hc.2 _ hv'
      calc v * (g * c * g⁻¹) = g * ((g⁻¹ * v * g) * c) * g⁻¹ := by group
        _ = g * (c * (g⁻¹ * v * g)) * g⁻¹ := by rw [hcomm]
        _ = g * c * g⁻¹ * v := by group
    refine ⟨key g hg c, fun hc => ?_⟩
    simpa [mul_assoc] using key g⁻¹ (L.inv_mem hg) _ hc
  rcases h.le_pCoreOf_or_eq inf_le_left hnorm with hle | heq
  · exact hle
  · exfalso
    apply hVL
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff]
    exact heq.symm.le.trans inf_le_right

omit [Finite G] in
theorem le_normalizer_inf_centralizer (hLV : L ⊔ T ≤ Subgroup.normalizer (V : Set G)) :
    L ⊔ T ≤ Subgroup.normalizer
      (((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  have key : ∀ g ∈ L ⊔ T, ∀ c, c ∈ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) →
      g * c * g⁻¹ ∈ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) := by
    intro g hg c hc
    refine ⟨(L ⊔ T).mul_mem ((L ⊔ T).mul_mem hg hc.1) ((L ⊔ T).inv_mem hg), ?_⟩
    show g * c * g⁻¹ ∈ Subgroup.centralizer (V : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hv' : g⁻¹ * v * g ∈ V := by
      have := (Subgroup.mem_normalizer_iff.mp (hLV ((L ⊔ T).inv_mem hg)) v).mp hv
      simpa using this
    have hcomm := Subgroup.mem_centralizer_iff.mp hc.2 _ hv'
    calc v * (g * c * g⁻¹) = g * ((g⁻¹ * v * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * v * g)) * g⁻¹ := by rw [hcomm]
      _ = g * c * g⁻¹ * v := by group
  intro c
  refine ⟨key g hg c, fun hc => ?_⟩
  simpa [mul_assoc] using key g⁻¹ ((L ⊔ T).inv_mem hg) _ hc

theorem sup_inf_centralizer_eq (h : Hyp5_0_1 G T M L n) (hV : IsCh5Module T L V) :
    (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 (L ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hred := hV.isTwoReducedIn
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans hred.2.1
  have hCL := h.inf_centralizer_le hLV hV.2.2
  have hTN := h.T_le_normalizer
  have hC2 : IsPGroup 2 ↥((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G)) := by
    rintro ⟨x, hxLT, hxC⟩
    have hx : x ∈ ((L : Set G) * (T : Set G)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left L T hTN]
      exact hxLT
    obtain ⟨l, hl, t, ht, rfl⟩ := hx
    obtain ⟨a, ha⟩ := h.sylow.1 ⟨t, ht⟩
    have hta : t ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
    obtain ⟨l', hl', he⟩ := pow_mul_mem_of_mem_normalizer hl (hTN ht) (2 ^ a)
    rw [hta, mul_one] at he
    have hC : (l * t) ^ 2 ^ a ∈ Subgroup.centralizer (V : Set G) :=
      Subgroup.pow_mem _ hxC _
    rw [he] at hC
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 L ⟨l', hCL ⟨hl', hC⟩⟩
    have hk' : l' ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    refine ⟨a + k, Subtype.ext ?_⟩
    rw [SubmonoidClass.coe_pow, OneMemClass.coe_one, pow_add, pow_mul, he, hk']
  apply le_antisymm
  · exact le_pCoreOf_of_le_normalizer 2 inf_le_left (le_normalizer_inf_centralizer hred.2.1) hC2
  · refine le_inf (pCoreOf_le 2 _) ?_
    refine hred.2.2.2 (pCoreOf 2 (L ⊔ T)) (pCoreOf_le 2 _) (le_normalizer_pCoreOf 2 _) ?_
    intro d hd
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 (L ⊔ T) ⟨d, hd⟩
    exact ⟨k, by
      have := congrArg Subtype.val hk
      simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at this
      rw [this]
      exact Subgroup.one_mem _⟩

theorem centralizer_eq_pCoreOf (h : Hyp5_0_1 G T M L n) (hV : IsCh5Module T L V) :
    T ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 (L ⊔ T) := by
  have hS : IsSylowTwoOf T (L ⊔ T) := h.isSylowTwoOf le_sup_right
  apply le_antisymm
  · rw [← h.sup_inf_centralizer_eq hV]
    exact inf_le_inf_right _ le_sup_right
  · refine le_inf (F7.isSylowTwoOf_pCoreOf_le hS) ?_
    rw [← h.sup_inf_centralizer_eq hV]
    exact inf_le_right

theorem oTwoUpper_sup_eq (h : Hyp5_0_1 G T M L n) : oTwoUpper (L ⊔ T) = L := by
  refine oTwoUpper_sup_eq_of_normal ?_ h.sylow.1 h.T_le_normalizer
  symm
  exact h.faithful.2.1 _ (oTwoUpper_le L)
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (oTwoUpper_le L)).mpr
      (le_normalizer_oTwoUpper L))
    fun x hx => exists_pow_mem_oTwoUpper L hx

theorem normalizer_le (h : Hyp5_0_1 G T M L n) (h331 : Stmt3_3_1) :
    Subgroup.normalizer (T : Set G) ≤ M :=
  (h331 G T h.simple h.nonabelian h.qtke h.sylow).1 M L h.maxTwoLocal h.T_le h.maximal h.L_le
    h.isQuasisimple

theorem minParabolic_of_isHStar (h : Hyp5_0_1 G T M L n) (h331 : Stmt3_3_1) {H : Subgroup G}
    (hH : IsHStar T M H) :
    MinParabolic H T (H ⊓ M) ∧ (1 < E1.nParam H → ¬ Group.IsSolvable ↥H ∧ SQTKGroup ↥H) := by
  refine ⟨⟨h.isSylowTwoOf hH.1.1, hH.not_le_normalizer (h.normalizer_le h331), ?_⟩, ?_⟩
  · obtain ⟨S, rfl⟩ := exists_sylow_coe_eq h.sylow
    exact hH.isUniqueMaxOver S h.T_le
  · intro hn
    refine ⟨fun hsolv => ?_, ?_⟩
    · have := E1.solvable_nParam_le_one hsolv
      exact absurd hn (not_lt.mpr this)
    · obtain ⟨hk, hq⟩ := isSQTKSub_of_inH h.qtke h.simple h.nonabelian hH.1
      exact ⟨hq, hk⟩

theorem hyp315Base (h : Hyp5_0_1 G T M L n) (hV : IsCh5Module T L V) {H : Subgroup G}
    (hH : IsHStar T M H) :
    Hyp315Base T M (L ⊔ T) H V ∧ Hyp315.CaseI M (L ⊔ T) H := by
  refine ⟨⟨le_sup_right, h.sup_le_M, hH, hV.isTwoReducedIn,
    (h.centralizer_eq_pCoreOf hV).symm⟩, ?_⟩
  show H ⊓ M ≤ Subgroup.normalizer (oTwoUpper (L ⊔ T) : Set G)
  rw [h.oTwoUpper_sup_eq]
  exact inf_le_right.trans h.normal

theorem le_inf_sup (h : Hyp5_0_1 G T M L n) {X : Subgroup G} (hTX : T ≤ X) (hX : X ≤ L ⊔ T) :
    X ≤ (X ⊓ L) ⊔ T := by
  intro x hx
  have hx' : x ∈ ((L : Set G) * (T : Set G)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left L T h.T_le_normalizer]
    exact hX hx
  obtain ⟨l, hl, t, ht, rfl⟩ := hx'
  have hlX : l ∈ X := by
    have := X.mul_mem hx (X.inv_mem (hTX ht))
    simpa using this
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨hlX, hl⟩) (Subgroup.mem_sup_right ht)

theorem T_le_normalizer_inf (h : Hyp5_0_1 G T M L n) :
    T ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := by
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro w
  constructor
  · rintro ⟨hwT, hwL⟩
    exact ⟨T.mul_mem (T.mul_mem ht hwT) (T.inv_mem ht),
      (Subgroup.mem_normalizer_iff.mp (h.T_le_normalizer ht) w).mp hwL⟩
  · rintro ⟨hwT, hwL⟩
    refine ⟨?_, (Subgroup.mem_normalizer_iff.mp (h.T_le_normalizer ht) w).mpr hwL⟩
    have := T.mul_mem (T.mul_mem (T.inv_mem ht) hwT) ht
    simpa [mul_assoc] using this

theorem T_le_normalizer_borel (h : Hyp5_0_1 G T M L n) :
    T ≤ Subgroup.normalizer ((borelL T L : Subgroup G) : Set G) := by
  intro t ht
  have h1 := h.T_le_normalizer ht
  have h2 := h.T_le_normalizer_inf ht
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · rintro ⟨hzL, hzN⟩
    exact ⟨(Subgroup.mem_normalizer_iff.mp h1 z).mp hzL,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ h2 hzN) (Subgroup.inv_mem _ h2)⟩
  · rintro ⟨hzL, hzN⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp h1 z).mpr hzL, ?_⟩
    have := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ h2) hzN) h2
    simpa [mul_assoc] using this

omit [Finite G] in
theorem inf_le_borel (T L : Subgroup G) : T ⊓ L ≤ borelL T L :=
  le_inf inf_le_right Subgroup.le_normalizer

theorem borel_sup_inf (h : Hyp5_0_1 G T M L n) : (borelL T L ⊔ T) ⊓ L = borelL T L := by
  apply le_antisymm
  · rintro y ⟨hy, hyL⟩
    have hy' : y ∈ ((borelL T L : Set G) * (T : Set G)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ T h.T_le_normalizer_borel]
      exact hy
    obtain ⟨b, hb, t, ht, rfl⟩ := hy'
    have htL : t ∈ L := by
      have := L.mul_mem (L.inv_mem hb.1) hyL
      simpa using this
    exact (borelL T L).mul_mem hb (inf_le_borel T L ⟨ht, htL⟩)
  · exact le_inf le_sup_left inf_le_left

theorem rankOneAt (h : Hyp5_0_1 G T M L n) (hR : L2RankOneSylowFact) : RankOneAt L (T ⊓ L) := by
  have hS : IsSylowTwoOf T (L ⊔ T) := h.isSylowTwoOf le_sup_right
  have hSL : IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal hS le_sup_left h.sup_le_normalizer
  have hR1 : IsRankOneSylow (oTwoQuot ↥L) :=
    (hR _ n h.two_le h.lie).of_mulEquiv
      (QuotientGroup.quotientMulEquivOfEq (CFSG.pCore_eq_open ↥L 2))
  exact F1.rankOneAt_of_isRankOneSylow hSL hR1

theorem minParabolic_sup (h : Hyp5_0_1 G T M L n) (hR : L2RankOneSylowFact) :
    MinParabolic (L ⊔ T) T (borelL T L ⊔ T) := by
  have hS : IsSylowTwoOf T (L ⊔ T) := h.isSylowTwoOf le_sup_right
  have hRA := h.rankOneAt hR
  have hkey : ∀ X : Subgroup G, T ≤ X → X ≤ L ⊔ T → X ≠ L ⊔ T → X ≤ borelL T L ⊔ T := by
    intro X hTX hX hne
    have hXL : X ⊓ L ≠ L := by
      intro heq
      apply hne
      exact le_antisymm hX (sup_le (heq ▸ inf_le_left) hTX)
    have hle : X ⊓ L ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) :=
      hRA.unique_max (X ⊓ L) (inf_le_inf_right L hTX) inf_le_right hXL
    exact (h.le_inf_sup hTX hX).trans (sup_le_sup_right (le_inf inf_le_right hle) T)
  have hBle : borelL T L ⊔ T ≤ L ⊔ T := sup_le_sup_right inf_le_left T
  have hne : borelL T L ⊔ T ≠ L ⊔ T := by
    intro heq
    apply hRA.borel_ne
    have h1 := h.borel_sup_inf
    rw [heq, inf_eq_right.mpr le_sup_left] at h1
    exact h1.symm
  refine ⟨hS, ?_, ?_⟩
  · intro hle
    apply hRA.borel_ne
    apply le_antisymm inf_le_left
    intro x hxL
    refine ⟨hxL, ?_⟩
    have hxT := hle (Subgroup.mem_sup_left hxL)
    show x ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G)
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · rintro ⟨hwT, hwL⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp hxT w).mp hwT,
        L.mul_mem (L.mul_mem hxL hwL) (L.inv_mem hxL)⟩
    · rintro ⟨hwT, hwL⟩
      refine ⟨(Subgroup.mem_normalizer_iff.mp hxT w).mpr hwT, ?_⟩
      have := L.mul_mem (L.mul_mem (L.inv_mem hxL) hwL) hxL
      simpa [mul_assoc] using this
  · refine Set.ext fun N => ⟨fun hN => ?_, fun hN => ?_⟩
    · obtain ⟨hNmax, hTN⟩ := hN
      rw [Set.mem_singleton_iff]
      have h1 : N ≤ borelL T L ⊔ T := hkey N hTN hNmax.1.le hNmax.1.ne
      by_contra hne'
      exact hne (hNmax.2 (borelL T L ⊔ T) (lt_of_le_of_ne h1 hne') hBle)
    · rw [Set.mem_singleton_iff] at hN
      subst hN
      refine ⟨⟨lt_of_le_of_ne hBle hne, fun K hK hKle => ?_⟩, le_sup_right⟩
      by_contra hKne
      exact (lt_irrefl _) (lt_of_lt_of_le hK (hkey K (le_sup_right.trans hK.le) hKle hKne))

end Hyp5_0_1

theorem stmt5_1_1_of (h331 : Stmt3_3_1) (hR : L2RankOneSylowFact) : Stmt5_1_1 := by
  intro G _ _ T M L V n h hV
  exact ⟨h.centralizer_eq_pCoreOf hV, fun H hH => h.minParabolic_of_isHStar h331 hH,
    fun H hH => h.hyp315Base hV hH, ⟨_, h.minParabolic_sup hR⟩⟩

end CFSG.Quasithin.H13
