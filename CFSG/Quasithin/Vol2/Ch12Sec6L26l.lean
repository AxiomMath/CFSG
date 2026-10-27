module

public import CFSG.Quasithin.Vol2.Ch12Sec6L26k
public import CFSG.Quasithin.Vol2.Ch12Sec6KGFacts26
public import CFSG.Quasithin.Vol2.Ch12Sec6D29

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7
open CFSG.Quasithin.CosetGeom CFSG.SectionRank
open CFSG.Blueprint CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F Equiv
open scoped commutatorElement


namespace S126L26

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem inv_bar (h1224 : Lemma12_6_24) (F : Frame126 T L V) (hH : Hyp126 G T L V)
    (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) {H : Subgroup G} (hHz : S126.InHz T L F.V1 H)
    {v : G} (hv : v ∈ V) (hvH : v ∈ H) (hvQ : v ∉ pCoreOf 2 H) (x : ↥H ⧸ CFSG.pCore 2 ↥H)
    (hx : Odd (orderOf x))
    (hinv : ((⟨v, hvH⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) * x *
      ((⟨v, hvH⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H)⁻¹ = x⁻¹) :
    x ^ 3 = 1 ∨ x ^ 5 = 1 := by
  obtain ⟨h, hidx, hyp5, hcard, hC⟩ := setup126 h1224 F hH hZ hHz
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨m, hm⟩ := hx
  have hodd : (y : G) ^ (2 * m + 1) ∈ pCoreOf 2 H := by
    have : ((y ^ (2 * m + 1) : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) = 1 := by
      rw [QuotientGroup.mk_pow, ← hm, pow_orderOf_eq_one]
    exact (mk_eq_one_iff _).mp this
  have hinv' : v * y * v⁻¹ * y ∈ pCoreOf 2 H := by
    have : ((⟨v, hvH⟩ * y * (⟨v, hvH⟩ : ↥H)⁻¹ * y : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        hinv, inv_mul_cancel]
    exact (mk_eq_one_iff _).mp this
  rcases inverted_pow_mem h hidx hyp5 hcard hC hv hvQ y.2 hinv' hodd with h3 | h5
  · left
    rw [← QuotientGroup.mk_pow]
    exact (mk_eq_one_iff (y ^ 3)).mpr h3
  · right
    rw [← QuotientGroup.mk_pow]
    exact (mk_eq_one_iff (y ^ 5)).mpr h5

omit [Finite G] in
theorem mem_normalizer_closure {S : Set G} {x : G} (h1 : ∀ s ∈ S, x * s * x⁻¹ ∈ S)
    (h2 : ∀ s ∈ S, x⁻¹ * s * x ∈ S) : x ∈ Subgroup.normalizer (Subgroup.closure S : Set G) := by
  have key : ∀ y : G, (∀ s ∈ S, y * s * y⁻¹ ∈ S) → ∀ a ∈ Subgroup.closure S,
      y * a * y⁻¹ ∈ Subgroup.closure S := by
    intro y hy a ha
    have : (Subgroup.closure S).map (MulAut.conj y).toMonoidHom ≤ Subgroup.closure S := by
      rw [MonoidHom.map_closure]
      refine Subgroup.closure_le _ |>.mpr ?_
      rintro _ ⟨s, hs, rfl⟩
      exact Subgroup.subset_closure (hy s hs)
    exact this ⟨a, ha, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · exact key x h1 a
  · intro ha
    have := key x⁻¹ (fun s hs => by simpa using h2 s hs) _ ha
    simpa [mul_assoc] using this

omit [Finite G] in
theorem mem_normalizer_L₁ {V₁ : Subgroup G} {x : G} (hxL : x ∈ Subgroup.normalizer (L : Set G))
    (hxV : x ∈ Subgroup.normalizer (V₁ : Set G)) :
    x ∈ Subgroup.normalizer (L₁Of L V₁ : Set G) := by
  have hc : ∀ y : G, y ∈ Subgroup.normalizer (L : Set G) →
      y ∈ Subgroup.normalizer (V₁ : Set G) →
      ∀ s ∈ {u | u ∈ L ⊓ Subgroup.normalizer (V₁ : Set G) ∧ ∃ m, Odd m ∧ u ^ m = 1},
        y * s * y⁻¹ ∈ {u | u ∈ L ⊓ Subgroup.normalizer (V₁ : Set G) ∧ ∃ m, Odd m ∧ u ^ m = 1} := by
    rintro y hyL hyV s ⟨⟨hsL, hsV⟩, m, hm, hsm⟩
    refine ⟨⟨(Subgroup.mem_normalizer_iff.mp hyL s).mp hsL, ?_⟩, m, hm, ?_⟩
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hyV hsV) (Subgroup.inv_mem _ hyV)
    · rw [conj_pow, hsm, mul_one, mul_inv_cancel]
  refine mem_normalizer_closure (hc x hxL hxV) fun s hs => ?_
  have := hc x⁻¹ (Subgroup.inv_mem _ hxL) (Subgroup.inv_mem _ hxV) s hs
  simpa using this

omit [Finite G] in
theorem map_le_normalizer {H X K : Subgroup G} (N : Subgroup ↥H) [N.Normal]
    (hXK : X ≤ Subgroup.normalizer (K : Set G)) :
    (X.subgroupOf H).map (QuotientGroup.mk' N) ≤
      Subgroup.normalizer
        (((K.subgroupOf H).map (QuotientGroup.mk' N) : Subgroup (↥H ⧸ N)) : Set (↥H ⧸ N)) := by
  rintro _ ⟨x, hx, rfl⟩
  replace hx : (x : G) ∈ X := Subgroup.mem_subgroupOf.mp hx
  rw [Subgroup.mem_normalizer_iff]
  intro w
  constructor
  · rintro ⟨k, hk, rfl⟩
    replace hk : (k : G) ∈ K := Subgroup.mem_subgroupOf.mp hk
    refine ⟨x * k * x⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by simp⟩
    exact (Subgroup.mem_normalizer_iff.mp (hXK hx) k).mp hk
  · rintro ⟨k, hk, hke⟩
    replace hk : (k : G) ∈ K := Subgroup.mem_subgroupOf.mp hk
    refine ⟨x⁻¹ * k * x, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
    · have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hXK hx)) (k : G)).mp hk
      rw [inv_inv] at h1
      exact h1
    · have e : (QuotientGroup.mk' N) k =
          (QuotientGroup.mk' N) x * w * ((QuotientGroup.mk' N) x)⁻¹ := hke
      rw [map_mul, map_mul, map_inv, e]
      group

theorem v_central_bar (h1224 : Lemma12_6_24) (F : Frame126 T L V) (hH : Hyp126 G T L V)
    (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) {H : Subgroup G} (hHz : S126.InHz T L F.V1 H)
    {v : G} (hv : v ∈ V) (hvH : v ∈ H) (hvQ : v ∉ pCoreOf 2 H) :
    ∀ t ∈ (T.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)),
      ((⟨v, hvH⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) * t =
        t * ((⟨v, hvH⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) := by
  obtain ⟨h, hidx, -, -, -⟩ := setup126 h1224 F hH hZ hHz
  have hTH : T ≤ H := le_sup_right.trans hHz.1.1
  have hT5 : T ≤ Subgroup.normalizer (F.V5 : Set G) := le_sup_right.trans h.L₁T_normalizes_Vp
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := fun t ht => h.normalizer_le ⟨hTH ht, hT5 ht⟩
  have hvp : v ∉ F.V5 := fun h5 => hvQ (h.Vp_le_pCoreOf_and_commutator_le.1 h5)
  rintro _ ⟨t, ht, rfl⟩
  have htT : (t : G) ∈ T := Subgroup.mem_subgroupOf.mp ht
  have hw : (t : G) * v * (t : G)⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hTV htT) v).mp hv
  rcases mem_or_inv_mul_mem hidx hv hvp hw with h5 | h5
  · exact absurd ((Subgroup.mem_normalizer_iff.mp (hT5 htT) v).mpr h5) hvp
  · show ((⟨v, hvH⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) * (t : ↥H ⧸ CFSG.pCore 2 ↥H) =
      (t : ↥H ⧸ CFSG.pCore 2 ↥H) * ((⟨v, hvH⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H)
    rw [mk_comm_iff]
    have hc : v⁻¹ * ((t : G) * v * (t : G)⁻¹) = (t : G) * v * (t : G)⁻¹ * v⁻¹ :=
      congrArg Subtype.val (h.elemAbelian.1.is_comm.comm (⟨v⁻¹, V.inv_mem hv⟩ : ↥V) ⟨_, hw⟩)
    rw [hc] at h5
    have h6 := (F.V5).inv_mem h5
    have e : ((t : G) * v * (t : G)⁻¹ * v⁻¹)⁻¹ = v * (t : G) * v⁻¹ * (t : G)⁻¹ := by group
    rw [e] at h6
    exact h.Vp_le_pCoreOf_and_commutator_le.1 h6

theorem centralizer_le_normalizer_L₁ (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2)
    (h1224 : Lemma12_6_24) (F : Frame126 T L V) (hH : Hyp126 G T L V)
    (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) {H : Subgroup G} (hHz : S126.InHz T L F.V1 H)
    {v : G} (hv : v ∈ V) (hvH : v ∈ H) (hvQ : v ∉ pCoreOf 2 H) :
    Subgroup.centralizer ({((⟨v, hvH⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H)} : Set (↥H ⧸ CFSG.pCore 2 ↥H)) ≤
      Subgroup.normalizer
        ((((L₁Of L F.V1).subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) :
          Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
  obtain ⟨h, hidx, -, -, -⟩ := setup126 h1224 F hH hZ hHz
  have hV : ¬ V ≤ pCoreOf 2 H := fun hle => hvQ (hle hv)
  have hQn : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := le_normalizer_pCoreOf 2 H
  have hvp : v ∉ F.V5 := fun h5 => hvQ (h.Vp_le_pCoreOf_and_commutator_le.1 h5)
  intro xb hxb
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective xb
  rw [Subgroup.mem_centralizer_singleton_iff] at hxb
  have hxv : (x : G) * v * (x : G)⁻¹ * v⁻¹ ∈ pCoreOf 2 H := (mk_comm_iff x ⟨v, hvH⟩).mp hxb
  have hxC : (x : G) ∈ centralizerMod (pCoreOf 2 H) H V := by
    refine ⟨x.2, hQn x.2, fun a ha => ?_⟩
    rcases mem_or_inv_mul_mem hidx hv hvp ha with h5 | h5
    · have haQ : a ∈ pCoreOf 2 H := h.Vp_le_pCoreOf_and_commutator_le.1 h5
      have h1 : (x : G) * a * (x : G)⁻¹ ∈ pCoreOf 2 H :=
        (Subgroup.mem_normalizer_iff.mp (hQn x.2) a).mp haQ
      exact (pCoreOf 2 H).mul_mem h1 ((pCoreOf 2 H).inv_mem haQ)
    · have hq : v⁻¹ * a ∈ pCoreOf 2 H := h.Vp_le_pCoreOf_and_commutator_le.1 h5
      have h1 : (x : G) * (v⁻¹ * a) * (x : G)⁻¹ ∈ pCoreOf 2 H :=
        (Subgroup.mem_normalizer_iff.mp (hQn x.2) _).mp hq
      have h2 : (x : G) * (v⁻¹ * a) * (x : G)⁻¹ * (v⁻¹ * a)⁻¹ ∈ pCoreOf 2 H :=
        (pCoreOf 2 H).mul_mem h1 ((pCoreOf 2 H).inv_mem hq)
      have h3 : v * ((x : G) * (v⁻¹ * a) * (x : G)⁻¹ * (v⁻¹ * a)⁻¹) * v⁻¹ ∈ pCoreOf 2 H :=
        (Subgroup.mem_normalizer_iff.mp (hQn hvH) _).mp h2
      have e : (x : G) * a * (x : G)⁻¹ * a⁻¹ = ((x : G) * v * (x : G)⁻¹ * v⁻¹) *
          (v * ((x : G) * (v⁻¹ * a) * (x : G)⁻¹ * (v⁻¹ * a)⁻¹) * v⁻¹) := by group
      rw [e]
      exact (pCoreOf 2 H).mul_mem hxv h3
  have hxV : (x : G) ∈ Subgroup.normalizer (V : Set G) := by
    have h1 := (h.F95_3 hidx hV).1 ▸ hxC
    have h2 := (h.F95_3 hidx hV).2 ▸ h1
    exact h2.2
  have hxL : (x : G) ∈ Subgroup.normalizer (L : Set G) :=
    S126L20c.normalizer_V_le h331 h1222 F hH hxV
  have hxV1 : (x : G) ∈ Subgroup.normalizer (F.V1 : Set G) :=
    Subgroup.centralizer_le_normalizer _ (hHz.2.2 x.2)
  have hxL1 := mem_normalizer_L₁ hxL hxV1
  exact map_le_normalizer (X := Subgroup.normalizer (L₁Of L F.V1 : Set G)) _ le_rfl
    ⟨x, Subgroup.mem_subgroupOf.mpr hxL1, rfl⟩

omit [Finite G] [IsMulCommutative ↥V] in
theorem oTwoUpper_map_L₁ {H V₁ : Subgroup G} (hL1H : L₁Of L V₁ ≤ H) :
    oTwoUpper (((L₁Of L V₁).subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))) =
      ((L₁Of L V₁).subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) := by
  refine le_antisymm (oTwoUpper_le _) ?_
  set Lb := ((L₁Of L V₁).subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) with hLb
  set Y : Subgroup G :=
    ((oTwoUpper Lb).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥H))).map H.subtype with hY
  have hLY : L₁Of L V₁ ≤ Y := by
    rw [← S126D29.oTwoUpper_L₁Of L V₁]
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hxL, hxo⟩
    have hxH : x ∈ H := hL1H hxL
    refine ⟨⟨x, hxH⟩, ?_, rfl⟩
    show QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨x, hxH⟩ ∈ oTwoUpper Lb
    refine mem_oTwoUpper_of_odd ⟨⟨x, hxH⟩, Subgroup.mem_subgroupOf.mpr hxL, rfl⟩ ?_
    have hd : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨x, hxH⟩) ∣
        orderOf (⟨x, hxH⟩ : ↥H) := orderOf_map_dvd _ _
    have ho : orderOf (⟨x, hxH⟩ : ↥H) = orderOf x := (Subgroup.orderOf_coe _).symm
    rw [ho] at hd
    exact Odd.of_dvd_nat hxo hd
  rintro _ ⟨l, hl, rfl⟩
  obtain ⟨y, hy, hyl⟩ := hLY (Subgroup.mem_subgroupOf.mp hl)
  have : y = l := Subtype.ext hyl
  rw [← this]
  exact hy

theorem three_of_mem_map_L₁ (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V)
    {H : Subgroup G} :
    ∀ x ∈ ((L₁Of L F.V1).subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)),
      Odd (orderOf x) → x ^ 3 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rintro _ ⟨l, hl, rfl⟩ hodd
  replace hl : (l : G) ∈ L₁Of L F.V1 := Subgroup.mem_subgroupOf.mp hl
  set m := orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥H) l) with hm
  have hlm : l ^ m ∈ CFSG.pCore 2 ↥H := by
    have h0 : ((l ^ m : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) = 1 := by
      rw [QuotientGroup.mk_pow]
      exact pow_orderOf_eq_one (QuotientGroup.mk' (CFSG.pCore 2 ↥H) l)
    exact (QuotientGroup.eq_one_iff _).mp h0
  obtain ⟨c, hc⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 ↥H)) ⟨_, hlm⟩
  have hc' : (l : G) ^ (m * 2 ^ c) = 1 := by
    have := congrArg (fun z : CFSG.pCore 2 ↥H => ((z : ↥H) : G)) hc
    simpa [pow_mul] using this
  have hu : ((l : G) ^ 2 ^ c) ^ m = 1 := by rw [← pow_mul, mul_comm]; exact hc'
  have hL1 : L₁Of L F.V1 ≤ L ⊓ Subgroup.normalizer (F.V1 : Set G) := oTwoRes_le _
  have hu3 := S126L19b.pow_three_of_mem h1222 F hH (L.pow_mem (hL1 hl).1 _)
    (Subgroup.pow_mem _ (hL1 hl).2 _) hodd hu
  have h1 : (QuotientGroup.mk' (CFSG.pCore 2 ↥H) l) ^ (3 * 2 ^ c) = 1 := by
    have h2 : (l : G) ^ (3 * 2 ^ c) = 1 := by rw [mul_comm, pow_mul]; exact hu3
    have : (l ^ (3 * 2 ^ c) : ↥H) = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact h2)
    rw [← map_pow, this, map_one]
  have h2 : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥H) l) ∣ 3 := by
    have hd := orderOf_dvd_of_pow_eq_one h1
    have hcop : Nat.Coprime (orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥H) l)) (2 ^ c) :=
      Nat.Coprime.pow_right _ (Nat.coprime_two_left.mpr hodd).symm
    exact hcop.dvd_of_dvd_mul_right hd
  exact orderOf_dvd_iff_pow_eq_one.mp h2

theorem exists_noncomm_L₁ (h1222 : Stmt12_2_2) (h1224 : Lemma12_6_24) (F : Frame126 T L V)
    (hH : Hyp126 G T L V) (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) {H : Subgroup G}
    (hHz : S126.InHz T L F.V1 H) {v : G} (hv : v ∈ V) (hvH : v ∈ H) (hvQ : v ∉ pCoreOf 2 H)
    {K : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)} (hK : CFSG.IsComponent K)
    (hnc : ∃ k ∈ K, ((⟨v, hvH⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) * k ≠
      k * ((⟨v, hvH⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H)) :
    ∃ l ∈ ((L₁Of L F.V1).subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)),
      ∃ k ∈ K, l * k ≠ k * l := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hall
  push Not at hall
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hπ
  set Lb := ((L₁Of L F.V1).subgroupOf H).map π with hLb
  set Cb : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H) := Subgroup.centralizer (Lb : Set _) with hCb
  have hKC : K ≤ Cb := fun k hk =>
    Subgroup.mem_centralizer_iff.mpr fun l hl => hall l hl k hk
  set C : Subgroup G := centralizerMod (pCoreOf 2 H) H (Li L F.V1) with hC
  have hCH : C ≤ H := fun x hx => hx.1
  set Rb : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H) := ((pCoreOf 2 C).subgroupOf H).map π with hRb
  have hVR := le_pCoreOf_K h1222 h1224 F hH hZ hHz (fun hle => hvQ (hle hv))
  have hvR : ((⟨v, hvH⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) ∈ Rb :=
    ⟨⟨v, hvH⟩, Subgroup.mem_subgroupOf.mpr (hVR hv), rfl⟩
  have hpre : ∀ x : ↥H, π x ∈ Cb → (x : G) ∈ C := by
    intro x hx
    refine ⟨x.2, le_normalizer_pCoreOf 2 H x.2, fun l hl => ?_⟩
    have hlH : l ∈ H := (le_sup_left.trans hHz.1.1) hl
    have h1 := Subgroup.mem_centralizer_iff.mp hx (π ⟨l, hlH⟩)
      ⟨⟨l, hlH⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
    exact (mk_comm_iff x ⟨l, hlH⟩).mp h1.symm
  have hRC : Rb ≤ Cb := by
    rintro _ ⟨r, hr, rfl⟩
    replace hr : (r : G) ∈ pCoreOf 2 C := Subgroup.mem_subgroupOf.mp hr
    have hrC : (r : G) ∈ C := pCoreOf_le 2 C hr
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨l, hl, rfl⟩
    replace hl : (l : G) ∈ L₁Of L F.V1 := Subgroup.mem_subgroupOf.mp hl
    exact ((mk_comm_iff r l).mpr (hrC.2.2 l hl)).symm
  have hRn : Cb ≤ Subgroup.normalizer (Rb : Set _) := by
    intro c hc
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
    have hxC := hpre x hc
    exact map_le_normalizer (X := Subgroup.normalizer (pCoreOf 2 C : Set G)) _ le_rfl
      ⟨x, Subgroup.mem_subgroupOf.mpr (le_normalizer_pCoreOf 2 C hxC), rfl⟩
  have hR2 : IsPGroup 2 ↥Rb := by
    have h2 : IsPGroup 2 ↥((pCoreOf 2 C).subgroupOf H) :=
      (pCoreOf_isPGroup 2 C).of_equiv
        (Subgroup.subgroupOfEquivOfLe ((pCoreOf_le 2 C).trans hCH)).symm
    exact h2.map _
  have hKs : (K.subgroupOf Cb).IsSubnormal := hK.2.subgroupOf
  have hKq : CFSG.IsQuasisimple ↥(K.subgroupOf Cb) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKC).symm hK.1
  have hRn' : (Rb.subgroupOf Cb).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRC).mpr hRn
  have hRs : Group.IsSolvable ↥(Rb.subgroupOf Cb) := by
    have h2 : IsPGroup 2 ↥(Rb.subgroupOf Cb) :=
      hR2.of_equiv (Subgroup.subgroupOfEquivOfLe hRC).symm
    have := h2.isNilpotent
    infer_instance
  have hcomm := (CFSG.LocalCores.component_solvable_centralizer hRs hRn'.isSubnormal).1 _
    ⟨hKq, hKs⟩
  obtain ⟨k, hk, hvk⟩ := hnc
  apply hvk
  have hmem : ⁅(⟨k, hKC hk⟩ : ↥Cb), (⟨_, hRC hvR⟩ : ↥Cb)⁆ ∈
      ⁅K.subgroupOf Cb, Rb.subgroupOf Cb⁆ :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mpr hk)
      (Subgroup.mem_subgroupOf.mpr hvR)
  rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
  exact (congrArg Subtype.val hmem).symm

omit [Finite G] in
theorem card_map_P {H P : Subgroup G} (hPH : P ≤ H) (hP3 : IsElemAbelian 3 P) :
    Nat.card ((P.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))) = Nat.card P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinj : Function.Injective
      ((QuotientGroup.mk' (CFSG.pCore 2 ↥H)).comp (P.subgroupOf H).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hx
    have h3 : (x : ↥H) ^ 3 = 1 :=
      Subtype.ext (by
        rw [Subgroup.coe_pow]
        exact hP3.2 _ (Subgroup.mem_subgroupOf.mp x.2))
    obtain ⟨c, hc⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 ↥H)) ⟨_, hx⟩
    have h2 : (x : ↥H) ^ 2 ^ c = 1 := by simpa using congrArg Subtype.val hc
    have h3d := orderOf_dvd_of_pow_eq_one h3
    have h2d := orderOf_dvd_of_pow_eq_one h2
    have hcop : Nat.Coprime 3 (2 ^ c) := Nat.Coprime.pow_right c (by norm_num)
    have h1 := (Nat.Coprime.coprime_dvd_left h3d hcop).eq_one_of_dvd h2d
    rw [orderOf_eq_one_iff] at h1
    exact Subgroup.mem_bot.mpr (Subtype.ext h1)
  have e1 : (P.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) =
      ((QuotientGroup.mk' (CFSG.pCore 2 ↥H)).comp (P.subgroupOf H).subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [e1, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPH).toEquiv

omit [Finite G] in
theorem isElemAbelian_map_P {H P : Subgroup G} (hP3 : IsElemAbelian 3 P) :
    IsElemAbelian 3 ((P.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨p, hp, hpa⟩ := a.2
    obtain ⟨q, hq, hqb⟩ := b.2
    apply Subtype.ext
    show (a : ↥H ⧸ CFSG.pCore 2 ↥H) * b = b * a
    rw [← hpa, ← hqb, ← map_mul, ← map_mul]
    congr 1
    have hc : (p : G) * q = q * p := congrArg Subtype.val (hP3.1.is_comm.comm
      (⟨_, Subgroup.mem_subgroupOf.mp hp⟩ : ↥P) ⟨_, Subgroup.mem_subgroupOf.mp hq⟩)
    exact Subtype.ext hc
  · rintro _ ⟨p, hp, rfl⟩
    rw [← map_pow]
    have : p ^ 3 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow]
      exact hP3.2 _ (Subgroup.mem_subgroupOf.mp hp))
    rw [this, map_one]

theorem exists_conf (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h1224 : Lemma12_6_24)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (F : Frame126 T L V)
    (hH : Hyp126 G T L V) (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) {H : Subgroup G}
    (hHz : S126.InHz T L F.V1 H) {v : G} (hv : v ∈ V) (hvH : v ∈ H) (hvQ : v ∉ pCoreOf 2 H) :
    ∃ K ∈ cComp H, ∃ P ≤ L₁Of L F.V1, IsElemAbelian 3 P ∧ Nat.card P = 9 ∧
      S126C.Conf12626 (modO2Image H K)
        (((L₁Of L F.V1).subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)))
        ((P.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)))
        ((T.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)))
        ((⟨v, hvH⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) := by
  classical
  have hyp := hH.hyp
  have : IsSimpleGroup G := hyp.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat hyp.nonabelian hyp.qtke).1
  obtain ⟨h, -, -, -, -⟩ := setup126 h1224 F hH hZ hHz
  have hTH : T ≤ H := le_sup_right.trans hHz.1.1
  have hL1H : L₁Of L F.V1 ≤ H := le_sup_left.trans hHz.1.1
  obtain ⟨Kb, hKb, hvN, hnc⟩ := exists_component h1222 h1224 h38 F hH hZ hHz hv hvH hvQ
  obtain ⟨K, hK, hKe⟩ := exists_cComp_modO2Image_eq (mem_cComp_top_of_isComponent hKb)
  subst hKe
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hL1K : L₁Of L F.V1 ≤ Subgroup.normalizer (K : Set G) :=
    S153D.le_normalizer_of_oTwoUpper_eq hKH hL1H (S126D29.oTwoUpper_L₁Of L F.V1)
      ((Vol2Native.lemma_1_2_1_three hloc h37 h38 hHz.1.2 hK).imp id fun h => h.1)
  obtain ⟨P, hPL, hPe, hP9⟩ := exists_E9 h1222 F hH
  have hVK := V_le_K h1222 h1224 F hH hZ hHz
  refine ⟨K, hK, P, hPL, hPe, hP9, ⟨hKb, isSylowTwoOf_mk (isSylowTwoOf_of_le h.sylow hTH),
    ⟨⟨v, hvH⟩, Subgroup.mem_subgroupOf.mpr (h.V_le_T hv), rfl⟩,
    v_central_bar h1224 F hH hZ hHz hv hvH hvQ, ?_, hvN, hnc,
    fun x hx hinv => inv_bar h1224 F hH hZ hHz hv hvH hvQ x hx hinv, ?_,
    centralizer_le_normalizer_L₁ h331 h1222 h1224 F hH hZ hHz hv hvH hvQ,
    map_le_normalizer _ hL1K, oTwoUpper_map_L₁ hL1H, three_of_mem_map_L₁ h1222 F hH,
    exists_noncomm_L₁ h1222 h1224 F hH hZ hHz hv hvH hvQ hKb hnc,
    Subgroup.map_mono (fun x hx => Subgroup.mem_subgroupOf.mpr (hPL hx)),
    isElemAbelian_map_P hPe, (card_map_P (hPL.trans hL1H) hPe).trans hP9⟩⟩
  · have hv2 : v ^ 2 = 1 := isElemAbelian_pow_eq_one h.elemAbelian hv
    rw [← QuotientGroup.mk_pow,
      show (⟨v, hvH⟩ : ↥H) ^ 2 = 1 from Subtype.ext (by simpa using hv2), QuotientGroup.mk_one]
  · rintro _ ⟨l, hl, rfl⟩
    replace hl : (l : G) ∈ L₁Of L F.V1 := Subgroup.mem_subgroupOf.mp hl
    exact (mk_comm_iff ⟨v, hvH⟩ l).mpr ((hVK hv).2.2 l hl)

end S126L26

end CFSG.Quasithin.H13
