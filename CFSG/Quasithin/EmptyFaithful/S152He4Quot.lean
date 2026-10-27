module

public import CFSG.Quasithin.EmptyFaithful.S153YCases
public import CFSG.Quasithin.EmptyFaithful.S14620B
public import CFSG.Quasithin.EmptyFaithful.S151Basic
public import CFSG.Quasithin.Recognition.F112WLocal2

public section

namespace CFSG.Quasithin.He4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_imageOTwoQuot_mul {X Z : Subgroup G} (hZX : Z ≤ X) :
    Nat.card (imageOTwoQuot X Z) * Nat.card ↥(Z ⊓ pCoreOf 2 X) = Nat.card Z := by
  classical
  let A : Subgroup ↥X := Z.subgroupOf X
  let f : ↥A →* OTwoQuot X := (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥X)).comp A.subtype
  have hrange : f.range = imageOTwoQuot X Z := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  have hmem : ∀ x : ↥f.ker, (((x.1 : ↥A) : ↥X) : G) ∈ Z ⊓ pCoreOf 2 X := by
    intro x
    refine ⟨Subgroup.mem_subgroupOf.1 x.1.2, ?_⟩
    have hx : f x.1 = 1 := x.2
    exact (mk_eq_one_iff_mem_pCoreOf (((x.1 : ↥A) : ↥X))).1 hx
  have hker : Nat.card f.ker = Nat.card ↥(Z ⊓ pCoreOf 2 X) := by
    refine Nat.card_congr (Equiv.ofBijective (fun x => (⟨_, hmem x⟩ : ↥(Z ⊓ pCoreOf 2 X))) ⟨?_, ?_⟩)
    · intro x y hxy
      have h1 : (((x.1 : ↥A) : ↥X) : G) = (((y.1 : ↥A) : ↥X) : G) := by
        simpa using hxy
      exact Subtype.ext (Subtype.ext (Subtype.ext h1))
    · rintro ⟨g, hg⟩
      have hgX : g ∈ X := hZX hg.1
      refine ⟨⟨⟨⟨g, hgX⟩, Subgroup.mem_subgroupOf.2 hg.1⟩, ?_⟩, rfl⟩
      exact (mk_eq_one_iff_mem_pCoreOf (⟨g, hgX⟩ : ↥X)).2 hg.2
  have h := Subgroup.card_ker_mul_card_range f
  rw [hrange, hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZX).toEquiv] at h
  rw [← h, mul_comm]


theorem isSylowTwoOf_imageOTwoQuot_top {X T : Subgroup G} (hT : IsSylowTwoOf T X) :
    IsSylowTwoOf (imageOTwoQuot X T) ⊤ := by
  have hQT : pCoreOf 2 X ≤ T := hT.pCoreOf_le
  have hQX : pCoreOf 2 X ≤ X := pCoreOf_le 2 X
  have h1 := card_imageOTwoQuot_mul (X := X) (Z := X) le_rfl
  have h2 := card_imageOTwoQuot_mul (X := X) (Z := T) hT.1
  rw [imageOTwoQuot_self_eq_top, inf_eq_right.2 hQX, Subgroup.card_top] at h1
  rw [inf_eq_right.2 hQT] at h2
  have hidx := Subgroup.card_mul_index (T.subgroupOf X)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT.1).toEquiv] at hidx
  have hQpos : 0 < Nat.card (pCoreOf 2 X) := Nat.card_pos
  have hqpos : 0 < Nat.card (imageOTwoQuot X T) := Nat.card_pos
  have hYcard : Nat.card (OTwoQuot X) =
      Nat.card (imageOTwoQuot X T) * (T.subgroupOf X).index := by
    apply Nat.eq_of_mul_eq_mul_right hQpos
    calc Nat.card (OTwoQuot X) * Nat.card (pCoreOf 2 X) = Nat.card X := h1
      _ = Nat.card T * (T.subgroupOf X).index := hidx.symm
      _ = Nat.card (imageOTwoQuot X T) * (T.subgroupOf X).index * Nat.card (pCoreOf 2 X) := by
        rw [← h2]; ring
  have hi := Subgroup.card_mul_index (imageOTwoQuot X T)
  have hidx' : (imageOTwoQuot X T).index = (T.subgroupOf X).index := by
    apply Nat.eq_of_mul_eq_mul_left hqpos
    rw [hi, hYcard]
  refine ⟨le_top, isPGroup_imageOTwoQuot' hT.2.1, ?_⟩
  change ¬ 2 ∣ (imageOTwoQuot X T).relIndex ⊤
  rw [Subgroup.relIndex_top_right, hidx']
  exact hT.2.2

omit [Finite G] in
theorem normal_imageOTwoQuot {X L : Subgroup G}
    (hn : ∀ x ∈ X, ∀ l ∈ L, x * l * x⁻¹ ∈ L) : (imageOTwoQuot X L).Normal := by
  refine ⟨fun u hu y => ?_⟩
  obtain ⟨l, hlX, hlL, rfl⟩ := mem_imageOTwoQuot_iff.1 hu
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  refine mem_imageOTwoQuot_iff.2 ⟨x * l * x⁻¹,
    X.mul_mem (X.mul_mem x.2 hlX) (X.inv_mem x.2), hn x x.2 l hlL, ?_⟩
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  rfl

omit [Finite G] in
theorem prod_imageOTwoQuot {X L T : Subgroup G} (hX : X = L ⊔ T)
    (hT : T ≤ Subgroup.normalizer (L : Set G)) (y : OTwoQuot X) :
    ∃ l ∈ imageOTwoQuot X L, ∃ t ∈ imageOTwoQuot X T, y = l * t := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  have hx : (x : G) ∈ ((L ⊔ T : Subgroup G) : Set G) := hX ▸ x.2
  rw [Subgroup.coe_mul_of_right_le_normalizer_left L T hT] at hx
  obtain ⟨l, hl, t, ht, hlt⟩ := Set.mem_mul.1 hx
  have hLX : L ≤ X := hX ▸ le_sup_left
  have hTX : T ≤ X := hX ▸ le_sup_right
  refine ⟨QuotientGroup.mk ⟨l, hLX hl⟩, mem_imageOTwoQuot_iff.2 ⟨l, hLX hl, hl, rfl⟩,
    QuotientGroup.mk ⟨t, hTX ht⟩, mem_imageOTwoQuot_iff.2 ⟨t, hTX ht, ht, rfl⟩, ?_⟩
  rw [← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext hlt.symm

omit [Finite G] in
theorem imageOTwoQuot_conj_mem' {X H N : Subgroup G}
    (hn : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) :
    ∀ h' ∈ imageOTwoQuot X H, ∀ n' ∈ imageOTwoQuot X N, h' * n' * h'⁻¹ ∈ imageOTwoQuot X N := by
  intro h' hh' n' hn'
  obtain ⟨h, hhX, hhH, rfl⟩ := mem_imageOTwoQuot_iff.1 hh'
  obtain ⟨n, hnX, hnN, rfl⟩ := mem_imageOTwoQuot_iff.1 hn'
  refine mem_imageOTwoQuot_iff.2 ⟨h * n * h⁻¹, X.mul_mem (X.mul_mem hhX hnX) (X.inv_mem hhX),
    hn h hhH n hnN, ?_⟩
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  rfl


theorem exists_subgroup_card_nine {H N : Subgroup G} (hN2 : IsPGroup 2 N)
    (hcard : Nat.card H = 72 * Nat.card N) : ∃ P : Subgroup G, P ≤ H ∧ Nat.card P = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, ha⟩ := hN2.exists_card_eq
  have hH : Nat.card H = 2 ^ (a + 3) * 9 := by rw [hcard, ha]; ring
  obtain ⟨P⟩ : Nonempty (Sylow 3 ↥H) := inferInstance
  have hPcard : Nat.card P = 9 := by
    rw [Sylow.card_eq_multiplicity, hH]
    have h9 : (9 : ℕ).factorization 3 = 2 := by
      rw [show (9 : ℕ) = 3 ^ 2 by norm_num, Nat.Prime.factorization_pow Nat.prime_three]
      simp
    have h2 : (2 ^ (a + 3)).factorization 3 = 0 := by
      rw [Nat.Prime.factorization_pow Nat.prime_two]
      simp
    have : (2 ^ (a + 3) * 9).factorization 3 = 2 := by
      rw [Nat.factorization_mul (by positivity) (by norm_num), Finsupp.add_apply, h9, h2]
    rw [this]
    norm_num
  exact ⟨(P : Subgroup ↥H).map H.subtype, Subgroup.map_subtype_le _, by
    rw [Subgroup.card_map_of_injective H.subtype_injective, hPcard]⟩

theorem le_oTwoUpper_of_isPGroup_three {H P : Subgroup G} (hPH : P ≤ H) (hP3 : IsPGroup 3 P) :
    P ≤ oTwoUpper H := by
  intro x hx
  obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper H (hPH hx)
  obtain ⟨j, hj⟩ := hP3 ⟨x, hx⟩
  have hxj : x ^ 3 ^ j = 1 := by simpa using congrArg Subtype.val hj
  have hord : orderOf x ∣ 3 ^ j := orderOf_dvd_of_pow_eq_one hxj
  have hcop : Nat.Coprime (2 ^ k) (orderOf x) := by
    refine Nat.Coprime.pow_left _ ?_
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hord
    rw [hi]
    exact Nat.Coprime.pow_right _ (by norm_num)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hm]
  exact (oTwoUpper H).pow_mem hk m


theorem eq_bot_of_normal_isPGroup_two (X : Subgroup G) (Q : Subgroup (OTwoQuot X)) (hQ : Q.Normal)
    (h2 : IsPGroup 2 Q) : Q = ⊥ := by
  have h := pCore_two_quot_eq_bot X
  exact le_bot_iff.1 ((CFSG.LieType.BorelTits.le_pCore 2 hQ h2).trans h.le)

structure YData {Y : Type*} [Group Y] (Lt T H N P : Subgroup Y) : Prop where
  normal : Lt.Normal
  prod : ∀ y : Y, ∃ l ∈ Lt, ∃ t ∈ T, y = l * t
  sylow : IsSylowTwoOf T ⊤
  le : T ≤ H
  nh : N ≤ H
  nn : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N
  n2 : IsPGroup 2 N
  card : Nat.card H = 72 * Nat.card N
  ph : P ≤ H
  pl : P ≤ Lt
  p9 : Nat.card P = 9

theorem exists_yData {T Mc H L : Subgroup G} (hT : quasithinIsSylowTwo T) (hTMc : T ≤ Mc)
    (hTH : T ≤ H) (hMcn : Mc ≤ Subgroup.normalizer (L : Set G)) (hKL : oTwoUpper H ≤ L)
    (hHcard : Nat.card H = 72 * Nat.card (pCoreOf 2 H)) :
    ∃ P : Subgroup G, YData (imageOTwoQuot (L ⊔ T) L) (imageOTwoQuot (L ⊔ T) T)
        (imageOTwoQuot (L ⊔ T) H) (imageOTwoQuot (L ⊔ T) (pCoreOf 2 H))
        (imageOTwoQuot (L ⊔ T) P) ∧ Nonempty (OTwoQuot L ≃* ↥(imageOTwoQuot (L ⊔ T) L)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set X : Subgroup G := L ⊔ T with hXdef
  have hLX : L ≤ X := le_sup_left
  have hTX : T ≤ X := le_sup_right
  have hTn : T ≤ Subgroup.normalizer (L : Set G) := hTMc.trans hMcn
  have hXn : X ≤ Subgroup.normalizer (L : Set G) :=
    sup_le Subgroup.le_normalizer hTn
  have hLnorm : ∀ x ∈ X, ∀ l ∈ L, x * l * x⁻¹ ∈ L := fun x hx l hl =>
    (Subgroup.mem_normalizer_iff.1 (hXn hx) l).1 hl
  have hTS : IsSylowTwoOf T X := isSylowTwoOf_of_le151 hT hTX
  have hTHS : IsSylowTwoOf T H := isSylowTwoOf_of_le151 hT hTH
  have hHX : H ≤ X := by
    rw [← F112W.sup_oTwoUpper_eq_of_isSylowTwoOf hTHS]
    exact sup_le hTX (hKL.trans hLX)
  have hQT : pCoreOf 2 X ≤ T := hTS.pCoreOf_le
  have hQH : pCoreOf 2 X ≤ H := hQT.trans hTH
  have hQX : pCoreOf 2 X ≤ X := pCoreOf_le 2 X
  have hQnorm : H ≤ Subgroup.normalizer (pCoreOf 2 X : Set G) := fun h hh =>
    le_normalizer_pCoreOf 2 X (hHX hh)
  have hQN : pCoreOf 2 X ≤ pCoreOf 2 H :=
    le_pCoreOf_of_le_normalizer 2 hQH hQnorm (pCoreOf_isPGroup 2 X)
  have hHn : ∀ h ∈ H, ∀ n ∈ pCoreOf 2 H, h * n * h⁻¹ ∈ pCoreOf 2 H := fun h hh n hn =>
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 H hh) n).1 hn
  obtain ⟨P, hPH, hP9⟩ := exists_subgroup_card_nine (pCoreOf_isPGroup 2 H) hHcard
  have hP3 : IsPGroup 3 P := IsPGroup.of_card (n := 2) (by rw [hP9]; norm_num)
  have hPL : P ≤ L := (le_oTwoUpper_of_isPGroup_three hPH hP3).trans hKL
  refine ⟨P, ⟨normal_imageOTwoQuot hLnorm, prod_imageOTwoQuot rfl hTn,
    isSylowTwoOf_imageOTwoQuot_top hTS, imageOTwoQuot_mono hTH,
    imageOTwoQuot_mono (pCoreOf_le 2 H), imageOTwoQuot_conj_mem' hHn,
    isPGroup_imageOTwoQuot' (pCoreOf_isPGroup 2 H), ?_, imageOTwoQuot_mono hPH,
    imageOTwoQuot_mono hPL, ?_⟩, ?_⟩
  · have h1 := card_imageOTwoQuot_mul (X := X) (Z := H) hHX
    have h2 := card_imageOTwoQuot_mul (X := X) (Z := pCoreOf 2 H) ((pCoreOf_le 2 H).trans hHX)
    rw [inf_eq_right.2 hQH] at h1
    rw [inf_eq_right.2 hQN] at h2
    have hQpos : 0 < Nat.card (pCoreOf 2 X) := Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_right hQpos
    rw [h1, hHcard, ← h2]
    ring
  · have h1 := card_imageOTwoQuot_mul (X := X) (Z := P) (hPH.trans hHX)
    have hbot : P ⊓ pCoreOf 2 X = ⊥ :=
      (IsPGroup.disjoint_of_ne 3 2 (by norm_num) P (pCoreOf 2 X) hP3 (pCoreOf_isPGroup 2 X)).eq_bot
    rw [hbot, Subgroup.card_bot, mul_one, hP9] at h1
    exact h1
  · obtain ⟨φ, -⟩ := exists_mulEquiv_imageOTwoQuot hLX hXn
    exact ⟨φ⟩

end CFSG.Quasithin.He4
