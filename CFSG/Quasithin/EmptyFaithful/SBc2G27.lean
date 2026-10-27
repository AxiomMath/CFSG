module

public import CFSG.Quasithin.EmptyFaithful.S153G27
public import CFSG.Quasithin.EmptyFaithful.SBc2N34
public import CFSG.Quasithin.EmptyFaithful.SBc15343
public import CFSG.Quasithin.Vol2.Ch1Rank
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

namespace SBc2

section Conj

variable {G : Type} [Group G]

theorem ncard_conjSubgroupsBy_eq_index (H K : Subgroup G) :
    (conjSubgroupsBy H K).ncard = ((Subgroup.normalizer (K : Set G)).subgroupOf H).index := by
  let φ : ↥H →* MulAut G := MulAut.conj.comp H.subtype
  let _ : MulAction ↥H (Subgroup G) := MulAction.compHom (Subgroup G) φ
  have hsmul : ∀ (h : ↥H) (X : Subgroup G), h • X = X.map (MulAut.conj (h : G)).toMonoidHom :=
    fun h X => rfl
  have hstab : MulAction.stabilizer ↥H K = (Subgroup.normalizer (K : Set G)).subgroupOf H := by
    ext h
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, hsmul,
      Subgroup.mem_normalizer_iff_map_conj_eq]
    exact Iff.rfl
  have horb : MulAction.orbit ↥H K = conjSubgroupsBy H K := by
    ext X
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨h, h.2, hsmul h K⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, ht⟩, hsmul ⟨t, ht⟩ K⟩
  rw [← hstab, MulAction.index_stabilizer, horb]

theorem exists_not_mem_normalizer_of_ncard_two {T H K : Subgroup G} (hT : IsSylowTwoOf T H)
    (hK : (conjSubgroupsBy H K).ncard = 2) : ∃ t ∈ T, t ∉ Subgroup.normalizer (K : Set G) := by
  by_contra h
  push Not at h
  rw [ncard_conjSubgroupsBy_eq_index] at hK
  have hle : T.subgroupOf H ≤ (Subgroup.normalizer (K : Set G)).subgroupOf H := fun t ht =>
    Subgroup.mem_subgroupOf.mpr (h t (Subgroup.mem_subgroupOf.mp ht))
  have hdvd := Subgroup.index_dvd_of_le hle
  rw [hK] at hdvd
  exact hT.2.2 hdvd

theorem map_conj_map_conj (g s : G) (K : Subgroup G) :
    (K.map (MulAut.conj s).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      K.map (MulAut.conj (g * s)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem swap_dichotomy {I L : Subgroup G} {s : G} (hs : s ∈ I)
    (hmem : ∀ K ∈ conjSubgroupsBy I L, K = L ∨ K = L.map (MulAut.conj s).toMonoidHom)
    (hne : L ≠ L.map (MulAut.conj s).toMonoidHom) {g : G} (hg : g ∈ I) :
    (L.map (MulAut.conj g).toMonoidHom = L ∧
        (L.map (MulAut.conj s).toMonoidHom).map (MulAut.conj g).toMonoidHom =
          L.map (MulAut.conj s).toMonoidHom) ∨
      (L.map (MulAut.conj g).toMonoidHom = L.map (MulAut.conj s).toMonoidHom ∧
        (L.map (MulAut.conj s).toMonoidHom).map (MulAut.conj g).toMonoidHom = L) := by
  have h1 := hmem _ ⟨g, hg, rfl⟩
  have h2 := hmem _ ⟨g * s, I.mul_mem hg hs, map_conj_map_conj g s L⟩
  have hinj : Function.Injective (Subgroup.map (MulAut.conj g).toMonoidHom) :=
    Subgroup.map_injective (MulAut.conj g).injective
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact absurd (hinj (h1.trans h2.symm)) hne
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact absurd (hinj (h1.trans h2.symm)) hne

theorem exists_swap [Finite G] {S I L : Subgroup G} (hS : IsSylowTwoOf S I) (hL : L ∈ cComp I)
    (hcard : (conjSubgroupsBy I L).ncard = 2) :
    ∃ s ∈ S, L ≠ L.map (MulAut.conj s).toMonoidHom ∧ L.map (MulAut.conj s).toMonoidHom ∈ cComp I ∧
      ∀ K ∈ conjSubgroupsBy I L, K = L ∨ K = L.map (MulAut.conj s).toMonoidHom := by
  classical
  obtain ⟨s, hs, hsn⟩ := exists_not_mem_normalizer_of_ncard_two hS hcard
  have hSI := hS.1
  have hL'mem : L.map (MulAut.conj s).toMonoidHom ∈ cComp I := map_conj_mem_cComp hL (hSI hs)
  have hLne : L ≠ L.map (MulAut.conj s).toMonoidHom := fun h =>
    hsn (A38.map_conj_eq_iff.mp h.symm)
  have hL''mem' : L.map (MulAut.conj s).toMonoidHom ∈ conjSubgroupsBy I L := ⟨s, hSI hs, rfl⟩
  have hLmem' : L ∈ conjSubgroupsBy I L := ⟨1, I.one_mem, by ext x; simp⟩
  refine ⟨s, hs, hLne, hL'mem, ?_⟩
  obtain ⟨x, y, hxy, hset⟩ := Set.ncard_eq_two.mp hcard
  intro K hK
  have hK' := hK
  have h1 := hLmem'
  have h2 := hL''mem'
  rw [hset] at hK' h1 h2
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hK' h1 h2
  rcases hK' with rfl | rfl <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
    first | exact Or.inl h1.symm | exact Or.inr h2.symm | (exfalso; exact hLne (h1.trans h2.symm))

end Conj

section Component

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_pCoreOf_of_mem_sup {I L L' Q : Subgroup G} (hL : L ∈ cComp I)
    (hsimple : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L)) (hQ2 : IsPGroup 2 Q)
    (hLQ : L ≤ Subgroup.normalizer (Q : Set G)) (hL'Q : L' ≤ Subgroup.normalizer (Q : Set G))
    (hcQ : ⁅L, L'⁆ ≤ Q) {l : G} (hl : l ∈ L) (hl' : l ∈ L' ⊔ Q) : l ∈ pCoreOf 2 L := by
  obtain ⟨l'', hl'', q'', hq'', hlq⟩ := exists_mul_of_mem_sup_of_le_normalizer hL'Q hl'
  have hQL : Q ⊓ L ≤ pCoreOf 2 L := by
    refine le_pCoreOf_of_le_normalizer 2 inf_le_right ?_ (hQ2.to_le inf_le_left)
    intro g hg
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hLQ hg, Subgroup.le_normalizer hg⟩
  refine S153D.mem_pCoreOf_of_commutators hL hsimple hl fun g hg => hQL ⟨?_, ?_⟩
  · have hu : g * q'' * g⁻¹ * q''⁻¹ ∈ Q :=
      Q.mul_mem ((Subgroup.mem_normalizer_iff.mp (hLQ hg) q'').mp hq'') (Q.inv_mem hq'')
    have h1 : l'' * (g * q'' * g⁻¹ * q''⁻¹) * l''⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hL'Q hl'') _).mp hu
    have h2 : g * l'' * g⁻¹ * l''⁻¹ ∈ Q := hcQ (Subgroup.commutator_mem_commutator hg hl'')
    have e : g * l * g⁻¹ * l⁻¹ =
        (g * l'' * g⁻¹ * l''⁻¹) * (l'' * (g * q'' * g⁻¹ * q''⁻¹) * l''⁻¹) := by
      rw [← hlq]
      group
    rw [e]
    exact Q.mul_mem h2 h1
  · exact L.mul_mem (L.mul_mem (L.mul_mem hg hl) (L.inv_mem hg)) (L.inv_mem hl)

omit [Finite G] in
theorem mem_of_mul_two_pow {H N : Subgroup G} (hNH : N ≤ H) (hHN : H ≤ Subgroup.normalizer (N : Set G))
    {u w x : G} (hu : u ∈ N) (hw : w ∈ H) (hx : x ∈ H) (hxuw : x = u * w) {j : ℕ} (hwj : w ^ 2 ^ j = 1)
    (hx3 : x ^ 3 = 1) : x ∈ N := by
  have hNn : (N.subgroupOf H).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mpr hHN
  set f := QuotientGroup.mk' (N.subgroupOf H) with hf
  have hu' : f ⟨u, hNH hu⟩ = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hu)
  have hfx : f ⟨x, hx⟩ = f ⟨w, hw⟩ := by
    have : (⟨x, hx⟩ : ↥H) = ⟨u, hNH hu⟩ * ⟨w, hw⟩ := Subtype.ext hxuw
    rw [this, map_mul, hu', one_mul]
  have h3 : f ⟨x, hx⟩ ^ 3 = 1 := by
    rw [← map_pow, show (⟨x, hx⟩ : ↥H) ^ 3 = 1 from Subtype.ext hx3, map_one]
  have h2 : f ⟨x, hx⟩ ^ 2 ^ j = 1 := by
    rw [hfx, ← map_pow, show (⟨w, hw⟩ : ↥H) ^ 2 ^ j = 1 from Subtype.ext hwj, map_one]
  have hd3 := orderOf_dvd_of_pow_eq_one h3
  have hd2 := orderOf_dvd_of_pow_eq_one h2
  have hcop : Nat.Coprime 3 (2 ^ j) := Nat.Coprime.pow_right j (by norm_num)
  have hd : orderOf (f ⟨x, hx⟩) ∣ Nat.gcd 3 (2 ^ j) := Nat.dvd_gcd hd3 hd2
  rw [hcop.gcd_eq_one] at hd
  have h1 : f ⟨x, hx⟩ = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)
  exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1)

theorem mem_of_order_three {Yp H N : Subgroup G} (hcard : Nat.card (OTwoQuot Yp) = 3) (hYH : Yp ≤ H)
    (hNH : N ≤ H) (hHN : H ≤ Subgroup.normalizer (N : Set G)) {a b : G} (ha : a ∈ Yp)
    (ha3 : orderOf a = 3) (haN : a ∈ N) (hb : b ∈ Yp) (hb3 : b ^ 3 = 1) : b ∈ N := by
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Q : Subgroup G := pCoreOf 2 Yp with hQdef
  have hQ2 : IsPGroup 2 Q := pCoreOf_isPGroup 2 Yp
  have hQY : Q ≤ Yp := pCoreOf_le 2 Yp
  have hmemQ' : ∀ g : ↥Yp, g ∈ CFSG.Open.pCore 2 ↥Yp ↔ (g : G) ∈ Q := fun g =>
    (Subgroup.mem_map_iff_mem Yp.subtype_injective).symm
  have hmemQ : ∀ g : ↥Yp, (QuotientGroup.mk g : OTwoQuot Yp) = 1 ↔ (g : G) ∈ Q := fun g =>
    (QuotientGroup.eq_one_iff g).trans (hmemQ' g)
  have habar1 : (QuotientGroup.mk (⟨a, ha⟩ : ↥Yp) : OTwoQuot Yp) ≠ 1 := by
    intro h
    have haQ : a ∈ Q := (hmemQ ⟨a, ha⟩).mp h
    obtain ⟨j, hj⟩ := hQ2 ⟨a, haQ⟩
    have hj' : a ^ 2 ^ j = 1 := congrArg Subtype.val hj
    have hd : 3 ∣ 2 ^ j := ha3 ▸ orderOf_dvd_of_pow_eq_one hj'
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow hd)
    omega
  have hgen : Subgroup.zpowers (QuotientGroup.mk (⟨a, ha⟩ : ↥Yp) : OTwoQuot Yp) = ⊤ :=
    zpowers_eq_top_of_prime_card hcard habar1
  have hbbar : (QuotientGroup.mk (⟨b, hb⟩ : ↥Yp) : OTwoQuot Yp) ∈
      Subgroup.zpowers (QuotientGroup.mk (⟨a, ha⟩ : ↥Yp) : OTwoQuot Yp) := by
    rw [hgen]
    trivial
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hbbar
  have hk' : (QuotientGroup.mk ((⟨a, ha⟩ : ↥Yp) ^ k) : OTwoQuot Yp) = QuotientGroup.mk ⟨b, hb⟩ := by
    rw [QuotientGroup.mk_zpow]
    exact hk
  have hqmem : ((⟨a, ha⟩ : ↥Yp) ^ k)⁻¹ * ⟨b, hb⟩ ∈ CFSG.Open.pCore 2 ↥Yp := QuotientGroup.eq.mp hk'
  have hq : (a ^ k)⁻¹ * b ∈ Q := by
    have h := (hmemQ' _).mp hqmem
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow] using h
  obtain ⟨j, hj⟩ := hQ2 ⟨(a ^ k)⁻¹ * b, hq⟩
  have hwj : ((a ^ k)⁻¹ * b) ^ 2 ^ j = 1 := congrArg Subtype.val hj
  exact mem_of_mul_two_pow hNH hHN (u := a ^ k) (w := (a ^ k)⁻¹ * b) (zpow_mem haN k)
    (hYH (hQY hq)) (hYH hb) (by group) hwj hb3

end Component

section Struct

variable {G : Type} [Group G] [Finite G]

theorem card_eq_three_of_exponent_three {P : Type} [Group P] [Finite P] (hexp : ∀ z : P, z ^ 3 = 1)
    (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup P) ≤ 1) (hne : ∃ z : P, z ≠ 1) : Nat.card P = 3 := by
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP : IsPGroup 3 P := fun z => ⟨1, by simpa using hexp z⟩
  obtain ⟨z₁, hz₁⟩ := hne
  have : Nontrivial P := ⟨⟨z₁, 1, hz₁⟩⟩
  have hcen : Nontrivial ↥(Subgroup.center P) := hP.center_nontrivial
  obtain ⟨c, hc⟩ := exists_ne (1 : ↥(Subgroup.center P))
  have hz1 : (c : P) ≠ 1 := fun h => hc (Subtype.ext h)
  have htop : Subgroup.zpowers (c : P) = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    by_cases hx1 : x = 1
    · rw [hx1]
      exact Subgroup.one_mem _
    · exact SBc.mem_zpowers_of_commute_of_pRank (H := ⊤) hrank (Subgroup.mem_top _) (Subgroup.mem_top _)
        hz1 (hexp _) (hexp _) ((Subgroup.mem_center_iff.mp c.2 x).symm)
  have h3 : orderOf (c : P) = 3 := orderOf_eq_prime (hexp _) hz1
  rw [← Subgroup.card_top (G := P), ← htop, Nat.card_zpowers, h3]

theorem card_OTwoQuot_eq_three {T Mc M V₁ V₂ Yp : Subgroup G} {t : G} (h113 : StageLemma14113)
    (h : Hyp15310 G T Mc M V₁ V₂ Yp t) (hr : CFSG.Open.pRank 3 Yp = 1) {y : G} (hy : y ∈ Yp)
    (hy3 : orderOf y = 3) : Nat.card (OTwoQuot Yp) = 3 := by
  have hp2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hYY : Yp ≤ Y153 Mc M := h.Yp_le_Y153
  have hmemQ' : ∀ g : ↥Yp, g ∈ CFSG.Open.pCore 2 ↥Yp ↔ (g : G) ∈ pCoreOf 2 Yp := fun g =>
    (Subgroup.mem_map_iff_mem Yp.subtype_injective).symm
  have hexp : ∀ z : OTwoQuot Yp, z ^ 3 = 1 := by
    intro z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hmemQ']
    have h1 : (x : G) ^ 3 ∈ pCoreOf 2 (Y153 Mc M) := h.hyp.pow_three_mem_pCoreOf_Y153 h113 (hYY x.2)
    have hnorm : Yp ≤ Subgroup.normalizer ((Yp ⊓ pCoreOf 2 (Y153 Mc M) : Subgroup G) : Set G) :=
      fun g hg => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hg, le_normalizer_pCoreOf 2 _ (hYY hg)⟩
    exact le_pCoreOf_of_le_normalizer 2 (inf_le_left : Yp ⊓ pCoreOf 2 (Y153 Mc M) ≤ Yp) hnorm
      ((pCoreOf_isPGroup 2 (Y153 Mc M)).to_le inf_le_right) ⟨Yp.pow_mem x.2 3, h1⟩
  have hrank : CFSG.Open.pRank 3 (⊤ : Subgroup (OTwoQuot Yp)) ≤ 1 := by
    have hnd : ¬ 3 ∣ Nat.card (CFSG.Open.pCore 2 ↥Yp) := by
      intro hd
      obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥Yp) 2).exists_card_eq
      rw [hk] at hd
      exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.prime_three.dvd_of_dvd_pow hd)) (by norm_num)
    have e2 := CFSG.SectionRank.pRank_quotient_eq (p := 3) (CFSG.Open.pCore 2 ↥Yp) hnd
    have e3 := pRank_top_subtype (p := 3) Yp
    calc CFSG.Open.pRank 3 (⊤ : Subgroup (OTwoQuot Yp))
        = CFSG.Open.pRank 3 (⊤ : Subgroup ↥Yp) := e2
      _ = CFSG.Open.pRank 3 Yp := e3
      _ ≤ 1 := hr.le
  have hne : ∃ z : OTwoQuot Yp, z ≠ 1 := by
    refine ⟨QuotientGroup.mk (⟨y, hy⟩ : ↥Yp), fun hz => ?_⟩
    have hyQ : y ∈ pCoreOf 2 Yp := (hmemQ' ⟨y, hy⟩).mp ((QuotientGroup.eq_one_iff _).mp hz)
    obtain ⟨j, hj⟩ := (pCoreOf_isPGroup 2 Yp : IsPGroup 2 ↥(pCoreOf 2 Yp)) ⟨y, hyQ⟩
    have hj' : y ^ 2 ^ j = 1 := congrArg Subtype.val hj
    have hd : 3 ∣ 2 ^ j := hy3 ▸ orderOf_dvd_of_pow_eq_one hj'
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow hd)
    omega
  exact card_eq_three_of_exponent_three hexp hrank hne

end Struct

section Solvable

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isSolvable_of_le_sup {X Y N : Subgroup G} (hX : X ≤ Y ⊔ N)
    (hY : Y ≤ Subgroup.normalizer (N : Set G)) (hYs : Group.IsSolvable ↥Y)
    (hXN : Group.IsSolvable ↥(X ⊓ N)) : Group.IsSolvable ↥X := by
  have hKN : Y ⊔ N ≤ Subgroup.normalizer (N : Set G) := sup_le hY Subgroup.le_normalizer
  have hnorm : (N.subgroupOf (Y ⊔ N)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr hKN
  have hquot : Group.IsSolvable (↥(Y ⊔ N) ⧸ N.subgroupOf (Y ⊔ N)) := by
    refine Group.isSolvable_of_surjective
      (f := (QuotientGroup.mk' (N.subgroupOf (Y ⊔ N))).comp
        (Subgroup.inclusion (le_sup_left : Y ≤ Y ⊔ N))) ?_
    intro z
    induction z using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨a, ha, b, hb, hx⟩ := exists_mul_of_mem_sup_of_le_normalizer hY x.2
      refine ⟨⟨a, ha⟩, ?_⟩
      show (QuotientGroup.mk (⟨a, _⟩ : ↥(Y ⊔ N)) : ↥(Y ⊔ N) ⧸ N.subgroupOf (Y ⊔ N)) =
        QuotientGroup.mk x
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have : (((⟨a, Subgroup.mem_sup_left ha⟩ : ↥(Y ⊔ N))⁻¹ * x : ↥(Y ⊔ N)) : G) = a⁻¹ * (a * b) := by
        simp [hx]
      rw [this]
      simpa using hb
  refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion (inf_le_left : X ⊓ N ≤ X))
    ((QuotientGroup.mk' (N.subgroupOf (Y ⊔ N))).comp (Subgroup.inclusion hX)) ?_
  intro x hx
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hx
  exact ⟨⟨(x : G), x.2, hx⟩, rfl⟩

end Solvable

section Main

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem three_dvd_orderOf {H N : Subgroup G} (hNH : N ≤ H) (hHN : H ≤ Subgroup.normalizer (N : Set G))
    {l y : G} (hl : l ∈ H) (hy : y ∈ H) (hyl : y⁻¹ * l ∈ N) (hlN : l ∉ N) (hy3 : y ^ 3 = 1) :
    3 ∣ orderOf l := by
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hNn : (N.subgroupOf H).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mpr hHN
  set f := QuotientGroup.mk' (N.subgroupOf H) with hf
  have heq : f ⟨y, hy⟩ = f ⟨l, hl⟩ := QuotientGroup.eq.mpr (Subgroup.mem_subgroupOf.mpr hyl)
  have hne : f ⟨l, hl⟩ ≠ 1 := fun h =>
    hlN (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h))
  have h3 : f ⟨l, hl⟩ ^ 3 = 1 := by
    rw [← heq, ← map_pow, show (⟨y, hy⟩ : ↥H) ^ 3 = 1 from Subtype.ext hy3, map_one]
  have hord : orderOf (f ⟨l, hl⟩) = 3 := orderOf_eq_prime h3 hne
  have hdvd : orderOf (f ⟨l, hl⟩) ∣ orderOf (⟨l, hl⟩ : ↥H) := orderOf_map_dvd f _
  rw [hord, Subgroup.orderOf_mk] at hdvd
  exact hdvd

omit [Finite G] in
theorem not_mem_of_orderOf_three {Q : Subgroup G} (hQ : IsPGroup 2 Q) {y : G} (hy : orderOf y = 3) :
    y ∉ Q := by
  intro hyQ
  obtain ⟨j, hj⟩ := hQ ⟨y, hyQ⟩
  have hj' : y ^ 2 ^ j = 1 := congrArg Subtype.val hj
  have hd : 3 ∣ 2 ^ j := hy ▸ orderOf_dvd_of_pow_eq_one hj'
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
    (Nat.prime_three.dvd_of_dvd_pow hd)
  omega

omit [Finite G] in
theorem map_piece (g : G) (A B Y Q : Subgroup G) (hY : Y.map (MulAut.conj g).toMonoidHom = Y)
    (hQ : Q.map (MulAut.conj g).toMonoidHom = Q) :
    (A ⊓ (Y ⊔ (B ⊔ Q))).map (MulAut.conj g).toMonoidHom =
      A.map (MulAut.conj g).toMonoidHom ⊓ (Y ⊔ (B.map (MulAut.conj g).toMonoidHom ⊔ Q)) := by
  rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective, Subgroup.map_sup, Subgroup.map_sup, hY, hQ]

end Main

section Final

theorem input27Normal_holds (h113 : StageLemma14113) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h122 : Lemma122A) : Input27Normal := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c _hB56
  classical
  by_contra hnot
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.ctx.hyp
  have hq := hh.hyp.qtfe
  have hLJ : L ∈ cComp (thompsonJ I) := c.conc.1
  have hLI : L ∈ cComp I := S153D.mem_cComp_of_mem_cComp_thompsonJ hLJ
  have hLle : L ≤ I := le_of_mem_cComp hLI
  have hS : IsSylowTwoOf (Sgp153 T V₁) I := c.facts.sylow
  have hSI : Sgp153 T V₁ ≤ I := hS.1
  have hYI : Yp ≤ I := le_sup_left.trans c.ctx.inH.1.1
  have hH : pCoreOf 2 I ≠ ⊥ := c.ctx.inH.1.2
  have hnotnormal : ¬ (L.subgroupOf I).Normal := fun hn =>
    hnot ((Subgroup.normal_subgroupOf_iff_le_normalizer hLle).mp hn)
  rcases lemma_1_2_1_three hq.qtke hq.simple hq.nonabelian h37 h38 hH hLI with hn | ⟨hcard, htypes⟩
  · exact hnotnormal hn
  obtain ⟨s, hs, hLne, hL'I, hmem⟩ := exists_swap hS hLI hcard
  set L' : Subgroup G := L.map (MulAut.conj s).toMonoidHom with hL'def
  have hsI : s ∈ I := hSI hs
  have hL'le : L' ≤ I := le_of_mem_cComp hL'I
  have hdich : ∀ g ∈ I,
      (L.map (MulAut.conj g).toMonoidHom = L ∧ L'.map (MulAut.conj g).toMonoidHom = L') ∨
        (L.map (MulAut.conj g).toMonoidHom = L' ∧ L'.map (MulAut.conj g).toMonoidHom = L) :=
    fun g hg => swap_dichotomy hsI hmem hLne hg
  have hL'swap : L'.map (MulAut.conj s).toMonoidHom = L := by
    rcases hdich s hsI with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact absurd h1.symm hLne
    · exact h2
  have hsimple : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) :=
    CFSG.QuasithinUnique.Vol2Native.L122A.isSimpleGroup_of_a38Types htypes
  have hsimple' : IsSimpleGroup (↥L' ⧸ CFSG.pCore 2 ↥L') := by
    rcases lemma_1_2_1_three hq.qtke hq.simple hq.nonabelian h37 h38 hH hL'I with hn' | ⟨-, htypes'⟩
    · exfalso
      have hIN : I ≤ Subgroup.normalizer (L' : Set G) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hL'le).mp hn'
      have h1 : L'.map (MulAut.conj s).toMonoidHom = L' := A38.map_conj_eq_iff.mpr (hIN hsI)
      exact hLne (hL'swap.symm.trans h1)
    · exact CFSG.QuasithinUnique.Vol2Native.L122A.isSimpleGroup_of_a38Types htypes'
  have hc : ⁅L, L'⁆ ≤ pCoreOf 2 L ⊓ pCoreOf 2 L' :=
    (lemma_1_2_1_two hq.qtke hq.simple hq.nonabelian h37 hH hLI hL'I hLne).1
  have hLN := le_normalizer_of_commutator_le hc
  have hL₀I : L ⊔ L' ≤ I := sup_le hLle hL'le
  have hnorm : I ⊓ Subgroup.normalizer (Yp : Set G) = M ⊓ I := c.facts.norm_eq
  have hSN : Sgp153 T V₁ ≤ Subgroup.normalizer (Yp : Set G) := by
    intro s' hs'
    have hsM : s' ∈ M ⊓ I := ⟨hh.hyp.T_le hs'.1, hSI hs'⟩
    rw [← hnorm] at hsM
    exact hsM.2
  have htheta : Yp = thetaOf (M ⊓ I) := c.facts.theta
  have hgenY : ∀ z ∈ M ⊓ I, orderOf z = 3 → z ∈ Yp := fun z hz hzo => by
    rw [htheta]
    exact Subgroup.subset_closure ⟨hz, hzo⟩
  have hYL₀ : Yp ≤ L ⊔ L' := by
    have hdvd : 3 ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := by
      have hr := pRank_modO2_eq L Nat.prime_three (by norm_num)
      obtain ⟨E, -, -, hE⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3)
        (⊤ : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L))
      have h3 : 3 ∣ Nat.card E := by
        rw [hE, hr]
        exact dvd_pow_self 3 (by have := c.conc.2.2.1; omega)
      exact h3.trans (Subgroup.card_subgroup_dvd_card E)
    have h122' := h122 G hq.simple hq.qtke hq.nonabelian I L hH hLI 3 Nat.prime_three (by norm_num)
      hcard hdvd
    have hcc : conjClosure L I ≤ L ⊔ L' := by
      refine conjClosure_le fun g hg l hl => ?_
      have hgl : g * l * g⁻¹ ∈ L.map (MulAut.conj g).toMonoidHom := ⟨l, hl, rfl⟩
      rcases hdich g hg with ⟨h1, -⟩ | ⟨h1, -⟩
      · rw [h1] at hgl
        exact Subgroup.mem_sup_left hgl
      · rw [h1] at hgl
        exact Subgroup.mem_sup_right hgl
    have hYle : Yp ≤ Subgroup.closure {x : G | x ∈ I ∧ ∃ k : ℕ, orderOf x = 3 ^ k} := by
      calc Yp = oTwoUpper Yp := hh.oTwoUpper_eq.symm
        _ ≤ _ := by
          rw [oTwoUpper, Subgroup.closure_le]
          rintro x ⟨hx, hodd⟩
          refine Subgroup.subset_closure ⟨hYI hx, ?_⟩
          have hx3 := pow_three_eq_one_of_odd h113 hh.hyp (hh.Yp_le_Y153 hx) hodd
          have hd : orderOf x ∣ 3 ^ 1 := by simpa using orderOf_dvd_of_pow_eq_one hx3
          obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd
          exact ⟨i, hi⟩
    exact hYle.trans (h122'.le.trans hcc)
  obtain ⟨y, hyY, hy3⟩ : ∃ y ∈ Yp, orderOf y = 3 := by
    obtain ⟨E, hEY, hE, hE9⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3) Yp
    rw [c.ctx.rank] at hE9
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥E) 3 (by rw [hE9]; norm_num)
    exact ⟨(z : G), hEY z.2, by rw [Subgroup.orderOf_coe, hz]⟩
  have hy3' : y ^ 3 = 1 := hy3 ▸ pow_orderOf_eq_one y
  have hcard3 : Nat.card (OTwoQuot Yp) = 3 := card_OTwoQuot_eq_three h113 hh c.ctx.rank hyY hy3
  have hL₀L : L ⊔ L' ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hLN.2
  have hL₀L' : L ⊔ L' ≤ Subgroup.normalizer (L' : Set G) := sup_le hLN.1 Subgroup.le_normalizer
  have hQ2 : IsPGroup 2 (pCoreOf 2 (L ⊔ L')) := pCoreOf_isPGroup 2 (L ⊔ L')
  have hQn : L ⊔ L' ≤ Subgroup.normalizer (pCoreOf 2 (L ⊔ L') : Set G) :=
    le_normalizer_pCoreOf 2 (L ⊔ L')
  have hQL₀ : pCoreOf 2 (L ⊔ L') ≤ L ⊔ L' := pCoreOf_le 2 (L ⊔ L')
  have hLL₀ : L ≤ L ⊔ L' := le_sup_left
  have hL'L₀ : L' ≤ L ⊔ L' := le_sup_right
  have hOL : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ L') := le_pCoreOf_of_le_normalizer 2
    ((pCoreOf_le 2 L).trans hLL₀)
    (fun g hg => normalizer_le_normalizer_pCoreOf 2 L (hL₀L hg)) (pCoreOf_isPGroup 2 L)
  have hOL' : pCoreOf 2 L' ≤ pCoreOf 2 (L ⊔ L') := le_pCoreOf_of_le_normalizer 2
    ((pCoreOf_le 2 L').trans hL'L₀)
    (fun g hg => normalizer_le_normalizer_pCoreOf 2 L' (hL₀L' hg)) (pCoreOf_isPGroup 2 L')
  have hcQ : ⁅L, L'⁆ ≤ pCoreOf 2 (L ⊔ L') := hc.trans (inf_le_left.trans hOL)
  have hcQ' : ⁅L', L⁆ ≤ pCoreOf 2 (L ⊔ L') := by
    rw [Subgroup.commutator_comm]
    exact hcQ
  have hT5 : ∀ l ∈ L, l ∈ L' ⊔ pCoreOf 2 (L ⊔ L') → l ∈ pCoreOf 2 (L ⊔ L') := fun l hl hl' =>
    hOL (mem_pCoreOf_of_mem_sup hLI hsimple hQ2 (hQn.trans' hLL₀) (hQn.trans' hL'L₀) hcQ hl hl')
  have hT5' : ∀ l ∈ L', l ∈ L ⊔ pCoreOf 2 (L ⊔ L') → l ∈ pCoreOf 2 (L ⊔ L') := fun l hl hl' =>
    hOL' (mem_pCoreOf_of_mem_sup hL'I hsimple' hQ2 (hQn.trans' hL'L₀) (hQn.trans' hLL₀) hcQ' hl hl')
  have hL₀map : ∀ g ∈ I, (L ⊔ L').map (MulAut.conj g).toMonoidHom = L ⊔ L' := by
    intro g hg
    rw [Subgroup.map_sup]
    rcases hdich g hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, sup_comm]
  have hQmap : ∀ g ∈ I, (pCoreOf 2 (L ⊔ L')).map (MulAut.conj g).toMonoidHom = pCoreOf 2 (L ⊔ L') :=
    fun g hg => A38.map_conj_eq_iff.mpr
      (normalizer_le_normalizer_pCoreOf 2 (L ⊔ L') (A38.map_conj_eq_iff.mp (hL₀map g hg)))
  have hYmap : ∀ g ∈ Sgp153 T V₁, Yp.map (MulAut.conj g).toMonoidHom = Yp := fun g hg =>
    A38.map_conj_eq_iff.mpr (hSN hg)
  have hN₁H : L' ⊔ pCoreOf 2 (L ⊔ L') ≤ L ⊔ L' := sup_le hL'L₀ hQL₀
  have hN₂H : L ⊔ pCoreOf 2 (L ⊔ L') ≤ L ⊔ L' := sup_le hLL₀ hQL₀
  have hHN₁ : L ⊔ L' ≤ Subgroup.normalizer ((L' ⊔ pCoreOf 2 (L ⊔ L') : Subgroup G) : Set G) :=
    fun g hg => mem_normalizer_sup (hL₀L' hg) (hQn hg)
  have hHN₂ : L ⊔ L' ≤ Subgroup.normalizer ((L ⊔ pCoreOf 2 (L ⊔ L') : Subgroup G) : Set G) :=
    fun g hg => mem_normalizer_sup (hL₀L hg) (hQn hg)
  have hN₁map : (L' ⊔ pCoreOf 2 (L ⊔ L')).map (MulAut.conj s).toMonoidHom =
      L ⊔ pCoreOf 2 (L ⊔ L') := by
    rw [Subgroup.map_sup, hL'swap, hQmap s hsI]
  have hN₂map : (L ⊔ pCoreOf 2 (L ⊔ L')).map (MulAut.conj s).toMonoidHom =
      L' ⊔ pCoreOf 2 (L ⊔ L') := by
    rw [Subgroup.map_sup, hQmap s hsI]
  have hswapN : ∀ z ∈ Yp, orderOf z = 3 →
      (z ∈ L' ⊔ pCoreOf 2 (L ⊔ L') → z ∈ L ⊔ pCoreOf 2 (L ⊔ L')) ∧
        (z ∈ L ⊔ pCoreOf 2 (L ⊔ L') → z ∈ L' ⊔ pCoreOf 2 (L ⊔ L')) := by
    intro z hz hz3
    have hzs : s * z * s⁻¹ ∈ Yp := (Subgroup.mem_normalizer_iff.mp (hSN hs) z).mp hz
    have hzs3 : orderOf (s * z * s⁻¹) = 3 := by
      have := orderOf_injective (MulAut.conj s).toMonoidHom (MulAut.conj s).injective z
      simpa [MulAut.conj_apply] using this.trans hz3
    have hz3' : z ^ 3 = 1 := hz3 ▸ pow_orderOf_eq_one z
    constructor
    · intro h1
      have h2 : s * z * s⁻¹ ∈ (L' ⊔ pCoreOf 2 (L ⊔ L')).map (MulAut.conj s).toMonoidHom := ⟨z, h1, rfl⟩
      rw [hN₁map] at h2
      exact mem_of_order_three hcard3 hYL₀ hN₂H hHN₂ hzs hzs3 h2 hz hz3'
    · intro h1
      have h2 : s * z * s⁻¹ ∈ (L ⊔ pCoreOf 2 (L ⊔ L')).map (MulAut.conj s).toMonoidHom := ⟨z, h1, rfl⟩
      rw [hN₂map] at h2
      exact mem_of_order_three hcard3 hYL₀ hN₁H hHN₁ hzs hzs3 h2 hz hz3'
  have hYs : Group.IsSolvable ↥Yp := S153D.isSolvable_of_le_Y153 h113 hh.hyp hh.Yp_le_Y153
  have hYN₁ : Yp ≤ Subgroup.normalizer ((L' ⊔ pCoreOf 2 (L ⊔ L') : Subgroup G) : Set G) :=
    fun g hg => hHN₁ (hYL₀ hg)
  have hYN₂ : Yp ≤ Subgroup.normalizer ((L ⊔ pCoreOf 2 (L ⊔ L') : Subgroup G) : Set G) :=
    fun g hg => hHN₂ (hYL₀ hg)
  have hXLs : Group.IsSolvable ↥(L ⊓ (Yp ⊔ (L' ⊔ pCoreOf 2 (L ⊔ L')))) := by
    refine isSolvable_of_le_sup (Y := Yp) (N := L' ⊔ pCoreOf 2 (L ⊔ L')) inf_le_right hYN₁ hYs ?_
    have hle : (L ⊓ (Yp ⊔ (L' ⊔ pCoreOf 2 (L ⊔ L')))) ⊓ (L' ⊔ pCoreOf 2 (L ⊔ L')) ≤
        pCoreOf 2 (L ⊔ L') := fun x hx => hT5 x hx.1.1 hx.2
    exact F1.isSolvable_of_isPGroup_two (hQ2.to_le hle)
  have hXL's : Group.IsSolvable ↥(L' ⊓ (Yp ⊔ (L ⊔ pCoreOf 2 (L ⊔ L')))) := by
    refine isSolvable_of_le_sup (Y := Yp) (N := L ⊔ pCoreOf 2 (L ⊔ L')) inf_le_right hYN₂ hYs ?_
    have hle : (L' ⊓ (Yp ⊔ (L ⊔ pCoreOf 2 (L ⊔ L')))) ⊓ (L ⊔ pCoreOf 2 (L ⊔ L')) ≤
        pCoreOf 2 (L ⊔ L') := fun x hx => hT5' x hx.1.1 hx.2
    exact F1.isSolvable_of_isPGroup_two (hQ2.to_le hle)
  have hXLn : (L ⊓ (Yp ⊔ (L' ⊔ pCoreOf 2 (L ⊔ L')))) ≤
      Subgroup.normalizer ((L' ⊓ (Yp ⊔ (L ⊔ pCoreOf 2 (L ⊔ L'))) : Subgroup G) : Set G) := by
    intro l hl
    refine A4.mem_normalizer_of_conj_mem fun x hx => ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hLN.1 hl.1) x).mp hx.1
    · have hcom : ⁅l, x⁆ ∈ pCoreOf 2 (L ⊔ L') :=
        hcQ (Subgroup.commutator_mem_commutator hl.1 hx.1)
      have e : l * x * l⁻¹ = ⁅l, x⁆ * x := by simp [commutatorElement_def, mul_assoc]
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_sup_right hcom)) hx.2
  have hXs : Group.IsSolvable ↥((L ⊓ (Yp ⊔ (L' ⊔ pCoreOf 2 (L ⊔ L')))) ⊔
      (L' ⊓ (Yp ⊔ (L ⊔ pCoreOf 2 (L ⊔ L'))))) := by
    have := F1.isSolvable_sup_of_le_normalizer hXL's hXLs hXLn
    rwa [sup_comm] at this
  have hXI : (L ⊓ (Yp ⊔ (L' ⊔ pCoreOf 2 (L ⊔ L')))) ⊔ (L' ⊓ (Yp ⊔ (L ⊔ pCoreOf 2 (L ⊔ L')))) ≤ I :=
    sup_le (inf_le_left.trans hLle) (inf_le_left.trans hL'le)
  have hdecomp_mem : ∀ y₀ ∈ Yp, ∀ l₀ ∈ L, ∀ l₀' ∈ L', l₀ * l₀' = y₀ →
      l₀ ∈ L ⊓ (Yp ⊔ (L' ⊔ pCoreOf 2 (L ⊔ L'))) ∧ l₀' ∈ L' ⊓ (Yp ⊔ (L ⊔ pCoreOf 2 (L ⊔ L'))) := by
    intro y₀ hy₀ l₀ hl₀ l₀' hl₀' hy
    refine ⟨⟨hl₀, ?_⟩, ⟨hl₀', ?_⟩⟩
    · have e : l₀ = y₀ * l₀'⁻¹ := by rw [← hy]; group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hy₀)
        (Subgroup.mem_sup_right (Subgroup.mem_sup_left (L'.inv_mem hl₀')))
    · have e : l₀' = l₀⁻¹ * y₀ := by rw [← hy]; group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_sup_left (L.inv_mem hl₀)))
        (Subgroup.mem_sup_left hy₀)
  have hYX : Yp ≤ (L ⊓ (Yp ⊔ (L' ⊔ pCoreOf 2 (L ⊔ L')))) ⊔ (L' ⊓ (Yp ⊔ (L ⊔ pCoreOf 2 (L ⊔ L')))) := by
    intro y₀ hy₀
    obtain ⟨l₀, hl₀, l₀', hl₀', hy⟩ := exists_mul_of_mem_sup_of_le_normalizer hLN.1 (hYL₀ hy₀)
    obtain ⟨h1, h2⟩ := hdecomp_mem y₀ hy₀ l₀ hl₀ l₀' hl₀' hy
    rw [← hy]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right h2)
  have hmapX : ∀ g ∈ Sgp153 T V₁,
      ((L ⊓ (Yp ⊔ (L' ⊔ pCoreOf 2 (L ⊔ L')))) ⊔ (L' ⊓ (Yp ⊔ (L ⊔ pCoreOf 2 (L ⊔ L'))))).map
        (MulAut.conj g).toMonoidHom =
      (L ⊓ (Yp ⊔ (L' ⊔ pCoreOf 2 (L ⊔ L')))) ⊔ (L' ⊓ (Yp ⊔ (L ⊔ pCoreOf 2 (L ⊔ L')))) := by
    intro g hg
    have hgI := hSI hg
    rw [Subgroup.map_sup, map_piece g L L' Yp _ (hYmap g hg) (hQmap g hgI),
      map_piece g L' L Yp _ (hYmap g hg) (hQmap g hgI)]
    rcases hdich g hgI with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, sup_comm]
  have hXn : Yp ⊔ Sgp153 T V₁ ≤ Subgroup.normalizer
      ((((L ⊓ (Yp ⊔ (L' ⊔ pCoreOf 2 (L ⊔ L')))) ⊔ (L' ⊓ (Yp ⊔ (L ⊔ pCoreOf 2 (L ⊔ L'))))) :
        Subgroup G) : Set G) :=
    sup_le (hYX.trans Subgroup.le_normalizer) (fun g hg => A38.map_conj_eq_iff.mp (hmapX g hg))
  have hXM := c.solv _ hXI hXs hXn
  obtain ⟨l, hl, l', hl', hly⟩ := exists_mul_of_mem_sup_of_le_normalizer hLN.1 (hYL₀ hyY)
  obtain ⟨hlX, hl'X⟩ := hdecomp_mem y hyY l hl l' hl' hly
  have hlM : l ∈ M ⊓ I := hXM (Subgroup.mem_sup_left hlX)
  have hl'M : l' ∈ M ⊓ I := hXM (Subgroup.mem_sup_right hl'X)
  have hyQ : y ∉ pCoreOf 2 (L ⊔ L') := not_mem_of_orderOf_three hQ2 hy3
  have hyN : y ∈ L' ⊔ pCoreOf 2 (L ⊔ L') → False := by
    intro h1
    have h2 : y ∈ L ⊔ pCoreOf 2 (L ⊔ L') := (hswapN y hyY hy3).1 h1
    have hlN : l ∈ L' ⊔ pCoreOf 2 (L ⊔ L') := by
      have e : l = y * l'⁻¹ := by rw [← hly]; group
      rw [e]
      exact Subgroup.mul_mem _ h1 (Subgroup.mem_sup_left (L'.inv_mem hl'))
    have hl'N : l' ∈ L ⊔ pCoreOf 2 (L ⊔ L') := by
      have e : l' = l⁻¹ * y := by rw [← hly]; group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (L.inv_mem hl)) h2
    exact hyQ (hly ▸ (pCoreOf 2 (L ⊔ L')).mul_mem (hT5 l hl hlN) (hT5' l' hl' hl'N))
  have hyN' : y ∈ L ⊔ pCoreOf 2 (L ⊔ L') → False := fun h2 => hyN ((hswapN y hyY hy3).2 h2)
  have hlN1 : l ∉ L' ⊔ pCoreOf 2 (L ⊔ L') := fun h => hyN (by
    rw [← hly]
    exact Subgroup.mul_mem _ h (Subgroup.mem_sup_left hl'))
  have hl'N2 : l' ∉ L ⊔ pCoreOf 2 (L ⊔ L') := fun h => hyN' (by
    rw [← hly]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hl) h)
  have hyL₀ : y ∈ L ⊔ L' := hYL₀ hyY
  have h3l : 3 ∣ orderOf l := by
    refine three_dvd_orderOf hN₁H hHN₁ (hLL₀ hl) hyL₀ ?_ hlN1 hy3'
    have e : y⁻¹ * l = l'⁻¹ := by rw [← hly]; group
    rw [e]
    exact Subgroup.mem_sup_left (L'.inv_mem hl')
  have h3l' : 3 ∣ orderOf l' := by
    refine three_dvd_orderOf hN₂H hHN₂ (hL'L₀ hl') hyL₀ ?_ hl'N2 hy3'
    have e : y⁻¹ * l' = l'⁻¹ * l⁻¹ * l'⁻¹⁻¹ := by rw [← hly]; group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hHN₂ (hL'L₀ (L'.inv_mem hl'))) (l⁻¹)).mp
      (Subgroup.mem_sup_left (L.inv_mem hl))
  have ha3 : orderOf (l ^ (orderOf l / 3)) = 3 := orderOf_pow_orderOf_div (orderOf_pos l).ne' h3l
  have haY : l ^ (orderOf l / 3) ∈ Yp := hgenY _ ((M ⊓ I).pow_mem hlM _) ha3
  have haL : l ^ (orderOf l / 3) ∈ L := L.pow_mem hl _
  have ha'3 : orderOf (l' ^ (orderOf l' / 3)) = 3 :=
    orderOf_pow_orderOf_div (orderOf_pos l').ne' h3l'
  have ha'Y : l' ^ (orderOf l' / 3) ∈ Yp := hgenY _ ((M ⊓ I).pow_mem hl'M _) ha'3
  have ha'3' : (l' ^ (orderOf l' / 3)) ^ 3 = 1 := by
    have := pow_orderOf_eq_one (l' ^ (orderOf l' / 3))
    rwa [ha'3] at this
  have ha'N2 : l' ^ (orderOf l' / 3) ∈ L ⊔ pCoreOf 2 (L ⊔ L') :=
    mem_of_order_three hcard3 hYL₀ hN₂H hHN₂ haY ha3 (Subgroup.mem_sup_left haL) ha'Y ha'3'
  exact not_mem_of_orderOf_three hQ2 ha'3 (hT5' _ (L'.pow_mem hl' _) ha'N2)

end Final

end SBc2

end CFSG.Quasithin
