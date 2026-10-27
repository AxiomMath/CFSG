module

public import CFSG.RankThree.PartTwo.Sec17.PropUStepFour
public import CFSG.RankThree.PartTwo.Sec17.PropUStepThree
public import CFSG.RankThree.PartTwo.Sec17.PropUGFree
public import CFSG.RankThree.PartTwo.Sec14.Item146General
public import CFSG.RankThree.PartTwo.Sec14.Item14Tools
public import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal

public section

namespace CFSG.RankThree.PartTwo.Sec17.PropU

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec17
  CFSG.GH74.GLS
open scoped commutatorElement

theorem exists_centralizer_lift {G : Type} [Group G] [Finite G] {C N₂ : Subgroup G} {c : G}
    (hc3 : c ^ 3 = 1) (hN₂ : IsPGroup 2 N₂) (hCN₂ : C ≤ Subgroup.normalizer (N₂ : Set G))
    (hcC : c ∈ Subgroup.normalizer (C : Set G)) (hcN₂ : c ∈ Subgroup.normalizer (N₂ : Set G))
    (htriv : ∀ x ∈ C, c * x * c⁻¹ * x⁻¹ ∈ N₂) {x₀ : G} (hx₀ : x₀ ∈ C) :
    ∃ x ∈ C ⊓ Subgroup.centralizer ({c} : Set G), x₀⁻¹ * x ∈ N₂ := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : ¬ 3 ∣ Nat.card ↥(C ⊓ N₂) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp hN₂
    intro h
    have h2 : 3 ∣ 2 ^ n := by
      rw [← hn]
      exact h.trans (Subgroup.card_dvd_of_le inf_le_right)
    have h3 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2
    omega
  have hTcard : ¬ 3 ∣ Nat.card {x : G // x ∈ C ∧ x₀⁻¹ * x ∈ N₂} := by
    have e : {x : G // x ∈ C ∧ x₀⁻¹ * x ∈ N₂} ≃ ↥(C ⊓ N₂) :=
      { toFun := fun t => ⟨x₀⁻¹ * t.1, Subgroup.mem_inf.mpr ⟨C.mul_mem (C.inv_mem hx₀) t.2.1, t.2.2⟩⟩
        invFun := fun y => ⟨x₀ * y.1, C.mul_mem hx₀ (Subgroup.mem_inf.mp y.2).1, by
          simpa using (Subgroup.mem_inf.mp y.2).2⟩
        left_inv := fun t => by ext; simp
        right_inv := fun y => by ext; simp }
    rw [Nat.card_congr e]
    exact hcard
  have hmaps : ∀ t : {x : G // x ∈ C ∧ x₀⁻¹ * x ∈ N₂},
      c * t.1 * c⁻¹ ∈ C ∧ x₀⁻¹ * (c * t.1 * c⁻¹) ∈ N₂ := by
    intro t
    obtain ⟨htC, htN⟩ := t.2
    refine ⟨(Subgroup.mem_set_normalizer_iff.mp hcC t.1).mp htC, ?_⟩
    have hn : c * t.1 * c⁻¹ * t.1⁻¹ ∈ N₂ := htriv t.1 htC
    have hconj : x₀⁻¹ * (c * t.1 * c⁻¹ * t.1⁻¹) * x₀ ∈ N₂ := by
      refine (Subgroup.mem_set_normalizer_iff.mp (hCN₂ hx₀)
        (x₀⁻¹ * (c * t.1 * c⁻¹ * t.1⁻¹) * x₀)).mpr ?_
      have e1 : x₀ * (x₀⁻¹ * (c * t.1 * c⁻¹ * t.1⁻¹) * x₀) * x₀⁻¹ = c * t.1 * c⁻¹ * t.1⁻¹ := by
        group
      rw [e1]
      exact hn
    have e2 : x₀⁻¹ * (c * t.1 * c⁻¹) = (x₀⁻¹ * (c * t.1 * c⁻¹ * t.1⁻¹) * x₀) * (x₀⁻¹ * t.1) := by
      group
    rw [e2]
    exact N₂.mul_mem hconj htN
  have hinj : Function.Injective
      (fun t : {x : G // x ∈ C ∧ x₀⁻¹ * x ∈ N₂} =>
        (⟨c * t.1 * c⁻¹, hmaps t⟩ : {x : G // x ∈ C ∧ x₀⁻¹ * x ∈ N₂})) := by
    intro s t hst
    have h1 : c * s.1 * c⁻¹ = c * t.1 * c⁻¹ := congrArg Subtype.val hst
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h1))
  obtain ⟨τ, hτ⟩ : ∃ τ : Equiv.Perm {x : G // x ∈ C ∧ x₀⁻¹ * x ∈ N₂},
      ∀ t : {x : G // x ∈ C ∧ x₀⁻¹ * x ∈ N₂}, (τ t).1 = c * t.1 * c⁻¹ :=
    ⟨Equiv.ofBijective (fun t : {x : G // x ∈ C ∧ x₀⁻¹ * x ∈ N₂} =>
        (⟨c * t.1 * c⁻¹, hmaps t⟩ : {x : G // x ∈ C ∧ x₀⁻¹ * x ∈ N₂}))
      (Finite.injective_iff_bijective.mp hinj), fun t => rfl⟩
  have hpow : ∀ (n : ℕ) (t : {x : G // x ∈ C ∧ x₀⁻¹ * x ∈ N₂}),
      ((τ ^ n) t).1 = c ^ n * t.1 * (c ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro t; simp
    | succ k ih =>
      intro t
      rw [pow_succ τ k, Equiv.Perm.mul_apply, ih, hτ, pow_succ c k, mul_inv_rev]
      group
  have hτ3 : τ ^ (3 ^ 1) = 1 := by
    refine Equiv.ext fun t => Subtype.ext ?_
    rw [hpow]
    norm_num [hc3]
  have hTcard' : ¬ 3 ∣ Fintype.card {x : G // x ∈ C ∧ x₀⁻¹ * x ∈ N₂} := by
    rwa [← Nat.card_eq_fintype_card]
  obtain ⟨a, ha⟩ := Equiv.Perm.exists_fixed_point_of_prime hTcard' hτ3
  have hfix : c * a.1 * c⁻¹ = a.1 := by
    rw [← hτ a, ha]
  refine ⟨a.1, Subgroup.mem_inf.mpr ⟨a.2.1, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩, a.2.2⟩
  exact (mul_inv_eq_iff_eq_mul.mp hfix).symm

theorem sup_eq_top_of_two_subgroups (hgen : J2GenByTwoSubgroups) {Y : Type} [Group Y] [Finite Y]
    {N : Subgroup Y} [N.Normal] (hYJ : Nonempty ((Y ⧸ N) ≃* J2))
    {B Δ : Subgroup Y} (hB3 : IsPGroup 3 B) (hB9 : Nat.card B = 9) (hN : IsPGroup 2 N)
    (hΔ : ∀ S : Subgroup (Y ⧸ N), IsPGroup 2 S →
      B.map (QuotientGroup.mk' N) ≤ Subgroup.normalizer (S : Set (Y ⧸ N)) →
      S ≤ Δ.map (QuotientGroup.mk' N)) :
    Δ ⊔ N = ⊤ := by
  have hker : IsPGroup 2 (QuotientGroup.mk' N : Y →* Y ⧸ N).ker := by
    rw [QuotientGroup.ker_mk']
    exact hN
  have hE9 : Nat.card (B.map (QuotientGroup.mk' N)) = 9 := by
    rw [CFSG.RankThree.PartTwo.Sec17.TailProof.card_map_of_isPGroup_three (QuotientGroup.mk' N)
      hker hB3, hB9]
  have hsup := hgen (Y ⧸ N) hYJ (B.map (QuotientGroup.mk' N)) hE9
  have hle : (⊤ : Subgroup (Y ⧸ N)) ≤ Δ.map (QuotientGroup.mk' N) := by
    rw [← hsup]
    apply sSup_le
    rintro S ⟨hS2, hSn⟩
    exact hΔ S hS2 hSn
  have htop : Δ.map (QuotientGroup.mk' N) = ⊤ := top_le_iff.mp hle
  rw [eq_top_iff]
  intro y _
  have hy : QuotientGroup.mk' N y ∈ Δ.map (QuotientGroup.mk' N) := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨d, hd, hdy⟩ := Subgroup.mem_map.mp hy
  have hdN : d⁻¹ * y ∈ N := QuotientGroup.eq.mp hdy
  have h2 : d * (d⁻¹ * y) ∈ Δ ⊔ N := Subgroup.mul_mem_sup hd hdN
  rwa [mul_inv_cancel_left] at h2

theorem mem_normalizer_map_comap_inf {G : Type} [Group G] {Y D : Subgroup G} {N : Subgroup ↥Y}
    [N.Normal] (S : Subgroup (↥Y ⧸ N)) {a : G} (haY : a ∈ Y)
    (haD : a ∈ Subgroup.normalizer (D : Set G))
    (haS : QuotientGroup.mk' N ⟨a, haY⟩ ∈ Subgroup.normalizer (S : Set (↥Y ⧸ N))) :
    a ∈ Subgroup.normalizer
      ((((S.comap (QuotientGroup.mk' N)) ⊓ D.subgroupOf Y).map Y.subtype : Subgroup G) : Set G) := by
  have key : ∀ b : ↥Y, (b : G) ∈ Subgroup.normalizer (D : Set G) →
      QuotientGroup.mk' N b ∈ Subgroup.normalizer (S : Set (↥Y ⧸ N)) →
      ∀ u ∈ ((S.comap (QuotientGroup.mk' N)) ⊓ D.subgroupOf Y).map Y.subtype,
        (b : G) * u * (b : G)⁻¹ ∈ ((S.comap (QuotientGroup.mk' N)) ⊓ D.subgroupOf Y).map Y.subtype := by
    intro b hbD hbS u hu
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hu
    obtain ⟨hyS, hyD⟩ := Subgroup.mem_inf.mp hy
    have hyS' : QuotientGroup.mk' N y ∈ S := Subgroup.mem_comap.mp hyS
    have hyD' : (y : G) ∈ D := Subgroup.mem_subgroupOf.mp hyD
    refine Subgroup.mem_map.mpr ⟨b * y * b⁻¹, Subgroup.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
    · apply Subgroup.mem_comap.mpr
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hbS _).mp hyS'
    · apply Subgroup.mem_subgroupOf.mpr
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      exact (Subgroup.mem_normalizer_iff.mp hbD _).mp hyD'
    · simp
  refine Subgroup.mem_normalizer_iff.mpr (fun u => ⟨fun hu => key ⟨a, haY⟩ haD haS u hu, fun hu => ?_⟩)
  have hinv := key (⟨a, haY⟩ : ↥Y)⁻¹ (inv_mem haD) (by rw [map_inv]; exact inv_mem haS)
    (a * u * a⁻¹) hu
  have e : (((⟨a, haY⟩ : ↥Y)⁻¹ : ↥Y) : G) * (a * u * a⁻¹) *
      (((⟨a, haY⟩ : ↥Y)⁻¹ : ↥Y) : G)⁻¹ = u := by
    simp only [Subgroup.coe_inv, inv_inv]
    group
  rw [e] at hinv
  exact hinv

theorem comm_mem_pCoreOf_of_covers {G : Type} [Group G] {L Y₀ : Subgroup G} {c : G}
    (hcL : L ≤ Subgroup.centralizer ({c} : Set G)) (hLY : L ≤ Y₀)
    (hcov : Y₀ = L ⊔ CFSG.Open.pCoreOf 2 Y₀)
    (hcN : c ∈ Subgroup.normalizer ((CFSG.Open.pCoreOf 2 Y₀ : Subgroup G) : Set G)) :
    ∀ x ∈ Y₀, c * x * c⁻¹ * x⁻¹ ∈ CFSG.Open.pCoreOf 2 Y₀ := by
  intro x hx
  obtain ⟨l, hl, v, hv, rfl⟩ := exists_mul_of_covers hLY hcov hx
  have hcl : c * l = l * c := Subgroup.mem_centralizer_iff.mp (hcL hl) c (Set.mem_singleton c)
  have hln : l ∈ Subgroup.normalizer ((CFSG.Open.pCoreOf 2 Y₀ : Subgroup G) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) Y₀ (hLY hl)
  have hcv : c * v * c⁻¹ * v⁻¹ ∈ CFSG.Open.pCoreOf 2 Y₀ :=
    Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp hcN v).mp hv) (inv_mem hv)
  have heq : c * (l * v) * c⁻¹ * (l * v)⁻¹ = l * (c * v * c⁻¹ * v⁻¹) * l⁻¹ := by
    calc c * (l * v) * c⁻¹ * (l * v)⁻¹ = (c * l) * (v * c⁻¹ * v⁻¹ * l⁻¹) := by group
      _ = (l * c) * (v * c⁻¹ * v⁻¹ * l⁻¹) := by rw [hcl]
      _ = l * (c * v * c⁻¹ * v⁻¹) * l⁻¹ := by group
  rw [heq]
  exact (Subgroup.mem_normalizer_iff.mp hln _).mp hcv

theorem pu_isQuasisimple_of_mulEquiv {Q J : Type} [Group Q] [Group J] [IsSimpleGroup J]
    [Group.IsPerfect J] (e : Q ≃* J) : CFSG.IsQuasisimple Q := by
  have hQs : IsSimpleGroup Q := e.isSimpleGroup
  have hQp : Group.IsPerfect Q :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hQn : Nontrivial Q := e.toEquiv.nontrivial
  have hcen : Subgroup.center Q = ⊥ := by
    rcases hQs.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h1 | h1
    · exact h1
    · exfalso
      haveI : IsMulCommutative Q := Subgroup.center_eq_top_iff.mp h1
      exact not_subsingleton Q inferInstance
  let φ : Q ⧸ Subgroup.center Q ≃* Q :=
    (QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot
  let ψ : Q ⧸ Subgroup.center Q ≃* J := φ.trans e
  have hnc : ∃ a b : Q ⧸ Subgroup.center Q, a * b ≠ b * a := by
    by_contra hcon
    simp only [not_exists, ne_eq, not_not] at hcon
    apply Group.IsPerfect.not_isMulCommutative J
    refine ⟨⟨fun a b => ?_⟩⟩
    have h1 := congrArg ψ (hcon (ψ.symm a) (ψ.symm b))
    simpa using h1
  unfold CFSG.IsQuasisimple
  exact ⟨hQp, φ.isSimpleGroup, hnc⟩

theorem isQuasisimple_of_equiv_J2 {Q : Type} [Group Q]
    (h : Nonempty (Q ≃* J2)) : CFSG.IsQuasisimple Q := by
  obtain ⟨e⟩ := h
  haveI : IsSimpleGroup J2 := Sporadic.J2.isSimpleGroup_J2
  haveI : Group.IsPerfect J2 := isPerfect_J2
  exact pu_isQuasisimple_of_mulEquiv e

theorem pu_oPrimeResidual_conj {H : Type} [Group H] (p : ℕ) (u : H) {r : H}
    (hr : r ∈ oPrimeResidual p H) : u * r * u⁻¹ ∈ oPrimeResidual p H := by
  have hle : oPrimeResidual p H ≤ (oPrimeResidual p H).comap (MulAut.conj u).toMonoidHom := by
    unfold oPrimeResidual
    rw [Subgroup.closure_le]
    intro s hs
    obtain ⟨k, hk⟩ := hs
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    apply Subgroup.subset_closure
    refine ⟨k, ?_⟩
    show (u * s * u⁻¹) ^ (p ^ k) = 1
    rw [conj_pow, hk, mul_one, mul_inv_cancel]
  exact hle hr

theorem pu_core {Y : Type} [Group Y] [Finite Y] (V : Subgroup Y) [V.Normal]
    [IsSimpleGroup (Y ⧸ V)] (h3 : 3 ∣ Nat.card (Y ⧸ V))
    (X' A : Subgroup Y) (hsurj : X' ⊔ V = ⊤)
    (hA3 : ∀ x ∈ X', ∀ a : ℕ, x ^ (3 ^ a) = 1 → x ∈ A)
    (hAnorm : ∀ x ∈ X', ∀ a ∈ A, x * a * x⁻¹ ∈ A) :
    A ⊔ V = ⊤ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hXsurj : ∀ q : Y ⧸ V, ∃ x ∈ X', (QuotientGroup.mk' V x : Y ⧸ V) = q := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective V q
    have hy : y ∈ X' ⊔ V := by
      rw [hsurj]
      exact Subgroup.mem_top y
    obtain ⟨x, hx, v, hv, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hy
    refine ⟨x, hx, ?_⟩
    have hv1 : (QuotientGroup.mk' V v : Y ⧸ V) = 1 := (QuotientGroup.eq_one_iff v).2 hv
    rw [map_mul, hv1, mul_one]
  haveI hN : (A.map (QuotientGroup.mk' V)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hn
    obtain ⟨x, hx, rfl⟩ := hXsurj g
    exact Subgroup.mem_map.2 ⟨x * a * x⁻¹, hAnorm x hx a ha, by simp [map_mul, map_inv]⟩
  have hnt : A.map (QuotientGroup.mk' V) ≠ ⊥ := by
    obtain ⟨q₀, hq₀⟩ := exists_prime_orderOf_dvd_card' (G := Y ⧸ V) 3 h3
    obtain ⟨x, hx, hxq⟩ := hXsurj q₀
    have hn0 : orderOf x ≠ 0 := (orderOf_pos x).ne'
    obtain ⟨e, m, hm3, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 3 (by norm_num)
    have hyA : x ^ m ∈ A := by
      apply hA3 (x ^ m) (pow_mem hx m) e
      rw [← pow_mul, mul_comm, ← hnm]
      exact pow_orderOf_eq_one x
    have hq_ne : q₀ ^ m ≠ 1 := by
      intro h1
      have hdvd := orderOf_dvd_of_pow_eq_one h1
      rw [hq₀] at hdvd
      exact hm3 hdvd
    intro hbot
    apply hq_ne
    have hmem : (QuotientGroup.mk' V (x ^ m) : Y ⧸ V) ∈ A.map (QuotientGroup.mk' V) :=
      Subgroup.mem_map_of_mem _ hyA
    rw [hbot, Subgroup.mem_bot] at hmem
    rw [← hxq, ← map_pow]
    exact hmem
  have htop : A.map (QuotientGroup.mk' V) = ⊤ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top (A.map (QuotientGroup.mk' V)) with h | h
    · exact absurd h hnt
    · exact h
  rw [eq_top_iff]
  intro y _
  have hy : (QuotientGroup.mk' V y : Y ⧸ V) ∈ A.map (QuotientGroup.mk' V) := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨a, ha, hay⟩ := Subgroup.mem_map.1 hy
  have hay' : (a : Y ⧸ V) = (y : Y ⧸ V) := hay
  have hav : a⁻¹ * y ∈ V := (QuotientGroup.eq (s := V)).1 hay'
  exact Subgroup.mem_sup_of_normal_right.2 ⟨a, ha, a⁻¹ * y, hav, mul_inv_cancel_left a y⟩

theorem oPrimeResidualOf_covers {G : Type} [Group G] [Finite G]
    {Y₀ X : Subgroup G} (hXY : X ≤ Y₀) (hcov : Y₀ = X ⊔ CFSG.Open.pCoreOf 2 Y₀)
    (hYJ : Nonempty (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀ ≃* J2)) :
    Y₀ = oPrimeResidualOf 3 X ⊔ CFSG.Open.pCoreOf 2 Y₀ := by
  obtain ⟨e⟩ := hYJ
  haveI : IsSimpleGroup J2 := CFSG.Sporadic.J2.isSimpleGroup_J2
  haveI : IsSimpleGroup (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀) := e.isSimpleGroup
  have hcard : Nat.card J2 = 604800 := CFSG.RankThree.PartTwo.KFacts.KS14.card_nativeJ2
  have h3 : 3 ∣ Nat.card (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀) := by
    rw [Nat.card_congr e.toEquiv, hcard]
    norm_num
  have hsurj : X.subgroupOf Y₀ ⊔ CFSG.pCore 2 ↥Y₀ = ⊤ := by
    refine Subgroup.map_injective Y₀.subtype_injective ?_
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hXY,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact hcov.symm
  have hA3 : ∀ x ∈ X.subgroupOf Y₀, ∀ a : ℕ, x ^ (3 ^ a) = 1 →
      x ∈ (oPrimeResidualOf 3 X).subgroupOf Y₀ := by
    intro x hx a hxa
    have hxX : (x : G) ∈ X := Subgroup.mem_subgroupOf.1 hx
    rw [Subgroup.mem_subgroupOf]
    unfold oPrimeResidualOf oPrimeResidual
    refine Subgroup.mem_map.2 ⟨⟨(x : G), hxX⟩, Subgroup.subset_closure ?_, rfl⟩
    refine ⟨a, ?_⟩
    apply Subtype.ext
    simpa using congrArg Subtype.val hxa
  have hAnorm : ∀ x ∈ X.subgroupOf Y₀, ∀ a ∈ (oPrimeResidualOf 3 X).subgroupOf Y₀,
      x * a * x⁻¹ ∈ (oPrimeResidualOf 3 X).subgroupOf Y₀ := by
    intro x hx a ha
    have hxX : (x : G) ∈ X := Subgroup.mem_subgroupOf.1 hx
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    unfold oPrimeResidualOf at ha ⊢
    obtain ⟨r, hr, hra⟩ := Subgroup.mem_map.1 ha
    have hra' : (r : G) = (a : G) := hra
    have key := pu_oPrimeResidual_conj 3 (⟨(x : G), hxX⟩ : ↥X) hr
    refine Subgroup.mem_map.2 ⟨_, key, ?_⟩
    simp [hra']
  have hAV := pu_core (CFSG.pCore 2 ↥Y₀) h3 (X.subgroupOf Y₀)
    ((oPrimeResidualOf 3 X).subgroupOf Y₀) hsurj hA3 hAnorm
  apply le_antisymm
  · intro g hg
    have hmem : (⟨g, hg⟩ : ↥Y₀) ∈ (⊤ : Subgroup ↥Y₀) := Subgroup.mem_top _
    rw [← hAV] at hmem
    obtain ⟨a, ha, v, hv, hav⟩ := Subgroup.mem_sup_of_normal_right.1 hmem
    have hg' : g = (a : G) * (v : G) := by
      rw [← Subgroup.coe_mul]
      exact (congrArg Subtype.val hav).symm
    have hvP : (v : G) ∈ CFSG.Open.pCoreOf 2 Y₀ := Subgroup.mem_map_of_mem Y₀.subtype hv
    rw [hg']
    exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.1 ha) hvP
  · exact sup_le ((Subgroup.map_subtype_le (oPrimeResidual 3 ↥X)).trans hXY)
      (Subgroup.map_subtype_le (CFSG.pCore 2 ↥Y₀))

theorem pu_pCoreOf_le (p : ℕ) {G : Type} [Group G] (H : Subgroup G) :
    CFSG.Open.pCoreOf p H ≤ H := by
  intro x hx
  rw [pu_pCoreOf_eq_map] at hx
  obtain ⟨y, _, rfl⟩ := Subgroup.mem_map.mp hx
  exact y.2

theorem pu_ker_comp_eq {G : Type} [Group G] [Finite G] {Y₀ X : Subgroup G} (hXY : X ≤ Y₀)
    (hcov : Y₀ = X ⊔ CFSG.Open.pCoreOf 2 Y₀) :
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀)).comp (Subgroup.inclusion hXY)).ker =
      CFSG.pCore 2 ↥X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ : ↥X →* ↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀ :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀)).comp (Subgroup.inclusion hXY) with hφ
  have hsurj : Function.Surjective φ := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨x, hx, v, hv, hxv⟩ := exists_mul_of_covers hXY hcov y.2
    have hvY : v ∈ Y₀ := pu_pCoreOf_le 2 Y₀ hv
    refine ⟨⟨x, hx⟩, ?_⟩
    rw [hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have e : (Subgroup.inclusion hXY ⟨x, hx⟩)⁻¹ * y = ⟨v, hvY⟩ := by
      apply Subtype.ext
      show x⁻¹ * (y : G) = v
      rw [hxv, inv_mul_cancel_left]
    rw [e]
    exact (pu_mem_pCoreOf_iff (p := 2) (⟨v, hvY⟩ : ↥Y₀)).mp hv
  refine le_antisymm ?_ ?_
  · have hk : φ.ker = (CFSG.pCore 2 ↥Y₀).comap (Subgroup.inclusion hXY) := by
      ext x
      simp [hφ, QuotientGroup.eq_one_iff]
    refine le_sSup ⟨φ.normal_ker, ?_⟩
    rw [hk]
    exact CFSG.pCore_isPGroup.comap_of_injective _ (Subgroup.inclusion_injective hXY)
  · intro x hx
    rw [MonoidHom.mem_ker]
    have hn : ((CFSG.pCore 2 ↥X).map φ).Normal := CFSG.pCore_normal.map φ hsurj
    have hp : IsPGroup 2 ((CFSG.pCore 2 ↥X).map φ) := CFSG.pCore_isPGroup.map φ
    have hle : (CFSG.pCore 2 ↥X).map φ ≤ CFSG.pCore 2 (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀) :=
      le_sSup ⟨hn, hp⟩
    rw [CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot] at hle
    exact (Subgroup.mem_bot).mp (hle ⟨x, hx, rfl⟩)

theorem pCore_two_of_covers {G : Type} [Group G] [Finite G]
    {Y₀ X : Subgroup G} (hXY : X ≤ Y₀) (hcov : Y₀ = X ⊔ CFSG.Open.pCoreOf 2 Y₀)
    (hYJ : Nonempty (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀ ≃* J2)) :
    CFSG.Open.pCoreOf 2 X = X ⊓ CFSG.Open.pCoreOf 2 Y₀ ∧
      Nonempty (↥X ⧸ CFSG.pCore 2 ↥X ≃* J2) := by
  obtain ⟨e⟩ := hYJ
  have hker := pu_ker_comp_eq hXY hcov
  have key : ∀ x : ↥X, x ∈ CFSG.pCore 2 ↥X ↔ (x : G) ∈ CFSG.Open.pCoreOf 2 Y₀ := by
    intro x
    rw [← hker, MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact (pu_mem_pCoreOf_iff (p := 2) (Subgroup.inclusion hXY x)).symm
  refine ⟨?_, ?_⟩
  · ext x
    rw [Subgroup.mem_inf]
    constructor
    · intro hx
      have hxX : x ∈ X := pu_pCoreOf_le 2 X hx
      exact ⟨hxX, (key ⟨x, hxX⟩).mp ((pu_mem_pCoreOf_iff (p := 2) (⟨x, hxX⟩ : ↥X)).mp hx)⟩
    · rintro ⟨hxX, hxP⟩
      exact (pu_mem_pCoreOf_iff (p := 2) (⟨x, hxX⟩ : ↥X)).mpr ((key ⟨x, hxX⟩).mpr hxP)
  · obtain ⟨f⟩ := CFSG.RankThree.PartTwo.Sec17.Proof17Res3.nonempty_quotient_pCore_two_equiv hXY hcov
    exact ⟨f.symm.trans e⟩

theorem mem_scriptQ_of_concl142 {G : Type} [Group G] [Finite G] {A : Subgroup G}
    {LB : Subgroup G → Subgroup G} (h142 : Concl142 A LB) {c : G}
    (hcΩ : Subgroup.zpowers c ∈ omegaA A) {V : Subgroup G}
    (hV : V ∈ invariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
      (piCompl 3)) : V ∈ scriptQ A LB := by
  obtain ⟨Qs, hQs, hVQs⟩ := exists_le_mem_maxInvariantPiSubgroups hV
  exact mem_scriptQ_of_le (h142 c hcΩ Qs hQs).1 hVQs hV.2.2

theorem covers_of_sup_eq_top {G : Type} [Group G] {Y₀ X : Subgroup G} (hXY : X ≤ Y₀)
    (h : X.subgroupOf Y₀ ⊔ CFSG.pCore 2 ↥Y₀ = ⊤) : Y₀ = X ⊔ CFSG.Open.pCoreOf 2 Y₀ := by
  have h1 := congrArg (Subgroup.map Y₀.subtype) h
  rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hXY, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at h1
  exact h1.symm

theorem mem_normalizer_centralizer_singleton {G : Type} [Group G] {a c : G} (h : a * c = c * a) :
    a ∈ Subgroup.normalizer ((Subgroup.centralizer ({c} : Set G) : Subgroup G) : Set G) := by
  have key : ∀ a : G, Commute a c → ∀ g ∈ Subgroup.centralizer ({c} : Set G),
      a * g * a⁻¹ ∈ Subgroup.centralizer ({c} : Set G) := by
    intro a ha g hg
    rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
    have hg' : Commute g c := hg
    exact (ha.mul_left hg').mul_left ha.inv_left
  have ha : Commute a c := h
  refine Subgroup.mem_normalizer_iff.mpr fun g => ⟨key a ha g, fun hg => ?_⟩
  have := key a⁻¹ ha.inv_left _ hg
  simpa [mul_assoc] using this

theorem delta_covers
    (hgen : J2GenByTwoSubgroups) {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G}
    {L Y₀ : Subgroup G} (hs : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* J2))
    (hLcov : Y₀ = L ⊔ CFSG.Open.pCoreOf 2 Y₀) (h142 : Concl142 A (lB A))
    {C : Subgroup G} (hCY : C ≤ Y₀) (hAC : A ≤ Subgroup.normalizer (C : Set G))
    (hcov : Y₀ = C ⊔ CFSG.Open.pCoreOf 2 Y₀) :
    Y₀ = delta A (lB A) C ⊔ CFSG.Open.pCoreOf 2 Y₀ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hJ2L, h9, hAc, -, -, -⟩ := hs.j2_local hJ
  have hcA : c ∈ A := hs.c_mem
  have hΩ : Subgroup.zpowers c ∈ omegaA A := hs.zpowers_mem_omegaA
  have hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hs.isE27.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hc3 : c ^ 3 = 1 := by
    have h3 : Nat.card (Subgroup.zpowers c) = 3 := (zpowers_mem_omegaA_iff.mp hΩ).2.1
    rw [Nat.card_zpowers] at h3
    rw [← h3]
    exact pow_orderOf_eq_one c
  have hYJ : Nonempty (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀ ≃* J2) := by
    obtain ⟨e⟩ := Proof17Res3.nonempty_quotient_pCore_two_equiv hs.le_y0 hLcov
    obtain ⟨f⟩ := hJ2L
    exact ⟨e.trans f⟩
  set N₂ : Subgroup G := CFSG.Open.pCoreOf 2 Y₀ with hN₂
  have hN₂p : IsPGroup 2 N₂ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y₀
  have hY₀N : Y₀ ≤ Subgroup.normalizer (N₂ : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) Y₀
  have hAN₂ : A ≤ Subgroup.normalizer (N₂ : Set G) :=
    hs.le_normalizer_y0.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := 2) Y₀)
  have hCN₂ : C ≤ Subgroup.normalizer (N₂ : Set G) := hCY.trans hY₀N
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) := hs.toSec13Data.le_centralizer
  have htriv : ∀ x ∈ C, c * x * c⁻¹ * x⁻¹ ∈ N₂ := fun x hx =>
    comm_mem_pCoreOf_of_covers hLc hs.le_y0 hLcov (hAN₂ hcA) x (hCY hx)
  have hcC : c ∈ Subgroup.normalizer (C : Set G) := hAC hcA
  set N : Subgroup ↥Y₀ := CFSG.pCore 2 ↥Y₀ with hN
  have hNp : IsPGroup 2 N := CFSG.pCore_isPGroup
  set π := QuotientGroup.mk' N with hπ
  have hker : IsPGroup 2 π.ker := by
    rw [hπ, QuotientGroup.ker_mk']
    exact hNp
  set B : Subgroup ↥Y₀ := (A ⊓ L).subgroupOf Y₀ with hB
  have hALY : A ⊓ L ≤ Y₀ := inf_le_right.trans hs.le_y0
  have hB3 : IsPGroup 3 B := (hs.isE27.isPGroup.to_le inf_le_left).comap_subtype
  have hB9 : Nat.card B = 9 := by
    rw [← h9]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hALY).toEquiv
  set D : Subgroup G := C ⊓ Subgroup.centralizer ({c} : Set G) with hD
  have hlift : ∀ y : ↥Y₀, ∃ d : ↥Y₀, (d : G) ∈ D ∧ π d = π y := by
    intro y
    obtain ⟨x₀, hx₀, v, hv, hxv⟩ := exists_mul_of_covers hCY hcov y.2
    obtain ⟨x, hxD, hx⟩ := exists_centralizer_lift hc3 hN₂p hCN₂ hcC (hAN₂ hcA) htriv hx₀
    refine ⟨⟨x, hCY (Subgroup.mem_inf.mp hxD).1⟩, hxD, ?_⟩
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    rw [← pu_mem_pCoreOf_iff]
    have e1 : (((⟨x, hCY (Subgroup.mem_inf.mp hxD).1⟩ : ↥Y₀)⁻¹ * y : ↥Y₀) : G) =
        (x₀⁻¹ * x)⁻¹ * v := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hxv]
      group
    rw [e1]
    exact N₂.mul_mem (N₂.inv_mem hx) hv
  set Δ' : Subgroup ↥Y₀ := (delta A (lB A) C).subgroupOf Y₀ with hΔ'
  have key : Δ' ⊔ N = ⊤ := by
    refine sup_eq_top_of_two_subgroups hgen hYJ hB3 hB9 hNp ?_
    intro S hS hBS q hq
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N q
    obtain ⟨d, hdD, hdπ⟩ := hlift y
    have hdS : d ∈ S.comap π := by
      rw [Subgroup.mem_comap, hdπ]
      exact hq
    set U : Subgroup G := ((S.comap π) ⊓ D.subgroupOf Y₀).map Y₀.subtype with hU
    have hdU : (d : G) ∈ U := ⟨d, ⟨hdS, hdD⟩, rfl⟩
    have hU2 : IsPGroup 2 U := by
      have h1 : IsPGroup 2 (S.comap π) := hS.comap_of_ker_isPGroup π hker
      exact (h1.to_le inf_le_left).map Y₀.subtype
    have hUD : ∀ u ∈ U, u ∈ D := by
      rintro _ ⟨u, hu, rfl⟩
      exact (Subgroup.mem_inf.mp hu).2
    have hUC : U ≤ C := fun u hu => (Subgroup.mem_inf.mp (hUD u hu)).1
    have hUc : U ≤ Subgroup.centralizer ({c} : Set G) := fun u hu =>
      (Subgroup.mem_inf.mp (hUD u hu)).2
    have hcU : c ∈ Subgroup.normalizer (U : Set G) := by
      have hfix : ∀ w ∈ U, c * w * c⁻¹ = w := fun w hw => by
        have := Subgroup.mem_centralizer_singleton_iff.mp (hUc hw)
        rw [← this]; group
      refine Subgroup.mem_normalizer_iff.mpr fun u => ⟨fun hu => ?_, fun hu => ?_⟩
      · rw [hfix u hu]; exact hu
      · have h2 := hfix _ hu
        have h3 : c * u * c⁻¹ = u := by
          calc c * u * c⁻¹ = c⁻¹ * (c * (c * u * c⁻¹) * c⁻¹) * c := by group
            _ = c⁻¹ * (c * u * c⁻¹) * c := by rw [h2]
            _ = u := by group
        rw [h3] at hu
        exact hu
    have hAU : A ≤ Subgroup.normalizer (U : Set G) := by
      refine hAc.le.trans (sup_le (Subgroup.zpowers_le.mpr hcU) ?_)
      intro a ha
      have haY : a ∈ Y₀ := hALY ha
      have haD : a ∈ Subgroup.normalizer (D : Set G) :=
        pu_le_normalizer_inf hAC
          (fun a' ha' => mem_normalizer_centralizer_singleton (hAab a' ha' c hcA)) ha.1
      have haS : π ⟨a, haY⟩ ∈ Subgroup.normalizer (S : Set (↥Y₀ ⧸ N)) :=
        hBS ⟨⟨a, haY⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
      exact mem_normalizer_map_comap_inf S haY haD haS
    have hUQ : U ∈ scriptQ A (lB A) := by
      refine mem_scriptQ_of_concl142 h142 hΩ ⟨hUc.trans
        (centralizer_singleton_le_normalizer_zpowers c), ?_, hAU⟩
      rw [isPiSubgroup_piCompl_iff Nat.prime_three]
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hU2
      rw [hn]
      intro h3
      have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
      omega
    have hUδ : U ≤ delta A (lB A) C := le_delta hUQ hUC
    exact ⟨d, hUδ hdU, hdπ⟩
  exact covers_of_sup_eq_top ((delta_le C).trans hCY) key

theorem nonempty_quotient_J2
    {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}
    (hs : Sec17Std G A c L Y₀) (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* J2))
    (hLcov : Y₀ = L ⊔ CFSG.Open.pCoreOf 2 Y₀) :
    Nonempty (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀ ≃* J2) := by
  obtain ⟨hJ2L, -⟩ := hs.j2_local hJ
  obtain ⟨e⟩ := Proof17Res3.nonempty_quotient_pCore_two_equiv hs.le_y0 hLcov
  obtain ⟨f⟩ := hJ2L
  exact ⟨e.trans f⟩

theorem exists_covering_Y4
    (hgen : J2GenByTwoSubgroups) {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G}
    {L Y₀ : Subgroup G} (hs : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* J2))
    (hLcov : Y₀ = L ⊔ CFSG.Open.pCoreOf 2 Y₀) (h142 : Concl142 A (lB A))
    {C : Subgroup G} (hCY : C ≤ Y₀) (hAC : A ≤ Subgroup.normalizer (C : Set G))
    (hcov : Y₀ = C ⊔ CFSG.Open.pCoreOf 2 Y₀) :
    ∃ X : Subgroup G, X ≤ C ∧ A ≤ Subgroup.normalizer (X : Set G) ∧
      Y₀ = X ⊔ CFSG.Open.pCoreOf 2 Y₀ ∧ X ∈ scriptY4 A (lB A) ∧
      CFSG.Open.pCoreOf 2 X = X ⊓ CFSG.Open.pCoreOf 2 Y₀ ∧
      Nonempty (↥X ⧸ CFSG.pCore 2 ↥X ≃* J2) := by
  classical
  have hYJ : Nonempty (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀ ≃* J2) := nonempty_quotient_J2 hs hJ hLcov
  obtain ⟨X, hXC, hXmin⟩ := exists_minimal_le_of_wellFoundedLT
    (fun X : Subgroup G => A ≤ Subgroup.normalizer (X : Set G) ∧
      Y₀ = X ⊔ CFSG.Open.pCoreOf 2 Y₀) C ⟨hAC, hcov⟩
  obtain ⟨⟨hAX, hXcov⟩, hmin⟩ := hXmin
  have hXY : X ≤ Y₀ := hXC.trans hCY
  have hΔ : delta A (lB A) X = X := by
    have hP : A ≤ Subgroup.normalizer ((delta A (lB A) X : Subgroup G) : Set G) ∧
        Y₀ = delta A (lB A) X ⊔ CFSG.Open.pCoreOf 2 Y₀ :=
      ⟨le_normalizer_delta X, delta_covers hgen hs hJ hLcov h142 hXY hAX hXcov⟩
    exact le_antisymm (delta_le X) (hmin hP (delta_le X))
  have hO : oPrimeResidualOf 3 X = X := by
    have hP : A ≤ Subgroup.normalizer ((oPrimeResidualOf 3 X : Subgroup G) : Set G) ∧
        Y₀ = oPrimeResidualOf 3 X ⊔ CFSG.Open.pCoreOf 2 Y₀ :=
      ⟨le_normalizer_oPrimeResidualOf hAX, oPrimeResidualOf_covers hXY hXcov hYJ⟩
    exact le_antisymm (oPrimeResidualOf_le_self 3 X) (hmin hP (oPrimeResidualOf_le_self 3 X))
  obtain ⟨hpc, hXJ⟩ := pCore_two_of_covers hXY hXcov hYJ
  have hY₀top : Y₀ ≠ ⊤ := (scriptY0Star_subset A (lB A) hs.mem_y0Star).1.1.1
  have hXtop : X ≠ ⊤ := fun htop => hY₀top (top_le_iff.mp (htop ▸ hXY))
  exact ⟨X, hXC, hAX, hXcov, ⟨⟨hXtop, hAX⟩, hO.symm, hΔ.symm,
    isQuasisimple_of_equiv_J2 hXJ⟩, hpc, hXJ⟩

end CFSG.RankThree.PartTwo.Sec17.PropU
