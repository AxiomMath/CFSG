module

public import CFSG.RankThree.OddKernel.EvenMinimalCover
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup
public import CFSG.RankThree.PartTwo.Census.Criteria
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.RankThree.OddKernel

open Subgroup CFSG.SectionRank
open CFSG.Assembly.RankThreeEven (localRank)

universe u

section Reduction

variable {p : ℕ}

@[expose] noncomputable def sylowPrimeComplement {X : Type*} [Group X] (p : ℕ)
    (C : Subgroup X) : Subgroup X :=
  sSup {M | ∃ q : ℕ, q.Prime ∧ q ≠ p ∧ ∃ Q : Sylow q C, M = (Q : Subgroup C).map C.subtype}

theorem isPGroup_quotient_of_forall_sylow_le [Fact p.Prime] {C : Type*} [Group C] [Finite C]
    (K : Subgroup C) [K.Normal]
    (hK : ∀ q : ℕ, q.Prime → q ≠ p → ∃ Q : Sylow q C, (Q : Subgroup C) ≤ K) :
    IsPGroup p (C ⧸ K) := by
  have hpos : Nat.card (C ⧸ K) ≠ 0 := Nat.card_pos.ne'
  refine IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd hpos fun {q} hq hqdvd => ?_)
  by_contra hqp
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨T, hTle⟩ := hK q hq hqp
  have hT₀ : ((T.mapSurjective (QuotientGroup.mk'_surjective K) : Sylow q (C ⧸ K)) :
      Subgroup (C ⧸ K)) = ⊥ := by
    rw [Sylow.coe_mapSurjective, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hTle
  have hcard := Sylow.card_eq_multiplicity (T.mapSurjective (QuotientGroup.mk'_surjective K))
  rw [hT₀, card_bot] at hcard
  have hpos' := hq.factorization_pos_of_dvd hpos hqdvd
  exact (Nat.one_lt_pow hpos'.ne' hq.one_lt).ne' hcard.symm

theorem sylowPrimeComplement_spec [Fact p.Prime] {X : Type*} [Group X] [Finite X]
    (C : Subgroup X)
    (hsyl : ∀ (q : ℕ) [Fact q.Prime] (Q : Sylow q C), ((Q : Subgroup C).map C.subtype).Normal) :
    (sylowPrimeComplement p C).Normal ∧ sylowPrimeComplement p C ≤ C ∧
      ¬ p ∣ Nat.card (sylowPrimeComplement p C) ∧
      ∀ c ∈ C, ∃ n : ℕ, c ^ p ^ n ∈ sylowPrimeComplement p C := by
  have hle : sylowPrimeComplement p C ≤ C := sSup_le fun M ⟨q, _, _, Q, hM⟩ =>
    hM ▸ map_subtype_le _
  have hnormal : (sylowPrimeComplement p C).Normal := Subgroup.sSup_normal _
    fun M ⟨q, hq, _, Q, hM⟩ => by
      have : Fact q.Prime := ⟨hq⟩
      exact hM ▸ hsyl q Q
  have hcop : ¬ p ∣ Nat.card (sylowPrimeComplement p C) := by
    have hle' : sylowPrimeComplement p C ≤ CFSG.pPrimeCore p X :=
      sSup_le fun M ⟨q, hq, hqp, Q, hM⟩ => by
        have : Fact q.Prime := ⟨hq⟩
        refine le_sSup ⟨hM ▸ hsyl q Q, ?_⟩
        obtain ⟨k, hk⟩ := (Q.isPGroup'.map C.subtype).exists_card_eq
        rw [hM, hk]
        exact Nat.Coprime.pow_right k ((Nat.coprime_primes Fact.out hq).2 (Ne.symm hqp))
    intro h
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).1 CFSG.pPrimeCore_coprime_card
      (h.trans (card_dvd_of_le hle'))
  refine ⟨hnormal, hle, hcop, fun c hc => ?_⟩
  have hKp : IsPGroup p (C ⧸ (sylowPrimeComplement p C).subgroupOf C) := by
    refine isPGroup_quotient_of_forall_sylow_le _ fun q hq hqp => ?_
    obtain ⟨Q⟩ : Nonempty (Sylow q C) := inferInstance
    have hQD : (Q : Subgroup C).map C.subtype ≤ sylowPrimeComplement p C :=
      le_sSup ⟨q, hq, hqp, Q, rfl⟩
    exact ⟨Q, fun x hx => mem_subgroupOf.2 (hQD (mem_map_of_mem _ hx))⟩
  obtain ⟨n, hn⟩ := hKp (QuotientGroup.mk ⟨c, hc⟩)
  refine ⟨n, ?_⟩
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf] at hn
  exact hn

theorem mem_map_iff_of_reduction [Fact p.Prime] {X S : Type*} [Group X] [Group S] [Finite X]
    [Finite S] (π : X →* S) (hπ : Function.Surjective π) (D : Subgroup X)
    (hDC : D ≤ (center S).comap π) (hcop : ¬ p ∣ Nat.card D)
    (hCD : ∀ c ∈ (center S).comap π, ∃ n : ℕ, c ^ p ^ n ∈ D) (z : S) :
    z ∈ D.map π ↔ z ∈ center S ∧ Nat.Coprime (orderOf z) p := by
  constructor
  · rintro ⟨d, hd, rfl⟩
    refine ⟨hDC hd, ?_⟩
    have h1 : orderOf (π d) ∣ Nat.card D :=
      (orderOf_map_dvd π d).trans (Subgroup.orderOf_dvd_natCard D hd)
    exact Nat.Coprime.coprime_dvd_left h1
      ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hcop).symm
  · rintro ⟨hz, hcopz⟩
    obtain ⟨c, rfl⟩ := hπ z
    obtain ⟨n, hn⟩ := hCD c hz
    have hord : orderOf (π c ^ p ^ n) = orderOf (π c) :=
      (Nat.Coprime.pow_right n hcopz).orderOf_pow
    have hzp : zpowers (π c ^ p ^ n) = zpowers (π c) :=
      eq_of_le_of_card_ge (zpowers_le.2 (pow_mem (mem_zpowers _) _))
        (by rw [Nat.card_zpowers, Nat.card_zpowers, hord])
    have hle : zpowers (π c ^ p ^ n) ≤ D.map π :=
      zpowers_le.2 (by rw [← map_pow]; exact mem_map_of_mem π hn)
    exact hle (hzp ▸ mem_zpowers (π c))

theorem exists_reduction_map {X S : Type*} [Group X] [Group S] (π : X →* S)
    (hπ : Function.Surjective π) (D : Subgroup X) [D.Normal] [(D.map π).Normal] :
    ∃ f : X ⧸ D →* S ⧸ D.map π, (∀ x : X, f (QuotientGroup.mk x) = QuotientGroup.mk (π x)) ∧
      Function.Surjective f ∧ f.ker = (π.ker ⊔ D).map (QuotientGroup.mk' D) := by
  have hD : D ≤ ((QuotientGroup.mk' (D.map π)).comp π).ker := fun d hd => by
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact mem_map_of_mem π hd
  let f : X ⧸ D →* S ⧸ D.map π := QuotientGroup.lift D ((QuotientGroup.mk' (D.map π)).comp π) hD
  have hf : ∀ x : X, f (QuotientGroup.mk x) = QuotientGroup.mk (π x) := fun _ => rfl
  refine ⟨f, hf, fun q => ?_, ?_⟩
  · obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨x, rfl⟩ := hπ s
    exact ⟨_, hf x⟩
  · ext y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    rw [MonoidHom.mem_ker, hf, QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply,
      ← mem_comap (f := QuotientGroup.mk' D) (K := (π.ker ⊔ D).map (QuotientGroup.mk' D)),
      comap_map_eq, QuotientGroup.ker_mk', sup_assoc, sup_idem]
    constructor
    · rintro ⟨d, hd, hdx⟩
      have h1 : x * d⁻¹ ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hdx, mul_inv_cancel]
      have := mul_mem_sup h1 hd
      rwa [inv_mul_cancel_right] at this
    · intro hx
      have hn : π.ker.Normal := inferInstance
      rw [← SetLike.mem_coe, mul_normal (π.ker) D, Set.mem_mul] at hx
      obtain ⟨k, hk, d, hd, rfl⟩ := hx
      refine ⟨d, hd, ?_⟩
      rw [map_mul, MonoidHom.mem_ker.1 hk, one_mul]

theorem center_reduction_quotient [Fact p.Prime] {X S : Type*} [Group X] [Group S] [Finite X]
    [Group.IsPerfect S] (π : X →* S) (hπ : Function.Surjective π) (D : Subgroup X) [D.Normal]
    [(D.map π).Normal] (hDC : D ≤ (center S).comap π)
    (hCD : ∀ c ∈ (center S).comap π, ∃ n : ℕ, c ^ p ^ n ∈ D) (f : X ⧸ D →* S ⧸ D.map π)
    (hf : ∀ x : X, f (QuotientGroup.mk x) = QuotientGroup.mk (π x)) :
    (center (S ⧸ D.map π)).comap (QuotientGroup.mk' (D.map π)) = center S ∧
      center (S ⧸ D.map π) = (center S).map (QuotientGroup.mk' (D.map π)) ∧
      IsPGroup p (center (S ⧸ D.map π)) ∧
      (center (S ⧸ D.map π)).comap f = ((center S).comap π).map (QuotientGroup.mk' D) := by
  have hZ₀ : D.map π ≤ center S := map_le_iff_le_comap.2 hDC
  have hcomap := CFSG.LocalCores.comap_center_eq_of_perfect ‹_› (QuotientGroup.mk' (D.map π))
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']; exact hZ₀)
  have hmap : center (S ⧸ D.map π) = (center S).map (QuotientGroup.mk' (D.map π)) := by
    rw [← hcomap, map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
  refine ⟨hcomap, hmap, ?_, ?_⟩
  · rintro ⟨z, hz⟩
    rw [hmap] at hz
    obtain ⟨z, hzc, rfl⟩ := mem_map.1 hz
    obtain ⟨c, rfl⟩ := hπ z
    obtain ⟨n, hn⟩ := hCD c hzc
    refine ⟨n, Subtype.ext ?_⟩
    change (QuotientGroup.mk' (D.map π) (π c)) ^ p ^ n = 1
    rw [← map_pow, ← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact mem_map_of_mem π hn
  · ext y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    have h1 : (QuotientGroup.mk x : X ⧸ D) ∈ ((center S).comap π).map (QuotientGroup.mk' D) ↔
        x ∈ (center S).comap π := by
      rw [← QuotientGroup.mk'_apply, ← mem_comap, comap_map_eq, QuotientGroup.ker_mk',
        sup_eq_left.2 hDC]
    rw [h1, mem_comap, mem_comap, hf]
    change QuotientGroup.mk' (D.map π) (π x) ∈ center (S ⧸ D.map π) ↔ _
    rw [← mem_comap, hcomap]

theorem eq_top_of_map_reduction {X S : Type*} [Group X] [Group S] [Group.IsPerfect S]
    (π : X →* S) (hπ : Function.Surjective π) (hmin : ∀ V : Subgroup X, V.map π = ⊤ → V = ⊤)
    (D : Subgroup X) [D.Normal]
    [(D.map π).Normal] [(((center S).comap π).map (QuotientGroup.mk' D)).Normal]
    (hDC : D ≤ (center S).comap π) (f : X ⧸ D →* S ⧸ D.map π)
    (hf : ∀ x : X, f (QuotientGroup.mk x) = QuotientGroup.mk (π x)) :
    (∀ U : Subgroup (X ⧸ D), U.map f = ⊤ → U = ⊤) ∧
      ∀ U : Subgroup (X ⧸ D),
        U.map (QuotientGroup.mk' (((center S).comap π).map (QuotientGroup.mk' D))) = ⊤ →
        U = ⊤ := by
  have hZ₀ : D.map π ≤ center S := map_le_iff_le_comap.2 hDC
  have key : ∀ U : Subgroup (X ⧸ D),
      (U.comap (QuotientGroup.mk' D)).map π ⊔ center S = ⊤ → U = ⊤ := by
    intro U hU
    have hV := hmin _ ((perfect_central_supplement ‹_›).1 _ hU)
    refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    have hx : x ∈ U.comap (QuotientGroup.mk' D) := hV ▸ mem_top x
    exact hx
  refine ⟨fun U hU => key U (eq_top_iff.2 fun s _ => ?_), fun U hU => key U
    (eq_top_iff.2 fun s _ => ?_)⟩
  · obtain ⟨u, hu, hus⟩ := mem_map.1 (hU ▸ mem_top (QuotientGroup.mk s : S ⧸ D.map π))
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective u
    rw [hf, QuotientGroup.eq] at hus
    have h1 : π v ∈ (U.comap (QuotientGroup.mk' D)).map π := mem_map_of_mem π hu
    have := mul_mem_sup h1 (hZ₀ hus)
    rwa [mul_inv_cancel_left] at this
  · obtain ⟨x, rfl⟩ := hπ s
    obtain ⟨u, hu, hux⟩ := mem_map.1 (hU ▸ mem_top (QuotientGroup.mk' _
      (QuotientGroup.mk x : X ⧸ D)))
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective u
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hux
    have hvx : v⁻¹ * x ∈ (center S).comap π := by
      have h2 : (QuotientGroup.mk (v⁻¹ * x) : X ⧸ D) ∈
          ((center S).comap π).map (QuotientGroup.mk' D) := by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
        exact hux
      rw [← QuotientGroup.mk'_apply, ← mem_comap, comap_map_eq, QuotientGroup.ker_mk',
        sup_eq_left.2 hDC] at h2
      exact h2
    have h1 : π v ∈ (U.comap (QuotientGroup.mk' D)).map π := mem_map_of_mem π hu
    have := mul_mem_sup h1 (show π (v⁻¹ * x) ∈ center S from hvx)
    rwa [map_mul, map_inv, mul_inv_cancel_left] at this

theorem pRank_le_map_of_not_dvd {V W : Type*} [Group V] [Group W] [Finite V] [Finite W]
    (hp : p.Prime) (π : V →* W) (M : Subgroup V) (hK : ¬ p ∣ Nat.card π.ker) :
    CFSG.Open.pRank p M ≤ CFSG.Open.pRank p (M.map π) := by
  have hcard : Nat.card (π.ker.subgroupOf M) ∣ Nat.card π.ker := by
    have h1 : Nat.card (π.ker.subgroupOf M) = Nat.card (π.ker ⊓ M : Subgroup V) := by
      rw [← subgroupOf_map_subtype, card_map_of_injective M.subtype_injective]
    rw [h1]
    exact card_dvd_of_le inf_le_left
  have hker : ¬ p ∣ Nat.card (π.domRestrict M).ker := by
    rw [MonoidHom.ker_domRestrict]
    exact fun h => hK (h.trans hcard)
  have e := (QuotientGroup.quotientKerEquivRange (π.domRestrict M)).trans
    (MulEquiv.subgroupCongr (MonoidHom.domRestrict_range M π))
  rw [pRank_eq_pRank_top_subgroup, pRank_eq_pRank_top_subgroup (M.map π),
    ← pRank_eq_open_pRank_top, ← pRank_eq_open_pRank_top,
    ← CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd hp _ hker,
    pRank_eq_open_pRank_top, pRank_eq_open_pRank_top]
  exact (pRank_top_eq_of_mulEquiv hp.one_lt e).le

theorem localRank_le_quotient_of_odd {V : Type*} [Group V] [Finite V] (hp : p.Prime)
    (K : Subgroup V) [K.Normal] (hodd : Odd (Nat.card K)) (hcop : ¬ p ∣ Nat.card K) :
    localRank p V ≤ localRank p (V ⧸ K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine csSup_le' ?_
  rintro k ⟨M, ⟨T, hT0, hT2, rfl⟩, rfl⟩
  have hTK : T ⊓ K = ⊥ := by
    refine disjoint_iff.1 (Subgroup.disjoint_of_coprime_natCard ?_)
    obtain ⟨m, hm⟩ := hT2.exists_card_eq
    rw [hm]
    exact Nat.Coprime.pow_left m (Nat.coprime_two_left.2 hodd)
  have hT'0 : T.map (QuotientGroup.mk' K) ≠ ⊥ := by
    intro h
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    exact hT0 (by rw [← inf_eq_left.2 h, hTK])
  have hle := le_normalizer_map (H := T) (QuotientGroup.mk' K)
  have h1 := pRank_le_map_of_not_dvd hp (QuotientGroup.mk' K) (normalizer (T : Set V))
    (by rw [QuotientGroup.ker_mk']; exact hcop)
  exact h1.trans ((CFSG.SectionRank.pRank_mono hp.one_lt hle).trans
    (CFSG.RankThree.Classical.pRank_le_localRank hp.one_lt ⟨_, hT'0, hT2.map _, rfl⟩))

theorem twoLocalOddRank_subgroup_le {G : Type*} [Group G] [Finite G] (X : Subgroup G) :
    CFSG.twoLocalOddRank X ≤ CFSG.twoLocalOddRank G := by
  rw [← evenRank_eq_twoLocalOddRank, ← evenRank_eq_twoLocalOddRank]
  exact CFSG.RankThree.PartTwo.evenRank_subgroup_le X

theorem stationary_source_four_one_odd_prime_kernel_failure_reduction {G : Type} [Group G]
    [Finite G] (hK : IsKGroupCat G) (he : CFSG.twoLocalOddRank G ≤ 3)
    (hr : ∀ r : ℕ, r.Prime → 3 < r → localRank r G ≤ 2) (H : Subgroup G) (N : Subgroup H)
    [N.Normal] (hS : CFSG.layer (H ⧸ N) = ⊤) (hp : p.Prime) (hp3 : 3 < p)
    (hfail : 2 < localRank p (H ⧸ N) ∨ (pRank p G ≤ 3 ∧ pRank p G < pRank p (H ⧸ N)))
    (X : Subgroup H) (hXS : X.map (QuotientGroup.mk' N) = ⊤)
    (hXmin : ∀ U : Subgroup H, U.map (QuotientGroup.mk' N) = ⊤ → Nat.card X ≤ Nat.card U) :
    let ρX : X →* H ⧸ N := (QuotientGroup.mk' N).comp X.subtype
    let C : Subgroup X := (center (H ⧸ N)).comap ρX
    let D : Subgroup X := sylowPrimeComplement p C
    Group.IsPerfect X ∧ IsKGroupCat X ∧ CFSG.twoLocalOddRank X ≤ 3 ∧
      (∀ r : ℕ, r.Prime → 3 < r → localRank r X ≤ 2) ∧ Group.IsNilpotent C ∧
      Odd (Nat.card C) ∧
      (∀ (q : ℕ) [Fact q.Prime] (Q : Sylow q C), ((Q : Subgroup C).map C.subtype).Normal) ∧
      ∃ _ : D.Normal, ∃ _ : (D.map ρX).Normal,
        Odd (Nat.card D) ∧ ¬ p ∣ Nat.card D ∧
        (∀ z : H ⧸ N, z ∈ D.map ρX ↔ z ∈ center (H ⧸ N) ∧ Nat.Coprime (orderOf z) p) ∧
        ∃ _ : (C.map (QuotientGroup.mk' D)).Normal,
        ∃ f : X ⧸ D →* (H ⧸ N) ⧸ D.map ρX,
          (∀ x : X, f (QuotientGroup.mk x) = QuotientGroup.mk (ρX x)) ∧
          Function.Surjective f ∧ f.ker = (N.subgroupOf X ⊔ D).map (QuotientGroup.mk' D) ∧
          f.ker ≠ ⊥ ∧ f.ker ≤ C.map (QuotientGroup.mk' D) ∧
          Group.IsPerfect (X ⧸ D) ∧ IsKGroupCat (X ⧸ D) ∧
          C.map (QuotientGroup.mk' D) ≠ ⊥ ∧ IsPGroup p (C.map (QuotientGroup.mk' D)) ∧
          CFSG.layer ((H ⧸ N) ⧸ D.map ρX) = ⊤ ∧ IsPGroup p (center ((H ⧸ N) ⧸ D.map ρX)) ∧
          center ((H ⧸ N) ⧸ D.map ρX) =
            (center (H ⧸ N)).map (QuotientGroup.mk' (D.map ρX)) ∧
          (center ((H ⧸ N) ⧸ D.map ρX)).comap f = C.map (QuotientGroup.mk' D) ∧
          (∃ e : (X ⧸ D) ⧸ C.map (QuotientGroup.mk' D) ≃* (H ⧸ N) ⧸ center (H ⧸ N),
            ∀ x : X, e (QuotientGroup.mk (QuotientGroup.mk x)) = QuotientGroup.mk (ρX x)) ∧
          center ((H ⧸ N) ⧸ center (H ⧸ N)) = ⊥ ∧
          CFSG.layer ((H ⧸ N) ⧸ center (H ⧸ N)) = ⊤ ∧
          (∀ U : Subgroup (X ⧸ D), U.map f = ⊤ → U = ⊤) ∧
          (∀ U : Subgroup (X ⧸ D),
            U.map (QuotientGroup.mk' (C.map (QuotientGroup.mk' D))) = ⊤ → U = ⊤) ∧
          pRank p (X ⧸ D) = pRank p X ∧ pRank p X ≤ pRank p G ∧
          localRank p (X ⧸ D) = localRank p X ∧ localRank p X ≤ 2 ∧
          pRank p ((H ⧸ N) ⧸ D.map ρX) = pRank p (H ⧸ N) ∧
          localRank p ((H ⧸ N) ⧸ D.map ρX) = localRank p (H ⧸ N) ∧
          (2 < localRank p (H ⧸ N) →
            2 < localRank p ((H ⧸ N) ⧸ D.map ρX) ∧ 3 ≤ pRank p (X ⧸ D)) ∧
          (pRank p G ≤ 3 → pRank p G < pRank p (H ⧸ N) →
            pRank p G = 3 ∧ pRank p (X ⧸ D) = 3 ∧ 3 < pRank p ((H ⧸ N) ⧸ D.map ρX)) ∧
          (C.map (QuotientGroup.mk' D) ≤ center (X ⧸ D) →
            C.map (QuotientGroup.mk' D) = center (X ⧸ D) ∧ CFSG.layer (X ⧸ D) = ⊤ ∧
              f.ker ≤ center (X ⧸ D)) ∧
          (¬ C.map (QuotientGroup.mk' D) ≤ center (X ⧸ D) →
            (MulAut.conjNormal : X ⧸ D →* MulAut (C.map (QuotientGroup.mk' D))) ≠ 1) := by
  intro ρX C D
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hρX : Function.Surjective ρX := by
    rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, range_subtype, hXS]
  have hXmin' : ∀ U : Subgroup H, U < X → U.map (QuotientGroup.mk' N) ≠ ⊤ :=
    fun U hU hUS => absurd (hXmin U hUS) (not_le.2 (card_lt_of_lt hU))
  have hminX : ∀ V : Subgroup X, V.map ρX = ⊤ → V = ⊤ := by
    intro V hV
    have h1 := hXmin (V.map X.subtype) (by rw [map_map]; exact hV)
    rw [card_map_of_injective X.subtype_injective] at h1
    exact eq_top_of_card_eq V (le_antisymm (card_le_card_group V) h1)
  have hmin' : ∀ Y : Subgroup X, Y ≠ ⊤ → Y.map ρX ≠ ⊤ := fun Y hY hYS => hY (hminX Y hYS)
  obtain ⟨hXp, -, hCnil, hsyl, ⟨e, heq⟩, hZq, hLq, hZXC, hLXC⟩ :=
    CFSG.SectionRank.minimal_semisimple_cover hS ρX hρX hmin'
  have hSp : Group.IsPerfect (H ⧸ N) :=
    Group.IsPerfect.top_iff.mp (hS ▸ CFSG.LocalCores.layer_isPerfect)
  obtain ⟨hDn, hDC, hDcop, hCD⟩ := sylowPrimeComplement_spec (p := p) C hsyl
  have hZ₀ : D.map ρX ≤ center (H ⧸ N) := map_le_iff_le_comap.2 hDC
  have hZ₀n : (D.map ρX).Normal := normal_of_le_center hZ₀
  have hlocX : ∀ r : ℕ, r.Prime → localRank r X ≤ localRank r G := fun r hr' =>
    (CFSG.RankThree.PartTwo.localRank_subgroup_le hr' X).trans
      (CFSG.RankThree.PartTwo.localRank_subgroup_le hr' H)
  have hpX : pRank p X ≤ pRank p G := by
    rw [pRank_eq_open_pRank_top, pRank_eq_open_pRank_top]
    exact pRank_top_le_of_injective hp.one_lt (H.subtype.comp X.subtype)
      (H.subtype_injective.comp X.subtype_injective)
  have hpH : pRank p H ≤ pRank p G := by
    rw [pRank_eq_open_pRank_top, pRank_eq_open_pRank_top]
    exact pRank_top_le_of_injective hp.one_lt H.subtype H.subtype_injective
  have hCodd : Odd (Nat.card C) := by
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    obtain ⟨h1, h2⟩ := even_cover_rank_le hp hp3 H N hS X hXS hXmin' (hr p hp hp3) hev
    rcases hfail with hf1 | ⟨hf1, hf2⟩
    · have := hr p hp hp3
      omega
    · have h3 : pRank p H ≤ 2 := by have := hr p hp hp3; omega
      have h4 := pRank_le_of_surjective_semisimple hp hp3 hS (QuotientGroup.mk' N)
        (QuotientGroup.mk'_surjective N) h3
      omega
  have hDodd : Odd (Nat.card D) := Odd.of_dvd_nat hCodd (card_dvd_of_le hDC)
  have hZ₀cop : ¬ p ∣ Nat.card (D.map ρX) := fun h => hDcop (h.trans (card_map_dvd D ρX))
  have hZ₀odd : Odd (Nat.card (D.map ρX)) := Odd.of_dvd_nat hDodd (card_map_dvd D ρX)
  have hCn : C.Normal := inferInstance
  have hPn : (C.map (QuotientGroup.mk' D)).Normal := hCn.map _ (QuotientGroup.mk'_surjective D)
  obtain ⟨f, hf, hfs, hfker⟩ := exists_reduction_map ρX hρX D
  have hρker : ρX.ker = N.subgroupOf X := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    exact QuotientGroup.eq_one_iff _
  rw [hρker] at hfker
  obtain ⟨hcomapZ, hmapZ, hZp, hpre⟩ := center_reduction_quotient ρX hρX D hDC hCD f hf
  obtain ⟨hnoS, hnoP⟩ := eq_top_of_map_reduction ρX hρX hminX D hDC f hf
  have hYp : Group.IsPerfect (X ⧸ D) := inferInstance
  have hS₀ : CFSG.layer ((H ⧸ N) ⧸ D.map ρX) = ⊤ :=
    CFSG.LocalCores.layer_eq_top_of_surjective hS _ (QuotientGroup.mk'_surjective _)
  have hPp : IsPGroup p (C.map (QuotientGroup.mk' D)) := by
    rintro ⟨y, hy⟩
    obtain ⟨c, hc, rfl⟩ := mem_map.1 hy
    obtain ⟨n, hn⟩ := hCD c hc
    refine ⟨n, Subtype.ext ?_⟩
    change (QuotientGroup.mk' D c) ^ p ^ n = 1
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).2 hn
  have hrY : pRank p (X ⧸ D) = pRank p X :=
    CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd hp D hDcop
  have hlY : localRank p (X ⧸ D) = localRank p X :=
    le_antisymm (CFSG.RankThree.Classical2.localRank_quotient_le hp hp2 D hDcop)
      (localRank_le_quotient_of_odd hp D hDodd hDcop)
  have hrS₀ : pRank p ((H ⧸ N) ⧸ D.map ρX) = pRank p (H ⧸ N) :=
    CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd hp _ hZ₀cop
  have hlS₀ : localRank p ((H ⧸ N) ⧸ D.map ρX) = localRank p (H ⧸ N) :=
    le_antisymm (CFSG.RankThree.Classical2.localRank_quotient_le hp hp2 _ hZ₀cop)
      (localRank_le_quotient_of_odd hp _ hZ₀odd hZ₀cop)
  have hlX2 : localRank p X ≤ 2 := (hlocX p hp).trans (hr p hp hp3)
  have hS₀small : pRank p (X ⧸ D) ≤ 2 → pRank p ((H ⧸ N) ⧸ D.map ρX) ≤ 2 := fun h =>
    pRank_le_two_of_surjective_semisimple hp hp3 h hS₀ f hfs
  have hlocle : localRank p ((H ⧸ N) ⧸ D.map ρX) ≤ pRank p ((H ⧸ N) ⧸ D.map ρX) := by
    have h := CFSG.RankThreeEvenClassification.Helpers.twoLocalRank_le_pRank p hp
      ((H ⧸ N) ⧸ D.map ρX)
    refine h.trans ?_
    change CFSG.Open.pRank p (⊤ : Subgroup _) ≤ _
    rw [← pRank_eq_open_pRank_top]
  have hA : f.ker ≠ ⊥ := by
    intro hbot
    have hinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).1 hbot
    let eY : X ⧸ D ≃* (H ⧸ N) ⧸ D.map ρX := MulEquiv.ofBijective f ⟨hinj, hfs⟩
    have h1 : localRank p (X ⧸ D) = localRank p ((H ⧸ N) ⧸ D.map ρX) :=
      CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv eY hp
    have h2 : pRank p (X ⧸ D) = pRank p ((H ⧸ N) ⧸ D.map ρX) := by
      rw [pRank_eq_open_pRank_top, pRank_eq_open_pRank_top]
      exact pRank_top_eq_of_mulEquiv hp.one_lt eY
    rcases hfail with hf1 | ⟨hf1, hf2⟩
    · omega
    · omega
  have hAP : f.ker ≤ C.map (QuotientGroup.mk' D) := by
    rw [hfker]
    refine map_mono (sup_le (fun x hx => ?_) hDC)
    rw [mem_comap, MonoidHom.comp_apply, Subgroup.coe_subtype]
    have h1 : QuotientGroup.mk' N (x : H) = 1 :=
      (QuotientGroup.eq_one_iff _).2 (mem_subgroupOf.1 hx)
    rw [h1]
    exact one_mem _
  have hP1 : C.map (QuotientGroup.mk' D) ≠ ⊥ := fun h => hA (le_bot_iff.1 (h ▸ hAP))
  let e3 : (X ⧸ D) ⧸ C.map (QuotientGroup.mk' D) ≃* X ⧸ C :=
    QuotientGroup.quotientQuotientEquivQuotient D C hDC
  have hZYP : center ((X ⧸ D) ⧸ C.map (QuotientGroup.mk' D)) = ⊥ := by
    rw [← map_center_eq e3.symm, hZXC, Subgroup.map_bot]
  have hLYP : CFSG.layer ((X ⧸ D) ⧸ C.map (QuotientGroup.mk' D)) = ⊤ :=
    CFSG.LocalCores.layer_eq_top_of_surjective hLXC e3.symm.toMonoidHom e3.symm.surjective
  refine ⟨hXp, (hK.subgroup H).subgroup X, (twoLocalOddRank_subgroup_le X).trans
    ((twoLocalOddRank_subgroup_le H).trans he), fun r hr' hr3 => (hlocX r hr').trans
    (hr r hr' hr3), hCnil, hCodd, hsyl, hDn, hZ₀n, hDodd, hDcop,
    mem_map_iff_of_reduction ρX hρX D hDC hDcop hCD, hPn, f, hf, hfs, hfker, hA, hAP, hYp,
    ((hK.subgroup H).subgroup X).quotient D, hP1, hPp, hS₀, hZp, hmapZ, hpre,
    ⟨e3.trans e, fun x => heq x⟩, hZq, hLq, hnoS, hnoP, hrY, hpX, hlY, hlX2, hrS₀, hlS₀,
    fun hf1 => ⟨hlS₀ ▸ hf1, ?_⟩, fun hf1 hf2 => ?_, fun hPZ => ?_, fun hPZ hconj => ?_⟩
  · by_contra h3
    have := hS₀small (by omega)
    omega
  · have hG3 : pRank p G = 3 := by
      by_contra hne
      have h4 := pRank_le_of_surjective_semisimple hp hp3 hS (QuotientGroup.mk' N)
        (QuotientGroup.mk'_surjective N) (by omega)
      omega
    refine ⟨hG3, ?_, by omega⟩
    by_contra hne
    have := hS₀small (by omega)
    omega
  · refine ⟨le_antisymm hPZ fun z hz => ?_, ?_, hAP.trans hPZ⟩
    · have hz' : QuotientGroup.mk' (C.map (QuotientGroup.mk' D)) z ∈
          center ((X ⧸ D) ⧸ C.map (QuotientGroup.mk' D)) :=
        map_center_le_center (QuotientGroup.mk'_surjective _) (mem_map_of_mem _ hz)
      rw [hZYP, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hz'
      exact hz'
    · exact CFSG.SectionRank.perfect_central_semisimple_extension hYp _ hPZ hLYP
  · apply hPZ
    intro y hy
    rw [mem_center_iff]
    intro g
    have h1 : MulAut.conjNormal g (⟨y, hy⟩ : C.map (QuotientGroup.mk' D)) = ⟨y, hy⟩ := by
      rw [hconj]
      rfl
    have h2 := congrArg Subtype.val h1
    rw [MulAut.conjNormal_apply] at h2
    calc g * y = g * y * g⁻¹ * g := by group
      _ = y * g := by rw [h2]

end Reduction

end CFSG.RankThree.OddKernel
