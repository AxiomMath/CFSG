module

public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10.Co3K

open Subgroup

variable {G : Type*} [Group G]

theorem card_dvd_pred_mul_card_inf_centralizer [Finite G] {L H : Subgroup G}
    (hL : (Nat.card L).Prime) (hH : H ≤ normalizer (L : Set G)) :
    Nat.card H ∣ (Nat.card L - 1) * Nat.card ↥(H ⊓ centralizer (L : Set G)) := by
  have : Fact (Nat.card L).Prime := ⟨hL⟩
  have : IsCyclic L := isCyclic_of_prime_card rfl
  let φ : H →* MulAut L := L.normalizerMonoidHom.comp (inclusion hH)
  have hker : φ.ker = (centralizer (L : Set G)).subgroupOf H := by
    ext h
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, normalizerMonoidHom_ker,
      mem_subgroupOf, mem_subgroupOf]
    rfl
  have hcard : Nat.card φ.ker = Nat.card ↥(H ⊓ centralizer (L : Set G)) := by
    rw [hker, ← card_map_of_injective (K := (centralizer (L : Set G)).subgroupOf H)
      H.subtype_injective, subgroupOf_map_subtype, inf_comm]
  have hAut : Nat.card (MulAut L) = Nat.card L - 1 := by
    rw [IsCyclic.card_mulAut, Nat.totient_prime hL]
  have : Finite (MulAut L) := Nat.finite_of_card_ne_zero (by rw [hAut]; have := hL.two_le; omega)
  have hrange : Nat.card φ.range ∣ Nat.card L - 1 := hAut ▸ card_subgroup_dvd_card _
  rw [← card_ker_mul_card_range φ, hcard, mul_comm (Nat.card L - 1)]
  exact Nat.mul_dvd_mul_left _ hrange

theorem exists_normal_comm_ne_bot [Finite G] [Nontrivial G] (hs : Group.IsSolvable G) :
    ∃ V : Subgroup G, V.Normal ∧ V ≠ ⊥ ∧ ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := by
  classical
  have hex : ∃ n, derivedSeries G n = ⊥ := hs.solvable
  have h0 : derivedSeries G (Nat.find hex) = ⊥ := Nat.find_spec hex
  have hn0 : Nat.find hex ≠ 0 := by
    intro h
    rw [h, derivedSeries_zero] at h0
    exact top_ne_bot h0
  obtain ⟨m, hm⟩ : ∃ m, Nat.find hex = m + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hD : derivedSeries G m ≠ ⊥ := Nat.find_min hex (by omega)
  have hDcomm : ⁅derivedSeries G m, derivedSeries G m⁆ = ⊥ := by
    rw [← derivedSeries_succ, ← hm]
    exact h0
  refine ⟨derivedSeries G m, derivedSeries_normal G m, hD, fun x hx y hy => ?_⟩
  have := Subgroup.commutator_mem_commutator hx hy
  rwa [hDcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this

theorem exists_normal_comm_exponent_prime [Finite G] [Nontrivial G] (hs : Group.IsSolvable G) :
    ∃ p : ℕ, p.Prime ∧ ∃ A : Subgroup G, A.Normal ∧ A ≠ ⊥ ∧ (∀ x ∈ A, x ^ p = 1) ∧
      ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
  classical
  obtain ⟨V, hVn, hV1, hcomm⟩ := exists_normal_comm_ne_bot hs
  have hVcard : Nat.card V ≠ 1 := by rwa [Ne, Subgroup.card_eq_one]
  have hp : (Nat.card V).minFac.Prime := Nat.minFac_prime hVcard
  have : Fact (Nat.card V).minFac.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (Nat.card V).minFac (Nat.minFac_dvd _)
  set p := (Nat.card V).minFac with hpdef
  let A : Subgroup G :=
    { carrier := {y | y ∈ V ∧ y ^ p = 1}
      mul_mem' := fun {a b} ha hb =>
        ⟨V.mul_mem ha.1 hb.1, by
          rw [(show Commute a b from hcomm a ha.1 b hb.1).mul_pow, ha.2, hb.2, one_mul]⟩
      one_mem' := ⟨V.one_mem, one_pow _⟩
      inv_mem' := fun {a} ha => ⟨V.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  refine ⟨p, hp, A, ⟨fun y hy g => ⟨hVn.conj_mem y hy.1 g, ?_⟩⟩, ?_, fun y hy => hy.2,
    fun a ha b hb => hcomm a ha.1 b hb.1⟩
  · rw [conj_pow, hy.2]
    simp
  · intro hbot
    have hxA : (x : G) ∈ A := by
      refine ⟨x.2, ?_⟩
      have := pow_orderOf_eq_one x
      rw [hx] at this
      simpa using congrArg Subtype.val this
    rw [hbot, Subgroup.mem_bot] at hxA
    have hx1 : x = 1 := Subtype.ext hxA
    rw [hx1, orderOf_one] at hx
    exact hp.one_lt.ne hx

theorem normal_of_le_normalizer {V H K : Subgroup G} (hVH : V ⊔ H = ⊤)
    (hV : V ≤ normalizer (K : Set G)) (hH : H ≤ normalizer (K : Set G)) : K.Normal := by
  rw [← normalizer_eq_top_iff, eq_top_iff, ← hVH]
  exact sup_le hV hH

theorem card_dvd_pred_of_normalCore_eq_bot [Finite G] (hs : Group.IsSolvable G) {H : Subgroup G}
    {p : ℕ} (hp : p.Prime) (hH : H.index = p) (hcore : H.normalCore = ⊥) :
    Nat.card H ∣ p - 1 := by
  classical
  have hHtop : H ≠ ⊤ := by
    intro h
    rw [h, index_top] at hH
    exact hp.one_lt.ne hH
  have : Nontrivial G := by
    by_contra hG
    rw [not_nontrivial_iff_subsingleton] at hG
    exact hHtop (Subsingleton.elim _ _)
  obtain ⟨V, hVn, hV1, hcomm⟩ := exists_normal_comm_ne_bot hs
  have hVH : ¬ V ≤ H := fun h => hV1 (le_bot_iff.1 (hcore ▸ normal_le_normalCore.2 h))
  have hsup : V ⊔ H = ⊤ := by
    have h1 := relIndex_mul_index (le_sup_right : H ≤ V ⊔ H)
    rw [hH] at h1
    rcases (Nat.dvd_prime hp).1 (Dvd.intro_left _ h1) with h2 | h2
    · exact (index_eq_one).1 h2
    · rw [h2, Nat.mul_eq_right hp.ne_zero, relIndex_eq_one] at h1
      exact absurd (le_sup_left.trans h1) hVH
  have hVHbot : V ⊓ H = ⊥ := by
    have : (V ⊓ H).Normal := by
      refine normal_of_le_normalizer hsup (fun v hv => ?_) (fun h hh => ?_)
      · rw [mem_normalizer_iff]
        intro x
        constructor
        · intro hx
          rwa [hcomm v hv x hx.1, mul_inv_cancel_right]
        · intro hx
          have hx' : x ∈ V := by
            have := V.mul_mem (V.mul_mem (V.inv_mem hv) hx.1) hv
            simpa [mul_assoc] using this
          rwa [hcomm v hv x hx', mul_inv_cancel_right] at hx
      · rw [mem_normalizer_iff]
        intro x
        constructor
        · intro hx
          exact ⟨hVn.conj_mem x hx.1 h, H.mul_mem (H.mul_mem hh hx.2) (H.inv_mem hh)⟩
        · intro hx
          have e : x = h⁻¹ * (h * x * h⁻¹) * h := by group
          rw [e]
          refine ⟨?_, H.mul_mem (H.mul_mem (H.inv_mem hh) hx.2) hh⟩
          have := hVn.conj_mem _ hx.1 h⁻¹
          simpa using this
    exact le_bot_iff.1 (hcore ▸ normal_le_normalCore.2 inf_le_right)
  have hVcard : Nat.card V = p := by
    have h1 : V.index = Nat.card H := by
      rw [← relIndex_top_right, ← hsup, sup_comm, relIndex_sup_right, relIndex,
        (subgroupOf_eq_bot.2 ?_), index_bot]
      rw [disjoint_iff]
      exact hVHbot
    have h2 := V.card_mul_index
    have h3 := H.card_mul_index
    rw [h1] at h2
    rw [hH, ← h2] at h3
    have hpos : 0 < Nat.card H := Nat.card_pos
    exact (Nat.eq_of_mul_eq_mul_left hpos (h3.trans (mul_comm _ _))).symm
  have hHC : H ⊓ centralizer (V : Set G) = ⊥ := by
    have : (H ⊓ centralizer (V : Set G)).Normal := by
      refine normal_of_le_normalizer hsup (fun v hv => ?_) (fun h hh => ?_)
      · rw [mem_normalizer_iff]
        intro x
        have hvx : x ∈ centralizer (V : Set G) → v * x * v⁻¹ = x := fun hx => by
          rw [mem_centralizer_iff.1 hx v hv, mul_inv_cancel_right]
        constructor
        · intro hx
          rwa [hvx hx.2]
        · intro hx
          have hC : v * x * v⁻¹ ∈ centralizer (V : Set G) := hx.2
          have hx2 : x ∈ centralizer (V : Set G) := by
            have := (centralizer (V : Set G)).mul_mem
              ((centralizer (V : Set G)).mul_mem (show v⁻¹ ∈ centralizer (V : Set G) from
                mem_centralizer_iff.2 fun y hy => by
                  rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← hcomm v hv y hy, inv_mul_cancel_left])
                hC) (show v ∈ centralizer (V : Set G) from
                mem_centralizer_iff.2 fun y hy => (hcomm v hv y hy).symm)
            simpa [mul_assoc] using this
          rw [hvx hx2] at hx
          exact hx
      · rw [mem_normalizer_iff]
        intro x
        constructor
        · intro hx
          exact ⟨H.mul_mem (H.mul_mem hh hx.1) (H.inv_mem hh),
            (normal_centralizer (H := V)).conj_mem x hx.2 h⟩
        · intro hx
          have e : x = h⁻¹ * (h * x * h⁻¹) * h := by group
          rw [e]
          refine ⟨H.mul_mem (H.mul_mem (H.inv_mem hh) hx.1) hh, ?_⟩
          have := (normal_centralizer (H := V)).conj_mem _ hx.2 h⁻¹
          simpa using this
    exact le_bot_iff.1 (hcore ▸ normal_le_normalCore.2 inf_le_left)
  have key := card_dvd_pred_mul_card_inf_centralizer (L := V) (H := H) (hVcard ▸ hp)
    (by rw [normalizer_eq_top]; exact le_top)
  rwa [hHC, card_bot, mul_one, hVcard] at key

theorem card_dvd_pred_mul_card_normalCore [Finite G] (hs : Group.IsSolvable G) {H : Subgroup G}
    {p : ℕ} (hp : p.Prime) (hH : H.index = p) :
    Nat.card H ∣ (p - 1) * Nat.card H.normalCore := by
  classical
  set K := H.normalCore
  let π : G →* G ⧸ K := QuotientGroup.mk' K
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective K
  have hker : π.ker = K := QuotientGroup.ker_mk' K
  have hKH : K ≤ H := normalCore_le H
  have hsQ : Group.IsSolvable (G ⧸ K) := by
    have := hs
    infer_instance
  have hidx : (H.map π).index = p := by
    rw [index_map_eq _ hπ (by rw [hker]; exact hKH), hH]
  have hcore : (H.map π).normalCore = ⊥ := by
    have hle : ((H.map π).normalCore.comap π) ≤ K := by
      have : ((H.map π).normalCore.comap π).Normal := Normal.comap inferInstance π
      refine normal_le_normalCore.2 ?_
      calc ((H.map π).normalCore.comap π) ≤ (H.map π).comap π :=
            comap_mono (normalCore_le _)
        _ = H := by rw [comap_map_eq, hker, sup_eq_left.2 hKH]
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨g, rfl⟩ := hπ x
    have hg : g ∈ K := hle hx
    rw [mem_bot, ← MonoidHom.mem_ker, hker]
    exact hg
  have h1 := card_dvd_pred_of_normalCore_eq_bot hsQ hp hidx hcore
  have h2 : Nat.card H = Nat.card (H.map π) * Nat.card K := by
    have e1 := H.card_mul_index
    have e2 := (H.map π).card_mul_index
    have e3 := card_eq_card_quotient_mul_card_subgroup K
    rw [hH] at e1
    rw [hidx] at e2
    have hp0 : 0 < p := hp.pos
    have : Nat.card H * p = Nat.card (H.map π) * Nat.card K * p := by
      rw [e1, e3, ← e2]
      ring
    exact Nat.eq_of_mul_eq_mul_right hp0 this
  rw [h2]
  exact Nat.mul_dvd_mul_right h1 _

theorem quot_comm_of_index_dvd_four {H K : Subgroup G} (hidx : (K.subgroupOf H).index ∣ 4)
    [hn : (K.subgroupOf H).Normal] (a b : ↥H ⧸ K.subgroupOf H) : a * b = b * a := by
  have hfin : (K.subgroupOf H).FiniteIndex := ⟨fun h => by rw [h] at hidx; norm_num at hidx⟩
  have hcard : Nat.card (↥H ⧸ K.subgroupOf H) ∣ 2 ^ 2 := by
    rw [← index_eq_card]
    simpa using hidx
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hcard
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  interval_cases k
  · have : Subsingleton (↥H ⧸ K.subgroupOf H) := (Nat.card_eq_one_iff_unique.1 hk').1
    exact Subsingleton.elim _ _
  · have : IsCyclic (↥H ⧸ K.subgroupOf H) := isCyclic_of_prime_card (p := 2) (by simpa using hk')
    exact IsCyclic.commutative.is_comm.comm a b
  · exact IsPGroup.commutative_of_card_eq_prime_sq hk' a b

theorem commutator_mem_of_index_dvd_four {H K : Subgroup G} [K.Normal]
    (hidx : (K.subgroupOf H).index ∣ 4) {x y : G} (hx : x ∈ H) (hy : y ∈ H) :
    x * y * x⁻¹ * y⁻¹ ∈ K := by
  have hn : (K.subgroupOf H).Normal := normal_subgroupOf
  have hc := quot_comm_of_index_dvd_four hidx (QuotientGroup.mk (⟨x, hx⟩ : H))
    (QuotientGroup.mk (⟨y, hy⟩ : H))
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at hc
  have : (⟨x * y * x⁻¹ * y⁻¹, H.mul_mem (H.mul_mem (H.mul_mem hx hy) (H.inv_mem hx))
      (H.inv_mem hy)⟩ : H) ∈ K.subgroupOf H := by
    have h2 := (K.subgroupOf H).inv_mem hc
    have h3 := hn.conj_mem _ h2 ⟨y * x, H.mul_mem hy hx⟩
    convert h3 using 1
    ext
    simp [mul_assoc]
  exact this

theorem pow_four_mem_of_index_dvd_four {H K : Subgroup G} [K.Normal]
    (hidx : (K.subgroupOf H).index ∣ 4) {x : G} (hx : x ∈ H) : x ^ 4 ∈ K := by
  have hn : (K.subgroupOf H).Normal := normal_subgroupOf
  have hfin : (K.subgroupOf H).FiniteIndex := ⟨fun h => by rw [h] at hidx; norm_num at hidx⟩
  have hcard : Nat.card (↥H ⧸ K.subgroupOf H) ∣ 4 := by
    rwa [← index_eq_card]
  have hfinQ : Finite (↥H ⧸ K.subgroupOf H) := Nat.finite_of_card_ne_zero (by
    intro h; rw [h] at hcard; norm_num at hcard)
  have h1 : (QuotientGroup.mk (⟨x, hx⟩ : H) : ↥H ⧸ K.subgroupOf H) ^ 4 = 1 := by
    obtain ⟨c, hc⟩ := hcard
    rw [hc, pow_mul, pow_card_eq_one', one_pow]
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h1
  have : (⟨x, hx⟩ : H) ^ 4 ∈ K.subgroupOf H := h1
  rw [mem_subgroupOf] at this
  simpa using this

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10.Co3K
