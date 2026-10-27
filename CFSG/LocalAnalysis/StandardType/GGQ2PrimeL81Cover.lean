module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.CoverAction

public section

namespace CFSG.GGQ2Prime

open Subgroup CFSG.LieType.Multipliers CFSG.LieType.Multipliers.U62 CFSG.Fischer
  CFSG.EvenSmallLie.UnitarySix
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence)
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom onCenterQuotient
  onCenterQuotient_apply_mk)

theorem cover_hom_mkC {L : Type*} [Group L] (h : Cover →* L) (v : List (Fin 5 × Bool)) :
    h (mkC v) = FreeGroup.lift (fun i => h (PresentedGroup.of i)) (FreeGroup.mk v) := by
  rw [mkC, ← MonoidHom.comp_apply]
  exact DFunLike.congr_fun (FreeGroup.ext_hom _ _ fun i => by
    rw [MonoidHom.comp_apply, FreeGroup.lift_apply_of]
    rfl) _

theorem center_eq_cover_word
    {L : Type*} [Group L] (q : L →* T46) (hker : q.ker = center L) (h : Cover →* L)
    (hhs : Function.Surjective h) (hhq : ∀ x, q (h x) = coverπ x) {z : L} (hz : z ∈ center L) :
    ∃ a < 3, ∃ b < 2, ∃ c < 2,
      z = h (mkC kerThree) ^ a * (h (mkC kerTwo) ^ b * h (mkC kerTwo') ^ c) := by
  obtain ⟨p, rfl⟩ := hhs z
  have hp : p ∈ coverπ.ker := by
    rw [MonoidHom.mem_ker, ← hhq, ← MonoidHom.mem_ker, hker]
    exact hz
  obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := exists_eq_zWord_of_mem_ker hp
  exact ⟨a, ha, b, hb, c, hc, by rw [mkC_zWord, map_mul, map_mul, map_pow, map_pow, map_pow]⟩

theorem cover_word_facts
    {L : Type*} [Group L] (q : L →* T46) (hker : q.ker = center L) (h : Cover →* L)
    (hhq : ∀ x, q (h x) = coverπ x) :
    h (mkC kerThree) ∈ center L ∧ h (mkC kerTwo) ∈ center L ∧ h (mkC kerTwo') ∈ center L ∧
      h (mkC kerThree) ^ 3 = 1 ∧ h (mkC kerTwo) ^ 2 = 1 ∧ h (mkC kerTwo') ^ 2 = 1 := by
  obtain ⟨-, hz₂, hz₂', hz₃, h3, h2, h2', -, -⟩ := cover_kernel_facts
  have hc : ∀ p ∈ coverπ.ker, h p ∈ center L := fun p hp => by
    rw [← hker, MonoidHom.mem_ker, hhq]
    exact hp
  exact ⟨hc _ hz₃, hc _ hz₂, hc _ hz₂', by rw [← map_pow, h3, map_one],
    by rw [← map_pow, h2, map_one], by rw [← map_pow, h2', map_one]⟩

theorem fix_of_pow_three {L : Type*} [Group L] (α : MulAut L) (hα3 : α ^ 3 = 1) {c : L}
    (hc3 : c ^ 3 = 1) {a : ℕ} (hαc : α c = c ^ a) : α c = c := by
  have hmod : c ^ a = c ^ (a % 3) := by
    conv_lhs => rw [← Nat.div_add_mod a 3, pow_add, pow_mul, hc3, one_pow, one_mul]
  have h3c : (α ^ 3) c = c := by rw [hα3]; rfl
  rw [hmod] at hαc
  have hlt : a % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases h : a % 3
  · rw [pow_zero] at hαc
    have : c = 1 := α.injective (by rw [hαc, map_one])
    rw [hαc, this]
  · rw [pow_one] at hαc
    exact hαc
  · have e1 : α (α c) = c := by
      rw [hαc, map_pow, hαc, ← pow_mul]
      calc c ^ (2 * 2) = c ^ 3 * c := by group
        _ = c := by rw [hc3, one_mul]
    have e2 : (α ^ 3) c = c ^ 2 := by
      rw [pow_succ, MulAut.mul_apply, sq, MulAut.mul_apply, e1, hαc]
    rw [h3c, sq] at e2
    have hc1 : c = 1 := mul_eq_left.mp e2.symm
    rw [hc1, map_one]

theorem not_lift_diagonal_of_fix
    {L : Type*} [Group L] [Group.IsPerfect L] (q : L →* T46)
    (hq : Function.Surjective q) (hker : q.ker = center L) (hev : ¬ Odd (Nat.card (center L)))
    (α : MulAut L) (hfix : ∀ z ∈ center L, α z = z) (t : T46)
    (hα : ∀ x, q (α x) = diagonalAut (t * q x * t⁻¹)) : False := by
  obtain ⟨h, hhs, hhq⟩ := exists_cover_hom q hq hker.le
  obtain ⟨-, hz₂, -, hz₃, -, -, -, -, -⟩ := cover_kernel_facts
  obtain ⟨hc₃, hc₂, hc₂', h3, h2, h2'⟩ := cover_word_facts q hker h hhq
  set ℓ : Fin 5 → L := fun i => h (PresentedGroup.of i)
  have hℓ : ∀ i, q (ℓ i) = genE i := fun i => by
    change q (h (PresentedGroup.of i)) = _
    rw [hhq]
    exact coverπ_mk (FreeGroup.of i) |>.trans (FreeGroup.lift_apply_of)
  have hfix' : ∀ z ∈ q.ker, α z = z := fun z hz => hfix z (hker ▸ hz)
  have hδ : ∀ i, diagonalAut.toMonoidHom (genE i) =
      FreeGroup.lift genE (FreeGroup.mk (deltaWords.getD i [])) := diagonalAut_genE
  have key := fun (w : List (Fin 5 × Bool)) =>
    lift_eq_lift_substWord_of_lift q hq hker.le genE deltaWords diagonalAut.toMonoidHom hδ ℓ hℓ
      α.toMonoidHom hfix' t hα w
  have eA : h (mkC obsWordA) = h (mkC obsWordA') := by
    rw [cover_hom_mkC, cover_hom_mkC]
    exact key obsWordA (mk_substWord_commGenWords_mem_commutator _) lift_genE_obsWordA
  have eB : h (mkC obsWordB) = h (mkC obsWordB') := by
    rw [cover_hom_mkC, cover_hom_mkC]
    exact key obsWordB (mk_substWord_commGenWords_mem_commutator _) lift_genE_obsWordB
  rw [obsWordA, mkC_substWord_commGenWords, mkC_obsWordA', map_mul] at eA
  rw [obsWordB, mkC_substWord_commGenWords, mkC_obsWordB', map_mul, map_pow] at eB
  have h2'1 : h (mkC kerTwo') = 1 := by rwa [left_eq_mul] at eA
  have h6 : h (mkC kerTwo') = h (mkC kerSix) ^ 3 := by
    rw [kerTwo', mkC_append, mkC_append, map_mul, map_mul, pow_three, mul_assoc]
  have hcomm : Commute (h (mkC kerThree) ^ 2) (h (mkC kerTwo)) :=
    mem_center_iff.1 hc₂ _
  have h21 : h (mkC kerTwo) = 1 := by
    rw [eB, hcomm.mul_pow, ← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul, h3, one_pow,
      one_mul, pow_succ, h2, one_mul, h2'1] at h6
    exact h6.symm
  have hcube : ∀ z ∈ center L, z ^ 3 = 1 := fun z hz => by
    obtain ⟨a, -, b, -, c, -, rfl⟩ := center_eq_cover_word q hker h hhs hhq hz
    rw [h21, h2'1, one_pow, one_pow, mul_one, mul_one, ← pow_mul, mul_comm, pow_mul, h3,
      one_pow]
  have : Finite Cover := cover_card_le.1
  have : Finite L := Finite.of_surjective h hhs
  have h2dvd : 2 ∣ Nat.card (center L) := by
    rcases Nat.even_or_odd (Nat.card (center L)) with he | ho
    · exact even_iff_two_dvd.1 he
    · exact absurd ho hev
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center L) 2 h2dvd
  have hz3 : z ^ 3 = 1 := Subtype.ext (by simpa using hcube z.1 z.2)
  have hz2 : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  have hz1 : z = 1 := by
    calc z = z ^ 3 * (z ^ 2)⁻¹ := by group
      _ = 1 := by rw [hz3, hz2, inv_one, mul_one]
  rw [hz1, orderOf_one] at hz
  exact absurd hz (by norm_num)

theorem exists_t46_quotient
    {L : Type} [Group L] (hQ : CFSG.Blueprint.LieModel (L ⧸ center L) .PSU 6 2 1) :
    ∃ (e : L ⧸ center L ≃* T46) (q : L →* T46), q = e.toMonoidHom.comp (QuotientGroup.mk' _) ∧
      Function.Surjective q ∧ q.ker = center L := by
  obtain ⟨e⟩ := nonempty_mulEquiv_T46 hQ
  refine ⟨e, _, rfl, e.surjective.comp (QuotientGroup.mk'_surjective _), ?_⟩
  ext x
  rw [MonoidHom.mem_ker]
  change e (QuotientGroup.mk' (center L) x) = 1 ↔ _
  rw [map_eq_one_iff _ e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

theorem fix_center_of_fix_two
    {L : Type*} [Group L] [Group.IsPerfect L] (q : L →* T46) (hq : Function.Surjective q)
    (hker : q.ker = center L) (α : MulAut L) (hα3 : α ^ 3 = 1)
    (hfix2 : ∀ z ∈ center L, (∃ k : ℕ, z ^ 2 ^ k = 1) → α z = z) :
    ∀ z ∈ center L, α z = z := by
  obtain ⟨h, hhs, hhq⟩ := exists_cover_hom q hq hker.le
  obtain ⟨hc₃, hc₂, hc₂', h3, h2, h2'⟩ := cover_word_facts q hker h hhq
  have hαc₃ : α (h (mkC kerThree)) ∈ center L :=
    (center L).characteristic_iff_map_eq.mp inferInstance α ▸ mem_map_of_mem α.toMonoidHom hc₃
  have hfix3 : α (h (mkC kerThree)) = h (mkC kerThree) := by
    obtain ⟨a, -, b, -, c, -, he⟩ := center_eq_cover_word q hker h hhs hhq hαc₃
    have hcube : (α (h (mkC kerThree))) ^ 3 = 1 := by rw [← map_pow, h3, map_one]
    have hv2 : (h (mkC kerTwo) ^ b * h (mkC kerTwo') ^ c) ^ 2 = 1 := by
      rw [(Commute.pow_pow (mem_center_iff.1 hc₂' _) b c).mul_pow, ← pow_mul, ← pow_mul,
        mul_comm b, mul_comm c, pow_mul, pow_mul, h2, h2', one_pow, one_pow, one_mul]
    have hwv : Commute (h (mkC kerThree) ^ a) (h (mkC kerTwo) ^ b * h (mkC kerTwo') ^ c) :=
      ((mem_center_iff.1 (mul_mem (pow_mem hc₂ b) (pow_mem hc₂' c)) _))
    have hv : h (mkC kerTwo) ^ b * h (mkC kerTwo') ^ c = 1 := by
      rw [he, hwv.mul_pow, ← pow_mul, mul_comm a, pow_mul, h3, one_pow, one_mul] at hcube
      have h3v : (h (mkC kerTwo) ^ b * h (mkC kerTwo') ^ c) ^ 3 =
          h (mkC kerTwo) ^ b * h (mkC kerTwo') ^ c := by
        rw [pow_succ, hv2, one_mul]
      rw [← h3v, hcube]
    exact fix_of_pow_three α hα3 h3 (a := a) (by rw [he, hv, mul_one])
  intro z hz
  obtain ⟨a, -, b, -, c, -, rfl⟩ := center_eq_cover_word q hker h hhs hhq hz
  rw [map_mul, map_mul, map_pow, map_pow, map_pow, hfix3,
    hfix2 _ hc₂ ⟨1, by rw [pow_one]; exact h2⟩, hfix2 _ hc₂' ⟨1, by rw [pow_one]; exact h2'⟩]

theorem fix_two_iff_inner
    {L : Type} [Group L] [Group.IsPerfect L] (hev : ¬ Odd (Nat.card (center L)))
    (hQ : CFSG.Blueprint.LieModel (L ⧸ center L) .PSU 6 2 1) (α : MulAut L) (hα3 : α ^ 3 = 1) :
    (∀ z ∈ center L, (∃ k : ℕ, z ^ 2 ^ k = 1) → α z = z) ↔ α ∈ inner L := by
  constructor
  · intro hfix2
    by_contra hin
    obtain ⟨e, q, rfl, hq, hker⟩ := exists_t46_quotient hQ
    have hfix := fix_center_of_fix_two _ hq hker α hα3 hfix2
    have h6 : Nat.card (Outer T46) = 6 := by
      rw [← Nat.card_congr (equivalence e).toEquiv]
      exact card_outer_of_lieModel hQ
    set o := outerToT46 e (QuotientGroup.mk α) with ho
    have ho1 : o ≠ 1 := fun h1 => hin ((QuotientGroup.eq_one_iff α).1
      (outerToT46_injective e (h1.trans (map_one _).symm)))
    have ho3 : o ^ 3 = 1 := by
      rw [ho, ← map_pow, ← QuotientGroup.mk_pow, hα3, QuotientGroup.mk_one, map_one]
    set d : Outer T46 := QuotientGroup.mk diagonalAut with hd
    have hd3 : d ^ 3 = 1 := by
      rw [hd, ← QuotientGroup.mk_pow, diagonalAut_pow_three, QuotientGroup.mk_one]
    have hd1 : d ≠ 1 := fun h1 => by
      have := orderOf_mk_diagonalAut
      rw [← hd, h1, orderOf_one] at this
      exact absurd this (by norm_num)
    have hdo : d ∈ zpowers o := by
      by_contra hn
      have := card_le_two_of_not_mem h6 (zpowers o) hd3 hn
      rw [Nat.card_zpowers, orderOf_eq_prime ho3 ho1] at this
      omega
    obtain ⟨n, hn⟩ := (mem_powers_iff_mem_zpowers.2 hdo : d ∈ Submonoid.powers o)
    have hmod : o ^ n = o ^ (n % 3) := by
      conv_lhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul, ho3, one_pow, one_mul]
    have hfixn : ∀ z ∈ center L, (α ^ (n % 3)) z = z := fun z hz => by
      induction n % 3 with
      | zero => rfl
      | succ k ih => rw [pow_succ, MulAut.mul_apply, hfix z hz, ih]
    have hαn : outerToT46 e (QuotientGroup.mk (α ^ (n % 3))) = d := by
      rw [QuotientGroup.mk_pow, map_pow, ← ho, ← hmod]
      exact hn
    rw [outerToT46_mk] at hαn
    obtain ⟨t, ht⟩ := QuotientGroup.eq.1 hαn
    set β := MulAut.congr e (centerQuotientHom L (α ^ (n % 3)))
    have hβ : diagonalAut = β * MulAut.conj t := by rw [ht, mul_inv_cancel_left]
    have hα' : ∀ x, (e.toMonoidHom.comp (QuotientGroup.mk' (center L))) ((α ^ (n % 3)) x) =
        diagonalAut (t⁻¹ * (e.toMonoidHom.comp (QuotientGroup.mk' (center L))) x * t⁻¹⁻¹) :=
      fun x => by
        rw [hβ, MulAut.mul_apply, MulAut.conj_apply]
        simp only [mul_assoc, inv_inv, mul_inv_cancel_left, mul_inv_cancel, mul_one]
        change e (QuotientGroup.mk' (center L) ((α ^ (n % 3)) x)) =
          e (onCenterQuotient (α ^ (n % 3)) (e.symm (e (QuotientGroup.mk' (center L) x))))
        rw [MulEquiv.symm_apply_apply, onCenterQuotient_apply_mk]
    exact not_lift_diagonal_of_fix _ hq hker hev (α ^ (n % 3)) hfixn t⁻¹ hα'
  · rintro ⟨u, rfl⟩ z hz -
    change u * z * u⁻¹ = z
    rw [mem_center_iff.1 hz u, mul_inv_cancel_right]

theorem card_two_part_eq_four
    {L : Type} [Group L] [Group.IsPerfect L] (hev : ¬ Odd (Nat.card (center L)))
    (hQ : CFSG.Blueprint.LieModel (L ⧸ center L) .PSU 6 2 1) (α : MulAut L) (hα3 : α ^ 3 = 1)
    (hout : α ∉ inner L) (K : Subgroup L) (hK : K ≤ center L) (hK2 : IsPGroup 2 K)
    (hKall : ∀ z ∈ center L, (∃ k : ℕ, z ^ 2 ^ k = 1) → z ∈ K) : Nat.card K = 4 := by
  obtain ⟨e, q, rfl, hq, hker⟩ := exists_t46_quotient hQ
  obtain ⟨h, hhs, hhq⟩ := exists_cover_hom _ hq hker.le
  obtain ⟨hc₃, hc₂, hc₂', h3, h2, h2'⟩ := cover_word_facts _ hker h hhq
  have : Finite Cover := cover_card_le.1
  have : Finite L := Finite.of_surjective h hhs
  set f : Fin 2 × Fin 2 → L := fun p => h (mkC kerTwo) ^ p.1.val * h (mkC kerTwo') ^ p.2.val
  have hsub : (K : Set L) ⊆ Set.range f := by
    intro z hzK
    obtain ⟨k, hk⟩ := hK2 ⟨z, hzK⟩
    have hk' : z ^ 2 ^ (k + 1) = 1 := by
      rw [pow_succ, pow_mul, show z ^ 2 ^ k = 1 from congrArg Subtype.val hk, one_pow]
    obtain ⟨a, -, b, hb, c, hc, rfl⟩ := center_eq_cover_word _ hker h hhs hhq (hK hzK)
    have hv2 : (h (mkC kerTwo) ^ b * h (mkC kerTwo') ^ c) ^ 2 = 1 := by
      rw [(Commute.pow_pow (mem_center_iff.1 hc₂' _) b c).mul_pow, ← pow_mul, ← pow_mul,
        mul_comm b, mul_comm c, pow_mul, pow_mul, h2, h2', one_pow, one_pow, one_mul]
    have hwv : Commute (h (mkC kerThree) ^ a) (h (mkC kerTwo) ^ b * h (mkC kerTwo') ^ c) :=
      ((mem_center_iff.1 (mul_mem (pow_mem hc₂ b) (pow_mem hc₂' c)) _))
    have hvk : (h (mkC kerTwo) ^ b * h (mkC kerTwo') ^ c) ^ 2 ^ (k + 1) = 1 := by
      rw [pow_succ', pow_mul, hv2, one_pow]
    have hw1 : h (mkC kerThree) ^ a = 1 := by
      rw [hwv.mul_pow, hvk, mul_one] at hk'
      refine (pow_eq_one_iff_of_coprime (m := 2 ^ (k + 1)) (n := 3)
        (Nat.Coprime.pow_left _ (by norm_num))).1 ⟨hk', ?_⟩
      rw [← pow_mul, mul_comm, pow_mul, h3, one_pow]
    exact ⟨(⟨b, hb⟩, ⟨c, hc⟩), by simp only [f, hw1, one_mul]⟩
  have hle : Nat.card K ≤ 4 := by
    have h1 := Nat.card_mono (Set.finite_range f) hsub
    have h2 := Finite.card_range_le f
    rw [Nat.card_prod, Nat.card_fin] at h2
    exact h1.trans h2
  have h2dvd : 2 ∣ Nat.card (center L) := by
    rcases Nat.even_or_odd (Nat.card (center L)) with he | ho
    · exact even_iff_two_dvd.1 he
    · exact absurd ho hev
  obtain ⟨z₀, hz₀⟩ := exists_prime_orderOf_dvd_card' (G := center L) 2 h2dvd
  have hz₀2 : (z₀ : L) ^ 2 ^ 1 = 1 := by
    rw [pow_one, ← hz₀]
    exact congrArg Subtype.val (pow_orderOf_eq_one z₀)
  have hz₀K : (z₀ : L) ∈ K := hKall _ z₀.2 ⟨1, hz₀2⟩
  have hz₀1 : (z₀ : L) ≠ 1 := fun h1 => by
    have : z₀ = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hz₀
    exact absurd hz₀ (by norm_num)
  obtain ⟨n, hn⟩ := hK2.exists_card_eq
  have hn2 : 2 ≤ 2 ^ n := by
    rw [← hn]
    have : (⟨z₀, hz₀K⟩ : K) ≠ 1 := fun h1 => hz₀1 (congrArg Subtype.val h1)
    exact (Finite.one_lt_card_iff_nontrivial.2 ⟨⟨_, _, this⟩⟩)
  have hn' : n ≠ 1 := by
    rintro rfl
    apply hout
    refine (fix_two_iff_inner hev hQ α hα3).1 fun z hz h2z => ?_
    have hzK : z ∈ K := hKall z hz h2z
    have hαzK : α z ∈ K := by
      obtain ⟨k, hk⟩ := h2z
      exact hKall _ ((center L).characteristic_iff_map_eq.mp inferInstance α ▸
        mem_map_of_mem α.toMonoidHom hz) ⟨k, by rw [← map_pow, hk, map_one]⟩
    by_cases hz1 : z = 1
    · rw [hz1, map_one]
    have hαz1 : α z ≠ 1 := fun h1 => hz1 (α.injective (h1.trans (map_one α).symm))
    have hK2' : Nat.card K = 2 := by rw [hn, pow_one]
    obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : K)).1 hK2'
    have e1 := hy ⟨z, hzK⟩ (fun h1 => hz1 (congrArg Subtype.val h1))
    have e2 := hy ⟨α z, hαzK⟩ (fun h1 => hαz1 (congrArg Subtype.val h1))
    exact congrArg Subtype.val (e2.trans e1.symm)
  have hn4 : 2 ^ n ≤ 4 := hn ▸ hle
  have hn12 : n = 2 := by
    have : n ≤ 2 := by
      by_contra hc
      have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases n <;> simp_all
  rw [hn, hn12]
  norm_num

end CFSG.GGQ2Prime
