module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporGen
public import CFSG.Sporadic.Schreier.LyLocalAutQ

import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporOrder
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporZTwo
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5CalL0
import CFSG.LocalAnalysis.WeakClosure81.W18ASNineCF
import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G47GapAbs
import CFSG.Sporadic.Schreier.LyOuter

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)
open CFSG.Sporadic.Ly CFSG.Sporadic.LySchreier

private def fbarPair (y : Fin 11) : Fin 11 :=
  if y.val < 8 then ⟨2 * (y.val / 2), by omega⟩ else y

theorem eq_one_of_commute_natPerm_four {τ : Equiv.Perm (Fin 11)} {p : ℕ} (hp : p.Prime)
    (h5 : 5 ≤ p) (hτ : τ ^ p = 1) (hc : ∀ y, τ (natPerm 4 y) = natPerm 4 (τ y)) : τ = 1 := by
  have hfix4 : ∀ y : Fin 11, natPerm 4 y = y ↔ 8 ≤ y.val := by decide
  have hinv4 : ∀ y : Fin 11, natPerm 4 (natPerm 4 y) = y := by decide
  have hiter : ∀ x, (⇑τ)^[p] x = x := fun x => by
    rw [Equiv.Perm.iterate_eq_pow, hτ, Equiv.Perm.coe_one, id]
  have hhigh : ∀ y : Fin 11, 8 ≤ y.val → τ y = y := by
    have h := CFSG.LocalAnalysis.UniquenessCase.PartTwo.s16c1_G47_fix_of_prime_iterate
      (f := ⇑τ) (S := ↑({8, 9, 10} : Finset (Fin 11)))
      (by rw [Set.ncard_coe_finset]; decide) (Finset.finite_toSet _) hp h5 hiter (by
        intro y hy
        have hy' : 8 ≤ y.val := by
          simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
            Set.mem_singleton_iff] at hy
          rcases hy with rfl | rfl | rfl <;> decide
        have : natPerm 4 (τ y) = τ y := by rw [← hc, (hfix4 y).2 hy']
        have h8 := (hfix4 _).1 this
        simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff]
        revert h8
        generalize τ y = v
        revert v
        decide)
    intro y hy
    refine h y ?_
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    revert hy
    revert y
    decide
  have hlow : ∀ y : Fin 11, y.val < 8 → (τ y).val < 8 := by
    intro y hy
    by_contra h8
    have := hhigh (τ y) (by omega)
    have := τ.injective this
    rw [this] at h8
    exact h8 hy
  have hlowpow : ∀ n : ℕ, ∀ y : Fin 11, y.val < 8 → ((τ ^ n) y).val < 8 := by
    intro n
    induction n with
    | zero => intro y hy; simpa using hy
    | succ n ih =>
      intro y hy
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact hlow _ (ih y hy)
  have hpair_f : ∀ y, fbarPair (natPerm 4 y) = fbarPair y := by unfold fbarPair; decide
  have hpair_or : ∀ y, fbarPair y = y ∨ fbarPair y = natPerm 4 y := by unfold fbarPair; decide
  have hkey : ∀ v, fbarPair (τ (fbarPair v)) = fbarPair (τ v) := by
    intro v
    rcases hpair_or v with h | h
    · rw [h]
    · rw [h, hc, hpair_f]
  have hpair_low : ∀ y : Fin 11, y.val < 8 →
      (fbarPair y).val < 8 ∧ (fbarPair y).val % 2 = 0 := by unfold fbarPair; decide
  have hpair_even : ∀ y : Fin 11, y.val < 8 → y.val % 2 = 0 → fbarPair y = y := by
    unfold fbarPair; decide
  let π : Fin 11 → Fin 11 := fun r => if r.val < 8 ∧ r.val % 2 = 0 then fbarPair (τ r) else r
  have hπ : ∀ n : ℕ, ∀ r : Fin 11, π^[n] r =
      if r.val < 8 ∧ r.val % 2 = 0 then fbarPair ((τ ^ n) r) else r := by
    intro n
    induction n with
    | zero =>
      intro r
      split_ifs with h
      · rw [Function.iterate_zero, id, pow_zero, Equiv.Perm.coe_one, id, hpair_even r h.1 h.2]
      · rfl
    | succ n ih =>
      intro r
      rw [Function.iterate_succ_apply', ih r]
      split_ifs with h
      · have hl := hpair_low _ (hlowpow n r h.1)
        simp only [π, if_pos hl]
        rw [hkey, pow_succ', Equiv.Perm.mul_apply]
      · simp only [π, if_neg h]
  have hπp : ∀ r, π^[p] r = r := by
    intro r
    rw [hπ p r]
    split_ifs with h
    · rw [hτ, Equiv.Perm.coe_one, id, hpair_even r h.1 h.2]
    · rfl
  have hfixπ := CFSG.LocalAnalysis.UniquenessCase.PartTwo.s16c1_G47_fix_of_prime_iterate
    (f := π) (S := {r | r.val < 8 ∧ r.val % 2 = 0}) (by
      have : ({r : Fin 11 | r.val < 8 ∧ r.val % 2 = 0} : Set (Fin 11)) =
          ↑({0, 2, 4, 6} : Finset (Fin 11)) := by
        ext r
        simp only [Set.mem_setOf_eq, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff]
        revert r
        decide
      rw [this, Set.ncard_coe_finset]
      decide) (Set.toFinite _) hp h5 hπp (by
      intro r hr
      have hr' : r.val < 8 ∧ r.val % 2 = 0 := hr
      show π r ∈ {r : Fin 11 | r.val < 8 ∧ r.val % 2 = 0}
      rw [Set.mem_setOf_eq]
      simp only [π, if_pos hr']
      exact hpair_low _ (hlow r hr'.1))
  have hsame : ∀ u v : Fin 11, u.val < 8 → v.val < 8 → fbarPair u = fbarPair v →
      u = v ∨ u = natPerm 4 v := by unfold fbarPair; decide
  have hτy : ∀ y : Fin 11, y.val < 8 → τ y = y ∨ τ y = natPerm 4 y := by
    intro y hy
    have hr := hpair_low y hy
    have h := hfixπ (fbarPair y) hr
    simp only [π, if_pos hr] at h
    rw [hkey] at h
    exact hsame _ _ (hlow y hy) hy h
  have hsq : τ ^ 2 = 1 := by
    refine Equiv.ext fun y => ?_
    rw [pow_two, Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
    by_cases hy : y.val < 8
    · rcases hτy y hy with h | h
      · rw [h, h]
      · rw [h, hc, h, hinv4]
    · rw [hhigh y (by omega), hhigh y (by omega)]
  have h2 : orderOf τ ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  have hpd : orderOf τ ∣ p := orderOf_dvd_of_pow_eq_one hτ
  have h1 : orderOf τ ∣ Nat.gcd 2 p := Nat.dvd_gcd h2 hpd
  rw [(Nat.coprime_primes Nat.prime_two hp).2 (by omega)] at h1
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h1)

theorem imgC_eq_natPerm_four_of_mem_lyCQ
    {x : J} (hx : x ∈ lyCQ)
    (hx2 : x ^ 2 = 1) (hx1 : x ≠ 1) (hxz : x ≠ lyz) :
    imgC ⟨x, centralizer_lyQ_le hx⟩ = natPerm 4 := by
  obtain ⟨m, hm, hmx⟩ := imgCQ_mem ⟨x, hx⟩
  have hmx' : imgC ⟨x, centralizer_lyQ_le hx⟩ = natPerm m := hmx
  have hsq : natPerm m ^ 2 = 1 := by
    rw [← hmx', ← map_pow]
    have : (⟨x, centralizer_lyQ_le hx⟩ : lyC) ^ 2 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hx2)
    rw [this, map_one]
  have hm14 : ∀ m : Fin 12, m.val ∈ [1, 4, 6, 8, 9, 11] → natPerm m ^ 2 = 1 →
      m = 1 ∨ m = 4 := by decide
  have hone : natPerm 1 = 1 := by decide
  rcases hm14 m hm hsq with rfl | rfl
  · exfalso
    rw [hone] at hmx'
    rcases mem_zGroup.1 ((imgC_eq_one_iff _).1 hmx') with h | h
    · have h' := congrArg Subtype.val h
      rw [Subgroup.coe_one] at h'
      exact hx1 h'
    · exact hxz (congrArg Subtype.val h)
  · exact hmx'

private theorem mem_center_lyQ_of_mem
    {y : J} (hy : y ∈ lyQ)
    (hc : ∀ q ∈ lyQ, y * q = q * y) :
    y = 1 ∨ y = lyz ∨ y = lyf ∨ y = (sE 207 : J) := by
  have hcen : (⟨y, hy⟩ : lyQ) ∈ Subgroup.center lyQ := by
    rw [Subgroup.mem_center_iff]
    intro q
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact (hc q q.2).symm
  obtain ⟨q, hq, hqy⟩ := (mem_center_lyQ_iff _).1 hcen
  have e : ((sE q : lyS) : J) = y := hqy
  simp only [zqList, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · left
    rw [← e, sE_zero, Subgroup.coe_one]
  · right; left
    rw [← e, sE_six]
  · right; right; left
    rw [← e, lyf_eq]
    rfl
  · right; right; right
    exact e.symm

theorem not_orderOf_eq_of_mem_lyN
    {g : J} (hg : g ∈ lyN) {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hgo : orderOf g = p) : False := by
  have hgp : g ^ p = 1 := hgo ▸ pow_orderOf_eq_one g
  set w : J := (sE 207 : J) with hw
  have hw1 : w ≠ 1 := by
    rw [hw, ← show ((sE 0 : lyS) : J) = 1 by rw [sE_zero]; rfl]
    exact sE_ne (by decide) (by norm_num) (by decide)
  let ZQ : J → Prop := fun y => y ∈ lyQ ∧ ∀ q ∈ lyQ, y * q = q * y
  have hzZ : ZQ lyz := ⟨lyz_mem_lyQ, fun q hq =>
    (Subgroup.mem_centralizer_iff.1 lyz_mem_lyCQ q hq).symm⟩
  have hfZ : ZQ lyf := ⟨lyf_mem_lyQ, fun q hq =>
    (Subgroup.mem_centralizer_iff.1 lyf_mem_lyCQ q hq).symm⟩
  have hwZ : ZQ w := by
    have hwQ : w ∈ lyQ := mem_lyQ.2 ⟨207, (tableFacts.zq 207 (by decide)).1, rfl⟩
    refine ⟨hwQ, fun q hq => ?_⟩
    have hcen : (⟨w, hwQ⟩ : lyQ) ∈ Subgroup.center lyQ :=
      (mem_center_lyQ_iff _).2 ⟨207, by decide, rfl⟩
    have h' := congrArg Subtype.val (Subgroup.mem_center_iff.1 hcen ⟨q, hq⟩)
    rw [Subgroup.coe_mul, Subgroup.coe_mul] at h'
    exact h'.symm
  have hconj : ∀ c ∈ lyN, ∀ y, ZQ y → ZQ (c * y * c⁻¹) := by
    intro c hc y ⟨hyQ, hyc⟩
    have hcQ : ∀ q, q ∈ lyQ ↔ c * q * c⁻¹ ∈ lyQ := (Subgroup.mem_normalizer_iff.1 hc)
    refine ⟨(hcQ y).1 hyQ, fun q hq => ?_⟩
    have hq' : c⁻¹ * q * c ∈ lyQ :=
      (hcQ _).2 (by rw [show c * (c⁻¹ * q * c) * c⁻¹ = q by group]; exact hq)
    have := hyc _ hq'
    calc c * y * c⁻¹ * q = c * (y * (c⁻¹ * q * c)) * c⁻¹ := by group
      _ = c * ((c⁻¹ * q * c) * y) * c⁻¹ := by rw [this]
      _ = q * (c * y * c⁻¹) := by group
  let S : Set J := {lyz, lyf, w}
  have hS4 : S.ncard ≤ 4 := by
    have h1 := Set.ncard_insert_le lyz ({lyf, w} : Set J)
    have h2 := Set.ncard_insert_le lyf ({w} : Set J)
    rw [Set.ncard_singleton] at h2
    exact h1.trans (by omega)
  have hSfin : S.Finite := Set.toFinite _
  let φ : J → J := fun y => g * y * g⁻¹
  have hφn : ∀ n : ℕ, ∀ y, φ^[n] y = g ^ n * y * (g ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro y; simp
    | succ n ih =>
      intro y
      rw [Function.iterate_succ_apply', ih y]
      simp only [φ]
      group
  have hφp : ∀ y, φ^[p] y = y := by
    intro y
    rw [hφn, hgp, one_mul, inv_one, mul_one]
  have hφS : ∀ y ∈ S, φ y ∈ S := by
    intro y hy
    have hyZ : ZQ y := by
      simp only [S, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      exacts [hzZ, hfZ, hwZ]
    have hy1 : y ≠ 1 := by
      simp only [S, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      exacts [lyz_ne_one, lyf_ne_one, hw1]
    obtain ⟨hQ, hc⟩ := hconj g hg y hyZ
    rcases mem_center_lyQ_of_mem hQ hc with h | h | h | h
    · exfalso
      apply hy1
      have : g * y * g⁻¹ = 1 := h
      calc y = g⁻¹ * (g * y * g⁻¹) * g := by group
        _ = 1 := by rw [this]; group
    · simp only [S, Set.mem_insert_iff, Set.mem_singleton_iff]; left; exact h
    · simp only [S, Set.mem_insert_iff, Set.mem_singleton_iff]; right; left; exact h
    · simp only [S, Set.mem_insert_iff, Set.mem_singleton_iff]; right; right; exact h
  have hfixS := CFSG.LocalAnalysis.UniquenessCase.PartTwo.s16c1_G47_fix_of_prime_iterate
    hS4 hSfin hp h5 hφp hφS
  have hgz : g * lyz * g⁻¹ = lyz := hfixS lyz (by simp [S])
  have hgf : g * lyf * g⁻¹ = lyf := hfixS lyf (by simp [S])
  have hgC : g ∈ lyC := by
    rw [full_involution_centralizer.1, Subgroup.mem_centralizer_singleton_iff]
    calc g * lyz = (g * lyz * g⁻¹) * g := by group
      _ = lyz * g := by rw [hgz]
  have hfC : lyf ∈ lyC := centralizer_lyQ_le lyf_mem_lyCQ
  set τ : Equiv.Perm (Fin 11) := imgC ⟨g, hgC⟩ with hτdef
  have hfbar : imgC ⟨lyf, hfC⟩ = natPerm 4 :=
    imgC_eq_natPerm_four_of_mem_lyCQ lyf_mem_lyCQ lyf_sq' lyf_ne_one lyz_ne_lyf.symm
  have hgf' : g * lyf = lyf * g := by
    calc g * lyf = (g * lyf * g⁻¹) * g := by group
      _ = lyf * g := by rw [hgf]
  have hprod : (⟨g, hgC⟩ : lyC) * ⟨lyf, hfC⟩ = ⟨lyf, hfC⟩ * ⟨g, hgC⟩ := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact hgf'
  have hcomm : τ * natPerm 4 = natPerm 4 * τ := by
    rw [← hfbar, hτdef, ← map_mul, ← map_mul, hprod]
  have hτp : τ ^ p = 1 := by
    rw [hτdef, ← map_pow]
    have : (⟨g, hgC⟩ : lyC) ^ p = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hgp)
    rw [this, map_one]
  have hτ1 := eq_one_of_commute_natPerm_four hp h5 hτp fun y => by
    have := congrArg (fun σ : Equiv.Perm (Fin 11) => σ y) hcomm
    simpa only [Equiv.Perm.mul_apply] using this
  rcases mem_zGroup.1 ((imgC_eq_one_iff _).1 (hτdef ▸ hτ1)) with h | h
  · have h' := congrArg Subtype.val h
    rw [Subgroup.coe_one] at h'
    have : g = 1 := h'
    rw [this, orderOf_one] at hgo
    omega
  · have : g = lyz := congrArg Subtype.val h
    rw [this, orderOf_lyz] at hgo
    omega

theorem card_lyN_dvd :
    Nat.card lyN ∣ 2 ^ 8 * 3 ^ 7 := by
  have hprime : ∀ r : ℕ, r.Prime → r ∣ Nat.card lyN → r = 2 ∨ r = 3 := by
    intro r hr hdvd
    by_contra h23
    push Not at h23
    have h5 : 5 ≤ r := by
      have h2 := hr.two_le
      have h4 : r ≠ 4 := fun h => by rw [h] at hr; norm_num at hr
      omega
    have : Fact r.Prime := ⟨hr⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' r hdvd
    exact not_orderOf_eq_of_mem_lyN x.2 hr h5 (by rw [Subgroup.orderOf_coe, hx])
  have hJ : Nat.card lyN ∣ 2 ^ 8 * 3 ^ 7 * 92458953125 := by
    rw [show (2 ^ 8 * 3 ^ 7 * 92458953125 : ℕ) = 51765179004000000 by norm_num, ← card_J]
    exact Subgroup.card_subgroup_dvd_card lyN
  refine Nat.Coprime.dvd_of_dvd_mul_right (Nat.coprime_of_dvd fun r hr h1 h2 => ?_) hJ
  rcases hprime r hr h1 with rfl | rfl <;> norm_num at h2

theorem isSylowIn_lyS :
    IsSylowIn 2 lyS ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨le_top, ?_, ?_⟩
  · rw [← lySylow_coe]
    exact lySylow.isPGroup'
  · rw [Subgroup.relIndex_top_right, ← lySylow_coe]
    exact lySylow.not_dvd_index

theorem lyS_le_lyN :
    lyS ≤ lyN := by
  have := lyQ_characteristic
  exact Subgroup.le_normalizer_of_normal_subgroupOf lyQ_le

private theorem map_eq_of_characteristic_subgroupOf {C : Type} [Group C] {S Q : Subgroup C}
    {ψ : C ≃* C} (hψ : S.map ψ.toMonoidHom = S) (hQS : Q ≤ S)
    (hQ : (Q.subgroupOf S).Characteristic) : Q.map ψ.toMonoidHom = Q := by
  have hmaps : ∀ φ : C ≃* C, S.map φ.toMonoidHom = S → ∀ y ∈ Q, φ y ∈ Q := by
    intro φ hφ y hy
    let φS : S ≃* S := (φ.subgroupMap S).trans (MulEquiv.subgroupCongr hφ)
    have hch := Subgroup.characteristic_iff_map_eq.1 hQ φS
    have hmem : φS ⟨y, hQS hy⟩ ∈ Q.subgroupOf S := by
      rw [← hch]
      exact ⟨⟨y, hQS hy⟩, Subgroup.mem_subgroupOf.2 hy, rfl⟩
    exact Subgroup.mem_subgroupOf.1 hmem
  have hψ' : S.map ψ.symm.toMonoidHom = S := by
    ext x
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm]
    constructor
    · intro hx
      have : ψ x ∈ S.map ψ.toMonoidHom := by rw [hψ]; exact hx
      rwa [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply] at this
    · intro hx
      rw [← hψ]
      exact ⟨x, hx, rfl⟩
  refine le_antisymm ?_ fun x hx => ?_
  · rintro _ ⟨y, hy, rfl⟩
    exact hmaps ψ hψ y hy
  · exact ⟨ψ.symm x, hmaps ψ.symm hψ' x hx, by simp⟩

private theorem eq_one_or_eq_lyz_of_mem_lyS :
    ∀ x ∈ lyS, (∀ p ∈ lyS, x * p = p * x) → x = 1 ∨ x = lyz := by
  intro x hx hc
  have hcen : (⟨x, hx⟩ : lyS) ∈ Subgroup.center lyS := by
    rw [Subgroup.mem_center_iff]
    intro p
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact (hc p p.2).symm
  rw [center_lyS, mem_zpowers_zS] at hcen
  rcases hcen with h | h
  · left
    have h' := congrArg Subtype.val h
    rw [Subgroup.coe_one] at h'
    exact h'
  · right
    exact congrArg Subtype.val h

section


theorem not_hasCompFactor_isCalL0_lyC :
    ¬ HasCompFactor lyC IsCalL0 := by
  rintro ⟨L, _, hL, hcal⟩
  have : Finite L := isCompositionFactor_finite hL
  rcases isCompositionFactor_of_normal (Subgroup.center lyC) hL with h | h
  · obtain ⟨a, b, hab⟩ := (isCalL0_nonabelian_not_sectionalTwoRankLE L hcal).1
    exact hab (isCompositionFactor_commute (fun x y => Subtype.ext
      (Subgroup.mem_center_iff.1 y.2 x)) h a b)
  · have : IsSimpleGroup (alternatingGroup (Fin 11)) := alternatingGroup.isSimpleGroup (by simp)
    have : IsSimpleGroup (lyC ⧸ Subgroup.center lyC) := lyCenterEquiv.isSimpleGroup
    have hc : Nat.card (lyC ⧸ Subgroup.center lyC) = 19958400 := by
      rw [Nat.card_congr lyCenterEquiv.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      decide
    exact not_isCalL0_of_isCompositionFactor_of_isSimpleGroup
      CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput (k := 7)
      (by rw [hc]; decide +kernel) h hcal

theorem not_hasCompFactor_isCalL0_lyN :
    ¬ HasCompFactor lyN IsCalL0 :=
  not_hasCompFactor_isCalL0_of_dvd CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
    (k := 8) (N := 559872) (by decide +kernel) (by simpa using card_lyN_dvd)

theorem isLPair_lyC_lyN :
    IsLPair IsCalL0 lyS lyC lyN where
  le_left := lyS_le_lyC
  le_right := lyS_le_lyN
  ne_top_left h := by
    have hc : Nat.card lyC = 39916800 := by
      rw [full_involution_centralizer.1]
      exact full_involution_centralizer.2
    rw [h, Subgroup.card_top, card_J] at hc
    omega
  ne_top_right h := by
    have h1 := card_lyN_dvd
    rw [h, Subgroup.card_top, card_J] at h1
    have := Nat.le_of_dvd (by norm_num) h1
    omega
  not_left := not_hasCompFactor_isCalL0_lyC
  not_right := not_hasCompFactor_isCalL0_lyN
  sup_eq_top := intrinsic_local_generation.2.2

theorem asch54SporGenAt_ly :
    Asch54SporGenAt .Ly :=
  asch54SporGenAt_of_isLPair_of_aut (C := J)
    (CFSG.Sporadic.Bridge.Ly.nonempty_mulEquiv.map fun f => f.symm.trans lyEquivJ)
    (fun X _ _ hX => (isCalL0_nonabelian_not_sectionalTwoRankLE X hX).1)
    (Nat.le_of_dvd two_pos card_outer_J_dvd) isSylowIn_lyS isLPair_lyC_lyN fun ψ hψ => by
      have hz : ψ lyz = lyz := apply_eq_of_center_eq_pair lyz_mem_lyS lyz_ne_one
        (fun p hp => (lyz_comm_S p hp).symm) eq_one_or_eq_lyz_of_mem_lyS hψ
      refine ⟨?_, ?_⟩
      · rw [full_involution_centralizer.1]
        exact map_centralizer_singleton_eq_of_apply_eq hz
      · unfold lyN
        rw [Subgroup.map_equiv_normalizer_eq,
          map_eq_of_characteristic_subgroupOf hψ lyQ_le lyQ_characteristic]

end

end CFSG.LocalAnalysis.WeakClosure81

end
