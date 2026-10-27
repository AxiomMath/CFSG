module

public import CFSG.Certificates.SubgroupEnumeration
public import CFSG.Certificates.NativeRefine
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogEvenCore
public import Certificates.Data.CFSGNative.FischerOddCore.Checks

public noncomputable section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.FischerOddCore.Native
open CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog

variable {n : ℕ}

theorem rep_powA {g : Array ℕ} {G : Equiv.Perm (Fin n)} (hg : Rep n g G) :
    ∀ k, Rep n (powA n g k) (G ^ k)
  | 0 => by rw [pow_zero]; exact rep_idA
  | k + 1 => by rw [pow_succ']; exact rep_compA hg (rep_powA hg k)

theorem rep_of_eqA {t u : Array ℕ} {G : Equiv.Perm (Fin n)} (hu : Rep n u G)
    (h : eqA n t u = true) : Rep n t G := fun x => by
  have := allLt_spec h x.2
  rw [beq_iff_eq] at this
  rw [this, hu x]

theorem isOrdP_iff {p : ℕ} {g : Array ℕ} {G : Equiv.Perm (Fin n)} (hg : Rep n g G) :
    isOrdP n p g = true ↔ G ≠ 1 ∧ G ^ p = 1 := by
  rw [isOrdP, Bool.and_eq_true, Bool.not_eq_true', eqA_iff (rep_powA hg p) rep_idA]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun h => ?_, h2⟩
    rw [(eqA_iff hg rep_idA).2 h] at h1
    exact absurd h1 (by decide)
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    cases h : eqA n g (idA n)
    · rfl
    · exact absurd ((eqA_iff hg rep_idA).1 h) h1

section Closure

variable {gens E : Array (Array ℕ)} {par gen nxt : Array ℕ} {Gs : ℕ → Equiv.Perm (Fin n)}

@[expose] def gensClosure (gens : Array (Array ℕ)) (Gs : ℕ → Equiv.Perm (Fin n)) :
    Subgroup (Equiv.Perm (Fin n)) :=
  Subgroup.closure {x | ∃ k < gens.size, Gs k = x}

theorem closureOK_facts (hok : closureOK n gens E par gen nxt = true) :
    0 < E.size ∧ eqA n E[0]! (idA n) = true ∧
      (∀ i < E.size, i ≠ 0 → par[i]! < i ∧ gen[i]! < gens.size ∧
        eqA n E[i]! (compA n gens[gen[i]!]! E[par[i]!]!) = true) ∧
      ∀ i < E.size, ∀ k < gens.size, nxt[i * gens.size + k]! < E.size ∧
        eqA n E[nxt[i * gens.size + k]!]! (compA n gens[k]! E[i]!) = true := by
  unfold closureOK at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨hpos, h0⟩, hpar⟩, hnxt⟩ := hok
  refine ⟨hpos, h0, fun i hi hi0 => ?_, fun i hi k hk => ?_⟩
  · have := allLt_spec hpar hi
    simp only [Bool.or_eq_true, beq_iff_eq, hi0, false_or, Bool.and_eq_true,
      decide_eq_true_eq] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  · have := allLt_spec (allLt_spec hnxt hi) hk
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this

theorem exists_rep_mem_closure (hgens : ∀ k < gens.size, Rep n gens[k]! (Gs k))
    (hok : closureOK n gens E par gen nxt = true) :
    ∀ i < E.size, ∃ g ∈ gensClosure gens Gs, Rep n E[i]! g := by
  obtain ⟨-, h0, hpar, -⟩ := closureOK_facts hok
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    by_cases hi0 : i = 0
    · subst hi0
      exact ⟨1, Subgroup.one_mem _, rep_of_eqA rep_idA h0⟩
    · obtain ⟨hp, hg, he⟩ := hpar i hi hi0
      obtain ⟨g, hgm, hgr⟩ := ih _ hp (lt_trans hp hi)
      exact ⟨Gs gen[i]! * g, Subgroup.mul_mem _ (Subgroup.subset_closure ⟨_, hg, rfl⟩) hgm,
        rep_of_eqA (rep_compA (hgens _ hg) hgr) he⟩

theorem exists_rep_of_mem_closure (hgens : ∀ k < gens.size, Rep n gens[k]! (Gs k))
    (hok : closureOK n gens E par gen nxt = true) {g : Equiv.Perm (Fin n)}
    (hg : g ∈ gensClosure gens Gs) : ∃ i < E.size, Rep n E[i]! g := by
  obtain ⟨hpos, h0, -, hnxt⟩ := closureOK_facts hok
  let Eset : Set (Equiv.Perm (Fin n)) := {x | ∃ i < E.size, Rep n E[i]! x}
  have hleft : ∀ k < gens.size, ∀ e ∈ Eset, Gs k * e ∈ Eset := by
    rintro k hk e ⟨i, hi, hie⟩
    obtain ⟨hj, he⟩ := hnxt i hi k hk
    exact ⟨_, hj, rep_of_eqA (rep_compA (hgens k hk) hie) he⟩
  have hpow : ∀ k < gens.size, ∀ m : ℕ, ∀ e ∈ Eset, Gs k ^ m * e ∈ Eset := by
    intro k hk m
    induction m with
    | zero => intro e he; rwa [pow_zero, one_mul]
    | succ m ih => intro e he; rw [pow_succ', mul_assoc]; exact hleft k hk _ (ih e he)
  have hE : Eset = (gensClosure gens Gs : Set (Equiv.Perm (Fin n))) := by
    apply CFSG.Certificates.subgroup_enumeration_completeness_of_transitions
    · exact ⟨0, hpos, rep_of_eqA rep_idA h0⟩
    · rintro e ⟨i, hi, hie⟩
      obtain ⟨g, hgm, hgr⟩ := exists_rep_mem_closure hgens hok i hi
      rw [hgr.unique hie] at hgm
      exact (CFSG.Certificates.SubgroupEnumeration.wordWitness_iff_mem_closure _ _).2 hgm
    · rintro a ⟨k, hk, rfl⟩ e he
      exact hleft k hk e he
    · rintro a ⟨k, hk, rfl⟩ e he
      have hinv : (Gs k)⁻¹ = Gs k ^ (orderOf (Gs k) - 1) := by
        rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, Nat.sub_add_cancel (orderOf_pos _),
          pow_orderOf_eq_one]
      rw [hinv]
      exact hpow k hk _ e he
  have : g ∈ Eset := by rw [hE]; exact hg
  exact this

theorem keyAt_eq {b : List ℕ} (hb : ∀ x ∈ b, x < n) {t u : Array ℕ} {G : Equiv.Perm (Fin n)}
    (ht : Rep n t G) (hu : Rep n u G) : keyAt n b t = keyAt n b u := by
  unfold keyAt
  induction b with
  | nil => rfl
  | cons x b ih =>
    simp only [List.foldr_cons]
    rw [ih fun y hy => hb y (List.mem_cons_of_mem _ hy), ht.apply (hb x List.mem_cons_self),
      hu.apply (hb x List.mem_cons_self)]

theorem card_closure_of_keysOK (hgens : ∀ k < gens.size, Rep n gens[k]! (Gs k))
    (hok : closureOK n gens E par gen nxt = true) {b : List ℕ} (hb : ∀ x ∈ b, x < n)
    (hkeys : keysOK n b E = true) : Nat.card (gensClosure gens Gs) = E.size := by
  have hrec := exists_rep_mem_closure hgens hok
  let f : Fin E.size → gensClosure gens Gs := fun i =>
    ⟨(hrec i i.2).choose, (hrec i i.2).choose_spec.1⟩
  have hnd : (E.toList.map (keyAt n b)).Nodup := by
    have hs := CFSG.Certificates.strictIncr_pairwise hkeys
    exact ((List.mergeSort_perm _ _).nodup_iff).1 (hs.imp ne_of_lt)
  have hinj : Function.Injective f := by
    intro i j hij
    have hg := congrArg Subtype.val hij
    have hi := (hrec i i.2).choose_spec.2
    have hj := (hrec j j.2).choose_spec.2
    simp only [f] at hg
    rw [hg] at hi
    have hk := keyAt_eq hb hi hj
    have hlen : (E.toList.map (keyAt n b)).length = E.size := by simp
    rw [getElem!_pos E (i : ℕ) i.2, getElem!_pos E (j : ℕ) j.2] at hk
    have := (hnd.getElem_inj_iff (i := i) (j := j) (hi := by rw [hlen]; exact i.2)
      (hj := by rw [hlen]; exact j.2)).1 (by
        simp only [List.getElem_map, Array.getElem_toList]
        exact hk)
    exact Fin.ext this
  have hsurj : Function.Surjective f := by
    rintro ⟨g, hg⟩
    obtain ⟨i, hi, hig⟩ := exists_rep_of_mem_closure hgens hok hg
    exact ⟨⟨i, hi⟩, Subtype.ext ((hrec i hi).choose_spec.2.unique hig)⟩
  rw [← Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩), Nat.card_eq_fintype_card,
    Fintype.card_fin]

theorem coverOK_spec (hgens : ∀ k < gens.size, Rep n gens[k]! (Gs k))
    (hok : closureOK n gens E par gen nxt = true) {p : ℕ} {xs : Array (Array ℕ)}
    {Xs : ℕ → Equiv.Perm (Fin n)} (hxs : ∀ w < xs.size, Rep n xs[w]! (Xs w))
    {cov : Array (ℕ × ℕ × ℕ)} (hcov : coverOK n p E xs cov = true) {g : Equiv.Perm (Fin n)}
    (hg : g ∈ gensClosure gens Gs) (hg1 : g ≠ 1) (hgp : g ^ p = 1) :
    ∃ w < xs.size, ∃ s ∈ gensClosure gens Gs, ∃ j, 0 < j ∧ j < p ∧
      g = s * Xs w ^ j * s⁻¹ := by
  obtain ⟨i, hi, hig⟩ := exists_rep_of_mem_closure hgens hok hg
  have hord : isOrdP n p E[i]! = true := (isOrdP_iff hig).2 ⟨hg1, hgp⟩
  have h := allLt_spec hcov hi
  simp only [hord, Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hw, hs⟩, hj0⟩, hjp⟩, heq⟩ := h
  obtain ⟨s, hsm, hsr⟩ := exists_rep_mem_closure hgens hok _ hs
  refine ⟨_, hw, s, hsm, _, hj0, hjp, ?_⟩
  have := eq_of_eqA (rep_compA hsr (rep_powA (hxs _ hw) _)) (rep_compA hig hsr) heq
  rw [this]
  group

end Closure

theorem oddCore_eq_bot_of_sylow_witnesses {G : Type*} [Group G] [Finite G]
    (h : ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ Nat.card G → ∃ P : Sylow p G,
      ∀ y ∈ (P : Subgroup G), orderOf y = p → ∃ x s : G, ∃ j : ℕ, 0 < j ∧ j < p ∧
        orderOf x = p ∧ y = s * x ^ j * s⁻¹ ∧
        ∃ g : G, ∃ k : ℕ, (x * g * x * g⁻¹) ^ k ≠ 1 ∧ ((x * g * x * g⁻¹) ^ k) ^ 2 = 1) :
    CFSG.oddCore G = ⊥ := by
  by_contra hne
  set N := CFSG.oddCore G
  have hodd : Odd (Nat.card N) := odd_card_oddCore
  have hN1 : Nat.card N ≠ 1 := fun h1 => hne (Subgroup.eq_bot_of_card_eq N h1)
  obtain ⟨p, hp, hpN⟩ := Nat.exists_prime_and_dvd hN1
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hpN)
  have hpG : p ∣ Nat.card G := hpN.trans (Subgroup.card_subgroup_dvd_card N)
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hP⟩ := h p hp hp2 hpG
  obtain ⟨y₀, hy₀⟩ := exists_prime_orderOf_dvd_card' (G := N) p hpN
  obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow (IsPGroup.of_card (p := p) (n := 1)
    (G := ↥(Subgroup.zpowers (y₀ : G))) (by
      rw [Nat.card_zpowers, Subgroup.orderOf_coe, hy₀, pow_one]))
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G Q P
  set y := c * (y₀ : G) * c⁻¹
  have hyP : y ∈ (P : Subgroup G) := by
    rw [← hc, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ (MulAut.conj c) _ (hQ (Subgroup.mem_zpowers _))
  have hyN : y ∈ N := (inferInstance : N.Normal).conj_mem _ y₀.2 c
  have hyo : orderOf y = p := by
    rw [show y = MulAut.conj c (y₀ : G) from rfl, MulEquiv.orderOf_eq, Subgroup.orderOf_coe, hy₀]
  obtain ⟨x, s, j, hj0, hjp, hxo, hy, g, k, hk1, hk2⟩ := hP y hyP hyo
  have hxj : x ^ j ∈ N := by
    have := (inferInstance : N.Normal).conj_mem _ hyN s⁻¹
    rwa [hy, inv_inv, show s⁻¹ * (s * x ^ j * s⁻¹) * s = x ^ j by group] at this
  have hcop : Nat.Coprime p j :=
    (Nat.Prime.coprime_iff_not_dvd hp).2 (Nat.not_dvd_of_pos_of_lt hj0 hjp)
  have hx : x ∈ N := by
    have hg := Nat.gcd_eq_gcd_ab j p
    rw [Nat.Coprime.gcd_eq_one hcop.symm, Nat.cast_one] at hg
    have hxp : x ^ p = 1 := hxo ▸ pow_orderOf_eq_one x
    have e : x = (x ^ j) ^ (Nat.gcdA j p) * (x ^ p) ^ (Nat.gcdB j p) := by
      rw [← zpow_natCast x j, ← zpow_natCast x p, ← zpow_mul, ← zpow_mul, ← zpow_add, ← hg,
        zpow_one]
    rw [e, hxp, one_zpow, mul_one]
    exact N.zpow_mem hxj _
  have hw : x * g * x * g⁻¹ ∈ N := by
    rw [show x * g * x * g⁻¹ = x * (g * x * g⁻¹) by group]
    exact N.mul_mem hx ((inferInstance : N.Normal).conj_mem _ hx g)
  exact not_mem_oddCore_of_sq_eq_one hk1 hk2 (N.pow_mem hw k)

end CFSG.Sporadic.FischerOddCore
