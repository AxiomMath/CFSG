module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
import TauCeti.GroupTheory.Perm.Jordan
import TauCeti.GroupTheory.Perm.MultipleTransitivity
import CFSG.LocalAnalysis.ComponentClassification.Sol78AltCentralizer
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Topology.Sheaves.Presheaf
import Std.Tactic.BVDecide.Normalize.Prop

public section

open Equiv Equiv.Perm MulAction

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GL42Seven

private theorem isCycle_subtypePerm_of_support_subset {α : Type*} [Fintype α] [DecidableEq α]
    {g : Perm α} {p : α → Prop} [DecidablePred p] (hg : g.IsCycle)
    (h : ∀ x, p (g x) ↔ p x) (hsub : ∀ x ∈ g.support, p x) :
    (g.subtypePerm h).IsCycle := by
  obtain ⟨x, hx, hcycle⟩ := hg
  have hpx : p x := hsub x (by rwa [Equiv.Perm.mem_support])
  refine ⟨⟨x, hpx⟩, ?_, ?_⟩
  · intro heq
    exact hx (congrArg Subtype.val heq)
  · intro y hy
    have hyv : g y.1 ≠ y.1 := fun hEq => hy (Subtype.ext hEq)
    exact (Equiv.Perm.sameCycle_subtypePerm).mpr (hcycle hyv)

private theorem card_support_eq_four_of_even_order_two {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (hΩ : Fintype.card Ω = 7) {t : Perm Ω} (ht2 : orderOf t = 2) (htev : sign t = 1) :
    t.support.card = 4 := by
  have htprime : Nat.Prime (orderOf t) := by rw [ht2]; exact Nat.prime_two
  obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order htprime
  have hsum : t.cycleType.sum = t.support.card := Equiv.Perm.sum_cycleType t
  have hcard : t.cycleType.card = n + 1 := by rw [hn, Multiset.card_replicate]
  have hsum' : t.cycleType.sum = (n + 1) * 2 := by
    rw [hn, Multiset.sum_replicate, ht2]
    simp
  have hsupp_le : t.support.card ≤ 7 := by
    simpa [hΩ] using Finset.card_le_univ t.support
  have hle : n + 1 ≤ 3 := by omega
  have hexp : t.cycleType.sum + t.cycleType.card = 3 * (n + 1) := by
    rw [hsum', hcard]; ring
  have hsign' : (-1 : ℤˣ) ^ (3 * (n + 1)) = 1 := by
    rw [← hexp, ← Equiv.Perm.sign_of_cycleType t]
    exact htev
  have hEven : Even (3 * (n + 1)) :=
    (neg_one_pow_eq_one_iff_even (show (-1 : ℤˣ) ≠ 1 by norm_num)).mp hsign'
  have hEvenn : Even (n + 1) := by
    rcases Nat.even_mul.mp hEven with h3 | h
    · exact absurd h3 (by decide)
    · exact h
  have hn1 : n + 1 = 2 := by
    rcases hEvenn with ⟨k, hk⟩
    omega
  rw [← hsum, hsum', hn1]

private theorem mem_support_compl_singleton {c : Perm (Fin 8)} {pt : Fin 8}
    (hpt : c.supportᶜ = {pt}) (x : Fin 8) : x ∈ c.support ↔ x ≠ pt := by
  have h : x ∉ c.support ↔ x = pt := by
    simpa using congr_arg (fun s : Finset (Fin 8) => x ∈ s) hpt
  simpa using h.not

private theorem fixes_of_not_isPretransitive {H : Subgroup (Perm (Fin 8))} {c : Perm (Fin 8)}
    (hc : c.IsCycle) (hcH : c ∈ H) (htrans : ¬ IsPretransitive ↥H (Fin 8)) {pt : Fin 8}
    (hpt : c.supportᶜ = {pt}) : ∀ h ∈ H, h pt = pt := by
  have hmem := mem_support_compl_singleton hpt
  intro h hh
  by_contra hne
  apply htrans
  rw [MulAction.isPretransitive_iff]
  intro x y
  have hzsupp : h pt ∈ c.support := (hmem _).mpr hne
  have hzc : c (h pt) ≠ h pt := Equiv.Perm.mem_support.mp hzsupp
  have horbit : ∀ z : Fin 8, ∃ g : ↥H, g • pt = z := by
    intro z
    by_cases hz : z = pt
    · exact ⟨1, by simp [hz]⟩
    · have hzsupp' : z ∈ c.support := (hmem z).mpr hz
      have hzc' : c z ≠ z := Equiv.Perm.mem_support.mp hzsupp'
      obtain ⟨i, hi⟩ := hc.exists_pow_eq hzc hzc'
      refine ⟨⟨c ^ i * h, H.mul_mem (H.pow_mem hcH i) hh⟩, ?_⟩
      simpa [Subgroup.smul_def] using hi
  obtain ⟨g1, hg1⟩ := horbit x
  obtain ⟨g2, hg2⟩ := horbit y
  refine ⟨g2 * g1⁻¹, ?_⟩
  have hinv : g1⁻¹ • x = pt := by
    rw [← hg1, ← mul_smul, inv_mul_cancel, one_smul]
  calc
    (g2 * g1⁻¹) • x = g2 • (g1⁻¹ • x) := mul_smul g2 g1⁻¹ x
    _ = g2 • pt := by rw [hinv]
    _ = y := hg2

private theorem ncard_orbit_eq_twoHundredTen_of_three_pretransitive {Ω : Type*} [Fintype Ω]
    [DecidableEq Ω] (hΩ : Fintype.card Ω = 7) {H : Subgroup (Perm Ω)}
    (h3 : IsMultiplyPretransitive ↥H Ω 3) (x : Fin 3 ↪ Ω) :
    (orbit ↥H x).ncard = 210 := by
  classical
  have hxorbit : orbit ↥H x = Set.univ :=
    (MulAction.isPretransitive_iff_orbit_eq_univ x).mp h3
  have hcount : Nat.card (Fin 3 ↪ Ω) = 210 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_embedding_eq, Fintype.card_fin, hΩ]
    norm_num [Nat.descFactorial]
  rw [hxorbit, Set.ncard_univ]
  exact hcount

private theorem card_stabilizer_mul_eq_of_three_pretransitive {Ω : Type*} [Fintype Ω]
    [DecidableEq Ω] (hΩ : Fintype.card Ω = 7) {H : Subgroup (Perm Ω)}
    (h3 : IsMultiplyPretransitive ↥H Ω 3) (x : Fin 3 ↪ Ω) :
    Nat.card ↥(stabilizer ↥H x) * 210 = Nat.card H :=
  calc Nat.card ↥(stabilizer ↥H x) * 210
      = Nat.card ↥(stabilizer ↥H x) * (orbit ↥H x).ncard :=
        congrArg (Nat.card ↥(stabilizer ↥H x) * ·)
          (ncard_orbit_eq_twoHundredTen_of_three_pretransitive hΩ h3 x).symm
    _ = Nat.card ↥(stabilizer ↥H x) * (stabilizer ↥H x).index :=
        congrArg (Nat.card ↥(stabilizer ↥H x) * ·)
          (MulAction.index_stabilizer (G := ↥H) (x := x)).symm
    _ = Nat.card H := Subgroup.card_mul_index _

private theorem dvd_card_of_three_pretransitive {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (hΩ : Fintype.card Ω = 7) {H : Subgroup (Perm Ω)}
    (h3 : IsMultiplyPretransitive ↥H Ω 3) : 210 ∣ Nat.card H :=
  Dvd.intro_left _ (card_stabilizer_mul_eq_of_three_pretransitive hΩ h3
    ((Fin.castLEEmb (by norm_num : 3 ≤ 7)).trans
      (Fintype.equivFinOfCardEq hΩ).symm.toEmbedding))

private theorem card_stabilizer_eq_one_of_card_eq_210 {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (hΩ : Fintype.card Ω = 7) {H : Subgroup (Perm Ω)}
    (h3 : IsMultiplyPretransitive ↥H Ω 3) (hcard : Nat.card H = 210) (x : Fin 3 ↪ Ω) :
    Nat.card ↥(stabilizer ↥H x) = 1 := by
  have h := card_stabilizer_mul_eq_of_three_pretransitive hΩ h3 x
  rw [hcard] at h
  omega

private theorem false_of_card_eq_210_of_three_pretransitive {Ω : Type*} [Fintype Ω]
    [DecidableEq Ω] (hΩ : Fintype.card Ω = 7) {H : Subgroup (Perm Ω)}
    (hHA : H ≤ alternatingGroup Ω) (h3 : IsMultiplyPretransitive ↥H Ω 3)
    (hcard : Nat.card H = 210) : False := by
  classical
  have h2dvd : 2 ∣ Nat.card H := by rw [hcard]; norm_num
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥H) 2 h2dvd
  have ht_perm : orderOf (t : Perm Ω) = 2 := by rw [Subgroup.orderOf_coe, ht]
  have ht_even : sign (t : Perm Ω) = 1 :=
    Equiv.Perm.mem_alternatingGroup.mp (hHA t.2)
  have ht_supp : (t : Perm Ω).support.card = 4 :=
    card_support_eq_four_of_even_order_two hΩ ht_perm ht_even
  have hfixcard : Fintype.card (Function.fixedPoints (t : Perm Ω)) = 3 := by
    rw [Equiv.Perm.card_fixedPoints, Equiv.Perm.sum_cycleType, ht_supp, hΩ]
  let eS : Fin 3 ≃ Function.fixedPoints (t : Perm Ω) :=
    (Fintype.equivFinOfCardEq hfixcard).symm
  let xS : Fin 3 ↪ Ω :=
    eS.toEmbedding.trans (Function.Embedding.subtype (Function.fixedPoints (t : Perm Ω)))
  have hfixx : t • xS = xS := by
    ext i
    rw [Function.Embedding.smul_apply, Subgroup.smul_def, Equiv.Perm.smul_def]
    exact (eS i).2
  have hstabcard := card_stabilizer_eq_one_of_card_eq_210 hΩ h3 hcard xS
  have hstab : stabilizer ↥H xS = ⊥ :=
    Subgroup.eq_bot_of_card_eq _ hstabcard
  have htstab : t ∈ stabilizer ↥H xS := by
    rw [MulAction.mem_stabilizer_iff]
    exact hfixx
  have htbot : t ∈ (⊥ : Subgroup ↥H) := by rwa [← hstab]
  have ht1 : t = 1 := by simpa using htbot
  rw [ht1] at ht
  simp at ht

private theorem support_subset_of_fixes {H : Subgroup (Perm (Fin 8))} {c : Perm (Fin 8)}
    {pt : Fin 8} (hpt : c.supportᶜ = {pt}) (hfixpt : ∀ h ∈ H, h pt = pt)
    {h : Perm (Fin 8)} (hh : h ∈ H) : h.support ⊆ c.support := by
  intro x hx
  rw [mem_support_compl_singleton hpt]
  intro hxp
  have hx' : h x ≠ x := Equiv.Perm.mem_support.mp hx
  exact hx' (by rw [hxp, hfixpt h hh])

private noncomputable def restrictionHom (H : Subgroup (Perm (Fin 8))) (c : Perm (Fin 8))
    {pt : Fin 8} (hpt : c.supportᶜ = {pt}) (hfixpt : ∀ h ∈ H, h pt = pt) :
    ↥H →* Perm ↥c.support :=
  { toFun := fun h => (h : Perm (Fin 8)).subtypePerm
      (fun x => Equiv.Perm.isInvariant_of_support_le
        (support_subset_of_fixes hpt hfixpt h.2) x)
    map_one' := by
      ext x
      rfl
    map_mul' := by
      intro a b
      ext x
      rfl }

private theorem restrictionHom_injective {H : Subgroup (Perm (Fin 8))} {c : Perm (Fin 8)}
    {pt : Fin 8} (hpt : c.supportᶜ = {pt}) (hfixpt : ∀ h ∈ H, h pt = pt) :
    Function.Injective (restrictionHom H c hpt hfixpt) := by
  classical
  intro a b hab
  apply Subtype.ext
  apply Equiv.Perm.ext
  intro x
  by_cases hx : x ∈ c.support
  · have h := congrArg (fun q : Perm ↥c.support => (q ⟨x, hx⟩ : ↥c.support)) hab
    exact congrArg Subtype.val h
  · have hxpt : x = pt := by
      by_contra hxne
      exact hx ((mem_support_compl_singleton hpt x).mpr hxne)
    rw [hxpt, hfixpt a a.2, hfixpt b b.2]

private theorem restrictionHom_range_le_alternating {H : Subgroup (Perm (Fin 8))}
    {c : Perm (Fin 8)} {pt : Fin 8} (hH : H ≤ alternatingGroup (Fin 8))
    (hpt : c.supportᶜ = {pt}) (hfixpt : ∀ h ∈ H, h pt = pt) :
    (restrictionHom H c hpt hfixpt).range ≤ alternatingGroup ↥c.support := by
  classical
  rintro h' ⟨g, rfl⟩
  rw [Equiv.Perm.mem_alternatingGroup]
  have hof : Equiv.Perm.ofSubtype (restrictionHom H c hpt hfixpt g) = (g : Perm (Fin 8)) := by
    apply Equiv.Perm.ofSubtype_subtypePerm
    · exact fun x => Equiv.Perm.isInvariant_of_support_le
        (support_subset_of_fixes hpt hfixpt g.2) x
    · intro x hx
      by_contra hxp
      have hxpt : x = pt := by
        by_contra hxne
        exact hxp ((mem_support_compl_singleton hpt x).mpr hxne)
      exact hx (by simp [hxpt, hfixpt g g.2])
  rw [← Equiv.Perm.sign_ofSubtype (restrictionHom H c hpt hfixpt g), hof]
  exact Equiv.Perm.mem_alternatingGroup.mp (hH g.2)

private theorem restrictionHom_isCycle {H : Subgroup (Perm (Fin 8))} {c : Perm (Fin 8)}
    {pt : Fin 8} (hpt : c.supportᶜ = {pt}) (hfixpt : ∀ h ∈ H, h pt = pt)
    {g : Perm (Fin 8)} (hg : g.IsCycle) (hh : g ∈ H) (hgs : g.support ⊆ c.support) :
    (restrictionHom H c hpt hfixpt ⟨g, hh⟩).IsCycle := by
  apply isCycle_subtypePerm_of_support_subset hg
    (fun x => Equiv.Perm.isInvariant_of_support_le
      (support_subset_of_fixes hpt hfixpt hh) x)
  intro x hx
  exact hgs hx

private theorem restrictionHom_range_three_pretransitive {H : Subgroup (Perm (Fin 8))}
    {c f : Perm (Fin 8)} {pt : Fin 8} (hc : c.IsCycle) (hcH : c ∈ H)
    (hcs : c.support.card = 7) (hf : f.IsCycle) (hfH : f ∈ H) (hfs : f.support.card = 5)
    (hpt : c.supportᶜ = {pt}) (hfixpt : ∀ h ∈ H, h pt = pt) :
    IsMultiplyPretransitive ↥((restrictionHom H c hpt hfixpt).range) ↥c.support 3 := by
  classical
  let ρ := restrictionHom H c hpt hfixpt
  let H' := ρ.range
  have hρ : Function.Injective ρ := restrictionHom_injective hpt hfixpt
  have hρc_cycle : (ρ ⟨c, hcH⟩).IsCycle :=
    restrictionHom_isCycle hpt hfixpt hc hcH subset_rfl
  have hco : orderOf c = 7 := by rw [hc.orderOf, hcs]
  have hΩcard : Fintype.card ↥c.support = 7 := by rw [Fintype.card_coe, hcs]
  have hρc_card : (ρ ⟨c, hcH⟩).support.card = Fintype.card ↥c.support := by
    rw [← hρc_cycle.orderOf, orderOf_injective ρ hρ ⟨c, hcH⟩, ← Subgroup.orderOf_coe, hco,
      Fintype.card_coe, hcs]
  have hρc_univ : (ρ ⟨c, hcH⟩).support = Finset.univ :=
    Finset.eq_univ_of_card _ hρc_card
  have hρc_mem : ρ ⟨c, hcH⟩ ∈ H' := ⟨⟨c, hcH⟩, rfl⟩
  have hpre7 : IsPreprimitive ↥H' ↥c.support :=
    MulAction.IsPreprimitive.of_prime_card (G := ↥H') (X := ↥c.support)
      (hGX := TauCeti.isPretransitive_of_isCycle_mem_of_support_eq_univ hρc_cycle hρc_mem hρc_univ)
      (by rw [Nat.card_eq_fintype_card, hΩcard]; exact (by decide : Nat.Prime 7))
  have hρf_cycle : (ρ ⟨f, hfH⟩).IsCycle :=
    restrictionHom_isCycle hpt hfixpt hf hfH (support_subset_of_fixes hpt hfixpt hfH)
  have hfo : orderOf f = 5 := by rw [hf.orderOf, hfs]
  have hρf_card : (ρ ⟨f, hfH⟩).support.card = 5 := by
    rw [← hρf_cycle.orderOf, orderOf_injective ρ hρ ⟨f, hfH⟩, ← Subgroup.orderOf_coe, hfo]
  have hρf_mem : ρ ⟨f, hfH⟩ ∈ H' := ⟨⟨f, hfH⟩, rfl⟩
  have hpremulRaw := TauCeti.isMultiplyPreprimitive_of_isCycle_mem hpre7 hρf_cycle
    (by rw [hρf_card]; exact (by decide : Nat.Prime 5)) hρf_mem
  have hpremul : IsMultiplyPreprimitive ↥H' ↥c.support 3 := by
    have hcardcompl : (ρ ⟨f, hfH⟩).supportᶜ.card + 1 = 3 := by
      rw [Finset.card_compl, hρf_card, hΩcard]
    simpa [hcardcompl] using hpremulRaw
  exact hpremul.isMultiplyPretransitive

private theorem exists_restriction_range {H : Subgroup (Perm (Fin 8))} {c f : Perm (Fin 8)}
    (hH : H ≤ alternatingGroup (Fin 8)) (hc : c.IsCycle) (hcH : c ∈ H)
    (hcs : c.support.card = 7) (hf : f.IsCycle) (hfH : f ∈ H) (hfs : f.support.card = 5)
    {pt : Fin 8} (hpt : c.supportᶜ = {pt}) (hfixpt : ∀ h ∈ H, h pt = pt) :
    ∃ H' : Subgroup (Perm ↥c.support),
      H' ≤ alternatingGroup ↥c.support ∧ Nat.card H' = Nat.card H ∧
      Nonempty (↥H ≃* ↥H') ∧ IsMultiplyPretransitive ↥H' ↥c.support 3 := by
  classical
  let ρ := restrictionHom H c hpt hfixpt
  let H' : Subgroup (Perm ↥c.support) := ρ.range
  have hρ : Function.Injective ρ := restrictionHom_injective hpt hfixpt
  have hH'A : H' ≤ alternatingGroup ↥c.support :=
    restrictionHom_range_le_alternating hH hpt hfixpt
  have h3 : IsMultiplyPretransitive ↥H' ↥c.support 3 :=
    restrictionHom_range_three_pretransitive hc hcH hcs hf hfH hfs hpt hfixpt
  refine ⟨H', hH'A, ?_, ⟨MonoidHom.ofInjective hρ⟩, h3⟩
  exact (Nat.card_congr (MonoidHom.ofInjective hρ).toEquiv).symm

private theorem restriction_card_cases {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (hΩ : Fintype.card Ω = 7) {H' : Subgroup (Perm Ω)}
    (hH'A : H' ≤ alternatingGroup Ω) (h3 : IsMultiplyPretransitive ↥H' Ω 3) :
    Nat.card H' = 2520 ∨ Nat.card H' = 210 := by
  classical
  have hdiv := dvd_card_of_three_pretransitive hΩ h3
  let A := alternatingGroup Ω
  let K := H'.subgroupOf A
  have hcardK : Nat.card K = Nat.card H' :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH'A).toEquiv
  have hnt : Nontrivial Ω := Fintype.one_lt_card_iff_nontrivial.mp (by rw [hΩ]; norm_num)
  have hcardA : Nat.card A = 2520 := by
    rw [@nat_card_alternatingGroup Ω _ _ hnt, Nat.card_eq_fintype_card, hΩ]
    norm_num
  have hmul : K.index * Nat.card H' = 2520 := by
    have h := Subgroup.card_mul_index K
    rw [hcardK, hcardA] at h
    rwa [mul_comm] at h
  obtain ⟨q, hq⟩ := hdiv
  have hindex_dvd : K.index ∣ 12 := by
    refine ⟨q, ?_⟩
    have h2 : (K.index * q) * 210 = 12 * 210 := by
      calc (K.index * q) * 210 = K.index * (210 * q) := by ring
        _ = 2520 := by rw [hq] at hmul; exact hmul
        _ = 12 * 210 := by norm_num
    exact (Nat.mul_right_cancel (by norm_num : 0 < 210) h2).symm
  by_cases hK : K = ⊤
  · left
    rw [← hcardK, hK, Subgroup.card_top, hcardA]
  · right
    have h7le : 7 ≤ K.index :=
      CFSG.ComponentClassification.Sol78.le_index_of_mulEquiv_alternating (m := 7)
        (by norm_num) (Equiv.altCongrHom (Fintype.equivFinOfCardEq hΩ)) hK
    have hle12 : K.index ≤ 12 := Nat.le_of_dvd (by norm_num) hindex_dvd
    have hidx : K.index = 12 := by
      interval_cases K.index
      · norm_num at hindex_dvd
      · norm_num at hindex_dvd
      · norm_num at hindex_dvd
      · norm_num at hindex_dvd
      · norm_num at hindex_dvd
      · rfl
    rw [hidx] at hmul
    omega

theorem nonempty_mulEquiv_alt_of_thirtyFive_dvd {H : Subgroup (Perm (Fin 8))}
    (hH : H ≤ alternatingGroup (Fin 8)) (h35 : 35 ∣ Nat.card H) :
    Nonempty (↥H ≃* alternatingGroup (Fin 8)) ∨ Nonempty (↥H ≃* alternatingGroup (Fin 7)) := by
  classical
  have h7dvd : 7 ∣ Nat.card H := dvd_trans (by norm_num : 7 ∣ 35) h35
  have h5dvd : 5 ∣ Nat.card H := dvd_trans (by norm_num : 5 ∣ 35) h35
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨⟨c, hcH⟩, hco⟩ := exists_prime_orderOf_dvd_card' (G := ↥H) 7 h7dvd
  obtain ⟨⟨f, hfH⟩, hfo⟩ := exists_prime_orderOf_dvd_card' (G := ↥H) 5 h5dvd
  have hco' : orderOf c = 7 := by rwa [Subgroup.orderOf_mk] at hco
  have hfo' : orderOf f = 5 := by rwa [Subgroup.orderOf_mk] at hfo
  have hc : c.IsCycle :=
    Equiv.Perm.isCycle_of_prime_order' (by rw [hco']; exact (by decide : Nat.Prime 7))
      (by rw [Fintype.card_fin, hco']; norm_num)
  have hf : f.IsCycle :=
    Equiv.Perm.isCycle_of_prime_order' (by rw [hfo']; exact (by decide : Nat.Prime 5))
      (by rw [Fintype.card_fin, hfo']; norm_num)
  have hcs : c.support.card = 7 := by rw [← hc.orderOf, hco']
  have hfs : f.support.card = 5 := by rw [← hf.orderOf, hfo']
  by_cases htrans : IsPretransitive ↥H (Fin 8)
  · left
    have hpre : IsPreprimitive ↥H (Fin 8) :=
      @TauCeti.isPreprimitive_of_isCycle_mem_of_card_support_add_one_eq_card (Fin 8) _ _ H
        htrans c hc hcH (by rw [hcs, Fintype.card_fin])
    have hAlt : alternatingGroup (Fin 8) ≤ H :=
      TauCeti.alternatingGroup_le_of_isPreprimitive_of_isCycle_mem hpre (p := 5)
        (by decide) (by rw [Nat.card_fin]) hf hfs hfH
    exact ⟨MulEquiv.subgroupCongr (le_antisymm hH hAlt)⟩
  · right
    have hcompl_card : c.supportᶜ.card = 1 := by
      rw [Finset.card_compl, Fintype.card_fin, hcs]
    obtain ⟨pt, hpt⟩ := Finset.card_eq_one.mp hcompl_card
    have hfixpt := fixes_of_not_isPretransitive hc hcH htrans hpt
    obtain ⟨H', hH'A, hcard, ⟨eH⟩, h3⟩ :=
      exists_restriction_range hH hc hcH hcs hf hfH hfs hpt hfixpt
    have hΩcard : Fintype.card ↥c.support = 7 := by rw [Fintype.card_coe, hcs]
    rcases restriction_card_cases hΩcard hH'A h3 with h2520 | h210
    · have hAcard : Nat.card (alternatingGroup ↥c.support) = 2520 := by
        have hnt : Nontrivial ↥c.support :=
          Fintype.one_lt_card_iff_nontrivial.mp (by rw [hΩcard]; norm_num)
        rw [@nat_card_alternatingGroup ↥c.support _ _ hnt, Nat.card_eq_fintype_card, hΩcard]
        norm_num
      have hH'eq : H' = alternatingGroup ↥c.support :=
        Subgroup.eq_of_le_of_card_ge hH'A (by rw [h2520, hAcard])
      exact ⟨eH.trans ((MulEquiv.subgroupCongr hH'eq).trans
        (Equiv.altCongrHom (Fintype.equivFinOfCardEq hΩcard)))⟩
    · exact (false_of_card_eq_210_of_three_pretransitive hΩcard hH'A h3 h210).elim

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GL42Seven
