module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BlockStabPerfect
import CFSG.Permutation.FiveTransitive.PermCentralizer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.AltTen

open Equiv Equiv.Perm

private theorem mem_alternatingGroup_of_isCycle_card_five {σ : Perm (Fin 10)}
    (hσ : σ.IsCycle) (hcard : σ.support.card = 5) : σ ∈ alternatingGroup (Fin 10) := by
  rw [Equiv.Perm.mem_alternatingGroup, hσ.sign, hcard]
  norm_num

private theorem exists_five_cycle_of_support {S : Finset (Fin 10)} (hS : S.card = 5) :
    ∃ c : Perm (Fin 10), c.IsCycle ∧ c.support = S ∧ c ^ 5 = 1 ∧
      (∀ x, c x ≠ x ↔ x ∈ S) ∧ c ∈ alternatingGroup (Fin 10) := by
  obtain ⟨c, hc, hsupp⟩ :=
    CFSG.AGLEmbedding.exists_isCycle_support_eq (s := S) (by rw [hS]; norm_num)
  have hcard : c.support.card = 5 := by rw [hsupp, hS]
  have hord : orderOf c = 5 := by rw [hc.orderOf, hcard]
  refine ⟨c, hc, hsupp, ?_, ?_,
    mem_alternatingGroup_of_isCycle_card_five hc hcard⟩
  · rw [← hord]
    exact pow_orderOf_eq_one c
  · intro x
    rw [← Equiv.Perm.mem_support, hsupp]


private theorem fixes_of_commute_of_five_set {O : Finset (Fin 10)} (hO : O.card = 5)
    {a b : Perm (Fin 10)}
    (haO : ∀ i, i ∈ O ↔ a i ∈ O) (hbO : ∀ i, i ∈ O ↔ b i ∈ O)
    (ha5 : a ^ 5 = 1) (hact : ∃ i ∈ O, a i ≠ i)
    (hcomm : Commute a b) (hbprime : (orderOf b).Prime) (hb5 : orderOf b ≠ 5) :
    ∀ i ∈ O, b i = i := by
  classical
  letI : Fintype {i // i ∈ O} := Subtype.fintype (fun i => i ∈ O)
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let aO : Perm {i // i ∈ O} := a.subtypePerm (fun i => (haO i).symm)
  have haO5 : aO ^ 5 = 1 := by
    change (a.subtypePerm (fun i => (haO i).symm)) ^ 5 = 1
    rw [Equiv.Perm.subtypePerm_pow]
    simp [ha5]
    ext x
    rfl
  have haO1 : aO ≠ 1 := by
    obtain ⟨i, hiO, hi⟩ := hact
    intro h
    apply hi
    have h2 := congrArg (fun f : Perm {i // i ∈ O} => f ⟨i, hiO⟩) h
    have h3 := congrArg Subtype.val h2
    simpa [aO, Equiv.Perm.subtypePerm_apply] using h3
  have hcardO : Fintype.card {i // i ∈ O} = 5 := by
    rw [← Nat.card_eq_fintype_card, Nat.subtype_card O (fun x => Iff.rfl), hO]
  have haOord : orderOf aO = 5 := orderOf_eq_prime haO5 haO1
  have haOcyc : aO.IsCycle := by
    refine Equiv.Perm.isCycle_of_prime_order'
      (show Nat.Prime (orderOf aO) by rw [haOord]; exact Nat.prime_five) ?_
    rw [hcardO, haOord]
    norm_num
  let g : Perm (Fin 10) := Equiv.Perm.ofSubtype aO
  have hgcyc : g.IsCycle := by
    rw [← Equiv.Perm.card_cycleType_eq_one] at haOcyc ⊢
    change (Equiv.Perm.ofSubtype aO).cycleType.card = 1
    rw [Equiv.Perm.cycleType_ofSubtype]
    exact haOcyc
  have hgsupp : g.support = O := by
    have hsupp : aO.support = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [← haOcyc.orderOf, haOord, hcardO]
    ext i
    change i ∈ (Equiv.Perm.ofSubtype aO).support ↔ i ∈ O
    rw [Equiv.Perm.mem_support_ofSubtype]
    constructor
    · rintro ⟨hi, -⟩
      exact hi
    · intro hi
      exact ⟨hi, (Finset.eq_univ_iff_forall.mp hsupp) ⟨i, hi⟩⟩
  have hgord : orderOf g = 5 := by
    rw [hgcyc.orderOf, hgsupp, hO]
  have hcommg : Commute g b := by
    have hg_mem : ∀ i (hi : i ∈ O), g i = a i := by
      intro i hi
      change (Equiv.Perm.ofSubtype aO) (↑(⟨i, hi⟩ : {i // i ∈ O})) = a i
      rw [Equiv.Perm.ofSubtype_apply_coe]
      rfl
    have hg_notmem : ∀ i (hi : i ∉ O), g i = i := by
      intro i hi
      change (Equiv.Perm.ofSubtype aO) i = i
      rw [Equiv.Perm.ofSubtype_apply_of_not_mem aO hi]
    ext i
    by_cases hi : i ∈ O
    · have hbi : b i ∈ O := (hbO i).1 hi
      rw [Perm.mul_apply, Perm.mul_apply, hg_mem i hi, hg_mem (b i) hbi]
      exact congrArg Fin.val
        (congrArg (fun f : Perm (Fin 10) => f i) hcomm.eq)
    · have hbi : b i ∉ O := fun h => hi ((hbO i).2 h)
      rw [Perm.mul_apply, Perm.mul_apply, hg_notmem i hi, hg_notmem (b i) hbi]
  have hcop : Nat.Coprime (orderOf b) (orderOf g) := by
    rw [hgord]
    exact (Nat.coprime_primes hbprime Nat.prime_five).2 hb5
  have hsupple :=
    CFSG.FiveTransitive.PermCentralizer.support_le_compl_of_isCycle_of_commute_of_coprime_order
      hgcyc hcommg.symm hcop
  intro i hi
  have hnot : i ∉ b.support := by
    intro hmem
    have := hsupple hmem
    rw [hgsupp] at this
    exact (Finset.mem_compl.1 this) hi
  exact Equiv.Perm.notMem_support.mp hnot

private theorem not_preserves_of_isCycle_support {B : Finset (Fin 10)} {c : Perm (Fin 10)}
    (hc : c.IsCycle) (hcard : c.support.card = 5) (hB : B.card = 5)
    (hSB : (c.support ∩ B).Nonempty) (hSBc : (c.support ∩ Bᶜ).Nonempty) :
    ¬ ((∀ i ∈ B, c i ∈ B) ∨ ∀ i ∈ B, c i ∉ B) := by
  classical
  rintro hpres
  have hO : 2 * B.card = Fintype.card (Fin 10) := by rw [hB]; norm_num
  have hcB : c ∈ CFSG.AGLEmbedding.KFactProofs.SmallIdent.blockStab B :=
    CFSG.AGLEmbedding.KFactProofs.SmallIdent.mem_blockStab_of_forall_mem_or_forall_not_mem hO hpres
  have hc5 : orderOf c = 5 := by rw [hc.orderOf, hcard]
  have hker : CFSG.AGLEmbedding.KFactProofs.SmallIdent.swapChar B 0 ⟨c, hcB⟩ = 1 := by
    set g := CFSG.AGLEmbedding.KFactProofs.SmallIdent.swapChar B 0 ⟨c, hcB⟩
    have h1 : orderOf g ∣ 5 := by
      have := orderOf_map_dvd (CFSG.AGLEmbedding.KFactProofs.SmallIdent.swapChar B 0)
        ⟨c, hcB⟩
      simpa [g, hc5] using this
    have h2 : orderOf g ∣ 2 := by
      have := orderOf_dvd_card (x := g)
      simpa using this
    have h3 : orderOf g = 1 := Nat.eq_one_of_dvd_coprimes (by norm_num) h1 h2
    exact orderOf_eq_one_iff.mp h3
  have hpresB : ∀ i, i ∈ B ↔ c i ∈ B :=
    (CFSG.AGLEmbedding.KFactProofs.SmallIdent.swapChar_eq_one_iff B 0 ⟨c, hcB⟩).1 hker
  obtain ⟨x, hx⟩ := hSB
  obtain ⟨hxsupp, hxB⟩ := Finset.mem_inter.1 hx
  obtain ⟨y, hy⟩ := hSBc
  obtain ⟨hysupp, hyBc⟩ := Finset.mem_inter.1 hy
  have hxmov : c x ≠ x := Equiv.Perm.mem_support.mp hxsupp
  have hymov : c y ≠ y := Equiv.Perm.mem_support.mp hysupp
  obtain ⟨n, hn⟩ := (hc.sameCycle hxmov hymov).exists_nat_pow_eq
  have hstable : ∀ n, (c ^ n) x ∈ B := by
    intro n
    induction n with
    | zero => simpa using hxB
    | succ n ih =>
      rw [pow_succ']
      exact (hpresB _).1 ih
  have hyB : y ∈ B := by
    have := hstable n
    rwa [hn] at this
  exact (Finset.mem_compl.1 hyBc) hyB

theorem eq_bot_of_normalized_by_alt_prod {B : Finset (Fin 10)} (hB : B.card = 5)
    {Q : Subgroup (alternatingGroup (Fin 10))} (hQ : Nat.Coprime (Nat.card Q) 5)
    (hQB : ∀ σ ∈ Q, (∀ i ∈ B, (σ : Equiv.Perm (Fin 10)) i ∈ B) ∨
      ∀ i ∈ B, (σ : Equiv.Perm (Fin 10)) i ∉ B)
    (hnorm : ∀ g : alternatingGroup (Fin 10), ((∀ i ∉ B, (g : Equiv.Perm (Fin 10)) i = i) ∨
      ∀ i ∈ B, (g : Equiv.Perm (Fin 10)) i = i) → ∀ σ ∈ Q, g * σ * g⁻¹ ∈ Q) : Q = ⊥ := by
  classical
  have hBc : Bᶜ.card = 5 := by
    rw [Finset.card_compl, Fintype.card_fin, hB]
  obtain ⟨a, ha_cyc, ha_supp, ha5, ha_moves, haA⟩ := exists_five_cycle_of_support hB
  obtain ⟨b, hb_cyc, hb_supp, hb5, hb_moves, hbA⟩ := exists_five_cycle_of_support hBc
  have ha_fix : ∀ i ∉ B, a i = i := by
    intro i hi
    rw [← Equiv.Perm.notMem_support, ha_supp]
    exact hi
  have hb_fix : ∀ i ∈ B, b i = i := by
    intro i hi
    rw [← Equiv.Perm.notMem_support, hb_supp]
    simpa using hi
  have hfix_inv : ∀ (g : alternatingGroup (Fin 10)) (i : Fin 10),
      (g : Perm (Fin 10)) i = i → ((g⁻¹ : alternatingGroup (Fin 10)) : Perm (Fin 10)) i = i :=
    fun g i hi => by rw [Subgroup.coe_inv, Equiv.Perm.inv_eq_iff_eq, hi]
  have hnormalizes : ∀ g : alternatingGroup (Fin 10),
      ((∀ i ∉ B, (g : Perm (Fin 10)) i = i) ∨ ∀ i ∈ B, (g : Perm (Fin 10)) i = i) →
      g ∈ Subgroup.normalizer (Q : Set (alternatingGroup (Fin 10))) := by
    intro g hg
    have hg' : (∀ i ∉ B, ((g⁻¹ : alternatingGroup (Fin 10)) : Perm (Fin 10)) i = i) ∨
        ∀ i ∈ B, ((g⁻¹ : alternatingGroup (Fin 10)) : Perm (Fin 10)) i = i :=
      hg.imp (fun h i hi => hfix_inv g i (h i hi)) (fun h i hi => hfix_inv g i (h i hi))
    refine Subgroup.mem_normalizer_iff.mpr fun σ => ⟨hnorm g hg σ, fun hσ => ?_⟩
    simpa [mul_assoc] using hnorm g⁻¹ hg' _ hσ
  have ha_norm := hnormalizes ⟨a, haA⟩ (Or.inl ha_fix)
  have hb_norm := hnormalizes ⟨b, hbA⟩ (Or.inr hb_fix)
  let U : Subgroup (Perm (Fin 10)) := Q.map (alternatingGroup (Fin 10)).subtype
  have hna : a ∈ Subgroup.normalizer (U : Set (Perm (Fin 10))) := by
    have hle := Subgroup.le_normalizer_map (H := Q)
      (f := (alternatingGroup (Fin 10)).subtype)
    exact hle ⟨⟨a, haA⟩, ha_norm, rfl⟩
  have hnb : b ∈ Subgroup.normalizer (U : Set (Perm (Fin 10))) := by
    have hle := Subgroup.le_normalizer_map (H := Q)
      (f := (alternatingGroup (Fin 10)).subtype)
    exact hle ⟨⟨b, hbA⟩, hb_norm, rfl⟩
  have hU : ¬ 5 ∣ Nat.card U := by
    rw [Subgroup.card_map_of_injective (K := Q)
      (alternatingGroup (Fin 10)).subtype_injective]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_five).mp (Nat.Coprime.symm hQ)
  have hbot : U = ⊥ :=
    CFSG.AGLEmbedding.KFactProofs.SmallIdent.eq_bot_of_normalized_by_cycles_coprime
      (Ω := Fin 10) (p := 5) (U := U) Nat.prime_five (by norm_num) hU
      ha5 hb5 hB hBc disjoint_compl_right ha_moves hb_moves hna hnb
  exact (Subgroup.map_eq_bot_iff_of_injective Q
    (alternatingGroup (Fin 10)).subtype_injective).1 hbot


theorem exists_five_commute_not_preserves {B : Finset (Fin 10)} (hB : B.card = 5)
    {x y : alternatingGroup (Fin 10)}
    (hx : (∀ i ∈ B, (x : Equiv.Perm (Fin 10)) i ∈ B) ∨ ∀ i ∈ B, (x : Equiv.Perm (Fin 10)) i ∉ B)
    (hy : (∀ i ∈ B, (y : Equiv.Perm (Fin 10)) i ∈ B) ∨ ∀ i ∈ B, (y : Equiv.Perm (Fin 10)) i ∉ B)
    (hx5 : x ^ 5 = 1) (hx1 : x ≠ 1) (hyr : (orderOf y).Prime) (hy2 : orderOf y ≠ 2)
    (hy5 : orderOf y ≠ 5) (hxy : x * y = y * x) :
    ∃ c : alternatingGroup (Fin 10), c ^ 5 = 1 ∧ c ≠ 1 ∧ c * y = y * c ∧
      ¬ ((∀ i ∈ B, (c : Equiv.Perm (Fin 10)) i ∈ B) ∨
        ∀ i ∈ B, (c : Equiv.Perm (Fin 10)) i ∉ B) := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let sx : Perm (Fin 10) := x
  let sy : Perm (Fin 10) := y
  have hx5' : sx ^ 5 = 1 := by
    have := congrArg (fun z : alternatingGroup (Fin 10) => (z : Perm (Fin 10))) hx5
    simpa [sx] using this
  have hx1' : sx ≠ 1 := by
    intro h
    apply hx1
    exact Subtype.ext (by simpa [sx] using h)
  have hxy' : Commute sx sy := by
    show sx * sy = sy * sx
    have := congrArg (fun z : alternatingGroup (Fin 10) => (z : Perm (Fin 10))) hxy
    simpa [sx, sy] using this
  have hyr' : (orderOf sy).Prime := by
    simpa [sy] using hyr
  have hy2' : orderOf sy ≠ 2 := by
    simpa [sy] using hy2
  have hy5' : orderOf sy ≠ 5 := by
    simpa [sy] using hy5
  have hO : 2 * B.card = Fintype.card (Fin 10) := by rw [hB]; norm_num
  have hxB : sx ∈ CFSG.AGLEmbedding.KFactProofs.SmallIdent.blockStab B :=
    CFSG.AGLEmbedding.KFactProofs.SmallIdent.mem_blockStab_of_forall_mem_or_forall_not_mem hO
      (by simpa [sx] using hx)
  have hyB : sy ∈ CFSG.AGLEmbedding.KFactProofs.SmallIdent.blockStab B :=
    CFSG.AGLEmbedding.KFactProofs.SmallIdent.mem_blockStab_of_forall_mem_or_forall_not_mem hO
      (by simpa [sy] using hy)
  have hxord : orderOf sx = 5 := orderOf_eq_prime hx5' hx1'
  have hxpresB : ∀ i, i ∈ B ↔ sx i ∈ B := by
    apply (CFSG.AGLEmbedding.KFactProofs.SmallIdent.swapChar_eq_one_iff B 0 ⟨sx, hxB⟩).1
    set g := CFSG.AGLEmbedding.KFactProofs.SmallIdent.swapChar B 0 ⟨sx, hxB⟩
    have h1 : orderOf g ∣ 5 := by
      have := orderOf_map_dvd (CFSG.AGLEmbedding.KFactProofs.SmallIdent.swapChar B 0)
        ⟨sx, hxB⟩
      simpa [g, hxord] using this
    have h2 : orderOf g ∣ 2 := by
      have := orderOf_dvd_card (x := g)
      simpa using this
    have h3 : orderOf g = 1 := Nat.eq_one_of_dvd_coprimes (by norm_num) h1 h2
    exact orderOf_eq_one_iff.mp h3
  have hypresB : ∀ i, i ∈ B ↔ sy i ∈ B := by
    apply (CFSG.AGLEmbedding.KFactProofs.SmallIdent.swapChar_eq_one_iff B 0 ⟨sy, hyB⟩).1
    set g := CFSG.AGLEmbedding.KFactProofs.SmallIdent.swapChar B 0 ⟨sy, hyB⟩
    have hodd : Odd (orderOf sy) := hyr'.odd_of_ne_two hy2'
    have h1 : orderOf g ∣ orderOf sy := by
      have := orderOf_map_dvd (CFSG.AGLEmbedding.KFactProofs.SmallIdent.swapChar B 0)
        ⟨sy, hyB⟩
      simpa [g, Subgroup.orderOf_coe] using this
    have h2 : orderOf g ∣ 2 := by
      have := orderOf_dvd_card (x := g)
      simpa using this
    have h3 : orderOf g = 1 :=
      Nat.eq_one_of_dvd_coprimes (Odd.coprime_two_right hodd) h1 h2
    exact orderOf_eq_one_iff.mp h3
  obtain ⟨O, hOcard, hpresOx, hpresOy, hact, hOB⟩ : ∃ O : Finset (Fin 10), O.card = 5 ∧
      (∀ i, i ∈ O ↔ sx i ∈ O) ∧ (∀ i, i ∈ O ↔ sy i ∈ O) ∧
      (∃ i ∈ O, sx i ≠ i) ∧ (O = B ∨ O = Bᶜ) := by
    by_cases hfixB : ∀ i ∈ B, sx i = i
    · have hBc : Bᶜ.card = 5 := by
        rw [Finset.card_compl, Fintype.card_fin, hB]
      have hpresOx : ∀ i, i ∈ Bᶜ ↔ sx i ∈ Bᶜ := by
        intro i
        simpa [Finset.mem_compl] using not_congr (hxpresB i)
      have hpresOy : ∀ i, i ∈ Bᶜ ↔ sy i ∈ Bᶜ := by
        intro i
        simpa [Finset.mem_compl] using not_congr (hypresB i)
      have hact : ∃ i ∈ Bᶜ, sx i ≠ i := by
        by_contra h
        push Not at h
        apply hx1'
        ext i
        by_cases hi : i ∈ B
        · exact congrArg Fin.val (hfixB i hi)
        · exact congrArg Fin.val (h i (Finset.mem_compl.2 hi))
      exact ⟨Bᶜ, hBc, hpresOx, hpresOy, hact, Or.inr rfl⟩
    · push Not at hfixB
      exact ⟨B, hB, hxpresB, hypresB, hfixB, Or.inl rfl⟩
  have hfixO : ∀ i ∈ O, sy i = i :=
    fixes_of_commute_of_five_set hOcard hpresOx hpresOy hx5' hact hxy' hyr' hy5'
  have hpresOc : ∀ i, i ∉ O ↔ sy i ∉ O := by
    intro i
    simpa [Finset.mem_compl] using not_congr (hpresOy i)
  let syC : Perm {i : Fin 10 // i ∉ O} := sy.subtypePerm (fun i => (hpresOc i).symm)
  have hcardOc : Fintype.card {i : Fin 10 // i ∉ O} = 5 := by
    rw [Fintype.card_subtype_compl (fun i : Fin 10 => i ∈ O), Fintype.card_fin,
      Fintype.card_coe, hOcard]
  have hsyCpow : syC ^ orderOf sy = 1 := by
    dsimp only [syC]
    rw [Equiv.Perm.subtypePerm_pow]
    simp [pow_orderOf_eq_one]
    ext x
    rfl
  have hnotdvd : ¬ orderOf sy ∣ Fintype.card {i : Fin 10 // i ∉ O} := by
    rw [hcardOc]
    exact fun h => hy5' ((Nat.prime_dvd_prime_iff_eq hyr' Nat.prime_five).1 h)
  haveI : Fact (Nat.Prime (orderOf sy)) := ⟨hyr'⟩
  obtain ⟨w', hw'⟩ := Equiv.Perm.exists_fixed_point_of_prime
    (p := orderOf sy) (n := 1) hnotdvd (by simpa using hsyCpow)
  let w : Fin 10 := w'.1
  have hwO : w ∉ O := w'.2
  have hwfix : sy w = w := by
    have := congrArg Subtype.val hw'
    simpa [syC, w] using this
  let e : O ≃ Fin 5 := Finset.equivFinOfCardEq hOcard
  let o : Fin 5 → Fin 10 := fun i => (e.symm i).1
  have ho_mem : ∀ i, o i ∈ O := fun i => (e.symm i).2
  have ho_inj : Function.Injective o := by
    intro i j h
    exact e.symm.injective (Subtype.ext h)
  have ho_ne : ∀ {i j : Fin 5}, i ≠ j → o i ≠ o j := fun hij h => hij (ho_inj h)
  let T : Finset (Fin 10) := {o 0, o 1, o 2, o 3}
  let S : Finset (Fin 10) := insert w T
  have hTcard : T.card = 4 := by
    change ({o 0, o 1, o 2, o 3} : Finset (Fin 10)).card = 4
    rw [Finset.card_eq_four]
    exact ⟨o 0, o 1, o 2, o 3,
      ho_ne (by decide), ho_ne (by decide), ho_ne (by decide),
      ho_ne (by decide), ho_ne (by decide), ho_ne (by decide), rfl⟩
  have hTsub : T ⊆ O := by
    intro i hi
    change i ∈ ({o 0, o 1, o 2, o 3} : Finset (Fin 10)) at hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> exact ho_mem _
  have hwT : w ∉ T := fun hw => hwO (hTsub hw)
  have hS_card : S.card = 5 := by
    change (insert w T).card = 5
    rw [Finset.card_insert_of_notMem hwT, hTcard]
  obtain ⟨c, hc_cyc, hc_supp, hc5, hc_moves, hcA⟩ := exists_five_cycle_of_support hS_card
  have hyS : ∀ x ∈ S, sy x = x := by
    intro x hx
    change x ∈ insert w T at hx
    rcases Finset.mem_insert.1 hx with rfl | hxT
    · exact hwfix
    · exact hfixO x (hTsub hxT)
  have hdisj : Equiv.Perm.Disjoint c sy := by
    intro x
    by_cases hx : x ∈ c.support
    · right
      rw [hc_supp] at hx
      exact hyS x hx
    · left
      exact Equiv.Perm.notMem_support.mp hx
  have hcomm_c : Commute c sy := hdisj.commute
  have hcomm_A : (⟨c, hcA⟩ : alternatingGroup (Fin 10)) * y = y * ⟨c, hcA⟩ := by
    apply Subtype.ext
    simpa [sy] using hcomm_c.eq
  have hc5A : (⟨c, hcA⟩ : alternatingGroup (Fin 10)) ^ 5 = 1 := by
    apply Subtype.ext
    simpa using hc5
  have hc1A : (⟨c, hcA⟩ : alternatingGroup (Fin 10)) ≠ 1 := by
    intro h
    apply hc_cyc.ne_one
    simpa using congrArg Subtype.val h
  have hcard_c : c.support.card = 5 := by rw [hc_supp, hS_card]
  have ho0S : o 0 ∈ S := by
    change o 0 ∈ insert w T
    exact Finset.mem_insert_of_mem (by
      change o 0 ∈ ({o 0, o 1, o 2, o 3} : Finset (Fin 10))
      simp)
  have hwS : w ∈ S := by
    change w ∈ insert w T
    exact Finset.mem_insert_self _ _
  have hSB : (c.support ∩ B).Nonempty := by
    rcases hOB with rfl | rfl
    · exact ⟨o 0, by rw [hc_supp]; exact Finset.mem_inter.2 ⟨ho0S, ho_mem 0⟩⟩
    · exact ⟨w, by rw [hc_supp]; exact Finset.mem_inter.2 ⟨hwS, by simpa using hwO⟩⟩
  have hSBc : (c.support ∩ Bᶜ).Nonempty := by
    rcases hOB with rfl | rfl
    · exact ⟨w, by rw [hc_supp]; exact Finset.mem_inter.2 ⟨hwS, Finset.mem_compl.2 hwO⟩⟩
    · exact ⟨o 0, by rw [hc_supp]; exact Finset.mem_inter.2 ⟨ho0S, ho_mem 0⟩⟩
  have hnotpres := not_preserves_of_isCycle_support hc_cyc hcard_c hB hSB hSBc
  exact ⟨⟨c, hcA⟩, hc5A, hc1A, hcomm_A, hnotpres⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.AltTen
