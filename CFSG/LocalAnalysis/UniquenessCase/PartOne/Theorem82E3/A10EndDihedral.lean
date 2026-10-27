module

public import CFSG.LocalAnalysis.EvenBN.Tits.Prelim.FixedCount
public import CFSG.GroupTheory.CentralizerSup
public import CFSG.GroupTheory.ConjQuot
public import CFSG.GroupTheory.CoprimeCosetFixed
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3AInsNoInv
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.pStability
public import Mathlib.Data.Int.Star
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10Gen

open Subgroup

variable {G : Type} [Group G] [Finite G]

private lemma finset_card_sdiff_eq [DecidableEq G] (C D : Finset G) :
    (D \ C).card = D.card - (C ∩ D).card :=
  Finset.card_sdiff

private lemma finset_card_sdiff_ge [DecidableEq G] {C D : Finset G} (h : 2 * C.card ≤ D.card) :
    C.card ≤ (D \ C).card := by
  rw [finset_card_sdiff_eq]
  have hInter : (C ∩ D).card ≤ C.card :=
    Finset.card_le_card Finset.inter_subset_left
  omega

private lemma finset_biUnion_sdiff_subset [DecidableEq G] {Q C : Finset G} {D : Fin 7 → Finset G}
    (hDQ : ∀ k, D k ⊆ Q) :
    Finset.univ.biUnion (fun k => D k \ C) ⊆ Q \ C := by
  intro x hx
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_sdiff] at hx ⊢
  obtain ⟨k, hk⟩ := hx
  exact ⟨hDQ k hk.1, hk.2⟩

private lemma finset_card_sdiff_eq_seven [DecidableEq G] {Q C : Finset G}
    (hCQ : C ⊆ Q) (hcardQ : Q.card = 8 * C.card) :
    (Q \ C).card = 7 * C.card := by
  rw [finset_card_sdiff_eq]
  have hInter : (C ∩ Q).card = C.card := by
    rw [Finset.inter_eq_left.mpr hCQ]
  rw [hInter, hcardQ]
  omega

private lemma finset_seven_cover_eq [DecidableEq G] {Q C : Finset G} {D : Fin 7 → Finset G}
    (hS : (Q \ C).card = 7 * C.card)
    (hlower : ∀ k, C.card ≤ (D k \ C).card)
    (hdisj : (↑(Finset.univ : Finset (Fin 7)) : Set (Fin 7)).PairwiseDisjoint
      (fun k => D k \ C))
    (hsub : Finset.univ.biUnion (fun k => D k \ C) ⊆ Q \ C) :
    (∀ k, (D k \ C).card = C.card) ∧
      Finset.univ.biUnion (fun k => D k \ C) = Q \ C := by
  have hsum : ∑ k : Fin 7, (D k \ C).card =
      (Finset.univ.biUnion (fun k => D k \ C)).card := by
    rw [Finset.card_biUnion hdisj]
  have hsum_ge : 7 * C.card ≤ ∑ k : Fin 7, (D k \ C).card := by
    calc 7 * C.card = ∑ _k : Fin 7, C.card := by simp
      _ ≤ ∑ k : Fin 7, (D k \ C).card := Finset.sum_le_sum (fun k _ => hlower k)
  have hupper : (Finset.univ.biUnion (fun k => D k \ C)).card ≤ 7 * C.card := by
    rw [← hS]
    exact Finset.card_le_card hsub
  have hsum_eq : ∑ k : Fin 7, (D k \ C).card = 7 * C.card := by
    rw [hsum]
    exact le_antisymm hupper (by rw [hsum] at hsum_ge; exact hsum_ge)
  have hEq : ∀ k, (D k \ C).card = C.card := by
    intro k
    by_contra hk
    have hlt : C.card < (D k \ C).card :=
      lt_of_le_of_ne (hlower k) (fun h => hk h.symm)
    have hstrict : (∑ _i : Fin 7, C.card) < ∑ i : Fin 7, (D i \ C).card :=
      Finset.sum_lt_sum (fun i _ => hlower i) ⟨k, Finset.mem_univ k, hlt⟩
    rw [hsum_eq] at hstrict
    simp at hstrict
  refine ⟨hEq, ?_⟩
  have hcardEq : (Finset.univ.biUnion (fun k => D k \ C)).card = (Q \ C).card := by
    rw [← hsum, show ∑ k : Fin 7, (D k \ C).card = 7 * C.card by simp [hEq], hS]
  exact Finset.eq_of_subset_of_card_le hsub (le_of_eq hcardEq.symm)

private lemma finset_seven_cover_card_and_subset [DecidableEq G] {Q C : Finset G}
    {D : Fin 7 → Finset G}
    (hCQ : C ⊆ Q) (hDlarge : ∀ k, 2 * C.card ≤ (D k).card)
    (hTcard : ∀ k, (D k \ C).card = C.card) :
    (∀ k, (D k).card = 2 * C.card) ∧ (∀ k, C ⊆ D k) := by
  have hInter_le : ∀ k, (C ∩ D k).card ≤ C.card := fun k =>
    Finset.card_le_card Finset.inter_subset_left
  have hDcard : ∀ k, (D k).card = 2 * C.card := by
    intro k
    have hT := hTcard k
    rw [finset_card_sdiff_eq] at hT
    have hle := hInter_le k
    have hlarge := hDlarge k
    omega
  refine ⟨hDcard, fun k => ?_⟩
  have hT := hTcard k
  rw [finset_card_sdiff_eq] at hT
  have hInter : (C ∩ D k).card = C.card := by
    have h := hDcard k
    have hle := hInter_le k
    omega
  have heq : C ∩ D k = C :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_left (le_of_eq hInter.symm)
  rw [← heq]
  exact Finset.inter_subset_right

private lemma finset_pairwiseDisjoint_sdiff_of_subgroup [DecidableEq G]
    {C : Subgroup G} {D : Fin 7 → Subgroup G} {Cf : Finset G} {Df : Fin 7 → Finset G}
    (hCf : ∀ x, x ∈ Cf ↔ x ∈ C) (hDf : ∀ k x, x ∈ Df k ↔ x ∈ D k)
    (hdisj : ∀ i j : Fin 7, i ≠ j → D i ⊓ D j ≤ C) :
    (↑(Finset.univ : Finset (Fin 7)) : Set (Fin 7)).PairwiseDisjoint
      (fun k => Df k \ Cf) := by
  intro i _ j _ hij
  change Disjoint (Df i \ Cf) (Df j \ Cf)
  rw [Finset.disjoint_left]
  intro x hxi hxj
  simp only [Finset.mem_sdiff] at hxi hxj
  have hxC : x ∈ C := hdisj i j hij ⟨(hDf i x).mp hxi.1, (hDf j x).mp hxj.1⟩
  exact hxi.2 ((hCf x).mpr hxC)

private theorem finset_seven_cover_to_subgroup [DecidableEq G]
    {Q C : Subgroup G} {D : Fin 7 → Subgroup G} {Cf Qf : Finset G} {Df : Fin 7 → Finset G}
    (hCQ : C ≤ Q) (hCfcard : Cf.card = Nat.card C)
    (hDfcard : ∀ k, (Df k).card = Nat.card (D k))
    (hCf : ∀ x, x ∈ Cf ↔ x ∈ C) (hQf : ∀ x, x ∈ Qf ↔ x ∈ Q)
    (hDf : ∀ k x, x ∈ Df k ↔ x ∈ D k)
    (hDlargeF : ∀ k, 2 * Cf.card ≤ (Df k).card)
    (hTcard : ∀ k, (Df k \ Cf).card = Cf.card)
    (hUnion : Finset.univ.biUnion (fun k => Df k \ Cf) = Qf \ Cf) :
    (∀ k, Nat.card (D k) = 2 * Nat.card C) ∧
      (∀ k, C ≤ D k) ∧
      (∀ q ∈ Q, q ∈ C ∨ ∃ k, q ∈ D k) := by
  have hCsubQf : Cf ⊆ Qf := by
    intro x hx
    exact (hQf x).mpr (hCQ ((hCf x).mp hx))
  obtain ⟨hDcardF, hCDf⟩ := finset_seven_cover_card_and_subset hCsubQf hDlargeF hTcard
  refine ⟨?_, ?_, ?_⟩
  · intro k
    rw [← hDfcard k, ← hCfcard]
    exact hDcardF k
  · intro k c hc
    exact (hDf k c).mp (hCDf k ((hCf c).mpr hc))
  · intro q hq
    by_cases hqC : q ∈ C
    · exact Or.inl hqC
    · right
      have hqS : q ∈ Qf \ Cf := by
        rw [Finset.mem_sdiff]
        exact ⟨(hQf q).mpr hq, fun h => hqC ((hCf q).mp h)⟩
      have hunion : q ∈ Finset.univ.biUnion (fun k => Df k \ Cf) := by
        rw [hUnion]; exact hqS
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at hunion
      obtain ⟨k, hk⟩ := hunion
      exact ⟨k, (hDf k q).mp (Finset.mem_sdiff.mp hk).1⟩

theorem card_eq_two_mul_of_seven_cover {Q C : Subgroup G} {D : Fin 7 → Subgroup G}
    (hCQ : C ≤ Q) (hDQ : ∀ k, D k ≤ Q)
    (hcardQ : Nat.card Q = 8 * Nat.card C)
    (hDlarge : ∀ k, 2 * Nat.card C ≤ Nat.card (D k))
    (hdisj : ∀ i j : Fin 7, i ≠ j → D i ⊓ D j ≤ C) :
    (∀ k, Nat.card (D k) = 2 * Nat.card C) ∧
      (∀ k, C ≤ D k) ∧
      (∀ q ∈ Q, q ∈ C ∨ ∃ k, q ∈ D k) := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  let Cf : Finset G := (C : Set G).toFinset
  let Qf : Finset G := (Q : Set G).toFinset
  let Df : Fin 7 → Finset G := fun k => (D k : Set G).toFinset
  have hCfcard : Cf.card = Nat.card C := by
    simp [Cf, Set.toFinset_card, Nat.card_coe_set_eq]
  have hQfcard : Qf.card = Nat.card Q := by
    simp [Qf, Set.toFinset_card, Nat.card_coe_set_eq]
  have hDfcard : ∀ k, (Df k).card = Nat.card (D k) := by
    intro k
    simp [Df, Set.toFinset_card, Nat.card_coe_set_eq]
  have hCsubQ : Cf ⊆ Qf := by
    intro x hx
    simp only [Cf, Qf, Set.mem_toFinset] at hx ⊢
    exact hCQ hx
  have hcardQf : Qf.card = 8 * Cf.card := by
    rw [hQfcard, hCfcard, hcardQ]
  have hS : (Qf \ Cf).card = 7 * Cf.card :=
    finset_card_sdiff_eq_seven hCsubQ hcardQf
  have hDlargeF : ∀ k : Fin 7, 2 * Cf.card ≤ (Df k).card := by
    intro k
    rw [hDfcard k, hCfcard]
    exact hDlarge k
  have hlower : ∀ k : Fin 7, Cf.card ≤ (Df k \ Cf).card := fun k =>
    finset_card_sdiff_ge (hDlargeF k)
  have hCfmem : ∀ x, x ∈ Cf ↔ x ∈ C := by
    intro x; simp [Cf]
  have hQfmem : ∀ x, x ∈ Qf ↔ x ∈ Q := by
    intro x; simp [Qf]
  have hDfmem : ∀ k x, x ∈ Df k ↔ x ∈ D k := by
    intro k x; simp [Df]
  have hdisjF : (↑(Finset.univ : Finset (Fin 7)) : Set (Fin 7)).PairwiseDisjoint
      (fun k => Df k \ Cf) :=
    finset_pairwiseDisjoint_sdiff_of_subgroup hCfmem hDfmem hdisj
  have hsub : Finset.univ.biUnion (fun k => Df k \ Cf) ⊆ Qf \ Cf :=
    finset_biUnion_sdiff_subset (fun k => by
      intro x hx
      simpa [Qf, Df] using hDQ k (by simpa [Df] using hx))
  obtain ⟨hTcard, hUnion⟩ := finset_seven_cover_eq hS hlower hdisjF hsub
  exact finset_seven_cover_to_subgroup hCQ hCfcard hDfcard hCfmem hQfmem hDfmem
    hDlargeF hTcard hUnion

private lemma conj_involution_mul {y w : G} (hw : w ^ 2 = 1) (hwy : w * y * w⁻¹ = y⁻¹)
    {a b : ℕ} (hab : a ≤ b) :
    (y ^ b * w * (y ^ b)⁻¹) * (y ^ a * w * (y ^ a)⁻¹) = y ^ (2 * (b - a)) := by
  have hw2 : w * w = 1 := by simpa [pow_two] using hw
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
  have hconj : ∀ n : ℕ, w * y ^ n * w⁻¹ = (y ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        calc w * y ^ (n + 1) * w⁻¹ = (w * y ^ n * w⁻¹) * (w * y * w⁻¹) := by group
          _ = (y ^ n)⁻¹ * y⁻¹ := by rw [ih, hwy]
          _ = (y ^ (n + 1))⁻¹ := by group
  have hinner' : w * ((y ^ (b - a))⁻¹) * w = y ^ (b - a) := by
    have hcalc : w * ((y ^ (b - a))⁻¹) * w⁻¹ = y ^ (b - a) := by
      calc w * ((y ^ (b - a))⁻¹) * w⁻¹ = (w * y ^ (b - a) * w⁻¹)⁻¹ := by group
        _ = ((y ^ (b - a))⁻¹)⁻¹ := by rw [hconj]
        _ = y ^ (b - a) := by rw [inv_inv]
    rwa [hwinv] at hcalc
  calc (y ^ b * w * (y ^ b)⁻¹) * (y ^ a * w * (y ^ a)⁻¹)
      = y ^ b * (w * ((y ^ b)⁻¹ * y ^ a) * w) * (y ^ a)⁻¹ := by group
    _ = y ^ b * (w * ((y ^ (b - a))⁻¹) * w) * (y ^ a)⁻¹ := by
          have hinv : (y ^ b)⁻¹ * y ^ a = (y ^ (b - a))⁻¹ := by
            rw [pow_sub y hab]
            group
          rw [hinv]
    _ = y ^ b * y ^ (b - a) * (y ^ a)⁻¹ := by rw [hinner']
    _ = y ^ (2 * (b - a)) := by
          rw [← pow_add, ← pow_sub _ (by omega : a ≤ b + (b - a))]
          congr 1
          omega

private lemma gcd_two_mul_seven {d : ℕ} (h1 : 1 ≤ d) (h6 : d ≤ 6) :
    Nat.gcd (2 * d) 7 = 1 := by
  interval_cases d <;> norm_num

private lemma index_eq_one_or_seven_eight {p r : ℕ} (hpprime : p.Prime) (hp : 7 ≤ p)
    (hdvd : p ∣ r - 1) (hpow : ∃ k ≤ 4, r = 2 ^ k) :
    r = 1 ∨ (p = 7 ∧ r = 8) := by
  obtain ⟨k, hk4, hk⟩ := hpow
  interval_cases k
  · left; simpa using hk
  · exfalso
    rw [hk] at hdvd
    norm_num at hdvd
    exact hpprime.ne_one hdvd
  · exfalso
    rw [hk] at hdvd
    have hdvd3 : p ∣ 3 := by simpa using hdvd
    have : p ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd3
    omega
  · right
    refine ⟨?_, hk⟩
    rw [hk] at hdvd
    have hdvd7 : p ∣ 7 := by simpa using hdvd
    have hp7le : p ≤ 7 := Nat.le_of_dvd (by norm_num) hdvd7
    omega
  · exfalso
    rw [hk] at hdvd
    have hdvd15 : p ∣ 15 := by simpa using hdvd
    have hp35 : p = 3 ∨ p = 5 := by
      have h' : p ∣ 3 * 5 := by simpa using hdvd15
      rcases (Nat.Prime.dvd_mul hpprime).mp h' with h3 | h5
      · rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp h3 with h1 | h3'
        · omega
        · exact Or.inl h3'
      · rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp h5 with h1 | h5'
        · omega
        · exact Or.inr h5'
    omega

private lemma involution_mul_conj_eq_inv_mul_inv {y w : G} (hw : w ^ 2 = 1)
    (hwy : w * y * w⁻¹ = y⁻¹) : w * (y * w * y⁻¹) = y⁻¹ * y⁻¹ := by
  have hw2 : w * w = 1 := by simpa [pow_two] using hw
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
  have hwy' : w * y = y⁻¹ * w := by
    calc w * y = (w * y * w) * w := by rw [mul_assoc, hw2, mul_one]
      _ = (w * y * w⁻¹) * w := by rw [hwinv]
      _ = y⁻¹ * w := by rw [hwy]
  calc w * (y * w * y⁻¹) = (w * y) * w * y⁻¹ := by group
    _ = (y⁻¹ * w) * w * y⁻¹ := by rw [hwy']
    _ = y⁻¹ * (w * w) * y⁻¹ := by group
    _ = y⁻¹ * y⁻¹ := by rw [hw2]; group

private lemma commute_inv_sq_to_sq {x y : G} (h : Commute x (y⁻¹ * y⁻¹)) :
    Commute x (y ^ 2) := by
  have h3 : y⁻¹ * y⁻¹ = (y ^ 2)⁻¹ := by group
  rw [h3] at h
  simpa using h.inv_right

private lemma commute_of_commute_sq {x y : G} {p : ℕ} (hy : orderOf y = p) (hpodd : Odd p)
    (h : Commute x (y ^ 2)) : Commute x y := by
  have hy_mem_sq : y ∈ Subgroup.zpowers (y ^ 2) := by
    rw [mem_zpowers_pow_iff, hy]
    exact Nat.coprime_two_left.mpr hpodd
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hy_mem_sq
  have := h.zpow_right m
  rwa [hm] at this

private theorem relIndex_inf_centralizer_conj_le_four {Q : Subgroup G} {a w : G}
    (haQ : a ∈ Subgroup.normalizer (Q : Set G))
    (hidx : (Subgroup.centralizer ({w} : Set G)).relIndex Q ≤ 4) :
    (Q ⊓ Subgroup.centralizer ({a * w * a⁻¹} : Set G)).relIndex Q ≤ 4 := by
  let D : Subgroup G := Q ⊓ Subgroup.centralizer ({w} : Set G)
  let D' : Subgroup G := Q ⊓ Subgroup.centralizer ({a * w * a⁻¹} : Set G)
  have hDrel : D.relIndex Q ≤ 4 := by
    simpa [D, Subgroup.relIndex, inf_comm] using hidx
  have hcentralizer_conj : (Subgroup.centralizer ({w} : Set G)).map
      (MulAut.conj a).toMonoidHom = Subgroup.centralizer ({a * w * a⁻¹} : Set G) := by
    have hmap := CFSG.Glauberman.map_centralizer_eq_of_equiv (e := MulAut.conj a)
      (P := Subgroup.zpowers w)
    rw [CFSG.centralizer_zpowers_eq_centralizer_singleton w,
      MonoidHom.map_zpowers] at hmap
    rw [CFSG.centralizer_zpowers_eq_centralizer_singleton
      ((MulAut.conj a).toMonoidHom w)] at hmap
    simpa [MulAut.conj_apply] using hmap
  have hQmap : Q.map (MulAut.conj a).toMonoidHom = Q :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp haQ
  have hDmap : D' = D.map (MulAut.conj a).toMonoidHom := by
    calc D' = Q ⊓ Subgroup.centralizer ({a * w * a⁻¹} : Set G) := rfl
      _ = Q.map (MulAut.conj a).toMonoidHom ⊓
          (Subgroup.centralizer ({w} : Set G)).map (MulAut.conj a).toMonoidHom := by
            rw [hQmap, hcentralizer_conj]
      _ = (Q ⊓ Subgroup.centralizer ({w} : Set G)).map (MulAut.conj a).toMonoidHom :=
            (Subgroup.map_inf Q _ (MulAut.conj a).toMonoidHom
              (MulAut.conj a).injective).symm
      _ = D.map (MulAut.conj a).toMonoidHom := rfl
  have h := Subgroup.relIndex_map_map_of_injective D Q (MulAut.conj a).injective
    (f := (MulAut.conj a).toMonoidHom)
  rw [← hDmap, hQmap] at h
  rw [h]
  exact hDrel

private theorem inf_centralizer_inf_conj_le {p : ℕ} [Fact p.Prime] (hp : 7 ≤ p)
    {Q : Subgroup G} {y w : G} (hy : orderOf y = p) (hw : w ^ 2 = 1)
    (hwy : w * y * w⁻¹ = y⁻¹) :
    (Q ⊓ Subgroup.centralizer ({w} : Set G)) ⊓
        (Q ⊓ Subgroup.centralizer ({y * w * y⁻¹} : Set G)) ≤
      Q ⊓ Subgroup.centralizer ({y} : Set G) := by
  intro x hx
  have hxD : x ∈ Q ⊓ Subgroup.centralizer ({w} : Set G) := (Subgroup.mem_inf.mp hx).1
  have hxD' : x ∈ Q ⊓ Subgroup.centralizer ({y * w * y⁻¹} : Set G) :=
    (Subgroup.mem_inf.mp hx).2
  have hxQ : x ∈ Q := (Subgroup.mem_inf.mp hxD).1
  have hxw : Commute x w := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hxD).2
  have hxw' : Commute x (y * w * y⁻¹) :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hxD').2
  have hxww' : Commute x (w * (y * w * y⁻¹)) := hxw.mul_right hxw'
  rw [involution_mul_conj_eq_inv_mul_inv hw hwy] at hxww'
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hxy : x * y = y * x :=
    (commute_of_commute_sq hy hpodd (commute_inv_sq_to_sq hxww')).eq
  exact ⟨hxQ, Subgroup.mem_centralizer_singleton_iff.mpr hxy⟩

private theorem relIndex_inf_centralizer_le_sixteen {p : ℕ} [Fact p.Prime] (hp : 7 ≤ p)
    {Q : Subgroup G} {y w : G} (hyQ : y ∈ Subgroup.normalizer (Q : Set G))
    (hy : orderOf y = p) (hw : w ^ 2 = 1) (hwy : w * y * w⁻¹ = y⁻¹)
    (hidx : (Subgroup.centralizer ({w} : Set G)).relIndex Q ≤ 4) :
    (Q ⊓ Subgroup.centralizer ({y} : Set G)).relIndex Q ≤ 16 := by
  let C : Subgroup G := Q ⊓ Subgroup.centralizer ({y} : Set G)
  let D : Subgroup G := Q ⊓ Subgroup.centralizer ({w} : Set G)
  let D' : Subgroup G := Q ⊓ Subgroup.centralizer ({y * w * y⁻¹} : Set G)
  have hDrel : D.relIndex Q ≤ 4 := by
    simpa [D, Subgroup.relIndex, inf_comm] using hidx
  have hD'rel : D'.relIndex Q ≤ 4 := by
    simpa [D'] using relIndex_inf_centralizer_conj_le_four (Q := Q) (a := y) (w := w) hyQ hidx
  have hDinfC : D ⊓ D' ≤ C := by
    simpa [D, D', C] using inf_centralizer_inf_conj_le hp hy hw hwy
  have hDinfrel : (D ⊓ D').relIndex Q ≠ 0 := by
    intro h0
    have hmul := Subgroup.relIndex_mul_card (D ⊓ D') Q
    rw [h0, zero_mul] at hmul
    exact (Nat.card_pos (α := Q)).ne' hmul.symm
  have h1 : C.relIndex Q ≤ (D ⊓ D').relIndex Q :=
    Subgroup.relIndex_le_of_le_left hDinfC hDinfrel
  have h2 : (D ⊓ D').relIndex Q ≤ D.relIndex Q * D'.relIndex Q :=
    Subgroup.relIndex_inf_le
  nlinarith

private theorem card_modEq_inf_centralizer {p : ℕ} [Fact p.Prime] {Q : Subgroup G} {y : G}
    (hyQ : y ∈ Subgroup.normalizer (Q : Set G)) (hy : orderOf y = p) :
    Nat.card Q ≡ Nat.card ↥(Q ⊓ Subgroup.centralizer ({y} : Set G)) [MOD p] := by
  have hP : IsPGroup p (Subgroup.zpowers y) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hy, pow_one]
  have hle : Subgroup.zpowers y ≤ Subgroup.normalizer (Q : Set G) :=
    Subgroup.zpowers_le.mpr hyQ
  have hPA : ∀ x ∈ Subgroup.zpowers y, ∀ a ∈ Q, x * a * x⁻¹ ∈ Q := by
    intro x hx a ha
    exact (Subgroup.mem_normalizer_iff.mp (hle hx) a).mp ha
  have h := CFSG.LocalAnalysis.EvenBN.Tits.card_modEq_card_inf_centralizer hP hPA
  rwa [CFSG.centralizer_zpowers_eq_centralizer_singleton y] at h

private theorem index_dvd_sub_one {p : ℕ} [Fact p.Prime] (hp : 7 ≤ p) {Q C : Subgroup G}
    (hCQ : C ≤ Q) (hQ : IsPGroup 2 Q)
    (hmod : Nat.card Q ≡ Nat.card C [MOD p]) :
    p ∣ C.relIndex Q - 1 := by
  have hmulC : C.relIndex Q * Nat.card C = Nat.card Q := by
    simpa [inf_eq_left.mpr hCQ] using Subgroup.relIndex_mul_card C Q
  have hrelpos : 0 < C.relIndex Q := by
    rcases Nat.eq_zero_or_pos (C.relIndex Q) with h0 | hpos
    · exfalso
      rw [h0, zero_mul] at hmulC
      exact (Nat.card_pos (α := Q)).ne' hmulC.symm
    · exact hpos
  have hpdvdQ : ¬ p ∣ Nat.card Q := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := ↥Q)).mp hQ
    intro hpdvd
    rw [hn] at hpdvd
    have hp2 : p ∣ 2 := (Fact.out : p.Prime).dvd_of_dvd_pow hpdvd
    have hple : p ≤ 2 := Nat.le_of_dvd (by norm_num) hp2
    omega
  have hpndvdC : ¬ p ∣ Nat.card C := fun h =>
    hpdvdQ (h.trans (Subgroup.card_dvd_of_le hCQ))
  have hcop : Nat.Coprime p (Nat.card C) :=
    (Fact.out : p.Prime).coprime_iff_not_dvd.mpr hpndvdC
  have hle : Nat.card C ≤ C.relIndex Q * Nat.card C := by
    calc Nat.card C = 1 * Nat.card C := by rw [one_mul]
      _ ≤ C.relIndex Q * Nat.card C := Nat.mul_le_mul_right _ hrelpos
  have hdvd' : p ∣ C.relIndex Q * Nat.card C - Nat.card C :=
    (Nat.modEq_iff_dvd' hle).mp (by rw [hmulC]; exact hmod.symm)
  have hsub : C.relIndex Q * Nat.card C - Nat.card C =
      (C.relIndex Q - 1) * Nat.card C := by
    rw [Nat.sub_mul, one_mul]
  exact hcop.dvd_of_dvd_mul_right (by rwa [hsub] at hdvd')

private theorem exists_pow_two_index {Q C : Subgroup G} (hQ : IsPGroup 2 Q)
    (hindex_le : C.relIndex Q ≤ 16) :
    ∃ k ≤ 4, C.relIndex Q = 2 ^ k := by
  obtain ⟨k, hk⟩ := hQ.index (C.subgroupOf Q)
  refine ⟨k, ?_, hk⟩
  have hk16 : 2 ^ k ≤ 16 := by
    rw [← hk]
    exact hindex_le
  by_contra hk5
  have h5 : 5 ≤ k := by omega
  have := Nat.pow_le_pow_right (by norm_num : 0 < 2) h5
  omega

private theorem seven_cover_card_large {Q C : Subgroup G} {y w : G}
    (hyQ : y ∈ Subgroup.normalizer (Q : Set G))
    (hcardQ : Nat.card Q = 8 * Nat.card C)
    (hidx : (Subgroup.centralizer ({w} : Set G)).relIndex Q ≤ 4) :
    ∀ k : Fin 7, 2 * Nat.card C ≤
      Nat.card ↥(Q ⊓ Subgroup.centralizer
        ({y ^ (k : ℕ) * w * (y ^ (k : ℕ))⁻¹} : Set G)) := by
  intro k
  let a : G := y ^ (k : ℕ)
  let D : Subgroup G := Q ⊓ Subgroup.centralizer ({a * w * a⁻¹} : Set G)
  have haQ : a ∈ Subgroup.normalizer (Q : Set G) := pow_mem hyQ (k : ℕ)
  have hrel : D.relIndex Q ≤ 4 := by
    simpa [D, a] using relIndex_inf_centralizer_conj_le_four (Q := Q) (a := a) (w := w) haQ hidx
  have hmul := Subgroup.relIndex_mul_card D Q
  rw [inf_eq_left.mpr (show D ≤ Q from inf_le_left)] at hmul
  have h8 : 8 * Nat.card C = D.relIndex Q * Nat.card D := by
    calc 8 * Nat.card C = Nat.card Q := hcardQ.symm
      _ = D.relIndex Q * Nat.card D := hmul.symm
  have h2r : 2 * D.relIndex Q ≤ 8 := by omega
  have hmul2 : (2 * D.relIndex Q) * Nat.card D = 16 * Nat.card C := by
    calc (2 * D.relIndex Q) * Nat.card D = 2 * (D.relIndex Q * Nat.card D) := by ring
      _ = 2 * (8 * Nat.card C) := by rw [← h8]
      _ = 16 * Nat.card C := by ring
  have hle : (2 * D.relIndex Q) * Nat.card D ≤ 8 * Nat.card D :=
    Nat.mul_le_mul_right _ h2r
  have : 2 * Nat.card C ≤ Nat.card D := by omega
  simpa [D, a] using this

private theorem seven_cover_pairwise_inter_nat {Q C : Subgroup G} {y w : G}
    (hy7 : orderOf y = 7) (hw : w ^ 2 = 1) (hwy : w * y * w⁻¹ = y⁻¹)
    (hC : C = Q ⊓ Subgroup.centralizer ({y} : Set G)) {a b : ℕ} (hab : a < b) (hb7 : b < 7) :
    (Q ⊓ Subgroup.centralizer ({y ^ a * w * (y ^ a)⁻¹} : Set G)) ⊓
        (Q ⊓ Subgroup.centralizer ({y ^ b * w * (y ^ b)⁻¹} : Set G)) ≤ C := by
  intro x hx
  have hxa : x ∈ Q ⊓ Subgroup.centralizer ({y ^ a * w * (y ^ a)⁻¹} : Set G) :=
    (Subgroup.mem_inf.mp hx).1
  have hxb : x ∈ Q ⊓ Subgroup.centralizer ({y ^ b * w * (y ^ b)⁻¹} : Set G) :=
    (Subgroup.mem_inf.mp hx).2
  have hxQ : x ∈ Q := (Subgroup.mem_inf.mp hxa).1
  have hxwa : Commute x (y ^ a * w * (y ^ a)⁻¹) :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hxa).2
  have hxwb : Commute x (y ^ b * w * (y ^ b)⁻¹) :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hxb).2
  have hprod : (y ^ b * w * (y ^ b)⁻¹) * (y ^ a * w * (y ^ a)⁻¹) = y ^ (2 * (b - a)) :=
    conj_involution_mul hw hwy (le_of_lt hab)
  have hcomm : Commute x ((y ^ b * w * (y ^ b)⁻¹) * (y ^ a * w * (y ^ a)⁻¹)) :=
    hxwb.mul_right hxwa
  rw [hprod] at hcomm
  have hd : Nat.gcd (2 * (b - a)) 7 = 1 :=
    gcd_two_mul_seven (by omega) (by omega)
  have hygen : y ∈ Subgroup.zpowers (y ^ (2 * (b - a))) := by
    rw [mem_zpowers_pow_iff, hy7]
    exact hd
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hygen
  have hxy : x * y = y * x := by
    have := hcomm.zpow_right m
    rwa [hm] at this
  rw [hC]
  exact ⟨hxQ, Subgroup.mem_centralizer_singleton_iff.mpr hxy⟩

private theorem seven_cover_pairwise_inter {Q C : Subgroup G} {y w : G}
    (hy7 : orderOf y = 7) (hw : w ^ 2 = 1) (hwy : w * y * w⁻¹ = y⁻¹)
    (hC : C = Q ⊓ Subgroup.centralizer ({y} : Set G)) :
    ∀ i j : Fin 7, i ≠ j →
      (Q ⊓ Subgroup.centralizer ({y ^ (i : ℕ) * w * (y ^ (i : ℕ))⁻¹} : Set G)) ⊓
        (Q ⊓ Subgroup.centralizer ({y ^ (j : ℕ) * w * (y ^ (j : ℕ))⁻¹} : Set G)) ≤ C := by
  intro i j hij
  have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact seven_cover_pairwise_inter_nat hy7 hw hwy hC hlt j.isLt
  · rw [inf_comm]
    exact seven_cover_pairwise_inter_nat hy7 hw hwy hC hgt i.isLt

private theorem seven_cover_normal {Q C : Subgroup G} {D : Fin 7 → Subgroup G}
    (hDcard : ∀ k, Nat.card (D k) = 2 * Nat.card C)
    (hCD : ∀ k, C ≤ D k)
    (hcover : ∀ q ∈ Q, q ∈ C ∨ ∃ k, q ∈ D k) :
    Q ≤ Subgroup.normalizer (C : Set G) := by
  intro q hq
  rcases hcover q hq with hqC | ⟨k, hqk⟩
  · exact Subgroup.le_normalizer hqC
  · have hrel : (C.subgroupOf (D k)).index = 2 := by
      change C.relIndex (D k) = 2
      have hm := Subgroup.relIndex_mul_card C (D k)
      rw [inf_eq_left.mpr (hCD k), hDcard k] at hm
      have hCpos : 0 < Nat.card C := Nat.card_pos
      nlinarith
    exact ((Subgroup.normal_subgroupOf_iff_le_normalizer (hCD k)).mp
      (Subgroup.normal_of_index_eq_two hrel)) hqk

private theorem seven_cover_square {Q C : Subgroup G} {D : Fin 7 → Subgroup G}
    (hDcard : ∀ k, Nat.card (D k) = 2 * Nat.card C)
    (hCD : ∀ k, C ≤ D k)
    (hcover : ∀ q ∈ Q, q ∈ C ∨ ∃ k, q ∈ D k) :
    ∀ q ∈ Q, q ^ 2 ∈ C := by
  intro q hq
  rcases hcover q hq with hqC | ⟨k, hqk⟩
  · simpa [pow_two] using C.mul_mem hqC hqC
  · have hrel : (C.subgroupOf (D k)).index = 2 := by
      change C.relIndex (D k) = 2
      have hm := Subgroup.relIndex_mul_card C (D k)
      rw [inf_eq_left.mpr (hCD k), hDcard k] at hm
      have hCpos : 0 < Nat.card C := Nat.card_pos
      nlinarith
    haveI : (C.subgroupOf (D k)).Normal := Subgroup.normal_of_index_eq_two hrel
    have hpow := Subgroup.pow_index_mem (C.subgroupOf (D k)) (⟨q, hqk⟩ : D k)
    have hpow' : ((⟨q, hqk⟩ : D k) ^ 2) ∈ C.subgroupOf (D k) := by
      simpa [hrel] using hpow
    simpa using (Subgroup.mem_subgroupOf.mp hpow')

private theorem exp_two_comm {V : Type*} [Group V] (h : ∀ v : V, v ^ 2 = 1) :
    ∀ a b : V, a * b = b * a := by
  intro a b
  have ha : a * a = 1 := by simpa [pow_two] using h a
  have hb : b * b = 1 := by simpa [pow_two] using h b
  have hab : (a * b) * (a * b) = 1 := by simpa [pow_two] using h (a * b)
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right hab).symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [hainv, hbinv]

private theorem quotient_exp_two {Q C : Subgroup G} [(C.subgroupOf Q).Normal]
    (hexp : ∀ q : ↥Q, (q : ↥Q) ^ 2 ∈ C.subgroupOf Q) :
    ∀ v : (↥Q ⧸ C.subgroupOf Q), v ^ 2 = 1 := by
  intro v
  refine QuotientGroup.induction_on v ?_
  intro q
  rw [← QuotientGroup.mk_pow]
  exact (QuotientGroup.eq_one_iff (N := C.subgroupOf Q) (q ^ 2)).mpr (hexp q)

private theorem coprime_seven_card_subgroupOf_of_isPGroup_two {Q C : Subgroup G}
    (hQ : IsPGroup 2 Q) :
    Nat.Coprime 7 (Nat.card (C.subgroupOf Q)) := by
  rw [Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 7)]
  intro h7
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := ↥Q)).mp hQ
  have hdiv : Nat.card (C.subgroupOf Q) ∣ Nat.card Q := by
    simpa using Subgroup.card_dvd_of_le
      (le_top : C.subgroupOf Q ≤ (⊤ : Subgroup ↥Q))
  have h7Q : 7 ∣ Nat.card Q := h7.trans hdiv
  rw [hn] at h7Q
  have h72 : 7 ∣ 2 := (by norm_num : Nat.Prime 7).dvd_of_dvd_pow h7Q
  norm_num at h72

private theorem exists_inverting_actions {Q C : Subgroup G} [(C.subgroupOf Q).Normal]
    {y w : G} (hyQ : y ∈ Subgroup.normalizer (Q : Set G))
    (hwQ : w ∈ Subgroup.normalizer (Q : Set G))
    (hyC : y ∈ Subgroup.normalizer (C : Set G))
    (hwC : w ∈ Subgroup.normalizer (C : Set G))
    (hy7 : y ^ 7 = 1) (hwy : w * y * w⁻¹ = y⁻¹) :
    ∃ z t : MulAut (↥Q ⧸ C.subgroupOf Q),
      z ^ 7 = 1 ∧ t * z * t⁻¹ = z⁻¹ ∧
      (∀ q : ↥Q, z (QuotientGroup.mk (s := C.subgroupOf Q) q) =
        QuotientGroup.mk (s := C.subgroupOf Q)
          (Subgroup.normalizerMonoidHom Q ⟨y, hyQ⟩ q)) := by
  let L : Subgroup G := Subgroup.zpowers y ⊔ Subgroup.zpowers w
  have hyL : y ∈ L := Subgroup.mem_sup_left (Subgroup.mem_zpowers y)
  have hwL : w ∈ L := Subgroup.mem_sup_right (Subgroup.mem_zpowers w)
  have hLQ : L ≤ Subgroup.normalizer (Q : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr hyQ) (Subgroup.zpowers_le.mpr hwQ)
  have hLC : L ≤ Subgroup.normalizer (C : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr hyC) (Subgroup.zpowers_le.mpr hwC)
  let φ : ↥L →* MulAut (↥Q ⧸ C.subgroupOf Q) := CFSG.GroupTheory.conjQuotHom hLQ hLC
  let z : MulAut (↥Q ⧸ C.subgroupOf Q) := φ ⟨y, hyL⟩
  let t : MulAut (↥Q ⧸ C.subgroupOf Q) := φ ⟨w, hwL⟩
  have hz7 : z ^ 7 = 1 := by
    change (φ ⟨y, hyL⟩) ^ 7 = 1
    rw [← map_pow]
    have hyL7 : (⟨y, hyL⟩ : ↥L) ^ 7 = 1 := Subtype.ext (by simpa using hy7)
    rw [hyL7, map_one]
  have htz : t * z * t⁻¹ = z⁻¹ := by
    have hwyl : (⟨w, hwL⟩ : ↥L) * ⟨y, hyL⟩ * (⟨w, hwL⟩ : ↥L)⁻¹ =
        ⟨y⁻¹, L.inv_mem hyL⟩ := Subtype.ext hwy
    calc t * z * t⁻¹
        = φ ((⟨w, hwL⟩ : ↥L) * ⟨y, hyL⟩ * (⟨w, hwL⟩ : ↥L)⁻¹) := by
          change φ ⟨w, hwL⟩ * φ ⟨y, hyL⟩ * (φ ⟨w, hwL⟩)⁻¹ = φ _
          rw [← map_mul, ← map_inv, ← map_mul]
      _ = φ ⟨y⁻¹, L.inv_mem hyL⟩ := by rw [hwyl]
      _ = z⁻¹ := by
          change φ ⟨y⁻¹, L.inv_mem hyL⟩ = (φ ⟨y, hyL⟩)⁻¹
          rw [show (⟨y⁻¹, L.inv_mem hyL⟩ : ↥L) = (⟨y, hyL⟩ : ↥L)⁻¹ by
            ext; simp, map_inv]
  have hzapply : ∀ q : ↥Q,
      z (QuotientGroup.mk (s := C.subgroupOf Q) q) =
        QuotientGroup.mk (s := C.subgroupOf Q)
          (Subgroup.normalizerMonoidHom Q ⟨y, hyQ⟩ q) := by
    intro q
    change (φ ⟨y, hyL⟩) (QuotientGroup.mk (s := C.subgroupOf Q) q) =
      QuotientGroup.mk (s := C.subgroupOf Q)
        (Subgroup.normalizerMonoidHom Q ⟨y, hyQ⟩ q)
    rw [CFSG.GroupTheory.conjQuotHom_apply, CFSG.GroupTheory.conjQuotAut_mk]
    have hψq : Subgroup.normalizerMonoidHom Q ⟨y, hyQ⟩ q =
        (⟨y * (q : G) * y⁻¹,
          (Subgroup.mem_normalizer_iff.mp hyQ (q : G)).mp q.2⟩ : ↥Q) := by
      ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    rw [hψq]
  exact ⟨z, t, hz7, htz, hzapply⟩

private theorem fixed_eq_one_of_action {Q C : Subgroup G} [(C.subgroupOf Q).Normal]
    {y : G} (hyQ : y ∈ Subgroup.normalizer (Q : Set G))
    (hyC : y ∈ Subgroup.normalizer (C : Set G))
    (hC : C = Q ⊓ Subgroup.centralizer ({y} : Set G))
    (hy7 : y ^ 7 = 1) (hcop7 : Nat.Coprime 7 (Nat.card (C.subgroupOf Q)))
    (z : MulAut (↥Q ⧸ C.subgroupOf Q))
    (hzapply : ∀ q : ↥Q, z (QuotientGroup.mk (s := C.subgroupOf Q) q) =
      QuotientGroup.mk (s := C.subgroupOf Q)
        (Subgroup.normalizerMonoidHom Q ⟨y, hyQ⟩ q)) :
    ∀ v : (↥Q ⧸ C.subgroupOf Q), z v = v → v = 1 := by
  intro v hv
  revert hv
  refine QuotientGroup.induction_on v ?_
  intro q hv
  let ψ : MulAut ↥Q := Subgroup.normalizerMonoidHom Q ⟨y, hyQ⟩
  have hψ7 : ψ ^ 7 = 1 := by
    change (Subgroup.normalizerMonoidHom Q ⟨y, hyQ⟩) ^ 7 = 1
    rw [← map_pow]
    have hyN7 : (⟨y, hyQ⟩ : ↥(Subgroup.normalizer (Q : Set G))) ^ 7 = 1 :=
      Subtype.ext (by simpa using hy7)
    rw [hyN7, map_one]
  have hdisp : (q : ↥Q)⁻¹ * ψ q ∈ C.subgroupOf Q := by
    have heq : QuotientGroup.mk (s := C.subgroupOf Q) q =
        QuotientGroup.mk (s := C.subgroupOf Q) (ψ q) := by
      rw [← hzapply q]; exact hv.symm
    exact (QuotientGroup.eq).mp heq
  have hN : ∀ n ∈ C.subgroupOf Q, ψ n ∈ C.subgroupOf Q := by
    intro n hn
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hconj : ((ψ n : ↥Q) : G) = y * (n : G) * y⁻¹ :=
      Subgroup.normalizerMonoidHom_apply_apply_coe Q ⟨y, hyQ⟩ n
    rw [hconj]
    exact (Subgroup.mem_normalizer_iff.mp hyC (n : G)).mp hn
  have hcopψ : Nat.Coprime (orderOf ψ) (Nat.card (C.subgroupOf Q)) :=
    Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hψ7) hcop7
  obtain ⟨n, hnN, hnfix⟩ :=
    CFSG.GroupTheory.exists_fixed_mem_coset_of_coprime_mulAut
      (C.subgroupOf Q) ψ (g := q) hN hdisp hcopψ
  have hqnC : (q * n : ↥Q) ∈ C.subgroupOf Q := by
    rw [Subgroup.mem_subgroupOf, hC]
    refine Subgroup.mem_inf.mpr ⟨(q * n).2, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcoeeq : ((ψ (q * n) : ↥Q) : G) =
        y * ((q * n : ↥Q) : G) * y⁻¹ :=
      Subgroup.normalizerMonoidHom_apply_apply_coe Q ⟨y, hyQ⟩ (q * n)
    have hfixG : y * ((q * n : ↥Q) : G) * y⁻¹ = ((q * n : ↥Q) : G) := by
      rw [← hcoeeq, hnfix]
    calc ((q * n : ↥Q) : G) * y =
        (y * ((q * n : ↥Q) : G) * y⁻¹) * y := by rw [hfixG]
      _ = y * ((q * n : ↥Q) : G) := by group
  have hqC : (q : ↥Q) ∈ C.subgroupOf Q := by
    have hmul : (q * n) * n⁻¹ ∈ C.subgroupOf Q :=
      (C.subgroupOf Q).mul_mem hqnC ((C.subgroupOf Q).inv_mem hnN)
    simpa [mul_assoc] using hmul
  exact (QuotientGroup.eq_one_iff (N := C.subgroupOf Q) q).mpr hqC

private theorem index_one_case {Q C : Subgroup G} {y : G}
    (hC : C = Q ⊓ Subgroup.centralizer ({y} : Set G)) (hCQ : C ≤ Q)
    (hmulC : C.relIndex Q * Nat.card C = Nat.card Q) (hr1 : C.relIndex Q = 1) :
    Q ≤ Subgroup.centralizer ({y} : Set G) := by
  rw [hr1, one_mul] at hmulC
  have hCeqQ : C = Q := Subgroup.eq_of_le_of_card_ge hCQ (le_of_eq hmulC.symm)
  have hCcent : C ≤ Subgroup.centralizer ({y} : Set G) := by
    rw [hC]
    exact inf_le_right
  rwa [hCeqQ] at hCcent

private theorem y_mem_normalizer_inf_centralizer {Q : Subgroup G} {y : G} :
    y ∈ Subgroup.normalizer (Q ⊓ Subgroup.centralizer ({y} : Set G) : Set G) := by
  apply Subgroup.centralizer_le_normalizer
  rw [Subgroup.mem_centralizer_iff]
  intro c hc
  exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hc).2

private theorem mem_normalizer_of_le_inf_centralizer {C Q : Subgroup G} {w : G}
    (h : C ≤ Q ⊓ Subgroup.centralizer ({w} : Set G)) :
    w ∈ Subgroup.normalizer (C : Set G) := by
  apply Subgroup.centralizer_le_normalizer
  rw [Subgroup.mem_centralizer_iff]
  intro c hc
  exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp (h hc)).2

private theorem exists_actions_with_fixed {Q C : Subgroup G} [(C.subgroupOf Q).Normal]
    {y w : G} (hyQ : y ∈ Subgroup.normalizer (Q : Set G))
    (hwQ : w ∈ Subgroup.normalizer (Q : Set G))
    (hyC : y ∈ Subgroup.normalizer (C : Set G))
    (hwC : w ∈ Subgroup.normalizer (C : Set G))
    (hy7 : y ^ 7 = 1) (hwy : w * y * w⁻¹ = y⁻¹)
    (hC : C = Q ⊓ Subgroup.centralizer ({y} : Set G))
    (hcop7 : Nat.Coprime 7 (Nat.card (C.subgroupOf Q))) :
    ∃ z t : MulAut (↥Q ⧸ C.subgroupOf Q),
      z ^ 7 = 1 ∧ t * z * t⁻¹ = z⁻¹ ∧
      (∀ v : (↥Q ⧸ C.subgroupOf Q), z v = v → v = 1) := by
  obtain ⟨z, t, hz7, htz, hzapply⟩ := exists_inverting_actions hyQ hwQ hyC hwC hy7 hwy
  exact ⟨z, t, hz7, htz, fixed_eq_one_of_action hyQ hyC hC hy7 hcop7 z hzapply⟩

private theorem exceptional_case {p : ℕ} [Fact p.Prime] {Q : Subgroup G} {y w : G}
    (hQ : IsPGroup 2 Q) (hyQ : y ∈ Subgroup.normalizer (Q : Set G))
    (hwQ : w ∈ Subgroup.normalizer (Q : Set G)) (hy : orderOf y = p) (hw : w ^ 2 = 1)
    (hwy : w * y * w⁻¹ = y⁻¹)
    (hidx : (Subgroup.centralizer ({w} : Set G)).relIndex Q ≤ 4)
    (hmulC : (Q ⊓ Subgroup.centralizer ({y} : Set G)).relIndex Q *
      Nat.card ↥(Q ⊓ Subgroup.centralizer ({y} : Set G)) = Nat.card Q)
    (hp7 : p = 7) (hr8 : (Q ⊓ Subgroup.centralizer ({y} : Set G)).relIndex Q = 8) :
    Q ≤ Subgroup.centralizer ({y} : Set G) := by
  let C : Subgroup G := Q ⊓ Subgroup.centralizer ({y} : Set G)
  have hCQ : C ≤ Q := inf_le_left
  have hy7 : orderOf y = 7 := by rw [hy, hp7]
  have hy7pow : y ^ 7 = 1 := by rw [← hy7]; exact pow_orderOf_eq_one y
  have hcardQ : Nat.card Q = 8 * Nat.card C := by rw [← hmulC, hr8]
  let D : Fin 7 → Subgroup G := fun k =>
    Q ⊓ Subgroup.centralizer ({y ^ (k : ℕ) * w * (y ^ (k : ℕ))⁻¹} : Set G)
  have hDlarge : ∀ k : Fin 7, 2 * Nat.card C ≤ Nat.card (D k) := by
    simpa [D] using seven_cover_card_large (C := C) hyQ hcardQ hidx
  have hdisj : ∀ i j : Fin 7, i ≠ j → D i ⊓ D j ≤ C := by
    simpa [D] using seven_cover_pairwise_inter (C := C) hy7 hw hwy (by rfl)
  obtain ⟨hDcard, hCD, hcover⟩ :=
    card_eq_two_mul_of_seven_cover hCQ (fun k => inf_le_left) hcardQ hDlarge hdisj
  have hCnormal : Q ≤ Subgroup.normalizer (C : Set G) := seven_cover_normal hDcard hCD hcover
  have hsq : ∀ q ∈ Q, q ^ 2 ∈ C := seven_cover_square hDcard hCD hcover
  haveI : (C.subgroupOf Q).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCQ).mpr hCnormal
  let V := ↥Q ⧸ C.subgroupOf Q
  have hVcard : Nat.card V = 8 := by
    rw [← Subgroup.index_eq_card (C.subgroupOf Q)]
    exact hr8
  have hVexp : ∀ v : V, v ^ 2 = 1 :=
    quotient_exp_two (Q := Q) (C := C) (fun q => Subgroup.mem_subgroupOf.mpr (hsq q q.2))
  have hcommV : ∀ a b : V, a * b = b * a := exp_two_comm hVexp
  letI : CommGroup V := { (inferInstance : Group V) with mul_comm := hcommV }
  have hyC : y ∈ Subgroup.normalizer (C : Set G) := by
    simpa [C] using y_mem_normalizer_inf_centralizer (Q := Q) (y := y)
  have hC_le_D : C ≤ Q ⊓ Subgroup.centralizer ({w} : Set G) := by
    simpa [D] using hCD (0 : Fin 7)
  have hwC : w ∈ Subgroup.normalizer (C : Set G) :=
    mem_normalizer_of_le_inf_centralizer hC_le_D
  have hcop7 : Nat.Coprime 7 (Nat.card (C.subgroupOf Q)) :=
    coprime_seven_card_subgroupOf_of_isPGroup_two (Q := Q) (C := C) hQ
  obtain ⟨z, t, hz7, htz, hfix⟩ :=
    exists_actions_with_fixed (C := C) hyQ hwQ hyC hwC hy7pow hwy (by rfl) hcop7
  have hVrk : CFSG.Quasithin.rk V = 3 := by
    unfold CFSG.Quasithin.rk
    rw [hVcard, show 8 = 2 ^ 3 by norm_num, padicValNat.prime_pow]
  have hodd : Odd (CFSG.Quasithin.rk V) := by
    rw [hVrk]
    norm_num
  exfalso
  exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.s16t_a_false_of_inverted
    (T := V) (z := z) (a := t) hVexp hodd hz7 hfix htz

theorem le_centralizer_of_inverts {p : ℕ} [Fact p.Prime] (hp : 7 ≤ p) {Q : Subgroup G}
    {y w : G} (hQ : IsPGroup 2 Q) (hyQ : y ∈ Subgroup.normalizer (Q : Set G))
    (hwQ : w ∈ Subgroup.normalizer (Q : Set G)) (hy : orderOf y = p) (hw : w ^ 2 = 1)
    (hwy : w * y * w⁻¹ = y⁻¹) (hidx : (Subgroup.centralizer ({w} : Set G)).relIndex Q ≤ 4) :
    Q ≤ Subgroup.centralizer ({y} : Set G) := by
  classical
  let C : Subgroup G := Q ⊓ Subgroup.centralizer ({y} : Set G)
  have hCQ : C ≤ Q := inf_le_left
  have hindex_le : C.relIndex Q ≤ 16 := by
    simpa [C] using relIndex_inf_centralizer_le_sixteen hp hyQ hy hw hwy hidx
  have hmod : Nat.card Q ≡ Nat.card C [MOD p] := by
    simpa [C] using card_modEq_inf_centralizer hyQ hy
  have hdvd : p ∣ C.relIndex Q - 1 := index_dvd_sub_one hp hCQ hQ hmod
  have hpow : ∃ k ≤ 4, C.relIndex Q = 2 ^ k := exists_pow_two_index hQ hindex_le
  have hmulC : C.relIndex Q * Nat.card C = Nat.card Q := by
    simpa [inf_eq_left.mpr hCQ] using Subgroup.relIndex_mul_card C Q
  rcases index_eq_one_or_seven_eight (Fact.out : p.Prime) hp hdvd hpow with hr1 | ⟨hp7, hr8⟩
  · exact index_one_case (C := C) rfl hCQ hmulC hr1
  · exact exceptional_case hQ hyQ hwQ hy hw hwy hidx hmulC hp7 hr8
