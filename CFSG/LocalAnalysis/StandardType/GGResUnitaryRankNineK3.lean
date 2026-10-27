module

public import CFSG.LocalAnalysis.StandardType.GGResUnitaryRankSixK3
public import CFSG.LocalAnalysis.StandardType.GGResThreeCensusLabel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.StandardType.LineU TableB

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem GGTorusTorData.card_le {p m N : ℕ} (hp : p.Prime) (hm : m ≠ 0)
    {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)} {L' : Type} [Group L']
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A) (h : GGTorusTorData m N C M L' A) :
    Nat.card A ≤ p ^ N := by
  classical
  haveI : NeZero m := ⟨hm⟩
  obtain ⟨w, hw⟩ := h
  obtain ⟨-, hAT, -, hhom, -, -, -, -, -, -, hsep, -⟩ := hw
  have hone : ∀ k, w.α k 1 = 1 := fun k => ggTor_alpha_one w.T (w.α k) (hhom k)
  have hpow : ∀ (a : A) (k : Fin N), w.α k a ^ p = 1 := by
    intro a k
    rw [← ggTor_alpha_pow w.T (w.α k) (hhom k) a (hAT a.2) p, hA.2 a a.2, hone k]
  let f : A → Fin N → {z : Multiplicative (ZMod m) // z ^ p = 1} :=
    fun a k => ⟨w.α k a, hpow a k⟩
  have hf : Function.Injective f := by
    intro a b hab
    have hk : ∀ k, w.α k a = w.α k b := fun k => congrArg Subtype.val (congrFun hab k)
    have hb' : (b : MulAut L')⁻¹ ∈ w.T := w.T.inv_mem (hAT b.2)
    have hab' : ∀ k, w.α k ((a : MulAut L') * (b : MulAut L')⁻¹) = 1 := by
      intro k
      have e1 := hhom k a (hAT a.2) _ hb'
      have e2 := hhom k b (hAT b.2) _ hb'
      rw [mul_inv_cancel, hone k] at e2
      rw [e1, hk k, ← e2]
    exact Subtype.ext (mul_inv_eq_one.mp (hsep _ (w.T.mul_mem (hAT a.2) hb') hab'))
  have hZ : Nat.card {z : Multiplicative (ZMod m) // z ^ p = 1} ≤ p := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    convert IsCyclic.card_pow_eq_one_le (α := Multiplicative (ZMod m)) hp.pos
  calc Nat.card A ≤ Nat.card (Fin N → {z : Multiplicative (ZMod m) // z ^ p = 1}) :=
        Nat.card_le_card_of_injective f hf
    _ = Nat.card {z : Multiplicative (ZMod m) // z ^ p = 1} ^ N := by
        rw [Nat.card_fun, Nat.card_fin]
    _ ≤ p ^ N := Nat.pow_le_pow_left hZ N

theorem not_dvd_two_pow_add_one_of_dvd_sub {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : p ∣ 2 ^ n - 1) : ¬ p ∣ 2 ^ n + 1 := by
  intro h'
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have e : 2 ^ n + 1 = (2 ^ n - 1) + 2 := by omega
  rw [e] at h'
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp ((Nat.dvd_add_right h).mp h'))

theorem not_five_dvd_two_pow_add_one_of_odd {n : ℕ} (hn : Odd n) : ¬ 5 ∣ 2 ^ n + 1 := by
  obtain ⟨k, rfl⟩ := hn
  have h4 : ∀ k : ℕ, 4 ^ k % 5 = 1 ∨ 4 ^ k % 5 = 4 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, Nat.mul_mod]
      rcases ih with h | h <;> rw [h] <;> norm_num
  have e : 2 ^ (2 * k + 1) = 2 * 4 ^ k := by
    rw [pow_succ, pow_mul]
    norm_num
    ring
  rw [e]
  have := h4 k
  omega

theorem dvd_sub_of_split_untwisted {p : ℕ} (hp3 : p ≠ 3) {lab : LargeEvenLabel}
    (hs : LargeEvenSplit p lab) (hu : LargeEvenUntwisted lab.tag) : p ∣ 2 ^ lab.n - 1 := by
  rcases hs with ⟨-, h⟩ | ⟨h, -, -⟩ | ⟨h, -⟩ | ⟨-, h⟩
  · exact h
  · exact absurd hu h
  · rcases h with h | h <;> rw [h] at hu <;> simp [LargeEvenUntwisted] at hu
  · exact absurd h hp3

theorem dvd_add_of_split_twisted {p : ℕ} (hp3 : p ≠ 3) {lab : LargeEvenLabel}
    (hs : LargeEvenSplit p lab) (hu : ¬ LargeEvenUntwisted lab.tag) (hd : lab.tag ≠ .twD)
    (ht : lab.tag ≠ .triD4) : p ∣ 2 ^ lab.n + 1 := by
  rcases hs with ⟨h, -⟩ | ⟨-, -, h⟩ | ⟨h, -⟩ | ⟨-, h⟩
  · exact absurd h hu
  · exact h
  · rcases h with h | h
    · exact absurd h hd
    · exact absurd h ht
  · exact absurd h hp3

theorem ggTorEnn_eq_zero_of_dvd_sub {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (h : p ∣ 2 ^ lab.n - 1) : ggTorEnn p lab = 0 := by
  unfold ggTorEnn
  rw [if_neg (not_dvd_two_pow_add_one_of_dvd_sub hp hp2 h)]

theorem ggTorEnn_le_one (p : ℕ) (lab : LargeEvenLabel) : ggTorEnn p lab ≤ 1 := by
  unfold ggTorEnn
  split_ifs <;> omega

theorem ggTBTorRow_five_twA_of_bounds {lab : LargeEvenLabel} {r m N : ℕ}
    {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    (hrow : GGTBTorRowAt 5 lab r m N C M) (hs : LargeEvenSplit 5 lab) (hr : r ≤ 7)
    (hN : 8 ≤ N) : lab.tag = .twA ∧ 4 ≤ lab.rank := by
  have hp : (5 : ℕ).Prime := by norm_num
  have h0 : LargeEvenUntwisted lab.tag → ggTorEnn 5 lab = 0 := fun hu =>
    ggTorEnn_eq_zero_of_dvd_sub hp (by norm_num) (dvd_sub_of_split_untwisted (by norm_num) hs hu)
  have h1 := ggTorEnn_le_one 5 lab
  cases hrow with
  | aDep ht h2 h3 _ _ =>
    rcases ht with ht | ht
    · have := h0 (by rw [ht]; trivial)
      exfalso
      have h8 : lab.rank = 8 := by omega
      rw [h8] at h3
      norm_num at h3
    · exact ⟨ht, h2⟩
  | e6Three _ h2 _ => norm_num at h2
  | e8Three _ h2 => norm_num at h2
  | aInd ht _ _ =>
    rcases ht with ht | ht
    · have := h0 (by rw [ht]; trivial)
      omega
    · exact ⟨ht, by omega⟩
  | c ht _ =>
    have hu : LargeEvenUntwisted lab.tag := by rcases ht with ht | ht <;> rw [ht] <;> trivial
    have := h0 hu
    omega
  | d ht =>
    exfalso
    rcases ht with ⟨ht, -⟩ | ⟨-, -, hodd⟩
    · have := h0 (by rw [ht]; trivial)
      omega
    · obtain ⟨k, hk⟩ := hodd
      omega
  | e6Ind _ _ _ => omega
  | e7 _ _ => omega
  | e8Ind _ ht _ =>
    have := h0 (by rw [ht]; trivial)
    omega
  | f4 _ _ _ => omega
  | g2 _ _ => omega
  | relD _ => omega
  | relE6 _ _ => omega
  | relA5 _ _ => omega

theorem ggTBTorCov_five_of_split {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hs : LargeEvenSplit 5 lab) (htri : lab.tag ≠ .triD4)
    (hU : ¬ (lab.tag = .twA ∧ 4 ≤ lab.rank)) : GGTBTorCov 5 lab := by
  obtain ⟨t, l, n⟩ := lab
  have hm : ∀ {k : ℕ}, 5 ∣ k → 5 ∣ k * (2 ^ n + 1) := fun h => dvd_mul_of_dvd_left h _
  cases t with
  | A =>
    have h := dvd_sub_of_split_untwisted (by norm_num) hs trivial
    have hl : 1 ≤ l := hlab.2.1
    by_cases hd : 5 ∣ l + 1
    · have hl4 : 4 ≤ l := by have := Nat.le_of_dvd (by omega) hd; omega
      exact ⟨_, _, _, _, _, GGTBTorRowAt.aDep (Or.inl rfl) hl4 hd
        (by simpa [ggTorM] using h) (by rintro ⟨h3, -⟩; norm_num at h3)⟩
    · exact ⟨_, _, _, _, _, GGTBTorRowAt.aInd (Or.inl rfl) hd (by simpa [ggTorM] using h)⟩
  | twA =>
    have h := dvd_add_of_split_twisted (by norm_num) hs (by simp [LargeEvenUntwisted])
      (by simp) (by simp)
    have hl2 : 2 ≤ l := hlab.2.1
    have hl : l < 4 := by
      by_contra h4
      exact hU ⟨rfl, by change 4 ≤ l; omega⟩
    have hd : ¬ 5 ∣ l + 1 := by
      intro hd
      have := Nat.le_of_dvd (by omega) hd
      omega
    exact ⟨_, _, _, _, _, GGTBTorRowAt.aInd (Or.inr rfl) hd (by simpa [ggTorM] using h)⟩
  | B =>
    exact ⟨_, _, _, _, _, GGTBTorRowAt.c (Or.inl rfl)
      (hm (dvd_sub_of_split_untwisted (by norm_num) hs trivial))⟩
  | C =>
    exact ⟨_, _, _, _, _, GGTBTorRowAt.c (Or.inr rfl)
      (hm (dvd_sub_of_split_untwisted (by norm_num) hs trivial))⟩
  | D =>
    exact ⟨_, _, _, _, _, GGTBTorRowAt.d
      (Or.inl ⟨rfl, Or.inl (dvd_sub_of_split_untwisted (by norm_num) hs trivial)⟩)⟩
  | twD =>
    rcases hs with ⟨h, -⟩ | ⟨-, -, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
    · simp [LargeEvenUntwisted] at h
    · rcases Nat.even_or_odd l with he | ho
      · exact ⟨_, _, _, _, _, GGTBTorRowAt.relD (Or.inr ⟨rfl, Or.inr ⟨h, he⟩⟩)⟩
      · exact ⟨_, _, _, _, _, GGTBTorRowAt.d (Or.inr ⟨rfl, h, ho⟩)⟩
    · exact ⟨_, _, _, _, _, GGTBTorRowAt.relD (Or.inr ⟨rfl, Or.inl h⟩)⟩
    · norm_num at h
  | E6 =>
    exact ⟨_, _, _, _, _, GGTBTorRowAt.e6Ind (by norm_num) (Or.inl rfl)
      (by simpa [ggTorM] using dvd_sub_of_split_untwisted (by norm_num) hs trivial)⟩
  | E7 =>
    exact ⟨_, _, _, _, _, GGTBTorRowAt.e7 rfl
      (hm (dvd_sub_of_split_untwisted (by norm_num) hs trivial))⟩
  | E8 =>
    exact ⟨_, _, _, _, _, GGTBTorRowAt.e8Ind (by norm_num) rfl
      (hm (dvd_sub_of_split_untwisted (by norm_num) hs trivial))⟩
  | F4 =>
    exact ⟨_, _, _, _, _, GGTBTorRowAt.f4 rfl
      (hm (dvd_sub_of_split_untwisted (by norm_num) hs trivial))
      (by rintro ⟨h3, -⟩; norm_num at h3)⟩
  | twE6 =>
    have h := dvd_add_of_split_twisted (by norm_num) hs (by simp [LargeEvenUntwisted])
      (by simp) (by simp)
    exact ⟨_, _, _, _, _, GGTBTorRowAt.e6Ind (by norm_num) (Or.inr rfl)
      (by simpa [ggTorM] using h)⟩
  | triD4 => exact absurd rfl htri
  | G2 =>
    exact ⟨_, _, _, _, _, GGTBTorRowAt.g2 rfl
      (dvd_sub_of_split_untwisted (by norm_num) hs trivial)⟩
  | twB2 =>
    exact absurd (dvd_add_of_split_twisted (by norm_num) hs (by simp [LargeEvenUntwisted])
      (by simp) (by simp)) (not_five_dvd_two_pow_add_one_of_odd hlab.2.2.1)
  | twF4 =>
    exact absurd (dvd_add_of_split_twisted (by norm_num) hs (by simp [LargeEvenUntwisted])
      (by simp) (by simp)) (not_five_dvd_two_pow_add_one_of_odd hlab.2.2.1)
  | B2der =>
    have h := dvd_sub_of_split_untwisted (by norm_num) hs trivial
    have hn : n = 1 := hlab.2.2
    subst hn
    norm_num at h
  | G2der =>
    have h := dvd_sub_of_split_untwisted (by norm_num) hs trivial
    have hn : n = 1 := hlab.2.2
    subst hn
    norm_num at h
  | twF4der =>
    have h := dvd_add_of_split_twisted (by norm_num) hs (by simp [LargeEvenUntwisted])
      (by simp) (by simp)
    have hn : n = 1 := hlab.2.2
    subst hn
    norm_num at h

theorem GGResHyp.card_le_of_tbTorRow_L (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {r m N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ}
    {M : CoxeterMatrix (Fin N)}
    (hX : GGInnerDiagOnLabel (fun p lab => GGTBTorRowAt p lab r m N C M) p Bs L) :
    p ^ (r + 1) ≤ Nat.card B ∧ Nat.card Bs ≤ p ^ (N + 1) := by
  classical
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hcfg := hH.1
  obtain ⟨-, hBs, -, hLx, -⟩ := hcfg.tableB_facts
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  obtain ⟨hperf, lab, hΛ, hraw⟩ := largeEvenMarking_and_labelAll
    (S := fun lab => GGTBTorRowAt p lab r m N C M)
    (P' := fun R _ I _ => GGTorusLift p r R ∧ GGTorusTorW p r m N C M R I)
    (fun lab hΛ hrow => largeEvenLabelAll_and (hLift p lab r m N C M hp hp2 hΛ hrow)
      (ggTBTorWRows_of_all hT p lab r m N C M hp hp2 hΛ hrow))
    (fun _ _ _ _ _ _ hP => hP.1) hX
  obtain ⟨R, _, I, F, -, -, θ, ⟨hrow, hN, hind⟩, hlift, hTorW⟩ := largeEvenRawDatum_exists hraw
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut L θ ⟨b, hN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces L θ hN hind hb
  obtain ⟨hr, h3⟩ := card_range_ggGamma_bstar_ge hcfg hperf θ hN hlift
  have hTB := ggTorusTBGroup_of_marking hp hBs hSC hperf θ hN hBsI hr h3
  have hm : m ≠ 0 := (l05nPlP1_row_facts hp hp2 hΛ hrow).1.pos.ne'
  have hγ : Nat.card (ggGamma L hN).range ≤ p ^ N :=
    GGTorusTorData.card_le hp hm hTB.2.2.2.1 (hTorW ↥L (ggQuotHom θ) _ hTB)
  have hγBs : Nat.card (ggGamma L hN).range * p = Nat.card Bs := by
    have h := NbrU63.card_range_ggGamma_mul_card_inf (K := L) hN
    rwa [hcfg.card_bstar_inf_centralizer_L] at h
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have h1 := succ_le_twoLocalRank_of_torusLift hp hLx (hS.1.1.2 x hS.2.1) hS.2.2.1 hperf θ hlift
  refine ⟨?_, ?_⟩
  · rw [hS.1.2.1]
    exact Nat.pow_le_pow_right hp.pos h1
  · rw [← hγBs, pow_succ]
    exact Nat.mul_le_mul_right p hγ

theorem GGResHyp.unitary_exactThree_K_card_data
    (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {ℓ : ℕ}
    (hU : GGInnerDiagOnLabel
      (fun p lab => lab.tag = .twA ∧ lab.rank = ℓ ∧ p ∣ 2 ^ lab.n + 1) p Bs K)
    (hℓ : 4 ≤ ℓ) (h63 : ¬ (ℓ + 1 = 6 ∧ p = 3))
    (h3 : GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) :
    p ∣ ℓ + 1 ∧ Nat.card Bs = p ^ ℓ ∧ B < Bs := by
  classical
  obtain ⟨-, lab, hΛ, hraw⟩ := hU
  obtain ⟨R₀, iR₀, I₀, F₀, hQ₀⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨-, -, θ₀, hP₀⟩ := hQ₀
  obtain ⟨⟨htag, hrank, hpq⟩, -, -⟩ := hP₀
  obtain ⟨tag, rank, n⟩ := lab
  change tag = .twA at htag
  change rank = ℓ at hrank
  change p ∣ 2 ^ n + 1 at hpq
  subst htag hrank
  dsimp only [LargeEvenRawDatumLegacy] at hraw
  obtain ⟨F, hField, hFinite, hFK, hQ⟩ := hraw
  let _ : Field F := hField
  let _ : Finite F := hFinite
  obtain ⟨-, -, θ, -, hN, hact⟩ := hQ
  obtain ⟨ψ, hM, hdiag⟩ :=
    hH.exists_unitaryModel_K_of_marking_data hFK hΛ.1 (by omega) hpq h63 θ hN hact
  obtain ⟨r, hd, hpd, -, hcard, -, hlt, -⟩ :=
    hH.unitary_exactThree_typeA_card_J_of_K hLB hM hpq (by omega) hdiag h3
  refine ⟨hpd, ?_, hlt⟩
  rw [hcard]
  congr 1
  omega

section RowBoundsCertPool

private theorem row_bounds_core {G : Type} [Group G] [Finite G] {p r ℓ N : ℕ} {B Bs : Subgroup G}
    (hp : p.Prime) (hBsE : IsElemAbelian p Bs) (hBlt : B < Bs)
    (hB : p ^ (r + 1) ≤ Nat.card B) (hBs : Nat.card Bs ≤ p ^ (N + 1))
    (hcard : Nat.card Bs = p ^ ℓ) : r + 2 ≤ ℓ ∧ ℓ ≤ N + 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hmul := mul_card_le_card_of_lt hp hBsE hBlt
  have hpow : p ^ (r + 2) ≤ p ^ ℓ := by
    calc
      p ^ (r + 2) = p * p ^ (r + 1) := by
        rw [show r + 2 = r + 1 + 1 by omega, pow_succ, mul_comm]
      _ ≤ p * Nat.card B := Nat.mul_le_mul_left p hB
      _ ≤ Nat.card Bs := hmul
      _ = p ^ ℓ := hcard
  have hle : r + 2 ≤ ℓ := (Nat.pow_le_pow_iff_right hp.one_lt).mp hpow
  have hup : p ^ ℓ ≤ p ^ (N + 1) := by simpa [hcard] using hBs
  exact ⟨hle, (Nat.pow_le_pow_iff_right hp.one_lt).mp hup⟩

private theorem rankFive_card_of_original
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hU : GGInnerDiagOnLabel
      (fun p lab => lab.tag = .twA ∧ lab.rank = 5 ∧ 2 ≤ lab.n ∧
        p ∣ 2 ^ lab.n + 1) p Bs K)
    (h3 : GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) :
    p = 3 ∧ Nat.card Bs = 3 ^ 5 ∧ B < Bs := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hp3, _, _, _, hcard, _, _, hBlt⟩ :=
    hH.rankFiveK3_original_facts hU h3
  exact ⟨hp3, hcard, hBlt⟩

theorem GGResHyp.tbTorRow_bounds_of_unitary_exactThree_K
    (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {r m N : ℕ}
    {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    (hLrow : GGInnerDiagOnLabel (fun p lab => GGTBTorRowAt p lab r m N C M) p Bs L)
    {ℓ : ℕ}
    (hU : GGInnerDiagOnLabel
      (fun p lab => lab.tag = .twA ∧ lab.rank = ℓ ∧ 2 ≤ lab.n ∧
        p ∣ 2 ^ lab.n + 1) p Bs K)
    (hℓ4 : 4 ≤ ℓ)
    (h3 : GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) :
    r + 2 ≤ ℓ ∧ ℓ ≤ N + 1 := by
  classical
  have hp : p.Prime := Fact.out
  obtain ⟨hB, hBs⟩ := hH.card_le_of_tbTorRow_L hT hLift hLrow
  have hBsE : IsElemAbelian p Bs := hH.1.2.1.2.1
  by_cases h5 : ℓ = 5
  · subst ℓ
    obtain ⟨hp3, hcard, hBlt⟩ := rankFive_card_of_original hH hU h3
    exact row_bounds_core hp hBsE hBlt hB hBs (by simpa [hp3] using hcard)
  · have h63 : ¬ (ℓ + 1 = 6 ∧ p = 3) := by
      rintro ⟨h, -⟩
      exact h5 (by omega)
    have hU' : GGInnerDiagOnLabel
        (fun p lab => lab.tag = .twA ∧ lab.rank = ℓ ∧ p ∣ 2 ^ lab.n + 1) p Bs K :=
      hU.mono_label (fun lab h => ⟨h.1, h.2.1, h.2.2.2⟩)
    obtain ⟨-, hcard, hBlt⟩ :=
      hH.unitary_exactThree_K_card_data (ggGammaSuppliers_proved.1) hU' hℓ4 h63 h3
    exact row_bounds_core hp hBsE hBlt hB hBs hcard

theorem GGResHyp.tbTorRow_bounds_five_of_unitary_exactThree_K
    (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {r m N : ℕ}
    {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    (hLrow : GGInnerDiagOnLabel (fun p lab => GGTBTorRowAt p lab r m N C M) p Bs L)
    (hU : GGInnerDiagOnLabel
      (fun p lab => lab.tag = .twA ∧ lab.rank = 5 ∧ 2 ≤ lab.n ∧
        p ∣ 2 ^ lab.n + 1) p Bs K)
    (h3 : GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) :
    p = 3 ∧ r ≤ 3 ∧ 4 ≤ N := by
  have hb := hH.tbTorRow_bounds_of_unitary_exactThree_K hT hLift hLrow hU (by norm_num) h3
  obtain ⟨hp3, -, -⟩ := rankFive_card_of_original hH hU h3
  exact ⟨hp3, by omega, by omega⟩

end RowBoundsCertPool

section UnitaryL

theorem GGResHyp.false_of_unitary_rank_nine_exactThree_K (hT : GGTBTorAll)
    (hLift : GGTBTorLiftRows) (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hU : GGInnerDiagOnLabel
      (fun p lab => lab.tag = .twA ∧ lab.rank = 9 ∧ p ∣ 2 ^ lab.n + 1) p Bs K)
    (h3 : GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny)
    (hntwo : ¬ GGResRowAt ggRowTwoNode p J L) (hnSU2 : ¬ GGResRowAt ggRowSUCorank2 p J L)
    (hnSU3 : ¬ GGResRowAt ggRowSUCorank3 p J L) : False := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  obtain ⟨hpd, hcard, hlt⟩ :=
    hH.unitary_exactThree_K_card_data hLB hU (by norm_num) (by omega) h3
  have hp5 : p = 5 := by
    have h10 : p ∣ 2 * 5 := by simpa using hpd
    rcases (Nat.Prime.dvd_mul hp).mp h10 with h | h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h) hp2
    · exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h
  subst hp5
  have hst : LargeEvenStandardType 5 B x L := hH.1.1.2.2.2.2.2.2.2
  obtain ⟨lab, hlab, hhas, R, _, I, F, θ, hPl⟩ := largeEvenMarking_exists_hasLabel hst.1
  have hall : ∀ S : ℕ → LargeEvenLabel → Prop, S 5 lab → GGInnerDiagOnLabel S 5 Bs L := by
    intro S hS'
    refine largeEvenMarking_mono ?_ (ggInnerDiagOn_relabel hRig hH.2.2.1.1 hlab hhas)
    rintro lab' R' _ I' F' θ' ⟨h1, h2, h3⟩
    subst h1
    exact ⟨hS', h2, h3⟩
  have hs : LargeEvenSplit 5 lab := hPl.1
  by_cases htri : lab.tag = .triD4
  ·
    have hnot : ¬ GGTypeALabel 5 lab := by
      rintro (⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩) <;> rw [htri] at h <;> simp at h
    exact not_largeEvenMarking_smallExc hp hp2 (ggInnerDiagOnLabel_L_pRank_ge_three hH.1
      (hall (fun p lab => GGRootGenSmallExcLabel p lab ∧ GGRootGenOpenLabel p lab)
        ⟨Or.inr (Or.inl htri), ggLabPhiOneTwo_of_largeEvenSplit hs, hnot⟩))
  by_cases hU' : lab.tag = .twA ∧ 4 ≤ lab.rank
  ·
    have hpq : 5 ∣ 2 ^ lab.n + 1 := dvd_add_of_split_twisted (by norm_num) hs
      (by rw [hU'.1]; simp [LargeEvenUntwisted]) (by rw [hU'.1]; decide)
      (by rw [hU'.1]; decide)
    exact hH.not_exactThree_either_of_unitary_L_allfields
      (hall (fun p lab => lab.tag = .twA ∧ 4 ≤ lab.rank ∧ p ∣ 2 ^ lab.n + 1)
        ⟨hU'.1, hU'.2, hpq⟩) hntwo hnSU2 hnSU3 (Or.inr h3)
  obtain ⟨r, m, N, C, M, hrow⟩ := ggTBTorCov_five_of_split hlab hs htri hU'
  obtain ⟨hB, hBs⟩ := hH.card_le_of_tbTorRow_L hT hLift
    (hall (fun p lab => GGTBTorRowAt p lab r m N C M) hrow)
  have hpB := mul_card_le_card_of_lt hp hH.1.2.1.2.1 hlt
  rw [hcard] at hpB hBs
  have hr7 : r ≤ 7 := by
    have h1 : 5 ^ (r + 2) ≤ 5 ^ 9 := by
      calc 5 ^ (r + 2) = 5 * 5 ^ (r + 1) := by ring
        _ ≤ 5 * Nat.card B := Nat.mul_le_mul_left 5 hB
        _ ≤ 5 ^ 9 := hpB
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 5)).mp h1
    omega
  have hN8 : 8 ≤ N := by
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 5)).mp hBs
    omega
  exact hU' (ggTBTorRow_five_twA_of_bounds hrow hs hr7 hN8)

end UnitaryL

section Cert

theorem ggResLeaf_unitary_rank_nine_exactThree_K :
    GGResLeaf fun _ _ _ p _ _ Bs _ L _ J _ K =>
      GGInnerDiagOnLabel
        (fun p lab => lab.tag = .twA ∧ lab.rank = 9 ∧ 2 ≤ lab.n ∧
          p ∣ 2 ^ lab.n + 1) p Bs K ∧
      GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny ∧
      ¬ ggReservedRows p J L K ∧
      ¬ (GGResRowAt ggRowTwoNode p J L ∨ GGResRowAt ggRowTwoNode p J K) ∧
      ¬ (GGResRowAt ggRowCorank2C p J L ∨ GGResRowAt ggRowCorank2C p J K) ∧
      ¬ (GGResRowAt ggRowSUCorank2 p J L ∨ GGResRowAt ggRowSUCorank2 p J K) := by
  intro G _ _ p B Bs x L D J y K hH _ _ _ _ hP
  obtain ⟨hU, h3, hres, htwo, -, hSU2⟩ := hP
  exact (hH.false_of_unitary_rank_nine_exactThree_K (ggTBTorAll_of_remaining trivial)
    ggTBTorLiftRows_holds ggLabelRigidInput_holds
    (ggLBalanceInput_of_catalogueSchreier CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds)
    (GGInnerDiagOnLabel.mono_label (fun _ h => ⟨h.1, h.2.1, h.2.2.2⟩) hU) h3
    (fun h => htwo (Or.inl h)) (fun h => hSU2 (Or.inl h)) (fun h => hres (Or.inl h))).elim

end Cert

end CFSG.StandardType

end
