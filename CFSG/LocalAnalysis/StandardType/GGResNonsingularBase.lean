module

public import CFSG.LocalAnalysis.StandardType.GGTBXPlumb
public import CFSG.LocalAnalysis.StandardType.GGPZWeylType
public import CFSG.LocalAnalysis.StandardType.GGResFixedWeylCentralizer
public import CFSG.LocalAnalysis.StandardType.GGResThreeSingularDefs
public import CFSG.LocalAnalysis.StandardType.GGTwE6BadWeyl
import CFSG.LocalAnalysis.StandardType.GGNbrU63Setup

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem factorial_succ_ne_of_between {k a n : ℕ} (h1 : a.factorial < n)
    (h2 : n < (a + 1).factorial) : (k + 1).factorial ≠ n := by
  intro h
  rcases lt_trichotomy (k + 1) (a + 1) with hlt | heq | hgt
  · have := Nat.factorial_le (show k + 1 ≤ a by omega)
    omega
  · rw [heq] at h
    omega
  · have := Nat.factorial_le (show a + 1 ≤ k + 1 by omega)
    omega

theorem factorial_succ_ne_two_pow_mul_factorial {k r : ℕ} (hr : 2 ≤ r) :
    (k + 1).factorial ≠ 2 ^ r * r.factorial := by
  intro h
  have hkr : k = r := ggWeylTypeA_rank_eq_B hr h
  subst hkr
  rw [Nat.factorial_succ] at h
  have h1 : k + 1 = 2 ^ k := Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos k) h
  have h2 : k - 1 < 2 ^ (k - 1) := Nat.lt_two_pow_self
  have h3 : 2 ^ k = 2 * 2 ^ (k - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  omega

theorem factorial_succ_ne_two_pow_pred_mul_factorial {k r : ℕ} (hr : 4 ≤ r) :
    (k + 1).factorial ≠ 2 ^ (r - 1) * r.factorial := by
  intro h
  have hkr : k = r := ggWeylTypeA_rank_eq_D hr h
  subst hkr
  rw [Nat.factorial_succ] at h
  have h1 : k + 1 = 2 ^ (k - 1) := Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos k) h
  have h2 : k - 2 < 2 ^ (k - 2) := Nat.lt_two_pow_self
  have h3 : 2 ^ (k - 1) = 2 * 2 ^ (k - 2) := by
    rw [← pow_succ']
    congr 1
    omega
  omega

theorem two_pow_mul_factorial_ne_E6 {r : ℕ} (hr : 2 ≤ r) :
    2 ^ r * r.factorial ≠ 51840 := by
  intro h
  have hr6 : r ≤ 6 := by
    by_contra hr7
    have := ggWeylTypeB_order_le (show 7 ≤ r by omega)
    norm_num [Nat.factorial] at this
    omega
  interval_cases r <;> norm_num [Nat.factorial] at h

theorem two_pow_pred_mul_factorial_ne_E6 {r : ℕ} (hr : 4 ≤ r) :
    2 ^ (r - 1) * r.factorial ≠ 51840 := by
  intro h
  have hr7 : r ≤ 7 := by
    by_contra hr8
    have := ggWeylTypeD_order_le (show 8 ≤ r by omega)
    norm_num [Nat.factorial] at this
    omega
  interval_cases r <;> norm_num [Nat.factorial] at h

@[expose] def ggSingularWeylOrder (p n : ℕ) : Prop :=
  (∃ k, 1 ≤ k ∧ p ∣ k + 1 ∧ n = (k + 1).factorial) ∨ (p = 3 ∧ n = 51840)

theorem ggTBTorRowAt_singular_fields_of_card
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) {r m N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ}
    {M : CoxeterMatrix (Fin N)} (hrow : GGTBTorRowAt p lab r m N C M) (hM : GGIsWeylMatrix M)
    (hsing : ggSingularWeylOrder p (Nat.card M.Group)) : ggSingularBaseLabel p lab ∧ p ∣ ggTorM lab := by
  have hE6 : ∀ k : ℕ, (k + 1).factorial ≠ 51840 := fun k =>
    factorial_succ_ne_of_between (a := 8) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial])
  have hbad : ∀ n : ℕ, Nat.card M.Group = n → (∀ k : ℕ, (k + 1).factorial ≠ n) →
      n ≠ 51840 → False := by
    intro n hn hk hne
    rcases hsing with ⟨k, -, -, hk'⟩ | ⟨-, hk'⟩
    · exact hk k (hn ▸ hk').symm
    · exact hne (hn ▸ hk')
  cases hrow with
  | aDep h1 _ h3 h4 _ =>
    have hq2 : ∀ {a : ℕ}, 1 ≤ a → p ∣ a - 1 → p ∣ a + 1 → False := fun {a} ha hm hp' => by
      have h := Nat.dvd_sub hp' hm
      rw [show a + 1 - (a - 1) = 2 by omega] at h
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
    refine ⟨Or.inl ⟨h1, h3, ?_⟩, h4⟩
    rintro ⟨-, ⟨hA, hq⟩ | ⟨hA, hq⟩⟩
    · exact hq2 Nat.one_le_two_pow (by simpa [ggTorM, hA] using h4) hq
    · exact hq2 Nat.one_le_two_pow hq (by simpa [ggTorM, hA] using h4)
  | e6Three h1 h2 h3 => exact ⟨Or.inr ⟨h1, h2⟩, h2.symm ▸ h3⟩
  | e8Three _ _ =>
    exact (hbad _ l05nQW_ord_coxeterE8 (fun k => factorial_succ_ne_of_between (a := 12)
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])) (by norm_num)).elim
  | e8Ind _ _ _ =>
    exact (hbad _ l05nQW_ord_coxeterE8 (fun k => factorial_succ_ne_of_between (a := 12)
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])) (by norm_num)).elim
  | e7 _ _ =>
    exact (hbad _ l05nQW_ord_coxeterE7 (fun k => factorial_succ_ne_of_between (a := 9)
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])) (by norm_num)).elim
  | f4 _ _ _ =>
    exact (hbad _ l04fFRC_ord_card_coxeterF4 (fun k => factorial_succ_ne_of_between (a := 6)
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])) (by norm_num)).elim
  | relE6 _ _ =>
    exact (hbad _ l04fFRC_ord_card_coxeterF4 (fun k => factorial_succ_ne_of_between (a := 6)
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])) (by norm_num)).elim
  | g2 _ _ =>
    exact (hbad _ l04fFRC_card_coxeterG2 (fun k => factorial_succ_ne_of_between (a := 3)
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])) (by norm_num)).elim
  | relA5 _ _ =>
    have h48 : Nat.card (CoxeterMatrix.B 3).Group = 48 :=
      le_antisymm (card_coxeterB_le 3) (SpFrame.card_coxeterB_ge 3 (by norm_num))
    exact (hbad _ h48 (fun k => factorial_succ_ne_of_between (a := 4)
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])) (by norm_num)).elim
  | e6Ind h1 _ _ =>
    exfalso
    rcases hsing with ⟨k, -, -, hk'⟩ | ⟨h3, -⟩
    · exact hE6 k (l05nQW_ord_coxeterE6 ▸ hk').symm
    · exact h1 h3
  | aInd _ h2 _ =>
    exfalso
    rw [l05nK3a_card_coxeterA] at hsing
    rcases hsing with ⟨k, hk1, hpk, hk'⟩ | ⟨-, hk'⟩
    · exact h2 (ggWeylTypeA_rank_eq_A hk1 hk'.symm ▸ hpk)
    · exact hE6 _ hk'
  | c h1 _ =>
    exfalso
    have hr : 2 ≤ lab.rank := by
      rcases h1 with h | h <;> simp only [LargeEvenInLambda2, h] at hlab <;> exact hlab.2.1
    have hB : Nat.card (CoxeterMatrix.B lab.rank).Group = 2 ^ lab.rank * lab.rank.factorial :=
      le_antisymm (card_coxeterB_le _) (SpFrame.card_coxeterB_ge _ hr)
    rw [hB] at hsing
    rcases hsing with ⟨k, -, -, hk'⟩ | ⟨-, hk'⟩
    · exact factorial_succ_ne_two_pow_mul_factorial hr hk'.symm
    · exact two_pow_mul_factorial_ne_E6 hr hk'
  | relD h1 =>
    exfalso
    have hr : 1 ≤ lab.rank - 1 := by
      rcases h1 with ⟨h, -⟩ | ⟨h, -⟩ <;> simp only [LargeEvenInLambda2, h] at hlab <;> omega
    rcases (by omega : lab.rank - 1 = 1 ∨ 2 ≤ lab.rank - 1) with h1r | hr2
    · have hle : Nat.card (CoxeterMatrix.B (lab.rank - 1)).Group ≤ 2 := by
        simpa [h1r] using card_coxeterB_le (lab.rank - 1)
      rcases hsing with ⟨k, hk1, hpk, hk'⟩ | ⟨-, hk'⟩
      · have hkk : k = 1 := by
          by_contra hk
          have h6 : 6 ≤ (k + 1).factorial := Nat.factorial_le (show 3 ≤ k + 1 by omega)
          omega
        subst hkk
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hpk)
      · omega
    · have hB : Nat.card (CoxeterMatrix.B (lab.rank - 1)).Group =
          2 ^ (lab.rank - 1) * (lab.rank - 1).factorial :=
        le_antisymm (card_coxeterB_le _) (SpFrame.card_coxeterB_ge _ hr2)
      rw [hB] at hsing
      rcases hsing with ⟨k, -, -, hk'⟩ | ⟨-, hk'⟩
      · exact factorial_succ_ne_two_pow_mul_factorial hr2 hk'.symm
      · exact two_pow_mul_factorial_ne_E6 hr2 hk'
  | d h1 =>
    exfalso
    have hr : 3 ≤ lab.rank := by
      rcases h1 with ⟨h, -⟩ | ⟨h, -, hodd⟩
      · simp only [LargeEvenInLambda2, h] at hlab
        exact hlab.2
      · simp only [LargeEvenInLambda2, h] at hlab
        obtain ⟨j, hj⟩ := hodd
        omega
    rcases (by omega : lab.rank = 3 ∨ 4 ≤ lab.rank) with h3 | h4
    · have hwt := ggWeylTypeData_of_isWeylMatrix hM
      rw [Fintype.card_fin] at hwt
      generalize Nat.card (ggCoxeterMatrixD lab.rank).Group = n0 at hwt hsing
      rw [h3] at hwt
      have hn : n0 = 24 ∨ n0 = 48 := by
        rcases hwt with ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ |
            ⟨h, -⟩
        · left; simpa [Nat.factorial] using h
        · right; simpa [Nat.factorial] using h
        all_goals omega
      rcases hsing with ⟨k, hk1, hpk, hk'⟩ | ⟨-, hk'⟩
      · rcases hn with hn | hn
        · rw [hn] at hk'
          have hk3 : k = 3 := ggWeylTypeA_rank_eq_A (s := 3) hk1 (by rw [← hk']; rfl)
          subst hk3
          have h4 : p ∣ 2 ^ 2 := by norm_num; exact hpk
          exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h4))
        · exact factorial_succ_ne_of_between (a := 4) (by norm_num [Nat.factorial])
            (by norm_num [Nat.factorial]) (hk'.symm.trans hn)
      · rcases hn with hn | hn <;> omega
    · rw [OrthF3.card_coxeterD_eq _ h4] at hsing
      rcases hsing with ⟨k, -, -, hk'⟩ | ⟨-, hk'⟩
      · exact factorial_succ_ne_two_pow_pred_mul_factorial h4 hk'.symm
      · exact two_pow_pred_mul_factorial_ne_E6 h4 hk'

theorem ggInnerDiagOnLabel_row_of_not_singular_field
    {G : Type} [Group G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Bs X : Subgroup G}
    (h : GGInnerDiagOnLabel
      (fun p lab => GGTBTorCov p lab ∧ ¬ (ggSingularBaseLabel p lab ∧ p ∣ ggTorM lab))
      p Bs X) :
    GGInnerDiagOnLabel (fun p lab => ∃ (r m N : ℕ) (C : Matrix (Fin N) (Fin N) ℤ)
      (M : CoxeterMatrix (Fin N)), GGTBTorRowAt p lab r m N C M ∧
        ¬ ggSingularWeylOrder p (Nat.card M.Group)) p Bs X := by
  obtain ⟨hperf, lab, hlab, hraw⟩ := h
  refine ⟨hperf, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, ⟨⟨r, m, N, C, M, hrow⟩, hns⟩, hN, hind⟩
  obtain ⟨-, -, hM, -⟩ := l05nPlP1_row_facts hp hp2 hlab hrow
  exact ⟨hs, hna, θ, ⟨r, m, N, C, M, hrow,
    fun hc => hns (ggTBTorRowAt_singular_fields_of_card hp hp2 hlab hrow hM hc)⟩,
    hN, hind⟩

theorem ggTBTorRowAt_singular_of_card
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) {r m N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ}
    {M : CoxeterMatrix (Fin N)} (hrow : GGTBTorRowAt p lab r m N C M) (hM : GGIsWeylMatrix M)
    (hsing : ggSingularWeylOrder p (Nat.card M.Group)) : ggSingularBaseLabel p lab := by
  exact (ggTBTorRowAt_singular_fields_of_card hp hp2 hlab hrow hM hsing).1

theorem ggTD_card_automizer {G : Type} [Group G] [Finite G] {p m N : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hm : Odd m) (hpm : p ∣ m) {C : Matrix (Fin N) (Fin N) ℤ}
    {M : CoxeterMatrix (Fin N)} {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hS : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hTor : GGTorusTorData m N C M ↥X (ggGamma X hN).range) :
    Nat.card ↥(ggAutomizer X Bs) = Nat.card M.Group := by
  obtain ⟨w, hw⟩ := hTor
  obtain ⟨V, hVadd, hVmod, hι⟩ := exists_ggLinData (p := p) (G := G) (Bs := Bs) hBs
  let : AddCommGroup V := hVadd
  let : Module (ZMod p) V := hVmod
  obtain ⟨ι⟩ := hι
  obtain ⟨hnk, -⟩ := ggTD_linearData hm hpm hBs hS hN w hw V ι
  obtain ⟨e, -⟩ := ggTD_weyl hN hw hp2 hBs hnk
  exact (Nat.card_congr e.toEquiv).symm

theorem GGResLeviDatumCard.card_eq_factorial_of_typLADvd
    {k : ℕ} {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs X J Y : Subgroup G} {sel : Prop → Prop → Prop}
    (hD : GGResLeviDatumCard k p Bs X J Y sel (ggTypLADvd p)) :
    ∃ n : ℕ, 1 ≤ n ∧ p ∣ n + 1 ∧
      Nat.card ↥(ggAutomizer X Bs) = (n + 1).factorial := by
  obtain ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α, -, -, -, -, -, -,
    -, ⟨⟨n, e, hn1, hMe⟩, hpd⟩, -, -, -, -, -, ⟨fL, -⟩, -⟩ := hD
  have hΛ : Nat.card Λ = n := by rw [← Nat.card_congr e, Nat.card_fin]
  refine ⟨n, hn1, hΛ ▸ hpd, ?_⟩
  rw [← Nat.card_congr fL.toEquiv, hMe,
    Nat.card_congr ((CoxeterMatrix.A n).reindexGroupEquiv e).toEquiv, l05nK3a_card_coxeterA]

theorem GGResLeviDatumCard.singular_card
    {k : ℕ} {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs X J Y : Subgroup G} {sel : Prop → Prop → Prop}
    (hD : GGResLeviDatumCard k p Bs X J Y sel (ggTypLADvd p) ∨
      (p = 3 ∧ GGResLeviDatumCard k p Bs X J Y sel ggTypLE6)) :
    ggSingularWeylOrder p (Nat.card ↥(ggAutomizer X Bs)) := by
  rcases hD with hA | ⟨hp3, hE⟩
  · exact Or.inl hA.card_eq_factorial_of_typLADvd
  · obtain ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α, -, -, -, -, -, -,
      -, ⟨e, hMe⟩, -, -, -, -, -, ⟨fL, -⟩, -⟩ := hE
    refine Or.inr ⟨hp3, ?_⟩
    rw [← Nat.card_congr fL.toEquiv, hMe,
      Nat.card_congr (CoxeterMatrix.E₆.reindexGroupEquiv e).toEquiv, l05nQW_ord_coxeterE6]

theorem ggInnerDiagOnLabel_row_of_nonsingular
    {G : Type} [Group G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Bs X : Subgroup G}
    (h : GGInnerDiagOnLabel (fun p lab => GGTBTorCov p lab ∧ ¬ ggSingularBaseLabel p lab)
      p Bs X) :
    GGInnerDiagOnLabel (fun p lab => ∃ (r m N : ℕ) (C : Matrix (Fin N) (Fin N) ℤ)
      (M : CoxeterMatrix (Fin N)), GGTBTorRowAt p lab r m N C M ∧
        ¬ ggSingularWeylOrder p (Nat.card M.Group)) p Bs X := by
  obtain ⟨hperf, lab, hlab, hraw⟩ := h
  refine ⟨hperf, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, ⟨⟨r, m, N, C, M, hrow⟩, hns⟩, hN, hind⟩
  obtain ⟨-, -, hM, -⟩ := l05nPlP1_row_facts hp hp2 hlab hrow
  exact ⟨hs, hna, θ, ⟨r, m, N, C, M, hrow,
    fun hc => hns (ggTBTorRowAt_singular_of_card hp hp2 hlab hrow hM hc)⟩, hN, hind⟩

theorem GGResHyp.exists_row_card_automizer_L (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {P : ∀ (_r _m N : ℕ), Matrix (Fin N) (Fin N) ℤ → CoxeterMatrix (Fin N) → Prop}
    (hL : GGInnerDiagOnLabel (fun p lab => ∃ (r m N : ℕ) (C : Matrix (Fin N) (Fin N) ℤ)
      (M : CoxeterMatrix (Fin N)), GGTBTorRowAt p lab r m N C M ∧ P r m N C M) p Bs L) :
    ∃ (r m N : ℕ) (C : Matrix (Fin N) (Fin N) ℤ) (M : CoxeterMatrix (Fin N)),
      P r m N C M ∧ Nat.card ↥(ggAutomizer L Bs) = Nat.card M.Group := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hBs : IsElemAbelian p Bs := hH.1.tableB_facts.2.1
  have hS : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hH.1.2.1.2.2.2
  obtain ⟨_lab, r, m, N, C, M, R, _instR, θ, I, hN, hperf, hlab, hrow, hP, hBsI, hlift, hW, -⟩ :=
    l05nPlQ_marking_with (ggTBTorWRows_of_all hT) hLift hp2 P hL
  have hTor := hW ↥L (ggQuotHom θ) (ggGamma L hN).range
    (ggTorusTBGroup_of_L hH.1 hperf θ hN hBsI hlift)
  obtain ⟨hom, hpm, -, -⟩ := l05nPlP1_row_facts hp hp2 hlab hrow
  exact ⟨r, m, N, C, M, hP, ggTD_card_automizer hp2 hom hpm hBs hS hN hTor⟩

theorem GGResHyp.exists_row_card_automizer_K (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {P : ∀ (_r _m N : ℕ), Matrix (Fin N) (Fin N) ℤ → CoxeterMatrix (Fin N) → Prop}
    (hK : GGInnerDiagOnLabel (fun p lab => ∃ (r m N : ℕ) (C : Matrix (Fin N) (Fin N) ℤ)
      (M : CoxeterMatrix (Fin N)), GGTBTorRowAt p lab r m N C M ∧ P r m N C M) p Bs K) :
    ∃ (r m N : ℕ) (C : Matrix (Fin N) (Fin N) ℤ) (M : CoxeterMatrix (Fin N)),
      P r m N C M ∧ Nat.card ↥(ggAutomizer K Bs) = Nat.card M.Group := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hBs : IsElemAbelian p Bs := hH.1.tableB_facts.2.1
  have hS : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hH.1.2.1.2.2.2
  obtain ⟨_lab, r, m, N, C, M, R, _instR, θ, I, hN, hperf, hlab, hrow, hP, hBsI, hlift, hW, -⟩ :=
    l05nPlQ_marking_with (ggTBTorWRows_of_all hT) hLift hp2 P hK
  have hTor := hW ↥K (ggQuotHom θ) (ggGamma K hN).range
    (ggTorusTBGroup_of_nbr hH.1 hH.2.2.2.2.1 hperf θ hN hBsI hlift)
  obtain ⟨hom, hpm, -, -⟩ := l05nPlP1_row_facts hp hp2 hlab hrow
  exact ⟨r, m, N, C, M, hP, ggTD_card_automizer hp2 hom hpm hBs hS hN hTor⟩

theorem GGResHyp.false_of_singular_card_nonsingular_L
    (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hL : GGInnerDiagOnLabel (fun p lab => GGTBTorCov p lab ∧ ¬ ggSingularBaseLabel p lab)
      p Bs L)
    (hsing : ggSingularWeylOrder p (Nat.card ↥(ggAutomizer L Bs))) : False := by
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  obtain ⟨_, _, _, _, M, hP, hc⟩ := hH.exists_row_card_automizer_L hT hLift
    (ggInnerDiagOnLabel_row_of_nonsingular Fact.out hp2 hL)
  rw [hc] at hsing
  exact hP hsing

theorem GGResHyp.false_of_singular_card_nonsingular_K
    (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hK : GGInnerDiagOnLabel (fun p lab => GGTBTorCov p lab ∧ ¬ ggSingularBaseLabel p lab)
      p Bs K)
    (hsing : ggSingularWeylOrder p (Nat.card ↥(ggAutomizer K Bs))) : False := by
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  obtain ⟨_, _, _, _, M, hP, hc⟩ := hH.exists_row_card_automizer_K hT hLift
    (ggInnerDiagOnLabel_row_of_nonsingular Fact.out hp2 hK)
  rw [hc] at hsing
  exact hP hsing

theorem ggResExact3_false_of_card_L
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hfwd : ∀ b : ↥Bs, (∀ a ∈ ggAutomizer J Bs, a b = b) →
      (b : G) ∈ Subgroup.centralizer (J : Set G))
    (hL : ¬ ggSingularWeylOrder p (Nat.card ↥(ggAutomizer L Bs)))
    (hD : GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny) : False :=
  hL (GGResLeviDatumCard.singular_card (ggResExact3_typed_dichotomy_L_of_fixed hH hfwd hD).1)

theorem ggResExact3_false_of_card_K
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hfwd : ∀ b : ↥Bs, (∀ a ∈ ggAutomizer J Bs, a b = b) →
      (b : G) ∈ Subgroup.centralizer (J : Set G))
    (hK : ¬ ggSingularWeylOrder p (Nat.card ↥(ggAutomizer K Bs)))
    (hD : GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) : False :=
  hK (GGResLeviDatumCard.singular_card
    (ggResExact3_typed_dichotomy_K_base_of_fixed hH hfwd hD).1)

theorem ggIsTypeE6_of_card
    {ι : Type} {M : CoxeterMatrix ι} (hM : GGIsWeylMatrix M) (hc : Nat.card M.Group = 51840) :
    GGIsTypeE6 M := by
  rcases hM with ⟨n, e, -, hA | ⟨hn2, hB⟩ | ⟨hn4, hD⟩⟩ | ⟨e, hE⟩ | ⟨e, hE⟩ | ⟨e, hE⟩ | ⟨e, hE⟩ |
      ⟨e, hE⟩
  · subst hA
    rw [Nat.card_congr ((CoxeterMatrix.A n).reindexGroupEquiv e).toEquiv,
      l05nK3a_card_coxeterA] at hc
    exact absurd hc (factorial_succ_ne_of_between (a := 8) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]))
  · subst hB
    rw [Nat.card_congr ((CoxeterMatrix.B n).reindexGroupEquiv e).toEquiv,
      le_antisymm (card_coxeterB_le n) (SpFrame.card_coxeterB_ge n hn2)] at hc
    exact absurd hc (two_pow_mul_factorial_ne_E6 hn2)
  · subst hD
    rw [Nat.card_congr ((ggCoxeterMatrixD n).reindexGroupEquiv e).toEquiv,
      OrthF3.card_coxeterD_eq n hn4] at hc
    exact absurd hc (two_pow_pred_mul_factorial_ne_E6 hn4)
  · exact ⟨e, hE⟩
  · subst hE
    rw [Nat.card_congr (CoxeterMatrix.E₇.reindexGroupEquiv e).toEquiv,
      l05nQW_ord_coxeterE7] at hc
    norm_num at hc
  · subst hE
    rw [Nat.card_congr (CoxeterMatrix.E₈.reindexGroupEquiv e).toEquiv,
      l05nQW_ord_coxeterE8] at hc
    norm_num at hc
  · subst hE
    rw [Nat.card_congr (CoxeterMatrix.F₄.reindexGroupEquiv e).toEquiv,
      l04fFRC_ord_card_coxeterF4] at hc
    norm_num at hc
  · subst hE
    rw [Nat.card_congr (CoxeterMatrix.G₂.reindexGroupEquiv e).toEquiv,
      l04fFRC_card_coxeterG2] at hc
    norm_num at hc

theorem GGResLeviDatumCard.typLE6_of_card
    {k : ℕ} {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs X J Y : Subgroup G} {sel : Prop → Prop → Prop}
    {typ : ∀ {Λ Λ' : Type}, CoxeterMatrix Λ → CoxeterMatrix Λ' → Prop}
    (hc : Nat.card ↥(ggAutomizer X Bs) = 51840) (hD : GGResLeviDatumCard k p Bs X J Y sel typ) :
    GGResLeviDatumCard k p Bs X J Y sel ggTypLE6 := by
  obtain ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α, hS, hA1, hA3, hML,
    hCL, hMK, hCK, -, hlin, hrefl, hpairL, hpairK, hsel, ⟨fL, hfL⟩, hfK, hclosL, hclosK, hdel,
    hclosJ⟩ := hD
  have hcard : Nat.card ML.Group = 51840 := by rw [Nat.card_congr fL.toEquiv]; exact hc
  exact ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α, hS, hA1, hA3, hML,
    hCL, hMK, hCK, ggIsTypeE6_of_card hML hcard, hlin, hrefl, hpairL, hpairK, hsel, ⟨fL, hfL⟩,
    hfK, hclosL, hclosK, hdel, hclosJ⟩

@[expose] def ggE6TorusLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .E6 ∧ p ∣ 2 ^ lab.n - 1) ∨ (lab.tag = .twE6 ∧ p ≠ 3 ∧ p ∣ 2 ^ lab.n + 1)

theorem ggInnerDiagOnLabel_row_of_e6Torus
    {G : Type} [Group G] {p : ℕ} {Bs X : Subgroup G}
    (h : GGInnerDiagOnLabel ggE6TorusLabel p Bs X) :
    GGInnerDiagOnLabel (fun p lab => ∃ (r m N : ℕ) (C : Matrix (Fin N) (Fin N) ℤ)
      (M : CoxeterMatrix (Fin N)), GGTBTorRowAt p lab r m N C M ∧ Nat.card M.Group = 51840)
      p Bs X := by
  refine GGInnerDiagOnLabel.mono_label (fun lab hlab => ?_) h
  rcases hlab with ⟨htag, hdvd⟩ | ⟨htag, hp3, hdvd⟩
  · have hM : ggTorM lab = 2 ^ lab.n - 1 := by simp [ggTorM, htag]
    rw [← hM] at hdvd
    by_cases hp3 : p = 3
    · subst hp3
      exact ⟨_, _, _, _, _, GGTBTorRowAt.e6Three htag rfl hdvd, l05nQW_ord_coxeterE6⟩
    · exact ⟨_, _, _, _, _, GGTBTorRowAt.e6Ind hp3 (Or.inl htag) hdvd, l05nQW_ord_coxeterE6⟩
  · have hM : ggTorM lab = 2 ^ lab.n + 1 := by simp [ggTorM, htag]
    rw [← hM] at hdvd
    exact ⟨_, _, _, _, _, GGTBTorRowAt.e6Ind hp3 (Or.inr htag) hdvd, l05nQW_ord_coxeterE6⟩

theorem GGResHyp.levi_typLE6_of_e6Torus_L
    (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hL : GGInnerDiagOnLabel ggE6TorusLabel p Bs L)
    {k : ℕ} {sel : Prop → Prop → Prop}
    {typ : ∀ {Λ Λ' : Type}, CoxeterMatrix Λ → CoxeterMatrix Λ' → Prop}
    (hD : GGResLeviDatumCard k p Bs L J K sel typ) :
    GGResLeviDatumCard k p Bs L J K sel ggTypLE6 := by
  obtain ⟨_, _, _, _, _, hc, hcard⟩ :=
    hH.exists_row_card_automizer_L hT hLift (ggInnerDiagOnLabel_row_of_e6Torus hL)
  exact hD.typLE6_of_card (hcard.trans hc)

theorem GGResHyp.levi_typLE6_of_e6Torus_K
    (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hK : GGInnerDiagOnLabel ggE6TorusLabel p Bs K)
    {k : ℕ} {sel : Prop → Prop → Prop}
    {typ : ∀ {Λ Λ' : Type}, CoxeterMatrix Λ → CoxeterMatrix Λ' → Prop}
    (hD : GGResLeviDatumCard k p Bs K J L sel typ) :
    GGResLeviDatumCard k p Bs K J L sel ggTypLE6 := by
  obtain ⟨_, _, _, _, _, hc, hcard⟩ :=
    hH.exists_row_card_automizer_K hT hLift (ggInnerDiagOnLabel_row_of_e6Torus hK)
  exact hD.typLE6_of_card (hcard.trans hc)

theorem ggTorusNoFixTB_of_torW_of_diag {p r m N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ}
    {M : CoxeterMatrix (Fin N)} (hp : p.Prime) (hp2 : p ≠ 2) (hCd : ∀ k, C k k = 2)
    {R : Type} [Group R] {I : Set (MulAut R)} (h : GGTorusTorW p r m N C M R I) :
    ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
      GGTorusTBGroup p r R I L' ψ A →
        ∀ a ∈ A, (∀ n : L', GGTorusWeylElt p A n →
          MulAut.conj n * a * (MulAut.conj n)⁻¹ = a) → a = 1 := by
  intro L' _ _ ψ A hTB a ha hfix
  have hA : IsElemAbelian p A := hTB.2.2.2.1
  obtain ⟨w, hw⟩ := h L' ψ A hTB
  have hAT := hw.2.1
  have hαmul := hw.2.2.2.1
  have hpair := hw.2.2.2.2.2.2.2.1
  have hWaut := hw.2.2.2.2.2.2.2.2.1
  have hsep := hw.2.2.2.2.2.2.2.2.2.2.1
  refine hsep a (hAT ha) fun k => ?_
  have h1 := hfix (w.n k) (w.weylElt hw hA k)
  rw [hWaut k a (hAT ha)] at h1
  have h2 : MulAut.conj (w.cor k (w.α k a)) = 1 := inv_eq_one.mp (mul_eq_left.mp h1)
  have h3 := hpair k k (w.α k a)
  rw [h2, ggTor_alpha_one w.T (w.α k) (hαmul k), hCd k, zpow_two, ← pow_two] at h3
  have hpow : w.α k a ^ p = 1 := by
    rw [← ggTor_alpha_pow w.T (w.α k) (hαmul k) a (hAT ha), hA.2 a ha]
    exact ggTor_alpha_one w.T (w.α k) (hαmul k)
  have h4 : w.α k a ^ Nat.gcd 2 p = 1 := pow_gcd_eq_one.mpr ⟨h3.symm, hpow⟩
  rwa [((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)).gcd_eq_one, pow_one] at h4

theorem GGResHyp.fix_mem_centralizer_J_of_torW {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    {R : Type} [Group R] {I : Set (MulAut R)}
    (θ : ↥J ⧸ Subgroup.center ↥J ≃* R)
    (hBs3 : ∀ b ∈ Bs, ∃ φ ∈ I,
      LargeEvenInduces θ (fun j j' => (j' : G) = b⁻¹ * j * b) φ)
    {r m N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    (hLift : GGTorusLift p r R) (hTorW : GGTorusTorW p r m N C M R I)
    (hCd : ∀ k, C k k = 2)
    (h3 : p ^ 3 ≤ Nat.card (ggGamma J hH.Bs_le_normalizer_J).range) :
    ∀ b : Bs, (∀ φ ∈ ggAutomizer J Bs, φ b = b) →
      (b : G) ∈ Subgroup.centralizer (J : Set G) := by
  classical
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hN : Bs ≤ Subgroup.normalizer (J : Set G) := GGResHyp.Bs_le_normalizer_J hH
  have hBs : IsElemAbelian p Bs := hH.1.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  have hpre : LargeEvenStdSubPre p B x L D J := hH.1.2.2.1
  have hJperf : commutator ↥J = ⊤ := hpre.2.2.2.2.2.1.2.2.1
  have hBp : ∀ b : Bs, b ^ p = 1 := fun b => Subtype.ext (by simpa using hBs.2 b b.2)
  have hBc : ∀ a b : Bs, a * b = b * a := fun a b => by
    have := hBs.1
    exact mul_comm' a b
  have hA : IsElemAbelian p (ggGamma J hN).range :=
    isElemAbelian_range hBc hBp (ggGamma J hN)
  have hAI : ∀ a ∈ (ggGamma J hN).range, ∃ φ ∈ I,
      ∀ l : J, φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    rintro _ ⟨b, rfl⟩
    exact ⟨ggBeta J θ hN b, ggBeta_mem J θ hN hBs3 b,
      fun l => ggBeta_ggQuotHom J hN θ b l⟩
  have hTB : GGTorusTBGroup p r R I J (ggQuotHom θ) (ggGamma J hN).range :=
    ⟨ggQuotHom_surjective θ, by rw [ker_ggQuotHom], hJperf, hA, hAI,
      GGResHyp.pow_le_card_range_gamma_J_of_torusLift hH θ hLift, h3,
      GGResHyp.gamma_J_selfCent hH⟩
  exact fix_mem_centralizer_of_pointwise_noFix hp hBs hSC θ hN hBs3
    (ggTorusNoFixTB_of_torW_of_diag hp hp2 hCd hTorW J (ggQuotHom θ) (ggGamma J hN).range hTB)

theorem GGResHyp.fix_mem_centralizer_J_of_cov (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hJ : GGInnerDiagOnLabel GGTBTorCov p Bs J)
    (h3 : p ^ 3 ≤ Nat.card (ggGamma J hH.Bs_le_normalizer_J).range) :
    ∀ b : ↥Bs, (∀ a ∈ ggAutomizer J Bs, a b = b) →
      (b : G) ∈ Subgroup.centralizer (J : Set G) := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hJ' : GGInnerDiagOnLabel (fun p lab => ∃ (r m N : ℕ) (C : Matrix (Fin N) (Fin N) ℤ)
      (M : CoxeterMatrix (Fin N)), GGTBTorRowAt p lab r m N C M ∧ True) p Bs J :=
    GGInnerDiagOnLabel.mono_label (fun _ ⟨r, m, N, C, M, h⟩ => ⟨r, m, N, C, M, h, trivial⟩) hJ
  obtain ⟨_lab, r, m, N, C, M, R, _instR, θ, I, hN, -, hlab, hrow, -, hBsI, hlift, hW, -⟩ :=
    l05nPlQ_marking_with (ggTBTorWRows_of_all hT) hLift hp2 _ hJ'
  have hBs3 : ∀ b ∈ Bs, ∃ φ ∈ I,
      LargeEvenInduces θ (fun j j' => (j' : G) = b⁻¹ * j * b) φ := fun b hb =>
    ⟨_, hBsI b⁻¹ (Bs.inv_mem hb), largeEvenInduces_ggLAut_inv J θ (hN (Bs.inv_mem hb))⟩
  exact hH.fix_mem_centralizer_J_of_torW θ hBs3 hlift hW
    (l05nPlP1_row_facts hp hp2 hlab hrow).2.2.2.1 h3

theorem ggSingularWeylOrder_of_type
    {Λ : Type} [Fintype Λ] {M : CoxeterMatrix Λ} {H : Type} [Group H] (f : M.Group ≃* H)
    {p : ℕ} (h : (GGIsTypeA M ∧ p ∣ Fintype.card Λ + 1) ∨ (p = 3 ∧ GGIsTypeE6 M)) :
    ggSingularWeylOrder p (Nat.card H) := by
  rcases h with ⟨⟨n, e, hn1, hMe⟩, hpd⟩ | ⟨hp3, ⟨e, hMe⟩⟩
  · have hΛ : Fintype.card Λ = n := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_congr e, Nat.card_fin]
    refine Or.inl ⟨n, hn1, hΛ ▸ hpd, ?_⟩
    rw [← Nat.card_congr f.toEquiv, hMe,
      Nat.card_congr ((CoxeterMatrix.A n).reindexGroupEquiv e).toEquiv, l05nK3a_card_coxeterA]
  · refine Or.inr ⟨hp3, ?_⟩
    rw [← Nat.card_congr f.toEquiv, hMe,
      Nat.card_congr (CoxeterMatrix.E₆.reindexGroupEquiv e).toEquiv, l05nQW_ord_coxeterE6]

theorem GGResHyp.pow_three_le_card_gamma_J_of_twoLocalRank {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K) (hm : 5 ≤ LargeEvenTwoLocalRank p G) :
    p ^ 3 ≤ Nat.card (ggGamma J hH.Bs_le_normalizer_J).range :=
  (Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by omega)).trans
    (hH.1.pow_le_card_gamma_J hH.Bs_le_normalizer_J)

theorem GGResHyp.succ_le_twoLocalRank_of_torusLift_L {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K) (hL : commutator ↥L = ⊤)
    {R : Type} [Group R] (θ : ↥L ⧸ Subgroup.center ↥L ≃* R) {r : ℕ}
    (hlift : GGTorusLift p r R) : r + 1 ≤ LargeEvenTwoLocalRank p G := by
  have hS : LargeEvenSStar p B x L := hH.1.1.2.2.2.2.2.2.1
  exact succ_le_twoLocalRank_of_torusLift Fact.out hS.2.2.2.1.1 (hS.1.1.2 x hS.2.1) hS.2.2.1 hL
    θ hlift

theorem GGResHyp.succ_le_twoLocalRank_of_torusLift_K {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K) (hK : commutator ↥K = ⊤)
    {R : Type} [Group R] (θ : ↥K ⧸ Subgroup.center ↥K ≃* R) {r : ℕ}
    (hlift : GGTorusLift p r R) : r + 1 ≤ LargeEvenTwoLocalRank p G := by
  have hS : LargeEvenSHat p B y K := hH.2.2.2.2.1.1
  exact succ_le_twoLocalRank_of_torusLift Fact.out hS.2.2.2.1 (hS.1.1.2 y hS.2.1) hS.2.2.1 hK
    θ hlift

theorem GGResHyp.five_le_twoLocalRank_of_row_L (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hL : GGInnerDiagOnLabel (fun p lab => ∃ (r m N : ℕ) (C : Matrix (Fin N) (Fin N) ℤ)
      (M : CoxeterMatrix (Fin N)), GGTBTorRowAt p lab r m N C M ∧ 4 ≤ r) p Bs L) :
    5 ≤ LargeEvenTwoLocalRank p G := by
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  obtain ⟨_, _, _, _, _, _, _, _, θ, _, _, hperf, -, -, hr4, -, hlift, -, -⟩ :=
    l05nPlQ_marking_with (ggTBTorWRows_of_all hT) hLift hp2 _ hL
  have := hH.succ_le_twoLocalRank_of_torusLift_L hperf θ hlift
  omega

theorem GGResHyp.levi_typLE6_of_twE6_qplus_L
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    [Fact (Nat.Prime 3)]
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hL : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1) 3 Bs L)
    {k : ℕ} {sel : Prop → Prop → Prop}
    {typ : ∀ {Λ Λ' : Type}, CoxeterMatrix Λ → CoxeterMatrix Λ' → Prop}
    (hD : GGResLeviDatumCard k 3 Bs L J K sel typ) :
    GGResLeviDatumCard k 3 Bs L J K sel ggTypLE6 := by
  obtain ⟨e, -⟩ := ggTwE6Bad_weylOfType hH
    (GGInnerDiagOnLabel.mono_label (fun _ h => ⟨h.1, rfl, h.2⟩) hL)
  have hcard : Nat.card (ggAutomizer L Bs) = 51840 :=
    (Nat.card_congr e.toEquiv).symm.trans l05nQW_ord_coxeterE6
  exact hD.typLE6_of_card hcard

end CFSG.StandardType
