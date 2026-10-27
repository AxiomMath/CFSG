module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22r

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem uc22p22r_card_inf_le (D : Data G) (h63 : UC6.R6_3 D) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {P : Subgroup G} (hPM : P ≤ D.M) (hPq : IsPGroup q ↥P) (hPexp : ∀ x ∈ P, x ^ q = 1)
    (hΓ : rankThreeGamma 1 q P ≤ D.M) {N : Subgroup G} (hN : rankThreeIsMaxTwoLocal N) (hNM : N ≠ D.M) :
    Nat.card ↥(P ⊓ N) ≤ q := by
  refine uc22p22f_card_le_of_lt_sq hq (hPq.to_le inf_le_left) ?_
  by_contra hge
  push Not at hge
  exact hNM (uc22p22f_two_le D h63 hq hq2 hPM hPq hPexp hΓ hN hge)

theorem uc22p22r_normalizer_le {q : ℕ} (hq : q.Prime) {M P A : Subgroup G} (hAP : A ≤ P)
    (hAcard : Nat.card ↥A = q) (hΓ : rankThreeGamma 1 q P ≤ M) : normalizer (A : Set G) ≤ M := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hrankA : 1 ≤ CFSG.Open.pRank q A := by
    haveI : IsCyclic ↥A := isCyclic_of_prime_card hAcard
    refine CFSG.SectionRank.le_pRank hq.one_lt le_rfl ⟨inferInstance, fun x hx => ?_⟩ ?_
    · have h1 : (⟨x, hx⟩ : ↥A) ^ Nat.card ↥A = 1 := pow_card_eq_one'
      rw [hAcard] at h1
      simpa using congrArg Subtype.val h1
    · rw [hAcard, pow_one]
  exact (CFSG.RankThreeCoreUniqueness.Helpers.gamma_normalizer_le 1 q P A hAP hrankA).trans hΓ

theorem uc22p22r_final2210_holds (D : Data G) (h63 : UC6.R6_3 D) : Final2210 D := by
  classical
  intro q hq hq2 P₁ P₂ A g z hP₁M hP₂M hP₁q hP₂q hP₁exp hP₂exp hP₁card hP₂card hΓ₁ hΓ₂ hAcard hAP₁ hAP₂
    hz1 hzO hzA hgz hgM hAne hcomm hD'M hAM₁ hD'N hAN
  haveI : Fact q.Prime := ⟨hq⟩
  have hq2le := hq.two_le
  set D' : Subgroup G := uniqueFourConj g A with hD'
  set P₂' : Subgroup G := uniqueFourConj g P₂ with hP₂'
  set M₁ : Subgroup G := uniqueFourConj g D.M with hM₁
  set M₂ : Subgroup G := uniqueFourConj g⁻¹ D.M with hM₂
  have hAq : IsPGroup q ↥A := hP₁q.to_le hAP₁
  have hD'q : IsPGroup q ↥D' := uc22p22r_isPGroup_conj hAq g
  have hD'card : Nat.card ↥D' = q := (uc22p22r_card_conj A g).trans hAcard
  have hP₂'q : IsPGroup q ↥P₂' := uc22p22r_isPGroup_conj hP₂q g
  have hP₂'card : Nat.card ↥P₂' = Nat.card ↥P₂ := uc22p22r_card_conj P₂ g
  have hAM : A ≤ D.M := hAP₁.trans hP₁M
  have hNA : normalizer (A : Set G) ≤ D.M := uc22p22r_normalizer_le hq hAP₁ hAcard hΓ₁
  have hM₁max : rankThreeIsMaxTwoLocal M₁ := uc22p22r_maxTwoLocal_conj D.maxLocal g
  have hM₂max : rankThreeIsMaxTwoLocal M₂ := uc22p22r_maxTwoLocal_conj D.maxLocal g⁻¹
  have hM₁ne : M₁ ≠ D.M := uc22p22r_conj_ne_of_not_mem D hgM
  have hM₂ne : M₂ ≠ D.M :=
    uc22p22r_conj_ne_of_not_mem D (fun h => hgM (by simpa using D.M.inv_mem h))
  have hP₁M₁ : Nat.card ↥(P₁ ⊓ M₁) ≤ q :=
    uc22p22r_card_inf_le D h63 hq hq2 hP₁M hP₁q hP₁exp hΓ₁ hM₁max hM₁ne
  have hP₂'M : Nat.card ↥(P₂' ⊓ D.M) ≤ q := by
    refine le_trans ?_ (uc22p22r_card_inf_le D h63 hq hq2 hP₂M hP₂q hP₂exp hΓ₂ hM₂max hM₂ne)
    let f : ↥(P₂' ⊓ D.M) → ↥(P₂ ⊓ M₂) := fun x =>
      ⟨g * (x : G) * g⁻¹, (uc22p22f_mem_conj P₂ g x).1 x.2.1, (uc22p22r_mem_conj_inv D.M g _).2 (by
        rw [show g⁻¹ * (g * (x : G) * g⁻¹) * g = x by group]
        exact x.2.2)⟩
    have hf : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      have := congrArg Subtype.val hab
      simpa [f] using this
    exact Nat.card_le_card_of_injective f hf
  have hAeq : A = P₁ ⊓ M₁ :=
    Subgroup.eq_of_le_of_card_ge (le_inf hAP₁ hAM₁) (hP₁M₁.trans hAcard.ge)
  have hD'P₂' : D' ≤ P₂' := uc22p22r_conj_mono hAP₂ g
  have hD'eq : D' = P₂' ⊓ D.M :=
    Subgroup.eq_of_le_of_card_ge (le_inf hD'P₂' hD'M) (hP₂'M.trans hD'card.ge)
  have hD'M₁ : D' ≤ M₁ := uc22p22r_conj_mono hAM g
  have hAD' : A ⊓ D' = ⊥ := by
    have hdvd : Nat.card ↥(A ⊓ D') ∣ q := hAcard ▸ Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime hq).1 hdvd with h1 | h1
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have h2 : A ⊓ D' = A :=
        Subgroup.eq_of_le_of_card_ge (inf_le_left : A ⊓ D' ≤ A) (by omega)
      have h3 : A ≤ D' := by
        rw [← h2]
        exact inf_le_right
      exact hAne (Subgroup.eq_of_le_of_card_ge h3 (by omega)).symm
  have hP₁D' : P₁ ⊓ D' = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : x ∈ A := by
      rw [hAeq]
      exact ⟨hx.1, hD'M₁ hx.2⟩
    have h2 : x ∈ A ⊓ D' := ⟨h1, hx.2⟩
    rw [hAD'] at h2
    exact h2
  have hP₂'A : P₂' ⊓ A = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : x ∈ D' := by
      rw [hD'eq]
      exact ⟨hx.1, hAM hx.2⟩
    have h2 : x ∈ A ⊓ D' := ⟨hx.2, h1⟩
    rw [hAD'] at h2
    exact h2
  have hAcent : A ≤ centralizer (D' : Set G) := fun a ha =>
    Subgroup.mem_centralizer_iff.2 fun d hd => (hcomm a ha d hd).symm
  have hAnorm : A ≤ normalizer (D' : Set G) :=
    hAcent.trans (Subgroup.centralizer_le_normalizer _)
  have hEmul : ((A ⊔ D' : Subgroup G) : Set G) = (A : Set G) * (D' : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right A D' hAnorm
  have hAE : A ≤ A ⊔ D' := le_sup_left
  have hDE : D' ≤ A ⊔ D' := le_sup_right
  have hP₁E : ¬ P₁ ≤ A ⊔ D' := by
    intro hle
    have hP₁A : P₁ ≤ A := by
      intro x hx
      have hx' : x ∈ ((A ⊔ D' : Subgroup G) : Set G) := hle hx
      rw [hEmul] at hx'
      obtain ⟨a, ha, d, hd, rfl⟩ := Set.mem_mul.1 hx'
      have hdP : d ∈ P₁ := by
        have := P₁.mul_mem (P₁.inv_mem (hAP₁ ha)) hx
        simpa using this
      have h1 : d ∈ P₁ ⊓ D' := ⟨hdP, hd⟩
      rw [hP₁D'] at h1
      have hd1 : d = 1 := h1
      rw [hd1, mul_one]
      exact ha
    have h1 : Nat.card ↥P₁ ≤ Nat.card ↥A := Subgroup.card_le_of_le hP₁A
    have h2 : q ^ 2 ≤ q := hP₁card.trans (h1.trans hAcard.le)
    nlinarith
  have hP₂'E : ¬ P₂' ≤ A ⊔ D' := by
    intro hle
    have hP₂'D : P₂' ≤ D' := by
      intro x hx
      have hx' : x ∈ ((A ⊔ D' : Subgroup G) : Set G) := hle hx
      rw [hEmul] at hx'
      obtain ⟨a, ha, d, hd, rfl⟩ := Set.mem_mul.1 hx'
      have haP : a ∈ P₂' := by
        have := P₂'.mul_mem hx (P₂'.inv_mem (hD'P₂' hd))
        simpa using this
      have h1 : a ∈ P₂' ⊓ A := ⟨haP, ha⟩
      rw [hP₂'A] at h1
      have ha1 : a = 1 := h1
      rw [ha1, one_mul]
      exact hd
    have h1 : Nat.card ↥P₂' ≤ Nat.card ↥D' := Subgroup.card_le_of_le hP₂'D
    have h2 : q ^ 2 ≤ q := (hP₂card.trans hP₂'card.ge).trans (h1.trans hD'card.le)
    nlinarith
  obtain ⟨x₁, hx₁P, hx₁N, hx₁E⟩ := uc22p22f_exists_normalizer_inf (q := q) (P := P₁) (X := D')
    (E := A ⊔ D') hP₁q hD'q hD'N hDE (sup_le (hAP₁.trans le_sup_right) le_sup_left) hP₁E
  have hR₁card : q ^ 2 ≤ Nat.card ↥(normalizer ((A ⊔ D' : Subgroup G) : Set G) ⊓ P₁) :=
    uc22p22f_card_ge_sq hq (hP₁q.to_le inf_le_right)
      (le_inf (hAE.trans Subgroup.le_normalizer) hAP₁) hAcard ⟨hx₁N, hx₁P⟩
      (fun h => hx₁E (hAE h))
  obtain ⟨x₂, hx₂P, hx₂N, hx₂E⟩ := uc22p22f_exists_normalizer_inf (q := q) (P := P₂') (X := A)
    (E := A ⊔ D') hP₂'q hAq hAN hAE (sup_le le_sup_left (hD'P₂'.trans le_sup_right)) hP₂'E
  have hR₂card : q ^ 2 ≤ Nat.card ↥(normalizer ((A ⊔ D' : Subgroup G) : Set G) ⊓ P₂') :=
    uc22p22f_card_ge_sq hq (hP₂'q.to_le inf_le_right)
      (le_inf (hDE.trans Subgroup.le_normalizer) hD'P₂') hD'card ⟨hx₂N, hx₂P⟩
      (fun h => hx₂E (hDE h))
  have hzA' : A ≤ centralizer ({z} : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    exact (hzA a ha).symm
  have hzD' : D' ≤ centralizer ({z} : Set G) := by
    intro d hd
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    have hza : z * (g * d * g⁻¹) = (g * d * g⁻¹) * z :=
      Subgroup.mem_centralizer_iff.1 (hzA' ((uc22p22f_mem_conj A g d).1 hd)) z (Set.mem_singleton z)
    have hzg : z * g = g * z := Subgroup.mem_centralizer_iff.1 hgz z (Set.mem_singleton z)
    have hzg' : g⁻¹ * z * g = z := by
      rw [mul_assoc, hzg]
      group
    calc z * d = (g⁻¹ * z * g) * d := by rw [hzg']
      _ = g⁻¹ * (z * (g * d * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * d * g⁻¹) * z) * g := by rw [hza]
      _ = d * (g⁻¹ * z * g) := by group
      _ = d * z := by rw [hzg']
  have hEz : A ⊔ D' ≤ centralizer ({z} : Set G) := sup_le hzA' hzD'
  obtain ⟨C, hCdef⟩ : ∃ C : Subgroup G, C = centralizer ((A ⊔ D' : Subgroup G) : Set G) :=
    ⟨_, rfl⟩
  have hzC : z ∈ C := by
    rw [hCdef, Subgroup.mem_centralizer_iff]
    intro e he
    exact (Subgroup.mem_centralizer_iff.1 (hEz he) z (Set.mem_singleton z)).symm
  have hCM : C ≤ D.M := by
    rw [hCdef]
    exact (Subgroup.centralizer_le (hAE : A ≤ A ⊔ D')).trans
      ((Subgroup.centralizer_le_normalizer _).trans hNA)
  have hOC : pCoreOf 2 D.M ⊓ C ≤ pCoreOf 2 C := by
    refine uc22p22f_le_pCoreOf inf_le_right
      ((uc22p22f_isPGroup_pCoreOf D.M).to_le inf_le_left) ?_
    intro k hk x hx
    exact ⟨uc22p22f_conj_mem_pCoreOf_self (hCM hk) hx.1, C.mul_mem (C.mul_mem hk hx.2) (C.inv_mem hk)⟩
  have hzS : z ∈ pCoreOf 2 C := hOC ⟨hzO, hzC⟩
  have hnormC : ∀ n ∈ normalizer ((A ⊔ D' : Subgroup G) : Set G), ∀ k ∈ C, n * k * n⁻¹ ∈ C := by
    intro n hn k hk
    rw [hCdef] at hk ⊢
    rw [Subgroup.mem_centralizer_iff] at hk ⊢
    intro e he
    have hn' : n⁻¹ ∈ normalizer ((A ⊔ D' : Subgroup G) : Set G) := Subgroup.inv_mem _ hn
    have he' : n⁻¹ * e * n ∈ (A ⊔ D' : Subgroup G) := by
      have := (Subgroup.mem_normalizer_iff.1 hn' e).1 he
      simpa using this
    have h1 := hk _ he'
    calc e * (n * k * n⁻¹) = n * ((n⁻¹ * e * n) * k) * n⁻¹ := by group
      _ = n * (k * (n⁻¹ * e * n)) * n⁻¹ := by rw [h1]
      _ = (n * k * n⁻¹) * e := by group
  have hnormS : ∀ r ∈ normalizer ((A ⊔ D' : Subgroup G) : Set G),
      r ∈ normalizer ((pCoreOf 2 C : Subgroup G) : Set G) := by
    intro r hr
    refine uc22p22f_mem_normalizer_pCoreOf (hnormC r hr) ?_
    intro k hk
    have := hnormC r⁻¹ (Subgroup.inv_mem _ hr) k hk
    simpa using this
  have hSne : pCoreOf 2 C ≠ ⊥ := by
    intro h
    apply hz1
    have := hzS
    rw [h] at this
    exact this
  have hloc : IsTwoLocal (normalizer ((pCoreOf 2 C : Subgroup G) : Set G)) :=
    ⟨pCoreOf 2 C, hSne, uc22p22f_isPGroup_pCoreOf C, rfl⟩
  obtain ⟨N, hNmax, hSN⟩ := uc22p22f_exists_maxTwoLocal_ge hloc
  have hNM : N = D.M := by
    refine uc22p22f_two_le D h63 hq hq2 hP₁M hP₁q hP₁exp hΓ₁ hNmax ?_
    refine hR₁card.trans (Subgroup.card_le_of_le ?_)
    intro r hr
    exact ⟨hr.2, hSN (hnormS r hr.1)⟩
  have hR₂D : normalizer ((A ⊔ D' : Subgroup G) : Set G) ⊓ P₂' ≤ D' := by
    intro r hr
    have hrN : r ∈ N := hSN (hnormS r hr.1)
    rw [hNM] at hrN
    have h1 : r ∈ P₂' ⊓ D.M := ⟨hr.2, hrN⟩
    rw [← hD'eq] at h1
    exact h1
  have h1 : q ^ 2 ≤ q := (hR₂card.trans (Subgroup.card_le_of_le hR₂D)).trans hD'card.le
  nlinarith

end CFSG.LocalAnalysis.UniquenessCase.UC22
