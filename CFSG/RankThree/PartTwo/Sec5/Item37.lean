module

public import CFSG.RankThree.PartTwo.Sec5.Hyp
import CFSG.RankThree.PartTwo.Sec5.Bender.Core
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartTwo.Source.MinimalFaithfulCentralProduct

public section

namespace CFSG.RankThree.PartTwo.Sec5

open CFSG
open scoped commutatorElement

universe u

namespace Bender

variable {X : Type*} [Group X]

theorem mem_centralizer_of_mem_inter {P S : Subgroup X}
    (hSP : S ≤ Subgroup.normalizer (P : Set X))
    (hinf : S ⊓ P = ⊥) {y : X} (hyP : y ∈ P) (hyS : y ∈ Subgroup.normalizer (S : Set X)) :
    y ∈ Subgroup.centralizer (S : Set X) := by
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  have h1 : y * s * y⁻¹ * s⁻¹ ∈ S :=
    S.mul_mem ((Subgroup.mem_normalizer_iff.mp hyS s).mp hs) (S.inv_mem hs)
  have h2 : y * s * y⁻¹ * s⁻¹ ∈ P := by
    have : s * y⁻¹ * s⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp (hSP hs) _).mp (P.inv_mem hyP)
    have h3 := P.mul_mem hyP this
    simpa [mul_assoc] using h3
  have h4 : y * s * y⁻¹ * s⁻¹ = 1 := by
    have : y * s * y⁻¹ * s⁻¹ ∈ S ⊓ P := Subgroup.mem_inf.mpr ⟨h1, h2⟩
    rw [hinf] at this
    exact Subgroup.mem_bot.mp this
  have h5 : y * s = s * y := by
    calc y * s = (y * s * y⁻¹ * s⁻¹) * (s * y) := by group
      _ = s * y := by rw [h4, one_mul]
  exact h5.symm

theorem le_centralizer_of_le_centralizer_elemAbelian [Finite X] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {A K P : Subgroup X} (hA : CFSG.Assembly.IsElemAbelian p A)
    (hK : ¬ p ∣ Nat.card K) (hP : IsPGroup p P) (hAP : A ≤ Subgroup.normalizer (P : Set X))
    (hKP : K ≤ Subgroup.normalizer (P : Set X)) (hKA : K ≤ Subgroup.centralizer (A : Set X))
    (hΩ : ∀ y ∈ (A ⊔ P) ⊓ Subgroup.centralizer (A : Set X), y ^ p = 1 → y ∈ A) :
    K ≤ Subgroup.centralizer (P : Set X) := by
  have hAcen : A ≤ Subgroup.centralizer (A : Set X) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy =>
      congrArg Subtype.val (hA.1.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)
  have hKQ : K ≤ Subgroup.centralizer
      ((P ⊓ Subgroup.centralizer (A : Set X) : Subgroup X) : Set X) := by
    by_cases hQ : P ⊓ Subgroup.centralizer (A : Set X) = ⊥
    · rw [hQ]
      intro k _
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hy
      rw [hy, one_mul, mul_one]
    obtain ⟨D, hDQ, -, hDexp, -, hDfaith⟩ :=
      exists_critical_faithful hp2 (hP.to_le inf_le_left) hQ
    refine hDfaith K hK (fun k hk => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hKP hk, Subgroup.le_normalizer (hKA hk)⟩) fun k hk => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have hdQ := Subgroup.mem_inf.mp (hDQ hd)
    have hdA : d ∈ A :=
      hΩ d (Subgroup.mem_inf.mpr ⟨(le_sup_right : P ≤ A ⊔ P) hdQ.1, hdQ.2⟩) (hDexp d hd)
    exact Subgroup.mem_centralizer_iff.mp (hKA hk) d hdA
  have hA3 : IsPGroup p A := isPGroup_of_isElemAbelian hA
  have hPA : IsPGroup p ((P ⊔ A : Subgroup X)) := IsPGroup.to_sup_of_normal_left' hP hA3 hAP
  have hKT : K ≤ Subgroup.normalizer ((P ⊔ A : Subgroup X) : Set X) := fun k hk =>
    Subgroup.inf_normalizer_le_normalizer_sup P A
      ⟨hKP hk, Subgroup.centralizer_le_normalizer _ (hKA hk)⟩
  have hfix : K ≤ Subgroup.centralizer
      (((P ⊔ A) ⊓ Subgroup.centralizer (A : Set X) : Subgroup X) : Set X) := by
    refine le_trans ?_ (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr
      (sup_inf_centralizer_le hAP hAcen)))
    rw [Source.centralizer_sup_eq]
    exact le_inf hKQ hKA
  have h := Source.le_centralizer_of_le_centralizer_inf_centralizer hPA hK le_sup_right hKT hKA hfix
  exact h.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left))

theorem bender [Finite X] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {A : Subgroup X}
    (hA : CFSG.Assembly.IsElemAbelian p A) :
    ∀ (n : ℕ) (S P : Subgroup X), Nat.card S + Nat.card P = n → ¬ p ∣ Nat.card S →
      A ≤ Subgroup.normalizer (S : Set X) → IsPGroup p P →
      A ≤ Subgroup.normalizer (P : Set X) → S ≤ Subgroup.normalizer (P : Set X) →
      (∀ y ∈ (A ⊔ P) ⊓ Subgroup.centralizer (A : Set X), y ^ p = 1 → y ∈ A) →
      ⁅P, S⁆ = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S P hn hS hAS hP hAP hSP hΩ
  by_contra hne
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hAcen : ∀ x ∈ A, ∀ y ∈ A, x ∈ Subgroup.centralizer ({y} : Set X) := fun x hx y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hAcomm x hx y hy)
  have hbot_iff : ∀ Q : Subgroup X, ⁅Q, S⁆ = ⊥ ↔ S ≤ Subgroup.centralizer (Q : Set X) := by
    intro Q
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff]
  have hPred : ∀ P' : Subgroup X, P' < P → A ≤ Subgroup.normalizer (P' : Set X) →
      S ≤ Subgroup.normalizer (P' : Set X) → S ≤ Subgroup.centralizer (P' : Set X) := by
    intro P' hP' hAP' hSP'
    have hlt : Nat.card S + Nat.card P' < n := by
      have := Subgroup.card_lt_of_lt hP'
      omega
    refine (hbot_iff P').mp (ih _ hlt S P' rfl hS hAS (hP.to_le hP'.le) hAP' hSP' fun y hy hy1 =>
      hΩ y ?_ hy1)
    have hy' := Subgroup.mem_inf.mp hy
    exact Subgroup.mem_inf.mpr ⟨sup_le_sup_left hP'.le A hy'.1, hy'.2⟩
  have hSred : ∀ S' : Subgroup X, S' < S → A ≤ Subgroup.normalizer (S' : Set X) →
      S' ≤ Subgroup.centralizer (P : Set X) := by
    intro S' hS' hAS'
    have hlt : Nat.card S' + Nat.card P < n := by
      have := Subgroup.card_lt_of_lt hS'
      omega
    have h := ih _ hlt S' P rfl (fun h => hS (h.trans (Subgroup.card_dvd_of_le hS'.le))) hAS'
      hP hAP (hS'.le.trans hSP) hΩ
    rwa [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff] at h
  have hSA : ¬ S ≤ Subgroup.centralizer (A : Set X) := fun hSA =>
    hne ((hbot_iff P).mpr
      (le_centralizer_of_le_centralizer_elemAbelian hp2 hA hS hP hAP hSP hSA hΩ))
  obtain ⟨a, haA, haS⟩ : ∃ a ∈ A, a ∉ Subgroup.centralizer (S : Set X) := by
    by_contra h
    push Not at h
    exact hSA (Subgroup.le_centralizer_iff.mp h)
  have hap : a ^ p = 1 := hA.2 a haA
  have ha1 : a ≠ 1 := by
    rintro rfl
    exact haS (Subgroup.one_mem _)
  have hacard : Nat.card (Subgroup.zpowers a) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime hap ha1]
  have hcopS : Nat.Coprime p (Nat.card S) := (Nat.Prime.coprime_iff_not_dvd hp).mpr hS
  have hSe : ∀ e ∈ A, e ∉ Subgroup.centralizer (S : Set X) →
      S ⊓ Subgroup.centralizer ({e} : Set X) ≤ Subgroup.centralizer (P : Set X) := by
    intro e heA heS
    refine hSred _ (lt_of_le_of_ne inf_le_left fun h => heS ?_) fun x hx =>
      Subgroup.inf_normalizer_le_normalizer_inf
        ⟨hAS hx, Subgroup.le_normalizer (hAcen x hx e heA)⟩
    have hSe' : S ≤ Subgroup.centralizer ({e} : Set X) := inf_eq_left.mp h
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact Subgroup.mem_centralizer_singleton_iff.mp (hSe' hs)
  have hza : CFSG.Assembly.IsElemAbelian p (Subgroup.zpowers a) :=
    isElemAbelian_of_le hA (Subgroup.zpowers_le.mpr haA)
  have hAa : A ≤ (A ⊓ Subgroup.centralizer (S : Set X)) ⊔ Subgroup.zpowers a := by
    intro b hbA
    by_contra hb
    have hbz : b ∉ Subgroup.zpowers a := fun h => hb (Subgroup.mem_sup_right h)
    obtain ⟨hEel, hEcard⟩ := isElemAbelian_sup_zpowers hza hbz (hA.2 b hbA)
      (fun x hx => hAcomm x (Subgroup.zpowers_le.mpr haA hx) b hbA)
    have hEA : Subgroup.zpowers a ⊔ Subgroup.zpowers b ≤ A :=
      sup_le (Subgroup.zpowers_le.mpr haA) (Subgroup.zpowers_le.mpr hbA)
    refine hne ((hbot_iff P).mpr (le_of_forall_inf_centralizer_le hp hEel
      (by rw [hEcard, hacard, sq]) (hEA.trans hAS) hcopS fun e he he1 => hSe e (hEA he) ?_))
    intro heS
    have he3 : e ^ p = 1 := hA.2 e (hEA he)
    by_cases hea : e ∈ Subgroup.zpowers a
    · apply haS
      have hze : Subgroup.zpowers e = Subgroup.zpowers a :=
        Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hea)
          (by rw [hacard, Nat.card_zpowers, orderOf_eq_prime he3 he1])
      have hamem : a ∈ Subgroup.zpowers e := hze ▸ Subgroup.mem_zpowers a
      exact (Subgroup.zpowers_le.mpr heS) hamem
    · apply hb
      obtain ⟨-, hcard2⟩ := isElemAbelian_sup_zpowers hza hea he3
        (fun x hx => hAcomm x (Subgroup.zpowers_le.mpr haA hx) e (hEA he))
      have hEeq : Subgroup.zpowers a ⊔ Subgroup.zpowers e =
          Subgroup.zpowers a ⊔ Subgroup.zpowers b :=
        Subgroup.eq_of_le_of_card_ge (sup_le le_sup_left (Subgroup.zpowers_le.mpr he))
          (by rw [hcard2, hEcard])
      have hbmem : b ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers e :=
        hEeq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
      have hle : Subgroup.zpowers a ⊔ Subgroup.zpowers e ≤
          (A ⊓ Subgroup.centralizer (S : Set X)) ⊔ Subgroup.zpowers a :=
        sup_le le_sup_right ((Subgroup.zpowers_le.mpr
          (Subgroup.mem_inf.mpr ⟨hEA he, heS⟩)).trans le_sup_left)
      exact hle hbmem
  have hSA0 : S ≤ Subgroup.centralizer
      ((A ⊓ Subgroup.centralizer (S : Set X) : Subgroup X) : Set X) :=
    Subgroup.le_centralizer_iff.mp inf_le_right
  have hA0P : A ⊓ Subgroup.centralizer (S : Set X) ≤ Subgroup.centralizer (P : Set X) := by
    by_contra hA0
    have hlt : P ⊓ Subgroup.centralizer
        ((A ⊓ Subgroup.centralizer (S : Set X) : Subgroup X) : Set X) < P :=
      lt_of_le_of_ne inf_le_left fun h =>
        hA0 (Subgroup.le_centralizer_iff.mp (inf_eq_left.mp h))
    have hAQ : A ≤ Subgroup.normalizer ((P ⊓ Subgroup.centralizer
        ((A ⊓ Subgroup.centralizer (S : Set X) : Subgroup X) : Set X) : Subgroup X) : Set X) :=
      fun x hx => Subgroup.inf_normalizer_le_normalizer_inf ⟨hAP hx, Subgroup.le_normalizer
        (Subgroup.mem_centralizer_iff.mpr fun y hy => hAcomm y (Subgroup.mem_inf.mp hy).1 x hx)⟩
    have hSQ : S ≤ Subgroup.normalizer ((P ⊓ Subgroup.centralizer
        ((A ⊓ Subgroup.centralizer (S : Set X) : Subgroup X) : Set X) : Subgroup X) : Set X) :=
      fun s hs => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨hSP hs, Subgroup.le_normalizer (hSA0 hs)⟩
    have h1 := hPred _ hlt hAQ hSQ
    apply hne
    apply (hbot_iff P).mpr
    have hA0p : IsPGroup p (A ⊓ Subgroup.centralizer (S : Set X) : Subgroup X) :=
      (isPGroup_of_isElemAbelian hA).to_le inf_le_left
    have hPA0 : IsPGroup p ((P ⊔ (A ⊓ Subgroup.centralizer (S : Set X)) : Subgroup X)) :=
      IsPGroup.to_sup_of_normal_left' hP hA0p (fun x hx => hAP (Subgroup.mem_inf.mp hx).1)
    have hKT : S ≤ Subgroup.normalizer
        ((P ⊔ (A ⊓ Subgroup.centralizer (S : Set X)) : Subgroup X) : Set X) := fun s hs =>
      Subgroup.inf_normalizer_le_normalizer_sup _ _
        ⟨hSP hs, Subgroup.centralizer_le_normalizer _ (hSA0 hs)⟩
    have hA0cen : A ⊓ Subgroup.centralizer (S : Set X) ≤ Subgroup.centralizer
        ((A ⊓ Subgroup.centralizer (S : Set X) : Subgroup X) : Set X) := fun x hx =>
      Subgroup.mem_centralizer_iff.mpr fun y hy =>
        hAcomm y (Subgroup.mem_inf.mp hy).1 x (Subgroup.mem_inf.mp hx).1
    have hfix : S ≤ Subgroup.centralizer (((P ⊔ (A ⊓ Subgroup.centralizer (S : Set X))) ⊓
        Subgroup.centralizer ((A ⊓ Subgroup.centralizer (S : Set X) : Subgroup X) : Set X) :
          Subgroup X) : Set X) := by
      refine le_trans ?_ (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr
        (sup_inf_centralizer_le (fun x hx => hAP (Subgroup.mem_inf.mp hx).1) hA0cen)))
      rw [Source.centralizer_sup_eq]
      exact le_inf h1 hSA0
    have h2 := Source.le_centralizer_of_le_centralizer_inf_centralizer hPA0 hS le_sup_right hKT
      hSA0 hfix
    exact h2.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left))
  have hPbot : P ≠ ⊥ := fun h => hne (by rw [h]; exact Subgroup.commutator_bot_left S)
  obtain ⟨D, hDP, hDnorm, hDexp, hDcl, hDfaith⟩ := exists_critical_faithful hp2 hP hPbot
  have hDeq : D = P := by
    by_contra hD
    have h1 := hPred D (lt_of_le_of_ne hDP hD) (fun x hx => hDnorm x (hAP hx))
      (fun s hs => hDnorm s (hSP hs))
    exact hne ((hbot_iff P).mpr (hDfaith S hS hSP h1))
  rw [hDeq] at hDexp hDcl
  have hcopSP : Nat.Coprime (Nat.card S) (Nat.card P) := by
    obtain ⟨k, hk⟩ := hP.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right _ hcopS.symm
  have hPS : ⁅P, S⁆ = P := by
    by_contra h
    have hle : ⁅P, S⁆ ≤ P := Subgroup.le_normalizer_iff_commutator_le_left.mp hSP
    have hA' : A ≤ Subgroup.normalizer ((⁅P, S⁆ : Subgroup X) : Set X) := fun x hx =>
      Source.mem_normalizer_commutator (hAP hx) (hAS hx)
    have hS' : S ≤ Subgroup.normalizer ((⁅P, S⁆ : Subgroup X) : Set X) := fun s hs =>
      Source.mem_normalizer_commutator (hSP hs) (Subgroup.le_normalizer hs)
    have h1 := hPred _ (lt_of_le_of_ne hle h) hA' hS'
    have h2 := commutator_le_commutator_commutator P S hSP hcopSP
    have h3 : ⁅⁅P, S⁆, S⁆ = ⊥ := (hbot_iff _).mpr h1
    exact hne (le_bot_iff.mp (h3 ▸ h2))
  have hinf : S ⊓ P = ⊥ := (Subgroup.disjoint_of_coprime_natCard hcopSP).eq_bot
  have hCP : P ⊓ Subgroup.centralizer ({a} : Set X) ≤ Subgroup.centralizer (S : Set X) := by
    intro y hy
    obtain ⟨hyP, hya⟩ := Subgroup.mem_inf.mp hy
    have hyA0 : y ∈ Subgroup.centralizer
        ((A ⊓ Subgroup.centralizer (S : Set X) : Subgroup X) : Set X) :=
      Subgroup.mem_centralizer_iff.mpr fun g hg =>
        (Subgroup.mem_centralizer_iff.mp (hA0P hg) y hyP).symm
    have hyza : y ∈ Subgroup.centralizer ((Subgroup.zpowers a : Subgroup X) : Set X) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      exact hya
    have hyA : y ∈ Subgroup.centralizer (A : Set X) := by
      have : y ∈ Subgroup.centralizer
          (((A ⊓ Subgroup.centralizer (S : Set X)) ⊔ Subgroup.zpowers a : Subgroup X) : Set X) := by
        rw [Source.centralizer_sup_eq]
        exact Subgroup.mem_inf.mpr ⟨hyA0, hyza⟩
      exact Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hAa) this
    have hyAA : y ∈ A := hΩ y (Subgroup.mem_inf.mpr ⟨(le_sup_right : P ≤ A ⊔ P) hyP, hyA⟩)
      (hDexp y hyP)
    exact mem_centralizer_of_mem_inter hSP hinf hyP (hAS hyAA)
  exact hPbot (bender_core hp2 hP hDexp hDcl hS hSP hPS (hAP haA) (hAS haA) hap
    (hSe a haA haS) hCP)

end Bender

theorem rank3II_3_7 : Item37.{u} := by
  intro X _ _ p hp hp2 A S P hA hS hAS hP hAP hSP hΩ
  exact Bender.bender hp hp2 hA _ S P rfl hS hAS hP hAP hSP hΩ

end CFSG.RankThree.PartTwo.Sec5
