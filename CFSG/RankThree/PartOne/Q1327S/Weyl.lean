module

public import CFSG.RankThree.PartOne.S12.Hyp
public import CFSG.RankThree.PartOne.Assembly

public section

namespace CFSG.RankThree.PartOne.Q1327S

open CFSG CFSG.RankThree.PartOne

section Weyl

variable {Q : Type} [Group Q]

theorem coe_normalizerMonoidHom_apply' {E : Subgroup Q} {g : Q}
    (hg : g ∈ Subgroup.normalizer (E : Set Q)) (e : E) :
    ((E.normalizerMonoidHom ⟨g, hg⟩ e : E) : Q) = g * e * g⁻¹ := rfl

theorem torusImage_top_eq_range' (E : Subgroup Q) :
    torusImage E ⊤ = E.normalizerMonoidHom.range := by
  unfold torusImage
  rw [Subgroup.top_subgroupOf, MonoidHom.range_eq_map]

theorem card_torusImage_top_mul (E : Subgroup Q) :
    Nat.card (torusImage E ⊤) * Nat.card (Subgroup.centralizer (E : Set Q)) =
      Nat.card (Subgroup.normalizer (E : Set Q)) := by
  have h := Subgroup.card_ker_mul_card_range E.normalizerMonoidHom
  rw [Subgroup.normalizerMonoidHom_ker] at h
  have hle := Subgroup.centralizer_le_normalizer (E : Set Q)
  have hc : Nat.card ((Subgroup.centralizer (E : Set Q)).subgroupOf
      (Subgroup.normalizer (E : Set Q))) = Nat.card (Subgroup.centralizer (E : Set Q)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  rw [hc, ← torusImage_top_eq_range', mul_comm] at h
  exact h

variable {p : ℕ} [Fact p.Prime]

theorem mem_centralizer_of_pElement {E : Subgroup Q} (hW : ¬ p ∣ Nat.card (torusImage E ⊤))
    {n : Q} (hn : n ∈ Subgroup.normalizer (E : Set Q)) {k : ℕ} (hk : n ^ (p ^ k) = 1) :
    n ∈ Subgroup.centralizer (E : Set Q) := by
  set w := E.normalizerMonoidHom ⟨n, hn⟩ with hw
  have hwmem : w ∈ torusImage E ⊤ := by
    rw [torusImage_top_eq_range']
    exact ⟨⟨n, hn⟩, rfl⟩
  have h1 : orderOf w ∣ Nat.card (torusImage E ⊤) := Subgroup.orderOf_dvd_natCard _ hwmem
  have h2 : orderOf w ∣ p ^ k := by
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [hw, ← map_pow]
    have : (⟨n, hn⟩ : Subgroup.normalizer (E : Set Q)) ^ (p ^ k) = 1 := Subtype.ext hk
    rw [this, map_one]
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).1 h2
  have hj0 : j = 0 := by
    by_contra hj0
    apply hW
    rw [hj] at h1
    exact (dvd_pow_self p hj0).trans h1
  rw [hj0, pow_zero, orderOf_eq_one_iff] at hj
  rw [Subgroup.mem_centralizer_iff]
  intro e he
  have h3 := congrArg (fun φ : MulAut E => ((φ ⟨e, he⟩ : E) : Q)) hj
  simp only [MulAut.one_apply] at h3
  rw [hw, coe_normalizerMonoidHom_apply'] at h3
  calc e * n = (n * e * n⁻¹) * n := by rw [h3]
    _ = n * e := by group

theorem le_centralizer_of_weyl_coprime {E P : Subgroup Q} [Finite Q] [IsElementaryAbelian p E]
    (hmax : ∀ y ∈ Subgroup.centralizer (E : Set Q), y ^ p = 1 → y ∈ E)
    (hW : ¬ p ∣ Nat.card (torusImage E ⊤)) (hP : IsPGroup p P) (hEP : E ≤ P) :
    P ≤ Subgroup.centralizer (E : Set Q) := by
  classical
  set R : Subgroup Q := P ⊓ Subgroup.centralizer (E : Set Q) with hR
  have hEpow : ∀ e ∈ E, e ^ p = 1 := fun e he => elemPow_eq_one_of_isElementaryAbelian e he
  have hEcomm : ∀ e ∈ E, ∀ f ∈ E, e * f = f * e := fun e he f hf =>
    congrArg Subtype.val ((IsMulCommutative.is_comm (M := E)).comm ⟨e, he⟩ ⟨f, hf⟩)
  have hER : ∀ e ∈ E, e ∈ R := fun e he =>
    ⟨hEP he, Subgroup.mem_centralizer_iff.2 fun f hf => hEcomm f hf e he⟩
  have step1 : ∀ n ∈ P, n ∈ Subgroup.normalizer (E : Set Q) →
      n ∈ Subgroup.centralizer (E : Set Q) := by
    intro n hnP hnN
    obtain ⟨k, hk⟩ := hP ⟨n, hnP⟩
    exact mem_centralizer_of_pElement hW hnN (k := k) (by simpa using congrArg Subtype.val hk)
  have conjE : ∀ m ∈ P, (∀ r ∈ R, m * r * m⁻¹ ∈ R) → ∀ e ∈ E, m * e * m⁻¹ ∈ E := by
    intro m hmP hmR e he
    apply hmax
    · exact (hmR e (hER e he)).2
    · calc (m * e * m⁻¹) ^ p = m * e ^ p * m⁻¹ := by rw [conj_pow]
        _ = 1 := by rw [hEpow e he]; group
  have step2 : ∀ n ∈ P, (∀ r ∈ R, n * r * n⁻¹ ∈ R) → (∀ r ∈ R, n⁻¹ * r * n ∈ R) →
      n ∈ Subgroup.normalizer (E : Set Q) := by
    intro n hnP h1 h2
    rw [Subgroup.mem_normalizer_iff]
    intro e
    constructor
    · exact fun he => conjE n hnP h1 e he
    · intro he
      have := conjE n⁻¹ (P.inv_mem hnP) (by simpa using h2) _ he
      simpa [mul_assoc] using this
  have hRP : P ≤ R := by
    have : Finite P := inferInstance
    have : Group.IsNilpotent P := hP.isNilpotent
    have hnc := Group.normalizerCondition_of_isNilpotent (G := P)
    rw [normalizerCondition_iff_only_full_group_self_normalizing] at hnc
    set R' : Subgroup P := R.subgroupOf P with hR'
    have hself : Subgroup.normalizer (R' : Set P) = R' := by
      refine le_antisymm (fun x hx => ?_) (Subgroup.le_normalizer)
      rw [Subgroup.mem_normalizer_iff] at hx
      have hconj : ∀ r ∈ R, (x : Q) * r * (x : Q)⁻¹ ∈ R := by
        intro r hr
        have hrP : r ∈ P := hr.1
        have := (hx ⟨r, hrP⟩).1 (Subgroup.mem_subgroupOf.2 hr)
        exact Subgroup.mem_subgroupOf.1 this
      have hconj' : ∀ r ∈ R, (x : Q)⁻¹ * r * (x : Q) ∈ R := by
        intro r hr
        have hrP : r ∈ P := hr.1
        have h1 : (⟨(x : Q)⁻¹ * r * (x : Q), P.mul_mem (P.mul_mem (P.inv_mem x.2) hrP) x.2⟩ : P)
            ∈ R' := by
          rw [hx, hR', Subgroup.mem_subgroupOf]
          simpa [mul_assoc] using hr
        exact Subgroup.mem_subgroupOf.1 h1
      have hxN := step2 (x : Q) x.2 hconj hconj'
      have hxC := step1 (x : Q) x.2 hxN
      exact Subgroup.mem_subgroupOf.2 ⟨x.2, hxC⟩
    have htop := hnc R' hself
    intro x hx
    have : (⟨x, hx⟩ : P) ∈ R' := htop ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.1 this
  exact fun x hx => (hRP hx).2

theorem card_eq_six_of_perm3 {W : Type*} [Group W] (φ : W ≃* Equiv.Perm (Fin 3)) :
    Nat.card W = 6 := by
  rw [Nat.card_congr φ.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  rfl

theorem not_dvd_card_of_perm3 {W : Type*} [Group W] (φ : W ≃* Equiv.Perm (Fin 3)) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) : ¬ p ∣ Nat.card W := by
  rw [card_eq_six_of_perm3 φ]
  intro h
  have h1 : p ≤ 6 := Nat.le_of_dvd (by norm_num) h
  interval_cases p
  · omega
  · exact absurd hp (by norm_num)

theorem pow_six_eq_one_of_perm3 {W : Type*} [Group W] (φ : W ≃* Equiv.Perm (Fin 3)) (w : W) :
    w ^ 6 = 1 := by
  have := pow_card_eq_one' (G := W) (x := w)
  rwa [card_eq_six_of_perm3 φ] at this

theorem not_nonempty_perm3_of_pow_six {E : Subgroup Q} {h : Q}
    (hh : h ∈ Subgroup.normalizer (E : Set Q)) {e : Q} (he : e ∈ E)
    (hne : h ^ 6 * e * (h ^ 6)⁻¹ ≠ e) :
    ¬ Nonempty (torusImage E ⊤ ≃* Equiv.Perm (Fin 3)) := by
  rintro ⟨φ⟩
  have hw : E.normalizerMonoidHom ⟨h, hh⟩ ∈ torusImage E ⊤ := by
    rw [torusImage_top_eq_range']
    exact ⟨⟨h, hh⟩, rfl⟩
  have h6 : (⟨E.normalizerMonoidHom ⟨h, hh⟩, hw⟩ : torusImage E ⊤) ^ 6 = 1 :=
    pow_six_eq_one_of_perm3 φ _
  have h7 : E.normalizerMonoidHom ⟨h, hh⟩ ^ 6 = 1 := congrArg Subtype.val h6
  have h8 := congrArg (fun ψ : MulAut E => ((ψ ⟨e, he⟩ : E) : Q)) h7
  rw [← map_pow] at h8
  have h9 : (⟨h, hh⟩ : Subgroup.normalizer (E : Set Q)) ^ 6 =
      ⟨h ^ 6, pow_mem hh 6⟩ := Subtype.ext (by simp)
  rw [h9] at h8
  apply hne
  have h10 := coe_normalizerMonoidHom_apply' (E := E) (pow_mem hh 6) ⟨e, he⟩
  simp only [MulAut.one_apply] at h8
  rw [h10] at h8
  exact h8

theorem factorization_eq_two {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) (h2 : p ^ 2 ∣ n)
    (h3 : ¬ p ^ 3 ∣ n) : n.factorization p = 2 := by
  have h1 := (Nat.Prime.pow_dvd_iff_le_factorization hp hn).1 h2
  have h4 : ¬ 3 ≤ n.factorization p := fun h =>
    h3 ((Nat.Prime.pow_dvd_iff_le_factorization hp hn).2 h)
  omega

end Weyl

end CFSG.RankThree.PartOne.Q1327S
