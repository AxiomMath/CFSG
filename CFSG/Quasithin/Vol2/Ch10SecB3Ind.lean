module

public import CFSG.Quasithin.Vol2.Ch10SecB3Aut
public import CFSG.Quasithin.Vol2.Ch10SecB3Comm
public import CFSG.Quasithin.Vol2.Ch11SecB21Hall

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

@[expose] def HallFaithful (T L I H : Subgroup G) : Prop :=
  ∀ B : Subgroup G, QuasithinUnique.Lin2.IsHallTwoPrimeOf B (H ⊓ fsuM T L) →
    ∀ b ∈ B, (∀ l ∈ fsuL0 T L,
      b * l * b⁻¹ * l⁻¹ ∈ Subgroup.centralizer (fsuVM T L I : Set G)) → b = 1

theorem mem_normalizer_of_pow_prime (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) {b : G} (hbM : b ∈ fsuM T L)
    {p : ℕ} (hp : Odd p) (hbp : b ^ p = 1) : b ∈ Subgroup.normalizer (L : Set G) := by
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp hyp.not_normal
  have htM : t ∈ fsuM T L := SecA.le_fsuM T L ht
  have hsq : b * b ∈ Subgroup.normalizer (L : Set G) := by
    rcases SecA.conjugate_eq_or h37 h38 hyp ht htn hbM with h | h
    · have hb := SecA.conjugate_eq_self_iff.mp h
      exact Subgroup.mul_mem _ hb hb
    · rw [← SecA.conjugate_eq_self_iff, ← SecA.conjugate_conjugate, h,
        SecA.conjugate_conjugate]
      rcases SecA.conjugate_eq_or h37 h38 hyp ht htn (Subgroup.mul_mem _ htM hbM) with h' | h'
      · exact h'
      · exfalso
        apply htn
        have h1 := SecA.mul_inv_mem_normalizer_of_conjugate_eq h'
        have h2 := SecA.mul_inv_mem_normalizer_of_conjugate_eq h
        have e : t = t * b * t⁻¹ * (b * t⁻¹)⁻¹ := by group
        rw [e]
        exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ h2)
  obtain ⟨k, hk⟩ := hp
  have e : b = (b * b) ^ (k + 1) := by
    rw [← pow_two, ← pow_mul]
    calc b = b ^ p * b := by rw [hbp, one_mul]
      _ = b ^ (2 * (k + 1)) := by rw [← pow_succ, hk]; ring_nf
  rw [e]
  exact Subgroup.pow_mem _ hsq _

theorem mem_normalizer_conjugate_of_pow_prime (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) {b : G} (hbM : b ∈ fsuM T L)
    {p : ℕ} (hp : Odd p) (hbp : b ^ p = 1) {t : G} (ht : t ∈ T) :
    b ∈ Subgroup.normalizer (CFSG.conjugate L t : Set G) := by
  have htM : t ∈ fsuM T L := SecA.le_fsuM T L ht
  have h1 : t * b * t⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
    mem_normalizer_of_pow_prime h37 h38 hyp
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ htM hbM) (Subgroup.inv_mem _ htM)) hp
      (by rw [conj_pow, hbp, mul_one, mul_inv_cancel])
  rw [← SecA.conjugate_eq_self_iff, SecA.conjugate_conjugate]
  have e : t * b = t * b * t⁻¹ * t := by group
  rw [e, ← SecA.conjugate_conjugate, SecA.conjugate_eq_self_iff.mpr h1]

omit [Finite G] in
theorem finite_mulAut (Q : Type*) [Group Q] [Finite Q] : Finite (MulAut Q) :=
  Finite.of_injective (fun φ : MulAut Q => (φ : Q → Q)) fun _ _ h => MulEquiv.ext (congrFun h)

theorem conj_mem_pCoreOf_of_pow_prime {K : Subgroup G} {b : G}
    (hb : b ∈ Subgroup.normalizer (K : Set G)) {p : ℕ} (hp : p.Prime) (hbp : b ^ p = 1)
    (hpK : ¬ p ∣ Nat.card (MulAut (↥K ⧸ CFSG.pCore 2 ↥K))) :
    ∀ k ∈ K, b * k * b⁻¹ * k⁻¹ ∈ pCoreOf 2 K := by
  have := finite_mulAut (↥K ⧸ CFSG.pCore 2 ↥K)
  set β : MulAut ↥K := conjAct K ⟨b, hb⟩ with hβ
  have hα : autQuot2 ↥K β = 1 := by
    refine eq_one_of_pow_prime_eq_one hp ?_ hpK
    rw [← map_pow, hβ, ← map_pow]
    have h1 : (⟨b, hb⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ p = 1 :=
      Subtype.ext (by simpa using hbp)
    rw [h1, map_one, map_one]
  intro k hk
  have h1 := congrArg (fun φ : MulAut (↥K ⧸ CFSG.pCore 2 ↥K) =>
    φ ((⟨k, hk⟩ : ↥K) : ↥K ⧸ CFSG.pCore 2 ↥K)) hα
  simp only [autQuot2_mk, MulAut.one_apply] at h1
  rw [QuotientGroup.eq_iff_div_mem] at h1
  refine ⟨_, h1, ?_⟩
  simp only [Subgroup.coe_subtype, div_eq_mul_inv, Subgroup.coe_mul, Subgroup.coe_inv, hβ,
    conjAct_apply_coe]

omit [Finite G] in
theorem mem_cenL0_of_sup {b : G} (hbM : b ∈ fsuM T L) {K₁ K₂ : Subgroup G}
    (hL0 : fsuL0 T L = K₁ ⊔ K₂)
    (h₁ : ∀ l ∈ K₁, b * l * b⁻¹ * l⁻¹ ∈ Subgroup.centralizer (fsuVM T L I : Set G))
    (h₂ : ∀ l ∈ K₂, b * l * b⁻¹ * l⁻¹ ∈ Subgroup.centralizer (fsuVM T L I : Set G)) :
    b ∈ cenL0 T L I := by
  have hK₁ : K₁ ≤ fsuM T L := (hL0 ▸ (le_sup_left : K₁ ≤ K₁ ⊔ K₂)).trans (SecA.fsuL0_le_fsuM T L)
  have hK₂ : K₂ ≤ fsuM T L :=
    (hL0 ▸ (le_sup_right : K₂ ≤ K₁ ⊔ K₂)).trans (SecA.fsuL0_le_fsuM T L)
  have hN : ∀ x ∈ fsuM T L, x ∈ Subgroup.normalizer
      ((Subgroup.centralizer (fsuVM T L I : Set G) : Subgroup G) : Set G) := fun x hx =>
    SecA.le_normalizer_centralizer (SecA.fsuM_le_normalizer_fsuVM T L I) hx
  let S : Subgroup G :=
    { carrier := {l | l ∈ fsuM T L ∧
        b * l * b⁻¹ * l⁻¹ ∈ Subgroup.centralizer (fsuVM T L I : Set G)}
      mul_mem' := by
        rintro x y ⟨hx, hxc⟩ ⟨hy, hyc⟩
        refine ⟨Subgroup.mul_mem _ hx hy, ?_⟩
        have h1 := (Subgroup.mem_normalizer_iff.mp (hN x hx) _).mp hyc
        have e : b * (x * y) * b⁻¹ * (x * y)⁻¹ =
            (b * x * b⁻¹ * x⁻¹) * (x * (b * y * b⁻¹ * y⁻¹) * x⁻¹) := by group
        rw [e]
        exact Subgroup.mul_mem _ hxc h1
      one_mem' := ⟨Subgroup.one_mem _, by simp⟩
      inv_mem' := by
        rintro x ⟨hx, hxc⟩
        refine ⟨Subgroup.inv_mem _ hx, ?_⟩
        have h1 := (Subgroup.mem_normalizer_iff.mp (hN x⁻¹ (Subgroup.inv_mem _ hx)) _).mp
          (Subgroup.inv_mem _ hxc)
        have e : b * x⁻¹ * b⁻¹ * x⁻¹⁻¹ = x⁻¹ * (b * x * b⁻¹ * x⁻¹)⁻¹ * x⁻¹⁻¹ := by group
        rw [e]
        exact h1 }
  have hS : K₁ ⊔ K₂ ≤ S :=
    sup_le (fun l hl => ⟨hK₁ hl, h₁ l hl⟩) (fun l hl => ⟨hK₂ hl, h₂ l hl⟩)
  exact mem_cenL0.mpr ⟨hbM, fun l hl => (hS (hL0 ▸ hl)).2⟩

theorem mem_cenL0_of_pow_prime (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h322 : TmpL6_3_2_2_two) (hyp : Hyp10 G T L I) {b : G}
    (hbM : b ∈ fsuM T L) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hbp : b ^ p = 1)
    (hpL : ¬ p ∣ Nat.card (MulAut (↥L ⧸ CFSG.pCore 2 ↥L))) : b ∈ cenL0 T L I := by
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp hyp.not_normal
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hbL := mem_normalizer_of_pow_prime h37 h38 hyp hbM hodd hbp
  have hbLt := mem_normalizer_conjugate_of_pow_prime h37 h38 hyp hbM hodd hbp ht
  have hpLt : ¬ p ∣ Nat.card
      (MulAut (↥(CFSG.conjugate L t) ⧸ CFSG.pCore 2 ↥(CFSG.conjugate L t))) := by
    rwa [← Nat.card_congr (MulAut.congr (quotO2Equiv (conjEquiv L t))).toEquiv]
  have h1 := conj_mem_pCoreOf_of_pow_prime hbL hp hbp hpL
  have h2 := conj_mem_pCoreOf_of_pow_prime hbLt hp hbp hpLt
  have hO1 : pCoreOf 2 L ≤ Subgroup.centralizer (fsuVM T L I : Set G) :=
    SecA.pCoreOf_le_centralizer_fsuVM h322 hyp
  have hO2 : pCoreOf 2 (CFSG.conjugate L t) ≤ Subgroup.centralizer (fsuVM T L I : Set G) := by
    rw [SecA.pCoreOf_conjugate]
    intro x hx
    rw [SecA.mem_conjugate_iff] at hx
    have htN : t⁻¹ ∈ Subgroup.normalizer
        ((Subgroup.centralizer (fsuVM T L I : Set G) : Subgroup G) : Set G) :=
      SecA.le_normalizer_centralizer (SecA.le_normalizer_fsuVM T L I) (T.inv_mem ht)
    have := (Subgroup.mem_normalizer_iff.mp htN _).mp (hO1 hx)
    simpa [mul_assoc] using this
  exact mem_cenL0_of_sup hbM (SecA.fsuL0_eq_sup h37 h38 hyp ht htn)
    (fun l hl => hO1 (h1 l hl)) (fun l hl => hO2 (h2 l hl))

omit [Finite G] in
theorem isPGroup_zpowers_of_pow_eq_one {z : G} {p : ℕ} (hp : p.Prime) (h : z ^ p = 1) :
    IsPGroup p (Subgroup.zpowers z) := by
  rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one h) with h1 | h1
  · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h1, pow_zero])
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h1, pow_one])

theorem isHallTwoPrimeOf_conjSub {B X : Subgroup G} {x : G} (hx : x ∈ X)
    (hB : QuasithinUnique.Lin2.IsHallTwoPrimeOf B X) :
    QuasithinUnique.Lin2.IsHallTwoPrimeOf (conjSub x B) X := by
  obtain ⟨hBX, hodd, k, hk⟩ := hB
  have hle : conjSub x B ≤ X := by
    rintro _ ⟨b, hb, rfl⟩
    simpa [MulAut.conj_apply] using X.mul_mem (X.mul_mem hx (hBX hb)) (X.inv_mem hx)
  have hcard : Nat.card (conjSub x B) = Nat.card B :=
    (Nat.card_congr (B.equivMapOfInjective _ (MulAut.conj x).injective).toEquiv).symm
  refine ⟨hle, hcard ▸ hodd, k, ?_⟩
  have h1 := Subgroup.relIndex_mul_card (conjSub x B) X
  have h2 := Subgroup.relIndex_mul_card B X
  rw [inf_of_le_left hle, hcard] at h1
  rw [inf_of_le_left hBX] at h2
  rw [Nat.eq_of_mul_eq_mul_right Nat.card_pos (h1.trans h2.symm), hk]

theorem eq_one_of_pow_prime (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h322 : TmpL6_3_2_2_two) (hyp : Hyp10 G T L I) {H : Subgroup G}
    (hfaith : HallFaithful T L I H) {B : Subgroup G}
    (hB : QuasithinUnique.Lin2.IsHallTwoPrimeOf B (H ⊓ fsuM T L)) {z : G}
    (hz : z ∈ H ⊓ fsuM T L) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hzp : z ^ p = 1)
    (hpL : ¬ p ∣ Nat.card (MulAut (↥L ⧸ CFSG.pCore 2 ↥L))) : z = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hzC := mem_cenL0_of_pow_prime h37 h38 h322 hyp hz.2 hp hp2 hzp hpL
  obtain ⟨x, hx, hle⟩ := Ch11.SecB.exists_conj_le_hall hp2 hB (Subgroup.zpowers_le.mpr hz)
    (isPGroup_zpowers_of_pow_eq_one hp hzp)
  exact hfaith _ (isHallTwoPrimeOf_conjSub hx hB) z (hle (Subgroup.mem_zpowers z))
    (mem_cenL0.mp hzC).2

theorem mem_fsuL0_of_odd (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h322 : TmpL6_3_2_2_two) (h1013 : Stmt10_1_3) (hyp : Hyp10 G T L I) {H : Subgroup G}
    (hfaith : HallFaithful T L I H) {B : Subgroup G}
    (hB : QuasithinUnique.Lin2.IsHallTwoPrimeOf B (H ⊓ fsuM T L))
    (hodd : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ Nat.card (MulAut (↥L ⧸ CFSG.pCore 2 ↥L)) →
      r ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L))
    {z : G} (hz : z ∈ H ⊓ fsuM T L) (hzo : Odd (orderOf z)) : z ∈ fsuL0 T L := by
  refine mem_of_forall_primePow (isOfFinOrder_of_finite z) fun k hk => ?_
  obtain ⟨r, j, hr, hj, hrj⟩ := hk
  have hr' : r.Prime := Nat.prime_iff.mpr hr
  have hzk : z ^ k ∈ H ⊓ fsuM T L := Subgroup.pow_mem _ hz k
  have hok : Odd (orderOf (z ^ k)) := hzo.of_dvd_nat (orderOf_pow_dvd k)
  have hr2 : r ≠ 2 := by
    rintro rfl
    rw [← hrj] at hok
    exact (Nat.not_even_iff_odd.mpr hok) (Nat.even_pow.mpr ⟨even_two, hj.ne'⟩)
  by_cases hrA : r ∣ Nat.card (MulAut (↥L ⧸ CFSG.pCore 2 ↥L))
  · rw [← h1013 G T L I hyp r hr' hr2 (hodd r hr' hr2 hrA)]
    exact Subgroup.subset_closure ⟨hzk.2, j, hrj.symm⟩
  · exfalso
    have hrj' : r ^ j = r ^ (j - 1) * r := by rw [← pow_succ]; congr 1; omega
    have hyo : orderOf ((z ^ k) ^ r ^ (j - 1)) = r := by
      rw [orderOf_pow_of_dvd (pow_pos hr'.pos _).ne'
          (by rw [← hrj, hrj']; exact dvd_mul_right _ _),
        ← hrj, hrj', Nat.mul_div_cancel_left _ (pow_pos hr'.pos _)]
    have hyr : ((z ^ k) ^ r ^ (j - 1)) ^ r = 1 := by
      have := pow_orderOf_eq_one ((z ^ k) ^ r ^ (j - 1))
      rwa [hyo] at this
    have hy1 := eq_one_of_pow_prime h37 h38 h322 hyp hfaith hB (Subgroup.pow_mem _ hzk _) hr' hr2
      hyr hrA
    rw [hy1, orderOf_one] at hyo
    exact hr'.one_lt.ne' hyo.symm

end CFSG.Quasithin.Vol2.Ch10.SecB
