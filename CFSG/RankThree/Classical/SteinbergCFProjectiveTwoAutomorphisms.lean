module

public import CFSG.RankThree.Classical.SteinbergCFProjectiveElementary
public import CFSG.Assembly.OrderReductions.FrattiniAutomorphisms
public import CFSG.Assembly.OrderReductions.FrattiniElementary
public import CFSG.LocalAnalysis.RankTwoShapes.FourShapes.CyclicCriterion

public section

namespace CFSG.RankThree.Classical

open Matrix Matrix.ProjGenLinGroup
open CFSG.OrderReductions.FrattiniAutomorphisms CFSG.OrderReductions.FrattiniElementary
open scoped MatrixGroups

universe u v

variable {k : Type u} [Field k]

theorem commute_of_commute_traceless (h2 : (2 : k) ≠ 0) {A G H : Matrix (Fin 2) (Fin 2) k}
    (hA : A.trace = 0) (hdet : A.det ≠ 0) (hG : G * A = A * G) (hH : H * A = A * H) :
    G * H = H * G := by
  obtain ⟨α, β, rfl⟩ := exists_eq_smul_one_add_smul h2 hA hdet hG
  obtain ⟨γ, δ, rfl⟩ := exists_eq_smul_one_add_smul h2 hA hdet hH
  simp only [add_mul, mul_add, smul_mul_smul_comm, one_mul, mul_one]
  rw [mul_comm α γ, mul_comm β γ, mul_comm α δ, mul_comm β δ]
  abel

@[expose] def projCommutant (A : GL (Fin 2) k) : Subgroup PGL(2, k) :=
  (Subgroup.centralizer ({A} : Set (GL (Fin 2) k))).map mk

theorem mk_mem_projCommutant {A G : GL (Fin 2) k}
    (hG : (G : Matrix (Fin 2) (Fin 2) k) * A = A * G) : mk G ∈ projCommutant A :=
  ⟨G, Subgroup.mem_centralizer_singleton_iff.2 (Units.ext hG), rfl⟩

theorem exists_of_mem_projCommutant {A : GL (Fin 2) k} {x : PGL(2, k)}
    (hx : x ∈ projCommutant A) :
    ∃ G : GL (Fin 2) k, mk G = x ∧ (G : Matrix (Fin 2) (Fin 2) k) * A = A * G := by
  obtain ⟨G, hG, rfl⟩ := hx
  exact ⟨G, rfl, congrArg Units.val (Subgroup.mem_centralizer_singleton_iff.1 hG)⟩

theorem projCommutant_mul_comm (h2 : (2 : k) ≠ 0) {A : GL (Fin 2) k}
    (hA : (A : Matrix (Fin 2) (Fin 2) k).trace = 0) {x y : PGL(2, k)}
    (hx : x ∈ projCommutant A) (hy : y ∈ projCommutant A) : x * y = y * x := by
  obtain ⟨G, rfl, hG⟩ := exists_of_mem_projCommutant hx
  obtain ⟨H, rfl, hH⟩ := exists_of_mem_projCommutant hy
  rw [← map_mul, ← map_mul]
  congr 1
  exact Units.ext (commute_of_commute_traceless h2 hA (det_ne_zero_of_GL A) hG hH)

theorem eq_one_or_eq_of_mem_projCommutant (h2 : (2 : k) ≠ 0) {A : GL (Fin 2) k}
    (hA : (A : Matrix (Fin 2) (Fin 2) k).trace = 0) {x : PGL(2, k)}
    (hx : x ∈ projCommutant A) (hsq : x * x = 1) : x = 1 ∨ x = mk A := by
  obtain ⟨G, rfl, hG⟩ := exists_of_mem_projCommutant hx
  by_cases h1 : mk G = 1
  · exact Or.inl h1
  · exact Or.inr (mk_eq_of_commute_traceless h2 hA (trace_eq_zero_of_mk_mul_self hsq h1) hG)

theorem exists_anticomm_of_not_mem {A : GL (Fin 2) k} {x : PGL(2, k)}
    (hx : x * mk A = mk A * x) (hx0 : x ∉ projCommutant A) :
    ∃ G : GL (Fin 2) k, mk G = x ∧
      (G : Matrix (Fin 2) (Fin 2) k) * A = -((A : Matrix (Fin 2) (Fin 2) k) * G) := by
  obtain ⟨G, rfl⟩ := mk_surjective x
  obtain ⟨c, hc, hGA⟩ := exists_mul_eq_smul_of_commute hx
  rcases mul_self_eq_one_iff.1 hc with rfl | rfl
  · rw [one_smul] at hGA
    exact absurd (mk_mem_projCommutant hGA) hx0
  · rw [neg_one_smul] at hGA
    exact ⟨G, rfl, hGA⟩

theorem mul_inv_mem_projCommutant {A : GL (Fin 2) k} {x y : PGL(2, k)}
    (hx : x * mk A = mk A * x) (hx0 : x ∉ projCommutant A)
    (hy : y * mk A = mk A * y) (hy0 : y ∉ projCommutant A) : x * y⁻¹ ∈ projCommutant A := by
  obtain ⟨G, rfl, hG⟩ := exists_anticomm_of_not_mem hx hx0
  obtain ⟨H, rfl, hH⟩ := exists_anticomm_of_not_mem hy hy0
  rw [← map_inv, ← map_mul]
  apply mk_mem_projCommutant
  have hH' : ((H⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) * A =
      -((A : Matrix (Fin 2) (Fin 2) k) * (H⁻¹ : GL (Fin 2) k)) := by
    have e1 : ((H⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) * H = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have e2 : (H : Matrix (Fin 2) (Fin 2) k) * (H⁻¹ : GL (Fin 2) k) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hAH : (A : Matrix (Fin 2) (Fin 2) k) * H = -((H : Matrix (Fin 2) (Fin 2) k) * A) := by
      rw [hH, neg_neg]
    calc ((H⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) * A
        = ((H⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) * A *
            (H * (H⁻¹ : GL (Fin 2) k)) := by rw [e2, mul_one]
      _ = ((H⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) * (A * H) *
            (H⁻¹ : GL (Fin 2) k) := by simp only [mul_assoc]
      _ = -(((H⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) * H * A *
            (H⁻¹ : GL (Fin 2) k)) := by
          rw [hAH]
          simp only [mul_neg, neg_mul, mul_assoc]
      _ = -((A : Matrix (Fin 2) (Fin 2) k) * (H⁻¹ : GL (Fin 2) k)) := by rw [e1, one_mul]
  rw [Units.val_mul, mul_assoc, hH', mul_neg, ← mul_assoc, hG, neg_mul, neg_neg, mul_assoc]

theorem zpow_eq_one_or_eq {G : Type*} [Group G] {a : G} (ha : a ^ 2 = 1) (n : ℤ) :
    a ^ n = 1 ∨ a ^ n = a := by
  rw [zpow_eq_zpow_emod n (n := 2) (by exact_mod_cast ha)]
  rcases Int.emod_two_eq_zero_or_one n with h | h <;> rw [h]
  · exact Or.inl (zpow_zero a)
  · exact Or.inr (zpow_one a)

theorem card_frattini_quotient_le_four (h2 : (2 : k) ≠ 0) (Q : Subgroup PGL(2, k)) [Finite Q]
    (hQ : IsPGroup 2 Q) : Nat.card (Q ⧸ frattini Q) ≤ 4 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V := Q ⧸ frattini Q
  set π : Q →* V := QuotientGroup.mk' (frattini Q)
  have hV2 : ∀ v : V, v ^ 2 = 1 := frattini_quotient_exponent 2 hQ
  rcases subsingleton_or_nontrivial Q with hQ1 | hQ1
  · have : Subsingleton V := (QuotientGroup.mk'_surjective (frattini Q)).subsingleton
    rw [Nat.card_unique]
    norm_num
  obtain ⟨z, hz⟩ : ∃ z : Subgroup.center Q, orderOf z = 2 := by
    have hc := hQ.to_subgroup (Subgroup.center Q)
    have : Nontrivial (Subgroup.center Q) := hQ.center_nontrivial
    obtain ⟨n, hn⟩ := hc.exists_card_eq
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [pow_zero, Nat.card_eq_one_iff_unique] at hn
      exact not_subsingleton _ hn.1
    exact exists_prime_orderOf_dvd_card' 2 (hn ▸ dvd_pow_self 2 hn0)
  set z₀ : PGL(2, k) := ((z : Q) : PGL(2, k)) with hz₀
  have hzQ : z₀ ∈ Q := (z : Q).2
  have hzsq : z₀ * z₀ = 1 := by
    have h := pow_orderOf_eq_one z
    rw [hz, sq] at h
    rw [hz₀, ← Subgroup.coe_mul, ← Subgroup.coe_mul, h]
    rfl
  have hz1 : z₀ ≠ 1 := by
    intro h
    have : z = 1 := Subtype.ext (Subtype.ext h)
    rw [this, orderOf_one] at hz
    exact absurd hz (by norm_num)
  have hzc : ∀ x ∈ Q, x * z₀ = z₀ * x := fun x hx => by
    have := congrArg Subtype.val (Subgroup.mem_center_iff.1 z.2 ⟨x, hx⟩)
    simp only [Subgroup.coe_mul] at this
    exact this
  obtain ⟨A, hAz, hA⟩ := exists_traceless_lift hzsq hz1
  set Q₀ : Subgroup Q := (projCommutant A).subgroupOf Q with hQ₀
  have hzQ₀ : (z : Q) ∈ Q₀ := by
    rw [hQ₀, Subgroup.mem_subgroupOf]
    change z₀ ∈ _
    rw [← hAz]
    exact mk_mem_projCommutant rfl
  have hQ₀comm : ∀ x y : Q₀, x * y = y * x := fun x y => Subtype.ext (Subtype.ext
    (projCommutant_mul_comm h2 hA (Subgroup.mem_subgroupOf.1 x.2) (Subgroup.mem_subgroupOf.1 y.2)))
  let : CommGroup Q₀ := { (inferInstance : Group Q₀) with mul_comm := hQ₀comm }
  have hcyc : IsCyclic Q₀ := by
    refine (CFSG.RankTwoShapes.isCyclic_iff_elementary_card_le (hQ.to_subgroup Q₀)).2
      fun E hE => ?_
    have hmem : ∀ e ∈ E, e ∈ ({1, ⟨(z : Q), hzQ₀⟩} : Finset Q₀) := fun e he => by
      have hsq : ((e : Q) : PGL(2, k)) * ((e : Q) : PGL(2, k)) = 1 := by
        have h := hE e he
        rw [sq] at h
        have h' := congrArg (fun y : Q₀ => ((y : Q) : PGL(2, k))) h
        simpa using h'
      rcases eq_one_or_eq_of_mem_projCommutant h2 hA (Subgroup.mem_subgroupOf.1 e.2) hsq with
        h | h
      · simp [show e = 1 from Subtype.ext (Subtype.ext h)]
      · simp [show e = ⟨(z : Q), hzQ₀⟩ from Subtype.ext (Subtype.ext (h.trans hAz))]
    exact (finite_and_card_le_of_forall_mem E _ hmem).2.trans Finset.card_le_two
  obtain ⟨a, ha⟩ := hcyc.exists_generator
  obtain ⟨r, hr⟩ : ∃ r : Q, ∀ x : Q, x ∈ Q₀ ∨ x * r⁻¹ ∈ Q₀ := by
    by_cases hex : ∃ r : Q, r ∉ Q₀
    · obtain ⟨r, hr⟩ := hex
      refine ⟨r, fun x => or_iff_not_imp_left.2 fun hx => Subgroup.mem_subgroupOf.2 ?_⟩
      rw [Subgroup.coe_mul, Subgroup.coe_inv]
      refine mul_inv_mem_projCommutant (hAz ▸ hzc x x.2) (fun h => hx ?_)
        (hAz ▸ hzc r r.2) fun h => hr ?_
      · exact Subgroup.mem_subgroupOf.2 h
      · exact Subgroup.mem_subgroupOf.2 h
    · push Not at hex
      exact ⟨1, fun x => Or.inl (hex x)⟩
  have hpow : ∀ n : ℤ, π ((a : Q) ^ n) = 1 ∨ π ((a : Q) ^ n) = π a := fun n => by
    rw [map_zpow]
    exact zpow_eq_one_or_eq (hV2 _) n
  have hmemV : ∀ v : V, v ∈ ({1, π a, π r, π a * π r} : Finset V) := by
    intro v
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (frattini Q) v
    rcases hr x with hx | hx
    · obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (ha ⟨x, hx⟩)
      have hxn : (a : Q) ^ n = x := congrArg Subtype.val hn
      change π x ∈ _
      rcases hpow n with h | h <;> rw [← hxn, h] <;> simp
    · obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (ha ⟨x * r⁻¹, hx⟩)
      have hxn : (a : Q) ^ n * r = x := by
        rw [show (a : Q) ^ n = x * r⁻¹ from congrArg Subtype.val hn, inv_mul_cancel_right]
      change π x ∈ _
      rcases hpow n with h | h <;> rw [← hxn, map_mul, h] <;> simp
  have hle := (finite_and_card_le_of_forall_mem (⊤ : Subgroup V) _
    fun v _ => hmemV v).2.trans (card_four_le _ _ _ _)
  rwa [Subgroup.card_top] at hle


theorem odd_projective_linear_two_subgroup_automorphisms_no_large_primes (k : Type u) [Field k]
    (hk : ringChar k ≠ 2) (Q : Subgroup PGL(2, k)) [Finite Q] (hQ : IsPGroup 2 Q) :
    (∀ p : ℕ, p.Prime → p ∣ Nat.card (MulAut Q) → p = 2 ∨ p = 3) ∧
    ∀ p : ℕ, p.Prime → 3 < p → ∀ (P : Type v) [Group P], IsPGroup p P →
      ∀ (φ : P →* MulAut Q) (g : P), φ g = 1 := by
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hk
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card (MulAut Q) → p = 2 ∨ p = 3 := by
    intro p hp hdvd
    set f := quotientAutomorphism (frattini Q)
    have hker : IsPGroup 2 f.ker := frattini_automorphism_kernel_isPGroup 2 hQ
    have hcard : Nat.card (MulAut Q) = Nat.card f.ker * Nat.card f.range := by
      rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, mul_comm,
        ← Subgroup.card_eq_card_quotient_mul_card_subgroup]
    rw [hcard] at hdvd
    rcases (Nat.Prime.dvd_mul hp).1 hdvd with h | h
    · obtain ⟨n, hn⟩ := hker.exists_card_eq
      rw [hn] at h
      exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
    · have h1 : Nat.card f.range ∣ Nat.card (MulAut (Q ⧸ frattini Q)) :=
        Subgroup.card_subgroup_dvd_card _
      have h3 : Nat.card (MulAut (Q ⧸ frattini Q)) ∣ (Nat.card (Q ⧸ frattini Q)).factorial := by
        rw [← Nat.card_perm]
        exact Subgroup.card_dvd_of_injective (MulAut.toPerm _) fun σ τ hστ =>
          MulEquiv.ext fun x => congrArg (fun π : Equiv.Perm _ => π x) hστ
      have hp4 := (hp.dvd_factorial).1 (h.trans (h1.trans h3))
      have h4 := card_frattini_quotient_le_four h2 Q hQ
      have hp2 := hp.two_le
      have hp4' : p ≤ 4 := hp4.trans h4
      interval_cases p
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd hp (by norm_num)
  refine ⟨hprime, fun p hp hp3 P _ hP φ g => ?_⟩
  by_contra hne
  obtain ⟨n, hn⟩ := hP g
  have hdvd : orderOf (φ g) ∣ p ^ n := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hn, map_one])
  obtain ⟨i, hi, hord⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  have hi0 : i ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hord
    exact hne hord
  have hpd : p ∣ Nat.card (MulAut Q) :=
    (dvd_pow_self p hi0).trans (hord ▸ orderOf_dvd_natCard (φ g))
  rcases hprime p hp hpd with rfl | rfl <;> omega

end CFSG.RankThree.Classical
