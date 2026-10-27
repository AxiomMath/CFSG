module

public import CFSG.RankThree.PartTwo.Sec18.Item183KSylow
import CFSG.RankThree.PartTwo.Sec13.Item136E
import CFSG.RankThree.PartTwo.Sec4.LThreePiCaseI
public import CFSG.RankThree.PartTwo.Sec18.Item183One

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item183K

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late

variable {G : Type} [Group G] [Finite G] {A M K S : Subgroup G} {c : G}

theorem not_subset_zpowers_of_le {D H : Subgroup G} (hDH : D ≤ H) (hexp : ∀ x ∈ D, x ^ 3 = 1)
    (h9 : 9 ≤ Nat.card D) : ¬ ∃ x : G, (H : Set G) ⊆ (Subgroup.zpowers x : Set G) := by
  rintro ⟨w, hw⟩
  have hDw : D ≤ Subgroup.zpowers w := fun y hy => hw (hDH hy)
  have : IsCyclic D := Subgroup.isCyclic_of_le hDw
  exact Sec13.not_isCyclic_of_nine_le hexp h9 this

omit [Finite G] in
theorem card_le_three_of_subset_zpowers {H : Subgroup G} (hexp : ∀ x ∈ H, x ^ 3 = 1) {w : G}
    (hw : (H : Set G) ⊆ (Subgroup.zpowers w : Set G)) : Nat.card H ≤ 3 := by
  have : IsCyclic H := Subgroup.isCyclic_of_le (fun y hy => hw hy : H ≤ Subgroup.zpowers w)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := H)
  have hcard : Nat.card H = orderOf g := by
    rw [← Nat.card_zpowers g]
    exact Nat.card_congr (Equiv.subtypeUnivEquiv hg).symm
  have hg3 : g ^ 3 = 1 := Subtype.ext (by simpa using hexp g g.2)
  rw [hcard]
  exact orderOf_le_of_pow_eq_one (by norm_num) hg3

theorem eq_of_nine_lt {D E : Subgroup G} (hE : IsE27 E) (hDE : D ≤ E) (h9 : 9 < Nat.card D) :
    D = E := by
  have hdvd : Nat.card D ∣ 3 ^ 3 := by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hE.2]
    exact Subgroup.card_dvd_of_le hDE
  obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  refine Subgroup.eq_of_le_of_card_ge hDE ?_
  rw [hE.2, hk]
  interval_cases k <;> simp_all

theorem card_eq_nine_of_le {D E : Subgroup G} (hE : IsE27 E) (hDE : D ≤ E) (h9 : 9 ≤ Nat.card D)
    (hne : D ≠ E) : Nat.card D = 9 := by
  rcases h9.lt_or_eq with hlt | heq
  · exact absurd (eq_of_nine_lt hE hDE hlt) hne
  · exact heq.symm

theorem orderOf_c (h : Hyp183 G A M c K) : orderOf c = 3 :=
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  orderOf_eq_prime (h.pow_three h.mem_A) h.ne_one

omit [Finite G] in
theorem exists_not_mem_not_mem {B₁ B₂ : Subgroup G} (h₁ : B₁ ≤ A) (h₂ : B₂ ≤ A) (hne₁ : B₁ ≠ A)
    (hne₂ : B₂ ≠ A) : ∃ a ∈ A, a ∉ B₁ ∧ a ∉ B₂ := by
  obtain ⟨u, huA, hu⟩ : ∃ u ∈ A, u ∉ B₁ := by
    by_contra hne
    push Not at hne
    exact hne₁ (le_antisymm h₁ hne)
  obtain ⟨v, hvA, hv⟩ : ∃ v ∈ A, v ∉ B₂ := by
    by_contra hne
    push Not at hne
    exact hne₂ (le_antisymm h₂ hne)
  by_cases hu₂ : u ∈ B₂
  · by_cases hv₁ : v ∈ B₁
    · refine ⟨u * v, A.mul_mem huA hvA, fun h => hu ?_, fun h => hv ?_⟩
      · simpa using B₁.mul_mem h (B₁.inv_mem hv₁)
      · simpa using B₂.mul_mem (B₂.inv_mem hu₂) h
    · exact ⟨v, hvA, hv₁, hv⟩
  · exact ⟨u, huA, hu, hu₂⟩

variable (h : Hyp183 G A M c K) (hS : SylowS A K S)
include h hS

theorem mem_A_of_mem_inf_C {z : G} (hz : z ∈ S ⊓ K) (hzC : z ∈ Sec4.thetaQuotCentralizer K) :
    z ∈ A := by
  refine h.mem_of_commute (pow_three_of_mem_inf h hS hz) fun b hb => ?_
  obtain ⟨y, hy, hyb⟩ := exists_actsLike h hS hb
  have hbS := hS.le hb
  have h1 : z * y = y * z := commute_of_mem_C h hS hz.1 hzC hy
  have h2 : y⁻¹ * b * z = z * (y⁻¹ * b) :=
    commute_of_mem_C h hS (S.mul_mem (S.inv_mem hy.1) hbS) hyb hz
  calc b * z = y * (y⁻¹ * b * z) := by group
    _ = y * (z * (y⁻¹ * b)) := by rw [h2]
    _ = z * y * (y⁻¹ * b) := by rw [h1]; group
    _ = z * b := by group

theorem inf_noncyclic_of_not_cyclic_aux
    (hC : ¬ ∃ x : G, sectionCentralizer A K (CFSG.Open.pCoreOf 2 K) ⊆
      (Subgroup.zpowers x : Set G)) :
    ¬ ∃ x : G, ((A ⊓ K : Subgroup G) : Set G) ⊆ (Subgroup.zpowers x : Set G) := by
  set C := Sec4.thetaQuotCentralizer K with hCdef
  rw [h.sectionCentralizer_eq h.le_normalizer] at hC
  have hCA9 : 9 ≤ Nat.card (A ⊓ C : Subgroup G) :=
    nine_le_card_of_not_subset_zpowers (fun x hx => h.pow_three hx.1) hC
  obtain ⟨z, hz, hzC, hz1⟩ := exists_mem_inf_C h hS
  have hzA := mem_A_of_mem_inf_C h hS hz hzC
  obtain ⟨x, hxA, hxK, hxC⟩ : ∃ x ∈ A, x ∈ K ∧ x ∉ C := by
    by_cases hall : ∀ b ∈ A, b ∈ C
    · obtain ⟨x, hx, hxC⟩ : ∃ x ∈ S ⊓ K, x ∉ C := by
        by_contra hne
        push Not at hne
        have hle : S ⊓ K ≤ S ⊓ K ⊓ C := fun x hx => ⟨hx, hne x hx⟩
        have h1 := Subgroup.card_le_of_le hle
        rw [card_inf h hS] at h1
        have h2 : Nat.card (S ⊓ K ⊓ C : Subgroup G) ≤ 3 := card_inf_C_le h hS
        omega
      refine ⟨x, h.mem_of_commute (pow_three_of_mem_inf h hS hx) fun b hb => ?_, hx.2, hxC⟩
      exact commute_of_mem_C h hS (hS.le hb) (hall b hb) hx
    · push Not at hall
      obtain ⟨a, haA, haC⟩ := hall
      obtain ⟨x, hx, hxa⟩ := exists_actsLike h hS haA
      have hxC : x ∉ C := fun hxC => haC (by simpa using C.mul_mem hxC hxa)
      have hxs : x⁻¹ * a * x = x * (x⁻¹ * a) :=
        commute_of_mem_C h hS (S.mul_mem (S.inv_mem hx.1) (hS.le haA)) hxa hx
      have hD : Subgroup.zpowers a ⊔ (A ⊓ C) = A := by
        refine eq_of_nine_lt h.isE27 (sup_le (Subgroup.zpowers_le.mpr haA) inf_le_left) ?_
        have hle : A ⊓ C ≤ Subgroup.zpowers a ⊔ (A ⊓ C) := le_sup_right
        have hne : A ⊓ C ≠ Subgroup.zpowers a ⊔ (A ⊓ C) := fun heq =>
          haC (heq ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers a) : a ∈ A ⊓ C).2
        have hdvd := Subgroup.card_dvd_of_le hle
        have hlt : Nat.card (A ⊓ C : Subgroup G) ≠
            Nat.card (Subgroup.zpowers a ⊔ (A ⊓ C) : Subgroup G) :=
          fun heq => hne (Subgroup.eq_of_le_of_card_ge hle heq.ge)
        have hpos : 0 < Nat.card (Subgroup.zpowers a ⊔ (A ⊓ C) : Subgroup G) := Nat.card_pos
        obtain ⟨m, hm⟩ := hdvd
        rcases m with _ | _ | m
        · rw [hm, mul_zero] at hpos
          exact absurd hpos (lt_irrefl 0)
        · rw [zero_add, mul_one] at hm
          exact absurd hm.symm hlt
        · rw [hm]
          nlinarith
      have hcen : A ≤ Subgroup.centralizer ({x} : Set G) := by
        rw [← hD]
        refine sup_le (Subgroup.zpowers_le.mpr ?_) fun d hd => ?_
        · rw [Subgroup.mem_centralizer_singleton_iff]
          calc a * x = x * (x⁻¹ * a * x) := by group
            _ = x * (x * (x⁻¹ * a)) := by rw [hxs]
            _ = x * a := by group
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact commute_of_mem_C h hS (hS.le hd.1) hd.2 hx
      refine ⟨x, h.mem_of_commute (pow_three_of_mem_inf h hS hx) fun b hb => ?_, hx.2, hxC⟩
      exact Subgroup.mem_centralizer_singleton_iff.mp (hcen hb)
  have hz3 : orderOf z = 3 :=
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    orderOf_eq_prime (h.pow_three hzA) hz1
  have hxz : x ∉ Subgroup.zpowers z := fun hxz =>
    hxC ((Subgroup.zpowers_le.mpr hzC) hxz)
  have h9 := Sec4.card_zpowers_sup_zpowers (h.pow_three hxA) hz3 hxz (h.commute hxA hzA)
  refine not_subset_zpowers_of_le (D := Subgroup.zpowers z ⊔ Subgroup.zpowers x)
    (sup_le (Subgroup.zpowers_le.mpr ⟨hzA, hz.2⟩) (Subgroup.zpowers_le.mpr ⟨hxA, hxK⟩))
    (fun y hy => ?_) h9.ge
  exact (Sec13.isElemAbelian_zpowers_sup (h.pow_three hzA) (h.pow_three hxA)
    (h.commute hzA hxA)).2 y hy

section Cyclic

variable (hC : ∃ w : G, sectionCentralizer A K (CFSG.Open.pCoreOf 2 K) ⊆
  (Subgroup.zpowers w : Set G))
include hC

omit hS in
theorem inf_C_eq : A ⊓ Sec4.thetaQuotCentralizer K = Subgroup.zpowers c := by
  obtain ⟨w, hw⟩ := hC
  rw [h.sectionCentralizer_eq h.le_normalizer] at hw
  have h3 := card_le_three_of_subset_zpowers (H := A ⊓ Sec4.thetaQuotCentralizer K)
    (fun x hx => h.pow_three hx.1) hw
  symm
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr ⟨h.mem_A, h.c_mem_C⟩) ?_
  rw [Nat.card_zpowers, orderOf_c h]
  exact h3

theorem c_mem_K : c ∈ K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨z, hz, hzC, hz1⟩ := exists_mem_inf_C h hS
  have hzA := mem_A_of_mem_inf_C h hS hz hzC
  have hzc : z ∈ Subgroup.zpowers c := by
    rw [← inf_C_eq h hC]
    exact ⟨hzA, hzC⟩
  have hz3 : orderOf z = 3 := orderOf_eq_prime (h.pow_three hzA) hz1
  have heq : Subgroup.zpowers z = Subgroup.zpowers c :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzc)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hz3, orderOf_c h])
  have hc : c ∈ Subgroup.zpowers z := heq ▸ Subgroup.mem_zpowers c
  exact (Subgroup.zpowers_le.mpr hz.2) hc

theorem inf_inf_C_eq : S ⊓ K ⊓ Sec4.thetaQuotCentralizer K = Subgroup.zpowers c := by
  symm
  refine Subgroup.eq_of_le_of_card_ge
    (Subgroup.zpowers_le.mpr ⟨⟨hS.le h.mem_A, c_mem_K h hS hC⟩, h.c_mem_C⟩) ?_
  rw [Nat.card_zpowers, orderOf_c h]
  exact card_inf_C_le h hS

omit hS hC in
theorem exists_a : ∃ a ∈ A, a ∉ Subgroup.zpowers c ∧ a ∉ K := by
  have hAK : A ⊓ K ≠ A := fun heq => h.false_of_isE27_le h.isE27 (inf_eq_left.mp heq)
  have hcA : Subgroup.zpowers c ≠ A := fun heq => by
    have h27 := h.isE27.2
    rw [← heq, Nat.card_zpowers, orderOf_c h] at h27
    norm_num at h27
  obtain ⟨a, ha, h1, h2⟩ :=
    exists_not_mem_not_mem (Subgroup.zpowers_le.mpr h.mem_A) inf_le_left hcA hAK
  exact ⟨a, ha, h1, fun haK => h2 ⟨ha, haK⟩⟩

theorem commutator_mem_zpowers {a x : G} (ha : a ∈ A) (hx : x ∈ S ⊓ K)
    (hxa : x⁻¹ * a ∈ Sec4.thetaQuotCentralizer K) {b : G} (hb : b ∈ A) :
    x * b * x⁻¹ * b⁻¹ ∈ Subgroup.zpowers c := by
  obtain ⟨y, hy, hyb⟩ := exists_actsLike h hS hb
  have h1 := h.commutator_mem_C ha hb hx.2 hy.2 hxa hyb
  have h2 : x * y * x⁻¹ * y⁻¹ ∈ S ⊓ K :=
    ⟨S.mul_mem (S.mul_mem (S.mul_mem hx.1 hy.1) (S.inv_mem hx.1)) (S.inv_mem hy.1),
      K.mul_mem (K.mul_mem (K.mul_mem hx.2 hy.2) (K.inv_mem hx.2)) (K.inv_mem hy.2)⟩
  have h3 : x * y * x⁻¹ * y⁻¹ ∈ Subgroup.zpowers c := by
    rw [← inf_inf_C_eq h hS hC]
    exact ⟨h2, h1⟩
  have ht0 : (y⁻¹ * b) * x = x * (y⁻¹ * b) :=
    commute_of_mem_C h hS (S.mul_mem (S.inv_mem hy.1) (hS.le hb)) hyb hx
  have ht' : (y⁻¹ * b) * x⁻¹ = x⁻¹ * (y⁻¹ * b) := by
    calc (y⁻¹ * b) * x⁻¹ = x⁻¹ * (x * (y⁻¹ * b)) * x⁻¹ := by group
      _ = x⁻¹ * ((y⁻¹ * b) * x) * x⁻¹ := by rw [ht0]
      _ = x⁻¹ * (y⁻¹ * b) := by group
  have e : x * b * x⁻¹ * b⁻¹ = x * y * x⁻¹ * y⁻¹ := by
    calc x * b * x⁻¹ * b⁻¹ = x * y * ((y⁻¹ * b) * x⁻¹) * b⁻¹ := by group
      _ = x * y * (x⁻¹ * (y⁻¹ * b)) * b⁻¹ := by rw [ht']
      _ = x * y * x⁻¹ * y⁻¹ := by group
  rw [e]
  exact h3

end Cyclic

end CFSG.RankThree.PartTwo.Sec18.Item183K
