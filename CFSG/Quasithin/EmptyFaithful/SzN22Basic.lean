module

public import CFSG.Quasithin.EmptyFaithful.SzN19Par

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

namespace SzN22

section Sylow

variable {Ω : Type*} [Group Ω]

theorem isSylowTwoOf_of_le {S H H' : Subgroup Ω} (hS : IsSylowTwoOf S H) (hSH' : S ≤ H')
    (hH'H : H' ≤ H) : IsSylowTwoOf S H' := by
  refine ⟨hSH', hS.2.1, fun h => hS.2.2 ?_⟩
  have h1 := Subgroup.relIndex_mul_relIndex S H' H hSH' hH'H
  exact h.trans ⟨H'.relIndex H, h1.symm⟩

theorem eq_of_isSylowTwoOf_le [Finite Ω] {S D X : Subgroup Ω} (hS : IsSylowTwoOf S X) (hSD : S ≤ D)
    (hDX : D ≤ X) (hD : IsPGroup 2 D) : D = S := by
  have hS' := isSylowTwoOf_of_le hS hSD hDX
  have hodd : Odd (S.relIndex D) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hS'.2.2)
  have hmul := Subgroup.relIndex_mul_card S D
  rw [inf_eq_left.mpr hSD] at hmul
  obtain ⟨k, hk⟩ := hD.exists_card_eq
  have hdvd : S.relIndex D ∣ 2 ^ k := ⟨Nat.card ↥S, by rw [← hk, ← hmul]⟩
  have h1 : S.relIndex D = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right k hodd.coprime_two_right) hdvd
  exact le_antisymm (Subgroup.relIndex_eq_one.mp h1) hSD

theorem isSylowTwoOf_inf_normalized {T H N : Subgroup Ω} (hT : IsSylowTwoOf T H) (hNH : N ≤ H)
    (hTN : T ≤ Subgroup.normalizer (N : Set Ω)) : IsSylowTwoOf (T ⊓ N) N :=
  SzN19.isSylowTwoOf_inf_of_normalizes (isSylowTwoOf_of_le hT le_sup_right (sup_le hNH hT.1))
    le_sup_left hTN le_rfl

end Sylow

section Three

variable {Ω : Type*} [Group Ω]

theorem two_pow_mod_three (k : ℕ) : 2 ^ k % 3 = 1 ∨ 2 ^ k % 3 = 2 := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ]; omega

theorem mem_of_pow_three_sup {Y S : Subgroup Ω} (hS : IsPGroup 2 S)
    (hSY : S ≤ Subgroup.normalizer (Y : Set Ω)) {x : Ω} (hx : x ∈ Y ⊔ S) (hx3 : x ^ 3 = 1) :
    x ∈ Y := by
  obtain ⟨y, hy, s, hs, rfl⟩ := SzN19.exists_mul_of_normalizes hSY hx
  obtain ⟨k, hk⟩ := hS ⟨s, hs⟩
  have hsk : s ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have key : ∀ n : ℕ, ∃ y' ∈ Y, (y * s) ^ n = y' * s ^ n := by
    intro n
    induction n with
    | zero => exact ⟨1, Y.one_mem, by simp⟩
    | succ n ih =>
      obtain ⟨y', hy', h⟩ := ih
      refine ⟨y' * (s ^ n * y * (s ^ n)⁻¹), ?_, ?_⟩
      · refine Y.mul_mem hy' ?_
        have := (Subgroup.mem_normalizer_iff.mp (hSY (S.pow_mem hs n)) y).mp hy
        exact this
      · rw [pow_succ, h]
        group
  obtain ⟨y', hy', h⟩ := key (2 ^ k)
  rw [hsk, mul_one] at h
  have hmod : (y * s) ^ 2 ^ k = (y * s) ^ (2 ^ k % 3) := pow_eq_pow_mod _ hx3
  rcases two_pow_mod_three k with h1 | h2
  · rw [h1, pow_one] at hmod
    rw [← hmod, h]
    exact hy'
  · rw [h2] at hmod
    have hsq : (y * s) ^ 2 ∈ Y := by rw [← hmod, h]; exact hy'
    have : y * s = ((y * s) ^ 2) ^ 2 := by
      have h4 : (y * s) ^ 4 = y * s := by
        calc (y * s) ^ 4 = (y * s) ^ 3 * (y * s) := by rw [pow_succ]
          _ = y * s := by rw [hx3, one_mul]
      rw [← pow_mul]
      exact h4.symm
    rw [this]
    exact Y.pow_mem hsq 2

theorem le_of_orderThree_mem [Finite Ω] {Y Q : Subgroup Ω}
    (hYgen : Y = Subgroup.closure {y | y ∈ Y ∧ orderOf y = 3})
    (hY3 : ∀ E : Subgroup Ω, E ≤ Y → IsPGroup 3 E → Nat.card E ≤ 3)
    (hQ : ∀ y ∈ Y, ∀ q ∈ Q, y * q * y⁻¹ ∈ Q) {b : Ω} (hbY : b ∈ Y) (hbQ : b ∈ Q)
    (hb3 : orderOf b = 3) : Y ≤ Q := by
  have hF3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have key : ∀ (c : Ω) (hcY : c ∈ Y), orderOf c = 3 →
      ∃ P : Sylow 3 ↥Y, (P : Subgroup ↥Y) = Subgroup.zpowers (⟨c, hcY⟩ : ↥Y) := by
    intro c hcY hc3
    have hc3' : orderOf (⟨c, hcY⟩ : ↥Y) = 3 := (Subgroup.orderOf_mk c hcY).trans hc3
    have hz : IsPGroup 3 (Subgroup.zpowers (⟨c, hcY⟩ : ↥Y)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hc3']; norm_num)
    obtain ⟨P, hP⟩ := hz.exists_le_sylow
    have hPle : Nat.card ↥(P : Subgroup ↥Y) ≤ 3 := by
      have hmap : IsPGroup 3 ↥((P : Subgroup ↥Y).map Y.subtype) :=
        P.isPGroup'.of_equiv (Subgroup.equivMapOfInjective _ _ Y.subtype_injective)
      have hle : (P : Subgroup ↥Y).map Y.subtype ≤ Y := fun x ⟨y, _, hy⟩ => hy ▸ y.2
      have := hY3 _ hle hmap
      rwa [Subgroup.card_map_of_injective Y.subtype_injective] at this
    refine ⟨P, (Subgroup.eq_of_le_of_card_ge hP ?_).symm⟩
    rw [Nat.card_zpowers, hc3']
    exact hPle
  rw [hYgen]
  refine (Subgroup.closure_le Q).mpr ?_
  rintro z ⟨hzY, hz3⟩
  obtain ⟨Pb, hPb⟩ := key b hbY hb3
  obtain ⟨Pz, hPz⟩ := key z hzY hz3
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥Y) Pb Pz
  have hgg := congrArg (fun P : Sylow 3 ↥Y => (P : Subgroup ↥Y)) hg
  simp only [Sylow.coe_subgroup_smul] at hgg
  have hzPz : (⟨z, hzY⟩ : ↥Y) ∈ (Pz : Subgroup ↥Y) := by
    rw [hPz]
    exact Subgroup.mem_zpowers _
  rw [← hgg, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, hPb] at hzPz
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hzPz
  have hi' : (g : Ω)⁻¹ * z * (g : Ω) = b ^ i := by
    have := congrArg Subtype.val hi
    simpa [MulAut.conj_inv_apply] using this.symm
  have hzeq : z = (g : Ω) * b ^ i * (g : Ω)⁻¹ := by
    rw [← hi']
    group
  rw [hzeq]
  exact hQ g g.2 _ (Q.zpow_mem hbQ i)

end Three

section Two

variable {Ω : Type*} [Group Ω]

theorem isPGroup_two_of_no_orderThree {D : Subgroup Ω} (m : ℕ)
    (hD : ∀ x ∈ D, x ^ (2 ^ m * 3) = 1) (hno : ∀ x ∈ D, orderOf x ≠ 3) : IsPGroup 2 D := by
  have hF3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rintro ⟨x, hx⟩
  refine ⟨m, Subtype.ext ?_⟩
  show x ^ 2 ^ m = 1
  by_contra hne
  have hy3 : (x ^ 2 ^ m) ^ 3 = 1 := by rw [← pow_mul]; exact hD x hx
  exact hno _ (D.pow_mem hx _) (orderOf_eq_prime hy3 hne)

omit [Group Ω] in
theorem sq_mod_three {m : ℕ} (hm : ¬ 3 ∣ m) : m ^ 2 % 3 = 1 := by
  have : m % 3 = 1 ∨ m % 3 = 2 := by omega
  rcases this with h | h <;> simp [Nat.pow_mod, h]

theorem centralizes_of_inner [Finite Ω] {N : Subgroup Ω} {z x : Ω} (hxN : x ∈ N) (hz3 : z ^ 3 = 1)
    (hxz : ∀ n ∈ N, z * n * z⁻¹ = x * n * x⁻¹) (hx3 : ¬ 3 ∣ orderOf x) :
    ∀ n ∈ N, z * n * z⁻¹ = n := by
  set c : Ω := x⁻¹ * z with hc
  have hcN : ∀ n ∈ N, c * n * c⁻¹ = n := by
    intro n hn
    have := hxz n hn
    calc c * n * c⁻¹ = x⁻¹ * (z * n * z⁻¹) * x := by rw [hc]; group
      _ = n := by rw [this]; group
  have hzc : z = x * c := by rw [hc]; group
  have hcomm : Commute x c := by
    have := hcN x hxN
    exact (Commute.symm (by
      have h' : c * x = x * c := by
        calc c * x = (c * x * c⁻¹) * c := by group
          _ = x * c := by rw [this]
      exact h'))
  have hm1 : x ^ orderOf x = 1 := pow_orderOf_eq_one x
  set m := orderOf x with hm
  have hmod : z ^ (m ^ 2) = z := by
    rw [pow_eq_pow_mod _ hz3, sq_mod_three hx3, pow_one]
  have hzp : z = c ^ (m ^ 2) := by
    calc z = z ^ (m ^ 2) := hmod.symm
      _ = (x * c) ^ (m ^ 2) := by rw [← hzc]
      _ = x ^ (m ^ 2) * c ^ (m ^ 2) := hcomm.mul_pow _
      _ = c ^ (m ^ 2) := by rw [sq, pow_mul x m m, hm1, one_pow, one_mul]
  intro n hn
  have hpow : ∀ k : ℕ, c ^ k * n * (c ^ k)⁻¹ = n := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc c ^ (k + 1) * n * (c ^ (k + 1))⁻¹ = c ^ k * (c * n * c⁻¹) * (c ^ k)⁻¹ := by
            rw [pow_succ', mul_inv_rev]; group
        _ = n := by rw [hcN n hn, ih]
  rw [hzp]
  exact hpow _

end Two

section Proj

variable {Ω : Type*} [Group Ω]

theorem isPGroup_proj {N C S : Subgroup Ω} (hinf : N ⊓ C = ⊥) (hS : IsPGroup 2 S)
    (hSC : S ≤ Subgroup.normalizer (C : Set Ω)) : IsPGroup 2 ↥((C ⊔ S) ⊓ N) := by
  have hnorm : (C.subgroupOf (C ⊔ S)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hSC)
  have hsurj : Function.Surjective
      ((QuotientGroup.mk' (C.subgroupOf (C ⊔ S))).comp
        (Subgroup.inclusion (le_sup_right : S ≤ C ⊔ S))) := by
    intro z
    induction z using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨c, hc, s, hs, hx⟩ := SzN19.exists_mul_of_normalizes hSC x.2
      refine ⟨⟨s, hs⟩, ?_⟩
      show (QuotientGroup.mk (⟨s, Subgroup.mem_sup_right hs⟩ : ↥(C ⊔ S)) :
          ↥(C ⊔ S) ⧸ C.subgroupOf (C ⊔ S)) = QuotientGroup.mk x
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have e : (((⟨s, Subgroup.mem_sup_right hs⟩ : ↥(C ⊔ S))⁻¹ * x : ↥(C ⊔ S)) : Ω) =
          s⁻¹ * c * s := by
        simp [hx, mul_assoc]
      rw [e]
      have := (Subgroup.mem_normalizer_iff.mp (hSC (S.inv_mem hs)) c).mp hc
      simpa using this
  have hq : IsPGroup 2 (↥(C ⊔ S) ⧸ C.subgroupOf (C ⊔ S)) := hS.of_surjective _ hsurj
  refine hq.of_injective
    ((QuotientGroup.mk' (C.subgroupOf (C ⊔ S))).comp
      (Subgroup.inclusion (inf_le_left : (C ⊔ S) ⊓ N ≤ C ⊔ S))) ?_
  rw [injective_iff_map_eq_one]
  intro x hx
  have h1 : ((Subgroup.inclusion (inf_le_left : (C ⊔ S) ⊓ N ≤ C ⊔ S) x : ↥(C ⊔ S)) : Ω) ∈ C :=
    Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hx)
  have h2 : (x : Ω) ∈ N ⊓ C := ⟨x.2.2, h1⟩
  rw [hinf, Subgroup.mem_bot] at h2
  exact Subtype.ext h2

end Proj

end SzN22

end CFSG.Quasithin
