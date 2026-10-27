module

public import CFSG.Walter.ReeOrder.WardLocal.Five

public section

open scoped BigOperators Classical MatrixGroups Pointwise

namespace CFSG.Walter.WardLocal

open CFSG CFSG.Walter.Ward CFSG.Walter.JT CFSG.SmallDefect CFSG.DirectProduct

variable {G : Type} [Group G] [Fintype G] {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [CharP K 3] {q : ℕ} {S : WardSetup G PSL(2, K) q (-1)} {D : S.EtaData} {m : ℕ}
  (B : Block S D m) {k : ℕ} (hq : q = 3 ^ (2 * k + 1)) (hK : Fintype.card K = q)
  (hG : Nat.card G = q ^ 3 * (q ^ 3 + 1) * (q - 1))
  {P : Subgroup G} (hP1P : PP1 S ≤ P) (hPc : Nat.card P = q ^ 3)
  (hPn : ∀ n ∈ NN1 S, ∀ x ∈ P, n * x * n⁻¹ ∈ P) (hN1c : Nat.card (NN1 S) = q ^ 3 * (q - 1))
  {Q : Subgroup G} {g : G} (hQ : ∀ x, x ∈ Q ↔ g⁻¹ * x * g ∈ P)

namespace Block

include hQ in
omit [Fintype G] [Fintype K] [DecidableEq K] [CharP K 3] in
theorem mem_normalizer_Q {n : G} : n ∈ Subgroup.normalizer (Q : Set G) ↔
    g⁻¹ * n * g ∈ Subgroup.normalizer (P : Set G) :=
  mem_normalizer_of_conj hQ

include hq hPc hQ in
omit [Fintype G] [Fintype K] [DecidableEq K] [CharP K 3] in
theorem isPGroup_Q : IsPGroup 3 Q := by
  rw [IsPGroup.iff_orderOf]
  rintro ⟨x, hx⟩
  obtain ⟨N, hN⟩ := (IsPGroup.iff_orderOf.mp (isPGroup_P hq hPc)) ⟨_, (hQ x).mp hx⟩
  refine ⟨N, ?_⟩
  rw [Subgroup.orderOf_mk] at hN ⊢
  rw [← hN, show g⁻¹ * x * g = g⁻¹ * x * g⁻¹⁻¹ by group, ← MulAut.conj_apply,
    MulEquiv.orderOf_eq]

include hQ in
omit [Fintype K] [DecidableEq K] [CharP K 3] in
theorem card_normalizer_Q : Nat.card (Subgroup.normalizer (Q : Set G)) =
    Nat.card (Subgroup.normalizer (P : Set G)) := by
  rw [← card_filter_eq, ← card_filter_eq, Finset.card_eq_sum_ones, Finset.card_eq_sum_ones,
    ← Nat.cast_inj (R := ℂ)]
  push_cast
  exact sum_conj (fun n => mem_normalizer_Q hQ) (fun _ => 1)

include B hq hK hG hP1P hPc hPn hN1c hQ in
theorem sum_normalizer_Q :
    ∑ n ∈ Finset.univ.filter (· ∈ Subgroup.normalizer (Q : Set G)), B.ξ₃ n =
      Nat.card (Subgroup.normalizer (Q : Set G)) := by
  rw [sum_conj (fun n => mem_normalizer_Q hQ), card_normalizer_Q hQ]
  simp_rw [B.xi3_class]
  exact B.sum_normalizer hq hK hG hP1P hPc hPn hN1c

include B hq hK hG hP1P hPc hPn hN1c hQ in
theorem xi3_cases_Q {n : G} (hn : n ∈ Subgroup.normalizer (Q : Set G)) :
    n = 1 ∨ orderOf n = 2 ∨ B.ξ₃ n = 0 ∨ B.ξ₃ n = 1 := by
  have h := B.xi3_cases hq hK hG hP1P hPc hPn hN1c ((mem_normalizer_Q hQ).mp hn)
  have ho : orderOf (g⁻¹ * n * g) = orderOf n := by
    rw [show g⁻¹ * n * g = g⁻¹ * n * g⁻¹⁻¹ by group, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
  have hx : B.ξ₃ (g⁻¹ * n * g) = B.ξ₃ n := by
    rw [show g⁻¹ * n * g = g⁻¹ * n * g⁻¹⁻¹ by group, B.xi3_class]
  rw [ho, hx] at h
  rcases h with h | h
  · left
    have := congrArg (fun t => g * t * g⁻¹) h
    simpa [mul_assoc] using this
  · exact Or.inr h

include B hq hK hG hP1P hPc hPn hN1c hQ in
theorem card_normalizer_Q_eq : Nat.card (Subgroup.normalizer (Q : Set G)) = q ^ 3 * (q - 1) := by
  rw [card_normalizer_Q hQ, card_normalizer hq hK (B.hcT hq hK hG) hG (B.card_AA hq hK hG)
    (fun _ hx h3 => B.card_centralizer_dvd hq hG hx h3) hP1P hPc hPn hN1c]

include B hq hK hG hP1P hPc hPn hN1c hQ in
theorem index_normalizer_Q : (Subgroup.normalizer (Q : Set G)).index = q ^ 3 + 1 := by
  have h := (Subgroup.normalizer (Q : Set G)).card_mul_index
  rw [B.card_normalizer_Q_eq hq hK hG hP1P hPc hPn hN1c hQ, hG] at h
  have hq3 : 3 ≤ q := by rw [hq]; exact Nat.le_self_pow (by omega) 3
  have hpos : 0 < q ^ 3 * (q - 1) := by
    have : 0 < q - 1 := by omega
    positivity
  have : q ^ 3 * (q - 1) * (Subgroup.normalizer (Q : Set G)).index =
      q ^ 3 * (q - 1) * (q ^ 3 + 1) := by rw [h]; ring
  exact Nat.eq_of_mul_eq_mul_left hpos this

include B hq hK hG hP1P hPc hPn hN1c hQ in
theorem fixedPointCount_eq :
    fixedPointCount G (G ⧸ Subgroup.normalizer (Q : Set G)) = 1 + B.ξ₃ := by
  have hpair : BlocksInnerProduct (fixedPointCount G (G ⧸ Subgroup.normalizer (Q : Set G)))
      B.ξ₃ = 1 := by
    rw [blocksInnerProduct_fixedPointCount _ _ (fun g x => B.xi3_class g x) B.real_3,
      B.sum_normalizer_Q hq hK hG hP1P hPc hPn hN1c hQ]
    have : (Nat.card (Subgroup.normalizer (Q : Set G)) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    field_simp
  have hdeg : deg B.ξ₃ + 1 = Nat.card (G ⧸ Subgroup.normalizer (Q : Set G)) := by
    rw [← Subgroup.index, B.index_normalizer_Q hq hK hG hP1P hPc hPn hN1c hQ, B.deg_3]
    push_cast; ring
  exact fixedPointCount_eq_one_add B.irr_3 B.n13.symm hdeg hpair

include B hq hK hG hP1P hPc hPn hN1c hQ in
theorem card_fixedBy {x : G} {n : ℕ} (h : 1 + B.ξ₃ x = n) :
    Nat.card (MulAction.fixedBy (G ⧸ Subgroup.normalizer (Q : Set G)) x) = n := by
  have h1 := congrFun (B.fixedPointCount_eq hq hK hG hP1P hPc hPn hN1c hQ) x
  rw [fixedPointCount, Pi.add_apply, Pi.one_apply, h] at h1
  exact_mod_cast h1

include B hq hK hG hP1P hPc hPn hN1c hQ in
theorem card_fixedBy_three {x : G} (hx : 3 ∣ orderOf x) :
    Nat.card (MulAction.fixedBy (G ⧸ Subgroup.normalizer (Q : Set G)) x) = 1 :=
  B.card_fixedBy hq hK hG hP1P hPc hPn hN1c hQ (by rw [B.xi3_eq_zero hq hG hx]; simp)

include B hq hK hG hP1P hPc hPn hN1c hQ in
theorem card_fixedBy_involution {t : G} (ht : orderOf t = 2) :
    Nat.card (MulAction.fixedBy (G ⧸ Subgroup.normalizer (Q : Set G)) t) = q + 1 :=
  B.card_fixedBy hq hK hG hP1P hPc hPn hN1c hQ (by rw [B.xi3_involution ht]; push_cast; ring)

omit [Fintype G] in
theorem conj_smul_eq_of_mem_normalizer {H : Subgroup G} {c : G}
    (hc : c ∈ Subgroup.normalizer (H : Set G)) : MulAut.conj c • H = H := by
  ext x
  rw [mem_conj_smul_iff]
  have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hc) x)
  rw [inv_inv] at this
  exact this.symm

include B hq hK hG hP1P hPc hPn hN1c hQ in
theorem inf_conj (c : G) : Q ⊓ (MulAut.conj c • Q) = ⊥ ∨ Q ⊓ (MulAut.conj c • Q) = Q := by
  by_cases h : Q ⊓ (MulAut.conj c • Q) = ⊥
  · exact Or.inl h
  right
  obtain ⟨⟨x, hx⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp h
  have hx1' : x ≠ 1 := fun h' => hx1 (Subtype.ext h')
  obtain ⟨hxQ, hxc⟩ := Subgroup.mem_inf.mp hx
  rw [mem_conj_smul_iff] at hxc
  have h3 : 3 ∣ orderOf x := three_dvd_of_mem (isPGroup_Q hq hPc hQ) hxQ hx1'
  have hcard := B.card_fixedBy_three hq hK hG hP1P hPc hPn hN1c hQ h3
  have hf1 : ((1 : G) : G ⧸ Subgroup.normalizer (Q : Set G)) ∈
      MulAction.fixedBy (G ⧸ Subgroup.normalizer (Q : Set G)) x := by
    rw [MulAction.mem_fixedBy, smul_mk_eq_iff]
    simpa using Subgroup.le_normalizer hxQ
  have hfc : (c : G ⧸ Subgroup.normalizer (Q : Set G)) ∈
      MulAction.fixedBy (G ⧸ Subgroup.normalizer (Q : Set G)) x := by
    rw [MulAction.mem_fixedBy, smul_mk_eq_iff]
    exact Subgroup.le_normalizer hxc
  have : Subsingleton (MulAction.fixedBy (G ⧸ Subgroup.normalizer (Q : Set G)) x) :=
    (Nat.card_eq_one_iff_unique.mp hcard).1
  have heq := congrArg Subtype.val (Subsingleton.elim (⟨_, hf1⟩ :
    MulAction.fixedBy (G ⧸ Subgroup.normalizer (Q : Set G)) x) ⟨_, hfc⟩)
  simp only at heq
  have hcN : c ∈ Subgroup.normalizer (Q : Set G) := by
    have := QuotientGroup.eq.mp heq
    simpa using this
  rw [conj_smul_eq_of_mem_normalizer hcN, inf_idem]

include B hq hK hG hP1P hPc hPn hN1c hQ in
theorem isMultiplyPretransitive :
    MulAction.IsMultiplyPretransitive G (G ⧸ Subgroup.normalizer (Q : Set G)) 2 := by
  have h := (permutation_character_orbit_count G (G ⧸ Subgroup.normalizer (Q : Set G))).2.2.2
    inferInstance (by
      rw [← Subgroup.index, B.index_normalizer_Q hq hK hG hP1P hPc hPn hN1c hQ]
      have : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ (by rw [hq]; positivity)
      omega)
  refine h.mpr ?_
  rw [B.fixedPointCount_eq hq hK hG hP1P hPc hPn hN1c hQ, add_sub_cancel_left]
  exact B.irr_3

include B hq hK hG hP1P hPc hPn hN1c hQ in
theorem eq_one_or_involution {n : G} (hn : n ∈ Subgroup.normalizer (Q : Set G))
    (h3 : 3 ≤ Nat.card (MulAction.fixedBy (G ⧸ Subgroup.normalizer (Q : Set G)) n)) :
    n = 1 ∨ orderOf n = 2 := by
  rcases B.xi3_cases_Q hq hK hG hP1P hPc hPn hN1c hQ hn with h | h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · rw [B.card_fixedBy hq hK hG hP1P hPc hPn hN1c hQ (n := 1) (by rw [h]; simp)] at h3
    omega
  · rw [B.card_fixedBy hq hK hG hP1P hPc hPn hN1c hQ (n := 2) (by rw [h]; norm_num)] at h3
    omega

include B hq hK hG hP1P hPc hPn hN1c hQ in
theorem eq_one_or_involution' {s : G}
    (h3 : 3 ≤ Nat.card (MulAction.fixedBy (G ⧸ Subgroup.normalizer (Q : Set G)) s))
    (a : G ⧸ Subgroup.normalizer (Q : Set G)) (ha : s • a = a) : s = 1 ∨ orderOf s = 2 := by
  obtain ⟨g₀, hg₀⟩ := MulAction.exists_smul_eq G a ((1 : G) : G ⧸ Subgroup.normalizer (Q : Set G))
  set s' := g₀ * s * g₀⁻¹ with hs'
  have hs'N : s' ∈ Subgroup.normalizer (Q : Set G) := by
    have h1 : s' • ((1 : G) : G ⧸ Subgroup.normalizer (Q : Set G)) = (1 : G) := by
      rw [← hg₀, hs', mul_smul, mul_smul, inv_smul_smul, ha]
    rw [smul_mk_eq_iff] at h1
    simpa using h1
  have hcard : Nat.card (MulAction.fixedBy (G ⧸ Subgroup.normalizer (Q : Set G)) s') =
      Nat.card (MulAction.fixedBy (G ⧸ Subgroup.normalizer (Q : Set G)) s) := by
    have h1 := congrFun (B.fixedPointCount_eq hq hK hG hP1P hPc hPn hN1c hQ) (g₀ * s * g₀⁻¹)
    have h2 := congrFun (B.fixedPointCount_eq hq hK hG hP1P hPc hPn hN1c hQ) s
    simp only [Pi.add_apply, Pi.one_apply] at h1 h2
    rw [B.xi3_class, ← h2] at h1
    simp only [fixedPointCount] at h1
    exact_mod_cast h1
  rcases B.eq_one_or_involution hq hK hG hP1P hPc hPn hN1c hQ hs'N (hcard ▸ h3) with h | h
  · left
    have := congrArg (fun t => g₀⁻¹ * t * g₀) h
    simpa [hs', mul_assoc] using this
  · right
    rw [← h, hs', show g₀ * s * g₀⁻¹ = MulAut.conj g₀ s from rfl, MulEquiv.orderOf_eq]

include B hq hK hG hP1P hPc hPn hN1c hQ in
theorem faithfulSMul : FaithfulSMul G (G ⧸ Subgroup.normalizer (Q : Set G)) := by
  refine ⟨fun {g₁ g₂} h => ?_⟩
  set n := g₂⁻¹ * g₁ with hn
  have hfix : ∀ a : G ⧸ Subgroup.normalizer (Q : Set G), n • a = a := by
    intro a; rw [hn, mul_smul, h a, inv_smul_smul]
  have hall : Nat.card (MulAction.fixedBy (G ⧸ Subgroup.normalizer (Q : Set G)) n) =
      q ^ 3 + 1 := by
    rw [← B.index_normalizer_Q hq hK hG hP1P hPc hPn hN1c hQ, Subgroup.index]
    rw [show MulAction.fixedBy (G ⧸ Subgroup.normalizer (Q : Set G)) n = Set.univ from
      Set.eq_univ_of_forall hfix, Nat.card_univ]
  have hq3 : 3 ≤ q := by rw [hq]; exact Nat.le_self_pow (by omega) 3
  have h3 : 3 ≤ Nat.card (MulAction.fixedBy (G ⧸ Subgroup.normalizer (Q : Set G)) n) := by
    rw [hall]
    have : 27 ≤ q ^ 3 := by
      calc 27 = 3 ^ 3 := by norm_num
        _ ≤ q ^ 3 := Nat.pow_le_pow_left hq3 3
    omega
  rcases B.eq_one_or_involution' hq hK hG hP1P hPc hPn hN1c hQ h3 _
    (hfix ((1 : G) : G ⧸ Subgroup.normalizer (Q : Set G))) with h1 | h2
  · have := congrArg (fun t => g₂ * t) h1
    simpa [hn] using this
  · exfalso
    rw [B.card_fixedBy_involution hq hK hG hP1P hPc hPn hN1c hQ h2] at hall
    have : q < q ^ 3 := by
      calc q = q ^ 1 := (pow_one q).symm
        _ < q ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
    omega

include B hq hK hG hP1P hPc hPn hN1c hQ in
theorem card_stabilizer_three_le (a b c : G ⧸ Subgroup.normalizer (Q : Set G)) (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) : Nat.card (MulAction.stabilizer G a ⊓ MulAction.stabilizer G b ⊓
      MulAction.stabilizer G c : Subgroup G) ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hel : ∀ s ∈ (MulAction.stabilizer G a ⊓ MulAction.stabilizer G b ⊓
      MulAction.stabilizer G c : Subgroup G), s = 1 ∨ orderOf s = 2 := by
    intro s hs
    obtain ⟨hsab, hsc⟩ := Subgroup.mem_inf.mp hs
    obtain ⟨hsa, hsb⟩ := Subgroup.mem_inf.mp hsab
    rw [MulAction.mem_stabilizer_iff] at hsa hsb hsc
    have h3 : 3 ≤ Nat.card (MulAction.fixedBy (G ⧸ Subgroup.normalizer (Q : Set G)) s) := by
      rw [Nat.card_eq_fintype_card]
      have := (Fintype.two_lt_card_iff
        (α := MulAction.fixedBy (G ⧸ Subgroup.normalizer (Q : Set G)) s)).mpr
        ⟨⟨a, hsa⟩, ⟨b, hsb⟩, ⟨c, hsc⟩,
        fun h => hab (congrArg Subtype.val h), fun h => hac (congrArg Subtype.val h),
        fun h => hbc (congrArg Subtype.val h)⟩
      omega
    exact B.eq_one_or_involution' hq hK hG hP1P hPc hPn hN1c hQ h3 a hsa
  have hp : IsPGroup 2 (MulAction.stabilizer G a ⊓ MulAction.stabilizer G b ⊓
      MulAction.stabilizer G c : Subgroup G) := by
    rw [IsPGroup.iff_orderOf]
    rintro ⟨s, hs⟩
    rw [Subgroup.orderOf_mk]
    rcases hel s hs with rfl | h
    · exact ⟨0, by simp⟩
    · exact ⟨1, by rw [h, pow_one]⟩
  obtain ⟨e, he⟩ := hp.exists_card_eq
  have hdvd : Nat.card (MulAction.stabilizer G a ⊓ MulAction.stabilizer G b ⊓
      MulAction.stabilizer G c : Subgroup G) ∣ q ^ 3 * (q - 1) := by
    have h1 : Nat.card (MulAction.stabilizer G a ⊓ MulAction.stabilizer G b ⊓
      MulAction.stabilizer G c : Subgroup G) ∣ Nat.card (MulAction.stabilizer G a) :=
      Subgroup.card_dvd_of_le (inf_le_left.trans inf_le_left)
    have h2 := (MulAction.stabilizer G a).card_mul_index
    rw [MulAction.index_stabilizer_of_transitive, ← Subgroup.index,
      B.index_normalizer_Q hq hK hG hP1P hPc hPn hN1c hQ, hG] at h2
    have hq3 : 3 ≤ q := by rw [hq]; exact Nat.le_self_pow (by omega) 3
    have h2' : Nat.card (MulAction.stabilizer G a) = q ^ 3 * (q - 1) := by
      have : Nat.card (MulAction.stabilizer G a) * (q ^ 3 + 1) = q ^ 3 * (q - 1) * (q ^ 3 + 1) :=
        by rw [h2]; ring
      exact Nat.eq_of_mul_eq_mul_right (by positivity) this
    rwa [h2'] at h1
  rw [he] at hdvd ⊢
  obtain ⟨k', hk', hodd⟩ := Block.q_half hq
  have hle : e ≤ 1 := by
    by_contra hlt
    push Not at hlt
    have h4 : 4 ∣ q ^ 3 * (q - 1) := (pow_dvd_pow 2 hlt).trans hdvd
    have hq1 : q - 1 = 2 * k' := by omega
    rw [hq1] at h4
    have hqodd : Odd (q ^ 3) := by rw [hq, ← pow_mul]; exact Odd.pow (by decide)
    have : Odd (q ^ 3 * k') := hqodd.mul hodd
    obtain ⟨t, ht⟩ := this
    have : 4 ∣ 2 * (q ^ 3 * k') := by rw [mul_left_comm] at h4; exact h4
    omega
  calc 2 ^ e ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hle
    _ = 2 := by norm_num

include B hq hK hG hP1P hPc hPn hN1c hQ in
theorem exists_card_stabilizer_three_eq : ∃ a b c : G ⧸ Subgroup.normalizer (Q : Set G),
    a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ Nat.card (MulAction.stabilizer G a ⊓ MulAction.stabilizer G b ⊓
      MulAction.stabilizer G c : Subgroup G) = 2 := by
  have hJ := B.card_fixedBy_involution hq hK hG hP1P hPc hPn hN1c hQ S.orderOf_J
  have hq3 : 3 ≤ q := by rw [hq]; exact Nat.le_self_pow (by omega) 3
  have h2 : 2 < Fintype.card (MulAction.fixedBy (G ⧸ Subgroup.normalizer (Q : Set G)) S.J) := by
    rw [← Nat.card_eq_fintype_card, hJ]; omega
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.mp h2
  have hab' : a ≠ b := fun h => hab (Subtype.ext h)
  have hac' : a ≠ c := fun h => hac (Subtype.ext h)
  have hbc' : b ≠ c := fun h => hbc (Subtype.ext h)
  refine ⟨a, b, c, hab', hac', hbc', le_antisymm
    (B.card_stabilizer_three_le hq hK hG hP1P hPc hPn hN1c hQ a b c hab' hac' hbc') ?_⟩
  have hJs : S.J ∈ (MulAction.stabilizer G a ⊓ MulAction.stabilizer G b ⊓
      MulAction.stabilizer G c : Subgroup G) := ⟨⟨ha, hb⟩, hc⟩
  have hne : (MulAction.stabilizer G a ⊓ MulAction.stabilizer G b ⊓
      MulAction.stabilizer G c : Subgroup G) ≠ ⊥ := by
    intro h
    rw [h, Subgroup.mem_bot] at hJs
    exact S.J_ne hJs
  have := (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
  omega

end Block

end CFSG.Walter.WardLocal
