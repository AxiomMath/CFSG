module

public import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructCase3Aux
public import CFSG.Quasithin.EmptyFaithfulMultiple.F618CompThree
public import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace Gold14610

namespace Struct

variable {D : Type} [Group D] [Finite D]

theorem center_eq_bot_of_nonab {Y : Type*} [Group Y] [IsSimpleGroup Y]
    (hnc : ∃ a b : Y, a * b ≠ b * a) : Subgroup.center Y = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Y) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    exact hab ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b)) a)

omit [Finite D] in
theorem exists_mul_of_mem_sup_of_comm {K Z : Subgroup D}
    (hcomm : ∀ k ∈ K, ∀ z ∈ Z, k * z = z * k) {x : D} (hx : x ∈ K ⊔ Z) :
    ∃ k ∈ K, ∃ z ∈ Z, x = k * z := by
  have hZN : Z ≤ Subgroup.normalizer (K : Set D) := fun z hz =>
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun k hk => hcomm k hk z hz)
  have hx' : x ∈ ((K ⊔ Z : Subgroup D) : Set D) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left K Z hZN] at hx'
  obtain ⟨k, hk, z, hz, rfl⟩ := hx'
  exact ⟨k, hk, z, hz, rfl⟩

theorem inf_sup_twoResidual_eq_top {D₁ D₂ : Subgroup D} (hT : IsGoldschmidtTriple D₁ D₂) :
    (D₁ ⊓ D₂) ⊔ twoResidual (⊤ : Subgroup D) = ⊤ := by
  obtain ⟨T, hTe⟩ := hT.sylow
  exact sup_twoResidual_eq (hTe ▸ isSylowTwoOf_top_of_sylow T)

theorem case3_core {H₁ H₂ : Subgroup D} (h : F6.IsF618CaseThree H₁ H₂) :
    ∃ (p : ℕ) (K Z : Subgroup D), p.Prime ∧ (p % 24 = 11 ∨ p % 24 = 13) ∧ F6.IsL2 p 1 ↥K ∧
      CFSG.IsComponent K ∧ K.Normal ∧ Z.Normal ∧ K ⊔ Z = twoResidual ⊤ ∧
      ¬ twoResidual H₁ ≤ Z ∧ ¬ twoResidual H₂ ≤ Z := by
  obtain ⟨p, K, Z, hp, hp24, hK, hZ3, hKZ, -, hcomm, ⟨eT⟩, ⟨e₁⟩, ⟨e₂⟩, hout⟩ := h
  have hp2 : p ≠ 2 := by omega
  obtain ⟨hs, hnab, hcard⟩ :=
    EmptyFaithfulMultiple.F618Comp.isL2_facts hK hp2 (by rw [pow_one]; omega)
  rw [pow_one] at hcard
  have : IsSimpleGroup ↥K := hs
  have hKw : ∃ w, Odd w ∧ Nat.card ↥K = 2 ^ 2 * w := by
    obtain ⟨w, hw, hw'⟩ := EmptyFaithfulMultiple.F618Comp.psl2_card_eq_of_mod_eight (q := p)
      (by omega)
    exact ⟨w, hw, by rw [hcard]; exact hw'⟩
  have : Group.IsPerfect ↥K := F6.isPerfect_of_isSimpleGroup hnab
  have hZ : ∀ z ∈ Z, ∀ z' ∈ Z, z * z' = z' * z := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have : IsCyclic ↥Z := isCyclic_of_prime_card hZ3
    intro z hz z' hz'
    exact congrArg Subtype.val
      ((IsCyclic.isMulCommutative (α := ↥Z)).is_comm.comm ⟨z, hz⟩ ⟨z', hz'⟩)
  have hLn := F6.twoResidual_top_normal (D := D)
  have hKn : K.Normal := by
    rw [← EmptyFaithfulMultiple.F618Comp.commutator_sup_eq hcomm hZ, hKZ]
    exact Subgroup.commutator_normal _ _
  have hZeq : Z = twoResidual ⊤ ⊓ Subgroup.centralizer (K : Set D) := by
    apply le_antisymm
    · refine le_inf (hKZ ▸ le_sup_right) fun z hz => Subgroup.mem_centralizer_iff.mpr
        fun k hk => hcomm k hk z hz
    · rintro x ⟨hxL, hxC⟩
      rw [← hKZ] at hxL
      obtain ⟨k, hk, z, hz, rfl⟩ := exists_mul_of_mem_sup_of_comm hcomm hxL
      have hkc : (⟨k, hk⟩ : ↥K) ∈ Subgroup.center ↥K := by
        rw [Subgroup.mem_center_iff]
        intro g
        have h1 := Subgroup.mem_centralizer_iff.mp hxC g g.2
        have h2 := hcomm g g.2 z hz
        apply Subtype.ext
        show (g : D) * k = k * g
        have h3 : (g : D) * k * z = k * g * z := by
          calc (g : D) * k * z = g * (k * z) := by rw [mul_assoc]
            _ = k * z * g := h1
            _ = k * (z * g) := by rw [mul_assoc]
            _ = k * (g * z) := by rw [← h2]
            _ = k * g * z := by rw [← mul_assoc]
        exact mul_right_cancel h3
      rw [center_eq_bot_of_nonab hnab, Subgroup.mem_bot] at hkc
      have hk1 : k = 1 := congrArg Subtype.val hkc
      rw [hk1, one_mul]
      exact hz
  have hZn : Z.Normal := by
    have : (Subgroup.centralizer (K : Set D)).Normal := Subgroup.normal_centralizer
    rw [hZeq]
    infer_instance
  have hT8 : Nat.card ↥(H₁ ⊓ H₂) = 8 := by
    rw [Nat.card_congr eT.toEquiv, DihedralGroup.nat_card]
  have hTK : ∀ t ∈ H₁ ⊓ H₂, (∀ z ∈ Z, z * t = t * z) → t ∈ K := by
    intro t ht htC
    by_contra htK
    obtain ⟨y, hyZ, hne⟩ := (hout t ht htK).2.2 1 Z.one_mem
    apply hne
    rw [← htC y hyZ]
    group
  refine ⟨p, K, Z, hp, hp24, hK, ⟨isQuasisimple_of_simple_nonab hnab,
    Subgroup.Normal.isSubnormal hKn⟩, hKn, hZn, hKZ, ?_, not_twoResidual_le_of_perm hZ3 e₂⟩
  intro hle
  have hne : ∃ a ∈ twoResidual H₁, a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have h3 : 3 ∣ Nat.card ↥H₁ := by
      rw [Nat.card_congr e₁.toEquiv, DihedralGroup.nat_card]
      norm_num
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3
    obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient H₁ (x : D) x.2
    have h1 : (x : D) ^ 2 ^ k = 1 := hcon _ hk
    have h2 : orderOf (x : D) = 3 := by rw [Subgroup.orderOf_coe]; exact hx
    have h3' : 3 ∣ 2 ^ k := h2 ▸ orderOf_dvd_of_pow_eq_one h1
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3') (by norm_num)
  obtain ⟨a, ha, ha1⟩ := hne
  have haZ : a ∈ Z := hle ha
  have haH : a ∈ H₁ := twoResidual_le H₁ ha
  have ha3 : a ^ 3 = 1 := by
    have h1 := pow_card_eq_one' (G := ↥Z) (x := ⟨a, haZ⟩)
    rw [hZ3] at h1
    simpa using congrArg Subtype.val h1
  have hCH : (H₁ ⊓ H₂) ⊓ Subgroup.centralizer (Z : Set D) ≤ H₁ := inf_le_left.trans inf_le_left
  have hmem : ∀ c : ↥((H₁ ⊓ H₂) ⊓ Subgroup.centralizer (Z : Set D)),
      e₁ (Subgroup.inclusion hCH c) ∈ Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup 12) := by
    intro c
    refine dih12_mem_zpowers_of_comm (a := e₁ ⟨a, haH⟩) ?_ ?_ ?_
    · rw [← map_pow]
      have : (⟨a, haH⟩ : ↥H₁) ^ 3 = 1 := Subtype.ext (by simpa using ha3)
      rw [this, map_one]
    · intro h'
      apply ha1
      have : (⟨a, haH⟩ : ↥H₁) = 1 := e₁.injective (by rw [h', map_one])
      simpa using congrArg Subtype.val this
    · rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      show (c : D) * a = a * c
      exact (Subgroup.mem_centralizer_iff.mp c.2.2 a haZ).symm
  have hcyc : IsCyclic ↥((H₁ ⊓ H₂) ⊓ Subgroup.centralizer (Z : Set D)) := by
    refine isCyclic_of_injective
      (((e₁.toMonoidHom.comp (Subgroup.inclusion hCH)).codRestrict
        (Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup 12)) hmem)) ?_
    intro c c' hcc
    have h1 : e₁ (Subgroup.inclusion hCH c) = e₁ (Subgroup.inclusion hCH c') :=
      congrArg Subtype.val hcc
    exact Subgroup.inclusion_injective hCH (e₁.injective h1)
  exact false_of_cyclic_kernel hZ3 hT8 hTK hKw hcyc

theorem case3_conclusion {D₁ D₂ : Subgroup D} (hT : IsGoldschmidtTriple D₁ D₂)
    (h : F6.IsF618CaseThree D₁ D₂ ∨ F6.IsF618CaseThree D₂ D₁) :
    ∃ Kb : Subgroup D, CFSG.IsComponent Kb ∧ Kb.Normal ∧ F618Core ↥Kb ∧
      ∃ Zb : Subgroup D, Zb.Normal ∧ (⊤ : Subgroup D) = Kb ⊔ Zb ⊔ (D₁ ⊓ D₂) ∧
        ¬ twoResidual D₁ ≤ Zb ∧
        ∃ p : ℕ, p.Prime ∧ (p % 24 = 11 ∨ p % 24 = 13) ∧ F6.IsL2 p 1 ↥Kb := by
  have hsup := inf_sup_twoResidual_eq_top hT
  have fin : ∀ {p : ℕ} {K Z : Subgroup D}, p.Prime → (p % 24 = 11 ∨ p % 24 = 13) →
      F6.IsL2 p 1 ↥K → CFSG.IsComponent K → K.Normal → Z.Normal → K ⊔ Z = twoResidual ⊤ →
      ¬ twoResidual D₁ ≤ Z → ∃ Kb : Subgroup D, CFSG.IsComponent Kb ∧ Kb.Normal ∧
        F618Core ↥Kb ∧ ∃ Zb : Subgroup D, Zb.Normal ∧
          (⊤ : Subgroup D) = Kb ⊔ Zb ⊔ (D₁ ⊓ D₂) ∧ ¬ twoResidual D₁ ≤ Zb ∧
          ∃ p : ℕ, p.Prime ∧ (p % 24 = 11 ∨ p % 24 = 13) ∧ F6.IsL2 p 1 ↥Kb := by
    intro p K Z hp hp24 hK hc hKn hZn hKZ hn
    refine ⟨K, hc, hKn, Or.inl ⟨p, hp, hp24, hK⟩, Z, hZn, ?_, hn, p, hp, hp24, hK⟩
    rw [hKZ, sup_comm, hsup]
  rcases h with h | h
  · obtain ⟨p, K, Z, hp, hp24, hK, hc, hKn, hZn, hKZ, hn1, -⟩ := case3_core h
    exact fin hp hp24 hK hc hKn hZn hKZ hn1
  · obtain ⟨p, K, Z, hp, hp24, hK, hc, hKn, hZn, hKZ, -, hn2⟩ := case3_core h
    exact fin hp hp24 hK hc hKn hZn hKZ hn2

end Struct

end Gold14610

end CFSG.Quasithin
