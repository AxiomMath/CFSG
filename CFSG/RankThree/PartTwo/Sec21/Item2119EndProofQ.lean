module

public import CFSG.RankThree.PartTwo.Sec21.Item2119EndProof2124

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item2119EndProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open scoped commutatorElement

section Exponent

variable {G : Type*} [Group G]

theorem commute_conj_of_cube {x y : G} (hy3 : y ^ 3 = 1) (h1 : (y⁻¹ * x) ^ 3 = 1)
    (h2 : (x * y) ^ 3 = 1) : x * (y⁻¹ * x * y) = (y⁻¹ * x * y) * x := by
  rw [pow_three] at h1 h2
  have e1 : x * y⁻¹ * x = y * x⁻¹ * y := by
    calc x * y⁻¹ * x = y * (y⁻¹ * x * (y⁻¹ * x * (y⁻¹ * x))) * x⁻¹ * y := by group
      _ = y * x⁻¹ * y := by rw [h1]; group
  have e2 : x * y * x = y⁻¹ * x⁻¹ * y⁻¹ := by
    calc x * y * x = (x * y * (x * y * (x * y))) * (y * x * y)⁻¹ := by group
      _ = y⁻¹ * x⁻¹ * y⁻¹ := by rw [h2]; group
  have h3' : y * y * y = 1 := by rw [← pow_three']; exact hy3
  have hyy : y * y = y⁻¹ := eq_inv_of_mul_eq_one_left h3'
  have hy2 : y⁻¹ * y⁻¹ = y := by
    calc y⁻¹ * y⁻¹ = y⁻¹ * y⁻¹ * (y * y * y) := by rw [h3', mul_one]
      _ = y := by group
  calc x * (y⁻¹ * x * y) = (x * y⁻¹ * x) * y := by group
    _ = y * x⁻¹ * (y * y) := by rw [e1]; group
    _ = y * x⁻¹ * y⁻¹ := by rw [hyy]
    _ = y⁻¹ * y⁻¹ * x⁻¹ * y⁻¹ := by rw [hy2]
    _ = y⁻¹ * (x * y * x) := by rw [e2]; group
    _ = (y⁻¹ * x * y) * x := by group

theorem commute_commutatorElement_left {Q : Subgroup G} (h3 : ∀ g ∈ Q, g ^ 3 = 1) {x y : G}
    (hx : x ∈ Q) (hy : y ∈ Q) : ⁅x, y⁆ * x = x * ⁅x, y⁆ := by
  have hc := commute_conj_of_cube (x := x) (y := y⁻¹) (h3 _ (Q.inv_mem hy))
    (by rw [inv_inv]; exact h3 _ (Q.mul_mem hy hx)) (h3 _ (Q.mul_mem hx (Q.inv_mem hy)))
  rw [inv_inv] at hc
  have hc' : x * (y * x * y⁻¹)⁻¹ = (y * x * y⁻¹)⁻¹ * x :=
    (Commute.inv_right (show Commute x (y * x * y⁻¹) from hc)).eq
  rw [commutatorElement_def]
  calc x * y * x⁻¹ * y⁻¹ * x = x * (y * x * y⁻¹)⁻¹ * x := by group
    _ = x * (x * (y * x * y⁻¹)⁻¹) := by rw [mul_assoc, ← hc']
    _ = x * (x * y * x⁻¹ * y⁻¹) := by group

theorem commute_commutatorElement_right {Q : Subgroup G} (h3 : ∀ g ∈ Q, g ^ 3 = 1) {x y : G}
    (hx : x ∈ Q) (hy : y ∈ Q) : ⁅x, y⁆ * y = y * ⁅x, y⁆ := by
  have hc := commute_conj_of_cube (x := y) (y := x⁻¹) (h3 _ (Q.inv_mem hx))
    (by rw [inv_inv]; exact h3 _ (Q.mul_mem hx hy)) (h3 _ (Q.mul_mem hy (Q.inv_mem hx)))
  rw [inv_inv] at hc
  rw [commutatorElement_def]
  calc x * y * x⁻¹ * y⁻¹ * y = x * y * x⁻¹ := by group
    _ = (y * (x * y * x⁻¹)) * y⁻¹ := by rw [hc]; group
    _ = y * (x * y * x⁻¹ * y⁻¹) := by group

theorem commutatorElement_mem_of_closure {Q Z : Subgroup G} {S : Set G}
    (hZc : ∀ q ∈ Q, ∀ z ∈ Z, q * z * q⁻¹ = z) (hQ : Subgroup.closure S = Q)
    (hS : ∀ x ∈ S, ∀ y ∈ S, ⁅x, y⁆ ∈ Z) : ∀ x ∈ Q, ∀ y ∈ Q, ⁅x, y⁆ ∈ Z := by
  intro x hx y hy
  rw [← hQ] at hx hy hZc
  refine Subgroup.closure_induction₂ (p := fun x y _ _ => ⁅x, y⁆ ∈ Z)
    (fun x y hx hy => hS x hx y hy)
    (fun x _ => by rw [commutatorElement_one_left]; exact Z.one_mem)
    (fun x _ => by rw [commutatorElement_one_right]; exact Z.one_mem) ?_ ?_ ?_ ?_ hx hy
  · intro x x' y hx hx' _ h h'
    have e : ⁅x * x', y⁆ = (x * ⁅x', y⁆ * x⁻¹) * ⁅x, y⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e, hZc x hx _ h']
    exact Z.mul_mem h' h
  · intro y y' x hy hy' hx h h'
    have e : ⁅x, y * y'⁆ = ⁅x, y⁆ * (y * ⁅x, y'⁆ * y⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e, hZc y hy _ h']
    exact Z.mul_mem h h'
  · intro x y hx _ h
    have e : ⁅x⁻¹, y⁆ = x⁻¹ * ⁅x, y⁆⁻¹ * x⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e, hZc _ (Subgroup.inv_mem _ hx) _ (Z.inv_mem h)]
    exact Z.inv_mem h
  · intro x y _ hy h
    have e : ⁅x, y⁻¹⁆ = y⁻¹ * ⁅x, y⁆⁻¹ * y⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e, hZc _ (Subgroup.inv_mem _ hy) _ (Z.inv_mem h)]
    exact Z.inv_mem h

end Exponent

section Extraspecial

variable {P : Type*} [Group P] [Finite P]

theorem isExtraspecialPGroup_three_of (hP : IsPGroup 3 P) {Z : Subgroup P} (hZ : Nat.card Z = 3)
    (hZc : Z ≤ Subgroup.center P) (hcomm : ∀ x y : P, ⁅x, y⁆ ∈ Z) (hcube : ∀ x : P, x ^ 3 ∈ Z)
    (hcent : ∀ x : P, (∀ y : P, x * y = y * x) → x ∈ Z) (hnab : ∃ x : P, x ∉ Z) :
    IsExtraspecialPGroup 3 P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (IsPGroup 3 P) := ⟨hP⟩
  have hcenter : Subgroup.center P = Z := by
    refine le_antisymm (fun x hx => hcent x fun y => ?_) hZc
    exact (Subgroup.mem_center_iff.mp hx y).symm
  have hcom_le : commutator P ≤ Z := by
    rw [_root_.commutator_def]
    exact Subgroup.commutator_le.mpr fun x _ y _ => hcomm x y
  have hcom : commutator P = Z := by
    refine le_antisymm hcom_le ?_
    obtain ⟨x, hx⟩ := hnab
    have hnc : ¬ ∀ y : P, x * y = y * x := fun h => hx (hcent x h)
    push Not at hnc
    obtain ⟨y, hy⟩ := hnc
    have hg1 : ⁅x, y⁆ ≠ 1 := fun h => hy (commutatorElement_eq_one_iff_mul_comm.mp h)
    have hgZ : ⁅x, y⁆ ∈ Z := hcomm x y
    have hgc : ⁅x, y⁆ ∈ commutator P := by
      rw [_root_.commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
    have hzp : Subgroup.zpowers ⁅x, y⁆ = Z := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hgZ) ?_
      rw [hZ, Nat.card_zpowers]
      have h3 : orderOf ⁅x, y⁆ ∣ 3 := by
        have := orderOf_dvd_natCard (⟨_, hgZ⟩ : Z)
        rwa [hZ, Subgroup.orderOf_mk] at this
      rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hg1
      · exact h.ge
    rw [← hzp]
    exact (Subgroup.zpowers_le).mpr hgc
  have hfr : frattini P = Z := by
    refine le_antisymm ?_ (hcom ▸ commutator_le_frattini_of_isPGroup (R := P) (p := 3))
    rw [frattini_eq_closure_commutator_union_powers (p := 3)]
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ (hx | ⟨y, rfl⟩)
    · exact hcom_le hx
    · exact hcube y
  refine ⟨hP, ?_, ?_, ?_⟩
  · rw [hcom, hcenter]
  · rw [hfr, hcenter]
  · rw [hcenter]
    exact hZ

end Extraspecial

section Claim

variable {G : Type} [Group G] [Finite G]

theorem isExtra2127_of {A Q : Subgroup G} (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (h3 : ∀ x ∈ A, x ^ 3 = 1) (h27 : Nat.card A = 27) {c d a : G} (hcA : c ∈ A) (hdA : d ∈ A)
    (haA : a ∈ A) (hd1 : d ≠ 1)
    (hB9 : Nat.card (Subgroup.zpowers d ⊔ Subgroup.zpowers c : Subgroup G) = 9)
    (haB : a ∉ Subgroup.zpowers d ⊔ Subgroup.zpowers c) (hAQ : A ≤ Q)
    (hQN : Q ≤ Subgroup.normalizer (A : Set G))
    (hCQ : Q ⊓ Subgroup.centralizer (A : Set G) = A) (hQ3 : ∀ x ∈ Q, x ^ 3 = 1)
    (hQA : ∀ x ∈ Q, ∀ y ∈ A, y⁻¹ * (x * y * x⁻¹) ∈ Subgroup.zpowers d)
    (hQd : ∀ x ∈ Q, x * d * x⁻¹ = d) {x₁ x₂ : G} (hx₁Q : x₁ ∈ Q) (hx₂Q : x₂ ∈ Q)
    (hx₁c : x₁ * c * x₁⁻¹ = c) (hx₁d : x₁ * d * x₁⁻¹ = d) {k₁ : ℕ} (hk₁ : k₁ < 3)
    (hk₁0 : k₁ ≠ 0) (hx₁a : x₁ * a * x₁⁻¹ = a * d ^ k₁) (hx₂a : x₂ * a * x₂⁻¹ = a)
    (hx₂d : x₂ * d * x₂⁻¹ = d) {k₂ : ℕ} (hk₂ : k₂ < 3) (hk₂0 : k₂ ≠ 0)
    (hx₂c : x₂ * c * x₂⁻¹ = c * d ^ k₂)
    (hrepr : ∀ q ∈ Q, ∃ m₁ m₂ : ℕ, ∃ a₀ ∈ A, q = x₂ ^ m₂ * x₁ ^ m₁ * a₀) :
    IsExtra2127 Q := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hd3 : d ^ 3 = 1 := h3 d hdA
  have hod : orderOf d = 3 := orderOf_eq_prime hd3 hd1
  have hdQ : d ∈ Q := hAQ hdA
  have hpow1 : ∀ {k m : ℕ}, k < 3 → k ≠ 0 → d ^ (k * m) = 1 → 3 ∣ m := by
    intro k m hk hk0 h
    have h1 := orderOf_dvd_of_pow_eq_one h
    rw [hod] at h1
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h1 with h2 | h2
    · exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) h2) (by omega)
    · exact h2
  have hpow3 : ∀ {x : G}, x ^ 3 = 1 → ∀ {m : ℕ}, 3 ∣ m → x ^ m = 1 := by
    intro x hx m hm
    obtain ⟨r, rfl⟩ := hm
    rw [pow_mul, hx, one_pow]
  have hdk : ∀ k : ℕ, d ^ k ∈ A := fun k => Subgroup.pow_mem _ hdA k
  have hconj3 : ∀ (v : G) (m j i : ℕ), v * (a ^ m * (d ^ j * c ^ i)) * v⁻¹ =
      (v * a * v⁻¹) ^ m * ((v * d * v⁻¹) ^ j * (v * c * v⁻¹) ^ i) := fun v m j i => by
    rw [← MulAut.conj_apply, ← MulAut.conj_apply, ← MulAut.conj_apply, ← MulAut.conj_apply,
      map_mul, map_mul, map_pow, map_pow, map_pow]
  have hZc : ∀ q ∈ Q, ∀ z ∈ Subgroup.zpowers d, q * z * q⁻¹ = z := fun q hq z hz =>
    Item21LateProof.conj_eq_of_mem_zpowers (hQd q hq) hz
  have hcent : ∀ z ∈ Q, (∀ q ∈ Q, z * q = q * z) → z ∈ Subgroup.zpowers d := by
    intro z hzQ hz
    have hzA : z ∈ A := by
      rw [← hCQ]
      exact ⟨hzQ, Subgroup.mem_centralizer_iff.mpr fun y hy => (hz y (hAQ hy)).symm⟩
    obtain ⟨m, j, i, rfl⟩ := exists_basis_repr hcomm h3 h27 haA hdA hcA hB9 haB _ hzA
    have e1 : x₁ * (a ^ m * (d ^ j * c ^ i)) * x₁⁻¹ = a ^ m * (d ^ j * c ^ i) := by
      rw [← hz x₁ hx₁Q, mul_inv_cancel_right]
    rw [hconj3, hx₁a, hx₁d, hx₁c,
      (Commute.mul_pow (hcomm a haA _ (hdk k₁)) m)] at e1
    have e3 : a ^ m * ((d ^ k₁) ^ m * (d ^ j * c ^ i)) = a ^ m * (d ^ j * c ^ i) := by
      rw [← mul_assoc]
      exact e1
    have e2 : (d ^ k₁) ^ m = 1 := mul_eq_right.mp (mul_left_cancel e3)
    rw [← pow_mul] at e2
    have hm := hpow1 hk₁ hk₁0 e2
    have e4 : x₂ * (a ^ m * (d ^ j * c ^ i)) * x₂⁻¹ = a ^ m * (d ^ j * c ^ i) := by
      rw [← hz x₂ hx₂Q, mul_inv_cancel_right]
    rw [hconj3, hx₂a, hx₂d, hx₂c,
      (Commute.mul_pow (hcomm c hcA _ (hdk k₂)) i)] at e4
    have e5 : (d ^ k₂) ^ i = 1 := by
      have e6 := mul_left_cancel (mul_left_cancel e4)
      exact mul_eq_left.mp e6
    rw [← pow_mul] at e5
    have hi := hpow1 hk₂ hk₂0 e5
    rw [hpow3 (h3 a haA) hm, hpow3 (h3 c hcA) hi, one_mul, mul_one]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers d) j
  have hcommA : ∀ x ∈ A, ∀ y ∈ Q, ⁅x, y⁆ ∈ Subgroup.zpowers d := by
    intro x hx y hy
    have hδ := hQA y hy x hx
    have e : ⁅x, y⁆ = x * (x⁻¹ * (y * x * y⁻¹))⁻¹ * x⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [e, hZc x (hAQ hx) _ (Subgroup.inv_mem _ hδ)]
    exact Subgroup.inv_mem _ hδ
  have hcommA' : ∀ x ∈ Q, ∀ y ∈ A, ⁅x, y⁆ ∈ Subgroup.zpowers d := by
    intro x hx y hy
    rw [← commutatorElement_inv]
    exact Subgroup.inv_mem _ (hcommA y hy x hx)
  have hx₁N : x₁ ∈ Subgroup.normalizer (A : Set G) := hQN hx₁Q
  have hx₂N : x₂ ∈ Subgroup.normalizer (A : Set G) := hQN hx₂Q
  have hφ : A.normalizerMonoidHom ⟨x₁, hx₁N⟩ * A.normalizerMonoidHom ⟨x₂, hx₂N⟩ =
      A.normalizerMonoidHom ⟨x₂, hx₂N⟩ * A.normalizerMonoidHom ⟨x₁, hx₁N⟩ := by
    apply MulEquiv.toMonoidHom_injective
    refine MonoidHom.eq_of_eqOn_dense (closure_basis_eq_top hcomm h3 h27 haA hdA hcA hB9 haB) ?_
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    apply Subtype.ext
    simp only [MulEquiv.coe_toMonoidHom, MulAut.mul_apply]
    rcases hy with rfl | rfl | rfl
    · rw [Sec4.normalizerMonoidHom_apply_coe, Sec4.normalizerMonoidHom_apply_coe,
        Sec4.normalizerMonoidHom_apply_coe, Sec4.normalizerMonoidHom_apply_coe]
      simp only
      rw [hx₂a, hx₁a, conj_mul_pow, hx₂a, hx₂d]
    · rw [Sec4.normalizerMonoidHom_apply_coe, Sec4.normalizerMonoidHom_apply_coe,
        Sec4.normalizerMonoidHom_apply_coe, Sec4.normalizerMonoidHom_apply_coe]
      simp only
      rw [hx₂d, hx₁d, hx₂d]
    · rw [Sec4.normalizerMonoidHom_apply_coe, Sec4.normalizerMonoidHom_apply_coe,
        Sec4.normalizerMonoidHom_apply_coe, Sec4.normalizerMonoidHom_apply_coe]
      simp only
      rw [hx₂c, hx₁c, conj_mul_pow, hx₁c, hx₁d, hx₂c]
  have hW : ∀ y ∈ A, x₁ * (x₂ * y * x₂⁻¹) * x₁⁻¹ = x₂ * (x₁ * y * x₁⁻¹) * x₂⁻¹ := by
    intro y hy
    have e1 := congrArg (fun φ : MulAut A => ((φ ⟨y, hy⟩ : A) : G)) hφ
    simp only [MulAut.mul_apply, Sec4.normalizerMonoidHom_apply_coe] at e1
    exact e1
  set z := ⁅x₁, x₂⁆ with hzdef
  have hzQ : z ∈ Q := by
    rw [hzdef, commutatorElement_def]
    exact Q.mul_mem (Q.mul_mem (Q.mul_mem hx₁Q hx₂Q) (Q.inv_mem hx₁Q)) (Q.inv_mem hx₂Q)
  have hzA : z ∈ A := by
    rw [← hCQ]
    refine ⟨hzQ, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    have hgN : (x₂ * x₁)⁻¹ ∈ Subgroup.normalizer (A : Set G) :=
      hQN (Q.inv_mem (Q.mul_mem hx₂Q hx₁Q))
    have hu : (x₂ * x₁)⁻¹ * y * (x₂ * x₁)⁻¹⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hgN y).mp hy
    have e1 := hW _ hu
    have e2 : x₂ * (x₁ * ((x₂ * x₁)⁻¹ * y * (x₂ * x₁)⁻¹⁻¹) * x₁⁻¹) * x₂⁻¹ = y := by group
    rw [e2] at e1
    rw [hzdef, commutatorElement_def]
    calc y * (x₁ * x₂ * x₁⁻¹ * x₂⁻¹) =
        (x₁ * (x₂ * ((x₂ * x₁)⁻¹ * y * (x₂ * x₁)⁻¹⁻¹) * x₂⁻¹) * x₁⁻¹) *
          (x₁ * x₂ * x₁⁻¹ * x₂⁻¹) := by rw [e1]
      _ = (x₁ * x₂ * x₁⁻¹ * x₂⁻¹) * y := by group
  have hzc : ∀ q ∈ Q, z * q = q * z := by
    intro q hq
    obtain ⟨m₁, m₂, a₀, ha₀, rfl⟩ := hrepr q hq
    have c1 : Commute z x₁ := commute_commutatorElement_left hQ3 hx₁Q hx₂Q
    have c2 : Commute z x₂ := commute_commutatorElement_right hQ3 hx₁Q hx₂Q
    have c3 : Commute z a₀ := hcomm z hzA a₀ ha₀
    exact ((c2.pow_right m₂).mul_right (c1.pow_right m₁)).mul_right c3
  have hzd : z ∈ Subgroup.zpowers d := hcent z hzQ hzc
  have hS : Subgroup.closure ((A : Set G) ∪ {x₁, x₂}) = Q := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro y (hy | hy | hy)
      · exact hAQ hy
      · rw [hy]
        exact hx₁Q
      · rw [Set.mem_singleton_iff.mp hy]
        exact hx₂Q
    · intro q hq
      obtain ⟨m₁, m₂, a₀, ha₀, rfl⟩ := hrepr q hq
      refine Subgroup.mul_mem _ (Subgroup.mul_mem _
        (Subgroup.pow_mem _ (Subgroup.subset_closure ?_) _)
        (Subgroup.pow_mem _ (Subgroup.subset_closure ?_) _)) (Subgroup.subset_closure ?_)
      · exact Or.inr (Or.inr rfl)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl ha₀
  have hSQ : ∀ x ∈ (A : Set G) ∪ {x₁, x₂}, x ∈ Q := by
    rintro y (hy | hy | hy)
    · exact hAQ hy
    · rw [hy]
      exact hx₁Q
    · rw [Set.mem_singleton_iff.mp hy]
      exact hx₂Q
  have hcommQ := commutatorElement_mem_of_closure hZc hS (fun x hx y hy => by
    rcases hx with hx | rfl | rfl
    · exact hcommA x hx y (hSQ y hy)
    · rcases hy with hy | rfl | rfl
      · exact hcommA' _ hx₁Q y hy
      · rw [commutatorElement_self]
        exact Subgroup.one_mem _
      · exact hzd
    · rcases hy with hy | rfl | rfl
      · exact hcommA' _ hx₂Q y hy
      · rw [← commutatorElement_inv]
        exact Subgroup.inv_mem _ hzd
      · rw [commutatorElement_self]
        exact Subgroup.one_mem _)
  have hka : ∀ (i j : ℕ) (a₀ : G), a₀ ∈ A →
      (x₂ ^ j * x₁ ^ i * a₀) * a * (x₂ ^ j * x₁ ^ i * a₀)⁻¹ = a * d ^ (k₁ * i) := by
    intro i j a₀ ha₀
    have e1 : (x₂ ^ j * x₁ ^ i * a₀) * a * (x₂ ^ j * x₁ ^ i * a₀)⁻¹ =
        x₂ ^ j * (x₁ ^ i * (a₀ * a * a₀⁻¹) * (x₁ ^ i)⁻¹) * (x₂ ^ j)⁻¹ := by group
    rw [e1, show a₀ * a * a₀⁻¹ = a by rw [hcomm a₀ ha₀ a haA, mul_inv_cancel_right],
      conj_pow_eq_mul_pow hx₁d hx₁a, conj_mul_pow, conj_pow_eq_of_conj_eq hx₂a,
      conj_pow_eq_of_conj_eq hx₂d]
  have hkc : ∀ (i j : ℕ) (a₀ : G), a₀ ∈ A →
      (x₂ ^ j * x₁ ^ i * a₀) * c * (x₂ ^ j * x₁ ^ i * a₀)⁻¹ = c * d ^ (k₂ * j) := by
    intro i j a₀ ha₀
    have e1 : (x₂ ^ j * x₁ ^ i * a₀) * c * (x₂ ^ j * x₁ ^ i * a₀)⁻¹ =
        x₂ ^ j * (x₁ ^ i * (a₀ * c * a₀⁻¹) * (x₁ ^ i)⁻¹) * (x₂ ^ j)⁻¹ := by group
    rw [e1, show a₀ * c * a₀⁻¹ = c by rw [hcomm a₀ ha₀ c hcA, mul_inv_cancel_right],
      conj_pow_eq_of_conj_eq hx₁c, conj_pow_eq_mul_pow hx₂d hx₂c]
  have hinj : ∀ {k : ℕ}, k < 3 → k ≠ 0 → ∀ {i i' : ℕ}, i < 3 → i' < 3 →
      d ^ (k * i) = d ^ (k * i') → i = i' := by
    intro k hk hk0 i i' hi hi' h
    rw [pow_eq_pow_iff_modEq, hod] at h
    unfold Nat.ModEq at h
    have hk' : k = 1 ∨ k = 2 := by omega
    rcases hk' with rfl | rfl <;> omega
  have hcard : Nat.card Q = 3 ^ 5 := by
    let f : Fin 3 × Fin 3 × A → Q := fun p => ⟨x₂ ^ (p.2.1 : ℕ) * x₁ ^ (p.1 : ℕ) * (p.2.2 : G),
      Q.mul_mem (Q.mul_mem (Q.pow_mem hx₂Q _) (Q.pow_mem hx₁Q _)) (hAQ p.2.2.2)⟩
    have hf : Function.Bijective f := by
      constructor
      · rintro ⟨i, j, a₀⟩ ⟨i', j', a₀'⟩ h
        have h' : x₂ ^ (j : ℕ) * x₁ ^ (i : ℕ) * (a₀ : G) =
            x₂ ^ (j' : ℕ) * x₁ ^ (i' : ℕ) * (a₀' : G) := congrArg Subtype.val h
        have hii : i = i' := by
          have e1 := hka i j a₀ a₀.2
          rw [h', hka i' j' a₀' a₀'.2] at e1
          exact Fin.ext (hinj hk₁ hk₁0 i.2 i'.2 (mul_left_cancel e1).symm)
        have hjj : j = j' := by
          have e1 := hkc i j a₀ a₀.2
          rw [h', hkc i' j' a₀' a₀'.2] at e1
          exact Fin.ext (hinj hk₂ hk₂0 j.2 j'.2 (mul_left_cancel e1).symm)
        subst hii hjj
        have ha : a₀ = a₀' := Subtype.ext (mul_left_cancel h')
        rw [ha]
      · intro q
        obtain ⟨m₁, m₂, a₀, ha₀, hq⟩ := hrepr q q.2
        refine ⟨(⟨m₁ % 3, Nat.mod_lt _ (by norm_num)⟩, ⟨m₂ % 3, Nat.mod_lt _ (by norm_num)⟩,
          ⟨a₀, ha₀⟩), Subtype.ext ?_⟩
        show x₂ ^ (m₂ % 3) * x₁ ^ (m₁ % 3) * a₀ = q
        rw [hq, ← Item21LateProof.pow_eq_pow_mod_three (hQ3 x₂ hx₂Q),
          ← Item21LateProof.pow_eq_pow_mod_three (hQ3 x₁ hx₁Q)]
    rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod, Nat.card_prod, Nat.card_fin,
      h27]
    norm_num
  have hexp : Monoid.exponent Q = 3 := by
    have : Nontrivial Q := ⟨⟨⟨d, hdQ⟩, 1, fun h => hd1 (congrArg Subtype.val h)⟩⟩
    rw [Monoid.exponent_eq_prime_iff Nat.prime_three]
    intro g hg
    exact orderOf_eq_prime (Subtype.ext (by simpa using hQ3 g g.2)) hg
  have hext : IsExtraspecialPGroup 3 Q := by
    refine isExtraspecialPGroup_three_of (Z := (Subgroup.zpowers d).subgroupOf Q) ?_ ?_ ?_ ?_
      ?_ ?_ ?_
    · intro g
      exact ⟨1, Subtype.ext (by simpa using hQ3 g g.2)⟩
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hdQ)).toEquiv,
        Nat.card_zpowers, hod]
    · intro w hw
      rw [Subgroup.mem_center_iff]
      intro q
      apply Subtype.ext
      have hw' : (w : G) ∈ Subgroup.zpowers d := Subgroup.mem_subgroupOf.mp hw
      have e1 := hZc q q.2 w hw'
      simp only [Subgroup.coe_mul]
      calc (q : G) * (w : G) = ((q : G) * (w : G) * (q : G)⁻¹) * (q : G) := by group
        _ = (w : G) * (q : G) := by rw [e1]
    · intro x y
      rw [Subgroup.mem_subgroupOf]
      have e1 := hcommQ x x.2 y y.2
      simpa [commutatorElement_def] using e1
    · intro x
      rw [Subgroup.mem_subgroupOf]
      have e1 : ((x ^ 3 : Q) : G) = 1 := by simpa using hQ3 x x.2
      rw [e1]
      exact Subgroup.one_mem _
    · intro x hx
      rw [Subgroup.mem_subgroupOf]
      exact hcent x x.2 (fun q hq => congrArg Subtype.val (hx ⟨q, hq⟩))
    · refine ⟨⟨x₁, hx₁Q⟩, fun h => ?_⟩
      have h1 : x₁ ∈ Subgroup.zpowers d := Subgroup.mem_subgroupOf.mp h
      have h2 : x₁ ∈ A := Subgroup.zpowers_le.mpr hdA h1
      have e1 : x₁ * a * x₁⁻¹ = a := by rw [hcomm x₁ h2 a haA, mul_inv_cancel_right]
      rw [hx₁a] at e1
      have e2 : d ^ (k₁ * 1) = 1 := by rw [mul_one]; exact mul_eq_left.mp e1
      have := hpow1 hk₁ hk₁0 e2
      omega
  exact ⟨hext, hcard, hexp⟩

end Claim

end CFSG.RankThree.PartTwo.Sec21.Item2119EndProof

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open Item2119EndProof

theorem item2127QExtra_of
    (h211 : Item211) (h2116 : Item2116) (h45 : Sec4.Item4_5)
    (h66 : Sec6.Item6_6) : Item2127QExtra := by
  intro G _ _ A E U c L d U₀ a X hE h23 _ _ _ _ F _ hQ
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨eXL⟩, hdX, hdTX, -⟩ := h23
  have hcfg := hE.cfg
  have hpair := hcfg.pair
  obtain ⟨n, -, -, ⟨eL⟩⟩ := hcfg.lthree
  have hpair' : Sec21Pair G A E U₀ a X :=
    { toSec21Std := hpair.toSec21Std
      mem_E := hpair.mem_E
      mem_U := hE.mem_U₀.1
      mem_pair := hE.mem_pair }
  obtain ⟨hn', he', hC', h27', hS3'⟩ :=
    Item21LateProof.case7_of_lBar_L3 h211 h2116 hpair' (eXL.trans eL)
  have hcfgX : Config2119 G A E U₀ a X :=
    ⟨hpair', ⟨n, hn', he', ⟨eXL.trans eL⟩⟩, hC', h27', hS3'⟩
  obtain ⟨hcL, d₀, -, -, -, hTU, -, -, -, ⟨w, ⟨hwL, hwN⟩, -, hwd₀, hwA, hwmove⟩, -⟩ :=
    Item21Late2Proof.frame_of h45 h66 hcfg
  obtain ⟨-, d', -, -, -, hTU', -, -, -, ⟨w', ⟨hw'X, hw'N⟩, -, hw'd', hw'A, hw'move⟩, -⟩ :=
    Item21Late2Proof.frame_of h45 h66 hcfgX
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hpairs' := mem_lThreeStarPairs_iff.mp hE.mem_pair
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have h3 : ∀ x ∈ A, x ^ 3 = 1 := hAe.2
  have h27 : Nat.card A = 27 := by rw [hcfg.card]; norm_num
  have hcA : c ∈ A := hpair.mem_E.2 hpairs.1.1
  have haA : a ∈ A := hpair.mem_E.2 hpairs'.1.1
  have hdA : d ∈ A := hE.mem_d.1
  have hdL : d ∈ L := hE.mem_d.2
  have hd1 := hE.ne_one_d
  have hd3 : d ^ 3 = 1 := h3 d hdA
  have hLC : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt (lZeroStarAt_subset A c hpairs.2.2.1)
  have hXC : X ≤ Subgroup.centralizer ({a} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt (lZeroStarAt_subset A a hpairs'.2.2.1)
  have hwc : w * c * w⁻¹ = c := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp (hLC hwL), mul_inv_cancel_right]
  have hw'a : w' * a * w'⁻¹ = a := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp (hXC hw'X), mul_inv_cancel_right]
  have hZ₀ : Subgroup.zpowers d₀ = Subgroup.zpowers d :=
    zpowers_eq_of_eq_or_eq_inv (hTU d hE.mem_d hd1 hE.type_d)
  have hZ' : Subgroup.zpowers d' = Subgroup.zpowers d :=
    zpowers_eq_of_eq_or_eq_inv (hTU' d ⟨hdA, hdX⟩ hd1 hdTX)
  have hwd : w * d * w⁻¹ = d :=
    Item21LateProof.conj_eq_of_mem_zpowers hwd₀ (by rw [hZ₀]; exact Subgroup.mem_zpowers d)
  have hw'd : w' * d * w'⁻¹ = d :=
    Item21LateProof.conj_eq_of_mem_zpowers hw'd' (by rw [hZ']; exact Subgroup.mem_zpowers d)
  rw [hZ₀] at hwA
  rw [hZ'] at hw'A
  have hcd : c ∉ Subgroup.zpowers d := fun h => hcL ((Subgroup.zpowers_le.mpr hdL) h)
  have haB : a ∉ Subgroup.zpowers d ⊔ Subgroup.zpowers c := by
    rw [sup_comm]
    exact not_mem_sup_of_config2119End hE
  have hB9 := Item21LateProof.card_zpowers_sup_zpowers (hcomm d hdA c hcA) hd3 (h3 c hcA) hd1 hcd
  obtain ⟨k₁, hk₁, hk₁e⟩ := Item21LateProof.exists_pow_lt_three_of_mem_zpowers hd3 (hwA a haA)
  have hwa : w * a * w⁻¹ = a * d ^ k₁ := by
    rw [← hk₁e]
    group
  have hk₁0 : k₁ ≠ 0 := by
    rintro rfl
    rw [pow_zero, mul_one] at hwa
    obtain ⟨y, hyA, hy⟩ := hwmove
    exact hy (conj_eq_of_fix_basis hcomm h3 h27 hcA hdA haA hB9 haB hwa hwd hwc y hyA)
  obtain ⟨k₂, hk₂, hk₂e⟩ := Item21LateProof.exists_pow_lt_three_of_mem_zpowers hd3 (hw'A c hcA)
  have hw'c : w' * c * w'⁻¹ = c * d ^ k₂ := by
    rw [← hk₂e]
    group
  have hk₂0 : k₂ ≠ 0 := by
    rintro rfl
    rw [pow_zero, mul_one] at hw'c
    obtain ⟨y, hyA, hy⟩ := hw'move
    exact hy (conj_eq_of_fix_basis hcomm h3 h27 hcA hdA haA hB9 haB hw'a hw'd hw'c y hyA)
  obtain ⟨hSyl, hCQ, hstar, hunion, hAF⟩ := hQ
  have hAQ : A ≤ q2127Of A d F :=
    calc A = q2127Of A d F ⊓ Subgroup.centralizer (A : Set G) := hCQ.symm
      _ ≤ q2127Of A d F := inf_le_left
  have hQN : q2127Of A d F ≤ Subgroup.normalizer (A : Set G) := by
    obtain ⟨P, hP⟩ := hSyl
    rw [← hP]
    exact Subgroup.map_subtype_le _
  have hQ3 : ∀ x ∈ q2127Of A d F, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨e, he, hed, hxe⟩ := hunion x hx
    exact (hAF e he hed).2 x hxe
  have hQT : ∀ x (hx : x ∈ q2127Of A d F), A.normalizerMonoidHom ⟨x, hQN hx⟩ ∈
      trivOnQuot A (Subgroup.zpowers d) ⊓ fixOn A (Subgroup.zpowers d) := by
    intro x hx
    rw [← hstar]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx)
  have hQA : ∀ x ∈ q2127Of A d F, ∀ y ∈ A, y⁻¹ * (x * y * x⁻¹) ∈ Subgroup.zpowers d :=
    fun x hx y hy => (hQT x hx).1 ⟨y, hy⟩
  have hQd : ∀ x ∈ q2127Of A d F, x * d * x⁻¹ = d := fun x hx =>
    congrArg Subtype.val ((hQT x hx).2 ⟨d, hdA⟩ (Subgroup.mem_zpowers d))
  have hT : ∀ (v : G) (hvN : v ∈ Subgroup.normalizer (A : Set G)), v * d * v⁻¹ = d →
      (∀ y ∈ A, y⁻¹ * (v * y * v⁻¹) ∈ Subgroup.zpowers d) →
      A.normalizerMonoidHom ⟨v, hvN⟩ ∈ starOf A (q2127Of A d F) := by
    intro v hvN hvd hvA
    rw [hstar]
    exact ⟨fun y => hvA y y.2, fun y hy => Subtype.ext (by
      rw [Sec4.normalizerMonoidHom_apply_coe]
      exact Item21LateProof.conj_eq_of_mem_zpowers hvd hy)⟩
  obtain ⟨⟨x₁, hx₁N⟩, hx₁Q, hx₁e⟩ := hT w hwN hwd hwA
  obtain ⟨⟨x₂, hx₂N⟩, hx₂Q, hx₂e⟩ := hT w' hw'N hw'd hw'A
  have hx₁Q' : x₁ ∈ q2127Of A d F := Subgroup.mem_subgroupOf.mp hx₁Q
  have hx₂Q' : x₂ ∈ q2127Of A d F := Subgroup.mem_subgroupOf.mp hx₂Q
  have hact : ∀ {v x : G} (hvN : v ∈ Subgroup.normalizer (A : Set G))
      (hxN : x ∈ Subgroup.normalizer (A : Set G)),
      A.normalizerMonoidHom ⟨x, hxN⟩ = A.normalizerMonoidHom ⟨v, hvN⟩ →
        ∀ y ∈ A, x * y * x⁻¹ = v * y * v⁻¹ := fun hvN hxN h y hy =>
    congrArg (fun φ : MulAut A => ((φ ⟨y, hy⟩ : A) : G)) h
  have hx₁c : x₁ * c * x₁⁻¹ = c := (hact hwN hx₁N hx₁e c hcA).trans hwc
  have hx₁d : x₁ * d * x₁⁻¹ = d := (hact hwN hx₁N hx₁e d hdA).trans hwd
  have hx₁a : x₁ * a * x₁⁻¹ = a * d ^ k₁ := (hact hwN hx₁N hx₁e a haA).trans hwa
  have hx₂a : x₂ * a * x₂⁻¹ = a := (hact hw'N hx₂N hx₂e a haA).trans hw'a
  have hx₂d : x₂ * d * x₂⁻¹ = d := (hact hw'N hx₂N hx₂e d hdA).trans hw'd
  have hx₂c : x₂ * c * x₂⁻¹ = c * d ^ k₂ := (hact hw'N hx₂N hx₂e c hcA).trans hw'c
  have hrepr : ∀ q ∈ q2127Of A d F, ∃ m₁ m₂ : ℕ, ∃ a₀ ∈ A, q = x₂ ^ m₂ * x₁ ^ m₁ * a₀ := by
    intro q hq
    have hqT := hQT q hq
    obtain ⟨m₁, m₂, heq⟩ := exists_eq_mul_of_mem_trivOnQuot hcomm h3 h27 hcA hdA haA hB9 haB
      hx₁N hx₂N hx₁c hx₁d hk₁ hk₁0 hx₁a hx₂a hx₂d hk₂ hk₂0 hx₂c hqT.1
      (hqT.2 ⟨d, hdA⟩ (Subgroup.mem_zpowers d))
    refine ⟨m₁, m₂, (x₂ ^ m₂ * x₁ ^ m₁)⁻¹ * q, ?_, by group⟩
    have hmem : (x₂ ^ m₂ * x₁ ^ m₁)⁻¹ * q ∈
        q2127Of A d F ⊓ Subgroup.centralizer (A : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mul_mem _
        (Subgroup.pow_mem _ hx₂Q' _) (Subgroup.pow_mem _ hx₁Q' _))) hq, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have e1 := congrArg (fun φ : MulAut A => ((φ ⟨y, hy⟩ : A) : G)) heq
      simp only [MulAut.mul_apply, Sec4.normalizerMonoidHom_apply_coe] at e1
      calc y * ((x₂ ^ m₂ * x₁ ^ m₁)⁻¹ * q) =
          (x₂ ^ m₂ * x₁ ^ m₁)⁻¹ * (x₂ ^ m₂ * (x₁ ^ m₁ * y * (x₁ ^ m₁)⁻¹) * (x₂ ^ m₂)⁻¹) * q := by
            group
        _ = (x₂ ^ m₂ * x₁ ^ m₁)⁻¹ * (q * y * q⁻¹) * q := by rw [e1]
        _ = ((x₂ ^ m₂ * x₁ ^ m₁)⁻¹ * q) * y := by group
    rw [hCQ] at hmem
    exact hmem
  exact isExtra2127_of hcomm h3 h27 hcA hdA haA hd1 hB9 haB hAQ hQN hCQ hQ3 hQA hQd hx₁Q' hx₂Q'
    hx₁c hx₁d hk₁ hk₁0 hx₁a hx₂a hx₂d hk₂ hk₂0 hx₂c hrepr

end CFSG.RankThree.PartTwo.Sec21
