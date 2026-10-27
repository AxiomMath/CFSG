module

public import CFSG.Timmesfeld.Exceptional.DeepNear

public section

namespace CFSG.Timmesfeld.Moufang.Deep

open CFSG.Timmesfeld CFSG.Timmesfeld.Moufang
open scoped Pointwise

variable {G : Type*} [Group G]

@[expose] def SameLine (p a q : G) : Prop := q = a ∨ q = p * a

theorem sameLine_refl (p a : G) : SameLine p a a := Or.inl rfl

theorem sameLine_symm {p a q : G} (hp : p * p = 1) (h : SameLine p a q) : SameLine p q a := by
  rcases h with rfl | rfl
  · exact Or.inl rfl
  · right
    rw [← mul_assoc, hp, one_mul]

theorem sameLine_trans {p a q r : G} (hp : p * p = 1) (h₁ : SameLine p a q)
    (h₂ : SameLine p q r) : SameLine p a r := by
  rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · left
    rw [← mul_assoc, hp, one_mul]

theorem sameLine_conj {p g a q : G} (hgp : Commute g p) (h : SameLine p a q) :
    SameLine p (g * a * g⁻¹) (g * q * g⁻¹) := by
  rcases h with rfl | rfl
  · exact Or.inl rfl
  · right
    rw [show g * (p * a) * g⁻¹ = g * p * g⁻¹ * (g * a * g⁻¹) by group, hgp.eq,
      mul_inv_cancel_right]

theorem commute_of_conj_eq_mul {p z q : G} (hp : p * p = 1) (hz3 : z ^ 3 = 1)
    (hzp : Commute z p) (h : z * q * z⁻¹ = p * q) : Commute z q := by
  have h2 : z * (z * q * z⁻¹) * z⁻¹ = q := by
    rw [h, show z * (p * q) * z⁻¹ = z * p * z⁻¹ * (z * q * z⁻¹) by group, hzp.eq,
      mul_inv_cancel_right, h, ← mul_assoc, hp, one_mul]
  have hz3' : z * z * z = 1 := by rw [mul_assoc, ← pow_three]; exact hz3
  have h3 : z * q * z⁻¹ = z * z * z * q * (z * z * z)⁻¹ := by
    calc z * q * z⁻¹ = z * (z * (z * q * z⁻¹) * z⁻¹) * z⁻¹ := by rw [h2]
      _ = z * z * z * q * (z * z * z)⁻¹ := by group
  rw [hz3', one_mul, inv_one, mul_one] at h3
  exact mul_inv_eq_iff_eq_mul.1 h3

theorem not_sameLine_conj {p z q : G} (hp : p * p = 1) (hz3 : z ^ 3 = 1) (hzp : Commute z p)
    (hzq : ¬ Commute z q) : ¬ SameLine p q (z * q * z⁻¹) := by
  rintro (h | h)
  · exact hzq (mul_inv_eq_iff_eq_mul.1 h)
  · exact hzq (commute_of_conj_eq_mul hp hz3 hzp h)

theorem sameLine_cover [Finite G] {p z : G} (hp : p * p = 1) (hp1 : p ≠ 1) (hzp : Commute z p)
    (hz3 : z ^ 3 = 1) {O : Set G} (hO6 : O.ncard = 6) (hOp : ∀ q ∈ O, p * q ∈ O)
    (hzO : ∀ q ∈ O, z * q * z⁻¹ ∈ O) (hzf : ∀ q ∈ O, ¬ Commute z q) {y : G} (hy : y ∈ O) :
    ∀ q ∈ O, SameLine p y q ∨ SameLine p (z * y * z⁻¹) q ∨
      SameLine p (z * (z * y * z⁻¹) * z⁻¹) q := by
  set y₁ := z * y * z⁻¹
  set y₂ := z * y₁ * z⁻¹
  have hy₁ : y₁ ∈ O := hzO y hy
  have hy₂ : y₂ ∈ O := hzO y₁ hy₁
  have hz3' : z * z * z = 1 := by rw [mul_assoc, ← pow_three]; exact hz3
  have hzy₂ : z * y₂ * z⁻¹ = y := by
    calc z * y₂ * z⁻¹ = z * z * z * y * (z * z * z)⁻¹ := by simp only [y₂, y₁]; group
      _ = y := by rw [hz3', one_mul, inv_one, mul_one]
  have n01 : ¬ SameLine p y y₁ := not_sameLine_conj hp hz3 hzp (hzf y hy)
  have n12 : ¬ SameLine p y₁ y₂ := not_sameLine_conj hp hz3 hzp (hzf y₁ hy₁)
  have n20 : ¬ SameLine p y₂ y := by
    have := not_sameLine_conj hp hz3 hzp (hzf y₂ hy₂)
    rwa [hzy₂] at this
  have hmem : ∀ a q : G, q ∈ ({a, p * a} : Set G) ↔ SameLine p a q := fun a q => by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, SameLine]
  have hdisj : ∀ a b : G, ¬ SameLine p a b → Disjoint ({a, p * a} : Set G) {b, p * b} := by
    intro a b hab
    rw [Set.disjoint_left]
    intro q hqa hqb
    exact hab (sameLine_trans hp ((hmem a q).1 hqa) (sameLine_symm hp ((hmem b q).1 hqb)))
  have hcard : ∀ a : G, ({a, p * a} : Set G).ncard = 2 := fun a => Set.ncard_pair fun h => hp1 (by
    have := congrArg (· * a⁻¹) h
    simpa using this.symm)
  have hsub : ∀ a ∈ O, ({a, p * a} : Set G) ⊆ O := by
    rintro a ha q (rfl | rfl)
    exacts [ha, hOp a ha]
  set T : Set G := {y, p * y} ∪ ({y₁, p * y₁} ∪ {y₂, p * y₂})
  have hTO : T ⊆ O := Set.union_subset (hsub y hy) (Set.union_subset (hsub y₁ hy₁) (hsub y₂ hy₂))
  have hT6 : T.ncard = 6 := by
    rw [Set.ncard_union_eq _ (Set.toFinite _) (Set.toFinite _),
      Set.ncard_union_eq (hdisj _ _ n12) (Set.toFinite _) (Set.toFinite _), hcard, hcard, hcard]
    exact Set.disjoint_union_right.2 ⟨hdisj _ _ n01,
      hdisj _ _ fun h => n20 (sameLine_symm hp h)⟩
  have hT : T = O := Set.eq_of_subset_of_ncard_le hTO (by rw [hT6, hO6]) (Set.toFinite _)
  intro q hq
  rw [← hT] at hq
  rcases hq with hq | hq | hq
  · exact Or.inl ((hmem _ _).1 hq)
  · exact Or.inr (Or.inl ((hmem _ _).1 hq))
  · exact Or.inr (Or.inr ((hmem _ _).1 hq))

theorem sameLine_of_sameLine [Finite G] {p z z' : G} (hp : p * p = 1) (hp1 : p ≠ 1)
    (hzp : Commute z p) (hz'p : Commute z' p) (hz3 : z ^ 3 = 1) (hz'3 : z' ^ 3 = 1)
    {O : Set G} (hO6 : O.ncard = 6) (hOp : ∀ q ∈ O, p * q ∈ O)
    (hzO : ∀ q ∈ O, z * q * z⁻¹ ∈ O) (hz'O : ∀ q ∈ O, z' * q * z'⁻¹ ∈ O)
    (hzf : ∀ q ∈ O, ¬ Commute z q) (hz'f : ∀ q ∈ O, ¬ Commute z' q) {y : G} (hy : y ∈ O)
    (hψ : SameLine p (z * y * z⁻¹) (z' * y * z'⁻¹)) :
    ∀ q ∈ O, SameLine p q ((z⁻¹ * z') * q * (z⁻¹ * z')⁻¹) := by
  have hcov := sameLine_cover hp hp1 hzp hz3 hO6 hOp hzO hzf hy
  set y₁ := z * y * z⁻¹
  set y₂ := z * y₁ * z⁻¹
  have hy₁ : y₁ ∈ O := hzO y hy
  have hy₂ : y₂ ∈ O := hzO y₁ hy₁
  have hz3' : z * z * z = 1 := by rw [mul_assoc, ← pow_three]; exact hz3
  have hz'3' : z' * z' * z' = 1 := by rw [mul_assoc, ← pow_three]; exact hz'3
  have hzy₂ : z * y₂ * z⁻¹ = y := by
    calc z * y₂ * z⁻¹ = z * z * z * y * (z * z * z)⁻¹ := by simp only [y₂, y₁]; group
      _ = y := by rw [hz3', one_mul, inv_one, mul_one]
  have n20 : ¬ SameLine p y₂ y := by
    have := not_sameLine_conj hp hz3 hzp (hzf y₂ hy₂)
    rwa [hzy₂] at this
  have hzi₁ : z⁻¹ * y₁ * z⁻¹⁻¹ = y := by simp only [y₁]; group
  have hzi₂ : z⁻¹ * y₂ * z⁻¹⁻¹ = y₁ := by simp only [y₂]; group
  have hzi₀ : z⁻¹ * y * z⁻¹⁻¹ = y₂ := by
    rw [← hzy₂]
    group
  have nA : ∀ q ∈ O, ¬ SameLine p q (z' * q * z'⁻¹) := fun q hq =>
    not_sameLine_conj hp hz'3 hz'p (hz'f q hq)
  have hsq : ∀ q ∈ O, ¬ SameLine p q (z' * (z' * q * z'⁻¹) * z'⁻¹) := by
    intro q hq h
    have h' := sameLine_conj (hz'p.mul_left hz'p) h
    have e1 : z' * z' * q * (z' * z')⁻¹ = z' * (z' * q * z'⁻¹) * z'⁻¹ := by group
    have e2 : z' * z' * (z' * (z' * q * z'⁻¹) * z'⁻¹) * (z' * z')⁻¹ = z' * q * z'⁻¹ := by
      calc _ = z' * z' * z' * (z' * q * z'⁻¹) * (z' * z' * z')⁻¹ := by group
        _ = z' * q * z'⁻¹ := by rw [hz'3', one_mul, inv_one, mul_one]
    rw [e1, e2] at h'
    exact nA q hq (sameLine_trans hp h h')
  have hb : SameLine p y₂ (z' * y₁ * z'⁻¹) := by
    rcases hcov _ (hz'O y₁ hy₁) with h | h | h
    · exact absurd (sameLine_trans hp h (sameLine_conj hz'p hψ)) (hsq y hy)
    · exact absurd h (nA y₁ hy₁)
    · exact h
  have hc : SameLine p y (z' * y₂ * z'⁻¹) := by
    rcases hcov _ (hz'O y₂ hy₂) with h | h | h
    · exact h
    · exfalso
      have h2 := sameLine_conj hz'p.inv_left (sameLine_trans hp (sameLine_symm hp hψ) h)
      have e : ∀ a : G, z'⁻¹ * (z' * a * z'⁻¹) * z'⁻¹⁻¹ = a := fun a => by group
      rw [e, e] at h2
      exact n20 (sameLine_symm hp h2)
    · exact absurd h (nA y₂ hy₂)
  intro q hq
  have hg : (z⁻¹ * z') * q * (z⁻¹ * z')⁻¹ = z⁻¹ * (z' * q * z'⁻¹) * z⁻¹⁻¹ := by group
  rw [hg]
  rcases hcov q hq with h | h | h
  · have h2 := sameLine_conj hzp.inv_left (sameLine_trans hp hψ (sameLine_conj hz'p h))
    rw [hzi₁] at h2
    exact sameLine_trans hp (sameLine_symm hp h) h2
  · have h2 := sameLine_conj hzp.inv_left (sameLine_trans hp hb (sameLine_conj hz'p h))
    rw [hzi₂] at h2
    exact sameLine_trans hp (sameLine_symm hp h) h2
  · have h2 := sameLine_conj hzp.inv_left (sameLine_trans hp hc (sameLine_conj hz'p h))
    rw [hzi₀] at h2
    exact sameLine_trans hp (sameLine_symm hp h) h2

theorem exists_sameLine [Finite G] {p z z' : G} (hp : p * p = 1) (hp1 : p ≠ 1)
    (hzp : Commute z p) (hz'p : Commute z' p) (hz3 : z ^ 3 = 1) (hz'3 : z' ^ 3 = 1)
    {O : Set G} (hO6 : O.ncard = 6) (hOp : ∀ q ∈ O, p * q ∈ O)
    (hzO : ∀ q ∈ O, z * q * z⁻¹ ∈ O) (hz'O : ∀ q ∈ O, z' * q * z'⁻¹ ∈ O)
    (hzf : ∀ q ∈ O, ¬ Commute z q) (hz'f : ∀ q ∈ O, ¬ Commute z' q) :
    ∃ g, (g = z⁻¹ * z' ∨ g = z * z') ∧ ∀ q ∈ O, SameLine p q (g * q * g⁻¹) := by
  obtain ⟨y, hy⟩ : O.Nonempty := Set.nonempty_of_ncard_ne_zero (by rw [hO6]; decide)
  have hcov := sameLine_cover hp hp1 hzp hz3 hO6 hOp hzO hzf hy
  rcases hcov _ (hz'O y hy) with h | h | h
  · exact absurd h (not_sameLine_conj hp hz'3 hz'p (hz'f y hy))
  · exact ⟨_, Or.inl rfl, sameLine_of_sameLine hp hp1 hzp hz'p hz3 hz'3 hO6 hOp hzO hz'O hzf
      hz'f hy h⟩
  ·
    have hz3' : z * z * z = 1 := by rw [mul_assoc, ← pow_three]; exact hz3
    have hzi3 : z⁻¹ ^ 3 = 1 := by rw [inv_pow, hz3, inv_one]
    have hziO : ∀ q ∈ O, z⁻¹ * q * z⁻¹⁻¹ ∈ O := fun q hq => by
      have e : z⁻¹ * q * z⁻¹⁻¹ = z * (z * q * z⁻¹) * z⁻¹ := by
        calc z⁻¹ * q * z⁻¹⁻¹ = z⁻¹ * (z * z * z) * q * (z⁻¹ * (z * z * z))⁻¹ := by
              rw [hz3']; group
          _ = z * (z * q * z⁻¹) * z⁻¹ := by group
      rw [e]
      exact hzO _ (hzO q hq)
    have hzif : ∀ q ∈ O, ¬ Commute z⁻¹ q := fun q hq h => hzf q hq (by
      simpa using h.inv_left)
    have hzi : z⁻¹ * y * z⁻¹⁻¹ = z * (z * y * z⁻¹) * z⁻¹ := by
      calc z⁻¹ * y * z⁻¹⁻¹ = z⁻¹ * (z * z * z) * y * (z⁻¹ * (z * z * z))⁻¹ := by
            rw [hz3']; group
        _ = z * (z * y * z⁻¹) * z⁻¹ := by group
    refine ⟨z * z', Or.inr rfl, ?_⟩
    have := sameLine_of_sameLine hp hp1 hzp.inv_left hz'p hzi3 hz'3 hO6 hOp hziO hz'O hzif hz'f
      hy (by rw [hzi]; exact h)
    simpa using this

theorem ncard_le_four [Finite G] {M : Subgroup G} (hM : Nat.card M = 32) {z₀ : G}
    (hz₀ : orderOf z₀ = 3) (hnorm : z₀ ∈ Subgroup.normalizer (M : Set G)) {K : Subgroup G}
    (hK24 : 24 ≤ Nat.card K)
    (hKL : K ≤ M ⊔ Subgroup.zpowers z₀) (hKc : ∀ k ∈ K, Commute k z₀)
    {T : Set (Subgroup G)}
    (hT : ∀ Z ∈ T, ∃ z' ∈ M ⊔ Subgroup.zpowers z₀, orderOf z' = 3 ∧ Z = Subgroup.zpowers z') :
    T.ncard ≤ 4 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set L := M ⊔ Subgroup.zpowers z₀ with hL_def
  have hLmul : (L : Set G) = (M : Set G) * (Subgroup.zpowers z₀ : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left M _ ((Subgroup.zpowers_le).2 hnorm)
  have hLle : Nat.card L ≤ 96 := by
    have h := Set.natCard_mul_le (s := (M : Set G)) (t := (Subgroup.zpowers z₀ : Set G))
    rw [← hLmul] at h
    have h3 : Nat.card (Subgroup.zpowers z₀ : Set G) = 3 := by
      rw [show Nat.card (Subgroup.zpowers z₀ : Set G) = Nat.card (Subgroup.zpowers z₀) from rfl,
        Nat.card_zpowers, hz₀]
    have hM' : Nat.card (M : Set G) = 32 := hM
    rw [hM', h3] at h
    exact h
  have h32 : 32 ∣ Nat.card L := hM ▸ Subgroup.card_dvd_of_le le_sup_left
  have h3 : 3 ∣ Nat.card L := by
    have := Subgroup.card_dvd_of_le (le_sup_right : Subgroup.zpowers z₀ ≤ L)
    rwa [Nat.card_zpowers, hz₀] at this
  have hpos : 0 < Nat.card L := Nat.card_pos
  have hL96 : Nat.card L = 96 := by omega
  have hsyl : ∀ Z : Subgroup G, Z ≤ L → Nat.card Z = 3 →
      IsPGroup 3 (Z.subgroupOf L) ∧ ¬ 3 ∣ (Z.subgroupOf L).index := by
    intro Z hZ hZ3
    have hc : Nat.card (Z.subgroupOf L) = 3 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZ).toEquiv, hZ3]
    refine ⟨IsPGroup.of_card (n := 1) (by rw [hc, pow_one]), ?_⟩
    have := (Z.subgroupOf L).index_mul_card
    rw [hc, hL96] at this
    omega
  obtain ⟨hP1, hP2⟩ := hsyl _ le_sup_right (by rw [Nat.card_zpowers, hz₀])
  have hcardSyl : Nat.card (Sylow 3 L) ≤ 4 := by
    rw [Sylow.card_eq_index_normalizer (hP1.toSylow hP2)]
    have hle : K.subgroupOf L ≤ Subgroup.normalizer
        ((hP1.toSylow hP2 : Sylow 3 L) : Set L) := by
      intro k hk
      have hkz : Commute (k : G) z₀ := hKc _ (Subgroup.mem_subgroupOf.1 hk)
      have hfix : ∀ w ∈ Subgroup.zpowers z₀, (k : G) * w * (k : G)⁻¹ = w := by
        intro w hw
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
        rw [(hkz.zpow_right n).eq, mul_inv_cancel_right]
      show k ∈ Subgroup.normalizer (((Subgroup.zpowers z₀).subgroupOf L : Subgroup L) : Set L)
      rw [Subgroup.mem_normalizer_iff]
      intro h
      simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
      constructor
      · intro hh
        rw [hfix _ hh]
        exact hh
      · intro hh
        have hfix' : ∀ w ∈ Subgroup.zpowers z₀, (k : G)⁻¹ * w * (k : G) = w := by
          intro w hw
          obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
          rw [mul_assoc, ← (hkz.zpow_right n).eq, ← mul_assoc, inv_mul_cancel, one_mul]
        have e := hfix' _ hh
        rw [show (k : G)⁻¹ * ((k : G) * (h : G) * (k : G)⁻¹) * (k : G) = h by group] at e
        rw [e]
        exact hh
    have hKidx := (K.subgroupOf L).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKL).toEquiv, hL96] at hKidx
    have hidx : (K.subgroupOf L).index ≤ 4 := by
      by_contra h
      push Not at h
      nlinarith
    exact (Subgroup.index_antitone hle).trans hidx
  have hTL : ∀ Z ∈ T, Z ≤ L ∧ Nat.card Z = 3 := by
    intro Z hZ
    obtain ⟨z', hz'L, hz'3, rfl⟩ := hT Z hZ
    exact ⟨(Subgroup.zpowers_le).2 hz'L, by rw [Nat.card_zpowers, hz'3]⟩
  let f : T → Sylow 3 L := fun Z =>
    (hsyl Z.1 (hTL Z.1 Z.2).1 (hTL Z.1 Z.2).2).1.toSylow
      (hsyl Z.1 (hTL Z.1 Z.2).1 (hTL Z.1 Z.2).2).2
  have hf : Function.Injective f := by
    intro a b hab
    have h := congrArg (fun S : Sylow 3 L => (S : Subgroup L).map L.subtype) hab
    simp only [f, IsPGroup.toSylow_coe,
      Subgroup.map_subgroupOf_eq_of_le (hTL a.1 a.2).1,
      Subgroup.map_subgroupOf_eq_of_le (hTL b.1 b.2).1] at h
    exact Subtype.ext h
  rw [← Nat.card_coe_set_eq]
  exact (Nat.card_le_card_of_injective f hf).trans hcardSyl

end CFSG.Timmesfeld.Moufang.Deep
