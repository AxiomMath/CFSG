module

public import CFSG.Quasithin.Vol2.Ch5Sec1M23L34Perm

public section

namespace CFSG.Quasithin.H13

namespace M23Perm

open CFSG.M23.M23Group

variable {A : Subgroup ↥H0}

open Classical in
@[expose] noncomputable def orbA (A : Subgroup ↥H0) (w : Fin 23) : Finset (Fin 23) :=
  Finset.univ.filter fun p => ∃ a ∈ A, (a : ↥H0) • w = p

theorem mem_orbA {w p : Fin 23} : p ∈ orbA A w ↔ ∃ a ∈ A, (a : ↥H0) • w = p := by
  classical
  unfold orbA
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem self_mem_orbA (w : Fin 23) : w ∈ orbA A w :=
  mem_orbA.mpr ⟨1, A.one_mem, one_smul _ _⟩

theorem smul_mem_orbA {w p : Fin 23} {a : ↥H0} (ha : a ∈ A) (hp : p ∈ orbA A w) :
    a • p ∈ orbA A w := by
  obtain ⟨b, hb, rfl⟩ := mem_orbA.mp hp
  exact mem_orbA.mpr ⟨a * b, A.mul_mem ha hb, mul_smul a b w⟩

theorem smul_not_mem_orbA {w p : Fin 23} {a : ↥H0} (ha : a ∈ A) (hp : p ∉ orbA A w) :
    a • p ∉ orbA A w := fun h => hp (by
  have := smul_mem_orbA (A.inv_mem ha) h
  rwa [inv_smul_smul] at this)

theorem orbA_eq_of_mem {w p : Fin 23} (hp : p ∈ orbA A w) : orbA A p = orbA A w := by
  obtain ⟨b, hb, rfl⟩ := mem_orbA.mp hp
  ext q
  constructor
  · intro hq
    obtain ⟨c, hc, rfl⟩ := mem_orbA.mp hq
    exact mem_orbA.mpr ⟨c * b, A.mul_mem hc hb, mul_smul c b w⟩
  · intro hq
    obtain ⟨c, hc, rfl⟩ := mem_orbA.mp hq
    refine mem_orbA.mpr ⟨c * b⁻¹, A.mul_mem hc (A.inv_mem hb), ?_⟩
    rw [mul_smul, inv_smul_smul]

theorem card_orbA_dvd (w : Fin 23) : (orbA A w).card ∣ Nat.card A := by
  have h := MulAction.index_stabilizer (↥A) w
  have horb : (MulAction.orbit (↥A) w).ncard = (orbA A w).card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext p
    simp only [MulAction.mem_orbit_iff, Finset.mem_coe, mem_orbA]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, a.2, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
  rw [← horb, ← h]
  exact Subgroup.index_dvd_card _

@[expose] noncomputable def orbSub (A : Subgroup ↥H0) (w : Fin 23) : SubMulAction ↥A (Fin 23) where
  carrier := orbA A w
  smul_mem' a _ hp := smul_mem_orbA a.2 hp

theorem faithful_or_fixed [IsSimpleGroup ↥A] (w : Fin 23) :
    (∀ a ∈ A, (a : ↥H0) • w = w) ∨
      Function.Injective (MulAction.toPermHom ↥A ↥(orbSub A w)) := by
  set ρ := MulAction.toPermHom ↥A ↥(orbSub A w) with hρ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρ.ker with h | h
  · exact Or.inr ((MonoidHom.ker_eq_bot_iff ρ).mp h)
  · left
    intro a ha
    have hk : (⟨a, ha⟩ : ↥A) ∈ ρ.ker := by rw [h]; exact Subgroup.mem_top _
    rw [MonoidHom.mem_ker] at hk
    have h1 := congrArg (fun σ : Equiv.Perm ↥(orbSub A w) => ((σ ⟨w, self_mem_orbA w⟩ :
      ↥(orbSub A w)) : Fin 23)) hk
    simpa [hρ] using h1

theorem card_orbSub (w : Fin 23) : Nat.card ↥(orbSub A w) = (orbA A w).card := by
  have : Nat.card ↥(orbSub A w) = Nat.card ↥((orbA A w : Set (Fin 23))) := rfl
  rw [this, Nat.card_coe_set_eq, Set.ncard_coe_finset]

theorem eight_le_of_injective (hcard : Nat.card A = 20160) (w : Fin 23)
    (hinj : Function.Injective (MulAction.toPermHom ↥A ↥(orbSub A w))) :
    8 ≤ (orbA A w).card := by
  have h := Subgroup.card_dvd_of_injective _ hinj
  rw [hcard, Nat.card_perm, card_orbSub] at h
  by_contra hlt
  push Not at hlt
  interval_cases hk : (orbA A w).card <;> simp [Nat.factorial] at h

theorem false_of_card_eight (hcard : Nat.card A = 20160)
    (hA8 : ∀ (Ω : Type) [Fintype Ω] [DecidableEq Ω], Fintype.card Ω = 8 →
      IsEmpty (↥A ≃* ↥(alternatingGroup Ω))) (w : Fin 23)
    (hinj : Function.Injective (MulAction.toPermHom ↥A ↥(orbSub A w)))
    (h8 : (orbA A w).card = 8) : False := by
  classical
  set ρ := MulAction.toPermHom ↥A ↥(orbSub A w) with hρ
  have hΩ : Fintype.card ↥(orbSub A w) = 8 := by
    rw [← Nat.card_eq_fintype_card, card_orbSub, h8]
  have : Nontrivial ↥(orbSub A w) := Fintype.one_lt_card_iff_nontrivial.mp (by rw [hΩ]; norm_num)
  have hrange : Nat.card ρ.range = 20160 := by
    rw [← hcard]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hperm : Nat.card (Equiv.Perm ↥(orbSub A w)) = 40320 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, hΩ]
    decide
  have hidx : ρ.range.index = 2 := by
    have := Subgroup.card_mul_index ρ.range
    rw [hrange, hperm] at this
    omega
  have hle : alternatingGroup ↥(orbSub A w) ≤ ρ.range :=
    Equiv.Perm.alternatingGroup_le_of_index_le_two (by omega)
  have hcardAlt : Nat.card (alternatingGroup ↥(orbSub A w)) = 20160 := by
    have h := two_mul_nat_card_alternatingGroup (α := ↥(orbSub A w))
    rw [Nat.card_perm, Nat.card_eq_fintype_card (α := ↥(orbSub A w)), hΩ] at h
    have h8f : Nat.factorial 8 = 40320 := by decide
    omega
  have heq : alternatingGroup ↥(orbSub A w) = ρ.range :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hrange, hcardAlt])
  exact (hA8 ↥(orbSub A w) hΩ).false
    ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr heq.symm))

theorem card_fixed_modEq {g : ↥H0} {p : ℕ} [hp : Fact p.Prime] (hgA : g ∈ A)
    (hg : orderOf g = p) (Y : Finset (Fin 23)) (hY : ∀ a ∈ A, ∀ q ∈ Y, (a : ↥H0) • q ∈ Y) :
    (Y.filter fun q => g • q = q).card ≡ Y.card [MOD p] := by
  classical
  have hZA : Subgroup.zpowers g ≤ A := Subgroup.zpowers_le.mpr hgA
  let Ys : SubMulAction ↥(Subgroup.zpowers g) (Fin 23) :=
    { carrier := Y
      smul_mem' := fun z q hq => hY z (hZA z.2) q hq }
  have hZ : IsPGroup p ↥(Subgroup.zpowers g) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hg, pow_one])
  have h := hZ.card_modEq_card_fixedPoints ↥Ys
  have hYc : Nat.card ↥Ys = Y.card := by
    have : Nat.card ↥Ys = Nat.card ↥((Y : Set (Fin 23))) := rfl
    rw [this, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  have hst : ∀ q : Fin 23, g • q = q → ∀ z ∈ Subgroup.zpowers g, z • q = q := by
    intro q hq z hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hgq : g ∈ MulAction.stabilizer ↥H0 q := hq
    exact (MulAction.stabilizer ↥H0 q).zpow_mem hgq n
  let e : ↑(MulAction.fixedPoints ↥(Subgroup.zpowers g) ↥Ys) ≃
      {q // q ∈ Y.filter fun q => g • q = q} :=
    { toFun := fun y => ⟨(y.1 : Fin 23), Finset.mem_filter.mpr ⟨y.1.2,
        congrArg Subtype.val (y.2 ⟨g, Subgroup.mem_zpowers g⟩)⟩⟩
      invFun := fun q => ⟨⟨q.1, (Finset.mem_filter.mp q.2).1⟩, fun z => Subtype.ext
        (hst q.1 (Finset.mem_filter.mp q.2).2 z z.2)⟩
      left_inv := fun y => rfl
      right_inv := fun q => rfl }
  have hfc : Nat.card ↑(MulAction.fixedPoints ↥(Subgroup.zpowers g) ↥Ys) =
      (Y.filter fun q => g • q = q).card := by
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [hYc, hfc] at h
  exact h.symm

theorem fixed_of_card_lt [IsSimpleGroup ↥A] (hcard : Nat.card A = 20160) {Y : Finset (Fin 23)}
    (hY : Y.card < 8) (hYo : ∀ c ∈ Y, orbA A c ⊆ Y) {c : Fin 23} (hc : c ∈ Y) :
    ∀ a ∈ A, (a : ↥H0) • c = c := by
  rcases faithful_or_fixed (A := A) c with h | h
  · exact h
  · have h8 := eight_le_of_injective hcard c h
    have := Finset.card_le_card (hYo c hc)
    omega

theorem orbA_subset_compl {w c : Fin 23} (hc : c ∉ orbA A w) :
    orbA A c ⊆ Finset.univ \ orbA A w := by
  intro q hq
  rw [Finset.mem_sdiff]
  refine ⟨Finset.mem_univ _, fun hqw => hc ?_⟩
  have h1 := orbA_eq_of_mem hqw
  have h2 := orbA_eq_of_mem hq
  rw [← h1, h2]
  exact self_mem_orbA c

theorem orbit_structure
    [IsSimpleGroup ↥A] (hcard : Nat.card A = 20160)
    (hA8 : ∀ (Ω : Type) [Fintype Ω] [DecidableEq Ω], Fintype.card Ω = 8 →
      IsEmpty (↥A ≃* ↥(alternatingGroup Ω))) :
    ∃ x y : Fin 23, x ≠ y ∧ (∀ a ∈ A, (a : ↥H0) • x = x) ∧ (∀ a ∈ A, (a : ↥H0) • y = y) ∧
      ∀ p q : Fin 23, p ≠ x → p ≠ y → q ≠ x → q ≠ y → ∃ a ∈ A, (a : ↥H0) • p = q := by
  classical
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨g7, hg7⟩ := exists_prime_orderOf_dvd_card' (G := ↥A) 7 (by rw [hcard]; norm_num)
  obtain ⟨g5, hg5⟩ := exists_prime_orderOf_dvd_card' (G := ↥A) 5 (by rw [hcard]; norm_num)
  have hf7 : fixCount (g7 : ↥H0) = 2 :=
    fixCount_eq_two_of_orderOf_seven (by rw [Subgroup.orderOf_coe, hg7])
  have hf5 : fixCount (g5 : ↥H0) = 3 :=
    fixCount_eq_three_of_orderOf_five (by rw [Subgroup.orderOf_coe, hg5])
  obtain ⟨w, a₀, ha₀, hw⟩ : ∃ w : Fin 23, ∃ a ∈ A, (a : ↥H0) • w ≠ w := by
    by_contra hall
    push Not at hall
    have h1 : A = ⊥ := by
      rw [eq_bot_iff]
      intro a ha
      rw [Subgroup.mem_bot]
      apply Subtype.ext
      ext p
      exact congrArg Fin.val (hall p a ha)
    rw [h1, Subgroup.card_bot] at hcard
    omega
  set O := orbA A w with hOdef
  have hinj : Function.Injective (MulAction.toPermHom ↥A ↥(orbSub A w)) := by
    rcases faithful_or_fixed (A := A) w with h | h
    · exact absurd (h a₀ ha₀) hw
    · exact h
  have hk8 := eight_le_of_injective hcard w hinj
  have hkd := card_orbA_dvd (A := A) w
  rw [hcard] at hkd
  have hk23 : O.card ≤ 23 := (Finset.card_le_univ O).trans (by simp)
  have hkne8 : O.card ≠ 8 := fun h => false_of_card_eight hcard hA8 w hinj h
  set C := Finset.univ \ O with hCdef
  have hCc : C.card = 23 - O.card := by
    rw [hCdef, Finset.card_univ_sdiff, Fintype.card_fin]
  have hOinv : ∀ a ∈ A, ∀ q ∈ O, (a : ↥H0) • q ∈ O := fun a ha q hq => smul_mem_orbA ha hq
  have hCinv : ∀ a ∈ A, ∀ q ∈ C, (a : ↥H0) • q ∈ C := by
    intro a ha q hq
    rw [hCdef, Finset.mem_sdiff] at hq ⊢
    exact ⟨Finset.mem_univ _, smul_not_mem_orbA ha hq.2⟩
  have hCo : ∀ c ∈ C, orbA A c ⊆ C := fun c hc =>
    orbA_subset_compl (Finset.mem_sdiff.mp hc).2
  have hsplit : ∀ g : ↥H0, fixCount g =
      (O.filter fun q => g • q = q).card + (C.filter fun q => g • q = q).card := by
    intro g
    rw [fixCount, ← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter
      (Finset.disjoint_sdiff : Disjoint O (Finset.univ \ O))), ← Finset.filter_union,
      Finset.union_sdiff_of_subset (Finset.subset_univ O)]
  have h7O := card_fixed_modEq (A := A) g7.2 (by rw [Subgroup.orderOf_coe, hg7]) O hOinv
  have h7C := card_fixed_modEq (A := A) g7.2 (by rw [Subgroup.orderOf_coe, hg7]) C hCinv
  have h5O := card_fixed_modEq (A := A) g5.2 (by rw [Subgroup.orderOf_coe, hg5]) O hOinv
  have h5C := card_fixed_modEq (A := A) g5.2 (by rw [Subgroup.orderOf_coe, hg5]) C hCinv
  have hs7 := hsplit g7
  have hs5 := hsplit g5
  rw [hf7] at hs7
  rw [hf5] at hs5
  unfold Nat.ModEq at h7O h7C h5O h5C
  rw [hCc] at h7C h5C
  have hk : O.card = 15 ∨ O.card = 16 ∨ O.card = 21 := by
    obtain ⟨m, hm⟩ := hkd
    interval_cases hO : O.card <;> omega
  rcases hk with hk | hk | hk
  ·
    exfalso
    by_cases hall : ∀ c ∈ C, ∀ a ∈ A, (a : ↥H0) • c = c
    · have hfixC : (C.filter fun q => (g7 : ↥H0) • q = q) = C :=
        Finset.filter_true_of_mem fun c hc => hall c hc _ g7.2
      rw [hfixC, hCc, hk] at hs7
      omega
    · push Not at hall
      obtain ⟨c, hc, a, ha, hac⟩ := hall
      have hinjc : Function.Injective (MulAction.toPermHom ↥A ↥(orbSub A c)) := by
        rcases faithful_or_fixed (A := A) c with h | h
        · exact absurd (h a ha) hac
        · exact h
      have h8c := eight_le_of_injective hcard c hinjc
      have hle := Finset.card_le_card (hCo c hc)
      rw [hCc, hk] at hle
      exact false_of_card_eight hcard hA8 c hinjc (by omega)
  ·
    exfalso
    have hall : ∀ c ∈ C, ∀ a ∈ A, (a : ↥H0) • c = c := fun c hc =>
      fixed_of_card_lt hcard (by rw [hCc, hk]; norm_num) hCo hc
    have hfixC : (C.filter fun q => (g7 : ↥H0) • q = q) = C :=
      Finset.filter_true_of_mem fun c hc => hall c hc _ g7.2
    rw [hfixC, hCc, hk] at hs7
    omega
  ·
    have hC2 : C.card = 2 := by rw [hCc, hk]
    obtain ⟨x, y, hxy, hCxy⟩ := Finset.card_eq_two.mp hC2
    have hall : ∀ c ∈ C, ∀ a ∈ A, (a : ↥H0) • c = c := fun c hc =>
      fixed_of_card_lt hcard (by rw [hC2]; norm_num) hCo hc
    have hxC : x ∈ C := by rw [hCxy]; simp
    have hyC : y ∈ C := by rw [hCxy]; simp
    refine ⟨x, y, hxy, hall x hxC, hall y hyC, fun p q hpx hpy hqx hqy => ?_⟩
    have hmem : ∀ r : Fin 23, r ≠ x → r ≠ y → r ∈ O := by
      intro r hrx hry
      by_contra hr
      have : r ∈ C := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hr⟩
      rw [hCxy] at this
      simp at this
      tauto
    have hpO := hmem p hpx hpy
    have hqO := hmem q hqx hqy
    have hq' : q ∈ orbA A p := by
      rw [orbA_eq_of_mem hpO]
      exact hqO
    exact mem_orbA.mp hq'

end M23Perm

end CFSG.Quasithin.H13
