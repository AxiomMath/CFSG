module

public import CFSG.Quasithin.Background.MulAutTwo
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut
public import CFSG.Quasithin.Background.A4Aut
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open Matrix

namespace Lem25

open Module in
theorem exists_coords_index_two {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w * w = 1)
    {n : ℕ} (hcard : Nat.card W = 2 ^ (n + 1)) {A : Subgroup W} (hA : A.index = 2) :
    ∃ e : W ≃* Multiplicative (Fin (n + 1) → ZMod 2),
      ∀ w : W, w ∈ A ↔ Multiplicative.toAdd (e w) 0 = 0 := by
  classical
  let _ := MulAutTwo.zmod2Module hW
  have : Module.Finite (ZMod 2) (Additive W) := Module.Finite.of_finite
  set A' : Submodule (ZMod 2) (Additive W) :=
    AddSubgroup.toZModSubmodule 2 (Subgroup.toAddSubgroup A) with hA'
  have hmem : ∀ x : Additive W, x ∈ A' ↔ Additive.toMul x ∈ A := fun x => by
    rw [hA', AddSubgroup.mem_toZModSubmodule]
    exact Iff.rfl
  have hAc : Nat.card A * 2 = 2 ^ (n + 1) := by
    have h1 := Subgroup.card_mul_index A
    rw [hA, hcard] at h1
    exact h1
  have hA'c : Nat.card A' = 2 ^ n := by
    have h1 : Nat.card A' = Nat.card A :=
      Nat.card_congr
        { toFun := fun x => ⟨Additive.toMul x.1, (hmem x.1).mp x.2⟩
          invFun := fun a => ⟨Additive.ofMul a.1, (hmem _).mpr a.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    rw [h1]
    rw [pow_succ] at hAc
    omega
  have : Module.Finite (ZMod 2) A' := Module.Finite.of_finite
  have hrank : finrank (ZMod 2) A' = n := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := A')
    rw [Nat.card_zmod, hA'c] at h
    exact (Nat.pow_right_injective (le_refl 2) h).symm
  set bA := Module.finBasisOfFinrankEq (ZMod 2) A' hrank with hbA
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : W, w₀ ∉ A := by
    by_contra hno
    push Not at hno
    have htop : A = ⊤ := eq_top_iff.mpr fun x _ => hno x
    rw [htop, Subgroup.index_top] at hA
    omega
  have hz2 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  have hsmul : ∀ (c : ZMod 2) (x : Additive W), c • x ∈ A' ↔ c = 0 ∨ x ∈ A' := by
    intro c x
    rcases hz2 c with rfl | rfl
    · simp [A'.zero_mem]
    · simp
  have hli : ∀ (c : ZMod 2), ∀ x ∈ A', c • Additive.ofMul w₀ + x = 0 → c = 0 := by
    intro c x hx h0
    have h1 : c • Additive.ofMul w₀ = -x := eq_neg_of_add_eq_zero_left h0
    have h2 : c • Additive.ofMul w₀ ∈ A' := by rw [h1]; exact A'.neg_mem hx
    rcases (hsmul c _).mp h2 with h3 | h3
    · exact h3
    · exact absurd ((hmem _).mp h3) hw₀
  have hsp : ∀ z : Additive W, ∃ c : ZMod 2, z + c • Additive.ofMul w₀ ∈ A' := by
    intro z
    by_cases hz : z ∈ A'
    · exact ⟨0, by rw [zero_smul, add_zero]; exact hz⟩
    · refine ⟨1, ?_⟩
      rw [one_smul, hmem]
      have h1 : Additive.toMul z ∉ A := fun h => hz ((hmem z).mpr h)
      have h2 := (Subgroup.mul_mem_iff_of_index_two hA (a := Additive.toMul z) (b := w₀)).mpr
        (iff_of_false h1 hw₀)
      exact h2
  set b := Basis.mkFinCons (Additive.ofMul w₀) bA hli hsp with hb
  refine ⟨AddEquiv.toMultiplicativeRight b.equivFun.toAddEquiv, fun w => ?_⟩
  show w ∈ A ↔ b.equivFun (Additive.ofMul w) 0 = 0
  rw [Basis.equivFun_apply]
  set x := Additive.ofMul w with hx
  have hsum := b.sum_repr x
  rw [Fin.sum_univ_succ] at hsum
  have hrest : ∑ i : Fin n, (b.repr x) i.succ • b i.succ ∈ A' := by
    refine A'.sum_mem fun i _ => A'.smul_mem _ ?_
    rw [hb, Basis.coe_mkFinCons]
    simp only [Fin.cons_succ, Function.comp_apply]
    exact (bA i).2
  have hb0 : b 0 = Additive.ofMul w₀ := by
    rw [hb, Basis.coe_mkFinCons]
    simp only [Fin.cons_zero]
  rw [hb0] at hsum
  have key : w ∈ A ↔ (b.repr x) 0 • Additive.ofMul w₀ ∈ A' := by
    have h1 : w ∈ A ↔ x ∈ A' := by rw [hmem]; exact Iff.rfl
    rw [h1]
    constructor
    · intro hxA
      have h2 : (b.repr x) 0 • Additive.ofMul w₀ =
          x - ∑ i : Fin n, (b.repr x) i.succ • b i.succ := by
        rw [eq_sub_iff_add_eq]
        exact hsum
      rw [h2]
      exact A'.sub_mem hxA hrest
    · intro h0
      rw [← hsum]
      exact A'.add_mem h0 hrest
  rw [key, hsmul]
  constructor
  · rintro (h | h)
    · exact h
    · exact absurd ((hmem _).mp h) hw₀
  · exact Or.inl

@[expose] def M12 : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![1, 0, 0, 0, 0; 0, 0, 1, 0, 0; 0, 1, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]

@[expose] def M23 : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 1, 1, 0; 0, 0, 0, 0, 1]

@[expose] def M34 : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 0, 1; 0, 0, 0, 1, 1]

@[expose] def m12 : GL (Fin 5) (ZMod 2) :=
  ⟨M12, M12 ^ 2, by unfold M12; decide +kernel, by unfold M12; decide +kernel⟩

@[expose] def m23 : GL (Fin 5) (ZMod 2) :=
  ⟨M23, M23 ^ 2, by unfold M23; decide +kernel, by unfold M23; decide +kernel⟩

@[expose] def m34 : GL (Fin 5) (ZMod 2) :=
  ⟨M34, M34 ^ 2, by unfold M34; decide +kernel, by unfold M34; decide +kernel⟩

theorem coe_m12 : (m12 : Matrix (Fin 5) (Fin 5) (ZMod 2)) = M12 := rfl

theorem coe_m23 : (m23 : Matrix (Fin 5) (Fin 5) (ZMod 2)) = M23 := rfl

theorem coe_m34 : (m34 : Matrix (Fin 5) (Fin 5) (ZMod 2)) = M34 := rfl

theorem m12_cube : m12 ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, coe_m12, Units.val_one]
  unfold M12
  decide +kernel

theorem m23_cube : m23 ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, coe_m23, Units.val_one]
  unfold M23
  decide +kernel

theorem m34_cube : m34 ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, coe_m34, Units.val_one]
  unfold M34
  decide +kernel

theorem m12_ne_one : m12 ≠ 1 := fun h => by
  have := congrArg (fun g : GL (Fin 5) (ZMod 2) => (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) 1 1) h
  simp only [coe_m12, Units.val_one] at this
  revert this
  unfold M12
  decide

theorem m23_ne_one : m23 ≠ 1 := fun h => by
  have := congrArg (fun g : GL (Fin 5) (ZMod 2) => (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) 2 2) h
  simp only [coe_m23, Units.val_one] at this
  revert this
  unfold M23
  decide

theorem m12_m34_comm : m12 * m34 = m34 * m12 := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_m12, coe_m34]
  unfold M12 M34
  decide +kernel

theorem orderOf_eq_three {K : Type*} [Group K] {g : K} (hg : g ^ 3 = 1) (hg1 : g ≠ 1) :
    orderOf g = 3 :=
  orderOf_eq_prime hg hg1

theorem M12_mulVec_zero (x : Fin 5 → ZMod 2) : (M12 *ᵥ x) 0 = x 0 := by
  simp [M12, Matrix.mulVec, dotProduct, Fin.sum_univ_five]

theorem M23_mulVec_zero (x : Fin 5 → ZMod 2) : (M23 *ᵥ x) 0 = x 0 := by
  simp [M23, Matrix.mulVec, dotProduct, Fin.sum_univ_five]

theorem M34_mulVec_zero (x : Fin 5 → ZMod 2) : (M34 *ᵥ x) 0 = x 0 := by
  simp [M34, Matrix.mulVec, dotProduct, Fin.sum_univ_five]

theorem m12_m23_fix : ∀ x : Fin 5 → ZMod 2, x 0 = 0 → M12 *ᵥ x = x → M23 *ᵥ x = x →
    x = 0 ∨ x = Pi.single 4 1 := by
  unfold M12 M23
  decide +kernel

theorem single4_zero : (Pi.single 4 1 : Fin 5 → ZMod 2) 0 = 0 := by decide

theorem single4_ne_zero : (Pi.single 4 1 : Fin 5 → ZMod 2) ≠ 0 := by decide

theorem M12_single4 : M12 *ᵥ (Pi.single 4 1 : Fin 5 → ZMod 2) = Pi.single 4 1 := by
  unfold M12
  decide +kernel

theorem M23_single4 : M23 *ᵥ (Pi.single 4 1 : Fin 5 → ZMod 2) = Pi.single 4 1 := by
  unfold M23
  decide +kernel

section Pair

variable {K : Type*} [Group K]

theorem pow_mod_three' {g : K} (hg : g ^ 3 = 1) (k : ℕ) : g ^ k = g ^ (k % 3) := by
  conv_lhs => rw [← Nat.mod_add_div k 3, pow_add, pow_mul, hg, one_pow, mul_one]

@[expose] def pairMap (a b : K) (q : Fin 3 × Fin 3) : K := a ^ (q.1 : ℕ) * b ^ (q.2 : ℕ)

@[expose] def pairSubgroup (a b : K) (hab : a * b = b * a) (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) :
    Subgroup K where
  carrier := Set.range (pairMap a b)
  mul_mem' := by
    rintro _ _ ⟨q, rfl⟩ ⟨r, rfl⟩
    refine ⟨(⟨(q.1 + r.1 : ℕ) % 3, Nat.mod_lt _ (by norm_num)⟩,
      ⟨(q.2 + r.2 : ℕ) % 3, Nat.mod_lt _ (by norm_num)⟩), ?_⟩
    simp only [pairMap]
    rw [← pow_mod_three' ha, ← pow_mod_three' hb, pow_add, pow_add]
    have hc : Commute a b := hab
    calc a ^ (q.1 : ℕ) * a ^ (r.1 : ℕ) * (b ^ (q.2 : ℕ) * b ^ (r.2 : ℕ)) =
        a ^ (q.1 : ℕ) * (a ^ (r.1 : ℕ) * b ^ (q.2 : ℕ)) * b ^ (r.2 : ℕ) := by group
      _ = a ^ (q.1 : ℕ) * (b ^ (q.2 : ℕ) * a ^ (r.1 : ℕ)) * b ^ (r.2 : ℕ) := by
        rw [((hc.pow_left _).pow_right _).eq]
      _ = _ := by group
  one_mem' := ⟨(0, 0), by simp [pairMap]⟩
  inv_mem' := by
    rintro _ ⟨q, rfl⟩
    refine ⟨(⟨(3 - q.1 : ℕ) % 3, Nat.mod_lt _ (by norm_num)⟩,
      ⟨(3 - q.2 : ℕ) % 3, Nat.mod_lt _ (by norm_num)⟩), ?_⟩
    simp only [pairMap]
    rw [← pow_mod_three' ha, ← pow_mod_three' hb]
    have hc : Commute a b := hab
    rw [_root_.mul_inv_rev, ← ((hc.pow_left _).pow_right _).inv_inv.eq]
    have ha' : a ^ (3 - (q.1 : ℕ)) = (a ^ (q.1 : ℕ))⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_add, Nat.sub_add_cancel q.1.isLt.le, ha]
    have hb' : b ^ (3 - (q.2 : ℕ)) = (b ^ (q.2 : ℕ))⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_add, Nat.sub_add_cancel q.2.isLt.le, hb]
    rw [ha', hb']

theorem card_pairSubgroup [Finite K] {a b : K} (hab : a * b = b * a) (ha : a ^ 3 = 1)
    (hb : b ^ 3 = 1) (hinj : Function.Injective (pairMap a b)) :
    Nat.card (pairSubgroup a b hab ha hb) = 9 := by
  have h : ((pairSubgroup a b hab ha hb : Subgroup K) : Set K) = Set.range (pairMap a b) := rfl
  rw [← SetLike.coe_sort_coe, h, Nat.card_range_of_injective hinj, Nat.card_prod,
    Nat.card_eq_fintype_card, Fintype.card_fin]

theorem pairSubgroup_elem {a b : K} (hab : a * b = b * a) (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) :
    IsElemAbelian 3 (pairSubgroup a b hab ha hb) := by
  have hc : Commute a b := hab
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨q, hq⟩ := x.2
    obtain ⟨r, hr⟩ := y.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul, ← hq, ← hr, pairMap]
    have h1 : Commute (a ^ (q.1 : ℕ) * b ^ (q.2 : ℕ)) (a ^ (r.1 : ℕ) * b ^ (r.2 : ℕ)) :=
      Commute.mul_left (Commute.mul_right ((Commute.refl a).pow_pow _ _)
          ((hc.pow_left _).pow_right _))
        (Commute.mul_right ((hc.symm.pow_left _).pow_right _) ((Commute.refl b).pow_pow _ _))
    exact h1.eq
  · obtain ⟨q, rfl⟩ := hx
    simp only [pairMap]
    rw [((hc.pow_left _).pow_right _).mul_pow, ← pow_mul, ← pow_mul, mul_comm (q.1 : ℕ),
      mul_comm (q.2 : ℕ), pow_mul, pow_mul, ha, hb, one_pow, one_pow, mul_one]

theorem mem_pairSubgroup_left {a b : K} (hab : a * b = b * a) (ha : a ^ 3 = 1)
    (hb : b ^ 3 = 1) : a ∈ pairSubgroup a b hab ha hb :=
  ⟨(1, 0), by simp [pairMap]⟩

end Pair

theorem pairMap_M12_M34_injective : ∀ q r : Fin 3 × Fin 3,
    M12 ^ (q.1 : ℕ) * M34 ^ (q.2 : ℕ) = M12 ^ (r.1 : ℕ) * M34 ^ (r.2 : ℕ) → q = r := by
  unfold M12 M34
  decide +kernel

theorem pairMap_m12_m34_injective : Function.Injective (pairMap m12 m34) := by
  intro q r h
  have h' := congrArg Units.val h
  simp only [pairMap, Units.val_mul, Units.val_pow_eq_pow_val, coe_m12, coe_m34] at h'
  exact pairMap_M12_M34_injective q r h'

@[expose] def e9five : Subgroup (GL (Fin 5) (ZMod 2)) :=
  pairSubgroup m12 m34 m12_m34_comm m12_cube m34_cube

theorem card_e9five : Nat.card e9five = 9 :=
  card_pairSubgroup _ _ _ pairMap_m12_m34_injective

theorem e9five_elem : IsElemAbelian 3 e9five := pairSubgroup_elem _ _ _

theorem e9five_mulVec_zero {g : GL (Fin 5) (ZMod 2)} (hg : g ∈ e9five)
    (x : Fin 5 → ZMod 2) : ((g : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ x) 0 = x 0 := by
  obtain ⟨q, rfl⟩ := hg
  simp only [pairMap, Units.val_mul, Units.val_pow_eq_pow_val, coe_m12, coe_m34]
  rw [← Matrix.mulVec_mulVec]
  have h12 : ∀ k : ℕ, ∀ y, ((M12 ^ k) *ᵥ y) 0 = y 0 := by
    intro k
    induction k with
    | zero => intro y; simp
    | succ k ih => intro y; rw [pow_succ, ← Matrix.mulVec_mulVec, ih, M12_mulVec_zero]
  have h34 : ∀ k : ℕ, ∀ y, ((M34 ^ k) *ᵥ y) 0 = y 0 := by
    intro k
    induction k with
    | zero => intro y; simp
    | succ k ih => intro y; rw [pow_succ, ← Matrix.mulVec_mulVec, ih, M34_mulVec_zero]
  rw [h12, h34]

theorem exists_odd_lift {G K : Type*} [Group G] [Finite G] [Group K] {X : Subgroup G}
    (ψ : ↥X →* K) (hψ : Function.Surjective ψ) {g : K} (hg : Odd (orderOf g)) :
    ∃ x : ↥X, Odd (orderOf (x : G)) ∧ ψ x = g := by
  obtain ⟨x₀, hx₀⟩ := hψ g
  obtain ⟨k, m, hm, hlm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x₀).ne'
  have hx₁ : orderOf (x₀ ^ 2 ^ k) = m := by
    rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) (by rw [hlm]; exact dvd_mul_right _ _),
      hlm, Nat.mul_div_cancel_left _ (by positivity)]
  have hcop : Nat.Coprime (2 ^ k) (orderOf g) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hg)
  obtain ⟨j, hj⟩ := exists_pow_eq_self_of_coprime hcop
  refine ⟨(x₀ ^ 2 ^ k) ^ j, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe]
    have hdvd : orderOf ((x₀ ^ 2 ^ k) ^ j) ∣ m := hx₁ ▸ orderOf_pow_dvd _
    exact Odd.of_dvd_nat hm hdvd
  · rw [map_pow, map_pow, hx₀, hj]

theorem exists_elemAbelian_lift {G K : Type*} [Group G] [Finite G] [Group K] [Finite K]
    {X : Subgroup G}
    (ψ : ↥X →* K) (hker : IsPGroup 2 ψ.ker) {E : Subgroup K} (hE : E ≤ ψ.range)
    (hEa : IsElemAbelian 3 E) {k : ℕ} (hEc : Nat.card E = 3 ^ k) :
    ∃ S : Subgroup G, S ≤ X ∧ Nat.card S = 3 ^ k ∧ IsElemAbelian 3 S ∧
      (∀ x : ↥X, (x : G) ∈ S → ψ x ∈ E) ∧ (∀ x : ↥X, (x : G) ∈ S → ψ x = 1 → x = 1) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Q : Subgroup ↥X := E.comap ψ with hQ
  let ψQ : ↥Q →* ↥E := (ψ.comp Q.subtype).codRestrict E fun q => q.2
  have hψQ : Function.Surjective ψQ := by
    rintro ⟨e, he⟩
    obtain ⟨y, hy⟩ := hE he
    exact ⟨⟨y, show ψ y ∈ E by rw [hy]; exact he⟩, Subtype.ext hy⟩
  have h9 : 3 ^ k ∣ Nat.card Q := by
    have := Subgroup.card_dvd_of_surjective hψQ
    rw [hEc] at this
    exact this
  obtain ⟨P'', hP''⟩ := Sylow.exists_subgroup_card_pow_prime 3 h9
  set P' : Subgroup ↥X := P''.map Q.subtype with hP'
  have hP'Q : P' ≤ Q := Subgroup.map_subtype_le P''
  have hcardP' : Nat.card P' = 3 ^ k := by
    rw [hP', Subgroup.card_map_of_injective Q.subtype_injective, hP'']
  have hinj : ∀ y ∈ P', ψ y = 1 → y = 1 := by
    intro y hy h1
    have h9' : y ^ 3 ^ k = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (hcardP' ▸ Subgroup.orderOf_dvd_natCard P' hy)
    obtain ⟨j, hj⟩ := hker ⟨y, h1⟩
    have h2 : y ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    have hcop : Nat.gcd (2 ^ j) (3 ^ k) = 1 :=
      Nat.Coprime.pow j k (by norm_num)
    have := pow_gcd_eq_one.mpr ⟨h2, h9'⟩
    rwa [hcop, pow_one] at this
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hEa.1.1.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hcomm' : ∀ a ∈ P', ∀ b ∈ P', a * b = b * a := by
    intro a ha b hb
    have h1 : ψ (a * b * a⁻¹ * b⁻¹) = 1 := by
      have hc : ψ a * ψ b = ψ b * ψ a := hEcomm _ (hP'Q ha) _ (hP'Q hb)
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc]
      group
    have h2 := hinj _ (P'.mul_mem (P'.mul_mem (P'.mul_mem ha hb) (P'.inv_mem ha)) (P'.inv_mem hb))
      h1
    calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
      _ = b * a := by rw [h2, one_mul]
  have hpow' : ∀ a ∈ P', a ^ 3 = 1 := by
    intro a ha
    refine hinj _ (P'.pow_mem ha 3) ?_
    rw [map_pow]
    exact hEa.2 _ (hP'Q ha)
  refine ⟨P'.map X.subtype, Subgroup.map_subtype_le P', ?_, ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩,
    ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective X.subtype_injective, hcardP']
  · obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp x.2
    obtain ⟨b, hb, hby⟩ := Subgroup.mem_map.mp y.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hax, ← hby, Subgroup.coe_subtype,
      ← Subgroup.coe_mul, hcomm' a ha b hb, Subgroup.coe_mul]
  · obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.coe_subtype, ← Subgroup.coe_pow, hpow' a ha, Subgroup.coe_one]
  · intro y hy
    obtain ⟨a, ha, hay⟩ := Subgroup.mem_map.mp hy
    have : a = y := Subtype.ext hay
    rw [← this]
    exact hP'Q ha
  · intro y hy h1
    obtain ⟨a, ha, hay⟩ := Subgroup.mem_map.mp hy
    have : a = y := Subtype.ext hay
    rw [← this] at h1 ⊢
    exact hinj a ha h1

variable {G : Type} [Group G]

@[expose] noncomputable def actGL {L V : Subgroup G} (hLV : L ≤ Subgroup.normalizer (V : Set G))
    {n : ℕ} (e : ↥V ≃* Multiplicative (Fin n → ZMod 2)) : ↥L →* GL (Fin n) (ZMod 2) :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  (CFSG.SectionRank.Ccomm.elemAutEquivGL e).toMonoidHom.comp (A4.actionOn V L hLV)

theorem actGL_mulVec {L V : Subgroup G} (hLV : L ≤ Subgroup.normalizer (V : Set G)) {n : ℕ}
    (e : ↥V ≃* Multiplicative (Fin n → ZMod 2)) (l : ↥L) (v : ↥V) :
    ((actGL hLV e l : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
        Multiplicative.toAdd (e v) =
      Multiplicative.toAdd (e (A4.actionOn V L hLV l v)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.SectionRank.Ccomm.elemAutEquivGL_mulVec e (A4.actionOn V L hLV l) v

theorem actGL_eq_one_iff {L V : Subgroup G} (hLV : L ≤ Subgroup.normalizer (V : Set G)) {n : ℕ}
    (e : ↥V ≃* Multiplicative (Fin n → ZMod 2)) (l : ↥L) :
    actGL hLV e l = 1 ↔ (l : G) ∈ Subgroup.centralizer (V : Set G) := by
  rw [← A4.actionOn_eq_one_iff hLV l]
  simp only [actGL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]

theorem mem_normalizer_of_actGL {L V A : Subgroup G} (hLV : L ≤ Subgroup.normalizer (V : Set G))
    {n : ℕ} (e : ↥V ≃* Multiplicative (Fin n → ZMod 2)) (i : Fin n) (hAV : A ≤ V)
    (he : ∀ w : ↥V, (w : G) ∈ A ↔ Multiplicative.toAdd (e w) i = 0) (l : ↥L)
    (hl : ∀ y : Fin n → ZMod 2,
      (((actGL hLV e l : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ y) i = y i) :
    (l : G) ∈ Subgroup.normalizer (A : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  by_cases hg : g ∈ V
  · have h1 := actGL_mulVec hLV e l ⟨g, hg⟩
    have h2 : ((A4.actionOn V L hLV l ⟨g, hg⟩ : ↥V) : G) = l * g * (l : G)⁻¹ :=
      A4.actionOn_apply_coe hLV l ⟨g, hg⟩
    rw [show g = ((⟨g, hg⟩ : ↥V) : G) from rfl, he, ← h2, he, ← h1, hl]
  · have hg' : l * g * (l : G)⁻¹ ∉ V := fun h3 => by
      have := (Subgroup.mem_normalizer_iff.mp (hLV l.2) g).mpr h3
      exact hg this
    exact iff_of_false (fun h3 => hg (hAV h3)) (fun h3 => hg' (hAV h3))

theorem actGL_surjective {L V : Subgroup G} (hLV : L ≤ Subgroup.normalizer (V : Set G)) {n : ℕ}
    (e : ↥V ≃* Multiplicative (Fin n → ZMod 2)) (htop : autOn L V = ⊤) :
    Function.Surjective (actGL hLV e) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro g
  obtain ⟨x, hx⟩ := (A4.mem_autOn_iff hLV).mp
    (htop ▸ Subgroup.mem_top ((CFSG.SectionRank.Ccomm.elemAutEquivGL e).symm g))
  refine ⟨x, ?_⟩
  simp only [actGL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hx, MulEquiv.apply_symm_apply]

end Lem25

end CFSG.Quasithin.H13
