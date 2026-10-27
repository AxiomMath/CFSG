module

public import CFSG.RankThree.PartTwo.KFacts.KS14HJCentralizer
import CFSG.Models.PGLOrders
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PerfectResiduals

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS14

open CFSG CFSG.Blueprint CFSG.RankThree.PartTwo
open scoped commutatorElement Pointwise

theorem card_projSL_three_four :
    Nat.card (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)) = 20160 :=
  CFSG.PGLModel.card_projSL_three_four

theorem le_card_of_mulEquiv_sylow_two_projSL {S : Type*} [Group S]
    (T : Sylow 2 (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)))
    (e : S ≃* (T : Subgroup (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)))) :
    64 ≤ Nat.card S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)) :=
    Nat.finite_of_card_ne_zero (by rw [card_projSL_three_four]; norm_num)
  have hdvd := T.pow_dvd_card_of_pow_dvd_card (n := 6) (by rw [card_projSL_three_four]; norm_num)
  rw [Nat.card_congr e.toEquiv]
  exact Nat.le_of_dvd Nat.card_pos hdvd

theorem perm_three_conj_witness : ∀ y : Equiv.Perm (Fin 3), y ≠ 1 → y * y = 1 →
    ∃ g : Equiv.Perm (Fin 3), g * y * g⁻¹ * y ≠ 1 ∧ (g * y * g⁻¹ * y) ^ 3 = 1 := by
  decide +kernel

theorem eq_bot_of_normal_isPGroup_two_perm_three {K : Subgroup (Equiv.Perm (Fin 3))}
    (hKn : K.Normal) (hK2 : IsPGroup 2 K) : K = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hK2.exists_card_eq
  have h6 : Nat.card K ∣ 6 := by
    have h := Subgroup.card_subgroup_dvd_card K
    have hS : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
      rfl
    rwa [hS] at h
  have hk1 : k ≤ 1 := by
    by_contra hk1
    have : 2 ^ 2 ∣ 6 := (pow_dvd_pow 2 (by omega)).trans (hk ▸ h6)
    norm_num at this
  have hsq : ∀ t ∈ K, t * t = 1 := by
    intro t ht
    have h := pow_card_eq_one' (G := K) (x := ⟨t, ht⟩)
    rw [hk] at h
    interval_cases k
    · have h1 : (⟨t, ht⟩ : K) = 1 := by simpa using h
      rw [show t = 1 from congrArg Subtype.val h1, one_mul]
    · have h1 := congrArg Subtype.val h
      simpa [sq] using h1
  refine eq_bot_iff.mpr fun y hy => ?_
  rw [Subgroup.mem_bot]
  by_contra hy1
  obtain ⟨g, hg1, hg3⟩ := perm_three_conj_witness y hy1 (hsq y hy)
  have ht : g * y * g⁻¹ * y ∈ K := mul_mem (hKn.conj_mem y hy g) hy
  have htt := hsq _ ht
  apply hg1
  rw [pow_succ, pow_two, htt, one_mul] at hg3
  exact hg3

theorem card_alternatingGroup_four : Nat.card (alternatingGroup (Fin 4)) = 12 :=
  alternatingGroup.card_of_card_eq_four (by simp)

theorem card_le_four_of_normal_isPGroup_two
    {H : Subgroup (Equiv.Perm (Fin 3) × alternatingGroup (Fin 4))} (hHn : H.Normal)
    (hH2 : IsPGroup 2 H) : Nat.card H ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set f := MonoidHom.fst (Equiv.Perm (Fin 3)) (alternatingGroup (Fin 4)) with hf
  have hfs : Function.Surjective f := fun a => ⟨(a, 1), rfl⟩
  have hbot : H.map f = ⊥ :=
    eq_bot_of_normal_isPGroup_two_perm_three (hHn.map f hfs) (hH2.map f)
  have hker : H ≤ f.ker := by
    rwa [Subgroup.map_eq_bot_iff] at hbot
  have h12 : Nat.card f.ker = 12 := by
    rw [hf, MonoidHom.ker_fst, Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod,
      Subgroup.card_bot, Subgroup.card_top, one_mul, card_alternatingGroup_four]
  obtain ⟨k, hk⟩ := hH2.exists_card_eq
  have hdvd : 2 ^ k ∣ 12 := hk ▸ h12 ▸ Subgroup.card_dvd_of_le hker
  have hk2 : k ≤ 2 := by
    by_contra h
    have : 2 ^ 3 ∣ 12 := (pow_dvd_pow 2 (by omega)).trans hdvd
    norm_num at this
  rw [hk]
  calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
    _ = 4 := by norm_num

section PCore

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem normalizer_le_normalizer_centralizer (H : Subgroup X) :
    Subgroup.normalizer (H : Set X) ≤
      Subgroup.normalizer (Subgroup.centralizer (H : Set X) : Set X) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff] at hn ⊢
  intro g
  simp only [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  constructor
  · intro hg h hh
    have h' : n⁻¹ * h * n ∈ H := (hn _).mpr (by simpa [mul_assoc] using hh)
    have := hg _ h'
    calc h * (n * g * n⁻¹) = n * (n⁻¹ * h * n * g) * n⁻¹ := by group
      _ = n * (g * (n⁻¹ * h * n)) * n⁻¹ := by rw [this]
      _ = n * g * n⁻¹ * h := by group
  · intro hg h hh
    have h' : n * h * n⁻¹ ∈ H := (hn h).mp hh
    have := hg _ h'
    have h2 : n * (h * g) * n⁻¹ = n * (g * h) * n⁻¹ := by
      calc n * (h * g) * n⁻¹ = n * h * n⁻¹ * (n * g * n⁻¹) := by group
        _ = n * g * n⁻¹ * (n * h * n⁻¹) := this
        _ = n * (g * h) * n⁻¹ := by group
    simpa using h2

omit [Finite X] in
theorem centralizer_zpowers_eq (c : X) :
    Subgroup.centralizer ((Subgroup.zpowers c : Subgroup X) : Set X) =
      Subgroup.centralizer ({c} : Set X) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

omit [Finite X] in
theorem centralizer_eq_of_zpowers_eq {c d : X} (h : Subgroup.zpowers c = Subgroup.zpowers d) :
    Subgroup.centralizer ({c} : Set X) = Subgroup.centralizer ({d} : Set X) := by
  rw [← centralizer_zpowers_eq, h, centralizer_zpowers_eq]

omit [Finite X] in
theorem map_inSubgroup_pCore_two {X' : Type} [Group X'] (φ : X ≃* X') (H : Subgroup X) :
    (inSubgroup (CFSG.pCore 2) H).map φ.toMonoidHom =
      inSubgroup (CFSG.pCore 2) (H.map φ.toMonoidHom) := by
  rw [inSubgroup, inSubgroup,
    ← CFSG.pCore_map_iso 2 (H.equivMapOfInjective φ.toMonoidHom φ.injective), Subgroup.map_map,
    Subgroup.map_map]
  rfl

omit [Finite X] in
theorem conjugate_inSubgroup_pCore_centralizer (c x : X) :
    conjugate (inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({c} : Set X))) x =
      inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({x⁻¹ * c * x} : Set X)) := by
  rw [conjugate, map_inSubgroup_pCore_two]
  congr 1
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, inv_inv]
  constructor
  · rintro ⟨w, hw, rfl⟩
    calc x⁻¹ * w * x * (x⁻¹ * c * x) = x⁻¹ * (w * c) * x := by group
      _ = x⁻¹ * (c * w) * x := by rw [hw]
      _ = x⁻¹ * c * x * (x⁻¹ * w * x) := by group
  · intro hy
    refine ⟨x * y * x⁻¹, ?_, by group⟩
    calc x * y * x⁻¹ * c = x * (y * (x⁻¹ * c * x)) * x⁻¹ := by group
      _ = x * (x⁻¹ * c * x * y) * x⁻¹ := by rw [hy]
      _ = c * (x * y * x⁻¹) := by group

omit [Finite X] in
theorem normalizer_zpowers_le_normalizer_pCore (c : X) :
    Subgroup.normalizer (Subgroup.zpowers c : Set X) ≤
      Subgroup.normalizer
        (inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({c} : Set X)) : Set X) := by
  refine (normalizer_le_normalizer_centralizer (Subgroup.zpowers c)).trans ?_
  rw [centralizer_zpowers_eq]
  exact CFSG.RankThreeCoreUniqueness.Helpers.normalizer_le_normalizer_characteristic_map _ _
    inferInstance

theorem j2_card_pCore_two_centralizer_le_four (h415 : Sec4.Item4_15)
    (hX : Nonempty (X ≃* NativeSporadic.J2)) (P : Sylow 3 X) {A : Subgroup X}
    (hAP : A ≤ P) (hA9 : Nat.card A = 9) {c : X} (hcA : c ∈ A)
    (hcZ : c ∉ (P : Subgroup X) ⊓ Subgroup.centralizer ((P : Subgroup X) : Set X)) :
    Nat.card (inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({c} : Set X))) ≤ 4 := by
  obtain ⟨-, -, -, h4, -⟩ := h415 X hX P _ rfl _ rfl
  obtain ⟨-, ⟨e⟩, -⟩ := h4 A ⟨hAP, hA9⟩ c hcA hcZ
  set C := Subgroup.centralizer ({c} : Set X) with hC
  set N := Subgroup.normalizer (Subgroup.zpowers c : Set X) with hN
  set V := inSubgroup (CFSG.pCore 2) C with hV
  have hVC : V ≤ C := Subgroup.map_subtype_le _
  have hCN : C ≤ N := by
    rw [hC, hN, ← centralizer_zpowers_eq]
    exact Subgroup.centralizer_le_normalizer _
  have hVN : V ≤ N := hVC.trans hCN
  have hVn : (V.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVN).mpr
      (normalizer_zpowers_le_normalizer_pCore c)
  have hV2 : IsPGroup 2 V := (CFSG.pCore_isPGroup (p := 2) (G := ↥C)).map C.subtype
  have hV2' : IsPGroup 2 (V.subgroupOf N) := hV2.comap_subtype
  have hW := card_le_four_of_normal_isPGroup_two (hVn.map e.toMonoidHom e.surjective)
    (hV2'.map e.toMonoidHom)
  rw [Subgroup.card_map_of_injective e.injective,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVN).toEquiv] at hW
  exact hW

end PCore

section Signalizer

variable {X : Type} [Group X] [Finite X]

theorem sup_zpowers_eq_of_not_mem (h415 : Sec4.Item4_15) (hX : Nonempty (X ≃* NativeSporadic.J2))
    (P : Sylow 3 X) {A : Subgroup X} (hAP : A ≤ P) (hA9 : Nat.card A = 9) {x : X}
    (hxP : x ∈ (P : Subgroup X)) (hxA : x ∉ A) : A ⊔ Subgroup.zpowers x = P := by
  obtain ⟨⟨hHeis, -⟩, -⟩ := h415 X hX P _ rfl _ rfl
  obtain ⟨-, h27, -⟩ := hHeis
  have hle : A ⊔ Subgroup.zpowers x ≤ P := sup_le hAP (Subgroup.zpowers_le.mpr hxP)
  have hd1 : Nat.card ↥(A ⊔ Subgroup.zpowers x) ∣ 27 := h27 ▸ Subgroup.card_dvd_of_le hle
  have hd2 : 9 ∣ Nat.card ↥(A ⊔ Subgroup.zpowers x) := hA9 ▸ Subgroup.card_dvd_of_le le_sup_left
  have hcases : Nat.card ↥(A ⊔ Subgroup.zpowers x) = 9 ∨
      Nat.card ↥(A ⊔ Subgroup.zpowers x) = 27 := by
    have : Nat.card ↥(A ⊔ Subgroup.zpowers x) ∈ Nat.divisors 27 :=
      Nat.mem_divisors.mpr ⟨hd1, by norm_num⟩
    have hdiv : Nat.divisors 27 = {1, 3, 9, 27} := by decide
    rw [hdiv] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h | h | h | h <;> rw [h] at hd2 <;> norm_num at hd2 <;> simp [h]
  rcases hcases with h | h
  · exfalso
    have heq : A = A ⊔ Subgroup.zpowers x :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h, hA9])
    exact hxA (heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
  · exact Subgroup.eq_of_le_of_card_ge hle (by rw [h, h27])

omit [Finite X] in
theorem commute_of_mem_inf_centralizer {P : Subgroup X} {z y : X}
    (hz : z ∈ P ⊓ Subgroup.centralizer (P : Set X)) (hy : y ∈ P) : y * z = z * y :=
  Subgroup.mem_centralizer_iff.mp hz.2 y hy

theorem j2_mem_inf_centralizer_eq (h415 : Sec4.Item4_15)
    (hX : Nonempty (X ≃* NativeSporadic.J2)) (P : Sylow 3 X) {u w : X}
    (hu : u ∈ (P : Subgroup X) ⊓ Subgroup.centralizer ((P : Subgroup X) : Set X)) (hu1 : u ≠ 1)
    (hw : w ∈ (P : Subgroup X) ⊓ Subgroup.centralizer ((P : Subgroup X) : Set X)) :
    w = 1 ∨ w = u ∨ w = u * u := by
  obtain ⟨⟨hHeis, -⟩, -⟩ := h415 X hX P _ rfl _ rfl
  obtain ⟨⟨-, -, -, hZ3⟩, -, hexp⟩ := hHeis
  set Z := (P : Subgroup X) ⊓ Subgroup.centralizer ((P : Subgroup X) : Set X) with hZdef
  have hZ3' : Nat.card Z = 3 := by
    rw [hZdef, ← Sec14.map_subtype_center_eq,
      Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    exact hZ3
  have hu3 : u ^ 3 = 1 := by
    have h := Monoid.pow_exponent_eq_one (⟨u, hu.1⟩ : ↥(P : Subgroup X))
    rw [hexp] at h
    exact congrArg Subtype.val h
  have hZu : Subgroup.zpowers u = Z := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hu) ?_
    rw [hZ3']
    have hdvd : Nat.card (Subgroup.zpowers u) ∣ 3 :=
      hZ3' ▸ Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hu)
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exfalso
      rw [Nat.card_zpowers, orderOf_eq_one_iff] at h1
      exact hu1 h1
    · rw [h3]
  rw [← hZu] at hw
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hw
  have hk' : u ^ (k % 3) = w := by
    rw [← hk]
    conv_rhs => rw [← Int.mul_ediv_add_emod k 3]
    rw [zpow_add, zpow_mul, show ((3 : ℤ)) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, hu3,
      one_zpow, one_mul]
  rcases (show k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 by omega) with h | h | h
  · left
    rw [h, zpow_zero] at hk'
    exact hk'.symm
  · right; left
    rw [h, zpow_one] at hk'
    exact hk'.symm
  · right; right
    rw [h] at hk'
    rw [← hk', show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_two]

theorem j2_zpowers_conj_of_eq (h415 : Sec4.Item4_15) (hX : Nonempty (X ≃* NativeSporadic.J2))
    (P : Sylow 3 X) {A : Subgroup X} (hAP : A ≤ P) (hA9 : Nat.card A = 9) {a b x : X}
    (haA : a ∈ A) (hbA : b ∈ A) (hab : Subgroup.closure {a, b} = A) (hxa : x * a ≠ a * x)
    (hu : a⁻¹ * (x⁻¹ * a * x) = b⁻¹ * (x⁻¹ * b * x))
    (hZ : ∀ c ∈ (P : Subgroup X), c⁻¹ * (x⁻¹ * c * x) ∈
      (P : Subgroup X) ⊓ Subgroup.centralizer ((P : Subgroup X) : Set X))
    (hker : ∀ c ∈ A, c⁻¹ * (x⁻¹ * c * x) = 1 → c ∈
      (P : Subgroup X) ⊓ Subgroup.centralizer ((P : Subgroup X) : Set X)) :
    Subgroup.zpowers (x⁻¹ * a * x) = Subgroup.zpowers b ∨
      Subgroup.zpowers (x⁻¹ * b * x) = Subgroup.zpowers a := by
  obtain ⟨⟨hHeis, -⟩, -⟩ := h415 X hX P _ rfl _ rfl
  obtain ⟨-, -, hexp⟩ := hHeis
  set Z := (P : Subgroup X) ⊓ Subgroup.centralizer ((P : Subgroup X) : Set X) with hZdef
  have hpow3 : ∀ y ∈ (P : Subgroup X), y ^ 3 = 1 := by
    intro y hy
    have h := Monoid.pow_exponent_eq_one (⟨y, hy⟩ : ↥(P : Subgroup X))
    rw [hexp] at h
    exact congrArg Subtype.val h
  have haP := hAP haA
  have hbP := hAP hbA
  set u := a⁻¹ * (x⁻¹ * a * x) with hudef
  have huZ : u ∈ Z := hZ a haP
  have hu1 : u ≠ 1 := by
    intro h
    apply hxa
    have : x⁻¹ * a * x = a := by
      rw [hudef, inv_mul_eq_one] at h
      exact h.symm
    calc x * a = x * (x⁻¹ * a * x) := by rw [this]
      _ = a * x := by group
  set w := a⁻¹ * b with hwdef
  have hwZ : w ∈ Z := by
    have h1 : w⁻¹ * (x⁻¹ * w * x) = 1 := by
      have hbu : x⁻¹ * b * x = b * u := by
        rw [hu]
        group
      have hau : x⁻¹ * a * x = a * u := by
        rw [hudef]
        group
      have hcomm : u * a⁻¹ = a⁻¹ * u := (commute_of_mem_inf_centralizer huZ (inv_mem haP)).symm
      calc w⁻¹ * (x⁻¹ * w * x) = b⁻¹ * a * ((x⁻¹ * a * x)⁻¹ * (x⁻¹ * b * x)) := by
            rw [hwdef]
            group
        _ = b⁻¹ * a * ((a * u)⁻¹ * (b * u)) := by rw [hau, hbu]
        _ = b⁻¹ * a * (u⁻¹ * (a⁻¹ * b) * u) := by group
        _ = 1 := by
            have hcomm2 : (a⁻¹ * b) * u = u * (a⁻¹ * b) :=
              (commute_of_mem_inf_centralizer huZ (mul_mem (inv_mem haP) hbP))
            rw [mul_assoc u⁻¹, hcomm2]
            group
    exact hker w (mul_mem (inv_mem haA) hbA) h1
  have hw1 : w ≠ 1 := by
    intro h
    have hba : b = a := by
      rw [hwdef, inv_mul_eq_one] at h
      exact h.symm
    have hcl : A = Subgroup.zpowers a := by
      rw [← hab, hba, Set.insert_eq_of_mem (Set.mem_singleton a), ← Subgroup.zpowers_eq_closure]
    have hcard : Nat.card A ∣ 3 := by
      rw [hcl, Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one (hpow3 a haP)
    rw [hA9] at hcard
    norm_num at hcard
  have hw : w = u ∨ w = u * u := by
    rcases j2_mem_inf_centralizer_eq h415 hX P huZ hu1 hwZ with h | h
    · exact absurd h hw1
    · exact h
  rcases hw with h | h
  · left
    congr 1
    calc x⁻¹ * a * x = a * u := by rw [hudef]; group
      _ = a * w := by rw [h]
      _ = b := by rw [hwdef]; group
  · right
    congr 1
    have hu3 : u * u * u = 1 := by
      have := hpow3 u huZ.1
      rwa [pow_succ, pow_two] at this
    have hbu : x⁻¹ * b * x = b * u := by
      rw [hu]
      group
    calc x⁻¹ * b * x = b * u := hbu
      _ = a * w * u := by rw [hwdef]; group
      _ = a * (u * u * u) := by rw [h]; group
      _ = a := by rw [hu3, mul_one]

omit [Finite X] in
theorem closure_pair_inv_right (a b : X) :
    Subgroup.closure {a, b⁻¹} = Subgroup.closure ({a, b} : Set X) := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact inv_mem (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
  · rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · have : y⁻¹ ∈ Subgroup.closure {a, y⁻¹} :=
        Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
      simpa using inv_mem this

omit [Finite X] in
theorem conjugate_eq_of_mem_normalizer {H : Subgroup X} {x : X}
    (hx : x ∈ Subgroup.normalizer (H : Set X)) : conjugate H x = H := by
  rw [conjugate]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (inv_mem hx)

omit [Finite X] in
theorem mem_normalizer_of_conjugate_eq {H : Subgroup X} {x : X} (h : conjugate H x = H) :
    x ∈ Subgroup.normalizer (H : Set X) := by
  rw [conjugate] at h
  simpa using inv_mem (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h)

theorem j2_exists_maxInvariant_ne_inf_ne_bot (h415 : Sec4.Item4_15)
    (hX : Nonempty (X ≃* NativeSporadic.J2)) (P : Sylow 3 X) {A : Subgroup X}
    (hAP : A ≤ P) (hA9 : Nat.card A = 9) :
    ∃ U₁ ∈ maxInvariantPiSubgroups ⊤ A (piOf 2), ∃ U₂ ∈ maxInvariantPiSubgroups ⊤ A (piOf 2),
      U₁ ≠ U₂ ∧ U₁ ⊓ U₂ ≠ ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨hHeis, -⟩, -, ⟨-, hext, -⟩, -, h5⟩ := h415 X hX P _ rfl _ rfl
  obtain ⟨⟨-, hcomm, -, -⟩, -, hexp⟩ := hHeis
  obtain ⟨S, hS, hSP, hS3, ⟨T, ⟨eT⟩⟩, a, b, hab, hprod⟩ := h5 A ⟨hAP, hA9⟩
  set Z := (P : Subgroup X) ⊓ Subgroup.centralizer ((P : Subgroup X) : Set X) with hZ
  set W := S ⊓ Subgroup.centralizer (Z : Set X) with hW
  have haA : a ∈ A := hab ▸ Subgroup.subset_closure (Set.mem_insert a {b})
  have hbA : b ∈ A := hab ▸ Subgroup.subset_closure (Set.mem_insert_of_mem a rfl)
  have haP := hAP haA
  have hbP := hAP hbA
  have hpow3 : ∀ y ∈ (P : Subgroup X), y ^ 3 = 1 := by
    intro y hy
    have h := Monoid.pow_exponent_eq_one (⟨y, hy⟩ : ↥(P : Subgroup X))
    rw [hexp] at h
    exact congrArg Subtype.val h
  have hS2 : IsPGroup 2 S := (isPiSubgroup_piOf_iff Nat.prime_two S).mp hS.prop.2.1
  have hVaS : inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({a} : Set X)) ≤ S := by
    intro v hv
    have h := Set.mul_mem_mul (Set.mul_mem_mul (SetLike.mem_coe.mpr (one_mem W))
      (SetLike.mem_coe.mpr hv)) (SetLike.mem_coe.mpr (one_mem
        (inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({b} : Set X)))))
    rw [hprod, one_mul, mul_one] at h
    exact h
  have hVbS : inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({b} : Set X)) ≤ S := by
    intro v hv
    have h := Set.mul_mem_mul (Set.mul_mem_mul (SetLike.mem_coe.mpr (one_mem W))
      (SetLike.mem_coe.mpr (one_mem
        (inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({a} : Set X))))))
      (SetLike.mem_coe.mpr hv)
    rw [hprod, mul_one, one_mul] at h
    exact h
  have h64 : 64 ≤ Nat.card S := le_card_of_mulEquiv_sylow_two_projSL T eT
  have hcardS : Nat.card S ≤ Nat.card W *
      Nat.card (inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({a} : Set X))) *
      Nat.card (inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({b} : Set X))) := by
    have h1 := Set.natCard_mul_le (s := (W : Set X) *
      (inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({a} : Set X)) : Set X))
      (t := (inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({b} : Set X)) : Set X))
    have h2 := Set.natCard_mul_le (s := (W : Set X))
      (t := (inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({a} : Set X)) : Set X))
    rw [hprod] at h1
    exact h1.trans (Nat.mul_le_mul_right _ h2)
  have hW8 : Nat.card W ≤ 8 := by
    have hW2 : IsPGroup 2 W := hS2.to_le inf_le_left
    have hC : Nat.card (Subgroup.centralizer (Z : Set X)) = 1080 :=
      card_eq_of_isExtOf_alternating_six hext
    obtain ⟨k, hk⟩ := hW2.exists_card_eq
    have hdvd : 2 ^ k ∣ 1080 := hk ▸ hC ▸ Subgroup.card_dvd_of_le inf_le_right
    have hk3 : k ≤ 3 := by
      by_contra h
      have : 2 ^ 4 ∣ 1080 := (pow_dvd_pow 2 (by omega)).trans hdvd
      norm_num at this
    rw [hk]
    calc 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hk3
      _ = 8 := by norm_num
  have hne1 : ∀ c d : X, Subgroup.closure {c, d} = A → d ∈ A → c = 1 → False := by
    intro c d hcd hdA hc
    have hcl : A = Subgroup.zpowers d := by
      rw [← hcd, hc, Subgroup.zpowers_eq_closure]
      apply le_antisymm
      · rw [Subgroup.closure_le]
        rintro y (rfl | rfl)
        · exact one_mem _
        · exact Subgroup.subset_closure rfl
      · exact Subgroup.closure_mono (Set.subset_insert _ _)
    have hcard : Nat.card A ∣ 3 := by
      rw [hcl, Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one (hpow3 d (hAP hdA))
    rw [hA9] at hcard
    norm_num at hcard
  have ha1 : a ≠ 1 := fun h => hne1 a b hab hbA h
  have hb1 : b ≠ 1 := fun h => hne1 b a (by rw [Set.pair_comm]; exact hab) haA h
  have hV : ∀ c ∈ A, c ≠ 1 →
      Nat.card (inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({c} : Set X))) ≤ 4 ∧
        (c ∈ Z →
          Nat.card (inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({c} : Set X))) = 1) := by
    intro c hcA hc1
    have hZcase : c ∈ Z →
        Nat.card (inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({c} : Set X))) = 1 := by
      intro hcZ
      have hbot := j2_pCore_two_centralizer_eq_bot h415 hX hc1
        ⟨P, hcZ.1, fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr
          (commute_of_mem_inf_centralizer hcZ hy)⟩
      rw [inSubgroup, hbot, Subgroup.map_bot, Subgroup.card_bot]
    refine ⟨?_, hZcase⟩
    by_cases hcZ : c ∈ Z
    · rw [hZcase hcZ]
      norm_num
    · exact j2_card_pCore_two_centralizer_le_four h415 hX P hAP hA9 hcA hcZ
  obtain ⟨hVa4, hVaZ⟩ := hV a haA ha1
  obtain ⟨hVb4, hVbZ⟩ := hV b hbA hb1
  set fa := Nat.card (inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({a} : Set X))) with hfa
  set fb := Nat.card (inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({b} : Set X))) with hfb
  have hprod64 : 64 ≤ 8 * fa * fb :=
    h64.trans (hcardS.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hW8)))
  have hfa2 : 2 ≤ fa := by
    interval_cases fa <;> interval_cases fb <;> omega
  have hfb2 : 2 ≤ fb := by
    interval_cases fa <;> interval_cases fb <;> omega
  have haZ : a ∉ Z := fun h => by
    have := hVaZ h
    omega
  have hbZ : b ∉ Z := fun h => by
    have := hVbZ h
    omega
  have hVa1 : inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({a} : Set X)) ≠ ⊥ := by
    intro h
    rw [hfa, h, Subgroup.card_bot] at hfa2
    norm_num at hfa2
  have hVb1 : inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({b} : Set X)) ≠ ⊥ := by
    intro h
    rw [hfb, h, Subgroup.card_bot] at hfb2
    norm_num at hfb2
  obtain ⟨x, hxP, hxa⟩ : ∃ x ∈ (P : Subgroup X), x * a ≠ a * x := by
    by_contra h
    apply haZ
    refine ⟨haP, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    by_contra hne
    exact h ⟨y, hy, hne⟩
  have hAcomm : ∀ c ∈ A, ∀ d ∈ A, c * d = d * c := by
    intro c hc d hd
    have h := (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (G := A)
      (by rw [hA9]; norm_num)).is_comm.comm ⟨c, hc⟩ ⟨d, hd⟩
    exact congrArg Subtype.val h
  have hxA : x ∉ A := fun h => hxa (hAcomm x h a haA)
  have hPx := sup_zpowers_eq_of_not_mem h415 hX P hAP hA9 hxP hxA
  have hφZ : ∀ c ∈ (P : Subgroup X), c⁻¹ * (x⁻¹ * c * x) ∈ Z := by
    intro c hc
    have hm : ⁅(⟨c⁻¹, inv_mem hc⟩ : ↥(P : Subgroup X)), ⟨x⁻¹, inv_mem hxP⟩⁆ ∈
        commutator ↥(P : Subgroup X) := by
      rw [commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    rw [hcomm] at hm
    have hm' := Subgroup.mem_map_of_mem (P : Subgroup X).subtype hm
    rw [Sec14.map_subtype_center_eq] at hm'
    have heq : ((P : Subgroup X).subtype
        ⁅(⟨c⁻¹, inv_mem hc⟩ : ↥(P : Subgroup X)), ⟨x⁻¹, inv_mem hxP⟩⁆) =
          c⁻¹ * (x⁻¹ * c * x) := by
      simp [commutatorElement_def, mul_assoc]
    rw [heq] at hm'
    exact hm'
  have hker : ∀ c ∈ A, c⁻¹ * (x⁻¹ * c * x) = 1 → c ∈ Z := by
    intro c hcA h1
    have hcx : x⁻¹ * c * x = c := by
      rw [inv_mul_eq_one] at h1
      exact h1.symm
    have hle : A ⊔ Subgroup.zpowers x ≤ Subgroup.centralizer ({c} : Set X) := by
      refine sup_le (fun d hd => Subgroup.mem_centralizer_singleton_iff.mpr
        (hAcomm c hcA d hd).symm) (Subgroup.zpowers_le.mpr ?_)
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc x * c = x * (x⁻¹ * c * x) := by rw [hcx]
        _ = c * x := by group
    rw [hPx] at hle
    exact ⟨hAP hcA, Subgroup.mem_centralizer_iff.mpr fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.mp (hle hy)⟩
  set u := a⁻¹ * (x⁻¹ * a * x) with hu
  have huZ : u ∈ Z := hφZ a haP
  have hu1 : u ≠ 1 := fun h => haZ (hker a haA h)
  have hφb : b⁻¹ * (x⁻¹ * b * x) ∈ Z := hφZ b hbP
  have hφb1 : b⁻¹ * (x⁻¹ * b * x) ≠ 1 := fun h => hbZ (hker b hbA h)
  have hkey : Subgroup.zpowers (x⁻¹ * a * x) = Subgroup.zpowers b ∨
      Subgroup.zpowers (x⁻¹ * b * x) = Subgroup.zpowers a := by
    rcases j2_mem_inf_centralizer_eq h415 hX P huZ hu1 hφb with h | h | h
    · exact absurd h hφb1
    · exact j2_zpowers_conj_of_eq h415 hX P hAP hA9 haA hbA hab hxa h.symm hφZ hker
    ·
      have hu3 : u * u * u = 1 := by
        have := hpow3 u huZ.1
        rwa [pow_succ, pow_two] at this
      have hinv : (b⁻¹)⁻¹ * (x⁻¹ * b⁻¹ * x) = u := by
        have hcb : b * (u * u)⁻¹ = (u * u)⁻¹ * b :=
          commute_of_mem_inf_centralizer (inv_mem (mul_mem huZ huZ)) hbP
        have hbx : x⁻¹ * b * x = b * (u * u) := by
          rw [← h]
          group
        have hbx' : x⁻¹ * b⁻¹ * x = (u * u)⁻¹ * b⁻¹ := by
          rw [show x⁻¹ * b⁻¹ * x = (x⁻¹ * b * x)⁻¹ by group, hbx, mul_inv_rev]
        have huu : (u * u)⁻¹ = u := inv_eq_iff_mul_eq_one.mpr hu3
        rw [inv_inv, hbx', ← mul_assoc, hcb, mul_assoc, mul_inv_cancel, mul_one, huu]
      have := j2_zpowers_conj_of_eq h415 hX P hAP hA9 haA (inv_mem hbA)
        (by rw [closure_pair_inv_right]; exact hab) hxa hinv.symm hφZ hker
      rcases this with h' | h'
      · left
        rw [h', Subgroup.zpowers_inv]
      · right
        rw [← h', show x⁻¹ * b⁻¹ * x = (x⁻¹ * b * x)⁻¹ by group, Subgroup.zpowers_inv]
  have hSx : conjugate S x ∈ maxInvariantPiSubgroups ⊤ A (piOf 2) := by
    rw [hSP]
    exact ⟨x, hxP, rfl⟩
  have hne : S ≠ conjugate S x := by
    intro h
    have hxN : x ∈ Subgroup.normalizer (S : Set X) := mem_normalizer_of_conjugate_eq h.symm
    have hPN : (P : Subgroup X) ≤ Subgroup.normalizer (S : Set X) := by
      rw [← hPx]
      exact sup_le hS.prop.2.2 (Subgroup.zpowers_le.mpr hxN)
    have hsub : maxInvariantPiSubgroups ⊤ A (piOf 2) ⊆ {S} := by
      rw [hSP]
      rintro _ ⟨y, hy, rfl⟩
      exact conjugate_eq_of_mem_normalizer (hPN hy)
    have := Set.ncard_le_ncard hsub (Set.finite_singleton S)
    rw [hS3, Set.ncard_singleton] at this
    norm_num at this
  refine ⟨S, hS, conjugate S x, hSx, hne, ?_⟩
  rcases hkey with h | h
  ·
    refine fun hbot => hVb1 (eq_bot_iff.mpr ?_)
    rw [← hbot]
    refine le_inf hVbS ?_
    rw [centralizer_eq_of_zpowers_eq h.symm, ← conjugate_inSubgroup_pCore_centralizer]
    exact Subgroup.map_mono hVaS
  · refine fun hbot => hVa1 (eq_bot_iff.mpr ?_)
    rw [← hbot]
    refine le_inf hVaS ?_
    rw [centralizer_eq_of_zpowers_eq h.symm, ← conjugate_inSubgroup_pCore_centralizer]
    exact Subgroup.map_mono hVbS

end Signalizer

end CFSG.RankThree.PartTwo.KFacts.KS14
