module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem19X
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem8Cases
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem8Star
public import CFSG.Quasithin.Background.A3Structure318
public import CFSG.Quasithin.Vol2.Ch1Inputs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative commutatorElement

namespace L619

theorem commute_closure {D : Type*} [Group D] {S T : Set D}
    (h : ∀ a ∈ S, ∀ b ∈ T, a * b = b * a) :
    ∀ a ∈ Subgroup.closure S, ∀ b ∈ Subgroup.closure T, a * b = b * a := by
  have h1 : Subgroup.closure T ≤ Subgroup.centralizer S := by
    rw [Subgroup.closure_le]
    intro b hb
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro a ha
    exact h a ha b hb
  have h2 : Subgroup.closure S ≤ Subgroup.centralizer (Subgroup.closure T : Set D) := by
    rw [Subgroup.closure_le]
    intro a ha
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro b hb
    exact ((Subgroup.mem_centralizer_iff.mp (h1 hb)) a ha).symm
  intro a ha b hb
  exact ((Subgroup.mem_centralizer_iff.mp (h2 ha)) b hb).symm

theorem closure_pair_maximal {D : Type*} [Group D] [Finite D] {x y : D} (hxy : x * y = y * x)
    (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1) (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hxy1 : x ≠ y)
    (hxy2 : x ≠ y ^ 2) (hD : ¬ 27 ∣ Nat.card D) :
    ∀ R : Subgroup D, IsPGroup 3 R → Subgroup.closure ({x, y} : Set D) ≤ R →
      R ≤ Subgroup.closure ({x, y} : Set D) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hox : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hoy : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have heq : Subgroup.closure ({x, y} : Set D) = Subgroup.zpowers x ⊔ Subgroup.zpowers y := by
    rw [show ({x, y} : Set D) = {x} ∪ {y} from rfl, Subgroup.closure_union,
      Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure]
  have hc : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ Subgroup.zpowers y, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact ((Commute.zpow_zpow (show Commute x y from hxy) i j)).eq
  have hd : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥ := by
    have hdvd : Nat.card ↥(Subgroup.zpowers x ⊓ Subgroup.zpowers y) ∣ 3 := by
      rw [← hox, ← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have hle : Subgroup.zpowers x ≤ Subgroup.zpowers y := by
        have := Subgroup.eq_of_le_of_card_ge (inf_le_left :
          Subgroup.zpowers x ⊓ Subgroup.zpowers y ≤ Subgroup.zpowers x)
          (by rw [h3, Nat.card_zpowers, hox])
        rw [← this]
        exact inf_le_right
      have hxm : x ∈ Subgroup.zpowers y := hle (Subgroup.mem_zpowers x)
      rw [mem_zpowers_iff_mem_range_orderOf, hoy] at hxm
      simp only [Finset.mem_image, Finset.mem_range] at hxm
      obtain ⟨k, hk, hkx⟩ := hxm
      interval_cases k
      · exact hx1 (by rw [← hkx, pow_zero])
      · exact hxy1 (by rw [← hkx, pow_one])
      · exact hxy2 hkx.symm
  have hcard : Nat.card ↥(Subgroup.closure ({x, y} : Set D)) = 3 ^ 2 := by
    rw [heq, card_sup_of_commute hc hd, Nat.card_zpowers, Nat.card_zpowers, hox, hoy]
    norm_num
  intro R hR hBR
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card).mp hR
  have hj2 : j ≤ 2 := by
    by_contra hlt
    push Not at hlt
    apply hD
    have : 3 ^ 3 ∣ Nat.card R := hj ▸ pow_dvd_pow 3 hlt
    exact this.trans (Subgroup.card_subgroup_dvd_card R)
  have hle : Nat.card R ≤ Nat.card ↥(Subgroup.closure ({x, y} : Set D)) := by
    rw [hj, hcard]
    exact Nat.pow_le_pow_right (by norm_num) hj2
  exact (Subgroup.eq_of_le_of_card_ge hBR hle).symm.le

theorem exists_abelian_sylow_three_of_pairs {E D : Type*} [Group E] [Finite E] [Group D]
    [Finite D] (η : E →* D) (hsurj : Function.Surjective η)
    (hcentral : η.ker ≤ Subgroup.center E) {a b c e : D} (hac : a * c = c * a)
    (hae : a * e = e * a) (hbc : b * c = c * b) (hbe : b * e = e * b) (hx3 : ⁅a, b⁆ ^ 3 = 1)
    (hy3 : ⁅c, e⁆ ^ 3 = 1) (hx1 : ⁅a, b⁆ ≠ 1) (hy1 : ⁅c, e⁆ ≠ 1) (hxy1 : ⁅a, b⁆ ≠ ⁅c, e⁆)
    (hxy2 : ⁅a, b⁆ ≠ ⁅c, e⁆ ^ 2) (hD : ¬ 27 ∣ Nat.card D) :
    ∃ P : Sylow 3 E, IsMulCommutative (P : Subgroup E) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set X := Subgroup.closure ({a, b} : Set D) with hX
  set Y := Subgroup.closure ({c, e} : Set D) with hY
  have hXY : ∀ u ∈ X, ∀ v ∈ Y, u * v = v * u := commute_closure (by
    rintro u (rfl | rfl) v (rfl | rfl) <;> assumption)
  have ha : a ∈ X := Subgroup.subset_closure (Set.mem_insert a _)
  have hb : b ∈ X := Subgroup.subset_closure (Set.mem_insert_of_mem a rfl)
  have hc : c ∈ Y := Subgroup.subset_closure (Set.mem_insert c _)
  have he : e ∈ Y := Subgroup.subset_closure (Set.mem_insert_of_mem c rfl)
  have hxX : ⁅a, b⁆ ∈ ⁅X, X⁆ := Subgroup.commutator_mem_commutator ha hb
  have hxX' : ⁅a, b⁆ ∈ X := by
    rw [commutatorElement_def]
    exact X.mul_mem (X.mul_mem (X.mul_mem ha hb) (X.inv_mem ha)) (X.inv_mem hb)
  have hyY : ⁅c, e⁆ ∈ Y := by
    rw [commutatorElement_def]
    exact Y.mul_mem (Y.mul_mem (Y.mul_mem hc he) (Y.inv_mem hc)) (Y.inv_mem he)
  have hxy : ⁅a, b⁆ * ⁅c, e⁆ = ⁅c, e⁆ * ⁅a, b⁆ := hXY _ hxX' _ hyY
  exact exists_abelian_sylow_of_commute η hsurj hcentral hXY hxX hyY (i := 1) (j := 1)
    (by rwa [pow_one]) (by rwa [pow_one])
    (closure_pair_maximal hxy hx3 hy3 hx1 hy1 hxy1 hxy2 hD)

theorem not_sq_dvd_of_factor {N a b m : ℕ} (hN : N = 2 ^ a * 3 ^ b * m)
    (hm : ∀ r : ℕ, r ≤ 33 → r.Prime → r ≠ 2 → r ≠ 3 → ¬ r ^ 2 ∣ m) (hm' : m ≤ 1085) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3) : ¬ r ^ 2 ∣ N := by
  intro h
  have hcop : Nat.Coprime (r ^ 2) (2 ^ a * 3 ^ b) := by
    refine Nat.Coprime.pow_left 2 (Nat.Coprime.mul_right ?_ ?_)
    · exact Nat.Coprime.pow_right a ((Nat.coprime_primes hr Nat.prime_two).mpr hr2)
    · exact Nat.Coprime.pow_right b ((Nat.coprime_primes hr Nat.prime_three).mpr hr3)
  have hdvd : r ^ 2 ∣ m := hcop.dvd_of_dvd_mul_left (hN ▸ h)
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · exfalso
      subst h0
      exact hm 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (dvd_zero _)
    · exact h0
  have hle : r ^ 2 ≤ m := Nat.le_of_dvd hm0 hdvd
  have hr33 : r ≤ 33 := by
    by_contra hc
    push Not at hc
    have : 34 ^ 2 ≤ r ^ 2 := Nat.pow_le_pow_left hc 2
    omega
  exact hm r hr33 hr hr2 hr3 hdvd

theorem ext_of_pairs {D : Type} [Group D] [Finite D]
    (h5 : ∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ 3 → ¬ r ^ 2 ∣ Nat.card D) {a b c e : D}
    (hac : a * c = c * a) (hae : a * e = e * a) (hbc : b * c = c * b) (hbe : b * e = e * b)
    (hx3 : ⁅a, b⁆ ^ 3 = 1) (hy3 : ⁅c, e⁆ ^ 3 = 1) (hx1 : ⁅a, b⁆ ≠ 1) (hy1 : ⁅c, e⁆ ≠ 1)
    (hxy1 : ⁅a, b⁆ ≠ ⁅c, e⁆) (hxy2 : ⁅a, b⁆ ≠ ⁅c, e⁆ ^ 2) (hD : ¬ 27 ∣ Nat.card D) :
    ∀ (E : Type) [Group E] [Finite E] (η : E →* D), Function.Surjective η →
      η.ker ≤ Subgroup.center E → ∀ p [Fact p.Prime], p ≠ 2 →
        ∃ P : Sylow p E, IsMulCommutative (P : Subgroup E) := by
  intro E _ _ η hs hc p hp hp2
  by_cases hp3 : p = 3
  · subst hp3
    exact exists_abelian_sylow_three_of_pairs η hs hc hac hae hbc hbe hx3 hy3 hx1 hy1 hxy1 hxy2
      hD
  · obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p E))
    exact ⟨P, isMulCommutative_sylow_of_cyclic η hs hc (fun R =>
      CFSG.SectionRank.sylow_isCyclic_of_not_sq_dvd (h5 p hp.out hp2 hp3) R) P⟩

structure RankTwoType (Kt : Type) [Group Kt] [Finite Kt] : Prop where
  ext : ∀ (E : Type) [Group E] [Finite E] (η : E →* Kt), Function.Surjective η →
    η.ker ≤ Subgroup.center E → ∀ p [Fact p.Prime], p ≠ 2 →
      ∃ P : Sylow p E, IsMulCommutative (P : Subgroup E)
  simple : IsSimpleGroup ↥(threePartTop Kt)
  nonab : ∃ a b : ↥(threePartTop Kt), a * b ≠ b * a
  facts : Lem8.RankTwoFacts ↥(threePartTop Kt)

theorem threePartTop_perm (m : ℕ) :
    threePartTop (Equiv.Perm (Fin m)) = alternatingGroup (Fin m) := by
  refine le_antisymm (threePartTop_le_alternating m) ?_
  rw [← Equiv.Perm.closure_three_cycles_eq_alternating]
  refine (Subgroup.closure_le _).mpr fun σ hσ => Subgroup.subset_closure ⟨1, ?_⟩
  rw [pow_one, ← hσ.orderOf, pow_orderOf_eq_one]

theorem perm_pair_facts {m : ℕ} (hm : 6 ≤ m ∧ m ≤ 8) :
    ∃ a b c e : Equiv.Perm (Fin m), a * c = c * a ∧ a * e = e * a ∧ b * c = c * b ∧
      b * e = e * b ∧ ⁅a, b⁆ ^ 3 = 1 ∧ ⁅c, e⁆ ^ 3 = 1 ∧ ⁅a, b⁆ ≠ 1 ∧ ⁅c, e⁆ ≠ 1 ∧
      ⁅a, b⁆ ≠ ⁅c, e⁆ ∧ ⁅a, b⁆ ≠ ⁅c, e⁆ ^ 2 := by
  obtain ⟨hm6, hm8⟩ := hm
  interval_cases m
  · refine ⟨Equiv.swap 0 1, Equiv.swap 1 2, Equiv.swap 3 4, Equiv.swap 4 5, ?_⟩
    simp only [commutatorElement_def]
    decide
  · refine ⟨Equiv.swap 0 1, Equiv.swap 1 2, Equiv.swap 3 4, Equiv.swap 4 5, ?_⟩
    simp only [commutatorElement_def]
    decide
  · refine ⟨Equiv.swap 0 1, Equiv.swap 1 2, Equiv.swap 3 4, Equiv.swap 4 5, ?_⟩
    simp only [commutatorElement_def]
    decide

theorem rankTwoType_perm {m : ℕ} (hm : 6 ≤ m ∧ m ≤ 8) : RankTwoType (Equiv.Perm (Fin m)) := by
  have hT := threePartTop_perm m
  obtain ⟨a, b, c, e, hac, hae, hbc, hbe, hx3, hy3, hx1, hy1, hxy1, hxy2⟩ := perm_pair_facts hm
  have hcard : Nat.card (Equiv.Perm (Fin m)) = m.factorial := by
    rw [Nat.card_perm, Nat.card_fin]
  have hfac : m.factorial = 2 ^ 4 * 3 ^ 2 * 5 ∨ m.factorial = 2 ^ 4 * 3 ^ 2 * 35 ∨
      m.factorial = 2 ^ 7 * 3 ^ 2 * 35 := by
    obtain ⟨hm6, hm8⟩ := hm
    interval_cases m <;> decide
  refine ⟨ext_of_pairs (fun r hr hr2 hr3 => ?_) hac hae hbc hbe hx3 hy3 hx1 hy1 hxy1 hxy2 ?_,
    ?_, ?_, ?_⟩
  · rw [hcard]
    rcases hfac with h | h | h
    · exact not_sq_dvd_of_factor h (by decide) (by norm_num) hr hr2 hr3
    · exact not_sq_dvd_of_factor h (by decide) (by norm_num) hr hr2 hr3
    · exact not_sq_dvd_of_factor h (by decide) (by norm_num) hr hr2 hr3
  · rw [hcard]
    rcases hfac with h | h | h <;> rw [h] <;> decide
  · rw [hT]
    exact alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; omega)
  · obtain ⟨hm6, hm8⟩ := hm
    have h1 : (Equiv.swap (⟨0, by omega⟩ : Fin m) ⟨1, by omega⟩ *
        Equiv.swap ⟨1, by omega⟩ ⟨2, by omega⟩) ^ 3 ^ 1 = 1 := by
      interval_cases m <;> decide +revert
    have h2 : (Equiv.swap (⟨1, by omega⟩ : Fin m) ⟨2, by omega⟩ *
        Equiv.swap ⟨2, by omega⟩ ⟨3, by omega⟩) ^ 3 ^ 1 = 1 := by
      interval_cases m <;> decide +revert
    refine ⟨⟨_, Subgroup.subset_closure ⟨1, h1⟩⟩, ⟨_, Subgroup.subset_closure ⟨1, h2⟩⟩,
      fun h => ?_⟩
    have := congrArg Subtype.val h
    simp only [Subgroup.coe_mul] at this
    revert this
    interval_cases m <;> decide +revert
  · exact Lem8.rankTwoFacts_alt (by omega) (MulEquiv.subgroupCongr hT)

@[expose] def invGL {m : ℕ} (A : Matrix (Fin m) (Fin m) (ZMod 2)) (hA : A * A = 1) :
    Matrix.GeneralLinearGroup (Fin m) (ZMod 2) :=
  ⟨A, A, hA, hA⟩

theorem gl4_pair_facts :
    ∃ a b c e : Matrix.GeneralLinearGroup (Fin 4) (ZMod 2), a * c = c * a ∧ a * e = e * a ∧
      b * c = c * b ∧ b * e = e * b ∧ ⁅a, b⁆ ^ 3 = 1 ∧ ⁅c, e⁆ ^ 3 = 1 ∧ ⁅a, b⁆ ≠ 1 ∧
      ⁅c, e⁆ ≠ 1 ∧ ⁅a, b⁆ ≠ ⁅c, e⁆ ∧ ⁅a, b⁆ ≠ ⁅c, e⁆ ^ 2 ∧ a * b ≠ b * a := by
  refine ⟨invGL !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] (by decide),
    invGL !![1, 1, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] (by decide),
    invGL !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0] (by decide),
    invGL !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 1; 0, 0, 0, 1] (by decide), ?_⟩
  simp only [commutatorElement_def]
  refine ⟨Units.ext ?_, Units.ext ?_, Units.ext ?_, Units.ext ?_, Units.ext ?_, Units.ext ?_,
    fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
    first
    | (simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_one, invGL]; decide)
    | (have := congrArg Units.val h
       simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_one, invGL] at this
       revert this; decide)

theorem gl5_pair_facts :
    ∃ a b c e : Matrix.GeneralLinearGroup (Fin 5) (ZMod 2), a * c = c * a ∧ a * e = e * a ∧
      b * c = c * b ∧ b * e = e * b ∧ ⁅a, b⁆ ^ 3 = 1 ∧ ⁅c, e⁆ ^ 3 = 1 ∧ ⁅a, b⁆ ≠ 1 ∧
      ⁅c, e⁆ ≠ 1 ∧ ⁅a, b⁆ ≠ ⁅c, e⁆ ∧ ⁅a, b⁆ ≠ ⁅c, e⁆ ^ 2 ∧ a * b ≠ b * a := by
  refine ⟨invGL !![0, 1, 0, 0, 0; 1, 0, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]
      (by decide),
    invGL !![1, 1, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]
      (by decide),
    invGL !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 1, 0, 0; 0, 0, 0, 0, 1]
      (by decide),
    invGL !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 1, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]
      (by decide), ?_⟩
  simp only [commutatorElement_def]
  refine ⟨Units.ext ?_, Units.ext ?_, Units.ext ?_, Units.ext ?_, Units.ext ?_, Units.ext ?_,
    fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
    first
    | (simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_one, invGL]; decide)
    | (have := congrArg Units.val h
       simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_one, invGL] at this
       revert this; decide)

theorem rankTwoType_GL {m : ℕ} (hm : m = 4 ∨ m = 5) :
    RankTwoType (Matrix.GeneralLinearGroup (Fin m) (ZMod 2)) := by
  have : IsSimpleGroup (Matrix.GeneralLinearGroup (Fin m) (ZMod 2)) :=
    isSimpleGroup_GL_zmod_two (by omega)
  have hcard : Nat.card (Matrix.GeneralLinearGroup (Fin m) (ZMod 2)) = 2 ^ 6 * 3 ^ 2 * 35 ∨
      Nat.card (Matrix.GeneralLinearGroup (Fin m) (ZMod 2)) = 2 ^ 10 * 3 ^ 2 * 1085 := by
    rw [Matrix.card_GL_field, ZMod.card]
    rcases hm with rfl | rfl <;> decide
  have hT : threePartTop (Matrix.GeneralLinearGroup (Fin m) (ZMod 2)) = ⊤ :=
    threePartTop_eq_top_of_simple (by rcases hcard with h | h <;> rw [h] <;> decide)
  obtain ⟨a, b, c, e, hac, hae, hbc, hbe, hx3, hy3, hx1, hy1, hxy1, hxy2, hab⟩ :
      ∃ a b c e : Matrix.GeneralLinearGroup (Fin m) (ZMod 2), a * c = c * a ∧ a * e = e * a ∧
        b * c = c * b ∧ b * e = e * b ∧ ⁅a, b⁆ ^ 3 = 1 ∧ ⁅c, e⁆ ^ 3 = 1 ∧ ⁅a, b⁆ ≠ 1 ∧
        ⁅c, e⁆ ≠ 1 ∧ ⁅a, b⁆ ≠ ⁅c, e⁆ ∧ ⁅a, b⁆ ≠ ⁅c, e⁆ ^ 2 ∧ a * b ≠ b * a := by
    rcases hm with rfl | rfl
    · exact gl4_pair_facts
    · exact gl5_pair_facts
  refine ⟨ext_of_pairs (fun r hr hr2 hr3 => ?_) hac hae hbc hbe hx3 hy3 hx1 hy1 hxy1 hxy2 ?_,
    ?_, ?_, ?_⟩
  · rcases hcard with h | h
    · exact not_sq_dvd_of_factor h (by decide) (by norm_num) hr hr2 hr3
    · exact not_sq_dvd_of_factor h (by decide) (by norm_num) hr hr2 hr3
  · rcases hcard with h | h <;> rw [h] <;> decide
  · rw [hT]
    exact Subgroup.topEquiv.isSimpleGroup
  · refine ⟨⟨a, hT ▸ Subgroup.mem_top a⟩, ⟨b, hT ▸ Subgroup.mem_top b⟩, fun h => hab ?_⟩
    exact congrArg Subtype.val h
  · let e₁ : ↥(threePartTop (Matrix.GeneralLinearGroup (Fin m) (ZMod 2))) ≃*
        Matrix.SpecialLinearGroup (Fin m) (ZMod 2) :=
      ((MulEquiv.subgroupCongr hT).trans Subgroup.topEquiv).trans
        (CFSG.QuasithinUnique.Setup.Family.slEquivGL m).symm
    rcases hm with rfl | rfl
    · exact Lem8.rankTwoFacts_sl_four e₁
    · exact Lem8.rankTwoFacts_sl_five e₁

theorem isQuasisimple_of_simple {Q : Type*} [Group Q] [IsSimpleGroup Q]
    (hnab : ∃ a b : Q, a * b ≠ b * a) : CFSG.IsQuasisimple Q := by
  have hZ : Subgroup.center Q = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      exact hab ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b)) a)
  have hcomm : commutator Q = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator Q) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      have : ⁅a, b⁆ = 1 := by
        rw [← Subgroup.mem_bot, ← h]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      exact hab (commutatorElement_eq_one_iff_mul_comm.mp this)
    · exact h
  let e : Q ⧸ Subgroup.center Q ≃* Q :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  refine ⟨⟨hcomm⟩, e.isSimpleGroup, ?_⟩
  obtain ⟨a, b, hab⟩ := hnab
  refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
  have := congrArg e h
  simpa using this

theorem eq_bot_or_top_of_subnormal {Q : Type*} [Group Q] [IsSimpleGroup Q] {H : Subgroup Q}
    (hH : IsSubnormal H ⊤) : H = ⊥ ∨ H = ⊤ :=
  hH.eq_bot_or_top

variable {G : Type} [Group G]

theorem eq_of_subnormal_of_le_sup {A O H : Subgroup G} (hO2 : IsPGroup 2 O)
    (hgen : A ≤ Subgroup.closure {x | x ∈ A ∧ ∃ k : ℕ, x ^ 3 ^ k = 1})
    (hH : IsSubnormal H A) (hHO : A ≤ H ⊔ O) (hOA : O ≤ A) : H = A := by
  induction hH with
  | refl => rfl
  | @step H M K hle hN hMK ih =>
    have hMK' : M = K := ih hgen (hHO.trans (sup_le_sup_right hle O)) hOA
    subst hMK'
    refine le_antisymm hle ?_
    refine hgen.trans ((Subgroup.closure_le _).mpr ?_)
    rintro x ⟨hxM, k, hk⟩
    have hON : O ≤ Subgroup.normalizer (H : Set G) :=
      hOA.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hle).mp hN)
    exact mem_of_pow_three_eq_one hO2 hON (hHO hxM) hk

theorem pCore_eq_ker_of_simple {B S : Type*} [Group B] [Group S] [Finite S] [IsSimpleGroup S]
    (h3 : 3 ∣ Nat.card S) (χ : B →* S) (hχ : Function.Surjective χ) (hker : IsPGroup 2 χ.ker) :
    CFSG.pCore 2 B = χ.ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm ?_ (le_sSup ⟨χ.normal_ker, hker⟩)
  have hn : ((CFSG.pCore 2 B).map χ).Normal := CFSG.pCore_normal.map χ hχ
  have h2 : IsPGroup 2 ((CFSG.pCore 2 B).map χ) := CFSG.pCore_isPGroup.map χ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((CFSG.pCore 2 B).map χ) with hb | ht
  · intro x hx
    have : χ x ∈ (CFSG.pCore 2 B).map χ := ⟨x, hx, rfl⟩
    rwa [hb, Subgroup.mem_bot] at this
  · exfalso
    rw [ht] at h2
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp h2
    rw [Subgroup.card_top] at hk
    rw [hk] at h3
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega

end L619

variable {G : Type} [Group G] [Finite G] {T M L V H : Subgroup G} {n : ℕ} {y : G}

namespace Dat619

variable {z : G} {T' D' : Subgroup G} (hd : Dat619 T M L V H n y z T' D')
include hd

theorem false_of_rankTwo (h : Hyp6116 G T M L V n)
    (h432 : Stmt4_3_2) (hF : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (hW : IsElemAbelian 2 (ch619W T L V z))
    {Ks : Fin 1 → Subgroup (MulAut ↥(L619.V0 hW (ch6ZS T L V)
      (conjClosure (conjSub y V) (ch619I T L V ⊔ T'))))}
    (hdec : G6.IsTransvectionDecomposition
      (L619.img0 hW (ch6ZS T L V) (conjClosure (conjSub y V) (ch619I T L V ⊔ T'))) Ks)
    {Kt : Type} [Group Kt] [Finite Kt] (hKt : L619.RankTwoType Kt)
    (hK : Nonempty (↥(Ks 0) ≃* Kt)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have c := hd.cfg
  have hz := hd.z619
  have hY := hd.isY
  revert Ks
  set I := ch619I T L V with hI
  set P := conjClosure (conjSub y V) (I ⊔ T') with hP
  set K := L619.img0 hW (ch6ZS T L V) P with hKdef
  intro Ks hdec hK
  have hK0 : Ks 0 = K := by
    rw [← hdec.iSup_eq]
    refine le_antisymm (le_iSup Ks 0) (iSup_le fun j => ?_)
    rw [Subsingleton.elim j 0]
  rw [hK0] at hK
  obtain ⟨eK⟩ := hK
  have hPN := c.conjClosure_E_le_normWZX hY
  set φ := L619.actOn hW (ch6ZS T L V) P hPN (fun x => L619.act0_mem_img0 hW _ P x.2) with hφ
  have hφs : Function.Surjective φ := L619.actOn_surjective hW _ P hPN
  set ψ : ↥P →* Kt := eK.toMonoidHom.comp φ with hψ
  have hψs : Function.Surjective ψ := eK.surjective.comp hφs
  have hψ1 : ∀ x : ↥P, ψ x = 1 ↔ (x : G) ∈ ch619K2 T L V z := by
    intro x
    rw [hψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      Subtype.ext_iff]
    exact c.act0_eq_one_iff h h432 hz hY hW (x := Subgroup.inclusion hPN x) x.2
  have hext : ∀ (E : Type) [Group E] [Finite E] (η : E →* ↥K), Function.Surjective η →
      η.ker ≤ Subgroup.center E → ∀ p [Fact p.Prime], p ≠ 2 →
        ∃ R : Sylow p E, IsMulCommutative (R : Subgroup E) := by
    intro E _ _ η hη hηc p _ hp2
    refine hKt.ext E (eK.toMonoidHom.comp η) (eK.surjective.comp hη) (fun x hx => hηc ?_) p hp2
    rw [MonoidHom.mem_ker] at hx ⊢
    rwa [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff] at hx
  have hPK2 : P ⊓ ch619K2 T L V z ≤ pCoreOf 2 P := c.inf_K2_le_pCoreOf_of h h432 hz hY hW hext
  have hker : IsPGroup 2 ψ.ker := by
    have hle : ψ.ker ≤ (pCoreOf 2 P).subgroupOf P := fun x hx =>
      Subgroup.mem_subgroupOf.mpr (hPK2 ⟨x.2, (hψ1 x).mp hx⟩)
    exact ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P).of_equiv
      (Subgroup.subgroupOfEquivOfLe (CFSG.LieType.BorelTits.pCoreOf_le 2 P)).symm).to_le hle
  set S := L619.threePartTop Kt with hS
  have : IsSimpleGroup ↥S := hKt.simple
  obtain ⟨g3, hg3⟩ := Lem8.exists_orderOf_eq_three_of_two_le_pRank
    (le_trans (by norm_num) hKt.facts.rank)
  have h3S : 3 ∣ Nat.card ↥S := hg3 ▸ orderOf_dvd_natCard g3
  set A := L619.threePart P with hA
  have hAP : A ≤ P := L619.threePart_le P
  let ψA : ↥A →* ↥S := (ψ.comp (Subgroup.inclusion hAP)).codRestrict S fun a =>
    L619.psi_mem_threePartTop ψ a.2
  have hψAs : Function.Surjective ψA := by
    rintro ⟨k, hk⟩
    obtain ⟨x, hx, hxk⟩ := L619.exists_preimage_threePartTop ψ hψs hk
    exact ⟨⟨x, hx⟩, Subtype.ext hxk⟩
  have hψA1 : ∀ x : ↥A, ψA x = 1 ↔ ψ (Subgroup.inclusion hAP x) = 1 := fun x =>
    Subtype.ext_iff
  have hψAker : IsPGroup 2 ψA.ker := by
    intro x
    obtain ⟨k, hk⟩ := hker ⟨_, (hψA1 x.1).mp x.2⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    simpa using congrArg (fun u : ↥ψ.ker => ((u : ↥P) : G)) hk
  set O : Subgroup G := ψA.ker.map A.subtype with hO
  have hO2 : IsPGroup 2 O := hψAker.map _
  have hOA : O ≤ A := Subgroup.map_subtype_le _
  have hAO : ∀ x (hx : x ∈ A), ψA ⟨x, hx⟩ = 1 → x ∈ O := fun x hx h1 => ⟨⟨x, hx⟩, h1, rfl⟩
  have hgen : A ≤ Subgroup.closure {x | x ∈ A ∧ ∃ k : ℕ, x ^ 3 ^ k = 1} :=
    Subgroup.closure_mono fun x hx => ⟨L619.mem_threePart hx.1 hx.2.choose_spec, hx.2⟩
  obtain ⟨sa, sb, hsab⟩ := hKt.nonab
  have hSperf : commutator ↥S = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator ↥S) with h0 | h0
    · exfalso
      have : ⁅sa, sb⁆ = 1 := by
        rw [← Subgroup.mem_bot, ← h0]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top sa) (Subgroup.mem_top sb)
      exact hsab (commutatorElement_eq_one_iff_mul_comm.mp this)
    · exact h0
  have hsupp : ∀ (X : Subgroup G) (hXA : X ≤ A),
      (∀ s : ↥S, ∃ x, ∃ hx : x ∈ X, ψA ⟨x, hXA hx⟩ = s) → A ≤ X ⊔ O := by
    intro X hXA hX a ha
    obtain ⟨x, hx, hxa⟩ := hX (ψA ⟨a, ha⟩)
    have hk : ψA ⟨x⁻¹ * a, A.mul_mem (A.inv_mem (hXA hx)) ha⟩ = 1 := by
      have e : (⟨x⁻¹ * a, A.mul_mem (A.inv_mem (hXA hx)) ha⟩ : ↥A) =
          (⟨x, hXA hx⟩ : ↥A)⁻¹ * ⟨a, ha⟩ := rfl
      rw [e, map_mul, map_inv, hxa, inv_mul_cancel]
    have e : a = x * (x⁻¹ * a) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hx)
      (Subgroup.mem_sup_right (hAO _ _ hk))
  have hAperf : ⁅A, A⁆ = A := by
    have hCA : ⁅A, A⁆ ≤ A := Subgroup.commutator_le_self A
    refine L619.eq_of_subnormal_of_le_sup hO2 hgen
      (A3.subnormal_of_normal hCA ?_) ?_ hOA
    · rw [← Subgroup.map_subtype_commutator A]
      show (((commutator ↥A).map A.subtype).comap A.subtype).Normal
      rw [Subgroup.comap_map_eq_self_of_injective A.subtype_injective]
      exact (commutator ↥A).normal_of_characteristic
    · refine hsupp _ hCA fun s => ?_
      have hs : s ∈ (commutator ↥A).map ψA := by
        rw [_root_.commutator_def, Subgroup.map_commutator,
          Subgroup.map_top_of_surjective ψA hψAs, ← _root_.commutator_def, hSperf]
        exact Subgroup.mem_top s
      obtain ⟨u, hu, rfl⟩ := hs
      have hu' : (u : G) ∈ ⁅A, A⁆ := by
        rw [← Subgroup.map_subtype_commutator A]
        exact ⟨u, hu, rfl⟩
      exact ⟨u, hu', rfl⟩
  set H₀ := Subgroup.normalizer (ch6ZS T L V : Set G) with hH₀
  have hPI : P ≤ I := c.conjClosure_E_le_I hY
  have hIP : I ≤ Subgroup.normalizer (P : Set G) :=
    hY.I_le.trans (le_normalizer_conjClosure _ _)
  have hIH₀ : I ≤ H₀ := Subgroup.centralizer_le_normalizer _
  have hAI : A ≤ I := hAP.trans hPI
  have hAH₀ : A ≤ H₀ := hAI.trans hIH₀
  have hIA : I ≤ Subgroup.normalizer (A : Set G) :=
    hIP.trans (L619.normalizer_le_normalizer_threePart P)
  have hAsub : IsSubnormal A H₀ :=
    IsSubnormal.step hAI ((Subgroup.normal_subgroupOf_iff_le_normalizer hAI).mpr hIA)
      (A3.subnormal_of_normal hIH₀ ((Subgroup.normal_subgroupOf_iff_le_normalizer hIH₀).mpr
        (L619.normalizer_I_of le_rfl)))
  have hAc : A ∈ cComp H₀ := by
    refine ⟨fun h0 => ?_, hAperf, hAsub, fun X hXA hX0 hXperf hXsub => ?_⟩
    ·
      obtain ⟨⟨x, hx⟩, hxs⟩ := hψAs g3
      have hx1 : x = 1 := by rw [h0] at hx; exact hx
      subst hx1
      have : ψA ⟨1, hx⟩ = 1 := map_one ψA
      rw [hxs] at this
      rw [this, orderOf_one] at hg3
      omega
    ·
      have hXA' : IsSubnormal X A := A3.subnormal_of_le_of_le hXsub hXA.le hAH₀
      have hXS : IsSubnormal ((X.subgroupOf A).map ψA) ⊤ := by
        have h1 := A3.subnormal_map ψA (A4.subnormal_subgroupOf A hXA')
        rwa [Subgroup.subgroupOf_self, Subgroup.map_top_of_surjective ψA hψAs] at h1
      rcases L619.eq_bot_or_top_of_subnormal hXS with hb | ht
      ·
        apply hX0
        have hX2 : IsPGroup 2 (X.subgroupOf A) := hψAker.to_le fun u hu => by
          have : ψA u ∈ (X.subgroupOf A).map ψA := ⟨u, hu, rfl⟩
          rwa [hb, Subgroup.mem_bot] at this
        have hX2' : IsPGroup 2 X := hX2.of_equiv (Subgroup.subgroupOfEquivOfLe hXA.le)
        have : Group.IsNilpotent X := hX2'.isNilpotent
        have hsolv : Group.IsSolvable X := inferInstance
        rw [← (perfectCore_eq_self_iff X).mpr hXperf]
        exact (isSolvable_iff_perfectCore_eq_bot X).mp hsolv
      ·
        have hle : A ≤ X ⊔ O := hsupp X hXA.le fun s => by
          have hs : s ∈ (X.subgroupOf A).map ψA := ht ▸ Subgroup.mem_top s
          obtain ⟨u, hu, rfl⟩ := hs
          exact ⟨u, hu, rfl⟩
        exact hXA.ne (L619.eq_of_subnormal_of_le_sup hO2 hgen hXA' hle hOA)
  set A' : Subgroup ↥H₀ := A.subgroupOf H₀ with hA'
  have hA'c : A' ∈ cComp (⊤ : Subgroup ↥H₀) := subgroupOf_mem_cComp hAc
  let ψA' : ↥A' →* ↥S := ψA.comp (Subgroup.subgroupOfEquivOfLe hAH₀).toMonoidHom
  have hψA's : Function.Surjective ψA' := hψAs.comp (MulEquiv.surjective _)
  have hψA'ker : IsPGroup 2 ψA'.ker := by
    intro x
    obtain ⟨k, hk⟩ := hψAker ⟨(Subgroup.subgroupOfEquivOfLe hAH₀) x.1, x.2⟩
    refine ⟨k, Subtype.ext ((Subgroup.subgroupOfEquivOfLe hAH₀).injective ?_)⟩
    simpa using congrArg Subtype.val hk
  have hpc := L619.pCore_eq_ker_of_simple h3S ψA' hψA's hψA'ker
  let eA : ↥A' ⧸ CFSG.pCore 2 ↥A' ≃* ↥S :=
    (QuotientGroup.quotientMulEquivOfEq hpc).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψA' hψA's)
  have hQ' : CFSG.IsQuasisimple (↥A' ⧸ CFSG.pCore 2 ↥A') :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eA.symm
      (L619.isQuasisimple_of_simple ⟨sa, sb, hsab⟩)
  have h2A : ¬ 3 ∣ Nat.card (CFSG.pCore 2 ↥A') := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 (CFSG.pCore_isPGroup (G := ↥A') (p := 2))
    rw [hm]
    intro h3
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  have hrank : 1 < CFSG.Open.pRank 3 A' := by
    rw [← pRank_top_subtype A', ← CFSG.SectionRank.pRank_quotient_eq (CFSG.pCore 2 ↥A') h2A,
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) eA]
    exact lt_of_lt_of_le (by norm_num) hKt.facts.rank
  have hO2H₀ : pCoreOf 2 H₀ ≠ ⊥ := by
    intro h0
    apply h.toHyp611Nat.ZS_ne_bot
    rw [eq_bot_iff, ← h0]
    have hZel : IsElemAbelian 2 (ch6ZS T L V) :=
      B2F.isElemAbelian_mono inf_le_left h.toHyp611.isElemAbelian
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl
      (B2F.isPGroup_of_isElemAbelian hZel)
  have hsqtk : SQTKGroup ↥H₀ :=
    sqtkGroup_of_pCoreOf_ne_bot h.toHyp5_0_1.qtke h.toHyp5_0_1.simple h.toHyp5_0_1.nonabelian
      hO2H₀
  have hhyp := sqtkHyp_quotient_of_pCoreOf_ne_bot h.toHyp5_0_1.qtke h.toHyp5_0_1.simple
    h.toHyp5_0_1.nonabelian hO2H₀
  obtain ⟨d, hdD, hd1⟩ : ∃ d ∈ D', d ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : D' = ⊥ := (Subgroup.eq_bot_iff_forall D').mpr hcon
    have h3 := hd.card_D'
    rw [this, Subgroup.card_bot] at h3
    omega
  have hdA : d ∉ A := fun hdA => by
    have hdI : d ∈ D' ⊓ I := ⟨hdD, hAI hdA⟩
    rw [hd.D'_inf, Subgroup.mem_bot] at hdI
    exact hd1 hdI
  have hd3 : d ^ 3 = 1 := hd.pow_three_eq_one hdD
  have hdo : orderOf d = 3 := orderOf_eq_prime hd3 hd1
  haveI : A'.Normal := A318.normal_of_pRank_gt_one hsqtk (h38 _ hhyp) hA'c Nat.prime_three
    (by norm_num) hrank
  have hZS : Subgroup.center ↥S = ⊥ := Lem8.center_eq_bot_of_nonabelian ⟨sa, sb, hsab⟩
  have hZQ : Nat.card (Subgroup.center (↥A' ⧸ CFSG.pCore 2 ↥A')) ∣ 3 := by
    rw [Lem8.card_center_eq_of_mulEquiv eA, hZS, Subgroup.card_bot]
    exact one_dvd 3
  obtain ⟨eS⟩ := Lem8.nonempty_mulEquiv_starImage A' hQ' hZQ
    ⟨eA.symm g3, by rw [MulEquiv.orderOf_eq]; exact hg3⟩
  let e : ↥S ≃* ↥(starImage 3 A') := eA.symm.trans eS
  have hX : L34.ListOrd (Nat.card ↥(starImage 3 A')) := by
    rw [← Nat.card_congr e.toEquiv]
    exact hKt.facts.card
  have hX8 : Nat.card ↥(starImage 3 A') = 20160 →
      Nonempty (↥(starImage 3 A') ≃* alternatingGroup (Fin 8)) := fun h20 => by
    obtain ⟨e8⟩ := hKt.facts.a8 (by rw [Nat.card_congr e.toEquiv]; exact h20)
    exact ⟨e.symm.trans e8⟩
  have hZX : Nat.card (Subgroup.center ↥(starImage 3 A')) = 1 := by
    rw [← Lem8.card_center_eq_of_mulEquiv e, hZS, Subgroup.card_bot]
  rcases a318 hF hsqtk (h36 _ hhyp) (h38 _ hhyp) hA'c hQ' Nat.prime_three (by norm_num) hrank
    with h1 | ⟨-, s, q, hq, hpsl, -⟩ | ⟨-, h3g, -⟩
  ·
    apply hdA
    have hAeq := Lem8.eq_closure_image_of_subgroupOf_eq hAH₀ h1
    rw [Lem8.image_pElements_three] at hAeq
    rw [hAeq]
    exact Subgroup.subset_closure ⟨hd.D'_le_ZS hdD, 1, by rw [pow_one]; exact hd3⟩
  · exact L34.not_isPSLEps3q_of_card hX hX8 s q hq hpsl
  · rcases h3g with ⟨s, q, hq, hsl⟩ | hA6 | hA7 | hM22
    · exact L34.not_isSLEps3_of_card hX s q hq hsl
    · have := hA6.2.1
      omega
    · have := hA7.2.1
      omega
    · exact Lem8.not_isHat_M22 hX hM22

end Dat619

theorem case619RankTwo_of (h432 : Stmt4_3_2) (hF : A318Facts)
    (h36 : A36ForSQTK) (h38 : A38ForSQTK) : Case619RankTwo := by
  intro G _ _ T M L V H n y z T' D' h hd hW Ks hdec hK
  rcases hK with ⟨m, hm, ⟨e⟩⟩ | ⟨m, hm6, hm8, ⟨e⟩⟩
  · exact hd.false_of_rankTwo h h432 hF h36 h38 hW hdec (L619.rankTwoType_GL hm) ⟨e⟩
  · exact hd.false_of_rankTwo h h432 hF h36 h38 hW hdec (L619.rankTwoType_perm ⟨hm6, hm8⟩) ⟨e⟩

end CFSG.Quasithin.H13
