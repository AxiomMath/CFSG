module

public import CFSG.LocalAnalysis.EvenBN.TwoF4.ModelTorus
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public noncomputable section

namespace CFSG.Quasithin.H13.F431.TwoF4

open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
  CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.EvenBN.TwoF4
  CFSG.LieType.Ree.LargeReeCover

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem torusPair_conj_sylowVec (hK : Nat.card K = 2 ^ (2 * a + 1)) (t : Kˣ × Kˣ)
    (x : Fin 12 → K) :
    torusPair a t * sylowVec a K x * (torusPair a t)⁻¹ =
      sylowVec a K fun n => (rootChar K a (Idx.ofCoord n) t : K) * x n := by
  have e : ∀ τ p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ p₁₁ p₁₂ : ModGL F4.tag K,
      τ * (p₁ * p₂ * p₃ * p₄ * p₅ * p₆ * p₇ * p₈ * p₉ * p₁₀ * p₁₁ * p₁₂) * τ⁻¹ =
        (τ * p₁ * τ⁻¹) * (τ * p₂ * τ⁻¹) * (τ * p₃ * τ⁻¹) * (τ * p₄ * τ⁻¹) * (τ * p₅ * τ⁻¹) *
          (τ * p₆ * τ⁻¹) * (τ * p₇ * τ⁻¹) * (τ * p₈ * τ⁻¹) * (τ * p₉ * τ⁻¹) * (τ * p₁₀ * τ⁻¹) *
          (τ * p₁₁ * τ⁻¹) * (τ * p₁₂ * τ⁻¹) := fun _ _ _ _ _ _ _ _ _ _ _ _ _ => by group
  rw [sylowVec_eq_prod_rootElt hK, sylowVec_eq_prod_rootElt hK, e]
  simp only [torusPair_conj_rootElt hK]
  rfl

theorem coord_eq_zero_of_conj_eq (hK : Nat.card K = 2 ^ (2 * a + 1)) (t : Kˣ × Kˣ)
    {x : Fin 12 → K} (h : torusPair a t * sylowVec a K x * (torusPair a t)⁻¹ = sylowVec a K x)
    (n : Fin 12) (hn : rootChar K a (Idx.ofCoord n) t ≠ 1) : x n = 0 := by
  rw [torusPair_conj_sylowVec hK] at h
  have hx := congrFun ((bijOn_sylowVec hK).injOn trivial trivial h) n
  have h1 : ((rootChar K a (Idx.ofCoord n) t : Kˣ) : K) ≠ 1 := fun h1 => hn (Units.ext h1)
  have h2 : ((rootChar K a (Idx.ofCoord n) t : K) - 1) * x n = 0 := by
    rw [sub_mul, hx, one_mul, sub_self]
  exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 h1)

theorem torus_fixfree_of_chars (hK : Nat.card K = 2 ^ (2 * a + 1)) (t : Kˣ × Kˣ)
    {Z : Finset (Fin 12)} {H : Subgroup (ModGL F4.tag K)}
    (hH : (H : Set (ModGL F4.tag K)) = sylowVec a K '' {x | ∀ n ∈ Z, x n = 0})
    (hχ : ∀ n, n ∉ Z → rootChar K a (Idx.ofCoord n) t ≠ 1) :
    ∀ y ∈ H, torusPair a t * y * (torusPair a t)⁻¹ = y → y = 1 := by
  intro y hy hc
  have hy' : y ∈ (H : Set (ModGL F4.tag K)) := hy
  rw [hH] at hy'
  obtain ⟨x, hx, rfl⟩ := hy'
  have h0 : x = 0 := funext fun n => by
    by_cases hn : n ∈ Z
    · exact hx n hn
    · exact coord_eq_zero_of_conj_eq hK t hc n (hχ n hn)
  rw [h0, sylowVec_eq_prod_rootElt hK]
  simp [rootElt_zero]

theorem rootChar_gen (i : Idx) (g : Kˣ) (c : ℤ) :
    rootChar K a i (g, g ^ c) =
      g ^ (torusExp0 (2 ^ a) i.leadRoot + c * torusExp1 (2 ^ a) i.leadRoot) := by
  rw [rootChar, torusWeight_apply, ← zpow_mul, ← zpow_add, mul_comm c]

theorem zpow_ne_one_of_abs_lt {g : Kˣ} {z : ℤ} (h0 : z ≠ 0) (h1 : |z| < (orderOf g : ℤ)) :
    g ^ z ≠ 1 := fun h =>
  h0 (Int.eq_zero_of_abs_lt_dvd (orderOf_dvd_iff_zpow_eq_one.2 h) h1)

theorem exists_unit_orderOf (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∃ g : Kˣ, ((orderOf g : ℕ) : ℤ) = 2 * ((2 : ℤ) ^ a) ^ 2 - 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  refine ⟨g, ?_⟩
  rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hK,
    Nat.cast_sub Nat.one_le_two_pow]
  push_cast
  rw [pow_succ, pow_mul']
  ring

theorem rootChar_ne_one_of {g : Kˣ} {θ : ℤ} (hθ : (2 : ℤ) ^ a = θ) (c : ℤ) (i : Idx) {z : ℤ}
    (hz : torusExp0 θ i.leadRoot + c * torusExp1 θ i.leadRoot = z) (h0 : z ≠ 0)
    (h1 : |z| < (orderOf g : ℤ)) : rootChar K a i (g, g ^ c) ≠ 1 := by
  subst hθ
  rw [rootChar_gen, hz]
  exact zpow_ne_one_of_abs_lt h0 h1

theorem exp_bounds {θ z : ℤ} (hθ : 2 ≤ θ)
    (h : z = -θ ∨ z = 4 * θ - 3 ∨ z = 1 - 2 * θ ∨ z = 2 - 2 * θ ∨ z = 2 * θ ∨ z = 1 - θ ∨
      z = θ ∨ z = 3 * θ - 1 ∨ z = 3 * θ - 2 ∨ z = 3 - 3 * θ ∨ z = 2 * θ - 1 ∨ z = 3 * θ - 2) :
    z ≠ 0 ∧ |z| < 2 * θ ^ 2 - 1 := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    refine ⟨by omega, ?_⟩ <;> rw [abs_lt] <;> constructor <;> nlinarith

theorem rootChar_ne_one_of_mem {g : Kˣ} {θ : ℤ} (hθd : (2 : ℤ) ^ a = θ) (hθ : 2 ≤ θ)
    (hg : ((orderOf g : ℕ) : ℤ) = 2 * θ ^ 2 - 1) (c : ℤ) (i : Idx) (z : ℤ)
    (hz : torusExp0 θ i.leadRoot + c * torusExp1 θ i.leadRoot = z)
    (hzs : z = -θ ∨ z = 4 * θ - 3 ∨ z = 1 - 2 * θ ∨ z = 2 - 2 * θ ∨ z = 2 * θ ∨ z = 1 - θ ∨
      z = θ ∨ z = 3 * θ - 1 ∨ z = 3 * θ - 2 ∨ z = 3 - 3 * θ ∨ z = 2 * θ - 1 ∨ z = 3 * θ - 2) :
    rootChar K a i (g, g ^ c) ≠ 1 :=
  rootChar_ne_one_of hθd c i hz (exp_bounds hθ hzs).1 (by rw [hg]; exact (exp_bounds hθ hzs).2)

theorem chars_ne_one_radR (ha : 1 ≤ a) {g : Kˣ}
    (hg : ((orderOf g : ℕ) : ℤ) = 2 * ((2 : ℤ) ^ a) ^ 2 - 1) (n : Fin 12)
    (hn : n ∉ ({1, 2} : Finset (Fin 12))) :
    rootChar K a (Idx.ofCoord n) (g, g ^ (3 : ℤ)) ≠ 1 := by
  have hθ : (2 : ℤ) ≤ 2 ^ a := by
    calc (2 : ℤ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ a := pow_le_pow_right₀ (by norm_num) ha
  obtain ⟨θ, hθd⟩ : ∃ θ : ℤ, (2 : ℤ) ^ a = θ := ⟨_, rfl⟩
  rw [hθd] at hg hθ
  obtain ⟨⟨e11, e12⟩, ⟨e21, e22⟩, ⟨e31, e32⟩, ⟨e41, e42⟩, ⟨e51, e52⟩, ⟨e61, e62⟩, ⟨e71, e72⟩,
    ⟨e81, e82⟩, ⟨e91, e92⟩, ⟨e101, e102⟩, ⟨e111, e112⟩, ⟨e121, e122⟩⟩ := torusExp_leadRoot θ
  have key := rootChar_ne_one_of_mem (K := K) (a := a) hθd hθ hg 3
  fin_cases n
  · exact key .i3 (-θ) (by rw [e31, e32]; ring) (by simp)
  · simp at hn
  · simp at hn
  · exact key .i4 (4 * θ - 3) (by rw [e41, e42]; ring) (by simp)
  · exact key .i8 (1 - 2 * θ) (by rw [e81, e82]; ring) (by simp)
  · exact key .i6 (2 - 2 * θ) (by rw [e61, e62]; ring) (by simp)
  · exact key .i11 (2 * θ) (by rw [e111, e112]; ring) (by simp)
  · exact key .i5 (1 - θ) (by rw [e51, e52]; ring) (by simp)
  · exact key .i12 θ (by rw [e121, e122]; ring) (by simp)
  · exact key .i7 (3 * θ - 1) (by rw [e71, e72]; ring) (by simp)
  · exact key .i9 (3 * θ - 2) (by rw [e91, e92]; ring) (by simp)
  · exact key .i10 (3 - 3 * θ) (by rw [e101, e102]; ring) (by simp)

theorem chars_ne_one_radS (ha : 1 ≤ a) {g : Kˣ}
    (hg : ((orderOf g : ℕ) : ℤ) = 2 * ((2 : ℤ) ^ a) ^ 2 - 1) (n : Fin 12)
    (hn : n ∉ ({0} : Finset (Fin 12))) :
    rootChar K a (Idx.ofCoord n) (g, g ^ (2 : ℤ)) ≠ 1 := by
  have hθ : (2 : ℤ) ≤ 2 ^ a := by
    calc (2 : ℤ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ a := pow_le_pow_right₀ (by norm_num) ha
  obtain ⟨θ, hθd⟩ : ∃ θ : ℤ, (2 : ℤ) ^ a = θ := ⟨_, rfl⟩
  rw [hθd] at hg hθ
  obtain ⟨⟨e11, e12⟩, ⟨e21, e22⟩, ⟨e31, e32⟩, ⟨e41, e42⟩, ⟨e51, e52⟩, ⟨e61, e62⟩, ⟨e71, e72⟩,
    ⟨e81, e82⟩, ⟨e91, e92⟩, ⟨e101, e102⟩, ⟨e111, e112⟩, ⟨e121, e122⟩⟩ := torusExp_leadRoot θ
  have key := rootChar_ne_one_of_mem (K := K) (a := a) hθd hθ hg 2
  fin_cases n
  · simp at hn
  · exact key .i1 (3 * θ - 2) (by rw [e11, e12]; ring) (by simp)
  · exact key .i2 (1 - θ) (by rw [e21, e22]; ring) (by simp)
  · exact key .i4 (3 * θ - 2) (by rw [e41, e42]; ring) (by simp)
  · exact key .i8 (1 - θ) (by rw [e81, e82]; ring) (by simp)
  · exact key .i6 (1 - θ) (by rw [e61, e62]; ring) (by simp)
  · exact key .i11 θ (by rw [e111, e112]; ring) (by simp)
  · exact key .i5 (1 - θ) (by rw [e51, e52]; ring) (by simp)
  · exact key .i12 θ (by rw [e121, e122]; ring) (by simp)
  · exact key .i7 (2 * θ - 1) (by rw [e71, e72]; ring) (by simp)
  · exact key .i9 (2 * θ - 1) (by rw [e91, e92]; ring) (by simp)
  · exact key .i10 (2 - 2 * θ) (by rw [e101, e102]; ring) (by simp)

theorem torus_fixfree_rootV (hK : Nat.card K = 2 ^ (2 * a + 1)) (t : Kˣ × Kˣ)
    {Z : Finset (Fin 12)} (i : Idx) (hZ : ∀ n ∈ i.coords, n ∉ Z)
    (hχ : ∀ n, n ∉ Z → rootChar K a (Idx.ofCoord n) t ≠ 1) :
    ∀ x ∈ rootV K a i, torusPair a t * x * (torusPair a t)⁻¹ = x → x = 1 := by
  refine torus_fixfree_of_chars hK t (Z := Finset.univ \ i.coords) ?_ fun n hn => hχ n
    (hZ n (by simpa using hn))
  rw [coe_rootV hK]
  congr 1
  ext x
  simp

theorem exists_chars_radR (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∃ t : Kˣ × Kˣ, ∀ n, n ∉ ({1, 2} : Finset (Fin 12)) →
      rootChar K a (Idx.ofCoord n) t ≠ 1 := by
  obtain ⟨g, hg⟩ := exists_unit_orderOf (K := K) (a := a) hK
  exact ⟨(g, g ^ (3 : ℤ)), fun n hn => chars_ne_one_radR ha hg n hn⟩

theorem exists_chars_radS (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∃ t : Kˣ × Kˣ, ∀ n, n ∉ ({0} : Finset (Fin 12)) →
      rootChar K a (Idx.ofCoord n) t ≠ 1 := by
  obtain ⟨g, hg⟩ := exists_unit_orderOf (K := K) (a := a) hK
  exact ⟨(g, g ^ (2 : ℤ)), fun n hn => chars_ne_one_radS ha hg n hn⟩

end CFSG.Quasithin.H13.F431.TwoF4
