module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section2.Basic
import all CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section2.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.ClassSumFormula
-- `import all`: `classSumPairCountMul`'s body is not `@[expose]`d, so at the
-- default `.exported` import level of a `module` file it is loaded as an axiom
-- (bodies of non-exposed definitions are stripped); the pair-count lemmas need
-- the definitional body (`Nat.card {p : ci.carrier × cj.carrier // ...}`), so
-- this module is additionally imported with its private information (bodies).
import all CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.ClassSumFormula
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.ClassFunction
import all CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Defs

namespace CFSG
end CFSG
open CFSG

/-!
# Bender--Glauberman: Lemma 2.2

The class-sum expansions and the V/W forms used in the proof of Lemma 2.2,
together with the lemma statement (blocked on the dihedral-Sylow-2
structure of `H = C_G(t)`).
-/

noncomputable section

open scoped BigOperators
open scoped commutatorElement
open scoped Pointwise

namespace CFSG.BenderGlauberman

open GorensteinWalter
open Theory.Character

-- Local instances matching `Theory.Character`'s subgroup-sum convention; see
-- `BenderGlauberman/ClassFunction.lean`.
attribute [local instance] Fintype.ofFinite
attribute [local instance] Classical.propDecidable

universe u

section Section2

variable {G : Type u} [Group G] [Fintype G]
variable (c : Hyp11 G)

/-! ## Lemma 2.2 infrastructure: the class-sum expansions and the V/W forms

The bridge over `BenderGlauberman.Irr G` (a complete irreducible-character
family), the Fourier expansions of the pair counts `f` (on `G`) and `f_ij`
(on `H`), the paper's `V = |H|(f,δ*)_G` and `W = |H|(Σ f_ij,δ)_H` identities,
and the support facts for `δ = μ^H − ν^H`.  The `V = W` step and the three
case values are blocked on the dihedral-Sylow-2 structure of `H = C_G(t)`;
the two structure inputs `H0_index` (`|H : H0| = 2`) and `t1H_disjoint`
(`t1^H ∩ t2^H = ∅`) are now PROVED in `BenderGlauberman/Section2/Basic.lean`
(from the `H_eq_US` component of `Hyp11`; public, see
`node_graph/bg_section2/lemma_2_2.md`).
-/

/-- The family of irreducible characters of `G` as conj-class functions (the
bridge over `Irr G` for `ClassSumFormula`). -/
private noncomputable def irrFamily (G : Type u) [Group G] [Finite G] :
    Irr G → ConjClassFunction G :=
  fun χ => toConjClassFunction χ.1 (irreducibleCharacter_isClassFunction χ.2)

/-- An irreducible character of `G` is an irreducible conj-class character. -/
private theorem isConjCharacter_of_isIrreducibleCharacter {G : Type u} [Group G] [Finite G]
    {φ : ClassFunction G} (hφ : IsIrreducibleCharacter φ) :
    IsConjCharacter (toConjClassFunction φ (irreducibleCharacter_isClassFunction hφ)) := by
  classical
  rcases hφ with ⟨n, ρ, hρ, hφeq⟩
  refine ⟨n, ρ, ?_⟩
  cases hφeq
  exact toConjClassFunction_eq_of_apply (phi := ρ.character)
    (hphi := irreducibleCharacter_isClassFunction (φ := ρ.character) ⟨n, ρ, hρ, rfl⟩)
    (Phi := characterClassFunction ρ) (by intro g; rfl)

/-- `irrFamily G` is a complete family of irreducible characters of `G`. -/
private theorem irrFamily_isComplete (G : Type u) [Group G] [Finite G] :
    IsCompleteIrreducibleCharacterFamily (irrFamily (G := G)) := by
  classical
  refine ⟨?hirr, ?hsurj, ?hinj⟩
  · intro χ
    constructor
    · exact isConjCharacter_of_isIrreducibleCharacter χ.2
    · change classFunctionInner
        (toConjClassFunction χ.1 (irreducibleCharacter_isClassFunction χ.2))
        (toConjClassFunction χ.1 (irreducibleCharacter_isClassFunction χ.2)) = 1
      rw [classFunctionInner_toConjClassFunction]
      exact irreducible_scalarProduct_self χ.2
  · intro χ₀ hχ₀
    rcases hχ₀.1 with ⟨n, ρ, hρ⟩
    have : Representation.IsIrreducible ρ := by
      apply (irreducible_iff_character_norm_one (ρ := ρ)).2
      simpa [hρ] using hχ₀.2
    have hirr : IsIrreducibleCharacter (ofConjClassFunction χ₀) := by
      refine ⟨n, ρ, inferInstance, ?_⟩
      rw [hρ]
      exact ofConjClassFunction_characterClassFunction (G := G) (V := Fin n → ℂ) (rho := ρ)
    refine ⟨⟨ofConjClassFunction χ₀, hirr⟩, ?_⟩
    unfold irrFamily
    exact toConjClassFunction_eq_of_apply (phi := ofConjClassFunction χ₀)
      (hphi := irreducibleCharacter_isClassFunction hirr) (Phi := χ₀) (by intro g; rfl)
  · intro χ ν hEq
    apply Subtype.ext
    ext x
    have hx := congrFun hEq (ConjClasses.mk x)
    simpa [irrFamily, toConjClassFunction_apply] using hx

/-- `U ∩ S = 1`: the odd core of `H` meets the Sylow 2-subgroup trivially. -/
private lemma U_inter_S_eq_bot (c : Hyp11 G) {x : G} (hxU : x ∈ c.U)
    (hxS : x ∈ (c.S : Subgroup G)) : x = 1 := by
  classical
  have hcop : Nat.Coprime 2 (Nat.card ↥c.U) := by
    have h1 : Nat.card ↥c.U = Nat.card (pPrimeCore 2 c.H) := by
      dsimp [Hyp11.U]
      rw [oddCoreOf]
      exact Subgroup.card_map_of_injective (f := c.H.subtype)
        (K := pPrimeCore 2 c.H) (Subgroup.subtype_injective c.H)
    rw [h1]
    exact pPrimeCore_coprime_card (p := 2) (G := c.H)
  by_contra hx1
  have hordU : orderOf x ∣ Nat.card ↥c.U := by
    change orderOf (c.U.subtype (⟨x, hxU⟩ : ↥c.U)) ∣ Nat.card ↥c.U
    rw [orderOf_injective c.U.subtype (Subgroup.subtype_injective c.U) (⟨x, hxU⟩ : ↥c.U)]
    have hxU' : orderOf (⟨x, hxU⟩ : ↥c.U) ∣ Fintype.card ↥c.U :=
      orderOf_dvd_card (G := ↥c.U) (x := ⟨x, hxU⟩)
    rwa [← Nat.card_eq_fintype_card] at hxU'
  have hordS : orderOf x ∣ Nat.card (c.S : Subgroup G) := by
    change orderOf ((c.S : Subgroup G).subtype (⟨x, hxS⟩ : ↥(c.S : Subgroup G))) ∣
      Nat.card (c.S : Subgroup G)
    rw [orderOf_injective (c.S : Subgroup G).subtype
      (Subgroup.subtype_injective (c.S : Subgroup G)) (⟨x, hxS⟩ : ↥(c.S : Subgroup G))]
    have hxS' : orderOf (⟨x, hxS⟩ : ↥(c.S : Subgroup G)) ∣
        Fintype.card ↥(c.S : Subgroup G) :=
      orderOf_dvd_card (G := ↥(c.S : Subgroup G)) (x := ⟨x, hxS⟩)
    rwa [← Nat.card_eq_fintype_card] at hxS'
  have hpow : orderOf x ∣ 2 ^ (c.m + 1) := by
    have hpow' : orderOf x ∣ 2 * 2 ^ c.m := by
      rw [← S_nat_card c]
      exact hordS
    rwa [show 2 * 2 ^ c.m = 2 ^ (c.m + 1) by ring] at hpow'
  have hcop' : Nat.Coprime (2 ^ (c.m + 1)) (Nat.card ↥c.U) := by
    exact hcop.pow_left _
  have h1' : orderOf x = 1 := by
    have hdvd : orderOf x ∣ 1 := by
      rw [← hcop'.gcd_eq_one]
      exact Nat.dvd_gcd hpow hordU
    exact Nat.dvd_one.mp hdvd
  exact hx1 (orderOf_eq_one_iff.mp h1')

/-- An element of `S` lies in `H0` iff it lies in `S0`. -/
private lemma S_mem_H0_iff_S0 (c : Hyp11 G) (h12 : Hyp12 c)
    {x : G} (hx : x ∈ (c.S : Subgroup G)) : x ∈ c.H0 ↔ x ∈ (c.S0 : Subgroup G) := by
  constructor
  · intro hxH0
    rcases H0_eq_U_mul_S0 c h12 (x := ⟨x, hxH0⟩) with ⟨u, r, hxEq⟩
    have hxEq' : x = (u : G) * (r : G) := by
      simpa using hxEq
    have hxr : x * (r : G)⁻¹ = (u : G) := by
      calc
        x * (r : G)⁻¹ = ((u : G) * (r : G)) * (r : G)⁻¹ := by rw [hxEq']
        _ = (u : G) := by group
    have hxrS : x * (r : G)⁻¹ ∈ (c.S : Subgroup G) :=
      (c.S : Subgroup G).mul_mem hx ((c.S : Subgroup G).inv_mem (c.S0_le_S r.2))
    have hxrU : x * (r : G)⁻¹ ∈ c.U := by
      rw [hxr]
      exact u.2
    have hxr1 : x * (r : G)⁻¹ = 1 := U_inter_S_eq_bot c hxrU hxrS
    have hxr' : x = (r : G) := by
      calc
        x = (x * (r : G)⁻¹) * (r : G) := by group
        _ = 1 * (r : G) := by rw [hxr1]
        _ = (r : G) := by simp
    rw [hxr']
    exact r.2
  · intro hxS0
    exact S0_le_H0 c hxS0

/-- `t1 ∉ H0`. -/
private lemma t1_not_mem_H0 (c : Hyp11 G) (h12 : Hyp12 c) : c.t1 ∉ c.H0 := by
  intro h1
  exact c.t1_not_mem_S0 ((S_mem_H0_iff_S0 c h12 c.t1_mem_S).mp h1)

/-- `t2 ∉ H0`. -/
private lemma t2_not_mem_H0 (c : Hyp11 G) (h12 : Hyp12 c) : c.t2 ∉ c.H0 := by
  intro h1
  exact c.t2_not_mem_S0 ((S_mem_H0_iff_S0 c h12 c.t2_mem_S).mp h1)

/-- `s ∉ H0`. -/
private lemma s_not_mem_H0 (c : Hyp11 G) (h12 : Hyp12 c) : c.s ∉ c.H0 := by
  intro h1
  exact c.s_not_mem_S0 ((S_mem_H0_iff_S0 c h12 c.s_mem_S).mp h1)

/-- `U ⊴ H`: conjugation by any element of `H` preserves `U = O(H)`. -/
public lemma U_normal_in_H (c : Hyp11 G) {h u : G} (hh : h ∈ c.H) (hu : u ∈ c.U) :
    h * u * h⁻¹ ∈ c.U := by
  have huU : u ∈ (pPrimeCore 2 c.H).map c.H.subtype := by
    simpa [Hyp11.U, oddCoreOf] using hu
  have huH : u ∈ c.H :=
    SetLike.le_def.1 (Subgroup.map_subtype_le (H := c.H) (pPrimeCore 2 c.H)) huU
  have hchar : (pPrimeCore 2 c.H).Characteristic :=
    pPrimeCore_characteristic (p := 2) (G := c.H)
  have hcomap : (pPrimeCore 2 c.H) ≤ (pPrimeCore 2 c.H).comap
      (MulAut.conj ⟨h, hh⟩).toMonoidHom :=
    (Subgroup.characteristic_iff_le_comap.mp hchar) (MulAut.conj ⟨h, hh⟩)
  have huK : (⟨u, huH⟩ : ↥c.H) ∈ pPrimeCore 2 c.H := by
    rcases (Subgroup.mem_map.mp huU) with ⟨x, hx, hxeq⟩
    have hxeq' : (⟨u, huH⟩ : ↥c.H) = x := by
      ext
      simpa using hxeq.symm
    simpa [hxeq'] using hx
  have hconj : (MulAut.conj ⟨h, hh⟩) ⟨u, huH⟩ ∈ pPrimeCore 2 c.H :=
    Subgroup.mem_comap.mp (hcomap huK)
  refine (Subgroup.mem_map.mpr ?_)
  refine ⟨⟨h * u * h⁻¹, c.H.mul_mem (c.H.mul_mem hh huH) (c.H.inv_mem hh)⟩, ?_, rfl⟩
  have hcx : (MulAut.conj ⟨h, hh⟩) ⟨u, huH⟩ =
      (⟨h * u * h⁻¹, c.H.mul_mem (c.H.mul_mem hh huH) (c.H.inv_mem hh)⟩ : ↥c.H) := by
    ext
    simp [MulAut.conj_apply, mul_assoc]
  rw [← hcx]
  exact hconj


/-- `U ≤ H`: the odd core of `H` lies in `H`. -/
private lemma U_le_H (c : Hyp11 G) : (c.U : Subgroup G) ≤ c.H := by
  intro u hu
  have huU : u ∈ (pPrimeCore 2 c.H).map c.H.subtype := by
    simpa [Hyp11.U, oddCoreOf] using hu
  exact SetLike.le_def.1 (Subgroup.map_subtype_le (H := c.H) (pPrimeCore 2 c.H)) huU

/-! ## Local structure facts (private infrastructure mirrored from
`Section2/Basic.lean`, where the same lemmas are private to that file) -/

/-- Every element of `S` normalizes `U = O(H)`. -/
private lemma S_le_normalizer_U (c : Hyp11 G) :
    (c.S : Subgroup G) ≤ Subgroup.normalizer (c.U : Set G) := by
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · intro hu
    exact U_normal_in_H c (S_le_H c hs) hu
  · intro hsu
    have hs' : s⁻¹ ∈ c.H := c.H.inv_mem (S_le_H c hs)
    have h1 := U_normal_in_H c hs' hsu
    have h2 : s⁻¹ * (s * u * s⁻¹) * (s⁻¹)⁻¹ = u := by group
    rwa [h2] at h1

/-- Every element of `S0` normalizes `U`. -/
private lemma S0_le_normalizer_U (c : Hyp11 G) (h12 : Hyp12 c) :
    (c.S0 : Subgroup G) ≤ Subgroup.normalizer (c.U : Set G) := by
  intro r hr
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · intro hu
    exact (h12.U_normal_in_H0).2 r (S0_le_H0 c hr) u hu
  · intro hru
    have hr' : r⁻¹ ∈ c.H0 := c.H0.inv_mem (S0_le_H0 c hr)
    have h1 : r⁻¹ * (r * u * r⁻¹) * r⁻¹⁻¹ ∈ c.U :=
      (h12.U_normal_in_H0).2 (r⁻¹) hr' (r * u * r⁻¹) hru
    have h1' : r⁻¹ * (r * u * r⁻¹) * r ∈ c.U := by simpa using h1
    have h2 : r⁻¹ * (r * u * r⁻¹) * r = u := by group
    rwa [h2] at h1'

/-- `H = U·S` as set products (from `H_eq_US`). -/
private lemma H_set_eq_U_mul_S (c : Hyp11 G) :
    (↑c.H : Set G) = (c.U : Set G) * (↑(c.S : Subgroup G) : Set G) := by
  rw [← c.H_eq_US]
  exact Subgroup.coe_mul_of_right_le_normalizer_left c.U (c.S : Subgroup G)
    (S_le_normalizer_U c)

/-- `H0 = U·S0` as set products. -/
private lemma H0_set_eq_U_mul_S0 (c : Hyp11 G) (h12 : Hyp12 c) :
    (↑c.H0 : Set G) = (c.U : Set G) * ((c.S0 : Subgroup G) : Set G) := by
  dsimp [Hyp11.H0]
  exact Subgroup.coe_mul_of_right_le_normalizer_left c.U (c.S0 : Subgroup G)
    (S0_le_normalizer_U c h12)

/-- `|U|` is coprime to `2`. -/
private lemma U_card_coprime_two (c : Hyp11 G) : Nat.Coprime 2 (Nat.card ↥c.U) := by
  have h1 : Nat.card ↥c.U = Nat.card (pPrimeCore 2 c.H) := by
    dsimp [Hyp11.U]
    rw [oddCoreOf]
    exact Subgroup.card_map_of_injective (f := c.H.subtype)
      (K := pPrimeCore 2 c.H) (Subgroup.subtype_injective c.H)
  rw [h1]
  exact pPrimeCore_coprime_card (p := 2) (G := c.H)

/-- Every element of `U = O(H)` has a square root in `U` (`|U|` is odd); if
`s ∈ H` inverts `u`, then it inverts the square root too. -/
private lemma U_sq_exists (c : Hyp11 G) {u : G} (hu : u ∈ c.U) :
    ∃ v : G, v ∈ c.U ∧ v * v = u ∧
      ∀ s : G, s ∈ c.H → s * u * s⁻¹ = u⁻¹ → s * v * s⁻¹ = v⁻¹ := by
  classical
  let k := orderOf u
  have hk : k ∣ Nat.card ↥c.U := by
    dsimp [k]
    change orderOf (c.U.subtype (⟨u, hu⟩ : ↥c.U)) ∣ Nat.card ↥c.U
    rw [orderOf_injective c.U.subtype (Subgroup.subtype_injective c.U) (⟨u, hu⟩ : ↥c.U)]
    have h' : orderOf (⟨u, hu⟩ : ↥c.U) ∣ Fintype.card ↥c.U :=
      orderOf_dvd_card (G := ↥c.U) (x := ⟨u, hu⟩)
    rwa [← Nat.card_eq_fintype_card] at h'
  have hkodd : k % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one k with h | h
    · exfalso
      have h2 : 2 ∣ k := Nat.dvd_iff_mod_eq_zero.mpr h
      have h2n : 2 ∣ Nat.card ↥c.U := dvd_trans h2 hk
      have hg : 2 ∣ Nat.gcd 2 (Nat.card ↥c.U) := Nat.dvd_gcd (dvd_refl 2) h2n
      rw [(U_card_coprime_two c).gcd_eq_one] at hg
      exact (by norm_num : (2 : ℕ) ≠ 1) (Nat.dvd_one.mp hg)
    · exact h
  rcases (Nat.odd_iff.mpr hkodd) with ⟨m, hm⟩
  refine ⟨u ^ (m + 1), c.U.pow_mem hu (m + 1), ?_, ?_⟩
  · calc
      (u ^ (m + 1)) * (u ^ (m + 1)) = u ^ ((m + 1) + (m + 1)) := by rw [← pow_add]
      _ = u ^ (2 * (m + 1)) := by
        rw [show (m + 1) + (m + 1) = 2 * (m + 1) by omega]
      _ = u ^ (k + 1) := by
        rw [show 2 * (m + 1) = k + 1 by rw [hm]; omega]
      _ = u := by
        have hk : u ^ k = 1 := by
          dsimp [k]
          exact pow_orderOf_eq_one u
        calc
          u ^ (k + 1) = u * u ^ k := by rw [pow_succ']
          _ = u := by
            rw [hk]
            simp
  · intro s hs hsinv
    have hpow : ∀ n : ℕ, (s * u * s⁻¹) ^ n = s * u ^ n * s⁻¹ := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          calc
            (s * u * s⁻¹) ^ (n + 1) = (s * u * s⁻¹) ^ n * (s * u * s⁻¹) := by rw [pow_succ]
            _ = (s * u ^ n * s⁻¹) * (s * u * s⁻¹) := by rw [ih]
            _ = s * (u ^ n * u) * s⁻¹ := by group
            _ = s * u ^ (n + 1) * s⁻¹ := by rw [← pow_succ]
    calc
      s * (u ^ (m + 1)) * s⁻¹ = (s * u * s⁻¹) ^ (m + 1) := (hpow (m + 1)).symm
      _ = (u⁻¹) ^ (m + 1) := by rw [hsinv]
      _ = (u ^ (m + 1))⁻¹ := by rw [inv_pow]

/-- `t1, t2` as elements of `H`. -/
private noncomputable def lemma_2_2_tH (c : Hyp11 G) : Fin 2 → ↥c.H :=
  fun i => ⟨if (i : ℕ) = 0 then c.t1 else c.t2, by
    by_cases h : (i : ℕ) = 0
    · simpa [h] using t1_mem_H c
    · have hi1 : (i : ℕ) = 1 := by omega
      simpa [hi1] using t2_mem_H c⟩

/-- The type of elements of `S0` viewed inside `S` is equivalent to `S0` itself. -/
private def S0_subgroupOf_equiv (c : Hyp11 G) :
    ↥((c.S0 : Subgroup G).subgroupOf (c.S : Subgroup G)) ≃ ↥(c.S0 : Subgroup G) where
  toFun x := ⟨(x.1 : G), (Subgroup.mem_subgroupOf.mp x.2)⟩
  invFun y := ⟨⟨(y : G), c.S0_le_S y.2⟩, Subgroup.mem_subgroupOf.mpr y.2⟩
  left_inv x := by
    ext
    rfl
  right_inv y := by
    ext
    rfl

/-- Conjugation by any element of `S` fixes the unique involution `t` of `S0`. -/
private lemma S_conj_t' (c : Hyp11 G) {g : G} (hg : g ∈ (c.S : Subgroup G)) :
    g * c.t * g⁻¹ = c.t := by
  have hmem : g * c.t * g⁻¹ ∈ (c.S0 : Subgroup G) := S_conj_mem_S0 c hg c.t_mem_S0
  have hsq : (g * c.t * g⁻¹) ^ 2 = 1 := by
    calc
      (g * c.t * g⁻¹) ^ 2 = (g * c.t * g⁻¹) * (g * c.t * g⁻¹) := by rw [pow_two]
      _ = g * (c.t * c.t) * g⁻¹ := by group
      _ = g * 1 * g⁻¹ := by
        rw [show c.t * c.t = 1 by simpa [pow_two] using c.t_involution.2]
      _ = 1 := by group
  have hne : g * c.t * g⁻¹ ≠ 1 := by
    intro h
    have ht1 : c.t = 1 := by
      calc
        c.t = g⁻¹ * (g * c.t * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    exact c.t_involution.1 ht1
  have hsq' : (⟨g * c.t * g⁻¹, hmem⟩ : ↥(c.S0 : Subgroup G)) ^ 2 = 1 := by
    apply Subtype.ext
    simpa [Subgroup.coe_pow] using hsq
  rcases (S0_sq_eq_one_iff c (x := ⟨g * c.t * g⁻¹, hmem⟩)).1 hsq' with h1 | ht
  · exfalso
    exact hne (by simpa using (Subtype.ext_iff.mp h1))
  · exact Subtype.ext_iff.mp ht


/-! ## The dihedral model `S ≅ D_{2^m}` (mirrored from `Section2/Basic.lean`) -/

open DihedralGroup

/-- In the dihedral model `D_n` (`n = 2^m`), any element outside the rotation
subgroup `⟨r 1⟩` inverts every rotation. -/
private lemma dihedral_conj_rotate_inv (n : ℕ) [NeZero n] {w x : DihedralGroup n}
    (hw : w ∉ Subgroup.zpowers (r 1 : DihedralGroup n))
    (hx : x ∈ Subgroup.zpowers (r 1 : DihedralGroup n)) :
    w * x * w⁻¹ = x⁻¹ := by
  rcases x with ⟨b⟩ | ⟨b⟩
  · -- x = r b
    rcases w with ⟨i⟩ | ⟨i⟩
    · -- w = r i ∈ ⟨r 1⟩: contradiction
      exfalso
      exact hw (by
        refine (Subgroup.mem_zpowers_iff).2 ?_
        refine ⟨(i.val : ℤ), ?_⟩
        rw [r_one_zpow]
        congr 1
        simp)
    · -- w = sr i inverts r b
      rw [sr_mul_r, inv_sr, sr_mul_sr, inv_r]
      congr 1
      abel
  · -- x = sr b ∉ ⟨r 1⟩: contradiction
    have hnot : sr b ∉ Subgroup.zpowers (r 1 : DihedralGroup n) := by
      intro h
      rcases (Subgroup.mem_zpowers_iff.mp h) with ⟨k, hk⟩
      rw [r_one_zpow] at hk
      cases hk
    exfalso
    exact hnot hx

/-- For `m ≥ 2`, the image of `S0` in the dihedral model is the rotation
subgroup `⟨r 1⟩`. -/
private lemma eS0_eq_zpowers_r1 (c : Hyp11 G) (hm2 : 2 ≤ c.m)
    (e : ↥(c.S : Subgroup G) ≃* DihedralGroup (2 ^ c.m)) :
    (⊤ : Subgroup ↥(c.S0 : Subgroup G)).map
        (e.toMonoidHom.comp (Subgroup.inclusion c.S0_le_S)) =
      Subgroup.zpowers (r 1 : DihedralGroup (2 ^ c.m)) := by
  have : NeZero (2 ^ c.m) := ⟨pow_ne_zero c.m (by norm_num)⟩
  let : IsCyclic ↥(c.S0 : Subgroup G) := c.S0_cyclic
  rcases IsCyclic.exists_generator (α := ↥(c.S0 : Subgroup G)) with ⟨g, hg⟩
  have hgorder : orderOf g = 2 ^ c.m := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, S0_nat_card c]
  have hgorder4 : 4 ≤ orderOf g := by
    rw [hgorder]
    exact Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hm2
  have hegr : ∃ a : ZMod (2 ^ c.m), e (Subgroup.inclusion c.S0_le_S g) = r a := by
    rcases h : e (Subgroup.inclusion c.S0_le_S g) with ⟨a⟩ | ⟨a⟩
    · exact ⟨a, rfl⟩
    · exfalso
      have hord : orderOf (e (Subgroup.inclusion c.S0_le_S g)) = 2 ^ c.m := by
        rw [MulEquiv.orderOf_eq e]
        rw [orderOf_injective (Subgroup.inclusion c.S0_le_S)
          (Subgroup.inclusion_injective c.S0_le_S) g]
        exact hgorder
      have h2 : (2 : ℕ) = 2 ^ c.m := by
        calc
          2 = orderOf (sr a : DihedralGroup (2 ^ c.m)) := by rw [orderOf_sr]
          _ = orderOf (e (Subgroup.inclusion c.S0_le_S g)) := by rw [h]
          _ = 2 ^ c.m := hord
      omega
  have hsub : (⊤ : Subgroup ↥(c.S0 : Subgroup G)).map
      (e.toMonoidHom.comp (Subgroup.inclusion c.S0_le_S)) ≤
      Subgroup.zpowers (r 1 : DihedralGroup (2 ^ c.m)) := by
    intro y hy
    rcases (Subgroup.mem_map.mp hy) with ⟨x, hx, rfl⟩
    rcases (Subgroup.mem_zpowers_iff.mp (hg x)) with ⟨k, hk⟩
    rcases hegr with ⟨a, hega⟩
    have hcast : (((a * (k : ZMod (2 ^ c.m))).val : ℤ) : ZMod (2 ^ c.m)) =
        a * (k : ZMod (2 ^ c.m)) := by
      rw [Int.cast_natCast]
      exact ZMod.natCast_zmod_val (a * (k : ZMod (2 ^ c.m)))
    refine (Subgroup.mem_zpowers_iff).2 ?_
    refine ⟨((a * (k : ZMod (2 ^ c.m))).val : ℤ), ?_⟩
    rw [r_one_zpow]
    rw [hcast]
    rw [← r_zpow]
    rw [← hega]
    have hmp : e ((Subgroup.inclusion c.S0_le_S g) ^ k) =
        (e (Subgroup.inclusion c.S0_le_S g)) ^ k := by
      simp
    rw [← hmp]
    rw [← (Subgroup.inclusion c.S0_le_S).map_zpow]
    rw [hk]
    simp [MulEquiv.toMonoidHom_eq_coe]
  apply le_antisymm
  · exact hsub
  · -- |⟨r 1⟩| = 2^m ≤ 2^m = |K₀|
    have hcard : Nat.card (Subgroup.zpowers (r 1 : DihedralGroup (2 ^ c.m))) ≤
        Nat.card ((⊤ : Subgroup ↥(c.S0 : Subgroup G)).map
          (e.toMonoidHom.comp (Subgroup.inclusion c.S0_le_S))) := by
      rw [Nat.card_zpowers, orderOf_r_one]
      rw [Subgroup.card_map_of_injective (f := e.toMonoidHom.comp (Subgroup.inclusion c.S0_le_S))
        (by
          intro a b hab
          exact (Subgroup.inclusion_injective c.S0_le_S) (e.injective (by simpa using hab)))]
      rw [Subgroup.card_top, S0_nat_card c]
    exact (Subgroup.eq_of_le_of_card_ge hsub hcard).ge

/-- `s` inverts every element of `S0` (dihedral structure of `S`). -/
public lemma s_inverts_S0 (c : Hyp11 G) {x : G} (hx : x ∈ (c.S0 : Subgroup G)) :
    c.s * x * c.s⁻¹ = x⁻¹ := by
  by_cases hm1 : c.m = 1
  · -- m = 1: |S0| = 2, so x = 1 or x = t
    have hcard : Fintype.card ↥(c.S0 : Subgroup G) = 2 := by
      rw [← Nat.card_eq_fintype_card, S0_nat_card c, hm1]
      norm_num
    have hpow : (⟨x, hx⟩ : ↥(c.S0 : Subgroup G)) ^ 2 = 1 := by
      have h := pow_card_eq_one (G := ↥(c.S0 : Subgroup G)) (x := ⟨x, hx⟩)
      simpa [hcard] using h
    rcases (S0_sq_eq_one_iff c (x := ⟨x, hx⟩)).1 hpow with h1 | ht
    · have hx1 : x = 1 := by simpa using (Subtype.ext_iff.mp h1)
      simp [hx1]
    · have hxt : x = c.t := by simpa using (Subtype.ext_iff.mp ht)
      rw [hxt]
      rw [S_conj_t' c c.s_mem_S]
      have ht2 : c.t * c.t = 1 := by simpa [pow_two] using c.t_involution.2
      rw [inv_eq_of_mul_eq_one_left ht2]
  · -- m ≥ 2: transport through the dihedral model
    have hm2 : 2 ≤ c.m := by
      exact Nat.succ_le_of_lt (lt_of_le_of_ne c.one_le_m (Ne.symm hm1))
    let e : ↥(c.S : Subgroup G) ≃* DihedralGroup (2 ^ c.m) := Classical.choice c.dihedralEquiv
    have heq : (⊤ : Subgroup ↥(c.S0 : Subgroup G)).map
        (e.toMonoidHom.comp (Subgroup.inclusion c.S0_le_S)) =
        Subgroup.zpowers (r 1 : DihedralGroup (2 ^ c.m)) :=
      eS0_eq_zpowers_r1 c hm2 e
    let xS : ↥(c.S : Subgroup G) := ⟨x, c.S0_le_S hx⟩
    let sS : ↥(c.S : Subgroup G) := ⟨c.s, c.s_mem_S⟩
    have hxS : e xS ∈ Subgroup.zpowers (r 1 : DihedralGroup (2 ^ c.m)) := by
      rw [← heq]
      refine (Subgroup.mem_map).2 ?_
      refine ⟨⟨x, hx⟩, by simp, ?_⟩
      rfl
    have hsS : e sS ∉ Subgroup.zpowers (r 1 : DihedralGroup (2 ^ c.m)) := by
      intro h
      rw [← heq] at h
      rcases (Subgroup.mem_map.mp h) with ⟨y, hy, hyeq⟩
      have hys : (e.toMonoidHom.comp (Subgroup.inclusion c.S0_le_S)) y = e sS := hyeq
      have hι : Subgroup.inclusion c.S0_le_S y = sS := e.injective hys
      have hyG : (y : G) = c.s := by
        exact (congrArg (fun z : ↥(c.S : Subgroup G) => (z : G)) hι)
      apply c.s_not_mem_S0
      rw [← hyG]
      exact y.2
    have hmain : e (sS * xS * sS⁻¹) = e (xS⁻¹) := by
      have hM := dihedral_conj_rotate_inv (n := 2 ^ c.m) (w := e sS) hsS hxS
      calc
        e (sS * xS * sS⁻¹) = e sS * e xS * (e sS)⁻¹ := by simp [map_mul, map_inv]
        _ = (e xS)⁻¹ := hM
        _ = e (xS⁻¹) := by simp [map_inv]
    have hS : sS * xS * sS⁻¹ = xS⁻¹ := e.injective hmain
    simpa [Subgroup.coe_mul, Subgroup.coe_inv] using
      (congrArg (fun z : ↥(c.S : Subgroup G) => (z : G)) hS)

/-- The parity contradiction: `r 1 ∈ ⟨r (b − a)⟩ ≤ ⟨r 2⟩` forces
`n = orderOf (r 1) ∣ orderOf (r 2) ≤ n/2 < n`. -/
private lemma dihedral_sr_not_conj_of_rotation_sq (n : ℕ) [NeZero n] (hn2 : 2 ∣ n)
    {a b : ZMod n}
    (hgen : (r 1 : DihedralGroup n) ∈ Subgroup.zpowers (r (b - a) : DihedralGroup n))
    (hmem : (r (b - a) : DihedralGroup n) ∈ Subgroup.zpowers (r 2 : DihedralGroup n)) :
    False := by
  have hdvd1 : orderOf (r 1 : DihedralGroup n) ∣ orderOf (r (b - a) : DihedralGroup n) :=
    orderOf_dvd_of_mem_zpowers hgen
  have hdvd2 : orderOf (r (b - a) : DihedralGroup n) ∣ orderOf (r 2 : DihedralGroup n) :=
    orderOf_dvd_of_mem_zpowers hmem
  have hle1 : n ≤ orderOf (r (b - a) : DihedralGroup n) :=
    orderOf_r_one.symm.trans_le (Nat.le_of_dvd (orderOf_pos _) hdvd1)
  have hord2 : orderOf (r 2 : DihedralGroup n) ≤ n / 2 := by
    have hpow : (r 2 : DihedralGroup n) ^ (n / 2) = 1 := by
      rw [r_pow]
      have h2 : 2 * (n / 2) = n := Nat.mul_div_cancel' hn2
      have h3 : (2 : ZMod n) * ((n / 2 : ℕ) : ZMod n) = 0 := by
        norm_cast
        rw [h2]
        exact ZMod.natCast_self n
      rw [h3]
      rfl
    have h2le : 2 ≤ n := by
      have hn0 : 0 < n := NeZero.pos n
      omega
    have hdiv : 0 < n / 2 := by
      omega
    exact Nat.le_of_dvd hdiv (orderOf_dvd_of_pow_eq_one hpow)
  have hle2 : orderOf (r (b - a) : DihedralGroup n) ≤ orderOf (r 2 : DihedralGroup n) :=
    Nat.le_of_dvd (orderOf_pos _) hdvd2
  have hle : n ≤ n / 2 := le_trans hle1 (le_trans hle2 hord2)
  exact (Nat.not_lt_of_ge hle) (Nat.div_lt_self (NeZero.pos n) (by norm_num))

/-- Conjugation by the rotation `r c` sends the reflection `sr a` to `sr (a − 2c)`. -/
private lemma conj_r_sr (n : ℕ) [NeZero n] (a c : ZMod n) :
    (r c : DihedralGroup n) * (sr a : DihedralGroup n) * (r c)⁻¹ = sr (a - 2 * c) := by
  rw [inv_r, r_mul_sr, sr_mul_r]
  congr 1
  ring

/-- In the dihedral model, if `r (b − a)` generates the rotation subgroup
`⟨r 1⟩` (i.e. `S0 = ⟨t1·t2⟩` maps to it), then the reflections `sr a` and
`sr b` are not conjugate: conjugation by a rotation sends `sr a` to
`sr (a − 2c)` and by a reflection to `sr (2c − a)`, so `b − a = 2·d` lands in
`⟨r 2⟩`, whose elements have order dividing `n/2 < n`. -/
private lemma dihedral_sr_not_conj (n : ℕ) [NeZero n] (hn2 : 2 ∣ n) {a b : ZMod n}
    (hgen : (r 1 : DihedralGroup n) ∈ Subgroup.zpowers (r (b - a) : DihedralGroup n))
    (hconj : ∃ w : DihedralGroup n, w * (sr a : DihedralGroup n) * w⁻¹ = sr b) :
    False := by
  rcases hconj with ⟨w, hw⟩
  rcases w with ⟨c⟩ | ⟨c⟩
  · -- w = r c: sr b = sr (a - 2c)
    have hmem : (r (b - a) : DihedralGroup n) ∈ Subgroup.zpowers (r 2 : DihedralGroup n) := by
      have hb : b = a - 2 * c := by
        have h' : (sr b : DihedralGroup n) = sr (a - 2 * c) := by
          calc
            (sr b : DihedralGroup n) = (r c : DihedralGroup n) * sr a * (r c)⁻¹ := hw.symm
            _ = sr (a - 2 * c) := by rw [conj_r_sr]
        injection h' with hb
      have hd : b - a = -(2 * c) := by rw [hb]; ring
      rw [Subgroup.mem_zpowers_iff]
      refine ⟨-c.val, ?_⟩
      rw [r_zpow]
      congr 1
      rw [hd]
      rw [Int.cast_neg, Int.cast_natCast]
      rw [ZMod.natCast_zmod_val c]
      ring
    exact dihedral_sr_not_conj_of_rotation_sq n hn2 hgen hmem
  · -- w = sr c: sr b = sr (2c - a)
    have hmem : (r (b - a) : DihedralGroup n) ∈ Subgroup.zpowers (r 2 : DihedralGroup n) := by
      have hb : b = 2 * c - a := by
        have h' : (sr b : DihedralGroup n) = sr (2 * c - a) := by
          calc
            (sr b : DihedralGroup n) = (sr c : DihedralGroup n) * sr a * (sr c)⁻¹ := hw.symm
            _ = sr (2 * c - a) := by
              rw [inv_sr, sr_mul_sr, r_mul_sr]
              congr 1
              ring
        injection h' with hb
      have hd : b - a = 2 * (c - a) := by rw [hb]; ring
      rw [Subgroup.mem_zpowers_iff]
      refine ⟨(c - a).val, ?_⟩
      rw [r_zpow]
      congr 1
      rw [hd]
      rw [Int.cast_natCast]
      rw [ZMod.natCast_zmod_val (c - a)]
    exact dihedral_sr_not_conj_of_rotation_sq n hn2 hgen hmem

/-- Every rotation `r a` lies in `⟨r 1⟩`. -/
private lemma mem_r_one_zpowers (n : ℕ) [NeZero n] (a : ZMod n) :
    (r a : DihedralGroup n) ∈ Subgroup.zpowers (r 1 : DihedralGroup n) := by
  rw [Subgroup.mem_zpowers_iff]
  refine ⟨(a.val : ℤ), ?_⟩
  rw [r_zpow]
  congr 1
  rw [Int.cast_natCast]
  rw [ZMod.natCast_zmod_val a]
  simp

/-- `DihedralGroup 2` (the Klein four group) is commutative. -/
private lemma dihedral2_comm (w1 w2 : DihedralGroup 2) : w1 * w2 = w2 * w1 := by
  rcases w1 with ⟨a⟩ | ⟨a⟩ <;> rcases w2 with ⟨b⟩ | ⟨b⟩ <;>
    fin_cases a <;> fin_cases b <;> decide

/-- `DihedralGroup n` is commutative when `n = 2`. -/
private lemma dihedral_comm_of_two {n : ℕ} (hn : n = 2) (w1 w2 : DihedralGroup n) :
    w1 * w2 = w2 * w1 := by
  subst hn
  exact dihedral2_comm w1 w2

/-- An element of `ZMod n` (`2 ∣ n`) that is twice something has even
canonical representative. -/
private lemma zmod_two_mul_even_val {n : ℕ} [NeZero n] (hn2 : 2 ∣ n) {x : ZMod n}
    (h : ∃ c : ZMod n, 2 * c = x) : 2 ∣ x.val := by
  rcases h with ⟨c, hc⟩
  have hxval : x.val = (2 * c.val) % n := by
    calc
      x.val = (2 * c : ZMod n).val := by rw [hc]
      _ = (2 * (c.val : ZMod n) : ZMod n).val := by
        congr 1
        conv_lhs => rw [← ZMod.natCast_zmod_val c]
      _ = (2 * c.val : ZMod n).val := by
        congr 1
      _ = (2 * c.val) % n := by
        have hcast : (2 * (c.val : ZMod n) : ZMod n) = ((2 * c.val : ℕ) : ZMod n) := by
          norm_num
        rw [hcast]
        exact ZMod.val_natCast n (2 * c.val)
  rw [hxval]
  rw [Nat.dvd_iff_mod_eq_zero]
  rw [Nat.mod_mod_of_dvd (2 * c.val) hn2]
  exact Nat.mod_eq_zero_of_dvd (dvd_mul_right 2 c.val)

/-- In `ZMod n` with `2 ∣ n`, an element with even canonical representative is
twice something. -/
private lemma zmod_two_mul_of_even_val {n : ℕ} [NeZero n] (hn2 : 2 ∣ n) {x : ZMod n}
    (h : 2 ∣ x.val) : ∃ c : ZMod n, 2 * c = x := by
  refine ⟨((x.val / 2 : ℕ) : ZMod n), ?_⟩
  have hdiv : 2 * (x.val / 2) = x.val := by
    rw [mul_comm]
    exact Nat.div_mul_cancel h
  calc
    (2 : ZMod n) * (((x.val / 2 : ℕ) : ZMod n)) = (((2 * (x.val / 2) : ℕ) : ZMod n)) := by
      norm_num
    _ = (x.val : ZMod n) := by rw [hdiv]
    _ = x := by rw [ZMod.natCast_zmod_val]

/-- In `ZMod n` with `2 ∣ n`, if `x` and `y` are both not twice anything, then
`x − y` is twice something (the image of multiplication by `2` has index two). -/
private lemma zmod_two_mul_of_not_exists {n : ℕ} [NeZero n] (hn2 : 2 ∣ n) {x y : ZMod n}
    (hx : ¬ ∃ c : ZMod n, 2 * c = x) (hy : ¬ ∃ c : ZMod n, 2 * c = y) :
    ∃ c : ZMod n, 2 * c = x - y := by
  classical
  have hx2 : ¬ 2 ∣ x.val := by
    intro h
    exact hx (zmod_two_mul_of_even_val (n := n) hn2 h)
  have hy2 : ¬ 2 ∣ y.val := by
    intro h
    exact hy (zmod_two_mul_of_even_val (n := n) hn2 h)
  have hxodd : x.val % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one x.val with h | h
    · exfalso
      exact hx2 (Nat.dvd_iff_mod_eq_zero.mpr h)
    · exact h
  have hyodd : y.val % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one y.val with h | h
    · exfalso
      exact hy2 (Nat.dvd_iff_mod_eq_zero.mpr h)
    · exact h
  rcases (Nat.odd_iff.mpr hxodd) with ⟨m, hm⟩
  rcases (Nat.odd_iff.mpr hyodd) with ⟨m', hm'⟩
  refine ⟨(m : ZMod n) - (m' : ZMod n), ?_⟩
  have hx2m : x = 2 * (m : ZMod n) + 1 := by
    rw [← ZMod.natCast_zmod_val x, hm]
    norm_num
  have hy2m' : y = 2 * (m' : ZMod n) + 1 := by
    rw [← ZMod.natCast_zmod_val y, hm']
    norm_num
  rw [mul_sub, hx2m, hy2m']
  ring

/-- In the dihedral model `D_n` (`2 ∣ n`), if `b − a` is not twice anything,
then every reflection `sr j` is conjugate (by a rotation) to `sr a` or `sr b`. -/
private lemma dihedral_reflection_conj_to (n : ℕ) [NeZero n] (hn2 : 2 ∣ n)
    {a b j : ZMod n} (hb : ¬ ∃ c : ZMod n, 2 * c = b - a) :
    (∃ w : DihedralGroup n, w * (sr j : DihedralGroup n) * w⁻¹ = sr a) ∨
      (∃ w : DihedralGroup n, w * (sr j : DihedralGroup n) * w⁻¹ = sr b) := by
  classical
  by_cases h : ∃ c : ZMod n, 2 * c = j - a
  · left
    rcases h with ⟨c, hc⟩
    refine ⟨r c, ?_⟩
    calc
      (r c : DihedralGroup n) * (sr j : DihedralGroup n) * (r c)⁻¹ = sr (j - 2 * c) :=
        conj_r_sr n j c
      _ = sr a := by
        rw [hc]
        congr 1
        ring
  · right
    have h3 : ∃ c : ZMod n, 2 * c = (j - a) - (b - a) :=
      zmod_two_mul_of_not_exists (n := n) hn2 h hb
    rcases h3 with ⟨c, hc⟩
    refine ⟨r c, ?_⟩
    calc
      (r c : DihedralGroup n) * (sr j : DihedralGroup n) * (r c)⁻¹ = sr (j - 2 * c) :=
        conj_r_sr n j c
      _ = sr b := by
        -- (j - a) - (b - a) = j - b
        rw [hc]
        congr 1
        ring

/-! ## Involutions of `S − S0` and of `H − H0` are conjugate to `t1` or `t2` -/

/-- `t1 ≠ t2` (both lie in `S − S0` and `S0 = ⟨t1·t2⟩`). -/
private lemma t1_ne_t2 (c : Hyp11 G) : c.t1 ≠ c.t2 := by
  intro h
  have hS0 : (c.S0 : Subgroup G) = ⊥ := by
    rw [c.S0_eq_zpowers]
    have ht12 : c.t1 * c.t2 = 1 := by simpa [h, pow_two] using c.t1_involution.2
    rw [ht12]
    exact Subgroup.zpowers_one_eq_bot
  have hcard : Nat.card ↥(c.S0 : Subgroup G) = 1 := by
    rw [hS0]
    exact Subgroup.card_bot
  have hcard2 : Nat.card ↥(c.S0 : Subgroup G) = 2 ^ c.m := S0_nat_card c
  have hle : 2 ≤ 2 ^ c.m := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) c.one_le_m
  rw [← hcard2] at hle
  omega

/-- Every involution of `S − S0` is conjugate in `S` to `t1` or to `t2`. -/
private lemma involution_S_not_S0_conj_to_t1_or_t2 (c : Hyp11 G) {x : G}
    (hxS : x ∈ (c.S : Subgroup G)) (hxS0 : x ∉ (c.S0 : Subgroup G)) (hx2 : x * x = 1) :
    ∃ g : G, g ∈ (c.S : Subgroup G) ∧ (g * x * g⁻¹ = c.t1 ∨ g * x * g⁻¹ = c.t2) := by
  classical
  by_cases hm1 : c.m = 1
  · -- m = 1: |S| = 4, and the elements `1, t, t1, t2` exhaust `S`
    have hcard : Fintype.card ↥(c.S : Subgroup G) = 4 := by
      rw [← Nat.card_eq_fintype_card, S_nat_card c, hm1]
      norm_num
    let xS : ↥(c.S : Subgroup G) := ⟨x, hxS⟩
    have htS : c.t ∈ (c.S : Subgroup G) := c.S0_le_S c.t_mem_S0
    have huniv : ({⟨(1 : G), by simp⟩, ⟨c.t, htS⟩, ⟨c.t1, c.t1_mem_S⟩,
        ⟨c.t2, c.t2_mem_S⟩} : Finset ↥(c.S : Subgroup G)) = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [hcard]
      have hne1t : (⟨(1 : G), by simp⟩ : ↥(c.S : Subgroup G)) ≠ ⟨c.t, htS⟩ := by
        intro h
        have h1 : (1 : G) = c.t := by
          simpa using (congrArg (fun z : ↥(c.S : Subgroup G) => (z : G)) h)
        exact c.t_involution.1 (by rw [← h1])
      have hne1t1 : (⟨(1 : G), by simp⟩ : ↥(c.S : Subgroup G)) ≠ ⟨c.t1, c.t1_mem_S⟩ := by
        intro h
        exact c.t1_not_mem_S0 (by
          have h1 : (1 : G) = c.t1 := by
            simpa using (congrArg (fun z : ↥(c.S : Subgroup G) => (z : G)) h)
          rw [← h1]
          simp)
      have hne1t2 : (⟨(1 : G), by simp⟩ : ↥(c.S : Subgroup G)) ≠ ⟨c.t2, c.t2_mem_S⟩ := by
        intro h
        exact c.t2_not_mem_S0 (by
          have h1 : (1 : G) = c.t2 := by
            simpa using (congrArg (fun z : ↥(c.S : Subgroup G) => (z : G)) h)
          rw [← h1]
          simp)
      have hnet1 : (⟨c.t, htS⟩ : ↥(c.S : Subgroup G)) ≠ (⟨c.t1, c.t1_mem_S⟩ : ↥(c.S : Subgroup G)) := by
        intro h
        exact c.t1_not_mem_S0 (by
          have h1 : c.t = c.t1 := by
            simpa using (congrArg (fun z : ↥(c.S : Subgroup G) => (z : G)) h)
          rw [← h1]
          exact c.t_mem_S0)
      have hnet2 : (⟨c.t, htS⟩ : ↥(c.S : Subgroup G)) ≠ (⟨c.t2, c.t2_mem_S⟩ : ↥(c.S : Subgroup G)) := by
        intro h
        exact c.t2_not_mem_S0 (by
          have h1 : c.t = c.t2 := by
            simpa using (congrArg (fun z : ↥(c.S : Subgroup G) => (z : G)) h)
          rw [← h1]
          exact c.t_mem_S0)
      have hne12 : (⟨c.t1, c.t1_mem_S⟩ : ↥(c.S : Subgroup G)) ≠ (⟨c.t2, c.t2_mem_S⟩ : ↥(c.S : Subgroup G)) := by
        intro h
        exact t1_ne_t2 c (by simpa using (congrArg (fun z : ↥(c.S : Subgroup G) => (z : G)) h))
      simp [hne1t, hne1t1, hne1t2, hnet1, hnet2, hne12, Finset.card_insert_of_notMem]
    have hxmem : xS ∈ ({⟨(1 : G), by simp⟩, ⟨c.t, htS⟩, ⟨c.t1, c.t1_mem_S⟩,
        ⟨c.t2, c.t2_mem_S⟩} : Finset ↥(c.S : Subgroup G)) := by
      rw [huniv]
      simp
    rcases Finset.mem_insert.mp hxmem with h1 | hrest
    · exfalso
      exact hxS0 (by
        have hx1 : x = 1 := by
          simpa [xS] using (congrArg (fun z : ↥(c.S : Subgroup G) => (z : G)) h1)
        rw [hx1]
        simp)
    · rcases Finset.mem_insert.mp hrest with ht | hrest
      · exfalso
        exact hxS0 (by
          have hx1 : x = c.t := by
            simpa [xS] using (congrArg (fun z : ↥(c.S : Subgroup G) => (z : G)) ht)
          rw [hx1]
          exact c.t_mem_S0)
      · rcases Finset.mem_insert.mp hrest with ht1 | ht2
        · have hx1 : x = c.t1 := by
            simpa [xS] using (congrArg (fun z : ↥(c.S : Subgroup G) => (z : G)) ht1)
          refine ⟨1, by simp, ?_⟩
          left
          simpa [hx1]
        · rcases Finset.mem_singleton.mp ht2 with ht2'
          have hx2' : x = c.t2 := by
            simpa [xS] using (congrArg (fun z : ↥(c.S : Subgroup G) => (z : G)) ht2')
          refine ⟨1, by simp, ?_⟩
          right
          simpa [hx2']
  · -- m ≥ 2: transport to the dihedral model `S ≅ D_{2^m}`
    have hm2 : 2 ≤ c.m := Nat.succ_le_of_lt (lt_of_le_of_ne c.one_le_m (Ne.symm hm1))
    let n := 2 ^ c.m
    have : NeZero n := ⟨pow_ne_zero c.m (by norm_num)⟩
    let e : ↥(c.S : Subgroup G) ≃* DihedralGroup n := Classical.choice c.dihedralEquiv
    let t1S : ↥(c.S : Subgroup G) := ⟨c.t1, c.t1_mem_S⟩
    let t2S : ↥(c.S : Subgroup G) := ⟨c.t2, c.t2_mem_S⟩
    let xS : ↥(c.S : Subgroup G) := ⟨x, hxS⟩
    have hS0map : (⊤ : Subgroup ↥(c.S0 : Subgroup G)).map
        (e.toMonoidHom.comp (Subgroup.inclusion c.S0_le_S)) =
        Subgroup.zpowers (r 1 : DihedralGroup n) := by
      simpa [n] using eS0_eq_zpowers_r1 c hm2 e
    have hnot_rot_x : e xS ∉ Subgroup.zpowers (r 1 : DihedralGroup n) := by
      intro h
      rw [← hS0map] at h
      rcases (Subgroup.mem_map.mp h) with ⟨y, hy, hyeq⟩
      have hι : Subgroup.inclusion c.S0_le_S y = xS := e.injective hyeq
      have hyG : (y : G) = x := congrArg (fun z : ↥(c.S : Subgroup G) => (z : G)) hι
      exact hxS0 (by rw [← hyG]; exact y.2)
    have hnot_rot1 : e t1S ∉ Subgroup.zpowers (r 1 : DihedralGroup n) := by
      intro h
      rw [← hS0map] at h
      rcases (Subgroup.mem_map.mp h) with ⟨y, hy, hyeq⟩
      have hι : Subgroup.inclusion c.S0_le_S y = t1S := e.injective hyeq
      have hyG : (y : G) = c.t1 := congrArg (fun z : ↥(c.S : Subgroup G) => (z : G)) hι
      exact c.t1_not_mem_S0 (by rw [← hyG]; exact y.2)
    have hnot_rot2 : e t2S ∉ Subgroup.zpowers (r 1 : DihedralGroup n) := by
      intro h
      rw [← hS0map] at h
      rcases (Subgroup.mem_map.mp h) with ⟨y, hy, hyeq⟩
      have hι : Subgroup.inclusion c.S0_le_S y = t2S := e.injective hyeq
      have hyG : (y : G) = c.t2 := congrArg (fun z : ↥(c.S : Subgroup G) => (z : G)) hι
      exact c.t2_not_mem_S0 (by rw [← hyG]; exact y.2)
    rcases h1 : e xS with ⟨j⟩ | ⟨j⟩
    · exfalso
      exact hnot_rot_x (by
        rw [h1]
        exact mem_r_one_zpowers n j)
    · rcases h2 : e t1S with ⟨a⟩ | ⟨a⟩
      · exfalso
        exact hnot_rot1 (by
          rw [h2]
          exact mem_r_one_zpowers n a)
      · rcases h3 : e t2S with ⟨b⟩ | ⟨b⟩
        · exfalso
          exact hnot_rot2 (by
            rw [h3]
            exact mem_r_one_zpowers n b)
        · -- both reflections: `b − a` is odd, and every reflection is conjugate
          -- to `sr a` or `sr b` by a rotation
          have hgen : (r 1 : DihedralGroup n) ∈
              Subgroup.zpowers (r (b - a) : DihedralGroup n) := by
            have hst : Subgroup.zpowers (t1S * t2S) =
                (⊤ : Subgroup ↥(c.S0 : Subgroup G)).map (Subgroup.inclusion c.S0_le_S) := by
              ext x
              constructor
              · intro hx
                rcases (Subgroup.mem_zpowers_iff.mp hx) with ⟨k, hk⟩
                refine (Subgroup.mem_map).2 ?_
                refine ⟨⟨(x : G), ?_⟩, by simp, ?_⟩
                · rw [c.S0_eq_zpowers]
                  rw [Subgroup.mem_zpowers_iff]
                  exact ⟨k, by
                    simpa [t1S, t2S, Subgroup.coe_mul, Subgroup.coe_zpow] using
                      (congrArg (fun z : ↥(c.S : Subgroup G) => (z : G)) hk)⟩
                · rfl
              · intro hx
                rcases (Subgroup.mem_map.mp hx) with ⟨y, hy, hιy⟩
                have hxG : (x : G) = (y : G) := by
                  simpa using (congrArg (fun z : ↥(c.S : Subgroup G) => (z : G)) hιy).symm
                have hz : (x : G) ∈ Subgroup.zpowers (c.t1 * c.t2 : G) := by
                  have hy : (y : G) ∈ Subgroup.zpowers (c.t1 * c.t2 : G) := by
                    rw [← c.S0_eq_zpowers]
                    exact y.2
                  exact hxG ▸ hy
                rcases (Subgroup.mem_zpowers_iff.mp hz) with ⟨k, hk⟩
                rw [Subgroup.mem_zpowers_iff]
                refine ⟨k, ?_⟩
                apply Subtype.ext
                simpa [t1S, t2S, Subgroup.coe_mul, Subgroup.coe_zpow] using hk
            have hmain : Subgroup.zpowers (r (b - a) : DihedralGroup n) =
                (⊤ : Subgroup ↥(c.S0 : Subgroup G)).map
                  (e.toMonoidHom.comp (Subgroup.inclusion c.S0_le_S)) := by
              calc
                Subgroup.zpowers (r (b - a) : DihedralGroup n)
                    = Subgroup.zpowers (e (t1S * t2S)) := by
                        congr 1
                        calc
                          r (b - a) = sr a * sr b := by rw [sr_mul_sr]
                          _ = e t1S * e t2S := by rw [h2, h3]
                          _ = e (t1S * t2S) := by exact (map_mul e t1S t2S).symm
                _ = (Subgroup.zpowers (t1S * t2S)).map e := by
                        simp
                _ = ((⊤ : Subgroup ↥(c.S0 : Subgroup G)).map
                      (Subgroup.inclusion c.S0_le_S)).map e := by rw [hst]
                _ = (⊤ : Subgroup ↥(c.S0 : Subgroup G)).map
                      (e.toMonoidHom.comp (Subgroup.inclusion c.S0_le_S)) := by
                      simp [Subgroup.map_map]
            rw [hmain, hS0map]
            exact Subgroup.mem_zpowers _
          have hb : ¬ ∃ d : ZMod n, 2 * d = b - a := by
            intro hd0
            rcases hd0 with ⟨d, hd⟩
            exact dihedral_sr_not_conj_of_rotation_sq (n := n) (hn2 := by
              refine ⟨2 ^ (c.m - 1), ?_⟩
              rw [mul_comm, ← pow_succ, Nat.sub_add_cancel c.one_le_m]) hgen (by
              rw [← hd]
              rw [Subgroup.mem_zpowers_iff]
              refine ⟨(d.val : ℤ), ?_⟩
              rw [r_zpow]
              congr 1
              rw [Int.cast_natCast]
              rw [ZMod.natCast_zmod_val d])
          rcases dihedral_reflection_conj_to (n := n) (hn2 := by
            refine ⟨2 ^ (c.m - 1), ?_⟩
            rw [mul_comm, ← pow_succ, Nat.sub_add_cancel c.one_le_m]) (j := j) hb with hleft | hright
          · rcases hleft with ⟨w, hw⟩
            refine ⟨(e.symm w : ↥(c.S : Subgroup G)), (e.symm w).2, ?_⟩
            have hmain' : (e.symm w : ↥(c.S : Subgroup G)) * xS * (e.symm w : ↥(c.S : Subgroup G))⁻¹ = t1S := by
              apply e.injective
              calc
                e ((e.symm w : ↥(c.S : Subgroup G)) * xS * (e.symm w : ↥(c.S : Subgroup G))⁻¹)
                    = e (e.symm w) * e xS * (e (e.symm w))⁻¹ := by simp [map_mul, map_inv]
                _ = w * (sr j : DihedralGroup n) * w⁻¹ := by simp [h1]
                _ = sr a := hw
                _ = e t1S := h2.symm
            left
            simpa [xS, t1S] using (congrArg (fun z : ↥(c.S : Subgroup G) => (z : G)) hmain')
          · rcases hright with ⟨w, hw⟩
            refine ⟨(e.symm w : ↥(c.S : Subgroup G)), (e.symm w).2, ?_⟩
            have hmain' : (e.symm w : ↥(c.S : Subgroup G)) * xS * (e.symm w : ↥(c.S : Subgroup G))⁻¹ = t2S := by
              apply e.injective
              calc
                e ((e.symm w : ↥(c.S : Subgroup G)) * xS * (e.symm w : ↥(c.S : Subgroup G))⁻¹)
                    = e (e.symm w) * e xS * (e (e.symm w))⁻¹ := by simp [map_mul, map_inv]
                _ = w * (sr j : DihedralGroup n) * w⁻¹ := by simp [h1]
                _ = sr b := hw
                _ = e t2S := h3.symm
            right
            simpa [xS, t2S] using (congrArg (fun z : ↥(c.S : Subgroup G) => (z : G)) hmain')

/-- Every involution of `H − H0` is conjugate in `H` to `t1` or to `t2`:
`x = u·s'` with `u ∈ U`, `s' ∈ S − S0`; `x² = 1` makes `s'` invert `u`, so
`x = v·s'·v⁻¹` for the square root `v` of `u`, and `s'` is `S`-conjugate to
`t1` or `t2`. -/
private lemma involution_H_not_H0_conj_to_t1_or_t2 (c : Hyp11 G) (h12 : Hyp12 c)
    {x : G} (hxH : x ∈ c.H) (hx2 : x * x = 1) (hxH0 : x ∉ c.H0) :
    ∃ i : Fin 2, ∃ g : G, g ∈ c.H ∧ g * x * g⁻¹ = (lemma_2_2_tH c i : G) := by
  classical
  have hxH' : x ∈ (↑c.H : Set G) := hxH
  rw [H_set_eq_U_mul_S c] at hxH'
  rcases hxH' with ⟨u, hu, s, hs, hxEq⟩
  have hxEq' : x = (u : G) * s := hxEq.symm
  have hsS0 : s ∉ (c.S0 : Subgroup G) := by
    intro hsS0
    apply hxH0
    rw [hxEq']
    have hxH0' : (u : G) * s ∈ (↑c.H0 : Set G) := by
      rw [H0_set_eq_U_mul_S0 c h12]
      exact ⟨u, hu, s, hsS0, rfl⟩
    exact hxH0'
  have hu1 : s * (u : G) * s⁻¹ ∈ c.U := U_normal_in_H c (S_le_H c hs) hu
  have hs2 : s * s = 1 := by
    have hx2' : (u : G) * (s * (u : G) * s⁻¹) * (s * s) = 1 := by
      calc
        (u : G) * (s * (u : G) * s⁻¹) * (s * s) = (u : G) * s * (u : G) * s := by group
        _ = x * x := by
          rw [hxEq']
          group
        _ = 1 := hx2
    have hssU : s * s ∈ c.U := by
      have h : (s * s) = ((u : G) * (s * (u : G) * s⁻¹))⁻¹ := by
        calc
          (s * s) = ((u : G) * (s * (u : G) * s⁻¹))⁻¹ * ((u : G) * (s * (u : G) * s⁻¹)) * (s * s) := by group
          _ = ((u : G) * (s * (u : G) * s⁻¹))⁻¹ * ((u : G) * (s * (u : G) * s⁻¹) * (s * s)) := by group
          _ = ((u : G) * (s * (u : G) * s⁻¹))⁻¹ * 1 := by rw [hx2']
          _ = ((u : G) * (s * (u : G) * s⁻¹))⁻¹ := by simp
      rw [h]
      exact c.U.inv_mem (c.U.mul_mem hu hu1)
    exact U_inter_S_eq_bot c hssU (by simpa [pow_two] using (c.S : Subgroup G).pow_mem hs 2)
  have hu1inv : s * (u : G) * s⁻¹ = (u : G)⁻¹ := by
    have h : (u : G) * (s * (u : G) * s⁻¹) = 1 := by
      calc
        (u : G) * (s * (u : G) * s⁻¹) = (u : G) * (s * (u : G) * s⁻¹) * 1 := by rw [mul_one]
        _ = (u : G) * (s * (u : G) * s⁻¹) * (s * s) := by rw [hs2]
        _ = 1 := by
          calc
            (u : G) * (s * (u : G) * s⁻¹) * (s * s) = (u : G) * s * (u : G) * s := by group
            _ = x * x := by
              rw [hxEq']
              group
            _ = 1 := hx2
    exact (inv_eq_of_mul_eq_one_right h).symm
  rcases U_sq_exists c hu with ⟨v, hv, hv2, hvinv⟩
  have hvinv' : s * v * s⁻¹ = v⁻¹ := hvinv s (S_le_H c hs) hu1inv
  have hmain : v * s * v⁻¹ = x := by
    calc
      v * s * v⁻¹ = v * (s * v⁻¹ * s⁻¹) * s := by group
      _ = v * v * s := by
        have hsv : s * v⁻¹ * s⁻¹ = v := by
          calc
            s * v⁻¹ * s⁻¹ = (s * v * s⁻¹)⁻¹ := by group
            _ = (v⁻¹)⁻¹ := by rw [hvinv']
            _ = v := by simp
        rw [hsv]
      _ = (u : G) * s := by rw [hv2]
      _ = x := hxEq'.symm
  rcases involution_S_not_S0_conj_to_t1_or_t2 c hs hsS0 hs2 with ⟨g, hg, hgs⟩
  rcases hgs with hg1 | hg2
  · refine ⟨0, g * v⁻¹, ?_, ?_⟩
    · exact c.H.mul_mem (S_le_H c hg) (c.H.inv_mem (U_le_H c hv))
    · calc
        (g * v⁻¹) * x * (g * v⁻¹)⁻¹ = g * v⁻¹ * x * v * g⁻¹ := by group
        _ = g * v⁻¹ * (v * s * v⁻¹) * v * g⁻¹ := by rw [← hmain]
        _ = g * s * g⁻¹ := by group
        _ = c.t1 := hg1
  · refine ⟨1, g * v⁻¹, ?_, ?_⟩
    · exact c.H.mul_mem (S_le_H c hg) (c.H.inv_mem (U_le_H c hv))
    · calc
        (g * v⁻¹) * x * (g * v⁻¹)⁻¹ = g * v⁻¹ * x * v * g⁻¹ := by group
        _ = g * v⁻¹ * (v * s * v⁻¹) * v * g⁻¹ := by rw [← hmain]
        _ = g * s * g⁻¹ := by group
        _ = c.t2 := hg2

/-- The induced function vanishes outside `H0` (no index hypothesis needed;
`H0 ⊴ H` suffices). -/
private lemma inducedFromSub_eq_zero_of_not_mem' {H0 H : Subgroup G}
    (hH0 : H0 ≤ H) (hH0normal : IsNormalIn H0 H)
    {φ : ClassFunction (↥H0)} {x : ↥H} (hx : (x : G) ∉ H0) :
    inducedFromSub hH0 φ x = 0 := by
  classical
  have hnot : ∀ y : ↥H, ¬ y⁻¹ * x * y ∈ H0.subgroupOf H := by
    intro y hy
    apply hx
    have hmem : (y : G) * (((y⁻¹ * x * y : ↥H) : G)) * (y : G)⁻¹ ∈ H0 :=
      (hH0normal).2 y y.2 ((y⁻¹ * x * y : ↥H) : G) (Subgroup.mem_subgroupOf.mp hy)
    have hEq : (y : G) * (((y⁻¹ * x * y : ↥H) : G)) * (y : G)⁻¹ = (x : G) := by
      change (y : G) * ((y : G)⁻¹ * (x : G) * (y : G)) * (y : G)⁻¹ = (x : G)
      group
    rwa [hEq] at hmem
  unfold inducedFromSub inducedClassFunction
  simp [hnot]

/-- The conjugacy class of `x` has size `|G : C_G(x)|`. -/
private lemma card_conjClass_eq_index {G : Type u} [Group G] [Finite G] (x : G) :
    Nat.card (ConjClasses.mk x).carrier = (Subgroup.centralizer ({x} : Set G)).index := by
  classical
  have hst := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct G) x
  have hst' : Fintype.card (ConjClasses.mk x).carrier *
      Fintype.card (MulAction.stabilizer (ConjAct G) x) = Fintype.card G := by
    simpa [ConjAct.orbit_eq_carrier_conjClasses] using hst
  let e : MulAction.stabilizer (ConjAct G) x ≃ ↥(Subgroup.centralizer ({x} : Set G)) :=
    { toFun := fun y =>
        ⟨ConjAct.ofConjAct y.1, by
          rw [Subgroup.mem_centralizer_iff]
          intro z hz
          simp at hz
          rw [hz]
          have hy : y.1 • x = x := y.2
          rw [ConjAct.smul_def] at hy
          have hmain : ConjAct.ofConjAct y.1 * x = x * ConjAct.ofConjAct y.1 := by
            calc
              ConjAct.ofConjAct y.1 * x = (ConjAct.ofConjAct y.1 * x * (ConjAct.ofConjAct y.1)⁻¹) *
                  ConjAct.ofConjAct y.1 := by group
              _ = x * ConjAct.ofConjAct y.1 := by
                    rw [hy]
          exact hmain.symm⟩
      invFun := fun z => ⟨ConjAct.toConjAct (z : G), by
        change ConjAct.toConjAct (z : G) • x = x
        rw [ConjAct.toConjAct_smul]
        exact mul_inv_eq_of_eq_mul ((Subgroup.mem_centralizer_iff.mp z.2) x (by simp)).symm⟩
      left_inv := by intro y; apply Subtype.ext; rfl
      right_inv := by intro z; apply Subtype.ext; rfl }
  have hC : Fintype.card (MulAction.stabilizer (ConjAct G) x) =
      Nat.card (↥(Subgroup.centralizer ({x} : Set G))) := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_congr e
  have hN : (Subgroup.centralizer ({x} : Set G)).index *
      Fintype.card (MulAction.stabilizer (ConjAct G) x) = Fintype.card G := by
    rw [hC]
    rw [← Nat.card_eq_fintype_card]
    exact Subgroup.index_mul_card (Subgroup.centralizer ({x} : Set G))
  rw [Nat.card_eq_fintype_card]
  exact Nat.mul_right_cancel
    (by positivity : 0 < Fintype.card (MulAction.stabilizer (ConjAct G) x)) (by
      rw [← hN] at hst'
      exact hst')

/-- `|t^G| = |G : H|`. -/
private lemma card_t_class_eq_H_index (c : Hyp11 G) :
    Nat.card (ConjClasses.mk c.t).carrier = c.H.index := by
  rw [card_conjClass_eq_index, c.H_eq_centralizer]

/-- `|t1^H| = k1`. -/
private lemma card_t1_class_eq_k1 (c : Hyp11 G) :
    Nat.card (ConjClasses.mk (⟨c.t1, t1_mem_H c⟩ : ↥c.H)).carrier = c.k1 := by
  classical
  rw [card_conjClass_eq_index]
  rw [Hyp11.k1]
  congr 1
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_subgroupOf]
    refine ⟨x.2, ?_⟩
    have hx' : (⟨c.t1, t1_mem_H c⟩ : ↥c.H) * x = x * (⟨c.t1, t1_mem_H c⟩ : ↥c.H) :=
      (Subgroup.mem_centralizer_iff.mp hx) (⟨c.t1, t1_mem_H c⟩ : ↥c.H) (by simp)
    have hxG : (x : G) * c.t1 = c.t1 * (x : G) := by
      simpa using (congrArg (fun z : ↥c.H => (z : G)) hx'.symm)
    exact (Subgroup.mem_centralizer_iff.mpr (by
      intro z hz
      simp at hz
      rw [hz]
      exact hxG.symm))
  · intro hx
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    simp at hz
    rw [hz]
    have hx' : (x : G) ∈ Subgroup.centralizer ({c.t1} : Set G) :=
      (Subgroup.mem_subgroupOf.mp hx).2
    have hxG : c.t1 * (x : G) = (x : G) * c.t1 :=
      (Subgroup.mem_centralizer_iff.mp hx') c.t1 (by simp)
    apply Subtype.ext
    simpa using hxG

/-- `|t2^H| = k2`. -/
private lemma card_t2_class_eq_k2 (c : Hyp11 G) :
    Nat.card (ConjClasses.mk (⟨c.t2, t2_mem_H c⟩ : ↥c.H)).carrier = c.k2 := by
  classical
  rw [card_conjClass_eq_index]
  rw [Hyp11.k2]
  congr 1
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_subgroupOf]
    refine ⟨x.2, ?_⟩
    have hx' : (⟨c.t2, t2_mem_H c⟩ : ↥c.H) * x = x * (⟨c.t2, t2_mem_H c⟩ : ↥c.H) :=
      (Subgroup.mem_centralizer_iff.mp hx) (⟨c.t2, t2_mem_H c⟩ : ↥c.H) (by simp)
    have hxG : (x : G) * c.t2 = c.t2 * (x : G) := by
      simpa using (congrArg (fun z : ↥c.H => (z : G)) hx'.symm)
    exact (Subgroup.mem_centralizer_iff.mpr (by
      intro z hz
      simp at hz
      rw [hz]
      exact hxG.symm))
  · intro hx
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    simp at hz
    rw [hz]
    have hx' : (x : G) ∈ Subgroup.centralizer ({c.t2} : Set G) :=
      (Subgroup.mem_subgroupOf.mp hx).2
    have hxG : c.t2 * (x : G) = (x : G) * c.t2 :=
      (Subgroup.mem_centralizer_iff.mp hx') c.t2 (by simp)
    apply Subtype.ext
    simpa using hxG

/-- Linearity of the scalar product in a double sum. -/
private lemma scalarProduct_double_sum {G : Type u} [Group G] [Fintype G]
    {ι κ : Type u} [Fintype ι] [Fintype κ]
    (f : ι → κ → ClassFunction G) (δ : ClassFunction G) :
    scalarProduct G (fun g : G => ∑ i : ι, ∑ j : κ, f i j g) δ =
      ∑ i : ι, ∑ j : κ, scalarProduct G (f i j) δ := by
  classical
  unfold scalarProduct
  calc
    (Nat.card G : ℂ)⁻¹ * ∑ g : G, (∑ i : ι, ∑ j : κ, f i j g) * star (δ g)
        = (Nat.card G : ℂ)⁻¹ * ∑ g : G, (∑ i : ι, ∑ j : κ, f i j g * star (δ g)) := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro g hg
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [Finset.sum_mul]
    _ = (Nat.card G : ℂ)⁻¹ * ∑ i : ι, ∑ j : κ, ∑ g : G, f i j g * star (δ g) := by
            congr 1
            rw [Finset.sum_comm]
            congr 1
            funext i
            rw [Finset.sum_comm]
    _ = ∑ i : ι, ∑ j : κ, (Nat.card G : ℂ)⁻¹ * ∑ g : G, f i j g * star (δ g) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [Finset.mul_sum]

/-- An element of `U = O(H)` with square `1` is `1` (the odd core has odd
order). -/
private lemma U_sq_eq_one (c : Hyp11 G) {u : G} (hu : u ∈ c.U) : u ^ 2 = 1 → u = 1 := by
  classical
  intro hu2
  have hcop : Nat.Coprime 2 (Nat.card ↥c.U) := by
    have h1 : Nat.card ↥c.U = Nat.card (pPrimeCore 2 c.H) := by
      dsimp [Hyp11.U]
      rw [oddCoreOf]
      exact Subgroup.card_map_of_injective (f := c.H.subtype)
        (K := pPrimeCore 2 c.H) (Subgroup.subtype_injective c.H)
    rw [h1]
    exact pPrimeCore_coprime_card (p := 2) (G := c.H)
  have hordU : orderOf (u : G) ∣ Nat.card ↥c.U := by
    change orderOf (c.U.subtype (⟨u, hu⟩ : ↥c.U)) ∣ Nat.card ↥c.U
    rw [orderOf_injective c.U.subtype (Subgroup.subtype_injective c.U) (⟨u, hu⟩ : ↥c.U)]
    have h' : orderOf (⟨u, hu⟩ : ↥c.U) ∣ Fintype.card ↥c.U :=
      orderOf_dvd_card (G := ↥c.U) (x := ⟨u, hu⟩)
    rwa [← Nat.card_eq_fintype_card] at h'
  have hord2 : orderOf (u : G) ∣ 2 := orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using hu2)
  have h1' : orderOf (u : G) = 1 := by
    have hdvd : orderOf (u : G) ∣ 1 := by
      rw [← hcop.gcd_eq_one]
      exact Nat.dvd_gcd hord2 hordU
    exact Nat.dvd_one.mp hdvd
  exact orderOf_eq_one_iff.mp h1'

/-- `t ∈ T`. -/
private lemma t_mem_T (c : Hyp11 G) : c.t ∈ c.T := by
  dsimp [Hyp11.T]
  exact ⟨S0_le_H0 c c.t_mem_S0, t_not_mem_U c⟩

-- The class-sum identities are elaborated in a `[Finite G]`-only context: with the
-- file-level local instance `Fintype.ofFinite`, a `[Fintype G]` binder would give two
-- non-defeq `Fintype G` instances (the binder vs `Fintype.ofFinite`), breaking the
-- `scalarProduct`/`∑ χ : Irr G` terms.  `[Finite G]` keeps a single instance.
private lemma unique_involution_of_H0 (c : Hyp11 G) (h12 : Hyp12 c) :
    ∀ x : G, x ∈ c.H0 → x ^ 2 = 1 → x ≠ 1 → x = c.t := by
  classical
  intro x hxH0 hx2 hxne
  rcases H0_eq_U_mul_S0 c h12 (x := ⟨x, hxH0⟩) with ⟨u, r, hxEq⟩
  have hxEq' : x = (u : G) * (r : G) := by simpa using hxEq
  have hrurU : (r : G) * (u : G) * (r : G)⁻¹ ∈ c.U :=
    (h12.U_normal_in_H0).2 (r : G) (S0_le_H0 c r.2) (u : G) u.2
  have hx2exp : x ^ 2 = (u : G) * ((r : G) * (u : G) * (r : G)⁻¹) * (r : G) ^ 2 := by
    rw [hxEq', pow_two, pow_two]
    group
  let a : G := (u : G) * ((r : G) * (u : G) * (r : G)⁻¹)
  have haU : a ∈ c.U := c.U.mul_mem u.2 hrurU
  have har2 : a * (r : G) ^ 2 = 1 := by
    change (u : G) * ((r : G) * (u : G) * (r : G)⁻¹) * (r : G) ^ 2 = 1
    rw [← hx2exp]
    exact hx2
  have hr2 : (r : G) ^ 2 = 1 := by
    have ha : a = ((r : G) ^ 2)⁻¹ := by
      calc
        a = a * 1 := by rw [mul_one]
        _ = a * ((r : G) ^ 2 * ((r : G) ^ 2)⁻¹) := by rw [mul_inv_cancel]
        _ = (a * (r : G) ^ 2) * ((r : G) ^ 2)⁻¹ := by group
        _ = 1 * ((r : G) ^ 2)⁻¹ := by rw [har2]
        _ = ((r : G) ^ 2)⁻¹ := by rw [one_mul]
    have haS0 : a ∈ (c.S0 : Subgroup G) := by
      rw [ha]
      exact (c.S0 : Subgroup G).inv_mem ((c.S0 : Subgroup G).pow_mem r.2 2)
    have ha1 : a = 1 := U_inter_S_eq_bot c haU (c.S0_le_S haS0)
    have h : ((r : G) ^ 2)⁻¹ = 1 := by
      rw [← ha]
      exact ha1
    exact inv_eq_one.mp h
  rcases (S0_sq_eq_one_iff c (x := r)).1 (by
    apply Subtype.ext
    simpa [Subgroup.coe_pow] using hr2) with rfl | ht
  · have hxu : x = (u : G) := by simpa using hxEq'
    have hu2 : (u : G) ^ 2 = 1 := by simpa [hxu] using hx2
    have hu1 : (u : G) = 1 := U_sq_eq_one c u.2 hu2
    exact False.elim (hxne (by simpa [hu1] using hxu))
  · rw [ht] at hxEq'
    have hxEq'' : x = (u : G) * c.t := by simpa using hxEq'
    have huH : (u : G) ∈ c.H := U_le_H c u.2
    have htu : c.t * (u : G) = (u : G) * c.t := by
      have huC : (u : G) ∈ Subgroup.centralizer ({c.t} : Set G) := by
        simpa [c.H_eq_centralizer] using huH
      exact (Subgroup.mem_centralizer_iff.mp huC) c.t (by simp)
    have hsq : ((u : G) * c.t) ^ 2 = (u : G) ^ 2 * c.t ^ 2 := by
      rw [pow_two, pow_two, pow_two]
      calc
        (u : G) * c.t * ((u : G) * c.t) = (u : G) * (c.t * (u : G)) * c.t := by group
        _ = (u : G) * ((u : G) * c.t) * c.t := by rw [htu]
        _ = (u : G) * (u : G) * (c.t * c.t) := by group
    have hu2 : (u : G) ^ 2 = 1 := by
      have hx2'' : ((u : G) * c.t) ^ 2 = 1 := by
        rw [← hxEq'']
        exact hx2
      simpa [hsq, c.t_involution.2, pow_two] using hx2''
    have hu1 : (u : G) = 1 := U_sq_eq_one c u.2 hu2
    simp [hxEq'', hu1]

section Section2V

variable {G : Type u} [Group G] [Finite G]

/-- `(f_ij, φ)_G` for the pair count of the classes of the involutions `ti`, `tj`
(Gorenstein 4.2.12 as an inner-product identity). -/
private lemma scalarProduct_classSumPairCountMul_involutions
    {ti tj : G} (hti2 : ti * ti = 1) (htj2 : tj * tj = 1)
    (φ : ClassFunction G) :
    scalarProduct G (fun g : G => (classSumPairCountMul (ConjClasses.mk ti) (ConjClasses.mk tj) g : ℂ)) φ =
      ((Nat.card (ConjClasses.mk ti).carrier : ℂ) * (Nat.card (ConjClasses.mk tj).carrier : ℂ) /
          (Nat.card G : ℂ)) *
        ∑ χ : Irr G, (χ.1 ti * χ.1 tj / χ.1 1) * scalarProduct G χ.1 φ := by
  classical
  let c : ℂ := (Nat.card (ConjClasses.mk ti).carrier : ℂ) * (Nat.card (ConjClasses.mk tj).carrier : ℂ) /
    (Nat.card G : ℂ)
  let X : G → ℂ := fun g => ∑ χ : Irr G, (χ.1 ti * χ.1 tj / χ.1 1) * χ.1 g
  let S : Irr G → ℂ := fun χ => ∑ g : G, χ.1 g * star (φ g)
  have hfg (g : G) :
      (classSumPairCountMul (ConjClasses.mk ti) (ConjClasses.mk tj) g : ℂ) = c * X g := by
    calc
      (classSumPairCountMul (ConjClasses.mk ti) (ConjClasses.mk tj) g : ℂ)
          = ((Nat.card (ConjClasses.mk ti).carrier : ℂ) * (Nat.card (ConjClasses.mk tj).carrier : ℂ) /
              (Nat.card G : ℂ)) *
              ∑ χ : Irr G,
                (irrFamily G χ (ConjClasses.mk ti) * irrFamily G χ (ConjClasses.mk tj) /
                    irrFamily G χ (ConjClasses.mk 1)) * irrFamily G χ (ConjClasses.mk g) :=
              classSum_expansion_mul_of_involutions (ci := ConjClasses.mk ti) (cj := ConjClasses.mk tj)
                (ti := ti) (tj := tj) (hti := ConjClasses.mem_carrier_mk) (htj := ConjClasses.mem_carrier_mk)
                hti2 htj2 (χ := irrFamily G) (hχ := irrFamily_isComplete G) g
      _ = c * X g := by
              simp [c, X, irrFamily, toConjClassFunction_apply]
  calc
    scalarProduct G (fun g : G => (classSumPairCountMul (ConjClasses.mk ti) (ConjClasses.mk tj) g : ℂ)) φ
        = (Nat.card G : ℂ)⁻¹ * ∑ g : G,
            (classSumPairCountMul (ConjClasses.mk ti) (ConjClasses.mk tj) g : ℂ) * star (φ g) := rfl
    _ = (Nat.card G : ℂ)⁻¹ * ∑ g : G, (c * X g) * star (φ g) := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro g hg
            rw [hfg g]
    _ = c * ∑ χ : Irr G, (χ.1 ti * χ.1 tj / χ.1 1) * ((Nat.card G : ℂ)⁻¹ * S χ) := by
            have h1 : (Nat.card G : ℂ)⁻¹ * ∑ g : G, (c * X g) * star (φ g) =
                c * (Nat.card G : ℂ)⁻¹ * ∑ g : G, X g * star (φ g) := by
              calc
                (Nat.card G : ℂ)⁻¹ * ∑ g : G, (c * X g) * star (φ g)
                    = (Nat.card G : ℂ)⁻¹ * (c * ∑ g : G, X g * star (φ g)) := by
                        congr 1
                        calc
                          ∑ g : G, (c * X g) * star (φ g)
                              = ∑ g : G, c * (X g * star (φ g)) := by
                                  refine Finset.sum_congr rfl ?_
                                  intro g hg
                                  ring
                          _ = c * ∑ g : G, X g * star (φ g) := by
                                  rw [← Finset.mul_sum]
                _ = c * (Nat.card G : ℂ)⁻¹ * ∑ g : G, X g * star (φ g) := by
                        ring
            have h2 : ∑ g : G, X g * star (φ g) =
                ∑ χ : Irr G, (χ.1 ti * χ.1 tj / χ.1 1) * S χ := by
              calc
                ∑ g : G, (∑ χ : Irr G, (χ.1 ti * χ.1 tj / χ.1 1) * χ.1 g) * star (φ g)
                    = ∑ g : G, ∑ χ : Irr G, ((χ.1 ti * χ.1 tj / χ.1 1) * χ.1 g) * star (φ g) := by
                        refine Finset.sum_congr rfl ?_
                        intro g hg
                        dsimp [X]
                        rw [Finset.sum_mul]
                _ = ∑ χ : Irr G, ∑ g : G, ((χ.1 ti * χ.1 tj / χ.1 1) * χ.1 g) * star (φ g) := by
                        rw [Finset.sum_comm]
                _ = ∑ χ : Irr G, (χ.1 ti * χ.1 tj / χ.1 1) * ∑ g : G, χ.1 g * star (φ g) := by
                        refine Finset.sum_congr rfl ?_
                        intro χ hχ
                        rw [Finset.mul_sum]
                        refine Finset.sum_congr rfl ?_
                        intro g hg
                        ring
            calc
              (Nat.card G : ℂ)⁻¹ * ∑ g : G, (c * X g) * star (φ g)
                  = c * (Nat.card G : ℂ)⁻¹ * ∑ g : G, X g * star (φ g) := h1
              _ = c * ((Nat.card G : ℂ)⁻¹ * (∑ χ : Irr G, (χ.1 ti * χ.1 tj / χ.1 1) * S χ)) := by
                      rw [h2]
                      ring
              _ = c * (∑ χ : Irr G, (χ.1 ti * χ.1 tj / χ.1 1) * ((Nat.card G : ℂ)⁻¹ * S χ)) := by
                      congr 1
                      rw [Finset.mul_sum]
                      refine Finset.sum_congr rfl ?_
                      intro χ hχ
                      ring
    _ = ((Nat.card (ConjClasses.mk ti).carrier : ℂ) * (Nat.card (ConjClasses.mk tj).carrier : ℂ) /
          (Nat.card G : ℂ)) *
        ∑ χ : Irr G, (χ.1 ti * χ.1 tj / χ.1 1) * scalarProduct G χ.1 φ := by
          congr 1

/-- The paper's `f`: the pair count for the class of the involution `t`
(`classSumPairCount (mk t) = classSumPairCountMul (mk t) (mk t)`). -/
private noncomputable def lemma_2_2_f (c : Hyp11 G) : ClassFunction G :=
  fun g => (classSumPairCountMul (ConjClasses.mk c.t) (ConjClasses.mk c.t) g : ℂ)

/-- The left side of Lemma 2.2, the paper's `V`:
`|G:H|·Σ_{χ∈Irr(G)} χ(t)²/χ(1)·(χ,(μ−ν)*)_G`. -/
@[expose] public noncomputable def lemma_2_2_V (c : Hyp11 G) (μ ν : ClassFunction (↥c.H0)) : ℂ :=
  (c.H.index : ℂ) * ∑ χ : Irr G,
    (χ.1 c.t ^ 2 / χ.1 1) * scalarProduct G χ.1 (inducedClassFunction c.H0 (μ - ν))

/-- `V = |H|·(f, δ*)_G` with `δ* = (μ − ν)*` — the left side of Lemma 2.2
through the pair count `f`. -/
private lemma lemma_2_2_V_eq (c : Hyp11 G) (μ ν : ClassFunction (↥c.H0)) :
    lemma_2_2_V c μ ν =
      (Nat.card (↥c.H) : ℂ) * scalarProduct G (lemma_2_2_f c)
        (inducedClassFunction c.H0 (μ - ν)) := by
  classical
  have ht2 : c.t * c.t = 1 := by simpa [pow_two] using c.t_involution.2
  have hcard : Nat.card (ConjClasses.mk c.t).carrier = c.H.index := card_t_class_eq_H_index c
  have ha_ne : (Nat.card (ConjClasses.mk c.t).carrier : ℂ) ≠ 0 := by
    have : Nonempty (ConjClasses.mk c.t).carrier := ⟨⟨c.t, ConjClasses.mem_carrier_mk⟩⟩
    exact_mod_cast (Nat.card_pos (α := (ConjClasses.mk c.t).carrier)).ne'
  have hG_ne : (Nat.card G : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := G)).ne'
  have hsum :
      ∑ χ : Irr G, (χ.1 c.t ^ 2 / χ.1 1) * scalarProduct G χ.1 (inducedClassFunction c.H0 (μ - ν)) =
        ((Nat.card G : ℂ) / (Nat.card (ConjClasses.mk c.t).carrier : ℂ) ^ 2) *
          scalarProduct G (lemma_2_2_f c) (inducedClassFunction c.H0 (μ - ν)) := by
    have h'' : scalarProduct G (lemma_2_2_f c) (inducedClassFunction c.H0 (μ - ν)) =
        ((Nat.card (ConjClasses.mk c.t).carrier : ℂ) ^ 2 / (Nat.card G : ℂ)) *
          ∑ χ : Irr G, (χ.1 c.t ^ 2 / χ.1 1) *
            scalarProduct G χ.1 (inducedClassFunction c.H0 (μ - ν)) := by
      change scalarProduct G (fun g : G =>
          (classSumPairCountMul (ConjClasses.mk c.t) (ConjClasses.mk c.t) g : ℂ))
          (inducedClassFunction c.H0 (μ - ν)) =
        ((Nat.card (ConjClasses.mk c.t).carrier : ℂ) ^ 2 / (Nat.card G : ℂ)) *
          ∑ χ : Irr G, (χ.1 c.t ^ 2 / χ.1 1) *
            scalarProduct G χ.1 (inducedClassFunction c.H0 (μ - ν))
      simpa [pow_two, mul_assoc] using
        (scalarProduct_classSumPairCountMul_involutions (ti := c.t) (tj := c.t) ht2 ht2
          (inducedClassFunction c.H0 (μ - ν)))
    rw [h'']
    field_simp [ha_ne, hG_ne]
  unfold lemma_2_2_V
  rw [hsum]
  have hcard' : (Nat.card (ConjClasses.mk c.t).carrier : ℂ) = (c.H.index : ℂ) := by
    exact_mod_cast hcard
  have hG : (c.H.index : ℂ) * (Nat.card (↥c.H) : ℂ) = (Nat.card G : ℂ) := by
    exact_mod_cast (Subgroup.index_mul_card c.H)
  have hpos : (c.H.index : ℂ) ≠ 0 := by
    have hGpos : 0 < Nat.card G := Nat.card_pos (α := G)
    have hpos' : c.H.index ≠ 0 := by
      intro h0
      have hG : c.H.index * Nat.card (↥c.H) = Nat.card G := Subgroup.index_mul_card c.H
      have : 0 < c.H.index * Nat.card (↥c.H) := by
        rw [hG]
        exact hGpos
      rw [h0] at this
      simp at this
    exact_mod_cast hpos'
  rw [hcard']
  field_simp [hpos]
  rw [← hG]
  ring

/-- The scalar product is invariant under group isomorphisms. -/
private lemma scalarProduct_equiv_invariance {G H : Type u} [Group G] [Group H]
    [Fintype G] [Fintype H] (e : G ≃* H) (φ ψ : ClassFunction H) :
    scalarProduct H φ ψ = scalarProduct G (fun g : G => φ (e g)) (fun g : G => ψ (e g)) := by
  classical
  unfold scalarProduct
  have hcard : (Nat.card H : ℂ)⁻¹ = (Nat.card G : ℂ)⁻¹ := by
    congr 1
    exact congrArg (fun n : ℕ => (n : ℂ)) (Nat.card_congr e.toEquiv.symm)
  rw [hcard]
  have hsum : (∑ h : H, φ h * star (ψ h)) = (∑ g : G, φ (e g) * star (ψ (e g))) := by
    exact (Equiv.sum_comp e.toEquiv (fun y : H => φ y * star (ψ y))).symm
  rw [hsum]

/-- The identification `H0.subgroupOf H ≃ H0`. -/
private noncomputable def H0_subgroupOf_equiv (c : Hyp11 G) (h12 : Hyp12 c) :
    ↥(c.H0.subgroupOf c.H) ≃* ↥c.H0 where
  toFun x := ⟨(x : G), Subgroup.mem_subgroupOf.mp x.2⟩
  invFun y := ⟨⟨(y : G), (h12.H0_normal_in_H).1 y.2⟩, by
    rw [Subgroup.mem_subgroupOf]
    exact y.2⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv y := by
    apply Subtype.ext
    rfl
  map_mul' x y := by
    apply Subtype.ext
    rfl

/-- `f_ij` (on `H`): the pair count for the classes of the involutions
`tH i`, `tH j` of `H`. -/
private noncomputable def lemma_2_2_fij (c : Hyp11 G) (i j : Fin 2) : ClassFunction (↥c.H) :=
  fun g => (classSumPairCountMul (ConjClasses.mk (lemma_2_2_tH c i)) (ConjClasses.mk (lemma_2_2_tH c j)) g : ℂ)

/-- `fSum = Σ_{i,j} f_ij` (on `H`). -/
private noncomputable def lemma_2_2_fSum (c : Hyp11 G) : ClassFunction (↥c.H) :=
  fun g => ∑ i : Fin 2, ∑ j : Fin 2, lemma_2_2_fij c i j g

/-- `δ = μ^H − ν^H` (on `H`). -/
private noncomputable def lemma_2_2_delta (c : Hyp11 G) (h12 : Hyp12 c)
    (μ ν : ClassFunction (↥c.H0)) : ClassFunction (↥c.H) :=
  inducedFromSub (h12.H0_normal_in_H).1 (μ - ν)

/-- The paper's `W = |H|·(Σ f_ij, δ)_H`. -/
private noncomputable def lemma_2_2_W (c : Hyp11 G) (δ : ClassFunction (↥c.H)) : ℂ :=
  (Nat.card (↥c.H) : ℂ) * scalarProduct (↥c.H) (lemma_2_2_fSum c) δ

/-- `c(θ) = (k1·θ(t1) + k2·θ(t2))²/θ(1)`, the coefficient of `(θ, δ)_H` in
the paper's `W`. -/
private noncomputable def lemma_2_2_cθ (c : Hyp11 G) (θ : ClassFunction (↥c.H)) : ℂ :=
  ((c.k1 : ℂ) * θ (lemma_2_2_tH c 0) + (c.k2 : ℂ) * θ (lemma_2_2_tH c 1)) ^ 2 / θ 1

/-- The inner product of `φ` and `δ` depends only on the values of `φ` on
the support of `δ`. -/
private lemma scalarProduct_eq_of_eq_on_supported {G : Type u} [Group G] [Fintype G]
    {φ ψ δ : ClassFunction G} (h : ∀ g : G, δ g ≠ 0 → φ g = ψ g) :
    scalarProduct G φ δ = scalarProduct G ψ δ := by
  classical
  unfold scalarProduct
  congr 1
  refine Finset.sum_congr rfl ?_
  intro g hg
  by_cases hδ : δ g = 0
  · rw [hδ]
    simp
  · rw [h g hδ]

/-- The paper's `f` is a class function. -/
private lemma lemma_2_2_f_isClassFunction (c : Hyp11 G) :
    IsClassFunction (lemma_2_2_f c) := by
  unfold lemma_2_2_f
  exact classSumPairCountMul_isClassFunction (ConjClasses.mk c.t) (ConjClasses.mk c.t)

/-- Its restriction to `H` is a class function. -/
private lemma lemma_2_2_f_restrict_isClassFunction (c : Hyp11 G) :
    IsClassFunction (fun x : ↥c.H => lemma_2_2_f c (x : G)) := by
  intro x g
  change lemma_2_2_f c ((g : G) * (x : G) * (g : G)⁻¹) = lemma_2_2_f c (x : G)
  exact lemma_2_2_f_isClassFunction c (x : G) (g : G)

/-- Every element of `t^G` is an involution. -/
private lemma tG_mem_involution (c : Hyp11 G) {z : G} (hz : z ∈ (ConjClasses.mk c.t).carrier) :
    IsInvolution z := by
  classical
  have hconj : IsConj z c.t :=
    ConjClasses.mk_eq_mk_iff_isConj.mp ((ConjClasses.mem_carrier_iff_mk_eq).mp hz)
  rcases (isConj_iff.mp hconj) with ⟨g, hg⟩
  have hzeq : z = g⁻¹ * c.t * g := by
    calc
      z = g⁻¹ * (g * z * g⁻¹) * g := by group
      _ = g⁻¹ * c.t * g := by rw [hg]
  have ht2 : c.t * c.t = 1 := by simpa [pow_two] using c.t_involution.2
  constructor
  · intro hz1
    apply c.t_involution.1
    calc
      c.t = g * z * g⁻¹ := hg.symm
      _ = g * 1 * g⁻¹ := by rw [hz1]
      _ = 1 := by simp
  · change z ^ 2 = 1
    calc
      z ^ 2 = (g⁻¹ * c.t * g) ^ 2 := by rw [hzeq]
      _ = (g⁻¹ * c.t * g) * (g⁻¹ * c.t * g) := by rw [pow_two]
      _ = g⁻¹ * (c.t * c.t) * g := by group
      _ = 1 := by simp [ht2]

/-- `t_i^H ⊆ t^G`: the `H`-class of `tH i` lies in the `G`-class of `t`
(`G` has exactly one class of involutions). -/
private lemma tH_class_subset_tG (c : Hyp11 G) {i : Fin 2} {z : ↥c.H}
    (hz : z ∈ (ConjClasses.mk (lemma_2_2_tH c i)).carrier) :
    (z : G) ∈ (ConjClasses.mk c.t).carrier := by
  classical
  have hzconj : IsConj (z : ↥c.H) (lemma_2_2_tH c i) :=
    ConjClasses.mk_eq_mk_iff_isConj.mp ((ConjClasses.mem_carrier_iff_mk_eq).mp hz)
  have hzconjG : IsConj (z : G) ((lemma_2_2_tH c i : ↥c.H) : G) := by
    rcases (isConj_iff.mp hzconj) with ⟨h, hh⟩
    exact (isConj_iff.mpr ⟨(h : G), by simpa using (congrArg (fun w : ↥c.H => (w : G)) hh)⟩)
  have hti : IsInvolution (lemma_2_2_tH c i : G) := by
    fin_cases i
    · simpa [lemma_2_2_tH] using c.t1_involution
    · simpa [lemma_2_2_tH] using c.t2_involution
  have hz2 : (z : G) * (z : G) = 1 := by
    rcases (isConj_iff.mp hzconjG) with ⟨h, hh⟩
    have hzEq : (z : G) = h⁻¹ * (lemma_2_2_tH c i : G) * h := by
      calc
        (z : G) = h⁻¹ * (h * (z : G) * h⁻¹) * h := by group
        _ = h⁻¹ * (lemma_2_2_tH c i : G) * h := by rw [hh]
    have ht2 : (lemma_2_2_tH c i : G) * (lemma_2_2_tH c i : G) = 1 := by
      simpa [pow_two] using hti.2
    calc
      (z : G) * (z : G) = (h⁻¹ * (lemma_2_2_tH c i : G) * h) * (h⁻¹ * (lemma_2_2_tH c i : G) * h) := by rw [hzEq]
      _ = h⁻¹ * ((lemma_2_2_tH c i : G) * (lemma_2_2_tH c i : G)) * h := by group
      _ = 1 := by simp [ht2]
  have hzconjT : IsConj (z : G) c.t := by
    rcases (isConj_iff.mp hzconjG) with ⟨h, hh⟩
    rcases (c.one_involution_class (lemma_2_2_tH c i : G) c.t hti c.t_involution) with ⟨w, hw⟩
    exact (isConj_iff.mpr ⟨w * h, by
      calc
        (w * h) * (z : G) * (w * h)⁻¹ = w * (h * (z : G) * h⁻¹) * w⁻¹ := by group
        _ = w * (lemma_2_2_tH c i : G) * w⁻¹ := by rw [hh]
        _ = c.t := hw⟩)
  exact ConjClasses.mem_carrier_iff_mk_eq.mpr (ConjClasses.mk_eq_mk_iff_isConj.mpr hzconjT)

/-- `tH 0 = t1` (as an element of `H`). -/
private lemma lemma_2_2_tH_zero (c : Hyp11 G) : lemma_2_2_tH c 0 = ⟨c.t1, t1_mem_H c⟩ := by
  simp [lemma_2_2_tH]

/-- `tH 1 = t2` (as an element of `H`). -/
private lemma lemma_2_2_tH_one (c : Hyp11 G) : lemma_2_2_tH c 1 = ⟨c.t2, t2_mem_H c⟩ := by
  simp [lemma_2_2_tH]

/-- The two `H`-classes `t1^H`, `t2^H` are disjoint. -/
private lemma tH_carrier_disjoint (c : Hyp11 G) (h12 : Hyp12 c) :
    (ConjClasses.mk (lemma_2_2_tH c 0)).carrier ∩ (ConjClasses.mk (lemma_2_2_tH c 1)).carrier = ∅ := by
  simpa [lemma_2_2_tH_zero, lemma_2_2_tH_one] using t1H_disjoint c h12

/-- The carriers of distinct `t_i^H`, `t_j^H` are disjoint. -/
private lemma tH_carrier_disjoint' (c : Hyp11 G) (h12 : Hyp12 c) {i j : Fin 2} (hij : i ≠ j) :
    (ConjClasses.mk (lemma_2_2_tH c i)).carrier ∩ (ConjClasses.mk (lemma_2_2_tH c j)).carrier = ∅ := by
  fin_cases i <;> fin_cases j
  · exact False.elim (hij rfl)
  · exact tH_carrier_disjoint c h12
  · rw [Set.inter_comm]
    exact tH_carrier_disjoint c h12
  · exact False.elim (hij rfl)

/-- An element of `H` lying in both `t_i^H` and `t_j^H` forces `i = j`. -/
private lemma tH_class_unique (c : Hyp11 G) (h12 : Hyp12 c) {i j : Fin 2}
    {z : ↥c.H} (hzi : z ∈ (ConjClasses.mk (lemma_2_2_tH c i)).carrier)
    (hzj : z ∈ (ConjClasses.mk (lemma_2_2_tH c j)).carrier) : i = j := by
  by_contra hij
  have hdisj := tH_carrier_disjoint' c h12 hij
  have hz : z ∈ (ConjClasses.mk (lemma_2_2_tH c i)).carrier ∩
      (ConjClasses.mk (lemma_2_2_tH c j)).carrier := ⟨hzi, hzj⟩
  rw [hdisj] at hz
  simpa using hz

set_option backward.isDefEq.respectTransparency false in
/-- For involutions `x, y` with `x·y = g ∈ T`, the TI property of `T` gives
`x ∈ N_G(T) = H`. -/
private lemma pair_in_normalizer_T (c : Hyp11 G) (h12 : Hyp12 c)
    {x y : G} (hx2 : x * x = 1) (hy2 : y * y = 1) {g : G} (hg : g ∈ c.T) (hxy : x * y = g) :
    x ∈ c.H := by
  classical
  have hxinv' : x⁻¹ = x := (inv_eq_iff_mul_eq_one).mpr hx2
  have hyinv' : y⁻¹ = y := (inv_eq_iff_mul_eq_one).mpr hy2
  have hg' : g⁻¹ ∈ c.T := by
    dsimp [Hyp11.T] at hg ⊢
    exact ⟨c.H0.inv_mem hg.1, by
      intro hginv
      apply hg.2
      exact (c.U.inv_mem_iff (x := g)).mp hginv⟩
  have hconj : x * g * x⁻¹ = g⁻¹ := by
    calc
      x * g * x⁻¹ = x * (x * y) * x⁻¹ := by rw [hxy]
      _ = (x * x) * (y * x⁻¹) := by group
      _ = y * x := by
        rw [hx2]
        simp
        rw [hxinv']
      _ = (x * y)⁻¹ := by rw [mul_inv_rev, hxinv', hyinv']
      _ = g⁻¹ := by rw [hxy]
  have himage : g⁻¹ ∈ (fun t : G => x * t * x⁻¹) '' c.T := by
    refine ⟨g, hg, hconj⟩
  have hTdisj : ¬ c.T ∩ (fun t : G => x * t * x⁻¹) '' c.T = ∅ := by
    intro h
    have hmem : g⁻¹ ∈ c.T ∩ (fun t : G => x * t * x⁻¹) '' c.T := ⟨hg', himage⟩
    rw [h] at hmem
    simpa using hmem
  have hTconj : (fun t : G => x * t * x⁻¹) '' c.T = c.T := by
    rcases (h12.T_is_TI x) with h | h
    · exact h
    · exfalso
      exact hTdisj h
  have hxN : x ∈ Subgroup.normalizer c.T := by
    rw [Subgroup.mem_normalizer_iff_conj_image_eq]
    simpa [MulAut.conj_apply] using hTconj
  rw [← h12.T_normalizer]
  exact hxN

/-- Involutions `x, y ∈ G` with `x·y = g ∈ T` lie in `H`, outside `H0`, and
are `H`-conjugate to `t1` or to `t2`. -/
private lemma pair_mem_T_in_H (c : Hyp11 G) (h12 : Hyp12 c)
    {x y : G} (hx : x ∈ (ConjClasses.mk c.t).carrier) (hy : y ∈ (ConjClasses.mk c.t).carrier)
    {g : G} (hg : g ∈ c.T) (hxy : x * y = g) :
    x ∈ c.H ∧ y ∈ c.H ∧ x ∉ c.H0 ∧ y ∉ c.H0 ∧
      ∃ i j : Fin 2, ∃ gx : G, gx ∈ c.H ∧ gx * x * gx⁻¹ = (lemma_2_2_tH c i : G) ∧
        ∃ gy : G, gy ∈ c.H ∧ gy * y * gy⁻¹ = (lemma_2_2_tH c j : G) := by
  classical
  have hx2 : x * x = 1 := by simpa [pow_two] using (tG_mem_involution c hx).2
  have hy2 : y * y = 1 := by simpa [pow_two] using (tG_mem_involution c hy).2
  have hxH : x ∈ c.H := pair_in_normalizer_T c h12 hx2 hy2 hg hxy
  have hg' : g⁻¹ ∈ c.T := by
    dsimp [Hyp11.T] at hg ⊢
    exact ⟨c.H0.inv_mem hg.1, by
      intro hginv
      apply hg.2
      exact (c.U.inv_mem_iff (x := g)).mp hginv⟩
  have hyx : y * x = g⁻¹ := by
    have hxinv' : x⁻¹ = x := (inv_eq_iff_mul_eq_one).mpr hx2
    have hyinv' : y⁻¹ = y := (inv_eq_iff_mul_eq_one).mpr hy2
    calc
      y * x = (x * y)⁻¹ := by rw [mul_inv_rev, hxinv', hyinv']
      _ = g⁻¹ := by rw [hxy]
  have hyH : y ∈ c.H := pair_in_normalizer_T c h12 hy2 hx2 hg' hyx
  have hxH0 : x ∉ c.H0 := by
    intro hx0
    have hxt : x = c.t := unique_involution_of_H0 c h12 x hx0 (by simpa [pow_two] using hx2) (tG_mem_involution c hx).1
    have hty : c.t * y ∈ c.H0 := by
      have hgH0 : x * y ∈ c.H0 := by simpa [hxy] using hg.1
      simpa [hxt] using hgH0
    have hy0 : y ∈ c.H0 := by
      have htin : c.t⁻¹ ∈ c.H0 := c.H0.inv_mem (S0_le_H0 c c.t_mem_S0)
      have htm : c.t⁻¹ * (c.t * y) = y := by group
      have hmul : c.t⁻¹ * (c.t * y) ∈ c.H0 := c.H0.mul_mem htin hty
      rwa [htm] at hmul
    have hyt : y = c.t := unique_involution_of_H0 c h12 y hy0 (by simpa [pow_two] using hy2) (tG_mem_involution c hy).1
    have hg1 : g = 1 := by
      calc
        g = x * y := hxy.symm
        _ = c.t * c.t := by rw [hxt, hyt]
        _ = 1 := by simpa [pow_two] using c.t_involution.2
    exact hg.2 (hg1 ▸ c.U.one_mem)
  have hyH0 : y ∉ c.H0 := by
    intro hy0
    have hyt : y = c.t := unique_involution_of_H0 c h12 y hy0 (by simpa [pow_two] using hy2) (tG_mem_involution c hy).1
    have htx : x * c.t ∈ c.H0 := by
      have hgH0 : x * y ∈ c.H0 := by simpa [hxy] using hg.1
      simpa [hyt] using hgH0
    have hx0' : x ∈ c.H0 := by
      have htin : c.t⁻¹ ∈ c.H0 := c.H0.inv_mem (S0_le_H0 c c.t_mem_S0)
      have htm : (x * c.t) * c.t⁻¹ = x := by group
      have hmul : (x * c.t) * c.t⁻¹ ∈ c.H0 := c.H0.mul_mem htx htin
      rwa [htm] at hmul
    exact hxH0 hx0'
  refine ⟨hxH, hyH, hxH0, hyH0, ?_⟩
  rcases (involution_H_not_H0_conj_to_t1_or_t2 c h12 hxH hx2 hxH0) with ⟨i, gx, hgxm, hgx⟩
  rcases (involution_H_not_H0_conj_to_t1_or_t2 c h12 hyH hy2 hyH0) with ⟨j, gy, hgym, hgy⟩
  exact ⟨i, j, gx, hgxm, hgx, gy, hgym, hgy⟩

/-- `x ∈ H` for a pair `x·y = g ∈ T` (from `pair_mem_T_in_H`). -/
private lemma pair_mem_T_x_mem_H (c : Hyp11 G) (h12 : Hyp12 c)
    {x y : G} (hx : x ∈ (ConjClasses.mk c.t).carrier) (hy : y ∈ (ConjClasses.mk c.t).carrier)
    {g : G} (hg : g ∈ c.T) (hxy : x * y = g) : x ∈ c.H :=
  (pair_mem_T_in_H c h12 hx hy hg hxy).1

/-- `y ∈ H` for a pair `x·y = g ∈ T` (from `pair_mem_T_in_H`). -/
private lemma pair_mem_T_y_mem_H (c : Hyp11 G) (h12 : Hyp12 c)
    {x y : G} (hx : x ∈ (ConjClasses.mk c.t).carrier) (hy : y ∈ (ConjClasses.mk c.t).carrier)
    {g : G} (hg : g ∈ c.T) (hxy : x * y = g) : y ∈ c.H :=
  (pair_mem_T_in_H c h12 hx hy hg hxy).2.1

/-- The index `i` with `x ∈ t_i^H` for a pair `x·y = g ∈ T`. -/
private noncomputable def pair_mem_T_i (c : Hyp11 G) (h12 : Hyp12 c)
    {x y : G} (hx : x ∈ (ConjClasses.mk c.t).carrier) (hy : y ∈ (ConjClasses.mk c.t).carrier)
    {g : G} (hg : g ∈ c.T) (hxy : x * y = g) : Fin 2 :=
  Classical.choose (pair_mem_T_in_H c h12 hx hy hg hxy).2.2.2.2

/-- The index `j` with `y ∈ t_j^H` for a pair `x·y = g ∈ T`. -/
private noncomputable def pair_mem_T_j (c : Hyp11 G) (h12 : Hyp12 c)
    {x y : G} (hx : x ∈ (ConjClasses.mk c.t).carrier) (hy : y ∈ (ConjClasses.mk c.t).carrier)
    {g : G} (hg : g ∈ c.T) (hxy : x * y = g) : Fin 2 :=
  Classical.choose (Classical.choose_spec (pair_mem_T_in_H c h12 hx hy hg hxy).2.2.2.2)

/-- The conjugating element for `x` (see `pair_mem_T_gx_spec`). -/
private noncomputable def pair_mem_T_gx (c : Hyp11 G) (h12 : Hyp12 c)
    {x y : G} (hx : x ∈ (ConjClasses.mk c.t).carrier) (hy : y ∈ (ConjClasses.mk c.t).carrier)
    {g : G} (hg : g ∈ c.T) (hxy : x * y = g) : G :=
  Classical.choose (Classical.choose_spec
    (Classical.choose_spec (pair_mem_T_in_H c h12 hx hy hg hxy).2.2.2.2))

/-- The specification of `pair_mem_T_gx`. -/
private lemma pair_mem_T_gx_spec (c : Hyp11 G) (h12 : Hyp12 c)
    {x y : G} (hx : x ∈ (ConjClasses.mk c.t).carrier) (hy : y ∈ (ConjClasses.mk c.t).carrier)
    {g : G} (hg : g ∈ c.T) (hxy : x * y = g) :
    pair_mem_T_gx c h12 hx hy hg hxy ∈ c.H ∧
      pair_mem_T_gx c h12 hx hy hg hxy * x * (pair_mem_T_gx c h12 hx hy hg hxy)⁻¹ =
        (lemma_2_2_tH c (pair_mem_T_i c h12 hx hy hg hxy) : G) ∧
      ∃ gy : G, gy ∈ c.H ∧ gy * y * gy⁻¹ = (lemma_2_2_tH c (pair_mem_T_j c h12 hx hy hg hxy) : G) :=
  Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (pair_mem_T_in_H c h12 hx hy hg hxy).2.2.2.2))

/-- The conjugating element for `y` (see `pair_mem_T_gy_spec`). -/
private noncomputable def pair_mem_T_gy (c : Hyp11 G) (h12 : Hyp12 c)
    {x y : G} (hx : x ∈ (ConjClasses.mk c.t).carrier) (hy : y ∈ (ConjClasses.mk c.t).carrier)
    {g : G} (hg : g ∈ c.T) (hxy : x * y = g) : G :=
  Classical.choose (pair_mem_T_gx_spec c h12 hx hy hg hxy).2.2

/-- The specification of `pair_mem_T_gy`. -/
private lemma pair_mem_T_gy_spec (c : Hyp11 G) (h12 : Hyp12 c)
    {x y : G} (hx : x ∈ (ConjClasses.mk c.t).carrier) (hy : y ∈ (ConjClasses.mk c.t).carrier)
    {g : G} (hg : g ∈ c.T) (hxy : x * y = g) :
    pair_mem_T_gy c h12 hx hy hg hxy ∈ c.H ∧
      pair_mem_T_gy c h12 hx hy hg hxy * y * (pair_mem_T_gy c h12 hx hy hg hxy)⁻¹ =
        (lemma_2_2_tH c (pair_mem_T_j c h12 hx hy hg hxy) : G) :=
  Classical.choose_spec (pair_mem_T_gx_spec c h12 hx hy hg hxy).2.2

/-- The pair count `classSumPairCountMul (mk t) (mk t)` is the cardinal of
the pair subtype. -/
private lemma pair_count_eq_card (c : Hyp11 G) (x : ↥c.H) :
    (classSumPairCountMul (ConjClasses.mk c.t) (ConjClasses.mk c.t) (x : G) : ℂ) =
      (Nat.card {p : (ConjClasses.mk c.t).carrier × (ConjClasses.mk c.t).carrier //
        p.1.1 * p.2.1 = (x : G)} : ℂ) := by
  rfl

/-- The pair count `classSumPairCountMul (mk (tH i)) (mk (tH j))` is the
cardinal of the pair subtype. -/
private lemma pair_count_eq_card' (c : Hyp11 G) (x : ↥c.H) (i j : Fin 2) :
    (classSumPairCountMul (ConjClasses.mk (lemma_2_2_tH c i))
        (ConjClasses.mk (lemma_2_2_tH c j)) x : ℂ) =
      (Nat.card {p : (ConjClasses.mk (lemma_2_2_tH c i)).carrier ×
          (ConjClasses.mk (lemma_2_2_tH c j)).carrier //
        p.1.1 * p.2.1 = x} : ℂ) := by
  rfl

/-- The carriers of `t_i^H` and `t_j^H` have disjoint images in `G`. -/
private lemma class_carrier_image_disjoint (c : Hyp11 G) (h12 : Hyp12 c) {i j : Fin 2}
    (hij : i ≠ j) :
    (fun w : ↥c.H => (w : G)) '' (ConjClasses.mk (lemma_2_2_tH c i)).carrier ∩
      (fun w : ↥c.H => (w : G)) '' (ConjClasses.mk (lemma_2_2_tH c j)).carrier = ∅ := by
  classical
  have hdisj : (ConjClasses.mk (lemma_2_2_tH c i)).carrier ∩
      (ConjClasses.mk (lemma_2_2_tH c j)).carrier = ∅ := tH_carrier_disjoint' c h12 hij
  ext y
  constructor
  · intro hy
    rcases hy with ⟨⟨w₁, hw₁, h₁⟩, ⟨w₂, hw₂, h₂⟩⟩
    have hw : w₁ = w₂ := Subtype.ext (h₁.trans h₂.symm)
    have hw₂' : w₁ ∈ (ConjClasses.mk (lemma_2_2_tH c j)).carrier := by
      simpa [hw] using hw₂
    have hmem' : w₁ ∈ (ConjClasses.mk (lemma_2_2_tH c i)).carrier ∩
        (ConjClasses.mk (lemma_2_2_tH c j)).carrier := ⟨hw₁, hw₂'⟩
    simp [hdisj] at hmem'
  · intro hy
    exact False.elim hy

/-- For a pair `y·z = x ∈ T` with `y, z ∈ t^G`, both `y` and `z` lie in one of
the two `H`-classes `t_0^H`, `t_1^H` (they lie in `H`, outside `H0`, by the TI
property, and every involution of `H − H0` is conjugate to `t1` or `t2`). -/
private lemma pair_fiber_class_mem (c : Hyp11 G) (h12 : Hyp12 c) {x : ↥c.H}
    {y z : G} (hx : (x : G) ∈ c.T) (hyT : y ∈ (ConjClasses.mk c.t).carrier)
    (hzT : z ∈ (ConjClasses.mk c.t).carrier) (hyz : y * z = (x : G)) :
    y ∈ (fun w : ↥c.H => (w : G)) '' (ConjClasses.mk (lemma_2_2_tH c 0)).carrier ∪
        (fun w : ↥c.H => (w : G)) '' (ConjClasses.mk (lemma_2_2_tH c 1)).carrier ∧
    z ∈ (fun w : ↥c.H => (w : G)) '' (ConjClasses.mk (lemma_2_2_tH c 0)).carrier ∪
        (fun w : ↥c.H => (w : G)) '' (ConjClasses.mk (lemma_2_2_tH c 1)).carrier := by
  classical
  have hyzH := pair_mem_T_in_H c h12 hyT hzT hx hyz
  have hy2 : y * y = 1 := by simpa [pow_two] using (tG_mem_involution c hyT).2
  have hz2 : z * z = 1 := by simpa [pow_two] using (tG_mem_involution c hzT).2
  have hyC : y ∈ (fun w : ↥c.H => (w : G)) '' (ConjClasses.mk (lemma_2_2_tH c 0)).carrier ∪
      (fun w : ↥c.H => (w : G)) '' (ConjClasses.mk (lemma_2_2_tH c 1)).carrier := by
    rcases (involution_H_not_H0_conj_to_t1_or_t2 c h12 hyzH.1 hy2 hyzH.2.2.1) with ⟨i, g, hg, hgi⟩
    fin_cases i
    · apply Or.inl
      refine ⟨⟨y, hyzH.1⟩, ?_, rfl⟩
      rw [ConjClasses.mem_carrier_iff_mk_eq]
      rw [ConjClasses.mk_eq_mk_iff_isConj]
      refine (isConj_iff.mpr ⟨⟨g, hg⟩, ?_⟩)
      apply Subtype.ext
      exact hgi
    · apply Or.inr
      refine ⟨⟨y, hyzH.1⟩, ?_, rfl⟩
      rw [ConjClasses.mem_carrier_iff_mk_eq]
      rw [ConjClasses.mk_eq_mk_iff_isConj]
      refine (isConj_iff.mpr ⟨⟨g, hg⟩, ?_⟩)
      apply Subtype.ext
      exact hgi
  have hzC : z ∈ (fun w : ↥c.H => (w : G)) '' (ConjClasses.mk (lemma_2_2_tH c 0)).carrier ∪
      (fun w : ↥c.H => (w : G)) '' (ConjClasses.mk (lemma_2_2_tH c 1)).carrier := by
    rcases (involution_H_not_H0_conj_to_t1_or_t2 c h12 hyzH.2.1 hz2 hyzH.2.2.2.1) with ⟨i, g, hg, hgi⟩
    fin_cases i
    · apply Or.inl
      refine ⟨⟨z, hyzH.2.1⟩, ?_, rfl⟩
      rw [ConjClasses.mem_carrier_iff_mk_eq]
      rw [ConjClasses.mk_eq_mk_iff_isConj]
      refine (isConj_iff.mpr ⟨⟨g, hg⟩, ?_⟩)
      apply Subtype.ext
      exact hgi
    · apply Or.inr
      refine ⟨⟨z, hyzH.2.1⟩, ?_, rfl⟩
      rw [ConjClasses.mem_carrier_iff_mk_eq]
      rw [ConjClasses.mk_eq_mk_iff_isConj]
      refine (isConj_iff.mpr ⟨⟨g, hg⟩, ?_⟩)
      apply Subtype.ext
      exact hgi
  exact ⟨hyC, hzC⟩

/-- The class subtype `{w : G // w ∈ t_i^H}` is in bijection with the class
carrier `{w : ↥c.H // w ∈ t_i^H}`. -/
private noncomputable def class_image_equiv (c : Hyp11 G) (i : Fin 2) :
    {w : G // w ∈ (fun w : ↥c.H => (w : G)) '' (ConjClasses.mk (lemma_2_2_tH c i)).carrier} ≃
      {w : ↥c.H // w ∈ (ConjClasses.mk (lemma_2_2_tH c i)).carrier} := by
  classical
  let invFun : {w : ↥c.H // w ∈ (ConjClasses.mk (lemma_2_2_tH c i)).carrier} →
      {w : G // w ∈ (fun w : ↥c.H => (w : G)) '' (ConjClasses.mk (lemma_2_2_tH c i)).carrier} := fun w => by
    refine ⟨(w : G), ?_⟩
    rw [Set.mem_image]
    exact ⟨w, w.2, rfl⟩
  refine
    { toFun := fun y => ⟨Classical.choose y.2, (Classical.choose_spec y.2).1⟩
      invFun := invFun
      left_inv := fun y => by
        apply Subtype.ext
        exact (Classical.choose_spec y.2).2
      right_inv := fun w => by
        apply Subtype.ext
        apply Subtype.ext
        exact (Classical.choose_spec (invFun w).2).2 }

/-- Splitting a sum over `G` into the sums over the two `H`-classes (all terms
outside the classes vanish). -/
private lemma two_class_sum_split (c : Hyp11 G) (h12 : Hyp12 c) {ψ : G → ℂ}
    (hvanish : ∀ y : G,
      y ∉ (fun w : ↥c.H => (w : G)) '' (ConjClasses.mk (lemma_2_2_tH c 0)).carrier ∪
        (fun w : ↥c.H => (w : G)) '' (ConjClasses.mk (lemma_2_2_tH c 1)).carrier → ψ y = 0) :
    (∑ y : G, ψ y) =
      ∑ i : Fin 2, ∑ y : {w : ↥c.H // w ∈ (ConjClasses.mk (lemma_2_2_tH c i)).carrier}, ψ (y : G) := by
  classical
  let C : Fin 2 → Set G := fun i => (fun w : ↥c.H => (w : G)) '' (ConjClasses.mk (lemma_2_2_tH c i)).carrier
  have hpt : ∀ y : G, ψ y = ∑ i : Fin 2, if y ∈ C i then ψ y else 0 := by
    intro y
    by_cases hy0 : y ∈ C 0
    · have hy1 : y ∉ C 1 := by
        intro hy1
        have hdisj := class_carrier_image_disjoint c h12 (by decide : (0 : Fin 2) ≠ 1)
        have hmem' : y ∈ C 0 ∩ C 1 := ⟨hy0, hy1⟩
        simp [C, hdisj] at hmem'
      rw [Fin.sum_univ_two]
      simp [hy0, hy1]
    · by_cases hy1 : y ∈ C 1
      · have hy0' : y ∉ C 0 := by
          intro hy0'
          have hdisj := class_carrier_image_disjoint c h12 (by decide : (0 : Fin 2) ≠ 1)
          have hmem' : y ∈ C 0 ∩ C 1 := ⟨hy0', hy1⟩
          simp [C, hdisj] at hmem'
        rw [Fin.sum_univ_two]
        simp [hy0, hy1]
      · have hψ : ψ y = 0 := hvanish y (by simp [C, hy0, hy1])
        rw [Fin.sum_univ_two]
        simp [hy0, hy1, hψ]
  calc
    (∑ y : G, ψ y) = ∑ y : G, ∑ i : Fin 2, if y ∈ C i then ψ y else 0 := by
      apply Finset.sum_congr rfl
      intro y hy
      exact hpt y
    _ = ∑ i : Fin 2, ∑ y : G, if y ∈ C i then ψ y else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ i : Fin 2, ∑ y : {w : G // w ∈ C i}, ψ (y : G) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.sum_filter]
      rw [← Finset.sum_subtype_eq_sum_filter]
      simp [C]
    _ = ∑ i : Fin 2, ∑ y : {w : ↥c.H // w ∈ (ConjClasses.mk (lemma_2_2_tH c i)).carrier}, ψ (y : G) := by
      apply Finset.sum_congr rfl
      intro i hi
      -- the image subtype is in bijection with the class carrier
      symm
      exact Fintype.sum_equiv (class_image_equiv c i).symm
        (fun y : {w : ↥c.H // w ∈ (ConjClasses.mk (lemma_2_2_tH c i)).carrier} => ψ (y : G))
        (fun x : {w : G // w ∈ C i} => ψ (x : G))
        (fun y => by
          congr 1)

/-- The pairs with product `x` in `t_i^H × t_j^H` are in bijection with the
pairs in `t^G × t^G` whose ambient elements lie in `t_i^H`, `t_j^H`. -/
private lemma class_pair_cell (c : Hyp11 G) (h12 : Hyp12 c) {x : ↥c.H} (i j : Fin 2) :
    (∑ y : {w : ↥c.H // w ∈ (ConjClasses.mk (lemma_2_2_tH c i)).carrier},
      ∑ z : {w : ↥c.H // w ∈ (ConjClasses.mk (lemma_2_2_tH c j)).carrier},
        (Nat.card {p : (ConjClasses.mk c.t).carrier × (ConjClasses.mk c.t).carrier //
          (p.1.1 : G) = (y : G) ∧ (p.2.1 : G) = (z : G) ∧ p.1.1 * p.2.1 = (x : G)} : ℂ)) =
    (Nat.card {p : (ConjClasses.mk (lemma_2_2_tH c i)).carrier ×
        (ConjClasses.mk (lemma_2_2_tH c j)).carrier //
      p.1.1 * p.2.1 = x} : ℂ) := by
  classical
  let B : G → G → Type u := fun y z =>
    {p : (ConjClasses.mk c.t).carrier × (ConjClasses.mk c.t).carrier //
      (p.1.1 : G) = y ∧ (p.2.1 : G) = z ∧ p.1.1 * p.2.1 = (x : G)}
  let T : Type u := Σ y : {w : ↥c.H // w ∈ (ConjClasses.mk (lemma_2_2_tH c i)).carrier},
    Σ z : {w : ↥c.H // w ∈ (ConjClasses.mk (lemma_2_2_tH c j)).carrier}, B (y : G) (z : G)
  let BC : Type u := {p : (ConjClasses.mk (lemma_2_2_tH c i)).carrier ×
      (ConjClasses.mk (lemma_2_2_tH c j)).carrier // p.1.1 * p.2.1 = x}
  let toFun : T → BC := fun q => by
    cases q with
    | mk y q2 =>
      cases q2 with
      | mk z fp =>
        have h₁ : (fp.1.1.val : G) = (y : G) := fp.2.1
        have h₂ : (fp.1.2.val : G) = (z : G) := fp.2.2.1
        have h₃ : fp.1.1.val * fp.1.2.val = (x : G) := fp.2.2.2
        exact ⟨(⟨y.1, y.2⟩, ⟨z.1, z.2⟩), by
          apply Subtype.ext
          change (y.1 : G) * (z.1 : G) = (x : G)
          calc
            (y.1 : G) * (z.1 : G) = (fp.1.1.val : G) * (fp.1.2.val : G) := by rw [h₁, h₂]
            _ = (x : G) := h₃⟩
  let invFun : BC → T := fun p => by
    refine ⟨⟨p.1.1.1, p.1.1.2⟩, ⟨⟨p.1.2.1, p.1.2.2⟩, ?_⟩⟩
    refine ⟨(⟨p.1.1.1, tH_class_subset_tG c p.1.1.2⟩, ⟨p.1.2.1, tH_class_subset_tG c p.1.2.2⟩), ?_⟩
    refine ⟨rfl, ?_⟩
    refine ⟨rfl, ?_⟩
    change (p.1.1.1 : G) * (p.1.2.1 : G) = (x : G)
    exact congrArg (fun w : ↥c.H => (w : G)) p.2
  let e : T ≃ BC :=
    { toFun := toFun
      invFun := invFun
      left_inv := fun q => by
        cases q with
        | mk y q2 =>
          cases q2 with
          | mk z fp =>
            apply Sigma.ext
            · rfl
            · apply heq_of_eq
              apply Sigma.ext
              · rfl
              · apply heq_of_eq
                apply Subtype.ext
                · apply Prod.ext
                  · apply Subtype.ext
                    · exact fp.2.1.symm
                  · apply Subtype.ext
                    · exact fp.2.2.1.symm
      right_inv := fun p => by
        apply Subtype.ext
        · rfl }
  calc
    (∑ y : {w : ↥c.H // w ∈ (ConjClasses.mk (lemma_2_2_tH c i)).carrier},
      ∑ z : {w : ↥c.H // w ∈ (ConjClasses.mk (lemma_2_2_tH c j)).carrier},
        (Nat.card (B (y : G) (z : G)) : ℂ))
        = (Nat.card T : ℂ) := by
      dsimp [T]
      rw [Nat.card_eq_fintype_card]
      simp [Fintype.card_sigma, Nat.cast_sum]
    _ = (Nat.card BC : ℂ) := by
      congr 1
      exact Nat.card_congr e

/-- The class-indexed pair counts in `t_i^H × t_j^H` with product `x` sum to
the element-indexed pair count in `t^G × t^G` with product `x` (for `x ∈ T`):
every pair with product in `T` lies in `H` outside `H0`, hence in one of the
two classes `t_i^H` (the vanish of the off-class terms and the disjointness of
the classes split the sum). -/
private lemma class_pair_sum_decomp (c : Hyp11 G) (h12 : Hyp12 c)
    {x : ↥c.H} (hx : (x : G) ∈ c.T) :
    (∑ y : G, ∑ z : G,
      (Nat.card {p : (ConjClasses.mk c.t).carrier × (ConjClasses.mk c.t).carrier //
        (p.1.1 : G) = y ∧ (p.2.1 : G) = z ∧ p.1.1 * p.2.1 = (x : G)} : ℂ)) =
    ∑ i : Fin 2, ∑ j : Fin 2,
      (Nat.card {p : (ConjClasses.mk (lemma_2_2_tH c i)).carrier ×
          (ConjClasses.mk (lemma_2_2_tH c j)).carrier //
        p.1.1 * p.2.1 = x} : ℂ) := by
  classical
  let B : G → G → Type u := fun y z =>
    {p : (ConjClasses.mk c.t).carrier × (ConjClasses.mk c.t).carrier //
      (p.1.1 : G) = y ∧ (p.2.1 : G) = z ∧ p.1.1 * p.2.1 = (x : G)}
  let C : Fin 2 → Set G := fun i =>
    (fun w : ↥c.H => (w : G)) '' (ConjClasses.mk (lemma_2_2_tH c i)).carrier
  have hvanish_y : ∀ y : G, y ∉ C 0 ∪ C 1 →
      (∑ z : G, (Nat.card (B y z) : ℂ)) = 0 := by
    intro y hyC
    apply Finset.sum_eq_zero
    intro z hz
    have : IsEmpty (B y z) := by
      refine ⟨fun p => ?_⟩
      have hyC' : y ∈ C 0 ∪ C 1 := by
        simpa [C, p.2.1] using (pair_fiber_class_mem c h12 hx p.1.1.2 p.1.2.2 p.2.2.2).1
      exact hyC hyC'
    simp
  have hvanish_z : ∀ i : Fin 2, ∀ z : G, z ∉ C 0 ∪ C 1 →
      (∑ y : {w : ↥c.H // w ∈ (ConjClasses.mk (lemma_2_2_tH c i)).carrier},
        (Nat.card (B (y : G) z) : ℂ)) = 0 := by
    intro i z hzC
    apply Finset.sum_eq_zero
    intro y hy
    have : IsEmpty (B (y : G) z) := by
      refine ⟨fun p => ?_⟩
      have hzC' : z ∈ C 0 ∪ C 1 := by
        simpa [C, p.2.2.1] using (pair_fiber_class_mem c h12 hx p.1.1.2 p.1.2.2 p.2.2.2).2
      exact hzC hzC'
    simp
  calc
    (∑ y : G, ∑ z : G,
      (Nat.card {p : (ConjClasses.mk c.t).carrier × (ConjClasses.mk c.t).carrier //
        (p.1.1 : G) = y ∧ (p.2.1 : G) = z ∧ p.1.1 * p.2.1 = (x : G)} : ℂ))
        = ∑ y : G, ∑ z : G, (Nat.card (B y z) : ℂ) := by
      rfl
    _ = ∑ i : Fin 2,
        ∑ y : {w : ↥c.H // w ∈ (ConjClasses.mk (lemma_2_2_tH c i)).carrier},
          ∑ z : G, (Nat.card (B (y : G) z) : ℂ) := by
      exact two_class_sum_split c h12 hvanish_y
    _ = ∑ i : Fin 2, ∑ j : Fin 2,
        ∑ y : {w : ↥c.H // w ∈ (ConjClasses.mk (lemma_2_2_tH c i)).carrier},
          ∑ z : {w : ↥c.H // w ∈ (ConjClasses.mk (lemma_2_2_tH c j)).carrier},
            (Nat.card (B (y : G) (z : G)) : ℂ) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      calc
        (∑ y : {w : ↥c.H // w ∈ (ConjClasses.mk (lemma_2_2_tH c i)).carrier},
          ∑ z : G, (Nat.card (B (y : G) z) : ℂ))
            = ∑ z : G,
                ∑ y : {w : ↥c.H // w ∈ (ConjClasses.mk (lemma_2_2_tH c i)).carrier},
                  (Nat.card (B (y : G) z) : ℂ) := by
              rw [Finset.sum_comm]
        _ = ∑ j : Fin 2,
              ∑ z : {w : ↥c.H // w ∈ (ConjClasses.mk (lemma_2_2_tH c j)).carrier},
                ∑ y : {w : ↥c.H // w ∈ (ConjClasses.mk (lemma_2_2_tH c i)).carrier},
                  (Nat.card (B (y : G) z) : ℂ) := by
              exact two_class_sum_split c h12 (hvanish_z i)
        _ = ∑ j : Fin 2,
              ∑ y : {w : ↥c.H // w ∈ (ConjClasses.mk (lemma_2_2_tH c i)).carrier},
                ∑ z : {w : ↥c.H // w ∈ (ConjClasses.mk (lemma_2_2_tH c j)).carrier},
                  (Nat.card (B (y : G) (z : G)) : ℂ) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              rw [Finset.sum_comm]
    _ = ∑ i : Fin 2, ∑ j : Fin 2,
        (Nat.card {p : (ConjClasses.mk (lemma_2_2_tH c i)).carrier ×
            (ConjClasses.mk (lemma_2_2_tH c j)).carrier //
          p.1.1 * p.2.1 = x} : ℂ) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      refine Finset.sum_congr rfl ?_
      intro j hj
      exact class_pair_cell c h12 i j

/-- `f` and `Σ f_ij` coincide on `T`: pairs `(x,y) ∈ t^G × t^G` with
`x·y = g ∈ T` are in bijection with the disjoint union over `i, j` of the
pairs in `t_i^H × t_j^H` with the same product. -/
private lemma lemma_2_2_f_eq_fSum_on_T (c : Hyp11 G) (h12 : Hyp12 c)
    {x : ↥c.H} (hx : (x : G) ∈ c.T) :
    lemma_2_2_f c (x : G) = lemma_2_2_fSum c x := by
  classical
  let g : G := (x : G)
  let P : Type u :=
    {p : (ConjClasses.mk c.t).carrier × (ConjClasses.mk c.t).carrier // p.1.1 * p.2.1 = g}
  -- The element-indexed fiber: pairs in the `t^G`-carriers whose ambient
  -- elements are `y, z`, with product `x`.  Indexing by the elements (instead
  -- of by the class indices `i, j`) makes the fiber types proof-independent,
  -- so the `left_inv` of the bijection below is `rfl`-closeable.
  let B : G → G → Type u := fun y z =>
    {p : (ConjClasses.mk c.t).carrier × (ConjClasses.mk c.t).carrier //
      (p.1.1 : G) = y ∧ (p.2.1 : G) = z ∧ p.1.1 * p.2.1 = (x : G)}
  let Q : Type u := Σ y : G, Σ z : G, B y z
  let toFun : Q → P := fun q => by
    let y : G := q.1
    let z : G := q.2.1
    have h₁ : q.2.2.1.1.1 = y := q.2.2.2.1
    have h₂ : q.2.2.1.2.1 = z := q.2.2.2.2.1
    refine ⟨(⟨y, ?_⟩, ⟨z, ?_⟩), ?_⟩
    · exact h₁ ▸ q.2.2.1.1.2
    · exact h₂ ▸ q.2.2.1.2.2
    · change y * z = g
      dsimp [g]
      calc
        y * z = q.2.2.1.1.1 * q.2.2.1.2.1 := by rw [h₁, h₂]
        _ = (x : G) := q.2.2.2.2.2
  let invFun : P → Q := fun p => by
    refine ⟨p.1.1.1, ⟨p.1.2.1, ?_⟩⟩
    refine ⟨(⟨p.1.1.1, p.1.1.2⟩, ⟨p.1.2.1, p.1.2.2⟩), ?_⟩
    refine ⟨rfl, ?_⟩
    refine ⟨rfl, ?_⟩
    change p.1.1.1 * p.1.2.1 = (x : G)
    simpa [g] using p.2
  let e : Q ≃ P :=
    { toFun := toFun
      invFun := invFun
      left_inv := fun q => by
        cases q with
        | mk y q2 =>
          cases q2 with
          | mk z fp =>
            apply Sigma.ext
            · rfl
            · apply heq_of_eq
              apply Sigma.ext
              · rfl
              · -- the fibers have the same type; compare the data
                apply heq_of_eq
                apply Subtype.ext
                · apply Prod.ext
                  · apply Subtype.ext
                    · exact fp.2.1.symm
                  · apply Subtype.ext
                    · exact fp.2.2.1.symm
      right_inv := fun p => by
        apply Subtype.ext
        · rfl }
  calc
    lemma_2_2_f c (x : G) = (Nat.card P : ℂ) := by
      unfold lemma_2_2_f
      exact pair_count_eq_card c x
    _ = (Nat.card Q : ℂ) := by
      congr 1
      exact Nat.card_congr e.symm
    _ = ∑ y : G, ∑ z : G, (Nat.card (B y z) : ℂ) := by
      dsimp [Q]
      rw [Nat.card_eq_fintype_card]
      simp [Fintype.card_sigma, Nat.cast_sum]
    _ = ∑ i : Fin 2, ∑ j : Fin 2,
        (Nat.card {p : (ConjClasses.mk (lemma_2_2_tH c i)).carrier ×
            (ConjClasses.mk (lemma_2_2_tH c j)).carrier //
          p.1.1 * p.2.1 = x} : ℂ) := by
      dsimp [B]
      exact class_pair_sum_decomp c h12 hx
    _ = lemma_2_2_fSum c x := by
      unfold lemma_2_2_fSum lemma_2_2_fij
      refine Finset.sum_congr rfl ?_
      intro i hi
      refine Finset.sum_congr rfl ?_
      intro j hj
      exact (pair_count_eq_card' c x i j).symm

/-! ## The `τ`-case stage: `V` in the `W`-form

`V = |H|·(f, δ*)_G` with `δ* = (μ−ν)*`; since `μ, ν` lie in one `Λ`-orbit,
`μ − ν` vanishes on `U`, and `f = Σ f_ij` on `T = H0 − U`, the adjunction
(Frobenius reciprocity) moves both inner products down to `H0`, giving
`V = W = |H|·(Σ f_ij, δ)_H` with `δ = (μ−ν)^H`. -/

/-- `μ − ν` vanishes on `U` when `μ, ν` lie in one `Λ`-orbit (`μ = λ·ν` with
`λ|_U = 1`). -/
private lemma orbit_mem_sub_vanish_on_U (c : Hyp11 G) {μ ν : ClassFunction (↥c.H0)}
    (hEq : μ ∈ orbit c.H0 c.U ν) : ∀ u : ↥c.H0, (u : G) ∈ c.U → (μ - ν) u = 0 := by
  classical
  intro u hu
  rcases Finset.mem_image.mp hEq with ⟨l, _hlu, hμ⟩
  have hμ' : μ u = (LambdaChar l.1 * ν) u := congrArg (fun φ : ClassFunction (↥c.H0) => φ u) hμ.symm
  have hu1 : LambdaChar l.1 u = 1 := by
    unfold LambdaChar
    exact (congrArg (fun z : ℂˣ => (z : ℂ)) (l.2 u hu)).trans (by simp)
  change μ u - ν u = 0
  calc
    μ u - ν u = (LambdaChar l.1 * ν) u - ν u := congrArg (fun z : ℂ => z - ν u) hμ'
    _ = 0 := by
      change LambdaChar l.1 u * ν u - ν u = 0
      exact (congrArg (fun z : ℂ => z * ν u - ν u) hu1).trans (by norm_num)


/-- `f = Σ f_ij` on `H0` outside `U` (i.e. on `T`): for an element of `H0`
that is not in `U`, hence lies in `T`. -/
private lemma f_eq_fSum_on_H0 (c : Hyp11 G) (h12 : Hyp12 c) {x : ↥c.H}
    (hxH0 : (x : G) ∈ c.H0) (hxU : (x : G) ∉ c.U) :
    lemma_2_2_f c (x : G) = lemma_2_2_fSum c x := by
  classical
  have hxT : (x : G) ∈ c.T := by
    rw [Hyp11.T]
    exact ⟨hxH0, hxU⟩
  exact lemma_2_2_f_eq_fSum_on_T c h12 hxT

/-- The sum of the class functions `f_ij` is a class function. -/
private lemma lemma_2_2_fSum_isClassFunction (c : Hyp11 G) :
    IsClassFunction (lemma_2_2_fSum c) := by
  intro x g
  unfold lemma_2_2_fSum
  refine Finset.sum_congr rfl ?_
  intro i hi
  refine Finset.sum_congr rfl ?_
  intro j hj
  exact classSumPairCountMul_isClassFunction (ConjClasses.mk (lemma_2_2_tH c i))
    (ConjClasses.mk (lemma_2_2_tH c j)) x g

/-- `(f, δ*)_G = (Σ f_ij, δ)_H` — the adjunction applied twice with the
pointwise identity `f = Σ f_ij` on the support of `μ − ν` (`T`). -/
private lemma scalarProduct_f_delta_eq (c : Hyp11 G) (h12 : Hyp12 c)
    {μ ν : ClassFunction (↥c.H0)} (hvanish : ∀ u : ↥c.H0, (u : G) ∈ c.U → (μ - ν) u = 0) :
    scalarProduct G (lemma_2_2_f c) (inducedClassFunction c.H0 (μ - ν)) =
      scalarProduct (↥c.H) (lemma_2_2_fSum c) (lemma_2_2_delta c h12 μ ν) := by
  classical
  have h1 : scalarProduct G (lemma_2_2_f c) (inducedClassFunction c.H0 (μ - ν)) =
      scalarProduct (↥c.H0) (fun x : ↥c.H0 => lemma_2_2_f c (x : G)) (μ - ν) := by
    exact (scalarProduct_restrict_induced c.H0 (lemma_2_2_f_isClassFunction c) (μ - ν)).symm
  have h2 : scalarProduct (↥c.H) (lemma_2_2_fSum c) (lemma_2_2_delta c h12 μ ν) =
      scalarProduct (↥c.H0) (fun x : ↥c.H0 => lemma_2_2_fSum c ⟨(x : G), (h12.H0_normal_in_H).1 x.2⟩)
        (μ - ν) := by
    unfold lemma_2_2_delta
    let K : Subgroup (↥c.H) := c.H0.subgroupOf c.H
    let δ' : ClassFunction (↥K) := fun x => (μ - ν) ⟨(x : G), Subgroup.mem_subgroupOf.mp x.2⟩
    let e : ↥K ≃* ↥c.H0 := H0_subgroupOf_equiv c h12
    have hadj : scalarProduct (↥c.H) (lemma_2_2_fSum c) (inducedClassFunction K δ') =
        scalarProduct (↥K) (fun x : ↥K => lemma_2_2_fSum c (x : ↥c.H)) δ' := by
      exact (scalarProduct_restrict_induced K (lemma_2_2_fSum_isClassFunction c) δ').symm
    rw [hadj]
    -- move to H0 via the identification `e : K ≃* H0`; the composed
    -- restrictions are pointwise the same on `H0` by defeq
    rw [scalarProduct_equiv_invariance (e := e.symm) (φ := fun x : ↥K => lemma_2_2_fSum c (x : ↥c.H))
      (ψ := δ')]
    congr 1
  have h3 : scalarProduct (↥c.H0) (fun x : ↥c.H0 => lemma_2_2_f c (x : G)) (μ - ν) =
      scalarProduct (↥c.H0) (fun x : ↥c.H0 => lemma_2_2_fSum c ⟨(x : G), (h12.H0_normal_in_H).1 x.2⟩)
        (μ - ν) := by
    refine scalarProduct_eq_of_eq_on_supported (G := ↥c.H0)
      (φ := fun x : ↥c.H0 => lemma_2_2_f c (x : G))
      (ψ := fun x : ↥c.H0 => lemma_2_2_fSum c ⟨(x : G), (h12.H0_normal_in_H).1 x.2⟩)
      (δ := μ - ν) ?_
    intro x hx
    have hxU : (x : G) ∉ c.U := by
      intro hxU
      exact hx (hvanish x hxU)
    exact f_eq_fSum_on_H0 c h12 (x := ⟨(x : G), (h12.H0_normal_in_H).1 x.2⟩) x.2 hxU
  rw [h1, h2]
  exact h3

/-- The `W`-form of `V`: `V = |H|·(Σ f_ij, δ)_H` with `δ = (μ−ν)^H`, for
`μ, ν` in one `Λ`-orbit. -/
private lemma lemma_2_2_V_eq_W (c : Hyp11 G) (h12 : Hyp12 c)
    {μ ν : ClassFunction (↥c.H0)} (hEq : μ ∈ orbit c.H0 c.U ν) :
    lemma_2_2_V c μ ν = lemma_2_2_W c (lemma_2_2_delta c h12 μ ν) := by
  classical
  rw [lemma_2_2_V_eq]
  unfold lemma_2_2_W
  congr 1
  exact scalarProduct_f_delta_eq c h12 (orbit_mem_sub_vanish_on_U c hEq)

/-- The `H`-level involutions `t_i` square to one. -/
private lemma tH_involution (c : Hyp11 G) (i : Fin 2) :
    lemma_2_2_tH c i * lemma_2_2_tH c i = 1 := by
  fin_cases i
  · simpa [lemma_2_2_tH_zero, pow_two] using c.t1_involution.2
  · simpa [lemma_2_2_tH_one, pow_two] using c.t2_involution.2

/-- The pair count `f_ij` on `H` expands over `Irr(H)`:
`(f_ij, δ)_H = (|t_i^H|·|t_j^H|/|H|)·Σ_θ (θ(t_i)·θ(t_j)/θ(1))·(θ, δ)_H`. -/
private lemma scalarProduct_fij_delta (c : Hyp11 G) (h12 : Hyp12 c)
    (δ : ClassFunction (↥c.H)) (i j : Fin 2) :
    scalarProduct (↥c.H) (lemma_2_2_fij c i j) δ =
      ((Nat.card (ConjClasses.mk (lemma_2_2_tH c i)).carrier : ℂ) *
          (Nat.card (ConjClasses.mk (lemma_2_2_tH c j)).carrier : ℂ) /
        (Nat.card (↥c.H) : ℂ)) *
        ∑ θ : Irr (↥c.H), (θ.1 (lemma_2_2_tH c i) * θ.1 (lemma_2_2_tH c j) / θ.1 1) *
          scalarProduct (↥c.H) θ.1 δ := by
  unfold lemma_2_2_fij
  convert scalarProduct_classSumPairCountMul_involutions (G := ↥c.H)
    (ti := lemma_2_2_tH c i) (tj := lemma_2_2_tH c j) (tH_involution c i) (tH_involution c j) δ

/-- The coefficient of `(θ, δ)_H` in `W`:
`|H|·Σ_{i,j} (|t_i^H|·|t_j^H|/|H|)·θ(t_i)·θ(t_j)/θ(1) = c(θ)`. -/
private lemma cθ_coefficient (c : Hyp11 G) (θ : Irr (↥c.H)) :
    (Nat.card (↥c.H) : ℂ) * (∑ i : Fin 2, ∑ j : Fin 2,
      ((Nat.card (ConjClasses.mk (lemma_2_2_tH c i)).carrier : ℂ) *
          (Nat.card (ConjClasses.mk (lemma_2_2_tH c j)).carrier : ℂ) /
        (Nat.card (↥c.H) : ℂ)) *
        (θ.1 (lemma_2_2_tH c i) * θ.1 (lemma_2_2_tH c j) / θ.1 1)) =
      lemma_2_2_cθ c θ.1 := by
  classical
  have hk1 : (Nat.card (ConjClasses.mk (⟨c.t1, t1_mem_H c⟩ : ↥c.H)).carrier : ℂ) = (c.k1 : ℂ) := by
    exact_mod_cast card_t1_class_eq_k1 c
  have hk2 : (Nat.card (ConjClasses.mk (⟨c.t2, t2_mem_H c⟩ : ↥c.H)).carrier : ℂ) = (c.k2 : ℂ) := by
    exact_mod_cast card_t2_class_eq_k2 c
  have hHne : (Nat.card (↥c.H) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := ↥c.H)).ne'
  have hθ1 : θ.1 1 ≠ 0 := irreducible_char_one_ne_zero θ.2
  unfold lemma_2_2_cθ
  simp only [Fin.sum_univ_two]
  rw [lemma_2_2_tH_zero, lemma_2_2_tH_one]
  rw [hk1, hk2]
  field_simp [hHne, hθ1]

/-- `W = Σ_θ c(θ)·(θ, δ)_H` — the class-sum expansion of `W` over `Irr(H)`. -/
private lemma lemma_2_2_W_eq_sum_cθ (c : Hyp11 G) (h12 : Hyp12 c)
    (δ : ClassFunction (↥c.H)) :
    lemma_2_2_W c δ =
      ∑ θ : Irr (↥c.H), lemma_2_2_cθ c θ.1 * scalarProduct (↥c.H) θ.1 δ := by
  classical
  have hk (i : Fin 2) :
      (Nat.card (ConjClasses.mk (lemma_2_2_tH c i)).carrier : ℂ) =
        (if i = 0 then (c.k1 : ℂ) else (c.k2 : ℂ)) := by
    fin_cases i
    · simpa [lemma_2_2_tH_zero] using (congrArg (fun n : ℕ => (n : ℂ)) (card_t1_class_eq_k1 c))
    · simpa [lemma_2_2_tH_one] using (congrArg (fun n : ℕ => (n : ℂ)) (card_t2_class_eq_k2 c))
  calc
    lemma_2_2_W c δ = (Nat.card (↥c.H) : ℂ) * scalarProduct (↥c.H) (lemma_2_2_fSum c) δ := rfl
    _ = (Nat.card (↥c.H) : ℂ) *
          ∑ i : Fin 2, ∑ j : Fin 2, scalarProduct (↥c.H) (lemma_2_2_fij c i j) δ := by
      congr 1
      unfold lemma_2_2_fSum
      change scalarProduct (↥c.H) (∑ i : Fin 2, ∑ j : Fin 2, lemma_2_2_fij c i j) δ = _
      rw [scalarProduct_sum_left]
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [scalarProduct_sum_left]
    _ = (Nat.card (↥c.H) : ℂ) *
          ∑ i : Fin 2, ∑ j : Fin 2,
            ((Nat.card (ConjClasses.mk (lemma_2_2_tH c i)).carrier : ℂ) *
                (Nat.card (ConjClasses.mk (lemma_2_2_tH c j)).carrier : ℂ) /
              (Nat.card (↥c.H) : ℂ)) *
              ∑ θ : Irr (↥c.H), (θ.1 (lemma_2_2_tH c i) * θ.1 (lemma_2_2_tH c j) / θ.1 1) *
                scalarProduct (↥c.H) θ.1 δ := by
      congr 1
      refine Finset.sum_congr rfl ?_
      intro i hi
      refine Finset.sum_congr rfl ?_
      intro j hj
      exact scalarProduct_fij_delta c h12 δ i j
    _ = ∑ θ : Irr (↥c.H), lemma_2_2_cθ c θ.1 * scalarProduct (↥c.H) θ.1 δ := by
      let X : Fin 2 → Fin 2 → Irr (↥c.H) → ℂ := fun i j θ =>
        ((Nat.card (ConjClasses.mk (lemma_2_2_tH c i)).carrier : ℂ) *
            (Nat.card (ConjClasses.mk (lemma_2_2_tH c j)).carrier : ℂ) /
          (Nat.card (↥c.H) : ℂ)) *
          (θ.1 (lemma_2_2_tH c i) * θ.1 (lemma_2_2_tH c j) / θ.1 1) *
          scalarProduct (↥c.H) θ.1 δ
      calc
        (Nat.card (↥c.H) : ℂ) * (∑ i : Fin 2, ∑ j : Fin 2,
            ((Nat.card (ConjClasses.mk (lemma_2_2_tH c i)).carrier : ℂ) *
                (Nat.card (ConjClasses.mk (lemma_2_2_tH c j)).carrier : ℂ) /
              (Nat.card (↥c.H) : ℂ)) *
              ∑ θ : Irr (↥c.H), (θ.1 (lemma_2_2_tH c i) * θ.1 (lemma_2_2_tH c j) / θ.1 1) *
                scalarProduct (↥c.H) θ.1 δ)
            = (Nat.card (↥c.H) : ℂ) * (∑ i : Fin 2, ∑ j : Fin 2, ∑ θ : Irr (↥c.H), X i j θ) := by
              congr 1
              refine Finset.sum_congr rfl ?_
              intro i hi
              refine Finset.sum_congr rfl ?_
              intro j hj
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro θ hθ
              ring
        _ = (Nat.card (↥c.H) : ℂ) * (∑ θ : Irr (↥c.H), ∑ i : Fin 2, ∑ j : Fin 2, X i j θ) := by
              congr 1
              calc
                (∑ i : Fin 2, ∑ j : Fin 2, ∑ θ : Irr (↥c.H), X i j θ)
                    = ∑ i : Fin 2, ∑ θ : Irr (↥c.H), ∑ j : Fin 2, X i j θ := by
                      refine Finset.sum_congr rfl ?_
                      intro i hi
                      rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
                        (f := fun j : Fin 2 => fun θ : Irr (↥c.H) => X i j θ)]
                _ = ∑ θ : Irr (↥c.H), ∑ i : Fin 2, ∑ j : Fin 2, X i j θ := by
                      rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
                        (f := fun i : Fin 2 => fun θ : Irr (↥c.H) => ∑ j : Fin 2, X i j θ)]
        _ = ∑ θ : Irr (↥c.H), lemma_2_2_cθ c θ.1 * scalarProduct (↥c.H) θ.1 δ := by
              -- the |H|-factor enters; the identity `cθ_coefficient` closes
              calc
                (Nat.card (↥c.H) : ℂ) * (∑ θ : Irr (↥c.H), ∑ i : Fin 2, ∑ j : Fin 2, X i j θ)
                    = ∑ θ : Irr (↥c.H), (Nat.card (↥c.H) : ℂ) * (∑ i : Fin 2, ∑ j : Fin 2, X i j θ) := by
                      simp only [Finset.mul_sum]
                _ = ∑ θ : Irr (↥c.H), lemma_2_2_cθ c θ.1 * scalarProduct (↥c.H) θ.1 δ := by
                      refine Finset.sum_congr rfl ?_
                      intro θ hθ
                      -- goal: |H|·(Σ_i Σ_j X i j θ) = cθ(θ)·sp θ δ
                      change (Nat.card (↥c.H) : ℂ) * (∑ i : Fin 2, ∑ j : Fin 2,
                          ((Nat.card (ConjClasses.mk (lemma_2_2_tH c i)).carrier : ℂ) *
                              (Nat.card (ConjClasses.mk (lemma_2_2_tH c j)).carrier : ℂ) /
                            (Nat.card (↥c.H) : ℂ)) *
                            (θ.1 (lemma_2_2_tH c i) * θ.1 (lemma_2_2_tH c j) / θ.1 1) *
                            scalarProduct (↥c.H) θ.1 δ) =
                        lemma_2_2_cθ c θ.1 * scalarProduct (↥c.H) θ.1 δ
                      -- the scalar-product factor is common; the coefficient identity closes
                      simp only [← Finset.sum_mul]
                      rw [← mul_assoc]
                      exact congrArg (fun z : ℂ => z * scalarProduct (↥c.H) θ.1 δ) (cθ_coefficient c θ)


/-! ## The `τ`-case: the vanishing of `W`

For `μ^s ≠ μ` and `ν^s ≠ ν` in one `Λ`-orbit: `μ^H`, `ν^H` are irreducible
(Clifford for the index-2 extension `H/H0`), the induced characters vanish at
`t1, t2` (`t_i ∉ H0`, `H0 ⊴ H`), so `W = c(μ^H) − c(ν^H) = 0`. -/

/-- The `H`-level involutions `t_i` are outside `H0`. -/
private lemma tH_not_mem_H0 (c : Hyp11 G) (h12 : Hyp12 c) (i : Fin 2) :
    (lemma_2_2_tH c i : G) ∉ c.H0 := by
  fin_cases i
  · simpa [lemma_2_2_tH_zero] using t1_not_mem_H0 c h12
  · simpa [lemma_2_2_tH_one] using t2_not_mem_H0 c h12

/-- The induced `δ^H` (from `H0` to `H`) vanishes at `t_i`:
`t_i ∉ H0` and `H0 ⊴ H` keep every `H`-conjugate of `t_i` outside `H0`. -/
private lemma induced_delta_vanishes_at_tH (c : Hyp11 G) (h12 : Hyp12 c)
    (δ : ClassFunction (↥c.H0)) (i : Fin 2) :
    inducedFromSub (h12.H0_normal_in_H).1 δ (lemma_2_2_tH c i) = 0 := by
  unfold inducedFromSub
  apply inducedClassFunction_supportedOn
  intro x hx
  -- x⁻¹·(tH i)·x ∈ H0 (the val); by normality of H0 in H, tH i ∈ H0
  have hxH0 : (x⁻¹ * (lemma_2_2_tH c i) * x : G) ∈ c.H0 := Subgroup.mem_subgroupOf.mp hx
  have htH : (lemma_2_2_tH c i : G) ∈ c.H0 := by
    have hmem : (x : G) * ((x : G)⁻¹ * (lemma_2_2_tH c i : G) * (x : G)) * (x : G)⁻¹ ∈ c.H0 :=
      (h12.H0_normal_in_H).2 (x : G) x.2 ((x : G)⁻¹ * (lemma_2_2_tH c i : G) * (x : G)) hxH0
    -- the conjugate equals tH
    convert hmem using 1
    group
  exact tH_not_mem_H0 c h12 i htH

/-- The restriction of the induced character to `H0` — the Clifford formula
for the index-2 extension `H/H0`: `μ^H(h) = μ(h) + μ^s(h)`. -/
private lemma induced_restrict_eq_add_conj (c : Hyp11 G) (h12 : Hyp12 c)
    {μ : ClassFunction (↥c.H0)} (hμ : IsClassFunction μ) (h : ↥c.H0) :
    inducedFromSub (h12.H0_normal_in_H).1 μ ⟨(h : G), (h12.H0_normal_in_H).1 h.2⟩ =
      μ h + conjChar c.H0 (s_normalizes_H0 c h12) μ h := by
  simpa [conjChar, conjMonoidHom]
    using inducedFromSub_eq_add_conj_index_two (G := G) c.H0 c.H (h12.H0_normal_in_H).1
      (H0_index c h12) (s := c.s) (s_mem_H c) (s_not_mem_H0 c h12) μ hμ (h := h) h.2
      (s_normalizes_H0 c h12 h)


/-- `s⁻¹` normalizes `H0` (`s` is an involution, so `s⁻¹ = s`). -/
private lemma s_inv_normalizes_H0 (c : Hyp11 G) (h12 : Hyp12 c) :
    ∀ x : ↥c.H0, c.s⁻¹ * (x : G) * c.s ∈ c.H0 := by
  intro x
  have hsq : c.s⁻¹ = c.s := by
    exact inv_eq_of_mul_eq_one_right (by simpa [pow_two] using c.s_involution.2)
  have hx : c.s * (x : G) * c.s⁻¹ ∈ c.H0 := s_normalizes_H0 c h12 x
  simpa [hsq] using hx

/-- The `s`-conjugate `μ^s` of an irreducible character is irreducible. -/
private lemma conjChar_irreducible (c : Hyp11 G) (h12 : Hyp12 c)
    {μ : Irr (↥c.H0)} : IsIrreducibleCharacter (conjChar c.H0 (s_normalizes_H0 c h12) μ.1) := by
  refine isIrreducibleCharacter_of_norm_one_inv
    (isCharacter_conjChar c.H0 (s_normalizes_H0 c h12) (isCharacter_of_isIrreducibleCharacter μ.2)) ?_
  have hnorm := norm_inv_conjChar (H0 := c.H0) (s := c.s) (s_normalizes_H0 c h12)
    (s_inv_normalizes_H0 c h12) μ.1
  rw [hnorm]
  exact isIrreducible_norm_inv_one μ.2

/-- Clifford (index two): for `μ^s ≠ μ`, the induced `μ^H` is irreducible
— `(μ^H, μ^H)_H = (μ, μ + μ^s)_H0 = 1 + 0 = 1` with `(μ, μ^s) = 0` by
orthogonality of distinct irreducibles (`conjIrr`). -/
private lemma induced_irreducible_of_ne_conj (c : Hyp11 G) (h12 : Hyp12 c)
    {μ : Irr (↥c.H0)} (hμs : conjChar c.H0 (s_normalizes_H0 c h12) μ.1 ≠ μ.1) :
    IsIrreducibleCharacter (inducedFromSub (h12.H0_normal_in_H).1 μ.1) := by
  classical
  let α : ClassFunction (↥c.H) := inducedFromSub (h12.H0_normal_in_H).1 μ.1
  have hcharα : IsCharacter α := by
    simpa [α] using isCharacter_ind_index_two c.H0 c.H (h12.H0_normal_in_H).1 (H0_index c h12)
      (s_mem_H c) (s_not_mem_H0 c h12) μ.2 (s_normalizes_H0 c h12)
  have hclα : IsClassFunction α := isCharacter_isClassFunction hcharα
  have hsp : scalarProduct (↥c.H) α α = 1 := by
    have h1 : scalarProduct (↥c.H) α α =
        scalarProduct (↥c.H0) μ.1 (fun x : ↥c.H0 => α ⟨(x : G), (h12.H0_normal_in_H).1 x.2⟩) := by
      let K : Subgroup (↥c.H) := c.H0.subgroupOf c.H
      let δ' : ClassFunction (↥K) := fun x => μ.1 ⟨(x : G), Subgroup.mem_subgroupOf.mp x.2⟩
      let e : ↥K ≃* ↥c.H0 := H0_subgroupOf_equiv c h12
      have hadj : scalarProduct (↥c.H) (inducedClassFunction K δ') α =
          scalarProduct (↥K) δ' (fun x : ↥K => α (x : ↥c.H)) := by
        exact frobenius_reciprocity (G := ↥c.H) K δ' hclα
      change scalarProduct (↥c.H) (inducedClassFunction K δ') α =
        scalarProduct (↥c.H0) μ.1 (fun x : ↥c.H0 => α ⟨(x : G), (h12.H0_normal_in_H).1 x.2⟩)
      rw [hadj]
      rw [scalarProduct_equiv_invariance (e := e.symm) (φ := δ')
        (ψ := fun x : ↥K => α (x : ↥c.H))]
      congr 1
    have h2 : scalarProduct (↥c.H0) μ.1 (fun x : ↥c.H0 => α ⟨(x : G), (h12.H0_normal_in_H).1 x.2⟩) =
        scalarProduct (↥c.H0) μ.1 (μ.1 + conjChar c.H0 (s_normalizes_H0 c h12) μ.1) := by
      congr 1
      funext x
      exact induced_restrict_eq_add_conj c h12 (irreducibleCharacter_isClassFunction μ.2) x
    have h3 : scalarProduct (↥c.H0) μ.1 (μ.1 + conjChar c.H0 (s_normalizes_H0 c h12) μ.1) =
        scalarProduct (↥c.H0) μ.1 μ.1 +
          scalarProduct (↥c.H0) μ.1 (conjChar c.H0 (s_normalizes_H0 c h12) μ.1) := by
      rw [scalarProduct_add_right]
    have h4 : scalarProduct (↥c.H0) μ.1 μ.1 = 1 := scalarProduct_irreducible_self μ.2
    have h5 : scalarProduct (↥c.H0) μ.1 (conjChar c.H0 (s_normalizes_H0 c h12) μ.1) = 0 := by
      exact scalarProduct_irreducible_orthogonal μ.2 (conjChar_irreducible c h12) hμs.symm
    rw [h1, h2, h3, h4, h5]
    norm_num
  refine isIrreducibleCharacter_of_norm_one_inv hcharα ?_
  have hb : star (scalarProduct (↥c.H) α α) = scalarProductInv (↥c.H) α α :=
    star_scalarProduct_eq_inv_of_char hcharα
  rw [hsp] at hb
  simpa using hb.symm

/-- The `Irr(H)`-expansion of `c(·)` against an irreducible `ψ`:
`Σ_θ c(θ)·(θ, ψ)_H = c(ψ)` by orthonormality. -/
private lemma sum_cθ_mul_scalarProduct_irreducible (c : Hyp11 G)
    {ψ : ClassFunction (↥c.H)} (hψ : IsIrreducibleCharacter ψ) :
    (∑ θ : Irr (↥c.H), lemma_2_2_cθ c θ.1 * scalarProduct (↥c.H) θ.1 ψ) =
      lemma_2_2_cθ c ψ := by
  classical
  let ψ' : Irr (↥c.H) := ⟨ψ, hψ⟩
  calc
    (∑ θ : Irr (↥c.H), lemma_2_2_cθ c θ.1 * scalarProduct (↥c.H) θ.1 ψ)
        = ∑ θ : Irr (↥c.H), (if θ = ψ' then lemma_2_2_cθ c ψ else 0) := by
            refine Finset.sum_congr rfl ?_
            intro θ hθ
            by_cases h : θ = ψ'
            · have hθψ : θ.1 = ψ := congrArg Subtype.val h
              rw [if_pos h, hθψ, scalarProduct_irreducible_self hψ]
              norm_num
            · have hsp0 : scalarProduct (↥c.H) θ.1 ψ = 0 := by
                refine scalarProduct_irreducible_orthogonal θ.2 hψ ?_
                intro hEq
                apply h
                apply Subtype.ext
                exact hEq
              rw [if_neg h, hsp0]
              norm_num
    _ = lemma_2_2_cθ c ψ := by
        simp [Finset.sum_ite_eq']

/-- `c(α) = 0` when `α` vanishes at `t1` and `t2` (the `τ`-case: `t_i ∉ H0`). -/
private lemma cθ_zero_of_vanishes_at_tH (c : Hyp11 G)
    {α : ClassFunction (↥c.H)} (hα : IsIrreducibleCharacter α)
    (h1 : α (lemma_2_2_tH c 0) = 0) (h2 : α (lemma_2_2_tH c 1) = 0) :
    lemma_2_2_cθ c α = 0 := by
  unfold lemma_2_2_cθ
  simp [h1, h2]

/-- Induction is linear on differences: `(μ − ν)^H = μ^H − ν^H`. -/
private lemma inducedFromSub_sub (c : Hyp11 G) (h12 : Hyp12 c)
    (μ ν : ClassFunction (↥c.H0)) :
    inducedFromSub (h12.H0_normal_in_H).1 (μ - ν) =
      inducedFromSub (h12.H0_normal_in_H).1 μ -
        inducedFromSub (h12.H0_normal_in_H).1 ν := by
  classical
  unfold inducedFromSub
  change inducedClassFunction (c.H0.subgroupOf c.H)
    (fun x : ↥(c.H0.subgroupOf c.H) =>
      μ ⟨(x : G), Subgroup.mem_subgroupOf.mp x.2⟩ -
        ν ⟨(x : G), Subgroup.mem_subgroupOf.mp x.2⟩) =
    inducedClassFunction (c.H0.subgroupOf c.H)
      (fun x : ↥(c.H0.subgroupOf c.H) =>
        μ ⟨(x : G), Subgroup.mem_subgroupOf.mp x.2⟩) -
    inducedClassFunction (c.H0.subgroupOf c.H)
      (fun x : ↥(c.H0.subgroupOf c.H) =>
        ν ⟨(x : G), Subgroup.mem_subgroupOf.mp x.2⟩)
  rw [← inducedClassFunction_sub]
  rfl

/-- The `τ`-case of Lemma 2.2: for `μ^s ≠ μ`, `ν^s ≠ ν` in one orbit,
`W = c(μ^H) − c(ν^H) = 0` — both induceds are irreducible and vanish on
`t1, t2 ∉ H0`. -/
private lemma lemma_2_2_W_tau_case (c : Hyp11 G) (h12 : Hyp12 c)
    {μ ν : Irr (↥c.H0)}
    (hμs : conjChar c.H0 (s_normalizes_H0 c h12) μ.1 ≠ μ.1)
    (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 ≠ ν.1) :
    lemma_2_2_W c (lemma_2_2_delta c h12 μ.1 ν.1) = 0 := by
  classical
  let α : ClassFunction (↥c.H) := inducedFromSub (h12.H0_normal_in_H).1 μ.1
  let β : ClassFunction (↥c.H) := inducedFromSub (h12.H0_normal_in_H).1 ν.1
  have hα : IsIrreducibleCharacter α := by
    simpa [α] using induced_irreducible_of_ne_conj c h12 hμs
  have hβ : IsIrreducibleCharacter β := by
    simpa [β] using induced_irreducible_of_ne_conj c h12 hνs
  have hδ : lemma_2_2_delta c h12 μ.1 ν.1 = α - β := by
    unfold lemma_2_2_delta
    rw [inducedFromSub_sub c h12 μ.1 ν.1]
  rw [lemma_2_2_W_eq_sum_cθ c h12 (lemma_2_2_delta c h12 μ.1 ν.1)]
  rw [hδ]
  calc
    (∑ θ : Irr (↥c.H), lemma_2_2_cθ c θ.1 * scalarProduct (↥c.H) θ.1 (α - β))
        = (∑ θ : Irr (↥c.H), lemma_2_2_cθ c θ.1 *
            (scalarProduct (↥c.H) θ.1 α - scalarProduct (↥c.H) θ.1 β)) := by
            refine Finset.sum_congr rfl ?_
            intro θ hθ
            congr 1
            exact scalarProduct_sub_right θ.1 α β
    _ = (∑ θ : Irr (↥c.H), lemma_2_2_cθ c θ.1 * scalarProduct (↥c.H) θ.1 α) -
          (∑ θ : Irr (↥c.H), lemma_2_2_cθ c θ.1 * scalarProduct (↥c.H) θ.1 β) := by
            rw [← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl ?_
            intro θ hθ
            rw [mul_sub]
    _ = lemma_2_2_cθ c α - lemma_2_2_cθ c β := by
            rw [sum_cθ_mul_scalarProduct_irreducible c hα]
            rw [sum_cθ_mul_scalarProduct_irreducible c hβ]
    _ = 0 := by
            have hα0 : lemma_2_2_cθ c α = 0 :=
              cθ_zero_of_vanishes_at_tH c hα
                (by simpa [α] using induced_delta_vanishes_at_tH c h12 μ.1 0)
                (by simpa [α] using induced_delta_vanishes_at_tH c h12 μ.1 1)
            have hβ0 : lemma_2_2_cθ c β = 0 :=
              cθ_zero_of_vanishes_at_tH c hβ
                (by simpa [β] using induced_delta_vanishes_at_tH c h12 ν.1 0)
                (by simpa [β] using induced_delta_vanishes_at_tH c h12 ν.1 1)
            rw [hα0, hβ0]
            norm_num
/-- `κ1` is fixed by `s` (`κ1^s = κ1`): `κ1` kills `S0` and `[S,U]`, and
`H0 = U·S0` with `s` inverting `S0` and normalizing `U`. -/
private lemma kappaOne_fixed_by_s (c : Hyp11 G) (h12 : Hyp12 c)
    {κ1 : ClassFunction (↥c.H0)} (hκ1lin : IsLinearCharacter κ1)
    (hκ1S0 : ∀ x : ↥c.H0, (x : G) ∈ (c.S0 : Subgroup G) → κ1 x = 1)
    (hκ1comm : ∀ x : ↥c.H0, (x : G) ∈ ⁅(c.S : Subgroup G), c.U⁆ → κ1 x = 1) :
    conjChar c.H0 (s_normalizes_H0 c h12) κ1 = κ1 := by
  classical
  funext x
  unfold conjChar conjMonoidHom
  rcases H0_eq_U_mul_S0 c h12 (x := x) with ⟨u, r, hx⟩
  have hsq : c.s⁻¹ = c.s := by
    exact inv_eq_of_mul_eq_one_right (by simpa [pow_two] using c.s_involution.2)
  have hsr : c.s * (r : G) * c.s⁻¹ = (r : G)⁻¹ := s_inverts_S0 c r.2
  have hcom : ⁅(c.s : G), (u : G)⁆ ∈ ⁅(c.S : Subgroup G), c.U⁆ := by
    let S : Subgroup G := (c.S : Subgroup G)
    have hc : ⁅(c.s : G), (u : G)⁆ ∈ ⁅S, c.U⁆ := by
      exact Subgroup.commutator_mem_commutator (H₁ := S) (H₂ := c.U) c.s_mem_S u.2
    simpa [S] using hc
  have hdecomp' : (c.s * (u : G) * c.s⁻¹) = ⁅(c.s : G), (u : G)⁆ * (u : G) := by
    rw [commutatorElement_def]
    group
  have hfac : c.s * ((u : G) * (r : G)) * c.s⁻¹ =
      (c.s * (u : G) * c.s⁻¹) * (c.s * (r : G) * c.s⁻¹) := by
    group
  have hval : (c.s * ((u : G) * (r : G)) * c.s⁻¹ : G) =
      ⁅(c.s : G), (u : G)⁆ * (u : G) * (r : G)⁻¹ := by
    rw [hfac, hsr, hdecomp']
  -- the value of κ1 at the conjugate
  have hk1 : κ1 ⟨c.s * (x : G) * c.s⁻¹, s_normalizes_H0 c h12 x⟩ = κ1 x := by
    have hxeq : x = ⟨(u : G) * (r : G),
        c.H0.mul_mem ((h12.U_normal_in_H0).1 u.2) (S0_le_H0 c r.2)⟩ := by
      apply Subtype.ext
      exact hx
    rw [hxeq]
    have hcu : ⁅(c.s : G), (u : G)⁆ ∈ c.H0 := by
      have hu1 : c.s * (u : G) * c.s⁻¹ ∈ c.U := s_normalizes_U c u.2
      have hw : (c.s * (u : G) * c.s⁻¹) * (u : G)⁻¹ = ⁅(c.s : G), (u : G)⁆ := by
        rw [commutatorElement_def]
      rw [← hw]
      exact (h12.U_normal_in_H0).1 (c.U.mul_mem hu1 (c.U.inv_mem u.2))
    have hconj : (⟨c.s * ((u : G) * (r : G)) * c.s⁻¹,
          s_normalizes_H0 c h12 ⟨(u : G) * (r : G), c.H0.mul_mem ((h12.U_normal_in_H0).1 u.2) (S0_le_H0 c r.2)⟩⟩ : ↥c.H0) =
        ⟨⁅(c.s : G), (u : G)⁆ * (u : G) * (r : G)⁻¹,
          c.H0.mul_mem (c.H0.mul_mem hcu ((h12.U_normal_in_H0).1 u.2))
            (S0_le_H0 c (c.S0.inv_mem r.2))⟩ := by
      apply Subtype.ext
      exact hval
    rw [hconj]
    -- κ1(⁅s,u⁆·u·r⁻¹) = κ1(⁅s,u⁆)·κ1(u)·κ1(r⁻¹)
    have h1 : κ1 ⟨⁅(c.s : G), (u : G)⁆ * (u : G) * (r : G)⁻¹,
          c.H0.mul_mem (c.H0.mul_mem hcu ((h12.U_normal_in_H0).1 u.2))
            (S0_le_H0 c (c.S0.inv_mem r.2))⟩ =
        κ1 ⟨⁅(c.s : G), (u : G)⁆, hcu⟩ * κ1 ⟨(u : G), (h12.U_normal_in_H0).1 u.2⟩ *
          κ1 ⟨(r : G)⁻¹, S0_le_H0 c (c.S0.inv_mem r.2)⟩ := by
      have hpr : (⟨⁅(c.s : G), (u : G)⁆, hcu⟩ *
            ⟨(u : G), (h12.U_normal_in_H0).1 u.2⟩ *
            ⟨(r : G)⁻¹, S0_le_H0 c (c.S0.inv_mem r.2)⟩ : ↥c.H0) =
          ⟨⁅(c.s : G), (u : G)⁆ * (u : G) * (r : G)⁻¹,
            c.H0.mul_mem (c.H0.mul_mem hcu ((h12.U_normal_in_H0).1 u.2))
              (S0_le_H0 c (c.S0.inv_mem r.2))⟩ := rfl
      rw [← hpr]
      rw [linearChar_mul hκ1lin]
      rw [linearChar_mul hκ1lin]
    rw [h1]
    have hκ1com : κ1 ⟨⁅(c.s : G), (u : G)⁆, hcu⟩ = 1 :=
      hκ1comm ⟨⁅(c.s : G), (u : G)⁆, hcu⟩ hcom
    have hκ1r : κ1 ⟨(r : G)⁻¹, S0_le_H0 c (c.S0.inv_mem r.2)⟩ = 1 :=
      hκ1S0 ⟨(r : G)⁻¹, S0_le_H0 c (c.S0.inv_mem r.2)⟩ (c.S0.inv_mem r.2)
    rw [hκ1com, hκ1r]
    -- κ1 x = κ1(u·r) = κ1(u)·1
    have h2 : κ1 ⟨(u : G) * (r : G),
        c.H0.mul_mem ((h12.U_normal_in_H0).1 u.2) (S0_le_H0 c r.2)⟩ =
        κ1 ⟨(u : G), (h12.U_normal_in_H0).1 u.2⟩ * κ1 ⟨(r : G), S0_le_H0 c r.2⟩ := by
      have hpr : (⟨(u : G), (h12.U_normal_in_H0).1 u.2⟩ * ⟨(r : G), S0_le_H0 c r.2⟩ : ↥c.H0) =
          ⟨(u : G) * (r : G), c.H0.mul_mem ((h12.U_normal_in_H0).1 u.2) (S0_le_H0 c r.2)⟩ := rfl
      rw [← hpr]
      rw [linearChar_mul hκ1lin]
    rw [h2]
    have hκ1r2 : κ1 ⟨(r : G), S0_le_H0 c r.2⟩ = 1 := hκ1S0 ⟨(r : G), S0_le_H0 c r.2⟩ r.2
    rw [hκ1r2]
    ring
  exact hk1

/-- For `|H : H0| = 2`, every element of `H` outside `H0` lies in `s⁻¹·H0`. -/
private lemma s_inv_mul_mem_H0_of_not_mem (c : Hyp11 G) (h12 : Hyp12 c)
    {g : ↥c.H} (hg : (g : G) ∉ c.H0) :
    c.s⁻¹ * (g : G) ∈ c.H0 := by
  have hiff := Subgroup.mul_mem_iff_of_index_two (G := ↥c.H)
    (H0_index c h12) (a := ⟨c.s, s_mem_H c⟩⁻¹) (b := g)
  have ha : (⟨c.s, s_mem_H c⟩⁻¹ : ↥c.H) ∉ c.H0.subgroupOf c.H := by
    intro h
    apply s_not_mem_H0 c h12
    have hsinv : (c.s⁻¹ : G) ∈ c.H0 := by
      simpa using (Subgroup.mem_subgroupOf.mp h)
    exact c.H0.inv_mem_iff.mp hsinv
  have hb : g ∉ c.H0.subgroupOf c.H := by
    intro h
    exact hg (Subgroup.mem_subgroupOf.mp h)
  have hmain : (⟨c.s, s_mem_H c⟩⁻¹ * g : ↥c.H) ∈ c.H0.subgroupOf c.H := by
    exact (hiff.mpr (by simp [ha, hb]))
  exact Subgroup.mem_subgroupOf.mp hmain

/-- The pointwise form of `κ1^s = κ1`: `κ1(s·h·s⁻¹) = κ1(h)`. -/
private lemma kappaOne_conj_fix_pointwise (c : Hyp11 G) (h12 : Hyp12 c)
    {κ1 : ClassFunction (↥c.H0)}
    (hκ1fix : conjChar c.H0 (s_normalizes_H0 c h12) κ1 = κ1) (h : ↥c.H0) :
    κ1 ⟨c.s * (h : G) * c.s⁻¹, s_normalizes_H0 c h12 h⟩ = κ1 h := by
  have hc := congrFun hκ1fix h
  simpa [conjChar, conjMonoidHom] using hc

private lemma not_mem_H0_of_mem_left_not_mem_right (c : Hyp11 G) (h12 : Hyp12 c)
    {x y : ↥c.H} (hx : (x : G) ∈ c.H0) (hy : (y : G) ∉ c.H0) :
    ((x * y : ↥c.H) : G) ∉ c.H0 := by
  intro hxy
  have hiff := Subgroup.mul_mem_iff_of_index_two (G := ↥c.H)
    (H0_index c h12) (a := x) (b := y)
  have hxK : x ∈ c.H0.subgroupOf c.H := Subgroup.mem_subgroupOf.mpr hx
  have hK : (x * y : ↥c.H) ∈ c.H0.subgroupOf c.H := Subgroup.mem_subgroupOf.mpr hxy
  exact hy (Subgroup.mem_subgroupOf.mp ((hiff.mp hK).mp hxK))

private lemma not_mem_H0_of_not_mem_left_mem_right (c : Hyp11 G) (h12 : Hyp12 c)
    {x y : ↥c.H} (hx : (x : G) ∉ c.H0) (hy : (y : G) ∈ c.H0) :
    ((x * y : ↥c.H) : G) ∉ c.H0 := by
  intro hxy
  have hiff := Subgroup.mul_mem_iff_of_index_two (G := ↥c.H)
    (H0_index c h12) (a := x) (b := y)
  have hyK : y ∈ c.H0.subgroupOf c.H := Subgroup.mem_subgroupOf.mpr hy
  have hK : (x * y : ↥c.H) ∈ c.H0.subgroupOf c.H := Subgroup.mem_subgroupOf.mpr hxy
  exact hx (Subgroup.mem_subgroupOf.mp ((hiff.mp hK).mpr hyK))

private lemma mem_H0_of_not_mem_left_not_mem_right (c : Hyp11 G) (h12 : Hyp12 c)
    {x y : ↥c.H} (hx : (x : G) ∉ c.H0) (hy : (y : G) ∉ c.H0) :
    ((x * y : ↥c.H) : G) ∈ c.H0 := by
  have hiff := Subgroup.mul_mem_iff_of_index_two (G := ↥c.H)
    (H0_index c h12) (a := x) (b := y)
  have hxK : x ∉ c.H0.subgroupOf c.H := by
    intro hxh
    exact hx (Subgroup.mem_subgroupOf.mp hxh)
  have hyK : y ∉ c.H0.subgroupOf c.H := by
    intro hyh
    exact hy (Subgroup.mem_subgroupOf.mp hyh)
  have hK : (x * y : ↥c.H) ∈ c.H0.subgroupOf c.H :=
    hiff.mpr (by simp [hxK, hyK])
  exact Subgroup.mem_subgroupOf.mp hK

/-- The `ε`-extension of a linear character `κ1` of `H0` to `H` (`ε = ±1`):
`κ1` on `H0`, and `ε·κ1(s⁻¹·g)` on the coset `s·H0`. -/
private noncomputable def tauExt (c : Hyp11 G) (h12 : Hyp12 c) (ε : ℂ)
    {κ1 : ClassFunction (↥c.H0)} (hκ1lin : IsLinearCharacter κ1) :
    ClassFunction (↥c.H) :=
  fun g => if hg : (g : G) ∈ c.H0 then κ1 ⟨(g : G), hg⟩
    else ε * κ1 ⟨c.s⁻¹ * (g : G), s_inv_mul_mem_H0_of_not_mem c h12 (g := g) hg⟩

/-- The extension is nonzero everywhere (`κ1` takes unit values). -/
private lemma tauExt_ne_zero (c : Hyp11 G) (h12 : Hyp12 c) (ε : ℂ) (εnz : ε ≠ 0)
    {κ1 : ClassFunction (↥c.H0)} (hκ1lin : IsLinearCharacter κ1) (g : ↥c.H) :
    tauExt c h12 ε hκ1lin g ≠ 0 := by
  unfold tauExt
  by_cases hg : (g : G) ∈ c.H0
  · simp [hg, linearChar_ne_zero hκ1lin]
  · simp [hg, εnz, linearChar_ne_zero hκ1lin]

/-- The extension is multiplicative (for `ε² = 1`). -/
private lemma tauExt_mul (c : Hyp11 G) (h12 : Hyp12 c) (ε : ℂ) (εsq : ε ^ 2 = 1)
    {κ1 : ClassFunction (↥c.H0)} (hκ1lin : IsLinearCharacter κ1)
    (hκ1fix : conjChar c.H0 (s_normalizes_H0 c h12) κ1 = κ1) :
    ∀ x y : ↥c.H, tauExt c h12 ε hκ1lin (x * y) =
      tauExt c h12 ε hκ1lin x * tauExt c h12 ε hκ1lin y := by
  classical
  intro x y
  have hsq : c.s⁻¹ = c.s := by
    exact inv_eq_of_mul_eq_one_right (by simpa [pow_two] using c.s_involution.2)
  have hss : c.s * c.s = 1 := by
    simpa [pow_two] using c.s_involution.2
  by_cases hx : (x : G) ∈ c.H0
  · by_cases hy : (y : G) ∈ c.H0
    · have hxy : (x : G) * (y : G) ∈ c.H0 := c.H0.mul_mem hx hy
      unfold tauExt
      simp [hx, hy, hxy]
      have hpr : (⟨(x : G), hx⟩ * ⟨(y : G), hy⟩ : ↥c.H0) =
          ⟨(x : G) * (y : G), c.H0.mul_mem hx hy⟩ := rfl
      rw [← hpr]
      rw [linearChar_mul hκ1lin]
    · have hxy0 : ((x * y : ↥c.H) : G) ∉ c.H0 :=
        not_mem_H0_of_mem_left_not_mem_right c h12 hx hy
      have hxy : (x : G) * (y : G) ∉ c.H0 := by
        simpa using hxy0
      unfold tauExt
      simp [hx, hy, hxy]
      have hm : c.s⁻¹ * (x : G) * c.s ∈ c.H0 := by
        simpa using conj_mem_of_index_two (H0 := c.H0) (H := c.H) (h12.H0_normal_in_H).1
          (H0_index c h12) (a := ⟨c.s, s_mem_H c⟩) (x := ⟨(x : G), hx⟩)
      have hxfix : κ1 ⟨c.s * (x : G) * c.s⁻¹, s_normalizes_H0 c h12 ⟨(x : G), hx⟩⟩ =
          κ1 ⟨(x : G), hx⟩ := kappaOne_conj_fix_pointwise c h12 hκ1fix ⟨(x : G), hx⟩
      have hfac : (c.s⁻¹ * ((x : G) * (y : G)) : G) =
          (c.s⁻¹ * (x : G) * c.s) * (c.s⁻¹ * (y : G)) := by
        group
      have hprod : (⟨c.s⁻¹ * (x : G) * c.s, hm⟩ *
          ⟨c.s⁻¹ * (y : G), s_inv_mul_mem_H0_of_not_mem c h12 (g := y) hy⟩ : ↥c.H0) =
          ⟨c.s⁻¹ * ((x : G) * (y : G)),
            s_inv_mul_mem_H0_of_not_mem c h12 (g := x * y) hxy0⟩ := by
        apply Subtype.ext
        change (c.s⁻¹ * (x : G) * c.s) * (c.s⁻¹ * (y : G)) = c.s⁻¹ * ((x : G) * (y : G))
        exact hfac.symm
      rw [← hprod]
      rw [linearChar_mul hκ1lin]
      have hxfix' : κ1 ⟨c.s⁻¹ * (x : G) * c.s, hm⟩ =
          κ1 ⟨(x : G), hx⟩ := by
        simpa [hsq] using hxfix
      rw [hxfix']
      ring
  · by_cases hy : (y : G) ∈ c.H0
    · have hxy0 : ((x * y : ↥c.H) : G) ∉ c.H0 :=
        not_mem_H0_of_not_mem_left_mem_right c h12 hx hy
      have hxy : (x : G) * (y : G) ∉ c.H0 := by
        simpa using hxy0
      unfold tauExt
      simp [hx, hy, hxy]
      have hprod : (⟨c.s⁻¹ * (x : G), s_inv_mul_mem_H0_of_not_mem c h12 (g := x) hx⟩ *
          ⟨(y : G), hy⟩ : ↥c.H0) =
          ⟨c.s⁻¹ * ((x : G) * (y : G)),
            s_inv_mul_mem_H0_of_not_mem c h12 (g := x * y) hxy0⟩ := by
        apply Subtype.ext
        change (c.s⁻¹ * (x : G)) * (y : G) = c.s⁻¹ * ((x : G) * (y : G))
        group
      rw [← hprod]
      rw [linearChar_mul hκ1lin]
      ring
    · have hxy0 : ((x * y : ↥c.H) : G) ∈ c.H0 :=
        mem_H0_of_not_mem_left_not_mem_right c h12 hx hy
      have hxy : (x : G) * (y : G) ∈ c.H0 := by
        simpa using hxy0
      unfold tauExt
      simp [hx, hy, hxy]
      have hm : c.s * (c.s⁻¹ * (x : G)) * c.s⁻¹ ∈ c.H0 :=
        s_normalizes_H0 c h12 ⟨c.s⁻¹ * (x : G), s_inv_mul_mem_H0_of_not_mem c h12 (g := x) hx⟩
      have hm2 : c.s * c.s * (c.s⁻¹ * (y : G)) ∈ c.H0 := by
        simpa [hss] using s_inv_mul_mem_H0_of_not_mem c h12 (g := y) hy
      have hxfix : κ1 ⟨c.s * (c.s⁻¹ * (x : G)) * c.s⁻¹, hm⟩ =
          κ1 ⟨c.s⁻¹ * (x : G), s_inv_mul_mem_H0_of_not_mem c h12 (g := x) hx⟩ :=
        kappaOne_conj_fix_pointwise c h12 hκ1fix ⟨c.s⁻¹ * (x : G), s_inv_mul_mem_H0_of_not_mem c h12 (g := x) hx⟩
      have hv : (⟨c.s * c.s * (c.s⁻¹ * (y : G)), hm2⟩ : ↥c.H0) =
          ⟨c.s⁻¹ * (y : G), s_inv_mul_mem_H0_of_not_mem c h12 (g := y) hy⟩ := by
        apply Subtype.ext
        simp [hss]
      have hfac : ((x : G) * (y : G) : G) =
          (c.s * (c.s⁻¹ * (x : G)) * c.s⁻¹) * (c.s * c.s * (c.s⁻¹ * (y : G))) := by
        group
      have hconj : (⟨(x : G) * (y : G), hxy⟩ : ↥c.H0) =
          ⟨(c.s * (c.s⁻¹ * (x : G)) * c.s⁻¹) * (c.s * c.s * (c.s⁻¹ * (y : G))),
            c.H0.mul_mem hm hm2⟩ := by
        apply Subtype.ext
        exact hfac
      rw [hconj]
      have hpr : (⟨c.s * (c.s⁻¹ * (x : G)) * c.s⁻¹, hm⟩ *
          ⟨c.s * c.s * (c.s⁻¹ * (y : G)), hm2⟩ : ↥c.H0) =
          ⟨(c.s * (c.s⁻¹ * (x : G)) * c.s⁻¹) * (c.s * c.s * (c.s⁻¹ * (y : G))),
            c.H0.mul_mem hm hm2⟩ := rfl
      rw [← hpr]
      rw [linearChar_mul hκ1lin]
      rw [hxfix]
      rw [hv]
      ring_nf
      rw [εsq]
      simp

/-- The extension is a linear character of `H`. -/
private lemma tauExt_isLinear (c : Hyp11 G) (h12 : Hyp12 c) (ε : ℂ) (εsq : ε ^ 2 = 1)
    {κ1 : ClassFunction (↥c.H0)} (hκ1lin : IsLinearCharacter κ1)
    (hκ1fix : conjChar c.H0 (s_normalizes_H0 c h12) κ1 = κ1) :
    IsLinearCharacter (tauExt c h12 ε hκ1lin) := by
  have εnz : ε ≠ 0 := by
    intro h
    rw [h] at εsq
    norm_num at εsq
  let φ : ↥c.H →* ℂˣ := {
    toFun := fun g => Units.mk0 (tauExt c h12 ε hκ1lin g) (tauExt_ne_zero c h12 ε εnz hκ1lin g)
    map_one' := by
      ext
      unfold tauExt
      simp [show (⟨(1 : G), c.H0.one_mem⟩ : ↥c.H0) = 1 from rfl, hκ1lin.2]
    map_mul' := by
      intro x y
      ext
      exact tauExt_mul c h12 ε εsq hκ1lin hκ1fix x y }
  convert isLinearCharacter_of_hom (G := ↥c.H) φ using 1
  funext g
  rfl

/-- The extension restricts to `κ1` on `H0`. -/
private lemma tauExt_apply_H0 (c : Hyp11 G) (h12 : Hyp12 c) (ε : ℂ)
    {κ1 : ClassFunction (↥c.H0)} (hκ1lin : IsLinearCharacter κ1)
    {h : G} (hh : h ∈ c.H0) :
    tauExt c h12 ε hκ1lin ⟨h, (h12.H0_normal_in_H).1 hh⟩ = κ1 ⟨h, hh⟩ := by
  unfold tauExt
  simp [hh]

/-- The extension has value `1` at the identity. -/
private lemma tauExt_apply_one (c : Hyp11 G) (h12 : Hyp12 c) (ε : ℂ)
    {κ1 : ClassFunction (↥c.H0)} (hκ1lin : IsLinearCharacter κ1) :
    tauExt c h12 ε hκ1lin 1 = 1 := by
  have h1 : (1 : G) ∈ c.H0 := c.H0.one_mem
  change tauExt c h12 ε hκ1lin ⟨(1 : G), (h12.H0_normal_in_H).1 h1⟩ = 1
  rw [tauExt_apply_H0 c h12 ε hκ1lin h1]
  exact hκ1lin.2

/-- `κ1^H = τ1 + τ1'` pointwise (the fixed-case Clifford formula). -/
private lemma induced_kappaOne_eq_tauExt_sum (c : Hyp11 G) (h12 : Hyp12 c)
    {κ1 : ClassFunction (↥c.H0)} (hκ1lin : IsLinearCharacter κ1)
    (hκ1fix : conjChar c.H0 (s_normalizes_H0 c h12) κ1 = κ1) :
    inducedFromSub (h12.H0_normal_in_H).1 κ1 =
      tauExt c h12 1 hκ1lin + tauExt c h12 (-1) hκ1lin := by
  funext g
  by_cases hg : (g : G) ∈ c.H0
  · have hg1 : ((tauExt c h12 1 hκ1lin + tauExt c h12 (-1) hκ1lin) g) =
        2 * κ1 ⟨(g : G), hg⟩ := by
      simp [tauExt, hg, two_mul]
    have hmain := induced_restrict_eq_add_conj c h12 (irreducibleCharacter_isClassFunction hκ1lin.1)
      ⟨(g : G), hg⟩
    have hfixpt : conjChar c.H0 (s_normalizes_H0 c h12) κ1 ⟨(g : G), hg⟩ = κ1 ⟨(g : G), hg⟩ := by
      rw [hκ1fix]
    have hmain' : inducedFromSub (h12.H0_normal_in_H).1 κ1 ⟨(g : G), (h12.H0_normal_in_H).1 hg⟩ =
        2 * κ1 ⟨(g : G), hg⟩ := by
      rw [hmain, hfixpt]
      ring
    rw [hg1]
    change inducedFromSub (h12.H0_normal_in_H).1 κ1 ⟨(g : G), (h12.H0_normal_in_H).1 hg⟩ =
      2 * κ1 ⟨(g : G), hg⟩
    exact hmain'
  · have hg2 : ((tauExt c h12 1 hκ1lin + tauExt c h12 (-1) hκ1lin) g) = 0 := by
      simp [tauExt, hg]
    rw [hg2]
    exact inducedFromSub_eq_zero_of_not_mem (H0 := c.H0) (H := c.H) (h12.H0_normal_in_H).1
      (H0_index c h12) hg

/-- The product of two linear characters is linear. -/
private lemma isLinearCharacter_mul (c : Hyp11 G) (h12 : Hyp12 c)
    {φ ψ : ClassFunction (↥c.H0)} (hφ : IsLinearCharacter φ) (hψ : IsLinearCharacter ψ) :
    IsLinearCharacter (φ * ψ) := by
  let φh := linearCharHom hφ
  let ψh := linearCharHom hψ
  convert isLinearCharacter_of_hom (G := ↥c.H0) (φh * ψh) using 1
  funext x
  rfl

/-- `λ^s = λ⁻¹` for `λ ∈ Λ` (`s` inverts `S0` and `U` is `s`-invariant, `λ`
is trivial on `U`). -/
private lemma LambdaChar_conj_eq_inv (c : Hyp11 G) (h12 : Hyp12 c)
    (l : LambdaHom c.H0 c.U) :
    conjChar c.H0 (s_normalizes_H0 c h12) (LambdaChar l.1) = (LambdaChar l.1)⁻¹ := by
  classical
  funext x
  change (l.1 ⟨c.s * (x : G) * c.s⁻¹, s_normalizes_H0 c h12 x⟩ : ℂ) = (l.1 x : ℂ)⁻¹
  rcases H0_eq_U_mul_S0 c h12 (x := x) with ⟨u, r, hx⟩
  have hsr : c.s * (r : G) * c.s⁻¹ = (r : G)⁻¹ := s_inverts_S0 c r.2
  have hsuU : c.s * (u : G) * c.s⁻¹ ∈ c.U := s_normalizes_U c u.2
  have hlu : l.1 ⟨c.s * (u : G) * c.s⁻¹, (h12.U_normal_in_H0).1 hsuU⟩ = 1 := by
    exact l.2 ⟨c.s * (u : G) * c.s⁻¹, (h12.U_normal_in_H0).1 hsuU⟩ hsuU
  have hsrS0 : c.s * (r : G) * c.s⁻¹ ∈ c.S0 := by
    rw [hsr]
    exact c.S0.inv_mem r.2
  have hval : l.1 ⟨c.s * (x : G) * c.s⁻¹, s_normalizes_H0 c h12 x⟩ =
      (l.1 ⟨(r : G), S0_le_H0 c r.2⟩)⁻¹ := by
    have hfac : (c.s * ((u : G) * (r : G)) * c.s⁻¹ : G) =
        (c.s * (u : G) * c.s⁻¹) * (c.s * (r : G) * c.s⁻¹) := by group
    have hsub : (⟨c.s * (x : G) * c.s⁻¹, s_normalizes_H0 c h12 x⟩ : ↥c.H0) =
        ⟨c.s * (u : G) * c.s⁻¹, (h12.U_normal_in_H0).1 hsuU⟩ *
          ⟨c.s * (r : G) * c.s⁻¹, S0_le_H0 c hsrS0⟩ := by
      apply Subtype.ext
      change (c.s * (x : G) * c.s⁻¹ : G) = (c.s * (u : G) * c.s⁻¹) * (c.s * (r : G) * c.s⁻¹)
      rw [hx]
      exact hfac
    rw [hsub]
    rw [map_mul]
    rw [hlu]
    have hlr : l.1 ⟨c.s * (r : G) * c.s⁻¹, S0_le_H0 c hsrS0⟩ =
        (l.1 ⟨(r : G), S0_le_H0 c r.2⟩)⁻¹ := by
      have hrv : (⟨c.s * (r : G) * c.s⁻¹, S0_le_H0 c hsrS0⟩ : ↥c.H0) =
          ⟨(r : G)⁻¹, S0_le_H0 c (c.S0.inv_mem r.2)⟩ := by
        apply Subtype.ext
        exact hsr
      rw [hrv]
      exact map_inv l.1 ⟨(r : G), S0_le_H0 c r.2⟩
    rw [hlr]
    simp
  have hxval : (l.1 x)⁻¹ = (l.1 ⟨(r : G), S0_le_H0 c r.2⟩)⁻¹ := by
    have hx2 : x = ⟨(u : G), (h12.U_normal_in_H0).1 u.2⟩ * ⟨(r : G), S0_le_H0 c r.2⟩ := by
      apply Subtype.ext
      exact hx
    rw [hx2]
    rw [map_mul]
    have hlu2 : l.1 ⟨(u : G), (h12.U_normal_in_H0).1 u.2⟩ = 1 :=
      l.2 ⟨(u : G), (h12.U_normal_in_H0).1 u.2⟩ u.2
    rw [hlu2]
    simp
  exact_mod_cast hval.trans hxval.symm

private lemma conj_kappa_apply (c : Hyp11 G) (h12 : Hyp12 c)
    {κ1 : ClassFunction (↥c.H0)} (hκ1lin : IsLinearCharacter κ1)
    (hκ1fix : conjChar c.H0 (s_normalizes_H0 c h12) κ1 = κ1)
    (l : LambdaHom c.H0 c.U) (x : ↥c.H0) :
    conjChar c.H0 (s_normalizes_H0 c h12) (kappa c κ1 l) x = (l.1 x⁻¹) * κ1 x := by
  classical
  have hcj := congrFun (LambdaChar_conj_eq_inv c h12 l) x
  have hcf := congrFun hκ1fix x
  have hcj' : (l.1 ⟨c.s * (x : G) * c.s⁻¹, s_normalizes_H0 c h12 x⟩ : ℂ) = (l.1 x : ℂ)⁻¹ := by
    simpa [LambdaChar, conjChar, conjMonoidHom] using hcj
  have hl : l.1 ⟨c.s * (x : G) * c.s⁻¹, s_normalizes_H0 c h12 x⟩ = (l.1 x)⁻¹ := by
    exact_mod_cast hcj' 
  have hk : κ1 ⟨c.s * (x : G) * c.s⁻¹, s_normalizes_H0 c h12 x⟩ = κ1 x := by
    simpa [conjChar, conjMonoidHom] using hcf
  simp [kappa, LambdaChar, conjChar, conjMonoidHom, hl, hk, map_inv]

/-- `(κ1·λ)^s ≠ κ1·λ` for `λ² ≠ 1` (`κ1` fixed, `λ^s = λ⁻¹`). -/
private lemma kappa_conj_ne_of_sq_ne_one (c : Hyp11 G) (h12 : Hyp12 c)
    {κ1 : ClassFunction (↥c.H0)} (hκ1lin : IsLinearCharacter κ1)
    (hκ1fix : conjChar c.H0 (s_normalizes_H0 c h12) κ1 = κ1)
    (l : LambdaHom c.H0 c.U) (hlsq : l ^ 2 ≠ 1) :
    conjChar c.H0 (s_normalizes_H0 c h12) (kappa c κ1 l) ≠ kappa c κ1 l := by
  intro h
  have hf : ∀ x : ↥c.H0, (l.1 x)⁻¹ = l.1 x := by
    intro x
    have hx := congrFun h x
    have hc := conj_kappa_apply c h12 hκ1lin hκ1fix l x
    have hk1 : (κ1 x : ℂ) ≠ 0 := linearChar_ne_zero hκ1lin x
    have hx' : (l.1 x⁻¹ : ℂ) * κ1 x = (l.1 x : ℂ) * κ1 x := by
      rw [← hc]
      simpa [kappa, LambdaChar] using hx
    have hlinv : (l.1 x⁻¹ : ℂ) = (l.1 x : ℂ) := mul_right_cancel₀ hk1 hx'
    have hm := congrArg (fun z : ℂˣ => (z : ℂ)) (map_inv l.1 x)
    exact_mod_cast (hm.symm.trans hlinv)
  have hl : l⁻¹ = l := by
    apply Subtype.ext
    apply MonoidHom.ext
    intro x
    change (l.1 x)⁻¹ = l.1 x
    exact hf x
  have hsq : l ^ 2 = 1 := by
    rw [pow_two]
    have hstep : l * l = l * l⁻¹ := congrArg (fun a => l * a) hl.symm
    rw [hstep]
    exact mul_inv_cancel l
  exact hlsq hsq

/-- `ΛChar l` is a linear character for every `l ∈ Λ`. -/
private lemma LambdaChar_isLinear (c : Hyp11 G) (l : LambdaHom c.H0 c.U) :
    IsLinearCharacter (LambdaChar l.1) := by
  convert isLinearCharacter_of_hom (G := ↥c.H0) (l.1) using 1
  rfl

/-- `t1·t2 ∈ S0` (`S0 = ⟨t1·t2⟩`). -/
private lemma t1t2_mem_S0 (c : Hyp11 G) : c.t1 * c.t2 ∈ (c.S0 : Subgroup G) := by
  rw [c.S0_eq_zpowers]
  exact Subgroup.mem_zpowers (c.t1 * c.t2)

/-- `λ2(t1·t2) = −1`: `λ2` is nontrivial of order two and kills `U` and
`S' = ⟨(t1·t2)²⟩`, while `S0 = ⟨t1·t2⟩`, so `λ2(t1·t2) = ±1` and the
`+1` alternative would make `λ2` trivial on all of `H0 = U·S0`. -/
private lemma lambdaTwo_t12_eq_neg_one (c : Hyp11 G) (h12 : Hyp12 c) :
    (lambdaTwo c h12).1 ⟨c.t1 * c.t2, S0_le_H0 c (t1t2_mem_S0 c)⟩ = (-1 : ℂˣ) := by
  classical
  let l : LambdaHom c.H0 c.U := lambdaTwo c h12
  let x : ↥c.H0 := ⟨c.t1 * c.t2, S0_le_H0 c (t1t2_mem_S0 c)⟩
  have hsqx : l.1 x * l.1 x = 1 := by
    have h1 : (l.1 : ↥c.H0 →* ℂˣ) ^ 2 = 1 :=
      congrArg Subtype.val (by simpa [l] using lambdaTwo_sq_eq_one c h12)
    have hx := congrArg (fun z : ↥c.H0 →* ℂˣ => z x) h1
    simpa [pow_two] using hx
  have hc : (l.1 x : ℂ) = 1 ∨ (l.1 x : ℂ) = -1 := by
    exact sq_eq_one_iff.mp (by simpa [pow_two] using congrArg (fun z : ℂˣ => (z : ℂ)) hsqx)
  by_cases h1 : l.1 x = 1
  · exfalso
    have hl1 : l = 1 := by
      apply Subtype.ext
      apply MonoidHom.ext
      intro y
      rcases H0_eq_U_mul_S0 c h12 (x := y) with ⟨u, r, hy⟩
      have hyEq : y = ⟨(u : G), (h12.U_normal_in_H0).1 u.2⟩ * ⟨(r : G), S0_le_H0 c r.2⟩ := by
        apply Subtype.ext
        exact hy
      rw [hyEq]
      rw [map_mul]
      have hlu : l.1 ⟨(u : G), (h12.U_normal_in_H0).1 u.2⟩ = 1 :=
        l.2 ⟨(u : G), (h12.U_normal_in_H0).1 u.2⟩ u.2
      rw [hlu]
      have hlr : l.1 ⟨(r : G), S0_le_H0 c r.2⟩ = 1 := by
        rcases (Subgroup.mem_zpowers_iff.mp (by simpa [c.S0_eq_zpowers] using r.2)) with ⟨n, hn⟩
        have hrS0 : (c.t1 * c.t2) ^ n ∈ (c.S0 : Subgroup G) := by
          rw [c.S0_eq_zpowers]
          exact Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩
        have heq : (⟨(r : G), S0_le_H0 c r.2⟩ : ↥c.H0) =
            ⟨c.t1 * c.t2, S0_le_H0 c (t1t2_mem_S0 c)⟩ ^ n := by
          apply Subtype.ext
          rw [Subgroup.coe_zpow]
          exact hn.symm
        rw [heq]
        rw [map_zpow l.1 ⟨c.t1 * c.t2, S0_le_H0 c (t1t2_mem_S0 c)⟩]
        rw [h1]
        simp
      rw [hlr]
      simp
    exact lambdaTwo_ne_one c h12 (by simpa [l] using hl1)
  · rcases hc with hc1 | hc2
    · exfalso
      exact h1 (by apply Units.ext; exact hc1)
    · apply Units.ext
      exact hc2

/-- The value of the `ε`-extension at `t1·t2` is `κ(t1·t2)` (the product
lies in `H0`). -/
private lemma tauExt_apply_t1t2 (c : Hyp11 G) (h12 : Hyp12 c) (ε : ℂ)
    {κ : ClassFunction (↥c.H0)} (hκlin : IsLinearCharacter κ) :
    tauExt c h12 ε hκlin
      ⟨c.t1 * c.t2, (h12.H0_normal_in_H).1 (S0_le_H0 c (t1t2_mem_S0 c))⟩ =
      κ ⟨c.t1 * c.t2, S0_le_H0 c (t1t2_mem_S0 c)⟩ := by
  exact tauExt_apply_H0 c h12 ε hκlin (S0_le_H0 c (t1t2_mem_S0 c))

/-- `c(τ_ε) = (k1 + x·k2)²` where `x = τ_ε(t1·t2)`: `τ_ε(t1)² = 1`,
`τ_ε(t2) = x·τ_ε(t1)` by multiplicativity, so
`(k1·τ(t1) + k2·τ(t2))² = (k1 + x·k2)²·τ(t1)² = (k1 + x·k2)²`. -/
private lemma cθ_tauExt_of_prod (c : Hyp11 G) (h12 : Hyp12 c) (ε : ℂ) (εsq : ε ^ 2 = 1)
    {κ : ClassFunction (↥c.H0)} (hκlin : IsLinearCharacter κ)
    (hκfix : conjChar c.H0 (s_normalizes_H0 c h12) κ = κ)
    (x : ℂ) (ht12 : tauExt c h12 ε hκlin
      ⟨c.t1 * c.t2, (h12.H0_normal_in_H).1 (S0_le_H0 c (t1t2_mem_S0 c))⟩ = x) :
    lemma_2_2_cθ c (tauExt c h12 ε hκlin) = ((c.k1 : ℂ) + x * (c.k2 : ℂ)) ^ 2 := by
  classical
  let τ : ClassFunction (↥c.H) := tauExt c h12 ε hκlin
  unfold lemma_2_2_cθ
  rw [lemma_2_2_tH_zero, lemma_2_2_tH_one]
  change ((c.k1 : ℂ) * τ ⟨c.t1, t1_mem_H c⟩ + (c.k2 : ℂ) * τ ⟨c.t2, t2_mem_H c⟩) ^ 2 / τ 1 =
    ((c.k1 : ℂ) + x * (c.k2 : ℂ)) ^ 2
  have hτ1 : τ 1 = 1 := by
    simpa [τ] using tauExt_apply_one c h12 ε hκlin
  have hτmul : ∀ u v : ↥c.H, τ (u * v) = τ u * τ v := by
    intro u v
    simpa [τ] using tauExt_mul c h12 ε εsq hκlin hκfix u v
  have ht12' : τ ⟨c.t1 * c.t2, (h12.H0_normal_in_H).1 (S0_le_H0 c (t1t2_mem_S0 c))⟩ = x := by
    simpa [τ] using ht12
  have ht12eq : (⟨c.t1, t1_mem_H c⟩ * ⟨c.t2, t2_mem_H c⟩ : ↥c.H) =
      ⟨c.t1 * c.t2, (h12.H0_normal_in_H).1 (S0_le_H0 c (t1t2_mem_S0 c))⟩ := by
    apply Subtype.ext
    rfl
  have hab : τ ⟨c.t1, t1_mem_H c⟩ * τ ⟨c.t2, t2_mem_H c⟩ = x := by
    have hm := hτmul ⟨c.t1, t1_mem_H c⟩ ⟨c.t2, t2_mem_H c⟩
    rw [ht12eq] at hm
    rw [ht12'] at hm
    exact hm.symm
  have ha2 : τ ⟨c.t1, t1_mem_H c⟩ ^ 2 = 1 := by
    have ht11 : (⟨c.t1, t1_mem_H c⟩ * ⟨c.t1, t1_mem_H c⟩ : ↥c.H) = 1 := by
      apply Subtype.ext
      change c.t1 * c.t1 = (1 : G)
      simpa [pow_two] using c.t1_involution.2
    have hm := hτmul ⟨c.t1, t1_mem_H c⟩ ⟨c.t1, t1_mem_H c⟩
    rw [ht11] at hm
    rw [hτ1] at hm
    simpa [pow_two] using hm.symm
  have ha1 : τ ⟨c.t1, t1_mem_H c⟩ ≠ 0 := by
    intro h0
    have h0' : (τ ⟨c.t1, t1_mem_H c⟩) ^ 2 = 0 := by rw [h0]; norm_num
    rw [ha2] at h0'
    norm_num at h0'
  have hb : τ ⟨c.t2, t2_mem_H c⟩ = x * τ ⟨c.t1, t1_mem_H c⟩ := by
    have hb1 : τ ⟨c.t2, t2_mem_H c⟩ = x * (τ ⟨c.t1, t1_mem_H c⟩)⁻¹ := by
      field_simp [ha1]
      rw [mul_comm]
      exact hab
    rw [hb1]
    rw [inv_eq_of_mul_eq_one_right (by simpa [pow_two] using ha2)]
  rw [hb, hτ1]
  simp only [div_one]
  ring_nf
  rw [ha2]
  ring

/-- `Σ_θ c(θ)·(θ, κ^H)_H = 2·(k1 + x·k2)²` for an `s`-fixed linear character
`κ` with `κ(t1·t2) = x`: `κ^H = τ1 + τ1'` with `c(τ_ε) = (k1 + x·k2)²`. -/
private lemma sum_cθ_induced_of_decomp (c : Hyp11 G) (h12 : Hyp12 c)
    {κ : ClassFunction (↥c.H0)} (hκlin : IsLinearCharacter κ)
    (hκfix : conjChar c.H0 (s_normalizes_H0 c h12) κ = κ)
    (x : ℂ) (ht12 : κ ⟨c.t1 * c.t2, S0_le_H0 c (t1t2_mem_S0 c)⟩ = x) :
    (∑ θ : Irr (↥c.H), lemma_2_2_cθ c θ.1 * scalarProduct (↥c.H) θ.1
        (inducedFromSub (h12.H0_normal_in_H).1 κ)) = 2 * ((c.k1 : ℂ) + x * (c.k2 : ℂ)) ^ 2 := by
  classical
  let τ1 : ClassFunction (↥c.H) := tauExt c h12 1 hκlin
  let τ1' : ClassFunction (↥c.H) := tauExt c h12 (-1) hκlin
  have hτ1 : IsIrreducibleCharacter τ1 := (tauExt_isLinear c h12 1 (by norm_num) hκlin hκfix).1
  have hτ1' : IsIrreducibleCharacter τ1' := (tauExt_isLinear c h12 (-1) (by norm_num) hκlin hκfix).1
  have hind : inducedFromSub (h12.H0_normal_in_H).1 κ = τ1 + τ1' := by
    simpa [τ1, τ1'] using induced_kappaOne_eq_tauExt_sum c h12 hκlin hκfix
  rw [hind]
  have hτ1t12 : tauExt c h12 1 hκlin
      ⟨c.t1 * c.t2, (h12.H0_normal_in_H).1 (S0_le_H0 c (t1t2_mem_S0 c))⟩ = x := by
    rw [tauExt_apply_H0 c h12 1 hκlin (S0_le_H0 c (t1t2_mem_S0 c))]
    exact ht12
  have hτ1't12 : tauExt c h12 (-1) hκlin
      ⟨c.t1 * c.t2, (h12.H0_normal_in_H).1 (S0_le_H0 c (t1t2_mem_S0 c))⟩ = x := by
    rw [tauExt_apply_H0 c h12 (-1) hκlin (S0_le_H0 c (t1t2_mem_S0 c))]
    exact ht12
  have hc1 : lemma_2_2_cθ c τ1 = ((c.k1 : ℂ) + x * (c.k2 : ℂ)) ^ 2 := by
    simpa [τ1] using cθ_tauExt_of_prod c h12 1 (by norm_num) hκlin hκfix x hτ1t12
  have hc2 : lemma_2_2_cθ c τ1' = ((c.k1 : ℂ) + x * (c.k2 : ℂ)) ^ 2 := by
    simpa [τ1'] using cθ_tauExt_of_prod c h12 (-1) (by norm_num) hκlin hκfix x hτ1't12
  calc
    (∑ θ : Irr (↥c.H), lemma_2_2_cθ c θ.1 * scalarProduct (↥c.H) θ.1 (τ1 + τ1'))
        = (∑ θ : Irr (↥c.H), lemma_2_2_cθ c θ.1 *
            (scalarProduct (↥c.H) θ.1 τ1 + scalarProduct (↥c.H) θ.1 τ1')) := by
            refine Finset.sum_congr rfl ?_
            intro θ hθ
            congr 1
            exact scalarProduct_add_right θ.1 τ1 τ1'
    _ = (∑ θ : Irr (↥c.H), lemma_2_2_cθ c θ.1 * scalarProduct (↥c.H) θ.1 τ1) +
          (∑ θ : Irr (↥c.H), lemma_2_2_cθ c θ.1 * scalarProduct (↥c.H) θ.1 τ1') := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl ?_
            intro θ hθ
            rw [mul_add]
    _ = ((c.k1 : ℂ) + x * (c.k2 : ℂ)) ^ 2 + ((c.k1 : ℂ) + x * (c.k2 : ℂ)) ^ 2 := by
            rw [sum_cθ_mul_scalarProduct_irreducible c hτ1]
            rw [sum_cθ_mul_scalarProduct_irreducible c hτ1']
            rw [hc1, hc2]
    _ = 2 * ((c.k1 : ℂ) + x * (c.k2 : ℂ)) ^ 2 := by ring

/-- Lemma 2.2, case 2: `μ = κ1`, `ν = κ1·l` with `l² ≠ 1`. Here
`κ1^H = τ1 + τ1'` with `c(τ1) + c(τ1') = 2k²` (values `τ_ε(t1) = τ_ε(t2) = ±1`),
while `ν^H` is irreducible (Clifford, `ν^s ≠ ν`) and vanishes at `t1, t2`. -/
private lemma lemma_2_2_W_kappaOne_l_case (c : Hyp11 G) (h12 : Hyp12 c)
    {κ1 : ClassFunction (↥c.H0)} (hκ1lin : IsLinearCharacter κ1)
    (hκ1S0 : ∀ x : ↥c.H0, (x : G) ∈ (c.S0 : Subgroup G) → κ1 x = 1)
    (hκ1comm : ∀ x : ↥c.H0, (x : G) ∈ ⁅(c.S : Subgroup G), c.U⁆ → κ1 x = 1)
    (l : LambdaHom c.H0 c.U) (hlsq : l ^ 2 ≠ 1) :
    lemma_2_2_W c (lemma_2_2_delta c h12 κ1 (kappa c κ1 l)) = 2 * (c.k : ℂ) ^ 2 := by
  classical
  let α : ClassFunction (↥c.H) := inducedFromSub (h12.H0_normal_in_H).1 κ1
  let β : ClassFunction (↥c.H) := inducedFromSub (h12.H0_normal_in_H).1 (kappa c κ1 l)
  have hκ1fix : conjChar c.H0 (s_normalizes_H0 c h12) κ1 = κ1 :=
    kappaOne_fixed_by_s c h12 hκ1lin hκ1S0 hκ1comm
  have hκlirr : IsIrreducibleCharacter (kappa c κ1 l) := by
    exact (isLinearCharacter_mul c h12 (LambdaChar_isLinear c l) hκ1lin).1
  have hβ : IsIrreducibleCharacter β := by
    simpa [β] using induced_irreducible_of_ne_conj c h12
      (μ := ⟨kappa c κ1 l, hκlirr⟩) (kappa_conj_ne_of_sq_ne_one c h12 hκ1lin hκ1fix l hlsq)
  have hδ : lemma_2_2_delta c h12 κ1 (kappa c κ1 l) = α - β := by
    unfold lemma_2_2_delta
    rw [inducedFromSub_sub c h12 κ1 (kappa c κ1 l)]
  rw [lemma_2_2_W_eq_sum_cθ c h12 (lemma_2_2_delta c h12 κ1 (kappa c κ1 l))]
  rw [hδ]
  calc
    (∑ θ : Irr (↥c.H), lemma_2_2_cθ c θ.1 * scalarProduct (↥c.H) θ.1 (α - β))
        = (∑ θ : Irr (↥c.H), lemma_2_2_cθ c θ.1 *
            (scalarProduct (↥c.H) θ.1 α - scalarProduct (↥c.H) θ.1 β)) := by
            refine Finset.sum_congr rfl ?_
            intro θ hθ
            congr 1
            exact scalarProduct_sub_right θ.1 α β
    _ = (∑ θ : Irr (↥c.H), lemma_2_2_cθ c θ.1 * scalarProduct (↥c.H) θ.1 α) -
          (∑ θ : Irr (↥c.H), lemma_2_2_cθ c θ.1 * scalarProduct (↥c.H) θ.1 β) := by
            rw [← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl ?_
            intro θ hθ
            rw [mul_sub]
    _ = 2 * (c.k : ℂ) ^ 2 := by
            have hκ1t12 : κ1 ⟨c.t1 * c.t2, S0_le_H0 c (t1t2_mem_S0 c)⟩ = 1 :=
              hκ1S0 ⟨c.t1 * c.t2, S0_le_H0 c (t1t2_mem_S0 c)⟩ (t1t2_mem_S0 c)
            have hk' : (c.k : ℂ) = (c.k1 : ℂ) + (c.k2 : ℂ) := by
              simp [Hyp11.k]
            have hsumα : (∑ θ : Irr (↥c.H), lemma_2_2_cθ c θ.1 * scalarProduct (↥c.H) θ.1 α) =
                2 * (c.k : ℂ) ^ 2 := by
              have hsum' : (∑ θ : Irr (↥c.H), lemma_2_2_cθ c θ.1 * scalarProduct (↥c.H) θ.1 α) =
                  2 * ((c.k1 : ℂ) + (c.k2 : ℂ)) ^ 2 := by
                simpa [α] using sum_cθ_induced_of_decomp c h12 hκ1lin hκ1fix (1 : ℂ) hκ1t12
              rw [hsum']
              exact congrArg (fun z : ℂ => 2 * z ^ 2) hk'.symm
            have hsumβ : (∑ θ : Irr (↥c.H), lemma_2_2_cθ c θ.1 * scalarProduct (↥c.H) θ.1 β) = 0 := by
              rw [sum_cθ_mul_scalarProduct_irreducible c hβ]
              exact cθ_zero_of_vanishes_at_tH c hβ
                (by simpa [β] using induced_delta_vanishes_at_tH c h12 (kappa c κ1 l) 0)
                (by simpa [β] using induced_delta_vanishes_at_tH c h12 (kappa c κ1 l) 1)
            rw [hsumα, hsumβ]
            norm_num

/-- Lemma 2.2, case 3: `μ = κ1`, `ν = κ2 = κ1·λ2`, `k1 = k2`. Here
`κ2^s = κ2` (`λ2^s = λ2⁻¹ = λ2`), so `κ2^H = τ2 + τ2'` with
`τ2(t1)·τ2(t2) = κ2(t1·t2) = −1` and `c(τ2) = c(τ2') = (k1−k2)² = 0`. -/
private lemma lemma_2_2_W_kappaOne_lambdaTwo_case (c : Hyp11 G) (h12 : Hyp12 c)
    {κ1 : ClassFunction (↥c.H0)} (hκ1lin : IsLinearCharacter κ1)
    (hκ1S0 : ∀ x : ↥c.H0, (x : G) ∈ (c.S0 : Subgroup G) → κ1 x = 1)
    (hκ1comm : ∀ x : ↥c.H0, (x : G) ∈ ⁅(c.S : Subgroup G), c.U⁆ → κ1 x = 1)
    (hk12 : c.k1 = c.k2) :
    lemma_2_2_W c (lemma_2_2_delta c h12 κ1 (kappa c κ1 (lambdaTwo c h12))) =
      2 * (c.k : ℂ) ^ 2 := by
  classical
  let l2 : LambdaHom c.H0 c.U := lambdaTwo c h12
  let κ2 : ClassFunction (↥c.H0) := kappa c κ1 l2
  let α : ClassFunction (↥c.H) := inducedFromSub (h12.H0_normal_in_H).1 κ1
  let β : ClassFunction (↥c.H) := inducedFromSub (h12.H0_normal_in_H).1 κ2
  have hκ1fix : conjChar c.H0 (s_normalizes_H0 c h12) κ1 = κ1 :=
    kappaOne_fixed_by_s c h12 hκ1lin hκ1S0 hκ1comm
  have hl2lin : IsLinearCharacter (LambdaChar l2.1) := by
    simpa [l2] using LambdaChar_isLinear c (lambdaTwo c h12)
  have hκ2lin : IsLinearCharacter κ2 := by
    simpa [κ2, l2, kappa] using isLinearCharacter_mul c h12 hl2lin hκ1lin
  have hl2inv : (LambdaChar l2.1)⁻¹ = LambdaChar l2.1 := by
    funext x
    change ((l2.1 x : ℂ)⁻¹) = (l2.1 x : ℂ)
    have hsqx : l2.1 x * l2.1 x = 1 := by
      have h1 : (l2.1 : ↥c.H0 →* ℂˣ) ^ 2 = 1 :=
        congrArg Subtype.val (by simpa [l2] using lambdaTwo_sq_eq_one c h12)
      have hx := congrArg (fun z : ↥c.H0 →* ℂˣ => z x) h1
      simpa [pow_two] using hx
    have hinv : (l2.1 x)⁻¹ = l2.1 x := inv_eq_of_mul_eq_one_right hsqx
    have hc : (((l2.1 x)⁻¹ : ℂˣ) : ℂ) = (l2.1 x : ℂ) := congrArg (fun z : ℂˣ => (z : ℂ)) hinv
    rw [← Units.val_inv_eq_inv_val (l2.1 x)]
    exact hc
  have hconj_mul : conjChar c.H0 (s_normalizes_H0 c h12) (LambdaChar l2.1 * κ1) =
      conjChar c.H0 (s_normalizes_H0 c h12) (LambdaChar l2.1) *
        conjChar c.H0 (s_normalizes_H0 c h12) κ1 := by
    funext x
    rfl
  have hκ2fix : conjChar c.H0 (s_normalizes_H0 c h12) κ2 = κ2 := by
    change conjChar c.H0 (s_normalizes_H0 c h12) (LambdaChar l2.1 * κ1) = LambdaChar l2.1 * κ1
    rw [hconj_mul, hκ1fix, LambdaChar_conj_eq_inv c h12 l2, hl2inv]
  have hκ2t12 : κ2 ⟨c.t1 * c.t2, S0_le_H0 c (t1t2_mem_S0 c)⟩ = -1 := by
    have hκ1t12 : κ1 ⟨c.t1 * c.t2, S0_le_H0 c (t1t2_mem_S0 c)⟩ = 1 :=
      hκ1S0 ⟨c.t1 * c.t2, S0_le_H0 c (t1t2_mem_S0 c)⟩ (t1t2_mem_S0 c)
    have hl2t12 : (lambdaTwo c h12).1 ⟨c.t1 * c.t2, S0_le_H0 c (t1t2_mem_S0 c)⟩ = (-1 : ℂˣ) :=
      lambdaTwo_t12_eq_neg_one c h12
    change (LambdaChar l2.1 * κ1) ⟨c.t1 * c.t2, S0_le_H0 c (t1t2_mem_S0 c)⟩ = -1
    rw [Pi.mul_apply]
    rw [LambdaChar]
    rw [hκ1t12]
    have hc := congrArg (fun z : ℂˣ => (z : ℂ)) (by simpa [l2] using hl2t12)
    rw [hc]
    simp
  have hδ : lemma_2_2_delta c h12 κ1 κ2 = α - β := by
    unfold lemma_2_2_delta
    rw [inducedFromSub_sub c h12 κ1 κ2]
  rw [lemma_2_2_W_eq_sum_cθ c h12 (lemma_2_2_delta c h12 κ1 κ2)]
  rw [hδ]
  calc
    (∑ θ : Irr (↥c.H), lemma_2_2_cθ c θ.1 * scalarProduct (↥c.H) θ.1 (α - β))
        = (∑ θ : Irr (↥c.H), lemma_2_2_cθ c θ.1 *
            (scalarProduct (↥c.H) θ.1 α - scalarProduct (↥c.H) θ.1 β)) := by
            refine Finset.sum_congr rfl ?_
            intro θ hθ
            congr 1
            exact scalarProduct_sub_right θ.1 α β
    _ = (∑ θ : Irr (↥c.H), lemma_2_2_cθ c θ.1 * scalarProduct (↥c.H) θ.1 α) -
          (∑ θ : Irr (↥c.H), lemma_2_2_cθ c θ.1 * scalarProduct (↥c.H) θ.1 β) := by
            rw [← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl ?_
            intro θ hθ
            rw [mul_sub]
    _ = 2 * (c.k : ℂ) ^ 2 := by
            have hκ1t12 : κ1 ⟨c.t1 * c.t2, S0_le_H0 c (t1t2_mem_S0 c)⟩ = 1 :=
              hκ1S0 ⟨c.t1 * c.t2, S0_le_H0 c (t1t2_mem_S0 c)⟩ (t1t2_mem_S0 c)
            have hk' : (c.k : ℂ) = (c.k1 : ℂ) + (c.k2 : ℂ) := by
              simp [Hyp11.k]
            have hsumα : (∑ θ : Irr (↥c.H), lemma_2_2_cθ c θ.1 * scalarProduct (↥c.H) θ.1 α) =
                2 * (c.k : ℂ) ^ 2 := by
              have hsum' : (∑ θ : Irr (↥c.H), lemma_2_2_cθ c θ.1 * scalarProduct (↥c.H) θ.1 α) =
                  2 * ((c.k1 : ℂ) + (c.k2 : ℂ)) ^ 2 := by
                simpa [α] using sum_cθ_induced_of_decomp c h12 hκ1lin hκ1fix (1 : ℂ) hκ1t12
              rw [hsum']
              exact congrArg (fun z : ℂ => 2 * z ^ 2) hk'.symm
            have hsumβ : (∑ θ : Irr (↥c.H), lemma_2_2_cθ c θ.1 * scalarProduct (↥c.H) θ.1 β) = 0 := by
              have hsum' : (∑ θ : Irr (↥c.H), lemma_2_2_cθ c θ.1 * scalarProduct (↥c.H) θ.1 β) =
                  2 * ((c.k1 : ℂ) - (c.k2 : ℂ)) ^ 2 := by
                simpa [β, κ2, l2, sub_eq_add_neg] using sum_cθ_induced_of_decomp c h12 hκ2lin hκ2fix (-1) hκ2t12
              rw [hsum']
              rw [hk12]
              ring
            rw [hsumα, hsumβ]
            norm_num

public lemma lemma_2_2_V_zero_of_pair (c : Hyp11 G) (h12 : Hyp12 c)
    {μ ν : Irr (↥c.H0)} (hEq : μ.1 ∈ orbit c.H0 c.U ν.1)
    (hμs : conjChar c.H0 (s_normalizes_H0 c h12) μ.1 ≠ μ.1)
    (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 ≠ ν.1) :
    (c.H.index : ℂ) * (∑ χ : Irr G, (χ.1 c.t ^ 2 / χ.1 1) *
      scalarProduct G χ.1 (inducedClassFunction c.H0 (μ.1 - ν.1))) = 0 := by
  change lemma_2_2_V c μ.1 ν.1 = 0
  rw [lemma_2_2_V_eq_W c h12 hEq]
  exact lemma_2_2_W_tau_case c h12 hμs hνs

/-- Lemma 2.2, case 1 in bare-sum form: the sum without the nonzero
`(c.H.index : ℂ)` factor vanishes. -/
public lemma lemma_2_2_V_zero_of_pair_sum (c : Hyp11 G) (h12 : Hyp12 c)
    {μ ν : Irr (↥c.H0)} (hEq : μ.1 ∈ orbit c.H0 c.U ν.1)
    (hμs : conjChar c.H0 (s_normalizes_H0 c h12) μ.1 ≠ μ.1)
    (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 ≠ ν.1) :
    (∑ χ : Irr G, (χ.1 c.t ^ 2 / χ.1 1) *
      scalarProduct G χ.1 (inducedClassFunction c.H0 (μ.1 - ν.1))) = 0 := by
  have hV : lemma_2_2_V c μ.1 ν.1 = 0 := by
    change (c.H.index : ℂ) * (∑ χ : Irr G, (χ.1 c.t ^ 2 / χ.1 1) *
      scalarProduct G χ.1 (inducedClassFunction c.H0 (μ.1 - ν.1))) = 0
    exact lemma_2_2_V_zero_of_pair c h12 hEq hμs hνs
  unfold lemma_2_2_V at hV
  have hne : (c.H.index : ℂ) ≠ 0 := by
    have hpos' : c.H.index ≠ 0 := by
      intro h0
      have hG : c.H.index * Nat.card (↥c.H) = Nat.card G := Subgroup.index_mul_card c.H
      have hGpos : 0 < c.H.index * Nat.card (↥c.H) := by
        rw [hG]
        exact Nat.card_pos (α := G)
      rw [h0] at hGpos
      simp at hGpos
    exact_mod_cast hpos'
  exact (mul_eq_zero.mp hV).resolve_left hne

/-- Lemma 2.2: for equivalent `μ, ν ∈ Irr(H0)`, `V = 0` when `μ^s ≠ μ` and
`ν^s ≠ ν`, `V = 2k²` when `μ = κ1` and `ν = κi` (`i ≥ 3`), and `V = 2k²`
when `μ = κ1`, `ν = κ2` and `k1 = k2`. -/
public theorem lemma_2_2 (c : Hyp11 G) (h12 : Hyp12 c) {μ ν : Irr (↥c.H0)}
    (hEq : μ.1 ∈ orbit c.H0 c.U ν.1) {κ1 : ClassFunction (↥c.H0)}
    (hκ1lin : IsLinearCharacter κ1)
    (hκ1S0 : ∀ x : ↥c.H0, (x : G) ∈ (c.S0 : Subgroup G) → κ1 x = 1)
    (hκ1comm : ∀ x : ↥c.H0, (x : G) ∈ ⁅(c.S : Subgroup G), c.U⁆ → κ1 x = 1) :
    (conjChar c.H0 (s_normalizes_H0 c h12) μ.1 ≠ μ.1 →
      conjChar c.H0 (s_normalizes_H0 c h12) ν.1 ≠ ν.1 → lemma_2_2_V c μ.1 ν.1 = 0) ∧
    (μ.1 = κ1 → (∃ l : LambdaHom c.H0 c.U, l ^ 2 ≠ 1 ∧ ν.1 = kappa c κ1 l) →
      lemma_2_2_V c μ.1 ν.1 = (2 * c.k ^ 2 : ℂ)) ∧
    (μ.1 = κ1 → ν.1 = kappa c κ1 (lambdaTwo c h12) → c.k1 = c.k2 →
      lemma_2_2_V c μ.1 ν.1 = (2 * c.k ^ 2 : ℂ)) := by
  -- The two dihedral-Sylow-2 structure inputs are PROVED in
  -- `BenderGlauberman/Section2/Basic.lean` (public, from the `H_eq_US`
  -- component of `Hyp11`):
  -- `H0_index` : `|H : H0| = 2` (`H0 = U·S0` of index 2 in `H = C_G(t)`,
  -- equivalently `H = O(H)·S`), needed for the paper's Remark 1.4 (the
  -- τ-extensions of `κ_j`) and for `t1H_disjoint`;
  -- `t1H_disjoint` : `t1^H ∩ t2^H = ∅` (the same index-2 structure keeps
  -- the two reflection classes of `S` apart in `H/U ≅ D_{2^m}`), needed for
  -- the TI-coincidence `f = Σ f_ij` on `T`: involutions `x, y` with
  -- `xy ∈ T` lie in `N_G(T) = H` (TI-set) and then outside `H0`, since `t`
  -- is the only non-identity square-one element of `H0`
  -- (`unique_involution_of_H0`, proved); the remaining claim that every
  -- involution of `H − H0` lies in `t1^H ∪ t2^H` is provable from `Hyp11`
  -- alone (recorded in the theorem card).
  -- The left side has been reduced to `V = |H|·(f, δ*)_G` with
  -- `f(g) = #{(x,y) : x,y ∈ t^G, x·y = g}` (see `lemma_2_2_V_eq` and the
  -- helpers above) and then to `V = W = |H|·(Σ f_ij, δ)_H` with
  -- `δ = (μ−ν)^H` (`lemma_2_2_V_eq_W`); the `τ`-case (`μ^s ≠ μ`, `ν^s ≠ ν`)
  -- is proved below (`lemma_2_2_W_tau_case`): by Clifford's theorem for the
  -- index-two extension `H/H0` both induceds `μ^H, ν^H` are irreducible and
  -- vanish on `t1, t2 ∉ H0`, so `W = c(μ^H) − c(ν^H) = 0`.
  -- The two `κ1`-cases (`V = 2k²`) are proved below via the value
  -- evaluations `(k1·θ(t1) + k2·θ(t2))²` = `k²` for `θ = τ1, τ1'` and
  -- `(k1 − k2)²` for `θ = τ2, τ2'` (paper pp. 205–207), from Remark 1.4's
  -- τ-extension character theory of `H/H0 ≅ C2` (`H0_index`): case 2
  -- (`ν = κ1·l`, `l² ≠ 1`: `ν^H` irreducible and vanishing at `t1, t2`,
  -- `κ1^H = τ1 + τ1'` contributes `2k²` — `lemma_2_2_W_kappaOne_l_case`);
  -- case 3 (`ν = κ2 = κ1·λ2`, `k1 = k2`: `κ2^s = κ2`, `κ2(t1·t2) = −1`, so
  -- `c(τ2) + c(τ2') = 2(k1−k2)² = 0` — `lemma_2_2_W_kappaOne_lambdaTwo_case`).
  constructor
  · intro hμs hνs
    rw [lemma_2_2_V_eq_W c h12 hEq]
    exact lemma_2_2_W_tau_case c h12 hμs hνs
  · constructor
    · intro hμ1 hl
      rcases hl with ⟨l, hlsq, hνl⟩
      rw [lemma_2_2_V_eq_W c h12 hEq]
      rw [hμ1, hνl]
      simpa using lemma_2_2_W_kappaOne_l_case c h12 hκ1lin hκ1S0 hκ1comm l hlsq
    · intro hμ1 hν2 hk12
      rw [lemma_2_2_V_eq_W c h12 hEq]
      rw [hμ1, hν2]
      simpa using lemma_2_2_W_kappaOne_lambdaTwo_case c h12 hκ1lin hκ1S0 hκ1comm hk12


end Section2V
end Section2

end CFSG.BenderGlauberman
