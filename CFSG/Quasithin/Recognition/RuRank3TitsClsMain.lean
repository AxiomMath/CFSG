module

public import CFSG.Quasithin.Recognition.RuRank3TitsCls

public section

namespace CFSG.Quasithin.RuRank3

open CFSG.Sporadic.Schreier.Tits CFSG.Sporadic.RuSchreier
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
open scoped MatrixGroups

attribute [local instance] fact_prime_five'

theorem badGen_zero (i : ℕ) : badGen i 0 = titsX13 := by simp [badGen]

theorem badGen_one (i : ℕ) : badGen i 1 = titsTInv := by simp [badGen]

theorem badGen_two (i : ℕ) : badGen i 2 = titsRep i := by simp [badGen]

theorem exists_conj_eq_titsK0
    {K : Subgroup (Equiv.Perm (Fin 1755))} (hKA : K ≤ titsA)
    (e : K ≃* PSL(2, GaloisField 5 2)) :
    ∃ g ∈ titsA, K.map (MulAut.conj g).toMonoidHom = titsK0 := by
  have h13 : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  obtain ⟨hcard, x, s, u, hx, hs, hsx, hu, hus, hunot, hgen, hpow⟩ := psl225_witnesses e
  set X := (x : Equiv.Perm (Fin 1755)) with hXdef
  set S := (s : Equiv.Perm (Fin 1755)) with hSdef
  set U := (u : Equiv.Perm (Fin 1755)) with hUdef
  have hXA : X ∈ titsA := hKA x.2
  have hSA : S ∈ titsA := hKA s.2
  have hUA : U ∈ titsA := hKA u.2
  have hKgen : K = Subgroup.closure {X, S, U} := by
    have := congrArg (Subgroup.map K.subtype) hgen
    rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at this
    rw [← this]
    congr 1
    simp [Set.image_insert_eq, Set.image_singleton, hXdef, hSdef, hUdef]
  obtain ⟨g₁, hg₁A, hX₁⟩ : ∃ g₁ ∈ titsA, g₁ * X * g₁⁻¹ ∈ Subgroup.zpowers titsX13 := by
    have hXo : orderOf (⟨X, hXA⟩ : titsA) = 13 := by
      rw [← Subgroup.orderOf_coe]
      show orderOf X = 13
      rw [hXdef, Subgroup.orderOf_coe]
      exact hx
    obtain ⟨Q1, hQ1⟩ := exists_sylow_eq_of_card (p := 13) (e := 1)
      (K := Subgroup.zpowers (⟨X, hXA⟩ : titsA)) (by rw [Nat.card_zpowers, hXo, pow_one])
      (by norm_num)
    obtain ⟨Q2, hQ2⟩ := exists_sylow_eq_of_card (p := 13) (e := 1)
      (K := Subgroup.zpowers titsX13A) (by
        rw [Nat.card_zpowers, pow_one, ← Subgroup.orderOf_coe]
        exact orderOf_titsX13) (by norm_num)
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq titsA Q1 Q2
    have hmem : g * ⟨X, hXA⟩ * g⁻¹ ∈ (Q2 : Subgroup titsA) := by
      rw [← hg, Sylow.coe_subgroup_smul]
      exact ⟨⟨X, hXA⟩, by rw [hQ1]; exact Subgroup.mem_zpowers _, rfl⟩
    rw [hQ2] at hmem
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hmem
    refine ⟨g, g.2, Subgroup.mem_zpowers_iff.2 ⟨j, ?_⟩⟩
    have := congrArg Subtype.val hj
    simpa [titsX13A] using this
  set X₁ := g₁ * X * g₁⁻¹ with hX₁def
  have hX₁1 : X₁ ≠ 1 := by
    intro h1
    have : X = 1 := by
      have := congrArg (fun w => g₁⁻¹ * w * g₁) h1
      simpa [hX₁def, mul_assoc] using this
    have hX1 : x = 1 := Subtype.ext this
    rw [hX1, orderOf_one] at hx
    norm_num at hx
  obtain ⟨k₁, hk₁⟩ := Subgroup.mem_zpowers_iff.1 (titsX13_mem_zpowers hX₁ hX₁1)
  have hS₁ : (g₁ * S * g₁⁻¹) * titsX13 * (g₁ * S * g₁⁻¹)⁻¹ = titsX13⁻¹ := by
    have hSX : S * X * S⁻¹ = X⁻¹ := by
      have := congrArg Subtype.val hsx
      simpa using this
    have h1 : (g₁ * S * g₁⁻¹) * X₁ * (g₁ * S * g₁⁻¹)⁻¹ = X₁⁻¹ := by
      rw [hX₁def]
      calc g₁ * S * g₁⁻¹ * (g₁ * X * g₁⁻¹) * (g₁ * S * g₁⁻¹)⁻¹ =
            g₁ * (S * X * S⁻¹) * g₁⁻¹ := by group
        _ = (g₁ * X * g₁⁻¹)⁻¹ := by rw [hSX]; group
    rw [← hk₁, conj_zpow_eq, h1, inv_zpow', zpow_neg]
  obtain ⟨l, hl⟩ := exists_zpow_conj_eq_titsT (mul_mem (mul_mem hg₁A hSA) (inv_mem hg₁A)) hS₁
  set g₂ := titsX13 ^ l * g₁ with hg₂def
  have hg₂A : g₂ ∈ titsA := mul_mem (zpow_mem titsX13_mem l) hg₁A
  have hS₂ : g₂ * S * g₂⁻¹ = titsTInv := by
    rw [← hl, hg₂def]
    group
  have hX₂ : g₂ * X * g₂⁻¹ = X₁ := by
    rw [hg₂def, hX₁def]
    have hc : Commute (titsX13 ^ l) X₁ := by
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hX₁
      rw [← hj]
      exact (Commute.refl titsX13).zpow_zpow l j
    calc titsX13 ^ l * g₁ * X * (titsX13 ^ l * g₁)⁻¹ =
          titsX13 ^ l * X₁ * (titsX13 ^ l)⁻¹ := by rw [hX₁def]; group
      _ = X₁ := by rw [hc.eq, mul_inv_cancel_right]
  set U₂ := g₂ * U * g₂⁻¹ with hU₂def
  have hU₂A : U₂ ∈ titsA := mul_mem (mul_mem hg₂A hUA) (inv_mem hg₂A)
  have hU2 : U * U = 1 := by
    have := congrArg Subtype.val (pow_orderOf_eq_one u)
    rw [hu] at this
    simpa [sq] using this
  have hUS : U * S = S * U := congrArg Subtype.val hus
  have hU₂2 : U₂ * U₂ = 1 := by
    rw [hU₂def]
    calc g₂ * U * g₂⁻¹ * (g₂ * U * g₂⁻¹) = g₂ * (U * U) * g₂⁻¹ := by group
      _ = 1 := by rw [hU2]; group
  have hU₂1 : U₂ ≠ 1 := by
    intro h1
    have : U = 1 := by
      have := congrArg (fun w => g₂⁻¹ * w * g₂) h1
      simpa [hU₂def, mul_assoc] using this
    have : u = 1 := Subtype.ext this
    rw [this, orderOf_one] at hu
    norm_num at hu
  have hU₂t : U₂ * titsTInv = titsTInv * U₂ := by
    rw [← hS₂, hU₂def]
    calc g₂ * U * g₂⁻¹ * (g₂ * S * g₂⁻¹) = g₂ * (U * S) * g₂⁻¹ := by group
      _ = g₂ * (S * U) * g₂⁻¹ := by rw [hUS]
      _ = g₂ * S * g₂⁻¹ * (g₂ * U * g₂⁻¹) := by group
  have hU₂ne : U₂ ≠ titsTInv := by
    intro h
    rw [← hS₂, hU₂def] at h
    have hUS' : U = S := by
      have := congrArg (fun w => g₂⁻¹ * w * g₂) h
      simpa [mul_assoc] using this
    apply hunot
    have : u = s := Subtype.ext hUS'
    rw [this]
    exact Subgroup.subset_closure (by simp)
  obtain ⟨k, hk, i, hi, hki⟩ := involution_centralizer_classified hU₂A hU₂t hU₂2 hU₂1 hU₂ne
  set g₃ := titsY12 ^ k * g₂ with hg₃def
  have hg₃A : g₃ ∈ titsA := mul_mem (pow_mem titsY12_mem k) hg₂A
  have hy12 : ∀ n : ℕ, titsY12 ^ n * titsX13 * (titsY12 ^ n)⁻¹ ∈ Subgroup.zpowers titsX13 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 : titsY12 * titsX13 * titsY12⁻¹ = titsX13 ^ 11 := by
        rw [titsY12_conj, mul_inv_cancel_right]
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 ih
      rw [pow_succ', mul_inv_rev]
      have e : titsY12 * titsY12 ^ n * titsX13 * ((titsY12 ^ n)⁻¹ * titsY12⁻¹) =
          titsY12 * (titsY12 ^ n * titsX13 * (titsY12 ^ n)⁻¹) * titsY12⁻¹ := by group
      rw [e, ← hj, conj_zpow_eq, h1]
      exact zpow_mem (pow_mem (Subgroup.mem_zpowers _) 11) j
  have hX₃ : g₃ * X * g₃⁻¹ ∈ Subgroup.zpowers titsX13 := by
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hX₁
    rw [hg₃def]
    have e : titsY12 ^ k * g₂ * X * (titsY12 ^ k * g₂)⁻¹ =
        (titsY12 ^ k * titsX13 * (titsY12 ^ k)⁻¹) ^ j := by
      have e' : titsY12 ^ k * g₂ * X * (titsY12 ^ k * g₂)⁻¹ =
          titsY12 ^ k * (g₂ * X * g₂⁻¹) * (titsY12 ^ k)⁻¹ := by group
      rw [e', hX₂, ← hj, conj_zpow_eq]
    rw [e]
    exact zpow_mem (hy12 k) j
  have hX₃1 : g₃ * X * g₃⁻¹ ≠ 1 := by
    intro h1
    have : X = 1 := by
      have := congrArg (fun w => g₃⁻¹ * w * g₃) h1
      simpa [mul_assoc] using this
    have hX1 : x = 1 := Subtype.ext this
    rw [hX1, orderOf_one] at hx
    norm_num at hx
  have hS₃ : g₃ * S * g₃⁻¹ = titsTInv := by
    rw [hg₃def]
    calc titsY12 ^ k * g₂ * S * (titsY12 ^ k * g₂)⁻¹ =
          titsY12 ^ k * (g₂ * S * g₂⁻¹) * (titsY12 ^ k)⁻¹ := by group
      _ = titsTInv := by
          rw [hS₂, ((show Commute titsY12 titsTInv from titsY12_comm).pow_left k).eq,
            mul_inv_cancel_right]
  have hU₃ : g₃ * U * g₃⁻¹ = titsRep i := by
    rw [← hki, hg₃def, hU₂def]
    group
  set K₃ := K.map (MulAut.conj g₃).toMonoidHom with hK₃def
  have hK₃ : K₃ = Subgroup.closure {g₃ * X * g₃⁻¹, titsTInv, titsRep i} := by
    rw [hK₃def, hKgen, MonoidHom.map_closure]
    congr 1
    simp only [Set.image_insert_eq, Set.image_singleton, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, hS₃, hU₃]
  have hx13K₃ : titsX13 ∈ K₃ := by
    rw [hK₃]
    exact Subgroup.zpowers_le.2 (Subgroup.subset_closure (by simp))
      (titsX13_mem_zpowers hX₃ hX₃1)
  have htK₃ : titsTInv ∈ K₃ := by rw [hK₃]; exact Subgroup.subset_closure (by simp)
  have hrK₃ : titsRep i ∈ K₃ := by rw [hK₃]; exact Subgroup.subset_closure (by simp)
  have hcardK₃ : Nat.card K₃ = 7800 := by
    rw [hK₃def, ← hcard]
    exact Nat.card_congr (Subgroup.equivMapOfInjective K _ (MulAut.conj g₃).injective).toEquiv.symm
  have hcase := allLt_spec clsReps.2.2.2 hi
  by_cases hgood : titsRepGood.getD i false = true
  ·
    simp only [hgood, ↓reduceIte] at hcase
    have hrK0 : titsRep i ∈ titsK0 := mem_titsK0_of_sift (rep_titsRep hi) hcase
    refine ⟨g₃, hg₃A, ?_⟩
    have hle : K₃ ≤ titsK0 := by
      rw [hK₃, Subgroup.closure_le]
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · exact Subgroup.zpowers_le.2 titsX13_mem_K0 hX₃
      · exact titsTInv_mem_K0
      · exact hrK0
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_titsK0, hcardK₃])
  ·
    rw [Bool.not_eq_true] at hgood
    simp only [hgood, Bool.false_eq_true, ↓reduceIte] at hcase
    rw [badOK, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.not_eq_true',
      Bool.not_eq_true', Bool.not_eq_true'] at hcase
    obtain ⟨hlet, h12, h13', h5⟩ := hcase
    set W := Quiver.SchreierGraph.evalWord (fun h : Fin 3 => badGen i h)
      (toLetters 3 (titsBadWords.getD i [])) with hWdef
    have hW : Rep 1755 (badWordArr i) W :=
      rep_wordA (rep_badLetters hi) (rep_badLetters_inv hi) _ hlet
    have hWK : W ∈ K₃ := by
      have hle : Subgroup.closure (Set.range fun h : Fin 3 => badGen i h) ≤ K₃ := by
        rw [Subgroup.closure_le]
        rintro _ ⟨h, rfl⟩
        fin_cases h
        · show badGen i 0 ∈ K₃
          rw [badGen_zero]
          exact hx13K₃
        · show badGen i 1 ∈ K₃
          rw [badGen_one]
          exact htK₃
        · show badGen i 2 ∈ K₃
          rw [badGen_two]
          exact hrK₃
      exact hle (Quiver.SchreierGraph.evalWord_mem_closure _ _)
    obtain ⟨k₀, hk₀K, hk₀⟩ := hWK
    have hpk := hpow ⟨k₀, hk₀K⟩
    have hpow' : ∀ n : ℕ, (⟨k₀, hk₀K⟩ : K) ^ n = 1 → W ^ n = 1 := by
      intro n hn
      rw [← hk₀, MulEquiv.coe_toMonoidHom, ← map_pow]
      have : k₀ ^ n = 1 := by
        have := congrArg Subtype.val hn
        simpa using this
      rw [this, map_one]
    exfalso
    rcases hpk with h | h | h
    · have := (eqA_iff (rep_powArr hW 12) rep_idA).2 (hpow' 12 h)
      rw [h12] at this
      exact Bool.false_ne_true this
    · have := (eqA_iff (rep_powArr hW 13) rep_idA).2 (hpow' 13 h)
      rw [h13'] at this
      exact Bool.false_ne_true this
    · have := (eqA_iff (rep_powArr hW 5) rep_idA).2 (hpow' 5 h)
      rw [h5] at this
      exact Bool.false_ne_true this

end CFSG.Quasithin.RuRank3
