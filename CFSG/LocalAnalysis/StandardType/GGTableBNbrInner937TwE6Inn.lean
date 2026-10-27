module

public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaOutdiag
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTwE6Torus

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace TableB.TwE6

theorem compat_le_torus₀ {K : Type} [Field K] [Finite K] {σ : K →+* K} {q : ℕ} (hq : 2 ≤ q)
    (hK : Nat.card K = q ^ 2) (hσ : ∀ c, σ c = c ^ q) (h3 : ¬ 3 ∣ q + 1) :
    compat σ ≤ torus₀ σ := by
  have hσσ := sigma_sigma hK hσ
  have key : ∀ x : Kˣ, edge σ x ∈ torus₀ σ := by
    intro x
    have hcop1 : Nat.Coprime (q - 1) (4 * q - 5) := by
      rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_eq_one_iff]
      intro c hc1 hc2
      have h4 : c ∣ 4 * (q - 1) := by
        simpa [mul_comm] using dvd_mul_of_dvd_right hc1 4
      have hsub : 4 * (q - 1) - (4 * q - 5) = 1 := by omega
      have h := Nat.dvd_sub h4 hc2
      rw [hsub] at h
      exact Nat.dvd_one.mp h
    have hcop2 : Nat.Coprime (q + 1) (4 * q - 5) := by
      rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_eq_one_iff]
      intro c hc1 hc2
      have h4 : c ∣ 4 * (q + 1) := by
        simpa [mul_comm] using dvd_mul_of_dvd_right hc1 4
      have hsub : 4 * (q + 1) - (4 * q - 5) = 9 := by omega
      have hc9 : c ∣ 9 := by
        have h := Nat.dvd_sub h4 hc2
        rwa [hsub] at h
      have hc9' : c = 1 ∨ c = 3 ∨ c = 9 := by
        have hcle : c ≤ 9 := Nat.le_of_dvd (by norm_num) hc9
        interval_cases c <;> simp_all
      rcases hc9' with rfl | rfl | rfl
      · rfl
      · exact absurd hc1 h3
      · exact absurd (dvd_trans (by norm_num : 3 ∣ 9) hc1) h3
    have hcard : Nat.card Kˣ = (q - 1) * (q + 1) := by
      rw [Nat.card_units, hK]
      have hs := Nat.sq_sub_sq q 1
      rw [one_pow] at hs
      rw [hs, mul_comm]
    have hcop : Nat.Coprime (Nat.card Kˣ) (4 * q - 5) := by
      rw [hcard]
      exact Nat.Coprime.mul_left hcop1 hcop2
    obtain ⟨u, hu⟩ := (Nat.Coprime.pow_left_bijective hcop).2 x
    let t : Kˣ := u⁻¹
    let w : Kˣ := t ^ 3
    let a : Kˣ := t ^ (q + 1)
    have hmap : ∀ y : Kˣ, Units.map σ.toMonoidHom y = y ^ q := by
      intro y
      apply Units.ext
      rw [Units.val_pow_eq_pow_val]
      exact hσ (y : K)
    have hy : ∀ y : Kˣ, y ^ (q ^ 2) = y := by
      intro y
      have h1 := units_map_map hσσ y
      rw [hmap, hmap] at h1
      rw [pow_two, pow_mul]
      exact h1
    have ha : Units.map σ.toMonoidHom a = a := by
      dsimp only [a]
      rw [hmap]
      rw [← pow_mul, show (q + 1) * q = q ^ 2 + q by ring, pow_add, hy t, pow_succ']
    have h3' : a ^ 3 = w * Units.map σ.toMonoidHom w := by
      dsimp only [a, w]
      rw [hmap, ← pow_mul, ← pow_mul, ← pow_add]
      congr 1
      ring
    have ht : t ^ (4 * q - 5) = x⁻¹ := by
      dsimp only [t]
      have hu' : u ^ (4 * q - 5) = x := by simpa using hu
      rw [inv_pow, hu']
    have hx' : x * a ^ 4 = w ^ 3 := by
      dsimp only [a, w]
      rw [← pow_mul, ← pow_mul]
      have h1 : x * t ^ (4 * q - 5) = 1 := by rw [ht, mul_inv_cancel]
      have hexp : (q + 1) * 4 = (4 * q - 5) + 9 := by omega
      rw [hexp, pow_add, ← mul_assoc, h1, one_mul]
    have hxU : x = w ^ 3 * (a ^ 4)⁻¹ := (eq_mul_inv_iff_mul_eq).2 hx'
    refine ⟨![w ^ 2 * (a ^ 2)⁻¹, a, w, a ^ 2, Units.map σ.toMonoidHom w,
      Units.map σ.toMonoidHom (w ^ 2 * (a ^ 2)⁻¹)], fun i => ?_, ?_⟩
    · fin_cases i
      · simp [rhoE6_values]
      · simpa [rhoE6_values] using ha.symm
      · simp [rhoE6_values]
      · simpa [rhoE6_values, map_pow] using congrArg (fun z => z ^ 2) ha.symm
      · simpa [rhoE6_values] using (units_map_map hσσ w).symm
      · apply Units.ext
        simp [rhoE6_values]
        rw [hσσ (w : K), hσσ (a : K)]
    · rw [cartanHom_eq, edge_apply]
      funext l
      fin_cases l
      · apply Units.ext
        simp
        have hxK : (x : K) * (a : K) ^ 4 = (w : K) ^ 3 := congrArg Units.val hx'
        field_simp
        linear_combination -hxK
      · apply Units.ext
        simp
      · apply Units.ext
        simp
      · apply Units.ext
        simp only [Units.coe_map]
        simp
        have h3K : (a : K) ^ 3 = (w : K) * σ (w : K) := by
          simpa [Units.coe_map] using congrArg Units.val h3'
        field_simp
        linear_combination h3K
      · apply Units.ext
        simp only [Units.coe_map]
        simp
        have haK : σ (a : K) = (a : K) := by
          simpa [Units.coe_map] using congrArg Units.val ha
        field_simp
        rw [haK]
      · rw [hxU]
        apply Units.ext
        simp
        field_simp
  intro b hb
  obtain ⟨x, hx⟩ := exists_mul_edge_inv_mem hq hK hσ hb
  have h := (torus₀ σ).mul_mem hx (key x)
  simpa [mul_assoc] using h

section Diag


section RootSetMem

variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (ρ : Equiv.Perm (Fin r)) (n : ℕ) (K : Type)
  [Field K]

private def DiagMemOn (S : (Fin r → ℤ) → Prop) : Prop :=
  ∀ a : Fin r → Kˣ,
    (∀ h ∈ MarkChev.twistedH A S K ρ n, ∃ h' ∈ MarkChev.twistedH A S K ρ n,
      (h' : Module.End K (MarkChev.Space S K)) * markDiag S K a = markDiag S K a * h) →
    ∃ g ∈ MarkChev.twistedH A S K ρ n,
      (g : Module.End K (MarkChev.Space S K)) = markDiag S K a

variable {A ρ n K}

private theorem DiagMemOn.of_eq {S S' : (Fin r → ℤ) → Prop} (hS : S = S')
    (h : DiagMemOn A ρ n K S) : DiagMemOn A ρ n K S' :=
  hS ▸ h

end RootSetMem

private theorem diagMemOn_isRoot {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (h3 : ¬ 3 ∣ 2 ^ n + 1) :
    DiagMemOn TwistTag.E6.tag.cartan TwistTag.E6.perm n K (IsRoot TwistTag.E6.tag) := by
  have : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  set σ := iterateFrobenius K 2 n
  have hσ : ∀ c, σ c = c ^ 2 ^ n := iterateFrobenius_def 2 n
  have hq : 2 ≤ 2 ^ n :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hC : MarkChev.twistedH TwistTag.E6.tag.cartan (IsRoot TwistTag.E6.tag) K TwistTag.E6.perm
      n = graphFixedRootGroup TwistTag.E6 K σ := by
    rw [twistedH_eq_commutator K .E6 n σ hσ]
    exact (finite_fixed_root_group_perfect TwistTag.E6 Nat.prime_two hn K hK σ hσ).2.2.1
  intro a ha
  rw [hC] at ha ⊢
  have hconj : ∀ g ∈ graphFixedRootGroup TwistTag.E6 K σ, rootDiagUnit TwistTag.E6.tag a * g *
      (rootDiagUnit TwistTag.E6.tag a)⁻¹ ∈ graphFixedRootGroup TwistTag.E6 K σ := by
    intro g hg
    obtain ⟨h', hh', e⟩ := ha g hg
    rw [markDiag_isRoot] at e
    rw [← eq_conj_of_mul_rootDiag e]
    exact hh'
  have hT : ∀ c ∈ torus₀ σ,
      rootDiagUnit TwistTag.E6.tag c ∈ graphFixedRootGroup TwistTag.E6 K σ := by
    rintro _ ⟨s, hs, rfl⟩
    exact rootDiagUnit_cartanChar_mem (t := TwistTag.E6) hs
  exact ⟨_, hT _ (compat_le_torus₀ hq hK hσ h3 fun i => compat_of_forall_conj_mem hconj i),
    (markDiag_isRoot _).symm⟩

theorem diagHom_mem_twE6 {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (h3 : ¬ 3 ∣ 2 ^ n + 1) {a : Fin 6 → Kˣ}
    (ha : ∀ x ∈ LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n,
      diagHom (LargeEvenCartanE 6) K a * x * (diagHom (LargeEvenCartanE 6) K a)⁻¹ ∈
        LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n) :
    diagHom (LargeEvenCartanE 6) K a ∈
      LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n := by
  have hroot : LargeEvenIsRoot (LargeEvenCartanE 6) = IsRoot TwistTag.E6.tag :=
    largeEvenIsRoot_eq_isRoot TwistTag.E6.tag
  rw [largeEvenTwistedH_eq] at ha ⊢
  have hmem : DiagMemOn (LargeEvenCartanE 6) LargeEvenRhoE6 n K
      (LargeEvenIsRoot (LargeEvenCartanE 6)) :=
    (diagMemOn_isRoot hn hK h3).of_eq hroot.symm
  have ha2 : ∀ h ∈ MarkChev.twistedH (LargeEvenCartanE 6) (LargeEvenIsRoot (LargeEvenCartanE 6)) K
        LargeEvenRhoE6 n,
      ∃ h' ∈ MarkChev.twistedH (LargeEvenCartanE 6) (LargeEvenIsRoot (LargeEvenCartanE 6)) K
        LargeEvenRhoE6 n,
        (h' : Module.End K (MarkChev.Space (LargeEvenIsRoot (LargeEvenCartanE 6)) K)) *
            markDiag (LargeEvenIsRoot (LargeEvenCartanE 6)) K a =
          markDiag (LargeEvenIsRoot (LargeEvenCartanE 6)) K a * h := by
    intro h hh
    refine ⟨_, ha h hh, ?_⟩
    rw [← largeEvenDiagMap_eq_markDiag]
    exact (diag_rel_iff a h _).2 rfl
  obtain ⟨g, hg, hgd⟩ := hmem a ha2
  have hge : g = diagHom (LargeEvenCartanE 6) K a := Units.ext (by
    rw [hgd, coe_diagHom, largeEvenDiagMap_eq_markDiag])
  rw [← hge]
  exact hg

end Diag

end TableB.TwE6

namespace TwE6Delta


variable {n : ℕ} {K : Type} [Field K] [Finite K]

theorem recipeI_subset_inn_of_not_dvd (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (h3 : ¬ 3 ∣ 2 ^ n + 1) :
    RecipeI K n ⊆ Set.range (MulAut.conj : RecipeR K n →* MulAut (RecipeR K n)) := by
  intro φ hφ
  have hle : Subgroup.closure (LargeEvenInnSet (RecipeR K n) ∪
      LargeEvenChevDiagImage (LargeEvenCartanE 6) K (RecipeH K n)) ≤
      (MulAut.conj : RecipeR K n →* MulAut (RecipeR K n)).range := by
    rw [Subgroup.closure_le]
    rintro ψ (⟨x, rfl⟩ | hψ)
    · exact ⟨x, rfl⟩
    · obtain ⟨a, ha⟩ := TableB.exists_isDiagOf hψ
      rw [TableB.isDiagOf_eq_conj ha
        (TableB.TwE6.diagHom_mem_twE6 hn hK h3 ha.1)]
      exact ⟨_, rfl⟩
  exact hle hφ

end TwE6Delta

end CFSG.StandardType

end
