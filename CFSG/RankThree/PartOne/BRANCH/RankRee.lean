module

public import CFSG.RankThree.PartOne.BRANCH.RankFinal
public import CFSG.RankThree.PartOne.BRANCH.RankSylow
public import CFSG.RankThree.PartOne.BRANCH.RankArith

public section

namespace CFSG.RankThree.PartOne.BRANCH

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.RF4 CFSG.RankThree.PartOne.KLR CFSG.RankThree.PartOne.KEXC
  CFSG.RankThree.PartOne.N143X CFSG.RankThree.LargeReeOrder

section Sector

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}
  {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L 2] [IsAlgClosed L]
  (D : ReeFrameData K L a)

theorem card_le_of_sector_three {w : WeylGroup ReeTag.F4.tag} {m : ℕ} (hmodd : Odd m)
    {U : Fin 2 → Fin ReeTag.F4.tag.rank → ℤ} (hP : ParamData a L D.F w m U)
    (hidx : ∀ i : ℕ, i * m ^ 2 = Nat.card (ReeTag.F4.reeGamma K a) → ¬ 9 ∣ i)
    {E : Subgroup (ReeTag.F4.reeGamma K a)} (hE : ∀ x ∈ E, x ^ 3 = 1) :
    Nat.card E ≤ 3 ^ (1 + 2) := by
  classical
  obtain ⟨Φ, hΦinj, hΦ, -, hΦF⟩ := hP.param
  set n := canonicalRep (coxeterSystem ReeTag.F4.tag) L w with hn
  have hnadj : n ∈ adjointGroup ReeTag.F4.tag L := canonicalRep_mem_adjointGroup _ L w
  obtain ⟨h, hh⟩ := D.lang ⟨n, hnadj⟩
  have hFh : D.F h = h * ⟨n, hnadj⟩ := by
    rw [hh]
    group
  set g₀ : ModGL ReeTag.F4.tag L := (h : ModGL ReeTag.F4.tag L) with hg₀
  have hg₀adj : g₀ ∈ adjointGroup ReeTag.F4.tag L := h.2
  have hFg₀ : Fext D.F g₀ = g₀ * n := by
    rw [Fext_of_mem D.F hg₀adj]
    have : (⟨g₀, hg₀adj⟩ : adjointGroup ReeTag.F4.tag L) = h := rfl
    rw [this, hFh]
    rfl
  have hΦrange : Φ.range ≤ twistedFixed D.F n := by
    rintro _ ⟨z, rfl⟩
    exact hΦF z
  obtain ⟨T, hTmem, -, hTcard⟩ := exists_twisted_embedding D hg₀adj hFg₀ Φ.range hΦrange
  have : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  have hTm : Nat.card T = m ^ 2 := by rw [hTcard, card_range_of_odd hmodd Φ hΦinj]
  have hindex : ¬ 3 ^ (1 + 1) ∣ T.index := by
    have h1 := T.index_mul_card
    rw [hTm] at h1
    simpa using hidx _ h1
  have hex : ∀ t : T, ∃ z, Φ z = g₀⁻¹ * thetaGamma L a (t : ReeTag.F4.reeGamma K a) * g₀ :=
    fun t => (hTmem t.1).1 t.2
  choose z hz using hex
  let φ : T → (Fin 2 → Lˣ) := fun t => ![((z t).1 : Lˣ), ((z t).2 : Lˣ)]
  have hφ : Function.Injective φ := by
    intro x y hxy
    have h1 : (z x).1 = (z y).1 := Subtype.ext (congrFun hxy 0)
    have h2 : (z x).2 = (z y).2 := Subtype.ext (congrFun hxy 1)
    have hzz : z x = z y := Prod.ext h1 h2
    have h3 : g₀⁻¹ * thetaGamma L a (x : ReeTag.F4.reeGamma K a) * g₀ =
        g₀⁻¹ * thetaGamma L a (y : ReeTag.F4.reeGamma K a) * g₀ := by
      rw [← hz x, ← hz y, hzz]
    have h4 := mul_left_cancel (mul_right_cancel h3)
    exact Subtype.ext (thetaGamma_injective L h4)
  have hφr : ∀ t : T, t ^ 3 = 1 → ∀ i, φ t i ^ 3 = 1 := by
    intro t ht i
    have h1 : (t : ReeTag.F4.reeGamma K a) ^ 3 = 1 := by
      have := congrArg Subtype.val ht
      simpa using this
    have h2 : Φ (z t ^ 3) = 1 := by
      rw [map_pow, hz t]
      have h3 : (g₀⁻¹ * thetaGamma L a (t : ReeTag.F4.reeGamma K a) * g₀) ^ 3 =
          g₀⁻¹ * thetaGamma L a ((t : ReeTag.F4.reeGamma K a) ^ 3) * g₀ := by
        have := conj_pow (a := g₀⁻¹) (b := thetaGamma L a (t : ReeTag.F4.reeGamma K a)) (i := 3)
        simpa [map_pow] using this
      rw [h3, h1, map_one]
      group
    have h3 : z t ^ 3 = 1 := hΦinj (h2.trans (map_one Φ).symm)
    fin_cases i
    · exact congrArg (fun y => (y.1 : Lˣ)) h3
    · exact congrArg (fun y => (y.2 : Lˣ)) h3
  exact card_le_of_torus' Nat.prime_three φ hφ hφr hindex hE

end Sector

theorem reeThreeRank :
    ReeThreeRank := by
  intro X _ _ f hX E hE hcard
  classical
  obtain ⟨a, K, _, _, _, ha, hfa, hK, ⟨e⟩⟩ := exists_gamma_of_model hX
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  have : Finite (ReeTag.F4.reeGamma K a) := Finite.of_equiv X e.toEquiv
  have hE3 : ∀ x ∈ E.map e.toMonoidHom, x ^ 3 = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_pow, elemPow_eq_one_of_isElementaryAbelian (p := 3) y hy, map_one]
  have hcard' : Nat.card (E.map e.toMonoidHom) = 3 ^ 7 := by
    rw [Subgroup.card_map_of_injective e.injective, hcard]
  obtain ⟨D⟩ := reeFrameData_nonempty (K := K) (L := AlgebraicClosure K) hK'
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have horder := (large_Ree_exact_native_order_and_prime_factor_exhaustion a K hK').1
  have hmod3 : (2 ^ (2 * a + 1)) % 3 = 2 := by
    rcases two_pow_mod_three (2 * a + 1) with ⟨-, h⟩ | ⟨h, -⟩
    · exact absurd h (by simp)
    · exact h
  have hQ2 : 2 ≤ 2 ^ (2 * a + 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hb := card_le_of_sector_three D (odd_mPhi2' a) (torusParam_phi2 D.isFrob)
    (fun i hi => not_nine_dvd_ree_twisted hQ2 hmod3 (by
      rw [mPhi2] at hi
      rw [horder] at hi
      rw [mul_comm] at hi
      exact hi)) hE3
  rw [hcard'] at hb
  norm_num at hb

end CFSG.RankThree.PartOne.BRANCH
