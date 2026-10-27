module

public import CFSG.RankThree.PartOne.KE8F.HIDetect
public import CFSG.RankThree.PartOne.KE.E8RootCharacterTorus
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.PartOne.KE8F.HV

public noncomputable section

namespace CFSG.RankThree.PartOne.KE8F

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix Pointwise MatrixGroups Polynomial
open Polynomial (X C)

set_option linter.unusedSectionVars false


section Charpoly

variable {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L] {ℓ f p : ℕ}
  [Fact ℓ.Prime] [CharP L ℓ]

theorem charpoly_eq_map_of_conj (σ : K →+* K) (Y m : ModGL .E8 K)
    (h : Y = m * Units.map (entrywiseHom σ) Y * m⁻¹) :
    ((Y : ModGL .E8 K) : Module.End K (RootModule .E8 K)).charpoly.map σ =
      ((Y : ModGL .E8 K) : Module.End K (RootModule .E8 K)).charpoly := by
  have h1 : ((Y : ModGL .E8 K) : Module.End K (RootModule .E8 K)) =
      (m : Module.End K (RootModule .E8 K)) *
        entrywise σ (Y : Module.End K (RootModule .E8 K)) *
          ((m⁻¹ : ModGL .E8 K) : Module.End K (RootModule .E8 K)) := by
    have := congrArg Units.val h
    rw [Units.val_mul, Units.val_mul] at this
    exact this
  conv_rhs => rw [h1]
  rw [charpoly_conj_unit m (entrywise σ (Y : Module.End K (RootModule .E8 K)))]
  exact (charpoly_baseChangeEnd σ (Y : Module.End K (RootModule .E8 K))).symm

theorem charpoly_psiC (F : E8P4Frame0 K L ℓ f) (c y : adjointGroup .E8 K) :
    ((psiC F c y : ModGL .E8 L) : Module.End L (RootModule .E8 L)).charpoly =
      (((y : ModGL .E8 K) : Module.End K (RootModule .E8 K)).charpoly).map (algebraMap K L) := by
  rw [psiC_apply]
  have e1 : ((F.g0⁻¹ * adjEmb .E8 K L (c * y * c⁻¹) * F.g0 : ModGL .E8 L) :
      Module.End L (RootModule .E8 L)) =
      ((F.g0⁻¹ : ModGL .E8 L) : Module.End L (RootModule .E8 L)) *
        ((adjEmb .E8 K L (c * y * c⁻¹) : ModGL .E8 L) : Module.End L (RootModule .E8 L)) *
          (((F.g0⁻¹)⁻¹ : ModGL .E8 L) : Module.End L (RootModule .E8 L)) := by
    rw [inv_inv, Units.val_mul, Units.val_mul]
  rw [e1, charpoly_conj_unit, adjEmb_apply, coe_baseChangeGL, charpoly_baseChangeEnd]
  congr 1
  have e2 : (((c * y * c⁻¹ : adjointGroup .E8 K) : ModGL .E8 K) :
      Module.End K (RootModule .E8 K)) =
      ((c : ModGL .E8 K) : Module.End K (RootModule .E8 K)) *
        ((y : ModGL .E8 K) : Module.End K (RootModule .E8 K)) *
          ((((c : ModGL .E8 K))⁻¹ : ModGL .E8 K) : Module.End K (RootModule .E8 K)) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul]
  rw [e2, charpoly_conj_unit]

end Charpoly

section Torsion

variable {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L] [IsAlgClosed L] {ℓ f p : ℕ}
  [Fact ℓ.Prime] [CharP L ℓ]

theorem exists_torsionC_of_mem (F : E8P4Frame0 K L ℓ f) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    (hp : p.Prime) (hpf : p ∣ Nat.card K * Nat.card K + 1) (c : adjointGroup .E8 K)
    (hcard : Nat.card (torsionC p F c) = p ^ 4) {b : Fin Tag.E8.rank → Lˣ}
    (hb : b ∈ T0tors (iterateFrobenius L ℓ f) p) :
    ∃ y ∈ torsionC p F c, psiC F c y = rootDiagUnit .E8 b := by
  have hFr : ∀ x, iterateFrobenius L ℓ f x = x ^ Nat.card K := fun x => by
    rw [hK]
    exact iterateFrobenius_def ℓ f x
  have hpℓ : ¬ ℓ ∣ p := not_dvd_char hf hK hp hpf
  set S : Subgroup (ModGL .E8 L) :=
    (T0tors (iterateFrobenius L ℓ f) p).map (rootDiagUnitHom .E8 L) with hS
  have hScard : Nat.card S = p ^ 4 := by
    rw [hS, Subgroup.card_map_of_injective (rootDiagUnit_injective (τ := .E8) (K := L)),
      card_T0tors hFr hp hpf hpℓ]
  have hle : (torsionC p F c).map (psiC F c) ≤ S := Subgroup.map_comap_le _ _
  have hSfin : Finite S := Nat.finite_of_card_ne_zero (by rw [hScard]; exact pow_ne_zero 4 hp.ne_zero)
  have heq : (torsionC p F c).map (psiC F c) = S := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective (psiC_injective F c), hcard, hScard]
  have hbS : rootDiagUnit .E8 b ∈ S := ⟨b, hb, rfl⟩
  rw [← heq] at hbS
  obtain ⟨y, hy, hyb⟩ := hbS
  exact ⟨y, hy, hyb⟩

end Torsion

section Arith

theorem sixteen_lt {p q₀ : ℕ} (hp : p.Prime) (hp10 : 10 < p)
    (h : p ∣ (q₀ * q₀) * (q₀ * q₀) + 1) : 16 < p := by
  have : Fact p.Prime := ⟨hp⟩
  have hq4 : (q₀ : ZMod p) ^ 4 + 1 = 0 := by
    have := (ZMod.natCast_eq_zero_iff _ p).2 h
    push_cast at this
    linear_combination this
  have h8 : (q₀ : ZMod p) ^ 8 = 1 := by linear_combination ((q₀ : ZMod p) ^ 4 - 1) * hq4
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    have := Nat.le_of_dvd (by norm_num) ((ZMod.natCast_eq_zero_iff 2 p).1 h')
    omega
  have h4 : ¬ (q₀ : ZMod p) ^ 4 = 1 := by
    intro h
    apply h2
    linear_combination hq4 - h
  have hord : orderOf (q₀ : ZMod p) = 8 := by
    have := orderOf_eq_prime_pow (p := 2) (n := 2) (x := (q₀ : ZMod p))
      (by simpa using h4) (by simpa using h8)
    simpa using this
  have hne : (q₀ : ZMod p) ≠ 0 := by
    intro h0
    rw [h0] at hq4
    simp at hq4
  have hdvd := ZMod.orderOf_dvd_card_sub_one hne
  rw [hord] at hdvd
  omega

end Arith

section Main

variable {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L] [IsAlgClosed L] {ℓ f p : ℕ}
  [Fact ℓ.Prime] [CharP L ℓ]

theorem outer_involution_absurd (F : E8P4Frame0 K L ℓ f) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hp10 : 10 < p)
    (hpf : p ∣ Nat.card K * Nat.card K + 1) (c : adjointGroup .E8 K)
    (hcard : Nat.card (torsionC p F c) = p ^ 4) {η : MulAut (adjointGroup .E8 K)} (hη : η ^ 2 = 1)
    (hout : η ∉ (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K)).range)
    (hfix : ∀ y ∈ torsionC p F c, η y = y) : False := by
  classical
  obtain ⟨-, -, hNF⟩ := ordinary_E_exact_automorphism_normal_form .E8 (Or.inr (Or.inr rfl)) K
  obtain ⟨Θ, -, -, -, hsq, hquad⟩ :=
    ordinary_E_field_graph_quotient_and_involutions .E8 (Or.inr (Or.inr rfl)) K
  obtain ⟨g, a, σ, ε, hgaσ⟩ := hNF η
  have hQ : exactQ .E8 K ε = 1 := rfl
  have hη' : ∀ h : adjointGroup .E8 K, (η h : ModGL .E8 K) =
      (g : ModGL .E8 K) * rootDiagUnit .E8 a *
        Units.map (entrywiseHom σ.toRingHom) (h : ModGL .E8 K) * (rootDiagUnit .E8 a)⁻¹ *
          (g : ModGL .E8 K)⁻¹ := fun h => by
    rw [hgaσ h, hQ, mul_one, inv_one, mul_one]
  have hσ2 : σ ^ 2 = 1 := hsq η g a σ ε hgaσ hη
  by_cases hσ1 : σ = 1
  ·
    subst hσ1
    apply hout
    have h1 : ∀ x : ModGL .E8 K, Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) x = x :=
      fun x => Units.ext (entrywise_id _)
    refine ⟨⟨(g : ModGL .E8 K) * rootDiagUnit .E8 a,
      mul_mem g.2 (rootDiagUnit_E8_mem_adjointGroup a)⟩, ?_⟩
    refine MulEquiv.ext fun h => Subtype.ext ?_
    rw [hη' h, h1]
    simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv, _root_.mul_inv_rev, mul_assoc]
  · obtain ⟨hev, hσc, -⟩ := hquad ℓ f (Fact.out : ℓ.Prime) hf hK σ hσ2 hσ1
    set q₀ : ℕ := ℓ ^ (f / 2) with hq₀
    have hq : Nat.card K = q₀ * q₀ := by
      rw [hK, hq₀, ← pow_add]
      congr 1
      obtain ⟨m, hm⟩ := hev
      omega
    have hpq4 : p ∣ (q₀ * q₀) * (q₀ * q₀) + 1 := by
      rw [← hq]
      exact hpf
    have hp16 : 16 < p := sixteen_lt hp hp10 hpq4
    have hpℓ : ¬ ℓ ∣ p := not_dvd_char hf hK hp hpf
    obtain ⟨ζ, hζ⟩ := exists_unit_orderOf (L := L) hp hpℓ
    have hζp : ζ ^ p = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
    have hFr : ∀ x, iterateFrobenius L ℓ f x = x ^ Nat.card K := fun x => by
      rw [hK]
      exact iterateFrobenius_def ℓ f x
    set b : Fin Tag.E8.rank → Lˣ := pairGauss (Nat.card K) 0 1 ζ 1 with hb
    have hbT : b ∈ T0tors (iterateFrobenius L ℓ f) p :=
      pairGauss_mem hFr hpf (by decide) hζp (one_pow p)
    obtain ⟨y, hy, hyb⟩ := exists_torsionC_of_mem F hf hK hp hpf c hcard hbT
    have hηy := hfix y hy
    have hconj : (y : ModGL .E8 K) =
        ((g : ModGL .E8 K) * rootDiagUnit .E8 a) *
          Units.map (entrywiseHom σ.toRingHom) (y : ModGL .E8 K) *
            ((g : ModGL .E8 K) * rootDiagUnit .E8 a)⁻¹ := by
      have := hη' y
      rw [hηy] at this
      rw [_root_.mul_inv_rev]
      simp only [mul_assoc] at this ⊢
      exact this
    have hQσ := charpoly_eq_map_of_conj σ.toRingHom (y : ModGL .E8 K) _ hconj
    have hpoly : (((y : ModGL .E8 K) : Module.End K (RootModule .E8 K)).charpoly).map
        (algebraMap K L) = ∏ l : Label .E8, (X - C (evLabel b l)) := by
      rw [← charpoly_psiC F c y, hyb]
      exact charpoly_rootDiag b
    set σ' : L →+* L := iterateFrobenius L ℓ (f / 2) with hσ'
    have hσ'x : ∀ x, σ' x = x ^ q₀ := fun x => iterateFrobenius_def ℓ (f / 2) x
    have hcomp : σ'.comp (algebraMap K L) = (algebraMap K L).comp σ.toRingHom := by
      refine RingHom.ext fun x => ?_
      change σ' (algebraMap K L x) = algebraMap K L (σ x)
      rw [hσ'x, ← map_pow, hσc x]
    have hstab : (∏ l : Label .E8, (X - C (evLabel b l))).map σ' =
        ∏ l : Label .E8, (X - C (evLabel b l)) := by
      rw [← hpoly, Polynomial.map_map, hcomp, ← Polynomial.map_map, hQσ]
    have hmap : (∏ l : Label .E8, (X - C (evLabel b l))).map σ' =
        ∏ l : Label .E8, (X - C (σ' (evLabel b l))) := by
      rw [Polynomial.map_prod]
      simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    have hroots := congrArg Polynomial.roots hstab
    rw [hmap, roots_prod_X_sub_C_univ, roots_prod_X_sub_C_univ] at hroots
    refine not_stable hFr hq hp hp16 hpf hζ ?_
    simpa only [hσ'x] using hroots

end Main

end CFSG.RankThree.PartOne.KE8F
