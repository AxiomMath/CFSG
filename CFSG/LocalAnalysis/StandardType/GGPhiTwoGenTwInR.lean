module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5Index

public section

namespace CFSG.StandardType.PhiTwoRootGen

open CFSG.Open CFSG.LieType.Chevalley
open CFSG.Blueprint.Chevalley (Tag TwistTag ModGL adjointGroup)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem twInR_rootDiagUnit_mem_graphFixed
    {K : Type} [Field K] {σ : K →+* K}
    {t : Fin 6 → Kˣ} (ht : t ∈ TableB.TwE6.torus₀ σ) :
    rootDiagUnit TwistTag.E6.tag t ∈ graphFixedRootGroup TwistTag.E6 K σ := by
  obtain ⟨s, hs, rfl⟩ := ht
  exact TableB.TwE6.rootDiagUnit_cartanChar_mem (t := TwistTag.E6) hs

theorem twInndiag_pow_three_mem
    {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    {d : ModGL TwistTag.E6.tag K} (hd : d ∈ RecipeExcLang.twInndiagGroup K σ) :
    d ^ 3 ∈ graphFixedRootGroup TwistTag.E6 K σ.toRingHom := by
  classical
  have hq : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hK2 : Nat.card K = 2 ^ (n * 2) := by rw [hK, ← pow_mul]
  have : CharP K 2 := charP_two_of_card hK2
  set L := AlgebraicClosure K
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  obtain ⟨b, hb, c, hc, hdec⟩ := RecipeExcLang.exists_decomp_of_mem_twInndiag hn hK
    (σ := σ) hσ (L := L) (Fr := iterateFrobenius L 2 n)
    (fun c => by rw [iterateFrobenius_def]) hd
  let b6 : Fin 6 → Kˣ := b
  have hσσ : ∀ x : K, σ.toRingHom (σ.toRingHom x) = x :=
    TableB.TwE6.sigma_sigma (σ := σ.toRingHom) hK hσ
  have hb3T : b6 ^ 3 ∈ TableB.TwE6.torus₀ σ.toRingHom := by
    have hb' : b6 ∈ TableB.TwE6.compat σ.toRingHom :=
      (TableB.TwE6.mem_compat σ.toRingHom).2 hb
    obtain ⟨x, hx⟩ := TableB.TwE6.exists_mul_edge_inv_mem (σ := σ.toRingHom) hq hK hσ hb'
    have hbx : b6 = (b6 * (TableB.TwE6.edge σ.toRingHom x)⁻¹) *
        TableB.TwE6.edge σ.toRingHom x := by
      group
    rw [hbx, mul_pow, ← map_pow (TableB.TwE6.edge σ.toRingHom) x 3]
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ hx 3)
      (TableB.TwE6.edge_pow_three_mem (σ := σ.toRingHom) hσσ x)
  have hb3C : rootDiagUnit TwistTag.E6.tag b6 ^ 3 ∈
      graphFixedRootGroup TwistTag.E6 K σ.toRingHom := by
    rw [rootDiagUnit_pow (τ := TwistTag.E6.tag) b6 3]
    exact twInR_rootDiagUnit_mem_graphFixed hb3T
  set a : ModGL TwistTag.E6.tag K := rootDiagUnit TwistTag.E6.tag b6 with ha
  have haΓ : a ∈ RecipeExcLang.twInndiagGroup K σ :=
    RecipeExcLang.rootDiagUnit_mem_twInndiag hb
  have h1 : a * c * a⁻¹ ∈ graphFixedRootGroup TwistTag.E6 K σ.toRingHom :=
    RecipeExcLang.conj_mem_C0_of_mem_twInndiag hn hK (σ := σ) hσ (L := L)
      (Fr := iterateFrobenius L 2 n) (fun c => by rw [iterateFrobenius_def]) haΓ hc
  have h2 : a * (a * c * a⁻¹) * a⁻¹ ∈ graphFixedRootGroup TwistTag.E6 K σ.toRingHom :=
    RecipeExcLang.conj_mem_C0_of_mem_twInndiag hn hK (σ := σ) hσ (L := L)
      (Fr := iterateFrobenius L 2 n) (fun c => by rw [iterateFrobenius_def]) haΓ h1
  have h3 : a ^ 3 ∈ graphFixedRootGroup TwistTag.E6 K σ.toRingHom := by
    rw [ha]
    exact hb3C
  have hcube : (a * c) ^ 3 =
      (a * c * a⁻¹) * (a * (a * c * a⁻¹) * a⁻¹) * a ^ 3 * c := by
    rw [pow_succ, pow_succ, pow_one]
    group
  have hdac : d = a * c := hdec
  rw [hdac, hcube]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ h1 h2) h3) hc

end CFSG.StandardType.PhiTwoRootGen

end
