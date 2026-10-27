module

public import CFSG.RankThree.Chevalley.SteinbergBTEvenTwistedE6SixTorus
public import CFSG.LieType.Chevalley.RootDiagonalWeylTransporter

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

@[expose] def qplusPower : Tag → ℕ
  | .E7 => 9
  | _ => 15

@[expose] def qplusWord (τ : Tag) : List (Fin τ.rank) :=
  (List.replicate (qplusPower τ) (List.finRange τ.rank)).flatten

theorem qplus_foldr_E7 : ∀ k : Fin Tag.E7.rank,
    (qplusWord .E7).foldr (reflect .E7) (Pi.single k 1) = -Pi.single k 1 := by
  decide +kernel

theorem qplus_foldr_E8 : ∀ k : Fin Tag.E8.rank,
    (qplusWord .E8).foldr (reflect .E8) (Pi.single k 1) = -Pi.single k 1 := by
  decide +kernel

@[expose] def qplusW (τ : Tag) : WeylGroup τ :=
  (coxeterSystem τ).wordProd (qplusWord τ)

theorem qplusW_smul_single {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) (k : Fin τ.rank) :
    qplusW τ • (Pi.single k 1 : Fin τ.rank → ℤ) = -Pi.single k 1 := by
  rw [qplusW, wordProd_smul]
  rcases hτ with rfl | rfl
  · exact qplus_foldr_E7 k
  · exact qplus_foldr_E8 k

theorem qplusW_smul {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) (v : Fin τ.rank → ℤ) :
    qplusW τ • v = -v := by
  have hv : v = ∑ i, v i • (Pi.single i 1 : Fin τ.rank → ℤ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have h : ∀ i, qplusW τ • (v i • (Pi.single i 1 : Fin τ.rank → ℤ)) =
      -(v i • (Pi.single i 1 : Fin τ.rank → ℤ)) := fun i => by
    rw [smul_comm (qplusW τ) (v i), qplusW_smul_single hτ, smul_neg]
  calc qplusW τ • v = qplusW τ • ∑ i, v i • (Pi.single i 1 : Fin τ.rank → ℤ) := by rw [← hv]
    _ = -∑ i, v i • (Pi.single i 1 : Fin τ.rank → ℤ) := by
        rw [Finset.smul_sum]
        simp only [h, Finset.sum_neg_distrib]
    _ = -v := by rw [← hv]

theorem qplusW_comm {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) (u : WeylGroup τ) :
    u * qplusW τ = qplusW τ * u := by
  refine ext_single fun i => ?_
  rw [mul_smul, mul_smul, qplusW_smul_single hτ, qplusW_smul hτ, smul_neg]

section CanonicalRep

variable {τ : Tag} {K : Type} [Field K] [CharP K 2]

theorem qplus_torusElt_neg_one (i : Fin τ.rank) : torusElt τ K i (-1) = 1 := by
  rw [CFSG.RankThree.Chevalley.sixTorus_units_neg_one (CharP.cast_eq_zero K 2), torusElt_one]

theorem qplus_weylElt_mul_canonicalRep (i : Fin τ.rank) (w : WeylGroup τ) :
    weylElt τ K i 1 * canonicalRep (coxeterSystem τ) K w =
      canonicalRep (coxeterSystem τ) K (simple τ i * w) := by
  rw [weylElt_mul_canonicalRep]
  split_ifs
  · rfl
  · rw [qplus_torusElt_neg_one, one_mul]

theorem qplus_canonicalRep_wordProd_mul (ω : List (Fin τ.rank)) (w : WeylGroup τ) :
    canonicalRep (coxeterSystem τ) K ((coxeterSystem τ).wordProd ω * w) =
      (ω.map fun i => weylElt τ K i 1).prod * canonicalRep (coxeterSystem τ) K w := by
  induction ω with
  | nil => simp
  | cons i ω ih =>
    rw [CoxeterSystem.wordProd_cons, mul_assoc, ← qplus_weylElt_mul_canonicalRep, ih,
      List.map_cons, List.prod_cons, mul_assoc]

theorem qplus_canonicalRep_wordProd (ω : List (Fin τ.rank)) :
    canonicalRep (coxeterSystem τ) K ((coxeterSystem τ).wordProd ω) =
      (ω.map fun i => weylElt τ K i 1).prod := by
  have h := qplus_canonicalRep_wordProd_mul (K := K) ω 1
  rwa [mul_one, canonicalRep_one (coxeterSystem τ) K, mul_one] at h

theorem qplus_canonicalRep_mul (u w : WeylGroup τ) :
    canonicalRep (coxeterSystem τ) K (u * w) =
      canonicalRep (coxeterSystem τ) K u * canonicalRep (coxeterSystem τ) K w := by
  obtain ⟨ω, -, rfl⟩ := (coxeterSystem τ).exists_isReduced u
  rw [qplus_canonicalRep_wordProd_mul, qplus_canonicalRep_wordProd]

end CanonicalRep

@[expose] def qplusZ (τ : Tag) (K : Type) [Field K] : ModGL τ K :=
  ((qplusWord τ).map fun i => weylElt τ K i 1).prod

section Z

variable {τ : Tag} {K : Type} [Field K]

theorem qplusZ_mem : qplusZ τ K ∈ adjointGroup τ K :=
  list_prod_mem fun x hx => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    exact weylElt_mem_adjointGroup i 1

theorem qplus_rootChar_inv_neg (a : Fin τ.rank → Kˣ) (v : Fin τ.rank → ℤ) :
    rootChar a⁻¹ (-v) = rootChar a v := by
  simp only [rootChar, Pi.inv_apply, Pi.neg_apply, zpow_neg, inv_zpow, inv_inv]

variable [CharP K 2]

theorem qplusZ_eq_canonicalRep :
    qplusZ τ K = canonicalRep (coxeterSystem τ) K (qplusW τ) :=
  (qplus_canonicalRep_wordProd _).symm

theorem qplusZ_comm (hτ : τ = .E7 ∨ τ = .E8) (i : Fin τ.rank) :
    qplusZ τ K * weylElt τ K i 1 = weylElt τ K i 1 * qplusZ τ K := by
  rw [qplusZ_eq_canonicalRep, ← canonicalRep_simple (coxeterSystem τ) K i,
    ← qplus_canonicalRep_mul, ← qplus_canonicalRep_mul, qplusW_comm hτ (simple τ i)]

theorem qplusZ_conj_rootDiagUnit (hτ : τ = .E7 ∨ τ = .E8) (a : Fin τ.rank → Kˣ) :
    qplusZ τ K * rootDiagUnit τ a * (qplusZ τ K)⁻¹ = rootDiagUnit τ a⁻¹ := by
  rw [qplusZ_eq_canonicalRep]
  symm
  rw [rootDiagUnit_eq_conj_canonicalRep_iff]
  intro v
  rw [qplusW_smul hτ, qplus_rootChar_inv_neg]

end Z

end CFSG.RankThree.PartOne.KE
