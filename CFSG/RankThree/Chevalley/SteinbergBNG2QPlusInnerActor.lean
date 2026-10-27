module

public import CFSG.RankThree.Chevalley.SteinbergBNG2QPlusLocalCore
public import CFSG.RankThree.Chevalley.SteinbergCAG2ToralPrimePlane

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.LocalRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.UnbalancedCatalog
open Subgroup
open scoped Pointwise commutatorElement

namespace SteinbergBN

theorem toral_or_monomial_neg_of_conj_eq_pow {L : Type} [Field L] [Finite L] {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hpq : p ∣ Nat.card L - 1) {v : ModGL .G2 L}
    (hv : v ∈ adjointGroup .G2 L) {m : ℕ} (hvV : ∀ x ∈ torusTorsion L p, v * x * v⁻¹ = x ^ m) :
    v ∈ torusGroup .G2 L ∨ ∃ hvN : v ∈ monomialSubgroup .G2 L,
      ∀ w : Fin Tag.G2.rank → ℤ, weylQuotientHom .G2 L ⟨v, hvN⟩ • w = -w := by
  obtain ⟨-, -, -, hnf, -, -, hscal, -⟩ :=
    G2_toral_prime_plane_centralizer_and_scalar_normalizers L hp hp3 hpq
  have : Finite (Module.End L (RootModule .G2 L)) := Module.finite_of_finite L
  have hvN : v ∈ adjointGroup .G2 L ⊓ normalizer (torusTorsion L p : Set (ModGL .G2 L)) :=
    ⟨hv, mem_normalizer_fintype fun x hx => by
      rw [hvV x hx]
      exact pow_mem hx m⟩
  obtain ⟨h, hh, w, rfl⟩ := hnf v hvN
  have hpow : ∀ x ∈ torusTorsion L p, x ^ m = x ^ (m : ZMod p).val := by
    intro x hx
    have hxp : x ^ p = 1 := (mem_torusTorsion_iff.1 hx).2
    rw [ZMod.val_natCast]
    conv_lhs => rw [← Nat.div_add_mod m p, pow_add, pow_mul, hxp, one_pow, one_mul]
  rcases hscal h hh w (m : ZMod p) (fun x hx => by rw [hvV x hx, hpow x hx]) with
    ⟨rfl, -⟩ | ⟨hw, -⟩
  · left
    rw [canonicalRep_one, mul_one]
    exact hh
  · right
    have hn : h * canonicalRep (coxeterSystem .G2) L w ∈ monomialSubgroup .G2 L :=
      mul_mem (torusGroup_le_monomialSubgroup hh) (canonicalRep_mem_monomialSubgroup L w)
    refine ⟨hn, fun u => ?_⟩
    have hπ : weylQuotientHom .G2 L ⟨h * canonicalRep (coxeterSystem .G2) L w, hn⟩ = w :=
      weylQuotientHom_eq (by
        simpa using (mapsRootLines_of_mem_torusGroup hh).mul (mapsRootLines_canonicalRep w))
    rw [hπ]
    exact hw u

end SteinbergBN

open SteinbergBN

theorem odd_G2_qplus_inner_actor_local_core_product_odd {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = ℓ ^ f)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpq : p ∣ Nat.card K + 1)
    (B : Subgroup (MulAut (adjointGroup .G2 K)))
    (hB : (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)).range ≤ B)
    (E : Subgroup B) (hE : IsElementaryAbelian p E) (hEcard : Nat.card E = p ^ 2) (t : B)
    (htE : t ∈ E) (ht1 : t ≠ 1)
    (htinn : (t : MulAut (adjointGroup .G2 K)) ∈
      (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)).range) :
    thetaT p E = ⊥ ∧
    Odd (Nat.card ↥(⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer {t}), E⁆ :
      Subgroup B)) ∧
    ((⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer {t}), E⁆ : Subgroup B) :
        Set B) * (thetaT p E : Set B) =
      ((⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer {t}), E⁆ ⊔ thetaT p E :
        Subgroup B) : Set B) ∧
    Odd (Nat.card ↥(⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer {t}), E⁆ ⊔
      thetaT p E)) := by
  have hIB := thetaT_eq_bot_qplus_of_normalizer hℓ hℓ2 hℓ3 hf K hK hp hp3 hpq
    (fun L _ _ _ hpL v hv _ hvV => toral_or_monomial_neg_of_conj_eq_pow hp hp3 hpL hv hvV)
    B hB E hE hEcard
  have hodd := odd_card_commutator_qplus_inner hℓ hℓ2 hℓ3 hf K hK hp hp3 hpq B hB E hE t htE ht1
    htinn
  refine ⟨hIB, hodd, ?_, ?_⟩
  · rw [hIB, sup_bot_eq, Subgroup.coe_bot, Set.mul_singleton]
    simp
  · rw [hIB, sup_bot_eq]
    exact hodd

end CFSG.RankThree.Chevalley
