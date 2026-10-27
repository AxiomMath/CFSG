module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P20o
import CFSG.GH74.Filter.Lie.SepWitness
import CFSG.LocalAnalysis.UniquenessCase.Lie.ExcShared
import CFSG.LocalAnalysis.UniquenessCase.UC22P20v

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley Subgroup
open CFSG.Blueprint (LieModel)

theorem uc22pwex_eq_one_of_prod_zpow_eq_one {G : Type*} [CommGroup G] {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) ℤ} {m p : ℕ} (hAB : A * B = m • (1 : Matrix (Fin n) (Fin n) ℤ))
    (hcop : Nat.Coprime m p) {t : Fin n → G} (ht : ∀ i, t i ^ p = 1)
    (h : ∀ j, ∏ i, t i ^ A i j = 1) : t = 1 := by
  funext k
  have hk : t k ^ m = 1 := by
    have h1 : t k ^ m = ∏ i, t i ^ ((A * B) i k) := by
      rw [hAB]
      simp [Matrix.smul_apply, Matrix.one_apply]
    rw [h1]
    simp only [Matrix.mul_apply, ← prod_zpow_eq_zpow_sum, zpow_mul]
    rw [Finset.prod_comm]
    simp only [Finset.prod_zpow, h, one_zpow, Finset.prod_const_one]
  have h2 := (pow_gcd_eq_one (a := t k)).2 ⟨hk, ht k⟩
  rw [Pi.one_apply]
  rwa [hcop, pow_one] at h2

section Torus


theorem uc22pwex_torusCoordHom_ker_pTorsion {τ : Tag} {R : Type*} [CommRing R]
    {B : Matrix (Fin τ.rank) (Fin τ.rank) ℤ} {m p : ℕ}
    (hB : τ.cartan * B = m • (1 : Matrix (Fin τ.rank) (Fin τ.rank) ℤ)) (hcop : Nat.Coprime m p)
    {t : Fin τ.rank → Rˣ} (ht : ∀ i, t i ^ p = 1) (h : torusCoordHom τ R t = 1) : t = 1 := by
  refine uc22pwex_eq_one_of_prod_zpow_eq_one hB hcop ht fun j => Units.ext ?_
  have h' := torusCoordHom_apply_rootVec_single (R := R) t j
  rw [h, OneMemClass.coe_one, Units.val_one, Module.End.one_apply,
    rootVec_eq_single_of_isRoot (isRoot_single τ j)] at h'
  have h'' := congrArg (fun v : RootModule τ R =>
    v (Sum.inr ⟨Pi.single j 1, isRoot_single τ j⟩)) h'
  simp only [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one] at h''
  rw [Units.val_one, ← h'']

theorem uc22pwex_e6_torusCoordHom_ker {K : Type} [Field K] {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    {t : Fin Tag.E6.rank → Kˣ} (ht : ∀ i, t i ^ p = 1) (h : torusCoordHom Tag.E6 K t = 1) :
    t = 1 :=
  uc22pwex_torusCoordHom_ker_pTorsion (B := cubeMatrixE6) (m := 3) cartan_mul_cubeMatrixE6
    ((Nat.coprime_primes Nat.prime_three hp).2 (Ne.symm hp3)) ht h

end Torus

theorem uc22pwex_e6_model {G : Type} [Group G] {n : ℕ} (h : LieModel G .E6 0 2 n) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
      Nonempty (G ≃* CFSG.Blueprint.AdjointQuotient .E6 F) :=
  (h.chevalleyExceptionalModel (by decide)).2

section Witness


theorem uc22pwex_e6_borelWit {G : Type} [Group G] [Finite G] {n : ℕ} (hG : LieModel G .E6 0 2 n)
    {p : ℕ} (hp : p.Prime) (hpn : p ∣ 2 ^ n - 1) (hp3 : p ≠ 3) : uc22p20oBorelWit G p 4 := by
  obtain ⟨F, _, _, hF, ⟨e₀⟩⟩ := uc22pwex_e6_model hG
  let e : G ≃* ↥(adjointGroup .E6 F) := e₀.trans (CFSG.GH74.Filter.Lie.adjointQuotientEquiv .E6 F)
  haveI : CharP F 2 := uc22pwex_charP_two hF
  have hle : posUnipotent .E6 F ≤ adjointGroup .E6 F := posUnipotent_le_adjointGroup
  obtain ⟨hU, hidx⟩ := isPGroup_and_not_dvd_index 2 hle (card_posUnipotent (τ := .E6) (K := F))
  have hpF : p ∣ Nat.card F - 1 := by rw [hF]; exact hpn
  obtain ⟨μ, hμc, hμp⟩ := uc22pwex_exists_mu hp hpF
  have hT : torusGroup .E6 F ≤ adjointGroup .E6 F :=
    torusGroup_le_borelGroup.trans borelGroup_le_adjointGroup'
  let Φ : (Fin Tag.E6.rank → μ) →* ↥(adjointGroup .E6 F) :=
    (Subgroup.inclusion hT).comp ((torusCoordHom .E6 F).comp
      (Pi.monoidHom fun i => μ.subtype.comp (Pi.evalMonoidHom (fun _ => μ) i)))
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 : torusCoordHom .E6 F (fun i => (a i : Fˣ)) = 1 := by
      have := congrArg (fun x : ↥(adjointGroup .E6 F) => (x : ModGL .E6 F)) ha
      exact Subtype.ext this
    have h2 := uc22pwex_e6_torusCoordHom_ker hp hp3 (fun i => hμp (a i)) h1
    funext i
    exact Subtype.ext (congrFun h2 i)
  have hA : Nat.card (Fin Tag.E6.rank → μ) = p ^ 6 := by
    rw [Nat.card_pi]
    simp [hμc]
    rfl
  obtain ⟨hE, hc⟩ := uc22pwex_elemAbelian_range Φ hinj (fun a b => mul_comm a b)
    (fun a => funext fun i => Subtype.ext (hμp (a i))) hA
  have hN : Φ.range ≤ normalizer (((posUnipotent .E6 F).subgroupOf (adjointGroup .E6 F) :
      Subgroup ↥(adjointGroup .E6 F)) : Set ↥(adjointGroup .E6 F)) := by
    rintro _ ⟨a, rfl⟩
    refine uc22pwex_mem_normalizer_subgroupOf ?_
    exact torusGroup_le_normalizer_posUnipotent (((torusCoordHom .E6 F)
      (Pi.monoidHom (fun i => μ.subtype.comp (Pi.evalMonoidHom (fun _ => μ) i)) a)).2)
  exact uc22p20v_borelWit_mono hp (uc22pwex_borelWit_of_equiv e _ hU hidx Φ.range hN hE hc)
    (by norm_num)

end Witness

end CFSG.LocalAnalysis.UniquenessCase.UC22
