module

public import CFSG.RankThree.PartOne.KE6.EqpTorus
public import CFSG.RankThree.Lattice.SteinbergBIE6QplusData
public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusWeyl
public import CFSG.LieType.Chevalley.FoldedWeylIdentification
public import CFSG.LieType.Chevalley.FoldedWeylData
public import CFSG.RankThree.PartOne.K133H.F4Weyl
public import CFSG.RankThree.PartOne.KE.CTLangData
public import CFSG.LieType.Chevalley.GraphFixedData
public import CFSG.Timmesfeld.Orders.ExceptionalTwisted
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.SignKernelComponentBruhat
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.RankThree.Classical2.TwistedE6Phi3Centralizer
public import CFSG.RankThree.Lattice.SteinbergBIE6Qplus
public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
public import CFSG.RankThree.PartOne.KE.CTCasesCycloGlue
public import CFSG.RankThree.PartOne.KE6.EqpArith
public import CFSG.RankThree.PartOne.KE6.Phi3Arith
public import CFSG.RankThree.PartOne.KE6.Phi3Lattice
public import CFSG.RankThree.PartOne.KE6.Phi3Torus
public import CFSG.RankThree.PartOne.KE6.Phi6Arith
public import CFSG.RankThree.PartOne.KF4.KernelTools
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.RankThree.PartOne.KE6 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace CFSG.StandardType.ExcFrames.E6QPlusThree

section Certs

section E6Rho

open CFSG.RankThree.E6

private theorem permLattice_e6Rho_invol (v : Fin Tag.E6.rank → ℤ) :
    permLattice e6Rho (permLattice e6Rho v) = v := by
  have hs : e6Rho.symm = e6Rho := by decide
  have h := permLattice_symm_permLattice (τ := Tag.E6) e6Rho v
  rwa [hs] at h

end E6Rho

private theorem units_map_iterateFrobenius_eqpN_pow
    (L : Type) [Field L] [CharP L 2]
    (g0 : ModGL Tag.E6 L)
    (hg0 : Units.map (entrywiseHom (frobenius L 2)) g0 = g0 * eqpN L) (k : ℕ) :
    Units.map (entrywiseHom (iterateFrobenius L 2 k)) g0 = g0 * eqpN L ^ k := by
  have hfix : Units.map (entrywiseHom (frobenius L 2)) (eqpN L) = eqpN L :=
    CFSG.RankThree.PartOne.KE.frobenius_canonicalRep (frobenius L 2) e6W0
  induction k with
  | zero =>
      rw [iterateFrobenius_zero, pow_zero, mul_one]
      exact Units.ext (entrywise_id _)
  | succ k ih =>
      have hcomp : iterateFrobenius L 2 (k + 1) =
          (frobenius L 2).comp (iterateFrobenius L 2 k) := by
        rw [show k + 1 = 1 + k by omega, iterateFrobenius_add, iterateFrobenius_one]
      calc
        Units.map (entrywiseHom (iterateFrobenius L 2 (k + 1))) g0
            = Units.map (entrywiseHom ((frobenius L 2).comp (iterateFrobenius L 2 k))) g0 := by
                rw [hcomp]
        _ = Units.map (entrywiseHom (frobenius L 2))
              (Units.map (entrywiseHom (iterateFrobenius L 2 k)) g0) :=
              (units_map_entrywiseHom_comp (t := TwistTag.E6) (frobenius L 2)
                (iterateFrobenius L 2 k) g0).symm
        _ = Units.map (entrywiseHom (frobenius L 2)) (g0 * eqpN L ^ k) := by rw [ih]
        _ = Units.map (entrywiseHom (frobenius L 2)) g0 *
              Units.map (entrywiseHom (frobenius L 2)) (eqpN L ^ k) := by rw [map_mul]
        _ = (g0 * eqpN L) * (eqpN L) ^ k := by rw [hg0, map_pow, hfix]
        _ = g0 * eqpN L ^ (k + 1) := by rw [pow_succ', mul_assoc]

theorem e6W0_mul_self :
    e6W0 * e6W0 = 1 := by
  apply FaithfulSMul.eq_of_smul_eq_smul (α := Fin Tag.E6.rank → ℤ)
  intro v
  rw [mul_smul, e6W0_smul, e6W0_smul, permLattice_neg, neg_neg, permLattice_e6Rho_invol,
    one_smul]

theorem eqpN_mul_self
    (L : Type) [Field L] [CharP L 2] : eqpN L * eqpN L = 1 := by
  change canonicalRep (coxeterSystem Tag.E6) L e6W0 *
    canonicalRep (coxeterSystem Tag.E6) L e6W0 = 1
  rw [← CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_mul_of_charTwo, e6W0_mul_self,
    canonicalRep_one (coxeterSystem Tag.E6) L]

theorem centralizer_e6W0 :
    Subgroup.centralizer ({e6W0} : Set (WeylGroup Tag.E6)) = relWeylTwist TwistTag.E6 := by
  ext w
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hw
    refine (mem_relWeylTwist_iff_smul TwistTag.E6).2 fun (v : Fin Tag.E6.rank → ℤ) => ?_
    have h := congrArg (fun g : WeylGroup Tag.E6 => g • v) hw
    simp only [mul_smul, e6W0_smul, smul_neg] at h
    exact neg_inj.mp h
  · intro h
    have h' := (mem_relWeylTwist_iff_smul TwistTag.E6).1 h
    apply FaithfulSMul.eq_of_smul_eq_smul (α := Fin Tag.E6.rank → ℤ)
    intro v
    have hv : w • permLattice CFSG.RankThree.E6.e6Rho v =
        permLattice CFSG.RankThree.E6.e6Rho (w • v) := h' v
    calc
      (w * e6W0) • v = w • (e6W0 • v) := by rw [mul_smul]
      _ = w • (-permLattice CFSG.RankThree.E6.e6Rho v) := by rw [e6W0_smul]
      _ = -(w • permLattice CFSG.RankThree.E6.e6Rho v) := by rw [smul_neg]
      _ = -permLattice CFSG.RankThree.E6.e6Rho (w • v) := by rw [hv]
      _ = e6W0 • (w • v) := by rw [e6W0_smul]
      _ = (e6W0 * w) • v := by rw [mul_smul]

theorem card_centralizer_e6W0 :
    Nat.card (Subgroup.centralizer ({e6W0} : Set (WeylGroup Tag.E6))) = 1152 := by
  rw [centralizer_e6W0]
  exact (Nat.card_congr (foldedWeylEquiv TwistTag.E6).toEquiv).trans
    CFSG.RankThree.PartOne.K133H.card_weylGroup_F4

theorem exists_lang_eqpN
    (K : Type) [Field K] [Finite K] [CharP K 2] (h3 : 3 ∣ Nat.card K + 1)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L 2]
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K) :
    ∃ g0 : ModGL .E6 L, g0 ∈ adjointGroup .E6 L ∧
      Units.map (entrywiseHom (frobenius L 2)) g0 = g0 * eqpN L ∧
      Units.map (entrywiseHom Fr) g0 = g0 * eqpN L := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨f, -, hfcard⟩ := FiniteField.card K 2
  have hq : Nat.card K = 2 ^ (f : ℕ) := by
    rw [Nat.card_eq_fintype_card, hfcard]
  have hfpos : 1 ≤ (f : ℕ) := f.pos
  have hodd : Odd (f : ℕ) := by
    rw [← Nat.not_even_iff_odd]
    intro hev
    have hmod : (2 ^ (f : ℕ) + 1) % 3 = 0 :=
      Nat.dvd_iff_mod_eq_zero.mp (by simpa only [hq] using h3)
    rw [Nat.add_mod, CFSG.Timmesfeld.ExceptionalOrders.two_pow_mod_three,
      if_pos hev] at hmod
    norm_num at hmod
  obtain ⟨g0, hg0adj, hg0⟩ :=
    CFSG.RankThree.PartOne.KE.lang_conjugator Tag.E6 K (ℓ := 2) (f := 1) le_rfl L e6W0
  have hg0' : Units.map (entrywiseHom (iterateFrobenius L 2 1)) g0 = g0 * eqpN L := by
    simpa only [eqpN] using hg0
  have h1 : Units.map (entrywiseHom (frobenius L 2)) g0 = g0 * eqpN L := by
    rw [← iterateFrobenius_one]
    exact hg0'
  refine ⟨g0, hg0adj, h1, ?_⟩
  have hFrEq : Fr = iterateFrobenius L 2 (f : ℕ) := by
    refine RingHom.ext fun c => ?_
    rw [hFr, hq, iterateFrobenius_def]
  rw [hFrEq, units_map_iterateFrobenius_eqpN_pow L g0 h1 (f : ℕ)]
  have hpow : eqpN L ^ (f : ℕ) = eqpN L := by
    obtain ⟨m, hm⟩ := hodd
    rw [hm, pow_add, pow_mul, pow_two, eqpN_mul_self L, one_pow, one_mul, pow_one]
  rw [hpow]

end Certs

end CFSG.StandardType.ExcFrames.E6QPlusThree
