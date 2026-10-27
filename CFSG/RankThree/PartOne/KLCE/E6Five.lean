module

public import CFSG.RankThree.PartOne.KLCE.A1Sector
public import CFSG.RankThree.PartOne.KE.A1E6Five
public import CFSG.RankThree.PartOne.KLC.EigE6
public import CFSG.RankThree.PartOne.KLC.Degenerate
public import CFSG.LieType.AlgebraicGroups.E6GraphCentralizerRationalDescent

public noncomputable section

namespace CFSG.RankThree.PartOne.KLCE

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KE
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Lattice
open CFSG.RankThree.Chevalley (exhaustionPhi)

open scoped Matrix Polynomial MatrixGroups

section Frame


theorem e6Five_frame {K₀ L : Type} [Field K₀] [Finite K₀] [Field L] [Algebra K₀ L]
    [IsAlgClosure K₀ L] [CharP L 2] {f₀ p : ℕ} (hf₀ : 1 ≤ f₀) (hK₀ : Nat.card K₀ = 2 ^ f₀)
    (hp : p.Prime) (hp5 : 5 < p) (hpf : (p : ℤ) ∣ (exhaustionPhi 5).eval (Nat.card K₀ : ℤ)) :
    7 < p ∧ ¬ p ∣ Nat.card (WeylGroup .E6) ∧
    ∃ n₀ : ModGL .E6 L, n₀ ∈ adjointGroup .E6 L ∧
      Units.map (entrywiseHom (iterateFrobenius L 2 f₀)) n₀ = n₀ ∧
      n₀ ∈ Subgroup.centralizer (rootRankOneGroup .E6 L e6O5Theta : Set (ModGL .E6 L)) ∧
      ∃ N₀ : ℕ, N₀ ≠ 0 ∧
        Nat.card (subtorusA1 n₀ (Units.map (entrywiseHom (iterateFrobenius L 2 f₀))) e6O5Theta) =
          N₀ ∧
        p ^ (Nat.card (adjointGroup .E6 K₀)).factorization p = p ^ N₀.factorization p ∧
        (∀ a : Fin Tag.E6.rank → Lˣ,
          rootDiagUnit .E6 a ∈ subtorusA1 n₀ (Units.map (entrywiseHom (iterateFrobenius L 2 f₀)))
            e6O5Theta → orderOf (rootDiagUnit .E6 a) = p →
          rootCharKernel a ⊆ {e6O5Theta, -e6O5Theta}) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K₀ 2 := ⟨fun x => by
    rw [← (algebraMap K₀ L).injective.eq_iff, map_natCast, map_zero]
    exact CharP.cast_eq_zero_iff L 2 x⟩
  have hq2 : 2 ≤ Nat.card K₀ := Finite.one_lt_card
  have : Fintype K₀ := Fintype.ofFinite K₀
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K₀
  have hpf' : (p : ℤ) ∣ (Nat.card K₀ : ℤ) ^ 4 + (Nat.card K₀ : ℤ) ^ 3 + (Nat.card K₀ : ℤ) ^ 2 +
      (Nat.card K₀ : ℤ) + 1 := by simpa [exhaustionPhi] using hpf
  obtain ⟨hp7, hpq, hord5⟩ := CTE6.e6Five_data hp hp5 hpf'
  have hordW : ¬ p ∣ Nat.card (WeylGroup .E6) := not_dvd_card_weylGroup_E hp hp7 (Or.inl rfl)
  have hΦ5 : ((Nat.card K₀ : ℕ) : ZMod p) ^ 4 + ((Nat.card K₀ : ℕ) : ZMod p) ^ 3 +
      ((Nat.card K₀ : ℕ) : ZMod p) ^ 2 + ((Nat.card K₀ : ℕ) : ZMod p) + 1 = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((Nat.card K₀ : ℤ) ^ 4 + (Nat.card K₀ : ℤ) ^ 3 +
      (Nat.card K₀ : ℤ) ^ 2 + (Nat.card K₀ : ℤ) + 1) p).2 hpf'
    simpa using this
  set w : WeylGroup .E6 := (coxeterSystem .E6).wordProd [0, 2, 3, 4] with hwdef
  have hw : ∀ u, w • u = e6O5W *ᵥ u := wordProd_smul_eq_wordMat_mulVec .E6 [0, 2, 3, 4]
  set n : ModGL .E6 L := canonicalRep (coxeterSystem .E6) L w with hndef
  have hnC : n ∈ adjointGroup .E6 L := canonicalRep_mem_adjointGroup (coxeterSystem .E6) L w
  set Fr : L →+* L := iterateFrobenius L 2 f₀ with hFrdef
  have hFr : ∀ c, Fr c = c ^ Nat.card K₀ := fun c => by
    rw [hK₀]
    exact iterateFrobenius_def 2 f₀ c
  have hℓq : 2 ∣ Nat.card K₀ := by
    rw [hK₀]
    exact dvd_pow_self _ (by omega)
  have hnfix : Units.map (entrywiseHom Fr) n = n := by
    have := CFSG.LieType.Chevalley.entrywise_canonicalRep
      (iterateFrobeniusEquiv L 2 f₀) w
    rw [CFSG.LieType.AlgebraicGroups.iterateFrobeniusEquiv_toRingHom] at this
    exact this
  have hθroot : IsRoot .E6 e6O5Theta := E6_order_five_lattice_and_exact_A1_prime_root_kernel.1
  set J : Set (Fin Tag.E6.rank) := {i | i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4} with hJ
  have hJorth : ∀ i ∈ J, CFSG.LieType.Steinberg.Adjoint.iform
      (Pi.single i 1 : Fin Tag.E6.rank → ℤ) e6O5Theta = 0 := by
    intro i hi
    rcases hi with rfl | rfl | rfl | rfl <;> decide +kernel
  have hwJ : w ∈ parabolicWeylGroup .E6 J := by
    refine wordProd_mem_parabolicWeylGroup (fun i hi => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    exact hi
  have hsl : ∀ j : Fin Tag.E6.rank, Tag.E6.symmetrizer j j = 1 := by decide
  have hn : n ∈ Subgroup.centralizer (rootRankOneGroup .E6 L e6O5Theta : Set (ModGL .E6 L)) :=
    canonicalRep_mem_centralizer_rootRankOneGroup hsl hθroot hJorth hwJ
  have hT : twistedTorusOf n (Units.map (entrywiseHom Fr)) =
      (fixedCharTuples e6O5W Fr).map (rootDiagUnitHom .E6 L) := by
    rw [← twistedFixedTuples_eq_fixedCharTuples hw Fr]
    exact twistedTorus_eq_map_twistedFixedTuples w Fr
  have hZeq := subtorusA1_eq_map_fixedBlockTuples hT hθroot
  have hinj0 : Function.Injective (rootDiagUnitHom .E6 L) := rootDiagUnit_injective
  have hne : e6FiveBlock.P.eval (Nat.card K₀ : ℤ) ≠ 0 := by
    have h1 : (1 : ℤ) < (Nat.card K₀ : ℤ) ^ 5 := by
      have : (2 : ℤ) ≤ Nat.card K₀ := by exact_mod_cast hq2
      calc (1 : ℤ) < 2 := by norm_num
        _ ≤ 2 ^ 5 := by norm_num
        _ ≤ (Nat.card K₀ : ℤ) ^ 5 := pow_le_pow_left₀ (by norm_num) this 5
    show (Polynomial.X ^ 5 - Polynomial.C 1 : ℤ[X]).eval (Nat.card K₀ : ℤ) ≠ 0
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
    omega
  obtain ⟨hcycB, hcardB⟩ := e6FiveBlock.isCyclic_and_card Fr hFr Nat.prime_two hℓq hne
  have hZcard : Nat.card (subtorusA1 n (Units.map (entrywiseHom Fr)) e6O5Theta) =
      Nat.card K₀ ^ 5 - 1 := by
    rw [hZeq, Subgroup.card_map_of_injective hinj0, hcardB]
    show ((Polynomial.X ^ 5 - Polynomial.C 1 : ℤ[X]).eval (Nat.card K₀ : ℤ)).natAbs = _
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
    have h1 : 1 ≤ Nat.card K₀ ^ 5 := Nat.one_le_pow _ _ (by omega)
    have e : ((Nat.card K₀ : ℤ) ^ 5 - 1) = ((Nat.card K₀ ^ 5 - 1 : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub h1]
      ring
    rw [e, Int.natAbs_natCast]
  have hN : Nat.card K₀ ^ 5 - 1 ≠ 0 := by
    have : 1 < Nat.card K₀ ^ 5 := Nat.one_lt_pow (by norm_num) (by omega)
    omega
  have hord : p ^ (Nat.card (adjointGroup .E6 K₀)).factorization p =
      p ^ (Nat.card K₀ ^ 5 - 1).factorization p := by
    have h1 : 1 ≤ Nat.card K₀ ^ 5 := Nat.one_le_pow _ _ (by omega)
    exact ordProj_card_adjointGroup_E6 hp (by omega) hpq hord5 (d₀ := 5) (by decide) (by decide)
      hN (R := 1) (by push_cast [Nat.cast_sub h1]; ring) (by
        intro h
        exact hp.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h))
  have hz : ∀ z : Fin Tag.E6.rank → ZMod p, z ≠ 0 →
      (e6O5W.map (Int.cast : ℤ → ZMod p))ᵀ *ᵥ z = ((Nat.card K₀ : ℕ) : ZMod p) • z →
        {α | IsRoot .E6 α ∧ pair α z = 0} = {e6O5Theta, -e6O5Theta} := fun z hz0 hzM =>
    E6_order_five_lattice_and_exact_A1_prime_root_kernel.2.2.2.2.2.2.2.2 p hp hp5
      ((Nat.card K₀ : ℕ) : ZMod p) hΦ5 z hz0 hzM
  refine ⟨hp7, hordW, n, hnC, hnfix, hn, Nat.card K₀ ^ 5 - 1, hN, hZcard, hord, ?_⟩
  intro a ha hap
  rw [hZeq] at ha
  obtain ⟨a', ha', haa'⟩ := ha
  have : a' = a := hinj0 haa'
  subst this
  exact (A1BlockData.rootCharKernel_eq Fr hFr hp hz ha'.1
    (KE.pow_eq_one_of_orderOf_rootDiagUnit hap) (KE.ne_one_of_orderOf_rootDiagUnit hp hap)).le

end Frame

section Sector


theorem frobSector_E6_5 : FrobSector .E6 5 :=
  frobSector_of_a1Frame (τ := .E6) (d := 3) (Or.inl ⟨rfl, rfl⟩) (e := 5) (p₀ := 5) le_rfl
    (θ := e6O5Theta) E6_order_five_lattice_and_exact_A1_prime_root_kernel.1
    (fun K _ _ p f₀ hp hp5 hf₀ hK hΦ hpr => by
      by_contra hle
      have h5 : p = 5 := le_antisymm (not_lt.1 hle) hp5
      subst h5
      have hpK : ¬ 5 ∣ Nat.card K := by
        intro h
        rw [hK] at h
        have := Nat.le_of_dvd (by norm_num) (Nat.prime_five.dvd_of_dvd_pow h)
        omega
      have h1 : (5 : ℤ) ∣ (Nat.card K : ℤ) - 1 :=
        KLC.dvd_sub_one_of_dvd_phi_five (by exact_mod_cast hΦ)
      have h2 := KLC.two_le_pRank_E6_of_sector hp hp5 hpK (e := 1) (Or.inl rfl)
        (by simpa [exhaustionPhi] using h1)
      omega)
    (fun K₀ L _ _ _ _ _ _ f₀ p hf₀ hK₀ hp hp5 hpf => by
      obtain ⟨-, hordW, rest⟩ := e6Five_frame (K₀ := K₀) (L := L) hf₀ hK₀ hp hp5 hpf
      exact ⟨hordW, rest⟩)

theorem layerSector_E6_5 : KLC.LayerSector .E6 5 := layerSector_of_frob frobSector_E6_5

end Sector

end CFSG.RankThree.PartOne.KLCE
