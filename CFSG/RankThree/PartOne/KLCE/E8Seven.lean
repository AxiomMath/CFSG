module

public import CFSG.RankThree.PartOne.KLCE.A1Sector
public import CFSG.RankThree.PartOne.KE.A1E8Seven
public import CFSG.RankThree.PartOne.KLC.EigE8
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


theorem e8Seven_frame {K₀ L : Type} [Field K₀] [Finite K₀] [Field L] [Algebra K₀ L]
    [IsAlgClosure K₀ L] [CharP L 2] {f₀ : ℕ} (hf₀ : 1 ≤ f₀) (hK₀ : Nat.card K₀ = 2 ^ f₀)
    (δ : ℤ) (hδ : δ = 1 ∨ δ = -1) {p : ℕ} (hp : p.Prime) (hp7 : 7 < p) {m : ℕ}
    (hm : m = 7 ∨ m = 14) (hordq : orderOf ((Nat.card K₀ : ℕ) : ZMod p) = m)
    (hpq : ¬ p ∣ Nat.card K₀) (hR : ¬ (p : ℤ) ∣ (Nat.card K₀ : ℤ) ^ 7 + δ) (a : ZMod p)
    (ha : a ^ 6 + a ^ 5 + a ^ 4 + a ^ 3 + a ^ 2 + a + 1 = 0)
    (hcol : ∀ z : Fin Tag.E8.rank → ZMod p,
      ((δ • e8O7W).map (Int.cast : ℤ → ZMod p))ᵀ *ᵥ z = ((Nat.card K₀ : ℕ) : ZMod p) • z →
        (e8O7W.map (Int.cast : ℤ → ZMod p))ᵀ *ᵥ z = a • z)
    (n : ModGL .E8 L) (hnm : n ∈ monomialSubgroup .E8 L)
    (hnW : ∀ u, weylQuotientHom .E8 L ⟨n, hnm⟩ • u = (δ • e8O7W) *ᵥ u) :
    ¬ p ∣ Nat.card (WeylGroup .E8) ∧ ∃ N₀ : ℕ, N₀ ≠ 0 ∧
      Nat.card (subtorusA1 n (Units.map (entrywiseHom (iterateFrobenius L 2 f₀))) e8O7Theta) =
        N₀ ∧
      p ^ (Nat.card (adjointGroup .E8 K₀)).factorization p = p ^ N₀.factorization p ∧
      (∀ a : Fin Tag.E8.rank → Lˣ,
        rootDiagUnit .E8 a ∈ subtorusA1 n (Units.map (entrywiseHom (iterateFrobenius L 2 f₀)))
          e8O7Theta → orderOf (rootDiagUnit .E8 a) = p →
        rootCharKernel a ⊆ {e8O7Theta, -e8O7Theta}) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K₀ 2 := ⟨fun x => by
    rw [← (algebraMap K₀ L).injective.eq_iff, map_natCast, map_zero]
    exact CharP.cast_eq_zero_iff L 2 x⟩
  have hq2 : 2 ≤ Nat.card K₀ := Finite.one_lt_card
  have : Fintype K₀ := Fintype.ofFinite K₀
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K₀
  set Fr : L →+* L := iterateFrobenius L 2 f₀ with hFrdef
  have hFr : ∀ c, Fr c = c ^ Nat.card K₀ := fun c => by
    rw [hK₀]
    exact iterateFrobenius_def 2 f₀ c
  have hℓq : 2 ∣ Nat.card K₀ := by
    rw [hK₀]
    exact dvd_pow_self _ (by omega)
  have hordW : ¬ p ∣ Nat.card (WeylGroup .E8) :=
    not_dvd_card_weylGroup_E hp hp7 (Or.inr (Or.inr rfl))
  have hθroot : IsRoot .E8 e8O7Theta :=
    E8_order_seven_lattice_exact_A1_root_kernel_and_negative_frame.1
  have hT : twistedTorusOf n (Units.map (entrywiseHom Fr)) =
      (fixedCharTuples (δ • e8O7W) Fr).map (rootDiagUnitHom .E8 L) := by
    rw [← twistedFixedTuples_eq_fixedCharTuples hnW Fr]
    exact twistedTorus_eq_map_twistedFixedTuples_of_weylImage hnm _ rfl Fr
  have hZeq := subtorusA1_eq_map_fixedBlockTuples hT hθroot
  have hinj0 : Function.Injective (rootDiagUnitHom .E8 L) := rootDiagUnit_injective
  set D := e8SevenBlock δ hδ with hD
  have hq7 : (1 : ℤ) < (Nat.card K₀ : ℤ) ^ 7 := by
    have : (2 : ℤ) ≤ Nat.card K₀ := by exact_mod_cast hq2
    calc (1 : ℤ) < 2 := by norm_num
      _ ≤ 2 ^ 7 := by norm_num
      _ ≤ (Nat.card K₀ : ℤ) ^ 7 := pow_le_pow_left₀ (by norm_num) this 7
  have hδle : δ ≤ 1 := by rcases hδ with rfl | rfl <;> norm_num
  have hδge : -1 ≤ δ := by rcases hδ with rfl | rfl <;> norm_num
  have hne : D.P.eval (Nat.card K₀ : ℤ) ≠ 0 := by
    show (Polynomial.X ^ 7 - Polynomial.C δ : ℤ[X]).eval (Nat.card K₀ : ℤ) ≠ 0
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
    omega
  obtain ⟨hcycB, hcardB⟩ := D.isCyclic_and_card Fr hFr Nat.prime_two hℓq hne
  set N : ℕ := ((Nat.card K₀ : ℤ) ^ 7 - δ).natAbs with hNdef
  have hNint : (N : ℤ) = (Nat.card K₀ : ℤ) ^ 7 - δ := by
    rw [hNdef]
    exact Int.natAbs_of_nonneg (by omega)
  have hZcard : Nat.card (subtorusA1 n (Units.map (entrywiseHom Fr)) e8O7Theta) = N := by
    rw [hZeq, Subgroup.card_map_of_injective hinj0, hcardB]
    show ((Polynomial.X ^ 7 - Polynomial.C δ : ℤ[X]).eval (Nat.card K₀ : ℤ)).natAbs = N
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
    exact hNdef.symm
  have hN : N ≠ 0 := by
    intro h0
    rw [h0] at hNint
    push_cast at hNint
    omega
  have hord : p ^ (Nat.card (adjointGroup .E8 K₀)).factorization p =
      p ^ N.factorization p := by
    have h1 : 1 ≤ Nat.card K₀ ^ 14 := Nat.one_le_pow _ _ (by omega)
    have hrest : ∀ d ∈ ([2, 8, 12, 14, 18, 20, 24, 30] : List ℕ), d ≠ 14 → ¬ m ∣ d := by
      intro d hd hd14
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hm with rfl | rfl <;>
        rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    refine ordProj_card_adjointGroup_E8 hp (by omega) hpq hordq (d₀ := 14) (by decide) hrest hN
      (R := (Nat.card K₀ : ℤ) ^ 7 + δ) ?_ hR
    push_cast [Nat.cast_sub h1]
    rw [hNint]
    rcases hδ with rfl | rfl <;> ring
  have hz : ∀ z : Fin Tag.E8.rank → ZMod p, z ≠ 0 →
      ((δ • e8O7W).map (Int.cast : ℤ → ZMod p))ᵀ *ᵥ z = ((Nat.card K₀ : ℕ) : ZMod p) • z →
        {α | IsRoot .E8 α ∧ pair α z = 0} = {e8O7Theta, -e8O7Theta} := fun z hz0 hzM =>
    E8_order_seven_lattice_exact_A1_root_kernel_and_negative_frame.2.2.2.2.2.2.2.2.2.1 p hp hp7 a
      ha z hz0 (hcol z hzM)
  refine ⟨hordW, N, hN, hZcard, hord, ?_⟩
  intro b hb hbp
  rw [hZeq] at hb
  obtain ⟨b', hb', hbb'⟩ := hb
  have : b' = b := hinj0 hbb'
  subst this
  exact (A1BlockData.rootCharKernel_eq Fr hFr hp hz hb'.1
    (KE.pow_eq_one_of_orderOf_rootDiagUnit hbp)
    (KE.ne_one_of_orderOf_rootDiagUnit hp hbp)).le

end Frame

section Seven


theorem e8Seven_frame_plus {K₀ L : Type} [Field K₀] [Finite K₀] [Field L] [Algebra K₀ L]
    [IsAlgClosure K₀ L] [CharP L 2] {f₀ p : ℕ} (hf₀ : 1 ≤ f₀) (hK₀ : Nat.card K₀ = 2 ^ f₀)
    (hp : p.Prime) (hp7 : 7 < p) (hpf : (p : ℤ) ∣ (exhaustionPhi 7).eval (Nat.card K₀ : ℤ)) :
    ¬ p ∣ Nat.card (WeylGroup .E8) ∧
      ∃ n₀ : ModGL .E8 L, n₀ ∈ adjointGroup .E8 L ∧
        Units.map (entrywiseHom (iterateFrobenius L 2 f₀)) n₀ = n₀ ∧
        n₀ ∈ Subgroup.centralizer (rootRankOneGroup .E8 L e8O7Theta : Set (ModGL .E8 L)) ∧
        ∃ N₀ : ℕ, N₀ ≠ 0 ∧
          Nat.card (subtorusA1 n₀ (Units.map (entrywiseHom (iterateFrobenius L 2 f₀)))
            e8O7Theta) = N₀ ∧
          p ^ (Nat.card (adjointGroup .E8 K₀)).factorization p = p ^ N₀.factorization p ∧
          (∀ a : Fin Tag.E8.rank → Lˣ,
            rootDiagUnit .E8 a ∈ subtorusA1 n₀
              (Units.map (entrywiseHom (iterateFrobenius L 2 f₀))) e8O7Theta →
            orderOf (rootDiagUnit .E8 a) = p → rootCharKernel a ⊆ {e8O7Theta, -e8O7Theta}) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K₀
  have h7' : (p : ℤ) ∣ (Nat.card K₀ : ℤ) ^ 6 + (Nat.card K₀ : ℤ) ^ 5 + (Nat.card K₀ : ℤ) ^ 4 +
      (Nat.card K₀ : ℤ) ^ 3 + (Nat.card K₀ : ℤ) ^ 2 + (Nat.card K₀ : ℤ) + 1 := by
    simpa [exhaustionPhi] using hpf
  obtain ⟨hpq, hord, hdvd⟩ := CTE8.e8SevenPlus_data hp hp7 h7'
  have hΦ : ((Nat.card K₀ : ℕ) : ZMod p) ^ 6 + ((Nat.card K₀ : ℕ) : ZMod p) ^ 5 +
      ((Nat.card K₀ : ℕ) : ZMod p) ^ 4 + ((Nat.card K₀ : ℕ) : ZMod p) ^ 3 +
      ((Nat.card K₀ : ℕ) : ZMod p) ^ 2 + ((Nat.card K₀ : ℕ) : ZMod p) + 1 = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((Nat.card K₀ : ℤ) ^ 6 + (Nat.card K₀ : ℤ) ^ 5 +
      (Nat.card K₀ : ℤ) ^ 4 + (Nat.card K₀ : ℤ) ^ 3 + (Nat.card K₀ : ℤ) ^ 2 + (Nat.card K₀ : ℤ) + 1)
      p).2 h7'
    simpa using this
  have hcm := canonicalRep_mem_monomialSubgroup L e8W
  have hπ : weylQuotientHom .E8 L ⟨canonicalRep (coxeterSystem .E8) L e8W, hcm⟩ = e8W :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep e8W)
  have hnW : ∀ u, weylQuotientHom .E8 L ⟨canonicalRep (coxeterSystem .E8) L e8W, hcm⟩ • u =
      ((1 : ℤ) • e8O7W) *ᵥ u := fun u => by
    rw [hπ, one_smul]
    exact wordProd_smul_eq_wordMat_mulVec .E8 [0, 2, 3, 4, 5, 6] u
  obtain ⟨hordW, N₀, hN₀, hZcard, hord', hker⟩ := e8Seven_frame hf₀ hK₀ 1 (Or.inl rfl) hp hp7
    (m := 7) (Or.inl rfl) hord hpq (fun h => CTE8.not_dvd_add_of_dvd_sub hp7 hdvd h) _ hΦ
    (fun z hz => by simpa only [one_smul] using hz) _ hcm hnW
  have hfix : Units.map (entrywiseHom (iterateFrobenius L 2 f₀))
      (canonicalRep (coxeterSystem .E8) L e8W) = canonicalRep (coxeterSystem .E8) L e8W := by
    have := CFSG.LieType.Chevalley.entrywise_canonicalRep (iterateFrobeniusEquiv L 2 f₀) e8W
    rw [CFSG.LieType.AlgebraicGroups.iterateFrobeniusEquiv_toRingHom] at this
    exact this
  exact ⟨hordW, canonicalRep (coxeterSystem .E8) L e8W,
    canonicalRep_mem_adjointGroup (coxeterSystem .E8) L e8W, hfix, e8W_centralizes L,
    N₀, hN₀, hZcard, hord', hker⟩

theorem frobSector_E8_7 : FrobSector .E8 7 :=
  frobSector_of_a1Frame (τ := .E8) (d := 1) (Or.inr (Or.inr ⟨rfl, rfl⟩)) (e := 7) (p₀ := 7)
    (by norm_num) (θ := e8O7Theta)
    E8_order_seven_lattice_exact_A1_root_kernel_and_negative_frame.1
    (fun K _ _ p f₀ hp hp5 hf₀ hK hΦ hpr => by
      by_contra hle
      have hp7 : p ≤ 7 := not_lt.1 hle
      have hpK : ¬ p ∣ Nat.card K := by
        intro h
        rw [hK] at h
        have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h)
        omega
      have h1 : (p : ℤ) ∣ (Nat.card K : ℤ) - 1 :=
        KLC.dvd_sub_one_of_dvd_phi_seven_of_le hp hp5 hp7 hΦ
      have h2 := KLC.two_le_pRank_E8_of_sector hp hp5 hpK (e := 1) (Or.inl rfl)
        (by simpa [exhaustionPhi] using h1)
      omega)
    (fun K₀ L _ _ _ _ _ _ f₀ p hf₀ hK₀ hp hp7 hpf =>
      e8Seven_frame_plus (K₀ := K₀) (L := L) hf₀ hK₀ hp hp7 hpf)

theorem layerSector_E8_7 : KLC.LayerSector .E8 7 := layerSector_of_frob frobSector_E8_7

end Seven

section Fourteen


theorem map_WSL {L L' : Type} [Field L] [Field L'] (f : L →+* L') :
    Matrix.SpecialLinearGroup.map f (WSL : SL(2, L)) = WSL := by
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp [coe_WSL, Matrix.SpecialLinearGroup.map_apply_coe]

theorem WSL_mul_self_of_charTwo {L : Type} [Field L] [CharP L 2] :
    (WSL : SL(2, L)) * WSL = 1 := by
  have h2 : (-1 : L) = 1 := CharTwo.neg_eq 1
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp [coe_WSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, h2]

theorem e8Seven_frame_minus {K₀ L : Type} [Field K₀] [Finite K₀] [Field L] [Algebra K₀ L]
    [IsAlgClosure K₀ L] [CharP L 2] {f₀ p : ℕ} (hf₀ : 1 ≤ f₀) (hK₀ : Nat.card K₀ = 2 ^ f₀)
    (hp : p.Prime) (hp7 : 7 < p) (hpf : (p : ℤ) ∣ (exhaustionPhi 14).eval (Nat.card K₀ : ℤ)) :
    ¬ p ∣ Nat.card (WeylGroup .E8) ∧
      ∃ n₀ : ModGL .E8 L, n₀ ∈ adjointGroup .E8 L ∧
        Units.map (entrywiseHom (iterateFrobenius L 2 f₀)) n₀ = n₀ ∧
        (∃ J₀ : SL(2, L),
          (∀ B : SL(2, L), n₀ * rootSL2 .E8 L e8O7Theta B * n₀⁻¹ =
            rootSL2 .E8 L e8O7Theta (J₀ * B * J₀⁻¹)) ∧
          Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 f₀) J₀ = J₀ ∧ J₀ * J₀ = 1 ∧
          ∃ P₀ : GL (Fin 2) L, P₀ * Matrix.GeneralLinearGroup.map (iterateFrobenius L 2 f₀) P₀⁻¹ =
            Matrix.SpecialLinearGroup.toGL J₀) ∧
        ∃ N₀ : ℕ, N₀ ≠ 0 ∧
          Nat.card (subtorusA1 n₀ (Units.map (entrywiseHom (iterateFrobenius L 2 f₀)))
            e8O7Theta) = N₀ ∧
          p ^ (Nat.card (adjointGroup .E8 K₀)).factorization p = p ^ N₀.factorization p ∧
          (∀ a : Fin Tag.E8.rank → Lˣ,
            rootDiagUnit .E8 a ∈ subtorusA1 n₀
              (Units.map (entrywiseHom (iterateFrobenius L 2 f₀))) e8O7Theta →
            orderOf (rootDiagUnit .E8 a) = p → rootCharKernel a ⊆ {e8O7Theta, -e8O7Theta}) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K₀
  have : CharP K₀ 2 := ⟨fun x => by
    rw [← (algebraMap K₀ L).injective.eq_iff, map_natCast, map_zero]
    exact CharP.cast_eq_zero_iff L 2 x⟩
  have h14' : (p : ℤ) ∣ (Nat.card K₀ : ℤ) ^ 6 - (Nat.card K₀ : ℤ) ^ 5 + (Nat.card K₀ : ℤ) ^ 4 -
      (Nat.card K₀ : ℤ) ^ 3 + (Nat.card K₀ : ℤ) ^ 2 - (Nat.card K₀ : ℤ) + 1 := by
    simpa [exhaustionPhi] using hpf
  obtain ⟨hpq, hord, hdvd, ha⟩ := CTE8.e8SevenMinus_data hp hp7 h14'
  obtain ⟨hnm, hW, hQ⟩ := e8_negative_data (L := L)
  have hnW : ∀ u, weylQuotientHom .E8 L ⟨_, hnm⟩ • u = ((-1 : ℤ) • e8O7W) *ᵥ u := fun u => by
    rw [hW u, neg_one_smul, Matrix.neg_mulVec]
  obtain ⟨hordW, N₀, hN₀, hZcard, hord', hker⟩ := e8Seven_frame hf₀ hK₀ (-1) (Or.inr rfl) hp hp7
    (m := 14) (Or.inr rfl) hord hpq
    (fun h => CTE8.not_dvd_add_of_dvd_sub hp7 (by simpa [sub_eq_add_neg] using h) hdvd)
    (-((Nat.card K₀ : ℕ) : ZMod p)) ha
    (fun z hz => by
      rw [neg_one_smul, Matrix.map_neg (Int.cast : ℤ → ZMod p) (fun a => Int.cast_neg a) e8O7W,
        Matrix.transpose_neg, Matrix.neg_mulVec] at hz
      rw [neg_smul, ← hz, neg_neg]) _ hnm hnW
  have hfixW : Units.map (entrywiseHom (iterateFrobenius L 2 f₀))
      (canonicalRep (coxeterSystem .E8) L e8W) = canonicalRep (coxeterSystem .E8) L e8W := by
    have := CFSG.LieType.Chevalley.entrywise_canonicalRep (iterateFrobeniusEquiv L 2 f₀) e8W
    rw [CFSG.LieType.AlgebraicGroups.iterateFrobeniusEquiv_toRingHom] at this
    exact this
  have hfixN : Units.map (entrywiseHom (iterateFrobenius L 2 f₀)) (e8N0 L) = e8N0 L := by
    unfold e8N0
    rw [map_list_prod, List.map_ofFn]
    refine congrArg List.prod (congrArg List.ofFn (funext fun i => ?_))
    change Units.map (entrywiseHom (iterateFrobenius L 2 f₀))
      (rootSL2 .E8 L (e8Frame i) WSL) = rootSL2 .E8 L (e8Frame i) WSL
    rw [entrywise_rootSL2_of_field, map_WSL]
  have hfix : Units.map (entrywiseHom (iterateFrobenius L 2 f₀))
      (canonicalRep (coxeterSystem .E8) L e8W * e8N0 L) =
      canonicalRep (coxeterSystem .E8) L e8W * e8N0 L := by
    rw [map_mul, hfixW, hfixN]
  have hFr₀ : ∀ c, iterateFrobenius L 2 f₀ c = c ^ Nat.card K₀ := fun c => by
    rw [hK₀]
    exact iterateFrobenius_def 2 f₀ c
  obtain ⟨P₀, hP₀⟩ := exists_WSL_twist (K := K₀) (L := L) (iterateFrobenius L 2 f₀) hFr₀
  exact ⟨hordW, canonicalRep (coxeterSystem .E8) L e8W * e8N0 L, monomialSubgroup_le_adjointGroup' hnm,
    hfix, ⟨WSL, hQ, map_WSL _, WSL_mul_self_of_charTwo, P₀, hP₀⟩, N₀, hN₀, hZcard, hord', hker⟩

theorem frobSector_E8_14 : FrobSector .E8 14 :=
  frobSector_of_a1FrameU (τ := .E8) (d := 1) (Or.inr (Or.inr ⟨rfl, rfl⟩)) (e := 14) (p₀ := 7)
    (by norm_num) (θ := e8O7Theta)
    E8_order_seven_lattice_exact_A1_root_kernel_and_negative_frame.1
    (fun K _ _ p f₀ hp hp5 hf₀ hK hΦ hpr => by
      by_contra hle
      have hp7 : p ≤ 7 := not_lt.1 hle
      have hpK : ¬ p ∣ Nat.card K := by
        intro h
        rw [hK] at h
        have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h)
        omega
      have h1 : (p : ℤ) ∣ (Nat.card K : ℤ) + 1 :=
        KLC.dvd_add_one_of_dvd_phi_fourteen_of_le hp hp5 hp7 hΦ
      have h2 := KLC.two_le_pRank_E8_of_sector hp hp5 hpK (e := 2) (Or.inr (Or.inl rfl))
        (by simpa [exhaustionPhi] using h1)
      omega)
    (fun K₀ L _ _ _ _ _ _ f₀ p hf₀ hK₀ hp hp7 hpf =>
      e8Seven_frame_minus (K₀ := K₀) (L := L) hf₀ hK₀ hp hp7 hpf)

theorem layerSector_E8_14 : KLC.LayerSector .E8 14 := layerSector_of_frob frobSector_E8_14

end Fourteen

end CFSG.RankThree.PartOne.KLCE
