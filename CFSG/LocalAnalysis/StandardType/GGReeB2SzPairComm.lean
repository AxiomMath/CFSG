module

public import CFSG.LocalAnalysis.StandardType.GGReeB2SzPairDefs
public import CFSG.RankThree.PartOne.SEITZ7.SzPair
public import CFSG.LieType.Ree.SmallReeCollectionCheck

public section

namespace CFSG.StandardType.ReeB2Fixed

open CFSG.SectionRank.LargeRee CFSG.LieType.Ree CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution CFSG.RankThree.PartOne.SEITZ7 CFSG.Quasithin.B45Sz

private theorem pinnedX_eq_eltUnit_two_ring
    {R : Type} [CommRing R] (h2 : (2 : R) = 0)
    {α : Fin Tag.F4.rank → ℤ} (hα : IsRoot Tag.F4 α) (c : R) :
    pinnedX Tag.F4 R α c = (rootOperatorFamily Tag.F4).eltUnit R ⟨α, hα⟩ c := by
  rw [(rootOperatorFamily Tag.F4).pinnedX_eq_eltUnit R hα c]
  congr 1
  rcases (rootOperatorFamily Tag.F4).pinnedFamilySign_eq α with h | h <;> rw [h]
  · simp
  · rw [Int.cast_neg, Int.cast_one]
    have hneg : (-1 : R) = 1 := by
      linear_combination (-1 : R) * h2
    rw [hneg, one_mul]

private def wordCheckTwo (L L' : List Factor) : Bool :=
  (L ++ L').all (fun f => Nat.blt f.2.2.1 Tag.F4.rootCertificate.roots.length) &&
    modEqCheck 2 (factorsN Tag.F4 [] L) (factorsN Tag.F4 [] L')

private theorem factorsProd_eq_factorPinned_two
    {R : Type} [CommRing R] (h2 : (2 : R) = 0) (fs : List Factor)
    (hfs : ∀ f ∈ fs, f.2.2.1 < Tag.F4.rootCertificate.roots.length) (s t : R) :
    factorsProd Tag.F4 R fs s t =
      (factorPinned Tag.F4 R fs s t : Module.End R (RootModule Tag.F4 R)) := by
  induction fs with
  | nil => simp [factorsProd, factorPinned]
  | cons f fs ih =>
    have hlt := hfs f List.mem_cons_self
    rw [factorsProd_cons, ih fun g hg => hfs g (List.mem_cons_of_mem _ hg), factorPinned_cons,
      Units.val_mul, dite_eq_left hlt,
      pinnedX_eq_eltUnit_two_ring h2
        (CFSG.LieType.Chevalley.RootWalk.isRoot_rootCertificate_root hlt),
      RootOperatorFamily.coe_eltUnit]
    rfl

private theorem factorPinned_eq_of_wordCheckTwo_type
    {L L' : List Factor} (h : wordCheckTwo L L' = true)
    (R : Type) [CommRing R] (hn : (2 : R) = 0) (s t : R) :
    factorPinned Tag.F4 R L s t = factorPinned Tag.F4 R L' s t := by
  simp only [wordCheckTwo, Bool.and_eq_true, List.all_eq_true, Nat.blt_eq] at h
  obtain ⟨hlen, hmod⟩ := h
  have hL : ∀ f ∈ L, f.2.2.1 < Tag.F4.rootCertificate.roots.length := fun f hf =>
    hlen f (List.mem_append_left _ hf)
  have hL' : ∀ f ∈ L', f.2.2.1 < Tag.F4.rootCertificate.roots.length := fun f hf =>
    hlen f (List.mem_append_right _ hf)
  have hv := (RootOps.dataChecks Tag.F4).valid
  have hnil : ValidP Tag.F4 ([] : List PEntry) := fun x hx => absurd hx List.not_mem_nil
  have heq : 1 + pOp Tag.F4 R (factorsN Tag.F4 [] L) s t =
      1 + pOp Tag.F4 R (factorsN Tag.F4 [] L') s t := by
    rw [pOp_eq_of_modEqCheck (τ := Tag.F4) hn hmod s t]
  rw [one_add_pOp_factorsN hv L hL [] hnil,
    one_add_pOp_factorsN hv L' hL' [] hnil,
    pOp_nil, add_zero, one_mul, one_mul, factorsProd_eq_factorPinned_two hn L hL,
    factorsProd_eq_factorPinned_two hn L' hL'] at heq
  exact Units.ext heq

open MvPolynomial in
private theorem factorPinned_eq_of_wordCheckTwo
    {L L' : List Factor} (h : wordCheckTwo L L' = true)
    (R : Type*) [CommRing R] (hn : (2 : R) = 0) (s t : R) :
    factorPinned Tag.F4 R L s t = factorPinned Tag.F4 R L' s t := by
  set A := MvPolynomial (Fin 2) (ZMod 2)
  have hA : ((2 : ℕ) : A) = 0 := by
    rw [← map_natCast (MvPolynomial.C (σ := Fin 2)), ZMod.natCast_self, map_zero]
  have h0 := factorPinned_eq_of_wordCheckTwo_type h A hA (X 0) (X 1)
  set φ : ZMod 2 →+* R := ZMod.castHom (ringChar.dvd hn) R
  set g : A →+* R := eval₂Hom φ ![s, t]
  have hg0 : g (X 0) = s := eval₂Hom_X' _ _ _
  have hg1 : g (X 1) = t := eval₂Hom_X' _ _ _
  have hb := baseChange_factorPinned (τ := Tag.F4) g L (X 0) (X 1)
  have hb' := baseChange_factorPinned (τ := Tag.F4) g L' (X 0) (X 1)
  rw [hg0, hg1] at hb hb'
  rw [h0] at hb
  exact Units.ext (hb.unique hb')

private def szPosA : List ℕ := [1, 2, 6, 7, 8, 9, 14, 18]

private def szPosB : List ℕ := [15, 16, 23, 26, 43, 44, 46, 47]

private theorem szRootsA_posA :
    ∀ γ ∈ szRootsA, ∃ m ∈ szPosA, Tag.F4.rootCertificate.root m = γ := by
  decide +kernel

private theorem szRootsB_posB :
    ∀ γ ∈ szRootsB, ∃ n ∈ szPosB, Tag.F4.rootCertificate.root n = γ := by
  decide +kernel

private theorem szWcRow_1 : ∀ n ∈ szPosB,
    wordCheckTwo [(1, 0, 1, 1), (0, 1, n, 1)] [(0, 1, n, 1), (1, 0, 1, 1)] = true := by
  decide +kernel

private theorem szWcRow_2 : ∀ n ∈ szPosB,
    wordCheckTwo [(1, 0, 2, 1), (0, 1, n, 1)] [(0, 1, n, 1), (1, 0, 2, 1)] = true := by
  decide +kernel

private theorem szWcRow_6 : ∀ n ∈ szPosB,
    wordCheckTwo [(1, 0, 6, 1), (0, 1, n, 1)] [(0, 1, n, 1), (1, 0, 6, 1)] = true := by
  decide +kernel

private theorem szWcRow_7 : ∀ n ∈ szPosB,
    wordCheckTwo [(1, 0, 7, 1), (0, 1, n, 1)] [(0, 1, n, 1), (1, 0, 7, 1)] = true := by
  decide +kernel

private theorem szWcRow_8 : ∀ n ∈ szPosB,
    wordCheckTwo [(1, 0, 8, 1), (0, 1, n, 1)] [(0, 1, n, 1), (1, 0, 8, 1)] = true := by
  decide +kernel

private theorem szWcRow_9 : ∀ n ∈ szPosB,
    wordCheckTwo [(1, 0, 9, 1), (0, 1, n, 1)] [(0, 1, n, 1), (1, 0, 9, 1)] = true := by
  decide +kernel

private theorem szWcRow_14 : ∀ n ∈ szPosB,
    wordCheckTwo [(1, 0, 14, 1), (0, 1, n, 1)] [(0, 1, n, 1), (1, 0, 14, 1)] = true := by
  decide +kernel

private theorem szWcRow_18 : ∀ n ∈ szPosB,
    wordCheckTwo [(1, 0, 18, 1), (0, 1, n, 1)] [(0, 1, n, 1), (1, 0, 18, 1)] = true := by
  decide +kernel

private theorem szWc_all : ∀ m ∈ szPosA, ∀ n ∈ szPosB,
    wordCheckTwo [(1, 0, m, 1), (0, 1, n, 1)] [(0, 1, n, 1), (1, 0, m, 1)] = true := by
  intro m hm
  simp only [szPosA, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [szWcRow_1, szWcRow_2, szWcRow_6, szWcRow_7, szWcRow_8, szWcRow_9, szWcRow_14,
    szWcRow_18]

private theorem commute_pinnedX_szRoots_two
    {R : Type*} [CommRing R] (h2 : (2 : R) = 0)
    {γ δ : Fin Tag.F4.rank → ℤ} (hγ : γ ∈ szRootsA) (hδ : δ ∈ szRootsB) (x y : R) :
    Commute (pinnedX Tag.F4 R γ x) (pinnedX Tag.F4 R δ y) := by
  obtain ⟨m, hm, rfl⟩ := szRootsA_posA γ hγ
  obtain ⟨n, hn, rfl⟩ := szRootsB_posB δ hδ
  have hw := factorPinned_eq_of_wordCheckTwo (szWc_all m hm n hn) R h2 x y
  simp only [factorPinned_cons, factorPinned_nil, Int.cast_one, one_mul, pow_zero, pow_one,
    mul_one] at hw
  exact hw

private theorem reeFixedEmb_relNrepHom
    {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}
    (w : ReeTag.F4.relWeylRee) :
    reeFixedEmb K m (relNrepHom K m w) =
      canonicalRep (coxeterSystem F4.tag) K (w : WeylGroup F4.tag) := by
  letI : CharP K ReeTag.F4.prime := ‹CharP K 2›
  change ((relNrepHom K m w : adjointGroup F4.tag K) : ModGL F4.tag K) = _
  rw [coe_relNrepHom]
  rfl

private theorem szW_eq_three :
    szW = F4.fixedOrbitElement ⟨0, by decide⟩ *
      F4.fixedOrbitElement ⟨1, by decide⟩ *
      F4.fixedOrbitElement ⟨0, by decide⟩ := by
  have e : F4.fixedRelWord ⟨5, by decide⟩ =
      [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨0, by decide⟩] := by decide
  rw [szW, fixedRelElt, e]
  simp [mul_assoc]

private theorem blockGen_mul_blockGen_mul_blockGen_coe :
    ((blockGen 0 * blockGen 1 * blockGen 0 : ReeTag.F4.relWeylRee) : WeylGroup F4.tag) = szW := by
  have e0 : (blockGen 0 : WeylGroup F4.tag) = F4.fixedOrbitElement ⟨0, by decide⟩ := by
    rw [coe_blockGen, blockElt_eq]
    rfl
  have e1 : (blockGen 1 : WeylGroup F4.tag) = F4.fixedOrbitElement ⟨1, by decide⟩ := by
    rw [coe_blockGen, blockElt_eq]
    rfl
  rw [szW_eq_three]
  change ((blockGen 0 : WeylGroup F4.tag) * (blockGen 1 : WeylGroup F4.tag) *
    (blockGen 0 : WeylGroup F4.tag)) = _
  rw [e0, e1]

private theorem reeFixedEmb_reeNa_mul_reeNb_mul_reeNa
    {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ} :
    reeFixedEmb K m (reeNa K m * reeNb K m * reeNa K m) = szNw K := by
  simp only [reeNa, reeNb]
  rw [← map_mul, ← map_mul]
  rw [reeFixedEmb_relNrepHom, szNw, blockGen_mul_blockGen_mul_blockGen_coe]

private theorem commute_rankOneGroupTwo_szSubB_two
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {m : ℕ} :
    ∀ x ∈ rankOneGroupTwo K m, ∀ y ∈ szSubB K m, x * y = y * x := by
  intro x hx y hy
  have h2 : (2 : K) = 0 := by
    have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
    exact CharTwo.two_eq_zero
  exact (commute_of_mem_rootSpan (S := szSetA) (T := szSetB)
    (fun α hα β hβ s t => commute_pinnedX_szRoots_two h2 hα hβ s t)
    (rankOneGroupTwo_le_rootSpan hx) (szSubB_le_rootSpan hy)).eq

theorem reeSz_comm
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] [CharP K 2] [Fintype K] {m : ℕ}
    (hK : Nat.card K = ReeTag.F4.prime ^ (2 * m + 1)) (hm : 1 ≤ m) :
    ∀ x y, reeSz₁ hK hm x * reeSz₂ hK hm y = reeSz₂ hK hm y * reeSz₁ hK hm x := by
  intro x y
  let g := reeNa K m * reeNb K m * reeNa K m
  have hconj : reeSz₂ hK hm y = g * reeSz₁ hK hm y * g⁻¹ := by
    rfl
  have mem_rank : ∀ z, reeFixedEmb K m (reeSz₁ hK hm z) ∈ rankOneGroupTwo K m := by
    intro z
    rw [rankOneGroupTwo_eq_map hK]
    refine Subgroup.mem_map_of_mem (f := reeFixedEmb K m) ?_
    exact ((r2EquivSuzuki K m hK hm).symm
      ((MulAut.conj (CFSG.LieType.Ree.suzukiWElt m K)) z)).2
  have hxmem := mem_rank x
  have hymem1 := mem_rank y
  have hgy : reeFixedEmb K m (reeSz₂ hK hm y) =
      szNw K * reeFixedEmb K m (reeSz₁ hK hm y) * (szNw K)⁻¹ := by
    rw [hconj]
    dsimp only [g]
    rw [map_mul, map_mul, map_inv, reeFixedEmb_reeNa_mul_reeNb_mul_reeNa]
  have hymem : reeFixedEmb K m (reeSz₂ hK hm y) ∈ szSubB K m := by
    rw [hgy]
    simp only [szSubB]
    exact Subgroup.mem_map_of_mem (f := (MulAut.conj (szNw K)).toMonoidHom) hymem1
  have hcommMod := commute_rankOneGroupTwo_szSubB_two
    (reeFixedEmb K m (reeSz₁ hK hm x)) hxmem
    (reeFixedEmb K m (reeSz₂ hK hm y)) hymem
  exact (reeFixedEmb_injective (K := K) (a := m)) hcommMod

end CFSG.StandardType.ReeB2Fixed
