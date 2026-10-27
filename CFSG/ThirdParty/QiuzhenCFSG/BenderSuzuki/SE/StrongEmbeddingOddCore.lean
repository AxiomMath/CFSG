module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.StrongEmbedding
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Compat
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.proposition_1_16
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj

namespace CFSG
end CFSG
open CFSG

/-!
# Odd-core control from a four-group in a strongly embedded subgroup

This module isolates the coprime-action core of Lemma 3.13.  It is placed
upstream of both Theorem 4 and Corollary 7.13 so those arguments can share the
same checked containment theorem.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open scoped IsMulCommutative

open PFAppendixIII PFchapter1section1

universe u

public theorem isMulCommutative_of_forall_sq_one
    {A : Type*} [Group A] (hA : ∀ x : A, x ^ 2 = 1) :
    IsMulCommutative A := by
  refine IsMulCommutative.mk <| Std.Commutative.mk ?_
  intro a b
  have hinv : ∀ x : A, x⁻¹ = x := by
    intro x
    have hx : x * x = 1 := by
      simpa [pow_two] using hA x
    calc
      x⁻¹ = x⁻¹ * 1 := by simp
      _ = x⁻¹ * (x * x) := by rw [hx]
      _ = x := by simp
  calc
    a * b = (a * b)⁻¹ := (hinv (a * b)).symm
    _ = b⁻¹ * a⁻¹ := by simp
    _ = b * a := by rw [hinv a, hinv b]

public theorem noncyclic_of_card_four_and_sq_one
    {A : Type*} [Group A] [Finite A]
    (hcard : Nat.card A = 4) (hsq : ∀ x : A, x ^ 2 = 1) :
    ¬ IsCyclic A := by
  intro hcyc
  rcases (isCyclic_iff_exists_orderOf_eq_natCard (α := A)).mp hcyc with
    ⟨a, ha⟩
  have horder_dvd : orderOf a ∣ 2 :=
    orderOf_dvd_iff_pow_eq_one.mpr (hsq a)
  rw [hcard] at ha
  rw [ha] at horder_dvd
  norm_num at horder_dvd

/-- A four-group in a strongly embedded subgroup controls every normalized
odd-order subgroup.  This is the coprime-action core used in Lemma 3.13. -/
public theorem fourGroup_odd_subgroup_le_stronglyEmbedded
    {X : Type*} [Group X] [Finite X]
    {M U W : Subgroup X}
    (hM : IsStronglyEmbedded M)
    (hUM : U ≤ M)
    (hUcard : Nat.card U = 4)
    (hUsq : ∀ u : U, u ^ 2 = 1)
    (hUnormW : U ≤ Subgroup.normalizer W)
    (hWodd : Odd (Nat.card W)) :
    W ≤ M := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : IsMulCommutative U := isMulCommutative_of_forall_sq_one hUsq
  letI : CommGroup U := IsMulCommutative.instCommGroup
  haveI : Fact (IsPGroup 2 U) := by
    refine ⟨IsPGroup.of_card (p := 2) (G := U) (n := 2) ?_⟩
    norm_num [hUcard]
  haveI : Subgroup.Normalizes U W := ⟨hUnormW⟩
  have hUnoncyclic : ¬ IsCyclic U :=
    noncyclic_of_card_four_and_sq_one hUcard hUsq
  have hWcop : Nat.Coprime 2 (Nat.card W) :=
    (Nat.prime_two.coprime_iff_not_dvd).2 hWodd.not_two_dvd_nat
  have hgen :
      (⨆ (u : U) (_ : u ≠ 1),
        fixedPointSubgroup (↥(Subgroup.zpowers u)) W) = ⊤ := by
    exact proposition_1_16_a (G := W) (A := U) 2 hWcop hUnoncyclic
  have hfixed_map_le :
      ∀ u : U, ∀ hu_ne : u ≠ 1,
        (fixedPointSubgroup (↥(Subgroup.zpowers u)) W).map W.subtype ≤ M := by
    intro u hu_ne
    have huX_ne : (u : X) ≠ 1 := by
      intro huX
      exact hu_ne (Subtype.ext huX)
    have hu_sq : (u : X) ^ 2 = 1 := by
      simpa using congrArg Subtype.val (hUsq u)
    have hu_inv : IsInvolution (u : X) := ⟨huX_ne, hu_sq⟩
    have hfix_eq :
        fixedPointSubgroup (↥(Subgroup.zpowers u)) W =
          (elementCentralizerIn W (u : X)).subgroupOf W := by
      simpa using
        fixedPointSubgroup_zpowers_subgroup_conj_eq_elementCentralizerIn
          W U hUnormW u
    have hfix_map :
        (fixedPointSubgroup (↥(Subgroup.zpowers u)) W).map W.subtype =
          elementCentralizerIn W (u : X) := by
      calc
        (fixedPointSubgroup (↥(Subgroup.zpowers u)) W).map W.subtype =
            ((elementCentralizerIn W (u : X)).subgroupOf W).map W.subtype := by
              rw [hfix_eq]
        _ = elementCentralizerIn W (u : X) ⊓ W := by
              rw [Subgroup.subgroupOf_map_subtype]
        _ = elementCentralizerIn W (u : X) := inf_eq_left.2 inf_le_left
    calc
      (fixedPointSubgroup (↥(Subgroup.zpowers u)) W).map W.subtype =
          elementCentralizerIn W (u : X) := hfix_map
      _ ≤ Subgroup.centralizer ({(u : X)} : Set X) := inf_le_right
      _ ≤ M := hM.centralizer_le (hUM u.property) hu_inv
  have htop_map_W : (⊤ : Subgroup W).map W.subtype = W := by
    simpa [MonoidHom.range_eq_map] using (Subgroup.range_subtype (H := W))
  calc
    W = (⊤ : Subgroup W).map W.subtype := htop_map_W.symm
    _ =
        (⨆ (u : U) (_ : u ≠ 1),
          fixedPointSubgroup (↥(Subgroup.zpowers u)) W).map W.subtype := by
          simp [hgen]
    _ ≤ M := by
      rw [Subgroup.map_iSup]
      refine iSup_le ?_
      intro u
      rw [Subgroup.map_iSup]
      refine iSup_le ?_
      intro hu_ne
      exact hfixed_map_le u hu_ne

/-- Generic Lemma 3.13 form: a four-group in the intersection with `L`
forces the odd core of `L` into the ambient strongly embedded subgroup. -/
public theorem oddCore_map_le_stronglyEmbedded_of_twoRank_intersection
    {X : Type u} [Group X] [Finite X]
    (M L : Subgroup X)
    (hM : IsStronglyEmbedded M)
    (hrank : TwoRankAtLeastTwo (M.comap L.subtype)) :
    (twoPrimeCore L).map L.subtype ≤ M := by
  let H : Subgroup L := M.comap L.subtype
  let W : Subgroup X := (twoPrimeCore L).map L.subtype
  obtain ⟨E, hEcard, hEsq⟩ := TwoRankAtLeastTwo.exists_subgroup hrank
  let i : H →* X := L.subtype.comp H.subtype
  let U : Subgroup X := E.map i
  have hi : Function.Injective i := by
    intro a b hab
    exact Subtype.ext (Subtype.ext hab)
  have hUM : U ≤ M := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨e, _heE, rfl⟩
    exact e.property
  have hUcard : Nat.card U = 4 := by
    rw [show Nat.card U = Nat.card E from
      Subgroup.card_map_of_injective hi]
    exact hEcard
  have hUsq : ∀ u : U, u ^ 2 = 1 := by
    intro u
    apply Subtype.ext
    change (u : X) ^ 2 = 1
    rcases Subgroup.mem_map.mp u.property with ⟨e, heE, heu⟩
    let eE : E := ⟨e, heE⟩
    have he2 : (e : H) ^ 2 = 1 := by
      convert congrArg Subtype.val (hEsq eE) using 1 <;> rfl
    calc
      (u : X) ^ 2 = (i e) ^ 2 := by rw [heu]
      _ = 1 := by simpa using congrArg i he2
  have hWL : W ≤ L := by
    intro x hx
    rcases hx with ⟨w, _hw, rfl⟩
    exact w.property
  have hWsub : W.subgroupOf L = twoPrimeCore L := by
    change W.comap L.subtype = twoPrimeCore L
    dsimp [W]
    exact Subgroup.comap_map_eq_self_of_injective
      Subtype.val_injective (twoPrimeCore L)
  have hWnormalL : (W.subgroupOf L).Normal := by
    rw [hWsub]
    infer_instance
  have hLnormW : L ≤ Subgroup.normalizer W :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWL).mp hWnormalL
  have hUL : U ≤ L := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨e, _heE, rfl⟩
    exact (e : L).property
  have hUnormW : U ≤ Subgroup.normalizer W := hUL.trans hLnormW
  have hWodd : Odd (Nat.card W) := by
    have hcard : Nat.card W = Nat.card (twoPrimeCore L) :=
      Subgroup.card_map_of_injective Subtype.val_injective
    rw [hcard]
    exact Nat.coprime_two_left.mp (by
      simpa [twoPrimeCore] using
        (pPrimeCore_coprime_card (p := 2) (G := L)))
  exact fourGroup_odd_subgroup_le_stronglyEmbedded
    hM hUM hUcard hUsq hUnormW hWodd

end CFSG.BenderSuzuki
