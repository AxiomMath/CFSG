module

public import CFSG.RankThree.PartOne.KC.UnitaryGoodModel
public import CFSG.RankThree.PartOne.KC.UnitaryGoodAbstract
public import CFSG.RankThree.PartOne.KC.UnitaryGoodSpecial

public section

namespace CFSG.RankThree.PartOne.KCUnitaryModel

open Polynomial Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCUnitaryRegular
  CFSG.RankThree.PartOne.KCPrimary
open scoped commutatorElement

variable {ℓ f n p : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}

variable (h) in
abbrev GoodBlockIdx (x : gramSU h (idGram K n)) : Type :=
  {a : primaryFactors ((toLinU h n (liftUnitary x) : LinearMap.GeneralLinearGroup K
      (Fin n → K)) : Module.End K (Fin n → K)) //
    IsGoodBlock h (toLinU h n (liftUnitary x)) a}

@[expose] noncomputable def idInnCentralizer (h : UnitaryFieldData ℓ f K) (n : ℕ)
    (t : MulAut (primeFormP h (idGram K n))) : Subgroup (MulAut (primeFormP h (idGram K n))) :=
  (MulAut.conj : primeFormP h (idGram K n) →* MulAut (primeFormP h (idGram K n))).range ⊓
    Subgroup.centralizer ({t} : Set (MulAut (primeFormP h (idGram K n))))

@[expose] noncomputable def idLocalCore (h : UnitaryFieldData ℓ f K) (n p : ℕ)
    (B : Subgroup (MulAut (primeFormP h (idGram K n))))
    (t : MulAut (primeFormP h (idGram K n))) : Subgroup (MulAut (primeFormP h (idGram K n))) :=
  CFSG.inSubgroup (CFSG.RankThree.LocalRank.aschbacherSolvableCore p)
    (B ⊓ Subgroup.centralizer ({t} : Set (MulAut (primeFormP h (idGram K n)))))

variable (h) in
@[expose] noncomputable def idGoodProduct (x : gramSU h (idGram K n)) :
    Subgroup (MulAut (primeFormP h (idGram K n))) :=
  ⨆ i : GoodBlockIdx h x, idBlockImage h x (i.1 : K[X])

theorem mem_idSpecialBlock_iff {x : gramSU h (idGram K n)} {a : K[X]}
    {Y : primeFormUnitary h (idGram K n)} :
    Y ∈ idSpecialBlock h x a ↔
      (toLinU h n Y ∈ unitaryCentralizer (idForm h n) (toLinU h n (liftUnitary x)) ∧
        ∀ b ∈ primaryFactors ((toLinU h n (liftUnitary x) : LinearMap.GeneralLinearGroup K
          (Fin n → K)) : Module.End K (Fin n → K)), b ∉ ({a, dualPoly h.bar a} : Set K[X]) →
          ∀ v ∈ primaryComponent ((toLinU h n (liftUnitary x) : LinearMap.GeneralLinearGroup K
            (Fin n → K)) : Module.End K (Fin n → K)) b,
            ((toLinU h n Y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
              Module.End K (Fin n → K)) v = v) ∧
      ∃ hg : toLinU h n Y ∈ gl_centralizer (toLinU h n (liftUnitary x)),
        blockDetHom (toLinU h n (liftUnitary x)) a ⟨toLinU h n Y, hg⟩ = 1 :=
  mem_specialBlock

theorem two_le_pow_of (h : UnitaryFieldData ℓ f K) : 2 ≤ ℓ ^ f := by
  have h1 : 1 < ℓ ^ f := Nat.one_lt_pow (by have := h.one_le; omega) h.prime.one_lt
  omega

namespace PlaneData

variable {x : gramSU h (idGram K n)} (L : PlaneData h n p x)

include L in
theorem goodSetting (B : Subgroup (MulAut (primeFormP h (idGram K n))))
    (hB : (MulAut.conj : primeFormP h (idGram K n) →*
      MulAut (primeFormP h (idGram K n))).range ≤ B) :
    GoodSetting (primeFormConjHom h (idGram K n)) B
      (primeFormConjHom h (idGram K n) (liftUnitary x))
      ((gramSU h (idGram K n)).subgroupOf (primeFormUnitary h (idGram K n)))
      (Subgroup.centralizer ({liftUnitary x} : Set (primeFormUnitary h (idGram K n))))
      (fun a : GoodBlockIdx h x => idSpecialBlock h x (a.1 : K[X])) := by
  have hq2 := two_le_pow_of h
  have H := L.primaryData
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u hu g
    exact commute_of_mem_ker_of_ne L.three_le L.ne hu g
  · rw [map_gramSU_eq_range_conj]
    exact CFSG.ComponentClassification.OuterAutomorphisms.innerNormal _
  · rw [map_gramSU_eq_range_conj]
    exact hB
  · exact L.centralizer_image_SU
  · intro a
    exact idSpecialBlock_le x _
  · intro a A hA
    have h1 := specialBlock_le_sesqSpecialUnitaryGroup_of_good H hq2 a.1 a.2 hA
    exact (toLin_mem_sesqSpecialUnitaryGroup_iff h (idGram K n) (A : GL (Fin n) K)).mp h1
  · intro a m hm g hg
    rw [mem_idSpecialBlock, map_mul, map_mul, map_inv]
    exact conj_mem_specialBlock ((mem_centralizer_iff_toLinU x m).mp hm.1) hg
  · intro a
    have hQ := (specialBlockFacts_of_good H hq2 a.1 a.2).quasisimple a.2.1
    have hinj := (toLinU_injective (h := h) (n := n))
    let e := (idSpecialBlock h x (a.1 : K[X])).equivMapOfInjective (toLinU h n) hinj
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (e.trans (MulEquiv.subgroupCongr (map_toLinU_idSpecialBlock x _))).symm hQ

end PlaneData

end CFSG.RankThree.PartOne.KCUnitaryModel
