module

public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeTorus
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeAbstract

public section

namespace CFSG.RankThree.PartOne.KCUnitaryModel

open Polynomial Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCUnitaryRegular
  CFSG.RankThree.PartOne.KCPrimary
open scoped commutatorElement

variable {ℓ f n p : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}

variable (h) in
abbrev BlockIdx (x : gramSU h (idGram K n)) : Type :=
  {a : primaryFactors ((toLinU h n (liftUnitary x) : LinearMap.GeneralLinearGroup K
      (Fin n → K)) : Module.End K (Fin n → K)) //
    2 ≤ primaryMultiplicity ((toLinU h n (liftUnitary x) : LinearMap.GeneralLinearGroup K
      (Fin n → K)) : Module.End K (Fin n → K)) (a : K[X])}

variable (h) in
@[expose] noncomputable def idCentralizerD (t : MulAut (primeFormP h (idGram K n))) :
    Subgroup (MulAut (primeFormP h (idGram K n))) :=
  primeFormD h (idGram K n) ⊓ Subgroup.centralizer ({t} : Set (MulAut (primeFormP h (idGram K n))))

variable (h) in
@[expose] noncomputable def idCenterN (t : MulAut (primeFormP h (idGram K n))) :
    Subgroup (MulAut (primeFormP h (idGram K n))) :=
  (Subgroup.center ↥(idCentralizerD h t)).map (idCentralizerD h t).subtype

variable {x : gramSU h (idGram K n)}

theorem mem_idCenterUnits_iff (A : primeFormUnitary h (idGram K n)) :
    A ∈ idCenterUnits h x ↔
      ∃ hz : Matrix.toLin' ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ∈
          commutant (Matrix.toLin' ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)),
        (⟨Matrix.toLin' ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K), hz⟩ :
          commutant (Matrix.toLin' ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) ∈
        Subalgebra.center K
          (commutant (Matrix.toLin' ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) :=
  ⟨fun ⟨_, hz, hc⟩ => ⟨hz, hc⟩, fun ⟨hz, hc⟩ => ⟨toLinU_mem A, hz, hc⟩⟩

theorem LiftData.projSetting (L : LiftData h n p x)
    (B : Subgroup (MulAut (primeFormP h (idGram K n))))
    (hB : (MulAut.conj : primeFormP h (idGram K n) →*
      MulAut (primeFormP h (idGram K n))).range ≤ B) :
    ProjSetting (primeFormConjHom h (idGram K n)) B
      (primeFormConjHom h (idGram K n) (liftUnitary x))
      ((gramSU h (idGram K n)).subgroupOf (primeFormUnitary h (idGram K n)))
      (Subgroup.centralizer ({liftUnitary x} : Set (primeFormUnitary h (idGram K n))))
      (idCenterUnits h x) (fun a : BlockIdx h x => idSpecialBlock h x (a.1 : K[X])) := by
  have hq4 : 4 ≤ ℓ ^ f := L.four_le
  have H := L.primaryData
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro u hu g
    obtain ⟨c, -, hc⟩ := (primeFormConjHom_eq_one_iff L.three_le L.four_le u).mp hu
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hc]
    exact (commute_scalar c (g : GL (Fin n) K)).symm.eq
  · exact primeFormD_normal L.three_le L.four_le
  · rw [map_gramSU_eq_range_conj]
    exact CFSG.ComponentClassification.OuterAutomorphisms.innerNormal _
  · rw [map_gramSU_eq_range_conj]
    exact hB
  · exact L.centralizer_image
  · intro a
    exact idSpecialBlock_le x _
  · intro a A hA
    have h1 := specialBlock_le_sesqSpecialUnitaryGroup H hq4 a.1 hA
    exact (toLin_mem_sesqSpecialUnitaryGroup_iff h (idGram K n) (A : GL (Fin n) K)).mp h1
  · intro a m hm g hg
    rw [mem_idSpecialBlock, map_mul, map_mul, map_inv]
    exact conj_mem_specialBlock ((mem_centralizer_iff_toLinU x m).mp hm) hg
  · intro a
    have hQ := (specialBlockFacts H hq4 a.1).quasisimple a.2
    have hinj := (toLinU_injective (h := h) (n := n))
    let e := (idSpecialBlock h x (a.1 : K[X])).equivMapOfInjective (toLinU h n) hinj
    refine CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (e.trans (MulEquiv.subgroupCongr (map_toLinU_idSpecialBlock x _))).symm hQ
  ·
    have hinj := (toLinU_injective (h := h) (n := n))
    have hXrange : unitaryCentralizer (idForm h n) (toLinU h n (liftUnitary x)) ≤
        (toLinU h n).range := by
      rw [range_toLinU]
      exact fun g hg => hg.1
    have hM : (Subgroup.centralizer ({liftUnitary x} :
        Set (primeFormUnitary h (idGram K n)))).map (toLinU h n) =
          unitaryCentralizer (idForm h n) (toLinU h n (liftUnitary x)) := by
      rw [centralizer_eq_comap_unitaryCentralizer x, Subgroup.map_comap_eq]
      exact inf_of_le_right hXrange
    apply Subgroup.map_injective hinj
    rw [Subgroup.map_commutator, hM, commutator_unitaryCentralizer_eq_iSup_specialBlock H hq4,
      Subgroup.map_iSup]
    refine iSup_congr fun a => ?_
    exact (map_toLinU_idSpecialBlock x _).symm
  · intro A hA
    exact (mem_centralizer_iff_toLinU x A).mpr (centerUnitary_le_unitaryCentralizer hA)
  · intro y hy m hm
    apply toLinU_injective
    rw [map_mul, map_mul]
    exact (commute_of_mem_centerUnitary hy ((mem_centralizer_iff_toLinU x m).mp hm)).eq
  · intro u hu
    obtain ⟨c, -, hc⟩ := (primeFormConjHom_eq_one_iff L.three_le L.four_le u).mp hu
    refine smul_mem_centerUnitary (toLinU_mem u) (c : K) fun v => ?_
    change (Matrix.toLin' ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) v = (c : K) • v
    rw [Matrix.toLin'_apply]
    have : ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        (c : K) • (1 : Matrix (Fin n) (Fin n) K) := by
      rw [hc, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
    rw [this, Matrix.smul_mulVec, Matrix.one_mulVec]
  · intro Y hY hcomm
    have hYX : toLinU h n Y ∈ unitaryCentralizer (idForm h n) (toLinU h n (liftUnitary x)) :=
      (mem_centralizer_iff_toLinU x Y).mp hY
    refine (mem_center_of_commute_specialBlocks H hq4 hYX fun a ha g' hg' => ?_)
    obtain ⟨g, hg⟩ := exists_toLinU (specialBlock_le_unitaryCentralizer hg').1
    subst hg
    have hgF : g ∈ idSpecialBlock h x (a : K[X]) := hg'
    have h1 := hcomm ⟨a, ha⟩ g hgF
    rw [commutatorElement_eq_one_iff_commute] at h1
    have := congrArg (toLinU h n) h1.eq
    rw [map_mul, map_mul] at this
    exact this

end CFSG.RankThree.PartOne.KCUnitaryModel
