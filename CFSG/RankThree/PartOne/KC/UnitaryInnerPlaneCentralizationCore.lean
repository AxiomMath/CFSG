module

public import CFSG.RankThree.PartOne.KC.UnitaryGoodSetting
public import CFSG.RankThree.PartOne.KC.UnitaryInnerPlaneLift

public section

namespace CFSG.RankThree.PartOne

open Polynomial Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCUnitaryPlane CFSG.RankThree.PartOne.KCPrimary
open scoped commutatorElement

theorem unitary_inner_plane_local_core_centralization {ℓ f n p : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2)) (hp : p.Prime)
    (hp3 : 3 < p) (hpℓ : p ≠ ℓ)
    (hZp : ∀ c : Kˣ, h.norm (c : K) = 1 → c ^ n = 1 → c ^ p = 1 → c = 1)
    (B : Subgroup (MulAut (primeFormP h (idGram K n))))
    (hB : (MulAut.conj : primeFormP h (idGram K n) →*
      MulAut (primeFormP h (idGram K n))).range ≤ B)
    (A : Subgroup (MulAut (primeFormP h (idGram K n))))
    (Ahat : Subgroup (gramSU h (idGram K n))) (hAhat : IsPlaneLift h n p A Ahat)
    (a : MulAut (primeFormP h (idGram K n))) (haA : a ∈ A)
    (x : gramSU h (idGram K n)) (hxA : x ∈ Ahat) (hxa : innerLift h n x = a)
    (hxp : orderOf x = p) :
    (∀ i : GoodBlockIdx h x,
      (idSpecialBlock h x (i.1 : K[X]) ≤
          (gramSU h (idGram K n)).subgroupOf (primeFormUnitary h (idGram K n)) ∧
        Group.IsPerfect (idSpecialBlock h x (i.1 : K[X])) ∧
        ∀ y ∈ Subgroup.centralizer ({liftUnitary x} : Set (primeFormUnitary h (idGram K n))) ⊓
            (gramSU h (idGram K n)).subgroupOf (primeFormUnitary h (idGram K n)),
          ∀ g ∈ idSpecialBlock h x (i.1 : K[X]), y * g * y⁻¹ ∈ idSpecialBlock h x (i.1 : K[X])) ∧
      (idBlockImage h x (i.1 : K[X]) ≤ (MulAut.conj : primeFormP h (idGram K n) →*
            MulAut (primeFormP h (idGram K n))).range ∧
        CFSG.IsComponent ((idBlockImage h x (i.1 : K[X])).subgroupOf
          (B ⊓ Subgroup.centralizer ({a} : Set (MulAut (primeFormP h (idGram K n)))))) ∧
        ((idBlockImage h x (i.1 : K[X])).subgroupOf (idInnCentralizer h n a)).Normal ∧
        ∀ s ∈ idLocalCore h n p B a, ∀ j ∈ idBlockImage h x (i.1 : K[X]), s * j = j * s)) ∧
    ((idGoodProduct h x).subgroupOf (idInnCentralizer h n a)).Normal ∧
    ⁅idLocalCore h n p B a, A⁆ = ⊥ ∧
    (∀ Y ∈ Subgroup.centralizer ({liftUnitary x} : Set (primeFormUnitary h (idGram K n))) ⊓
        (gramSU h (idGram K n)).subgroupOf (primeFormUnitary h (idGram K n)),
      (primeFormConjHom h (idGram K n) Y ∈
          Subgroup.centralizer
            ((idGoodProduct h x : Subgroup (MulAut (primeFormP h (idGram K n)))) :
              Set (MulAut (primeFormP h (idGram K n)))) ↔
        ∀ i : GoodBlockIdx h x, ∃ c : AdjoinRoot (i.1 : K[X]),
          ∀ v : primaryComponent ((toLinU h n (liftUnitary x) : LinearMap.GeneralLinearGroup K
              (Fin n → K)) : Module.End K (Fin n → K)) (i.1 : K[X]),
            ((toLinU h n Y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
              Module.End K (Fin n → K)) (v : Fin n → K) =
              ((c • v : primaryComponent ((toLinU h n (liftUnitary x) :
                LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K))
                  (i.1 : K[X])) : Fin n → K))) ∧
    (∀ y ∈ idInnCentralizer h n a, (∀ j ∈ idGoodProduct h x, y * j = j * y) →
      ∀ b ∈ A, b * y = y * b) ∧
    (∀ i : primaryFactors ((toLinU h n (liftUnitary x) : LinearMap.GeneralLinearGroup K
        (Fin n → K)) : Module.End K (Fin n → K)),
      dualPoly h.bar (i : K[X]) = i →
      (primaryMultiplicity ((toLinU h n (liftUnitary x) : LinearMap.GeneralLinearGroup K
          (Fin n → K)) : Module.End K (Fin n → K)) (i : K[X]) = 2 →
        ℓ ^ (f * (i : K[X]).natDegree) = 2 →
        Nat.card (supportedUnitary (idForm h n) (toLinU h n (liftUnitary x)) {(i : K[X])}) = 18) ∧
      (primaryMultiplicity ((toLinU h n (liftUnitary x) : LinearMap.GeneralLinearGroup K
          (Fin n → K)) : Module.End K (Fin n → K)) (i : K[X]) = 2 →
        ℓ ^ (f * (i : K[X]).natDegree) = 3 →
        Nat.card (supportedUnitary (idForm h n) (toLinU h n (liftUnitary x)) {(i : K[X])}) = 96) ∧
      (primaryMultiplicity ((toLinU h n (liftUnitary x) : LinearMap.GeneralLinearGroup K
          (Fin n → K)) : Module.End K (Fin n → K)) (i : K[X]) = 3 →
        ℓ ^ (f * (i : K[X]).natDegree) = 2 →
        Nat.card (supportedUnitary (idForm h n) (toLinU h n (liftUnitary x)) {(i : K[X])}) =
          648)) := by
  classical
  have hxp' : x ^ p = 1 := by
    rw [← hxp]
    exact pow_orderOf_eq_one x
  have L : PlaneData h n p x := ⟨hn, hne, hp, hpℓ, hZp, hxp'⟩
  have hq2 := two_le_pow_of h
  have H := L.primaryData
  have hfin : Finite (primeFormP h (idGram K n)) := finite_primeFormP
  have hat : a = primeFormConjHom h (idGram K n) (liftUnitary x) := by
    rw [← hxa, innerLift_apply, primeFormConjHom_liftUnitary]
  subst hat
  have GS := L.goodSetting B hB
  have hH : ((gramSU h (idGram K n)).subgroupOf (primeFormUnitary h (idGram K n))).map
      (primeFormConjHom h (idGram K n)) = (MulAut.conj : primeFormP h (idGram K n) →*
        MulAut (primeFormP h (idGram K n))).range := map_gramSU_eq_range_conj
  obtain ⟨hAel, -, hAmap, -⟩ := hAhat
  have hAlift : ∀ b ∈ A, ∃ b' ∈ Ahat, innerLift h n b' = b := by
    intro b hb
    have : b ∈ Ahat.map (innerLift h n) := hAmap ▸ hb
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp this
    exact ⟨b', hb', rfl⟩
  have hAcomm' : ∀ b ∈ Ahat, ∀ b' ∈ Ahat, b * b' = b' * b := by
    intro b hb b' hb'
    have := hAel
    exact congrArg Subtype.val
      ((IsMulCommutative.is_comm (M := ↥Ahat)).comm ⟨b, hb⟩ ⟨b', hb'⟩)
  have hApow' : ∀ b ∈ Ahat, b ^ p = 1 := by
    intro b hb
    have := hAel
    exact elemPow_eq_one_of_isElementaryAbelian b hb
  have hAH : A ≤ (MulAut.conj : primeFormP h (idGram K n) →*
      MulAut (primeFormP h (idGram K n))).range := by
    intro b hb
    obtain ⟨b', -, rfl⟩ := hAlift b hb
    exact ⟨(b' : primeFormP h (idGram K n)), (innerLift_apply b').symm⟩
  have hAcomm : ∀ b ∈ A, ∀ b' ∈ A, b * b' = b' * b := by
    intro b hb b' hb'
    obtain ⟨c, hc, rfl⟩ := hAlift b hb
    obtain ⟨c', hc', rfl⟩ := hAlift b' hb'
    rw [← map_mul, ← map_mul, hAcomm' c hc c' hc']
  have hApow : ∀ b ∈ A, b ^ p = 1 := by
    intro b hb
    obtain ⟨c, hc, rfl⟩ := hAlift b hb
    rw [← map_pow, hApow' c hc, map_one]
  have hÂ : ∀ b ∈ Ahat, toLinU h n (liftUnitary b) ∈
      unitaryCentralizer (idForm h n) (toLinU h n (liftUnitary x)) ∧
      (toLinU h n (liftUnitary b)) ^ p = 1 := by
    intro b hb
    refine ⟨?_, ?_⟩
    · rw [← mem_centralizer_iff_toLinU x (liftUnitary b)]
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      exact Subtype.ext (congrArg (fun z : gramSU h (idGram K n) => (z : GL (Fin n) K))
        (hAcomm' b hb x hxA))
    · rw [← map_pow]
      have : (liftUnitary b) ^ p = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow]
        exact congrArg Subtype.val (hApow' b hb))
      rw [this, map_one]
  have hcomm_iff : ∀ Y g : primeFormUnitary h (idGram K n),
      Commute (toLinU h n Y) (toLinU h n g) ↔ Commute Y g := by
    intro Y g
    constructor
    · intro hc
      apply toLinU_injective
      rw [map_mul, map_mul]
      exact hc.eq
    · intro hc
      exact hc.map (toLinU h n)
  have hC : idInnCentralizer h n (primeFormConjHom h (idGram K n) (liftUnitary x)) =
      ((gramSU h (idGram K n)).subgroupOf (primeFormUnitary h (idGram K n))).map
        (primeFormConjHom h (idGram K n)) ⊓
      Subgroup.centralizer ({primeFormConjHom h (idGram K n) (liftUnitary x)} :
        Set (MulAut (primeFormP h (idGram K n)))) := by
    unfold idInnCentralizer
    rw [hH]
  have hscal : ∀ Y ∈ Subgroup.centralizer ({liftUnitary x} :
        Set (primeFormUnitary h (idGram K n))),
      (∀ i : GoodBlockIdx h x, ∀ g ∈ idSpecialBlock h x (i.1 : K[X]), Commute Y g) →
      ∀ i : GoodBlockIdx h x, ∃ c : AdjoinRoot (i.1 : K[X]),
        ∀ v : primaryComponent ((toLinU h n (liftUnitary x) : LinearMap.GeneralLinearGroup K
            (Fin n → K)) : Module.End K (Fin n → K)) (i.1 : K[X]),
          ((toLinU h n Y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
            Module.End K (Fin n → K)) (v : Fin n → K) =
            ((c • v : primaryComponent ((toLinU h n (liftUnitary x) :
              LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K))
                (i.1 : K[X])) : Fin n → K) := by
    intro Y hY hF i
    have hYu := (mem_centralizer_iff_toLinU x Y).mp hY
    refine (commute_specialBlock_iff_scalar H hq2 i.1 i.2 hYu).mp (fun g hg => ?_)
    obtain ⟨g₀, rfl⟩ := exists_toLinU (specialBlock_le_unitaryCentralizer hg).1
    exact (hcomm_iff Y g₀).mpr (hF i g₀ hg)
  have hAJ : ∀ y ∈ (MulAut.conj : primeFormP h (idGram K n) →*
        MulAut (primeFormP h (idGram K n))).range ⊓
        Subgroup.centralizer ({primeFormConjHom h (idGram K n) (liftUnitary x)} :
          Set (MulAut (primeFormP h (idGram K n)))),
      (∀ j ∈ idGoodProduct h x, Commute y j) → ∀ b ∈ A, Commute b y := by
    intro y hy hyJ b hb
    have hy' : y ∈ (Subgroup.centralizer ({liftUnitary x} :
        Set (primeFormUnitary h (idGram K n))) ⊓
        (gramSU h (idGram K n)).subgroupOf (primeFormUnitary h (idGram K n))).map
          (primeFormConjHom h (idGram K n)) := by
      rw [← GS.C_eq, hH]
      exact hy
    obtain ⟨Y, hYmem, rfl⟩ := hy'
    have hYJ : primeFormConjHom h (idGram K n) Y ∈ Subgroup.centralizer
        ((idGoodProduct h x : Subgroup (MulAut (primeFormP h (idGram K n)))) :
          Set (MulAut (primeFormP h (idGram K n)))) :=
      Subgroup.mem_centralizer_iff.mpr fun j hj => (hyJ j hj).symm.eq
    have hFcomm := GS.mem_centralizer_iff.mp hYJ
    have hscalY := hscal Y hYmem.1 (fun i g hg => hFcomm i g hg)
    have hYu := (mem_centralizer_iff_toLinU x Y).mp hYmem.1
    obtain ⟨b', hb', rfl⟩ := hAlift b hb
    obtain ⟨hb'u, hb'p⟩ := hÂ b' hb'
    have h3 := commute_of_scalar_on_good H hp hp3 hYu hb'u hb'p
      (fun i hi => hscalY ⟨i, hi⟩)
    have h4 : Commute Y (liftUnitary b') := (hcomm_iff Y (liftUnitary b')).mp h3
    rw [innerLift_apply, ← primeFormConjHom_liftUnitary]
    exact (h4.map (primeFormConjHom h (idGram K n))).symm
  refine ⟨fun i => ⟨⟨GS.F_le_Hs i, (GS.F_quasi i).1,
      fun y hy g hg => GS.F_normal i y hy g hg⟩, ⟨?_, GS.isComponent_image i, ?_, ?_⟩⟩, ?_, ?_, ?_,
    ?_, ?_⟩
  · rw [← hH]
    exact GS.map_le_H i
  · rw [hC]
    exact GS.image_normal_C i
  · intro s hs j hj
    exact (GS.core_centralizes hp hs (Subgroup.mem_iSup_of_mem i hj)).symm.eq
  · rw [hC]
    exact GS.iSup_image_normal
  · exact commutator_core_plane hp B (MulAut.conj : primeFormP h (idGram K n) →*
      MulAut (primeFormP h (idGram K n))).range (idGoodProduct h x) A
      (by rw [← hH]; exact GS.H_normal) hB hAH haA hAcomm hApow
      (fun s hs j hj => (GS.core_centralizes hp hs hj).symm) hAJ
  · intro Y hY
    refine GS.mem_centralizer_iff.trans ?_
    constructor
    · intro hF i
      exact hscal Y hY.1 hF i
    · intro hs i g hg
      have hYu := (mem_centralizer_iff_toLinU x Y).mp hY.1
      have h1 := (commute_specialBlock_iff_scalar H hq2 i.1 i.2 hYu).mpr (hs i)
      exact (hcomm_iff Y g).mp (h1 (toLinU h n g) hg)
  · intro y hy hyJ b hb
    exact hAJ y hy hyJ b hb
  · intro i hself
    obtain ⟨h1, h2, h3⟩ := card_orbitFactor_exceptional H i hself
    rw [orbitFactor_eq_supportedUnitary_of_selfDual hself] at h1 h2 h3
    exact ⟨h1, h2, h3⟩

end CFSG.RankThree.PartOne
