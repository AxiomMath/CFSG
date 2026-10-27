module

public import CFSG.RankThree.PartTwo.Sec12.Hering129CFam6
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityAB
import CFSG.RankThree.PartTwo.Sec12.Hering129D4HTwo
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec19 (C0 Asub Bsub D4Par finite_C0 Asub_inf_Bsub)

namespace Hering129C


section Model

variable {X : Type} [Field X] [Finite X] {σ : X ≃+* X}

theorem false_of_perfect_centralizer_A (Ppar : D4Par 1 X σ) {y : C0 σ} (hyA : y ∈ Asub σ)
    (hy3 : orderOf y = 3) {P : Subgroup (C0 σ)} (hPC : P ≤ Subgroup.centralizer ({y} : Set (C0 σ)))
    (hPp : Group.IsPerfect ↥P) (hyP : y ∈ P) : False := by
  have hy31 : y ^ 3 = 1 := by rw [← hy3]; exact pow_orderOf_eq_one y
  have hy1 : y ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hy3
    omega
  haveI := Hering129D4H.d4ThreeACent_two_solvable X σ (by simpa using Ppar.card)
    (fun c => by simpa using Ppar.frob c) hyA hy31 hy1
  haveI : Group.IsSolvable ↥P :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hPC)
      (Subgroup.inclusion_injective hPC)
  haveI := hPp
  haveI : Nontrivial ↥P := ⟨⟨⟨y, hyP⟩, 1, fun h => hy1 (congrArg Subtype.val h)⟩⟩
  exact Group.IsPerfect.not_isSolvable ↥P ‹_›

theorem false_of_perfect_centralizer_B (Ppar : D4Par 1 X σ) {y : C0 σ} (hyB : y ∈ Bsub σ)
    (hy3 : orderOf y = 3) {P : Subgroup (C0 σ)} (hPC : P ≤ Subgroup.centralizer ({y} : Set (C0 σ)))
    (hPp : Group.IsPerfect ↥P) (hyP : y ∈ P) : False := by
  have hy1 : y ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hy3
    omega
  have hres := Hering129D4H.d4_resCent_threeB' Ppar hyB hy3
  have hPA : P ≤ Asub σ := by
    rw [← hres]
    exact le_inSubgroup_perfectResidual_of_isPerfect
      (X := (⊤ : Subgroup (C0 σ)) ⊓ Subgroup.centralizer ({y} : Set (C0 σ)))
      (le_inf le_top hPC) hPp
  have hbot : y ∈ Asub σ ⊓ Bsub σ := ⟨hPA hyP, hyB⟩
  rw [Asub_inf_Bsub Ppar, Subgroup.mem_bot] at hbot
  exact hy1 hbot

theorem false_of_perfect_centralizer_model (Ppar : D4Par 1 X σ) {y : C0 σ} (hy3 : orderOf y = 3)
    {P : Subgroup (C0 σ)} (hPC : P ≤ Subgroup.centralizer ({y} : Set (C0 σ)))
    (hPp : Group.IsPerfect ↥P) (hyP : y ∈ P) : False := by
  haveI : Finite (C0 σ) := finite_C0 (σ := σ)
  haveI := Ppar.charP
  have hy31 : y ^ 3 = 1 := by rw [← hy3]; exact pow_orderOf_eq_one y
  have hy1 : y ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hy3
    omega
  have h3 : ¬ 3 ∣ 2 ^ 1 := by norm_num
  obtain ⟨g, hg⟩ := Sec11.KS11Lie6Proof.d4ThreeConj_holds X (2 ^ 1) σ Ppar.card Ppar.frob h3 y
    hy31 hy1
  let cg : C0 σ ≃* C0 σ := MulAut.conj g
  have hy1o : orderOf (g * y * g⁻¹) = 3 := by rw [orderOf_conj_eq]; exact hy3
  have hXg : P.map cg.toMonoidHom ≤ Subgroup.centralizer ({g * y * g⁻¹} : Set (C0 σ)) := by
    rw [Hering129L.centralizer_conj_eq_map]
    exact Subgroup.map_mono hPC
  have hperf : Group.IsPerfect (P.map cg.toMonoidHom) := by
    haveI := hPp
    exact Group.IsPerfect.ofSurjective
      (f := (P.equivMapOfInjective cg.toMonoidHom cg.injective).toMonoidHom)
      (P.equivMapOfInjective cg.toMonoidHom cg.injective).surjective
  have hyg : g * y * g⁻¹ ∈ P.map cg.toMonoidHom := ⟨y, hyP, rfl⟩
  rcases hg with hA | hB
  · exact false_of_perfect_centralizer_A Ppar hA hy1o hXg hperf hyg
  · exact false_of_perfect_centralizer_B Ppar hB hy1o hXg hperf hyg

end Model

theorem kFCensus46SixD42_holds : KFCensus46SixD42 := by
  intro Q Lb _ _ _ c a I X f hQ hD
  exfalso
  obtain ⟨r, hrc, -, hG⟩ := isG2D4_of_chevalley_D4 hQ
  rcases hG with ⟨h31, -⟩ | ⟨-, hr, ⟨eQ⟩⟩
  · omega
  obtain ⟨K, _, _, σ, hK, hσ, ⟨eK⟩⟩ := Hering129KModels.exists_d4_model eQ
  have hr2 : r.card = 2 := by rw [hrc]; norm_num
  have Ppar : D4Par 1 K σ :=
    ⟨le_rfl, by rw [hK, hr2]; norm_num, fun c => by rw [hσ c, hr2]; norm_num⟩
  haveI : Finite (C0 σ) := finite_C0 (σ := σ)
  have hy3 : orderOf (eK c) = 3 := by rw [MulEquiv.orderOf_eq]; exact hD.orderOf_c
  have hPC : I.map eK.toMonoidHom ≤ Subgroup.centralizer ({eK c} : Set (C0 σ)) := by
    rw [Hering129L.centralizer_map_equiv_eq eK c]
    exact Subgroup.map_mono hD.le_centralizer
  have hPp : Group.IsPerfect (I.map eK.toMonoidHom) := by
    haveI := hD.isPerfect
    exact Group.IsPerfect.ofSurjective
      (f := (I.equivMapOfInjective eK.toMonoidHom eK.injective).toMonoidHom)
      (I.equivMapOfInjective eK.toMonoidHom eK.injective).surjective
  exact false_of_perfect_centralizer_model Ppar hy3 hPC hPp ⟨c, hD.c_mem, rfl⟩

end Hering129C

end CFSG.RankThree.PartTwo.Sec12
