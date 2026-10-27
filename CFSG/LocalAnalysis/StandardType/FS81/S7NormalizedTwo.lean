module

public import CFSG.LocalAnalysis.StandardType.FS81.S7ModelCent
import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortGlueTwo
import CFSG.LocalAnalysis.StandardType.GGFrameRouteOrder
import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoFusionE8
import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210gAux
import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210a

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.SeitzReduction


variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem eq_bot_of_isPGroup_two_of_le_centralizer_card_eight (hK : Nat.card K = 2)
    {E P : Subgroup (adjointGroup .E8 K)} (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 8) (hP : IsPGroup 2 P)
    (hPC : P ≤ Subgroup.centralizer (E : Set (adjointGroup .E8 K))) : P = ⊥ := by
  classical
  obtain ⟨c, hc⟩ := TableBExcTwoTB.exists_conj_frame_of_card_E8 hK hE hcard.ge
  let T : Subgroup (adjointGroup .E8 K) :=
    (TableBExcTwoTB.tE K TableBExcTwo.frameE8).range
  let φ : MulAut (adjointGroup .E8 K) := MulAut.conj c⁻¹
  have hET : E.map φ.toMonoidHom = T := by
    rw [hc, Subgroup.map_map]
    have hcomp : φ.toMonoidHom.comp (MulAut.conj c).toMonoidHom =
        MonoidHom.id (adjointGroup .E8 K) := by
      ext x
      simp [φ, MulAut.conj_apply, mul_assoc]
    rw [hcomp, Subgroup.map_id]
  have hPT : P.map φ.toMonoidHom ≤ T := by
    have h := (Subgroup.map_mono hPC).trans
      (Subgroup.map_centralizer_le_centralizer_image (E : Set (adjointGroup .E8 K))
        φ.toMonoidHom)
    have hset : φ '' (E : Set (adjointGroup .E8 K)) = (T : Set (adjointGroup .E8 K)) := by
      change ((E.map φ.toMonoidHom : Subgroup (adjointGroup .E8 K)) :
        Set (adjointGroup .E8 K)) = _
      rw [hET]
    change P.map φ.toMonoidHom ≤ Subgroup.centralizer (φ '' (E : Set (adjointGroup .E8 K))) at h
    rw [hset, show Subgroup.centralizer (T : Set (adjointGroup .E8 K)) = T from
      centralizer_tE_frameE8 hK] at h
    exact h
  have hT3 : IsPGroup 3 T := hET ▸ (hE.map φ.toMonoidHom).isPGroup
  have hdis : Disjoint (P.map φ.toMonoidHom) T :=
    IsPGroup.disjoint_of_coprime (hP.map φ.toMonoidHom) hT3 (by norm_num)
  have hbot : P.map φ.toMonoidHom = ⊥ := by
    have h := disjoint_iff.mp hdis
    rwa [inf_of_le_left hPT] at h
  apply le_bot_iff.mp
  intro x hx
  have hmem : φ x ∈ P.map φ.toMonoidHom := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact Subgroup.mem_bot.mpr (φ.injective (by simpa using hmem))

theorem eq_bot_of_isPGroup_two_of_le_centralizer_nonsplit (hK : Nat.card K = 2)
    {S E P : Subgroup (adjointGroup .E8 K)}
    (hSJ : S ≤ (EPilot.highRootSL2 .E8 K).subgroupOf (adjointGroup .E8 K))
    (hcyc : IsCyclic S) (hS : Nat.card S = Nat.card K + 1)
    (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 8)
    (hEC : E ≤ Subgroup.centralizer (S : Set (adjointGroup .E8 K)))
    (hP : IsPGroup 2 P)
    (hPC : P ≤ Subgroup.centralizer (S : Set (adjointGroup .E8 K)))
    (hEP : E ≤ Subgroup.normalizer (P : Set (adjointGroup .E8 K))) : P = ⊥ := by
  have hdesc : E6Pilot.PerpLeviFrobDescent .E8 K := E8Pilot.perpLeviFrobDescent_E8
  obtain ⟨hC, -, hSD⟩ := E6Pilot.centralizer_nonsplit_of_descent
    (Or.inr (Or.inr rfl)) hdesc hSJ hcyc hS
  have hSN : S ≤ Subgroup.normalizer
      (EPilot.perpLevi .E8 K : Set (adjointGroup .E8 K)) :=
    hSD.trans (Subgroup.centralizer_le_normalizer _)
  have hPN : P ≤ Subgroup.normalizer
      (EPilot.perpLevi .E8 K : Set (adjointGroup .E8 K)) :=
    hPC.trans (hC.le.trans
      (sup_le hSN Subgroup.le_normalizer))
  let e₇ : EPilot.perpLevi .E8 K ≃* adjointGroup .E7 K := E8Pilot.e7LeviEquiv K
  have hcard₇ := card_inf_perpLevi_of_nonsplit_card_eight hK hSJ hcyc hS hEC hE hcard
  have hPD : P ≤ Subgroup.centralizer
      (EPilot.perpLevi .E8 K : Set (adjointGroup .E8 K)) :=
    le_centralizer_of_E7Two_torus hK e₇ inf_le_right (hE.mono inf_le_left)
      hcard₇.ge hP hPN (inf_le_left.trans hEP)
  have hSP : S ≤ Subgroup.centralizer (P : Set (adjointGroup .E8 K)) :=
    Subgroup.le_centralizer_iff.mp hPC
  have hPE : P ≤ Subgroup.centralizer (E : Set (adjointGroup .E8 K)) := by
    apply Subgroup.le_centralizer_iff.mpr
    exact hEC.trans (hC.le.trans
      (sup_le hSP (Subgroup.le_centralizer_iff.mp hPD)))
  exact eq_bot_of_isPGroup_two_of_le_centralizer_card_eight hK hE hcard hP hPE

theorem eq_bot_of_isPGroup_two_of_normalized_card_eight (hK : Nat.card K = 2)
    {E P : Subgroup (adjointGroup .E8 K)} (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 8) (hP : IsPGroup 2 P)
    (hEP : E ≤ Subgroup.normalizer (P : Set (adjointGroup .E8 K))) : P = ⊥ := by
  classical
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hPne
  have hcop : Nat.Coprime 3 (Nat.card P) := by
    obtain ⟨n, hn⟩ := isPGroup_iff_card_dvd_pow.mp hP
    exact Nat.Coprime.of_dvd_right hn (Nat.Coprime.pow_right n (by norm_num))
  obtain ⟨F, hF, hFU⟩ :=
    CFSG.SignalizerFunctorTheorem.McBride.Near.Thm210g.exists_hyperplane_not_le
      Nat.prime_three hE (by rw [hcard]; norm_num) hEP hcop
      (fun h => hPne (le_bot_iff.mp h))
  have hFE : F ≤ E := hF.1
  have hFcard : Nat.card F = 3 ^ 7 := by
    have h := hF.2
    rw [hcard] at h
    norm_num at h ⊢
    omega
  have hECF : E ≤ Subgroup.centralizer (F : Set (adjointGroup .E8 K)) := by
    intro x hx
    exact Subgroup.mem_centralizer_iff.mpr fun f hf => hE.comm (hFE hf) hx
  let U : Subgroup (adjointGroup .E8 K) :=
    P ⊓ Subgroup.centralizer (F : Set (adjointGroup .E8 K))
  have hEU : E ≤ Subgroup.normalizer (U : Set (adjointGroup .E8 K)) :=
    (le_inf hEP (hECF.trans Subgroup.le_normalizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  obtain ⟨t, ht, ht1, g, hgt⟩ := TableBExcTwoFusion.exists_conj_mem_highRootSL2_E8
    hK (hE.mono hFE) hFcard.ge
  let φ : MulAut (adjointGroup .E8 K) := MulAut.conj g
  let S : Subgroup (adjointGroup .E8 K) := Subgroup.zpowers (φ t)
  have hSJ : S ≤ (EPilot.highRootSL2 .E8 K).subgroupOf (adjointGroup .E8 K) := by
    rw [Subgroup.zpowers_le]
    exact hgt
  have ht3 : t ^ 3 = 1 := hE.2 t (hFE ht)
  have hφt3 : (φ t) ^ 3 = 1 := by rw [← map_pow, ht3, map_one]
  have hφt1 : φ t ≠ 1 := fun h => ht1 (φ.injective (by simpa using h))
  have horder : orderOf (φ t) = 3 := orderOf_eq_prime_iff.mpr ⟨hφt3, hφt1⟩
  have hScard : Nat.card S = Nat.card K + 1 := by
    rw [Nat.card_zpowers, horder, hK]
  have hSF : S ≤ F.map φ.toMonoidHom :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_map.mpr ⟨t, ht, rfl⟩)
  have hEC : E.map φ.toMonoidHom ≤
      Subgroup.centralizer (S : Set (adjointGroup .E8 K)) := by
    have h : E.map φ.toMonoidHom ≤ Subgroup.centralizer
        (F.map φ.toMonoidHom : Set (adjointGroup .E8 K)) :=
      (Subgroup.map_mono hECF).trans
        (Subgroup.map_centralizer_le_centralizer_image
          (F : Set (adjointGroup .E8 K)) φ.toMonoidHom)
    exact h.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hSF))
  have hUC : U.map φ.toMonoidHom ≤
      Subgroup.centralizer (S : Set (adjointGroup .E8 K)) := by
    have h : U.map φ.toMonoidHom ≤ Subgroup.centralizer
        (F.map φ.toMonoidHom : Set (adjointGroup .E8 K)) :=
      (Subgroup.map_mono (show U ≤ Subgroup.centralizer
        (F : Set (adjointGroup .E8 K)) from inf_le_right)).trans
          (Subgroup.map_centralizer_le_centralizer_image
            (F : Set (adjointGroup .E8 K)) φ.toMonoidHom)
    exact h.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hSF))
  have hEUN : E.map φ.toMonoidHom ≤ Subgroup.normalizer
      (U.map φ.toMonoidHom : Set (adjointGroup .E8 K)) := by
    rw [← Subgroup.map_equiv_normalizer_eq U φ]
    exact Subgroup.map_mono hEU
  have hUbot : U.map φ.toMonoidHom = ⊥ :=
    eq_bot_of_isPGroup_two_of_le_centralizer_nonsplit hK hSJ (Subgroup.isCyclic_zpowers _)
      hScard (hE.map φ.toMonoidHom)
      (by rw [Subgroup.card_map_of_injective φ.injective, hcard]) hEC
      ((IsPGroup.to_inf_left hP).map φ.toMonoidHom) hUC hEUN
  apply hFU
  intro u hu
  have hmem : φ u ∈ U.map φ.toMonoidHom := Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
  rw [hUbot, Subgroup.mem_bot] at hmem
  exact Subgroup.mem_bot.mpr (φ.injective (by simpa using hmem))

end CFSG.StandardType.FrameRoute.FS81
