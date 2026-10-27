module

public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5U3Frame
public import CFSG.GH74.GLS.Stage4.T2NegRU3Conj

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Assembly.LowTwoRank
  CFSG.RankThree.CentralCover CFSG.RankThree.SubgroupLists CFSG.RankThree.Classical
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open scoped Matrix

namespace Lemma41aU3

theorem u37_exists_centralizer_quotient_card {p n : ℕ} {F : Type} [Field F]
    (h : UnitaryFieldData p n F) (hp2 : p ≠ 2)
    {w : StatedProj (StatedSU 3 (p ^ n) F)} (hw : orderOf w = 2) :
    ∃ (N : Subgroup ↥(GU2Stated (p ^ n) F)) (_ : N.Normal),
      Nat.card N = Nat.gcd 3 (p ^ n + 1) ∧
      Nonempty (↥(centralizer ({w} : Set (StatedProj (StatedSU 3 (p ^ n) F)))) ≃*
        (↥(GU2Stated (p ^ n) F) ⧸ N)) := by
  have hw1 : w * w = 1 := by
    have := pow_orderOf_eq_one w
    rwa [hw, sq] at this
  obtain ⟨a, ha, rfl⟩ := linConj_lift_involution (statedProjMk (StatedSU 3 (p ^ n) F))
    (statedProjMk_surjective _) (fun z hz => ker_pow_three h z hz) hw1
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [map_one, orderOf_one] at hw
    omega
  have ha_ord : orderOf a = 2 := orderOf_eq_prime (by rw [sq]; exact ha) ha1
  obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_unitaryInvT_of_orderOf h hp2 ha_ord)
  obtain ⟨N, hN, hcard, hiso⟩ := Lemma41aL3.exists_normal_quotient_equiv
    (statedProjMk (StatedSU 3 (p ^ n) F)) (statedProjMk_surjective _)
    (ker_statedProjMk_le_center _) (fun z hz => ker_pow_three h z hz) ha
    (phi h c) (phi_injective h c) (by rw [phi_range h hp2 c, hc])
  exact ⟨N, hN, by rw [hcard, card_ker h], hiso⟩

end Lemma41aU3

end CFSG.GH74.GLS.IVK.Proofs2

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup Matrix
open CFSG.Open
open CFSG.GH74.GLS.IVK.Proofs2
open CFSG.LocalAnalysis.ComponentInitial

open scoped Matrix

theorem u37_outer_in_gu2 {F : Type} [Field F] [Finite F] (hF : Nat.card F = 49)
    (E₀ : Subgroup ↥(CFSG.Quasithin.StatedGU 2 7 F))
    (hperf : Group.IsPerfect ↥E₀) (hcard : Nat.card ↥E₀ = 336) :
    E₀.Normal ∧ ∃ h₀ : ↥(CFSG.Quasithin.StatedGU 2 7 F),
      ∀ e ∈ E₀, ∃ x ∈ E₀, h₀ * x * h₀⁻¹ ≠ e * x * e⁻¹ := by
  let G : Subgroup (GL (Fin 2) F) := CFSG.Quasithin.StatedGU 2 7 F
  have hdata : UnitaryFieldData 7 1 F := ⟨by norm_num, le_rfl, by rw [hF]; norm_num⟩
  let δ : ↥G →* Fˣ := GeneralLinearGroup.det.comp G.subtype
  let K : Subgroup ↥G := δ.ker
  have hE₀K : E₀ ≤ K := by
    intro x hx
    have hxcomm : (⟨x, hx⟩ : ↥E₀) ∈ commutator ↥E₀ := by
      rw [hperf.commutator_eq_top]
      trivial
    have hker := Abelianization.commutator_subset_ker (δ.comp E₀.subtype) hxcomm
    simpa [K, MonoidHom.mem_ker] using hker
  have hcardG : Nat.card ↥G = 2688 := by
    have h := CFSG.GH74.GLS.IVK.Proofs2.Ivk41RU3.natCard_GU2Stated (q := 7) (F := F)
      (by rw [hF]; norm_num) (by norm_num)
    have hGU : G = CFSG.GH74.GLS.IVK.Proofs2.GU2Stated 7 F := rfl
    rw [hGU]
    simpa using h
  have hker' : Nat.card K * Nat.card δ.range = 2688 := by
    have h := Subgroup.card_ker_mul_card_range δ
    simpa [K, hcardG] using h
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  have hcard_units : Nat.card Fˣ = 48 := by
    rw [Nat.card_units, hF]
  have hg48 : orderOf g = 48 := by rw [hg, hcard_units]
  let a : Fˣ := g ^ 6
  have ha8 : orderOf a = 8 := by
    have hdvd : 6 ∣ orderOf g := by rw [hg48]; norm_num
    rw [orderOf_pow_of_dvd (by norm_num) hdvd, hg48]
  have ha8mul : (a : F) ^ 7 * (a : F) = 1 := by
    have h8 : a ^ 8 = 1 := by rw [← ha8]; exact pow_orderOf_eq_one a
    have h : a ^ 7 * a = 1 := by rw [← pow_succ]; simpa using h8
    simpa using congrArg Units.val h
  let D : GL (Fin 2) F :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero !![(a : F), 0; 0, 1] (by
      rw [Matrix.det_fin_two]
      simp)
  have hDmem : D ∈ G := by
    have hGU : G = CFSG.GH74.GLS.IVK.Proofs2.GU2Stated (7 ^ 1) F := rfl
    rw [hGU]
    rw [CFSG.GH74.GLS.IVK.Proofs2.Lemma41aU3.mem_GU2Stated_iff hdata]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [D, UnitaryFieldData.bar_apply, Matrix.mul_apply, Fin.sum_univ_two, ha8mul]
  have hDdet : GeneralLinearGroup.det D = a := by
    apply Units.ext
    rw [GeneralLinearGroup.val_det_apply]
    simp [D, Matrix.det_fin_two]
  let h₀ : ↥G := ⟨D, hDmem⟩
  have hKcard : Nat.card K ≤ 336 := by
    have hdvd : 8 ∣ Nat.card δ.range := by
      have ha_mem : a ∈ δ.range := ⟨h₀, by simpa [h₀, δ] using hDdet⟩
      have h := Subgroup.orderOf_dvd_natCard δ.range ha_mem
      rwa [ha8] at h
    have hle : Nat.card K * 8 ≤ 2688 := by
      calc Nat.card K * 8 ≤ Nat.card K * Nat.card δ.range :=
            Nat.mul_le_mul_left _ (Nat.le_of_dvd Nat.card_pos hdvd)
        _ = 2688 := hker'
    have hle' : Nat.card K * 8 ≤ 336 * 8 := by simpa using hle
    exact Nat.le_of_mul_le_mul_right hle' (by norm_num)
  have hE₀eq : E₀ = K :=
    Subgroup.eq_of_le_of_card_ge hE₀K (by rw [hcard]; exact hKcard)
  refine ⟨?_, ⟨h₀, ?_⟩⟩
  · rw [hE₀eq]
    infer_instance
  · intro e he
    by_contra hcon
    push Not at hcon
    let u : ↥G := e⁻¹ * h₀
    have hucomm : ∀ B ∈ CFSG.ClassicalInvolution.Q3.TA3.Q5GL2.slPart G,
        (u : GL (Fin 2) F) * (B : GL (Fin 2) F) =
          (B : GL (Fin 2) F) * (u : GL (Fin 2) F) := by
      intro B hB
      have hB' : (B : ↥G) ∈ E₀ := by
        rw [hE₀eq]
        exact hB
      have hh := hcon (B : ↥G) hB'
      have hc : u * B = B * u := by
        calc u * B = e⁻¹ * (h₀ * B * h₀⁻¹) * h₀ := by simp [u]; group
          _ = e⁻¹ * (e * B * e⁻¹) * h₀ := by rw [hh]
          _ = B * u := by simp [u]; group
      simpa using congrArg Subtype.val hc
    obtain ⟨c, hc⟩ :=
      (CFSG.ClassicalInvolution.Q3.TA3.Q5U3.slCentScalar_GU2 hdata) (u : GL (Fin 2) F)
        (fun B hB => hucomm B hB)
    have hdetu : δ u = a := by
      have he1 : δ e = 1 := by
        have : e ∈ K := hE₀eq ▸ he
        simpa [K, MonoidHom.mem_ker] using this
      calc δ u = δ e⁻¹ * δ h₀ := by simp [u, map_mul]
        _ = a := by rw [map_inv, he1, inv_one, one_mul]; simpa [h₀, δ] using hDdet
    have hc2 : c ^ 2 = a := by
      have h := hdetu
      change GeneralLinearGroup.det (u : GL (Fin 2) F) = a at h
      rw [hc, GeneralLinearGroup.det_scalar, Fintype.card_fin] at h
      simpa using h
    have hc8 : c ^ 8 = 1 := by
      have hmem : GeneralLinearGroup.scalar (Fin 2) c ∈
          CFSG.GH74.GLS.IVK.Proofs2.GU2Stated (7 ^ 1) F := by
        rw [← hc]
        exact u.2
      have hcond := (CFSG.GH74.GLS.IVK.Proofs2.Lemma41aU3.mem_GU2Stated_iff hdata).1 hmem
      have h00 := congrFun (congrFun hcond 0) 0
      simp [GeneralLinearGroup.coe_scalar, UnitaryFieldData.bar_apply,
        Matrix.mul_apply, Fin.sum_univ_two] at h00
      apply Units.ext
      have : (c : F) ^ 8 = 1 := by
        calc (c : F) ^ 8 = (c : F) ^ 7 * (c : F) := by ring
          _ = 1 := h00
      simpa using this
    have ha4 : a ^ 4 = 1 := by
      rw [← hc2, ← pow_mul]
      simpa using hc8
    have hdvd : orderOf a ∣ 4 := by
      rw [orderOf_dvd_iff_pow_eq_one]
      exact ha4
    rw [ha8] at hdvd
    norm_num at hdvd

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
