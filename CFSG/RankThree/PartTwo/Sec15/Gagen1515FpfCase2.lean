module

public import CFSG.RankThree.PartTwo.Sec15.Gagen1515FpfCtx
public import CFSG.RankThree.PartTwo.Sec14.Item148Steps
public import CFSG.RankThree.PartTwo.Sec17.RouteForms
import CFSG.RankThree.PartTwo.Sec15.Gagen1515FpfTypes
import CFSG.RankThree.PartTwo.Sec15.Gagen1515FpfImg
import CFSG.RankThree.PartTwo.Sec15.Gagen1515FpfRed
import CFSG.RankThree.PartTwo.Sec15.Gagen1515FpfDec
import CFSG.RankThree.PartTwo.Sec15.Gagen1515FpfA6Lift
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofLB
import CFSG.RankThree.PartTwo.Sec15.Item15Res11ProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec15.Gagen1515Fpf

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {A L : Subgroup G} {c d : G}

theorem not_case2
    (h134 : Item134) (h48 : Sec4.Item4_8) (h142 : Item142R)
    (h : Ctx A c L d) {g : G} (hgA : g ∈ Subgroup.normalizer (A : Set G))
    (hgX : g ∈ Subgroup.centralizer (x₀ L d : Set G)) (hgc : g * c * g⁻¹ = c * d)
    {T T₀ : Subgroup G} (hTX : T ≤ x₀ L d) (hT : T ≠ ⊥) (hTT₀ : T ≤ T₀)
    (hT₀2 : IsPGroup 2 ↥T₀) (hgT₀ : g ∈ Subgroup.normalizer (T₀ : Set G))
    (hY : Subgroup.normalizer (T₀ : Set G) ∈ scriptY A) :
    letI := ker148_normal hY.2
    ¬ Case148Two A (lB A) (Subgroup.normalizer (T₀ : Set G)) := by
  intro h2
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Y : Subgroup G := Subgroup.normalizer (T₀ : Set G) with hYdef
  set H : Subgroup G := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hHdef
  set V : Subgroup G := pPrimeCoreOf 3 H with hVdef
  set Dc : Subgroup G := deltaZero A (lB A) (Y ⊓ H) with hDcdef
  set F : Subgroup G :=
    inSubgroup perfectResidual (Dc ⊓ Subgroup.centralizer ({d} : Set G)) with hFdef
  set U : Subgroup G := T₀ ⊓ (x₀ L d ⊔ V) with hUdef
  have hgY : g ∈ Subgroup.normalizer (Y : Set G) := Subgroup.le_normalizer hgT₀
  obtain ⟨c', hc', hX', hF1, hF2⟩ := case2_type h134 h48 h hY h2
  have hX := case2_reduce h134 h48 h hgA hgX hgc hgY hc' hX'
  have hcA : c ∈ A := (zpowers_mem_omegaA_iff.mp h.sec13Data.zpowers_mem_omegaA).1
  have hc3 : orderOf c = 3 := by
    have hc3' := (zpowers_mem_omegaA_iff.mp h.sec13Data.zpowers_mem_omegaA).2.1
    rwa [Nat.card_zpowers] at hc3'
  have hd3 : orderOf d = 3 := orderOf_eq_prime (h.isE27.1.2 d h.mem_d) h.ne_d
  have hcd : Commute c d := by
    have hle : A ≤ Subgroup.centralizer (A : Set G) :=
      Subgroup.le_centralizer_iff_isMulCommutative.mpr h.isE27.1.1
    exact (Subgroup.mem_centralizer_iff.mp (hle hcA) d h.mem_d).symm
  have hO := pPrimeCoreOf_deltaZero_le (A := A) hY hF1
  have hd := commutator_zpowers_le (A := A) hY hcA hc3 hgA hgY hgc hO hX
  have h3F : 3 ∣ Nat.card ↥F :=
    three_dvd_card_residual (A := A) hY h.mem_d hd3 hcd hO hX hd hF2
  have hF_Dc : F ≤ Dc :=
    (Subgroup.map_subtype_le
      (perfectResidual ↥(Dc ⊓ Subgroup.centralizer ({d} : Set G)))).trans inf_le_left
  have hF_Cd : F ≤ Subgroup.centralizer ({d} : Set G) :=
    (Subgroup.map_subtype_le
      (perfectResidual ↥(Dc ⊓ Subgroup.centralizer ({d} : Set G)))).trans inf_le_right
  have hDc_le : Dc ≤ L ⊔ V :=
    (deltaZero_mono (inf_le_right : Y ⊓ H ≤ H)).trans (deltaZero_normalizer_le h142 h)
  have hF_XV : F ≤ x₀ L d ⊔ V :=
    (le_inf (hF_Dc.trans hDc_le) hF_Cd).trans (sup_inf_centralizer_le h)
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    le_centralizer_of_mem_thetaComponentsAt (lA_subset A c h.sec13Data.mem_lA)
  have hCH : Subgroup.centralizer ({c} : Set G) ≤ H := by
    have h := Subgroup.centralizer_le_normalizer (Subgroup.zpowers c : Set G)
    have hC : Subgroup.centralizer ({c} : Set G) =
        Subgroup.centralizer (Subgroup.zpowers c : Set G) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    rw [← hC] at h
    exact h
  have hX₀H : x₀ L d ≤ H :=
    ((Subgroup.map_subtype_le
        (perfectResidual ↥(L ⊓ Subgroup.centralizer ({d} : Set G)))).trans inf_le_left).trans
      (hLc.trans hCH)
  have hX₀N : x₀ L d ≤ Subgroup.normalizer (V : Set G) :=
    hX₀H.trans (le_normalizer_pPrimeCoreOf 3 H)
  obtain ⟨-, hX₀triple, hq, hZ3, -, -, -⟩ := h.residual_facts
  have hX₀V1 : x₀ L d ⊓ V = ⊥ :=
    Proof15Res11.inf_pPrimeCoreOf_eq_bot hX₀H hq hZ3
  have hF_perf : Group.IsPerfect ↥F := Item148HJ.residual_isPerfect Dc d
  have hU2 : IsPGroup 2 ↥U := hT₀2.to_le inf_le_left
  have hUX : U ≤ x₀ L d ⊔ V := inf_le_right
  have hTU : T ≤ U := le_inf hTT₀ (hTX.trans le_sup_left)
  have hFN : F ≤ Subgroup.normalizer (U : Set G) := by
    have hFT₀ : F ≤ Subgroup.normalizer (T₀ : Set G) :=
      hF_Dc.trans ((deltaZero_le (Y ⊓ H)).trans inf_le_left)
    have hFXV : F ≤ Subgroup.normalizer ((x₀ L d ⊔ V : Subgroup G) : Set G) :=
      hF_XV.trans Subgroup.le_normalizer
    exact (le_inf hFT₀ hFXV).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hFV : F ≤ V :=
    le_of_isPerfect_le_normalizer (X₀ := x₀ L d) (V := V) (F := F) (U := U) (T := T)
      hX₀triple hX₀N hX₀V1 hF_perf hF_XV hU2 hUX hFN hTX hTU hT
  have hnot3 : ¬ 3 ∣ Nat.card ↥F := by
    intro h3
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (coprime_card_pPrimeCoreOf 3 H) (h3.trans (Subgroup.card_dvd_of_le hFV))
  exact hnot3 h3F

end Ctx

end CFSG.RankThree.PartTwo.Sec15.Gagen1515Fpf
