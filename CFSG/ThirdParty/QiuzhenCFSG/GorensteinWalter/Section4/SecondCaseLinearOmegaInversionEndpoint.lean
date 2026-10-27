module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearOmegaInversionNormal
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearOmegaInvertedElements
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CentralizerSetupOddCoreNormal
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section1

namespace CFSG
end CFSG
open CFSG

/-! # The inversion endpoint of the linear omega argument -/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- The `s`-fixed elements of `U` lie in `M`.  For `b ∈ U` fixed by `s`,
conjugation by `b` preserves the `s`-fixed part `F = C_{F(U)}(s)` of
`F(U)` (both `b` and `F` are normalized by `F(U)`-conjugation and by
`s`), hence `b ∈ N_G(F) = M`.  This is the equation-(5) identity
`B = C_U(s)` in disguise. -/
private lemma fixed_U_le_M
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (od : SecondCaseLinearOmegaData c w d)
    (hF_full : od.F = centralizerIn c.FU (od.s : G)) :
    ∀ b : G, b ∈ c.U → (od.s : G) * b * (od.s : G)⁻¹ = b → b ∈ w.M := by
  intro b hbU hbfix
  have hUleH : c.U ≤ c.H := (centralizerSetup_U_isNormalIn_H c).1
  have hFleFU : od.F ≤ c.FU := by
    intro x hx
    rw [hF_full] at hx
    exact hx.1
  have hsInv_b : (od.s : G) * b⁻¹ * (od.s : G)⁻¹ = b⁻¹ := by
    calc
      (od.s : G) * b⁻¹ * (od.s : G)⁻¹ =
          ((od.s : G) * b * (od.s : G)⁻¹)⁻¹ := by group
      _ = b⁻¹ := by rw [hbfix]
  have hsx (x : G) (hxF : x ∈ od.F) :
      (od.s : G) * x * (od.s : G)⁻¹ = x := by
    rw [hF_full] at hxF
    have hxcent : x ∈ Subgroup.centralizer ({(od.s : G)} : Set G) := hxF.2
    have hxcomm : x * (od.s : G) = (od.s : G) * x :=
      (Subgroup.mem_centralizer_iff.mp hxcent (od.s : G) (by simp)).symm
    calc
      (od.s : G) * x * (od.s : G)⁻¹ = x * (od.s : G) * (od.s : G)⁻¹ := by
        rw [hxcomm]
      _ = x := by simp
  have hfixedNormF (y : G) (hyU : y ∈ c.U)
      (hyfix : (od.s : G) * y * (od.s : G)⁻¹ = y) :
      ∀ x : G, x ∈ od.F → y * x * y⁻¹ ∈ od.F := by
    intro x hxF
    have hxFU : x ∈ c.FU := hFleFU hxF
    have hyxFU : y * x * y⁻¹ ∈ c.FU :=
      (centralizerSetup_FU_isNormalIn_H c).2 y (hUleH hyU) x hxFU
    have hsInv_y : (od.s : G) * y⁻¹ * (od.s : G)⁻¹ = y⁻¹ := by
      calc
        (od.s : G) * y⁻¹ * (od.s : G)⁻¹ =
            ((od.s : G) * y * (od.s : G)⁻¹)⁻¹ := by group
        _ = y⁻¹ := by rw [hyfix]
    have hyxfix : (od.s : G) * (y * x * y⁻¹) * (od.s : G)⁻¹ =
        y * x * y⁻¹ := by
      calc
        (od.s : G) * (y * x * y⁻¹) * (od.s : G)⁻¹ =
            ((od.s : G) * y * (od.s : G)⁻¹) *
              ((od.s : G) * x * (od.s : G)⁻¹) *
                ((od.s : G) * y⁻¹ * (od.s : G)⁻¹) := by group
        _ = y * x * y⁻¹ := by rw [hyfix, hsx x hxF, hsInv_y]
    rw [hF_full]
    refine ⟨hyxFU, ?_⟩
    change y * x * y⁻¹ ∈ Subgroup.centralizer ({(od.s : G)} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hmul := congrArg (fun z : G => z * (od.s : G)) hyxfix
    have hcomm : (od.s : G) * (y * x * y⁻¹) =
        (y * x * y⁻¹) * (od.s : G) := by
      simpa [mul_assoc] using hmul
    exact hcomm.symm
  have hbNormF : b ∈ Subgroup.normalizer (od.F : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact hfixedNormF b hbU hbfix x
    · intro hbxF
      have hbInvU : b⁻¹ ∈ c.U := c.U.inv_mem hbU
      have hpre : b⁻¹ * (b * x * b⁻¹) * (b⁻¹)⁻¹ ∈ od.F :=
        hfixedNormF b⁻¹ hbInvU hsInv_b (b * x * b⁻¹) hbxF
      have heq : b⁻¹ * (b * x * b⁻¹) * (b⁻¹)⁻¹ = x := by group
      rwa [heq] at hpre
  rw [od.F_normalizer] at hbNormF
  exact hbNormF

public theorem secondCase_linear_omega_inversion_endpoint
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (od : SecondCaseLinearOmegaData c w d)
    (hF_full : od.F = centralizerIn c.FU (od.s : G))
    (hinvQ : ∀ x : G, x ∈ od.Q.map c.U.subtype →
      (od.s : G) * x * (od.s : G)⁻¹ = x⁻¹) :
    (od.B ⊔ od.K ⊔ c.FU).relIndex c.U ≤ od.p ∧
      (¬ (∃ I : Subgroup G, (I : Set G) = invertedElements c.U (od.s : G) ∧
          IsNormalIn I c.Hhat) →
        (normalizerIn c.U od.A).relIndex c.U ≤ od.p ∧
          IsNormalIn od.A c.FU) := by
  classical
  let s : G := od.s
  have hsI : IsInvolution s := od.s_involution
  have hUodd : Odd (Nat.card c.U) := by
    change Odd (Nat.card (oddCoreOf c.H))
    exact odd_card_oddCoreOf c.H
  have hcopU : Nat.Coprime 2 (Nat.card c.U) :=
    Nat.coprime_two_left.mpr hUodd
  have hsU : ∀ x : G, x ∈ c.U → s * x * s⁻¹ ∈ c.U :=
    (centralizerSetup_U_isNormalIn_H c).2 s od.s_mem_H
  have hCUs_le_M : ∀ x : G, x ∈ c.U → s * x * s⁻¹ = x → x ∈ w.M :=
    fixed_U_le_M c w d od hF_full
  have hB_CU : od.B = centralizerIn c.U (od.s : G) := by
    apply le_antisymm
    · intro b hb
      rw [od.B_fixed] at hb
      exact ⟨hb.1.1, hb.2⟩
    · intro b hb
      rw [od.B_fixed]
      exact ⟨⟨hb.1, hCUs_le_M b hb.1
        (by
          have hbcent : b ∈ Subgroup.centralizer
              ({(od.s : G)} : Set G) := hb.2
          have hbcomm : b * (od.s : G) = (od.s : G) * b :=
            (Subgroup.mem_centralizer_iff.mp hbcent (od.s : G) (by simp)).symm
          calc
            (od.s : G) * b * (od.s : G)⁻¹ =
                b * (od.s : G) * (od.s : G)⁻¹ := by rw [hbcomm]
            _ = b := by simp)⟩, hb.2⟩
  obtain ⟨I, _hIdef, hIeq, _hInormalU, hIleFU⟩ :=
    secondCase_linear_omega_invertedElements_le_fitting c w d od hF_full hinvQ
  have hInvLeFU : ∀ x : G, x ∈ invertedElements c.U s → x ∈ c.FU := by
    intro x hx
    apply hIleFU
    change x ∈ (I : Set G)
    rw [hIeq]
    simpa [s] using hx
  have hUeq : c.U = od.B ⊔ c.FU := by
    apply le_antisymm
    · intro x hxU
      obtain ⟨b, hb, i, hi, hxi⟩ :=
        fact_1_5_ii_decomposition (X := c.U) hsI hcopU hsU x hxU
      have hbB : b ∈ od.B := by
        rw [hB_CU]
        simpa [s] using hb
      rw [hxi]
      exact (od.B ⊔ c.FU).mul_mem
        (Subgroup.mem_sup_left hbB)
        (Subgroup.mem_sup_right (hInvLeFU i hi))
    · exact sup_le
        (by
          rw [hB_CU]
          exact inf_le_left)
        (fittingSubgroupOf_le c.U)
  have hrel : (od.B ⊔ od.K ⊔ c.FU).relIndex c.U ≤ od.p := by
    have hBK : od.B ⊔ od.K ≤ c.U := by
      rw [sup_comm, od.U_inter_M_eq]
      exact inf_le_left
    have hsq : od.B ⊔ od.K ⊔ c.FU = c.U := by
      apply le_antisymm
      · exact sup_le hBK (fittingSubgroupOf_le c.U)
      · intro x hx
        have hxBFU : x ∈ od.B ⊔ c.FU := by
          rw [← hUeq]
          exact hx
        have hBleBK : od.B ≤ od.B ⊔ od.K := le_sup_left
        have hBKle : od.B ⊔ od.K ≤ (od.B ⊔ od.K) ⊔ c.FU := le_sup_left
        have hFUle : c.FU ≤ (od.B ⊔ od.K) ⊔ c.FU := le_sup_right
        exact (sup_le (hBleBK.trans hBKle) hFUle) hxBFU
    rw [hsq, Subgroup.relIndex_self]
    exact od.hp_prime.one_le
  refine ⟨hrel, ?_⟩
  intro hnot
  exfalso
  obtain ⟨I, hIeq', hInormal⟩ :=
    secondCase_linear_omega_invertedElements_normal_Hhat
      hmin c w d od hF_full hinvQ
  exact hnot ⟨I, hIeq', hInormal⟩

end CFSG.GorensteinWalter
