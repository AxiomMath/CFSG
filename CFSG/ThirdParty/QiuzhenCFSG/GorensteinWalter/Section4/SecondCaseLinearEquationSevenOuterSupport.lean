module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearEquationSevenPrime
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearEquationSevenCentralizerPrime
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CentralizerSetupOddCoreNormal
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CentralizerSetupFittingNormal
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Section 4, equation (7): the outer-reflection support step

This module isolates the remaining join-support inference after the two
equation-(7) endpoint lemmas.  The source argument needs the cyclic normality
of `K₀` in `H ∩ M`; that fact is therefore an explicit hypothesis here until
the corresponding upstream interface is formalized.
-/

noncomputable section
namespace CFSG.GorensteinWalter
universe u

open scoped commutatorElement Pointwise

private theorem card_sup_dvd_card_mul_of_normal
    {G : Type u} [Group G] [Finite G]
    (A B : Subgroup G) [hA : A.Normal] :
    Nat.card (↥(A ⊔ B)) ∣ Nat.card (↥A) * Nat.card (↥B) := by
  let q : G →* G ⧸ A := QuotientGroup.mk' A
  have hBnorm : B ≤ Subgroup.normalizer (A : Set G) :=
    Subgroup.le_normalizer_of_normal (H := A) (K := B)
  have hset : ((A ⊔ B : Subgroup G) : Set G) =
      (B : Set G) * (A : Set G) := by
    rw [Subgroup.coe_mul_of_right_le_normalizer_left A B hBnorm]
    exact (Subgroup.set_mul_normalizer_comm (S := (B : Set G)) (N := A) hBnorm).symm
  have hcardmul : Nat.card ((B : Set G) * (A : Set G)) =
      Nat.card (↥A) * Nat.card ((B : Set G).image q) :=
    Subgroup.card_mul_eq_card_subgroup_mul_card_quotient (s := A) (t := (B : Set G))
  have hmapdvd : Nat.card ((B : Set G).image q) ∣ Nat.card (↥B) := by
    change Nat.card (B.map q) ∣ Nat.card (↥B)
    exact Subgroup.card_map_dvd (f := q) (H := B)
  calc
    Nat.card (↥(A ⊔ B)) = Nat.card ((A ⊔ B : Subgroup G) : Set G) := rfl
    _ = Nat.card ((B : Set G) * (A : Set G)) := by rw [hset]
    _ = Nat.card (↥A) * Nat.card ((B : Set G).image q) := hcardmul
    _ ∣ Nat.card (↥A) * Nat.card (↥B) := Nat.mul_dvd_mul_left _ hmapdvd

private theorem centralizer_of_sup
    {G : Type u} [Group G]
    {C A B : Subgroup G}
    (hA : C ≤ Subgroup.centralizer (A : Set G))
    (hB : C ≤ Subgroup.centralizer (B : Set G)) :
    C ≤ Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G) := by
  intro c hc
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  rw [Subgroup.sup_eq_closure] at hx
  refine Subgroup.closure_induction'' ?_ ?_ ?_ ?_ hx
  · intro x hx
    rcases hx with hx | hx
    · exact (Subgroup.mem_centralizer_iff.mp (hA hc)) x hx
    · exact (Subgroup.mem_centralizer_iff.mp (hB hc)) x hx
  · intro y hy
    rcases hy with hy | hy
    · have h := (Subgroup.mem_centralizer_iff.mp (hA hc)) y hy
      calc
        y⁻¹ * c = y⁻¹ * (c * y) * y⁻¹ := by group
        _ = y⁻¹ * (y * c) * y⁻¹ := by rw [← h]
        _ = c * y⁻¹ := by group
    · have h := (Subgroup.mem_centralizer_iff.mp (hB hc)) y hy
      calc
        y⁻¹ * c = y⁻¹ * (c * y) * y⁻¹ := by group
        _ = y⁻¹ * (y * c) * y⁻¹ := by rw [← h]
        _ = c * y⁻¹ := by group
  · simp
  · intro x y _ _ hx hy
    calc
      (x * y) * c = x * (y * c) := by group
      _ = x * (c * y) := by rw [hy]
      _ = (x * c) * y := by group
      _ = (c * x) * y := by rw [hx]
      _ = c * (x * y) := by group

private theorem commutator_le_centralizer_of_isNormalIn_isCyclic
    {G : Type u} [Group G] [Finite G]
    {B N : Subgroup G}
    (hNnormal : IsNormalIn N B) (hNcyc : IsCyclic N) :
    ⁅B, B⁆ ≤ Subgroup.centralizer (N : Set G) := by
  let ι : B →* Subgroup.normalizer (N : Set G) :=
    { toFun := fun b => ⟨(b : G),
        le_normalizer_of_isNormalIn hNnormal b.2⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp }
  let φ : B →* MulAut N := N.normalizerMonoidHom.comp ι
  let _ := (hNcyc.mulAutMulEquiv N).toMonoidHom.commGroupOfInjective
    (hNcyc.mulAutMulEquiv N).injective
  rw [Subgroup.commutator_le]
  intro x hx y hy
  let xB : B := ⟨x, hx⟩
  let yB : B := ⟨y, hy⟩
  have hxy : ⁅xB, yB⁆ ∈ ⁅(⊤ : Subgroup B), ⊤⁆ :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top xB) (Subgroup.mem_top yB)
  have hker : ⁅xB, yB⁆ ∈ φ.ker :=
    Abelianization.commutator_subset_ker φ hxy
  have hker' : ι ⁅xB, yB⁆ ∈ N.normalizerMonoidHom.ker := by
    exact hker
  rw [N.normalizerMonoidHom_ker] at hker'
  have hcent : (⁅(x : G), (y : G)⁆ : G) ∈ Subgroup.centralizer (N : Set G) := by
    have hxyval : ((ι ⁅xB, yB⁆ : Subgroup.normalizer (N : Set G)) : G) =
        ⁅(x : G), (y : G)⁆ := by
      simp [ι, xB, yB, commutatorElement_def]
    have hcent' : ((ι ⁅xB, yB⁆ : Subgroup.normalizer (N : Set G)) : G) ∈
        Subgroup.centralizer (N : Set G) := hker'
    rw [hxyval] at hcent'
    exact hcent'
  exact hcent

public theorem secondCase_equationSevenPrime_primeFactors_outerSupport_subset_K0
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (Kinv K0 F B : Subgroup G) (s : d.E) (r : G)
    (hKinv_carrier : (Kinv : Set G) =
      invertedElements (c.U ⊓ w.M) (s : G))
    (hKinv_cyclic : IsCyclic Kinv)
    (hKinv_le_E : Kinv ≤ d.E)
    (hK0_def : K0 = fittingSubgroupOf c.U ⊓ Kinv)
    (hF_eq : F = centralizerIn (fittingSubgroupOf c.U ⊓ w.M) (s : G))
    (hjoin : K0 ⊔ F = fittingSubgroupOf c.U ⊓ w.M)
    (hFcentE : F ≤ Subgroup.centralizer (d.E : Set G))
    (hLayer : ∀ X : Subgroup G, X ≠ ⊥ → X ≤ F →
      componentLayerOf (Subgroup.normalizer (X : Set G)) = d.E)
    (hB_fixed : B = centralizerIn (c.U ⊓ w.M) (s : G))
    (hK0_normal : IsNormalIn K0 (c.H ⊓ w.M))
    (hr_S : r ∈ c.S) (hr_M : r ∈ w.M) :
    ∀ p ∈ (Nat.card (↥(((⁅(Subgroup.zpowers r : Subgroup G), B⁆ : Subgroup G) ⊔
      Kinv) ⊔ c.FU))).primeFactors, p ∣ Nat.card K0 := by
  classical
  let Y : Subgroup G := c.FU ⊓ w.M
  let C : Subgroup G := c.U ⊓ Subgroup.centralizer (Y : Set G)
  let R : Subgroup G := Subgroup.zpowers r
  let D : Subgroup G := ⁅R, B⁆ ⊔ Kinv
  let J : Subgroup G := D ⊔ c.FU
  have hUleH : c.U ≤ c.H := (centralizerSetup_U_isNormalIn_H c).1
  have hRleS : R ≤ c.S := Subgroup.zpowers_le.mpr hr_S
  have hRleH : R ≤ c.H := hRleS.trans (centralizerSetup_S_le_H c)
  have hRleM : R ≤ w.M := Subgroup.zpowers_le.mpr hr_M
  have hB_le_X : B ≤ c.U ⊓ w.M := by
    rw [hB_fixed]
    exact inf_le_left
  have hB_leU : B ≤ c.U := hB_le_X.trans inf_le_left
  have hB_leM : B ≤ w.M := hB_le_X.trans inf_le_right
  have hFU_normalU : IsNormalIn c.FU c.U := by
    exact ⟨fittingSubgroupOf_le c.U, fun u hu x hx =>
      (centralizerSetup_FU_isNormalIn_H c).2 u (hUleH hu) x hx⟩
  have hFnormalM : IsNormalIn F w.M := by
    exact (secondCase_fitting_equation5_7_of_component_centralization
      hmin c w d Kinv K0 F s hKinv_cyclic
      (by rw [hK0_def]; exact inf_le_right) hF_eq hjoin hFcentE hLayer).1
  have hK0leK : K0 ≤ Kinv := by rw [hK0_def]; exact inf_le_right
  have hYeq : Y = K0 ⊔ F := by simpa [Y, CentralizerSetup.FU] using hjoin.symm
  have hKinv_leU : Kinv ≤ c.U := by
    intro x hx
    have hxI : x ∈ invertedElements (c.U ⊓ w.M) (s : G) := by
      rw [← hKinv_carrier]
      exact hx
    exact hxI.1.1
  have hKinv_centK0 : Kinv ≤ Subgroup.centralizer (K0 : Set G) := by
    let : IsCyclic Kinv := hKinv_cyclic
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hxy := (IsCyclic.isMulCommutative (α := Kinv)).is_comm.comm
      ⟨x, hx⟩ ⟨y, hK0leK hy⟩
    exact (congrArg Subtype.val hxy).symm
  have hKinv_centF : Kinv ≤ Subgroup.centralizer (F : Set G) := by
    intro x hx f hf
    exact ((Subgroup.mem_centralizer_iff.mp (hFcentE hf)) (x : G)
      (hKinv_le_E hx)).symm
  have hKinv_centY : Kinv ≤ Subgroup.centralizer (Y : Set G) := by
    rw [hYeq]
    exact centralizer_of_sup hKinv_centK0 hKinv_centF
  have hK0cyc : IsCyclic K0 := by
    let : IsCyclic Kinv := hKinv_cyclic
    exact Subgroup.isCyclic_of_le hK0leK
  have hFcyc : IsCyclic F := by
    exact (secondCase_fitting_equation5_7_of_component_centralization
      hmin c w d Kinv K0 F s hKinv_cyclic
      (by rw [hK0_def]; exact inf_le_right) hF_eq hjoin hFcentE hLayer).2.2.2.2.2.1
  let M0 : Subgroup G := c.H ⊓ w.M
  have hRleM0 : R ≤ M0 := le_inf hRleH hRleM
  have hB_leH : B ≤ c.H := hB_leU.trans hUleH
  have hBleM0 : B ≤ M0 := le_inf hB_leH hB_leM
  have hK0normal_central : ⁅M0, M0⁆ ≤
      Subgroup.centralizer (K0 : Set G) := by
    exact commutator_le_centralizer_of_isNormalIn_isCyclic hK0_normal hK0cyc
  have hFnormal_central : ⁅M0, M0⁆ ≤
      Subgroup.centralizer (F : Set G) := by
    exact commutator_le_centralizer_of_isNormalIn_isCyclic
      (by
        have hFleFU : F ≤ c.FU := by
          rw [hF_eq]
          intro x hx
          exact hx.1.1
        have hFleU : F ≤ c.U := hFleFU.trans (fittingSubgroupOf_le c.U)
        have hFleH : F ≤ c.H := hFleU.trans hUleH
        refine ⟨le_inf hFleH hFnormalM.1, ?_⟩
        intro m hm f hf
        exact hFnormalM.2 m hm.2 f hf)
      hFcyc
  have hRB_centK0 : ⁅R, B⁆ ≤ Subgroup.centralizer (K0 : Set G) := by
    exact (Subgroup.commutator_mono hRleM0 hBleM0).trans hK0normal_central
  have hRB_centF : ⁅R, B⁆ ≤ Subgroup.centralizer (F : Set G) := by
    exact (Subgroup.commutator_mono hRleM0 hBleM0).trans hFnormal_central
  have hRB_centY : ⁅R, B⁆ ≤ Subgroup.centralizer (Y : Set G) := by
    rw [hYeq]
    exact centralizer_of_sup hRB_centK0 hRB_centF
  have hRB_leU : ⁅R, B⁆ ≤ c.U := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have hconj : x * y * x⁻¹ ∈ c.U :=
      (centralizerSetup_U_isNormalIn_H c).2 x (hRleH hx) y (hB_leU hy)
    exact c.U.mul_mem hconj (hB_leU hy |> c.U.inv_mem)
  have hRB_leC : ⁅R, B⁆ ≤ C := le_inf hRB_leU hRB_centY
  have hKinv_leC : Kinv ≤ C := le_inf hKinv_leU hKinv_centY
  have hD_leC : D ≤ C := sup_le hRB_leC hKinv_leC
  have hD_leU : D ≤ c.U := sup_le hRB_leU hKinv_leU
  have hJ_leU : J ≤ c.U := sup_le hD_leU (fittingSubgroupOf_le c.U)
  have hFUleJ : c.FU ≤ J := le_sup_right
  have hFU_normalJ : IsNormalIn c.FU J := by
    refine ⟨hFUleJ, ?_⟩
    intro j hj f hf
    exact hFU_normalU.2 j (hJ_leU hj) f hf
  let FUJ : Subgroup J := c.FU.subgroupOf J
  let DJ : Subgroup J := D.subgroupOf J
  have hFUJnormal : FUJ.Normal := by
    rw [Subgroup.normal_subgroupOf_iff hFUleJ]
    intro f j hf hj
    exact hFU_normalJ.2 (j : G) hj (f : G) hf
  let : FUJ.Normal := hFUJnormal
  have hFUJ_card : Nat.card (↥FUJ) = Nat.card (↥c.FU) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFUleJ).toEquiv
  have hDJ_card : Nat.card (↥DJ) = Nat.card (↥D) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : D ≤ J)).toEquiv
  have hsup_top : FUJ ⊔ DJ = ⊤ := by
    have hsub : (c.FU ⊔ D).subgroupOf J = ⊤ := by
      rw [show c.FU ⊔ D = J by
        dsimp [J]
        rw [sup_comm]]
      exact Subgroup.subgroupOf_self J
    simpa [FUJ, DJ, Subgroup.subgroupOf_sup hFUleJ
      (le_sup_left : D ≤ J)] using hsub
  have hcard_join_dvd : Nat.card (↥J) ∣ Nat.card (↥FUJ) * Nat.card (↥DJ) := by
    have h := card_sup_dvd_card_mul_of_normal FUJ DJ
    simpa [hsup_top] using h
  intro p hp
  change p ∈ (Nat.card (↥J)).primeFactors at hp
  have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpdvdJ : p ∣ Nat.card (↥J) := Nat.dvd_of_mem_primeFactors hp
  have hpdvdprod : p ∣ Nat.card (↥FUJ) * Nat.card (↥DJ) :=
    hpdvdJ.trans hcard_join_dvd
  rcases hpprime.dvd_mul.mp hpdvdprod with hFUJ | hDJ
  · have hpdvdFU : p ∣ Nat.card (↥c.FU) := by
      rw [← hFUJ_card]
      exact hFUJ
    exact secondCase_equationSevenPrime_primeFactors_FU_subset_K0
      hmin c w d Kinv K0 F s hKinv_carrier hKinv_cyclic hK0_def hF_eq
      hjoin hFcentE hLayer hpprime hpdvdFU
  · have hpdvdD : p ∣ Nat.card (↥D) := by
      rw [← hDJ_card]
      exact hDJ
    have hpdvdC : p ∣ Nat.card (↥C) :=
      hpdvdD.trans (Subgroup.card_dvd_of_le hD_leC)
    have hpdvdC' : p ∣ Nat.card (↥(c.U ⊓ Subgroup.centralizer
        ((fittingSubgroupOf c.U ⊓ w.M : Subgroup G) : Set G))) := by
      simpa [C, Y, CentralizerSetup.FU] using hpdvdC
    exact secondCase_equationSevenPrime_primeFactors_centralizerIn_FU_inter_M_subset_K0
      hmin c w d Kinv K0 F s hKinv_carrier hKinv_cyclic hK0_def hF_eq hjoin
      hFcentE hLayer hpprime hpdvdC'

end CFSG.GorensteinWalter
