module

public import CFSG.RankThree.PartTwo.Sec6.Item65One
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
import CFSG.RankThree.PartTwo.Source.MinimalFaithfulCentralProduct
import CFSG.LocalAnalysis.SignalizerFunctor.AmbientCommutators

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Ctx65

variable {A L B E : Subgroup G} {a₀ : G} (h : Ctx65 G A L B E a₀)
include h

theorem false_of_R_Y_of_local (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h49 : Sec4.Item4_9)
    {Z' R Y : Subgroup G}
    (hZ' : Z' ∈ thetaComponentsIn (Subgroup.centralizer (B : Set G)))
    (hZ'K : ∀ a ∈ B, a ≠ 1 → ∀ K ∈ thetaComponentsAt 3 a,
      inSubgroup perfectResidual ((L ⊓ Subgroup.centralizer {a}) ⊔
        inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer {a})) ≤ K → Z' ≤ K)
    (hloc : ∀ a ∈ B, a ≠ 1 → ∀ K ∈ thetaComponentsAt 3 a,
      inSubgroup perfectResidual ((L ⊓ Subgroup.centralizer {a}) ⊔
        inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer {a})) ≤ K →
      ⁅inSubgroup (aschbacherSolvableCore 3) Z', Z'⁆ ≤ inSubgroup (aschbacherSolvableCore 3) K)
    (hR1 : R ≠ ⊥) (hR2 : IsPGroup 2 R) (hER : E ≤ Subgroup.normalizer (R : Set G))
    (hYp : Group.IsPerfect Y) (hY1 : Y ≠ ⊥) (hYZ' : Y ≤ Z')
    (hZ'Y : Z' ≤ Y ⊔ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer (B : Set G)))
    (hYR : Y ≤ Subgroup.centralizer (R : Set G)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set CB := Subgroup.centralizer (B : Set G) with hCB
  set T := inSubgroup (aschbacherSolvableCore 3) CB with hT
  set NR := Subgroup.normalizer (R : Set G) with hNR
  set W := inSubgroup (CFSG.pCore 2) NR with hW
  have hW2 : IsPGroup 2 W := CFSG.pCore_isPGroup.map _
  have hcopW : Nat.Coprime 3 (Nat.card W) := by
    obtain ⟨k, hk⟩ := hW2.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  have hNRW : NR ≤ Subgroup.normalizer (W : Set G) :=
    Subgroup.le_normalizer.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (CFSG.pCore 2 NR))
  have hEW : E ≤ Subgroup.normalizer (W : Set G) := hER.trans hNRW
  have hBW : B ≤ Subgroup.normalizer (W : Set G) := h.B_le_E.trans hEW
  have hYNR : Y ≤ NR := hYR.trans (Subgroup.centralizer_le_normalizer _)
  have hYW : Y ≤ Subgroup.normalizer (W : Set G) := hYNR.trans hNRW
  have hZ'C : Z' ≤ CB := le_of_mem_thetaComponentsIn hZ'
  have hYC : Y ≤ CB := hYZ'.trans hZ'C
  have hBY : ⁅B, Y⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hYC
  have hBNY : B ≤ Subgroup.normalizer (Y : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hBY).trans
      (Subgroup.centralizer_le_normalizer _)
  have hYNB : Y ≤ Subgroup.normalizer (B : Set G) :=
    hYC.trans (Subgroup.centralizer_le_normalizer _)
  have hWY : ⁅W, Y⁆ ≠ ⊥ := by
    intro h0
    rw [Subgroup.commutator_comm] at h0
    have hYCW : Y ≤ Subgroup.centralizer (W : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp h0
    have hc := h.standing.charTwoType NR ⟨R, hR1, hR2, rfl⟩
    rw [pCoreOf_two_eq_inSubgroup] at hc
    exact not_isPGroup_two_of_isPerfect hYp hY1 (hW2.to_le ((le_inf hYNR hYCW).trans hc))
  have hVa : ∀ a ∈ B, a ≠ 1 → ⁅⁅W ⊓ Subgroup.centralizer {a}, B⁆, Y⁆ = ⊥ := by
    intro a haB ha1
    obtain ⟨K, hK, hLK⟩ := exists_mem_thetaComponentsAt_residual_le h48 h.standing h.mem_S.1
      h.a₀_mem h.a₀_ne (h.B_le_A haB) ha1 h.mem_L (h.B_le_C haB)
    set S := W ⊓ Subgroup.centralizer ({a} : Set G) with hS
    have hEa := h.E_le_centralizer haB
    have hES : E ≤ Subgroup.normalizer (S : Set G) :=
      (le_inf hEW (hEa.trans Subgroup.le_normalizer)).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    have hBS : B ≤ Subgroup.normalizer (S : Set G) := h.B_le_E.trans hES
    set V := ⁅S, B⁆ with hV
    have hVS : V ≤ S := Subgroup.le_normalizer_iff_commutator_le_left.mp hBS
    have hS2 : IsPGroup 2 S := hW2.to_le inf_le_left
    have hV2 : IsPGroup 2 V := hS2.to_le hVS
    have hVa' : V ≤ Subgroup.centralizer {a} := hVS.trans inf_le_right
    have hEV : E ≤ Subgroup.normalizer (V : Set G) := fun e he =>
      Source.mem_normalizer_commutator (hES he) (h.E_le_normalizer_B he)
    have hVB : ⁅V, B⁆ = V := by
      have hcop : (Nat.card B).Coprime (Nat.card S) := by
        obtain ⟨k, hk⟩ := hS2.exists_card_eq
        rw [h.cardB, hk]
        exact Nat.Coprime.pow_right k (by norm_num)
      exact CFSG.BenderSuzuki.ig1114_commutator_idempotent_of_coprime S B hcop hBS
    have hVC : V ≤ thetaQuotCentralizer K :=
      h.le_thetaQuotCentralizer h45 h49 haB ha1 hK hLK hV2 hVa' hEV hVB.ge
    have hVK : V ≤ Subgroup.normalizer (K : Set G) :=
      hVC.trans (thetaQuotCentralizer_le_normalizer K)
    have hYK : Y ≤ K := hYZ'.trans (hZ'K a haB ha1 K hK hLK)
    have hCBa : CB ≤ Subgroup.centralizer ({a} : Set G) :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haB)
    have hYS : Y ≤ Subgroup.normalizer (S : Set G) :=
      (le_inf hYW ((hYC.trans hCBa).trans Subgroup.le_normalizer)).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    have hYV : Y ≤ Subgroup.normalizer (V : Set G) := fun y hy =>
      Source.mem_normalizer_commutator (hYS hy) (hYNB hy)
    have hVYV : ⁅V, Y⁆ ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp hYV
    have hVYθ : ⁅V, Y⁆ ≤ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer {a}) := by
      have h1 := (commutator_le_theta_iff hVK).mpr hVC
      rw [theta_eq_inf_of_mem_thetaComponentsAt hK] at h1
      calc ⁅V, Y⁆ ≤ ⁅V, K⁆ := Subgroup.commutator_mono le_rfl hYK
        _ = ⁅K, V⁆ := Subgroup.commutator_comm _ _
        _ ≤ _ := h1.trans inf_le_right
    have hBVY : B ≤ Subgroup.normalizer ((⁅V, Y⁆ : Subgroup G) : Set G) := fun β hβ =>
      Source.mem_normalizer_commutator (h.B_le_E.trans hEV hβ) (hBNY hβ)
    have h0 := commutator_eq_bot_of_mem_partTwoS h.mem_S (h.B_le_A haB) ha1 h.B_le_A hVYθ
      (hV2.to_le hVYV) hBVY
    have h1 : ⁅⁅B, Y⁆, V⁆ = ⊥ := by rw [hBY, Subgroup.commutator_bot_left]
    have h2 : ⁅⁅Y, V⁆, B⁆ = ⊥ := by rw [Subgroup.commutator_comm Y V]; exact h0
    have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
    rwa [hVB] at h3
  set V₀ := W ⊓ CB with hV₀
  have hU : ⁅V₀, Y⁆ ≠ ⊥ := by
    intro hU0
    apply hWY
    have hWY' : W ≤ Subgroup.centralizer (Y : Set G) := by
      refine Sec5.le_of_forall_inf_centralizer_le Nat.prime_three h.elemB
        (by rw [h.cardB]; norm_num) hBW hcopW fun a haB ha1 => ?_
      set S := W ⊓ Subgroup.centralizer ({a} : Set G) with hS
      have hBS : B ≤ Subgroup.normalizer (S : Set G) :=
        (le_inf hBW ((h.B_le_centralizer haB).trans Subgroup.le_normalizer)).trans
          Subgroup.inf_normalizer_le_normalizer_inf
      have hcopS : Nat.Coprime 3 (Nat.card S) := by
        obtain ⟨k, hk⟩ := (hW2.to_le inf_le_left : IsPGroup 2 S).exists_card_eq
        rw [hk]
        exact Nat.Coprime.pow_right k (by norm_num)
      have hfac := CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_factorization 3
        Nat.prime_three B S h.isPGroup_B hBS hcopS
      rw [← hfac]
      refine sup_le (Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hVa a haB ha1)) ?_
      exact (inf_le_inf_right CB inf_le_left).trans
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hU0)
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hWY'
  have hV₀2 : IsPGroup 2 V₀ := hW2.to_le inf_le_left
  have hV₀sol : Group.IsSolvable V₀ := by
    have : Group.IsNilpotent V₀ := hV₀2.isNilpotent
    infer_instance
  have hYV₀ : Y ≤ Subgroup.normalizer (V₀ : Set G) :=
    (le_inf hYW (hYC.trans Subgroup.le_normalizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hV₀Z' : V₀ ≤ Subgroup.normalizer (Z' : Set G) :=
    le_normalizer_of_isPerfect_le_of_mem_thetaComponentsIn hZ' hYZ' hYp hY1 inf_le_right hV₀sol
      hYV₀
  set θZ' := inSubgroup (aschbacherSolvableCore 3) Z' with hθZ'
  have hθZ'eq : θZ' = Z' ⊓ T := theta_eq_inf_of_mem_thetaComponentsIn hZ'
  have hZ'p := isPerfect_of_mem_thetaComponentsIn hZ'
  have hZ'q := isQuasisimple_of_mem_thetaComponentsIn hZ'
  have hZ'Yθ : Z' ≤ Y ⊔ θZ' := by
    intro z hz
    have hz' : z ∈ (Y : Set G) * (T : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right Y T
        (hYC.trans (le_normalizer_theta CB))]
      exact hZ'Y hz
    obtain ⟨y, hy, t, ht, rfl⟩ := hz'
    have htZ' : t ∈ Z' := by
      have := Z'.mul_mem (Z'.inv_mem (hYZ' hy)) hz
      simpa using this
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hy)
      (Subgroup.mem_sup_right (hθZ'eq ▸ ⟨htZ', ht⟩))
  set U := ⁅V₀, Y⁆ with hUdef
  have hUV₀ : U ≤ V₀ := Subgroup.le_normalizer_iff_commutator_le_left.mp hYV₀
  have hU2 : IsPGroup 2 U := hV₀2.to_le hUV₀
  have hUZ' : U ≤ Z' := by
    calc U ≤ ⁅V₀, Z'⁆ := Subgroup.commutator_mono le_rfl hYZ'
      _ = ⁅Z', V₀⁆ := Subgroup.commutator_comm _ _
      _ ≤ Z' := Subgroup.le_normalizer_iff_commutator_le_left.mp hV₀Z'
  have hYθZ' : Y ≤ Subgroup.normalizer (θZ' : Set G) := hYZ'.trans (le_normalizer_theta Z')
  have hV₀θZ' : V₀ ≤ Subgroup.normalizer (θZ' : Set G) :=
    hV₀Z'.trans (normalizer_le_normalizer_theta Z')
  have hUθ : ⁅U ⊔ θZ', Z'⁆ ≤ θZ' := by
    have hXZ' : U ⊔ θZ' ≤ Z' := sup_le hUZ' (theta_le Z')
    have hZ'X : Z' ≤ Subgroup.normalizer ((U ⊔ θZ' : Subgroup G) : Set G) := by
      refine hZ'Yθ.trans (sup_le ?_ ?_)
      · apply le_normalizer_sup_of_conj
        · intro y hy x hx
          exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp
            (le_normalizer_commutator_right V₀ Y hy) x).mp hx)
        · intro y hy x hx
          exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hYθZ' hy) x).mp hx)
      · apply le_normalizer_sup_of_conj
        · intro t ht u hu
          have h1 : u⁻¹ * t * u⁻¹⁻¹ ∈ θZ' := (Subgroup.mem_normalizer_iff.mp
            (le_normalizer_theta Z' (Z'.inv_mem (hUZ' hu))) t).mp ht
          rw [show t * u * t⁻¹ = u * ((u⁻¹ * t * u⁻¹⁻¹) * t⁻¹) by group]
          exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hu)
            (Subgroup.mem_sup_right (θZ'.mul_mem h1 (θZ'.inv_mem ht)))
        · intro t ht x hx
          exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp
            (le_normalizer_theta Z' (theta_le Z' ht)) x).mp hx)
    rcases sup_theta_eq_or_commutator_le hZ'q hXZ' hZ'X with hcov | hcen
    · exfalso
      have hUθN : U ≤ Subgroup.normalizer (θZ' : Set G) :=
        hUZ'.trans (le_normalizer_theta Z')
      have hUsol : Group.IsSolvable U := by
        have : Group.IsNilpotent U := hU2.isNilpotent
        infer_instance
      have hXsol := isSolvable_sup_of_le_normalizer hUθN (theta_solvable_and_not_dvd Z').1 hUsol
      rw [sup_assoc, sup_idem] at hcov
      rw [sup_comm] at hXsol
      have hsol : Group.IsSolvable Z' := hcov ▸ hXsol
      have hZ'1 : Z' ≠ ⊥ := fun h0 => hY1 (le_bot_iff.mp (h0 ▸ hYZ'))
      have : Nontrivial Z' := (Subgroup.nontrivial_iff_ne_bot _).mpr hZ'1
      have := hZ'p
      exact Group.IsPerfect.not_isSolvable Z' hsol
    · exact hcen
  have hZ'V₀ : ⁅Z', V₀⁆ ≤ θZ' := by
    have hA : ⁅Z', V₀⁆ ≤ U ⊔ θZ' := by
      calc ⁅Z', V₀⁆ ≤ ⁅Y ⊔ θZ', V₀⁆ := Subgroup.commutator_mono hZ'Yθ le_rfl
        _ ≤ ⁅Y, V₀⁆ ⊔ θZ' := commutator_sup_le_of_le_normalizer hYθZ' hV₀θZ'
        _ = U ⊔ θZ' := by rw [Subgroup.commutator_comm Y V₀]
    have h1 : ⁅⁅Z', V₀⁆, Z'⁆ ≤ θZ' := (Subgroup.commutator_mono hA le_rfl).trans hUθ
    have h2 : ⁅⁅V₀, Z'⁆, Z'⁆ ≤ θZ' := by rw [Subgroup.commutator_comm V₀ Z']; exact h1
    have h3 := three_subgroups_mod (X := Z') (Y := V₀) (Z := Z') (N := θZ')
      (le_normalizer_theta Z') hV₀θZ' (le_normalizer_theta Z') h1 h2
    rwa [commutator_self_eq_of_isPerfect hZ'p] at h3
  have hUa : ∀ a ∈ B, a ≠ 1 →
      U ≤ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G)) := by
    intro a haB ha1
    obtain ⟨K, hK, hLK⟩ := exists_mem_thetaComponentsAt_residual_le h48 h.standing h.mem_S.1
      h.a₀_mem h.a₀_ne (h.B_le_A haB) ha1 h.mem_L (h.B_le_C haB)
    have hZ'Ka : Z' ≤ K := hZ'K a haB ha1 K hK hLK
    have hYK : Y ≤ K := hYZ'.trans hZ'Ka
    have hCBa : CB ≤ Subgroup.centralizer ({a} : Set G) :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haB)
    have hV₀K : V₀ ≤ Subgroup.normalizer (K : Set G) :=
      le_normalizer_of_isPerfect_le_of_mem_thetaComponentsIn hK hYK hYp hY1
        (inf_le_right.trans hCBa) hV₀sol hYV₀
    have hB3' := hloc a haB ha1 K hK hLK
    set θK := inSubgroup (aschbacherSolvableCore 3) K with hθK
    have hZ'θK : Z' ≤ Subgroup.normalizer (θK : Set G) := hZ'Ka.trans (le_normalizer_theta K)
    have hV₀θK : V₀ ≤ Subgroup.normalizer (θK : Set G) :=
      hV₀K.trans (normalizer_le_normalizer_theta K)
    have h1 : ⁅⁅Z', V₀⁆, Z'⁆ ≤ θK := (Subgroup.commutator_mono hZ'V₀ le_rfl).trans hB3'
    have h2 : ⁅⁅V₀, Z'⁆, Z'⁆ ≤ θK := by rw [Subgroup.commutator_comm V₀ Z']; exact h1
    have h3 := three_subgroups_mod (X := Z') (Y := V₀) (Z := Z') (N := θK) hZ'θK hV₀θK hZ'θK h1 h2
    rw [commutator_self_eq_of_isPerfect hZ'p] at h3
    have hθKa :
        θK ≤ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G)) := by
      rw [hθK, theta_eq_inf_of_mem_thetaComponentsAt hK]
      exact inf_le_right
    calc U ≤ ⁅V₀, Z'⁆ := Subgroup.commutator_mono le_rfl hYZ'
      _ = ⁅Z', V₀⁆ := Subgroup.commutator_comm _ _
      _ ≤ θK := h3
      _ ≤ _ := hθKa
  have hUT : U ≤ thetaT 3 B := by
    simp only [thetaT]
    exact le_iInf fun a => le_iInf fun haB => le_iInf fun ha1 => hUa a haB ha1
  have hodd : Odd (Nat.card (thetaT 3 B)) := h.mem_S.2.2 B h.B_le_A h.cardB
  obtain ⟨k, hk⟩ := hU2.exists_card_eq
  have hdvd := Subgroup.card_dvd_of_le hUT
  rw [hk] at hdvd
  have hk0 : k = 0 := by
    by_contra hk0
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr ((dvd_pow_self 2 hk0).trans hdvd))
  rw [hk0, pow_zero] at hk
  exact hU (Subgroup.eq_bot_of_card_eq _ hk)

end Ctx65

end CFSG.RankThree.PartTwo.Sec6
