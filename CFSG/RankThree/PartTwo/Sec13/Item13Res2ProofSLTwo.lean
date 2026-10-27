module

public import CFSG.RankThree.PartTwo.Sec13.Item131bProofDefs
public import CFSG.RankThree.PartTwo.Sec12.Item128Bar
public import CFSG.RankThree.PartTwo.Sec13.Item13SLTwo
public import CFSG.RankThree.PartTwo.Sec4.StatementsSporadic
import CFSG.RankThree.PartTwo.Sec13.Item13Res2ProofCubeLift
import CFSG.RankThree.PartTwo.Sec13.Item13Res2ProofJ2
import CFSG.RankThree.PartTwo.Sec13.Item131bProofHeis
import CFSG.RankThree.PartTwo.Sec13.Item13ResProofTypes
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec13.OmegaNonempty
import CFSG.RankThree.PartTwo.Sec13.Item131Facts
import CFSG.RankThree.PartTwo.Sec12.Item125Act

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def Step131bSLTwoInE : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec13Data G A c L → Sec4.IsSLThreePiTwo (lBarA c L A) →
    ∀ E : Subgroup G, E ≤ (L ⊔ A) ⊓ Subgroup.normalizer (A : Set G) →
      CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 27 →
      ¬ IsCyclic (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) →
      ¬ IsCyclic (E ⊓ L : Subgroup G) → E ∈ partTwoE G

namespace Res2Proof

theorem card_inf_le_three {X : Type} [Group X] [Finite X] {π : Bool} {p f : ℕ} {K : Type}
    [Field K] (D : SLTwoData X π p f K) {Ab : Subgroup X}
    (hAe : CFSG.Assembly.IsElemAbelian 3 Ab) (h27 : Nat.card Ab = 27) (hsup : D.L₀ ⊔ Ab = ⊤) :
    Nat.card (Ab ⊓ D.L₀ : Subgroup X) ≤ 3 := by
  set C := Subgroup.centralizer (D.L₀ : Set X) with hC
  have hB9 := D.card_inf_sup_eq_nine h27 hsup
  have hle : Ab ⊓ D.L₀ ≤ Ab ⊓ (D.L₀ ⊔ C) := inf_le_inf_left _ le_sup_left
  have hdvd : Nat.card (Ab ⊓ D.L₀ : Subgroup X) ∣ 3 ^ 2 := by
    rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← hB9]
    exact Subgroup.card_dvd_of_le hle
  by_contra hgt
  have h9 : Nat.card (Ab ⊓ D.L₀ : Subgroup X) = 9 := by
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    interval_cases k <;> simp_all
  have hBeq : Ab ⊓ D.L₀ = Ab ⊓ (D.L₀ ⊔ C) :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hB9, h9])
  obtain ⟨α, hαA, hαL⟩ : ∃ α ∈ Ab, α ∉ D.L₀ := by
    by_contra h
    push Not at h
    rw [inf_eq_left.mpr h, h27] at h9
    norm_num at h9
  have hAbeq : (Ab ⊓ D.L₀) ⊔ Subgroup.zpowers α = Ab :=
    Sec12.eq_of_card_nine_lt h27 (sup_le inf_le_left (Subgroup.zpowers_le.mpr hαA)) le_sup_left
      h9 (Subgroup.mem_sup_right (Subgroup.mem_zpowers α)) (fun h => hαL h.2)
  have hX : D.L₀ ⊔ Subgroup.zpowers α = ⊤ := by
    rw [eq_top_iff, ← hsup, ← hAbeq]
    exact sup_le le_sup_left (sup_le (inf_le_right.trans le_sup_left) le_sup_right)
  have hu : D.u ∈ D.L₀ ⊔ Subgroup.zpowers α := hX ▸ Subgroup.mem_top _
  obtain ⟨ℓ, hℓ, w, hw, hℓw⟩ := Subgroup.mem_sup_of_normal_left.mp hu
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  have hα3 : α ^ 3 = 1 := hAe.2 α hαA
  have hαj : α ^ j ∈ D.L₀ ⊔ C := by
    have e1 : α ^ j = ℓ⁻¹ * D.u := by rw [← hℓw]; group
    rw [e1]
    exact mul_mem (Subgroup.mem_sup_left (inv_mem hℓ)) (Subgroup.mem_sup_right D.mem_centralizer)
  have hαC : α ∈ D.L₀ ⊔ C := by
    rw [zpow_eq_zpow_emod' j hα3] at hαj hℓw
    have hj : j % (3 : ℕ) = 0 ∨ j % (3 : ℕ) = 1 ∨ j % (3 : ℕ) = 2 := by omega
    rcases hj with h0 | h1 | h2
    · rw [h0, zpow_zero, mul_one] at hℓw
      exact absurd (hℓw ▸ hℓ) D.not_mem
    · rwa [h1, zpow_one] at hαj
    · rw [h2] at hαj
      have e2 : α ^ (2 : ℤ) = α⁻¹ := by
        rw [zpow_two]
        refine eq_inv_of_mul_eq_one_left ?_
        rw [← hα3, pow_three, mul_assoc]
      rw [e2] at hαj
      exact inv_mem_iff.mp hαj
  have : α ∈ Ab ⊓ D.L₀ := hBeq ▸ ⟨hαA, hαC⟩
  exact hαL this.2

variable {G : Type} [Group G] [Finite G] {A L : Subgroup G} {c : G}

theorem subgroupOf_lBar_eq_L₀ {π : Bool} {p f : ℕ} {K : Type} [Field K]
    (hD : Sec13Data G A c L) (D : SLTwoData (lBarA c L A) π p f K) :
    (Sec12.lBar c L).subgroupOf (lBarA c L A) = D.L₀ := by
  set Λ := (Sec12.lBar c L).subgroupOf (lBarA c L A) with hΛdef
  have hΛn : Λ.Normal := lBar_normal hD
  have hΛp : Group.IsPerfect Λ := isPerfect_subgroupOf_lBar hD
  have hΛ1 : Λ ≠ ⊥ := subgroupOf_lBar_ne_bot hD
  have hq2 : 2 < p ^ f := by
    by_contra hq2
    have hp := D.piField.prime
    have hf := D.piField.one_le
    have h2 : p ^ f = 2 := by
      have : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) _)
      omega
    have := SLTwoData.isSolvable_of_two D h2
    have : Group.IsSolvable Λ := Group.isSolvable_of_isSolvable_injective Λ.subtype_injective
    have : Nontrivial Λ := (Subgroup.nontrivial_iff_ne_bot Λ).mpr hΛ1
    exact Group.IsPerfect.not_isSolvable Λ inferInstance
  exact le_antisymm (D.le_of_isPerfect hΛp) (D.le_of_normal hq2 hΛn hΛp hΛ1)

theorem inf_le_zpowers_of_isSLThreePiTwo (hD : Sec13Data G A c L)
    (hSL : Sec4.IsSLThreePiTwo (lBarA c L A)) : A ⊓ L ≤ Subgroup.zpowers c := by
  obtain ⟨π, p, f, K, _, ⟨D⟩⟩ := exists_sLTwoData hSL
  have hcL : c ∈ L := mem_of_isSLThreePiTwo slTwoCenter hD hSL
  set Λ := (Sec12.lBar c L).subgroupOf (lBarA c L A) with hΛdef
  have hL₀ : D.L₀ = Λ := (subgroupOf_lBar_eq_L₀ hD D).symm
  set Ab := (aBarHom hD).range with hAb
  have hAb27 : Nat.card Ab = 27 := by
    rw [hAb, ← Nat.card_congr (MonoidHom.ofInjective (aBarHom_injective hD)).toEquiv,
      hD.card_eq]
  have hAbe : CFSG.Assembly.IsElemAbelian 3 Ab := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
    · obtain ⟨_, a, rfl⟩ := x
      obtain ⟨_, b, rfl⟩ := y
      apply Subtype.ext
      change aBarHom hD a * aBarHom hD b = aBarHom hD b * aBarHom hD a
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hD.commute a.2 b.2)
    · rintro _ ⟨a, rfl⟩
      rw [← map_pow]
      have : a ^ 3 = 1 := Subtype.ext (by simpa using hD.isElemAbelian.2 _ a.2)
      rw [this, map_one]
  have hsup : D.L₀ ⊔ Ab = ⊤ := by rw [hL₀]; exact lBar_sup_range_aBarHom hD
  have h3 := card_inf_le_three D hAbe hAb27 hsup
  set z := mkC (L := L) hD.mem_A with hz
  have hzAb : z ∈ Ab := ⟨⟨c, hD.mem_A⟩, (mkC_eq_aBarHom hD).symm⟩
  have hzL : z ∈ D.L₀ := hL₀ ▸ mkC_mem_lBar hD hcL
  have hzeq : Subgroup.zpowers z = Ab ⊓ D.L₀ := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr ⟨hzAb, hzL⟩) ?_
    rw [Nat.card_zpowers, orderOf_mkC hD]
    exact h3
  intro a ha
  set a' : A := ⟨a, ha.1⟩ with ha'
  have hmem : aBarHom hD a' ∈ Ab ⊓ D.L₀ := by
    refine ⟨⟨a', rfl⟩, ?_⟩
    have hΛmem : aBarHom hD a' ∈ Λ := by
      rw [hΛdef, Subgroup.mem_subgroupOf, aBarHom_apply]
      exact ⟨⟨a, hD.A_le_normalizer_zpowers ha.1⟩, Subgroup.mem_subgroupOf.mpr ha.2, rfl⟩
    exact hL₀ ▸ hΛmem
  rw [← hzeq] at hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hk' : aBarHom hD ((⟨c, hD.mem_A⟩ : A) ^ k) = aBarHom hD a' := by
    rw [map_zpow, ← mkC_eq_aBarHom hD, hk]
  have heq := aBarHom_injective hD hk'
  have : a = c ^ k := by
    have h := congrArg Subtype.val heq
    simpa [ha'] using h.symm
  rw [this]
  exact Subgroup.zpow_mem_zpowers c k

end Res2Proof

open Res2Proof Item131bProof

theorem step131bSLTwo_of_inE
    (h128 : Sec12.Item128BarAt) (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5)
    (h415 : Sec4.Item4_15) (hInE : Step131bSLTwoInE) : Step131bSLTwo := by
  intro G _ _ A c L hD hSL2 E hEle hEe hE27 hEC hEL
  by_contra hET
  have hcL : c ∈ L := mem_of_isSLThreePiTwo slTwoCenter hD hSL2
  have hSL : Sec4.IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L) :=
    ResProof.isSLThreePi_of_isSLThreePiTwo hD hSL2
  have hty : HeisType (L ⧸ aschbacherSolvableCore 3 L) := Or.inl hSL
  obtain ⟨hcE, hC9, hEL9, hsup⟩ :=
    e_facts hD hty hcL (hEle.trans inf_le_left) hEe hE27 hEC hEL
  have hAL : A ⊓ L ≤ Subgroup.zpowers c := inf_le_zpowers_of_isSLThreePiTwo hD hSL2
  have hAN : A ≤ Subgroup.normalizer (E : Set G) :=
    le_normalizer_of_heis hD hAL (hEle.trans inf_le_right) hcE hsup
  have hstd : Sec12.Sec12StdBar G E c L := sec12StdBar_of_heis hD hcL hEe hE27 hcE hC9 hsup hAN
  have hEE : E ∈ partTwoE G := hInE G A c L hD hSL2 E hEle hEe hE27 hEC hEL
  have hEF : E ∈ partTwoF G := hstd.partTwoF_eq ▸ hEE
  obtain ⟨F, hF⟩ := omegaA_nonempty hD.toPartTwoStanding hD.partTwoS_eq hEF hET
  obtain ⟨hFE, hF3, e, rfl, -⟩ := id hF
  obtain ⟨hcase, hHJ⟩ := (h128 G E c L hstd hEE (Or.inl hSL)).resolve_left hET e hF
  rcases hcase with ⟨-, hA6⟩ | ⟨heL, hEL', -⟩
  · exact not_isTripleCover_six hty hA6
  have heE : e ∈ E := hFE (Subgroup.mem_zpowers e)
  have he3 : e ^ 3 = 1 := hEe.2 e heE
  have heo : orderOf e = 3 := by rw [← Nat.card_zpowers]; exact hF3
  have hec : e * c = c * e := congrArg Subtype.val (hEe.1.is_comm.comm ⟨e, heE⟩ ⟨c, hcE⟩)
  have hecz : e ∉ Subgroup.zpowers c := by
    intro hmem
    have h1 : Subgroup.zpowers e ⊔ Subgroup.zpowers c = Subgroup.zpowers c :=
      sup_eq_right.mpr (Subgroup.zpowers_le.mpr hmem)
    rw [hEL', h1, Nat.card_zpowers, hD.orderOf_eq] at hEL9
    norm_num at hEL9
  have hce : c ∉ Subgroup.zpowers e := by
    intro hmem
    apply hecz
    have h1 : Subgroup.zpowers c = Subgroup.zpowers e := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hmem) ?_
      rw [Nat.card_zpowers, Nat.card_zpowers, heo, hD.orderOf_eq]
    rw [h1]
    exact Subgroup.mem_zpowers e
  obtain ⟨K, hK⟩ := Sec12.exists_mem_lA422 h422 h45 hstd.toPartTwoStanding hEF hE27 hF
  obtain ⟨x, -, hxe, hx3⟩ := exists_cube_root_of_isSLThreePiTwo hD hSL2 heL he3 hec hecz
  exact not_cube_of_j2 h45 h415 sporadicModels131 hD.toTheoremFourHyp hEe heo hK (hHJ K hK)
    hcE hce hxe hx3

end CFSG.RankThree.PartTwo.Sec13
