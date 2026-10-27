module

public import CFSG.ClassicalGroups.UnitaryFlag.SU3TorusFixVec
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FSqIndex
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Defs
public import CFSG.Quasithin.H13.L32NSp4Over
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TorusQS

open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19 (IsZModSq)
open scoped Matrix Pointwise

section PerfectAction

open scoped commutatorElement

variable {K G M : Type*} [Field K] [Group G] [AddCommGroup M] [Module K M]
  [DistribMulAction G M] [SMulCommClass G K M]

private theorem fix_of_perfect_line {R : Subgroup G} (hRR : ⁅R, R⁆ = R) {x : M} (hx : x ≠ 0)
    (hR : ∀ g ∈ R, ∃ c : K, g • x = c • x) : ∀ g ∈ R, g • x = x := by
  have hle : R ≤ MulAction.stabilizer G x := by
    rw [← hRR, Subgroup.commutator_le]
    intro a ha b hb
    obtain ⟨α, hα⟩ := hR a ha
    obtain ⟨β, hβ⟩ := hR b hb
    have hne : ∀ {γ : K} {g : G}, g • x = γ • x → γ ≠ 0 := by
      rintro γ g hg rfl
      rw [zero_smul, smul_eq_zero_iff_eq] at hg
      exact hx hg
    have hαβ : α * β ≠ 0 := mul_ne_zero (hne hα) (hne hβ)
    have e1 : (b * a) • x = (α * β) • x := by
      rw [mul_smul, hα, smul_comm b α x, hβ, smul_smul]
    have e2 : (a * b) • x = (α * β) • x := by
      rw [mul_smul, hβ, smul_comm a β x, hα, smul_smul, mul_comm]
    have key : ⁅a, b⁆ • ((b * a) • x) = (a * b) • x := by
      rw [← mul_smul]
      congr 1
      group
    rw [e1, e2, smul_comm] at key
    rw [MulAction.mem_stabilizer_iff]
    calc ⁅a, b⁆ • x = (α * β)⁻¹ • ((α * β) • (⁅a, b⁆ • x)) := (inv_smul_smul₀ hαβ _).symm
      _ = x := by rw [key, inv_smul_smul₀ hαβ]
  exact fun g hg => hle hg

variable (K) in
private def flagGroup (w y : M) : Subgroup G where
  carrier := {g | g • w = w ∧ ∃ b : K, g • y = y + b • w}
  mul_mem' := by
    rintro g g' ⟨hgw, b, hgy⟩ ⟨hg'w, b', hg'y⟩
    refine ⟨by rw [mul_smul, hg'w, hgw], b + b', ?_⟩
    rw [mul_smul, hg'y, smul_add, hgy, smul_comm g b' w, hgw, add_smul, add_assoc]
  one_mem' := ⟨one_smul _ _, 0, by rw [one_smul, zero_smul, add_zero]⟩
  inv_mem' := by
    rintro g ⟨hgw, b, hgy⟩
    refine ⟨by rw [inv_smul_eq_iff, hgw], -b, ?_⟩
    rw [inv_smul_eq_iff, smul_add, hgy, smul_comm g (-b) w, hgw, neg_smul,
      add_neg_cancel_right]

private theorem commutator_mem_flagGroup {w y : M} (hy : y ∉ K ∙ w) {a b : G}
    (haw : a • w = w) (hbw : b • w = w) (hcw : ⁅a, b⁆ • w = w)
    {α α' β β' : K} (ha : a • y = α • y + α' • w) (hb : b • y = β • y + β' • w) :
    ⁅a, b⁆ ∈ flagGroup K w y := by
  have hne : ∀ {g : G} {γ γ' : K}, g • w = w → g • y = γ • y + γ' • w → γ ≠ 0 := by
    rintro g γ γ' hgw hg rfl
    apply hy
    rw [zero_smul, zero_add, ← eq_inv_smul_iff, smul_comm, inv_smul_eq_iff.mpr hgw.symm] at hg
    exact Submodule.mem_span_singleton.mpr ⟨γ', hg.symm⟩
  have hαβ : α * β ≠ 0 := mul_ne_zero (hne haw ha) (hne hbw hb)
  have e1 : (b * a) • y = (α * β) • y + (α * β' + α') • w := by
    rw [mul_smul, ha, smul_add, smul_comm b α y, smul_comm b α' w, hb, hbw]
    module
  have e2 : (a * b) • y = (α * β) • y + (β * α' + β') • w := by
    rw [mul_smul, hb, smul_add, smul_comm a β y, smul_comm a β' w, ha, haw]
    module
  have key : ⁅a, b⁆ • ((b * a) • y) = (a * b) • y := by
    rw [← mul_smul]
    congr 1
    group
  rw [e1, e2, smul_add, smul_comm _ (α * β) y, smul_comm _ _ w, hcw] at key
  refine ⟨hcw, (α * β)⁻¹ * (β * α' + β' - (α * β' + α')), ?_⟩
  calc ⁅a, b⁆ • y = (α * β)⁻¹ • ((α * β) • (⁅a, b⁆ • y)) := (inv_smul_smul₀ hαβ _).symm
    _ = (α * β)⁻¹ • ((α * β) • y + (β * α' + β' - (α * β' + α')) • w) := by
      congr 1
      generalize ⁅a, b⁆ • y = z at key ⊢
      linear_combination (norm := module) key
    _ = y + ((α * β)⁻¹ * (β * α' + β' - (α * β' + α'))) • w := by
      rw [smul_add, inv_smul_smul₀ hαβ, smul_smul]

private theorem commutator_fix_of_flagGroup {w y : M} {a b : G} (hcw : ⁅a, b⁆ • w = w)
    (ha : a ∈ flagGroup K w y) (hb : b ∈ flagGroup K w y) : ⁅a, b⁆ • y = y := by
  obtain ⟨haw, α, hay⟩ := ha
  obtain ⟨hbw, β, hby⟩ := hb
  have e1 : (b * a) • y = y + (α + β) • w := by
    rw [mul_smul, hay, smul_add, hby, smul_comm b α w, hbw]
    module
  have e2 : (a * b) • y = y + (α + β) • w := by
    rw [mul_smul, hby, smul_add, hay, smul_comm a β w, haw]
    module
  have key : ⁅a, b⁆ • ((b * a) • y) = (a * b) • y := by
    rw [← mul_smul]
    congr 1
    group
  rw [e1, e2, smul_add, smul_comm _ _ w, hcw] at key
  exact add_right_cancel key

private theorem fix_of_perfect_flag {R : Subgroup G} (hRR : ⁅R, R⁆ = R) {w y : M}
    (hy : y ∉ K ∙ w) (hRw : ∀ g ∈ R, g • w = w)
    (hRy : ∀ g ∈ R, ∃ a b : K, g • y = a • y + b • w) : ∀ g ∈ R, g • y = y := by
  have hc : ∀ a ∈ R, ∀ b ∈ R, ⁅a, b⁆ ∈ R := fun a ha b hb =>
    hRR ▸ Subgroup.commutator_mem_commutator ha hb
  have h1 : R ≤ flagGroup K w y := by
    rw [← hRR, Subgroup.commutator_le]
    intro a ha b hb
    obtain ⟨α, α', hα⟩ := hRy a ha
    obtain ⟨β, β', hβ⟩ := hRy b hb
    exact commutator_mem_flagGroup hy (hRw a ha) (hRw b hb) (hRw _ (hc a ha b hb)) hα hβ
  have h2 : R ≤ MulAction.stabilizer G y := by
    rw [← hRR, Subgroup.commutator_le]
    intro a ha b hb
    exact commutator_fix_of_flagGroup (hRw _ (hc a ha b hb)) (h1 ha) (h1 hb)
  exact fun g hg => h2 hg

end PerfectAction

section SU3

open CFSG.LinearGroups CFSG.ClassicalGroups.UnitaryFlag CFSG.LieType.BorelTits

variable {K : Type} [Field K] [Finite K] {n : ℕ}

private theorem unitaryForm_β_eq (hK : Nat.card K = (2 ^ n) ^ 2) [CharP K 2]
    (x y : Fin 3 → K) :
    (unitaryForm 2 n hK 3).β x y = stdHermForm (unitaryFieldDataOfCard hK) 3 x y := by
  rw [unitaryForm_β hK x y, stdHermForm_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [unitaryInvolution_apply, (unitaryFieldDataOfCard hK).bar_apply]

private theorem exists_invariant_line (hK : Nat.card K = (2 ^ n) ^ 2)
    {W : Submodule K (Fin 3 → K)} (hW0 : W ≠ ⊥) (hW1 : W ≠ ⊤) :
    ∃ L : Submodule K (Fin 3 → K), Module.finrank K L = 1 ∧
      ∀ g : CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ n) K, (∀ x ∈ W, g • x ∈ W) →
        (∀ x ∈ W, g⁻¹ • x ∈ W) → ∀ x ∈ L, g • x ∈ L := by
  have : CharP K 2 := (unitaryFieldDataOfCard hK).charP
  have h1 : 1 ≤ Module.finrank K W := Submodule.one_le_finrank_iff.mpr hW0
  have h2 := Submodule.finrank_lt hW1
  rw [Module.finrank_fin_fun] at h2
  by_cases hW : Module.finrank K W = 1
  · exact ⟨W, hW, fun g hg _ => hg⟩
  · have hdim := (unitaryForm 2 n hK 3).finrank_perp W
    rw [Module.finrank_fin_fun] at hdim
    refine ⟨(unitaryForm 2 n hK 3).perp W, by omega, fun g _ hg' x hx => ?_⟩
    rw [ReflForm.mem_perp] at hx ⊢
    intro a ha
    have hx' := hx _ (hg' a ha)
    rw [unitaryForm_β_eq] at hx' ⊢
    rwa [← stdHermForm_smul_smul (unitaryFieldDataOfCard hK) g (g⁻¹ • a) x,
      smul_inv_smul] at hx'

private theorem exists_coeffs_of_perp (hK : Nat.card K = (2 ^ n) ^ 2) {w v x : Fin 3 → K}
    (hw0 : w ≠ 0) (hww : stdHermForm (unitaryFieldDataOfCard hK) 3 w w = 0)
    (hwv : stdHermForm (unitaryFieldDataOfCard hK) 3 w v = 0) (hv : v ∉ K ∙ w)
    (hwx : stdHermForm (unitaryFieldDataOfCard hK) 3 w x = 0) :
    ∃ a b : K, x = a • v + b • w := by
  have : CharP K 2 := (unitaryFieldDataOfCard hK).charP
  have hdim := (unitaryForm 2 n hK 3).finrank_perp (K ∙ w)
  rw [Module.finrank_fin_fun, finrank_span_singleton hw0] at hdim
  have hmem : ∀ y, stdHermForm (unitaryFieldDataOfCard hK) 3 w y = 0 →
      y ∈ (unitaryForm 2 n hK 3).perp (K ∙ w) := fun y hy =>
    (unitaryForm 2 n hK 3).mem_perp_span_singleton.mpr (by rwa [unitaryForm_β_eq])
  have hlt : K ∙ w < K ∙ w ⊔ K ∙ v :=
    lt_of_le_of_ne le_sup_left fun heq =>
      hv (heq ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self v))
  have hlt' := Submodule.finrank_lt_finrank_of_lt hlt
  rw [finrank_span_singleton hw0] at hlt'
  have hle : K ∙ w ⊔ K ∙ v ≤ (unitaryForm 2 n hK 3).perp (K ∙ w) :=
    sup_le ((Submodule.span_singleton_le_iff_mem _ _).mpr (hmem w hww))
      ((Submodule.span_singleton_le_iff_mem _ _).mpr (hmem v hwv))
  have heq := Submodule.eq_of_le_of_finrank_le hle (by omega)
  have hx : x ∈ K ∙ w ⊔ K ∙ v := by
    rw [heq]
    exact hmem x hwx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hy
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
  exact ⟨a, b, add_comm _ _⟩

private theorem herm_eq_zero_of_isotropic (hK : Nat.card K = (2 ^ n) ^ 2)
    {T : Subgroup (CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ n) K)} {v w : Fin 3 → K}
    (hvT : ∀ b ∈ T, b • v = v)
    (hvU : ∀ x : Fin 3 → K, (∀ b ∈ T, b • x = x) → ∃ c : K, x = c • v)
    (hw0 : w ≠ 0) (hww : stdHermForm (unitaryFieldDataOfCard hK) 3 w w = 0)
    (hwT : ∀ t ∈ T, ∃ c : K, t • w = c • w) :
    stdHermForm (unitaryFieldDataOfCard hK) 3 w v = 0 := by
  set h := unitaryFieldDataOfCard hK
  by_contra hne
  have hfix : ∀ t ∈ T, t • w = w := by
    intro t ht
    obtain ⟨c, hc⟩ := hwT t ht
    have hiso := stdHermForm_smul_smul h t w v
    rw [hc, hvT t ht] at hiso
    simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul] at hiso
    have hbar : h.bar c = 1 := mul_right_cancel₀ hne (hiso.trans (one_mul _).symm)
    have hc1 : c = 1 := h.bar.injective (hbar.trans (map_one _).symm)
    rw [hc, hc1, one_smul]
  obtain ⟨d, hd⟩ := hvU w hfix
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hw0 (by rw [hd, zero_smul])
  apply hne
  rw [show v = d⁻¹ • w by rw [hd, inv_smul_smul₀ hd0], map_smul, hww, smul_zero]

private theorem fixes_of_line (hK : Nat.card K = (2 ^ n) ^ 2)
    {T R : Subgroup (CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ n) K)}
    (hT : Nat.card T = 2 ^ n - 1) (hRR : ⁅R, R⁆ = R) {v w : Fin 3 → K}
    (hvT : ∀ b ∈ T, b • v = v)
    (hvU : ∀ x : Fin 3 → K, (∀ b ∈ T, b • x = x) → ∃ c : K, x = c • v)
    (hw0 : w ≠ 0) (hwT : ∀ t ∈ T, ∃ c : K, t • w = c • w)
    (hwR : ∀ g ∈ R, ∃ c : K, g • w = c • w) : ∀ g ∈ R, g • v = v := by
  set h := unitaryFieldDataOfCard hK
  have hRw := fix_of_perfect_line hRR hw0 hwR
  by_cases hww : stdHermForm h 3 w w = 0
  · have hwv := herm_eq_zero_of_isotropic hK hvT hvU hw0 hww hwT
    by_cases hvw : v ∈ K ∙ w
    · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hvw
      intro g hg
      rw [smul_comm, hRw g hg]
    · refine fix_of_perfect_flag hRR hvw hRw fun g hg => ?_
      refine exists_coeffs_of_perp hK hw0 hww hwv hvw ?_
      rw [← hRw g hg, stdHermForm_smul_smul, hwv]
  · have hfix : ∀ t ∈ T, t • w = w := by
      intro t ht
      obtain ⟨c, hc⟩ := hwT t ht
      have hc1 : c = 1 := eq_one_of_pow_sub_one_and_norm_eq_one h
        (torus_eigenvalue_pow_eq_one hT ht hw0 hc) (norm_eq_one_of_mulVec_eq_smul h hww hc)
      rw [hc, hc1, one_smul]
    obtain ⟨d, hd⟩ := hvU w hfix
    have hd0 : d ≠ 0 := by
      rintro rfl
      exact hw0 (by rw [hd, zero_smul])
    intro g hg
    rw [show v = d⁻¹ • w by rw [hd, inv_smul_smul₀ hd0], smul_comm, hRw g hg]

end SU3

theorem fixes_of_reducible_su3 {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2)
    {T R : Subgroup (CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ n) K)}
    (hT : Nat.card T = 2 ^ n - 1) (hRR : ⁅R, R⁆ = R) {v : Fin 3 → K}
    (hvT : ∀ b ∈ T, ((b : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v = v)
    (hvU : ∀ w : Fin 3 → K,
      (∀ b ∈ T, ((b : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w = w) → ∃ c : K, w = c • v)
    {W : Submodule K (Fin 3 → K)}
    (hWT : ∀ t ∈ T, ∀ w ∈ W, ((t : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w ∈ W)
    (hWR : ∀ h ∈ R, ∀ w ∈ W, ((h : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w ∈ W)
    (hW0 : W ≠ ⊥) (hW1 : W ≠ ⊤) :
    ∀ g ∈ R, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v = v := by
  obtain ⟨L, hL1, hLinv⟩ := exists_invariant_line hK hW0 hW1
  obtain ⟨w, hwL, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (Submodule.one_le_finrank_iff.mp hL1.ge)
  have hLw : L = K ∙ w := eq_span_singleton_of_mem_of_finrank_eq_one hL1 hwL hw0
  have hline : ∀ g : CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ n) K, (∀ x ∈ W, g • x ∈ W) →
      (∀ x ∈ W, g⁻¹ • x ∈ W) → ∃ c : K, g • w = c • w := by
    intro g h1 h2
    have hgw := hLinv g h1 h2 w hwL
    rw [hLw] at hgw
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hgw
    exact ⟨c, hc.symm⟩
  exact fixes_of_line hK hT hRR hvT hvU hw0
    (fun t ht => hline t (hWT t ht) (hWT t⁻¹ (T.inv_mem ht)))
    (fun g hg => hline g (hWR g hg) (hWR g⁻¹ (R.inv_mem hg)))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TorusQS

end
