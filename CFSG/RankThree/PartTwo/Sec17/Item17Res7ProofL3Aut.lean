module

public import CFSG.RankThree.PartTwo.Sec17.Item17Res7ProofL3Defs
public import CFSG.RankThree.PartTwo.Sec17.Item17Res7ProofL3AutLin
public import CFSG.RankThree.PartTwo.Sec17.Item17Res7ProofL3AutUni
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.PartTwo.Sec13.Item138ProofOmega
import CFSG.RankThree.PartTwo.Sec19.Step1915WProofLie3K
import CFSG.RankThree.PartTwo.Sec19.Step1919NarrowRank

public section

namespace CFSG.RankThree.PartTwo.Sec17.Proof17Res7

open Matrix CFSG.RankThree.PartTwo.Sec4 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Assembly.RankThreeEven (projImage)

variable {K : Type} [Field K] {p : ℕ}

theorem eq_conj_of_transport {M N : Type*} [Group M] [Group N] (Φ : N ≃* M) (β : MulAut M)
    {x : N} (h : (Φ.trans β).trans Φ.symm = MulAut.conj x) : β = MulAut.conj (Φ x) := by
  ext y
  have := congrArg (fun γ : MulAut N => Φ (γ (Φ.symm y))) h
  simp only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply, MulAut.conj_apply, map_mul,
    map_inv] at this
  rw [this, MulAut.conj_apply]

theorem autCent_projImage {π : Bool} (hK : PiField π p 1 K) (hq : ModThree π (p ^ 1))
    (hp3 : 3 < p) {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {dM cM : projImage (slPi π 3 (p ^ 1) K)}
    (hdM : (dM : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (diagTau hτ))
    (hcM : (cM : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (cycThree : GL (Fin 3) K))
    (β : MulAut (projImage (slPi π 3 (p ^ 1) K))) (hd : β dM = dM) (hc : β cM = cM) :
    ∃ m j : ℕ, β = MulAut.conj (dM ^ m * cM ^ j) := by
  have hp : p.Prime := hK.prime
  have : Fact p.Prime := ⟨hp⟩
  have := hK.finite
  cases π
  ·
    have h := hK.unitary
    have hq' : p % 3 = 2 := by
      have := hq
      change p ^ 1 % 3 = 2 at this
      rwa [pow_one] at this
    set Φ := unitaryModelEquiv h with hΦ
    set dU : unitarySU p 1 K 3 :=
      ⟨diagTau hτ, diagTau_mem_slPi (π := false) (fun _ => h) (fun _ => hq) hτ⟩
      with hdU
    set cU : unitarySU p 1 K 3 := ⟨cycThree, cycThree_mem_slPi (π := false) (fun _ => h)⟩
      with hcU
    have hΦd : Φ (dU : unitaryPSU h 3) = dM := Subtype.ext (by
      rw [hΦ, coe_unitaryModelEquiv_mk, hdM])
    have hΦc : Φ (cU : unitaryPSU h 3) = cM := Subtype.ext (by
      rw [hΦ, coe_unitaryModelEquiv_mk, hcM])
    set β' : MulAut (unitaryPSU h 3) := (Φ.trans β).trans Φ.symm with hβ'
    have hd' : β' (dU : unitaryPSU h 3) = dU := by
      rw [hβ', MulEquiv.trans_apply, MulEquiv.trans_apply, hΦd, hd, ← hΦd,
        MulEquiv.symm_apply_apply]
    have hc' : β' (cU : unitaryPSU h 3) = cU := by
      rw [hβ', MulEquiv.trans_apply, MulEquiv.trans_apply, hΦc, hc, ← hΦc,
        MulEquiv.symm_apply_apply]
    obtain ⟨m, j, hmj⟩ := autCent_unitaryPSU hτ hτ1 h hp3 hq' rfl rfl β' hd' hc'
    refine ⟨m, j, ?_⟩
    rw [eq_conj_of_transport Φ β hmj, map_mul, map_pow, map_pow, hΦd, hΦc]
  ·
    have hcard : Nat.card K = p := by
      have := hK.card
      change Nat.card K = p ^ 1 at this
      rwa [pow_one] at this
    set Φ := linearModelEquiv (K := K) (p ^ 1) with hΦ
    have hΦd : Φ (proj 3 K (dSL hτ)) = dM := Subtype.ext (by
      rw [hΦ, coe_linearModelEquiv_proj, toGL_dSL, hdM])
    have hΦc : Φ (proj 3 K cSL) = cM := Subtype.ext (by
      rw [hΦ, coe_linearModelEquiv_proj, toGL_cSL, hcM])
    set β' : MulAut (projectiveSL 3 K) := (Φ.trans β).trans Φ.symm with hβ'
    have hd' : β' (proj 3 K (dSL hτ)) = proj 3 K (dSL hτ) := by
      rw [hβ', MulEquiv.trans_apply, MulEquiv.trans_apply, hΦd, hd, ← hΦd,
        MulEquiv.symm_apply_apply]
    have hc' : β' (proj 3 K cSL) = proj 3 K cSL := by
      rw [hβ', MulEquiv.trans_apply, MulEquiv.trans_apply, hΦc, hc, ← hΦc,
        MulEquiv.symm_apply_apply]
    obtain ⟨m, j, hmj⟩ := autCent_projectiveSL hτ hτ1 hcard β' hd' hc'
    refine ⟨m, j, ?_⟩
    rw [eq_conj_of_transport Φ β hmj, map_mul, map_pow, map_pow, hΦd, hΦc]

end CFSG.RankThree.PartTwo.Sec17.Proof17Res7

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projImage)

theorem ks17L3AutCent : KS17L3AutCent := by
  intro X _ _ p _ hp3 hiso h91 h98 B hB α hα
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h9 : (Nat.card X).factorization 3 = 2 :=
    Sec13.Item138Proof.factorization_card_three_eq_two le_rfl hiso (by simp; omega)
  obtain ⟨π, K, _, hK, hq, ⟨ψ⟩⟩ := Sec13.exists_projImage_model le_rfl hiso
  have := hK.finite
  have : Finite (Matrix.ProjGenLinGroup (Fin 3) K) := by
    unfold Matrix.ProjGenLinGroup
    infer_instance
  set M := projImage (slPi π 3 (p ^ 1) K) with hM
  have h9M : (Nat.card M).factorization 3 = 2 := by rw [← Nat.card_congr ψ.toEquiv, h9]
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  obtain ⟨dM, cM, hdM, hcM, hdc, hdo, hco, hcd⟩ := Sec19.Step1915WProof.exists_heisPair hK hq hτ hτ1
  set E := Subgroup.zpowers dM ⊔ Subgroup.zpowers cM with hE
  have hE9 : Nat.card E = 9 := by
    rw [hE, Sec19.Step1919NarrowRank.card_sup_zpowers_of_orderOf _ hco hcd (by
      rintro _ ⟨k, rfl⟩
      exact ((Commute.zpow_left hdc k).eq)), Nat.card_zpowers, hdo]
  set S₀ := Sylow.ofCard E (by rw [hE9, h9M]; norm_num) with hS₀
  have hB'card : Nat.card (B.map ψ.toMonoidHom) = 3 ^ (Nat.card M).factorization 3 := by
    rw [Subgroup.card_map_of_injective ψ.injective, hB, h9M]
    norm_num
  set S' := Sylow.ofCard (B.map ψ.toMonoidHom) hB'card with hS'
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq M S₀ S'
  have hmemB : ∀ w ∈ E, ψ.symm (k * w * k⁻¹) ∈ B := by
    intro w hw
    have h1 : k * w * k⁻¹ ∈ ((k • S₀ : Sylow 3 M) : Subgroup M) := by
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
      exact ⟨w, hw, by simp [MulAut.smul_def, MulAut.conj_apply]⟩
    rw [hk] at h1
    obtain ⟨y, hy, hye⟩ := h1
    have : ψ.symm (k * w * k⁻¹) = y := by
      rw [← hye]
      exact ψ.symm_apply_apply y
    rw [this]
    exact hy
  set α' : MulAut M := (ψ.symm.trans α).trans ψ with hα'
  set β : MulAut M := (MulAut.conj k)⁻¹ * α' * MulAut.conj k with hβ
  have hfix : ∀ w ∈ E, β w = w := by
    intro w hw
    have h1 : α' (k * w * k⁻¹) = k * w * k⁻¹ := by
      rw [hα', MulEquiv.trans_apply, MulEquiv.trans_apply, hα _ (hmemB w hw),
        MulEquiv.apply_symm_apply]
    rw [hβ, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, h1, MulAut.inv_def,
      MulAut.conj_symm_apply]
    group
  obtain ⟨m, j, hmj⟩ := Proof17Res7.autCent_projImage hK hq hp3 hτ hτ1 hdM hcM β
    (hfix dM (Subgroup.mem_sup_left (Subgroup.mem_zpowers dM)))
    (hfix cM (Subgroup.mem_sup_right (Subgroup.mem_zpowers cM)))
  set e := dM ^ m * cM ^ j with he
  have heE : e ∈ E := mul_mem (pow_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers dM)) m)
    (pow_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers cM)) j)
  refine ⟨ψ.symm (k * e * k⁻¹), hmemB e heE, ?_⟩
  have hα'eq : α' = MulAut.conj (k * e * k⁻¹) := by
    have : α' = MulAut.conj k * β * (MulAut.conj k)⁻¹ := by rw [hβ]; group
    rw [this, hmj, ← map_inv, ← map_mul, ← map_mul]
  ext x
  have h1 : α' (ψ x) = (k * e * k⁻¹) * ψ x * (k * e * k⁻¹)⁻¹ := by
    rw [hα'eq, MulAut.conj_apply]
  have h2 : α' (ψ x) = ψ (α x) := by
    rw [hα', MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rw [MulAut.conj_apply]
  apply ψ.injective
  rw [← h2, h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

end CFSG.RankThree.PartTwo.Sec17
