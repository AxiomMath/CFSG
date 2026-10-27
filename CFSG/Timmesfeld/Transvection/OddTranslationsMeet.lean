module

public import CFSG.Timmesfeld.Transvection.OddTranslations
import CFSG.Timmesfeld.Transvection.OddResidueBlockPrev
import CFSG.Timmesfeld.Transvection.OddLocal
import CFSG.Timmesfeld.Transvection.OddSU3Torus

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg
open CFSG.LocalAnalysis.UniquenessCase CFSG.LieType.BorelTits
open CFSG.Timmesfeld.Transvection.Pres
open scoped commutatorElement

section CertificateFree

variable {H : Type} [Group H] {Δ : Set (Subgroup H)} {r : ℕ} {P Q : Fin r → Subgroup H}
  {k : Fin r} {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

private theorem eq_one_of_conjSub_mul_mul_eq (h : TransvectionHyp H Δ)
    (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A) (hF : IsFrame Δ P Q) (hFn : Nat.card F = (2 ^ n) ^ 2)
    {θ : SU (unitaryInvolution F 2 n) 3 →* H} (hθr : θ.range = residueGroup Δ P Q k)
    {i : Fin r} (hik : i ≠ k) {y z b : H}
    (hy : y ∈ shortRootGroup Δ (P k) (Q k) (Q i) (P i))
    (hz : z ∈ shortRootGroup Δ (P k) (Q k) (P i) (Q i))
    (hb : b ∈ (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ)
    (hc : conjSub (P i) (y * z * b) = P i) : y = 1 := by
  haveI := h.finite
  have hKD := commuting_map_heis_of_ne (unitaryInvolution_involutive hFn) hθr hik
  have hbN : b ∈ Subgroup.normalizer (P i : Set H) :=
    conjSub_eq_self_iff.1 (conjSub_of_forall_commute fun a ha =>
      hKD b hb a (Subgroup.mem_sup_left ha))
  have hzN : z ∈ Subgroup.normalizer (P i : Set H) :=
    conjSub_eq_self_iff.1 (conjSub_of_forall_commute fun a ha =>
      commute_of_mem_lineGroup h.cls (hF.memP k) (hF.memP i) (hF.commuting_PP hik.symm) hz.1.1
        (le_lineGroup (right_mem_lineOf (hF.memP i)) ha))
  have hyN : y ∈ Subgroup.normalizer (P i : Set H) := by
    have hmem := (Subgroup.normalizer (P i : Set H)).mul_mem
      ((Subgroup.normalizer (P i : Set H)).mul_mem (conjSub_eq_self_iff.1 hc)
        ((Subgroup.normalizer (P i : Set H)).inv_mem hbN))
      ((Subgroup.normalizer (P i : Set H)).inv_mem hzN)
    rwa [show y * z * b * b⁻¹ * z⁻¹ = y by group] at hmem
  have hy' : y ∈ shortRootGroup Δ (Q i) (P i) (P k) (Q k) := by
    rwa [← shortRootGroup_swap_pairs (Q i) (P i) (P k) (Q k)]
  exact (hF.toPairFrame hik).eq_one_of_conjSub_eq h.cls (h.cls.noIsolated h.points h.rank)
    h.points (hq (P i) (hF.memP i)) hy' (conjSub_eq_self_iff.2 hyN)

private theorem exists_eq_mul_of_mem_map_heis_of_mem_sup (h : TransvectionHyp H Δ)
    (hML : MeetsLines Δ) (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A) (hF : IsFrame Δ P Q)
    (hFn : Nat.card F = (2 ^ n) ^ 2) (hcard : ∀ A ∈ Δ, Nat.card A = 2 ^ n)
    {θ θ' : SU (unitaryInvolution F 2 n) 3 →* H}
    (hθt : (su3Top (unitaryInvolution F 2 n)).map θ = P k) {i : Fin r} (hik : i ≠ k)
    (hθr' : θ'.range = residueGroup Δ P Q i)
    (hθt' : (su3Top (unitaryInvolution F 2 n)).map θ' = P i)
    (hθb' : (su3Bot (unitaryInvolution F 2 n)).map θ' = Q i) {b : H}
    (hb : b ∈ (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ)
    (hbU : b ∈ (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ' ⊔
      (shortRootGroup Δ (P i) (Q i) (Q k) (P k) ⊔
        shortRootGroup Δ (P i) (Q i) (P k) (Q k) ⊔ P i)) :
    ∃ z ∈ shortRootGroup Δ (P k) (Q k) (P i) (Q i),
      ∃ β ∈ (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ', b = z * β := by
  obtain ⟨y, hy, z, hz, β, hβ, hbyz⟩ :=
    hF.exists_eq_mul_mul_of_mem_map_heis_sup (k := i) (i := k) h hML hq hFn hcard hθr' hθt' hθb'
      hik.symm hbU
  have hbP : conjSub (P k) (y * z * β) = P k :=
    hbyz ▸ conjSub_eq_of_mem_map_heis (unitaryInvolution_involutive hFn) hθt hb
  have hy1 : y = 1 :=
    eq_one_of_conjSub_mul_mul_eq (k := i) (i := k) h hq hF hFn hθr' hik.symm hy hz hβ hbP
  refine ⟨z, ?_, β, hβ, by rw [hbyz, hy1, one_mul]⟩
  rwa [shortRootGroup_swap_pairs (P k) (Q k) (P i) (Q i)] at hz

section Certificates


private theorem eq_one_of_mem_map_heis_mul (h : TransvectionHyp H Δ) (hML : MeetsLines Δ)
    (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A) (hF : IsMaxFrame Δ P Q)
    (hFn : Nat.card F = (2 ^ n) ^ 2) (hcard : ∀ A ∈ Δ, Nat.card A = 2 ^ n)
    {θ θ' : SU (unitaryInvolution F 2 n) 3 →* H} (hθr : θ.range = residueGroup Δ P Q k)
    {i : Fin r} (hik : i ≠ k) (hns : ¬ IsSmallFrame Δ P Q i)
    (hθr' : θ'.range = residueGroup Δ P Q i) (hθk' : Odd (Nat.card θ'.ker))
    (hθt' : (su3Top (unitaryInvolution F 2 n)).map θ' = P i)
    (hθb' : (su3Bot (unitaryInvolution F 2 n)).map θ' = Q i)
    (hmem' : ∀ X : Subgroup H, X ∈ frameResidue Δ P Q i ↔
      ∃ g, X = (conjSub (su3Top (unitaryInvolution F 2 n)) g).map θ') {z β : H}
    (hz : z ∈ shortRootGroup Δ (P k) (Q k) (P i) (Q i))
    (hβ : β ∈ (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ')
    (hzβ : z * β ∈ (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ) : β = 1 := by
  haveI := h.finite
  have hKD := commuting_map_heis_of_ne (unitaryInvolution_involutive hFn) hθr hik
  have hQi : conjSub (conjSub (Q i) β) z = Q i := by
    rw [← conjSub_mul]
    exact conjSub_of_forall_commute fun a ha => hKD _ hzβ a (Subgroup.mem_sup_right ha)
  have hMeq : conjSub (Q i) β = conjSub (Q i) z⁻¹ := by
    rw [← Aux.conjSub_conjSub_inv (conjSub (Q i) β) z, hQi]
  have hMline : conjSub (Q i) β ∈ lineOf Δ (P k) (Q i) := by
    rw [hMeq]
    exact (mem_lineStab_iff.1 ((lineStab Δ (P k) (Q i)).inv_mem hz.2) (Q i)).2
      (right_mem_lineOf (hF.memQ i))
  have hMres : conjSub (Q i) β ∈ frameResidue Δ P Q i :=
    conjSub_mem_frameResidue h.cls (hF.toIsFrame.memQ_frameResidue i)
      (hθr' ▸ Subgroup.map_le_range θ' _ hβ)
  have hMQ : conjSub (Q i) β = Q i :=
    eq_of_commuting_of_not_commuting h.cls h.points (hF.memP k) (hF.memQ i)
      (hF.toIsFrame.Q_ne_P hik).symm (hF.toIsFrame.commuting_PQ hik.symm) hMline
      (right_mem_lineOf (hF.memQ i)) (hF.memQ k)
      (ModelRank.not_commuting_of_opposite (hF.opposite k).symm)
      (hMres.2 k hik.symm).2.symm (hF.toIsFrame.commuting_QQ hik.symm)
  exact (hF.existsUnique_conjSub_heis (k := i) h hML hq hns hFn hcard hθr' hθk' hθt' hθb' hmem'
    (hF.toIsFrame.memQ_frameResidue i) (hF.opposite i).1.symm).unique ⟨hβ, hMQ⟩
    ⟨Subgroup.one_mem _, conjSub_one _⟩

theorem IsMaxFrame.map_heis_sup_inf_map_heis_sup_le (h : TransvectionHyp H Δ)
    (hML : MeetsLines Δ) (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A) (hF : IsMaxFrame Δ P Q)
    (hFn : Nat.card F = (2 ^ n) ^ 2) (hcard : ∀ A ∈ Δ, Nat.card A = 2 ^ n)
    {θ : SU (unitaryInvolution F 2 n) 3 →* H} (hθr : θ.range = residueGroup Δ P Q k)
    (hθt : (su3Top (unitaryInvolution F 2 n)).map θ = P k)
    (hθb : (su3Bot (unitaryInvolution F 2 n)).map θ = Q k) {i : Fin r} (hik : i ≠ k)
    (hns : ¬ IsSmallFrame Δ P Q i) {θ' : SU (unitaryInvolution F 2 n) 3 →* H}
    (hθr' : θ'.range = residueGroup Δ P Q i) (hθk' : Odd (Nat.card θ'.ker))
    (hθt' : (su3Top (unitaryInvolution F 2 n)).map θ' = P i)
    (hθb' : (su3Bot (unitaryInvolution F 2 n)).map θ' = Q i)
    (hmem' : ∀ X : Subgroup H, X ∈ frameResidue Δ P Q i ↔
      ∃ g, X = (conjSub (su3Top (unitaryInvolution F 2 n)) g).map θ') :
    ((UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ ⊔
        (shortRootGroup Δ (P k) (Q k) (Q i) (P i) ⊔
          shortRootGroup Δ (P k) (Q k) (P i) (Q i) ⊔ P k)) ⊓
      ((UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ' ⊔
        (shortRootGroup Δ (P i) (Q i) (Q k) (P k) ⊔
          shortRootGroup Δ (P i) (Q i) (P k) (Q k) ⊔ P i)) ≤
      shortRootGroup Δ (P k) (Q k) (P i) (Q i) := by
  intro c hc
  obtain ⟨hck, hci⟩ := Subgroup.mem_inf.1 hc
  obtain ⟨y, hy, z, hz, b, hb, rfl⟩ :=
    hF.toIsFrame.exists_eq_mul_mul_of_mem_map_heis_sup h hML hq hFn hcard hθr hθt hθb hik hck
  have hcP : conjSub (P i) (y * z * b) = P i :=
    hF.toIsFrame.conjSub_eq_of_mem_map_heis_sup (k := i) (i := k) h.cls hFn hθt' hik.symm hci
  have hy1 : y = 1 := eq_one_of_conjSub_mul_mul_eq h hq hF.toIsFrame hFn hθr hik hy hz hb hcP
  subst hy1
  have hzi : z ∈ shortRootGroup Δ (P i) (Q i) (P k) (Q k) := by
    rwa [shortRootGroup_swap_pairs (P k) (Q k) (P i) (Q i)]
  have hbU := Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_right
    (Subgroup.mem_sup_left (Subgroup.mem_sup_right hzi)))) hci
  rw [one_mul, inv_mul_cancel_left] at hbU
  obtain ⟨z', hz', β, hβ, hbz⟩ :=
    exists_eq_mul_of_mem_map_heis_of_mem_sup h hML hq hF.toIsFrame hFn hcard hθt hik hθr' hθt'
      hθb' hb hbU
  have hβ1 : β = 1 :=
    eq_one_of_mem_map_heis_mul h hML hq hF hFn hcard hθr hik hns hθr' hθk' hθt' hθb' hmem' hz'
      hβ (hbz ▸ hb)
  rw [one_mul, hbz, hβ1, mul_one]
  exact Subgroup.mul_mem _ hz hz'

end Certificates

end CertificateFree

end CFSG.Timmesfeld.Transvection
