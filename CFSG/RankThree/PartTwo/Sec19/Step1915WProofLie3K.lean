module

public import CFSG.RankThree.PartTwo.Sec19.Step1915WProofLie3
public import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian
import CFSG.RankThree.PartTwo.Sec13.Item138ProofOmega
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.PartTwo.Sec19.Step1919NarrowRank
import CFSG.RankThree.PartTwo.Sec19.Step1915WProofLie9

public section

namespace CFSG.RankThree.PartTwo.Sec19.Step1915WProof

open Matrix CFSG.RankThree.PartTwo.Sec4 CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projImage projSL projSU)

section Heis

variable {π : Bool} {p f : ℕ} {K : Type} [Field K]

theorem cycThree_mul_diagTau_ne {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) :
    (cycThree : GL (Fin 3) K) * diagTau hτ ≠ diagTau hτ * cycThree := by
  intro h
  have hm := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 1 0) h
  simp [coe_cycThree, coe_diagTau, Matrix.mul_apply, Fin.sum_univ_three] at hm
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    norm_num at hτ
  apply hτ1
  have : τ * 1 = τ * τ := by rw [mul_one, ← sq]; exact hm
  exact (mul_left_cancel₀ hτ0 this).symm

theorem exists_heisPair (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {τ : K}
    (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) :
    ∃ dM cM : projImage (slPi π 3 (p ^ f) K),
      (dM : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (diagTau hτ) ∧
      (cM : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (cycThree : GL (Fin 3) K) ∧
      dM * cM = cM * dM ∧ orderOf dM = 3 ∧ orderOf cM = 3 ∧ cM ∉ Subgroup.zpowers dM := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  set dM : projImage (slPi π 3 (p ^ f) K) :=
    ⟨_, Subgroup.mem_map_of_mem _ (diagTau_mem_slPi hπ hq' hτ)⟩ with hdM
  set cM : projImage (slPi π 3 (p ^ f) K) :=
    ⟨_, Subgroup.mem_map_of_mem _ (cycThree_mem_slPi hπ)⟩ with hcM
  have hd3 : dM ^ 3 = 1 := Subtype.ext (by
    change ProjGenLinGroup.mk (diagTau hτ) ^ 3 = 1
    rw [← map_pow, diagTau_pow_three hτ, map_one])
  have hc3 : cM ^ 3 = 1 := Subtype.ext (by
    change ProjGenLinGroup.mk (cycThree : GL (Fin 3) K) ^ 3 = 1
    rw [← map_pow, cycThree_pow_three, map_one])
  have hd1 : dM ≠ 1 := fun h => mk_diagTau_ne_one hτ hτ1 (congrArg Subtype.val h)
  have hc1 : cM ≠ 1 := by
    intro h
    have h' : ProjGenLinGroup.mk (cycThree : GL (Fin 3) K) = 1 := congrArg Subtype.val h
    rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at h'
    obtain ⟨u, hu⟩ := h'
    have hm := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) hu
    simp [GeneralLinearGroup.coe_scalar, coe_cycThree, Matrix.scalar_apply] at hm
  refine ⟨dM, cM, rfl, rfl, Subtype.ext (mk_diagTau_cycThree hτ), orderOf_eq_prime hd3 hd1,
    orderOf_eq_prime hc3 hc1, ?_⟩
  intro hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hk' : ProjGenLinGroup.mk ((diagTau hτ) ^ k) =
      ProjGenLinGroup.mk (cycThree : GL (Fin 3) K) := by
    rw [map_zpow]
    exact congrArg Subtype.val hk
  rw [ProjGenLinGroup.mk_eq_mk_iff] at hk'
  obtain ⟨u, hu⟩ := hk'
  apply cycThree_mul_diagTau_ne hτ hτ1
  rw [← hu]
  have h1 := (Commute.zpow_left (Commute.refl (diagTau hτ)) k).eq
  have h2 := GeneralLinearGroup.scalar_commute (n := Fin 3) u (diagTau hτ)
  calc diagTau hτ ^ k * GeneralLinearGroup.scalar (Fin 3) u * diagTau hτ =
      diagTau hτ ^ k * (diagTau hτ * GeneralLinearGroup.scalar (Fin 3) u) := by
        rw [mul_assoc, h2]
    _ = diagTau hτ * (diagTau hτ ^ k * GeneralLinearGroup.scalar (Fin 3) u) := by
        rw [← mul_assoc, h1, mul_assoc]

theorem pow_three_eq_one_of_projImage [Finite K] (hK : PiField π p f K)
    (hq : ModThree π (p ^ f))
    (h9 : (Nat.card (projImage (slPi π 3 (p ^ f) K))).factorization 3 = 2)
    {m : projImage (slPi π 3 (p ^ f) K)} (hm : ∃ k : ℕ, m ^ 3 ^ k = 1) : m ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (ProjGenLinGroup (Fin 3) K) := by
    unfold ProjGenLinGroup
    infer_instance
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  obtain ⟨dM, cM, -, -, hdc, hdo, hco, hcd⟩ := exists_heisPair hK hq hτ hτ1
  set E := Subgroup.zpowers dM ⊔ Subgroup.zpowers cM with hE
  have hE9 : Nat.card E = 9 := by
    rw [hE, Step1919NarrowRank.card_sup_zpowers_of_orderOf _ hco hcd (by
      rintro _ ⟨k, rfl⟩
      exact ((Commute.zpow_left hdc k).eq)), Nat.card_zpowers, hdo]
  have hEexp : ∀ x ∈ E, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨i, j, rfl⟩ := exists_zpow_mul_of_mem_sup hdc hx
    have hd3 : dM ^ 3 = 1 := by simpa [hdo] using pow_orderOf_eq_one dM
    have hc3 : cM ^ 3 = 1 := by simpa [hco] using pow_orderOf_eq_one cM
    rw [(Commute.zpow_zpow hdc i j).mul_pow, ← zpow_natCast, ← zpow_natCast,
      ← _root_.zpow_mul, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, mul_comm (j : ℤ),
      _root_.zpow_mul]
    simp [hd3, hc3]
  have hEcard : Nat.card E = 3 ^ (Nat.card (projImage (slPi π 3 (p ^ f) K))).factorization 3 := by
    rw [hE9, h9]
    norm_num
  set S₀ := Sylow.ofCard E hEcard with hS₀
  have hm3 : IsPGroup 3 (Subgroup.zpowers m) := by
    obtain ⟨k, hk⟩ := hm
    rintro ⟨_, n, rfl⟩
    refine ⟨k, Subtype.ext ?_⟩
    change (m ^ n) ^ 3 ^ k = 1
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hk,
      _root_.one_zpow]
  obtain ⟨S, hmS⟩ := hm3.exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq (projImage (slPi π 3 (p ^ f) K)) S₀ S
  have hmS' : m ∈ (S : Subgroup _) := hmS (Subgroup.mem_zpowers m)
  rw [← hk, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hmS'
  obtain ⟨x, hxE, rfl⟩ := hmS'
  rw [MulAut.smul_def, MulAut.conj_apply, conj_pow, hEexp x hxE]
  group

end Heis

theorem ks1917Lie3Sylow : KS1917Lie3Sylow := by
  intro X _ _ p e _ he hiso h91 h98 S
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h9 : (Nat.card X).factorization 3 = 2 :=
    Sec13.Item138Proof.factorization_card_three_eq_two he hiso (by omega)
  refine ⟨by rw [Sylow.card_eq_multiplicity, h9]; norm_num, ?_⟩
  obtain ⟨π, K, _, hK, hq, ⟨φ⟩⟩ := Sec13.exists_projImage_model he hiso
  have := hK.finite
  have h9' : (Nat.card (projImage (slPi π 3 (p ^ e) K))).factorization 3 = 2 := by
    rw [← Nat.card_congr φ.toEquiv, h9]
  intro s hs
  have hs3 : ∃ k : ℕ, φ s ^ 3 ^ k = 1 := by
    obtain ⟨k, hk⟩ := S.isPGroup' ⟨s, hs⟩
    refine ⟨k, ?_⟩
    rw [← map_pow]
    have : s ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    rw [this, map_one]
  have h := pow_three_eq_one_of_projImage hK hq h9' hs3
  exact φ.injective (by rw [map_pow, h, map_one])

theorem ks1917Lie3Fusion : KS1917Lie3Fusion := by
  intro X _ _ p e _ he hiso h91 h98 S x hxS hx1
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hS9, hS3⟩ := ks1917Lie3Sylow X p e he hiso h91 h98 S
  have h9 : (Nat.card X).factorization 3 = 2 :=
    Sec13.Item138Proof.factorization_card_three_eq_two he hiso (by omega)
  obtain ⟨π, K, _, hK, hq, ⟨φ⟩⟩ := Sec13.exists_projImage_model he hiso
  have := hK.finite
  have : Finite (ProjGenLinGroup (Fin 3) K) := by
    unfold ProjGenLinGroup
    infer_instance
  have hπ : π = false → UnitaryFieldData p e K := fun h => by subst h; exact hK.unitary
  set M := projImage (slPi π 3 (p ^ e) K) with hM
  have h9M : (Nat.card M).factorization 3 = 2 := by rw [← Nat.card_congr φ.toEquiv, h9]
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  obtain ⟨dM, cM, hdM, hcM, hdc, hdo, hco, hcd⟩ := exists_heisPair hK hq hτ hτ1
  set E := Subgroup.zpowers dM ⊔ Subgroup.zpowers cM with hE
  have hE9 : Nat.card E = 9 := by
    rw [hE, Step1919NarrowRank.card_sup_zpowers_of_orderOf _ hco hcd (by
      rintro _ ⟨k, rfl⟩
      exact ((Commute.zpow_left hdc k).eq)), Nat.card_zpowers, hdo]
  set S₀ := Sylow.ofCard E (by rw [hE9, h9M]; norm_num) with hS₀
  have hS'card : Nat.card (S.map φ.toMonoidHom) = 3 ^ (Nat.card M).factorization 3 := by
    rw [Subgroup.card_map_of_injective φ.injective, hS9, h9M]
    norm_num
  set S' := Sylow.ofCard (S.map φ.toMonoidHom) hS'card with hS'
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq M S₀ S'
  have hmemS' : ∀ w ∈ E, k * w * k⁻¹ ∈ (S.map φ.toMonoidHom : Subgroup M) := by
    intro w hw
    have : k * w * k⁻¹ ∈ ((k • S₀ : Sylow 3 M) : Subgroup M) := by
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
      exact ⟨w, hw, by simp [MulAut.smul_def, MulAut.conj_apply]⟩
    rw [hk] at this
    exact this
  set x₁ := φ.symm (k * dM * k⁻¹) with hx₁
  set x₂ := φ.symm (k * cM * k⁻¹) with hx₂
  have hxS' : ∀ w ∈ E, φ.symm (k * w * k⁻¹) ∈ (S : Subgroup X) := by
    intro w hw
    obtain ⟨y, hy, hye⟩ := hmemS' w hw
    have : φ.symm (k * w * k⁻¹) = y := by
      rw [← hye]
      exact φ.symm_apply_apply y
    rw [this]
    exact hy
  have hx₁S : x₁ ∈ (S : Subgroup X) := hxS' _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers dM))
  have hx₂S : x₂ ∈ (S : Subgroup X) := hxS' _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers cM))
  have hx₁₂ : x₁ * x₂ = x₂ * x₁ := by
    apply φ.injective
    rw [map_mul, map_mul, hx₁, hx₂, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    calc k * dM * k⁻¹ * (k * cM * k⁻¹) = k * (dM * cM) * k⁻¹ := by group
      _ = k * (cM * dM) * k⁻¹ := by rw [hdc]
      _ = k * cM * k⁻¹ * (k * dM * k⁻¹) := by group
  have hx₂o : orderOf x₂ = 3 := by
    rw [hx₂, MulEquiv.orderOf_eq, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hco]
  have hx₂x₁ : x₂ ∉ Subgroup.zpowers x₁ := by
    intro h
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp h
    apply hcd
    refine Subgroup.mem_zpowers_iff.mpr ⟨j, ?_⟩
    have h1 := congrArg φ hj
    rw [map_zpow, hx₁, hx₂, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, conj_zpow]
      at h1
    have h2 := congrArg (fun w => k⁻¹ * w * k) h1
    simpa [mul_assoc] using h2
  have hsup9 : Nat.card (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ : Subgroup X) = 9 := by
    rw [Step1919NarrowRank.card_sup_zpowers_of_orderOf _ hx₂o hx₂x₁ (by
      rintro _ ⟨j, rfl⟩
      exact ((Commute.zpow_left hx₁₂ j).eq)), Nat.card_zpowers, hx₁,
      MulEquiv.orderOf_eq, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hdo]
  have hSeq : (S : Subgroup X) = Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ := by
    refine (Subgroup.eq_of_le_of_card_ge (sup_le (Subgroup.zpowers_le.mpr hx₁S)
      (Subgroup.zpowers_le.mpr hx₂S)) (by rw [hsup9, hS9])).symm
  obtain ⟨ĝ, hĝ, hĝk⟩ := k.2
  set e : (⊤ : Subgroup X) ≃* M := Subgroup.topEquiv.trans φ with he
  have he₁ : ((e ⟨x₁, Subgroup.mem_top x₁⟩ : M) : ProjGenLinGroup (Fin 3) K) =
      ProjGenLinGroup.mk (ĝ * diagTau hτ * ĝ⁻¹) := by
    rw [he, MulEquiv.trans_apply, Subgroup.topEquiv_apply, hx₁, MulEquiv.apply_symm_apply,
      map_mul, map_mul, map_inv, hĝk]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hdM]
  have he₂ : ((e ⟨x₂, Subgroup.mem_top x₂⟩ : M) : ProjGenLinGroup (Fin 3) K) =
      ProjGenLinGroup.mk (ĝ * cycThree * ĝ⁻¹) := by
    rw [he, MulEquiv.trans_apply, Subgroup.topEquiv_apply, hx₂, MulEquiv.apply_symm_apply,
      map_mul, map_mul, map_inv, hĝk]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hcM]
  have htr := transitive_of_normal_form hK hq e hτ hτ1 (slPi_le_glPi hπ hĝ)
    (Subgroup.mem_top x₁) (Subgroup.mem_top x₂) he₁ he₂
  obtain ⟨y, hyS, hyx⟩ : ∃ y ∈ (S : Subgroup X), y ∉ Subgroup.zpowers x := by
    by_contra h
    push Not at h
    have hle : (S : Subgroup X) ≤ Subgroup.zpowers x := h
    have h1 := Subgroup.card_le_of_le hle
    rw [hS9, Nat.card_zpowers] at h1
    have h2 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one (hS3 x hxS)
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  have hy1 : y ≠ 1 := fun h => hyx (h ▸ Subgroup.one_mem _)
  rw [hSeq] at hxS hyS
  obtain ⟨n, ⟨-, hnN⟩, hnxy⟩ := htr x hxS hx1 y hyS hy1
  exact ⟨n, hSeq ▸ hnN, hnxy ▸ hyx⟩

theorem step1917Z2KLie3_of_aut (hAut : KS1917Lie3AutCent) : Step1917Z2KLie3 :=
  step1917Z2KLie3_of ks1917Lie3Sylow ks1917Lie3Fusion hAut

end CFSG.RankThree.PartTwo.Sec19.Step1915WProof
