module

public import CFSG.RankThree.PartTwo.KFacts.KS163P6Rigid
public import CFSG.RankThree.PartTwo.Sec14.Item14Res8ProofHessModel
import CFSG.RankThree.PartTwo.Sec14.Item14Res8ProofHessConj
import CFSG.RankThree.PartTwo.Sec19.Item19ResProofAutCent
import CFSG.RankThree.PartTwo.Sec13.Item138ProofOmega

public section

namespace CFSG.RankThree.PartTwo.KFacts.KF163L3

open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec14.Res8Hess
open Matrix (ProjGenLinGroup)

theorem transitive_of_card_nine {X : Type} [Group X] [Finite X] {p f : ℕ} [Fact p.Prime]
    (hf : 1 ≤ f) (hiso : Sec4.IsoLThreePi X p f) (h9 : ¬ (p ^ f % 9 = 1 ∨ p ^ f % 9 = 8))
    {E : Subgroup X} (hE9 : Nat.card E = 9) :
    ∀ y₀ ∈ E, y₀ ≠ 1 → ∀ y₁ ∈ E, y₁ ≠ 1 →
      ∃ w ∈ Subgroup.normalizer (E : Set X), w * y₀ * w⁻¹ = y₁ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfac : (Nat.card X).factorization 3 = 2 :=
    Sec13.Item138Proof.factorization_card_three_eq_two hf hiso h9
  have h91 : p ^ f % 9 ≠ 1 := fun h => h9 (Or.inl h)
  have h98 : p ^ f % 9 ≠ 8 := fun h => h9 (Or.inr h)
  have hcard : Nat.card E = 3 ^ (Nat.card X).factorization 3 := by
    rw [hE9, hfac]
    norm_num
  set S : Sylow 3 X := Sylow.ofCard E hcard with hS
  have hSE : (S : Subgroup X) = E := by
    rw [hS]
    exact Sylow.coe_ofCard E hcard
  intro y₀ hy₀ hy₀1 y₁ hy₁ hy₁1
  obtain ⟨w, hw, hwy⟩ := Sec19.Item19ResProof.transitive_sylow hf hiso h91 h98 S y₀
    (hSE.symm ▸ hy₀) hy₀1 y₁ (hSE.symm ▸ hy₁) hy₁1
  exact ⟨w, hSE ▸ hw, hwy⟩

theorem exists_le_thetaC_comm {X : Type} [Group X] [Finite X] {p f : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hiso : Sec4.IsoLThreePi X p f)
    (h9 : ¬ (p ^ f % 9 = 1 ∨ p ^ f % 9 = 8)) {E : Subgroup X}
    (hEe : CFSG.Open.IsElemAbelian 3 E) (hE9 : Nat.card E = 9) {Y : Subgroup X}
    (hY3 : ¬ 3 ∣ Nat.card Y) (hEY : E ≤ Subgroup.normalizer (Y : Set X)) :
    ∃ x ∈ E, x ≠ 1 ∧ Y ≤ Sec14.Res8Hess.thetaC x ∧
      ∀ a ∈ Sec14.Res8Hess.thetaC x, ∀ b ∈ Sec14.Res8Hess.thetaC x, a * b = b * a := by
  have htr := transitive_of_card_nine hf hiso h9 hE9
  obtain ⟨π, K, _, hK, hq, τ, hτ, hτ1, dM, cM, hdM, hcM, hdc, hdo, hco, hcd, Φ, hΦE⟩ :=
    exists_hessian_equiv hf hiso hEe hE9 htr
  have := hK.finite
  have : Finite (ProjGenLinGroup (Fin 3) K) := by
    unfold ProjGenLinGroup
    infer_instance
  set Ê := Subgroup.zpowers dM ⊔ Subgroup.zpowers cM with hÊ
  have hΦE' : ∀ w ∈ Ê, Φ w ∈ E := fun w hw => hΦE ▸ ⟨w, hw, rfl⟩
  set Y' := Y.map Φ.symm.toMonoidHom with hY'
  have hY'3 : ¬ 3 ∣ Nat.card Y' := by
    rw [hY', Subgroup.card_map_of_injective Φ.symm.injective]
    exact hY3
  have hÊY' : Ê ≤ Subgroup.normalizer (Y' : Set (projImage (slPi π 3 (p ^ f) K))) := by
    intro w hw
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨Φ w * y * (Φ w)⁻¹, (Subgroup.mem_normalizer_iff.mp (hEY (hΦE' w hw)) y).mp hy, ?_⟩
    change Φ.symm (Φ w * y * (Φ w)⁻¹) = w * Φ.symm y * w⁻¹
    rw [map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
  obtain ⟨b, hbÊ, hb1, hY'b⟩ :=
    le_thetaC_model hK hp2 hτ hτ1 hq hdM hcM hdc hdo hco hcd hY'3 hÊY'
  have hd1 : dM ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hdo
    omega
  have hbcomm := thetaC_comm hK hp2 hτ hτ1 hq hdM hcM hd1 hbÊ hb1
  refine ⟨Φ b, hΦE' b hbÊ, ?_, ?_, ?_⟩
  · intro h
    apply hb1
    apply Φ.injective
    rw [h, map_one]
  · intro y hy
    have h1 : Φ.symm y ∈ thetaC b := hY'b ⟨y, hy, rfl⟩
    have h2 : Φ (Φ.symm y) ∈ (thetaC b).map Φ.toMonoidHom := ⟨_, h1, rfl⟩
    rw [thetaC_map_equiv, MulEquiv.apply_symm_apply] at h2
    exact h2
  · intro a ha c hc
    have ha' : Φ.symm a ∈ thetaC b := by
      rw [← Subgroup.mem_map_equiv, thetaC_map_equiv]
      exact ha
    have hc' : Φ.symm c ∈ thetaC b := by
      rw [← Subgroup.mem_map_equiv, thetaC_map_equiv]
      exact hc
    exact Φ.symm.injective (by rw [map_mul, map_mul]; exact hbcomm _ ha' _ hc')

theorem map_eq_of_le_thetaC {X : Type} [Group X] [Finite X] {E D : Subgroup X}
    (hD : IsMaxInvTwo E D) {x : X} (hxE : x ∈ E) (hDx : D ≤ Sec14.Res8Hess.thetaC x)
    (hcomm : ∀ a ∈ Sec14.Res8Hess.thetaC x, ∀ b ∈ Sec14.Res8Hess.thetaC x, a * b = b * a)
    (σ : MulAut X) (hσ : ∀ e ∈ E, σ e = e) : D.map σ.toMonoidHom = D := by
  set σD := D.map σ.toMonoidHom with hσD
  have hσDx : σD ≤ thetaC x := by
    calc σD = D.map σ.toMonoidHom := hσD
      _ ≤ (thetaC x).map σ.toMonoidHom := Subgroup.map_mono hDx
      _ = thetaC (σ x) := thetaC_map_equiv σ x
      _ = thetaC x := by rw [hσ x hxE]
  have hσD2 : IsPGroup 2 σD := by
    rw [hσD]
    exact hD.1.1.map σ.toMonoidHom
  have hEσD : E ≤ Subgroup.normalizer (σD : Set X) := by
    intro e he
    refine Subgroup.mem_normalizer_fintype fun s hs => ?_
    rw [hσD] at hs ⊢
    obtain ⟨d, hd, hds⟩ := hs
    rw [← hds]
    have h1 : e * d * e⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp (hD.1.2 he) d).mp hd
    have h2 : σ (e * d * e⁻¹) = e * σ d * e⁻¹ := by
      rw [map_mul, map_mul, map_inv, hσ e he]
    refine ⟨e * d * e⁻¹, h1, ?_⟩
    simpa using h2
  have hDσD : D ≤ Subgroup.normalizer (σD : Set X) := by
    intro d hd
    refine Subgroup.mem_normalizer_fintype fun s hs => ?_
    have hsx : s ∈ thetaC x := hσDx hs
    have hdx : d ∈ thetaC x := hDx hd
    have h : d * s * d⁻¹ = s := by
      rw [hcomm d hdx s hsx]
      group
    rw [h]
    exact hs
  have hsup2 : IsPGroup 2 (D ⊔ σD : Subgroup X) := hD.1.1.to_sup_of_normal_right' hσD2 hDσD
  have hEN : E ≤ Subgroup.normalizer ((D ⊔ σD : Subgroup X) : Set X) := fun e he =>
    Subgroup.inf_normalizer_le_normalizer_sup D σD ⟨hD.1.2 he, hEσD he⟩
  have hle : D ⊔ σD ≤ D := hD.2 ⟨hsup2, hEN⟩ le_sup_left
  have hσDle : σD ≤ D := le_sup_right.trans hle
  refine Subgroup.eq_of_le_of_card_ge hσDle ?_
  rw [hσD, Subgroup.card_map_of_injective σ.injective]

end CFSG.RankThree.PartTwo.KFacts.KF163L3

namespace CFSG.RankThree.PartTwo.KFacts

theorem ks163P6NormL3 : KS163P6NormL3 := by
  intro L _ _ p f _ hp2 hf hiso h9 E hEe hE9 D hD σ hσ _
  have hD3 : ¬ 3 ∣ Nat.card D := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hD.1.1
    rw [hk]
    exact fun h => absurd (Nat.prime_three.dvd_of_dvd_pow h) (by norm_num)
  obtain ⟨x, hxE, -, hDx, hcomm⟩ :=
    KF163L3.exists_le_thetaC_comm hp2 hf hiso h9 hEe hE9 hD3 hD.1.2
  exact KF163L3.map_eq_of_le_thetaC hD hxE hDx hcomm σ hσ

theorem ks163P6Norm :
    KS163P6Norm :=
  ks163P6Norm_of_l3 ks163P6NormL3

end CFSG.RankThree.PartTwo.KFacts
