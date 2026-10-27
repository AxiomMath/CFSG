module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148BFTFrameU

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148B

open Matrix CFSG.RankThree.PartTwo.Sec4 CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)

variable {f : ℕ} {F : Type} [Field F] {hU : UnitaryFieldData 2 f F}

@[expose] noncomputable def frameTorus (hU : UnitaryFieldData 2 f F) {W : GL (Fin 3) F}
    (hW : W ∈ unitaryIsom3 hU) (m : ℕ) : Subgroup (unitaryPSU hU 3) :=
  (diagTorusU hU m).map (psuConj hU ⟨W, hW⟩).toMonoidHom

theorem mem_frameTorus {W : GL (Fin 3) F} {hW : W ∈ unitaryIsom3 hU} {m : ℕ}
    {a : unitaryPSU hU 3} :
    a ∈ frameTorus hU hW m ↔ (psuConj hU ⟨W, hW⟩)⁻¹ a ∈ diagTorusU hU m := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    rwa [MulEquiv.coe_toMonoidHom, MulAut.inv_apply_self]
  · intro h
    exact ⟨_, h, by rw [MulEquiv.coe_toMonoidHom, MulAut.apply_inv_self]⟩

theorem not_three_dvd_card_frameTorus {W : GL (Fin 3) F} (hW : W ∈ unitaryIsom3 hU) {m : ℕ}
    (hm : Nat.Coprime m 3) : ¬ 3 ∣ Nat.card (frameTorus hU hW m) := by
  rw [frameTorus, Subgroup.card_map_of_injective (f := (psuConj hU ⟨W, hW⟩).toMonoidHom)
    (psuConj hU ⟨W, hW⟩).injective]
  exact not_three_dvd_card_diagTorusU hm

theorem exists_cycThree_pow_of_unitaryProj_conj {τ : F} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {M D : unitarySU 2 f F 3} (hD : (D : GL (Fin 3) F) = diagTau hτ)
    (h : unitaryProj hU 3 (M * D * M⁻¹) = unitaryProj hU 3 D) :
    ∃ k : ℕ, k < 3 ∧ ∃ a b e : Fˣ, (M : GL (Fin 3) F) = cycThree ^ k * diagUnits a b e := by
  obtain ⟨ζ, hζ⟩ := exists_scalar_of_unitaryProj_eq (hU := hU) h.symm
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hD] at hζ
  obtain ⟨k, hk, -, a, b, e, he⟩ := Ronan148V.exists_cycThree_pow_mul_of_conj hτ hτ1 hζ
  exact ⟨k, hk, a, b, e, he⟩

variable {τ : F} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) (hf : Odd f)

@[expose] noncomputable def dPSU (hU : UnitaryFieldData 2 f F) (hf : Odd f) : unitaryPSU hU 3 :=
  ((⟨diagTau hτ, diagTau_mem_unitarySU hU hf hτ⟩ : unitarySU 2 f F 3) : unitaryPSU hU 3)

include hτ1 in
theorem conj_mem_frameTorus_of_commute {W : GL (Fin 3) F} (hW : W ∈ unitaryIsom3 hU) {m : ℕ}
    {x : unitaryPSU hU 3} (hx : x * psuConj hU ⟨W, hW⟩ (dPSU hτ hU hf) =
      psuConj hU ⟨W, hW⟩ (dPSU hτ hU hf) * x) {a : unitaryPSU hU 3}
    (ha : a ∈ frameTorus hU hW m) : x * a * x⁻¹ ∈ frameTorus hU hW m := by
  set Γ := psuConj hU ⟨W, hW⟩ with hΓ
  obtain ⟨M, hM⟩ := unitaryProj_surjective hU 3 (Γ⁻¹ x)
  have hxM : x = Γ (unitaryProj hU 3 M) := by rw [hM, MulAut.apply_inv_self]
  have hcomm : unitaryProj hU 3 (M * ⟨diagTau hτ, diagTau_mem_unitarySU hU hf hτ⟩ * M⁻¹) =
      unitaryProj hU 3 ⟨diagTau hτ, diagTau_mem_unitarySU hU hf hτ⟩ := by
    apply Γ.injective
    rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, ← hxM]
    change x * Γ (dPSU hτ hU hf) * x⁻¹ = Γ (dPSU hτ hU hf)
    rw [hx, mul_inv_cancel_right]
  obtain ⟨k, hk, a', b', e', hke⟩ := exists_cycThree_pow_of_unitaryProj_conj hτ hτ1 rfl hcomm
  have hA : cycThree ^ k * diagUnits a' b' e' ∈ unitaryIsom3 hU := by
    rw [← hke]; exact unitarySU_le_unitaryIsom3 M.2
  rw [mem_frameTorus] at ha ⊢
  have hconj : Γ⁻¹ (x * a * x⁻¹) = psuConj hU ⟨_, hA⟩ (Γ⁻¹ a) := by
    rw [map_mul, map_mul, map_inv, ← hM]
    have h1 : psuConj hU ⟨_, hA⟩ =
        psuConj hU ⟨(M : GL (Fin 3) F), unitarySU_le_unitaryIsom3 M.2⟩ :=
      congrArg (psuConj hU) (Subtype.ext hke.symm)
    rw [h1, ← conj_mk_eq_psuConj, MulAut.conj_apply]
    rfl
  rw [hconj]
  exact psuConj_mem_diagTorusU hk hA ha

include hτ1 in
theorem aut_mem_frameTorus (ρ : F ≃+* F) (hρ : ρ τ = τ) {W : GL (Fin 3) F}
    (hW : W ∈ unitaryIsom3 hU) {m : ℕ} {M : GL (Fin 3) F} (hM : M ∈ unitaryIsom3 hU)
    (α : unitaryPSU hU 3 → unitaryPSU hU 3)
    (hα : ∀ y, α (psuConj hU ⟨W, hW⟩ y) =
      psuConj hU ⟨W, hW⟩ (psuConj hU ⟨M, hM⟩ (psuField hU ρ y)))
    (hαb : α (psuConj hU ⟨W, hW⟩ (dPSU hτ hU hf)) = psuConj hU ⟨W, hW⟩ (dPSU hτ hU hf))
    {a : unitaryPSU hU 3} (ha : a ∈ frameTorus hU hW m) : α a ∈ frameTorus hU hW m := by
  set Γ := psuConj hU ⟨W, hW⟩ with hΓ
  have hfd : psuField hU ρ (dPSU hτ hU hf) = dPSU hτ hU hf := by
    rw [dPSU, psuField_mk]
    congr 1
    apply Subtype.ext
    rw [coe_suField]
    exact glAut_diagTau ρ hτ hρ
  have hcd : psuConj hU ⟨M, hM⟩ (dPSU hτ hU hf) = dPSU hτ hU hf := by
    rw [hα, hfd] at hαb
    exact Γ.injective hαb
  have hMd : unitaryProj hU 3 (⟨M * diagTau hτ * M⁻¹,
      conj_mem_unitarySU hM (diagTau_mem_unitarySU hU hf hτ)⟩ : unitarySU 2 f F 3) =
      unitaryProj hU 3 ⟨diagTau hτ, diagTau_mem_unitarySU hU hf hτ⟩ := by
    calc unitaryProj hU 3 (⟨M * diagTau hτ * M⁻¹,
          conj_mem_unitarySU hM (diagTau_mem_unitarySU hU hf hτ)⟩ : unitarySU 2 f F 3)
        = psuConj hU ⟨M, hM⟩ (dPSU hτ hU hf) := by rw [dPSU, psuConj_mk]; rfl
      _ = dPSU hτ hU hf := hcd
      _ = _ := rfl
  obtain ⟨ζ, hζ⟩ := exists_scalar_of_unitaryProj_eq (hU := hU) hMd.symm
  change M * diagTau hτ * M⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ * diagTau hτ at hζ
  obtain ⟨k, hk, -, a', b', e', hke⟩ := Ronan148V.exists_cycThree_pow_mul_of_conj hτ hτ1 hζ
  have hA : cycThree ^ k * diagUnits a' b' e' ∈ unitaryIsom3 hU := by rw [← hke]; exact hM
  rw [mem_frameTorus] at ha ⊢
  have heq : α a = Γ (psuConj hU ⟨M, hM⟩ (psuField hU ρ (Γ⁻¹ a))) := by
    rw [← hα, MulAut.apply_inv_self]
  rw [heq, MulAut.inv_apply_self,
    show psuConj hU ⟨M, hM⟩ = psuConj hU ⟨_, hA⟩ from congrArg (psuConj hU) (Subtype.ext hke)]
  exact psuConj_mem_diagTorusU hk hA (psuField_mem_diagTorusU ρ ha)

include hτ1 in
theorem exists_fixed_frameTorus (ρ : F ≃+* F) (hρ3 : ∀ x, ρ (ρ (ρ x)) = x) {m : ℕ}
    (hm : Nat.Coprime m 3) {lam : Fˣ} (hlm : lam ^ m = 1) (hlN : hU.norm (lam : F) = 1)
    (hρl : ρ lam ≠ lam) {W : GL (Fin 3) F} (hW : W ∈ unitaryIsom3 hU) {N : GL (Fin 3) F}
    (hN : N ∈ unitaryIsom3 hU) (θ : unitaryPSU hU 3 → unitaryPSU hU 3)
    (hθ : ∀ y, θ (psuConj hU ⟨W, hW⟩ y) =
      psuConj hU ⟨W, hW⟩ (psuConj hU ⟨N, hN⟩ (psuField hU ρ y)))
    {ζ : Fˣ} (hζ : N * diagTau hτ * N⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ * diagTau hτ)
    (hζ1 : ζ ≠ 1) : ∃ u ∈ frameTorus hU hW m, u ≠ 1 ∧ θ u = u := by
  obtain ⟨k, hk3, hkζ, a', b', e', hke⟩ := Ronan148V.exists_cycThree_pow_mul_of_conj hτ hτ1 hζ
  have hk : k = 1 ∨ k = 2 := by
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | h | h
    · exact absurd (Units.ext (by rw [hkζ, mul_zero, pow_zero, Units.val_one])) hζ1
    · exact Or.inl h
    · exact Or.inr h
  have hA : cycThree ^ k * diagUnits a' b' e' ∈ unitaryIsom3 hU := by rw [← hke]; exact hN
  obtain ⟨uW, huW, huW1, hfix⟩ := exists_fixed_diagTorusU hm hk hA ρ hρ3 hlm hlN hρl
  refine ⟨psuConj hU ⟨W, hW⟩ uW, ⟨uW, huW, rfl⟩, fun h1 => huW1 ?_, ?_⟩
  · exact (psuConj hU ⟨W, hW⟩).injective (h1.trans (map_one _).symm)
  · rw [hθ, show psuConj hU ⟨N, hN⟩ = psuConj hU ⟨_, hA⟩ from
      congrArg (psuConj hU) (Subtype.ext hke), hfix]

theorem eq_one_of_commute_frameTorus {W : GL (Fin 3) F} (hW : W ∈ unitaryIsom3 hU) {m k : ℕ}
    (hm : Nat.Coprime m 3) (hk : k = 1 ∨ k = 2) {w₀ w₁ w₂ : Fˣ} {Mz : unitarySU 2 f F 3}
    (hMz : (Mz : GL (Fin 3) F) = cycThree ^ k * diagUnits w₀ w₁ w₂) {a : unitaryPSU hU 3}
    (ha : a ∈ frameTorus hU hW m)
    (hc : a * psuConj hU ⟨W, hW⟩ (unitaryProj hU 3 Mz) =
      psuConj hU ⟨W, hW⟩ (unitaryProj hU 3 Mz) * a) : a = 1 := by
  rw [mem_frameTorus] at ha
  have h1 := eq_one_of_commute_cycThree_powU hm hk hMz ha (by
    apply (psuConj hU ⟨W, hW⟩).injective
    rw [map_mul, map_mul, MulAut.apply_inv_self, hc])
  rw [← MulAut.apply_inv_self _ (psuConj hU ⟨W, hW⟩) a, h1, map_one]

end CFSG.RankThree.PartTwo.Sec4.Ronan148B
