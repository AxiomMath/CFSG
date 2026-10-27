module

public import CFSG.LocalAnalysis.StandardType.GGSixOddIndexAut
public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionRank

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Good

variable {H : Type*} [Group H]

@[expose] def GGGoodAut (r : H) (σ : MulAut H) : Prop :=
  (∀ Q : Subgroup H, (∀ q ∈ Q, σ q = q) → IsPGroup 2 Q →
      (∀ y : H, σ y = y → ∀ q ∈ Q, y * q * y⁻¹ ∈ Q) → Q = ⊥) ∧
    ∃ g : H, σ (g * r * g⁻¹) = g * r * g⁻¹ ∧
      ∃ a : H, σ a = a ∧ a * (g * r * g⁻¹) = g * r * g⁻¹ * a ∧ a ≠ 1 ∧ Odd (orderOf a)

theorem ggGoodOuterAut_iff {G : Type*} [Group G] (G₀ : Subgroup G) (r : G₀) (σ : MulAut G₀) :
    GGGoodOuterAut G₀ r σ ↔ GGGoodAut r σ :=
  Iff.rfl

theorem GGGoodAut.congr {H' : Type*} [Group H'] (Θ : H ≃* H') {r : H} {σ : MulAut H}
    (h : GGGoodAut r σ) : GGGoodAut (Θ r) (MulAut.congr Θ σ) := by
  have happ : ∀ x : H', MulAut.congr Θ σ x = Θ (σ (Θ.symm x)) := fun _ => rfl
  obtain ⟨hO, g, hg, a, ha, har, ha1, hao⟩ := h
  refine ⟨fun Q' hfix hQ' hnorm => ?_, Θ g, ?_, Θ a, ?_, ?_, ?_, ?_⟩
  · have hQ := hO (Q'.comap Θ.toMonoidHom)
      (fun q hq => Θ.injective (by
        have := hfix (Θ q) hq
        rwa [happ, MulEquiv.symm_apply_apply] at this))
      (hQ'.comap_of_injective Θ.toMonoidHom Θ.injective)
      (fun y hy q hq => by
        change Θ (y * q * y⁻¹) ∈ Q'
        rw [map_mul, map_mul, map_inv]
        exact hnorm (Θ y) (by rw [happ, MulEquiv.symm_apply_apply, hy]) (Θ q) hq)
    rw [Subgroup.eq_bot_iff_forall]
    intro q' hq'
    have hmem : Θ.symm q' ∈ Q'.comap Θ.toMonoidHom := by
      change Θ (Θ.symm q') ∈ Q'
      rwa [MulEquiv.apply_symm_apply]
    rw [hQ, Subgroup.mem_bot] at hmem
    rw [← Θ.apply_symm_apply q', hmem, map_one]
  · rw [happ, ← map_inv, ← map_mul, ← map_mul, MulEquiv.symm_apply_apply, hg]
  · rw [happ, MulEquiv.symm_apply_apply, ha]
  · rw [← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_mul, har]
  · intro h1
    exact ha1 (Θ.injective (by rw [h1, map_one]))
  · rwa [MulEquiv.orderOf_eq]

theorem GGGoodAut.of_conj {r : H} {σ : MulAut H} (h : GGGoodAut r σ) (k : H) :
    GGGoodAut (k * r * k⁻¹) σ := by
  obtain ⟨hO, g, hg, a, ha, har, ha1, hao⟩ := h
  have e : g * k⁻¹ * (k * r * k⁻¹) * (g * k⁻¹)⁻¹ = g * r * g⁻¹ := by group
  exact ⟨hO, g * k⁻¹, by rw [e]; exact hg, a, ha, by rw [e]; exact har, ha1, hao⟩

theorem ggMulAut_congr_self (e σ : MulAut H) : MulAut.congr e σ = e * σ * e⁻¹ := by
  ext x
  rfl

theorem GGGoodAut.conj {r : H} {σ : MulAut H} (h : GGGoodAut r σ) (e : MulAut H)
    (he : ∃ k : H, e r = k * r * k⁻¹) : GGGoodAut r (e * σ * e⁻¹) := by
  obtain ⟨k, hk⟩ := he
  have h' := h.congr e
  rw [ggMulAut_congr_self] at h'
  have h'' := h'.of_conj k⁻¹
  have e' : k⁻¹ * (MulEquiv.toEquiv e r) * k⁻¹⁻¹ = r := by
    change k⁻¹ * e r * k⁻¹⁻¹ = r
    rw [hk]
    group
  rwa [show (k⁻¹ * e r * k⁻¹⁻¹ : H) = r from e'] at h''

end Good

section Inputs

@[expose] def GGAutStructureAt (t : StatedLieTag) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n f : ℕ) (ψ : (ggU t n f).K →* G) (G₀ : Subgroup G),
    StatedLieAdmissible t n 2 f → 2 ≤ (ggU t n f).D.rank → ψ.range = G₀ →
    ψ.ker ≤ Subgroup.center (ggU t n f).K → commutator ↥G₀ = ⊤ →
    LieModel (↥G₀ ⧸ Subgroup.center ↥G₀) t n 2 f → Subgroup.centralizer (G₀ : Set G) = ⊥ →
    (∃ (p : ℕ) (Bs : Subgroup G), p.Prime ∧ p ≠ 2 ∧ IsElemAbelian p Bs ∧ p ^ 4 ≤ Nat.card Bs ∧
      Bs ≤ Subgroup.normalizer (G₀ : Set G) ∧ ∀ b ∈ Bs, GGPsiInnerDiag (ggU t n f).D ψ b) →
    ¬ (t = .F4 ∧ Odd f) →
    ∀ r : G₀, GGRootInvolution (ggU t n f).D t ψ (r : G) →
      ∃ I C : Subgroup (MulAut G₀), I.Normal ∧ (MulAut.conj : G₀ →* MulAut G₀).range ≤ I ∧
        Odd ((MulAut.conj : G₀ →* MulAut G₀).range.relIndex I) ∧
        (∀ σ : MulAut G₀, ∃ i ∈ I, ∃ c ∈ C, σ = i * c) ∧ I ⊓ C = ⊥ ∧
        ∀ c ∈ C, c ^ 2 = 1 → c ≠ 1 → ∀ e ∈ I, GGGoodOuterAut G₀ r (e * c * e⁻¹)

theorem ggAutStructureInput_of_at (h : ∀ t, GGAutStructureAt t) : GGAutStructureInput :=
  fun G _ _ t n f ψ G₀ => h t G n f ψ G₀

theorem ggAutStructureAt_of_rank_eq_zero {t : StatedLieTag}
    (ht : ∀ n f, (ggU t n f).D.rank = 0) : GGAutStructureAt t := by
  intro G _ _ n f ψ G₀ _ hrank
  rw [ht n f] at hrank
  exact absurd hrank (by norm_num)

theorem ggAutStructureAt_of_small {t : StatedLieTag}
    (ht : t = .G2 ∨ t = .trialityD4 ∨ t = .twistedB2 ∨ t = .twistedG2 ∨ t = .twistedF4 ∨
      t = .Tits) : GGAutStructureAt t :=
  ggAutStructureAt_of_rank_eq_zero fun n f => lieUniversal_rank_eq_zero t n 2 f Nat.prime_two ht

theorem ggAutStructureAt_POmegaOdd : GGAutStructureAt .POmegaOdd := by
  intro G _ _ n f ψ G₀ hadm
  exact absurd rfl hadm.2.2.2

@[expose] def GGAutStructureRest : Prop :=
  GGAutStructureAt .PSU ∧ GGAutStructureAt .PSp ∧ GGAutStructureAt .POmegaPlus ∧
    GGAutStructureAt .POmegaMinus ∧ GGAutStructureAt .F4 ∧ GGAutStructureAt .E6 ∧
    GGAutStructureAt .E7 ∧ GGAutStructureAt .E8 ∧ GGAutStructureAt .twistedE6

theorem ggAutStructureInput_of_psl_of_rest (hPSL : GGAutStructureAt .PSL)
    (h : GGAutStructureRest) : GGAutStructureInput := by
  obtain ⟨hU, hSp, hP, hM, hF4, hE6, hE7, hE8, h2E6⟩ := h
  refine ggAutStructureInput_of_at fun t => ?_
  cases t with
  | PSL => exact hPSL
  | PSU => exact hU
  | PSp => exact hSp
  | POmegaOdd => exact ggAutStructureAt_POmegaOdd
  | POmegaPlus => exact hP
  | POmegaMinus => exact hM
  | G2 => exact ggAutStructureAt_of_small (Or.inl rfl)
  | F4 => exact hF4
  | E6 => exact hE6
  | E7 => exact hE7
  | E8 => exact hE8
  | twistedE6 => exact h2E6
  | trialityD4 => exact ggAutStructureAt_of_small (Or.inr (Or.inl rfl))
  | twistedB2 => exact ggAutStructureAt_of_small (Or.inr (Or.inr (Or.inl rfl)))
  | twistedG2 => exact ggAutStructureAt_of_small (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  | twistedF4 => exact ggAutStructureAt_of_small (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  | Tits => exact ggAutStructureAt_of_small (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))

end Inputs

end CFSG.StandardType
