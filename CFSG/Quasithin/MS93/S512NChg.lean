module

public import CFSG.Quasithin.MS93.MSPSix
public import CFSG.Quasithin.MS93.MSPOrth

public section

namespace CFSG.Quasithin.MS93.S512N

open CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.Symplectic
open scoped Matrix

section Change

variable {K K' : Type} [Field K] [Field K']

@[expose] noncomputable def chgSp (c : K ≃+* K') : MSP.Sp4 K ≃* MSP.Sp4 K' :=
  ((MulEquiv.subgroupCongr (statedSp_eq_GLSymplectic (n := 2) (K := K))).trans
    (CFSG.Timmesfeld.Transvection.QTwo.glSympRingEquiv 2 c)).trans
    (MulEquiv.subgroupCongr (statedSp_eq_GLSymplectic (n := 2) (K := K')).symm)

theorem mat_chgSp_apply (c : K ≃+* K') (g : MSP.Sp4 K) (i j : Fin 2 ⊕ Fin 2) :
    MSP.mat (chgSp c g) i j = c (MSP.mat g i j) :=
  CFSG.Timmesfeld.Transvection.QTwo.glSympRingEquiv_apply 2 c _ i j

@[expose] noncomputable def chgV (c : K ≃+* K') : MSP.V4 K ≃+ MSP.V4 K' :=
  AddEquiv.piCongrRight fun _ => c.toAddEquiv

theorem chgV_apply (c : K ≃+* K') (v : MSP.V4 K) (i : Fin 2 ⊕ Fin 2) : chgV c v i = c (v i) :=
  rfl

theorem mat_chgSp_mulVec (c : K ≃+* K') (g : MSP.Sp4 K) (v : MSP.V4 K) :
    MSP.mat (chgSp c g) *ᵥ chgV c v = chgV c (MSP.mat g *ᵥ v) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, chgV_apply, mat_chgSp_apply, map_sum, map_mul]

end Change

section Two

variable {K : Type} [Field K]

theorem exists_eq_transv (hK : Nat.card K = 2) {A : Subgroup (MSP.Sp4 K)}
    (h3 : 3 ≤ Module.finrank K (MSP.fixSp A)) {x : MSP.Sp4 K} (hx : x ∈ A) (hx1 : x ≠ 1) :
    ∃ v : MSP.V4 K, v ≠ 0 ∧ x = MSP.transv v 1 := by
  have hle4 : Module.finrank K (MSP.fixSp A) ≤ 4 := by
    have := Submodule.finrank_le (MSP.fixSp A)
    simpa using this
  rcases (show Module.finrank K (MSP.fixSp A) = 3 ∨ Module.finrank K (MSP.fixSp A) = 4 by
    omega) with h | h
  · obtain ⟨p, hp, -, hAp⟩ := MSP.exists_point_of_finrank_fixSp_three h
    obtain ⟨v, hv0, rfl⟩ := MSP.exists_eq_span_of_isPoint hp
    obtain ⟨c, rfl⟩ := (MSP.mem_xPoint_span hv0).1 (hAp hx)
    refine ⟨v, hv0, ?_⟩
    rcases MSP.eq_zero_or_eq_one_of_card_two hK c with rfl | rfl
    · exact absurd (MSP.transv_zero v) hx1
    · rfl
  · exfalso
    have htop : MSP.fixSp A = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [h]; simp)
    have hbot := MSP.fixSp_eq_top_iff.1 htop
    rw [hbot] at hx
    exact hx1 hx

theorem eq_one_of_commute_commutator (hK : Nat.card K = 2) {x : MSP.Sp4 K}
    (hx : ∀ y ∈ commutator (MSP.Sp4 K), x * y = y * x) : x = 1 := by
  obtain ⟨c⟩ := MSP.nonempty_ringEquiv_of_card_two hK
  set σ := (B5FinSp.theta c).symm x with hσ
  have hσN : σ ∈ Subgroup.centralizer (alternatingGroup (Fin 6) : Set (Equiv.Perm (Fin 6))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro τ hτ
    have hτc : B5FinSp.theta c τ ∈ commutator (MSP.Sp4 K) := by
      rw [MSP.mem_commutator_iff_sign c, MulEquiv.symm_apply_apply]
      exact Equiv.Perm.mem_alternatingGroup.1 hτ
    apply (B5FinSp.theta c).injective
    rw [map_mul, map_mul, hσ, MulEquiv.apply_symm_apply]
    exact (hx _ hτc).symm
  by_contra hne
  have hσ1 : σ ≠ 1 := fun h1 => hne (by
    have := congrArg (B5FinSp.theta c) h1
    rwa [hσ, MulEquiv.apply_symm_apply, map_one] at this)
  set N := Subgroup.centralizer (alternatingGroup (Fin 6) : Set (Equiv.Perm (Fin 6))) with hN
  have hNt : Nontrivial N := ⟨⟨⟨σ, hσN⟩, 1, fun h => hσ1 (congrArg Subtype.val h)⟩⟩
  have hle := Equiv.Perm.alternatingGroup_le_of_normal (α := Fin 6) (by simp) (N := N) hNt
  have htop : Subgroup.center (alternatingGroup (Fin 6)) = ⊤ := by
    rw [eq_top_iff]
    intro τ _
    rw [Subgroup.mem_center_iff]
    intro τ'
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.1 (hle τ.2) τ' τ'.2
  have hc := alternatingGroup.center_eq_bot (α := Fin 6) (by simp)
  rw [htop] at hc
  exact top_ne_bot hc

end Two

end CFSG.Quasithin.MS93.S512N
