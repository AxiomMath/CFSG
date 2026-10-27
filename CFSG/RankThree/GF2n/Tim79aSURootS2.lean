module

public import CFSG.Timmesfeld.Transvection.ModelSUPoints
public import CFSG.RankThree.GF2n.Tim79aSpRootS2
public import CFSG.Timmesfeld.ARS.CaseMSU

public section

namespace CFSG.RankThree.GF2n.Tim79a

open Matrix CFSG.Open CFSG.LieType.Universal.Unitary CFSG.Timmesfeld.LieEmbed
  CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection.ModelRank
open scoped commutatorElement

variable {F : Type} [Field F] {σ : F ≃+* F} {m : ℕ}

theorem rootS2Model_su [CharP F 2] (hσ : ∀ c, σ (σ c) = c)
    (htr : ∀ c, σ c = c → ∃ e, e + σ e = c) {K : Type} [Group K] {Φ : SU σ m →* K}
    (hsurj : Function.Surjective Φ) (hker : Φ.ker ≤ Subgroup.center (SU σ m))
    {a d : Fin m → F} {T : Subgroup (SU σ m)} (hT : IsUTransGroup σ a T)
    (haa : uForm σ a a = 0) (hdd : uForm σ d d = 0) (had : uForm σ a d = 1)
    (Θ : SUThetaFacts σ a d T) (G : SUGeomFacts σ a d) (hS1 : RootS1Model K (T.map Φ))
    (hcore : pCoreOf 2 (Subgroup.normalizer ((T.map Φ : Subgroup K) : Set K)) =
      (uRad σ a).map Φ) : RootS2Model K (T.map Φ) := by
  have hComm : SUCommStmt σ m := suCommStmt_holds hσ
  have hSL2 : SUSL2Stmt σ m := suSL2Stmt_holds hσ htr
  intro α hfix hrad
  rw [hcore] at hrad ⊢
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp [uForm_eq] at had
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [uForm_zero_right] at had
    exact zero_ne_one had
  obtain ⟨Td, hTd⟩ := exists_isUTransGroup hσ hdd
  obtain ⟨gd, hgd⟩ := exists_suMat_mulVec_eq hσ haa hdd (by rw [had]; exact one_ne_zero)
    (by rw [had, map_one, CharTwo.add_self_eq_zero])
  have hTdeq : Td = conjSub T gd := hTd.eq (by have := hT.conjSub gd; rwa [hgd] at this)
  have hTdA : Td.map Φ = conjSub (T.map Φ) (Φ gd) := by
    rw [hTdeq]
    exact Subgroup.map_map_conj T Φ gd
  have hnc : ¬ Commuting (T.map Φ) (Td.map Φ) := by
    intro hc
    rcases (hComm hker hT hTd ha0 hd0 haa hdd).1 hc with h0 | ⟨l, hl⟩
    · rw [had] at h0
      exact one_ne_zero h0
    · rw [hl, uForm_smul_right, haa, mul_zero] at had
      exact zero_ne_one had
  have hTα : (T.map Φ).map α.toMonoidHom = T.map Φ := map_mulAut_eq_self hfix
  obtain ⟨g', hg'⟩ := hsurj (α (Φ gd))
  have hTdα : (Td.map Φ).map α.toMonoidHom = (conjSub T g').map Φ := by
    rw [hTdA, map_conjSub_mulAut, hTα, ← hg']
    exact (Subgroup.map_map_conj T Φ g').symm
  obtain ⟨d', hd'⟩ : ∃ d', suMat σ m g' *ᵥ a = d' := ⟨_, rfl⟩
  have hTg' : IsUTransGroup σ d' (conjSub T g') := by
    have := hT.conjSub g'
    rwa [hd'] at this
  have hd'd' : uForm σ d' d' = 0 := by
    rw [← hd', uForm_mulVec σ g' a a, haa]
  have had' : uForm σ a d' ≠ 0 := by
    intro h0
    apply hnc
    have hc := CaseMSU.commuting_map Φ (hT.commuting hσ hTg' h0)
    rw [← hTdα, ← hTα] at hc
    exact (commuting_map_mulAut_iff α).1 hc
  obtain ⟨d'', hd''⟩ : ∃ d'', (uForm σ a d')⁻¹ • d' = d'' := ⟨_, rfl⟩
  have hd''1 : uForm σ a d'' = 1 := by
    rw [← hd'', uForm_smul_right, inv_mul_cancel₀ had']
  have hd''d'' : uForm σ d'' d'' = 0 := by
    rw [← hd'', uForm_smul_left, uForm_smul_right, hd'd', mul_zero, mul_zero]
  have hTg'' : IsUTransGroup σ d'' (conjSub T g') :=
    IsUTransGroup.of_smul hσ had' (by rwa [← hd'', smul_smul, mul_inv_cancel₀ had', one_smul])
  obtain ⟨x₀, hx₀, hx₀d⟩ := exists_mem_uRad_mulVec_eq hσ haa hdd hd''d'' had hd''1
  have hTdx : conjSub T g' = conjSub Td x₀ :=
    hTg''.eq (by have := hTd.conjSub x₀; rwa [hx₀d] at this)
  have hTdα' : (Td.map Φ).map α.toMonoidHom = conjSub (Td.map Φ) (Φ x₀) := by
    rw [hTdα, hTdx]
    exact Subgroup.map_map_conj Td Φ x₀
  have hx₀T : ∀ y ∈ T.map Φ, Commute (Φ x₀) y := by
    rintro _ ⟨t, ht, rfl⟩
    exact (hT.commute_of_mulVec_eq hx₀.1 t ht).map Φ
  set β : MulAut K := MulAut.conj (Φ x₀)⁻¹ * α with hβ
  have hβapp : ∀ g, β g = (Φ x₀)⁻¹ * α g * Φ x₀ := fun g => by
    rw [hβ, MulAut.mul_apply, MulAut.conj_apply, inv_inv]
  have hβA : ∀ y ∈ T.map Φ, β y = y := fun y hy => by
    rw [hβapp, hfix y hy, mul_assoc, ← (hx₀T y hy).eq, inv_mul_cancel_left]
  have hβTd : (Td.map Φ).map β.toMonoidHom = Td.map Φ := by
    rw [hβ, map_mul_mulAut, hTdα']
    change conjSub (conjSub (Td.map Φ) (Φ x₀)) (Φ x₀)⁻¹ = Td.map Φ
    rw [← conjSub_mul, inv_mul_cancel, conjSub_one]
  have hβrad : ∀ z ∈ uRad σ a, (Φ z)⁻¹ * β (Φ z) ∈ T.map Φ := by
    intro z hz
    obtain ⟨t', ht', hαz⟩ : ∃ t' ∈ T.map Φ, α (Φ z) = Φ z * t' :=
      ⟨_, hrad (Φ z) ⟨z, hz, rfl⟩, (mul_inv_cancel_left _ _).symm⟩
    have hc : ⁅z⁻¹, x₀⁻¹⁆ ∈ T := Θ.comm_mem (inv_mem hz) (inv_mem hx₀)
    have e : (Φ z)⁻¹ * β (Φ z) = Φ ⁅z⁻¹, x₀⁻¹⁆ * t' := by
      calc (Φ z)⁻¹ * β (Φ z) = (Φ z)⁻¹ * (Φ x₀)⁻¹ * Φ z * (t' * Φ x₀) := by
            rw [hβapp, hαz]
            group
        _ = (Φ z)⁻¹ * (Φ x₀)⁻¹ * Φ z * (Φ x₀ * t') := by rw [(hx₀T t' ht').eq]
        _ = Φ ⁅z⁻¹, x₀⁻¹⁆ * t' := by
            rw [commutatorElement_def]
            simp only [map_mul, map_inv, inv_inv]
            group
    rw [e]
    exact (T.map Φ).mul_mem ⟨_, hc, rfl⟩ ht'
  have hβQ : ∀ z ∈ uRad σ a, β (Φ z) = Φ z :=
    apply_map_uRad_eq_self hσ hker hT hTd hdd had Θ G hComm β hβA hβTd hβrad
  have hβTd' : ∀ x ∈ Td.map Φ, β x = x := hSL2 hker hT hTd haa hdd had β hβA hβTd
  obtain ⟨x, hx, hx1⟩ : ∃ x ∈ Td.map Φ, x ≠ 1 := by
    by_contra hne
    push Not at hne
    apply hnc
    intro y _ x hx
    rw [hne x hx]
    exact Commute.one_right y
  have hgen := hS1 (Φ gd) (fun h => hnc fun y hy x hx => h y hy x (hTdA ▸ hx)) x
    (hTdA ▸ hx) hx1
  rw [hcore] at hgen
  have hβ1 : ∀ k, β k = k := by
    intro k
    have hle : (uRad σ a).map Φ ⊔ Subgroup.zpowers x ≤
        β.toMonoidHom.eqLocus (MonoidHom.id K) := by
      refine sup_le ?_ ?_
      · rintro _ ⟨z, hz, rfl⟩
        exact hβQ z hz
      · rw [Subgroup.zpowers_le]
        exact hβTd' x hx
    exact hle (by rw [hgen]; exact Subgroup.mem_top k)
  refine ⟨Φ x₀, ⟨x₀, hx₀, rfl⟩, MulEquiv.ext fun g => ?_⟩
  have h2 := hβ1 g
  rw [hβapp] at h2
  calc α g = Φ x₀ * ((Φ x₀)⁻¹ * α g * Φ x₀) * (Φ x₀)⁻¹ := by group
    _ = MulAut.conj (Φ x₀) g := by rw [h2, MulAut.conj_apply]

end CFSG.RankThree.GF2n.Tim79a
