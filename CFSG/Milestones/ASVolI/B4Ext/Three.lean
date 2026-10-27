module

public import CFSG.Milestones.ASVolI.B4Ext.SL3
public import CFSG.Milestones.ASVolI.B4Ext.ThreeT
public import CFSG.Milestones.ASVolI.B4Ext.WT
public import CFSG.Quasithin.Background.B3Q

public section

namespace CFSG.ASVolI

open CFSG.Quasithin

section ThreeMain

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {V : Type} [CommGroup V] [Finite V] {G : Subgroup (MulAut V)} {U : Subgroup V}
  {K : Type} [Field K] [Finite K] [CharP K 2] {π : ↥(CFSG.Open.StatedSL 3 K) →* ↥G}

theorem burnsideB49x_card_setσ_nat (C : burnsideB49_Coord3 G U K π) (hσ : ∀ s, C.σ s = s)
    (A : Subgroup (MulAut V)) :
    Nat.card {x : Fin 3 → K // ∀ s ∈ burnsideB49x_hat C A,
      ((C.σ s : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec x = x} =
      Nat.card ↥(burnsideB49x_fixN (burnsideB49x_hat C A)) :=
  Nat.card_congr (Equiv.subtypeEquivRight fun x => by
    simp only [hσ]
    exact Iff.rfl)

theorem burnsideB49x_card_setσ_dual (C : burnsideB49_Coord3 G U K π)
    (hσ : ∀ s, C.σ s = CFSG.Quasithin.JonesParshall.invTransposeSL 3 K s)
    (A : Subgroup (MulAut V)) :
    Nat.card {x : Fin 3 → K // ∀ s ∈ burnsideB49x_hat C A,
      ((C.σ s : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec x = x} =
      Nat.card ↥(burnsideB49x_fixD (burnsideB49x_hat C A)) :=
  Nat.card_congr (Equiv.subtypeEquivRight fun x => by
    simp only [hσ, CFSG.Quasithin.JonesParshall.invTransposeSL_coe]
    exact Iff.rfl)

theorem burnsideB49x_card_setN (C : burnsideB49_Coord3 G U K π) (A : Subgroup (MulAut V)) :
    Nat.card {x : Fin 3 → K // ∀ s ∈ burnsideB49x_hat C A,
      (s : Matrix (Fin 3) (Fin 3) K).mulVec x = x} =
      Nat.card ↥(burnsideB49x_fixN (burnsideB49x_hat C A)) :=
  Nat.card_congr (Equiv.subtypeEquivRight fun x => Iff.rfl)

theorem burnsideB49x_three_chain_nat (C : burnsideB49_Coord3 G U K π) (hσ : ∀ s, C.σ s = s)
    (hreal : (FFModel.nat (CFSG.Open.StatedSL 3 K)).RealizesVia G U ⊥ π)
    {A : Subgroup (MulAut V)} (hAG : A ≤ G) :
    Nat.card A * Nat.card ↥(fixV A) ≤ Nat.card (burnsideB49x_hat C A) *
      Nat.card ↥(burnsideB49x_fixN (burnsideB49x_hat C A)) ^ 2 := by
  have hπ : ∀ g : ↥G, ∃ γ, π γ = g := hreal.1
  have hU := burnsideB49x_card_fixU_le C A
  rw [burnsideB49x_card_setσ_nat C hσ] at hU
  have hVf := burnsideB49x_card_fixV_le C A
  rw [burnsideB49x_card_setN] at hVf
  rw [← burnsideB49x_card_hat C hreal hπ hAG, pow_two]
  exact Nat.mul_le_mul_left _ (hVf.trans (Nat.mul_le_mul_right _ hU))

theorem burnsideB49x_three_bound_nat (C : burnsideB49_Coord3 G U K π) (hσ : ∀ s, C.σ s = s)
    (hreal : (FFModel.nat (CFSG.Open.StatedSL 3 K)).RealizesVia G U ⊥ π)
    {A : Subgroup (MulAut V)} (hAG : A ≤ G) (hA : IsElemAbelian2 A) :
    Nat.card A * Nat.card ↥(fixV A) ≤ Nat.card V := by
  rw [burnsideB49x_card_V C hreal]
  exact (burnsideB49x_three_chain_nat C hσ hreal hAG).trans
    (burnsideB49x_sl3_boundN (B := burnsideB49x_hat C A) (burnsideB49x_hat_comm C hreal hA)
      (burnsideB49x_hat_sq C hreal hA))

theorem burnsideB49x_three_eq_nat (C : burnsideB49_Coord3 G U K π) (hσ : ∀ s, C.σ s = s)
    (hreal : (FFModel.nat (CFSG.Open.StatedSL 3 K)).RealizesVia G U ⊥ π)
    {A : Subgroup (MulAut V)} (hAG : A ≤ G) (hA : IsElemAbelian2 A) (hne : A ≠ ⊥)
    (hoff : Nat.card V ≤ Nat.card A * Nat.card ↥(fixV A)) :
    ∃ H : Submodule K (Fin 3 → K), Module.finrank K H = 2 ∧
      burnsideB49x_hat C A = burnsideB49x_RW H := by
  have hπ : ∀ g : ↥G, ∃ γ, π γ = g := hreal.1
  have h1 := burnsideB49x_three_chain_nat C hσ hreal hAG
  have h2 := burnsideB49x_sl3_boundN (B := burnsideB49x_hat C A) (burnsideB49x_hat_comm C hreal hA)
    (burnsideB49x_hat_sq C hreal hA)
  rw [burnsideB49x_card_V C hreal] at hoff
  exact burnsideB49x_sl3_eqN (B := burnsideB49x_hat C A) (burnsideB49x_hat_comm C hreal hA)
    (burnsideB49x_hat_sq C hreal hA) (burnsideB49x_hat_ne_bot C hπ hAG hne)
    (le_antisymm h2 (hoff.trans h1))

theorem burnsideB49x_three_dual_false (C : burnsideB49_Coord3 G U K π)
    (hσ : ∀ s, C.σ s = CFSG.Quasithin.JonesParshall.invTransposeSL 3 K s)
    (hreal : (FFModel.nat (CFSG.Open.StatedSL 3 K)).RealizesVia G U ⊥ π)
    {A : Subgroup (MulAut V)} (hAG : A ≤ G) (hA : IsElemAbelian2 A) (hne : A ≠ ⊥)
    (hoff : Nat.card V ≤ Nat.card A * Nat.card ↥(fixV A)) : False := by
  have hπ : ∀ g : ↥G, ∃ γ, π γ = g := hreal.1
  set B := burnsideB49x_hat C A with hB
  have hc := burnsideB49x_hat_comm C hreal hA
  have hs := burnsideB49x_hat_sq C hreal hA
  have hU := burnsideB49x_card_fixU_le C A
  rw [burnsideB49x_card_setσ_dual C hσ] at hU
  have hVf := burnsideB49x_card_fixV_le C A
  rw [burnsideB49x_card_setN] at hVf
  have hN := burnsideB49x_sl3_boundN hc hs
  have hD := burnsideB49x_sl3_boundD hc hs
  rw [burnsideB49x_card_V C hreal, ← burnsideB49x_card_hat C hreal hπ hAG] at hoff
  set b := Nat.card B
  set n := Nat.card ↥(burnsideB49x_fixN B)
  set d := Nat.card ↥(burnsideB49x_fixD B)
  set c := Nat.card K ^ 6
  have hchain : c ≤ b * d * n := by
    calc c ≤ b * Nat.card ↥(fixV A) := hoff
      _ ≤ b * (Nat.card ↥(fixV A ⊓ U) * n) := Nat.mul_le_mul_left _ hVf
      _ ≤ b * (d * n) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hU)
      _ = b * d * n := by ring
  have hb : 0 < b := Nat.card_pos
  have hn : 0 < n := Nat.card_pos
  have hd : 0 < d := Nat.card_pos
  have hND : (b * d * n) ^ 2 = (b * d ^ 2) * (b * n ^ 2) := by ring
  have hsq : c ^ 2 ≤ (b * d ^ 2) * (b * n ^ 2) := by
    rw [← hND]
    exact Nat.pow_le_pow_left hchain 2
  have hNeq : b * n ^ 2 = c := by
    by_contra hlt
    have hlt' : b * n ^ 2 < c := lt_of_le_of_ne hN hlt
    have : (b * d ^ 2) * (b * n ^ 2) < c * c := by
      calc (b * d ^ 2) * (b * n ^ 2) < (b * d ^ 2) * c :=
            Nat.mul_lt_mul_of_pos_left hlt' (by positivity)
        _ ≤ c * c := Nat.mul_le_mul_right _ hD
    rw [← pow_two] at this
    exact absurd hsq (not_le.2 this)
  have hDeq : b * d ^ 2 = c := by
    by_contra hlt
    have hlt' : b * d ^ 2 < c := lt_of_le_of_ne hD hlt
    have : (b * d ^ 2) * (b * n ^ 2) < c * c := by
      calc (b * d ^ 2) * (b * n ^ 2) < c * (b * n ^ 2) :=
            Nat.mul_lt_mul_of_pos_right hlt' (by positivity)
        _ ≤ c * c := Nat.mul_le_mul_left _ hN
    rw [← pow_two] at this
    exact absurd hsq (not_le.2 this)
  have hBne := burnsideB49x_hat_ne_bot C hπ hAG hne
  obtain ⟨H, hH, hBH⟩ := burnsideB49x_sl3_eqN hc hs hBne hNeq
  obtain ⟨p, hp, hBp⟩ := burnsideB49x_sl3_eqD hc hs hBne hDeq
  exact burnsideB49x_sl3_RW_ne hH hp (hBH.symm.trans hBp)

end ThreeMain

section ThreeFinal

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {V : Type} [CommGroup V] [Finite V] {G : Subgroup (MulAut V)} {U : Subgroup V}
  {K : Type} [Field K] [Finite K] {π : ↥(CFSG.Open.StatedSL 3 K) →* ↥G}

theorem burnsideB49x_quotIsoSub_of_coord (C : burnsideB49_Coord3 G U K π) (hσ : ∀ s, C.σ s = s)
    (hreal : (FFModel.nat (CFSG.Open.StatedSL 3 K)).RealizesVia G U ⊥ π) :
    CFSG.ASVolI.ChB.QuotIsoSub G U := by
  have hπ : ∀ g : ↥G, ∃ γ, π γ = g := hreal.1
  have hker : U = C.qV.ker := by
    ext v
    rw [MonoidHom.mem_ker]
    exact (C.hker v).symm
  let e₁ : V ⧸ U ≃* Multiplicative (Fin 3 → K) :=
    (QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective C.qV C.hqs)
  have he₁ : ∀ v, e₁ (QuotientGroup.mk v) = C.qV v := fun v => rfl
  let e₂ : ↥U ≃* Multiplicative (Fin 3 → K) := MulEquiv.ofBijective C.β₀ C.hβb
  have he₂ : ∀ u, e₂ u = C.β₀ u := fun u => rfl
  refine ⟨e₁.trans e₂.symm, fun g hg v => ?_⟩
  obtain ⟨s, hs⟩ := burnsideB49_rhoHat_surj C hπ g hg
  set u : ↥U := e₂.symm (e₁ (QuotientGroup.mk v)) with hu
  have hβu : C.β₀ u = C.qV v := by rw [← he₂, hu, MulEquiv.apply_symm_apply, he₁]
  have hgu : g (u : V) ∈ U := hreal.2.2.2.1 ⟨g, hg⟩ u u.2
  have hgu' : ((π (burnsideB49_slToStated 3 K (C.σ s)) : ↥G) : MulAut V) (u : V) ∈ U := by
    rw [← burnsideB49_rhoHat_apply, hs]
    exact hgu
  have h3 : (⟨((π (burnsideB49_slToStated 3 K (C.σ s)) : ↥G) : MulAut V) (u : V), hgu'⟩ :
      ↥U) = ⟨g (u : V), hgu⟩ := Subtype.ext (show
        ((π (burnsideB49_slToStated 3 K (C.σ s)) : ↥G) : MulAut V) (u : V) = g (u : V) by
          rw [← burnsideB49_rhoHat_apply, hs])
  have h1 := C.hβe (C.σ s) u hgu'
  rw [h3, hσ s] at h1
  change ((e₂.symm (e₁ (QuotientGroup.mk (g v))) : ↥U) : V) = g (u : V)
  have h2 : e₂.symm (e₁ (QuotientGroup.mk (g v))) = ⟨g (u : V), hgu⟩ := by
    apply e₂.injective
    rw [MulEquiv.apply_symm_apply, he₁, he₂, h1, hβu, ← hs, burnsideB49_qV_rhoHat]
  rw [h2]

theorem burnsideB49x_quadHyp_of (C : burnsideB49_Coord3 G U K π) {A₀ : Subgroup (MulAut V)}
    (hq : IsQuadratic A₀) (g : Matrix.SpecialLinearGroup (Fin 3) K)
    (hg : ∀ w : Fin 2 → K, g⁻¹ * burnsideB49_tau w * g ∈ burnsideB49x_hat C A₀) :
    burnsideB49_QuadHyp (C.toCore3.conj g) := by
  intro w w' a
  have hρ : ∀ (s : Matrix.SpecialLinearGroup (Fin 3) K) (b : Additive V),
      (C.toCore3.conj g).ρ s b =
        Additive.ofMul (burnsideB49_rhoHat C (g⁻¹ * s * g) (Additive.toMul b)) := by
    intro s b
    show burnsideB49_addEnd (burnsideB49_rhoHat C (g⁻¹ * s * g⁻¹⁻¹)) b = _
    rw [inv_inv]
    rfl
  rw [hρ, hρ]
  have hm1 : burnsideB49_rhoHat C (g⁻¹ * burnsideB49_tau w * g) ∈ A₀ := hg w
  have hm2 : burnsideB49_rhoHat C (g⁻¹ * burnsideB49_tau w' * g) ∈ A₀ := hg w'
  set v := Additive.toMul a with hv
  have hcomm : burnsideB49_rhoHat C (g⁻¹ * burnsideB49_tau w' * g) v * v⁻¹ ∈ commV A₀ :=
    Subgroup.subset_closure ⟨_, hm2, v, rfl⟩
  have hfix := hq hcomm _ hm1
  apply Additive.toMul.injective
  simp only [toMul_ofMul, toMul_sub, div_eq_mul_inv]
  exact hfix

theorem burnsideB49x_three (hV : ∀ v : V, v ^ 2 = 1) {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f)
    (hreal : (FFModel.nat (CFSG.Open.StatedSL 3 K)).RealizesVia G U ⊥ π)
    (hquot : CFSG.ASVolI.ChB.QuotIsoSub G U ∨ CFSG.ASVolI.ChB.QuotIsoDual G U)
    {T : Subgroup (MulAut V)} (hT : CFSG.QuasithinUnique.IsSylowTwoOf T G)
    {A : Subgroup (MulAut V)} (hA : IsFFStarOffender T A) :
    CFSG.ASVolI.ChB.SplitsOver G U ∧ CFSG.ASVolI.ChB.QuotIsoSub G U ∧
      qOf G = ((1 : ℚ) : WithTop ℚ) := by
  haveI := burnsideB49_charP_two hf hK
  have hπ : ∀ g : ↥G, ∃ γ, π γ = g := hreal.1
  have hAG' : IsFFStarOffender G A := burnsideB49x_offender_mono hT.1 hA
  obtain ⟨C⟩ := burnsideB49_coord3_exists hreal hquot
  rcases C.hσ with hσ | hσ
  swap
  · exact (burnsideB49x_three_dual_false C hσ hreal hAG'.1 hAG'.2.2.1 hAG'.2.1
      (burnsideB49x_offender_card hAG')).elim
  refine ⟨?_, burnsideB49x_quotIsoSub_of_coord C hσ hreal, ?_⟩
  · obtain ⟨A₀, -, hmin⟩ := B1.exists_isFFStarMin_le hAG'
    have hq : IsQuadratic A₀ := B1_4_3 hV hmin
    have hA₀ := hmin.1
    obtain ⟨H, hH, hAH⟩ := burnsideB49x_three_eq_nat C hσ hreal hA₀.1 hA₀.2.2.1 hA₀.2.1
      (burnsideB49x_offender_card hA₀)
    obtain ⟨g, hg⟩ := burnsideB49x_sl3_tau_conj hH
    exact burnsideB49_split_of_quad hV C hπ g
      (burnsideB49x_quadHyp_of C hq g (fun w => hAH ▸ hg w))
  · refine qOf_eq_of_offenders hV le_rfl (fun B hB => ?_) ⟨A, hAG', B1_4_1 hV hAG'⟩
    have hle := burnsideB49x_three_bound_nat C hσ hreal hB.1 hB.2.2.1
    by_contra hlt
    have hlt' := (rAV_lt_one_iff hV hB.isA2).1 (not_le.1 hlt)
    omega

end ThreeFinal

end CFSG.ASVolI
