module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpModel
public import CFSG.LocalAnalysis.StandardType.GGSignedPermCount
public import CFSG.LocalAnalysis.StandardType.GGNbrTableBWeylOn
public import CFSG.LocalAnalysis.StandardType.GGNbrTableBOrderRestOn

public section

namespace CFSG.StandardType

open CFSG.Assembly TableBSymp SpCoord Multiplicative

section Model

variable {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}

theorem ggTorusReflGenW_of_signedElt (hp : p.Prime) (hp2 : p ≠ 2)
    (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R)) (hZ : Subgroup.center R = ⊥)
    (h : GGTorusSignedElt p r R) : GGTorusReflGenW p r R I := by
  intro L' _ _ ψ A hA v hv
  obtain ⟨hψ, hker, hperf, hA, hAI, hr, h3, -⟩ := hA
  obtain ⟨k, Θ, -, hW, hS, hP, hN⟩ :=
    exists_signedModel hp hp2 hI hZ h hψ hker hperf hA hAI hr h3
  obtain ⟨c, ⟨n, rfl⟩, hcN, hvc⟩ := mem_ggAutomizer_iff.mp hv
  have hv' : v = ggConjAut A hcN := MulEquiv.ext fun a => Subtype.ext (hvc a)
  set H : Subgroup (MulAut (Fin k → Multiplicative (ZMod p))) :=
    (Subgroup.closure (ggTorusReflSet p A)).comap (MulAut.congr Θ).toMonoidHom with hH
  have hgen : ∀ α : MulAut (Fin k → Multiplicative (ZMod p)), α ^ 2 = 1 →
      Nat.card {f // α f = f} * p = Nat.card (Fin k → Multiplicative (ZMod p)) →
      (∃ (m : L') (hm : MulAut.conj m ∈ Subgroup.normalizer (A : Set (MulAut L'))),
        ggConjAut A hm = MulAut.congr Θ α) → α ∈ H := by
    rintro α hα2 hαfix ⟨m, hm, hmα⟩
    refine Subgroup.subset_closure ⟨m, hm, hW m hm, hmα.symm, ?_⟩
    exact ⟨by rw [← map_pow, hα2, map_one],
      (ggIsPseudoReflection_congr Θ (pow_sub_one_eq_one_of_sq hp hp2 hα2) hαfix).2⟩
  have hsH : ∀ i, sgnAut i ∈ H := fun i =>
    hgen _ (sgnAut_sq i) (card_fix_sgnAut hp hp2 i) (hS i)
  have htH : ∀ a b : Fin k, a ≠ b → permAut (Equiv.swap a b) ∈ H := fun a b hab =>
    hgen _ (permAut_swap_sq a b) (card_fix_permAut_swap hp hp2 hab) (hP _)
  have hmem := mem_of_isSignedPerm hsH htH (hN n hcN)
  rw [hH, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] at hmem
  rw [hv']
  exact hmem

theorem ggTorusAutCardDvdSCr_of_signedElt (hp : p.Prime) (hp2 : p ≠ 2)
    (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R)) (hZ : Subgroup.center R = ⊥)
    (h : GGTorusSignedElt p r R) : GGTorusAutCardDvdSCr p r R I (2 ^ r * r.factorial) := by
  intro L' _ _ ψ A hA
  obtain ⟨hψ, hker, hperf, hA, hAI, hr, h3, -⟩ := hA
  obtain ⟨k, Θ, -, -, hS, hP, hN⟩ :=
    exists_signedModel hp hp2 hI hZ h hψ hker hperf hA hAI hr h3
  set W := ggAutomizer (MulAut.conj : L' →* MulAut L').range A with hW
  set H : Subgroup (MulAut (Fin k → Multiplicative (ZMod p))) :=
    W.comap (MulAut.congr Θ).toMonoidHom with hH
  have hcardHW : Nat.card H = Nat.card W := by
    rw [hH, Subgroup.comap_equiv_eq_map_symm']
    exact Subgroup.card_map_of_injective (MulAut.congr Θ).symm.injective
  have hHmem : ∀ u ∈ H, IsSignedPerm ⇑u := by
    intro u hu
    rw [hH, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom] at hu
    obtain ⟨c, ⟨n, rfl⟩, hcN, hvc⟩ := mem_ggAutomizer_iff.mp hu
    have hv' : MulAut.congr Θ u = ggConjAut A hcN := MulEquiv.ext fun a => Subtype.ext (hvc a)
    have h1 := hN n hcN
    rwa [← hv', MulEquiv.symm_apply_apply] at h1
  have hsH : ∀ i, sgnAut i ∈ H := fun i => by
    obtain ⟨m, hm, hmα⟩ := hS i
    rw [hH, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, ← hmα]
    exact ggConjAut_mem_ggAutomizer (MonoidHom.mem_range.mpr ⟨m, rfl⟩) hm
  have htH : ∀ a b : Fin k, a ≠ b → permAut (Equiv.swap a b) ∈ H := fun a b _ => by
    obtain ⟨m, hm, hmα⟩ := hP (Equiv.swap a b)
    rw [hH, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, ← hmα]
    exact ggConjAut_mem_ggAutomizer (MonoidHom.mem_range.mpr ⟨m, rfl⟩) hm
  have hcardH : Nat.card H = 2 ^ k * k.factorial :=
    SignedPermCount.card_eq_of_isSignedPerm hp hp2 hHmem hsH htH
  have hcardA : Nat.card A = p ^ k := by
    have hcV : Nat.card (Fin k → Multiplicative (ZMod p)) = p ^ k := by
      rw [Nat.card_fun, Nat.card_fin]
      congr 1
      exact Nat.card_zmod p
    have h1 : Nat.card (Fin k → Multiplicative (ZMod p)) = Nat.card A :=
      Nat.card_congr Θ.toEquiv
    rw [hcV] at h1
    exact h1.symm
  have hrk : r ≤ k := by
    rw [hcardA] at hr
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hr
  rw [← hcardHW, hcardH]
  exact mul_dvd_mul (pow_dvd_pow 2 hrk) (Nat.factorial_dvd_factorial hrk)

end Model

theorem recipeSymplectic_reflGenW {l n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpn : p ∣ 2 ^ n - 1) (hl : 1 ≤ l) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeSymplectic l (2 ^ n) false Q) :
    LargeEvenRecipeSymplectic l (2 ^ n) false fun R _ I F =>
      Q R I F ∧ ∃ r, GGTorusLift p r R ∧ GGTorusReflGenW p r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have := charP_two_of_card hK
  have : NeZero l := ⟨by omega⟩
  have hpq : p ∣ Nat.card K - 1 := by
    rw [hK]
    exact hpn
  exact ⟨K, inferInstance, inferInstance, hK, hQ, l, ggTorusLift_symplectic hp hp2 hpq hl,
    ggTorusReflGenW_of_signedElt hp hp2 sp_I_subset_inn center_spProj_eq_bot
      (SpModel.ggTorusSignedElt_sp hp hp2 hpq)⟩

theorem recipeSymplectic_autCardDvd {l n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpn : p ∣ 2 ^ n - 1) (hl : 1 ≤ l) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeSymplectic l (2 ^ n) false Q) :
    LargeEvenRecipeSymplectic l (2 ^ n) false fun R _ I F =>
      Q R I F ∧ ∃ r, GGTorusLift p r R ∧ GGTorusAutCardDvdSCr p r R I (2 ^ l * l.factorial) := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have := charP_two_of_card hK
  have : NeZero l := ⟨by omega⟩
  have hpq : p ∣ Nat.card K - 1 := by
    rw [hK]
    exact hpn
  exact ⟨K, inferInstance, inferInstance, hK, hQ, l, ggTorusLift_symplectic hp hp2 hpq hl,
    ggTorusAutCardDvdSCr_of_signedElt hp hp2 sp_I_subset_inn center_spProj_eq_bot
      (SpModel.ggTorusSignedElt_sp hp hp2 hpq)⟩

theorem ggNbrTableBWeylInputOn_typeBC_holds :
    GGNbrTableBWeylInputOn fun _ lab => lab.tag = .B ∨ lab.tag = .C := by
  rintro p hp hp2 ⟨tag, l, n⟩ hlab htag - hsp Q hQ
  dsimp only at htag
  rcases htag with rfl | rfl <;>
    exact recipeSymplectic_reflGenW hp hp2 hsp.2.2 (le_trans (by norm_num) hlab.2.1) hQ

theorem ggNbrTableBOrderRestInputOn_typeC_holds :
    GGNbrTableBOrderRestInputOn fun _ lab => lab.tag = .C := by
  rintro p hp hp2 ⟨tag, l, n⟩ N hlab htag hsp hN Q hQ
  dsimp only at htag
  subst htag
  obtain rfl : N = 2 ^ l * l.factorial := by
    rcases hN with ⟨-, hN⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact hN
    all_goals exact absurd h (by simp)
  exact recipeSymplectic_autCardDvd hp hp2 hsp.2.2 (le_trans (by norm_num) hlab.2.1) hQ

end CFSG.StandardType
