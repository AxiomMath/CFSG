module

public import CFSG.Quasithin.Background.D36GluedL3
import CFSG.Quasithin.Background.D36GluedL3Coord
public import CFSG.Quasithin.Background.D36GluedDim
import CFSG.Quasithin.Background.D36GluedL3Mod
import CFSG.Quasithin.Background.I4Recognition

public section

namespace CFSG.Quasithin

open CFSG.Open

theorem nonempty_equiv_sl3_of_isPSL {X : Type} [Group X] (h : IsPSL 2 7 1 X) :
    Nonempty (X ≃* L3.Γ) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have h7 : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = Fintype.card (ZMod 7) := by
    rw [ZMod.card, ← Nat.card_eq_fintype_card, hK, pow_one]
  let φ : K ≃+* ZMod 7 := FiniteField.ringEquivOfCardEq hcard
  let e₁ : StatedProj (StatedSL 2 K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7) :=
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm.trans
      (CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv φ (Fin 2))
  obtain ⟨e₂⟩ := CFSG.Quasithin.I4.nonempty_psl3_two_equiv_psl2_seven
  let e₃ : Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) ≃* L3.Γ :=
    (QuotientGroup.quotientMulEquivOfEq
      CFSG.LocalAnalysis.ComponentInitial.center_SL_three_zmod_two_eq_bot).trans
      QuotientGroup.quotientBot
  exact ⟨((e.trans e₁).trans e₂.symm).trans e₃⟩

theorem exists_l3Data {Y : Type} [CommGroup Y] [Finite Y] {L₀ : Subgroup (MulAut Y)}
    {U Z : Subgroup Y} (hY : ∀ y : Y, y ^ 2 = 1) (hZU : Z ≤ U) (hU : L₀ ≤ stabSub U)
    (hZ : L₀ ≤ stabSub Z) (hcard : Nat.card (Sec U Z) = 8)
    (hinj : Function.Injective (glueSecAct hU hZ)) (hL : Nat.card L₀ = 168) :
    Nonempty (L3Data L₀ U Z) := by
  have hSec2 : ∀ a : Sec U Z, a ^ 2 = 1 := by
    intro a
    induction a using QuotientGroup.induction_on with
    | H u =>
      have : u ^ 2 = 1 := Subtype.ext (hY u)
      rw [← QuotientGroup.mk_pow, this]
      rfl
  obtain ⟨β', ρ, hβρ⟩ := exists_coord_of_mulAut (d := 3) hSec2 (by rw [hcard]; norm_num)
    (glueSecAct hU hZ)
  have hρinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro l hl
    apply hinj
    rw [map_one]
    refine MulEquiv.ext fun x => ?_
    apply β'.injective
    rw [hβρ, hl]
    simp
  have hGL : Nat.card (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) = 168 := by
    rw [← L3Mod.card_Γ]
    exact (Nat.card_congr (MulEquiv.ofBijective _
      CFSG.LocalAnalysis.ComponentInitial.bijective_toGL_three_zmod_two).toEquiv).symm
  have hbij : Function.Bijective ρ :=
    hρinj.bijective_of_nat_card_le (by rw [hGL, hL])
  let eρ : ↥L₀ ≃* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2) := MulEquiv.ofBijective ρ hbij
  let eΓ : L3.Γ ≃* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2) :=
    MulEquiv.ofBijective _ CFSG.LocalAnalysis.ComponentInitial.bijective_toGL_three_zmod_two
  let π : L3.Γ →* ↥L₀ := eρ.symm.toMonoidHom.comp eΓ.toMonoidHom
  have hρπ : ∀ γ : L3.Γ, ρ (π γ) = eΓ γ := fun γ => eρ.apply_symm_apply (eΓ γ)
  let β : ↥U →* Multiplicative L3.Vec :=
    β'.toMonoidHom.comp (QuotientGroup.mk' (Z.subgroupOf U))
  refine ⟨⟨π, β, ?_, ?_, ?_, hZU, fun g hg u hu => (hU hg u).2 hu,
    fun g hg z hz => (hZ hg z).2 hz, ?_⟩⟩
  · intro l
    refine ⟨eΓ.symm (eρ l), ?_⟩
    show eρ.symm (eΓ (eΓ.symm (eρ l))) = l
    rw [MulEquiv.apply_symm_apply, MulEquiv.symm_apply_apply]
  · intro w
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (β'.symm w)
    exact ⟨x, by
      show β' (QuotientGroup.mk x) = w
      rw [hx, MulEquiv.apply_symm_apply]⟩
  · intro u
    show β' (QuotientGroup.mk u) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  · intro γ u hu
    have h1 : β ⟨((π γ : ↥L₀) : MulAut Y) (u : Y), hu⟩ =
        β' (glueSecAct hU hZ (π γ) (QuotientGroup.mk u)) := rfl
    rw [h1, hβρ, hρπ]
    rfl

namespace GluedSwap

variable {Y : Type} [CommGroup Y] [Finite Y] {X A L₀ : Subgroup (MulAut Y)} {U U' : Subgroup Y}

theorem false_of_L3Data (h : GluedSwap X A U U') (hY : ∀ y : Y, y ^ 2 = 1) (hL₀X : L₀ ≤ X)
    (hL₀ : ∀ l ∈ L₀, ∀ u ∈ U', l u = u)
    (hdiag : ∀ b ∈ A ⊓ stabSub U, ∃ l ∈ L₀, ∀ u ∈ U, b u = l u)
    (D : L3Data L₀ U (U ⊓ fixV L₀)) : False := by
  have hcU := D.card_U
  rw [card_eq_two_pow hY U, card_eq_two_pow hY (U ⊓ fixV L₀)] at hcU
  have hU3 : rk ↥U = rk ↥(U ⊓ fixV L₀) + 3 := by
    have : 2 ^ rk ↥U = 2 ^ (rk ↥(U ⊓ fixV L₀) + 3) := by rw [hcU, pow_add]; ring
    exact Nat.pow_right_injective (le_refl 2) this
  have hRel := h.diag_isElemAbelian2 hL₀ hdiag
  have hkR := h.rk_le_diagSub hdiag hRel
  have hR4 := D.elemAbelian_card_le_four glueDiagSub_le hRel
  have hk2 : rk ↥(glueDiagSub L₀ A U) ≤ 2 := by
    rw [card_eq_two_pow_of_isPGroup hRel.isPGroup] at hR4
    by_contra hcon
    push Not at hcon
    have h8 : 2 ^ 3 ≤ 2 ^ rk ↥(glueDiagSub L₀ A U) := Nat.pow_le_pow_right (by norm_num) hcon
    omega
  obtain ⟨c, hc⟩ : ∃ c : L3.Vec, c ≠ 0 := ⟨fun _ => 1, by decide⟩
  have hEL := D.d36_centre_le hc
  have hEel := D.d36_centre_isElemAbelian2 hc
  have hEcard := D.d36_centre_card hc
  have hEne : (ASsub c hc).map D.rho ≠ ⊥ := fun he => by
    rw [he, Subgroup.card_bot] at hEcard
    omega
  have hE : IsA2 X ((ASsub c hc).map D.rho) := ⟨hEL.trans hL₀X, hEne, hEel⟩
  have hE3 := D.d36_centre_cubic hc h.pair.sup_eq hL₀ (inf_le_right : U ⊓ fixV L₀ ≤ fixV L₀)
  have hcmp := h.compare_cubic hE hE3 (fun e he u hu => hL₀ e (hEL he) u hu)
  have hrkE : rk ↥((ASsub c hc).map D.rho) = 2 := by
    have h1 := card_eq_two_pow_of_isPGroup hEel.isPGroup
    rw [hEcard] at h1
    have : 2 ^ rk ↥((ASsub c hc).map D.rho) = 2 ^ 2 := by omega
    exact Nat.pow_right_injective (le_refl 2) this
  rw [hrkE] at hcmp
  obtain ⟨y, hyU, hyfix, hyZ⟩ := D.d36_centre_lift hY hc (inf_le_right : U ⊓ fixV L₀ ≤ fixV L₀)
  have hlt : rk ↥(U ⊓ fixV L₀) < rk ↥(U ⊓ fixV ((ASsub c hc).map D.rho)) := by
    have hle : U ⊓ fixV L₀ ≤ U ⊓ fixV ((ASsub c hc).map D.rho) :=
      inf_le_inf_left U (fun z hz e he => hz e (hEL he))
    by_contra hcon
    push Not at hcon
    have heq := eq_of_le_of_rk_le hY hle hcon
    exact hyZ (heq ▸ ⟨hyU, hyfix⟩)
  have hDZ : U ⊓ U' ≤ U ⊓ fixV L₀ := le_inf inf_le_left (fun d hd l hl => hL₀ l hl d hd.2)
  have hdz := rk_mono hDZ
  obtain ⟨hs1, -, -⟩ := h.shape_B hY
  have hUh : rk ↥(commModSub U (A ⊓ stabSub U) (U ⊓ U')) ≤ rk ↥U :=
    rk_mono (commModSub_le _ _ _)
  have hF : rk ↥(U ⊓ fixV ((ASsub c hc).map D.rho)) ≤ rk ↥U := rk_mono inf_le_left
  have ht : rk ↥U - rk ↥(U ⊓ fixV ((ASsub c hc).map D.rho)) ≤ 2 := by omega
  have hk : rk ↥(A ⊓ stabSub U) ≤ 2 := by omega
  have hub : 3 ≤ rk ↥U - rk ↥(U ⊓ U') := by omega
  have h6 : (rk ↥(A ⊓ stabSub U) + 1) * (rk ↥U - rk ↥(U ⊓ fixV ((ASsub c hc).map D.rho))) ≤
      3 * 2 := Nat.mul_le_mul (by omega) ht
  omega

end GluedSwap

end CFSG.Quasithin
