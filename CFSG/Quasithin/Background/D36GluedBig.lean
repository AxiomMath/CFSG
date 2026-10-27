module

public import CFSG.Quasithin.Background.D36GluedDim
public import CFSG.Quasithin.Background.D36GluedGen
import CFSG.Quasithin.Background.F918Z4c1PSL
import CFSG.Quasithin.Background.F918Z4c2Main
import CFSG.Quasithin.Background.F918Z4bL2

public section

namespace CFSG.Quasithin

theorem glue_comm_identity {G : Type*} [CommGroup G] (P Q x y u : G) :
    P * Q⁻¹ = (P * x⁻¹ * (y * u⁻¹)⁻¹) * (Q * y⁻¹ * (x * u⁻¹)⁻¹)⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem sup_map_conj_eq_of_subgroupOf {Γ : Type*} [Group Γ] {G R : Subgroup Γ} (hRG : R ≤ G)
    (g : ↥G)
    (h : R.subgroupOf G ⊔ (R.subgroupOf G).map (MulAut.conj g).toMonoidHom = ⊤) :
    R ⊔ R.map (MulAut.conj (g : Γ)).toMonoidHom = G := by
  have h1 := congrArg (Subgroup.map G.subtype) h
  rw [Subgroup.map_sup, Subgroup.map_map, Subgroup.map_top, Subgroup.range_subtype,
    Subgroup.map_subgroupOf_eq_of_le hRG] at h1
  have h2 : G.subtype.comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj (g : Γ)).toMonoidHom.comp G.subtype := by
    ext x
    simp
  rw [h2, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hRG] at h1
  exact h1

section FixLocus

variable {Y : Type} [CommGroup Y] {U D : Subgroup Y}

theorem commModSub_inf_le_sup {R R' : Subgroup (MulAut Y)}
    (hD : ∀ l ∈ R ⊔ R', ∀ d ∈ D, l d = d) :
    commModSub U R D ⊓ commModSub U R' D ≤ commModSub U (R ⊔ R') D := by
  rintro u ⟨⟨huU, hu1⟩, -, hu2⟩
  refine ⟨huU, ?_⟩
  let S : Subgroup (MulAut Y) :=
    { carrier := {g | g ∈ R ⊔ R' ∧ g u * u⁻¹ ∈ D}
      one_mem' := ⟨one_mem _, by simp⟩
      mul_mem' := by
        rintro g₁ g₂ ⟨hg₁, h₁⟩ ⟨hg₂, h₂⟩
        refine ⟨mul_mem hg₁ hg₂, ?_⟩
        have e : (g₁ * g₂) u * u⁻¹ = g₁ (g₂ u * u⁻¹) * (g₁ u * u⁻¹) := by
          simp only [MulAut.mul_apply, map_mul, map_inv]
          group
        rw [e, hD g₁ hg₁ _ h₂]
        exact D.mul_mem h₂ h₁
      inv_mem' := by
        rintro g ⟨hg, h⟩
        refine ⟨inv_mem hg, ?_⟩
        have hgi := hD g⁻¹ (inv_mem hg) _ h
        have e : g⁻¹ u * u⁻¹ = (g⁻¹ (g u * u⁻¹))⁻¹ := by
          simp only [map_mul, map_inv]
          have : g⁻¹ (g u) = u := by
            have := congrArg (fun φ : MulAut Y => φ u) (inv_mul_cancel g)
            simpa [MulAut.mul_apply] using this
          rw [this]
          group
        rw [e, hgi]
        exact D.inv_mem h }
  have hle : R ⊔ R' ≤ S :=
    sup_le (fun r hr => ⟨(le_sup_left : R ≤ R ⊔ R') hr, hu1 r hr⟩)
      (fun r hr => ⟨(le_sup_right : R' ≤ R ⊔ R') hr, hu2 r hr⟩)
  intro g hg
  exact (hle hg).2

theorem map_commModSub_le {R : Subgroup (MulAut Y)} {g : MulAut Y} (hgU : g ∈ stabSub U)
    (hgD : ∀ d ∈ D, g d ∈ D) :
    (commModSub U R D).map g.toMonoidHom ≤ commModSub U (R.map (MulAut.conj g).toMonoidHom) D := by
  rintro _ ⟨v, ⟨hvU, hv⟩, rfl⟩
  refine ⟨(hgU v).mpr hvU, ?_⟩
  rintro _ ⟨r, hr, rfl⟩
  have h1 : ((MulAut.conj g) r : MulAut Y) (g v) = g (r v) := by
    simp [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply]
  have e : ((MulAut.conj g).toMonoidHom r) (g v) * (g v)⁻¹ = g (r v * v⁻¹) := by
    show ((MulAut.conj g) r : MulAut Y) (g v) * (g v)⁻¹ = _
    rw [h1, map_mul, map_inv]
  show ((MulAut.conj g).toMonoidHom r) (g v) * (g v)⁻¹ ∈ D
  rw [e]
  exact hgD _ (hv r hr)

variable [Finite Y]

theorem rk_le_two_mul_of_gen_pair {L₀ R : Subgroup (MulAut Y)} {g : MulAut Y} (hg : g ∈ L₀)
    (hU : L₀ ≤ stabSub U) (hD : ∀ l ∈ L₀, ∀ d ∈ D, l d = d)
    (hgen : R ⊔ R.map (MulAut.conj g).toMonoidHom = L₀) :
    rk ↥U - rk ↥(commModSub U L₀ D) ≤ 2 * (rk ↥U - rk ↥(commModSub U R D)) := by
  have h1 : commModSub U R D ⊓ commModSub U (R.map (MulAut.conj g).toMonoidHom) D ≤
      commModSub U L₀ D := by
    have := commModSub_inf_le_sup (U := U) (D := D) (R := R)
      (R' := R.map (MulAut.conj g).toMonoidHom) (hgen ▸ hD)
    rwa [hgen] at this
  have h2 := map_commModSub_le (U := U) (D := D) (R := R) (hU hg)
    (fun d hd => by rw [hD g hg d hd]; exact hd)
  have h3 : rk ↥(commModSub U R D) ≤
      rk ↥(commModSub U (R.map (MulAut.conj g).toMonoidHom) D) := by
    have := rk_mono h2
    rwa [rk_map_aut_eq] at this
  have h4 := rk_sup_add_rk_inf (commModSub U R D)
    (commModSub U (R.map (MulAut.conj g).toMonoidHom) D)
  have h5 : rk ↥(commModSub U R D ⊔ commModSub U (R.map (MulAut.conj g).toMonoidHom) D) ≤
      rk ↥U := rk_mono (sup_le (commModSub_le _ _ _) (commModSub_le _ _ _))
  have h6 := rk_mono h1
  have h7 : rk ↥(commModSub U R D) ≤ rk ↥U := rk_mono (commModSub_le _ _ _)
  omega

end FixLocus

section Glued

variable {Y : Type} [CommGroup Y] [Finite Y] {X A L₀ : Subgroup (MulAut Y)} {U U' : Subgroup Y}

namespace GluedSwap

theorem commModSub_diagSub (hdiag : ∀ b ∈ A ⊓ stabSub U, ∃ l ∈ L₀, ∀ u ∈ U, b u = l u) :
    commModSub U (glueDiagSub L₀ A U) (U ⊓ U') = commModSub U (A ⊓ stabSub U) (U ⊓ U') := by
  ext u
  constructor
  · rintro ⟨huU, hu⟩
    refine ⟨huU, fun b hb => ?_⟩
    obtain ⟨l, hl, hbl⟩ := hdiag b hb
    rw [hbl u huU]
    exact hu l ⟨hl, b, hb, hbl⟩
  · rintro ⟨huU, hu⟩
    refine ⟨huU, fun r hr => ?_⟩
    obtain ⟨-, b, hb, hbr⟩ := hr
    rw [← hbr u huU]
    exact hu b hb

theorem exists_gl_sec (h : GluedSwap X A U U') (hY : ∀ y : Y, y ^ 2 = 1)
    (hL₀ : ∀ l ∈ L₀, ∀ u ∈ U', l u = u) (hL₀U : L₀ ≤ stabSub U)
    (hdiag : ∀ b ∈ A ⊓ stabSub U, ∃ l ∈ L₀, ∀ u ∈ U, b u = l u) (hsimple : IsSimpleGroup ↥L₀)
    (hnonab : ∃ a b : ↥L₀, a * b ≠ b * a) :
    ∃ d, d = rk ↥U - rk ↥(commModSub U L₀ (U ⊓ U')) ∧
      ∃ ρ : ↥L₀ →* Matrix.GeneralLinearGroup (Fin d) (ZMod 2), Function.Injective ρ := by
  have hcent : L₀ ≤ centSub (U ⊓ U') := fun l hl d hd => hL₀ l hl d hd.2
  have hD : L₀ ≤ stabSub (U ⊓ U') := hcent.trans (centSub_le_stabSub _)
  have hinjD := glueSecAct_injective hL₀U hD hsimple (h.exists_not_mem_of_diag hdiag)
  have hfix : ∀ l ∈ L₀, ∀ d ∈ U ⊓ U', l d = d := fun l hl d hd => hL₀ l hl d hd.2
  have hinv : ∀ l ∈ L₀, ∀ u ∈ commModSub U L₀ (U ⊓ U'), l u ∈ commModSub U L₀ (U ⊓ U') := by
    rintro l hl u ⟨huU, hu⟩
    refine ⟨(hL₀U hl u).mpr huU, fun g hg => ?_⟩
    have e : g (l u) * (l u)⁻¹ = ((g * l) u * u⁻¹) * (l u * u⁻¹)⁻¹ := by
      simp only [MulAut.mul_apply]
      group
    rw [e]
    exact (U ⊓ U').mul_mem (hu (g * l) (L₀.mul_mem hg hl)) ((U ⊓ U').inv_mem (hu l hl))
  have hF : L₀ ≤ stabSub (commModSub U L₀ (U ⊓ U')) := by
    intro l hl u
    refine ⟨fun h' => ?_, hinv l hl u⟩
    have := hinv l⁻¹ (L₀.inv_mem hl) _ h'
    simpa [MulAut.inv_apply] using this
  have hnt : ∃ l ∈ L₀, ∃ u ∈ U, l u * u⁻¹ ∉ commModSub U L₀ (U ⊓ U') := by
    by_contra hcon
    push Not at hcon
    obtain ⟨a, b, hab⟩ := hnonab
    apply hab
    apply hinjD
    refine MulEquiv.ext fun x => ?_
    induction x using QuotientGroup.induction_on with
    | H u =>
      simp only [map_mul, MulAut.mul_apply, glueSecAct_mk]
      rw [mk_eq_mk_iff, Subgroup.mem_subgroupOf]
      have ha := hcon a a.2 u u.2
      have hb := hcon b b.2 u u.2
      have e : ∀ x : Y, a.1 (b.1 x) * (b.1 (a.1 x))⁻¹ =
          (a.1 (b.1 x * x⁻¹) * (b.1 x * x⁻¹)⁻¹) *
            (b.1 (a.1 x * x⁻¹) * (a.1 x * x⁻¹)⁻¹)⁻¹ := by
        intro x
        simp only [map_mul, map_inv]
        exact glue_comm_identity (G := Y) _ _ _ _ _
      show a.1 (b.1 (u : Y)) * (b.1 (a.1 (u : Y)))⁻¹ ∈ U ⊓ U'
      rw [e (u : Y)]
      exact (U ⊓ U').mul_mem (hb.2 a a.2) ((U ⊓ U').inv_mem (ha.2 b b.2))
  have hinjF := glueSecAct_injective hL₀U hF hsimple hnt
  have hSec2 : ∀ a : Sec U (commModSub U L₀ (U ⊓ U')), a ^ 2 = 1 := by
    intro a
    induction a using QuotientGroup.induction_on with
    | H u =>
      have : u ^ 2 = 1 := Subtype.ext (hY u)
      rw [← QuotientGroup.mk_pow, this]
      rfl
  obtain ⟨ρ, hρ⟩ := exists_injective_GL_of_mulAut hSec2 (glueSecAct hL₀U hF) hinjF
  refine ⟨rk (Sec U (commModSub U L₀ (U ⊓ U'))), ?_, ρ, hρ⟩
  have hcard := card_sec_mul (V := Y) (W := U) (U := commModSub U L₀ (U ⊓ U'))
    (commModSub_le _ _ _)
  have h1 : rk (Sec U (commModSub U L₀ (U ⊓ U'))) + rk ↥(commModSub U L₀ (U ⊓ U')) = rk ↥U := by
    unfold rk
    rw [← padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne', hcard]
  omega

theorem rk_diagSub_le (h : GluedSwap X A U U') (hL₀ : ∀ l ∈ L₀, ∀ u ∈ U', l u = u)
    (hdiag : ∀ b ∈ A ⊓ stabSub U, ∃ l ∈ L₀, ∀ u ∈ U, b u = l u) (hsimple : IsSimpleGroup ↥L₀)
    (hnonab : ∃ a b : ↥L₀, a * b ≠ b * a) {m : ℕ} (hAut : AutRankLe ↥L₀ m) :
    rk ↥(glueDiagSub L₀ A U) ≤ m := by
  have hRel := h.diag_isElemAbelian2 hL₀ hdiag
  have hRL : glueDiagSub L₀ A U ≤ L₀ := glueDiagSub_le
  have hE : IsElemAb2 ((glueDiagSub L₀ A U).subgroupOf L₀) :=
    ⟨fun a ha b hb => Subtype.ext (hRel.1 _ ha _ hb), fun a ha => Subtype.ext (hRel.2 _ ha)⟩
  have hrk : rk ↥((glueDiagSub L₀ A U).subgroupOf L₀) = rk ↥(glueDiagSub L₀ A U) := by
    unfold rk
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRL).toEquiv]
  have hm := rk_le_of_autRankLe_simple hsimple hnonab hAut hE
  omega

theorem false_of_psl2_two (h : GluedSwap X A U U') (hY : ∀ y : Y, y ^ 2 = 1) (hL₀X : L₀ ≤ X)
    (hL₀ : ∀ l ∈ L₀, ∀ u ∈ U', l u = u) (hL₀U : L₀ ≤ stabSub U)
    (hdiag : ∀ b ∈ A ⊓ stabSub U, ∃ l ∈ L₀, ∀ u ∈ U, b u = l u) (hsimple : IsSimpleGroup ↥L₀)
    (hnonab : ∃ a b : ↥L₀, a * b ≠ b * a) {n : ℕ} (hn : 3 ≤ n) (hL : IsPSL 2 2 n ↥L₀) :
    False := by
  have hF2 : Nat.card (ZMod 2) = 2 ^ 1 := by rw [Nat.card_zmod]; norm_num
  have hdim : ∀ {d : ℕ} (ρ : ↥L₀ →* Matrix.GeneralLinearGroup (Fin d) (ZMod 2)),
      Function.Injective ρ → 2 * n ≤ d := by
    intro d ρ hρ
    by_cases h3 : n = 3
    · subst h3
      have := Z4c2.six_le_of_psl2_eight hL hF2 ρ hρ
      omega
    · have := two_mul_le_of_psl2_two (by omega) h3 hL hF2 ρ hρ
      omega
  obtain ⟨d, hd, ρ, hρ⟩ := h.exists_gl hY hL₀ hL₀U hdiag hsimple
  have h2n := hdim ρ hρ
  have hAut := autRankLe_psl2_two (by omega) hL
  have hRle := h.rk_diagSub_le hL₀ hdiag hsimple hnonab hAut
  obtain ⟨hs1, hsk, hB⟩ := h.shape_B hY
  have hRel := h.diag_isElemAbelian2 hL₀ hdiag
  have hkR := h.rk_le_diagSub hdiag hRel
  have hR : rk ↥(glueDiagSub L₀ A U) = n := by omega
  have hRcard : Nat.card ↥(glueDiagSub L₀ A U) = 2 ^ n := by
    rw [card_eq_two_pow_of_isPGroup hRel.isPGroup, hR]
  have hRL : glueDiagSub L₀ A U ≤ L₀ := glueDiagSub_le
  have hRG : Nat.card ↥((glueDiagSub L₀ A U).subgroupOf L₀) = 2 ^ n := by
    rw [← hRcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRL).toEquiv
  obtain ⟨g, hg⟩ := exists_gen_pair_of_psl2_two hL hRG
  have hgen := sup_map_conj_eq_of_subgroupOf hRL g hg
  have hgL : (g : MulAut Y) ∈ L₀ := g.2
  have hfix : ∀ l ∈ L₀, ∀ d ∈ U ⊓ U', l d = d := fun l hl d hd => hL₀ l hl d hd.2
  have hGP := rk_le_two_mul_of_gen_pair (U := U) (D := U ⊓ U') hgL hL₀U hfix hgen
  rw [commModSub_diagSub hdiag] at hGP
  obtain ⟨-, -, -, -, hC, -⟩ := h.diag_bound hY hL₀X hL₀ hdiag
  obtain ⟨d₁, hd₁, ρ₁, hρ₁⟩ := h.exists_gl_sec hY hL₀ hL₀U hdiag hsimple hnonab
  have h2n₁ := hdim ρ₁ hρ₁
  have hUh : rk ↥(commModSub U (A ⊓ stabSub U) (U ⊓ U')) ≤ rk ↥U := rk_mono (commModSub_le _ _ _)
  omega

end GluedSwap

end Glued

end CFSG.Quasithin
