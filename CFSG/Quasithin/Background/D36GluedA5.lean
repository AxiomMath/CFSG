module

public import CFSG.Quasithin.Background.D36GluedBig
import CFSG.Quasithin.Background.F918Z4c1PSL
import CFSG.Quasithin.Background.F918Z4bL2
public import CFSG.Quasithin.Background.D36GluedLift

public section

namespace CFSG.Quasithin

section Lemmas

variable {Y : Type} [CommGroup Y] {U D : Subgroup Y}

theorem mem_commModSub_of_gen {Λ : Subgroup (MulAut Y)} (hΛ : ∀ l ∈ Λ, ∀ d ∈ D, l d = d) {u : Y}
    (huU : u ∈ U) {T : Set (MulAut Y)} (hT : Subgroup.closure T = Λ)
    (hgen : ∀ g ∈ T, g u * u⁻¹ ∈ D) : u ∈ commModSub U Λ D := by
  refine ⟨huU, ?_⟩
  let S : Subgroup (MulAut Y) :=
    { carrier := {g | g ∈ Λ ∧ g u * u⁻¹ ∈ D}
      one_mem' := ⟨one_mem _, by simp⟩
      mul_mem' := by
        rintro g₁ g₂ ⟨hg₁, h₁⟩ ⟨hg₂, h₂⟩
        refine ⟨mul_mem hg₁ hg₂, ?_⟩
        have e : (g₁ * g₂) u * u⁻¹ = g₁ (g₂ u * u⁻¹) * (g₁ u * u⁻¹) := by
          simp only [MulAut.mul_apply, map_mul, map_inv]
          group
        rw [e, hΛ g₁ hg₁ _ h₂]
        exact D.mul_mem h₂ h₁
      inv_mem' := by
        rintro g ⟨hg, h⟩
        refine ⟨inv_mem hg, ?_⟩
        have hgi := hΛ g⁻¹ (inv_mem hg) _ h
        have e : g⁻¹ u * u⁻¹ = (g⁻¹ (g u * u⁻¹))⁻¹ := by
          simp only [map_mul, map_inv]
          have : g⁻¹ (g u) = u := by
            have := congrArg (fun φ : MulAut Y => φ u) (inv_mul_cancel g)
            simpa [MulAut.mul_apply] using this
          rw [this]
          group
        rw [e, hgi]
        exact D.inv_mem h }
  have hle : Λ ≤ S := by
    rw [← hT, Subgroup.closure_le]
    intro g hg
    exact ⟨hT ▸ Subgroup.subset_closure hg, hgen g hg⟩
  intro g hg
  exact (hle hg).2

theorem mem_commModSub_zpowers {r : MulAut Y} (hD : ∀ d ∈ D, r d = d) {u : Y} (huU : u ∈ U)
    (hu : r u * u⁻¹ ∈ D) : u ∈ commModSub U (Subgroup.zpowers r) D := by
  have hr : r ∈ centSub D := hD
  have hle : Subgroup.zpowers r ≤ centSub D := Subgroup.zpowers_le.mpr hr
  refine mem_commModSub_of_gen (fun l hl d hd => hle hl d hd) huU (T := {r})
    (Subgroup.zpowers_eq_closure r).symm ?_
  intro g hg
  rw [Set.mem_singleton_iff] at hg
  rw [hg]
  exact hu

@[expose] def commHomOn (r : MulAut Y) (W : Subgroup Y) : ↥W →* Y where
  toFun u := r u.1 * (u.1)⁻¹
  map_one' := by simp
  map_mul' u v := by
    show r (u.1 * v.1) * (u.1 * v.1)⁻¹ = (r u.1 * (u.1)⁻¹) * (r v.1 * (v.1)⁻¹)
    rw [map_mul, mul_inv_rev, mul_comm (v.1)⁻¹ (u.1)⁻¹]
    exact mul_mul_mul_comm _ _ _ _

theorem commHomOn_apply (r : MulAut Y) (W : Subgroup Y) (u : ↥W) :
    commHomOn r W u = r u.1 * (u.1)⁻¹ := rfl

variable [Finite Y]

theorem exists_comm_of_card (hY : ∀ y : Y, y ^ 2 = 1) {F₁ F₂ : Subgroup Y} {r : MulAut Y}
    (hDF₁ : D ≤ F₁) (hDF₂ : D ≤ F₂) (hrk : rk ↥F₁ = rk ↥F₂)
    (hD : ∀ d ∈ D, r d = d) (hrF : ∀ u ∈ F₂, r u * u⁻¹ ∈ F₁)
    (hinj : ∀ u ∈ F₂, r u * u⁻¹ ∈ D → u ∈ D) :
    ∀ x ∈ F₁, ∃ z ∈ F₂, r z * z⁻¹ * x⁻¹ ∈ D := by
  have hker : (commHomOn r F₂).ker = D.subgroupOf F₂ := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, commHomOn_apply]
    constructor
    · intro h1
      exact hinj u.1 u.2 (by rw [h1]; exact D.one_mem)
    · intro hu
      rw [hD _ hu]
      simp
  have hcard := B1More.card_map_mul_card_inf_ker (⊤ : Subgroup ↥F₂) (commHomOn r F₂)
  rw [Subgroup.map_top, top_inf_eq, Subgroup.card_top, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDF₂).toEquiv,
    card_eq_two_pow hY, card_eq_two_pow hY, card_eq_two_pow hY] at hcard
  have hrr : rk ↥(commHomOn r F₂).range + rk ↥D = rk ↥F₂ := by
    rw [← pow_add] at hcard
    exact Nat.pow_right_injective (le_refl 2) hcard
  have hrange_le : (commHomOn r F₂).range ≤ F₁ := by
    rintro _ ⟨u, rfl⟩
    exact hrF u.1 u.2
  have hinf : (commHomOn r F₂).range ⊓ D = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨u, rfl⟩, hu⟩
    have hu' : (u : Y) ∈ D := hinj u.1 u.2 hu
    rw [Subgroup.mem_bot, commHomOn_apply, hD _ hu']
    simp
  have hsup := rk_sup_add_rk_inf (commHomOn r F₂).range D
  rw [hinf, rk_bot] at hsup
  have hle2 : (commHomOn r F₂).range ⊔ D ≤ F₁ := sup_le hrange_le hDF₁
  have heq : (commHomOn r F₂).range ⊔ D = F₁ := eq_of_le_of_rk_le hY hle2 (by omega)
  intro x hx
  rw [← heq] at hx
  obtain ⟨y, ⟨z, rfl⟩, d, hd, hyd⟩ := Subgroup.mem_sup.mp hx
  refine ⟨z.1, z.2, ?_⟩
  rw [commHomOn_apply] at hyd
  have : r z.1 * (z.1)⁻¹ * x⁻¹ = d⁻¹ := by
    rw [← hyd, mul_inv, mul_inv_cancel_left]
  rw [this]
  exact D.inv_mem hd

theorem map_subtype_sup_conj {Γ : Type*} [Group Γ] {G R : Subgroup Γ} (hRG : R ≤ G) (g : ↥G)
    {P : Subgroup ↥G} (h : P ⊔ (R.subgroupOf G).map (MulAut.conj g).toMonoidHom = ⊤) :
    P.map G.subtype ⊔ R.map (MulAut.conj (g : Γ)).toMonoidHom = G := by
  have h1 := congrArg (Subgroup.map G.subtype) h
  rw [Subgroup.map_sup, Subgroup.map_map, Subgroup.map_top, Subgroup.range_subtype] at h1
  have h2 : G.subtype.comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj (g : Γ)).toMonoidHom.comp G.subtype := by
    ext x
    simp
  rw [h2, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hRG] at h1
  exact h1

end Lemmas

section Glued

variable {Y : Type} [CommGroup Y] [Finite Y] {X A L₀ : Subgroup (MulAut Y)} {U U' : Subgroup Y}

namespace GluedSwap

theorem false_of_psl2_four (h : GluedSwap X A U U') (hY : ∀ y : Y, y ^ 2 = 1) (hL₀X : L₀ ≤ X)
    (hL₀ : ∀ l ∈ L₀, ∀ u ∈ U', l u = u) (hL₀U : L₀ ≤ stabSub U)
    (hdiag : ∀ b ∈ A ⊓ stabSub U, ∃ l ∈ L₀, ∀ u ∈ U, b u = l u) (hsimple : IsSimpleGroup ↥L₀)
    (hnonab : ∃ a b : ↥L₀, a * b ≠ b * a) (hL : IsPSL 2 2 2 ↥L₀) : False := by
  have hF2 : Nat.card (ZMod 2) = 2 ^ 1 := by rw [Nat.card_zmod]; norm_num
  have hdim : ∀ {d : ℕ} (ρ : ↥L₀ →* Matrix.GeneralLinearGroup (Fin d) (ZMod 2)),
      Function.Injective ρ → 4 ≤ d := by
    intro d ρ hρ
    have := two_mul_le_of_psl2_two (by norm_num) (by norm_num) hL hF2 ρ hρ
    omega
  obtain ⟨d, hd, ρ, hρ⟩ := h.exists_gl hY hL₀ hL₀U hdiag hsimple
  have h4 := hdim ρ hρ
  have hAut := autRankLe_psl2_two (by norm_num) hL
  have hRle := h.rk_diagSub_le hL₀ hdiag hsimple hnonab hAut
  obtain ⟨hs1, hsk, hB⟩ := h.shape_B hY
  have hRel := h.diag_isElemAbelian2 hL₀ hdiag
  have hkR := h.rk_le_diagSub hdiag hRel
  have hR2 : rk ↥(glueDiagSub L₀ A U) = 2 := by omega
  have hRcard : Nat.card ↥(glueDiagSub L₀ A U) = 2 ^ 2 := by
    rw [card_eq_two_pow_of_isPGroup hRel.isPGroup, hR2]
  have hRL : glueDiagSub L₀ A U ≤ L₀ := glueDiagSub_le
  have hRG : Nat.card ↥((glueDiagSub L₀ A U).subgroupOf L₀) = 2 ^ 2 := by
    rw [← hRcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRL).toEquiv
  obtain ⟨g, hg, hgr⟩ := exists_gen_pair_strong hL hRG
  have hgen := sup_map_conj_eq_of_subgroupOf hRL g hg
  have hgL : (g : MulAut Y) ∈ L₀ := g.2
  have hfix : ∀ l ∈ L₀, ∀ d ∈ U ⊓ U', l d = d := fun l hl d hd => hL₀ l hl d hd.2
  have hgenr : ∀ r ∈ glueDiagSub L₀ A U, r ≠ 1 →
      Subgroup.zpowers r ⊔ (glueDiagSub L₀ A U).map (MulAut.conj (g : MulAut Y)).toMonoidHom =
        L₀ := by
    intro r hr hr1
    have h1 := hgr ⟨r, hRL hr⟩ hr (fun e => hr1 (by simpa using congrArg Subtype.val e))
    have h2 := map_subtype_sup_conj hRL g (P := Subgroup.zpowers (⟨r, hRL hr⟩ : ↥L₀)) h1
    rwa [MonoidHom.map_zpowers] at h2
  have hGP := rk_le_two_mul_of_gen_pair (U := U) (D := U ⊓ U') hgL hL₀U hfix hgen
  rw [commModSub_diagSub hdiag] at hGP
  obtain ⟨-, -, -, -, hC, -⟩ := h.diag_bound hY hL₀X hL₀ hdiag
  obtain ⟨d₁, hd₁, ρ₁, hρ₁⟩ := h.exists_gl_sec hY hL₀ hL₀U hdiag hsimple hnonab
  have h4' := hdim ρ₁ hρ₁
  have hDF : U ⊓ U' ≤ commModSub U L₀ (U ⊓ U') := fun d hd =>
    ⟨hd.1, fun l hl => by rw [hfix l hl d hd]; simp⟩
  have hrDF := rk_mono hDF
  have hUh : rk ↥(commModSub U (A ⊓ stabSub U) (U ⊓ U')) ≤ rk ↥U :=
    rk_mono (commModSub_le _ _ _)
  have hFU : rk ↥(commModSub U L₀ (U ⊓ U')) ≤ rk ↥U := rk_mono (commModSub_le _ _ _)
  have hDU : rk ↥(U ⊓ U') ≤ rk ↥U := rk_mono inf_le_left
  have hFD : commModSub U L₀ (U ⊓ U') = U ⊓ U' :=
    (eq_of_le_of_rk_le hY hDF (by omega)).symm
  obtain ⟨R', hR'⟩ : ∃ R' : Subgroup (MulAut Y),
      R' = (glueDiagSub L₀ A U).map (MulAut.conj (g : MulAut Y)).toMonoidHom := ⟨_, rfl⟩
  rw [← hR'] at hgen hgenr
  have hR'L : R' ≤ L₀ := by
    rw [hR']
    rintro _ ⟨r, hr, rfl⟩
    exact L₀.mul_mem (L₀.mul_mem hgL (hRL hr)) (L₀.inv_mem hgL)
  have hF12 : commModSub U (A ⊓ stabSub U) (U ⊓ U') ⊓ commModSub U R' (U ⊓ U') ≤
      commModSub U L₀ (U ⊓ U') := by
    have := commModSub_inf_le_sup (U := U) (D := U ⊓ U') (R := glueDiagSub L₀ A U) (R' := R')
      (by rw [hgen]; exact hfix)
    rw [hgen, commModSub_diagSub hdiag] at this
    exact this
  have hmap : (commModSub U (A ⊓ stabSub U) (U ⊓ U')).map (g : MulAut Y).toMonoidHom ≤
      commModSub U R' (U ⊓ U') := by
    rw [← commModSub_diagSub hdiag, hR']
    exact map_commModSub_le (hL₀U hgL) (fun d hd => by rw [hfix _ hgL d hd]; exact hd)
  have hrk12 : rk ↥(commModSub U (A ⊓ stabSub U) (U ⊓ U')) ≤ rk ↥(commModSub U R' (U ⊓ U')) := by
    have := rk_mono hmap
    rwa [rk_map_aut_eq] at this
  have hsi := rk_sup_add_rk_inf (commModSub U (A ⊓ stabSub U) (U ⊓ U')) (commModSub U R' (U ⊓ U'))
  have hsu : rk ↥(commModSub U (A ⊓ stabSub U) (U ⊓ U') ⊔ commModSub U R' (U ⊓ U')) ≤ rk ↥U :=
    rk_mono (sup_le (commModSub_le _ _ _) (commModSub_le _ _ _))
  have hin : rk ↥(commModSub U (A ⊓ stabSub U) (U ⊓ U') ⊓ commModSub U R' (U ⊓ U')) ≤
      rk ↥(U ⊓ U') := by
    have := rk_mono hF12
    rwa [hFD] at this
  have hrk : rk ↥(commModSub U (A ⊓ stabSub U) (U ⊓ U')) = rk ↥(commModSub U R' (U ⊓ U')) := by
    omega
  refine h.false_of_commutators hY hL₀X hL₀ hdiag fun x hx r hr hr1 => ?_
  have hDF₁ : U ⊓ U' ≤ commModSub U (A ⊓ stabSub U) (U ⊓ U') := fun d hd =>
    ⟨hd.1, fun b hb => by
      obtain ⟨l, hl, hbl⟩ := hdiag b hb
      rw [hbl d hd.1, hfix l hl d hd]
      simp⟩
  have hDF₂ : U ⊓ U' ≤ commModSub U R' (U ⊓ U') := fun d hd =>
    ⟨hd.1, fun l hl => by rw [hfix l (hR'L hl) d hd]; simp⟩
  have hrfix : ∀ d ∈ U ⊓ U', r d = d := fun d hd => hfix r (hRL hr) d hd
  have hrF : ∀ u ∈ commModSub U R' (U ⊓ U'),
      r u * u⁻¹ ∈ commModSub U (A ⊓ stabSub U) (U ⊓ U') := by
    intro u hu
    have huU : u ∈ U := hu.1
    obtain ⟨-, b, hb, hbr⟩ := hr
    have e : r u * u⁻¹ = b u * u⁻¹ := by rw [hbr u huU]
    have hmem : b u * u⁻¹ ∈ U := U.mul_mem ((hb.2 u).mpr huU) (U.inv_mem huU)
    rw [e]
    exact ⟨hmem, fun b' hb' => h.quad hb hb' huU⟩
  have hinj : ∀ u ∈ commModSub U R' (U ⊓ U'), r u * u⁻¹ ∈ U ⊓ U' → u ∈ U ⊓ U' := by
    intro u hu hru
    have h1 := mem_commModSub_zpowers (U := U) hrfix hu.1 hru
    have h2 : u ∈ commModSub U (Subgroup.zpowers r ⊔ R') (U ⊓ U') :=
      commModSub_inf_le_sup (U := U) (D := U ⊓ U') (R := Subgroup.zpowers r) (R' := R')
        (by rw [hgenr r hr hr1]; exact hfix) ⟨h1, hu⟩
    rw [hgenr r hr hr1, hFD] at h2
    exact h2
  obtain ⟨z, hz, hzx⟩ := exists_comm_of_card hY hDF₁ hDF₂ hrk hrfix hrF hinj x hx
  exact ⟨z, hz.1, hzx⟩

end GluedSwap

end Glued

end CFSG.Quasithin
