module

public import CFSG.Quasithin.Background.D36GluedNDNum
public import CFSG.Quasithin.Background.D36GluedNDL27
public import CFSG.Quasithin.Background.D36GluedNDEven
import CFSG.Quasithin.Background.F918J2
import CFSG.Quasithin.Background.F918J3
import CFSG.Quasithin.Background.F918Z7aTypes

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

@[expose] def NDResidualL24 : Prop :=
  ∀ (Y : Type) [CommGroup Y] [Finite Y] (X A L₀ : Subgroup (MulAut Y)) (U U' : Subgroup Y),
    NDSetup X A L₀ U U' → IsPSL 2 2 2 ↥L₀ → False

@[expose] def D36Inner : Prop :=
  D3L38 → ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W))
    (V : Subgroup W) (t : MulAut W), D36Norm M Mp T L V t →
    ∀ g ∈ T, ∀ m ∈ L, g ∈ stabSub (commSub (orbSup T V) L) →
      (∀ v ∈ orbSup T V, (g * g) v = v) → (∀ v ∈ orbSup T V, (m * m) v = v) →
      (∀ l ∈ L, ∀ v ∈ orbSup T V, (g * l * g⁻¹) v = (m * l * m⁻¹) v) →
      ∀ u ∈ commSub (orbSup T V) L, g u = m u

section Normalized

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W}

theorem d36nd_stab (n : D36Norm M Mp T L V t) {g : MulAut W} (hg : g ∈ stabSub (orbSup T V))
    (hgU : resHom (orbSup T V) ⟨g, hg⟩ ∈
      stabSub ((commSub (orbSup T V) L).subgroupOf (orbSup T V))) :
    g ∈ stabSub (commSub (orbSup T V) L) := by
  intro w
  have hUV := d36t_U_le n
  by_cases hw : w ∈ orbSup T V
  · have := hgU ⟨w, hw⟩
    simpa [Subgroup.mem_subgroupOf, resHom_apply] using this
  · have h1 : w ∉ commSub (orbSup T V) L := fun h => hw (hUV h)
    have h2 : g w ∉ orbSup T V := fun h => hw ((hg w).mp h)
    exact ⟨fun h => absurd (hUV h) h2, fun h => absurd h h1⟩

theorem d36nd_normalizer (hL38 : D3L38) (n : D36Norm M Mp T L V t) {g : MulAut W} (hgT : g ∈ T)
    (hgU : g ∈ stabSub (commSub (orbSup T V) L)) :
    g ∈ Subgroup.normalizer (L : Set (MulAut W)) := by
  have hz : g ∈ Mp ⊔ T := Subgroup.mem_sup_right hgT
  rcases d36t_conj_cases hL38 n hz with h | h
  · exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h
  · exfalso
    have hgV : g ∈ stabSub (orbSup T V) := le_stabSub_orbSup T V hgT
    have h1 : (commSub (orbSup T V) L).map g.toMonoidHom =
        commSub (orbSup T V) (conjAutSub g L) := d36t_map_U hgV
    have h2 : (commSub (orbSup T V) L).map g.toMonoidHom = commSub (orbSup T V) L :=
      mem_stabSub_iff_map_eq.mp hgU
    have h3 : commSub (orbSup T V) L = (commSub (orbSup T V) L).map t.toMonoidHom :=
      calc commSub (orbSup T V) L = (commSub (orbSup T V) L).map g.toMonoidHom := h2.symm
        _ = commSub (orbSup T V) (conjAutSub g L) := h1
        _ = commSub (orbSup T V) (conjAutSub t L) := by rw [h]
        _ = (commSub (orbSup T V) L).map t.toMonoidHom := (d36t_Ut_eq n).symm
    have hrank := d36t_rank hL38 n
    rw [← h3, inf_idem] at hrank
    omega

theorem resHom_conj_apply (U : Subgroup W) (g l : stabSub U) (u : ↥U) :
    (((resHom U g * resHom U l * (resHom U g)⁻¹) u : ↥U) : W) =
      ((g : MulAut W) * (l : MulAut W) * (g : MulAut W)⁻¹) (u : W) := by
  rw [← map_inv, ← map_mul, ← map_mul, resHom_apply]
  rfl

theorem d36nd_norm_Y (hL38 : D3L38) (n : D36Norm M Mp T L V t) {A : Subgroup (MulAut W)}
    (hA : A ≤ T) {b : MulAut ↥(orbSup T V)}
    (hb : b ∈ autSub A (orbSup T V) ⊓
      stabSub ((commSub (orbSup T V) L).subgroupOf (orbSup T V))) :
    ∀ l ∈ autSub L (orbSup T V), b * l * b⁻¹ ∈ autSub L (orbSup T V) := by
  obtain ⟨g, hgA, rfl⟩ := mem_autSub.mp hb.1
  have hgU := d36nd_stab n g.2 hb.2
  have hnorm := d36nd_normalizer hL38 n (hA hgA) hgU
  intro l hl
  obtain ⟨m, hmL, rfl⟩ := mem_autSub.mp hl
  refine mem_autSub.mpr ⟨g * m * g⁻¹, ?_, by simp [map_mul, map_inv]⟩
  exact (Subgroup.mem_normalizer_iff.mp hnorm _).mp hmL

theorem d36nd_inner_Y (hInner : D36Inner) (hL38 : D3L38) (n : D36Norm M Mp T L V t)
    {A : Subgroup (MulAut W)} (hA : A ≤ T) (hAel : IsElemAbelian2 (autSub A (orbSup T V)))
    (hcinj : Function.Injective
      (MulAut.conj : ↥(autSub L (orbSup T V)) →* MulAut ↥(autSub L (orbSup T V)))) :
    ∀ b ∈ autSub A (orbSup T V) ⊓
        stabSub ((commSub (orbSup T V) L).subgroupOf (orbSup T V)),
      ∀ l₀ ∈ autSub L (orbSup T V),
        (∀ l ∈ autSub L (orbSup T V), b * l * b⁻¹ = l₀ * l * l₀⁻¹) →
          ∀ u ∈ (commSub (orbSup T V) L).subgroupOf (orbSup T V), b u = l₀ u := by
  intro b hb l₀ hl₀ hconj u hu
  obtain ⟨g, hgA, rfl⟩ := mem_autSub.mp hb.1
  obtain ⟨m, hmL, rfl⟩ := mem_autSub.mp hl₀
  have hgU := d36nd_stab n g.2 hb.2
  have hsq : ∀ v ∈ orbSup T V, ((g : MulAut W) * (g : MulAut W)) v = v := by
    intro v hv
    have h1 : resHom (orbSup T V) g * resHom (orbSup T V) g = 1 := by
      simpa [pow_two] using hAel.2 _ hb.1
    have := congrArg (fun φ : MulAut ↥(orbSup T V) => ((φ ⟨v, hv⟩ : ↥(orbSup T V)) : W)) h1
    simpa [MulAut.mul_apply, resHom_apply] using this
  have hinn : ∀ l ∈ L, ∀ v ∈ orbSup T V,
      ((g : MulAut W) * l * (g : MulAut W)⁻¹) v = ((m : MulAut W) * l * (m : MulAut W)⁻¹) v := by
    intro l hl v hv
    have hlstab : l ∈ stabSub (orbSup T V) := d36t_Mp_le_stab_orbSup n (d36t_L_le_Mp n hl)
    have h1 := congrArg (fun φ : MulAut ↥(orbSup T V) => ((φ ⟨v, hv⟩ : ↥(orbSup T V)) : W))
      (hconj (resHom (orbSup T V) ⟨l, hlstab⟩) (mem_autSub.mpr ⟨⟨l, hlstab⟩, hl, rfl⟩))
    simp only [resHom_conj_apply] at h1
    exact h1
  have hmsq : ∀ v ∈ orbSup T V, ((m : MulAut W) * (m : MulAut W)) v = v := by
    set b := resHom (orbSup T V) g with hbdef
    set l₀ := resHom (orbSup T V) m with hl₀def
    have hb2 : b * b = 1 := by simpa [pow_two] using hAel.2 _ hb.1
    have hbl₀ : b * l₀ * b⁻¹ = l₀ := by
      have := hconj l₀ hl₀
      simpa using this
    have hcentral : MulAut.conj (⟨l₀ * l₀, mul_mem hl₀ hl₀⟩ : ↥(autSub L (orbSup T V))) = 1 := by
      apply MulEquiv.ext
      intro l
      apply Subtype.ext
      show l₀ * l₀ * (l : MulAut ↥(orbSup T V)) * (l₀ * l₀)⁻¹ = l
      have h1 := hconj l l.2
      have h2 : b * l₀ = l₀ * b := by
        have := hbl₀
        rw [mul_inv_eq_iff_eq_mul] at this
        exact this
      calc l₀ * l₀ * (l : MulAut ↥(orbSup T V)) * (l₀ * l₀)⁻¹
          = l₀ * (l₀ * l * l₀⁻¹) * l₀⁻¹ := by group
        _ = l₀ * (b * l * b⁻¹) * l₀⁻¹ := by rw [h1]
        _ = b * (l₀ * l * l₀⁻¹) * b⁻¹ := by
          have e : l₀ * (b * l * b⁻¹) * l₀⁻¹ = (l₀ * b) * l * (l₀ * b)⁻¹ := by group
          rw [e, ← h2]; group
        _ = b * (b * l * b⁻¹) * b⁻¹ := by rw [h1]
        _ = (b * b) * l * (b * b)⁻¹ := by group
        _ = l := by rw [hb2]; group
    have h3 : (⟨l₀ * l₀, mul_mem hl₀ hl₀⟩ : ↥(autSub L (orbSup T V))) = 1 := by
      apply hcinj
      rw [hcentral, map_one]
    have h4 : l₀ * l₀ = 1 := congrArg Subtype.val h3
    intro v hv
    have := congrArg (fun φ : MulAut ↥(orbSup T V) => ((φ ⟨v, hv⟩ : ↥(orbSup T V)) : W)) h4
    simpa [MulAut.mul_apply, resHom_apply, hl₀def] using this
  have key := hInner hL38 W M Mp T L V t n g (hA hgA) m hmL hgU hsq hmsq hinn
  have hu' : (u : W) ∈ commSub (orbSup T V) L := hu
  apply Subtype.ext
  show (g : MulAut W) (u : W) = (m : MulAut W) (u : W)
  exact key u hu'

end Normalized

theorem d36GluedNonDiag_of_residual
    (hL38 : D3L38) (hInner : D36Inner) (hres : NDResidualL24) : D36GluedNonDiag := by
  intro W _ _ M Mp T L V t n hd A hA hQ hAU hnd hcub hshape
  have hsw := d36_gluedSwap hL38 n hA hQ hAU
  obtain ⟨hA38, -, -, -⟩ := hL38 W M Mp T L V n.std t n.tT n.tn n.Mp_eq
  have hsimple : IsSimpleGroup ↥L := insp5a_sec_isSimpleGroup hA38
  have hLstab : L ≤ stabSub (orbSup T V) := (d36t_L_le_Mp n).trans (d36t_Mp_le_stab_orbSup n)
  have hLU : L ≤ stabSub (commSub (orbSup T V) L) := by
    intro l hl u
    constructor
    · intro h
      have := d36t_L_inv_U n l⁻¹ (L.inv_mem hl) _ h
      simpa using this
    · exact d36t_L_inv_U n l hl u
  have hnc : ¬ L ≤ centSub (orbSup T V) := by
    intro hLc
    have hgap := hsw.gap
    have hbot : commSub (orbSup T V) L = ⊥ := by
      rw [commSub_eq_bot_iff]
      intro v hv l hl
      exact hLc hl v hv
    have h0 : rk ↥((commSub (orbSup T V) L).subgroupOf (orbSup T V)) = 0 := by
      rw [hbot, Subgroup.bot_subgroupOf, rk_bot]
    rw [h0] at hgap
    omega
  have hfaith : L ⊓ centSub (orbSup T V) = ⊥ :=
    inf_centSub_eq_bot_of_isSimpleGroup hsimple hLstab hnc
  let e : ↥L ≃* ↥(autSub L (orbSup T V)) := autSubEquivOfFaithful hLstab hfaith
  have hsimple₀ : IsSimpleGroup ↥(autSub L (orbSup T V)) := MulEquiv.isSimpleGroup e.symm
  have hnonab₀ : ∃ a b : ↥(autSub L (orbSup T V)), a * b ≠ b * a := by
    have hns : ¬ Group.IsSolvable ↥L := not_isSolvable_of_mem_cComp n.std.hyp.comp
    by_contra hcon
    push Not at hcon
    apply hns
    refine Group.isSolvable_of_comm fun a b => ?_
    have h1 := hcon (e a) (e b)
    apply e.injective
    rw [map_mul, map_mul]
    exact h1
  have hA38₀ : A38Types ↥(autSub L (orbSup T V)) := a38Types_congr e hA38
  have hL₀U : autSub L (orbSup T V) ≤
      stabSub ((commSub (orbSup T V) L).subgroupOf (orbSup T V)) :=
    autSub_le_stabSub_subgroupOf hLU
  have hAel : IsElemAbelian2 (autSub A (orbSup T V)) := by
    obtain ⟨r, -, -, hAk, -⟩ := QhatStar_spec hQ
    exact hAk.1.1.2.2
  have S : NDSetup (autSub (Mp ⊔ T) (orbSup T V)) (autSub A (orbSup T V))
      (autSub L (orbSup T V)) ((commSub (orbSup T V) L).subgroupOf (orbSup T V))
      (((commSub (orbSup T V) L).map t.toMonoidHom).subgroupOf (orbSup T V)) :=
    ⟨hsw, d36_exp_VT n, d36_L_le_X n, d36_L_fix_Ut' hL38 n, hL₀U, hsimple₀, hnonab₀,
      commV_autSub_eq hLstab, fun b hb => d36nd_norm_Y hL38 n hA hb,
      d36nd_inner_Y hInner hL38 n hA hAel (conj_injective_of_simple hsimple₀ hnonab₀), hnd⟩
  rcases Z7a.a38_cases hA38₀ with ⟨k, hk, hL⟩ | ⟨k, hk, hL⟩ | hL | ⟨p, hp, hp7, hL⟩
  · by_cases hk2 : k = 2
    · subst hk2
      exact hres _ _ _ _ _ _ S hL
    · exact S.false_of_psl2_two (by omega) hL
  · exact S.false_of_sz hk hL
  · exact S.false_of_j1 hL
  · by_cases h7 : p = 7
    · subst h7
      exact S.false_of_psl2_seven hL
    by_cases h31 : p = 31
    · subst h31
      exact S.false_of_psl2_31 hL
    have h11 : 11 ≤ p := by
      by_contra hcon
      have : p = 8 ∨ p = 9 ∨ p = 10 := by omega
      rcases this with rfl | rfl | rfl <;> norm_num at hp
    exact S.false_of_psl2_prime hp h11 h31 hL

end CFSG.Quasithin
