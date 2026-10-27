module

public import CFSG.Quasithin.EmptyFaithful.F918C13

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {W : Type} [CommGroup W] [Finite W]

theorem s16c167_norm_irr_nontrivial {L : Subgroup (MulAut W)} {V : Subgroup W}
    (hV : XMod.IsIrr ↥L V) (hc : Nat.card ↥V = 8) : ∃ x ∈ L, ∃ v ∈ V, x v ≠ v := by
  by_contra hcon
  have htriv : ∀ x ∈ L, ∀ v ∈ V, x v = v := by
    intro x hx v hv
    by_contra hne
    exact hcon ⟨x, hx, v, hv, hne⟩
  obtain ⟨x₀, hx₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥V) 2 (by rw [hc]; norm_num)
  let J : Subgroup W := Subgroup.zpowers (x₀ : W)
  have hxV : (x₀ : W) ∈ V := x₀.2
  have hJV : J ≤ V := Subgroup.zpowers_le.mpr hxV
  have hJcard : Nat.card J = 2 := by
    change Nat.card (Subgroup.zpowers (x₀ : W)) = 2
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx₀]
  have hJinv : XMod.IsInv ↥L J := by
    intro a l hl
    have hlV : l ∈ V := hJV hl
    have hfix : (a : MulAut W) l = l := htriv a a.2 l hlV
    show (a : MulAut W) l ∈ J
    rw [hfix]; exact hl
  have hJbot : J ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hJcard
    omega
  have hJtop : J ≠ V := by
    intro h
    rw [h, hc] at hJcard
    omega
  rcases hV.2.2 J hJinv bot_le hJV with h | h
  · exact hJbot h
  · exact hJtop h

theorem s16c167_norm_eq_one_of_commute {L : Subgroup (MulAut W)} (hL : IsPSL 3 2 1 ↥L)
    {g : MulAut W} (hg : g ∈ L) (hgc : ∀ y ∈ L, g * y = y * g) : g = 1 := by
  haveI : IsSimpleGroup ↥L := (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 1 hL).2
  have hcenter : Subgroup.center ↥L = ⊥ := by
    refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥L)).resolve_right ?_
    intro ht
    haveI : IsMulCommutative ↥L := Subgroup.center_eq_top_iff.mp ht
    have hp : (Nat.card ↥L).Prime := (Group.is_simple_iff_prime_card (α := ↥L)).mp inferInstance
    rw [card_eq_168_of_isPSL_three_two hL] at hp
    exact absurd hp (by norm_num)
  have hg_center : (⟨g, hg⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hgc (y : ↥L) y.2).symm
  have hg1 : (⟨g, hg⟩ : ↥L) = 1 := by
    have hmem : (⟨g, hg⟩ : ↥L) ∈ (⊥ : Subgroup ↥L) := by
      rw [← hcenter]
      exact hg_center
    simpa using hmem
  exact congrArg Subtype.val hg1

theorem s16c167_norm_fixes_of_commute (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    (hL : IsPSL 3 2 1 ↥L) {V : Subgroup W} (hV : XMod.IsIrr ↥L V) (hc : Nat.card ↥V = 8)
    {g : MulAut W} (hgL : ∀ y ∈ L, g * y = y * g) (hgV : g ∈ stabSub V) :
    ∀ v ∈ V, g v = v := by
  have hVinv : ∀ x ∈ L, ∀ v ∈ V, x v ∈ V := fun x hx v hv => hV.1 ⟨x, hx⟩ v hv
  have hnt : ∃ x ∈ L, ∃ v ∈ V, x v ≠ v := s16c167_norm_irr_nontrivial hV hc
  have hsurj : autSub L V = ⊤ := rank3_surj hW hL hVinv hc hnt
  have hmem : resHom V ⟨g, hgV⟩ ∈ autSub L V := by rw [hsurj]; exact Subgroup.mem_top _
  obtain ⟨l, hlL, hlres⟩ := mem_autSub.mp hmem
  have hl : ∀ v ∈ V, (l : MulAut W) v = g v := fun v hv => by
    have := congrArg (fun φ : MulAut ↥V => ((φ ⟨v, hv⟩ : ↥V) : W)) hlres
    exact this
  have hlinvV : ∀ w ∈ V, (l : MulAut W)⁻¹ w = g⁻¹ w := by
    intro w hw
    have hg_inv : g⁻¹ ∈ stabSub V := (stabSub V).inv_mem hgV
    have hgw : g⁻¹ w ∈ V := (mem_stabSub.mp hg_inv w).2 hw
    have h1 : (l : MulAut W) ((l : MulAut W)⁻¹ w) = w := mulAut_apply_inv_apply _ _
    have h2 : (l : MulAut W) (g⁻¹ w) = g (g⁻¹ w) := hl _ hgw
    have h3 : g (g⁻¹ w) = w := mulAut_apply_inv_apply _ _
    exact (l : MulAut W).injective (by rw [h1, h2, h3])
  have hlcent : ∀ y ∈ L, (l : MulAut W) * y = y * (l : MulAut W) := by
    intro y hy
    have hzL : ((l : MulAut W) * y * (l : MulAut W)⁻¹) * y⁻¹ ∈ L :=
      L.mul_mem (L.mul_mem (L.mul_mem hlL hy) (L.inv_mem hlL)) (L.inv_mem hy)
    have hzV : ∀ v ∈ V, (((l : MulAut W) * y * (l : MulAut W)⁻¹) * y⁻¹) v = v := by
      intro v hv
      have hyinv : y⁻¹ v ∈ V := hVinv y⁻¹ (L.inv_mem hy) v hv
      have hg_inv_yinv : g⁻¹ (y⁻¹ v) ∈ V := by
        have hg_inv : g⁻¹ ∈ stabSub V := (stabSub V).inv_mem hgV
        exact (mem_stabSub.mp hg_inv (y⁻¹ v)).2 hyinv
      have h1 : (l : MulAut W) (y ((l : MulAut W)⁻¹ (y⁻¹ v))) =
          g (y (g⁻¹ (y⁻¹ v))) := by
        rw [hlinvV _ hyinv]
        exact hl _ (hVinv y hy _ hg_inv_yinv)
      have h2 : g (y (g⁻¹ (y⁻¹ v))) = y (g (g⁻¹ (y⁻¹ v))) := by
        have := congrArg (fun z : MulAut W => z (g⁻¹ (y⁻¹ v))) (hgL y hy)
        simpa only [MulAut.mul_apply] using this
      have h3 : g (g⁻¹ (y⁻¹ v)) = y⁻¹ v := mulAut_apply_inv_apply _ _
      calc (((l : MulAut W) * y * (l : MulAut W)⁻¹) * y⁻¹) v
          = (l : MulAut W) (y ((l : MulAut W)⁻¹ (y⁻¹ v))) := by
            simp only [MulAut.mul_apply]
        _ = g (y (g⁻¹ (y⁻¹ v))) := h1
        _ = y (g (g⁻¹ (y⁻¹ v))) := h2
        _ = y (y⁻¹ v) := by rw [h3]
        _ = v := mulAut_apply_inv_apply y v
    have hz1 : ((l : MulAut W) * y * (l : MulAut W)⁻¹) * y⁻¹ = 1 :=
      rank3_inj hL hVinv hnt _ hzL hzV
    have hly : (l : MulAut W) * y * (l : MulAut W)⁻¹ = y := mul_inv_eq_one.mp hz1
    have hcongr := congrArg (fun z : MulAut W => z * (l : MulAut W)) hly
    simpa [mul_assoc] using hcongr
  have hl1 : (l : MulAut W) = 1 := s16c167_norm_eq_one_of_commute hL hlL hlcent
  intro v hv
  have h1 : (l : MulAut W) v = g v := hl v hv
  rw [hl1] at h1
  simpa using h1.symm

theorem s16c167_norm_fixes_irr_of_fixes_ne_one {L : Subgroup (MulAut W)} {V : Subgroup W}
    (hV : XMod.IsIrr ↥L V) {g : MulAut W} (hgL : ∀ y ∈ L, g * y = y * g) {m : W} (hm : m ∈ V)
    (hm1 : m ≠ 1) (hgm : g m = m) : ∀ v ∈ V, g v = v := by
  let F : Subgroup W :=
    { carrier := {v | v ∈ V ∧ g v = v}
      one_mem' := ⟨V.one_mem, map_one g⟩
      mul_mem' := fun ha hb => ⟨V.mul_mem ha.1 hb.1, by rw [map_mul, ha.2, hb.2]⟩
      inv_mem' := fun ha => ⟨V.inv_mem ha.1, by rw [map_inv, ha.2]⟩ }
  have hFV : F ≤ V := fun v hv => hv.1
  have hmF : m ∈ F := ⟨hm, hgm⟩
  have hFinv : XMod.IsInv ↥L F := by
    intro a u hu
    refine ⟨hV.1 a u hu.1, ?_⟩
    show g ((a : MulAut W) u) = (a : MulAut W) u
    calc g ((a : MulAut W) u) = (g * (a : MulAut W)) u := by
          simp only [MulAut.mul_apply]
      _ = ((a : MulAut W) * g) u := by rw [hgL (a : MulAut W) a.2]
      _ = (a : MulAut W) (g u) := by simp only [MulAut.mul_apply]
      _ = (a : MulAut W) u := by rw [hu.2]
  have hFne : F ≠ ⊥ := by
    intro h
    have hm_bot : m ∈ (⊥ : Subgroup W) := h ▸ hmF
    rw [Subgroup.mem_bot] at hm_bot
    exact hm1 hm_bot
  rcases hV.2.2 F hFinv bot_le hFV with h | h
  · exact absurd h hFne
  · intro v hv
    have hvF : v ∈ F := h.symm ▸ hv
    exact hvF.2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
