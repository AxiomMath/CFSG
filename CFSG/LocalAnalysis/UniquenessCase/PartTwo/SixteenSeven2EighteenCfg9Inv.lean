module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg9Idx
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg9Nat

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {W : Type} [CommGroup W] [Finite W]

private theorem s16c167_isIrr_action_nontrivial {L : Subgroup (MulAut W)} {V : Subgroup W}
    (hV : XMod.IsIrr ↥L V) (hc : Nat.card ↥V = 8) :
    ∃ x ∈ L, ∃ v ∈ V, x v ≠ v := by
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

theorem s16c167_natSum3_uniform (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    (hL : IsPSL 3 2 1 ↥L) {V V' : Subgroup W} (hV : XMod.IsIrr ↥L V) (hV' : XMod.IsIrr ↥L V')
    (hc : Nat.card ↥V = 8) (hc' : Nat.card ↥V' = 8) {t : MulAut W}
    (hn : L.map (MulAut.conj t).toMonoidHom = L) (hVt : V.map t.toMonoidHom = V)
    (hV't : V'.map t.toMonoidHom = V') (h : ∀ v ∈ V', t v = v) : ∀ v ∈ V, t v = v := by
  have hVinv : ∀ x ∈ L, ∀ v ∈ V, x v ∈ V := fun x hx v hv => hV.1 ⟨x, hx⟩ v hv
  have hV'inv : ∀ x ∈ L, ∀ v ∈ V', x v ∈ V' := fun x hx v hv => hV'.1 ⟨x, hx⟩ v hv
  have hnt : ∃ x ∈ L, ∃ v ∈ V, x v ≠ v := s16c167_isIrr_action_nontrivial hV hc
  have hnt' : ∃ x ∈ L, ∃ v ∈ V', x v ≠ v := s16c167_isIrr_action_nontrivial hV' hc'
  have htL : ∀ y ∈ L, t * y * t⁻¹ ∈ L := by
    intro y hy
    have hmem : (MulAut.conj t).toMonoidHom y ∈ L.map (MulAut.conj t).toMonoidHom :=
      Subgroup.mem_map_of_mem ((MulAut.conj t).toMonoidHom) hy
    rw [hn] at hmem
    simpa [MulAut.conj_apply] using hmem
  have htinv_on : ∀ w ∈ V', t⁻¹ w = w := by
    intro w hw
    have hmem : t⁻¹ w ∈ V' := by
      have h1 : w ∈ V'.map t.toMonoidHom := by rw [hV't]; exact hw
      obtain ⟨u, hu, huw⟩ := Subgroup.mem_map.mp h1
      have h2 : t⁻¹ w = u := by
        rw [← huw]
        exact mulAut_inv_apply_apply t u
      rw [h2]; exact hu
    have h1 : t (t⁻¹ w) = t⁻¹ w := h _ hmem
    rw [mulAut_apply_inv_apply] at h1
    exact h1.symm
  have htcent : ∀ y ∈ L, t * y = y * t := by
    intro y hy
    have hzL : (t * y * t⁻¹) * y⁻¹ ∈ L := L.mul_mem (htL y hy) (L.inv_mem hy)
    have hzV' : ∀ v ∈ V', ((t * y * t⁻¹) * y⁻¹) v = v := by
      intro v hv
      have hyinv : y⁻¹ v ∈ V' := hV'inv y⁻¹ (L.inv_mem hy) v hv
      have h1 : t⁻¹ (y⁻¹ v) = y⁻¹ v := htinv_on _ hyinv
      have h2 : t v = v := h v hv
      calc ((t * y * t⁻¹) * y⁻¹) v
          = t (y (t⁻¹ (y⁻¹ v))) := by simp only [MulAut.mul_apply]
        _ = t (y (y⁻¹ v)) := by rw [h1]
        _ = t v := by rw [mulAut_apply_inv_apply]
        _ = v := h2
    have hz1 : (t * y * t⁻¹) * y⁻¹ = 1 := rank3_inj hL hV'inv hnt' _ hzL hzV'
    have hty : t * y * t⁻¹ = y := mul_inv_eq_one.mp hz1
    have := congrArg (fun z : MulAut W => z * t) hty
    simpa [mul_assoc] using this
  have hstabV : t ∈ stabSub V := by
    rw [mem_stabSub]
    intro u
    constructor
    · intro hu
      have h1 : t u ∈ V.map t.toMonoidHom := by rw [hVt]; exact hu
      obtain ⟨u', hu', hu'eq⟩ := Subgroup.mem_map.mp h1
      have h2 : u = u' := (t.injective hu'eq).symm
      rw [h2]; exact hu'
    · intro hu
      have h1 : t u ∈ V.map t.toMonoidHom := Subgroup.mem_map_of_mem t.toMonoidHom hu
      rwa [hVt] at h1
  have hsurj : autSub L V = ⊤ := rank3_surj hW hL hVinv hc hnt
  have hmem : resHom V ⟨t, hstabV⟩ ∈ autSub L V := by rw [hsurj]; exact Subgroup.mem_top _
  obtain ⟨g, hgL, hg⟩ := mem_autSub.mp hmem
  have hl : ∀ v ∈ V, (g : MulAut W) v = t v := fun v hv => by
    have := congrArg (fun φ : MulAut ↥V => ((φ ⟨v, hv⟩ : ↥V) : W)) hg
    exact this
  have hgcent : ∀ y ∈ L, (g : MulAut W) * y = y * (g : MulAut W) := by
    intro y hy
    have hzL : ((g : MulAut W) * y * (g : MulAut W)⁻¹) * y⁻¹ ∈ L :=
      L.mul_mem (L.mul_mem (L.mul_mem hgL hy) (L.inv_mem hgL)) (L.inv_mem hy)
    have hzV : ∀ v ∈ V, (((g : MulAut W) * y * (g : MulAut W)⁻¹) * y⁻¹) v = v := by
      intro v hv
      have hyinv : y⁻¹ v ∈ V := hVinv y⁻¹ (L.inv_mem hy) v hv
      have hg_inv_mem : (g : MulAut W)⁻¹ ∈ stabSub V := (stabSub V).inv_mem g.2
      have hwV : (g : MulAut W)⁻¹ (y⁻¹ v) ∈ V :=
        (mem_stabSub.mp hg_inv_mem (y⁻¹ v)).2 hyinv
      have hgw : (g : MulAut W) ((g : MulAut W)⁻¹ (y⁻¹ v)) = y⁻¹ v :=
        mulAut_apply_inv_apply (g : MulAut W) (y⁻¹ v)
      have hlt : (g : MulAut W) (y ((g : MulAut W)⁻¹ (y⁻¹ v))) =
          t (y ((g : MulAut W)⁻¹ (y⁻¹ v))) := hl _ (hVinv y hy _ hwV)
      have htw : t ((g : MulAut W)⁻¹ (y⁻¹ v)) = y⁻¹ v :=
        (hl _ hwV).symm.trans hgw
      have hty : t (y ((g : MulAut W)⁻¹ (y⁻¹ v))) =
          y (t ((g : MulAut W)⁻¹ (y⁻¹ v))) := by
        have hc := congrArg (fun z : MulAut W => z ((g : MulAut W)⁻¹ (y⁻¹ v))) (htcent y hy)
        simpa only [MulAut.mul_apply] using hc
      calc (((g : MulAut W) * y * (g : MulAut W)⁻¹) * y⁻¹) v
          = (g : MulAut W) (y ((g : MulAut W)⁻¹ (y⁻¹ v))) := by
            simp only [MulAut.mul_apply]
        _ = t (y ((g : MulAut W)⁻¹ (y⁻¹ v))) := hlt
        _ = y (t ((g : MulAut W)⁻¹ (y⁻¹ v))) := hty
        _ = y (y⁻¹ v) := by rw [htw]
        _ = v := mulAut_apply_inv_apply y v
    have hz1 : ((g : MulAut W) * y * (g : MulAut W)⁻¹) * y⁻¹ = 1 :=
      rank3_inj hL hVinv hnt _ hzL hzV
    have hgy : (g : MulAut W) * y * (g : MulAut W)⁻¹ = y := mul_inv_eq_one.mp hz1
    have := congrArg (fun z : MulAut W => z * (g : MulAut W)) hgy
    simpa [mul_assoc] using this
  have hcenter : Subgroup.center ↥L = ⊥ := by
    haveI : IsSimpleGroup ↥L := (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 1 hL).2
    refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥L)).resolve_right ?_
    intro ht
    haveI : IsMulCommutative ↥L := Subgroup.center_eq_top_iff.mp ht
    have hp : (Nat.card ↥L).Prime := (Group.is_simple_iff_prime_card (α := ↥L)).mp inferInstance
    rw [card_eq_168_of_isPSL_three_two hL] at hp
    exact absurd hp (by norm_num)
  have hg_center : (⟨(g : MulAut W), hgL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hgcent (y : ↥L) y.2).symm
  have hg1 : (g : MulAut W) = 1 := by
    have h1 : (⟨(g : MulAut W), hgL⟩ : ↥L) = 1 := by
      have hmem : (⟨(g : MulAut W), hgL⟩ : ↥L) ∈ (⊥ : Subgroup ↥L) := by
        rw [← hcenter]
        exact hg_center
      simpa using hmem
    exact congrArg Subtype.val h1
  intro v hv
  have h1 : (g : MulAut W) v = t v := hl v hv
  rw [hg1] at h1
  simpa using h1.symm

private theorem s16c167_inf_map_eq_bot_of_isIrr {L : Subgroup (MulAut W)} {R : Subgroup W}
    (hR : XMod.IsIrr ↥L R) {t : MulAut W}
    (htn : t ∈ Subgroup.normalizer (L : Set (MulAut W)))
    (hne : R.map t.toMonoidHom ≠ R) : R ⊓ R.map t.toMonoidHom = ⊥ := by
  have hR' : XMod.IsIrr ↥L (R.map t.toMonoidHom) := isIrr_map htn hR
  rcases hR.2.2 (R ⊓ R.map t.toMonoidHom) (hR.1.inf hR'.1) bot_le inf_le_left with h | h
  · exact h
  · exfalso
    have hle : R ≤ R.map t.toMonoidHom := inf_eq_left.mp h
    have hcard : Nat.card ↥(R.map t.toMonoidHom) = Nat.card ↥R :=
      Subgroup.card_map_of_injective t.injective
    have heq : R = R.map t.toMonoidHom := Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard)
    exact hne heq.symm

private theorem s16c167_moved_le_mQuot (hW : ∀ w : W, w ^ 2 = 1) (t : MulAut W)
    {J R : Subgroup W} (hRJ : R ≤ J) (hcR : Nat.card ↥R = 8)
    (hdisj : R ⊓ R.map t.toMonoidHom = ⊥) :
    3 ≤ E3.mQuot J (J ⊓ fixV (Subgroup.zpowers t)) := by
  have h := s16c167_rk_le_mQuot_of_inf_map_eq_bot hW t hRJ hdisj
  have hrk : rk ↥R = 3 := by
    have h2 := card_eq_two_pow hW R
    rw [hcR] at h2
    have h3 : (2 : ℕ) ^ 3 = 2 ^ rk ↥R := by rw [← h2]; norm_num
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 2) h3).symm
  omega

theorem s16c167_natSum3_involution (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    (hL : IsPSL 3 2 1 ↥L) {J : Subgroup W} (hJ : NatSum3 L J) {t : MulAut W} (ht : t * t = 1)
    (hn : L.map (MulAut.conj t).toMonoidHom = L) (hJt : J.map t.toMonoidHom = J) :
    J ≤ fixV (Subgroup.zpowers t) ∨ 3 ≤ E3.mQuot J (J ⊓ fixV (Subgroup.zpowers t)) := by
  obtain ⟨I₀, I₁, I₂, hi₀, hi₁, hi₂, hc₀, hc₁, hc₂, h01, h012, rfl⟩ := hJ
  have htn : t ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hn
  have uniform_pair : ∀ {A B : Subgroup W}, XMod.IsIrr ↥L A → XMod.IsIrr ↥L B →
      Nat.card ↥A = 8 → Nat.card ↥B = 8 →
      A.map t.toMonoidHom = A → B.map t.toMonoidHom = B →
      B ≤ fixV (Subgroup.zpowers t) → A ≤ fixV (Subgroup.zpowers t) := by
    intro A B hA hB hcA hcB hAt hBt hBle
    have htriv : ∀ v ∈ B, t v = v := fun v hv => (mem_fixV_zpowers t v).mp (hBle hv)
    have hone : ∀ v ∈ A, t v = v :=
      s16c167_natSum3_uniform hW hL hA hB hcA hcB hn hAt hBt htriv
    intro v hv
    exact (mem_fixV_zpowers t v).mpr (hone v hv)
  by_cases h0 : I₀.map t.toMonoidHom = I₀
  · by_cases h1 : I₁.map t.toMonoidHom = I₁
    · by_cases h2 : I₂.map t.toMonoidHom = I₂
      · have hiff01 : I₀ ≤ fixV (Subgroup.zpowers t) ↔ I₁ ≤ fixV (Subgroup.zpowers t) :=
          ⟨fun hh => uniform_pair hi₁ hi₀ hc₁ hc₀ h1 h0 hh,
           fun hh => uniform_pair hi₀ hi₁ hc₀ hc₁ h0 h1 hh⟩
        have hiff02 : I₀ ≤ fixV (Subgroup.zpowers t) ↔ I₂ ≤ fixV (Subgroup.zpowers t) :=
          ⟨fun hh => uniform_pair hi₂ hi₀ hc₂ hc₀ h2 h0 hh,
           fun hh => uniform_pair hi₀ hi₂ hc₀ hc₂ h0 h2 hh⟩
        by_cases hI0 : I₀ ≤ fixV (Subgroup.zpowers t)
        · left
          exact sup_le (sup_le hI0 (hiff01.mp hI0)) (hiff02.mp hI0)
        · right
          exact s16c167_three_le_mQuot_of_blocks hW t h01 h012 h0 h1 h2 hI0
            (fun hh => hI0 (hiff01.mpr hh)) (fun hh => hI0 (hiff02.mpr hh))
      · right
        exact s16c167_moved_le_mQuot hW t le_sup_right hc₂
          (s16c167_inf_map_eq_bot_of_isIrr hi₂ htn h2)
    · right
      exact s16c167_moved_le_mQuot hW t (le_sup_right.trans le_sup_left) hc₁
        (s16c167_inf_map_eq_bot_of_isIrr hi₁ htn h1)
  · right
    exact s16c167_moved_le_mQuot hW t (le_sup_left.trans le_sup_left) hc₀
      (s16c167_inf_map_eq_bot_of_isIrr hi₀ htn h0)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
