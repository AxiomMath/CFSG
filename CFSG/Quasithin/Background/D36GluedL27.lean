module

public import CFSG.Quasithin.Background.D36GluedOther
import CFSG.Quasithin.Background.D36GluedL3Mod
public import CFSG.Quasithin.Background.D36GluedL3Rec
import CFSG.Quasithin.Background.D36GluedBig
import CFSG.Quasithin.Background.F918J3
import CFSG.Quasithin.Background.F918Z4bPrime
import CFSG.ClassicalInvolution.Q3.TL4D1ML32B

public section

namespace CFSG.Quasithin

open scoped commutatorElement

section Perfect

theorem commutator_eq_top_of_simple {G : Type} [Group G] (hsimple : IsSimpleGroup G)
    (hnonab : ∃ a b : G, a * b ≠ b * a) : commutator G = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnonab
    apply hab
    have hmem : ⁅a, b⁆ ∈ commutator G :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot] at hmem
    exact commutatorElement_eq_one_iff_mul_comm.mp hmem
  · exact h

variable {Y : Type} [CommGroup Y] {L₀ : Subgroup (MulAut Y)}

theorem perfect_comm_le (hperf : commutator ↥L₀ = ⊤) {U N : Subgroup Y}
    (hU : ∀ l ∈ L₀, ∀ y : Y, l y * y⁻¹ ∈ U) (hN : ∀ l ∈ L₀, ∀ u ∈ U, l u * u⁻¹ ∈ N) :
    ∀ l ∈ L₀, ∀ y : Y, l y * y⁻¹ ∈ N := by
  have hd : ∀ (a b : ↥L₀) (y : Y), (a : MulAut Y) ((b : MulAut Y) y) *
      ((b : MulAut Y) ((a : MulAut Y) y))⁻¹ ∈ N := by
    intro a b y
    have hub := hU b b.2 y
    have hua := hU a a.2 y
    have h1 := hN a a.2 _ hub
    have h2 := hN b b.2 _ hua
    rw [map_mul, map_inv] at h1 h2
    rw [glue_comm_identity (G := Y) ((a : MulAut Y) ((b : MulAut Y) y))
      ((b : MulAut Y) ((a : MulAut Y) y)) ((a : MulAut Y) y) ((b : MulAut Y) y) y]
    exact N.mul_mem h1 (N.inv_mem h2)
  let K : Subgroup ↥L₀ :=
    { carrier := {l | ∀ y : Y, (l : MulAut Y) y * y⁻¹ ∈ N}
      one_mem' := fun y => by simp
      mul_mem' := fun {a b} ha hb y => by
        have h1 := N.mul_mem (ha ((b : MulAut Y) y)) (hb y)
        have e : ((a * b : ↥L₀) : MulAut Y) y * y⁻¹ =
            (a : MulAut Y) ((b : MulAut Y) y) * ((b : MulAut Y) y)⁻¹ *
              ((b : MulAut Y) y * y⁻¹) := by
          change (a : MulAut Y) ((b : MulAut Y) y) * y⁻¹ = _
          rw [mul_assoc, inv_mul_cancel_left]
        rw [e]
        exact h1
      inv_mem' := fun {a} ha y => by
        have h1 := N.inv_mem (ha (((a⁻¹ : ↥L₀) : MulAut Y) y))
        have e : ((a⁻¹ : ↥L₀) : MulAut Y) y * y⁻¹ =
            ((a : MulAut Y) (((a⁻¹ : ↥L₀) : MulAut Y) y) *
              (((a⁻¹ : ↥L₀) : MulAut Y) y)⁻¹)⁻¹ := by
          have : (a : MulAut Y) (((a⁻¹ : ↥L₀) : MulAut Y) y) = y :=
            MulAut.apply_inv_self (M := Y) (a : MulAut Y) y
          rw [this, mul_inv_rev, inv_inv, mul_comm]
        rw [e]
        exact h1 }
  have hcomm : ∀ a b : ↥L₀, ⁅a, b⁆ ∈ K := by
    intro a b y
    set w : Y := ((b : MulAut Y) * (a : MulAut Y))⁻¹ y with hw
    have hy : (b : MulAut Y) ((a : MulAut Y) w) = y :=
      MulAut.apply_inv_self (M := Y) ((b : MulAut Y) * (a : MulAut Y)) y
    have e : (⁅a, b⁆ : ↥L₀) = (a * b) * (b * a)⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [e]
    show (a : MulAut Y) ((b : MulAut Y) w) * y⁻¹ ∈ N
    have h := hd a b w
    rw [hy] at h
    exact h
  have hKtop : K = ⊤ := by
    rw [eq_top_iff, ← hperf]
    exact Subgroup.commutator_le.mpr (fun a _ b _ => hcomm a b)
  intro l hl y
  have : (⟨l, hl⟩ : ↥L₀) ∈ K := by rw [hKtop]; trivial
  exact this y

theorem fixed_of_perfect (hperf : commutator ↥L₀ = ⊤) {Z : Subgroup Y} (hZ : Z ≤ fixV L₀) {x : Y}
    (hx : ∀ l ∈ L₀, l x * x⁻¹ ∈ Z) : ∀ l ∈ L₀, l x = x := by
  have hab : ∀ a b : ↥L₀,
      (a : MulAut Y) ((b : MulAut Y) x) = (b : MulAut Y) ((a : MulAut Y) x) := by
    intro a b
    have hzb : (b : MulAut Y) x * x⁻¹ ∈ Z := hx b b.2
    have hza : (a : MulAut Y) x * x⁻¹ ∈ Z := hx a a.2
    have e1 : (a : MulAut Y) ((b : MulAut Y) x) =
        ((b : MulAut Y) x * x⁻¹) * (a : MulAut Y) x := by
      have h1 : (b : MulAut Y) x = ((b : MulAut Y) x * x⁻¹) * x := by
        rw [inv_mul_cancel_right]
      conv_lhs => rw [h1]
      rw [map_mul, hZ hzb a a.2]
    have e2 : (b : MulAut Y) ((a : MulAut Y) x) =
        ((a : MulAut Y) x * x⁻¹) * (b : MulAut Y) x := by
      have h1 : (a : MulAut Y) x = ((a : MulAut Y) x * x⁻¹) * x := by
        rw [inv_mul_cancel_right]
      conv_lhs => rw [h1]
      rw [map_mul, hZ hza b b.2]
    rw [e1, e2]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  let K : Subgroup ↥L₀ := MulAction.stabilizer ↥L₀ x
  have hmemK : ∀ l : ↥L₀, l ∈ K ↔ (l : MulAut Y) x = x := fun l => MulAction.mem_stabilizer_iff
  have hcomm : ∀ a b : ↥L₀, ⁅a, b⁆ ∈ K := by
    intro a b
    have key : ∀ a b : ↥L₀, a⁻¹ * b⁻¹ * a * b ∈ K := by
      intro a b
      rw [hmemK]
      have e : a⁻¹ * b⁻¹ * a * b = (b * a)⁻¹ * (a * b) := by group
      rw [e]
      change (((b : MulAut Y) * (a : MulAut Y))⁻¹) ((a : MulAut Y) ((b : MulAut Y) x)) = x
      rw [hab a b]
      change (((b : MulAut Y) * (a : MulAut Y))⁻¹) (((b : MulAut Y) * (a : MulAut Y)) x) = x
      exact MulAut.inv_apply_self (M := Y) _ _
    have := key a⁻¹ b⁻¹
    rw [inv_inv, inv_inv] at this
    rw [commutatorElement_def]
    exact this
  have hKtop : K = ⊤ := by
    rw [eq_top_iff, ← hperf]
    exact Subgroup.commutator_le.mpr (fun a _ b _ => hcomm a b)
  intro l hl
  have : (⟨l, hl⟩ : ↥L₀) ∈ K := by rw [hKtop]; trivial
  exact (hmemK _).mp this

end Perfect

section Sec

variable {Y : Type} [CommGroup Y] {L₀ : Subgroup (MulAut Y)} {U : Subgroup Y}

theorem le_stabSub_inf_fixV (hU : L₀ ≤ stabSub U) : L₀ ≤ stabSub (U ⊓ fixV L₀) := by
  intro l hl z
  constructor
  · rintro ⟨hzU, hzf⟩
    refine ⟨(hU hl z).1 hzU, fun l' hl' => ?_⟩
    have h := hzf (l * l' * l⁻¹) (L₀.mul_mem (L₀.mul_mem hl hl') (L₀.inv_mem hl))
    have h2 : l (l' z) = l z := by
      have : (l * l' * l⁻¹) (l z) = l (l' z) := by
        simp only [MulAut.mul_apply]
        rw [MulAut.inv_apply_self (M := Y)]
      rw [this] at h
      exact h
    exact l.injective h2
  · rintro ⟨hzU, hzf⟩
    refine ⟨(hU hl z).2 hzU, fun l' hl' => ?_⟩
    rw [hzf l hl]
    exact hzf l' hl'

theorem sec_fixed (hperf : commutator ↥L₀ = ⊤) (hU : L₀ ≤ stabSub U)
    (hZ : L₀ ≤ stabSub (U ⊓ fixV L₀)) (x : Sec U (U ⊓ fixV L₀))
    (hx : ∀ l : ↥L₀, glueSecAct hU hZ l x = x) : x = 1 := by
  induction x using QuotientGroup.induction_on with
  | H u =>
    have h1 : ∀ l ∈ L₀, (l : MulAut Y) (u : Y) * (u : Y)⁻¹ ∈ U ⊓ fixV L₀ := by
      intro l hl
      have := hx ⟨l, hl⟩
      rw [glueSecAct_mk] at this
      exact (mk_eq_mk_iff (U := (U ⊓ fixV L₀).subgroupOf U) _ _).1 this
    have h3 := fixed_of_perfect hperf (inf_le_right : U ⊓ fixV L₀ ≤ fixV L₀) h1
    have hu : u ∈ (U ⊓ fixV L₀).subgroupOf U := ⟨u.2, fun l hl => h3 l hl⟩
    exact (QuotientGroup.eq_one_iff u).2 hu

theorem sec_perfect (hperf : commutator ↥L₀ = ⊤) (hU : L₀ ≤ stabSub U)
    (hZ : L₀ ≤ stabSub (U ⊓ fixV L₀)) (hUcomm : commV L₀ = U)
    (N : Subgroup (Sec U (U ⊓ fixV L₀)))
    (hN : ∀ (l : ↥L₀) (x : Sec U (U ⊓ fixV L₀)), glueSecAct hU hZ l x * x⁻¹ ∈ N) : N = ⊤ := by
  have h1 : ∀ l ∈ L₀, ∀ y : Y, l y * y⁻¹ ∈ U := fun l hl y => by
    rw [← hUcomm]
    exact Subgroup.subset_closure ⟨l, hl, y, rfl⟩
  have h2 : ∀ l ∈ L₀, ∀ u ∈ U, l u * u⁻¹ ∈ commSub U L₀ := fun l hl u hu =>
    Subgroup.subset_closure ⟨l, hl, u, hu, rfl⟩
  have h3 := perfect_comm_le hperf h1 h2
  have hle' : commV L₀ ≤ commSub U L₀ := (Subgroup.closure_le _).2 (by
    rintro _ ⟨l, hl, y, rfl⟩
    exact h3 l hl y)
  have hle : U ≤ commSub U L₀ := by
    intro u hu
    rw [← hUcomm] at hu
    exact hle' hu
  let N' : Subgroup ↥U := N.comap (QuotientGroup.mk' ((U ⊓ fixV L₀).subgroupOf U))
  have hgen : commSub U L₀ ≤ N'.map U.subtype := by
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨l, hl, w, hw, rfl⟩
    refine ⟨⟨l w, (hU hl w).2 hw⟩ * ⟨w, hw⟩⁻¹, ?_, rfl⟩
    have := hN ⟨l, hl⟩ (QuotientGroup.mk ⟨w, hw⟩)
    rw [glueSecAct_mk] at this
    show QuotientGroup.mk' ((U ⊓ fixV L₀).subgroupOf U)
      (⟨l w, (hU hl w).2 hw⟩ * ⟨w, hw⟩⁻¹) ∈ N
    rw [map_mul, map_inv]
    exact this
  rw [eq_top_iff]
  intro x _
  induction x using QuotientGroup.induction_on with
  | H u =>
    obtain ⟨u', hu'N, hu'⟩ := hgen (hle u.2)
    have : u' = u := Subtype.ext hu'
    rw [this] at hu'N
    exact hu'N

end Sec

section Bridge

variable {W : Type} [CommGroup W]

theorem commV_autSub_eq {L : Subgroup (MulAut W)} {VT : Subgroup W} (hL : L ≤ stabSub VT) :
    commV (autSub L VT) = (commSub VT L).subgroupOf VT := by
  apply le_antisymm
  · rw [commV, Subgroup.closure_le]
    rintro _ ⟨x, hx, v, rfl⟩
    obtain ⟨g, hgL, rfl⟩ := mem_autSub.mp hx
    show ((resHom VT g v * v⁻¹ : ↥VT) : W) ∈ commSub VT L
    have : ((resHom VT g v * v⁻¹ : ↥VT) : W) = g.1 (v : W) * (v : W)⁻¹ := rfl
    rw [this]
    exact Subgroup.subset_closure ⟨g.1, hgL, v, v.2, rfl⟩
  · intro u hu
    have hmem : (u : W) ∈ commSub VT L := hu
    have hsub : commSub VT L ≤ (commV (autSub L VT)).map VT.subtype := by
      rw [commSub, Subgroup.closure_le]
      rintro _ ⟨g, hg, w, hw, rfl⟩
      refine ⟨resHom VT ⟨g, hL hg⟩ ⟨w, hw⟩ * ⟨w, hw⟩⁻¹,
        Subgroup.subset_closure ⟨_, ?_, _, rfl⟩, rfl⟩
      exact mem_autSub.mpr ⟨⟨g, hL hg⟩, hg, rfl⟩
    obtain ⟨u', hu', hu'e⟩ := hsub hmem
    have : u' = u := Subtype.ext hu'e
    rw [this] at hu'
    exact hu'

end Bridge

section Glued

variable {Y : Type} [CommGroup Y] [Finite Y] {X A L₀ : Subgroup (MulAut Y)} {U U' : Subgroup Y}

namespace GluedSwap

theorem false_of_l27 (h : GluedSwap X A U U') (hY : ∀ y : Y, y ^ 2 = 1) (hL₀X : L₀ ≤ X)
    (hL₀ : ∀ l ∈ L₀, ∀ u ∈ U', l u = u) (hL₀U : L₀ ≤ stabSub U)
    (hdiag : ∀ b ∈ A ⊓ stabSub U, ∃ l ∈ L₀, ∀ u ∈ U, b u = l u)
    (hsimple : IsSimpleGroup ↥L₀) (hnonab : ∃ a b : ↥L₀, a * b ≠ b * a)
    (hiso : Nonempty (↥L₀ ≃* L3.Γ)) (hUcomm : commV L₀ = U) (hAut : AutRankLe ↥L₀ 2) : False := by
  obtain ⟨e⟩ := hiso
  have hperf := commutator_eq_top_of_simple hsimple hnonab
  have hZ := le_stabSub_inf_fixV hL₀U
  have hZU : U ⊓ fixV L₀ ≤ U := inf_le_left
  have hM2 : ∀ a : Sec U (U ⊓ fixV L₀), a ^ 2 = 1 := by
    intro a
    induction a using QuotientGroup.induction_on with
    | H u =>
      have : u ^ 2 = 1 := Subtype.ext (hY u)
      rw [← QuotientGroup.mk_pow, this]
      rfl
  let ρ : L3.Γ →* MulAut (Sec U (U ⊓ fixV L₀)) := (glueSecAct hL₀U hZ).comp e.symm.toMonoidHom
  letI : MulDistribMulAction L3.Γ (Sec U (U ⊓ fixV L₀)) := MulDistribMulAction.compHom _ ρ
  have hsmul : ∀ (g : L3.Γ) (x : Sec U (U ⊓ fixV L₀)), g • x = glueSecAct hL₀U hZ (e.symm g) x :=
    fun _ _ => rfl
  have hfix : ∀ x : Sec U (U ⊓ fixV L₀), (∀ g : L3.Γ, g • x = x) → x = 1 := fun x hx =>
    sec_fixed hperf hL₀U hZ x fun l => by
      have := hx (e l)
      rwa [hsmul, MulEquiv.symm_apply_apply] at this
  have hperfM : ∀ N : Subgroup (Sec U (U ⊓ fixV L₀)),
      (∀ (g : L3.Γ) (x : Sec U (U ⊓ fixV L₀)), (g • x) * x⁻¹ ∈ N) → N = ⊤ := fun N hN =>
    sec_perfect hperf hL₀U hZ hUcomm N fun l x => by
      have := hN (e l) x
      rwa [hsmul, MulEquiv.symm_apply_apply] at this
  have hcard32 : Nat.card (Sec U (U ⊓ fixV L₀)) ≤ 32 := by
    have hu := h.ubar_le_of_autRankLe hY hL₀ hdiag hsimple hnonab hAut
    have hDZ : U ⊓ U' ≤ U ⊓ fixV L₀ := le_inf inf_le_left (fun d hd l hl => hL₀ l hl d hd.2)
    have hdz := rk_mono hDZ
    have hsec := card_sec_mul (V := Y) (W := U) (U := U ⊓ fixV L₀) hZU
    rw [card_eq_two_pow hY U, card_eq_two_pow hY (U ⊓ fixV L₀)] at hsec
    have hpos : 0 < 2 ^ rk ↥(U ⊓ fixV L₀) := by positivity
    have h1 : Nat.card (Sec U (U ⊓ fixV L₀)) * 2 ^ rk ↥(U ⊓ fixV L₀) ≤
        32 * 2 ^ rk ↥(U ⊓ fixV L₀) := by
      rw [hsec]
      calc 2 ^ rk ↥U ≤ 2 ^ (rk ↥(U ⊓ fixV L₀) + 5) :=
            Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 32 * 2 ^ rk ↥(U ⊓ fixV L₀) := by rw [pow_add]; ring
    exact Nat.le_of_mul_le_mul_right h1 hpos
  have hnt : ∃ x : Sec U (U ⊓ fixV L₀), x ≠ 1 := by
    obtain ⟨l, hl, u, hu, hlu⟩ := h.exists_not_mem_of_diag hdiag
    refine ⟨QuotientGroup.mk ⟨u, hu⟩, fun h1 => hlu ?_⟩
    have h2 : (⟨u, hu⟩ : ↥U) ∈ (U ⊓ fixV L₀).subgroupOf U := (QuotientGroup.eq_one_iff _).1 h1
    have h3 : l u = u := h2.2 l hl
    rw [h3, mul_inv_cancel]
    exact (U ⊓ U').one_mem
  have hcard8 := L3Mod.card_eq_eight hM2 hfix hperfM hcard32 hnt
  have hnt' : ∃ l ∈ L₀, ∃ u ∈ U, l u * u⁻¹ ∉ U ⊓ fixV L₀ := by
    by_contra hcon
    push Not at hcon
    obtain ⟨x, hx1⟩ := hnt
    apply hx1
    apply sec_fixed hperf hL₀U hZ x
    intro l
    induction x using QuotientGroup.induction_on with
    | H u =>
      rw [glueSecAct_mk]
      exact (mk_eq_mk_iff _ _).2 (hcon l l.2 u u.2)
  have hinj := glueSecAct_injective hL₀U hZ hsimple hnt'
  have hL : Nat.card L₀ = 168 := by
    rw [Nat.card_congr e.toEquiv]
    exact L3Mod.card_Γ
  obtain ⟨D⟩ := exists_l3Data hY hZU hL₀U hZ hcard8 hinj hL
  exact h.false_of_L3Data hY hL₀X hL₀ hdiag D

end GluedSwap

end Glued

theorem nonab_of_equiv_sl3 {G : Type} [Group G] (e : G ≃* L3.Γ) : ∃ a b : G, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := L3Fin.nonabelian
  refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
  have := congrArg e h
  simpa using this

theorem d36GluedDiagL27_of_L38 (hL38 : D3L38) : D36GluedDiagL27 := by
  intro W _ _ M Mp T L V t n hd A hA hQ hAU hdiag hn24 hn3 hL27 hcub hshape
  have hsw := d36_gluedSwap hL38 n hA hQ hAU
  obtain ⟨e₃⟩ := nonempty_equiv_sl3_of_isPSL hL27
  haveI : IsSimpleGroup L3.Γ := CFSG.ClassicalInvolution.Q3.TL4.isSimpleGroup_sl3Two
  have hsimple : IsSimpleGroup ↥L := MulEquiv.isSimpleGroup e₃
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
  have hiso : ↥(autSub L (orbSup T V)) ≃* L3.Γ := e.symm.trans e₃
  have hL₀U : autSub L (orbSup T V) ≤
      stabSub ((commSub (orbSup T V) L).subgroupOf (orbSup T V)) :=
    autSub_le_stabSub_subgroupOf hLU
  exact hsw.false_of_l27 (d36_exp_VT n) (d36_L_le_X n) (d36_L_fix_Ut' hL38 n) hL₀U hdiag
    hsimple₀ (nonab_of_equiv_sl3 hiso) ⟨hiso⟩ (commV_autSub_eq hLstab)
    (autRankLe_psl2_prime Nat.prime_seven le_rfl (isPSL_congr e hL27))

theorem d36ActsGlued_of_nondiag
    (hL38 : D3L38) (hN : D36GluedNonDiag) : D36ActsGlued :=
  d36ActsGlued_of_residual hL38 (d36GluedDiagL3_of_L38 hL38)
      (d36GluedDiagOther_of_l27 hL38 (d36GluedDiagL27_of_L38 hL38)) hN

end CFSG.Quasithin
