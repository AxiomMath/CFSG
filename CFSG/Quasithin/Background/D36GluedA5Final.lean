module

public import CFSG.Quasithin.Background.D36GluedA5Out
public import CFSG.Quasithin.Background.D36GluedNDFinal
public import CFSG.Quasithin.EmptyFaithful.T1521SA5Two
public import CFSG.Quasithin.Background.D36GluedA5Dich
public import CFSG.Quasithin.Background.D36GluedA5Lift
public import CFSG.Quasithin.Background.D36GluedA5Num
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod

public section

namespace CFSG.Quasithin

open CFSG.Quasithin.A5Mod

namespace A5Sec

variable {Y : Type} [CommGroup Y] {H : Subgroup (MulAut Y)} {U D : Subgroup Y}

theorem glueSecAct_fix_iff (hU : H ≤ stabSub U) (hD : H ≤ stabSub D) (a : ↥H) (u : ↥U) :
    glueSecAct hU hD a (QuotientGroup.mk u) = QuotientGroup.mk u ↔
      (a : MulAut Y) (u : Y) * (u : Y)⁻¹ ∈ D := by
  rw [glueSecAct_mk, mk_eq_mk_iff (U := D.subgroupOf U)]
  simp [Subgroup.mem_subgroupOf]

end A5Sec

open A5Sec

variable {Y : Type} [CommGroup Y] [Finite Y] {X A L₀ : Subgroup (MulAut Y)} {U U' : Subgroup Y}

namespace NDSetup

variable (S : NDSetup X A L₀ U U')

include S

theorem false_of_psl2_four (hL : IsPSL 2 2 2 ↥L₀) : False := by
  obtain ⟨e⟩ := nonempty_equiv_alt5_of_isPSL_two_two_two hL
  obtain ⟨hk, hū4, hū5, hs1, hs2, hsū⟩ := S.numerics hL
  obtain ⟨b₁, l, hb₁, hl, hb1, hbb, hll, hbl, l₀, g, hlu, hl₀2, hl₀1, hg3, hg1, hbg, hlg⟩ :=
    S.exists_outer_data e hk
  have hZU : U ⊓ fixV L₀ ≤ U := inf_le_left
  have hDZ : U ⊓ U' ≤ U ⊓ fixV L₀ := le_inf inf_le_left (fun d hd l hl => S.cent l hl d hd.2)
  have hZst : L₀ ≤ stabSub (U ⊓ fixV L₀) := le_stabSub_inf_fixV S.stab
  have hHU : L₀ ⊔ (A ⊓ stabSub U) ≤ stabSub U := sup_le S.stab inf_le_right
  have hHZ : L₀ ⊔ (A ⊓ stabSub U) ≤ stabSub (U ⊓ fixV L₀) :=
    sup_le hZst (fun b hb => S.mem_stabSub_inf_fixV hb)
  let act := glueSecAct hHU hHZ
  let actL := glueSecAct S.stab hZst
  have hcompat : ∀ l' : ↥L₀,
      act ⟨(l' : MulAut Y), Subgroup.mem_sup_left l'.2⟩ = actL l' := by
    intro l'
    apply MulEquiv.ext
    intro x
    induction x using QuotientGroup.induction_on with
    | H u => rfl
  have hnt : ∃ x : Sec U (U ⊓ fixV L₀), x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply S.not_le_fixV
    intro u hu
    have h1 : (QuotientGroup.mk ⟨u, hu⟩ : Sec U (U ⊓ fixV L₀)) = 1 := hcon _
    have h2 : (⟨u, hu⟩ : ↥U) ∈ (U ⊓ fixV L₀).subgroupOf U := (QuotientGroup.eq_one_iff _).1 h1
    exact h2.2
  have hinj : Function.Injective actL :=
    glueSecAct_injective S.stab hZst S.simple (S.exists_not_mem_Z hnt)
  have hSec2 : ∀ a : Sec U (U ⊓ fixV L₀), a ^ 2 = 1 := S.sec_sq
  have hrkSec : rk (Sec U (U ⊓ fixV L₀)) + rk ↥(U ⊓ fixV L₀) = rk ↥U := by
    have hcard := card_sec_mul (V := Y) (W := U) (U := U ⊓ fixV L₀) hZU
    unfold rk
    rw [← padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne', hcard]
  have hSec4 : 4 ≤ rk (Sec U (U ⊓ fixV L₀)) := by
    obtain ⟨ρ, hρ⟩ := exists_injective_GL_of_mulAut hSec2 actL hinj
    have hF2 : Nat.card (ZMod 2) = 2 ^ 1 := by rw [Nat.card_zmod]; norm_num
    have := two_mul_le_of_psl2_two (by norm_num) (by norm_num) hL hF2 ρ hρ
    omega
  have hDZrk : rk ↥(U ⊓ U') ≤ rk ↥(U ⊓ fixV L₀) := rk_mono hDZ
  have hrkU : rk ↥U = rk ↥(U ⊓ U') + (rk ↥U - rk ↥(U ⊓ U')) := by
    have : rk ↥(U ⊓ U') ≤ rk ↥U := rk_mono inf_le_left
    omega
  letI : MulDistribMulAction ↥L₀ (Sec U (U ⊓ fixV L₀)) := MulDistribMulAction.compHom _ actL
  have hsmul : ∀ (γ : ↥L₀) (x : Sec U (U ⊓ fixV L₀)), γ • x = actL γ x := fun _ _ => rfl
  have hfix : ∀ x : Sec U (U ⊓ fixV L₀), (∀ γ : ↥L₀, γ • x = x) → x = 1 := fun x hx =>
    sec_fixed S.perfect S.stab hZst x fun γ => by rw [← hsmul]; exact hx γ
  have hfaith : ∀ γ : ↥L₀, (∀ x : Sec U (U ⊓ fixV L₀), γ • x = x) → γ = 1 := fun γ h => by
    apply hinj
    rw [map_one]
    exact MulEquiv.ext fun x => h x
  let Hb : ↥(L₀ ⊔ (A ⊓ stabSub U)) := ⟨b₁, Subgroup.mem_sup_right hb₁⟩
  let Hl : ↥(L₀ ⊔ (A ⊓ stabSub U)) := ⟨l, Subgroup.mem_sup_right hl⟩
  have hcompat_l : act Hl = actL l₀ := by
    apply MulEquiv.ext
    intro x
    induction x using QuotientGroup.induction_on with
    | H u =>
      show glueSecAct hHU hHZ Hl (QuotientGroup.mk u) =
        glueSecAct S.stab hZst l₀ (QuotientGroup.mk u)
      rw [glueSecAct_mk, glueSecAct_mk]
      congr 1
      exact Subtype.ext (hlu u u.2)
  have htoMulAut : ∀ γ : ↥L₀,
      MulDistribMulAction.toMulAut ↥L₀ (Sec U (U ⊓ fixV L₀)) γ = actL γ :=
    fun γ => MulEquiv.ext fun x => rfl
  set Uh : Subgroup Y := commModSub U (A ⊓ stabSub U) (U ⊓ U') with hUh
  set π : ↥U →* Sec U (U ⊓ fixV L₀) := QuotientGroup.mk' ((U ⊓ fixV L₀).subgroupOf U) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  set K : Subgroup ↥U := Uh.subgroupOf U with hK
  have hKcard : Nat.card ↥K = Nat.card ↥Uh :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (commModSub_le _ _ _)).toEquiv
  have hmemK : ∀ g ∈ K, ((g : ↥U) : Y) ∈ Uh := fun g hg => hg
  have hs2' : rk ↥U - rk ↥Uh = 2 := by
    by_contra hne
    have hs1' : rk ↥U - rk ↥Uh = 1 := by omega
    have hUcard : Nat.card ↥U ≤ 2 * Nat.card ↥K := by
      rw [hKcard, card_eq_two_pow S.exp U, card_eq_two_pow S.exp Uh]
      have h1 : rk ↥U ≤ rk ↥Uh + 1 := by omega
      calc 2 ^ rk ↥U ≤ 2 ^ (rk ↥Uh + 1) := Nat.pow_le_pow_right (by norm_num) h1
        _ = 2 * 2 ^ rk ↥Uh := by rw [pow_succ]; ring
    have hker : ∀ g ∈ K, commHom (MulDistribMulAction.toMulAut ↥L₀ (Sec U (U ⊓ fixV L₀)) l₀)
        (π g) = 1 := by
      intro g hg
      rw [commHom_apply, mul_inv_eq_one, htoMulAut]
      show glueSecAct S.stab hZst l₀ (QuotientGroup.mk g) = QuotientGroup.mk g
      rw [glueSecAct_fix_iff S.stab hZst l₀ g, ← hlu g g.2]
      exact hDZ ((hmemK g hg).2 l hl)
    exact A5Dich.false_of_five e (fun x => hSec2 x) hfaith hl₀2 hl₀1
      (card_range_commHom_le_two π hπs _ K hUcard hker)
  have hΓ : Nat.card ↥L₀ = 60 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Quasithin.G11.G118.gl24_card_alt5
  have hSecrk : rk (Sec U (U ⊓ fixV L₀)) = 4 := by omega
  have hM16 : Nat.card (Sec U (U ⊓ fixV L₀)) = 16 := by
    rw [card_eq_two_pow_of_isPGroup (isPGroup_two_of_sq_eq_one hSec2), hSecrk]
    norm_num
  have hb2 : act Hb * act Hb = 1 := by
    rw [← map_mul]
    have : Hb * Hb = 1 := Subtype.ext hbb
    rw [this, map_one]
  have hb1' : act Hb ≠ 1 := by
    intro h
    apply hb1
    have h1 : ∀ l' : ↥L₀, S.theta ⟨b₁, hb₁⟩ l' = l' := by
      intro l'
      apply hinj
      rw [← hcompat, ← hcompat]
      have e1 : (⟨((S.theta ⟨b₁, hb₁⟩ l' : ↥L₀) : MulAut Y),
          Subgroup.mem_sup_left (S.theta _ l').2⟩ : ↥(L₀ ⊔ (A ⊓ stabSub U))) =
          Hb * ⟨(l' : MulAut Y), Subgroup.mem_sup_left l'.2⟩ * Hb⁻¹ := Subtype.ext rfl
      rw [e1, map_mul, map_mul, map_inv, h]
      simp
    have h2 : S.theta ⟨b₁, hb₁⟩ = 1 := MulEquiv.ext h1
    have h3 : (⟨b₁, hb₁⟩ : ↥(A ⊓ stabSub U)) = 1 := S.theta_injective (h2.trans (map_one _).symm)
    exact congrArg Subtype.val h3
  have hbg' : act Hb * MulDistribMulAction.toMulAut ↥L₀ (Sec U (U ⊓ fixV L₀)) g =
      MulDistribMulAction.toMulAut ↥L₀ (Sec U (U ⊓ fixV L₀)) g * act Hb := by
    rw [htoMulAut, ← hcompat g, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hbg
  have hbl' : act Hb * MulDistribMulAction.toMulAut ↥L₀ (Sec U (U ⊓ fixV L₀)) l₀ =
      MulDistribMulAction.toMulAut ↥L₀ (Sec U (U ⊓ fixV L₀)) l₀ * act Hb := by
    rw [htoMulAut, ← hcompat_l, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hbl
  have hg3' : g ^ 3 = 1 := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, pow_two]
    exact hg3
  rcases A5Dich.dichotomy hΓ S.simple (fun x => hSec2 x) hM16 hfix hg3' hg1 hl₀2 hl₀1 hlg hb2
      hb1' hbg' hbl' with hcase | ⟨e₁, e₂, c, h1, h2, h3, h4, h5, h6, h7, h8, v, hv1, hv2, hv3, hv4⟩
  ·
    have hKC : K.map π ≤ fixSub (act Hb) ⊓
        fixSub (MulDistribMulAction.toMulAut ↥L₀ (Sec U (U ⊓ fixV L₀)) l₀) := by
      rintro _ ⟨g', hg', rfl⟩
      have hgU := hmemK g' hg'
      refine ⟨?_, ?_⟩
      · show act Hb (QuotientGroup.mk g') = QuotientGroup.mk g'
        exact (glueSecAct_fix_iff hHU hHZ Hb g').2 (hDZ (hgU.2 b₁ hb₁))
      · show actL l₀ (QuotientGroup.mk g') = QuotientGroup.mk g'
        rw [glueSecAct_fix_iff S.stab hZst l₀ g', ← hlu g' g'.2]
        exact hDZ (hgU.2 l hl)
    have hle := card_le_mul_of_map_le π K _ hKC
    have hker : Nat.card π.ker = Nat.card ↥(U ⊓ fixV L₀) := by
      rw [hπ, QuotientGroup.ker_mk']
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZU).toEquiv
    rw [hKcard, hker] at hle
    have hle2 : Nat.card ↥Uh ≤ 2 * Nat.card ↥(U ⊓ fixV L₀) :=
      hle.trans (Nat.mul_le_mul_right _ hcase)
    rw [card_eq_two_pow S.exp Uh, card_eq_two_pow S.exp (U ⊓ fixV L₀)] at hle2
    have : rk ↥Uh ≤ rk ↥(U ⊓ fixV L₀) + 1 := by
      have h' : 2 ^ rk ↥Uh ≤ 2 ^ (rk ↥(U ⊓ fixV L₀) + 1) := by rw [pow_succ]; linarith
      exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h'
    omega
  ·
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective v
    have hu₁ : (e₁ : MulAut Y) (u : Y) * (u : Y)⁻¹ ∈ U ⊓ fixV L₀ :=
      (glueSecAct_fix_iff S.stab hZst e₁ u).1 hv2
    have huc : (c : MulAut Y) (u : Y) * (u : Y)⁻¹ ∈ U ⊓ fixV L₀ :=
      (glueSecAct_fix_iff S.stab hZst c u).1 hv4
    have huZ : (u : Y) ∉ U ⊓ fixV L₀ := fun hu => hv1 ((QuotientGroup.eq_one_iff _).2 hu)
    have hr : rk ↥U - rk ↥(U ⊓ fixV L₀) ≤ 4 := by omega
    have hsu : 5 ≤ (rk ↥U - rk ↥Uh) + (rk ↥U - rk ↥(U ⊓ U')) := by omega
    exact S.false_of_klein e₁.2 e₂.2 c.2 (congrArg Subtype.val h1) (congrArg Subtype.val h2)
      (congrArg Subtype.val h3) (fun h => h4 (Subtype.ext h)) (fun h => h5 (Subtype.ext h))
      (fun h => h6 (Subtype.ext h)) (congrArg Subtype.val h7) (congrArg Subtype.val h8) u.2
      huZ hu₁ huc hk hr hsu

end NDSetup

theorem ndResidualL24_holds : NDResidualL24 :=
  fun _ _ _ _ _ _ _ _ S hL => S.false_of_psl2_four hL

end CFSG.Quasithin
