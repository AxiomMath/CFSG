module

public import CFSG.Quasithin.Background.D36GluedGL
public import CFSG.Quasithin.Background.F918Z4bSz
public import CFSG.Quasithin.Background.F918Z4bJ1
import CFSG.Quasithin.Background.F918Z4bPrime
import CFSG.Quasithin.Background.F918Z4c1Sz
import CFSG.Quasithin.Background.F918Z4c1J1
import CFSG.Quasithin.Background.F918Z4e
public import CFSG.Quasithin.Background.D36GluedOffender

public section

namespace CFSG.Quasithin

section Sec

variable {Y : Type} [CommGroup Y] {L₀ : Subgroup (MulAut Y)} {U D : Subgroup Y}

@[expose] noncomputable def glueSecAct (hU : L₀ ≤ stabSub U) (hD : L₀ ≤ stabSub D) :
    ↥L₀ →* MulAut (Sec U D) :=
  (quotHom (D.subgroupOf U)).comp
    (((resHom U).comp (Subgroup.inclusion hU)).codRestrict (stabSub (D.subgroupOf U))
      fun l => autSub_le_stabSub_subgroupOf hD
        (mem_autSub.mpr ⟨Subgroup.inclusion hU l, l.2, rfl⟩))

theorem glueSecAct_mk (hU : L₀ ≤ stabSub U) (hD : L₀ ≤ stabSub D) (l : ↥L₀) (u : ↥U) :
    glueSecAct hU hD l (QuotientGroup.mk u) =
      QuotientGroup.mk ⟨l.1 (u : Y), (hU l.2 (u : Y)).2 u.2⟩ := rfl

theorem glueSecAct_injective (hU : L₀ ≤ stabSub U) (hD : L₀ ≤ stabSub D)
    (hsimple : IsSimpleGroup ↥L₀) (hnt : ∃ l ∈ L₀, ∃ u ∈ U, l u * u⁻¹ ∉ D) :
    Function.Injective (glueSecAct hU hD) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (glueSecAct hU hD).ker with h | h
  · exact h
  · exfalso
    obtain ⟨l, hl, u, hu, hlu⟩ := hnt
    have hker : (⟨l, hl⟩ : ↥L₀) ∈ (glueSecAct hU hD).ker := by rw [h]; trivial
    rw [MonoidHom.mem_ker] at hker
    have h1 := congrArg (fun φ : MulAut (Sec U D) => φ (QuotientGroup.mk ⟨u, hu⟩)) hker
    simp only [glueSecAct_mk, MulAut.one_apply] at h1
    apply hlu
    have h2 := (mk_eq_mk_iff (U := D.subgroupOf U) _ _).1 h1
    exact h2

end Sec

section Rank

theorem rk_le_of_autRankLe_simple {G : Type} [Group G] [Finite G] (hsimple : IsSimpleGroup G)
    (hnonab : ∃ a b : G, a * b ≠ b * a) {m : ℕ} (hAut : AutRankLe G m) {E : Subgroup G}
    (hE : IsElemAb2 E) : rk E ≤ m := by
  have hc : Subgroup.center G = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnonab
      apply hab
      have : a ∈ Subgroup.center G := by rw [h]; trivial
      exact ((Subgroup.mem_center_iff.mp this) b).symm
  have hinj : Function.Injective (MulAut.conj : G →* MulAut G) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have : g ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro h
      have := congrArg (fun φ : MulAut G => φ h) hg
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this.symm
    rw [hc] at this
    exact Subgroup.mem_bot.mp this
  rw [← rk_map_eq_of_injective _ hinj]
  exact hAut _ (hE.map _)

end Rank

theorem not_orderOf_two_le_five {p : ℕ} (hp : p.Prime) (h11 : 11 ≤ p) (h31 : p ≠ 31) :
    ¬ orderOf (2 : ZMod p) ≤ 5 := by
  intro hle
  obtain ⟨i, hpos, hi5, hone⟩ : ∃ i : ℕ, 0 < i ∧ i ≤ 5 ∧ (2 : ZMod p) ^ i = 1 := by
    refine ⟨orderOf (2 : ZMod p), ?_, hle, pow_orderOf_eq_one _⟩
    haveI : Fact p.Prime := ⟨hp⟩
    have h2 : (2 : ZMod p) ≠ 0 := by
      intro h
      have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
      rw [ZMod.natCast_eq_zero_iff] at h'
      have := Nat.le_of_dvd (by norm_num) h'
      omega
    have hd := orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one h2)
    exact Nat.pos_of_ne_zero fun h0 => by
      rw [h0, zero_dvd_iff] at hd
      omega
  have hdvd : p ∣ 2 ^ i - 1 := by
    have h1 : 1 ≤ 2 ^ i := Nat.one_le_two_pow
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub h1, Nat.cast_pow, Nat.cast_ofNat, hone,
      Nat.cast_one, sub_self]
  interval_cases i
  · have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  · have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  · have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  · have h15 : p ∣ 3 * 5 := by simpa using hdvd
    rcases (Nat.Prime.dvd_mul hp).mp h15 with h3 | h3 <;>
      · have := Nat.le_of_dvd (by norm_num) h3
        omega
  · exact h31 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hdvd)

section Glued

variable {Y : Type} [CommGroup Y] [Finite Y] {X A L₀ : Subgroup (MulAut Y)} {U U' : Subgroup Y}

namespace GluedSwap

theorem exists_not_mem_of_diag (h : GluedSwap X A U U')
    (hdiag : ∀ b ∈ A ⊓ stabSub U, ∃ l ∈ L₀, ∀ u ∈ U, b u = l u) :
    ∃ l ∈ L₀, ∃ u ∈ U, l u * u⁻¹ ∉ U ⊓ U' := by
  obtain ⟨b, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h.ne_bot
  have hb1' : (b : MulAut Y) ≠ 1 := fun e => hb1 (Subtype.ext e)
  obtain ⟨l, hl, hbl⟩ := hdiag b b.2
  by_contra hcon
  push Not at hcon
  exact hb1' (h.faithful_mod b.2 fun u hu => by rw [hbl u hu]; exact hcon l hl u hu)

theorem exists_gl (h : GluedSwap X A U U') (hY : ∀ y : Y, y ^ 2 = 1)
    (hL₀ : ∀ l ∈ L₀, ∀ u ∈ U', l u = u) (hL₀U : L₀ ≤ stabSub U)
    (hdiag : ∀ b ∈ A ⊓ stabSub U, ∃ l ∈ L₀, ∀ u ∈ U, b u = l u) (hsimple : IsSimpleGroup ↥L₀) :
    ∃ d, d = rk ↥U - rk ↥(U ⊓ U') ∧
      ∃ ρ : ↥L₀ →* Matrix.GeneralLinearGroup (Fin d) (ZMod 2), Function.Injective ρ := by
  have hcent : L₀ ≤ centSub (U ⊓ U') := fun l hl d hd => hL₀ l hl d hd.2
  have hD : L₀ ≤ stabSub (U ⊓ U') := hcent.trans (centSub_le_stabSub _)
  have hinj := glueSecAct_injective hL₀U hD hsimple (h.exists_not_mem_of_diag hdiag)
  have hSec2 : ∀ a : Sec U (U ⊓ U'), a ^ 2 = 1 := by
    intro a
    induction a using QuotientGroup.induction_on with
    | H u =>
      have : u ^ 2 = 1 := Subtype.ext (hY u)
      rw [← QuotientGroup.mk_pow, this]
      rfl
  obtain ⟨ρ, hρ⟩ := exists_injective_GL_of_mulAut hSec2 (glueSecAct hL₀U hD) hinj
  refine ⟨rk (Sec U (U ⊓ U')), ?_, ρ, hρ⟩
  have hcard := card_sec_mul (V := Y) (W := U) (U := U ⊓ U') inf_le_left
  have h1 : rk (Sec U (U ⊓ U')) + rk ↥(U ⊓ U') = rk ↥U := by
    unfold rk
    rw [← padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne', hcard]
  omega

theorem ubar_le_of_autRankLe (h : GluedSwap X A U U') (hY : ∀ y : Y, y ^ 2 = 1)
    (hL₀ : ∀ l ∈ L₀, ∀ u ∈ U', l u = u)
    (hdiag : ∀ b ∈ A ⊓ stabSub U, ∃ l ∈ L₀, ∀ u ∈ U, b u = l u) (hsimple : IsSimpleGroup ↥L₀)
    (hnonab : ∃ a b : ↥L₀, a * b ≠ b * a) {m : ℕ} (hAut : AutRankLe ↥L₀ m) :
    rk ↥U - rk ↥(U ⊓ U') ≤ 2 * m + 1 := by
  have hRel := h.diag_isElemAbelian2 hL₀ hdiag
  have hkR := h.rk_le_diagSub hdiag hRel
  have hRL : glueDiagSub L₀ A U ≤ L₀ := glueDiagSub_le
  have hE : IsElemAb2 ((glueDiagSub L₀ A U).subgroupOf L₀) :=
    ⟨fun a ha b hb => Subtype.ext (hRel.1 _ ha _ hb), fun a ha => Subtype.ext (hRel.2 _ ha)⟩
  have hrk : rk ↥((glueDiagSub L₀ A U).subgroupOf L₀) = rk ↥(glueDiagSub L₀ A U) := by
    unfold rk
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRL).toEquiv]
  have hm := rk_le_of_autRankLe_simple hsimple hnonab hAut hE
  obtain ⟨hs1, -, hB⟩ := h.shape_B hY
  omega

theorem false_of_sz (h : GluedSwap X A U U')
    (hY : ∀ y : Y, y ^ 2 = 1) (hL₀ : ∀ l ∈ L₀, ∀ u ∈ U', l u = u) (hL₀U : L₀ ≤ stabSub U)
    (hdiag : ∀ b ∈ A ⊓ stabSub U, ∃ l ∈ L₀, ∀ u ∈ U, b u = l u) (hsimple : IsSimpleGroup ↥L₀)
    (hnonab : ∃ a b : ↥L₀, a * b ≠ b * a) {n : ℕ} (hn : 3 ≤ n) (hL : IsSz n ↥L₀) : False := by
  obtain ⟨d, hd, ρ, hρ⟩ := h.exists_gl hY hL₀ hL₀U hdiag hsimple
  have hu := h.ubar_le_of_autRankLe hY hL₀ hdiag hsimple hnonab (autRankLe_sz hn hL)
  have hF : Nat.card (ZMod 2) = 2 ^ 1 := by rw [Nat.card_zmod]; norm_num
  have h4 := four_mul_le_of_isSz hn hL hF ρ hρ
  omega

theorem false_of_j1
    (h : GluedSwap X A U U') (hY : ∀ y : Y, y ^ 2 = 1) (hL₀ : ∀ l ∈ L₀, ∀ u ∈ U', l u = u)
    (hL₀U : L₀ ≤ stabSub U) (hdiag : ∀ b ∈ A ⊓ stabSub U, ∃ l ∈ L₀, ∀ u ∈ U, b u = l u)
    (hsimple : IsSimpleGroup ↥L₀) (hnonab : ∃ a b : ↥L₀, a * b ≠ b * a)
    (hL : IsSporadic .J1 ↥L₀) : False := by
  obtain ⟨d, hd, ρ, hρ⟩ := h.exists_gl hY hL₀ hL₀U hdiag hsimple
  have hu := h.ubar_le_of_autRankLe hY hL₀ hdiag hsimple hnonab (autRankLe_j1 hL)
  have hF : Nat.card (ZMod 2) = 2 ^ 1 := by rw [Nat.card_zmod]; norm_num
  have h18 := eighteen_le_of_j1 hL hF ρ hρ
  omega

theorem false_of_psl2_prime (h : GluedSwap X A U U') (hY : ∀ y : Y, y ^ 2 = 1)
    (hL₀ : ∀ l ∈ L₀, ∀ u ∈ U', l u = u) (hL₀U : L₀ ≤ stabSub U)
    (hdiag : ∀ b ∈ A ⊓ stabSub U, ∃ l ∈ L₀, ∀ u ∈ U, b u = l u) (hsimple : IsSimpleGroup ↥L₀)
    (hnonab : ∃ a b : ↥L₀, a * b ≠ b * a) {p : ℕ} (hp : p.Prime) (h11 : 11 ≤ p) (h31 : p ≠ 31)
    (hL : IsPSL 2 p 1 ↥L₀) : False := by
  obtain ⟨d, hd, ρ, hρ⟩ := h.exists_gl hY hL₀ hL₀U hdiag hsimple
  have hu := h.ubar_le_of_autRankLe hY hL₀ hdiag hsimple hnonab
    (autRankLe_psl2_prime hp (by omega) hL)
  have hF : Nat.card (ZMod 2) = 2 ^ 1 := by rw [Nat.card_zmod]; norm_num
  have hcard : p ∣ Nat.card ↥L₀ := by
    have h2 := Z4e.two_mul_card_of_isPSL_two_odd hp (by omega) hL
    have hdvd : p ∣ 2 * Nat.card ↥L₀ := by rw [h2]; exact dvd_mul_right _ _
    have hcop : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).mpr (by omega)
    exact hcop.dvd_of_dvd_mul_left hdvd
  have hord := orderOf_two_le_of_prime_dvd_card hF ρ hρ hp (by omega) hcard
  exact not_orderOf_two_le_five hp h11 h31 (by omega)

end GluedSwap

end Glued

end CFSG.Quasithin
