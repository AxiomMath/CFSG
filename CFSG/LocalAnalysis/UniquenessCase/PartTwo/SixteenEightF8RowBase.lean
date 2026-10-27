module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8Pred
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8Cent
import CFSG.LocalAnalysis.GLTheoremA.CatA.SFM12Block

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

structure S16gRowCtx (D : Data G) (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V) : Prop where
  std : S16gStd D
  setting : Setting16 D V₀ V L
  conc : Conc4_136 D V₀ V hV L
  s1 : s15 D.M V₀ V hV L = 1
  quasi : CFSG.Open.IsQuasisimple ↥(lBar V₀ V hV L)

variable {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}

theorem S16gRowCtx.comm_top (h : S16gRowCtx D V₀ V L hV) :
    commSub ⊤ (lBar V₀ V hV L) = ⊤ :=
  wTil_eq_top_of_case163_2 h.conc h.s1

theorem S16gRowCtx.mBar_le_normalizer (h : S16gRowCtx D V₀ V L hV) :
    Mbar D.M V₀ V hV ≤ Subgroup.normalizer
      (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) := by
  intro g hg
  by_contra hgn
  obtain ⟨t, -, -, -, -, -, hconj, -⟩ := h.conc
  have h2 := (hconj g hg hgn).2
  rw [h.comm_top] at h2
  have hfix := commSub_eq_bot_iff.1 h2
  have hbot : (lBar V₀ V hV L).map (MulAut.conj g).toMonoidHom = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    exact MulEquiv.ext fun v => hfix (Subgroup.mem_top v) x hx
  have hbot' := (Subgroup.map_eq_bot_iff_of_injective (lBar V₀ V hV L)
    (f := (MulAut.conj g).toMonoidHom) (MulEquiv.injective (MulAut.conj g))).1 hbot
  refine CFSG.LocalAnalysis.GLTheoremA.SFM12.not_all_commute_of_quasisimple h.quasi
    fun a b => ?_
  have ha : (a : MulAut (Vtil V₀ V hV)) = 1 := Subgroup.mem_bot.1 (hbot' ▸ a.2)
  exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, ha, one_mul, mul_one])

theorem S16gRowCtx.exists_embedding (h : S16gRowCtx D V₀ V L hV) {ι : Type} [Fintype ι]
    [DecidableEq ι] {K : Type} [Field K] {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)}
    (hR : (FFModel.nat Γ).Realizes (lBar V₀ V hV L) (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L))) :
    ∃ ρ : ↥(Mbar D.M V₀ V hV) →* MulAut (Multiplicative (ι → K)),
      Function.Injective ρ ∧ ∀ a : ↥(Mbar D.M V₀ V hV), ρ a ∈ s16gNorm Γ := by
  refine s16g_exists_embedding (A := Mbar D.M V₀ V hV) (H := lBar V₀ V hV L)
    (barSub_mono V₀ V hV h.setting.hyp151.le) (fun a ha x hx => ?_)
    (s16g_realizes_top h.conc h.s1 Γ hR) h.comm_top
  have h1 := Subgroup.mem_normalizer_iff.1 (h.mBar_le_normalizer ha) x
  exact h1.1 hx

theorem S16gRowCtx.three_le_pRank (h : S16gRowCtx D V₀ V L hV) {p : ℕ} (hpσ : p ∈ D.sig) :
    3 ≤ CFSG.Open.pRank p (Mbar D.M V₀ V hV) :=
  s16c1610_three_le_pRank_mBar_of_four D h.std.hx h.std.h61 h.std.h127 h.setting.hyp16 hV
    h.std.h4 hpσ

private theorem s16g_exists_ne_one {ι : Type} [DecidableEq ι] [Nonempty ι] {K : Type} [Field K] :
    ∃ a : Multiplicative (ι → K), a ≠ 1 := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  refine ⟨Multiplicative.ofAdd (Pi.single i 1), fun h1 => ?_⟩
  have h2 := congrFun (ofAdd_eq_one.1 h1) i
  simp at h2

theorem S16gRowCtx.false_of_fixNc (h : S16gRowCtx D V₀ V L hV) {ι : Type} [Fintype ι]
    [DecidableEq ι] [Nonempty ι] {K : Type} [Field K] [Finite K]
    {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)}
    (hR : (FFModel.nat Γ).Realizes (lBar V₀ V hV L) (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)))
    {p : ℕ} (hpσ : p ∈ D.sig) (hfix : FixNc Γ p) : False :=
  s16g_false_of_fixNc D h.std hV h.setting h.conc h.s1 Γ hR s16g_exists_ne_one
    (D.sig_prime p hpσ).1 (D.sig_prime p hpσ).2 hpσ hfix

theorem S16gRowCtx.false_of_fixOrd (h : S16gRowCtx D V₀ V L hV) {ι : Type} [Fintype ι]
    [DecidableEq ι] [Nonempty ι] {K : Type} [Field K] [Finite K]
    {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)}
    (hR : (FFModel.nat Γ).Realizes (lBar V₀ V hV L) (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)))
    {p : ℕ} (hpσ : p ∈ D.sig)
    (hz : Odd (Nat.card (Subgroup.center ↥(lBar V₀ V hV L))))
    (hmult : ¬ p ∣ Nat.card (CFSG.Open.griessHopfMultiplier ↥(lBar V₀ V hV L)))
    (hrk : CFSG.Open.pRank p (Mbar D.M V₀ V hV) ≤ 3) (hfix : FixOrd Γ p) : False :=
  s16g_false_of_fixOrd D h.std hV h.setting h.conc h.s1 Γ hR s16g_exists_ne_one h.quasi hz
    (D.sig_prime p hpσ).1 (D.sig_prime p hpσ).2 hpσ hmult
    (s16g_dvd_card_cTilde D h.std h.setting hpσ hrk) hfix

theorem S16gRowCtx.hom_eq_one (h : S16gRowCtx D V₀ V L hV) {p : ℕ} (hpσ : p ∈ D.sig)
    {C : Type*} [Group C] (hC : ∀ c : C, c ^ p = 1) (φ : ↥(Mbar D.M V₀ V hV) →* C) : φ = 1 := by
  have hp : p.Prime := (D.sig_prime p hpσ).1
  have hMst : D.M ≤ stabTil V₀ V := s16g_le_stabTil h.setting
  have hOp : UC22.F10.OpRes p D.M = D.M :=
    h.std.h638 p hp (D.sig_prime p hpσ).2 (Or.inl hpσ)
  have hrange : (barHom V₀ V hV hMst).range = Mbar D.M V₀ V hV := range_barHom V₀ V hV hMst
  have hmem : ∀ m : ↥D.M, barHom V₀ V hV hMst m ∈ Mbar D.M V₀ V hV := fun m => by
    rw [← hrange]
    exact ⟨m, rfl⟩
  let ψ : ↥D.M →* C := φ.comp ((barHom V₀ V hV hMst).codRestrict _ hmem)
  have hψ : ψ.ker = ⊤ := by
    refine UC6.eq_top_of_isPGroup_quotient_of_opRes_eq_uc6 hp hOp ψ.ker fun g => ?_
    refine ⟨1, ?_⟩
    induction g using QuotientGroup.induction_on with
    | H m =>
      rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, MonoidHom.mem_ker, map_pow]
      exact hC _
  refine MonoidHom.ext fun x => ?_
  obtain ⟨m, hm⟩ : x.1 ∈ (barHom V₀ V hV hMst).range := by
    rw [hrange]
    exact x.2
  have h1 : ψ m = 1 := by
    have : m ∈ ψ.ker := by rw [hψ]; exact Subgroup.mem_top m
    exact this
  have hx : (barHom V₀ V hV hMst).codRestrict _ hmem m = x := Subtype.ext hm
  rw [MonoidHom.one_apply, ← hx]
  exact h1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
