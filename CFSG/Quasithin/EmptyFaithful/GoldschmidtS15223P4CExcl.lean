module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4COff
public import CFSG.Quasithin.Background.FLc3Pos

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL StatedClassicalModel StatedProj StatedLieTag StatedLieAdmissible
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

namespace S15223P4

namespace C

variable {G : Type} [Group G] [Finite G]

theorem false_of_sumNatDual {T Mc Z₁ Z₂ L : Subgroup G} (hF : Facts15128 T Mc Z₁ Z₂ L)
    (hoff : Q1Offender15128 T Mc Z₁ Z₂ L) (hsum : SumNatDual15127 Z₂ L) : False := by
  obtain ⟨hU, n, hn, π, U₁, U₂, hdirect, hreal1, hreal2⟩ := hsum
  let _ : CommGroup ↥(uOf1527 Z₂ L) := commGroupOfElemAbelian hU
  have hU2 : ∀ a ∈ uOf1527 Z₂ L, a ^ 2 = 1 := hU.2
  have hV2 : ∀ w : ↥(uOf1527 Z₂ L), w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hU2 w w.2)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hm : 1 ≤ m := by omega
  have hn3 : 3 ≤ m + 2 := by omega
  obtain ⟨D₁⟩ := FLc.vmodelNat hreal1
    (fun g hg z hz => by rw [Subgroup.mem_bot.1 hz]; exact map_one g)
  obtain ⟨D₂⟩ := FLc.vmodelDual hreal2
    (fun g hg z hz => by rw [Subgroup.mem_bot.1 hz]; exact map_one g)
  obtain ⟨a, ha⟩ := FLc.exists_ne_one_nat (by omega : 1 ≤ m + 2)
  have hU₁ne : U₁ ≠ ⊥ := FLc.ne_bot_of_surj D₁.β D₁.surj a ha
  have hne : (uLOf1527 Z₂ L).subgroupOf (uOf1527 Z₂ L) ≠ ⊥ := fun h =>
    hU₁ne (eq_bot_iff.2 (le_sup_left.trans (hdirect.1.le.trans h.le)))
  have hne' : uLOf1527 Z₂ L ≠ ⊥ := fun h => hne (by rw [h, Subgroup.bot_subgroupOf])
  obtain ⟨hh, hinj, hr1, hr2, hT, hfixS⟩ :=
    normalize_rho hF hn3 (FLc.rhoOf π) (FLc.rhoOf_surj hreal1.1) (FLc.rhoOf_mem π) hne'
  set ρ := (FLc.rhoOf π).comp (MulAut.conj hh).toMonoidHom with hρ
  have D₁' := D₁.rtwist hh
  have D₂' := D₂.rtwist hh
  have hQ1 : FLc.QI (m + 2) {1, m + 1} ≤ FLc.QI (m + 2) {1} :=
    (FLc.QI_le_QI_iff (fun j hj => by
      rw [Set.mem_singleton_iff] at hj
      subst hj
      exact ⟨le_rfl, by omega⟩)).2 (by simp)
  have hQ2 : FLc.QI (m + 2) {1, m + 1} ≤ FLc.QI (m + 2) {m + 1} :=
    (FLc.QI_le_QI_iff (fun j hj => by
      rw [Set.mem_singleton_iff] at hj
      subst hj
      exact ⟨by omega, by omega⟩)).2 (by simp)
  have hfixZ : ∀ x ∈ FLc.QI (m + 2) {1, m + 1}, ∀ v : ↥(uOf1527 Z₂ L),
      (v : G) ∈ zUOf1528 Z₂ L → ρ x v = v := by
    intro x hx v hv
    have hvU : v ∈ U₁ ⊔ U₂ := by
      rw [hdirect.1]
      exact hF.ZUle hv
    obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := Subgroup.mem_sup.1 hvU
    have hcomp : ∀ s ∈ FLc.Ut (m + 2), ρ s v₁ = v₁ ∧ ρ s v₂ = v₂ := fun s hs =>
      FLc.fixed_of_two hdirect.2 (ρ s) (fun u hu => D₁'.inv s u hu) (fun u hu => D₂'.inv s u hu)
        hv₁ hv₂ (hfixS s hs _ hv)
    have h1 := FLc.fixQ_of_model D₁' hV2 (by omega) (c := 1)
      (fun a ha i hi hic => FLc.fix_nat a ha i hi hic) hv₁ (fun s hs => (hcomp s hs).1)
    have h2 := FLc.fixQ_of_model D₂' hV2 (by omega) (c := m + 1)
      (fun a ha i hi hic => FLc.fix_dual (by omega) a ha i hi (by omega)) hv₂
      (fun s hs => (hcomp s hs).2)
    rw [map_mul, h1 x (hQ1 hx), h2 x (hQ2 hx)]
  have hQJ := autOn_ML_of_fixZ hF ρ hr2 hfixZ
  obtain ⟨hU', A, hAQ, hAoff⟩ := hoff
  have hA : A ≠ ⊥ := hAoff.2.1
  have hst := FLc.stSetting_ctx hF.hU ρ hinj hF.LU hF.SL (le_refl _) hF.ZU hF.SZ hF.S2 hr1 hr2
    (fun u hu => FLc.autOn_mono' (inf_le_left : s1516 T Z₁ ⊓ L ≤ s1516 T Z₁) (hT u hu))
  have hnormQ := FLc.normQ_of_ctx ρ hF.LU hF.MQ (inf_le_right : mZ1516 Mc Z₁ ⊓ L ≤ L) hQJ
  have hlt := FLc.not_ff_sum_any hm hst hV2 hdirect.2 D₁' D₂' (FLc.autOn_mono' hF.QS) hnormQ hAQ hA
  have hge := @FLc.card_le_of_offender ↥(uOf1527 Z₂ L) (commGroupOfElemAbelian hF.hU) _ _ hAoff
  exact absurd hlt (not_lt.2 hge)

variable {T Mc M H : Subgroup G} {B₀ : Subgroup (MulAut (V154 T Mc M))} {I X : Subgroup G}

@[expose] def NatOne (T Mc M : Subgroup G) (B₀ : Subgroup (MulAut (V154 T Mc M)))
    (X : Subgroup G) : Prop :=
  ∃ (hU : IsElemAbelian 2 (uOf1527 (zSOf T Mc M B₀) X)) (n : ℕ), (n = 4 ∨ n = 5) ∧
    @DirectSumOfCopies ↥(uOf1527 (zSOf T Mc M B₀) X) (commGroupOfElemAbelian hU)
      (autOn X (uOf1527 (zSOf T Mc M B₀) X))
      ((uLOf1527 (zSOf T Mc M B₀) X).subgroupOf (uOf1527 (zSOf T Mc M B₀) X)) ⊥
      (FFModel.nat (StatedSL n (ZMod 2))) 1

namespace CData

variable (d : CData T Mc M H B₀ I X)

include d

theorem natOne_of (h12 : He12.StageLemma15212W) (hF : ¬ X ≤ Mc)
    (h : Lemma15127Concl (zSOf T Mc M B₀) X) : NatOne T Mc M B₀ X := by
  obtain ⟨hU, halt⟩ := h
  let _ : CommGroup ↥(uOf1527 (zSOf T Mc M B₀) X) := commGroupOfElemAbelian hU
  have hV2 : ∀ w : ↥(uOf1527 (zSOf T Mc M B₀) X), w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using hU.2 w w.2)
  have hF' := d.facts15128 hF
  have hoff := d.q1Offender h12 hF
  rcases halt with ⟨Z, hZ, -, hext⟩ | hext5 | ⟨n, hsum⟩ | ⟨n, hn, k, hk1, hkn, hnat⟩
  · exact (ctx_excl hF' (FLc.excl_ext4 hV2 (hZ.trans inf_le_left) hext) hoff).elim
  · exact (ctx_excl hF' (FLc.excl_ext5 hV2 hext5) hoff).elim
  · exact (false_of_sumNatDual hF' hoff ⟨hU, n, hsum⟩).elim
  · by_cases hk : k = 1
    · subst hk
      exact ⟨hU, n, hn, hnat⟩
    · exact (ctx_excl hF' (FLc.excl_nat2 hV2 (by rcases hn with rfl | rfl <;> norm_num)
        (by omega) hnat) hoff).elim

end CData

end C

end S15223P4

end CFSG.Quasithin
