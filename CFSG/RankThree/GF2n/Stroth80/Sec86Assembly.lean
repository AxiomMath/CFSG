module

public import CFSG.RankThree.GF2n.Stroth80.Sec84Basic
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailAssembly1617
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailBasic

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem step86MaxAb_holds :
    ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
      (hc : Ctx M Q Z B) (n : ℕ) (t : G), Sec5Hyp hc n t →
      ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
      IsIrredModule (Rt M (LB M Q B) t) (hc.CN t) Z0 → ¬ ⁅hc.CN t, hc.CN t⁆ ≤ Q →
      generalizedFitting ↥(bar M Q (NormH0 M Z Z0)) =
        (bar M Q (hc.CN t)).subgroupOf (bar M Q (NormH0 M Z Z0)) →
      IsMaxAbNormalMod (NormH0 M Z Z0) Z0 Q := by
  intro G _ _ M Q Z B _ hc n t hs Z0 hZ0 hirr hN' hF
  have ht : t ∈ LB M Q B := hs.mem
  have hnormR : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ y ∈ Q, ρ * y * ρ⁻¹ ∈ Q := fun ρ hρ y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hc.Rt_le_M t hρ)) y).mp hy
  have hRK : Rt M (LB M Q B) t ≤ NormH0 M Z Z0 := fun ρ hρ =>
    Subgroup.mem_inf.mpr ⟨hc.Rt_le_H0 t hρ, IsCentrePre.mem_normalizer hZ0 hnormR hρ⟩
  have hZK : Z0 ≤ NormH0 M Z Z0 := fun z hz => hRK (hZ0.le hz)
  have hKM : NormH0 M Z Z0 ≤ M := fun x hx => hx.1.1
  have hQN : Q ≤ hc.CN t := fun x hx =>
    Ctx.mem_CN.mpr ⟨hc.Q_le_Rt ht hx,
      fun v hv => hc.hyp.toHyp79.comm_mem_V hx (hc.Vt_le_Q t hv)⟩
  refine ⟨hZK, fun x hx y hy => hZ0.comm_mem hx (hZ0.le hy),
    fun k hk => conjSubgroup_eq_self_iff.mpr hk.2, ?_⟩
  intro A hZA hAK hAn hAab
  have hAN : A ≤ hc.CN t := step716_le_of_fstar hKM hQN hAK hAn hAab hF
  have hRA : ∀ r ∈ Rt M (LB M Q B) t, conjSubgroup r A = A := fun r hr => hAn r (hRK hr)
  rcases hirr.2.2.2 A hZA hAN hRA with h | h
  · exact h
  · exfalso
    apply hN'
    refine Subgroup.commutator_le.mpr fun x hx y hy => hAab x ?_ y ?_
    · rw [h]; exact hx
    · rw [h]; exact hy

theorem isIrredModule_of_min_sp (h51 : Stroth51Statement) (hA : Sec8AExistsStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec8Hyp hc n t)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {e : ℕ} (he : 1 ≤ e)
    (hN : Nat.card ↥(hc.CN t) = Nat.card ↥Z0 * Nat.card Z ^ e)
    (hmin : ∀ A : Subgroup G, Z0 ≤ A → A ≤ hc.CN t →
      (∀ r ∈ Rt M (LB M Q B) t, conjSubgroup r A = A) → A ≠ Z0 →
      Nat.card ↥Z0 * Nat.card Z ^ e ≤ Nat.card ↥A) :
    IsIrredModule (Rt M (LB M Q B) t) (hc.CN t) Z0 := by
  obtain ⟨r, -, -, hopp, -⟩ := sec8_Z0_data h51 hA hc hs hZ0
  obtain ⟨hI1, hI2, -, -, -, -, hab, hsq, -, -⟩ := hopp
  have hZ0N : Z0 ≤ hc.CN t := hI1.trans hI2
  have hq2 : 2 ≤ Nat.card Z := two_le_card_Z_of_ctx hc
  refine ⟨hab, hsq, lt_of_le_of_ne hZ0N fun h => ?_, ?_⟩
  · have h1 : Nat.card ↥(hc.CN t) = Nat.card ↥Z0 := by rw [h]
    have h2 : 2 ≤ Nat.card Z ^ e := by
      calc 2 ≤ Nat.card Z := hq2
        _ = Nat.card Z ^ 1 := (pow_one _).symm
        _ ≤ Nat.card Z ^ e := Nat.pow_le_pow_right (by omega) he
    have h3 : 0 < Nat.card ↥Z0 := Nat.card_pos
    rw [hN] at h1
    nlinarith
  · intro A hA1 hA2 hinv
    by_cases hAZ : A = Z0
    · exact Or.inl hAZ
    · right
      exact Subgroup.eq_of_le_of_card_ge hA2 (by rw [hN]; exact hmin A hA1 hA2 hinv hAZ)

theorem sec86Irred_of_inputs (h83 : Stroth83Statement) (h51 : Stroth51Statement)
    (hA : Sec8AExistsStatement) (hMin : Sec86MinOrderStatement) : Sec86IrredStatement := by
  intro G _ _ M Q Z B hc n t hs Z0 hZ0
  have hC := h83 G M Q Z B hc n t hs.toSec5 hs.sp
  have hZ0card : Nat.card ↥Z0 = Nat.card Q * Nat.card Z :=
    sec86ZCard_of_51 h51 hA G M Q Z B hc n t hs Z0 hZ0
  rcases hC with ⟨-, hsp3, hN⟩ | ⟨-, hsp4, hN⟩
  · refine isIrredModule_of_min_sp h51 hA hc hs hZ0 (e := 8) (by norm_num)
      (by rw [hN, hZ0card]; ring) ?_
    intro A hZA hAN hinv hAZ
    simpa using hMin G M Q Z B hc n t hs Z0 hZ0 A hZA hAN hinv hAZ 3 (by norm_num) hsp3
  · refine isIrredModule_of_min_sp h51 hA hc hs hZ0 (e := 16) (by norm_num)
      (by rw [hN, hZ0card]; ring) ?_
    intro A hZA hAN hinv hAZ
    simpa using hMin G M Q Z B hc n t hs Z0 hZ0 A hZA hAN hinv hAZ 4 (by norm_num) hsp4

theorem sec86NormLB_of_82 (h82 : Stroth82Statement) (hConj : Sec86ConjStatement)
    (hH : Sec86NormHStatement) : Sec86NormLBStatement := by
  intro G _ _ M Q Z B hc n t hs Z0 hZ0 hle
  have hall := sec8_not_forall_normalizer h82 hConj hc hs hZ0
  push_neg at hall
  obtain ⟨ν, hνM, hνL, hνZ⟩ := hall
  obtain ⟨ν', hν'H, hν'L, hν'Z⟩ := hH G M Q Z B hc n t hs Z0 hZ0 ν hνM hνL hνZ
  exact hν'Z (hle ⟨hν'H, hν'L⟩).2

theorem stroth86_of_inputs (h84 : Stroth84Statement) (h85 : Stroth85Statement)
    (hirr : Sec86IrredStatement) (hTI : Sec8TIStatement) (hNL : Sec86NormLBStatement)
    (h27 : Tim81StrothSpStatement)
    (hSub : Step86HypSubStatement) (hNU : Step86NotUnitaryStatement) : Stroth86Statement := by
  have hMax := step86MaxAb_holds
  intro G _ _ M Q Z B hc n t h5 hsp
  haveI := hc.normal_Q_in_M
  have hs : Sec8Hyp hc n t := ⟨h5, hsp⟩
  obtain ⟨Z0, hZ0⟩ := Ctx.exists_centre hc h5.mem
  have hN' := h84 G M Q Z B hc n t hs
  have hF := h85 G M Q Z B hc n t hs Z0 hZ0
  have hI := hirr G M Q Z B hc n t hs Z0 hZ0
  have hMA := hMax G M Q Z B hc n t h5 Z0 hZ0 hI hN' hF
  have hT := hTI G M Q Z B hc n t hs Z0 hZ0
  rcases h27 G M Q Z B hc n t hs Z0 hZ0 hMA hT hF (hNL G M Q Z B hc n t hs Z0 hZ0) with
    hU | ⟨g, hg, hle, hne⟩
  · exact absurd hU (hNU G M Q Z B hc n t hs)
  · exact (hSub G M Q Z B hc n t hs Z0 hZ0 hMA hT hF ⟨g, hg, hle, hne⟩).subConfig

end CFSG.RankThree.GF2n.Stroth80
