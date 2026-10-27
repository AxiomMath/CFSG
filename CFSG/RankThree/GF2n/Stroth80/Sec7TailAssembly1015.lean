module

public import CFSG.RankThree.GF2n.Stroth80.Sec12Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailBasic
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailSylow

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Vt_le_Wt_of_34 (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (h5 : Sec5Hyp hc n t) :
    Vt M (LB M Q B) B Z t ≤ Wt Q (Vt M (LB M Q B) B Z t) := by
  have h35 := (stroth_3_5 h34 hc h5.width h5.n_gt h5.noA2 h5.gen).2.1
  have hel := hc.Vt_isElemAbelian h35 h5.mem h5.notQ
  intro v hv
  refine ⟨hc.Vt_le_Q t hv, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
  exact congrArg Subtype.val (hel.1.is_comm.comm ⟨w, hw⟩ ⟨v, hv⟩)

theorem Z0_le_CN_of_34 (h34 : Stroth34Statement) (hZc : Sec7CentreMpStatement) (hc : Ctx M Q Z B)
    {n : ℕ} {t : G} (hs : Sec7Hyp hc n t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) : Z0 ≤ hc.CN t := by
  intro x hx
  refine ⟨hZ0.le hx, fun v hv => ?_⟩
  exact (hZc G M Q Z B hc n t hs Z0 hZ0 x hx).2 v (Vt_le_Wt_of_34 h34 hc hs.toSec5 hv)

theorem not_omegaMinus_two_of_cases {hc : Ctx M Q Z B} {t : G}
    (h : OmegaMinusNat hc t 3 ∨ OmegaPlusNat hc t 3 ∨ OmegaPlusNat hc t 4) :
    ¬ OmegaMinusNat hc t 2 := by
  intro hom
  rcases h with h | h | h
  · have := OmegaMinusNat.eq_of_minus (by norm_num) (by norm_num) h hom
    omega
  · have := omegaPlusNat_eq_omegaMinusNat (by norm_num) h hom
    omega
  · have := omegaPlusNat_eq_omegaMinusNat (by norm_num) h hom
    omega

theorem stroth710_of_steps (h34 : Stroth34Statement) (h77 : Stroth77Statement)
    (hZc : Sec7CentreMpStatement) (hNR : Sec7NormZ0Statement) (hZV : Sec7ZVStatement)
    (hNC : Sec7ConjStatement) (hNC4 : Sec7ConjOm4Statement) (hE : Step710EStatement)
    (hSyl : Sec7SylowLBStatement) (hEnd : Sec7EndStatement) : Stroth710Statement := by
  intro G _ _ M Q Z B hc n t hs Z0 hZ0
  by_contra hno
  have hH1 : ∀ g ∈ M, conjSubgroup g Z0 ≤ LB M Q B → conjSubgroup g Z0 = Z0 := by
    intro g hg hle
    by_contra hne
    exact hno ⟨g, hg, hle, hne⟩
  haveI : (Q.subgroupOf M).Normal := hc.normal_Q_in_M
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hZL : Z0 ≤ LB M Q B := fun z hz => (hZc G M Q Z B hc n t hs Z0 hZ0 z hz).1
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hQL : Q ≤ LB M Q B := sec39_Q_le_LB
  have hN : ∀ ν ∈ M, ν ∈ Subgroup.normalizer (LB M Q B : Set G) →
      ν ∈ Subgroup.normalizer (Z0 : Set G) := by
    intro ν hν hνL
    have hsub : conjSubgroup ν Z0 ≤ LB M Q B :=
      (Subgroup.map_mono hZL).trans (conjSubgroup_eq_self_iff.mpr hνL).le
    exact conjSubgroup_eq_self_iff.mp (hH1 ν hν hsub)
  have hZCN := Z0_le_CN_of_34 h34 hZc hc hs hZ0
  rcases h77 G M Q Z B hc n t hs with ha | ⟨hb, -⟩ | ⟨hb, -⟩ | ⟨hb, -⟩
  · obtain ⟨s, hsR, hsc, g, hg, hgL, hgN⟩ := ha
    have hsZ0 : s ∈ Z0 := (hZ0 s).mpr ⟨hsR, hsc⟩
    have hsM : s ∈ M := hc.Rt_le_M t hsR
    have hxM : g * s * g⁻¹ ∈ M := M.mul_mem (M.mul_mem hg hsM) (M.inv_mem hg)
    have hconj : ConjMod M Q s (g * s * g⁻¹) := ⟨hxM, g, hg, by simp [Q.one_mem]⟩
    obtain ⟨ν, hνM, hνL, hνQ⟩ : ∃ ν ∈ M, ν ∈ Subgroup.normalizer (LB M Q B : Set G) ∧
        g * s * g⁻¹ * (ν * s * ν⁻¹)⁻¹ ∈ Q := by
      by_cases hom : OmegaMinusNat hc t 2
      · exact hNC4 G M Q Z B hc n t hs hom Z0 hZ0 s hsZ0 _ hgL hconj
      · exact hNC G M Q Z B hc n t hs hom Z0 hZ0 s hsZ0 _ hgL hconj
    have hνs : ν * s * ν⁻¹ ∈ Z0 := (Subgroup.mem_normalizer_iff.mp (hN ν hνM hνL) s).mp hsZ0
    have hgs : g * s * g⁻¹ ∈ Z0 := by
      have e : g * s * g⁻¹ = (g * s * g⁻¹ * (ν * s * ν⁻¹)⁻¹) * (ν * s * ν⁻¹) := by group
      rw [e]
      exact Z0.mul_mem (hQZ0 hνQ) hνs
    exact hgN (hZCN hgs)
  all_goals
    have hty : OmegaMinusNat hc t 3 ∨ OmegaPlusNat hc t 3 ∨ OmegaPlusNat hc t 4 := by tauto
    have hnom : ¬ OmegaMinusNat hc t 2 := not_omegaMinus_two_of_cases hty
    have hTI := Z0_normalizes_of_nat hNR hZV G M Q Z B hc n t hs hnom Z0 hZ0
    obtain ⟨P, hP⟩ := hSyl G M Q Z B hc n t hs
    exact hEnd G M Q Z B hc n t hs Z0 hZ0 hTI
      ⟨P, sylow_le_normalizer_bar_Z0 hQL hc.LB_le_M hQZ0 hN hP⟩
      (hE G M Q Z B hc n t hs hty Z0 hZ0 hH1)

theorem stroth714_of_inputs (h78 : Stroth78Statement) (hn : Step714NotTwelveStatement) :
    Stroth714Statement := by
  intro G _ _ M Q Z B hc n t hs hp
  have h := h78 G M Q Z B hc n t hs.toSec5 hs.large hs.notPlus4 4 (by norm_num) (Or.inl hp)
  rcases h with ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨-, -, h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · omega
  · exact h
  · exact (hn G M Q Z B hc n t hs hp h).elim
  · omega
  · omega

theorem stroth715_of_steps (h1 : Step715ZNStatement) (h2 : Step715Hyp79Statement) :
    Stroth715Statement := by
  intro G _ _ M Q Z B _ hc n t hs hp
  obtain ⟨Z0, hZ0⟩ := Ctx.exists_centre hc hs.toSec5.mem
  exact (h2 G M Q Z B hc n t hs hp Z0 hZ0 (h1 G M Q Z B hc n t hs hp Z0 hZ0)).subConfig

theorem stroth713_of_steps (h712 : Stroth712Statement) (hO2 : Step713O2Statement) :
    Stroth713Statement := by
  intro G _ _ M Q Z B _ hc n t hs hn4 Z0 hZ0
  rw [h712 G M Q Z B hc n t hs Z0 hZ0]
  exact hO2 G M Q Z B hc n t hs hn4 Z0 hZ0

theorem close71Final_of_end (hEnd : Sec7EndStatement) : Close71FinalStatement :=
  fun G _ _ M Q Z B _ hc n t hcl Z0 hZ0 hTI hSyl hE =>
    hEnd G M Q Z B hc n t hcl.1 Z0 hZ0 hTI hSyl hE

end CFSG.RankThree.GF2n.Stroth80
