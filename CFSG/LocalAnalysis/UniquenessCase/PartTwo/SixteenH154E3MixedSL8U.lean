module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8TSig
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8TC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3SL8CoverConj
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3OmegaGen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8UAB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8UB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8UC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5JP

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {G : Type} [Group G] [Finite G]

theorem s16h_sl28_three_cfg_gen
    (D : Data G) (S : s16h_Std D) (hσ : D.sig = D.sig1)
    (hJP : K_JonesParshallH1) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hs2 : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2)
    {t : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)} (ht : t ∈ Mbar D.M ⊥ V h.hyp151.isElemAbelian)
    (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (htr : rk ↥(commSub ⊤ (zpowers t)) ≤ 3)
    (hW : Conc4_136W (Mbar D.M ⊥ V h.hyp151.isElemAbelian) t (lBar ⊥ V h.hyp151.isElemAbelian L))
    (hcomp : IsComponentOf (lBar ⊥ V h.hyp151.isElemAbelian L)
      (Mbar D.M ⊥ V h.hyp151.isElemAbelian))
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 →
      CFSG.Open.pRank q (lBar ⊥ V h.hyp151.isElemAbelian L) ≤ 1)
    (hZ : commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L) ≠ ⊥)
    (hbad : ∀ q ∈ D.sig, ∀ E : Subgroup G, E ≤ D.M → IsElemAbelian q E →
      Nat.card ↥(E ⊓ preBarSub D.M ⊥ V h.hyp151.isElemAbelian
        (centSub (wTil ⊥ V h.hyp151.isElemAbelian L))) < q ^ 2)
    (hrow : s16h_H5RowSL2 (lBar ⊥ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) 3)
    (hZ4 : 2 < Nat.card ↥(commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L)))
    (hU2 : R8100U2 D) (h7 : 7 ∉ D.sig)
    {x : G} (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L)
 :
    s16h_e3_omega_cfg_gen D (V := V) (L := L) h.hyp151.isElemAbelian := by
  have hsig : D.sig = {3} :=
    s16h_e3_sl28T_sig_eq_three D S h hs2 ht ht2 ht1 htr hW hcomp hthin hrow hbad h7
  have h3 : 3 ∈ D.sig := by rw [hsig]; exact Set.mem_singleton 3
  have he : evenRank G = 3 :=
    s16h_e3_sl28T_evenRank_eq_three D S h hs2 ht ht2 ht1 htr hW hcomp hthin hrow hbad h7
  obtain ⟨L₀, -, -, hL₀, -, -, h20, -, hO, hL₀M, hcent, -, -, hbar⟩ :=
    s16h_e3_sl28_cover_gen D S h hs2 hcomp hrow hbad hxM hxn
  obtain ⟨D₃, A, hD₃le, hD₃c, hD₃u, hAle, hAc, hAu⟩ :=
    s16h_e3_sl28_uniqueSet_subgroups D S hU2 he h3 hL₀
      (s16h_e3_sl28_cover_ncard_conjSetOf D h hcomp hs2 hxM hxn hL₀ hbar) h20
  refine ⟨hsig, L₀, D₃, A, hL₀, hL₀M, h20, hO, hD₃le, hD₃c, hD₃u, hAle, hAc, hAu, ?_⟩
  have hcZx := s16h_e3_sl28_cover_cent_zx D h hxM hxn hL₀ hbar
  have hv1 := s16h_e3_sl28_v1_le_wsub_sup_zx D h hs2 hxM hxn
  intro l hl
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  have hg' := (sup_le le_sup_left hv1) hg
  have hWl : wSub ⊥ V h.hyp151.isElemAbelian L ≤ Subgroup.centralizer ({l} : Set G) := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.1 hy]
    exact ((Subgroup.mem_centralizer_iff.1 (hcent hl)) w hw).symm
  have hZl : conjSubgroup (wSub ⊥ V h.hyp151.isElemAbelian L ⊓
      Subgroup.centralizer (L : Set G)) x ≤ Subgroup.centralizer ({l} : Set G) := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.1 hy]
    exact ((Subgroup.mem_centralizer_iff.1 (hcZx hl)) w hw).symm
  have hgl := (sup_le hWl hZl) hg'
  exact ((Subgroup.mem_centralizer_iff.1 hgl) l (Set.mem_singleton l)).symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
