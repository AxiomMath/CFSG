module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront07
import CFSG.GroupTheory.QuotientCoreFacts
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddPair
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214c
public import CFSG.Quasithin.Background.B6Sections

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.NineNineteenA5

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

theorem pRank_inf_le_one_of_pCoreOf_two_ne_bot {D : Data G} (h71 : F07.R71 D) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hsp : IsStronglyPEmbedded p D.M) {H : Subgroup G}
    (hH2 : pCoreOf 2 H ≠ ⊥) (hHtop : H ≠ ⊤) (hHM : ¬ H ≤ D.M) :
    CFSG.Open.pRank p (H ⊓ D.M) ≤ 1 := by
  by_contra hgt
  rw [not_le] at hgt
  have hsec : F07.Sec7Hyp D p H := ⟨hp, hp2, hsp, hHtop, hHM, hgt⟩
  have hodd : Odd (Nat.card (F07.PPrimeCoreIn p H)) := (h71 p H hsec).1
  have hle : pCoreOf 2 H ≤ F07.PPrimeCoreIn p H :=
    Subgroup.map_mono (CFSG.GroupTheory.pCore_le_pPrimeCore Nat.prime_two hp (Ne.symm hp2) ↥H)
  obtain ⟨n, hn⟩ := (IsPGroup.map (CFSG.pCore_isPGroup (p := 2) (G := ↥H)) H.subtype).exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    exact hH2 (Subgroup.card_eq_one.mp hn)
  have hdvd : 2 ∣ Nat.card (F07.PPrimeCoreIn p H) := by
    refine ((even_iff_two_dvd.mp (even_two.pow_of_ne_zero hn0)).trans ?_)
    exact hn ▸ Subgroup.card_dvd_of_le hle
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)

theorem inf_le_normalizer_of_pRank_le_one {M L H : Subgroup G} (hL : L ∈ calC M) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hZ : center (Bar2 L) = ⊥) (hpL : p ∣ Nat.card (Bar2 L))
    (hLH : L ≤ H) (h : CFSG.Open.pRank p (H ⊓ M) ≤ 1) : H ⊓ M ≤ normalizer (L : Set G) := by
  intro g hg
  by_contra hgn
  have hmap : L.map (MulAut.conj g).toMonoidHom ≠ L := fun heq =>
    hgn (Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq)
  have hL' : L.map (MulAut.conj g).toMonoidHom ∈ calC M :=
    uc22p2214_calC_of_mem_conjSetOf hL ⟨g, hg.2, rfl⟩
  have hLM : L ≤ M := CFSG.Open.IsSubnormal.le hL.1
  obtain ⟨x, hxL, hx⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.exists_orderOf_eq_of_dvd_card_bar2 hp hpL
  have hxH : x ∈ H := hLH hxL
  have hxM : x ∈ M := hLM hxL
  have hyL' : g * x * g⁻¹ ∈ L.map (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.mem_map]
    exact ⟨x, hxL, MulAut.conj_apply g x⟩
  have hyH : g * x * g⁻¹ ∈ H := H.mul_mem (H.mul_mem hg.1 hxH) (H.inv_mem hg.1)
  have hyM : g * x * g⁻¹ ∈ M := M.mul_mem (M.mul_mem hg.2 hxM) (M.inv_mem hg.2)
  have hy : orderOf (g * x * g⁻¹) = p := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hx]
  have h2 :=
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.two_le_pRank_of_pair hp hp2 hL hL'
      hmap.symm hZ inf_le_right hxL hyL' (mem_inf.mpr ⟨hxH, hxM⟩) (mem_inf.mpr ⟨hyH, hyM⟩) hx hy
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.NineNineteenA5
