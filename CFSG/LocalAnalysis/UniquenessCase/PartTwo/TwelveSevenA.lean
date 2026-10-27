module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveShort
import CFSG.LocalAnalysis.WeakClosure81.EightFour
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveFourteen
import CFSG.LocalAnalysis.UniquenessCase.UC22P22p
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open CFSG.CGT.Timmesfeld75 (IsTI)

variable {G : Type} [Group G] [Finite G]

namespace TwelveSeven

theorem two_lt_rk_of_card {V : Subgroup G} (hV : IsElemAbelian 2 V) (h8 : 8 ≤ Nat.card V) :
    2 < rk ↥V := by
  obtain ⟨n, hn⟩ := (CFSG.Open.IsElemAbelian.isPGroup hV).exists_card_eq
  have hrk : rk ↥V = n := by
    unfold rk
    rw [hn, padicValNat.prime_pow]
  rw [hrk]
  by_contra h
  have h2 : 2 ^ n ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem hyp7_of_inCalV (D : Data G) {V : Subgroup G} (hV : InCalV D.M V) (hTI : IsTI V)
    (h8 : 8 ≤ Nat.card V) : Hyp7 V :=
  ⟨hV.2.2.2, by omega, hTI⟩

theorem k_le_two (D : Data G) : D.k ≤ 2 := by
  unfold Data.k CFSG.LocalAnalysis.RankThreeUC.kParam
  split_ifs <;> norm_num

theorem isCalH_of_mem_hSet (D : Data G) {V H : Subgroup G} (hV : InCalV D.M V)
    (hH : H ∈ RankThreeUC.hSet D.T D.M) : IsCalH V H := by
  have hN : normalizer (V : Set G) = D.M := normalizer_eq_of_inCalV D hV
  have hSylH : IsSylowIn 2 D.T H := TwelveShort.isSylowIn_of_le D hH.1
  refine ⟨(uc22p22p_le_T_of_inCalV D hV).trans hH.1, hH.2.2, ?_⟩
  have hoddH : Odd (D.T.relIndex H) :=
    Nat.not_even_iff_odd.mp fun hEven => hSylH.not_dvd_relIndex (even_iff_two_dvd.mp hEven)
  have hdvd : (H ⊓ normalizer (V : Set G)).relIndex H ∣ D.T.relIndex H :=
    Subgroup.relIndex_dvd_of_le_left (L := H) (le_inf hH.1 (by rw [hN]; exact D.sylowM.le))
  exact Nat.not_even_iff_odd.mp fun hEven =>
    (Nat.not_even_iff_odd.mpr hoddH) (even_iff_two_dvd.mpr (hEven.two_dvd.trans hdvd))

theorem normalizersInM_of_uniqueMax (D : Data G) {V H W : Subgroup G} (hV : InCalV D.M V)
    (hW : W ≠ ⊥) (hW2 : IsPGroup 2 W)
    (hU : UniqueMax D.M (D.M ⊓ normalizer (W : Set G))) : NormalizersInM V H W := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : normalizer (V : Set G) = D.M := normalizer_eq_of_inCalV D hV
  have hNW : normalizer (W : Set G) ≤ D.M := normalizer_le_of_uniqueMax hU hW hW2 inf_le_right
  have hinf : normalizer (V : Set G) ⊓ normalizer (W : Set G) = normalizer (W : Set G) := by
    rw [hN]
    exact inf_eq_right.2 hNW
  intro X hX1 hXK hKX
  rw [hinf] at hXK hKX
  have hO : pCoreOf 2 X ≠ ⊥ :=
    TwelveFourteen.pCoreOf_ne_bot_of_normal D.standing.charTwo hW hW2 hX1 hXK hKX
  have hNXO := CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X
  rw [hN]
  exact inf_le_right.trans (hNXO.trans (normalizer_le_of_uniqueMax hU hO
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X) (inf_le_right.trans (hKX.trans hNXO))))

theorem wClos_zero_eq_inf_centralizer (D : Data G) {V : Subgroup G} (hV : InCalV D.M V)
    (hTI : IsTI V) :
    E3.wClos V 0 D.T = E3.wClos V 0 (D.T ⊓ centralizer (V : Set G)) := by
  have hN : normalizer (V : Set G) = D.M := normalizer_eq_of_inCalV D hV
  have hVab : IsElemAbelian 2 V := hV.2.2.2
  refine le_antisymm ?_ (E3.wClos_mono inf_le_left)
  rw [wClos_zero_eq_iSup hVab]
  refine iSup₂_le fun g hg => conjSubgroup_le_wClos_zero (le_inf hg ?_)
  have hgM : conjSubgroup V g ≤ D.M := hg.trans D.sylowM.le
  have hne : conjSubgroup V g ⊓ normalizer (V : Set G) ≠ ⊥ := by
    rw [hN, inf_eq_left.2 hgM]
    intro h
    apply hV.1
    have h1 := E3.card_conjSubgroup V g
    rw [h, Subgroup.card_bot] at h1
    exact Subgroup.card_eq_one.1 h1.symm
  rcases two_conj_eq_or_comm hVab hTI ⟨g, rfl⟩ ⟨1, (conjSubgroup_one V).symm⟩ hne with
    hcomm | ⟨y, hy, hyV⟩
  · intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (hcomm u hu v hv).symm
  · have hyM : y ∈ D.M := (sup_le hgM hV.2.1) hy
    rw [conjSubgroup_conjSubgroup] at hyV
    have hgy : g * y ∈ normalizer (V : Set G) := conjSubgroup_eq_iff_mem_normalizer.1 hyV.symm
    rw [hN] at hgy
    have hgM' : g ∈ normalizer (V : Set G) := by
      rw [hN]
      simpa using D.M.mul_mem hgy (D.M.inv_mem hyM)
    rw [conjSubgroup_eq_iff_mem_normalizer.2 hgM']
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact hVab.1.is_comm.comm ⟨v, hv⟩ ⟨u, hu⟩ |> congrArg Subtype.val

end TwelveSeven

theorem twelve_seven_one (hTim : CFSG.CGT.Timmesfeld75.NodeStatement)
    (hcat : ¬ CFSG.Blueprint.Catalog G) (D : Data G) (h86 : W3Lem86_1 G) (h126 : R126 D)
    (h124 : ∃ H₀ ∈ RankThreeUC.hSet D.T D.M, RankThreeUC.Hyp124 D.M H₀) {V : Subgroup G}
    (hV : InCalV D.M V) (hTI : IsTI V) (h8 : 8 ≤ Nat.card V) :
    ¬ UniqueMax D.M (D.M ⊓ normalizer (E3.wClos V 0 D.T : Set G)) := by
  intro hU
  obtain ⟨H₀, hmin⟩ := exists_hyp124Min D h124
  have hW1 : E3.wClos V 0 D.T ≠ ⊥ := TwelveShort.wClos_zero_ne_bot D hV
  have hW2 : IsPGroup 2 (E3.wClos V 0 D.T) :=
    D.sylowM.isPGroup.to_le (wClos_zero_le V D.T)
  have hle := TwelveFourteen.rk_le_k D h126 h86 hmin hV (TwelveSeven.hyp7_of_inCalV D hV hTI h8)
    (TwelveFourteen.wClos_zero_ne_self hTim hcat D hV hTI (by omega))
    (normalizer_le_of_uniqueMax hU hW1 hW2 inf_le_right)
    (TwelveSeven.normalizersInM_of_uniqueMax D hV hW1 hW2 hU)
  have h1 := TwelveSeven.two_lt_rk_of_card hV.2.2.2 h8
  have h2 := TwelveSeven.k_le_two D
  omega

theorem twelve_seven_two (hTim : CFSG.CGT.Timmesfeld75.NodeStatement)
    (hcat : ¬ CFSG.Blueprint.Catalog G) (D : Data G) (h86 : W3Lem86_1 G) (h126 : R126 D)
    (h124 : ∃ H₀ ∈ RankThreeUC.hSet D.T D.M, RankThreeUC.Hyp124 D.M H₀) {V : Subgroup G}
    (hV : InCalV D.M V) (hTI : IsTI V) (h8 : 8 ≤ Nat.card V) : ¬ InCalV1 D.M D.T V := by
  intro hV1
  apply twelve_seven_one hTim hcat D h86 h126 h124 hV hTI h8
  have hle : D.M ⊓ normalizer ((D.T ⊓ centralizer (V : Set G) : Subgroup G) : Set G) ≤
      D.M ⊓ normalizer (E3.wClos V 0 D.T : Set G) := by
    rw [TwelveSeven.wClos_zero_eq_inf_centralizer D hV hTI]
    exact inf_le_inf_left _ (E3.normalizer_le_normalizer_wClos (V := V) (i := 0) _)
  exact InCalU.mono D.maxLocal hV1.2 hle inf_le_left

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
