module

public import CFSG.Quasithin.H13.L32NQ8Pow
public import CFSG.Quasithin.H13.L32NItems143
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem centerOf_fsuU_le [Finite G] {T L V : Subgroup G} (hV : StmtL32NModule)
    (h : Hyp14310One G T L V) (hext : CFSG.IsExtraspecialPGroup 2 ↥(fsuU T V)) :
    centerOf (fsuU T V) ≤ V := by
  obtain ⟨hVe, -, -, hV1, -⟩ := hV G T L V h.hyp h.fsu
  have hVU : V ≤ fsuU T V := le_conjClosure V _
  have hV1U : fsuV1 T V ≤ fsuU T V := inf_le_left.trans hVU
  obtain ⟨z, hz1, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥(fsuV1 T V))).mp hV1
  have hz : (z : G) ≠ 1 := fun h0 => hz1 (Subtype.ext h0)
  have hmem : ∀ a ∈ fsuV1 T V, a = 1 ∨ a = z := by
    intro a ha
    by_cases ha1 : a = 1
    · exact Or.inl ha1
    · right
      have h1 := huniq ⟨a, ha⟩ (fun h0 => ha1 (congrArg Subtype.val h0))
      exact congrArg Subtype.val (h1.trans (huniq z hz1).symm)
  have hVN : V ≤ l32nH T V := by
    intro v hv
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun w hw => ?_)
    exact congrArg Subtype.val (hVe.1.is_comm.comm ⟨w, hw.1⟩ ⟨v, hv⟩)
  have hUN : fsuU T V ≤ l32nH T V := conjClosure_le fun x hx v hv =>
    (l32nH T V).mul_mem ((l32nH T V).mul_mem hx (hVN hv)) ((l32nH T V).inv_mem hx)
  have hNC := normalizer_eq_centralizer_of_card_two hV1 z.2 hz
  have hV1Z : fsuV1 T V ≤ centerOf (fsuU T V) := by
    intro a ha
    refine Subgroup.mem_inf.mpr ⟨hV1U ha, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
    rcases hmem a ha with rfl | rfl
    · rw [mul_one, one_mul]
    · have hu' : u ∈ Subgroup.centralizer ({(z : G)} : Set G) := hNC ▸ hUN hu
      exact (Subgroup.mem_centralizer_iff.mp hu' z rfl).symm
  have hZ : centerOf (fsuU T V) = fsuV1 T V :=
    (Subgroup.eq_of_le_of_card_ge hV1Z (by rw [l32n_card_centerOf, hext.2.2.2, hV1])).symm
  rw [hZ]
  exact inf_le_left

theorem lemma1442Q8Four_of_inputs (hV : StmtL32NModule) {G : Type} [Group G] [Finite G]
    {T L V : Subgroup G} (h : Hyp14310One G T L V)
    (hext : CFSG.IsExtraspecialPGroup 2 ↥(fsuU T V)) (h32 : Nat.card ↥(fsuU T V) = 2 ^ 5) :
    IsQ8CentralPow 2 ↥(fsuU T V) := by
  obtain ⟨hVe, hV8, -, -, -⟩ := hV G T L V h.hyp h.fsu
  have hVU : V ≤ fsuU T V := le_conjClosure V _
  exact Q8Pow.isQ8CentralPow_of_elemAbelian (j := 1) hext hVU (centerOf_fsuU_le hV h hext)
    (fun a ha b hb => congrArg Subtype.val (hVe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))
    (fun a ha => by rw [← pow_two]; exact hVe.2 a ha) one_pos (by rw [hV8]; norm_num)
    (by rw [h32])

end CFSG.Quasithin.H13
