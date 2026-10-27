module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148WL3CentConfig
public import CFSG.RankThree.PartTwo.Sec4.LThreePiMain
import CFSG.RankThree.PartTwo.Sec14.Ronan148WL3CentNT
import CFSG.RankThree.PartTwo.Sec14.Ronan148WL3CentTorus
import CFSG.RankThree.PartTwo.Sec14.Ronan148WL3CentBlock
import CFSG.RankThree.PartTwo.Sec14.Ronan148WL3CentInner
import CFSG.RankThree.PartTwo.Sec14.Ronan148WL3CentQ8
import CFSG.RankThree.PartTwo.Sec4.LThreePiCaseA

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148W

open CFSG CFSG.RankThree.PartTwo.Sec4 Matrix CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.RankThreeEven (projImage)

local notation "pmk" => Matrix.ProjGenLinGroup.mk

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem entries_of_commute_diagE {ε : Kˣ} (hε : ε ≠ 1) {Y : GL (Fin 3) K}
    (hY : Y * diagE ε = diagE ε * Y) :
    (Y : Matrix (Fin 3) (Fin 3) K) 0 1 = 0 ∧ (Y : Matrix (Fin 3) (Fin 3) K) 0 2 = 0 ∧
      (Y : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 ∧ (Y : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 := by
  have he' : (ε : K) ≠ 1 := fun h => hε (Units.ext h)
  have hc := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hY
  simp only [Units.val_mul, coe_diagE] at hc
  have z := fun i j (hij : (![(ε : K), 1, 1] : Fin 3 → K) i ≠ ![(ε : K), 1, 1] j) =>
    entry_eq_zero_of_commute_diagonal hc hij
  exact ⟨z 0 1 (by simpa using he'), z 0 2 (by simpa using he'), z 1 0 (by simpa using he'.symm),
    z 2 0 (by simpa using he'.symm)⟩

variable {ι : Type*} {α : ι → MulAut (projImage (slPi π 3 (p ^ f) K))}
  {e₀ : projImage (slPi π 3 (p ^ f) K)}

theorem CentConfig.false_of_normalForm (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (hq2 : 2 < p ^ f) (h4 : p ^ f ≠ 4) (h8 : p ^ f ≠ 8)
    (hexc : ¬ (p = 2 ∧ π = false ∧ ¬ 9 ∣ p ^ f + 1)) (hc : CentConfig π p f K α e₀)
    (he₀1 : e₀ ≠ 1) (he₀3 : e₀ ^ 3 = 1)
    (hd : (∃ (τ : K) (hτ : τ ^ 3 = 1), τ ≠ 1 ∧
        (e₀ : ProjGenLinGroup (Fin 3) K) = pmk (diagTau hτ)) ∨
      (∃ ε : Kˣ, (ε : K) ^ 3 = 1 ∧ ε ≠ 1 ∧ (e₀ : ProjGenLinGroup (Fin 3) K) = pmk (diagE ε) ∧
        ModNine π (p ^ f))) :
    False := by
  have h8' : ¬ (π = false ∧ p ^ f = 8) := fun h => h8 h.2
  rcases hd with ⟨τ, hτ, hτ1, he₀⟩ | ⟨ε, hε3, hε1, he₀, h9⟩
  ·
    by_cases hfield : ∃ x, IsFieldAct π p f K (α x)
    · obtain ⟨x, hx⟩ := hfield
      exact hc.false_of_field_typeOne hK hq h8' hτ hτ1 he₀ x hx
    push Not at hfield
    have hpgl : ∀ x, IsPGLAct π p f K (α x) := fun x => (hc.dich x).resolve_right (hfield x)
    obtain ⟨n, hn1, hn, hn3⟩ : ∃ n, 1 < n ∧ n ∣ qSubPi π (p ^ f) ∧ ¬ 3 ∣ n := by
      cases π
      · exact exists_coprime_three_dvd_add_one hK.prime hq2 h8 hq
      · exact exists_coprime_three_dvd_sub_one hK.prime hq2 h4 hq
    have hdiag := hc.diag_of_typeOne hK hq hτ hτ1 he₀ hpgl hn hn1 hn3
    cases π
    · by_cases hp2 : p = 2
      · have h9 : 9 ∣ qSubPi false (p ^ f) := by
          by_contra h
          exact hexc ⟨hp2, rfl, h⟩
        refine hc.false_of_block_lifts hK hq hq2 he₀1 he₀3 h9 fun x => ?_
        obtain ⟨y, hy, ⟨a, b, c, rfl⟩, hyx⟩ := hdiag x
        exact ⟨_, hy, by simp [coe_diagUnits], by simp [coe_diagUnits], by simp [coe_diagUnits],
          by simp [coe_diagUnits], hyx⟩
      · exact hc.false_of_quaternion hK hq hq2 hp2 hτ hτ1 he₀ hdiag
    · refine hc.false_of_rootGroup hK hq hτ hτ1 he₀ fun x => ?_
      obtain ⟨y, -, ⟨a, b, c, rfl⟩, hyx⟩ := hdiag x
      exact ⟨a, b, c, hyx⟩
  ·
    by_cases hfield : ∃ x, IsFieldAct π p f K (α x)
    · obtain ⟨x, hx⟩ := hfield
      exact hc.false_of_field_typeTwo hK hq h8' hε3 hε1 he₀ x hx
    push Not at hfield
    have h9' : 9 ∣ qSubPi π (p ^ f) := (modNine_iff (by omega)).mp h9
    refine hc.false_of_block_lifts hK hq hq2 he₀1 he₀3 h9' fun x => ?_
    obtain ⟨y, hy, hyx⟩ := (hc.dich x).resolve_right (hfield x)
    obtain ⟨c, hc'⟩ := exists_conj_eq_scalar_mul hyx (hc.fix x) he₀
    obtain ⟨l01, l02, l10, l20⟩ :=
      entries_of_commute_diagE hε1 (commute_of_conj_diagE (hK.three_ne_zero hq) hε3 hc')
    exact ⟨y, hy, l01, l02, l10, l20, hyx⟩

end CFSG.RankThree.PartTwo.Sec14.Ronan148W
