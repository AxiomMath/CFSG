module

public import CFSG.RankThree.PartOne.S12.InputsLinear
public import CFSG.RankThree.PartOne.LIT.JPSpecialLinear
public import CFSG.RankThree.PartOne.LIT.JPOmegaTransport
public import CFSG.RankThree.SubgroupLists2.OmegaThree

public section

namespace CFSG.RankThree.PartOne

open CFSG.Assembly.LowTwoRank (StatedSL specialLinearGroupEquivStatedSL)
open CFSG.RankThree.SubgroupLists (omegaGL soGL card_soGL_three)
open Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem exists_not_mem_of_finrank_succ {K : Type*} [Field K] {V : Type*} [AddCommGroup V]
    [Module K V] [Module.Finite K V] (B : Submodule K V)
    (hdim : Module.finrank K B + 1 = Module.finrank K V) : ∃ v : V, v ∉ B := by
  by_contra h
  have hB : B = ⊤ := eq_top_iff.mpr fun v _ => by_contra fun hv => h ⟨v, hv⟩
  rw [hB, finrank_top] at hdim
  omega

theorem splitFormK_transpose (K : Type*) [Field K] :
    (LIT.splitFormK K)ᵀ = LIT.splitFormK K := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [LIT.splitFormK]

theorem card_soGL_splitFormK {p : ℕ} [Fact p.Prime] (hp : 3 ≤ p) :
    Nat.card (soGL (LIT.splitFormK (ZMod p))) = p * (p ^ 2 - 1) := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h)
    have := Nat.le_of_dvd (by norm_num) this
    omega
  refine card_soGL_three (by omega) (splitFormK_transpose _) ?_
  simp [LIT.splitFormK, Matrix.det_fin_three, h2]

theorem extJonesParshallSL : ExtJonesParshallSL := by
  intro p _ hp V _ _ _ B n hn θ ρ hdim hB hq
  have hn2 : 2 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  obtain ⟨v₀, hv₀⟩ := exists_not_mem_of_finrank_succ B hdim
  let e := specialLinearGroupEquivStatedSL n (ZMod p)
  obtain ⟨v, hvB, hv⟩ := LIT.JP.jp_special_linear hp hn2 B θ
    (ρ.comp (e : SpecialLinearGroup (Fin n) (ZMod p) →* StatedSL n (ZMod p)))
    (fun y b => hB (e y) b) (fun y w => hq (e y) w) v₀
  refine ⟨v, fun hvB' => hv₀ ?_, fun y => ?_⟩
  · have := B.sub_mem hvB' hvB
    simpa using this
  · obtain ⟨x, rfl⟩ := e.surjective y
    exact hv x

theorem extJonesParshallOmega : ExtJonesParshallOmega := by
  intro p _ hp5 hp5' V _ _ _ B M hM hdet θ ρ hdim hB hq
  have hpp : p.Prime := Fact.out
  have hp6 : p ≠ 6 := fun h => by
    subst h
    exact absurd hpp (by norm_num)
  have hp7 : 7 ≤ p := by omega
  obtain ⟨v₀, hv₀⟩ := exists_not_mem_of_finrank_succ B hdim
  obtain ⟨v, hvB, hv⟩ := LIT.jp_omega_of_card hp7 (card_soGL_splitFormK (by omega)) B M hM hdet θ
    ρ hB hq v₀
  refine ⟨v, fun hvB' => hv₀ ?_, hv⟩
  have := B.sub_mem hvB' hvB
  simpa using this

theorem extJonesParshall : ExtJonesParshall :=
  ⟨extJonesParshallSL, extJonesParshallOmega⟩

end CFSG.RankThree.PartOne
