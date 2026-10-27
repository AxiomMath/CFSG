module

public import CFSG.Quasithin.Vol2.Ch10SecEA5

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecE

open CFSG.Quasithin CFSG.Assembly.LowTwoRank

theorem det_of_mem_statedSL {n : ℕ} {K : Type} [Field K] {g : GL (Fin n) K}
    (hg : g ∈ StatedSL n K) : (g : Matrix (Fin n) (Fin n) K).det = 1 :=
  CFSG.Open.StatedAPI.det_of_mem_statedSL hg

theorem mul_self_eq_one_of_binaryNaturalSL {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)}
    {Z : Subgroup W} {n : ℕ} (hn : 1 ≤ n) (h : BinaryNaturalSL H ⊤ Z 2 n) {x : MulAut W}
    (hx : x ∈ H) {u : W} (huZ : u ∉ Z) (hxu : x u = u) : x * x = 1 := by
  obtain ⟨K, hF, hfin, hcard, π, hπ⟩ := h
  obtain ⟨β, -, hβk, hβe⟩ := FFModel.RealizesVia.coord (D := FFModel.nat (StatedSL 2 K))
    rfl rfl hπ
  obtain ⟨g, hg⟩ := hπ.1 ⟨x, hx⟩
  have h2 : (2 : K) = 0 := two_eq_zero_of_card hn hcard
  set ū : ↥(⊤ : Subgroup W) := ⟨u, Subgroup.mem_top u⟩
  have hu' : ((π g : ↥H) : MulAut W) (ū : W) ∈ (⊤ : Subgroup W) := Subgroup.mem_top _
  have he := hβe g ū hu'
  have e1 : (⟨((π g : ↥H) : MulAut W) (ū : W), hu'⟩ : ↥(⊤ : Subgroup W)) = ū := by
    apply Subtype.ext
    show ((π g : ↥H) : MulAut W) u = u
    rw [hg]
    exact hxu
  rw [e1] at he
  set g' : ↥(StatedSL 2 K) := g
  set m : Multiplicative (Fin 2 → K) := β ū with hm
  have he' : m = Multiplicative.ofAdd (((g' : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).mulVec
      (Multiplicative.toAdd m)) := he
  have hne : Multiplicative.toAdd m ≠ 0 := by
    intro h0
    have h1 : β ū = 1 := Multiplicative.toAdd.injective (h0.trans toAdd_one.symm)
    exact huZ ((hβk ū).mp h1)
  have hfix : ((g' : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).mulVec
      (Multiplicative.toAdd m) = Multiplicative.toAdd m :=
    (congrArg Multiplicative.toAdd he').symm
  have hsq := mul_self_eq_one_of_mulVec_eq h2 (det_of_mem_statedSL g'.2) hne hfix
  have hgg : g' * g' = 1 := Subtype.ext (Units.ext hsq)
  have h3 : π g * π g = 1 := by
    rw [← map_mul, show g * g = 1 from hgg, map_one]
  rw [hg] at h3
  exact congrArg Subtype.val h3

end CFSG.Quasithin.Vol2.Ch10.SecE
