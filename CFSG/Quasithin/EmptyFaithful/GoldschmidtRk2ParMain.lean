module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ParSp4
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ParG2
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.Rk2

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6 CFSG.Quasithin
open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.QuasithinUnique.Setup.X7a
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

set_option linter.unusedSectionVars false

theorem Rank2Pkg.of_isSylow {Y : Type} [Group Y] [Finite Y] {U₀ U : Subgroup Y}
    {P₀ : Fin 2 → Subgroup Y} (h₀ : Rank2Pkg Y U₀ P₀) (hU₀ : IsSylowTwoOf U₀ ⊤)
    (hU : IsSylowTwoOf U ⊤) : ∃ P : Fin 2 → Subgroup Y, Rank2Pkg Y U P := by
  obtain ⟨k, -, hk⟩ := (isSylowTwoOf_iff_isSylowOf.1 hU₀).exists_mem_conj
    (isSylowTwoOf_iff_isSylowOf.1 hU)
  have hconj : U₀.map (MulAut.conj k).toMonoidHom = U := by
    ext x
    rw [Subgroup.mem_map_equiv]
    simp only [MulAut.conj_symm_apply]
    exact (hk x).symm
  refine ⟨fun j => (P₀ j).map (MulAut.conj k).toMonoidHom, ?_⟩
  have := h₀.map (MulAut.conj k)
  rwa [hconj] at this

theorem Rank2Pkg.exists_of_equiv {Y C : Type} [Group Y] [Group C] [Finite Y] [Finite C]
    (e : Y ≃* C) {U₀ : Subgroup C} {P₀ : Fin 2 → Subgroup C} (h : Rank2Pkg C U₀ P₀)
    (hU₀ : IsSylowTwoOf U₀ ⊤) {U : Subgroup Y} (hU : IsSylowTwoOf U ⊤) :
    ∃ P : Fin 2 → Subgroup Y, Rank2Pkg Y U P :=
  (h.map e.symm).of_isSylow (CFSG.QuasithinUnique.B113Lie.isSylowTwoOf_map_top e.symm hU₀) hU

theorem rank2Pkg_exists_psl3 {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hn : 2 ≤ n)
    (hY : IsPSL 3 2 n Y) {U : Subgroup Y} (hU : IsSylowTwoOf U ⊤) :
    ∃ P : Fin 2 → Subgroup Y, Rank2Pkg Y U P := by
  obtain ⟨-, K, hF, hFin, hcard, ⟨e⟩⟩ := hY
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hcard
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := exists_sylow_projUnitriangular (K := K) 2 (n := 3) (by norm_num)
  have hU₀ : IsSylowTwoOf (projUnitriangular 3 K) ⊤ := hP ▸ isSylowTwoOf_top_of_sylow P
  exact Rank2Pkg.exists_of_equiv (e.trans (statedSLEquivProjectiveSL 3 K))
    (rank2Pkg_proj3 hcard hn) hU₀ hU

theorem rank2Pkg_exists_sl3 {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hn : 2 ≤ n)
    (hY : IsSL3 (2 ^ n) Y) {U : Subgroup Y} (hU : IsSylowTwoOf U ⊤) :
    ∃ P : Fin 2 → Subgroup Y, Rank2Pkg Y U P := by
  obtain ⟨K, hF, hFin, hcard, ⟨e⟩⟩ := hY
  have hcard' : Nat.card K = 2 ^ n := hcard
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hcard'
  exact Rank2Pkg.exists_of_equiv (e.trans (specialLinearGroupEquivStatedSL 3 K).symm)
    (rank2Pkg_sl3 hcard' hn) (SzN2.isSylowTwoOf_unitriangular (by norm_num)) hU

theorem rank2Pkg_exists_sp4 {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hn : 2 ≤ n)
    (hY : IsPSp4 2 n Y) {U : Subgroup Y} (hU : IsSylowTwoOf U ⊤) :
    ∃ P : Fin 2 → Subgroup Y, Rank2Pkg Y U P := by
  obtain ⟨-, K, hF, hFin, hcard, ⟨e⟩⟩ := hY
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hcard
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := exists_sylow_projUnipotent (K := K) 2 (r := 2) (by norm_num)
  have hU₀ : IsSylowTwoOf (projUnipotent 2 K) ⊤ := hP ▸ isSylowTwoOf_top_of_sylow P
  exact Rank2Pkg.exists_of_equiv e (rank2Pkg_sp4 hcard hn) hU₀ hU

theorem rank2Pkg_exists_g2
    {Y : Type} [Group Y] [Finite Y] {n : ℕ}
    (hY : IsG2 2 n Y) {U : Subgroup Y} (hU : IsSylowTwoOf U ⊤) :
    ∃ P : Fin 2 → Subgroup Y, Rank2Pkg Y U P := by
  obtain ⟨hn, K, hF, hFin, hCh, hK, ⟨e⟩⟩ := exists_mulEquiv_G2_model hY
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  have hU₀ : IsSylowTwoOf ((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K)) ⊤ :=
    isSylowTwoOf_subgroupOf_top (isSylowTwoOf_iff_isSylowOf.2
      (unique_Chevalley_positive_Sylow (τ := Tag.G2) (K := K) 2).1)
  exact Rank2Pkg.exists_of_equiv e (rank2Pkg_g2 hK hn) hU₀ hU

theorem rank2Pkg_exists
    {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hn : 2 ≤ n)
    (hY : IsPSL 3 2 n Y ∨ IsSL3 (2 ^ n) Y ∨ IsPSp4 2 n Y ∨ IsG2 2 n Y) {U : Subgroup Y}
    (hU : IsSylowTwoOf U ⊤) : ∃ P : Fin 2 → Subgroup Y, Rank2Pkg Y U P := by
  rcases hY with h | h | h | h
  · exact rank2Pkg_exists_psl3 hn h hU
  · exact rank2Pkg_exists_sl3 hn h hU
  · exact rank2Pkg_exists_sp4 hn h hU
  · exact rank2Pkg_exists_g2 h hU

end CFSG.Quasithin.Rk2
