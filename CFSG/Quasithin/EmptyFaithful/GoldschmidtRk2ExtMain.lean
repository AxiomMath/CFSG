module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ExtL3
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ExtSp4
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ParSp4
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.Rk2

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6 CFSG.Quasithin
open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.QuasithinUnique.Setup.X7a
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

theorem Rank2Pkg.Ext.of_isSylow {Y : Type} [Group Y] [Finite Y] {U₀ U : Subgroup Y}
    {P₀ : Fin 2 → Subgroup Y} (h₀ : Rank2Pkg Y U₀ P₀) (x₀ : Rank2Pkg.Ext Y U₀ P₀)
    (hU₀ : IsSylowTwoOf U₀ ⊤) (hU : IsSylowTwoOf U ⊤) :
    ∃ P : Fin 2 → Subgroup Y, Rank2Pkg Y U P ∧ Rank2Pkg.Ext Y U P := by
  obtain ⟨k, -, hk⟩ := (isSylowTwoOf_iff_isSylowOf.1 hU₀).exists_mem_conj
    (isSylowTwoOf_iff_isSylowOf.1 hU)
  have hconj : U₀.map (MulAut.conj k).toMonoidHom = U := by
    ext x
    rw [Subgroup.mem_map_equiv]
    simp only [MulAut.conj_symm_apply]
    exact (hk x).symm
  subst hconj
  exact ⟨fun j => (P₀ j).map (MulAut.conj k).toMonoidHom, h₀.map (MulAut.conj k),
    x₀.map (MulAut.conj k)⟩

theorem Rank2Pkg.Ext.exists_of_equiv {Y C : Type} [Group Y] [Group C] [Finite Y] [Finite C]
    (e : Y ≃* C) {U₀ : Subgroup C} {P₀ : Fin 2 → Subgroup C} (h : Rank2Pkg C U₀ P₀)
    (x : Rank2Pkg.Ext C U₀ P₀) (hU₀ : IsSylowTwoOf U₀ ⊤) {U : Subgroup Y}
    (hU : IsSylowTwoOf U ⊤) : ∃ P : Fin 2 → Subgroup Y, Rank2Pkg Y U P ∧ Rank2Pkg.Ext Y U P :=
  Rank2Pkg.Ext.of_isSylow (h.map e.symm) (x.map e.symm)
    (CFSG.QuasithinUnique.B113Lie.isSylowTwoOf_map_top e.symm hU₀) hU

theorem rank2PkgExt_exists_psl3 {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hn : 2 ≤ n)
    (hY : IsPSL 3 2 n Y) {U : Subgroup Y} (hU : IsSylowTwoOf U ⊤) :
    ∃ P : Fin 2 → Subgroup Y, Rank2Pkg Y U P ∧ Rank2Pkg.Ext Y U P := by
  obtain ⟨-, K, hF, hFin, hcard, ⟨e⟩⟩ := hY
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hcard
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := exists_sylow_projUnitriangular (K := K) 2 (n := 3) (by norm_num)
  have hU₀ : IsSylowTwoOf (projUnitriangular 3 K) ⊤ := hP ▸ isSylowTwoOf_top_of_sylow P
  exact Rank2Pkg.Ext.exists_of_equiv (e.trans (statedSLEquivProjectiveSL 3 K))
    (rank2Pkg_proj3 hcard hn) (rank2PkgExt_proj3 hcard hn) hU₀ hU

theorem rank2PkgExt_exists_sp4 {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hn : 2 ≤ n)
    (hY : IsPSp4 2 n Y) {U : Subgroup Y} (hU : IsSylowTwoOf U ⊤) :
    ∃ P : Fin 2 → Subgroup Y, Rank2Pkg Y U P ∧ Rank2Pkg.Ext Y U P := by
  obtain ⟨-, K, hF, hFin, hcard, ⟨e⟩⟩ := hY
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hcard
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := exists_sylow_projUnipotent (K := K) 2 (r := 2) (by norm_num)
  have hU₀ : IsSylowTwoOf (projUnipotent 2 K) ⊤ := hP ▸ isSylowTwoOf_top_of_sylow P
  exact Rank2Pkg.Ext.exists_of_equiv e (rank2Pkg_sp4 hcard hn) (rank2PkgExt_sp4 hcard hn) hU₀ hU

theorem rank2PkgExt_exists {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hn : 2 ≤ n)
    (hY : IsPSL 3 2 n Y ∨ IsPSp4 2 n Y) {U : Subgroup Y} (hU : IsSylowTwoOf U ⊤) :
    ∃ P : Fin 2 → Subgroup Y, Rank2Pkg Y U P ∧ Rank2Pkg.Ext Y U P := by
  rcases hY with h | h
  · exact rank2PkgExt_exists_psl3 hn h hU
  · exact rank2PkgExt_exists_sp4 hn h hU

end CFSG.Quasithin.Rk2
