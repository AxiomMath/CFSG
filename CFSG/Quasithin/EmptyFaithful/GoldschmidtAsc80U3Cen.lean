module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80U3Syl

public section

namespace CFSG.Quasithin.E2P.Asc80

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.Assembly.LowTwoRank CFSG.RankThree.CentralCover CFSG.RankThree.Classical
  CFSG.GH74.GLS.IVK.Proofs2 CFSG.Quasithin.A312U3 CFSG.Quasithin.B6 CFSG.QuasithinUnique
open scoped MatrixGroups

variable {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem zcU_comm_leviCU (hF : Nat.card F = p ^ 2) {b : PSU3F p F} (hb : b ∈ leviCU hF) :
    zcU hF * b = b * zcU hF := by
  obtain ⟨gb, ⟨B, rfl⟩, rfl⟩ := hb
  have h := Lemma41aU3.blkU_commute (uniData hF) B
  show piU p F (tU hF) * piU p F (Lemma41aU3.blkU (uniData hF) B) =
    piU p F (Lemma41aU3.blkU (uniData hF) B) * piU p F (tU hF)
  rw [← map_mul, ← map_mul, h]

theorem tU_eq_sq (hp2 : p ≠ 2) (hF : Nat.card F = p ^ 2) {c d : ↥(StatedSU 2 (p ^ 1) F)}
    (hQ : QuatPair c d) : tU hF = ofSU2 hF c * ofSU2 hF c := by
  have h2 := two_ne_zero_u hp2 hF
  have hQ' := hQ.map (StatedSU 2 (p ^ 1) F).subtype (StatedSU 2 (p ^ 1) F).subtype_injective
  obtain ⟨hC, -, -⟩ := quat_relations h2 (det_of_mem_su2 hF c) hQ'
  apply ext_matU
  rw [matU_mul, matU_ofSU2, Lemma41aL3.blkMat_mul]
  have hC' : ((c : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (c : GL (Fin 2) F) = -1 := hC
  rw [hC', matU_tU]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Lemma41aL3.blkMat, negNegOneDiag]

theorem zcU_eq_sq (hp2 : p ≠ 2) (hF : Nat.card F = p ^ 2) {c d : ↥(StatedSU 2 (p ^ 1) F)}
    (hQ : QuatPair c d) : zcU hF = piU p F (ofSU2 hF c) * piU p F (ofSU2 hF c) := by
  rw [← map_mul, ← tU_eq_sq hp2 hF hQ]

theorem centralizer_zOf_eq_special_u (hp2 : p ≠ 2) (hF : Nat.card F = p ^ 2)
    {U : Subgroup (PSU3F p F)} {c d : ↥(StatedSU 2 (p ^ 1) F)} (hQ : QuatPair c d)
    (hc : piU p F (ofSU2 hF c) ∈ U) (hd : piU p F (ofSU2 hF d) ∈ U) (hUB : U ≤ leviCU hF) :
    Subgroup.centralizer (zOf U : Set (PSU3F p F)) = leviCU hF := by
  have hzU : zcU hF ∈ zOf U := by
    refine ⟨?_, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
    · rw [zcU_eq_sq hp2 hF hQ]
      exact U.mul_mem hc hc
    · exact (zcU_comm_leviCU hF (hUB hu)).symm
  apply le_antisymm
  · intro g hg
    exact mem_leviCU_of_commute_z hp2 hF (Subgroup.mem_centralizer_iff.mp hg (zcU hF) hzU).symm
  · intro b hb
    exact Subgroup.mem_centralizer_iff.mpr fun w hw => zOf_comm_leviU hp2 hF hQ hc hd hUB hw hb

theorem centralizer_zOf_eq_leviCU (hp2 : p ≠ 2) (hF : Nat.card F = p ^ 2)
    {U : Subgroup (PSU3F p F)} (hU : IsSylowTwoOf U ⊤) (hUB : U ≤ leviCU hF) :
    Subgroup.centralizer (zOf U : Set (PSU3F p F)) = leviCU hF := by
  obtain ⟨U₀, c, d, hU₀, hU₀B, hQ, hc, hd⟩ := exists_special_sylow_u hp2 hF
  obtain ⟨g, hg, hUg⟩ := isSylowTwoOf_exists_conj (isSylowTwoOf_mono hU₀ hU₀B le_top)
    (isSylowTwoOf_mono hU hUB le_top)
  have hUeq : U = U₀.map (MulAut.conj g).toMonoidHom := hUg
  rw [hUeq, ← map_zOf, ← map_centralizer_eq, centralizer_zOf_eq_special_u hp2 hF hQ hc hd hU₀B]
  exact conjSub_eq_self (Subgroup.le_normalizer hg)

end CFSG.Quasithin.E2P.Asc80
