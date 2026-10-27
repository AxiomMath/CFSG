module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniBlocks
public import CFSG.LocalAnalysis.StandardType.GGSignedCoordBlocks
import CFSG.LocalAnalysis.StandardType.GGTBRowSignedFrameAux
import CFSG.LocalAnalysis.StandardType.GGQTwoSUThreeDiagonalComm
import CFSG.LocalAnalysis.StandardType.GGSuNsRootGenTriples
import CFSG.LocalAnalysis.StandardType.GGSecFiveBNbrCompare

public section

namespace CFSG.StandardType

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

theorem exists_mem_conjAut_eq_permAut_swap_of_bBlockOn {G : Type} [Group G] {p n : ℕ}
    {Bs X : Subgroup G} {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {I : Finset (Fin n)}
    (hA : (ggAutomizer X Bs).map (MulAut.congr eta).toMonoidHom = bBlockOn n p I)
    {a b : Fin n} (ha : a ∈ I) (hb : b ∈ I) (hab : a ≠ b) :
    ∃ g ∈ X, ∃ hg : g ∈ Subgroup.normalizer (Bs : Set G),
      MulAut.congr eta (ggConjAut Bs hg) = SpCoord.permAut (Equiv.swap a b) := by
  have hmem : SpCoord.permAut (Equiv.swap a b) ∈
      (ggAutomizer X Bs).map (MulAut.congr eta).toMonoidHom := by
    rw [hA]
    exact Subgroup.subset_closure (Or.inr ⟨a, ha, b, hb, hab, rfl⟩)
  obtain ⟨g, hgN, hgX, hgτ⟩ := exists_mem_of_mem_map_congr eta hmem
  exact ⟨g, hgX, hgN, hgτ⟩

theorem exists_mem_conjAut_eq_permAut_of_swaps {G : Type} [Group G] {p n : ℕ}
    {Bs M : Subgroup G} {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {I J : Finset (Fin n)}
    (hIJ : I ∪ J = Finset.univ) (hIJne : (I ∩ J).Nonempty)
    (hswap : ∀ a b : Fin n, a ≠ b → (a ∈ I ∧ b ∈ I) ∨ (a ∈ J ∧ b ∈ J) →
      ∃ g ∈ M, ∃ hg : g ∈ Subgroup.normalizer (Bs : Set G),
        MulAut.congr eta (ggConjAut Bs hg) = SpCoord.permAut (Equiv.swap a b))
    (τ : Equiv.Perm (Fin n)) :
    ∃ g ∈ M, ∃ hg : g ∈ Subgroup.normalizer (Bs : Set G),
      MulAut.congr eta (ggConjAut Bs hg) = SpCoord.permAut τ := by
  let P : Subgroup (Equiv.Perm (Fin n)) :=
    Subgroup.comap (ggSpSigned_permAutHom p n)
      ((ggAutomizer M Bs).map (MulAut.congr eta).toMonoidHom)
  have hswapP : ∀ a b : Fin n, a ≠ b → ((a ∈ I ∧ b ∈ I) ∨ (a ∈ J ∧ b ∈ J)) →
      Equiv.swap a b ∈ P := by
    intro a b hab hcase
    obtain ⟨g, hgM, hgN, hgτ⟩ := hswap a b hab hcase
    exact Subgroup.mem_comap.mpr (Subgroup.mem_map.mpr
      ⟨ggConjAut Bs hgN, ggConjAut_mem_ggAutomizer hgM hgN, hgτ⟩)
  have hmixed : ∀ a b : Fin n, a ∈ I → b ∈ J → a ∉ J → b ∉ I → Equiv.swap a b ∈ P := by
    intro a b haI hbJ haJ hbI
    obtain ⟨c, hc⟩ := hIJne
    obtain ⟨hcI, hcJ⟩ := Finset.mem_inter.mp hc
    have hba : b ≠ a := fun h => hbI (h ▸ haI)
    have hbc : b ≠ c := fun h => hbI (h ▸ hcI)
    have h1 : Equiv.swap a c ∈ P :=
      hswapP a c (fun h => haJ (h ▸ hcJ)) (Or.inl ⟨haI, hcI⟩)
    have h2 : Equiv.swap c b ∈ P :=
      hswapP c b (Ne.symm hbc) (Or.inr ⟨hcJ, hbJ⟩)
    have hcycle : Equiv.swap a b = Equiv.swap a c * Equiv.swap c b * Equiv.swap a c := by
      rw [← Equiv.swap_mul_swap_mul_swap (x := b) (y := c) (z := a) hbc hba]
      rw [Equiv.swap_comm c a, Equiv.swap_comm b c]
    rw [hcycle]
    exact P.mul_mem (P.mul_mem h1 h2) h1
  have hswap_mem : ∀ a b : Fin n, a ≠ b → Equiv.swap a b ∈ P := by
    intro a b hab
    by_cases hI : a ∈ I ∧ b ∈ I
    · exact hswapP a b hab (Or.inl hI)
    by_cases hJ : a ∈ J ∧ b ∈ J
    · exact hswapP a b hab (Or.inr hJ)
    have haU : a ∈ I ∪ J := hIJ ▸ Finset.mem_univ a
    have hbU : b ∈ I ∪ J := hIJ ▸ Finset.mem_univ b
    rcases Finset.mem_union.mp haU with haI | haJ
    · have hbI : b ∉ I := fun hb => hI ⟨haI, hb⟩
      have hbJ : b ∈ J := (Finset.mem_union.mp hbU).resolve_left hbI
      have haJ : a ∉ J := fun ha => hJ ⟨ha, hbJ⟩
      exact hmixed a b haI hbJ haJ hbI
    · have hbJ : b ∉ J := fun hb => hJ ⟨haJ, hb⟩
      have hbI : b ∈ I := (Finset.mem_union.mp hbU).resolve_right hbJ
      have haI : a ∉ I := fun ha => hI ⟨ha, hbI⟩
      rw [Equiv.swap_comm a b]
      exact hmixed b a hbI haJ hbJ haI
  have hτP : τ ∈ P := by
    refine Equiv.Perm.swap_induction_on (motive := fun τ => τ ∈ P) τ P.one_mem ?_
    intro τ a b hab hτ
    exact P.mul_mem (hswap_mem a b hab) hτ
  have hmem : SpCoord.permAut τ ∈
      (ggAutomizer M Bs).map (MulAut.congr eta).toMonoidHom := by
    change ggSpSigned_permAutHom p n τ ∈
      (ggAutomizer M Bs).map (MulAut.congr eta).toMonoidHom
    exact Subgroup.mem_comap.mp hτP
  obtain ⟨g, hgN, hgM, hgτ⟩ := exists_mem_of_mem_map_congr eta hmem
  exact ⟨g, hgM, hgN, hgτ⟩

theorem GGSecFiveBPermUniLFrame.le_of_permLift {G : Type} [Group G] {p n : ℕ} {K : Type}
    [Field K] {Bs X M : Subgroup G} {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    {π : Equiv.Perm (Fin n)} {σ : ↥(unitarySU 2 1 K n) →* G} {χ : Multiplicative (ZMod p) →* Kˣ}
    (hF : GGSecFiveBPermUniLFrame Bs X eta π σ χ) (h : UnitaryFieldData 2 1 K) (hp : p.Prime)
    (hn : 3 ≤ n) {S₀ : Finset (Fin n)} (hS₀ : S₀.card = 3)
    (hS₀M : ggBlockComm Bs eta (S₀ : Set (Fin n)) ≤ M)
    (hlift : ∀ τ : Equiv.Perm (Fin n), ∃ g ∈ M, ∃ hg : g ∈ Subgroup.normalizer (Bs : Set G),
      MulAut.congr eta (ggConjAut Bs hg) = SpCoord.permAut τ) :
    X ≤ M := by
  rw [← hF.1, MonoidHom.range_eq_map]
  rw [← SuNsRootGen.iSup_blockSU_card_three_eq_top (K := K) (n := 1) (d := n) h hn]
  simp only [Subgroup.map_iSup]
  refine iSup_le fun S => iSup_le fun hS => ?_
  obtain ⟨τ, hτ⟩ := Equiv.Perm.exists_map_finset_eq S₀ (S.map π.toEmbedding)
    (by rw [Finset.card_map, hS, hS₀])
  have hτset : τ '' (S₀ : Set (Fin n)) = π '' (S : Set (Fin n)) := by
    have h := congrArg (fun t : Finset (Fin n) => (t : Set (Fin n))) hτ
    simpa only [Finset.coe_map, Equiv.coe_toEmbedding] using h
  obtain ⟨g, hgM, hgN, hgτ⟩ := hlift τ
  have hconj := ggBlockComm_map_conj (Bs := Bs) (eta := eta) hgN hgτ (S₀ : Set (Fin n))
  rw [hτset] at hconj
  have hblock : (ggBlockComm Bs eta (S₀ : Set (Fin n))).map
      (MulAut.conj g).toMonoidHom ≤ M := by
    rintro x ⟨y, hy, rfl⟩
    change MulAut.conj g y ∈ M
    rw [MulAut.conj_apply]
    exact M.mul_mem (M.mul_mem hgM (hS₀M hy)) (M.inv_mem hgM)
  refine (hF.map_blockSU_triple_le_ggBlockComm h hp S hS).trans ?_
  rw [← hconj]
  exact hblock

end CFSG.StandardType

end
