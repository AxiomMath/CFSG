module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48RkTwAHolds
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitDvdAct
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag

theorem card_ggGamma_range_ge_of_unitary_model
    {G : Type} [Group G] [Finite G] {p n d : ℕ} (hp : p.Prime)
    {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hpq : p ∣ 2 ^ n + 1) (hd : 4 ≤ d)
    {Bs X : Subgroup G} (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    {φ : ↥(unitarySU 2 n K d) →* ↥X} (hM : UnitTB.Model φ)
    (hdiag : ∀ a ∈ (ggGamma X hN).range, ∃ t : Fin d → K, LineU.ActsDiagU φ a t) :
    p ^ (d - 2) ≤ Nat.card (ggGamma X hN).range := by
  classical
  have hTle : CFSG.RankThree.PartOne.KFU.torusSU p d K ≤ unitarySU 2 n K d :=
    CFSG.RankThree.PartOne.KFU.torusSU_le_unitarySU hM.field hpq
  set T : Subgroup ↥(unitarySU 2 n K d) :=
    (CFSG.RankThree.PartOne.KFU.torusSU p d K).subgroupOf (unitarySU 2 n K d) with hTdef
  have hTcard : Nat.card T = p ^ (d - 1) := by
    rw [hTdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTle).toEquiv]
    exact ggTwA_torusSU_card hK hn hp hpq (by omega)
  set ψ : ↥T →* MulAut ↥X := (MulAut.conj : ↥X →* MulAut ↥X).comp (φ.comp T.subtype) with hψ
  have hSCA : GGTorusSelfCent p (ggGamma X hN).range := ggTorusSelfCent_ggGamma hN hSC
  have hrange : ψ.range ≤ (ggGamma X hN).range := by
    rintro _ ⟨t, rfl⟩
    have hTmem : (t.1 : GL (Fin d) K) ∈ CFSG.RankThree.PartOne.KFU.torusSU p d K :=
      Subgroup.mem_subgroupOf.mp t.2
    obtain ⟨e, _he1, _he2, he3⟩ := CFSG.RankThree.PartOne.KFU.mem_torusSU_iff.mp hTmem
    have hmat : ((t.1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        Matrix.diagonal (fun i => (e i : K)) := by
      rw [← he3, CFSG.RankThree.PartOne.KFU.diagU_val]
    have hfix : ∀ a ∈ (ggGamma X hN).range, a (φ t.1) = φ t.1 := by
      intro a ha
      obtain ⟨u, hu⟩ := hdiag a ha
      exact hu.fix_of_diagonal t.1 hmat
    have hpow : (φ t.1) ^ p = 1 := by
      rw [← map_pow, ggTwA_torus_pow t.1 hTmem, map_one]
    exact hSCA (φ t.1) hfix hpow
  have hker : ψ.ker.map T.subtype ≤
      T ⊓ (LargeEvenScalars (Fin d) K).subgroupOf (unitarySU 2 n K d) := by
    rintro _ ⟨t, ht, rfl⟩
    refine ⟨t.2, ?_⟩
    have h1 : ∀ y : ↥(unitarySU 2 n K d), φ (t.1 * y * t.1⁻¹) = φ y := by
      intro y
      have h := congrArg (fun f : MulAut ↥X => f (φ y)) (MonoidHom.mem_ker.mp ht)
      simpa [hψ, MulAut.conj_apply, map_mul, map_inv] using h
    obtain ⟨c, hc⟩ := UnitTB.scalar_of_map_conj_eq hM hK hd h1
    exact ggTwA_mem_scalars (by omega) (Subgroup.mem_subgroupOf.mp t.2) hc
  have hZs : Nat.card (T ⊓ (LargeEvenScalars (Fin d) K).subgroupOf (unitarySU 2 n K d) :
      Subgroup ↥(unitarySU 2 n K d)) ≤ p := ggTwA_scalarSubgroup_card_le hp (by omega)
  have hkercard : Nat.card ψ.ker ≤ p := by
    have h1 := Subgroup.card_le_of_le hker
    rw [Subgroup.card_map_of_injective T.subtype_injective] at h1
    exact h1.trans hZs
  have hmul : Nat.card ψ.ker * Nat.card ψ.range = Nat.card T :=
    Subgroup.card_ker_mul_card_range ψ
  have hA : Nat.card ψ.range ≤ Nat.card (ggGamma X hN).range := Subgroup.card_le_of_le hrange
  have h2 : p ^ (d - 1) ≤ p * Nat.card (ggGamma X hN).range := by
    calc p ^ (d - 1) = Nat.card ψ.ker * Nat.card ψ.range := by rw [hmul, hTcard]
      _ ≤ p * Nat.card (ggGamma X hN).range := Nat.mul_le_mul hkercard hA
  have h3 : p ^ (d - 1) = p * p ^ (d - 2) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [h3] at h2
  exact Nat.le_of_mul_le_mul_left h2 hp.pos

end CFSG.StandardType

end
