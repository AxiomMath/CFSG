module

public import CFSG.Quasithin.Vol2.KGFact3312Base
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6ResidualAll
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6TitsLattice
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListL3

public section

namespace CFSG.Quasithin.H13.KG3312

open CFSG.QuasithinUnique CFSG.Quasithin CFSG.QuasithinUnique.Setup.X6
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Assembly.LowTwoRank
open scoped Pointwise

theorem exists_conj_smul_eq {X : Type} [Group X] [Finite X] {U U₀ : Subgroup X}
    (hU : IsSylowTwoOf U ⊤) (hU₀ : IsSylowTwoOf U₀ ⊤) : ∃ g : X, MulAut.conj g • U₀ = U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hp₀, hi₀⟩ := K1.isSylowTwoOf_top_iff.mp hU₀
  obtain ⟨hp, hi⟩ := K1.isSylowTwoOf_top_iff.mp hU
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X (hp₀.toSylow hi₀) (hp.toSylow hi)
  refine ⟨g, ?_⟩
  have := congrArg (fun P : Sylow 2 X => (P : Subgroup X)) hg
  simpa [Sylow.coe_subgroup_smul] using this

theorem conj_smul_of_normal {X : Type} [Group X] {R : Subgroup X} (hR : R.Normal) (g : X) :
    MulAut.conj g • R = R :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mp
    (by rw [Subgroup.normalizer_eq_top_iff.mpr hR]; trivial)

theorem perfectCore_map_of_rank2
    {X : Type} [Group X] [Finite X] (hX : IsRank2LieChar2 X) {U : Subgroup X}
    (hU : IsSylowTwoOf U ⊤) {α : MulAut X} (hα : Odd (orderOf α))
    (hαU : U.map α.toMonoidHom = U) {M : Subgroup X} (hUM : U ≤ M) (hM : M ≠ ⊤)
    (hMs : ¬ Group.IsSolvable ↥M) : (perfectCore M).map α.toMonoidHom = perfectCore M := by
  have key : ResidualOvergroups X U ∨
      ∀ M' : Subgroup X, U ≤ M' → M' ≠ ⊤ → Group.IsSolvable ↥M' := by
    rcases hX with ⟨f, hL | hSL | hSp | hG2 | hD4 | hF4⟩ | hT
    · exact Or.inl (Setup.X7a.even_rank_two_classical_proper_Sylow_overgroup_residual hU
        (Or.inl ⟨f, hL.2⟩))
    · obtain ⟨hf, K, _, _, hcard, ⟨φ⟩⟩ := hSL
      have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hcard
      let e' : X ≃* Matrix.SpecialLinearGroup (Fin 3) K :=
        φ.trans (specialLinearGroupEquivStatedSL 3 K).symm
      obtain ⟨P₀, hP₀⟩ := exists_sylow_unitriangular (K := K) 2 (n := 3) (by norm_num)
      have hU₀ : IsSylowTwoOf (unitriangular 3 K) ⊤ := hP₀ ▸ isSylowTwoOf_top_of_sylow P₀
      have h₀ := Vol2Native.A312L.linear_three_residual_of_cover ⟨f, hcard⟩
        (MonoidHom.id (Matrix.SpecialLinearGroup (Fin 3) K)) Function.surjective_id
        (by rw [MonoidHom.ker_id]; exact bot_le)
      rw [Subgroup.map_id] at h₀
      exact Or.inl (ResidualOvergroups.of_isSylow e' ⟨_, h₀⟩ hU₀ hU)
    · exact Or.inl (Setup.X7a.even_rank_two_classical_proper_Sylow_overgroup_residual hU
        (Or.inr ⟨f, hSp.2⟩))
    · exact Or.inl (even_rank_two_exceptional_proper_Sylow_overgroup_residual hU
        (Or.inl ⟨f, hG2⟩))
    · exact Or.inl (even_rank_two_exceptional_proper_Sylow_overgroup_residual hU
        (Or.inr (Or.inl ⟨f, hD4⟩)))
    · exact Or.inl (even_rank_two_exceptional_proper_Sylow_overgroup_residual hU
        (Or.inr (Or.inr ⟨f, hF4.2.1, hF4.1, hF4.2.2⟩)))
    · refine Or.inr fun M' hUM' hM' => ?_
      obtain ⟨H, N, -, -, -, -, -, hlat, hHs, hNs⟩ := titsSylowOvergroupLattice X hT U hU
      rcases hlat M' hUM' with h | h | h | h
      · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        have : Group.IsNilpotent ↥M' := h ▸ hU.2.1.isNilpotent
        infer_instance
      · exact h ▸ hHs
      · exact h ▸ hNs
      · exact absurd h hM'
  rcases key with ⟨P, hP⟩ | hsolv
  · have h := hP.2.2.2.2.2 α hα hαU M hUM hM hMs
    rwa [Vol2Native.A312L.dInf_eq_perfectCore] at h
  · exact absurd (hsolv M hUM hM) hMs

theorem factLie2Norm3312_holds :
    FactLie2Norm3312 := by
  intro Q _ _ hQ A S P hA hS hP hSP d hd hodd
  obtain ⟨U, hU, hUT, hUd⟩ := exists_sylow_comap_conj hA hS
  have hdU : U.map d.toMonoidHom = U := hUd d (Subgroup.mem_inf.mp hd).1
  set R : Subgroup Q := perfectCore P with hR
  have hUR : U ≤ Subgroup.normalizer (R : Set Q) := hUT.trans (comap_conj_le_normalizer hSP)
  rcases eq_or_ne R ⊥ with hR1 | hR1
  · rw [hR1]
    exact mem_stabilizer_subgroup_iff.mpr (Subgroup.map_bot _)
  set M : Subgroup Q := R ⊔ U with hM
  have hRM : R ≤ M := le_sup_left
  have hUM : U ≤ M := le_sup_right
  have hMN : M ≤ Subgroup.normalizer (R : Set Q) := sup_le Subgroup.le_normalizer hUR
  have hUs : Group.IsSolvable ↥U := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : Group.IsNilpotent ↥U := hU.2.1.isNilpotent
    infer_instance
  have hMR : perfectCore M = R :=
    le_antisymm
      (perfectCore_le_of_sup_solvable hRM
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hRM).mpr hMN) hM hUs)
      (le_perfectCore_of_perfect hRM (perfectCore_perfect P))
  have hMtop : M ≠ ⊤ := by
    intro htop
    have hRn : R.Normal :=
      Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (htop ▸ hMN))
    obtain ⟨⟨-, U₀, hU₀, hN₀⟩, hPtop, -⟩ := hP
    have hU₀P : U₀ ≤ P := fun x hx => hN₀ ⟨Subgroup.mem_top x, Subgroup.le_normalizer hx⟩
    obtain ⟨g, hg⟩ := exists_conj_smul_eq hU hU₀
    have hle : M ≤ MulAut.conj g • P := by
      refine sup_le ?_ ?_
      · rw [← conj_smul_of_normal hRn g]
        exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr (perfectCore_le P)
      · rw [← hg]
        exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hU₀P
    rw [htop, top_le_iff] at hle
    apply hPtop
    refine Subgroup.eq_top_of_card_eq P ?_
    rw [Nat.card_congr (Subgroup.equivSMul (MulAut.conj g) P).toEquiv, hle, Subgroup.card_top]
  have hMs : ¬ Group.IsSolvable ↥M := by
    rw [isSolvable_iff_perfectCore_eq_bot, hMR]
    exact hR1
  have h := perfectCore_map_of_rank2 hQ hU hodd hdU hUM hMtop hMs
  rw [hMR] at h
  exact mem_stabilizer_subgroup_iff.mpr h

end CFSG.Quasithin.H13.KG3312
