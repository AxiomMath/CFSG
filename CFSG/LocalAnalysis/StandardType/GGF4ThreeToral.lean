module

public import CFSG.LocalAnalysis.StandardType.GGIrred937F4TorA

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial

@[expose] def ggF4Sh_A2A2
    {K : Type} [Field K] (e : adjointGroup Tag.F4 K) : Prop :=
  ∃ g ∈ adjointGroup Tag.F4 (AlgebraicClosure K),
    ∃ a : Fin Tag.F4.rank → (AlgebraicClosure K)ˣ, (∀ i, a i ^ 3 = 1) ∧
      (rootCharKernel (τ := Tag.F4) a).ncard = 12 ∧
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL Tag.F4 K) =
        g * rootDiagUnit Tag.F4 a * g⁻¹

theorem ggF4Sh_toral_of_notA2A2
    (K : Type) [Field K] [Finite K] [CharP K 2] (hq : 3 ∣ Nat.card K + 1)
    (E : Subgroup (adjointGroup Tag.F4 K)) (hE : IsElemAbelian 3 E)
    (e : adjointGroup Tag.F4 K) (he : e ∈ E) (he1 : e ≠ 1) (hne : ¬ ggF4Sh_A2A2 e) :
    ∃ g ∈ adjointGroup Tag.F4 (AlgebraicClosure K), ∀ x ∈ E,
      g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) ((x : adjointGroup Tag.F4 K) :
        ModGL Tag.F4 K) * g ∈ torusGroup Tag.F4 (AlgebraicClosure K) := by
  classical
  set L := AlgebraicClosure K
  have hK3 : ¬ 3 ∣ Nat.card K := by
    intro h
    have h1 : 3 ∣ 1 := (Nat.dvd_add_right h).1 hq
    omega
  have hmon : MonomialToralAt Tag.F4 3 := monomialToralAt_three_of_block a2BlockToral_F4
  have he3 : (e : ModGL Tag.F4 K) ^ 3 = 1 := by
    have := hE.2 e he
    exact congrArg Subtype.val this
  obtain ⟨g, hg, a, ha3, hga⟩ :=
    CFSG.LocalAnalysis.RankFourTheoremC.ExcRank.exists_toral_conj_gen Nat.prime_three hmon K hK3
      e.2 he3
  have ha1 : a ≠ 1 := by
    rintro rfl
    apply he1
    apply Subtype.ext
    apply baseChangeGL_injective (algebraMap K L)
    rw [hga, CFSG.LieType.Chevalley.rootDiagUnit_one, mul_one, mul_inv_cancel]
    exact (map_one _).symm
  rcases Irred937.f4ThreeKernelDichotomy_holds L a ha3 ha1 with h12 | h18
  · exact absurd ⟨g, hg, a, ha3, h12, hga⟩ hne
  · let φ : adjointGroup Tag.F4 K →* ModGL Tag.F4 L :=
      (baseChangeGL (algebraMap K L)).comp (adjointGroup Tag.F4 K).subtype
    let A : Subgroup (ModGL Tag.F4 L) := E.map φ
    have hAle : A ≤ adjointGroup Tag.F4 L := by
      rintro _ ⟨x, -, rfl⟩
      exact CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup _ x.2
    haveI : Finite (adjointGroup Tag.F4 K) := Subtype.finite
    have hAfin : Finite A := by
      change Finite ↥(E.map φ)
      exact Finite.Set.finite_image _ _
    have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      have := congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
      rw [← map_mul, ← map_mul]
      exact congrArg φ this
    have hAexp : ∀ x ∈ A, x ^ 3 = 1 := by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hE.2 x hx, map_one]
    have hmem : g * rootDiagUnit Tag.F4 a * g⁻¹ ∈ A := ⟨e, he, hga⟩
    obtain ⟨C, hC, hCT⟩ := Irred937.f4ThreeEighteenToral_holds K hK3 A hAle hAfin hAcomm hAexp g hg
      a ha3 h18 hmem
    exact ⟨C, hC, fun x hx => hCT _ ⟨x, hx, rfl⟩⟩

end CFSG.StandardType

end
