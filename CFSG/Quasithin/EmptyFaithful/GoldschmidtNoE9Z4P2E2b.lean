module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P2E2
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P2E3c

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
  CFSG.Quasithin.GoldS146P

section Fstar

variable {G : Type} [Group G] [Finite G] {T M H PQ : Subgroup G} {p : ℕ}

namespace E9P2.E2

theorem sp4_four_isSimple_nonabelian {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 4) :
    IsSimpleGroup (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSp 2 F)) ∧
      ∃ a b : CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSp 2 F),
        a * b ≠ b * a := by
  have hs : IsSimpleGroup
      (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSp 2 F)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp F 2 (by norm_num)
      (Or.inl (Or.inr (by omega)))
  refine ⟨hs, ?_⟩
  by_contra hcomm
  push Not at hcomm
  have : IsMulCommutative
      (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSp 2 F)) :=
    ⟨⟨fun a b => hcomm a b⟩⟩
  have hprime := IsSimpleGroup.prime_card
    (α := CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSp 2 F))
  rw [CFSG.QuasithinUnique.Id2519.USp4.card_projSp_two hF] at hprime
  norm_num at hprime

end E9P2.E2

theorem e9_isComponent_image_sp4_four {G₁ K : Subgroup G} (hK : K ∈ cComp G₁)
    (e : Nonempty (OTwoQuot K ≃* ↥(Matrix.symplecticGroup (Fin 2) (GaloisField 2 2)))) :
    CFSG.IsComponent (imageOTwoQuot G₁ K) := by
  obtain ⟨e⟩ := e
  obtain ⟨ψ₀⟩ := E9P2.E2.image_equiv_stated hK e
  have hcard : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by omega)]
    norm_num
  obtain ⟨hs, hnonab⟩ := E9P2.E2.sp4_four_isSimple_nonabelian hcard
  have := hs
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (ψ₀.trans (CFSG.QuasithinUnique.Lin2.Five.projEquiv (GaloisField 2 2))).symm
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnonab).1, ?_⟩
  exact Id2519.mathlib_isSubnormal_of_open_top (subnormal_of_mem_cComp (q_image_mem_cComp hK))

theorem e9_fstar_of_E2 (S : Setting146 G T M) (_hred : IsRedCE T M H PQ p)
    (hC : Stage14614E9C2 T H) : oTwoUpper H ≤ oTwoFstarIn (mcOf T) := by
  classical
  obtain ⟨hKz, ⟨e⟩, hG⟩ := hC
  have hKzG : conjClosure (oTwoUpper H) (mcOf T) ≤ mcOf T := le_of_mem_cComp hKz
  have hN := e9_isComponent_image_sp4_four hKz ⟨e⟩
  have hKzN : mcOf T ≤ Subgroup.normalizer
      ((conjClosure (oTwoUpper H) (mcOf T) : Subgroup G) : Set G) :=
    le_normalizer_conjClosure _ _
  have hNn : (imageOTwoQuot (mcOf T) (conjClosure (oTwoUpper H) (mcOf T))).Normal :=
    q_normal_image_of_normal hKzG hKzN
  have hNle : imageOTwoQuot (mcOf T) (conjClosure (oTwoUpper H) (mcOf T)) ≤
      CFSG.layer (OTwoQuot (mcOf T)) := CFSG.LocalCores.component_le_layer hN
  have hpq : IsPGroup 2 (OTwoQuot (mcOf T) ⧸
      imageOTwoQuot (mcOf T) (conjClosure (oTwoUpper H) (mcOf T))) :=
    isPGroup_two_quotient_of_decomp (q_hatT_sylow S).2.1 (e9_hX_of_eq_sup S hG)
  have : Group.IsNilpotent (OTwoQuot (mcOf T) ⧸
      imageOTwoQuot (mcOf T) (conjClosure (oTwoUpper H) (mcOf T))) := hpq.isNilpotent
  have hlayer : PerfInLayer (OTwoQuot (mcOf T)) := perfInLayer_of_le_layer _ hNle
  have hlayer' : PerfInLayer (↥(mcOf T) ⧸ CFSG.pCore 2 ↥(mcOf T)) :=
    PerfInLayer.of_equiv (QuotientGroup.quotientMulEquivOfEq (CFSG.pCore_eq_open ↥(mcOf T) 2))
      hlayer
  exact (le_conjClosure _ _).trans
    (perfect_le_oTwoFstarIn hlayer' hKzG (perfect_of_mem_cComp hKz))

end Fstar

end CFSG.Quasithin
