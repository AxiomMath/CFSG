module

public import CFSG.LinearAlgebra.SL2CharTwoFixedVector
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsThirtyNineAbFinal
public import CFSG.Quasithin.Background.G2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

namespace Ctx23L

theorem sq_mem_inf_centralizer_V_of_mem_centralizer_Z (D : Data G) (Ch : Choice2011 G)
    (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch)
    {b : G} (hbL : b ∈ c.L) (hbZ : b ∈ Subgroup.centralizer (D.Z : Set G)) :
    b ^ 2 ∈ c.L ⊓ Subgroup.centralizer (c.V : Set G) := by
  classical
  obtain ⟨⟨z, hzZ⟩, hz1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp (uc22main1_Z_ne_bot D)
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hzV : z ∈ c.V := uc22p22v_le_conjClosure c.N D.Z hzZ
  obtain ⟨hV, hLV, κ, hκker, -⟩ :=
    Ctx23L.exists_coordinates_V D Ch h4 h23 h1930 c
  let l : ↥c.L := ⟨b, hbL⟩
  let v : ↥c.V := ⟨z, hzV⟩
  have hconj : CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjV hLV l v = v := by
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr
      (Subgroup.mem_centralizer_iff.mp hbZ z hzZ).symm
  have hvne : Multiplicative.toAdd (κ.β v) ≠ 0 := by
    intro h0
    apply hz1'
    have h2 : v = 1 := κ.β_bij.1 (by
      simpa using Multiplicative.toAdd.injective (by simpa using h0))
    simpa [v] using congrArg Subtype.val h2
  have hfix : Matrix.mulVec (κ.α l : Matrix (Fin 2) (Fin 2) κ.K)
      (Multiplicative.toAdd (κ.β v)) = Multiplicative.toAdd (κ.β v) := by
    have h := congrArg Multiplicative.toAdd (κ.β_act l v)
    simpa [hconj] using h.symm
  have hsq : (κ.α l : Matrix (Fin 2) (Fin 2) κ.K) *
      (κ.α l : Matrix (Fin 2) (Fin 2) κ.K) = 1 :=
    CFSG.LinearAlgebra.mul_self_eq_one_of_mulVec_eq_self
      (κ.α l : Matrix (Fin 2) (Fin 2) κ.K) (κ.α l).det_coe hvne hfix
  have hker : l ^ 2 ∈ κ.α.ker := by
    rw [MonoidHom.mem_ker, map_pow]
    apply Subtype.ext
    simpa [sq] using hsq
  have hb2sub : l ^ 2 ∈ (c.L ⊓ Subgroup.centralizer (c.V : Set G)).subgroupOf c.L := by
    rw [← hκker]
    exact hker
  have hb2mem := Subgroup.mem_subgroupOf.mp hb2sub
  exact Subgroup.mem_inf.mpr ⟨hb2mem.1, hb2mem.2⟩

theorem B0_inf_centralizer_Z_eq_bot (D : Data G) (Ch : Choice2011 G)
    (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch) :
    c.B0 ⊓ Subgroup.centralizer (D.Z : Set G) = ⊥ := by
  classical
  rw [Subgroup.eq_bot_iff_forall]
  intro b hb
  obtain ⟨hbB, hbZ⟩ := Subgroup.mem_inf.mp hb
  have hbL : b ∈ c.L := c.hB0.1.trans c.hL0L hbB
  have hb2 : b ^ 2 ∈ c.L ⊓ Subgroup.centralizer (c.V : Set G) :=
    sq_mem_inf_centralizer_V_of_mem_centralizer_Z D Ch h4 h23 h1930 c hbL hbZ
  let K : Subgroup G := (c.L ⊔ D.T) ⊓ Subgroup.centralizer (c.V : Set G)
  have hb2K : b ^ 2 ∈ K :=
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_left hb2.1, hb2.2⟩
  have hKp : IsPGroup 2 K :=
    Ctx23L.isPGroup_sup_inf_centralizer_V D Ch h4 h23 h1930 c
  have hodd : Odd (orderOf b) := uc22p21d_odd_orderOf_of_mem_calB1 c.hB0 hbB
  have hbK : b ∈ K := by
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime (x := b) (n := 2)
      (Nat.coprime_two_left.mpr hodd)
    rw [← hm]
    exact pow_mem hb2K m
  exact CFSG.Quasithin.eq_one_of_odd_orderOf_of_mem hKp hbK hodd

theorem not_mem_centralizer_Z_of_mem_B0 (D : Data G) (Ch : Choice2011 G)
    (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch)
    {b : G} (hb : b ∈ c.B0) (hb1 : b ≠ 1) :
    b ∉ Subgroup.centralizer (D.Z : Set G) := by
  intro hbZ
  have hmem : b ∈ c.B0 ⊓ Subgroup.centralizer (D.Z : Set G) :=
    Subgroup.mem_inf.mpr ⟨hb, hbZ⟩
  rw [B0_inf_centralizer_Z_eq_bot D Ch h4 h23 h1930 c] at hmem
  exact hb1 (Subgroup.mem_bot.mp hmem)

end Ctx23L

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
