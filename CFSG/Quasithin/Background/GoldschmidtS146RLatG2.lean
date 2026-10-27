module

public import CFSG.Quasithin.Background.GoldschmidtS146RLatGen
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListG2
public import CFSG.Quasithin.SteinbergBSSolvableOrdinaryBorel

public section

namespace CFSG.Quasithin.GoldS146R

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.QuasithinUnique.Setup.X6 CFSG.Quasithin.SteinbergBS


theorem latShape_adjointGroup_G2 {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) :
    LatShape ↥(adjointGroup Tag.G2 K)
      ((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K)) := by
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hUC : posUnipotent Tag.G2 K ≤ adjointGroup Tag.G2 K := posUnipotent_le_adjointGroup
  have hsolv : ∀ Y : Subgroup ↥(adjointGroup Tag.G2 K),
      (posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K) ≤ Y → Group.IsSolvable ↥Y →
      Y ≤ Subgroup.normalizer
        (((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K) :
          Subgroup ↥(adjointGroup Tag.G2 K)) : Set ↥(adjointGroup Tag.G2 K)) := by
    intro Y hUY hY
    have hMC : Y.map (adjointGroup Tag.G2 K).subtype ≤ adjointGroup Tag.G2 K := by
      rintro _ ⟨y, -, rfl⟩
      exact y.2
    have hUM : posUnipotent Tag.G2 K ≤ Y.map (adjointGroup Tag.G2 K).subtype := by
      intro u hu
      exact ⟨⟨u, hUC hu⟩, hUY (by rwa [Subgroup.mem_subgroupOf]), rfl⟩
    have hMs : Group.IsSolvable ↥(Y.map (adjointGroup Tag.G2 K).subtype) :=
      Group.isSolvable_of_surjective
        (f := ((adjointGroup Tag.G2 K).subtype.subgroupMap Y))
        (MonoidHom.subgroupMap_surjective _ Y)
    have hB := solvable_ordinary_posUnipotent_overgroups_le_borelGroup Tag.G2 K hK4 hMC hUM hMs
    intro y hy
    have hyB : (y : ModGL Tag.G2 K) ∈ borelGroup Tag.G2 K := hB ⟨y, hy, rfl⟩
    have hyN : (y : ModGL Tag.G2 K) ∈
        Subgroup.normalizer (posUnipotent Tag.G2 K : Set (ModGL Tag.G2 K)) := by
      rw [← (borel_self_normalizers Tag.G2 K).1] at hyB
      exact hyB.2
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have key := Subgroup.mem_normalizer_iff.mp hyN (h : ModGL Tag.G2 K)
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact key
  choose g hg hker using fun j : Fin 2 =>
    CFSG.QuasithinUnique.Vol2Native.A312L.exists_levi_hom_adjoint (τ := Tag.G2) (K := K) hK hn
      (g2Index j)
  exact latShape_of_rank_two G2_residualOvergroupsAt hsolv hn hK
    g hg hker

theorem latShape_of_isG2 {X : Type} [Group X] [Finite X] {n : ℕ} (hn : 2 ≤ n)
    (hX : IsG2 2 n X) {U : Subgroup X} (hU : IsSylowTwoOf U ⊤) : LatShape X U := by
  obtain ⟨-, K, hF, hFin, hcp, hK, ⟨e⟩⟩ :=
    exists_mulEquiv_G2_model hX
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  have hU₀ : IsSylowTwoOf ((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K)) ⊤ :=
    isSylowTwoOf_subgroupOf_top (isSylowTwoOf_iff_isSylowOf.2
      (unique_Chevalley_positive_Sylow (τ := Tag.G2) (K := K) 2).1)
  exact LatShape.of_equiv_sylow e.symm hU₀ (latShape_adjointGroup_G2 hn hK) hU

end CFSG.Quasithin.GoldS146R
