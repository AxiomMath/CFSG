module

public import CFSG.Quasithin.Vol2.Ch9Sec3FactsF112PfA
public import CFSG.Quasithin.H13.NQCatG2RadModel
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModG2Perf

public section

namespace CFSG.Quasithin.H13.Ch9.F112Pf

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.QuasithinUnique.Setup.X6
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2

section G2

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem genComm_g2
    {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (i : Fin Tag.G2.rank) : GenComm (perfectCore (parabolicSubgroup Tag.G2 K {i})) := by
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hgen : parabolicRadical Tag.G2 K {i} ≤
      ⁅parabolicRadical Tag.G2 K {i}, perfectCore (parabolicSubgroup Tag.G2 K {i})⁆ := by
    fin_cases i
    · exact generated_zero hK4
    · exact generated_one hK4
  have heq := H13.NQCat.G2Rad.pCoreOf_perfectCore_eq (Sec53F.G2.radical_le_parabolic {i})
    (parabolicSubgroup_le_normalizer_parabolicRadical {i}) (pGroup_radical hK {i})
    ⟨hgen, levi_hom hK4 i⟩
  unfold GenComm
  rw [heq]
  exact hgen

theorem posUnipotent_le_perfectCore_g2
    (hK4 : 4 ≤ Nat.card K) (i : Fin Tag.G2.rank) :
    posUnipotent Tag.G2 K ≤ perfectCore (parabolicSubgroup Tag.G2 K {i}) := by
  fin_cases i
  · exact Sec53F.G2.posUnipotent_le_perfectCore_zero hK4
  · exact Sec53F.G2.posUnipotent_le_perfectCore_one hK4

theorem hasModelFacts_g2
    (f : ℕ) (hf : 2 ≤ f) : HasModelFacts (IsG2Over f) := by
  intro Y _ hY
  have hX : ChevalleyExceptionalModel Y .G2 2 f := by
    rcases hY with ⟨h, -⟩ | ⟨-, hL⟩
    · omega
    · rcases hL with ⟨h, -⟩ | ⟨-, -, h⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
      · exact absurd h (by decide)
      · exact h
      · exact absurd h (by decide)
      · exact absurd h (by decide)
  have hfin : Finite Y := by
    obtain ⟨-, K, _, _, _, -, ⟨e⟩⟩ := exists_mulEquiv_G2_model hX
    have : Finite (ModGL Tag.G2 K) := finite_modGL
    exact Finite.of_equiv _ e.symm.toEquiv
  refine ⟨hfin, fun T hT => ?_⟩
  obtain ⟨K, _, _, _, φ, hK, hφ, hres, -⟩ := even_rank_two_residual_G2 hX hT
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  refine ⟨_, hres, fun j => ?_⟩
  have hPC : parabolicSubgroup Tag.G2 K {g2Index j} ≤ adjointGroup Tag.G2 K :=
    parabolicSubgroup_le_adjointGroup Tag.G2 K {g2Index j}
  have hT' : T = ((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K)).map
      φ.symm.toMonoidHom := by
    rw [← hφ, Subgroup.map_map]
    have e : φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id Y := by
      ext
      simp
    rw [e, Subgroup.map_id]
  constructor
  · rw [hT', ← map_perfectCore]
    apply Subgroup.map_mono
    intro x hx
    rw [Sec53F.G2.mem_perfectCore_subgroupOf hPC]
    exact posUnipotent_le_perfectCore_g2 hK4 _ hx
  · rw [← map_perfectCore, genComm_map_iff φ.symm.injective,
      ← genComm_map_iff (adjointGroup Tag.G2 K).subtype_injective, map_perfectCore,
      Subgroup.map_subgroupOf_eq_of_le hPC]
    exact genComm_g2 hK hf _

end G2

end CFSG.Quasithin.H13.Ch9.F112Pf
