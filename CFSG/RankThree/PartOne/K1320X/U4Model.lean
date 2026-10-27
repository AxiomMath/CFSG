module

public import CFSG.RankThree.PartOne.K1320X.U4Emb
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.RankThree.PartOne.K1320X

open Matrix CFSG CFSG.LocalCores CFSG.LieType.Universal.Unitary CFSG.Assembly.LowTwoRank
  CFSG.LieType.BorelTits CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU

variable {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}

theorem four_pair_ne (q : ℕ) : ((4 : ℕ), q) ≠ (3, 2) := by
  intro h
  have := congrArg Prod.fst h
  simp at this

theorem isQuasisimple_SU_four (hK : Nat.card K = (2 ^ f) ^ 2) :
    IsQuasisimple ↥(SU (unitaryInvolution K 2 f) 4) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact isQuasisimple_SU hK (by norm_num) (four_pair_ne _)

theorem statedModel_SU_four (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 2 ≤ f) :
    StatedClassicalModel (↥(SU (unitaryInvolution K 2 f) 4) ⧸
      Subgroup.center ↥(SU (unitaryInvolution K 2 f) 4)) .PSU 4 2 f := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact statedClassicalModel_center_quotient ⟨Nat.prime_two, by omega, by norm_num,
    four_pair_ne _⟩ hK

theorem statedModel_psu_four_of_layer (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 2 ≤ f) {X Y : Type}
    [Group X] [Group Y] {D : Subgroup Y}
    {ι : ↥(SU (unitaryInvolution K 2 f) 4) →* Y} (hι : Function.Injective ι) (hD : D = ι.range)
    (e : X ⧸ Subgroup.center X ≃* ↥D ⧸ Subgroup.center ↥D) :
    StatedClassicalModel (X ⧸ Subgroup.center X) .PSU 4 2 f := by
  obtain ⟨e₃⟩ := exists_centerQuotient_mulEquiv (MulEquiv.subgroupCongr hD)
  obtain ⟨e₄⟩ := exists_centerQuotient_mulEquiv (MonoidHom.ofInjective hι).symm
  exact Equivariance.statedClassicalModel_of_mulEquiv (e.trans (e₃.trans e₄)).symm
    (statedModel_SU_four hK hf)

theorem su4_block_facts (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 2 ≤ f) {P : Type} [Group P] [Finite P]
    {p : ℕ} {q : ↥(SU (unitaryInvolution K 2 f) 5) →* P} (hq : IsCentralPQuot p q) :
    Group.IsPerfect ↥((su4Emb (unitaryInvolution K 2 f)).range.map q) ∧
      IsQuasisimple ↥((su4Emb (unitaryInvolution K 2 f)).range.map q) ∧
      StatedClassicalModel (↥((su4Emb (unitaryInvolution K 2 f)).range.map q) ⧸
        Subgroup.center ↥((su4Emb (unitaryInvolution K 2 f)).range.map q)) .PSU 4 2 f := by
  set B := (su4Emb (unitaryInvolution K 2 f)).range with hB
  have hBqs : IsQuasisimple ↥B :=
    LocalCores.isQuasisimple_of_mulEquiv
      (MonoidHom.ofInjective (su4Emb_injective (unitaryInvolution K 2 f)))
      (isQuasisimple_SU_four hK)
  have hBnot : ¬ B ≤ q.ker := fun hle =>
    not_le_center_of_isQuasisimple' hBqs (fun x hx => hq.central (hle hx))
  have hQqs : IsQuasisimple ↥(B.map q) := LocalCores.isQuasisimple_map hBqs q hBnot
  refine ⟨hQqs.1, hQqs, ?_⟩
  obtain ⟨e₁⟩ := centerQuotientEquiv_of_surjective hBqs.1 (q.subgroupMap B)
    (q.subgroupMap_surjective B) (ker_subgroupMap_le_center hq B)
  exact statedModel_psu_four_of_layer hK hf (su4Emb_injective (unitaryInvolution K 2 f))
    (hB.symm ▸ rfl) e₁.symm

end CFSG.RankThree.PartOne.K1320X
