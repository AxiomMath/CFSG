module

public import CFSG.RankThree.PartTwo.Sec19.Step1914Split
public import CFSG.RankThree.PartTwo.Sec13.Steps
import CFSG.RankThree.PartTwo.Sec19.Step1914MoreProofL34
import CFSG.RankThree.PartTwo.Sec19.Step1914MoreProofM12

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)

@[expose] def Step1914MoreSL34 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E M : Subgroup G),
    Ctx1912 G A c L E M → ¬ L ≤ M →
    Nonempty (L ⧸ CFSG.pCore 2 L ≃* projSL 3 (GaloisField 2 2)) →
    E = Subgroup.zpowers c ⊔ (E ⊓ L) → Subgroup.zpowers c ⊓ (E ⊓ L) = ⊥ →
      ∃ s ∈ Subgroup.normalizer (E : Set G),
        s ∉ Subgroup.normalizer (Subgroup.zpowers c : Set G)

@[expose] def Step1914MoreSM12 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E M : Subgroup G),
    Ctx1912 G A c L E M → ¬ L ≤ M →
    Nonempty (L ⧸ CFSG.pCore 2 L ≃* CFSG.Blueprint.NativeSporadic.M12) →
      ∃ s ∈ Subgroup.normalizer (E : Set G),
        s ∉ Subgroup.normalizer (Subgroup.zpowers c : Set G)

open Step1914MoreProof in
theorem step1914More_of
    (htri : Step1914Tri) (h131 : Sec13.Item131) (hSL : Step1914MoreSL34)
    (hSM : Step1914MoreSM12) : Step1914More := by
  intro G _ _ A c L E M hctx hLM
  rcases htri G A c L E M hctx with hle | ⟨hφ, hEeq, hdisj⟩ | hM12
  · exact absurd hle hLM
  · obtain ⟨X₁, X₂, M₁, M₂, hcore, hy⟩ := exists_coreData_of_l34 hctx hφ hEeq hdisj
    obtain ⟨s, hsE, hsc⟩ := hSL G A c L E M hctx hLM hφ hEeq hdisj
    exact isExtOf_of_coreData hcore hy fun hle => hsc (hle hsE)
  · obtain ⟨X₁, X₂, M₁, M₂, hcore, hy⟩ := exists_coreData_of_m12 htri h131 hctx hLM hM12
    obtain ⟨s, hsE, hsc⟩ := hSM G A c L E M hctx hLM hM12
    exact isExtOf_of_coreData hcore hy fun hle => hsc (hle hsE)

end CFSG.RankThree.PartTwo.Sec19
