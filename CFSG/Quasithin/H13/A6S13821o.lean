module

public import CFSG.Quasithin.H13.A6S13821n
public import CFSG.Quasithin.H13.A6S13821e

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7

@[expose] def Case13821L32Hat : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V), S.Hyp138 →
    IsHatA6 L → ∀ H ∈ S.Hz, ∀ K ∈ cComp H, IsPSL 3 2 1 (↥K ⧸ CFSG.pCore 2 ↥K) → S.L1 ≤ K

theorem case13821L32_of (hHat : Case13821L32Hat)
    (h16 : Lem13816) (h36c : QuasithinUnique.Vol2Native.A36CoreForSQTKCat) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h139 : Stmt13_3_9) (h1334 : Stmt13_3_4) (h13 : Lem13813)
    (hA21 : AsA21SQTKSection) (hD310 : D310) (hD391 : D391) (hI4 : Insp4) : Case13821L32 := by
  intro G _ _ T L V S hS H hH K hK hP
  by_cases hhat : IsHatA6 L
  · exact hHat G T L V S hS hhat H hH K hK hP
  · obtain ⟨-, hH₀, -, hKc, hKN₀, hF⟩ :=
      S.reduce13821 h16 h36c h37 h38 h139 h1334 h13 hS hH hK
    have hP' : IsPSL 3 2 1 (L32A.cStar K) := IsPSL.of_mulEquiv (L32A.C.cStarEquiv K).symm hP
    exact S.L1_le_of_l32_of_not_hat hA21 hD310 hD391 hI4 h13 hS hH₀ hF hKN₀ rfl hP' hhat

end CFSG.Quasithin.H13.A6
