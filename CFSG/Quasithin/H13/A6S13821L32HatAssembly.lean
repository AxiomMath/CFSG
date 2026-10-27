module

public import CFSG.Quasithin.H13.A6S13821L32HatDefs
public import CFSG.Quasithin.H13.A6S13821HatEnd
public import CFSG.Quasithin.H13.A6S13821HatMA
public import CFSG.Quasithin.H13.A6S13821o

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom

namespace L32Hat

theorem case13821L32Hat_of_leaves
    (h16 : Lem13816) (h36c : QuasithinUnique.Vol2Native.A36CoreForSQTKCat) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h139 : Stmt13_3_9) (h1334 : Stmt13_3_4) (h13 : Lem13813)
    (h13314 : Stmt13_3_14) (h13315 : Stmt13_3_15) (h1356two : Input1356Two)
    (hLeaves : ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V),
      S.Hyp138 → IsHatA6 L → ∀ H ∈ S.Hz, ∀ K ∈ cComp H,
        IsPSL 3 2 1 (↥K ⧸ CFSG.pCore 2 ↥K) → H ≤ Subgroup.normalizer (K : Set G) →
        H = K ⊔ (S.L1 ⊔ T) → ¬ S.L1 ≤ K → HatHyp S H) :
    Case13821L32Hat := by
  intro G _ _ T L V S hS hhat H hH K hK hP
  by_contra hL1K
  obtain ⟨hKn, hH₀, -, hKc, hKN₀, -⟩ :=
    S.reduce13821 h16 h36c h37 h38 h139 h1334 h13 hS hH hK
  obtain ⟨hA, hB, hC⟩ := hLeaves G T L V S hS hhat _ hH₀ K hKc hP hKN₀ rfl hL1K
  exact S.false_of_R_four h36c h139 h1334 h13 h13314 h13315 h1356two hS hH₀ hKc hKN₀ rfl
    (S.not_transv_R_of_solvRad h139 h1334 h13 hS hH₀ hA) hB hC

end L32Hat

end CFSG.Quasithin.H13.A6
