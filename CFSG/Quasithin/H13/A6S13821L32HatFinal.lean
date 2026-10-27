module

public import CFSG.Quasithin.H13.A6S13821L32HatAssembly
public import CFSG.Quasithin.H13.A6S13821L32HatB

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7

namespace L32Hat

theorem case13821L32Hat_of_c
    (h16 : Lem13816) (h36c : QuasithinUnique.Vol2Native.A36CoreForSQTKCat) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h139 : Stmt13_3_9) (h1334 : Stmt13_3_4) (h13 : Lem13813)
    (h13314 : Stmt13_3_14) (h13315 : Stmt13_3_15) (h1356two : Input1356Two)
    (hC : ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V),
      S.Hyp138 → IsHatA6 L → ∀ H ∈ S.Hz, ∀ K ∈ cComp H,
        IsPSL 3 2 1 (↥K ⧸ CFSG.pCore 2 ↥K) → H ≤ Subgroup.normalizer (K : Set G) →
        H = K ⊔ (S.L1 ⊔ T) → ¬ S.L1 ≤ K →
        4 ≤ mIdx (conjClosure S.V3 H)
          (centralizerMod (fsuV1 T V) (conjClosure S.V3 H) (pCoreOf 2 (S.L1 ⊔ T)))) :
    Case13821L32Hat :=
  case13821L32Hat_of_leaves h16 h36c h37 h38 h139 h1334 h13 h13314 h13315 h1356two
    (fun G _ _ T L V S hS hhat H hH K hK hP hKn hHK hL1K =>
      ⟨L32HatStep.oTwoRes_solvRad_ne_bot_hat h139 h37 h38 h1334 hS hhat hH hK hKn hP hHK,
        L32HatStep.relIndex_le_four h139 h37 h38 h1334 hS hhat hH hK hKn hP hHK,
        hC G T L V S hS hhat H hH K hK hP hKn hHK hL1K⟩)

end L32Hat

end CFSG.Quasithin.H13.A6
