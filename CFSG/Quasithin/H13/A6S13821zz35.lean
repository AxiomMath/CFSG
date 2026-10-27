module

public import CFSG.Quasithin.H13.A6S13821zz34
public import CFSG.Quasithin.H13.A6S13821zz25
public import CFSG.Quasithin.H13.A6S13821zz30
public import CFSG.Quasithin.H13.A6S13821zz32
public import CFSG.Quasithin.H13.A6S13821zz33

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem false_of_sl34_13820b
    (h36c : QuasithinUnique.Vol2Native.A36CoreForSQTKCat) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h139 : Stmt13_3_9) (h1334 : Stmt13_3_4) (h13 : Lem13813)
    (h1337 : Stmt13_3_7) (hD310 : D310) (hD391 : D391) (hI4 : Insp4) (hA21 : AsA21SQTKSection)
    (hG2 : FactG2Cayley) (h42 : AsB42) (h45 : AsB45) {H K : Subgroup G} {n : ℕ}
    (hC : S.Ctx13820 H K n) (hb : S.Case13820bHyp H K) (hL1K : S.L1 ≤ K)
    (hL34 : IsPSL 3 2 2 (↥(S.KSt H K) ⧸ Subgroup.center ↥(S.KSt H K)))
    (hZ : Nat.card (Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) = 3) : False := by
  obtain ⟨hF, I, -, hIU, hcase, hkerK⟩ :=
    S.exists_module_sl34_13820b h36c h37 h38 h139 h1334 h13 hD310 hD391 hI4 hA21 hG2 h42 h45 hC
      hL1K hL34 hZ
  have hFe := factElem hF hIU
  rcases hcase with ⟨-, hnat⟩ | ⟨t, htT, hnat, hinf, hsup, hniso⟩
  · exact S.false_of_natural_sl34_13820b h1334 h13 h1337 hC hb hL1K hF hIU hkerK hnat
  · obtain ⟨hS, hH, -, hKn, hHK, -, -⟩ := hC
    have hHKT : H = K ⊔ T := by
      rw [hHK, ← sup_assoc, sup_eq_left.mpr hL1K]
    exact S.false_of_pair_sl34_13820b hS hH hKn hHKT hF hIU hkerK t htT hnat hinf hsup hniso

end Setting4

theorem case13820bSL34U38_of
    (h36c : QuasithinUnique.Vol2Native.A36CoreForSQTKCat) (h36 : A36ForSQTK) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h139 : Stmt13_3_9) (h1334 : Stmt13_3_4) (h13 : Lem13813)
    (h1337 : Stmt13_3_7) (hD310 : D310) (hD391 : D391) (hI4 : Insp4) (hA21 : AsA21SQTKSection)
    (hG2 : FactG2Cayley) (h42 : AsB42) (h45 : AsB45) : Case13820bSL34U38 := by
  intro G _ _ T L V S H K n hC hb h24
  obtain ⟨hL1K, -, -⟩ :=
    S.claim_13820b h36c h36 h37 h38 h139 h1334 h13 hD310 hA21 hG2 h42 h45 hC hb h24
  obtain ⟨hS, hH, hK, hKN, -, -, -⟩ := id hC
  have hq := S.isQuasisimple_modO2 h36c h139 h1334 h13 hS hH hK
  obtain ⟨e₀⟩ := S.kst_equiv hS hH hK
  let e₁ : ((↥K ⧸ CFSG.pCore 2 ↥K) ⧸ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) ≃*
      (↥(S.KSt H K) ⧸ Subgroup.center ↥(S.KSt H K)) :=
    QuotientGroup.congr _ _ e₀ (Subgroup.map_center_eq e₀)
  rcases S.center_modO2_cases h36 hH hK hKN hq with hZ | hZ
  ·
    let e₂ : (↥K ⧸ CFSG.pCore 2 ↥K) ≃*
        ((↥K ⧸ CFSG.pCore 2 ↥K) ⧸ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) :=
      QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
    refine S.false_of_simple_13820b h36c h37 h38 h139 h1334 h13 hD310 hA21 hG2 h42 h45 hC ?_
    rcases hb.1 with h | h | h
    · exact absurd h h24
    · exact Or.inl (IsPSL.of_mulEquiv (e₂.trans e₁).symm h)
    · exact Or.inr (IsPSU.of_mulEquiv (e₂.trans e₁).symm h)
  · rcases hb.1 with h | h | h
    · exact h24 h
    · exact S.false_of_sl34_13820b h36c h37 h38 h139 h1334 h13 h1337 hD310 hD391 hI4 hA21 hG2
        h42 h45 hC hb hL1K h hZ
    · exact S.false_of_su38_13820b h36c h37 h38 h139 h1334 h13 hD310 hD391 hI4 hA21 h42 h45 hC
        hL1K h hZ

end CFSG.Quasithin.H13.A6
