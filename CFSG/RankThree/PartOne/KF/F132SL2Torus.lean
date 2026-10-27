module

public import CFSG.RankThree.PartOne.KF.F132Sl2
public import CFSG.RankThree.PartOne.KLAY.Core

public section

namespace CFSG.RankThree.PartOne.KF132

open CFSG CFSG.LocalCores CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU
  CFSG.RankThree.PartOne.KLAY CFSG.LieType.Chevalley CFSG.Assembly.LowTwoRank

theorem layerCore_of_SL2Torus {G : Type} [Group G] [Finite G] {p : ℕ} {A L : Subgroup G} {c : G}
    {P M : Type} [Group P] [Group M] [Finite M] [Finite P]
    (hp : p.Prime) (hp2 : p ≠ 2) (hAp : IsPGroup p ↥A) (hAel : IsElementaryAbelian p A)
    (hLc : L ≤ Subgroup.centralizer ({c} : Set G)) (hA : A ≤ Subgroup.zpowers c ⊔ (A ⊓ L))
    (ε : ↥L →* P) (q : M →* P) (hε : IsCentralPQuot p ε) (hq : IsCentralPQuot p q)
    {b : G} (hbA : b ∈ A) (hbL : b ∈ L) (hb1 : b ≠ 1) {m : M} (hmp : m ^ p = 1)
    (hbb : ε ⟨b, hbL⟩ = q m) {T₀ : Subgroup M}
    (hAT : ((A ⊓ L).subgroupOf L).map ε = T₀.map q)
    {k : Type} [Field k] [Finite k] [CharP k 2] {g : ℕ} (hkg : Nat.card k = 2 ^ g) (hg : 2 ≤ g)
    (hζk : ∃ ζ : kˣ, IsPrimitiveRoot ζ p) {φ : SL2 k →* M} (hSL : SL2Torus p φ T₀)
    (hD : layerD m = φ.range) :
    ∃ K : Subgroup G, LayerCore p A L b K ∧
      StatedClassicalModel (↥K ⧸ Subgroup.center ↥K) .PSL 2 2 g := by
  obtain ⟨U, hU, hU2, hTU, hnc⟩ := hSL.exists_upper
  obtain ⟨K, hd, hmod, -⟩ := layerCore_of_sl2_cover hp hp2 hAp hAel hLc hA ε q hε hq hbA hbL hb1
    hmp hbb hSL.exp hAT hkg hg φ hSL.inj hD (hSL.card_inf hp.pos hζk) hU hU2 hTU hnc
  exact ⟨K, hd, hmod⟩

end CFSG.RankThree.PartOne.KF132
