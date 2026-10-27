module

public import CFSG.RankThree.PartOne.KF.LayerTransfer
public import CFSG.RankThree.PartOne.KF.R7Levi
public import CFSG.RankThree.PartOne.KF.LayerFrame

public section

namespace CFSG.RankThree.PartOne.KF132

open Matrix CFSG CFSG.LocalCores CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU
  CFSG.Assembly.LowTwoRank

theorem map_kLayer_eq_of_cover {G : Type} [Group G] [Finite G] {p : ℕ} {L : Subgroup G}
    {P M : Type} [Group P] [Group M] [Finite M] [Finite P] (ε : ↥L →* P) (q : M →* P)
    (hε : IsCentralPQuot p ε) (hq : IsCentralPQuot p q) {b : G} (hbL : b ∈ L) (hbp : b ^ p = 1)
    {m : M} (hmp : m ^ p = 1) (hbb : ε ⟨b, hbL⟩ = q m)
    (hKq : IsQuasisimple ↥(inSubgroup perfectResidual (Subgroup.centralizer ({m} : Set M)))) :
    ((kLayer L b).subgroupOf L).map ε =
      (inSubgroup perfectResidual (Subgroup.centralizer ({m} : Set M))).map q := by
  have hb'p : (⟨b, hbL⟩ : ↥L) ^ p = 1 := Subtype.ext (by simpa using hbp)
  have hKEq := isQuasisimple_perfectResidual_centralizer hε hq hb'p hmp hbb hKq
  have hmap := map_perfectResidual_centralizer hε hq hb'p hmp hbb
  obtain ⟨hkL, -⟩ := kLayer_eq_map_of_isQuasisimple hbL hKEq
  rw [hkL, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective L.subtype_injective]
  exact hmap

theorem layerCore_of_sl2_cover {G : Type} [Group G] [Finite G] {p : ℕ} {A L : Subgroup G} {c : G}
    {P M : Type} [Group P] [Group M] [Finite M] [Finite P]
    (hp : p.Prime) (hp2 : p ≠ 2) (hAp : IsPGroup p ↥A) (hAel : IsElementaryAbelian p A)
    (hLc : L ≤ Subgroup.centralizer ({c} : Set G)) (hA : A ≤ Subgroup.zpowers c ⊔ (A ⊓ L))
    (ε : ↥L →* P) (q : M →* P) (hε : IsCentralPQuot p ε) (hq : IsCentralPQuot p q)
    {b : G} (hbA : b ∈ A) (hbL : b ∈ L) (hb1 : b ≠ 1) {m : M} (hmp : m ^ p = 1)
    (hbb : ε ⟨b, hbL⟩ = q m) {T₀ U : Subgroup M} (hT₀ : ∀ t ∈ T₀, t ^ p = 1)
    (hAT : ((A ⊓ L).subgroupOf L).map ε = T₀.map q)
    {k : Type} [Field k] [Finite k] [CharP k 2] {g : ℕ} (hkg : Nat.card k = 2 ^ g) (hg : 2 ≤ g)
    (ι : SpecialLinearGroup (Fin 2) k →* M) (hι : Function.Injective ι)
    (hKM : inSubgroup perfectResidual (Subgroup.centralizer ({m} : Set M)) = ι.range)
    (hTK : Nat.card ↥(T₀ ⊓ ι.range) = p) (hU : U ≤ ι.range) (hU2 : IsPGroup 2 ↥U)
    (hTU : T₀ ≤ Subgroup.normalizer (U : Set M)) (hnc : ∃ u ∈ U, ∃ t ∈ T₀, u * t ≠ t * u) :
    ∃ K : Subgroup G, LayerCore p A L b K ∧
      StatedClassicalModel (↥K ⧸ Subgroup.center ↥K) .PSL 2 2 g ∧
      ((kLayer L b).subgroupOf L).map ε = ι.range.map q := by
  have hk4 : 4 ≤ Nat.card k := by
    rw [hkg]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg
  have h4g : 4 ≤ 2 ^ g := hkg ▸ hk4
  have hqSL := CFSG.RankThree.CALinearPlane.isQuasisimple_SL_of_two_le (k := k) (m := 2) le_rfl hk4
  have hKq : IsQuasisimple ↥(inSubgroup perfectResidual (Subgroup.centralizer ({m} : Set M))) := by
    rw [hKM]
    exact isQuasisimple_of_mulEquiv (MonoidHom.ofInjective hι) hqSL
  have hc1 : Nat.card (Subgroup.center ↥ι.range) = 1 := by
    rw [← card_center_mulEquiv (MonoidHom.ofInjective hι)]
    exact card_center_SL_two
  have hbp : b ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian (p := p) (A := A) b hbA
  obtain ⟨KL, hKLeq, hKLq, hKLz, hAK, htwo, ⟨eqv⟩⟩ := exists_layerCore_of_cover hp hp2 hAp hAel hLc
    hA ε q hε hq hbA hbL hmp hbb hT₀ hAT hKq
    (by rw [hKM, hc1]; exact hp.not_dvd_one) (by rw [hKM]; exact hTK) (by rw [hKM]; exact hU) hU2
    hTU hnc
  refine ⟨KL, ⟨⟨hbA, hbL, hb1⟩, hKLeq, hKLq, hKLz, hAK, htwo⟩, ?_, ?_⟩
  · refine ⟨⟨Nat.prime_two, by omega, by norm_num, ?_, ?_⟩, k, inferInstance, inferInstance, hkg, ?_⟩
    · intro h2
      have := congrArg Prod.snd h2
      simp only at this
      omega
    · intro h2
      have := congrArg Prod.snd h2
      simp only at this
      omega
    · obtain ⟨e₃⟩ := exists_centerQuotient_mulEquiv (MulEquiv.subgroupCongr hKM)
      obtain ⟨e₄⟩ := exists_centerQuotient_mulEquiv (MonoidHom.ofInjective hι).symm
      exact ⟨eqv.trans (e₃.trans (e₄.trans (projectiveSpecialLinearGroupEquivStatedProj 2 k)))⟩
  · rw [map_kLayer_eq_of_cover ε q hε hq hbL hbp hmp hbb hKq, hKM]

end CFSG.RankThree.PartOne.KF132
