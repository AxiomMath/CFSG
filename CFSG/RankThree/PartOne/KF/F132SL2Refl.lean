module

public import CFSG.RankThree.PartOne.KF.F132Core
public import CFSG.RankThree.PartOne.KF.F132LayerData
public import CFSG.RankThree.PartOne.KF.F132Sl2
public import CFSG.RankThree.PartOne.KLAY.SL2

public section

namespace CFSG.RankThree.PartOne.KF132

open CFSG CFSG.LocalCores CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU
  CFSG.RankThree.PartOne.KLAY CFSG.LieType.Chevalley CFSG.Assembly.LowTwoRank

theorem reflection_of_cover_sl2 {G : Type} [Group G] [Finite G] {p : ℕ} {A L E : Subgroup G}
    {c : G} {P M : Type} [Group P] [Group M] [Finite M] [Finite P]
    (h : Sec12Hyp G p A c L E) (hEA : E = A) (hcL : c ∉ L)
    (ε : ↥L →* P) (q : M →* P) (hε : IsCentralPQuot p ε) (hq : IsCentralPQuot p q)
    (hεinj : Function.Injective ε) (hqinj : Function.Injective q)
    {x : G} (hxA : x ∈ A) (hxL : x ∈ L) (hb1 : x ≠ 1) {m : M} (hmp : m ^ p = 1)
    (hbb : ε ⟨x, hxL⟩ = q m) {T₀ : Subgroup M} (hT₀ : ∀ t ∈ T₀, t ^ p = 1)
    (hAT : ((A ⊓ L).subgroupOf L).map ε = T₀.map q)
    {k : Type} [Field k] [Finite k] [CharP k 2] {g : ℕ} (hkg : Nat.card k = 2 ^ g) (hg : 2 ≤ g)
    {ι : SL2 k →* M} (hι : Function.Injective ι)
    (hKM : inSubgroup perfectResidual (Subgroup.centralizer ({m} : Set M)) = ι.range)
    (hTK : Nat.card ↥(T₀ ⊓ ι.range) = p) :
    ∃ t : MulAut E, t ∈ torusImage E L ∧ IsAutReflection p E t ∧
      (∀ hxE : x ∈ E, ((t ⟨x, hxE⟩ : E) : G) = x) ∧ KFAt p E g t ∧ kZero p E t ≤ L ∧
      ((kZero p E t).subgroupOf L).map ε = ι.range.map q := by
  have hp := h.prime
  have hk4 : 4 ≤ Nat.card k := by
    rw [hkg]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg
  have hqSL := CFSG.RankThree.CALinearPlane.isQuasisimple_SL_of_two_le (k := k) (m := 2) le_rfl hk4
  have hKq : IsQuasisimple ↥(inSubgroup perfectResidual (Subgroup.centralizer ({m} : Set M))) := by
    rw [hKM]
    exact isQuasisimple_of_mulEquiv (MonoidHom.ofInjective hι) hqSL
  have hc1 : Nat.card (Subgroup.center ↥ι.range) = 1 := by
    rw [← card_center_mulEquiv (MonoidHom.ofInjective hι)]
    exact KFU.card_center_SL_two
  have := h.A_elem
  have hbp : x ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian (p := p) (A := A) x hxA
  obtain ⟨K₀, hK₀eq, hqs, hz', hAK, ⟨e⟩, hiso⟩ := layerData_of_cover hp h.A_elem ε q hε hq hxA hxL
    hmp hbb hT₀ hAT hKq (by rw [hKM, hc1]; exact hp.not_dvd_one) (by rw [hKM]; exact hTK)
  obtain ⟨eKD⟩ := hiso hεinj hqinj
  have hZ : Subgroup.center ↥K₀ = ⊥ := by
    apply Subgroup.eq_bot_of_card_eq
    rw [card_center_mulEquiv eKD, hKM, hc1]
  have hmodel : StatedClassicalModel (↥K₀ ⧸ Subgroup.center ↥K₀) .PSL 2 2 g :=
    statedModel_psl_two_of_layer hkg hg hι hKM e
  subst hK₀eq
  have hbE : x ∈ E := hEA ▸ hxA
  have hAK' : Nat.card ↥(E ⊓ kLayer L x) = p := by rw [hEA]; exact hAK
  have hE3 : Nat.card E = p ^ 3 := by rw [hEA]; exact h.A_card
  obtain ⟨t, htL, hr, hfix, -, hKF, hKz⟩ := exists_reflection_of_layer h hE3 h.L_le_centralizer hcL
    hbE hxL hb1 hAK' hmodel hZ
  refine ⟨t, htL, hr, fun _ => hfix, hKF, ?_, ?_⟩
  · rw [hKz]
    exact (Subgroup.map_subtype_le _ : kLayer L x ≤ L ⊓ Subgroup.centralizer ({x} : Set G)).trans
      inf_le_left
  · rw [hKz, map_kLayer_eq_of_cover ε q hε hq hxL hbp hmp hbb hKq, hKM]

end CFSG.RankThree.PartOne.KF132
