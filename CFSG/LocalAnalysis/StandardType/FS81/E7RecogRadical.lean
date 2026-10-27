module

public import CFSG.LocalAnalysis.StandardType.FS81.E7RecogPieces
public import CFSG.LocalAnalysis.StandardType.FS81.S79Radical
public import CFSG.LocalAnalysis.StandardType.FS81.L3TwoFixedPointFree
import CFSG.LocalAnalysis.StandardType.FS81.RootCentralizerO2
public import CFSG.LieType.BorelTits.Basic
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimeNormalizer

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.QuasithinUnique CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime

private theorem fs81_radicalOdd_T1_le {X : Type} [Group X] [Finite X]
    {Y P T T₀ T₁ : Subgroup X} {b₀ : X}
    (hT2 : IsPGroup 2 T) (hYNT : Y ≤ Subgroup.normalizer (T : Set X))
    (hTS : T ⊓ Subgroup.centralizer ({b₀} : Set X) ≤ Subgroup.centralizer (Y : Set X))
    (hb₀Y : b₀ ∈ Y) (hb₀3 : orderOf b₀ = 3) (hb₀P : b₀ ∈ P) (hPY : P ≤ Y)
    (hP : Nonempty (↥P ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))
    (hT₀ : T₀ = T ⊓ Subgroup.centralizer (Y : Set X))
    (hT₁ : T₁ = T ⊓ Subgroup.normalizer (T₀ : Set X)) :
    T₁ ≤ T₀ := by
  have hYc : Y ≤ Subgroup.centralizer (Subgroup.centralizer (Y : Set X) : Set X) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact (Subgroup.mem_centralizer_iff.mp hc y hy).symm
  have hYNT₀ : Y ≤ Subgroup.normalizer (T₀ : Set X) := by
    rw [hT₀]
    exact (le_inf hYNT (hYc.trans
      (Subgroup.centralizer_le_normalizer (Subgroup.centralizer (Y : Set X) : Set X)))).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := T)
        (K := Subgroup.centralizer (Y : Set X)))
  have hYNT₁ : Y ≤ Subgroup.normalizer (T₁ : Set X) := by
    rw [hT₁]
    exact (le_inf hYNT (hYNT₀.trans Subgroup.le_normalizer)).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := T)
        (K := Subgroup.normalizer (T₀ : Set X)))
  have hfpf : ∀ t' ∈ T₁, b₀ * t' * b₀⁻¹ * t'⁻¹ ∈ T₀ → t' ∈ T₀ :=
    fixedPointFree_quotient_of_inf_centralizer_le (S := Subgroup.centralizer (Y : Set X)) hTS
      (hYNT₀ hb₀Y) hb₀3 hT2 hT₀ hT₁
  have hT₁T₀ : T₀ ≤ T₁ := by
    rw [hT₁, hT₀]
    exact le_inf inf_le_left Subgroup.le_normalizer
  haveI : Group.IsNilpotent ↥T₁ :=
    IsPGroup.isNilpotent (hT2.to_le (by rw [hT₁]; exact inf_le_left))
  have hsol : IsSolvable ↥T₁ := IsNilpotent.to_isSolvable
  exact le_of_l3TwoFixedPointFree hT₁T₀ (by rw [hT₁]; exact inf_le_right)
    (hPY.trans hYNT₁) (hPY.trans hYNT₀) hP hb₀P hb₀3 hsol hfpf

private theorem fs81_radicalOdd_core {X : Type} [Group X] [Finite X]
    {Y R P : Subgroup X} {b₀ t : X}
    (hZ : Subgroup.centralizer (Y : Set X) ⊓ Y = ⊥)
    (hRY : R ≤ Subgroup.centralizer (Y : Set X))
    (hC : Subgroup.centralizer ({b₀} : Set X) =
      R ⊔ (Subgroup.centralizer ({b₀} : Set X) ⊓ Y))
    (hO2 : ∀ N : Subgroup X, IsPGroup 2 N →
      N ≤ Subgroup.centralizer ({b₀} : Set X) ⊓ Y →
      Subgroup.centralizer ({b₀} : Set X) ⊓ Y ≤ Subgroup.normalizer (N : Set X) → N = ⊥)
    (hb₀3 : orderOf b₀ = 3) (hb₀P : b₀ ∈ P) (hPY : P ≤ Y)
    (hP : Nonempty (↥P ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))
    (htR : t ∈ R) (ht2 : orderOf t = 2)
    (hchar : CharTwo (Subgroup.centralizer ({t} : Set X))) :
    pCoreOf 2 (Subgroup.centralizer ({t} : Set X)) =
      pCoreOf 2 (Subgroup.centralizer ({t} : Set X)) ⊓ Subgroup.centralizer (Y : Set X) := by
  classical
  let T : Subgroup X := pCoreOf 2 (Subgroup.centralizer ({t} : Set X))
  let T₀ : Subgroup X := T ⊓ Subgroup.centralizer (Y : Set X)
  let T₁ : Subgroup X := T ⊓ Subgroup.normalizer (T₀ : Set X)
  have hT2 : IsPGroup 2 T := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) _
  have hYt : Y ≤ Subgroup.centralizer ({t} : Set X) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp (hRY htR) y hy
  have hYNT : Y ≤ Subgroup.normalizer (T : Set X) :=
    hYt.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) _)
  have hinf : T ⊓ Subgroup.centralizer ({b₀} : Set X) ≤ R :=
    inf_centralizer_le_R hRY hZ hC hO2 T hT2 hYNT
  have hT₁le : T₁ ≤ T₀ :=
    fs81_radicalOdd_T1_le hT2 hYNT (hinf.trans hRY) (hPY hb₀P) hb₀3 hb₀P hPY hP rfl rfl
  have hT₀eqT : T₀ = T := by
    by_contra hne
    have hlt : T₀ < T := lt_of_le_of_ne inf_le_left hne
    have hgrowth : T₀ < T ⊓ Subgroup.normalizer (T₀ : Set X) :=
      pSubgroup_lt_normalizer_intersection 2 Nat.prime_two T₀ T hT2 hlt
    have hle : T ⊓ Subgroup.normalizer (T₀ : Set X) ≤ T₀ := hT₁le
    exact not_le_of_gt hgrowth hle
  exact hT₀eqT.symm

theorem fs81RadicalOdd_holds : FS81RadicalOdd := by
  intro X _ _ Y R P b₀ hZ hRY hC hO2 hb₀3 hb₀P hPY hP hind
  by_contra h2R
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥R) 2 h2R
  have htR : (t : X) ∈ R := t.2
  have ht2 : orderOf (t : X) = 2 := by rw [Subgroup.orderOf_coe]; exact ht
  have hchar := hind (t : X) htR ht2
  have hTeq : pCoreOf 2 (Subgroup.centralizer ({(t : X)} : Set X)) =
      pCoreOf 2 (Subgroup.centralizer ({(t : X)} : Set X)) ⊓
        Subgroup.centralizer (Y : Set X) :=
    fs81_radicalOdd_core hZ hRY hC hO2 hb₀3 hb₀P hPY hP htR ht2 hchar
  have hTleCY : pCoreOf 2 (Subgroup.centralizer ({(t : X)} : Set X)) ≤
      Subgroup.centralizer (Y : Set X) := by
    rw [hTeq]
    exact inf_le_right
  have hYCT : Y ≤ Subgroup.centralizer
      (pCoreOf 2 (Subgroup.centralizer ({(t : X)} : Set X)) : Set X) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact (Subgroup.mem_centralizer_iff.mp (hTleCY hc) y hy).symm
  have hYt : Y ≤ Subgroup.centralizer ({(t : X)} : Set X) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp (hRY htR) y hy
  have hYleT : Y ≤ pCoreOf 2 (Subgroup.centralizer ({(t : X)} : Set X)) :=
    (le_inf hYt hYCT).trans hchar
  have hY2 : IsPGroup 2 Y :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup
      (r := 2) (Subgroup.centralizer ({(t : X)} : Set X))).to_le hYleT
  have h3Y : 3 ∣ Nat.card Y := by
    rw [← hb₀3]
    exact Subgroup.orderOf_dvd_natCard Y (hPY hb₀P)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hY2
  rw [hk] at h3Y
  exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3Y) (by norm_num)

private theorem fs81_rootO2_centralizer_le_U {X : Type} [Group X] [Finite X]
    {Y R U T : Subgroup X} {b t₀ : X}
    (hZ : Subgroup.centralizer (Y : Set X) ⊓ Y = ⊥)
    (hRY : R ≤ Subgroup.centralizer (Y : Set X))
    (hCb : Subgroup.centralizer ({b} : Set X) =
      R ⊔ (Subgroup.centralizer ({b} : Set X) ⊓ Y))
    (hoddR : ¬ 2 ∣ Nat.card R) (hT2 : IsPGroup 2 T)
    (hTH : T ≤ Subgroup.centralizer ({t₀} : Set X))
    (hTN : Subgroup.centralizer ({t₀} : Set X) ≤ Subgroup.normalizer (T : Set X))
    (hUmax : ∀ N : Subgroup X, IsPGroup 2 N →
      N ≤ Subgroup.centralizer ({b} : Set X) ⊓ Subgroup.centralizer ({t₀} : Set X) ⊓ Y →
      Subgroup.centralizer ({b} : Set X) ⊓ Subgroup.centralizer ({t₀} : Set X) ⊓ Y ≤
        Subgroup.normalizer (N : Set X) → N ≤ U) :
    T ⊓ Subgroup.centralizer ({b} : Set X) ≤ U := by
  have hCTY : T ⊓ Subgroup.centralizer ({b} : Set X) ≤ Y :=
    inf_centralizer_le_Y hRY hZ hCb hoddR T hT2
  refine hUmax (T ⊓ Subgroup.centralizer ({b} : Set X)) (hT2.to_le inf_le_left) ?_ ?_
  · exact le_inf (le_inf inf_le_right (inf_le_left.trans hTH)) hCTY
  · refine (le_inf ?_ ?_).trans Subgroup.inf_normalizer_le_normalizer_inf
    · exact (inf_le_left.trans inf_le_right).trans hTN
    · exact (inf_le_left.trans inf_le_left).trans Subgroup.le_normalizer

private theorem fs81_rootO2_R_eq_bot {X : Type} [Group X]
    {Y R U T : Subgroup X} {t₀ : X}
    (hZ : Subgroup.centralizer (Y : Set X) ⊓ Y = ⊥)
    (hRY : R ≤ Subgroup.centralizer (Y : Set X))
    (hcharT : Subgroup.centralizer ({t₀} : Set X) ⊓
      Subgroup.centralizer (T : Set X) ≤ T)
    (hTU : T ≤ U) (hUY : U ≤ Y) (ht₀Y : t₀ ∈ Y) : R = ⊥ := by
  have hRH : R ≤ Subgroup.centralizer ({t₀} : Set X) :=
    hRY.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ht₀Y))
  have hRT : R ≤ Subgroup.centralizer (T : Set X) :=
    hRY.trans (Subgroup.centralizer_le (by intro x hx; exact hUY (hTU hx)))
  have hRY' : R ≤ Y := ((le_inf hRH hRT).trans hcharT).trans (hTU.trans hUY)
  refine le_bot_iff.mp ?_
  rw [← hZ]
  exact le_inf hRY hRY'

theorem fs81RootO2_holds : FS81RootO2 := by
  intro X _ _ Y R U L P b₀ b t₀ hZ hRY hC hoddR ht₀ ht₀U hU2 hUY hUt₀ hLt₀ hLU hirr
    ⟨y, hy, hb⟩ hb3 hbP hPL hP hUmax hChar
  classical
  let H : Subgroup X := Subgroup.centralizer ({t₀} : Set X)
  let T : Subgroup X := pCoreOf 2 H
  have hT2 : IsPGroup 2 T := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) H
  have hTH : T ≤ H := CFSG.LieType.BorelTits.pCoreOf_le (r := 2) H
  have hTN : H ≤ Subgroup.normalizer (T : Set X) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) H
  have hCb : Subgroup.centralizer ({b} : Set X) =
      R ⊔ (Subgroup.centralizer ({b} : Set X) ⊓ Y) :=
    centralizer_eq_sup_of_conj hy hb hRY hC
  have hCTU : T ⊓ Subgroup.centralizer ({b} : Set X) ≤ U :=
    fs81_rootO2_centralizer_le_U hZ hRY hCb hoddR hT2 hTH hTN hUmax
  have hTeqU : T = U :=
    pCoreOf_centralizer_eq_of_inf_centralizer_le ht₀ hLt₀ hLU hirr hb3 hbP hPL hP hCTU hChar
  have hcharT : H ⊓ Subgroup.centralizer (T : Set X) ≤ T := hChar
  have hTU : T ≤ U := le_of_eq hTeqU
  exact ⟨fs81_rootO2_R_eq_bot hZ hRY hcharT hTU hUY (hUY ht₀U), hTeqU⟩

end CFSG.StandardType.FrameRoute.FS81
