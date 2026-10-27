module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDL1Lift
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitRankTwo
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBlock
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosPerm
public import CFSG.LocalAnalysis.StandardType.GGSecFiveL1PhanTransfer
import CFSG.LocalAnalysis.StandardType.GGQTwoDL1UCore
import CFSG.LocalAnalysis.StandardType.GGQTwoDL1UOdd
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosBlockAux4
import CFSG.LieType.ChevTwo.OppCl.AutLiftsUnitary
import CFSG.RankThree.PartOne.SEITZ2.SU3Pair
import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldAut
import CFSG.RankThree.PartOne.CTP.SeitzFineU5
import CFSG.RankThree.PartOne.CTP.StdSub
import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
import CFSG.RankThree.PartOne.KC.UnitaryHigherCrossPrimeTorus
import CFSG.RankThree.PartOne.KC.UnitaryPlaneEndpoints
import CFSG.RankThree.PartTwo.KFacts.KS14SzLie

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan

private theorem p9uBU_fixes_of_le_centralizer {G : Type} [Group G] [Finite G] {Bs X : Subgroup G}
    {y : G} (hy : y ∈ Bs) (hXy : X ≤ Subgroup.centralizer ({y} : Set G)) {φ : MulAut ↥Bs}
    (hφ : φ ∈ ggAutomizer X Bs) : y ∈ ggHyperplane Bs φ := by
  obtain ⟨g, hgX, -, hact⟩ := mem_ggAutomizer_iff.mp hφ
  have hgy : g * y * g⁻¹ = y := by
    have h := Subgroup.mem_centralizer_singleton_iff.mp (hXy hgX)
    rw [h]; group
  refine ⟨⟨y, hy⟩, ?_, rfl⟩
  change φ ⟨y, hy⟩ = ⟨y, hy⟩
  apply Subtype.ext
  rw [hact]
  exact hgy

theorem qtwoDL1_baseU_inner {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs X : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} {ψ : Su K 2 1 n →* G}
    (hK : Nat.card K = 4) (h : GGNSLocalHyp p B Bs K 1 n ψ) (hrange : ψ.range = X)
    (hd : GGActsDiagonally (p := 2) (f := 1) ψ Bs)
    (hfull : Nat.card ↥Bs = 3 ^ (n - 1) *
      Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)))
    {a b c : Fin n} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) {r r' : MulAut ↥Bs}
    (hr : ∀ s : ↥Bs, ((r s : ↥Bs) : G) =
      ψ (ggPermSU (Equiv.swap a b)) * (s : G) * (ψ (ggPermSU (Equiv.swap a b)))⁻¹)
    (hr' : ∀ s : ↥Bs, ((r' s : ↥Bs) : G) =
      ψ (ggPermSU (Equiv.swap b c)) * (s : G) * (ψ (ggPermSU (Equiv.swap b c)))⁻¹) :
    ∀ t ∈ Subgroup.centralizer
        (((ggHyperplane Bs r ⊓ ggHyperplane Bs r') : Subgroup G) : Set G),
      t ∈ Subgroup.normalizer (X : Set G) → (∃ k : ℕ, t ^ (2 ^ k) = 1) →
        ∃ m ∈ ggOTwoPrime (X ⊓ Subgroup.centralizer
          (((ggHyperplane Bs r ⊓ ggHyperplane Bs r') : Subgroup G) : Set G)),
          ∀ y ∈ X, t * y * t⁻¹ = m * y * m⁻¹ := by
  rintro t htA htN ⟨k, htk⟩
  have hp3 : p = 3 := by
    have hdvd : p ∣ 3 := by simpa using h.dvd
    exact (Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_three).mp hdvd
  have hT : ({a, b, c} : Finset (Fin n)).card = 3 :=
    Finset.card_triple_eq_three_iff.mpr ⟨hab, hac, hbc⟩
  let α : MulAut ↥X := Subgroup.normalizerMonoidHom X ⟨t, htN⟩
  have hαval : ∀ y : ↥X, ((α y : ↥X) : G) = t * (y : G) * t⁻¹ := fun y =>
    Subgroup.normalizerMonoidHom_apply_apply_coe X ⟨t, htN⟩ y
  have hαk : α ^ (2 ^ k) = 1 := by
    have h2 : (⟨t, htN⟩ : Subgroup.normalizer (X : Set G)) ^ (2 ^ k) = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one, htk]
    change (Subgroup.normalizerMonoidHom X ⟨t, htN⟩) ^ (2 ^ k) = 1
    rw [← map_pow, h2, map_one]
  have hα : ∀ (s : Su K 2 1 n) (d : Fin n → K),
      ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = Matrix.diagonal d →
        (∀ l, d l ^ 3 = 1) →
          (∀ i ∈ ({a, b, c} : Finset (Fin n)), ∀ j ∈ ({a, b, c} : Finset (Fin n)), d i = d j) →
            ∀ z : ↥X, (z : G) = ψ s → ∀ y : ↥X, α (z * y * z⁻¹) = z * α y * z⁻¹ := by
    intro s d hsd hd3 hconst z hz y
    have hdp : ∀ l, d l ^ p = 1 := by rw [hp3]; exact hd3
    have hsA : ψ s ∈ ggHyperplane Bs r ⊓ ggHyperplane Bs r' :=
      Subgroup.mem_inf.mpr
        ⟨ggNSPosPB2_map_mem_hyperplane h hd a b hab r hr hsd hdp (hconst a (by simp) b (by simp)),
          ggNSPosPB2_map_mem_hyperplane h hd b c hbc r' hr' hsd hdp
            (hconst b (by simp) c (by simp))⟩
    have hts : ψ s * t = t * ψ s := Subgroup.mem_centralizer_iff.mp htA (ψ s) hsA
    have hts' : (ψ s)⁻¹ * t⁻¹ = t⁻¹ * (ψ s)⁻¹ := by rw [← mul_inv_rev, ← hts, mul_inv_rev]
    apply Subtype.ext
    rw [hαval (z * y * z⁻¹)]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hαval y, hz]
    calc t * (ψ s * (y : G) * (ψ s)⁻¹) * t⁻¹
        = (t * ψ s) * (y : G) * ((ψ s)⁻¹ * t⁻¹) := by group
      _ = (ψ s * t) * (y : G) * (t⁻¹ * (ψ s)⁻¹) := by rw [← hts, hts']
      _ = ψ s * (t * (y : G) * t⁻¹) * (ψ s)⁻¹ := by group
  obtain ⟨s, hsJ, -, hsact⟩ := qtwoDL1_unitChart_fixTorus hK h hrange
    (J := ({a, b, c} : Finset (Fin n))) (Or.inr hT) α hα hαk
  refine ⟨ψ s, ?_, ?_⟩
  · have hle := ggQTwoDUnit_le_rankTwoIn h hK hd hab hbc hac hr hr'
    rw [hrange] at hle
    exact hle ⟨s, hsJ, rfl⟩
  · intro y hy
    have hy' : y ∈ ψ.range := by rw [hrange]; exact hy
    obtain ⟨u, rfl⟩ := hy'
    have h1 := hsact u ⟨ψ u, hy⟩ rfl
    rw [hαval] at h1
    rw [h1, map_mul, map_mul, map_inv]


theorem qtwoDL1_baseU_hin {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (ha₀ : GGLNoncyclicInput)
    (hodd : Odd (Nat.card ↥(Subgroup.centralizer (Bs : Set G))))
    {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} [NeZero n] {ψ : Su K 2 1 n →* G}
    (hK : Nat.card K = 4) (h : GGNSLocalHyp p B Bs K 1 n ψ) (hrange : ψ.range = L)
    (hd : GGActsDiagonally (p := 2) (f := 1) ψ Bs)
    (hfull : Nat.card ↥Bs = 3 ^ (n - 1) * Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)))
    {r₀ r₀' : MulAut ↥Bs} (hr₀A : r₀ ∈ ggAutomizer L Bs) (hr₀'A : r₀' ∈ ggAutomizer L Bs)
    (hr₀refl : GGIsReflection p r₀) (hr₀'refl : GGIsReflection p r₀')
    (hrfun : ∀ s : ↥Bs, ((r₀ s : ↥Bs) : G) =
      ψ (ggPermSU (Equiv.swap (0 : Fin n) 1)) * (s : G) *
        (ψ (ggPermSU (Equiv.swap (0 : Fin n) 1)))⁻¹)
    (hr'fun : ∀ s : ↥Bs, ((r₀' s : ↥Bs) : G) =
      ψ (ggPermSU (Equiv.swap (1 : Fin n) 2)) * (s : G) *
        (ψ (ggPermSU (Equiv.swap (1 : Fin n) 2)))⁻¹) :
    ∀ c ∈ Subgroup.centralizer ((ggHyperplane Bs r₀ ⊓ ggHyperplane Bs r₀') : Set G),
      (∃ k : ℕ, c ^ (2 ^ k) = 1) →
        ∃ m ∈ ggOTwoPrime (L ⊓ Subgroup.centralizer
          ((ggHyperplane Bs r₀ ⊓ ggHyperplane Bs r₀') : Set G)),
          ∀ y ∈ L, c * y * c⁻¹ = m * y * m⁻¹ := by
  intro c hc h2
  have hn4 : 4 ≤ n := h.four_le
  have hxBs : x ∈ Bs := SecFiveL1Odd.le_bstar hcfg hcfg.1.1.2.2.1.2.2.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) :=
    hcfg.1.1.1.2.2.2.2.2.2.1.2.2.2.1.1
  have hS : LargeEvenSStar p B x L := hcfg.1.1.1.2.2.2.2.2.2.1
  have hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S :=
    ha₀ G p B x L hcfg.1.1.1
  have hxA : x ∈ ggHyperplane Bs r₀ ⊓ ggHyperplane Bs r₀' :=
    Subgroup.mem_inf.mpr
      ⟨p9uBU_fixes_of_le_centralizer hxBs hLx hr₀A,
       p9uBU_fixes_of_le_centralizer hxBs hLx hr₀'A⟩
  have hcx : c ∈ Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hc x hxA).symm
  have hcN : c ∈ Subgroup.normalizer (L : Set G) :=
    mem_normalizer_of_sstar hS hnc hcx
  have h01 : (0 : Fin n) ≠ 1 := by
    intro h
    have hv := congrArg Fin.val h
    change (Fin.ofNat n 0).val = (Fin.ofNat n 1).val at hv
    simp only [Fin.val_ofNat] at hv
    rw [Nat.zero_mod, Nat.mod_eq_of_lt (by omega : 1 < n)] at hv
    omega
  have h12 : (1 : Fin n) ≠ 2 := by
    intro h
    have hv := congrArg Fin.val h
    change (Fin.ofNat n 1).val = (Fin.ofNat n 2).val at hv
    simp only [Fin.val_ofNat] at hv
    rw [Nat.mod_eq_of_lt (by omega : 1 < n), Nat.mod_eq_of_lt (by omega : 2 < n)] at hv
    omega
  have h02 : (0 : Fin n) ≠ 2 := by
    intro h
    have hv := congrArg Fin.val h
    change (Fin.ofNat n 0).val = (Fin.ofNat n 2).val at hv
    simp only [Fin.val_ofNat] at hv
    rw [Nat.zero_mod, Nat.mod_eq_of_lt (by omega : 2 < n)] at hv
    omega
  exact qtwoDL1_baseU_inner hK h hrange hd hfull h01 h12 h02 hrfun hr'fun c hc hcN h2

theorem qtwoDL1_base_unit (ha₀ : GGLNoncyclicInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hodd : Odd (Nat.card ↥(Subgroup.centralizer (Bs : Set G))))
    {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} {ψ : Su K 2 1 n →* G}
    (hK : Nat.card K = 4) (h : GGNSLocalHyp p B Bs K 1 n ψ) (hrange : ψ.range = L)
    (hd : GGActsDiagonally (p := 2) (f := 1) ψ Bs)
    (hfull : Nat.card ↥Bs = 3 ^ (n - 1) * Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G))) :
    ∃ r₀ ∈ ggAutomizer L Bs, GGIsReflection p r₀ ∧ ∃ r₀' ∈ ggAutomizer L Bs,
      GGIsReflection p r₀' ∧ r₀ * r₀' ≠ r₀' * r₀ ∧ Nat.card ↥(ggRankTwo Bs r₀ r₀') ≤ 216 := by
  have hn4 : 4 ≤ n := h.four_le
  haveI : NeZero n := ⟨by omega⟩
  obtain ⟨ε, hact, hεrefl⟩ := ggNSDiag_automizer_perm (f := 1) h hd
  let r₀ : MulAut ↥Bs :=
    ((ε (Equiv.swap (0 : Fin n) 1) : ↥(ggAutomizer ψ.range Bs)) : MulAut ↥Bs)
  let r₀' : MulAut ↥Bs :=
    ((ε (Equiv.swap (1 : Fin n) 2) : ↥(ggAutomizer ψ.range Bs)) : MulAut ↥Bs)
  have h01 : (0 : Fin n) ≠ 1 := by
    intro h
    have hv := congrArg Fin.val h
    change (Fin.ofNat n 0).val = (Fin.ofNat n 1).val at hv
    simp only [Fin.val_ofNat] at hv
    rw [Nat.zero_mod, Nat.mod_eq_of_lt (by omega : 1 < n)] at hv
    omega
  have h12 : (1 : Fin n) ≠ 2 := by
    intro h
    have hv := congrArg Fin.val h
    change (Fin.ofNat n 1).val = (Fin.ofNat n 2).val at hv
    simp only [Fin.val_ofNat] at hv
    rw [Nat.mod_eq_of_lt (by omega : 1 < n), Nat.mod_eq_of_lt (by omega : 2 < n)] at hv
    omega
  have h02 : (0 : Fin n) ≠ 2 := by
    intro h
    have hv := congrArg Fin.val h
    change (Fin.ofNat n 0).val = (Fin.ofNat n 2).val at hv
    simp only [Fin.val_ofNat] at hv
    rw [Nat.zero_mod, Nat.mod_eq_of_lt (by omega : 2 < n)] at hv
    omega
  have hr₀refl : GGIsReflection p r₀ := hεrefl 0 1 h01
  have hr₀'refl : GGIsReflection p r₀' := hεrefl 1 2 h12
  have hr₀A : r₀ ∈ ggAutomizer L Bs := by
    have hmem : r₀ ∈ ggAutomizer ψ.range Bs := (ε (Equiv.swap (0 : Fin n) 1)).2
    rwa [hrange] at hmem
  have hr₀'A : r₀' ∈ ggAutomizer L Bs := by
    have hmem : r₀' ∈ ggAutomizer ψ.range Bs := (ε (Equiv.swap (1 : Fin n) 2)).2
    rwa [hrange] at hmem
  have hncperm : Equiv.swap (0 : Fin n) 1 * Equiv.swap (1 : Fin n) 2 ≠
      Equiv.swap (1 : Fin n) 2 * Equiv.swap (0 : Fin n) 1 := by
    intro he
    have h0 := congrArg (fun f => f (0 : Fin n)) he
    simp only [Equiv.Perm.mul_apply] at h0
    rw [Equiv.swap_apply_of_ne_of_ne h01 h02, Equiv.swap_apply_left,
      Equiv.swap_apply_left] at h0
    exact h12 h0
  have hcoe : r₀ * r₀' =
      ((ε (Equiv.swap (0 : Fin n) 1 * Equiv.swap (1 : Fin n) 2) :
        ↥(ggAutomizer ψ.range Bs)) : MulAut ↥Bs) := by
    change ((ε (Equiv.swap (0 : Fin n) 1) : ↥(ggAutomizer ψ.range Bs)) : MulAut ↥Bs) *
        ((ε (Equiv.swap (1 : Fin n) 2) : ↥(ggAutomizer ψ.range Bs)) : MulAut ↥Bs) =
      ((ε (Equiv.swap (0 : Fin n) 1 * Equiv.swap (1 : Fin n) 2) :
        ↥(ggAutomizer ψ.range Bs)) : MulAut ↥Bs)
    rw [← Subgroup.coe_mul, ← map_mul]
  have hcoe' : r₀' * r₀ =
      ((ε (Equiv.swap (1 : Fin n) 2 * Equiv.swap (0 : Fin n) 1) :
        ↥(ggAutomizer ψ.range Bs)) : MulAut ↥Bs) := by
    change ((ε (Equiv.swap (1 : Fin n) 2) : ↥(ggAutomizer ψ.range Bs)) : MulAut ↥Bs) *
        ((ε (Equiv.swap (0 : Fin n) 1) : ↥(ggAutomizer ψ.range Bs)) : MulAut ↥Bs) =
      ((ε (Equiv.swap (1 : Fin n) 2 * Equiv.swap (0 : Fin n) 1) :
        ↥(ggAutomizer ψ.range Bs)) : MulAut ↥Bs)
    rw [← Subgroup.coe_mul, ← map_mul]
  have hne : r₀ * r₀' ≠ r₀' * r₀ := by
    intro heq
    apply hncperm
    apply ε.injective
    apply Subtype.ext
    rw [← hcoe, ← hcoe']
    exact heq
  have hrfun : ∀ s : ↥Bs, ((r₀ s : ↥Bs) : G) =
      ψ (ggPermSU (Equiv.swap (0 : Fin n) 1)) * (s : G) *
        (ψ (ggPermSU (Equiv.swap (0 : Fin n) 1)))⁻¹ := by
    intro s
    simpa using hact (Equiv.swap (0 : Fin n) 1) s
  have hr'fun : ∀ s : ↥Bs, ((r₀' s : ↥Bs) : G) =
      ψ (ggPermSU (Equiv.swap (1 : Fin n) 2)) * (s : G) *
        (ψ (ggPermSU (Equiv.swap (1 : Fin n) 2)))⁻¹ := by
    intro s
    simpa using hact (Equiv.swap (1 : Fin n) 2) s
  have hoddC := qtwoDL1_baseU_oddC hodd hK h hrange hd h01 h12 h02 hrfun hr'fun
  have hin := qtwoDL1_baseU_hin hcfg ha₀ hodd hK h hrange hd hfull hr₀A hr₀'A hr₀refl hr₀'refl
    hrfun hr'fun
  have hlift : ggOTwoPrime (Subgroup.centralizer
        ((ggHyperplane Bs r₀ ⊓ ggHyperplane Bs r₀') : Set G)) =
      ggOTwoPrime (L ⊓ Subgroup.centralizer
        ((ggHyperplane Bs r₀ ⊓ ggHyperplane Bs r₀') : Set G)) :=
    qtwoDL1_ggOTwoPrime_eq_of_inner hoddC hin
  have hrank : ggRankTwo Bs r₀ r₀' = ggRankTwoIn L Bs r₀ r₀' := by
    rw [ggRankTwo, ggRankTwoIn]
    exact hlift
  have hcardIn : Nat.card ↥(ggRankTwoIn L Bs r₀ r₀') = 216 := by
    rw [← hrange]
    rw [ggQTwoDUnit_rankTwoIn_eq h hK hd h01 h12 h02 hrfun hr'fun]
    exact ggQTwoDUnit_card_map_coordBlockSU_three hK ψ h.ker h.four_le h01 h12 h02
  refine ⟨r₀, hr₀A, hr₀refl, r₀', hr₀'A, hr₀'refl, hne, ?_⟩
  rw [hrank, hcardIn]

end CFSG.StandardType.QTwo

end
