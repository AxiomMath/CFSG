module

public import CFSG.LocalAnalysis.UniquenessCase.UC6R3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.PartOneSixSeven
import CFSG.LocalAnalysis.UniquenessCase.UC6S9
import CFSG.LocalAnalysis.UniquenessCase.UCK47

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem six9_part1_data (D : Data G) (h67 : UC6.R6_7 D)
    (hsub : D.sig ⊆ D.sig1) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) {E : Subgroup G} (hEM : E ≤ D.M) (hEel : CFSG.Open.IsElemAbelian r E)
    (hEcard : Nat.card E = r ^ 2) (hΓ : rankThreeGamma 1 r E ≤ D.M) {p : ℕ} (hp : p.Prime)
    {X : Subgroup G} (hXcard : Nat.card X = p) (hEX : E ≤ normalizer (X : Set G))
    (hnX : ¬ normalizer (X : Set G) ≤ D.M) :
    Nat.card ↥(pCoreOf 2 D.M ⊓ centralizer (X : Set G) : Subgroup G) ≤ 2 ∧
      (3 < r → pCoreOf 2 D.M ⊓ centralizer (X : Set G) = ⊥) := by
  have hWle := UC6.inf_normalizer_le_pCoreOf_uc6 D.M X
  have hCle : centralizer (X : Set G) ≤ normalizer (X : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hQC : pCoreOf 2 D.M ⊓ centralizer (X : Set G) ≤
      pCoreOf 2 (normalizer (X : Set G) ⊓ D.M) :=
    (inf_le_inf_left _ hCle).trans hWle
  by_cases hO : pCoreOf 2 (normalizer (X : Set G) ⊓ D.M) = ⊥
  · rw [hO] at hQC
    have hbot : pCoreOf 2 D.M ⊓ centralizer (X : Set G) = ⊥ := le_bot_iff.1 hQC
    refine ⟨?_, fun _ => hbot⟩
    rw [hbot, Subgroup.card_bot]
    norm_num
  · have hNtop := UC6.normalizer_ne_top_of_card_prime_uc6 D.standing.simple D.standing.nonab
      hp hXcard
    obtain ⟨hr3, t, ht, hOt, -⟩ := h67 hsub r hr hr2 E hEM hEel hEcard hΓ
      (normalizer (X : Set G)) hEX hNtop hO hnX
    have hOt' : pCoreOf 2 (normalizer (X : Set G) ⊓ D.M) = zpowers t := hOt
    have hcard : Nat.card ↥(pCoreOf 2 (normalizer (X : Set G) ⊓ D.M)) = 2 := by
      rw [hOt', Nat.card_zpowers, ht]
    refine ⟨(Subgroup.card_le_of_le hQC).trans hcard.le, fun h3 => ?_⟩
    omega

private theorem six9_key_data (D : Data G) (hK : UCK.K47) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {X : Subgroup G} (hXM : X ≤ D.M) (hXcard : Nat.card X = p)
    (hfix : Nat.card ↥(pCoreOf 2 D.M ⊓ centralizer (X : Set G) : Subgroup G) ≤ 2)
    {P : Subgroup G} (hPM : P ≤ D.M) (hPp : IsPGroup p P) (hXP : X ≤ P) {y : G} (hy : y ∈ P)
    (hyc : ∀ x ∈ X, ∀ w ∈ P, (y * x * y⁻¹ * x⁻¹) * w = w * (y * x * y⁻¹ * x⁻¹)) :
    ∀ x ∈ X, y * x = x * y := by
  haveI := D.standing.simple
  have hMtop : D.M ≠ ⊤ :=
    CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top D.standing.nonab D.maxLocal.1
  have hMg : CFSG.Open.IsKGroup ↥D.M := D.standing.kProper.isKGroup D.M hMtop
  haveI hQn : (CFSG.pCore 2 ↥D.M).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ : IsPGroup 2 (CFSG.pCore 2 ↥D.M) := CFSG.LieType.BorelTits.pCore_isPGroup 2
  have hchar : centralizer ((CFSG.pCore 2 ↥D.M : Subgroup ↥D.M) : Set ↥D.M) ≤
      CFSG.pCore 2 ↥D.M := by
    intro x hx
    have h1 := D.standing.charTwo D.M D.maxLocal.1
    have hxG : (x : G) ∈ D.M ⊓ centralizer (pCoreOf 2 D.M : Set G) := by
      refine ⟨x.2, ?_⟩
      show (x : G) ∈ centralizer (pCoreOf 2 D.M : Set G)
      rw [mem_centralizer_iff]
      rintro _ ⟨q, hq, rfl⟩
      have := mem_centralizer_iff.1 hx q hq
      exact congrArg Subtype.val this
    obtain ⟨q, hq, hqx⟩ := h1 hxG
    have : q = x := Subtype.ext hqx
    exact this ▸ hq
  have hX'card : Nat.card (X.subgroupOf D.M) = p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXM).toEquiv]
    exact hXcard
  have hP'p : IsPGroup p (P.subgroupOf D.M) := hPp.comap_subtype
  have hX'P' : X.subgroupOf D.M ≤ P.subgroupOf D.M := fun x hx => hXP hx
  have hfix' : Nat.card ↥((CFSG.pCore 2 ↥D.M) ⊓
      centralizer ((X.subgroupOf D.M : Subgroup ↥D.M) : Set ↥D.M)) ≤ 2 := by
    have hle : ((CFSG.pCore 2 ↥D.M) ⊓
        centralizer ((X.subgroupOf D.M : Subgroup ↥D.M) : Set ↥D.M)).map D.M.subtype ≤
        pCoreOf 2 D.M ⊓ centralizer (X : Set G) := by
      rintro _ ⟨x, ⟨hxQ, hxC⟩, rfl⟩
      refine ⟨⟨x, hxQ, rfl⟩, ?_⟩
      show D.M.subtype x ∈ centralizer (X : Set G)
      rw [mem_centralizer_iff]
      intro h hh
      have := mem_centralizer_iff.1 hxC ⟨h, hXM hh⟩ hh
      exact congrArg Subtype.val this
    have := Subgroup.card_le_of_le hle
    rw [Subgroup.card_map_of_injective D.M.subtype_injective] at this
    exact this.trans hfix
  have hk := UC6.k47_transport_uc6 hK hMg (CFSG.pCore 2 ↥D.M) hQ hchar hp hp2
    (X.subgroupOf D.M) hX'card hfix' (P.subgroupOf D.M) hP'p hX'P' ⟨y, hPM hy⟩ hy
    (fun x hx w hw => Subtype.ext (by simpa using hyc x.1 hx w.1 hw))
  intro x hx
  exact congrArg Subtype.val (hk ⟨x, hXM hx⟩ hx)

theorem r6_9_of_r6_7 (D : Data G) (h63 : UC6.R6_3 D) (h67 : UC6.R6_7 D) : UC6.R6_9 D := by
  have hK : UCK.K47 := UCK.k47
  intro hsub r hr hr2 E hEM hEel hEcard hΓ p X hp hXM hXcard hEX hnX P hPM hPp hXP
  by_cases hp2 : p = 2
  · exfalso
    subst hp2
    have hXbot : X ≠ ⊥ := fun h => by
      rw [h, Subgroup.card_bot] at hXcard
      omega
    have hXp : IsPGroup 2 X := IsPGroup.of_card (n := 1) (by rw [pow_one]; exact hXcard)
    have hloc : IsTwoLocal (normalizer (X : Set G)) := ⟨X, hXbot, hXp, rfl⟩
    obtain ⟨N', hN'max, hN'⟩ := UC6.exists_rankThreeIsMaxTwoLocal_ge_uc6 hloc
    have h63' : calMOf E = {D.M} := h63 r hr hr2 E hEM hEel hEcard hΓ
    have hN'E : N' ∈ calMOf E := ⟨hN'max, hEX.trans hN'⟩
    rw [h63'] at hN'E
    have h2 : N' = D.M := hN'E
    have h3 : normalizer (X : Set G) ≤ D.M := h2 ▸ hN'
    exact hnX h3
  · have hpart1 := six9_part1_data D h67 hsub hr hr2 hEM hEel hEcard hΓ hp hXcard hEX hnX
    have hkey : ∀ y ∈ P, (∀ x ∈ X, ∀ w ∈ P,
        (y * x * y⁻¹ * x⁻¹) * w = w * (y * x * y⁻¹ * x⁻¹)) → ∀ x ∈ X, y * x = x * y :=
      fun y hy hyc => six9_key_data D hK hp hp2 hXM hXcard hpart1.1 hPM hPp hXP hy hyc
    refine ⟨hpart1, ?_, ?_⟩
    · intro y hy x hx
      obtain ⟨y₀, hy₀, rfl⟩ := hy
      have := hkey (y₀ : G) y₀.2 (fun x' hx' w hw =>
        UC6.commutator_commutes_of_mem_upperCentralSeries_two_uc6 hy₀ ⟨x', hXP hx'⟩ ⟨w, hw⟩) x hx
      exact this.symm
    · intro hX3 x hx
      obtain ⟨x₀, hx₀, hx₀x⟩ := hX3 hx
      refine ⟨⟨x, hXP hx⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      show (g : G) * x = x * (g : G)
      refine hkey (g : G) g.2 (fun x' hx' w hw => ?_) x hx
      obtain ⟨x'₀, hx'₀, hx'₀x⟩ := hX3 hx'
      have hc := UC6.commutator_commutes_of_mem_upperCentralSeries_two_uc6 hx'₀ g ⟨w, hw⟩
      have hx'eq : (x'₀ : G) = x' := hx'₀x
      have hcomm : Commute (x' * (g : G) * x'⁻¹ * (g : G)⁻¹) w := by
        have : ((x'₀ * g * x'₀⁻¹ * g⁻¹ : ↥P) : G) = x' * (g : G) * x'⁻¹ * (g : G)⁻¹ := by
          simp [hx'eq]
        rw [this] at hc
        exact hc
      have e : (g : G) * x' * (g : G)⁻¹ * x'⁻¹ = (x' * (g : G) * x'⁻¹ * (g : G)⁻¹)⁻¹ := by
        group
      rw [e]
      exact (Commute.inv_left hcomm).eq

namespace Three

open CFSG.LocalAnalysis.RankThreeUC

theorem r6_9_dataOfSetup (hS : Standing G) (hUC : rankThreeUC G) (hC : AGL81TheoremC G)
    (hK : UCK.K36) (S : Setup G) : UC6.R6_9 (dataOfSetup hS S) :=
  r6_9_of_r6_7 _ (r6_3_dataOfSetup hS hUC hC S) (r6_7_dataOfSetup hS hUC hC hK S)

end Three

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
