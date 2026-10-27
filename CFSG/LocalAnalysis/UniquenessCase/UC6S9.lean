module

public import CFSG.LocalAnalysis.UniquenessCase.UC6Mod
public import CFSG.LocalAnalysis.UniquenessCase.UC6S37

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 TheoremCAt Theorem614Four)

section Prelim

variable {G : Type} [Group G] [Finite G]

theorem exists_rankThreeIsMaxTwoLocal_ge_uc6 {H : Subgroup G} (hH : IsTwoLocal H) :
    ∃ N : Subgroup G, rankThreeIsMaxTwoLocal N ∧ H ≤ N := by
  classical
  set S : Set (Subgroup G) := {M | IsTwoLocal M ∧ H ≤ M} with hS
  obtain ⟨M, ⟨hM, hHM⟩, hmax⟩ :=
    Set.exists_max_image S (fun M => Nat.card M) (Set.toFinite S) ⟨H, hH, le_rfl⟩
  refine ⟨M, ⟨hM, fun K hK hMK => ?_⟩, hHM⟩
  have hKS : K ∈ S := ⟨hK, hHM.trans hMK⟩
  exact (Subgroup.eq_of_le_of_card_ge hMK (hmax K hKS)).symm

theorem normalizer_ne_top_of_card_prime_uc6 (hsimp : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) {p : ℕ} (hp : p.Prime) {X : Subgroup G}
    (hX : Nat.card X = p) : normalizer (X : Set G) ≠ ⊤ := by
  intro h
  haveI : X.Normal := Subgroup.normalizer_eq_top_iff.1 h
  rcases hsimp.eq_bot_or_eq_top_of_normal X with hb | ht
  · have : Nat.card X = 1 := by rw [hb]; exact Subgroup.card_bot
    rw [hX] at this
    exact hp.ne_one this
  · obtain ⟨a, b, hab⟩ := hnab
    have hel := isElemAbelian_of_card_prime hp hX
    have ha : a ∈ X := by rw [ht]; exact mem_top a
    have hb' : b ∈ X := by rw [ht]; exact mem_top b
    exact hab (congrArg Subtype.val (hel.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb'⟩))

theorem inf_normalizer_le_pCoreOf_uc6 (M X : Subgroup G) :
    pCoreOf 2 M ⊓ normalizer (X : Set G) ≤ pCoreOf 2 (normalizer (X : Set G) ⊓ M) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQM : pCoreOf 2 M ≤ M := CFSG.LieType.BorelTits.pCoreOf_le 2 M
  have hQp : IsPGroup 2 (pCoreOf 2 M) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    (fun x hx => ⟨hx.2, hQM hx.1⟩) ?_ (hQp.to_le inf_le_left)
  intro h hh
  rw [mem_normalizer_iff]
  intro x
  have h1 := mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 M hh.2) x
  have h2 : x ∈ normalizer (X : Set G) ↔ h * x * h⁻¹ ∈ normalizer (X : Set G) := by
    constructor
    · intro hx
      exact (normalizer (X : Set G)).mul_mem ((normalizer (X : Set G)).mul_mem hh.1 hx)
        ((normalizer (X : Set G)).inv_mem hh.1)
    · intro hx
      have := (normalizer (X : Set G)).mul_mem
        ((normalizer (X : Set G)).mul_mem ((normalizer (X : Set G)).inv_mem hh.1) hx) hh.1
      simpa [mul_assoc] using this
  rw [Subgroup.mem_inf, Subgroup.mem_inf]
  rw [h1, h2]

end Prelim

section Main

variable {G : Type} [Group G] [Finite G]
variable (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G)

include hS in
theorem six9_part1 (h67 : R6_7 (dataOfSetup4 hS hU S))
    (hsub : (dataOfSetup4 hS hU S).sig ⊆ (dataOfSetup4 hS hU S).sig1) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) {E : Subgroup G} (hEM : E ≤ S.M) (hEel : CFSG.Open.IsElemAbelian r E)
    (hEcard : Nat.card E = r ^ 2) (hΓ : rankThreeGamma 1 r E ≤ S.M) {p : ℕ} (hp : p.Prime)
    {X : Subgroup G} (hXcard : Nat.card X = p) (hEX : E ≤ normalizer (X : Set G))
    (hnX : ¬ normalizer (X : Set G) ≤ S.M) :
    Nat.card ↥(pCoreOf 2 S.M ⊓ centralizer (X : Set G) : Subgroup G) ≤ 2 ∧
      (3 < r → pCoreOf 2 S.M ⊓ centralizer (X : Set G) = ⊥) := by
  have hWle := inf_normalizer_le_pCoreOf_uc6 S.M X
  have hCle : centralizer (X : Set G) ≤ normalizer (X : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hQC : pCoreOf 2 S.M ⊓ centralizer (X : Set G) ≤
      pCoreOf 2 (normalizer (X : Set G) ⊓ S.M) :=
    (inf_le_inf_left _ hCle).trans hWle
  by_cases hO : pCoreOf 2 (normalizer (X : Set G) ⊓ S.M) = ⊥
  · rw [hO] at hQC
    have hbot : pCoreOf 2 S.M ⊓ centralizer (X : Set G) = ⊥ := le_bot_iff.1 hQC
    refine ⟨?_, fun _ => hbot⟩
    rw [hbot, Subgroup.card_bot]
    norm_num
  · have hNtop := normalizer_ne_top_of_card_prime_uc6 hS.simple hS.nonab hp hXcard
    obtain ⟨hr3, t, ht, hOt, -⟩ := h67 hsub r hr hr2 E hEM hEel hEcard hΓ
      (normalizer (X : Set G)) hEX hNtop hO hnX
    have hOt' : pCoreOf 2 (normalizer (X : Set G) ⊓ S.M) = zpowers t := hOt
    have hcard : Nat.card ↥(pCoreOf 2 (normalizer (X : Set G) ⊓ S.M)) = 2 := by
      rw [hOt', Nat.card_zpowers, ht]
    refine ⟨(Subgroup.card_le_of_le hQC).trans hcard.le, fun h3 => ?_⟩
    omega

include hS in
theorem six9_key (hK : UCK.K47) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X : Subgroup G}
    (hXM : X ≤ S.M) (hXcard : Nat.card X = p)
    (hfix : Nat.card ↥(pCoreOf 2 S.M ⊓ centralizer (X : Set G) : Subgroup G) ≤ 2)
    {P : Subgroup G} (hPM : P ≤ S.M) (hPp : IsPGroup p P) (hXP : X ≤ P) {y : G} (hy : y ∈ P)
    (hyc : ∀ x ∈ X, ∀ w ∈ P, (y * x * y⁻¹ * x⁻¹) * w = w * (y * x * y⁻¹ * x⁻¹)) :
    ∀ x ∈ X, y * x = x * y := by
  haveI := hS.simple
  have hMtop : S.M ≠ ⊤ :=
    CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top hS.nonab S.maxLocal.1
  have hMg : CFSG.Open.IsKGroup ↥S.M := hS.kProper.isKGroup S.M hMtop
  haveI hQn : (CFSG.pCore 2 ↥S.M).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ : IsPGroup 2 (CFSG.pCore 2 ↥S.M) := CFSG.LieType.BorelTits.pCore_isPGroup 2
  have hchar : centralizer ((CFSG.pCore 2 ↥S.M : Subgroup ↥S.M) : Set ↥S.M) ≤
      CFSG.pCore 2 ↥S.M := by
    intro x hx
    have h1 := hS.charTwo S.M S.maxLocal.1
    have hxG : (x : G) ∈ S.M ⊓ centralizer (pCoreOf 2 S.M : Set G) := by
      refine ⟨x.2, ?_⟩
      show (x : G) ∈ centralizer (pCoreOf 2 S.M : Set G)
      rw [mem_centralizer_iff]
      rintro _ ⟨q, hq, rfl⟩
      have := mem_centralizer_iff.1 hx q hq
      exact congrArg Subtype.val this
    obtain ⟨q, hq, hqx⟩ := h1 hxG
    have : q = x := Subtype.ext hqx
    exact this ▸ hq
  have hX'card : Nat.card (X.subgroupOf S.M) = p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXM).toEquiv]
    exact hXcard
  have hP'p : IsPGroup p (P.subgroupOf S.M) := hPp.comap_subtype
  have hX'P' : X.subgroupOf S.M ≤ P.subgroupOf S.M := fun x hx => hXP hx
  have hfix' : Nat.card ↥((CFSG.pCore 2 ↥S.M) ⊓
      centralizer ((X.subgroupOf S.M : Subgroup ↥S.M) : Set ↥S.M)) ≤ 2 := by
    have hle : ((CFSG.pCore 2 ↥S.M) ⊓
        centralizer ((X.subgroupOf S.M : Subgroup ↥S.M) : Set ↥S.M)).map S.M.subtype ≤
        pCoreOf 2 S.M ⊓ centralizer (X : Set G) := by
      rintro _ ⟨x, ⟨hxQ, hxC⟩, rfl⟩
      refine ⟨⟨x, hxQ, rfl⟩, ?_⟩
      show S.M.subtype x ∈ centralizer (X : Set G)
      rw [mem_centralizer_iff]
      intro h hh
      have := mem_centralizer_iff.1 hxC ⟨h, hXM hh⟩ hh
      exact congrArg Subtype.val this
    have := Subgroup.card_le_of_le hle
    rw [Subgroup.card_map_of_injective S.M.subtype_injective] at this
    exact this.trans hfix
  have hk := k47_transport_uc6 hK hMg (CFSG.pCore 2 ↥S.M) hQ hchar hp hp2
    (X.subgroupOf S.M) hX'card hfix' (P.subgroupOf S.M) hP'p hX'P' ⟨y, hPM hy⟩ hy
    (fun x hx w hw => Subtype.ext (by simpa using hyc x.1 hx w.1 hw))
  intro x hx
  exact congrArg Subtype.val (hk ⟨x, hXM hx⟩ hx)

theorem commutator_commutes_of_mem_upperCentralSeries_two_uc6 {P : Subgroup G} {a : ↥P}
    (ha : a ∈ Subgroup.upperCentralSeries ↥P 2) (g w : ↥P) :
    ((a * g * a⁻¹ * g⁻¹ : ↥P) : G) * (w : G) = (w : G) * ((a * g * a⁻¹ * g⁻¹ : ↥P) : G) := by
  have h1 : a * g * a⁻¹ * g⁻¹ ∈ Subgroup.upperCentralSeries ↥P 1 :=
    (Subgroup.mem_upperCentralSeries_succ_iff.1
      (show a ∈ Subgroup.upperCentralSeries ↥P (1 + 1) from ha)) g
  rw [Subgroup.upperCentralSeries_one] at h1
  have := Subgroup.mem_center_iff.1 h1 w
  exact (congrArg Subtype.val this).symm

include hS in
theorem r6_9_of_K47 (hK : UCK.K47) (hC : TheoremCAt S.M) (h67 : R6_7 (dataOfSetup4 hS hU S)) :
    R6_9 (dataOfSetup4 hS hU S) := by
  intro hsub r hr hr2 E hEM hEel hEcard hΓ p X hp hXM hXcard hEX hnX P hPM hPp hXP
  by_cases hp2 : p = 2
  · exfalso
    subst hp2
    have hXbot : X ≠ ⊥ := fun h => by
      rw [h, Subgroup.card_bot] at hXcard
      omega
    have hXp : IsPGroup 2 X := IsPGroup.of_card (n := 1) (by rw [pow_one]; exact hXcard)
    have hloc : IsTwoLocal (normalizer (X : Set G)) := ⟨X, hXbot, hXp, rfl⟩
    obtain ⟨N', hN'max, hN'⟩ := exists_rankThreeIsMaxTwoLocal_ge_uc6 hloc
    have h63 : calMOf E = {S.M} := r6_3_dataOfSetup4 hS hU S hC r hr hr2 E hEM hEel hEcard hΓ
    have hN'E : N' ∈ calMOf E := ⟨hN'max, hEX.trans hN'⟩
    rw [h63] at hN'E
    have h2 : N' = S.M := hN'E
    have h3 : normalizer (X : Set G) ≤ S.M := h2 ▸ hN'
    exact hnX h3
  · have hpart1 := six9_part1 hS hU S h67 hsub hr hr2 hEM hEel hEcard hΓ hp hXcard hEX hnX
    have hkey : ∀ y ∈ P, (∀ x ∈ X, ∀ w ∈ P,
        (y * x * y⁻¹ * x⁻¹) * w = w * (y * x * y⁻¹ * x⁻¹)) → ∀ x ∈ X, y * x = x * y :=
      fun y hy hyc => six9_key hS S hK hp hp2 hXM hXcard hpart1.1 hPM hPp hXP hy hyc
    refine ⟨hpart1, ?_, ?_⟩
    · intro y hy x hx
      obtain ⟨y₀, hy₀, rfl⟩ := hy
      have := hkey (y₀ : G) y₀.2 (fun x' hx' w hw =>
        commutator_commutes_of_mem_upperCentralSeries_two_uc6 hy₀ ⟨x', hXP hx'⟩ ⟨w, hw⟩) x hx
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
      have hc := commutator_commutes_of_mem_upperCentralSeries_two_uc6 hx'₀ g ⟨w, hw⟩
      have hx'eq : (x'₀ : G) = x' := hx'₀x
      have hcomm : Commute (x' * (g : G) * x'⁻¹ * (g : G)⁻¹) w := by
        have : ((x'₀ * g * x'₀⁻¹ * g⁻¹ : ↥P) : G) = x' * (g : G) * x'⁻¹ * (g : G)⁻¹ := by
          simp [hx'eq]
        rw [this] at hc
        exact hc
      have e : (g : G) * x' * (g : G)⁻¹ * x'⁻¹ = (x' * (g : G) * x'⁻¹ * (g : G)⁻¹)⁻¹ := by group
      rw [e]
      exact (Commute.inv_left hcomm).eq

end Main

end CFSG.LocalAnalysis.UniquenessCase.UC6
