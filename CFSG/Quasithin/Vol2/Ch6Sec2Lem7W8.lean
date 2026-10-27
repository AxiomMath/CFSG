module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem7W7
public import CFSG.Quasithin.EmptyFaithful.R3c2Hat

public section

namespace CFSG.Quasithin.H13

open CFSG.Open hiding StatedSL StatedClassicalModel StatedProj StatedLieTag StatedLieAdmissible
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G] {Γ : Type} [Group Γ] [Finite Γ]

omit [Finite Γ] in
theorem a318Data627 {H Y : Subgroup G} (hHY : H ≤ Y) (hYH : Y ≤ Subgroup.normalizer (H : Set G))
    (ρ : ↥H →* Γ) (hρ : ∀ x : ↥H, ρ x = 1 ↔ (x : G) ∈ pCoreOf 2 H) {K₀ : Subgroup G}
    (hK₀ : K₀ ∈ cComp H) {L : Subgroup Γ} (hK₀L : (K₀.subgroupOf H).map ρ = L) :
    ∃ ψ : ↥K₀ →* ↥L, Function.Surjective ψ ∧ ψ.ker = CFSG.pCore 2 ↥K₀ ∧
      (∀ x : ↥K₀, ψ x = 1 →
        (⟨x, hHY (le_of_mem_cComp hK₀ x.2)⟩ : ↥Y) ∈ CFSG.pPrimeCore 3 ↥Y) ∧
      ∀ x : ↥K₀, ψ x = 1 → ∃ n : ℕ, x ^ 2 ^ n = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK₀H : K₀ ≤ H := le_of_mem_cComp hK₀
  have hmem : ∀ k : ↥K₀, ρ (Subgroup.inclusion hK₀H k) ∈ L := fun k => by
    rw [← hK₀L]
    exact ⟨Subgroup.inclusion hK₀H k, k.2, rfl⟩
  set ψ : ↥K₀ →* ↥L := (ρ.comp (Subgroup.inclusion hK₀H)).codRestrict L hmem with hψ
  have hψ1 : ∀ x : ↥K₀, ψ x = 1 ↔ (x : G) ∈ pCoreOf 2 H := fun x => by
    show ψ x = 1 ↔ ((Subgroup.inclusion hK₀H x : ↥H) : G) ∈ pCoreOf 2 H
    rw [← hρ (Subgroup.inclusion hK₀H x)]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  have hO2 : IsPGroup 2 (pCoreOf 2 H) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have h2el : ∀ x : ↥K₀, ψ x = 1 → ∃ n : ℕ, x ^ 2 ^ n = 1 := by
    intro x hx
    obtain ⟨n, hn⟩ := hO2 ⟨x, (hψ1 x).mp hx⟩
    exact ⟨n, Subtype.ext (by simpa using congrArg Subtype.val hn)⟩
  refine ⟨ψ, fun l => ?_, ?_, fun x hx => ?_, h2el⟩
  · obtain ⟨k, hk, hkl⟩ := (hK₀L ▸ l.2 : (l : Γ) ∈ (K₀.subgroupOf H).map ρ)
    exact ⟨⟨k, hk⟩, Subtype.ext hkl⟩
  · apply le_antisymm
    · refine le_sSup ⟨MonoidHom.normal_ker ψ, fun x => ?_⟩
      obtain ⟨n, hn⟩ := h2el x x.2
      exact ⟨n, Subtype.ext hn⟩
    · intro x hx
      rw [MonoidHom.mem_ker, hψ1]
      have h1 : (x : G) ∈ pCoreOf 2 K₀ := by
        rw [show pCoreOf 2 K₀ = (CFSG.pCore 2 ↥K₀).map K₀.subtype by
          rfl]
        exact ⟨x, hx, rfl⟩
      exact A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hK₀) h1
  ·
    have hYn : Y ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := fun y hy =>
      CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 H (hYH hy)
    have hOY : pCoreOf 2 H ≤ Y := (CFSG.LieType.BorelTits.pCoreOf_le 2 H).trans hHY
    have hn : ((pCoreOf 2 H).subgroupOf Y).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hOY).mpr hYn
    have hcop : Nat.Coprime 3 (Nat.card ((pCoreOf 2 H).subgroupOf Y)) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOY).toEquiv]
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hO2
      rw [hk]
      exact Nat.Coprime.pow_right k (by norm_num)
    exact (le_sSup ⟨hn, hcop⟩ : (pCoreOf 2 H).subgroupOf Y ≤ CFSG.pPrimeCore 3 ↥Y)
      ((hψ1 x).mp hx)

theorem false_of_a318627 (hF : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK) {H Y : Subgroup G}
    (hHY : H ≤ Y) (hYH : Y ≤ Subgroup.normalizer (H : Set G)) (hSQ : SQTKGroup ↥Y) {d : G}
    (hdY : d ∈ Y) (hdH : d ∉ H) (hd3 : orderOf d = 3) {K₀ : Subgroup G} (hK₀ : K₀ ∈ cComp H)
    {L : Subgroup Γ} (hq : CFSG.IsQuasisimple ↥L) (ψ : ↥K₀ →* ↥L) (hψ : Function.Surjective ψ)
    (hker : ψ.ker = CFSG.pCore 2 ↥K₀) (h2el : ∀ x : ↥K₀, ψ x = 1 → ∃ n : ℕ, x ^ 2 ^ n = 1)
    (hr : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥L))
    (hgen : Subgroup.closure {y : ↥L | orderOf y = 3} = ⊤) (h3 : 3 ∣ Nat.card ↥L)
    (hn2 : ¬ A318Case2 (starImage 3 (K₀.subgroupOf Y)))
    (hn3 : A318Case3Group ↥(starImage 3 (K₀.subgroupOf Y)) →
      ¬ A318Case3b (starImage 3 (K₀.subgroupOf Y))) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK₀H : K₀ ≤ H := le_of_mem_cComp hK₀
  have hK₀Y : K₀ ∈ cComp Y :=
    cComp_mem_of_subnormal (A3.subnormal_of_normal hHY
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hHY).mpr hYH)) hK₀
  set e : (↥K₀ ⧸ CFSG.pCore 2 ↥K₀) ≃* ↥L :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψ) with he
  have hQ : CFSG.IsQuasisimple (↥K₀ ⧸ CFSG.pCore 2 ↥K₀) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hq
  have hk3 : ¬ 3 ∣ Nat.card ψ.ker := by
    intro h
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥ψ.ker) 3 h
    obtain ⟨n, hn⟩ := h2el x x.2
    have h1 : (x : ↥K₀) ^ 2 ^ n = 1 := hn
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [Subgroup.orderOf_coe, hx] at h2
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2)
    omega
  have hrK : 2 ≤ CFSG.Open.pRank 3 K₀ := by
    have h1 := R3c2.pRank_three_range_eq ψ hk3
    have h2 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥ψ.range) =
        CFSG.Open.pRank 3 (⊤ : Subgroup ↥L) := by
      rw [MonoidHom.range_eq_top.mpr hψ]
      exact CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) Subgroup.topEquiv
    rw [← pRank_top_subtype K₀, ← h1, h2]
    exact hr
  have hker3 : ∀ x ∈ ψ.ker, orderOf x ≠ 3 := by
    intro x hx h
    obtain ⟨n, hn⟩ := h2el x hx
    have h2 := orderOf_dvd_of_pow_eq_one hn
    rw [h] at h2
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2)
    omega
  have hθ : K₀ ≤ thetaOf Y := R3c2.le_thetaOf_of_surjection (le_of_mem_cComp hK₀Y)
    (perfect_of_mem_cComp hK₀) hQ ψ hψ hker3 hgen h3
  have heq := R3c2.eq_thetaOf_of_a318_of_group hF h36 h38 hSQ hK₀Y hQ hrK hn2 hn3 hθ
  apply hdH
  apply hK₀H
  rw [heq]
  exact Subgroup.subset_closure ⟨hdY, hd3⟩

theorem false_of_exclusion627 (hF : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    {H Y : Subgroup G} (hHY : H ≤ Y) (hYH : Y ≤ Subgroup.normalizer (H : Set G))
    (hSQ : SQTKGroup ↥Y) {d : G} (hdY : d ∈ Y) (hdH : d ∉ H) (hd3 : orderOf d = 3)
    (ρ : ↥H →* Γ) (hρ : ∀ x : ↥H, ρ x = 1 ↔ (x : G) ∈ pCoreOf 2 H) {L : Subgroup Γ}
    (hsn : IsSubnormal L ρ.range) (hq : CFSG.IsQuasisimple ↥L) (hS : A318Exclusion ↥L) :
    False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hkerS : Group.IsSolvable ρ.ker := by
    have h2 : IsPGroup 2 ρ.ker := fun x => by
      obtain ⟨n, hn⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
        ⟨(x : ↥H), (hρ x).mp x.2⟩
      exact ⟨n, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hn))⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := h2.isNilpotent
    infer_instance
  obtain ⟨K₀, hK₀, hK₀L⟩ := exists_cComp_of_quasisimple627 ρ hkerS hsn hq
  obtain ⟨ψ, hψ, hker, hkO, h2el⟩ := a318Data627 hHY hYH ρ hρ hK₀ hK₀L
  have hK₀Y : K₀ ≤ Y := (le_of_mem_cComp hK₀).trans hHY
  have := hS.simple
  have h3 : 3 ∣ Nat.card ↥L := (show 3 ∣ 9 by norm_num).trans hS.nine_dvd_card
  obtain ⟨π, hπ⟩ := R3c2.exists_surjection_starImage hK₀Y ψ hψ hkO
  have hrK1 : 1 ≤ CFSG.Open.pRank 3 K₀ := by
    have h1 := R3c2.pRank_three_range_eq ψ (by
      intro h
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥ψ.ker) 3 h
      obtain ⟨n, hn⟩ := h2el x x.2
      have h2 := orderOf_dvd_of_pow_eq_one (show (x : ↥K₀) ^ 2 ^ n = 1 from hn)
      rw [Subgroup.orderOf_coe, hx] at h2
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2)
      omega)
    have h2 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥ψ.range) =
        CFSG.Open.pRank 3 (⊤ : Subgroup ↥L) := by
      rw [MonoidHom.range_eq_top.mpr hψ]
      exact CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) Subgroup.topEquiv
    rw [← pRank_top_subtype K₀, ← h1, h2]
    exact le_trans (by norm_num) hS.rank
  have hπi : Function.Injective π := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with hb | ht
    · exact (MonoidHom.ker_eq_bot_iff π).mp hb
    · exfalso
      refine R3c2.not_subsingleton_starImage hK₀Y hrK1 ⟨fun a b => ?_⟩
      obtain ⟨a', rfl⟩ := hπ a
      obtain ⟨b', rfl⟩ := hπ b
      rw [MonoidHom.mem_ker.1 (ht ▸ Subgroup.mem_top a'),
        MonoidHom.mem_ker.1 (ht ▸ Subgroup.mem_top b')]
  obtain ⟨hn2, hn3⟩ := R3c2.not_case2_case3_of_equiv_exclusion _
    (MulEquiv.ofBijective π ⟨hπi, hπ⟩).symm hS
  exact false_of_a318627 hF h36 h38 hHY hYH hSQ hdY hdH hd3 hK₀ hq ψ hψ hker h2el hS.rank
    (R3c2.closure_orderOf_three_eq_top_of_simple h3) h3 hn2 (fun h => absurd h hn3)

theorem false_of_hat627 (hF : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    {H Y : Subgroup G} (hHY : H ≤ Y) (hYH : Y ≤ Subgroup.normalizer (H : Set G))
    (hSQ : SQTKGroup ↥Y) {d : G} (hdY : d ∈ Y) (hdH : d ∉ H) (hd3 : orderOf d = 3)
    (ρ : ↥H →* Γ) (hρ : ∀ x : ↥H, ρ x = 1 ↔ (x : G) ∈ pCoreOf 2 H) {L : Subgroup Γ}
    (hsn : IsSubnormal L ρ.range) (hHat : IsHat ↥L ↥(alternatingGroup (Fin 6))) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq : CFSG.IsQuasisimple ↥L := hHat.1
  have hkerS : Group.IsSolvable ρ.ker := by
    have h2 : IsPGroup 2 ρ.ker := fun x => by
      obtain ⟨n, hn⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
        ⟨(x : ↥H), (hρ x).mp x.2⟩
      exact ⟨n, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hn))⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := h2.isNilpotent
    infer_instance
  obtain ⟨K₀, hK₀, hK₀L⟩ := exists_cComp_of_quasisimple627 ρ hkerS hsn hq
  obtain ⟨ψ, hψ, hker, hkO, h2el⟩ := a318Data627 hHY hYH ρ hρ hK₀ hK₀L
  have hK₀Y : K₀ ≤ Y := (le_of_mem_cComp hK₀).trans hHY
  have h3r : FFC.ThreeRank2 ↥L := FFC.threeRank2_hat hHat
  have h3 : 3 ∣ Nat.card ↥L := by
    rw [R3c2.card_of_isHat_alt6 hHat]
    norm_num
  have hgen : Subgroup.closure {y : ↥L | orderOf y = 3} = ⊤ := by
    by_contra hne
    have := R3c2.normal_closure_orderOf_eq (X := ↥L) 3
    have hle := CFSG.Quasithin.Vol2.Ch11.SecA.le_center_of_normal_ne_top hq hne
    obtain ⟨x, y, hx1, hx3, hy3, -, hyx⟩ := h3r
    have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
    have hy1 : y ≠ 1 := fun h => hyx (h ▸ Subgroup.one_mem _)
    have hyo : orderOf y = 3 := orderOf_eq_prime hy3 hy1
    have hxc : x ∈ Subgroup.center ↥L := hle (Subgroup.subset_closure hxo)
    have hyc : y ∈ Subgroup.center ↥L := hle (Subgroup.subset_closure hyo)
    have hz : Subgroup.zpowers x = Subgroup.center ↥L :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hxc)
        (by rw [hHat.2.1, Nat.card_zpowers, hxo])
    exact hyx (hz ▸ hyc)
  obtain ⟨π, hπ⟩ := R3c2.exists_surjection_starImage hK₀Y ψ hψ hkO
  have hrK1 : 1 ≤ CFSG.Open.pRank 3 K₀ := by
    have h1 := R3c2.pRank_three_range_eq ψ (by
      intro h
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥ψ.ker) 3 h
      obtain ⟨n, hn⟩ := h2el x x.2
      have h2 := orderOf_dvd_of_pow_eq_one (show (x : ↥K₀) ^ 2 ^ n = 1 from hn)
      rw [Subgroup.orderOf_coe, hx] at h2
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2)
      omega)
    have h2 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥ψ.range) =
        CFSG.Open.pRank 3 (⊤ : Subgroup ↥L) := by
      rw [MonoidHom.range_eq_top.mpr hψ]
      exact CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) Subgroup.topEquiv
    rw [← pRank_top_subtype K₀, ← h1, h2]
    exact le_trans (by norm_num) h3r.pRank_two_le
  have hcard := R3c2.card_quotient_hat hHat π hπ (R3c2.not_subsingleton_starImage hK₀Y hrK1)
  refine false_of_a318627 hF h36 h38 hHY hYH hSQ hdY hdH hd3 hK₀ hq ψ hψ hker h2el
    h3r.pRank_two_le hgen h3 ?_ ?_
  · rintro ⟨s, q, hmod, hPSL, -⟩
    exact R3c2.not_case2_of_card_hat6 hcard s q hmod hPSL
  · rintro - ⟨s, q, x, hSL, -⟩
    exact R3c2.not_isSLEps3_of_card_hat6 hcard s q hSL

end CFSG.Quasithin.H13
