module

public import CFSG.RankThree.PartTwo.Sec21.FF84S33
public import CFSG.RankThree.PartTwo.Sec21.FF84S23Sub
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84

open CFSG CFSG.RankThree.PartTwo.Sec21

variable {G : Type} [Group G] [Finite G] {b b₁ b₂ : G} {L B : Subgroup G}

theorem exists_zpow_mul_of_mem_sup_cen {x : G} {H : Subgroup G}
    (hH : H ≤ Subgroup.centralizer ({x} : Set G)) {a : G} (ha : a ∈ Subgroup.zpowers x ⊔ H) :
    ∃ i : ℤ, ∃ h ∈ H, a = x ^ i * h := by
  have hc : ∀ k ∈ H, x * k = k * x := fun k hk =>
    (Subgroup.mem_centralizer_singleton_iff.1 (hH hk)).symm
  have hle : Subgroup.zpowers x ≤ Subgroup.normalizer (H : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have : x * h * x⁻¹ = h := by rw [hc h hh]; group
      rw [this]; exact hh
    · intro hh
      have h3 : x⁻¹ * (x * h * x⁻¹) = (x * h * x⁻¹) * x⁻¹ := by
        have := hc (x * h * x⁻¹) hh
        calc x⁻¹ * (x * h * x⁻¹) = x⁻¹ * (x * h * x⁻¹) * x * x⁻¹ := by group
          _ = x⁻¹ * (x * (x * h * x⁻¹)) * x⁻¹ := by rw [this]; group
          _ = (x * h * x⁻¹) * x⁻¹ := by group
      have h2 : x⁻¹ * (x * h * x⁻¹) * x = h := by group
      rw [h3] at h2
      have h4 : (x * h * x⁻¹) * x⁻¹ * x = x * h * x⁻¹ := by group
      rw [h4] at h2
      rw [← h2]; exact hh
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right (Subgroup.zpowers x) H hle
  have ha' : a ∈ ((Subgroup.zpowers x ⊔ H : Subgroup G) : Set G) := ha
  rw [hset] at ha'
  obtain ⟨y, hy, h, hh, rfl⟩ := ha'
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  exact ⟨i, h, hh, rfl⟩

theorem mem_zpowers_of_cen_cen (hs : FF84Sec3 b L B b₁ b₂) (hO : Opp 3 (Cen b) = ⊥)
    (hZ : Subgroup.center L = ⊥) {y : G} (hy : y ∈ Cen b) (hyL : ∀ k ∈ L, y * k = k * y) :
    y ∈ Subgroup.zpowers b := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C : Subgroup G := Cen b with hC
  set Y : Subgroup G := C ⊓ CenS L with hY
  have hLC : L ≤ C := hs.hyp.hLC
  have hLN : C ≤ Nor L := hs.hyp.hLN
  have hbC : b ∈ C := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hkey : ∀ c ∈ C, ∀ y ∈ Y, c * y * c⁻¹ ∈ Y := by
    intro c hc y hy
    obtain ⟨hyC, hyL⟩ := Subgroup.mem_inf.1 hy
    refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hc hyC) (inv_mem hc), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hk' : c⁻¹ * k * c ∈ L := by
      have := (Subgroup.mem_normalizer_iff.1 (hLN (inv_mem hc)) k).1 hk
      simpa using this
    have hcomm := Subgroup.mem_centralizer_iff.1 hyL (c⁻¹ * k * c) hk'
    calc k * (c * y * c⁻¹) = c * ((c⁻¹ * k * c) * y) * c⁻¹ := by group
      _ = c * (y * (c⁻¹ * k * c)) * c⁻¹ := by rw [hcomm]
      _ = c * y * c⁻¹ * k := by group
  have hCY : C ≤ Subgroup.normalizer (Y : Set G) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hkey c hc y hy, fun hy => ?_⟩
    have := hkey c⁻¹ (inv_mem hc) _ hy
    have e : c⁻¹ * (c * y * c⁻¹) * c⁻¹⁻¹ = y := by group
    rwa [e] at this
  have hYC : Y ≤ C := inf_le_left
  have hYn : (Y.subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYC).2 hCY
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 3 B C := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    obtain ⟨h1, h2, h3⟩ := hs.sylB
    exact ⟨h1, h2, (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 h3⟩
  obtain ⟨Q, hQ⟩ := hSyl.inf_of_le_normalizer hYC hCY
  have hbY : b ∈ Y := Subgroup.mem_inf.2 ⟨hbC, Subgroup.mem_centralizer_iff.2 fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.1 (hLC hk)⟩
  have hBY : B ⊓ Y ≤ Subgroup.zpowers b := by
    intro y hy
    obtain ⟨hyB, hyY⟩ := Subgroup.mem_inf.1 hy
    obtain ⟨hyC, hyL'⟩ := Subgroup.mem_inf.1 hyY
    have hK : B ≤ Subgroup.zpowers b ⊔ Subgroup.closure ({b₁, b₂} : Set G) :=
      B_le_of_mem hs (Subgroup.mem_sup_left (Subgroup.mem_zpowers b))
        (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp)))
        (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp)))
    have hQcen : Subgroup.closure ({b₁, b₂} : Set G) ≤ Cen b := by
      rw [Subgroup.closure_le]
      intro z hz
      rcases hz with rfl | hz
      · exact Subgroup.mem_centralizer_singleton_iff.2
          (comm_of_mem_B hs (mem_B_b₁ hs) (mem_B_b hs)).eq
      · rw [Set.mem_singleton_iff.1 hz]
        exact Subgroup.mem_centralizer_singleton_iff.2
          (comm_of_mem_B hs (mem_B_b₂ hs) (mem_B_b hs)).eq
    obtain ⟨i, h, hh, hyeq⟩ := exists_zpow_mul_of_mem_sup_cen hQcen (hK hyB)
    have hhL : h ∈ L := by
      have : h ∈ B ⊓ L := by rw [hs.gen]; exact hh
      exact (Subgroup.mem_inf.1 this).2
    have hh1 : h = 1 := by
      have hcen : (⟨h, hhL⟩ : ↥L) ∈ Subgroup.center ↥L := by
        rw [Subgroup.mem_center_iff]
        intro g
        apply Subtype.ext
        show (g : G) * h = h * (g : G)
        have hgb : Commute (g : G) b :=
          Subgroup.mem_centralizer_singleton_iff.1 (hLC g.2)
        have hgy : Commute (g : G) y := Subgroup.mem_centralizer_iff.1 hyL' g g.2
        have : h = (b ^ i)⁻¹ * y := by rw [hyeq]; group
        rw [this]
        exact (((hgb.zpow_right i).inv_right).mul_right hgy).eq
      rw [hZ, Subgroup.mem_bot] at hcen
      exact congrArg Subtype.val hcen
    rw [hyeq, hh1, mul_one]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers b) i
  have hBYeq : B ⊓ Y = Subgroup.zpowers b :=
    le_antisymm hBY (le_inf (Subgroup.zpowers_le.2 (mem_B_b hs)) (Subgroup.zpowers_le.2 hbY))
  have hS : (Q : Subgroup ↥Y) ≤ CFSG.centerIn (G := ↥Y) (Subgroup.normalizer (Q : Subgroup ↥Y)) := by
    intro x hx
    rw [CFSG.centerIn, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    refine ⟨Subgroup.le_normalizer hx, ?_⟩
    intro h _
    apply Subtype.ext
    have hxb : (x : G) ∈ Subgroup.zpowers b := by
      rw [← hBYeq, ← hQ]
      exact Subgroup.mem_map.2 ⟨x, hx, rfl⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hxb
    have hhb : Commute ((h : ↥Y) : G) b :=
      Subgroup.mem_centralizer_singleton_iff.1 (hYC h.2)
    show (h : G) * (x : G) = (x : G) * (h : G)
    rw [← hk]
    exact (hhb.zpow_right k).eq
  obtain ⟨N, hN, hcop, hquot⟩ :=
    CFSG.exists_normal_coprime_subgroup_and_pgroup_quotient_of_sylow_le_center_normalizer
      (G := ↥Y) 3 Q hS
  have hNle : N ≤ CFSG.pPrimeCore 3 ↥Y := le_sSup ⟨hN, hcop⟩
  have hmap := map_pPrimeCore_le_of_normal' (p := 3) hYC hYn
  have hmap' : (CFSG.pPrimeCore 3 ↥Y).map Y.subtype ≤ ⊥ := by
    refine hmap.trans ?_
    exact hO.le
  have hN1 : N = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : (x : G) ∈ (CFSG.pPrimeCore 3 ↥Y).map Y.subtype :=
      Subgroup.mem_map.2 ⟨x, hNle hx, rfl⟩
    have h2 := hmap' h1
    rw [Subgroup.mem_bot] at h2
    exact Subgroup.mem_bot.2 (Subtype.ext h2)
  subst hN1
  have hY3 : IsPGroup 3 ↥Y := hquot.of_equiv QuotientGroup.quotientBot
  obtain ⟨n, hn⟩ := hY3.index (Q : Subgroup ↥Y)
  have hn0 : n = 0 := by
    by_contra hne
    exact Q.not_dvd_index (hn ▸ dvd_pow_self 3 hne)
  have hQtop : (Q : Subgroup ↥Y) = ⊤ := Subgroup.index_eq_one.1 (by rw [hn, hn0, pow_zero])
  have hyY : y ∈ Y := Subgroup.mem_inf.2 ⟨hy, Subgroup.mem_centralizer_iff.2 fun k hk =>
    (hyL k hk).symm⟩
  rw [← hBYeq, ← hQ]
  exact Subgroup.mem_map.2 ⟨⟨y, hyY⟩, by rw [hQtop]; trivial, rfl⟩

end CFSG.RankThree.PartTwo.Sec21.FF84
