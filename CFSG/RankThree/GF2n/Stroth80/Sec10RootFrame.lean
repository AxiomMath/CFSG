module

public import CFSG.RankThree.GF2n.Stroth80.Sec10Swap

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Sec10Hyp.exists_frame (h34 : Stroth34Statement) (hspread : StrothNoA2SpreadStatement)
    {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n) {W : Subgroup G}
    (hW : ∃ g : G, W = conjSubgroup g Z) (hBW : B ≤ QB W) (hne : B ≠ W) :
    ∃ hcW : Ctx (Subgroup.normalizer (W : Set G)) (QB W) W B, Sec10Hyp hcW n := by
  obtain ⟨k, hkZ, hkB⟩ := H.exists_conj_pair h34 hspread hW hc.conj hBW hne
  have hQk : conjSubgroup k Q = QB W := by rw [← Smith81.QB_conj_eq hc.hyp k, hkZ]
  have hMk : conjSubgroup k M = Subgroup.normalizer (W : Set G) := by
    rw [← Smith81.normalizer_conj_eq hc.hyp k, hkZ]
  obtain ⟨b, hb⟩ := hc.conj
  let hcW : Ctx (Subgroup.normalizer (W : Set G)) (QB W) W B :=
    { hyp := by rw [← hMk, ← hQk, ← hkZ]; exact hc.hyp.conj k
      conj := ⟨b * k⁻¹, by
        rw [← hkZ, conjSubgroup_conjSubgroup, show b * k⁻¹ * k = b by group, hb]⟩
      le := hBW
      ne := hne }
  exact ⟨hcW, (H.conjG k).of_eq hcW hMk hQk hkZ hkB⟩

omit [Finite G] in
theorem isRoot_conj_iff {Y : Subgroup G} {g₀ : G} (hY : Y = conjSubgroup g₀ Z) {a : G} :
    (∃ g : G, ∃ y ∈ Y, y ≠ 1 ∧ g * y * g⁻¹ = a) ↔
      ∃ g : G, ∃ z ∈ Z, z ≠ 1 ∧ g * z * g⁻¹ = a := by
  subst hY
  constructor
  · rintro ⟨g, y, hy, hy1, rfl⟩
    refine ⟨g * g₀, g₀⁻¹ * y * g₀, mem_conjSubgroup.mp hy, fun h => hy1 ?_, by group⟩
    calc y = g₀ * (g₀⁻¹ * y * g₀) * g₀⁻¹ := by group
      _ = 1 := by rw [h]; group
  · rintro ⟨g, z, hz, hz1, rfl⟩
    refine ⟨g * g₀⁻¹, g₀ * z * g₀⁻¹, ?_, fun h => hz1 ?_, by group⟩
    · rw [mem_conjSubgroup, show g₀⁻¹ * (g₀ * z * g₀⁻¹) * g₀ = z by group]
      exact hz
    · calc z = g₀⁻¹ * (g₀ * z * g₀⁻¹) * g₀ := by group
        _ = 1 := by rw [h]; group

theorem mem_QB_conj_of_mem_centralizer {Y : Subgroup G} {c a : G} (ha : a ∈ QB Y)
    (hac : a ∈ Subgroup.centralizer ({c} : Set G)) : a ∈ QB (conjSubgroup c Y) := by
  rw [QB_conj, mem_conjSubgroup]
  have h : a * c = c * a := Subgroup.mem_centralizer_singleton_iff.mp hac
  rw [show c⁻¹ * a * c = a by rw [mul_assoc, h, ← mul_assoc, inv_mul_cancel, one_mul]]
  exact ha

end CFSG.RankThree.GF2n.Stroth80
