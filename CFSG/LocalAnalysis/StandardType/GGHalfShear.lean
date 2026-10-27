module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs

public section

namespace CFSG.StandardType.GGHalf

open CFSG.Assembly

variable {G : Type} [Group G] [Finite G]

theorem not_noTransvection_of_shear {Bs : Subgroup G}
    (hcomm : ∀ b ∈ Bs, ∀ c ∈ Bs, b * c = c * b) (hexp : ∀ b ∈ Bs, b ^ 3 = 1)
    {n a : G} (hn : n ∈ Subgroup.normalizer (Bs : Set G)) (ha : a ∈ Bs) (ha1 : a ≠ 1)
    (hna : n * a * n⁻¹ = a)
    (himg : ∀ b ∈ Bs, n * b * n⁻¹ * b⁻¹ ∈ Subgroup.zpowers a)
    (hmove : ∃ b ∈ Bs, n * b * n⁻¹ ≠ b) :
    ¬ GGNoTransvection 3 Bs := by
  have hc : ∀ x y : ↥Bs, x * y = y * x := fun x y => Subtype.ext (hcomm x x.2 y y.2)
  letI : CommGroup ↥Bs := CommGroup.mk hc
  let φ : MulAut ↥Bs := Bs.normalizerMonoidHom ⟨n, hn⟩
  have hφcoe : ∀ b : ↥Bs, ((φ b : ↥Bs) : G) = n * b * n⁻¹ :=
    fun b => Subgroup.normalizerMonoidHom_apply_apply_coe (H := Bs) ⟨n, hn⟩ b
  have hφa : φ ⟨a, ha⟩ = ⟨a, ha⟩ := by
    apply Subtype.ext
    rw [hφcoe]
    change n * a * n⁻¹ = a
    exact hna
  let ψ : ↥Bs →* ↥Bs := MonoidHom.mk' (fun b => φ b / b) (fun b c => by
    rw [map_mul]
    exact (div_mul_div_comm (φ b) b (φ c) c).symm)
  have hψapply : ∀ b : ↥Bs, ψ b = φ b / b := fun _ => rfl
  have hψcoe : ∀ b : ↥Bs, ((ψ b : ↥Bs) : G) = n * b * n⁻¹ * b⁻¹ := by
    intro b
    rw [hψapply, div_eq_mul_inv]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hφcoe b]
  have hfixS : ∀ z : ↥Bs, (z : G) ∈ Subgroup.zpowers a → φ z = z := by
    intro z hz
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
    have haz : (⟨a, ha⟩ : ↥Bs) ^ k = z := by
      apply Subtype.ext
      simpa using hk
    calc φ z = φ ((⟨a, ha⟩ : ↥Bs) ^ k) := by rw [haz]
      _ = (φ ⟨a, ha⟩) ^ k := map_zpow φ.toMonoidHom ⟨a, ha⟩ k
      _ = (⟨a, ha⟩ : ↥Bs) ^ k := by rw [hφa]
      _ = z := haz
  have hSle : Subgroup.zpowers a ≤ Bs := Subgroup.zpowers_le.mpr ha
  let P : Subgroup ↥Bs := (Subgroup.zpowers a).subgroupOf Bs
  have hPcard : Nat.card P = 3 := by
    have h1 : Nat.card P = Nat.card (Subgroup.zpowers a) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSle).toEquiv
    rw [h1, Nat.card_zpowers]
    exact orderOf_eq_prime (hexp a ha) ha1
  have hrange_le : ψ.range ≤ P := by
    rintro y ⟨b, rfl⟩
    rw [Subgroup.mem_subgroupOf, hψcoe b]
    exact himg b b.2
  have hne : ψ.range ≠ ⊥ := by
    intro hbot
    obtain ⟨b, hb, hbne⟩ := hmove
    have hmem : ψ ⟨b, hb⟩ ∈ (⊥ : Subgroup ↥Bs) := by
      rw [← hbot]
      exact ⟨⟨b, hb⟩, rfl⟩
    rw [Subgroup.mem_bot] at hmem
    have hfix : φ ⟨b, hb⟩ = ⟨b, hb⟩ := div_eq_one.mp hmem
    exact hbne (by
      calc n * b * n⁻¹ = ((φ ⟨b, hb⟩ : ↥Bs) : G) := (hφcoe ⟨b, hb⟩).symm
        _ = b := by simpa using congrArg Subtype.val hfix)
  have hcard_ne_one : Nat.card ψ.range ≠ 1 := fun h =>
    hne ((Subgroup.card_eq_one).mp h)
  have hψrange : Nat.card ψ.range = 3 := by
    have hdiv : Nat.card ψ.range ∣ 3 := by
      rw [← hPcard]
      exact Subgroup.card_dvd_of_le hrange_le
    rcases (show Nat.Prime 3 by norm_num).eq_one_or_self_of_dvd (Nat.card ψ.range) hdiv with h | h
    · exact absurd h hcard_ne_one
    · exact h
  have hker_fix : Nat.card {b : ↥Bs // φ b = b} = Nat.card ψ.ker := by
    refine Nat.card_congr ?_
    refine
      { toFun := fun b => ⟨b.1, ?_⟩
        invFun := fun b => ⟨b.1, ?_⟩
        left_inv := fun b => by ext; rfl
        right_inv := fun b => by ext; rfl }
    · rw [MonoidHom.mem_ker]
      change φ b.1 / b.1 = 1
      rw [div_eq_one]
      exact b.2
    · have hb : b.1 ∈ ψ.ker := b.2
      rw [MonoidHom.mem_ker] at hb
      change φ b.1 / b.1 = 1 at hb
      rw [div_eq_one] at hb
      exact hb
  have hcard_eq : Nat.card {b : ↥Bs // φ b = b} * 3 = Nat.card ↥Bs := by
    rw [hker_fix, ← hψrange]
    exact Subgroup.card_ker_mul_card_range ψ
  have hsecond : ∀ b : ↥Bs, φ (b⁻¹ * φ b) = b⁻¹ * φ b := by
    intro b
    have hmem : ((b⁻¹ * φ b : ↥Bs) : G) ∈ Subgroup.zpowers a := by
      have heq : b⁻¹ * φ b = ψ b := by
        rw [hψapply, div_eq_mul_inv]
        exact mul_comm _ _
      rw [heq]
      exact Subgroup.mem_subgroupOf.mp (hrange_le ⟨b, rfl⟩)
    exact hfixS (b⁻¹ * φ b) hmem
  intro hNo
  exact hNo φ ⟨n, Subgroup.mem_top n, hn, hφcoe⟩ ⟨hcard_eq, hsecond⟩

end CFSG.StandardType.GGHalf

end
