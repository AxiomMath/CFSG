module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.Monster.B

open Subgroup

variable {G : Type*} [Group G]

theorem map_center_eq_inf_centralizer (K : Subgroup G) :
    (center K).map K.subtype = K ⊓ centralizer (K : Set G) := by
  ext y
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine mem_inf.2 ⟨w.2, mem_centralizer_iff.2 fun s hs => ?_⟩
    exact congrArg Subtype.val ((mem_center_iff.1 hw) ⟨s, hs⟩)
  · intro hy
    obtain ⟨hyK, hy⟩ := mem_inf.1 hy
    refine ⟨⟨y, hyK⟩, mem_center_iff.2 fun s => Subtype.ext ?_, rfl⟩
    exact (mem_centralizer_iff.1 hy) s s.2

theorem mem_sylow_smul_iff {p : ℕ} {c y : G} {S : Sylow p G} :
    y ∈ ((c • S : Sylow p G) : Subgroup G) ↔ c⁻¹ * y * c ∈ (S : Subgroup G) := by
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp [MulAut.smul_def, MulAut.inv_def, mul_assoc]

variable [Finite G] {p : ℕ} [hp : Fact p.Prime]

theorem mem_zpowers_of_mem_zpowers_of_prime {z w : G} (hz : orderOf z = p) (hw : w ∈ zpowers z)
    (hw1 : w ≠ 1) : z ∈ zpowers w := by
  have hle : zpowers w ≤ zpowers z := (zpowers_le).2 hw
  have hdvd : orderOf w ∣ p := hz ▸ orderOf_dvd_of_mem_zpowers hw
  have hw' : orderOf w ≠ 1 := fun h => hw1 (orderOf_eq_one_iff.1 h)
  have hwp : orderOf w = p := ((Nat.dvd_prime hp.out).1 hdvd).resolve_left hw'
  have heq : zpowers w = zpowers z :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hwp, hz])
  rw [heq]
  exact mem_zpowers z

private theorem le_centralizer_of_le {z : G} (hz : orderOf z = p) {Q : Subgroup G}
    (hCQ : centralizer {z} ⊓ centralizer (Q : Set G) = zpowers z) (S : Subgroup G)
    (hSp : IsPGroup p S) (hzS : z ∈ S) (hQS : Q ≤ S) :
    S ≤ centralizer {z} ∧ S ⊓ centralizer (S : Set G) = zpowers z := by
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz
    exact hp.out.one_lt.ne hz
  have hZS : S ⊓ centralizer (S : Set G) ≤ zpowers z := by
    intro w hw
    obtain ⟨-, hwc⟩ := mem_inf.1 hw
    rw [← hCQ]
    refine mem_inf.2 ⟨?_, ?_⟩
    · rw [mem_centralizer_singleton_iff]
      exact ((mem_centralizer_iff.1 hwc) z hzS).symm
    · rw [mem_centralizer_iff]
      intro q hq
      exact (mem_centralizer_iff.1 hwc) q (hQS hq)
  have hSnt : Nontrivial S := ⟨⟨⟨z, hzS⟩, 1, fun h => hz1 (congrArg Subtype.val h)⟩⟩
  have hcnt := hSp.center_nontrivial
  obtain ⟨w, hw1⟩ := exists_ne (1 : center S)
  have hwmem : ((w : S) : G) ∈ S ⊓ centralizer (S : Set G) := by
    rw [← map_center_eq_inf_centralizer]
    exact ⟨w, w.2, rfl⟩
  have hw1' : ((w : S) : G) ≠ 1 := by
    intro h
    apply hw1
    exact Subtype.ext (Subtype.ext h)
  have hzw := mem_zpowers_of_mem_zpowers_of_prime hz (hZS hwmem) hw1'
  have hzc : z ∈ S ⊓ centralizer (S : Set G) := (zpowers_le.2 hwmem) hzw
  have hSH : S ≤ centralizer {z} := by
    intro s hs
    rw [mem_centralizer_singleton_iff]
    exact (mem_centralizer_iff.1 (mem_inf.1 hzc).2) s hs
  exact ⟨hSH, le_antisymm hZS (zpowers_le.2 hzc)⟩

theorem prime_centralizer_sylow_control {z : G} (hz : orderOf z = p) {Q : Subgroup G}
    (hQH : Q ≤ centralizer {z}) (hQn : (Q.subgroupOf (centralizer {z})).Normal)
    (hQp : IsPGroup p Q) (hZQ : (center Q).map Q.subtype = zpowers z)
    (hCQ : centralizer {z} ⊓ centralizer (Q : Set G) = zpowers z) :
    (∀ P : Sylow p (centralizer {z}), ∃ S : Sylow p G,
      (S : Subgroup G) = (P : Subgroup (centralizer {z})).map (centralizer {z}).subtype ∧
      (center (S : Subgroup G)).map (S : Subgroup G).subtype = zpowers z) ∧
    Nat.Coprime (centralizer {z}).index p ∧
    (∀ g : G, (∃ n : ℕ, g ^ p ^ n = 1) → ∃ c : G, c * g * c⁻¹ ∈ centralizer {z}) ∧
    (∀ S : Sylow p G, ∃ c : G,
      (center (S : Subgroup G)).map (S : Subgroup G).subtype = zpowers (c * z * c⁻¹)) := by
  have hzQ : z ∈ Q := by
    have : z ∈ (center Q).map Q.subtype := by rw [hZQ]; exact mem_zpowers z
    obtain ⟨q, -, hq⟩ := this
    rw [← hq]
    exact q.2
  have hmain : ∀ P : Sylow p (centralizer {z}), ∃ S : Sylow p G,
      (S : Subgroup G) = (P : Subgroup (centralizer {z})).map (centralizer {z}).subtype ∧
      (S : Subgroup G) ≤ centralizer {z} ∧
      (S : Subgroup G) ⊓ centralizer ((S : Subgroup G) : Set G) = zpowers z := by
    intro P
    have hQp' : IsPGroup p (Q.subgroupOf (centralizer {z})) :=
      hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQH).symm
    have hQP : Q.subgroupOf (centralizer {z}) ≤ P :=
      @IsPGroup.le_sylow_of_normal _ _ _ _ hQn hQp' P
    have hQP' : Q ≤ (P : Subgroup (centralizer {z})).map (centralizer {z}).subtype :=
      fun q hq => ⟨⟨q, hQH hq⟩, hQP (by rwa [mem_subgroupOf]), rfl⟩
    obtain ⟨S, hS⟩ := (P.isPGroup'.map (centralizer {z}).subtype).exists_le_sylow
    obtain ⟨hSH, hSZ⟩ := le_centralizer_of_le hz hCQ (S : Subgroup G) S.isPGroup'
      (hS (hQP' hzQ)) (hQP'.trans hS)
    have hSp : IsPGroup p ((S : Subgroup G).subgroupOf (centralizer {z})) :=
      S.isPGroup'.of_equiv (Subgroup.subgroupOfEquivOfLe hSH).symm
    have hPS : (P : Subgroup (centralizer {z})) ≤ (S : Subgroup G).subgroupOf (centralizer {z}) :=
      fun x hx => by
        rw [mem_subgroupOf]
        exact hS ⟨x, hx, rfl⟩
    have heq := P.is_maximal' hSp hPS
    refine ⟨S, ?_, hSH, hSZ⟩
    rw [← heq, Subgroup.map_subgroupOf_eq_of_le hSH]
  obtain ⟨S₀, -, hS₀H, hS₀Z⟩ := hmain default
  refine ⟨fun P => ?_, ?_, ?_, ?_⟩
  · obtain ⟨S, hS, -, hSZ⟩ := hmain P
    exact ⟨S, hS, by rw [map_center_eq_inf_centralizer, hSZ]⟩
  ·
    have h1 := S₀.not_dvd_index
    have h2 : (centralizer {z}).index ∣ (S₀ : Subgroup G).index := Subgroup.index_dvd_of_le hS₀H
    exact (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp.out).2
      fun h => h1 (h.trans h2)))
  ·
    intro g hg
    have hgp : IsPGroup p (zpowers g) := by
      obtain ⟨n, hn⟩ := hg
      intro x
      obtain ⟨k, hk⟩ := mem_zpowers_iff.1 x.2
      refine ⟨n, Subtype.ext ?_⟩
      rw [SubgroupClass.coe_pow, ← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
        zpow_natCast, hn, one_zpow, OneMemClass.coe_one]
    obtain ⟨S, hS⟩ := hgp.exists_le_sylow
    obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G S₀ S
    refine ⟨c⁻¹, hS₀H ?_⟩
    have hgS : g ∈ ((c • S₀ : Sylow p G) : Subgroup G) := by rw [hc]; exact hS (mem_zpowers g)
    rw [mem_sylow_smul_iff] at hgS
    simpa using hgS
  ·
    intro S
    obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G S₀ S
    refine ⟨c, ?_⟩
    rw [map_center_eq_inf_centralizer, ← hc]
    ext y
    rw [mem_inf, mem_centralizer_iff, mem_sylow_smul_iff]
    have hcen : (∀ h ∈ (((c • S₀ : Sylow p G) : Subgroup G) : Set G), h * y = y * h) ↔
        c⁻¹ * y * c ∈ centralizer ((S₀ : Subgroup G) : Set G) := by
      rw [mem_centralizer_iff]
      constructor
      · intro hy s hs
        have hcs : c⁻¹ * (c * s * c⁻¹) * c = s := by group
        have := hy (c * s * c⁻¹) (by rw [SetLike.mem_coe, mem_sylow_smul_iff, hcs]; exact hs)
        calc s * (c⁻¹ * y * c) = c⁻¹ * ((c * s * c⁻¹) * y) * c := by group
          _ = c⁻¹ * (y * (c * s * c⁻¹)) * c := by rw [this]
          _ = c⁻¹ * y * c * s := by group
      · intro hy h hh
        rw [SetLike.mem_coe, mem_sylow_smul_iff] at hh
        have := hy _ hh
        calc h * y = c * ((c⁻¹ * h * c) * (c⁻¹ * y * c)) * c⁻¹ := by group
          _ = c * ((c⁻¹ * y * c) * (c⁻¹ * h * c)) * c⁻¹ := by rw [this]
          _ = y * h := by group
    rw [hcen, ← mem_inf, hS₀Z, mem_zpowers_iff, mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      rw [conj_zpow, hk]
      group
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      rw [← hk, conj_zpow]
      group

end CFSG.Monster.B
