module

public import CFSG.Walter.W67.Section4.Prop41A
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Hall.theorem_14_4_2
public import CFSG.Walter.W67.Section5.Sylow52
public import CFSG.Walter.W67.W1Basic

public section

namespace CFSG.Walter.W67.Sec6

variable {G : Type} [Group G] [Finite G]

open BenderSuzuki.External

omit [Finite G] in
theorem exists_mul_of_mem_sup {K₀ E : Subgroup G} (hE : E ≤ Subgroup.normalizer (K₀ : Set G))
    {x : G} (hx : x ∈ E ⊔ K₀) : ∃ a ∈ E, ∃ k ∈ K₀, a * k = x := by
  rw [sup_comm] at hx
  obtain ⟨k, hk, a, ha, rfl⟩ := (mem_sup_iff_of_le_normalizer hE).mp hx
  refine ⟨a, ha, a⁻¹ * k * a, ?_, by group⟩
  have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hE ha)) k).mp hk
  simpa using this

omit [Finite G] in
theorem exists_pow_mul_eq {K₀ : Subgroup G} {a k : G}
    (ha : a ∈ Subgroup.normalizer (K₀ : Set G)) (hk : k ∈ K₀) (n : ℕ) :
    ∃ k' ∈ K₀, (a * k) ^ n = a ^ n * k' := by
  induction n with
  | zero => exact ⟨1, K₀.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨k', hk', h⟩ := ih
    refine ⟨a⁻¹ * k' * a * k, K₀.mul_mem ?_ hk, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ ha) k').mp hk'
      simpa using this
    · rw [pow_succ, h, pow_succ]
      group

theorem hallPResidual_ne_top {r : ℕ} [Fact r.Prime] {N K₀ H H₃ P₀ : Subgroup G}
    (hNK₀ : N ≤ Subgroup.normalizer (K₀ : Set G)) (hK₀N : K₀ ≤ N) (hN : N ≤ (N ⊓ H) ⊔ K₀)
    (hpow : ∀ x ∈ H, x ^ Nat.card P₀ ∈ H₃) (hint : N ⊓ H ⊓ K₀ ≤ H₃) (hP₀N : P₀ ≤ N ⊓ H)
    (hP₀ : P₀ ⊓ H₃ = ⊥) (hP₀1 : P₀ ≠ ⊥) (hP₀r : IsPGroup r P₀) :
    hallPResidual r N ≠ ⊤ := by
  have hKN : N ⊓ H ⊓ H₃ ≤ Subgroup.normalizer (K₀ : Set G) :=
    (inf_le_left.trans inf_le_left).trans hNK₀
  have hNH : N ⊓ H ≤ Subgroup.normalizer (K₀ : Set G) := inf_le_left.trans hNK₀
  obtain ⟨j, hj⟩ := hP₀r.exists_card_eq
  have hcop : ∀ g ∈ N, Nat.Coprime r (orderOf g) → g ∈ (N ⊓ H ⊓ H₃) ⊔ K₀ := by
    intro g hg hgr
    obtain ⟨a, ha, k, hk, rfl⟩ := exists_mul_of_mem_sup hNH (hN hg)
    set m := orderOf (a * k) with hm
    obtain ⟨k', hk', h1⟩ := exists_pow_mul_eq (hNH ha) hk m
    rw [pow_orderOf_eq_one] at h1
    have ham : a ^ m ∈ K₀ := by
      have : a ^ m = k'⁻¹ := eq_inv_of_mul_eq_one_left h1.symm
      rw [this]
      exact K₀.inv_mem hk'
    have ham3 : a ^ m ∈ H₃ := hint ⟨(N ⊓ H).pow_mem ha m, ham⟩
    have hap3 : a ^ Nat.card P₀ ∈ H₃ := hpow a (Subgroup.mem_inf.mp ha).2
    have hgcd : Nat.gcd m (Nat.card P₀) = 1 := by
      rw [hj]
      exact Nat.Coprime.pow_right j (Nat.coprime_comm.mp hgr)
    have ha3 : a ∈ H₃ := by
      have hb := Nat.gcd_eq_gcd_ab m (Nat.card P₀)
      rw [hgcd, Nat.cast_one] at hb
      have e : a = (a ^ m) ^ (Nat.gcdA m (Nat.card P₀)) *
          (a ^ Nat.card P₀) ^ (Nat.gcdB m (Nat.card P₀)) := by
        rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, ← hb,
          zpow_one]
      rw [e]
      exact H₃.mul_mem (H₃.zpow_mem ham3 _) (H₃.zpow_mem hap3 _)
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨ha, ha3⟩) (Subgroup.mem_sup_right hk)
  have hle : hallPResidual r N ≤ ((N ⊓ H ⊓ H₃) ⊔ K₀).subgroupOf N := by
    rw [hallPResidual, Subgroup.closure_le]
    intro g hg
    have hg' : Nat.Coprime r (orderOf (g : G)) := by rwa [Subgroup.orderOf_coe]
    exact hcop g g.2 hg'
  intro htop
  obtain ⟨p, hp, hp1⟩ := (Subgroup.bot_or_exists_ne_one P₀).resolve_left hP₀1
  have hpN₁ : p ∈ (N ⊓ H ⊓ H₃) ⊔ K₀ := by
    have : (⟨p, (Subgroup.mem_inf.mp (hP₀N hp)).1⟩ : N) ∈
        ((N ⊓ H ⊓ H₃) ⊔ K₀).subgroupOf N := hle (htop ▸ Subgroup.mem_top _)
    exact this
  obtain ⟨a, ha, k, hk, hak⟩ := exists_mul_of_mem_sup hKN hpN₁
  have haH : a ∈ H := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp ha).1).2
  have haN : a ∈ N := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp ha).1).1
  have hkH : k ∈ H := by
    have e : k = a⁻¹ * p := by rw [← hak]; group
    rw [e]
    exact H.mul_mem (H.inv_mem haH) (Subgroup.mem_inf.mp (hP₀N hp)).2
  have hk3 : k ∈ H₃ := hint ⟨⟨hK₀N hk, hkH⟩, hk⟩
  have hp3 : p ∈ H₃ := by
    rw [← hak]
    exact H₃.mul_mem (Subgroup.mem_inf.mp ha).2 hk3
  have : p ∈ P₀ ⊓ H₃ := ⟨hp, hp3⟩
  rw [hP₀, Subgroup.mem_bot] at this
  exact hp1 this

theorem hallPResidual_normalizer_eq_top {r : ℕ} [Fact r.Prime] (hperf : commutator G = ⊤)
    (P : Sylow r G) {W : Subgroup G} (hweak : WeaklyClosedIn (P : Subgroup G) W)
    (hcond : (∀ u z : G, u ∈ W → z ∈ W → engelSymbol (r - 1) u z = 1) ∨
      W.subgroupOf (P : Subgroup G) ≤ Subgroup.upperCentralSeries (P : Subgroup G) (r - 1)) :
    hallPResidual r (Subgroup.normalizer (W : Set G)) = ⊤ := by
  have hHW := hallWielandt_residual_intersection r P W _ rfl hweak (Or.inr hcond)
  have h1 := hHW.1
  rw [Sec52.hallPResidual_eq_top hperf, inf_top_eq] at h1
  apply Subgroup.map_injective (Subgroup.normalizer (W : Set G)).subtype_injective
  rw [h1, Subgroup.map_top, Subgroup.range_subtype]

omit [Finite G] in
theorem engelSymbol_eq_one_of_comm {r : ℕ} (hr : 3 ≤ r) {W : Subgroup G}
    (hW : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) :
    ∀ u z : G, u ∈ W → z ∈ W → engelSymbol (r - 1) u z = 1 := by
  intro u z hu hz
  have e : r - 1 - 1 = (r - 3) + 1 := by omega
  change iteratedInverseFirstCommutator (r - 1 - 1) u z = 1
  rw [e]
  exact Sec52.iterated_eq_one (hW u hu z hz) _

theorem false_of_metacyclic {r : ℕ} [Fact r.Prime] (hperf : commutator G = ⊤) (hr2 : r ≠ 2)
    {S C : Subgroup G} (hScard : Nat.card S = r ^ (Nat.card G).factorization r)
    (hCS : C ≤ S) (hCn : S ≤ Subgroup.normalizer (C : Set G)) (hC : IsCyclic C)
    {g : G} (hgS : g ∈ S) (hgen : S ≤ C ⊔ Subgroup.zpowers g)
    (hnc : ¬ ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) : False := by
  set P : Sylow r G := Sylow.ofCard S hScard with hP
  have hPS : (P : Subgroup G) = S := Sylow.coe_ofCard _ _
  apply false_of_perfect_of_metacyclic hperf hr2 P
  · intro hab
    apply hnc
    intro a ha b hb
    rw [← hPS] at ha hb
    exact congrArg Subtype.val (hab.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  · rw [hPS]
    have hnorm : (C.subgroupOf S).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hCS).mpr hCn
    refine ⟨C.subgroupOf S, hnorm, ?_, ?_⟩
    · exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hCS).symm.toMonoidHom
        (Subgroup.subgroupOfEquivOfLe hCS).symm.surjective
    · refine ⟨⟨QuotientGroup.mk ⟨g, hgS⟩, fun x => ?_⟩⟩
      obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective x
      have hgN : Subgroup.zpowers g ≤ Subgroup.normalizer (C : Set G) :=
        Subgroup.zpowers_le.mpr (hCn hgS)
      obtain ⟨c, hc, w, hw, hcw⟩ := (mem_sup_iff_of_le_normalizer hgN).mp (hgen s.2)
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      refine ⟨n, ?_⟩
      beta_reduce
      rw [← QuotientGroup.mk_zpow, QuotientGroup.eq]
      rw [Subgroup.mem_subgroupOf]
      have e : (((⟨g, hgS⟩ : S) ^ n)⁻¹ * s : S) = (g ^ n)⁻¹ * c * g ^ n := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, SubgroupClass.coe_zpow]
        rw [← hcw]
        group
      rw [e]
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hgN (Subgroup.mem_zpowers_iff.mpr
        ⟨n, rfl⟩))) c).mp hc
      simpa using this

end CFSG.Walter.W67.Sec6
