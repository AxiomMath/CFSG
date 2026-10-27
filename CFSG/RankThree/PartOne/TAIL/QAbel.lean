module

public import CFSG.RankThree.PartOne.TAIL.QStruct

public section

namespace CFSG.RankThree.PartOne.TAIL

open Subgroup

variable {G : Type} [Group G]

theorem mem_normalizer_zpowers_of_commute {x y : G} (hxy : x * y = y * x) :
    x ∈ Subgroup.normalizer (Subgroup.zpowers y : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  have hc : ∀ i : ℤ, x * y ^ i = y ^ i * x := fun i => (Commute.zpow_right (show Commute x y from hxy) i).eq
  constructor
  · intro hg
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have : x * y ^ i * x⁻¹ = y ^ i := by rw [hc i]; group
    rw [this]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers y) i
  · intro hg
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hg
    have : g = y ^ i := by
      calc g = x⁻¹ * (x * g * x⁻¹) * x := by group
        _ = x⁻¹ * y ^ i * x := by rw [← hi]
        _ = y ^ i := by
          have : x⁻¹ * y ^ i = y ^ i * x⁻¹ := by
            have := hc i
            calc x⁻¹ * y ^ i = x⁻¹ * (y ^ i * x) * x⁻¹ := by group
              _ = x⁻¹ * (x * y ^ i) * x⁻¹ := by rw [this]
              _ = y ^ i * x⁻¹ := by group
          rw [this]; group
    rw [this]
    exact Subgroup.mem_zpowers_iff.mpr ⟨i, rfl⟩

theorem card_eq_mul_of_decomp {Y Z Q : Subgroup G} (hinf : Y ⊓ Z = ⊥) (hYQ : Y ≤ Q) (hZQ : Z ≤ Q)
    (hQ : ∀ q ∈ Q, ∃ y ∈ Y, ∃ z ∈ Z, q = y * z) : Nat.card Q = Nat.card Y * Nat.card Z := by
  let Φ : ↥Y × ↥Z → ↥Q := fun p => ⟨p.1 * p.2, Q.mul_mem (hYQ p.1.2) (hZQ p.2.2)⟩
  have hinj : Function.Injective Φ := by
    rintro ⟨y, z⟩ ⟨y', z'⟩ he
    have he' : (y : G) * z = y' * z' := congrArg Subtype.val he
    have h1 : (y' : G)⁻¹ * y = z' * (z : G)⁻¹ := by
      calc (y' : G)⁻¹ * y = (y' : G)⁻¹ * (y * z) * (z : G)⁻¹ := by group
        _ = (y' : G)⁻¹ * (y' * z') * (z : G)⁻¹ := by rw [he']
        _ = z' * (z : G)⁻¹ := by group
    have hmemY : (y' : G)⁻¹ * y ∈ Y := Y.mul_mem (Y.inv_mem y'.2) y.2
    have hmemZ : (y' : G)⁻¹ * y ∈ Z := h1 ▸ Z.mul_mem z'.2 (Z.inv_mem z.2)
    have hbot : (y' : G)⁻¹ * y ∈ Y ⊓ Z := Subgroup.mem_inf.mpr ⟨hmemY, hmemZ⟩
    rw [hinf] at hbot
    have h2 : (y' : G)⁻¹ * y = 1 := Subgroup.mem_bot.mp hbot
    have hy : (y : G) = y' := by
      calc (y : G) = y' * ((y' : G)⁻¹ * y) := by group
        _ = y' := by rw [h2, mul_one]
    have hz : (z : G) = z' := by
      have : (y : G) * z = y * z' := by rw [he', hy]
      exact mul_left_cancel this
    exact Prod.ext (Subtype.ext hy) (Subtype.ext hz)
  have hsurj : Function.Surjective Φ := by
    rintro ⟨q, hq⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := hQ q hq
    exact ⟨(⟨y, hy⟩, ⟨z, hz⟩), rfl⟩
  rw [← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofBijective Φ ⟨hinj, hsurj⟩)).symm

@[expose] def Qproj (K Q : Subgroup G) : Subgroup G where
  carrier := {k | k ∈ K ∧ ∃ z ∈ Subgroup.centralizer (K : Set G), k * z ∈ Q}
  one_mem' := ⟨K.one_mem, 1, Subgroup.one_mem _, by simp⟩
  mul_mem' := by
    rintro k₁ k₂ ⟨hk₁, z₁, hz₁, hq₁⟩ ⟨hk₂, z₂, hz₂, hq₂⟩
    refine ⟨K.mul_mem hk₁ hk₂, z₁ * z₂, Subgroup.mul_mem _ hz₁ hz₂, ?_⟩
    have hc : k₂ * z₁ = z₁ * k₂ := Subgroup.mem_centralizer_iff.mp hz₁ k₂ hk₂
    have e : k₁ * k₂ * (z₁ * z₂) = (k₁ * z₁) * (k₂ * z₂) := by
      calc k₁ * k₂ * (z₁ * z₂) = k₁ * (k₂ * z₁) * z₂ := by group
        _ = k₁ * (z₁ * k₂) * z₂ := by rw [hc]
        _ = (k₁ * z₁) * (k₂ * z₂) := by group
    rw [e]
    exact Q.mul_mem hq₁ hq₂
  inv_mem' := by
    rintro k ⟨hk, z, hz, hq⟩
    refine ⟨K.inv_mem hk, z⁻¹, Subgroup.inv_mem _ hz, ?_⟩
    have hc : k * z = z * k := Subgroup.mem_centralizer_iff.mp hz k hk
    have e : k⁻¹ * z⁻¹ = (k * z)⁻¹ := by
      calc k⁻¹ * z⁻¹ = (z * k)⁻¹ := by group
        _ = (k * z)⁻¹ := by rw [hc]
    rw [e]
    exact Q.inv_mem hq

theorem Qproj_le (K Q : Subgroup G) : Qproj K Q ≤ K := fun _ hk => hk.1

theorem Qproj_pgroup {K Q : Subgroup G} (hQ7 : IsPGroup 7 ↥Q) (hKC : K ⊓ Subgroup.centralizer (K : Set G) = ⊥) :
    IsPGroup 7 ↥(Qproj K Q) := by
  rw [isPGroup_iff_orderOf_dvd_pow]
  intro g
  obtain ⟨hk, z, hz, hq⟩ := g.2
  obtain ⟨m, hm⟩ := hQ7.exists_orderOf_dvd_pow (⟨(g : G) * z, hq⟩ : ↥Q)
  refine ⟨m, ?_⟩
  rw [← Subgroup.orderOf_coe]
  have h1 : ((g : G) * z) ^ 7 ^ m = 1 := by
    have := (orderOf_dvd_iff_pow_eq_one.mp hm)
    have h2 : (((⟨(g : G) * z, hq⟩ : ↥Q) ^ 7 ^ m : ↥Q) : G) = 1 := by rw [this]; rfl
    exact h2
  have hcomm : Commute (g : G) z := (Subgroup.mem_centralizer_iff.mp hz g hk)
  rw [hcomm.mul_pow] at h1
  have h3 : (g : G) ^ 7 ^ m = (z ^ 7 ^ m)⁻¹ := eq_inv_of_mul_eq_one_left h1
  have h4 : (g : G) ^ 7 ^ m ∈ K ⊓ Subgroup.centralizer (K : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨Subgroup.pow_mem _ hk _, ?_⟩
    rw [h3]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hz _)
  rw [hKC] at h4
  exact orderOf_dvd_of_pow_eq_one (Subgroup.mem_bot.mp h4)

namespace SchemeHyp

variable [Finite G] {A B : Subgroup G} {c b d y₀ : G} {K M₀ : Subgroup G}
  (h : SchemeHyp G A B c b d y₀ K M₀)

include h in
theorem y₀_notMem_A : y₀ ∉ A := by
  intro hy
  obtain ⟨β₀, hβ₀B, hβ₀1, hy'⟩ := h.y₀_c
  have hcomm : y₀ * c = c * y₀ := h.A_comm hy h.c_mem
  apply hβ₀1
  have : c * β₀ = c * 1 := by
    rw [← hy', mul_one]
    calc y₀ * c * y₀⁻¹ = (c * y₀) * y₀⁻¹ := by rw [hcomm]
      _ = c := by group
  exact mul_left_cancel this

include h in
theorem y₀_orderOf : orderOf y₀ = 49 := by
  have hdord : orderOf d = 7 := orderOf_eq_prime (h.B_pow h.d_mem) h.d_ne
  have hdcard : Nat.card (Subgroup.zpowers d) = 7 := by rw [Nat.card_zpowers, hdord]
  have hdy : d ∈ Subgroup.normalizer (Subgroup.zpowers y₀ : Set G) := by
    apply mem_normalizer_zpowers_of_commute
    have := h.y₀_cB d h.d_mem
    calc d * y₀ = y₀ * d * y₀⁻¹ * y₀ := by rw [this]
      _ = y₀ * d := by group
  have hRK : Subgroup.zpowers y₀ ⊔ Subgroup.zpowers d ≤ K :=
    sup_le (Subgroup.zpowers_le.mpr h.y₀_K) (Subgroup.zpowers_le.mpr h.d_K)
  have hd7 : IsPGroup 7 ↥(Subgroup.zpowers d) := IsPGroup.of_card (n := 1) (by rw [hdcard]; norm_num)
  have hR7 : IsPGroup 7 ↥(Subgroup.zpowers y₀ ⊔ Subgroup.zpowers d) :=
    h.zpowers_y₀_pgroup.to_sup_of_normal_left' hd7 ((Subgroup.zpowers_le).mpr hdy)
  obtain ⟨hcyc, hcard⟩ := h.K_data.sylow _ hRK hR7
  obtain ⟨k, hk⟩ := h.y₀_ord
  have hyle : Subgroup.zpowers y₀ ≤ Subgroup.zpowers y₀ ⊔ Subgroup.zpowers d := le_sup_left
  have hcardy : Nat.card (Subgroup.zpowers y₀) = 7 ^ k := by rw [Nat.card_zpowers, hk]
  have hk2 : k ≤ 2 := by
    have h1 : 7 ^ k ≤ 49 := by
      rw [← hcardy]
      exact (Subgroup.card_le_of_le hyle).trans hcard
    by_contra hk3
    rw [not_le] at hk3
    have : 7 ^ 3 ≤ 7 ^ k := Nat.pow_le_pow_right (by norm_num) hk3
    omega
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hk
    exact h.y₀_notMem_A (hk ▸ A.one_mem)
  have hk1 : k ≠ 1 := by
    rintro rfl
    rw [pow_one] at hk
    have : IsCyclic ↥(Subgroup.zpowers y₀ ⊔ Subgroup.zpowers d) := hcyc
    have hdle : Subgroup.zpowers d ≤ Subgroup.zpowers y₀ ⊔ Subgroup.zpowers d := le_sup_right
    have e1 : Nat.card ((Subgroup.zpowers y₀).subgroupOf (Subgroup.zpowers y₀ ⊔ Subgroup.zpowers d)) = 7 := by
      rw [← hk, ← Nat.card_zpowers]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyle).toEquiv
    have e2 : Nat.card ((Subgroup.zpowers d).subgroupOf (Subgroup.zpowers y₀ ⊔ Subgroup.zpowers d)) = 7 := by
      rw [← hdcard]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hdle).toEquiv
    have heq := (IsCyclic.subgroup_eq_iff_card_eq (H := (Subgroup.zpowers y₀).subgroupOf
      (Subgroup.zpowers y₀ ⊔ Subgroup.zpowers d)) (K := (Subgroup.zpowers d).subgroupOf
      (Subgroup.zpowers y₀ ⊔ Subgroup.zpowers d))).mpr (by rw [e1, e2])
    have hmem : (⟨y₀, hyle (Subgroup.mem_zpowers y₀)⟩ : ↥(Subgroup.zpowers y₀ ⊔ Subgroup.zpowers d)) ∈
        (Subgroup.zpowers y₀).subgroupOf (Subgroup.zpowers y₀ ⊔ Subgroup.zpowers d) :=
      Subgroup.mem_zpowers y₀
    rw [heq] at hmem
    have hyd : y₀ ∈ Subgroup.zpowers d := hmem
    exact h.y₀_notMem_A (h.B_le ((Subgroup.zpowers_le.mpr h.d_mem) hyd))
  have : k = 2 := by omega
  rw [hk, this]
  norm_num

variable {P : Subgroup G} (hP : PData A B y₀ P)

include h hP

theorem y₀_mem_Q : y₀ ∈ Qsub K P :=
  Subgroup.mem_inf.mpr ⟨hP.y₀_mem, Subgroup.mem_sup_left h.y₀_K⟩

theorem Qproj_eq : Subgroup.zpowers y₀ = Qproj K (Qsub K P) := by
  have hle : Subgroup.zpowers y₀ ≤ Qproj K (Qsub K P) := by
    rw [Subgroup.zpowers_le]
    exact ⟨h.y₀_K, 1, Subgroup.one_mem _, by simpa using h.y₀_mem_Q hP⟩
  have hpg := Qproj_pgroup (hP.pgroup.to_le (Qsub_le K P)) h.K_data.inf_centralizer
  obtain ⟨_, hcard⟩ := h.K_data.sylow _ (Qproj_le K _) hpg
  have hy49 : Nat.card (Subgroup.zpowers y₀) = 49 := by rw [Nat.card_zpowers, h.y₀_orderOf]
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hy49]; exact hcard)

theorem Q_decomp {q : G} (hq : q ∈ Qsub K P) :
    ∃ i : ℤ, ∃ z ∈ Qsub K P ⊓ Subgroup.centralizer (K : Set G), q = y₀ ^ i * z := by
  obtain ⟨k, hk, z, hz, rfl⟩ := mem_KC_iff.mp (Subgroup.mem_inf.mp hq).2
  have hkQ : k ∈ Qproj K (Qsub K P) := ⟨hk, z, hz, hq⟩
  rw [← h.Qproj_eq hP] at hkQ
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hkQ
  refine ⟨i, z, Subgroup.mem_inf.mpr ⟨?_, hz⟩, rfl⟩
  have := (Qsub K P).mul_mem ((Qsub K P).inv_mem ((Qsub K P).zpow_mem (h.y₀_mem_Q hP) i)) hq
  simpa using this

theorem Z_card : Nat.card ↥(Qsub K P ⊓ Subgroup.centralizer (K : Set G)) = 7 ^ 2 := by
  have hY : Subgroup.zpowers y₀ ≤ Qsub K P := Subgroup.zpowers_le.mpr (h.y₀_mem_Q hP)
  have hinf : Subgroup.zpowers y₀ ⊓ (Qsub K P ⊓ Subgroup.centralizer (K : Set G)) = ⊥ := by
    rw [eq_bot_iff, ← h.K_data.inf_centralizer]
    exact inf_le_inf (Subgroup.zpowers_le.mpr h.y₀_K) inf_le_right
  have hcard := card_eq_mul_of_decomp hinf hY inf_le_left (fun q hq => by
    obtain ⟨i, z, hz, rfl⟩ := h.Q_decomp hP hq
    exact ⟨y₀ ^ i, Subgroup.mem_zpowers_iff.mpr ⟨i, rfl⟩, z, hz, rfl⟩)
  rw [h.Q_card hP, Nat.card_zpowers, h.y₀_orderOf] at hcard
  apply Nat.eq_of_mul_eq_mul_left (show 0 < 49 by norm_num)
  rw [← hcard]
  norm_num

theorem Z_comm {z z' : G} (hz : z ∈ Qsub K P ⊓ Subgroup.centralizer (K : Set G))
    (hz' : z' ∈ Qsub K P ⊓ Subgroup.centralizer (K : Set G)) : z * z' = z' * z := by
  have := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 7) (h.Z_card hP)
  exact congrArg Subtype.val (IsMulCommutative.is_comm.comm
    (⟨z, hz⟩ : ↥(Qsub K P ⊓ Subgroup.centralizer (K : Set G))) ⟨z', hz'⟩)

theorem Q_comm {x y : G} (hx : x ∈ Qsub K P) (hy : y ∈ Qsub K P) : x * y = y * x := by
  obtain ⟨i, z, hz, rfl⟩ := h.Q_decomp hP hx
  obtain ⟨j, z', hz', rfl⟩ := h.Q_decomp hP hy
  have hcz : ∀ (k : ℤ) (w : G), w ∈ Subgroup.centralizer (K : Set G) →
      y₀ ^ k * w = w * y₀ ^ k := fun k w hw =>
    (Commute.zpow_left (show Commute y₀ w from Subgroup.mem_centralizer_iff.mp hw y₀ h.y₀_K) k).eq
  have hzz := h.Z_comm hP hz hz'
  have hz1 := (Subgroup.mem_inf.mp hz).2
  have hz1' := (Subgroup.mem_inf.mp hz').2
  have e1 : y₀ ^ i * z * (y₀ ^ j * z') = (y₀ ^ i * y₀ ^ j) * (z * z') := by
    calc y₀ ^ i * z * (y₀ ^ j * z') = y₀ ^ i * (z * y₀ ^ j) * z' := by group
      _ = y₀ ^ i * (y₀ ^ j * z) * z' := by rw [← hcz j z hz1]
      _ = (y₀ ^ i * y₀ ^ j) * (z * z') := by group
  have e2 : y₀ ^ j * z' * (y₀ ^ i * z) = (y₀ ^ j * y₀ ^ i) * (z' * z) := by
    calc y₀ ^ j * z' * (y₀ ^ i * z) = y₀ ^ j * (z' * y₀ ^ i) * z := by group
      _ = y₀ ^ j * (y₀ ^ i * z') * z := by rw [← hcz i z' hz1']
      _ = (y₀ ^ j * y₀ ^ i) * (z' * z) := by group
  rw [e1, e2, ← zpow_add, ← zpow_add, add_comm, hzz]

end SchemeHyp

end CFSG.RankThree.PartOne.TAIL
