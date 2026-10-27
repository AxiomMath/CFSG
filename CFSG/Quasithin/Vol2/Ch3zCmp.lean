module

public import CFSG.Quasithin.Vol2.Ch3zSetup

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace Ch3z

section Odd

theorem exists_odd_pow_eq {A B : Type*} [Group A] [Group B] (φ : A →* B) {x : A}
    (hx : IsOfFinOrder x) (hodd : Odd (orderOf (φ x))) :
    ∃ n : ℕ, Odd (orderOf (x ^ n)) ∧ φ (x ^ n) = φ x := by
  have hopos : 0 < orderOf x := hx.orderOf_pos
  obtain ⟨a, o', ho', hoa⟩ := Nat.exists_eq_two_pow_mul_odd (n := orderOf x) hopos.ne'
  have hcop : Nat.Coprime (2 ^ a) (orderOf (φ x)) :=
    Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hodd)
  obtain ⟨n, hn1, hn2⟩ : ∃ n : ℕ, n ≡ 0 [MOD 2 ^ a] ∧ n ≡ 1 [MOD orderOf (φ x)] :=
    ⟨Nat.chineseRemainder hcop 0 1, (Nat.chineseRemainder hcop 0 1).2.1,
      (Nat.chineseRemainder hcop 0 1).2.2⟩
  refine ⟨n, ?_, ?_⟩
  · obtain ⟨c, hc⟩ := (Nat.modEq_zero_iff_dvd).mp hn1
    have hpow : (x ^ n) ^ o' = 1 := by
      rw [← pow_mul, hc, show 2 ^ a * c * o' = c * orderOf x by rw [hoa]; ring, pow_mul',
        pow_orderOf_eq_one, one_pow]
    exact ho'.of_dvd_nat (orderOf_dvd_of_pow_eq_one hpow)
  · have h3 : (φ x) ^ n = (φ x) ^ 1 := pow_eq_pow_iff_modEq.mpr hn2
    rw [map_pow, h3, pow_one]

theorem exists_odd_pow_two_part {G : Type*} [Group G] {x : G} (hx : IsOfFinOrder x) :
    ∃ n : ℕ, Odd (orderOf (x ^ n)) ∧ ∃ k : ℕ, (x * (x ^ n)⁻¹) ^ 2 ^ k = 1 := by
  have hopos : 0 < orderOf x := hx.orderOf_pos
  obtain ⟨a, o', ho', hoa⟩ := Nat.exists_eq_two_pow_mul_odd (n := orderOf x) hopos.ne'
  have hcop : Nat.Coprime (2 ^ a) o' := Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr ho')
  obtain ⟨n, hn1, hn2⟩ : ∃ n : ℕ, n ≡ 0 [MOD 2 ^ a] ∧ n ≡ 1 [MOD o'] :=
    ⟨Nat.chineseRemainder hcop 0 1, (Nat.chineseRemainder hcop 0 1).2.1,
      (Nat.chineseRemainder hcop 0 1).2.2⟩
  refine ⟨n, ?_, a, ?_⟩
  · obtain ⟨c, hc⟩ := (Nat.modEq_zero_iff_dvd).mp hn1
    have hpow : (x ^ n) ^ o' = 1 := by
      rw [← pow_mul, hc, show 2 ^ a * c * o' = c * orderOf x by rw [hoa]; ring, pow_mul',
        pow_orderOf_eq_one, one_pow]
    exact ho'.of_dvd_nat (orderOf_dvd_of_pow_eq_one hpow)
  · have hdvd : (o' : ℤ) ∣ (n : ℤ) - 1 := by
      have := (Nat.modEq_iff_dvd).mp hn2.symm
      exact this
    have h1 : x * (x ^ n)⁻¹ = x ^ ((1 : ℤ) - n) := by
      rw [zpow_sub, zpow_one, zpow_natCast]
    rw [h1, ← zpow_natCast, ← zpow_mul]
    refine (orderOf_dvd_iff_zpow_eq_one).mp ?_
    rw [hoa]
    obtain ⟨d, hd⟩ := hdvd
    refine ⟨-d, ?_⟩
    push_cast
    have : ((1 : ℤ) - n) = -((n : ℤ) - 1) := by ring
    rw [this, hd]
    ring

end Odd

section Cmp

variable {G : Type} [Group G] [Finite G] {H T M₂ : Subgroup G}

theorem kerIn_le_sup (hmp : MinParabolic H T M₂) :
    kerIn M₂ H ≤ twoResidual H ⊔ pCoreOf 2 H := by
  intro x hx
  have hxH : x ∈ H := hmp.kerIn_le_H hx
  obtain ⟨n, hodd, k, hk⟩ := exists_odd_pow_two_part (isOfFinOrder_of_finite x)
  have hy : x ^ n ∈ twoResidual H := F6.mem_twoResidual_of_odd (H.pow_mem hxH n) hodd
  set J := kerIn M₂ H with hJ
  have hz : x * (x ^ n)⁻¹ ∈ pCoreOf 2 H := by
    have hzJ : x * (x ^ n)⁻¹ ∈ J := J.mul_mem hx (J.inv_mem (J.pow_mem hx n))
    have hP : IsPGroup 2 (Subgroup.zpowers (x * (x ^ n)⁻¹)) := by
      intro g
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp g.2
      refine ⟨k, Subtype.ext ?_⟩
      show (g : G) ^ 2 ^ k = 1
      rw [← hj, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]
    exact hmp.le_pCoreOf_of_isPGroup_of_le_kerIn hP (Subgroup.zpowers_le.mpr hzJ)
      (Subgroup.mem_zpowers _)
  have e : x = (x ^ n) * (x * (x ^ n)⁻¹) := by
    have hc : x ^ n * x = x * x ^ n := ((Commute.refl x).pow_left n).eq
    rw [← mul_assoc, hc, mul_assoc, mul_inv_cancel, mul_one]
  exact e ▸ Subgroup.mul_mem_sup hy hz

theorem twoResidual_sup_eq_of_le (hmp : MinParabolic H T M₂) {C : Subgroup G}
    (hQC : pCoreOf 2 H ≤ C) (hCJ : C ≤ kerIn M₂ H) :
    twoResidual H ⊔ C = twoResidual H ⊔ kerIn M₂ H := by
  apply le_antisymm
  · exact sup_le_sup_left hCJ _
  · exact sup_le le_sup_left ((kerIn_le_sup hmp).trans (sup_le le_sup_left (hQC.trans le_sup_right)))

theorem thompsonJ_eq_sup_of_not_le (h : MinParabolic H T M₂) {A : Subgroup G}
    (hA : IsMaxElemAbelian T A) (hAn : ¬ A ≤ pCoreOf 2 H) :
    thompsonJ H = twoResidual H ⊔ thompsonJ T := by
  have hJT : thompsonJ T ≤ thompsonJ H := B6.thompsonJ_le_of_sylow h.isSylow
  have hnotJ : ¬ thompsonJ H ≤ kerIn M₂ H := by
    intro hle
    apply hAn
    exact h.le_pCoreOf_of_isPGroup_of_le_kerIn (h.isSylow.2.1.to_le hA.1)
      ((B6.le_thompsonJ hA).trans (hJT.trans hle))
  have hKJ : twoResidual H ≤ thompsonJ H :=
    (h.le_kerIn_or_twoResidual_le (B6.thompsonJ_le H)
      (B6.le_normalizer_thompsonJ H)).resolve_left hnotJ
  apply le_antisymm
  · have hTn : T ≤ Subgroup.normalizer ((twoResidual H ⊔ thompsonJ T : Subgroup G) : Set G) :=
      fun t ht => Subgroup.inf_normalizer_le_normalizer_sup _ _
        ⟨(le_normalizer_twoResidual H) (h.isSylow.1 ht), B6.le_normalizer_thompsonJ T ht⟩
    have hHn : H ≤ Subgroup.normalizer ((twoResidual H ⊔ thompsonJ T : Subgroup G) : Set G) := by
      calc H = T ⊔ twoResidual H := (sup_twoResidual_eq h.isSylow).symm
        _ ≤ _ := sup_le hTn (le_sup_left.trans Subgroup.le_normalizer)
    exact B6.thompsonJ_le_of_sylow_of_le h.isSylow le_sup_right hHn
  · exact sup_le hKJ hJT

end Cmp

section Step

variable {G : Type} [Group G] [Finite G] {H U L N : Subgroup G}

theorem pCoreOf_le_centralizerMod (hUH : U ≤ H) (hstep : IsChiefStep H U L N)
    (hE : IsElemAbelian 2 (chiefMod L N)) : pCoreOf 2 H ≤ centralizerMod L H N := by
  have hHL : H ≤ Subgroup.normalizer (L : Set G) := D14.le_normalizer_of_isNormalIn hstep.2.1
  have hHN : H ≤ Subgroup.normalizer (N : Set G) := D14.le_normalizer_of_isNormalIn hstep.1
  intro g hg
  have hgH : g ∈ H := pCoreOf_le 2 H hg
  have hmapmem : ∀ x : ↥H, x ∈ (pCoreOf 2 H).subgroupOf H →
      chiefPsi hHL hHN x ∈ chiefImg hHL hHN (pCoreOf 2 H) := fun x hx => ⟨x, hx, rfl⟩
  have hQX : chiefImg hHL hHN (pCoreOf 2 H) ≤ chiefAut H L N := by
    rintro _ ⟨x, -, rfl⟩
    exact chiefPsi_mem hHL hHN x
  have hQn : ((chiefImg hHL hHN (pCoreOf 2 H)).subgroupOf (chiefAut H L N)).Normal := by
    refine ⟨fun n hn y => ?_⟩
    obtain ⟨⟨p, hpH⟩, hp, hpn⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hn)
    obtain ⟨h, hh⟩ := chiefHom_surjective hHL hHN y
    have hy : (y : MulAut ↥(chiefMod L N)) = chiefPsi hHL hHN h := congrArg Subtype.val hh.symm
    rw [Subgroup.mem_subgroupOf] 
    show (y : MulAut ↥(chiefMod L N)) * (n : MulAut ↥(chiefMod L N)) * (y : MulAut ↥(chiefMod L N))⁻¹ ∈ _
    rw [hy, ← hpn]
    have hconj : (h : G) * p * (h : G)⁻¹ ∈ pCoreOf 2 H :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H h.2) p).mp (Subgroup.mem_subgroupOf.mp hp)
    refine ⟨h * ⟨p, hpH⟩ * h⁻¹, Subgroup.mem_subgroupOf.mpr hconj, ?_⟩
    simp
  have hQ2 : IsPGroup 2 (chiefImg hHL hHN (pCoreOf 2 H)) := by
    intro q
    obtain ⟨x, hx, hxq⟩ := Subgroup.mem_map.mp q.2
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 H ⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩
    refine ⟨k, Subtype.ext ?_⟩
    have hk' : (x : G) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hxk : x ^ 2 ^ k = 1 := Subtype.ext hk'
    show (q : MulAut ↥(chiefMod L N)) ^ 2 ^ k = 1
    rw [← hxq, ← map_pow, hxk, map_one]
  have hbot : chiefImg hHL hHN (pCoreOf 2 H) = (⊥ : Subgroup (MulAut ↥(chiefMod L N))) :=
    D15Proof.normal_two_eq_bot hUH hstep hE _ hQX hQn hQ2
  have hmem := hmapmem ⟨g, hgH⟩ (Subgroup.mem_subgroupOf.mpr hg)
  rw [hbot, Subgroup.mem_bot] at hmem
  have hc : chiefHom hHL hHN ⟨g, hgH⟩ = 1 := Subtype.ext hmem
  exact (chiefHom_eq_one_iff hHL hHN ((hstep.1.1.trans hUH).trans hHL) ⟨g, hgH⟩).1 hc

variable {T M₂ : Subgroup G}

theorem twoResidual_sup_centralizerMod_eq (hmp : MinParabolic H T M₂) (hUT : U ≤ T)
    (hstep : IsChiefStep H U L N) (hnc : ¬ IsCentralStep H L N)
    (hE : IsElemAbelian 2 (chiefMod L N)) :
    twoResidual H ⊔ centralizerMod L H N = twoResidual H ⊔ kerIn M₂ H :=
  twoResidual_sup_eq_of_le hmp (pCoreOf_le_centralizerMod (hUT.trans hmp.isSylow.1) hstep hE)
    (centralizerMod_le_kerIn hmp hUT hstep hnc)

end Step

end Ch3z

end CFSG.Quasithin
