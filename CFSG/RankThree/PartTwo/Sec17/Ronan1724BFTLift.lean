module

public import Mathlib.GroupTheory.Sylow
import CFSG.RankThree.PartTwo.Sec17.Ronan1724BFTLin

public section

namespace CFSG.RankThree.PartTwo.Sec17.Ronan1724BFT

open scoped commutatorElement

theorem exists_lift_heisenberg_inverting {H Γ : Type*} [Group H] [Finite H] [Group Γ]
    (π : H →* Γ) (hπ : Function.Surjective π) (h3 : ¬ 3 ∣ Nat.card π.ker)
    {a b c : Γ} (hP : IsPGroup 3 (Subgroup.closure ({a, b} : Set Γ)))
    (ha : a ^ 3 = 1) (hab : ⁅a, b⁆ ≠ 1) (hca : Commute ⁅a, b⁆ a) (hcb : Commute ⁅a, b⁆ b)
    (hc : c * ⁅a, b⁆ * c⁻¹ = ⁅a, b⁆ ^ 2) :
    ∃ x y g : H, x ^ 3 = 1 ∧ Commute ⁅x, y⁆ x ∧ Commute ⁅x, y⁆ y ∧ π ⁅x, y⁆ ≠ 1 ∧
      g * ⁅x, y⁆ * g⁻¹ = ⁅x, y⁆⁻¹ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set P : Subgroup Γ := Subgroup.closure ({a, b} : Set Γ) with hPdef
  set M : Subgroup H := P.comap π with hM
  set f : M →* P := π.subgroupComap P with hf
  have hfs : Function.Surjective f := π.subgroupComap_surjective P hπ
  obtain ⟨Q₀⟩ := (inferInstance : Nonempty (Sylow 3 M))
  have hQ₀top : (Q₀ : Subgroup M).map f = ⊤ := by
    have htop : IsPGroup 3 (⊤ : Subgroup P) := hP.of_equiv Subgroup.topEquiv.symm
    exact ((Q₀.mapSurjective hfs).is_maximal' htop le_top).symm
  set Q : Subgroup H := (Q₀ : Subgroup M).map M.subtype with hQ
  have hQ3 : IsPGroup 3 Q := Q₀.2.map M.subtype
  have hker : ∀ q ∈ Q, π q = 1 → q = 1 := by
    intro q hq hq1
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hQ3) ⟨q, hq⟩
    rw [Subgroup.orderOf_mk] at hk
    have hdvd : orderOf q ∣ Nat.card π.ker := by
      have h := orderOf_dvd_natCard (⟨q, MonoidHom.mem_ker.mpr hq1⟩ : π.ker)
      rwa [Subgroup.orderOf_mk] at h
    rcases k with _ | k
    · rw [pow_zero, orderOf_eq_one_iff] at hk
      exact hk
    · exact absurd ((dvd_pow_self 3 (Nat.succ_ne_zero k)).trans (hk ▸ hdvd)) h3
  have hinj : ∀ q₁ ∈ Q, ∀ q₂ ∈ Q, π q₁ = π q₂ → q₁ = q₂ := by
    intro q₁ h₁ q₂ h₂ h
    have h' := hker (q₁ * q₂⁻¹) (Q.mul_mem h₁ (Q.inv_mem h₂))
      (by rw [map_mul, map_inv, h, mul_inv_cancel])
    exact mul_inv_eq_one.mp h'
  have hlift : ∀ p ∈ P, ∃ q ∈ Q, π q = p := by
    intro p hp
    have hmem : (⟨p, hp⟩ : P) ∈ (Q₀ : Subgroup M).map f := by
      rw [hQ₀top]
      exact Subgroup.mem_top _
    obtain ⟨m, hm, hmp⟩ := Subgroup.mem_map.mp hmem
    refine ⟨(m : H), ⟨m, hm, rfl⟩, ?_⟩
    have h := congrArg Subtype.val hmp
    exact h
  obtain ⟨x, hxQ, hxa⟩ := hlift a (Subgroup.subset_closure (by simp))
  obtain ⟨y, hyQ, hyb⟩ := hlift b (Subgroup.subset_closure (by simp))
  set z := ⁅x, y⁆ with hz
  have hzQ : z ∈ Q := by
    rw [hz, commutatorElement_def]
    exact Q.mul_mem (Q.mul_mem (Q.mul_mem hxQ hyQ) (Q.inv_mem hxQ)) (Q.inv_mem hyQ)
  have hπz : π z = ⁅a, b⁆ := by rw [hz, map_commutatorElement, hxa, hyb]
  have hx3 : x ^ 3 = 1 := hker _ (Q.pow_mem hxQ 3) (by rw [map_pow, hxa, ha])
  have hzx : Commute z x := hinj _ (Q.mul_mem hzQ hxQ) _ (Q.mul_mem hxQ hzQ)
    (by rw [map_mul, map_mul, hπz, hxa]; exact hca.eq)
  have hzy : Commute z y := hinj _ (Q.mul_mem hzQ hyQ) _ (Q.mul_mem hyQ hzQ)
    (by rw [map_mul, map_mul, hπz, hyb]; exact hcb.eq)
  have hz1 : π z ≠ 1 := by rw [hπz]; exact hab
  have hz1' : z ≠ 1 := fun h => hz1 (by rw [h, map_one])
  have hz3 : z ^ 3 = 1 := commutatorElement_pow_three_eq_one hx3 hzx hzy
  have hab3 : ⁅a, b⁆ ^ 3 = 1 := commutatorElement_pow_three_eq_one ha hca hcb
  have hzord : orderOf z = 3 := orderOf_eq_prime hz3 hz1'
  obtain ⟨g', hg'⟩ := hπ c
  set w := g' * z * g'⁻¹ with hw
  have hπw : π w = ⁅a, b⁆ ^ 2 := by rw [hw, map_mul, map_mul, map_inv, hg', hπz, hc]
  have hw3 : w ^ 3 = 1 := by rw [hw, conj_pow, hz3, mul_one, mul_inv_cancel]
  have hw1 : w ≠ 1 := by
    intro h
    apply hz1'
    rw [hw] at h
    have h' : z = g'⁻¹ * (g' * z * g'⁻¹) * g' := by group
    rw [h', h]
    group
  have hword : orderOf w = 3 := orderOf_eq_prime hw3 hw1
  set K : Subgroup H := π.ker with hK
  set T : Subgroup H := Subgroup.zpowers z ⊔ K with hT
  have hzT : Subgroup.zpowers z ≤ T := le_sup_left
  have hKT : K ≤ T := le_sup_right
  have hwT : w ∈ T := by
    have hwz : w * z ∈ K := by
      rw [hK, MonoidHom.mem_ker, map_mul, hπw, hπz, ← pow_succ, hab3]
    have h : w = (w * z) * z⁻¹ := by group
    rw [h]
    exact T.mul_mem (hKT hwz) (T.inv_mem (hzT (Subgroup.mem_zpowers z)))
  have hdisj : Disjoint K (Subgroup.zpowers z) := by
    rw [Subgroup.disjoint_def]
    intro u huK huz
    exact hker u (Subgroup.zpowers_le.mpr hzQ huz) huK
  have hcardT : Nat.card T = 3 * Nat.card K := by
    haveI : K.Normal := by rw [hK]; infer_instance
    have h1 : K.relIndex T = K.relIndex (Subgroup.zpowers z) :=
      Subgroup.relIndex_sup_right (Subgroup.zpowers z) K
    have h2 : K.relIndex (Subgroup.zpowers z) = 3 := by
      rw [Subgroup.relIndex, Subgroup.subgroupOf_eq_bot.mpr hdisj, Subgroup.index_bot,
        Nat.card_zpowers, hzord]
    have h3' := (K.subgroupOf T).card_mul_index
    have h4 : Nat.card (K.subgroupOf T) = Nat.card K :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKT).toEquiv
    rw [h4, ← Subgroup.relIndex, h1, h2] at h3'
    rw [← h3', mul_comm]
  have hsyl : ∀ L : Subgroup H, L ≤ T → Nat.card L = 3 →
      ∃ S : Sylow 3 T, (S : Subgroup T) = L.subgroupOf T := by
    intro L hLT hL3
    have hcardL : Nat.card (L.subgroupOf T) = 3 := by
      rw [← hL3]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLT).toEquiv
    have hp : IsPGroup 3 (L.subgroupOf T) := IsPGroup.of_card (n := 1) (by rw [hcardL, pow_one])
    have hidx : ¬ 3 ∣ (L.subgroupOf T).index := by
      have h := (L.subgroupOf T).card_mul_index
      rw [hcardL, hcardT] at h
      have h' : (L.subgroupOf T).index = Nat.card K := by omega
      rw [h']
      exact h3
    exact ⟨hp.toSylow hidx, rfl⟩
  obtain ⟨S₁, hS₁⟩ := hsyl (Subgroup.zpowers z) hzT (by rw [Nat.card_zpowers, hzord])
  obtain ⟨S₂, hS₂⟩ := hsyl (Subgroup.zpowers w) (Subgroup.zpowers_le.mpr hwT)
    (by rw [Nat.card_zpowers, hword])
  obtain ⟨t, ht⟩ := MulAction.exists_smul_eq T S₂ S₁
  have htw : (t : H) * w * (t : H)⁻¹ ∈ Subgroup.zpowers z := by
    have hmem : (⟨w, hwT⟩ : T) ∈ (S₂ : Subgroup T) := by
      rw [hS₂]
      exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers w)
    have hmem' : MulAut.conj t (⟨w, hwT⟩ : T) ∈ (S₁ : Subgroup T) := by
      rw [← ht, Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ hmem
    rw [hS₁, Subgroup.mem_subgroupOf, MulAut.conj_apply] at hmem'
    simpa using hmem'
  have hπt : π t ∈ Subgroup.zpowers (π z) := by
    have h2 : T.map π ≤ Subgroup.zpowers (π z) := by
      rw [hT, Subgroup.map_sup, MonoidHom.map_zpowers,
        (Subgroup.map_eq_bot_iff K).mpr (by rw [hK]), sup_bot_eq]
    exact h2 (Subgroup.mem_map_of_mem π t.2)
  have hcomm : Commute (π t) (π w) := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hπt
    rw [← hk, hπw, ← hπz]
    exact ((Commute.refl (π z)).zpow_left k).pow_right 2
  have hπtw : π ((t : H) * w * (t : H)⁻¹) = π z⁻¹ := by
    rw [map_mul, map_mul, map_inv, hcomm.eq, mul_inv_cancel_right, hπw, map_inv, hπz,
      eq_inv_iff_mul_eq_one, ← pow_succ, hab3]
  have heq : (t : H) * w * (t : H)⁻¹ = z⁻¹ :=
    hinj _ (Subgroup.zpowers_le.mpr hzQ htw) _ (Q.inv_mem hzQ) hπtw
  refine ⟨x, y, (t : H) * g', hx3, hzx, hzy, hz1, ?_⟩
  rw [← hz, ← heq, hw]
  group

end CFSG.RankThree.PartTwo.Sec17.Ronan1724BFT
