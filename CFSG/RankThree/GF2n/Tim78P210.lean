module

public import CFSG.RankThree.GF2n.Tim78P210Quot
public import CFSG.RankThree.GF2n.Tim77Prop24Conj

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

@[expose] def sqPre (B F : Subgroup G) (hB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) : Subgroup G where
  carrier := {z | z ∈ B ∧ z * z ∈ F}
  one_mem' := ⟨B.one_mem, by rw [one_mul]; exact F.one_mem⟩
  mul_mem' := fun {a b} ha hb => ⟨B.mul_mem ha.1 hb.1, by
    have h := hB a ha.1 b hb.1
    rw [show a * b * (a * b) = (a * a) * (b * b) by
      rw [show a * b * (a * b) = a * (b * a) * b by group, ← h]; group]
    exact F.mul_mem ha.2 hb.2⟩
  inv_mem' := fun {a} ha => ⟨B.inv_mem ha.1, by
    rw [← mul_inv_rev]
    exact F.inv_mem ha.2⟩

namespace Setup210

variable {B₀ B₁ : Subgroup G} (S : Setup210 B₀ B₁)
include S

omit [Finite G] in
theorem mem_L₀ {x : G} : x ∈ PartTwo.omegaOneSub B₀ ↔ x ∈ B₀ ∧ x * x = 1 :=
  mem_omegaOneSub_iff S.comm

omit [Finite G] in
theorem mem_L₁ {x : G} : x ∈ PartTwo.omegaOneSub B₁ ↔ x ∈ B₁ ∧ x * x = 1 :=
  mem_omegaOneSub_iff S.comm₁

omit [Finite G] in
theorem sq_mem_L₀ {x : G} (hx : x ∈ B₀) (hx4 : x ^ 4 = 1) : x * x ∈ PartTwo.omegaOneSub B₀ := by
  rw [S.mem_L₀]
  refine ⟨B₀.mul_mem hx hx, ?_⟩
  rw [show x * x * (x * x) = x ^ 4 by simp [pow_succ, mul_assoc]]
  exact hx4

omit [Finite G] in
theorem exists_orderOf_four : ∃ y ∈ B₀, y * y ≠ 1 ∧ y ^ 4 = 1 := by
  obtain ⟨x, hx, hx2⟩ := S.exp_ne
  obtain ⟨k, hk⟩ := S.pow_two_pow_eq_one hx
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
  have hj2 : 2 ≤ j := by
    by_contra h
    apply hx2
    rw [← orderOf_dvd_iff_pow_eq_one, hj]
    have : 2 ^ j ∣ 2 ^ 1 := pow_dvd_pow 2 (by omega)
    simpa using this
  refine ⟨x ^ 2 ^ (j - 2), B₀.pow_mem hx _, ?_, ?_⟩
  · rw [← pow_add, ← two_mul, ← pow_succ']
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hj] at this
    have := Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2) |>.mp this
    omega
  · rw [← pow_mul, show 2 ^ (j - 2) * 4 = 2 ^ j by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add, Nat.sub_add_cancel hj2], ← hj,
      pow_orderOf_eq_one]

theorem prop24Setup (h0 : ∀ x ∈ nrm B₀ B₁, x * x = 1)
    (h1 : ∀ x ∈ nrm B₁ B₀, x * x = 1) (hFL : nrm B₀ B₁ ≠ PartTwo.omegaOneSub B₀) :
    Tim77.Prop24Setup (PartTwo.omegaOneSub B₀) (PartTwo.omegaOneSub B₁) (nrm B₀ B₁) (nrm B₁ B₀)
      (nrm B₀ B₁ ⊔ nrm B₁ B₀) := by
  obtain ⟨g, hg⟩ := S.conj
  have hL₁ : PartTwo.omegaOneSub B₁ = conjSubgroup g (PartTwo.omegaOneSub B₀) := by
    rw [hg, omegaOneSub_conj S.comm]
  have hN : ∀ {B : Subgroup G}, (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → IsTI B →
      PartTwo.omegaOneSub B ≠ ⊥ → ∀ x : G,
      (x ∈ Subgroup.normalizer (PartTwo.omegaOneSub B : Set G) ↔
        x ∈ Subgroup.normalizer (B : Set G)) := by
    intro B hBc hBti hL1 x
    rw [← conjSubgroup_eq_self_iff, ← conjSubgroup_eq_self_iff, ← omegaOneSub_conj hBc]
    constructor
    · intro h
      refine conjSubgroup_eq_of_isTI hBti fun hbot => hL1 ?_
      rw [eq_bot_iff]
      intro y hy
      have hy' : y ∈ PartTwo.omegaOneSub (conjSubgroup x B) := h ▸ hy
      have : y ∈ B ⊓ conjSubgroup x B :=
        Subgroup.mem_inf.mpr ⟨PartTwo.omegaOneSub_le B hy, PartTwo.omegaOneSub_le _ hy'⟩
      rwa [hbot] at this
    · intro h
      rw [h]
  have hF₁ : nrm B₁ B₀ ≠ ⊥ := S.ne_bot₁
  have hL0ne : PartTwo.omegaOneSub B₀ ≠ ⊥ := fun h => S.ne_bot (by
    rw [eq_bot_iff]
    intro x hx
    rw [← h]
    exact S.mem_L₀.mpr ⟨(mem_nrm.mp hx).1, h0 x hx⟩)
  have hL1ne : PartTwo.omegaOneSub B₁ ≠ ⊥ := fun h => hF₁ (by
    rw [eq_bot_iff]
    intro x hx
    rw [← h]
    exact S.mem_L₁.mpr ⟨(mem_nrm.mp hx).1, h1 x hx⟩)
  refine
    { elem := ⟨⟨⟨fun a b => Subtype.ext (S.comm _ (S.mem_L₀.mp a.2).1 _ (S.mem_L₀.mp b.2).1)⟩⟩,
        fun x hx => by rw [sq]; exact (S.mem_L₀.mp hx).2⟩
      ti := ?_
      conj := ⟨g, hL₁⟩
      hL := ?_
      hLb := ?_
      hM := rfl
      ne_bot := S.ne_bot
      ne := hFL }
  · intro k
    by_cases hk : PartTwo.omegaOneSub B₀ ⊓ conjSubgroup k (PartTwo.omegaOneSub B₀) = ⊥
    · exact Or.inl hk
    · right
      have hB : conjSubgroup k B₀ = B₀ := by
        refine conjSubgroup_eq_of_isTI S.ti fun hbot => hk ?_
        rw [eq_bot_iff]
        intro y hy
        obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.mp hy
        have hy2' : k⁻¹ * y * k ∈ PartTwo.omegaOneSub B₀ := mem_conjSubgroup.mp hy2
        have : y ∈ B₀ ⊓ conjSubgroup k B₀ := Subgroup.mem_inf.mpr
          ⟨PartTwo.omegaOneSub_le B₀ hy1, mem_conjSubgroup.mpr (PartTwo.omegaOneSub_le B₀ hy2')⟩
        rwa [hbot] at this
      rw [← omegaOneSub_conj S.comm, hB, inf_idem]
  · ext x
    rw [Subgroup.mem_inf, hN S.comm₁ S.ti₁ hL1ne x, mem_nrm]
    constructor
    · rintro ⟨hxB, hxN⟩
      exact ⟨S.mem_L₀.mpr ⟨hxB, h0 x (mem_nrm.mpr ⟨hxB, hxN⟩)⟩, hxN⟩
    · rintro ⟨hxL, hxN⟩
      exact ⟨(S.mem_L₀.mp hxL).1, hxN⟩
  · ext x
    rw [Subgroup.mem_inf, hN S.comm S.ti hL0ne x, mem_nrm]
    constructor
    · rintro ⟨hxB, hxN⟩
      exact ⟨S.mem_L₁.mpr ⟨hxB, h1 x (mem_nrm.mpr ⟨hxB, hxN⟩)⟩, hxN⟩
    · rintro ⟨hxL, hxN⟩
      exact ⟨(S.mem_L₁.mp hxL).1, hxN⟩

theorem mem_nrm_of_inverted {a c : G} (ha : a ∈ nrm B₁ B₀) (hcB : c ∈ B₀)
    (hcc : c * c = 1) (hinv : a * c * a⁻¹ = c⁻¹) (hc1 : a = 1 → c = 1) : c ∈ nrm B₀ B₁ := by
  by_cases ha1 : a = 1
  · rw [hc1 ha1]
    exact (nrm B₀ B₁).one_mem
  refine mem_nrm.mpr ⟨hcB, S.mem_normalizer_of_commute₁ (mem_nrm.mp ha).1 ha1 ?_⟩
  have h2 : a * c * a⁻¹ = c := hinv.trans (inv_eq_of_mul_eq_one_right hcc)
  calc c * a = (a * c * a⁻¹) * a := by rw [h2]
    _ = a * c := by group

theorem exists_sq_mem (h0 : ∀ x ∈ nrm B₀ B₁, x * x = 1) (h1 : ∀ x ∈ nrm B₁ B₀, x * x = 1)
    (hFL : nrm B₀ B₁ ≠ PartTwo.omegaOneSub B₀) :
    ∃ y ∈ B₀, y * y ≠ 1 ∧ y * y ∈ nrm B₀ B₁ := by
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  have P := S.prop24Setup h0 h1 hFL
  obtain ⟨y, hyB, hyy, hy4⟩ := S.exists_orderOf_four
  have hyF : y * y ∉ nrm B₀ B₁ := hcon y hyB hyy
  have hyL : y * y ∈ PartTwo.omegaOneSub B₀ := S.sq_mem_L₀ hyB hy4
  have hcomm : ∀ a ∈ nrm B₁ B₀, y⁻¹ * (a * y * a⁻¹) ∈ nrm B₀ B₁ := by
    intro a ha
    obtain ⟨haB, haN⟩ := mem_nrm.mp ha
    have haa := h1 a ha
    have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
    have hyaB : a * y * a⁻¹ ∈ B₀ := (Subgroup.mem_normalizer_iff.mp haN y).mp hyB
    have hcB : y⁻¹ * (a * y * a⁻¹) ∈ B₀ := B₀.mul_mem (B₀.inv_mem hyB) hyaB
    have hk : (y * y) * a * (y * y)⁻¹ * a⁻¹ ∈ nrm B₀ B₁ := P.commutator_mem_L hyL ha
    have hkB : ((y * y) * a * (y * y)⁻¹ * a⁻¹)⁻¹ ∈ B₀ := B₀.inv_mem (mem_nrm.mp hk).1
    have hc2 : (y⁻¹ * (a * y * a⁻¹)) * (y⁻¹ * (a * y * a⁻¹)) =
        ((y * y) * a * (y * y)⁻¹ * a⁻¹)⁻¹ := by
      have h1' := S.comm _ (B₀.inv_mem hyB) _ hyaB
      have h2' := S.comm _ (B₀.mul_mem hyB hyB) _ hkB
      have e1 : (y⁻¹ * (a * y * a⁻¹)) * (y⁻¹ * (a * y * a⁻¹)) =
          (y * y)⁻¹ * (a * (y * y) * a⁻¹) := by
        calc (y⁻¹ * (a * y * a⁻¹)) * (y⁻¹ * (a * y * a⁻¹)) =
            y⁻¹ * ((a * y * a⁻¹) * y⁻¹) * (a * y * a⁻¹) := by group
          _ = y⁻¹ * (y⁻¹ * (a * y * a⁻¹)) * (a * y * a⁻¹) := by rw [h1']
          _ = (y * y)⁻¹ * (a * (y * y) * a⁻¹) := by group
      rw [e1]
      obtain ⟨s, hs⟩ : ∃ s, s = y * y := ⟨_, rfl⟩
      rw [← hs] at h2' ⊢
      calc s⁻¹ * (a * s * a⁻¹) = s⁻¹ * ((s * a * s⁻¹ * a⁻¹)⁻¹ * s) := by group
        _ = s⁻¹ * (s * (s * a * s⁻¹ * a⁻¹)⁻¹) := by rw [h2']
        _ = (s * a * s⁻¹ * a⁻¹)⁻¹ := by group
    have hcc : (y⁻¹ * (a * y * a⁻¹)) * (y⁻¹ * (a * y * a⁻¹)) = 1 := by
      by_contra hne'
      exact hcon _ hcB hne' (by rw [hc2]; exact (nrm B₀ B₁).inv_mem hk)
    refine S.mem_nrm_of_inverted ha hcB hcc ?_ fun h => by rw [h]; group
    have e1 : a * (y⁻¹ * (a * y * a⁻¹)) * a⁻¹ = a * y⁻¹ * a * y * (a * a)⁻¹ := by group
    have e2 : (y⁻¹ * (a * y * a⁻¹))⁻¹ = a * y⁻¹ * a⁻¹ * y := by group
    rw [e1, e2, haa, inv_one, mul_one, hainv]
  have hyN : y ∈ Subgroup.normalizer ((nrm B₀ B₁ ⊔ nrm B₁ B₀ : Subgroup G) : Set G) := by
    have key : ∀ z ∈ B₀, (∀ a ∈ nrm B₁ B₀, z⁻¹ * (a * z * a⁻¹) ∈ nrm B₀ B₁) →
        ∀ x ∈ nrm B₀ B₁ ⊔ nrm B₁ B₀, z * x * z⁻¹ ∈ nrm B₀ B₁ ⊔ nrm B₁ B₀ := by
      intro z hz hza x hx
      obtain ⟨f, hf, b, hb, rfl⟩ := P.exists_mul_of_mem_M hx
      have hzf : z * f * z⁻¹ = f := by
        rw [S.comm _ hz _ (mem_nrm.mp hf).1, mul_inv_cancel_right]
      have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right (h1 b hb)
      have hbz : b * z * b⁻¹ ∈ B₀ := (Subgroup.mem_normalizer_iff.mp (mem_nrm.mp hb).2 z).mp hz
      have h' : z * b * z⁻¹ * b⁻¹ ∈ nrm B₀ B₁ := by
        have e : z * b * z⁻¹ * b⁻¹ = (z⁻¹ * (b * z * b⁻¹))⁻¹ := by
          have h1' := S.comm _ (B₀.inv_mem hz) _ hbz
          calc z * b * z⁻¹ * b⁻¹ = z * (b * z * b⁻¹)⁻¹ := by group
            _ = ((b * z * b⁻¹) * z⁻¹)⁻¹ := by group
            _ = (z⁻¹ * (b * z * b⁻¹))⁻¹ := by rw [h1']
        rw [e]
        exact (nrm B₀ B₁).inv_mem (hza b hb)
      rw [show z * (f * b) * z⁻¹ = (z * f * z⁻¹) * ((z * b * z⁻¹ * b⁻¹) * b) by group, hzf]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hf)
        (Subgroup.mul_mem _ (Subgroup.mem_sup_left h') (Subgroup.mem_sup_right hb))
    have hcomm' : ∀ a ∈ nrm B₁ B₀, y * (a * y⁻¹ * a⁻¹) ∈ nrm B₀ B₁ := by
      intro a ha
      have h := hcomm a ha
      have hyaB : a * y * a⁻¹ ∈ B₀ :=
        (Subgroup.mem_normalizer_iff.mp (mem_nrm.mp ha).2 y).mp hyB
      have e : y * (a * y⁻¹ * a⁻¹) = (y⁻¹ * (a * y * a⁻¹))⁻¹ := by
        have h1' := S.comm _ (B₀.inv_mem hyB) _ hyaB
        calc y * (a * y⁻¹ * a⁻¹) = (a * y * a⁻¹ * y⁻¹)⁻¹ := by group
          _ = (y⁻¹ * (a * y * a⁻¹))⁻¹ := by rw [← h1']
      rw [e]
      exact (nrm B₀ B₁).inv_mem h
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact key y hyB hcomm x
    · intro hx
      have := key y⁻¹ (B₀.inv_mem hyB) (fun a ha => by simpa using hcomm' a ha) _ hx
      rwa [show y⁻¹ * (y * x * y⁻¹) * y⁻¹⁻¹ = x by group] at this
  have hC : (nrm B₀ B₁ ⊔ nrm B₁ B₀) ⊓ Subgroup.centralizer ({y} : Set G) =
      (nrm B₀ B₁ ⊔ nrm B₁ B₀) ⊓ Subgroup.centralizer ({y ^ 2} : Set G) := by
    apply le_antisymm
    · intro q hq
      obtain ⟨hqQ, hqC⟩ := Subgroup.mem_inf.mp hq
      rw [Subgroup.mem_centralizer_singleton_iff] at hqC
      refine Subgroup.mem_inf.mpr ⟨hqQ, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff, sq]
      calc q * (y * y) = (q * y) * y := by group
        _ = (y * q) * y := by rw [hqC]
        _ = y * (q * y) := by group
        _ = y * (y * q) := by rw [hqC]
        _ = y * y * q := by group
    · intro q hq
      obtain ⟨hqQ, hqC⟩ := Subgroup.mem_inf.mp hq
      rw [Subgroup.mem_centralizer_singleton_iff, sq] at hqC
      have hqF := P.mem_L_of_commute_M hyL hyF hqQ hqC.symm
      refine Subgroup.mem_inf.mpr ⟨hqQ, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact S.comm _ (mem_nrm.mp hqF).1 _ hyB
  have hQc : IsMulCommutative ↥(nrm B₀ B₁ ⊔ nrm B₁ B₀) :=
    ⟨⟨fun a b => Subtype.ext (P.comm_M a.2 b.2)⟩⟩
  have hQ2 : IsPGroup 2 ↥(nrm B₀ B₁ ⊔ nrm B₁ B₀) := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one, sq]
    have := P.isElemAbelian_M.2 x x.2
    rwa [sq] at this)⟩
  have hcen := tim78_2_1 hQc hQ2 hyN ⟨2, by rw [show 2 ^ 2 = 4 by norm_num]; exact hy4⟩ hC
  obtain ⟨⟨f, hf⟩, hf1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp S.ne_bot₁
  have hf1 : f ≠ 1 := fun h => hf1' (Subtype.ext h)
  have hyf := hcen (Subgroup.mem_sup_right hf)
  rw [Subgroup.mem_centralizer_singleton_iff] at hyf
  have hyN₁ := S.mem_normalizer_of_commute₁ (mem_nrm.mp hf).1 hf1 hyf.symm
  exact hyy (h0 y (mem_nrm.mpr ⟨hyB, hyN₁⟩))

theorem comm_nrm (hne : B₀ ≠ B₁) {a b : G} (ha : a ∈ nrm B₀ B₁) (hb : b ∈ nrm B₁ B₀) :
    a * b = b * a := by
  obtain ⟨haB, haN⟩ := mem_nrm.mp ha
  obtain ⟨hbB, hbN⟩ := mem_nrm.mp hb
  have h1 : a * b * a⁻¹ * b⁻¹ ∈ B₁ :=
    B₁.mul_mem ((Subgroup.mem_normalizer_iff.mp haN b).mp hbB) (B₁.inv_mem hbB)
  have h2 : a * b * a⁻¹ * b⁻¹ ∈ B₀ := by
    rw [mul_assoc, mul_assoc]
    refine B₀.mul_mem haB ?_
    have := (Subgroup.mem_normalizer_iff.mp hbN a⁻¹).mp (B₀.inv_mem haB)
    rwa [← mul_assoc]
  have h3 : a * b * a⁻¹ * b⁻¹ ∈ B₀ ⊓ B₁ := Subgroup.mem_inf.mpr ⟨h2, h1⟩
  rw [S.inf_eq_bot hne, Subgroup.mem_bot] at h3
  calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
    _ = b * a := by rw [h3, one_mul]

end Setup210

end CFSG.RankThree.GF2n.Tim78
