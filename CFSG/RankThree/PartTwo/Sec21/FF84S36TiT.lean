module

public import CFSG.GH74.M12.T1Basic
public import CFSG.GF2Type.Aschbacher1976Full.WidthBasic

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S3

open CFSG.Quasithin

theorem S36_ext_fwd {H K : Type} [Group H] [Group K] (f : H →* K) (hf : Function.Injective f)
    {Q : Subgroup H} {z : H} (h : ExtraspecialAt Q z) : ExtraspecialAt (Q.map f) (f z) where
  card_eq := by rw [Subgroup.card_map_of_injective hf]; exact h.card_eq
  mem := Subgroup.mem_map_of_mem f h.mem
  ne_one := fun h1 => h.ne_one (hf (by rw [h1, map_one]))
  sq_eq := by rw [← map_mul, h.sq_eq, map_one]
  central := by
    intro q' hq'
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.1 hq'
    rw [← map_mul, ← map_mul, h.central q hq]
  center_le := by
    intro q' hq' hc
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.1 hq'
    have hcq : ∀ y ∈ Q, q * y = y * q := fun y hy => hf (by
      rw [map_mul, map_mul]; exact hc _ (Subgroup.mem_map_of_mem f hy))
    rcases h.center_le q hq hcq with h1 | h1
    · exact Or.inl (by rw [h1, map_one])
    · exact Or.inr (by rw [h1])
  sq_mem := by
    intro q' hq'
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.1 hq'
    rw [← map_mul]
    rcases h.sq_mem q hq with h1 | h1
    · exact Or.inl (by rw [h1, map_one])
    · exact Or.inr (by rw [h1])
  comm_mem := by
    intro q' hq' y' hy'
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.1 hq'
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hy'
    have e : f q * f y * (f q)⁻¹ * (f y)⁻¹ = f (q * y * q⁻¹ * y⁻¹) := by
      simp only [map_mul, map_inv]
    rw [e]
    rcases h.comm_mem q hq y hy with h1 | h1
    · exact Or.inl (by rw [h1, map_one])
    · exact Or.inr (by rw [h1])

theorem S36_ext_refl {H K : Type} [Group H] [Group K] (f : H →* K) (hf : Function.Injective f)
    {Q : Subgroup H} {z : H} (h : ExtraspecialAt (Q.map f) (f z)) : ExtraspecialAt Q z where
  card_eq := by rw [← Subgroup.card_map_of_injective hf]; exact h.card_eq
  mem := by
    obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.1 h.mem
    have : y = z := hf hyz
    rw [← this]
    exact hy
  ne_one := fun h1 => h.ne_one (by rw [h1, map_one])
  sq_eq := hf (by rw [map_mul, h.sq_eq, map_one])
  central := by
    intro q hq
    apply hf
    rw [map_mul, map_mul]
    exact h.central (f q) (Subgroup.mem_map_of_mem f hq)
  center_le := by
    intro q hq hc
    have hc' : ∀ y' ∈ Q.map f, f q * y' = y' * f q := by
      intro y' hy'
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hy'
      rw [← map_mul, ← map_mul, hc y hy]
    rcases h.center_le (f q) (Subgroup.mem_map_of_mem f hq) hc' with h1 | h1
    · exact Or.inl (hf (by rw [h1, map_one]))
    · exact Or.inr (hf h1)
  sq_mem := by
    intro q hq
    rcases h.sq_mem (f q) (Subgroup.mem_map_of_mem f hq) with h1 | h1
    · left
      apply hf
      rw [map_mul, h1, map_one]
    · right
      apply hf
      rw [map_mul, h1]
  comm_mem := by
    intro q hq y hy
    have e : f (q * y * q⁻¹ * y⁻¹) = f q * f y * (f q)⁻¹ * (f y)⁻¹ := by
      simp only [map_mul, map_inv]
    rcases h.comm_mem (f q) (Subgroup.mem_map_of_mem f hq) (f y)
        (Subgroup.mem_map_of_mem f hy) with h1 | h1
    · left
      apply hf
      rw [e, h1, map_one]
    · right
      apply hf
      rw [e, h1]

theorem S36_zpowers_two {G : Type} [Group G] {s x : G} (hs2 : s * s = 1) (hs1 : s ≠ 1)
    (hx : x ∈ Subgroup.zpowers s) : x = 1 ∨ x = s := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf s = 2 := orderOf_eq_prime (by rw [sq]; exact hs2) hs1
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  have hmod := zpow_mod_orderOf s k
  rw [hord] at hmod
  have hk : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by omega
  rcases hk with h0 | h1
  · left
    rw [← hmod, h0, zpow_zero]
  · right
    rw [← hmod, h1, zpow_one]

theorem S36_isExtraspecial_of_ext {G : Type} [Group G] [Finite G] {Q : Subgroup G} {z : G}
    (h : ExtraspecialAt Q z) : IsExtraspecialPGroup 2 ↥Q := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz2 : z * z = 1 := h.sq_eq
  have hz1 : z ≠ 1 := h.ne_one
  have hordz : orderOf z = 2 := orderOf_eq_prime (by rw [sq]; exact hz2) hz1
  have hP : IsPGroup 2 ↥Q := IsPGroup.of_card (show Nat.card ↥Q = 2 ^ 5 by rw [h.card_eq]; norm_num)
  haveI : Fact (IsPGroup 2 ↥Q) := ⟨hP⟩
  have hzc : ∀ x : ↥Q, x ∈ Subgroup.center ↥Q ↔ (x : G) = 1 ∨ (x : G) = z := by
    intro x
    constructor
    · intro hx
      have hxc : ∀ y ∈ Q, (x : G) * y = y * (x : G) := fun y hy =>
        (congrArg Subtype.val (Subgroup.mem_center_iff.1 hx ⟨y, hy⟩)).symm
      exact h.center_le x x.2 hxc
    · intro hx
      refine Subgroup.mem_center_iff.2 (fun g => Subtype.ext ?_)
      rcases hx with h1 | h1
      · simp only [Subgroup.coe_mul, h1, mul_one, one_mul]
      · simp only [Subgroup.coe_mul]
        rw [h1]
        exact h.central g.1 g.2
  have hcomm_le : commutator ↥Q ≤ Subgroup.center ↥Q := by
    refine Subgroup.commutator_le.2 (fun x _ y _ => ?_)
    refine (hzc _).2 ?_
    rw [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      Subgroup.coe_inv]
    exact h.comm_mem x.1 x.2 y.1 y.2
  have hnoncomm : ∃ a ∈ Q, ∃ b ∈ Q, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have hsub : Q ≤ Subgroup.zpowers z := by
      intro a ha
      have hac : ∀ b ∈ Q, a * b = b * a := fun b hb => hcon a ha b hb
      rcases h.center_le a ha hac with h1 | h1
      · rw [h1]
        exact one_mem _
      · rw [h1]
        exact Subgroup.mem_zpowers z
    have h1 := Subgroup.card_le_of_le hsub
    rw [Nat.card_zpowers, hordz, h.card_eq] at h1
    omega
  have hcenter_le : Subgroup.center ↥Q ≤ commutator ↥Q := by
    intro x hx
    rcases (hzc x).1 hx with h1 | h1
    · have hx1 : x = 1 := Subtype.ext (by simpa using h1)
      rw [hx1]
      exact one_mem _
    · obtain ⟨a, ha, b, hb, hab⟩ := hnoncomm
      obtain ⟨c, hc, hcz⟩ : ∃ c ∈ commutator ↥Q, (c : G) = z := by
        refine ⟨_, Subgroup.commutator_mem_commutator (Subgroup.mem_top (⟨a, ha⟩ : ↥Q))
          (Subgroup.mem_top (⟨b, hb⟩ : ↥Q)), ?_⟩
        rw [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
          Subgroup.coe_inv]
        rcases h.comm_mem a ha b hb with h2 | h2
        · exfalso
          apply hab
          exact commutatorElement_eq_one_iff_mul_comm.1 (by rw [commutatorElement_def]; exact h2)
        · exact h2
      have hxc : x = c := Subtype.ext (by rw [hcz, h1])
      rw [hxc]
      exact hc
  have hcomm_eq : commutator ↥Q = Subgroup.center ↥Q := le_antisymm hcomm_le hcenter_le
  have hfr_le : frattini ↥Q ≤ commutator ↥Q := by
    rw [CFSG.frattini_eq_closure_commutator_union_powers (R := Q) (p := 2),
      Subgroup.closure_le]
    rintro x (hx | ⟨y, rfl⟩)
    · exact hx
    · show y ^ 2 ∈ commutator ↥Q
      rw [sq, hcomm_eq]
      refine (hzc (y * y)).2 ?_
      rw [Subgroup.coe_mul]
      exact h.sq_mem y.1 y.2
  have hcomm_fr : commutator ↥Q ≤ frattini ↥Q := CFSG.commutator_le_frattini_of_isPGroup (p := 2)
  have hfr_eq : frattini ↥Q = Subgroup.center ↥Q :=
    le_antisymm (hfr_le.trans hcomm_eq.le) (hcomm_eq.symm.le.trans hcomm_fr)
  have hw : (⟨z, h.mem⟩ : ↥Q) ∈ Subgroup.center ↥Q := (hzc _).2 (Or.inr rfl)
  have hZ : Subgroup.center ↥Q = Subgroup.zpowers (⟨z, h.mem⟩ : ↥Q) := by
    refine le_antisymm (fun x hx => ?_) (Subgroup.zpowers_le.2 hw)
    rcases (hzc x).1 hx with h1 | h1
    · have hx1 : x = 1 := Subtype.ext (by simpa using h1)
      rw [hx1]
      exact one_mem _
    · have : x = ⟨z, h.mem⟩ := Subtype.ext h1
      rw [this]
      exact Subgroup.mem_zpowers _
  have hcZ : Nat.card (Subgroup.center ↥Q) = 2 := by
    rw [hZ, Nat.card_zpowers]
    have : orderOf (⟨z, h.mem⟩ : ↥Q) = 2 := by
      rw [← Subgroup.orderOf_coe]
      exact hordz
    rw [this]
  exact ⟨hP, hcomm_eq, hfr_eq, hcZ⟩

theorem S36_z_mem_of_card_eight {G : Type} [Group G] [Finite G] {Q : Subgroup G} {z : G}
    (h : ExtraspecialAt Q z) {A : Subgroup G} (hA : A ≤ Q) (hA8 : Nat.card A = 8)
    (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) : z ∈ A :=
  CFSG.GH74.M12.Thm1.z_mem_of_card_eight h hA hA8 hAab

theorem S36_ext_of_isExtraspecial {G : Type} [Group G] [Finite G] {Q : Subgroup G} {s : G}
    (hQ : IsExtraspecialPGroup 2 ↥Q) (hcard : Nat.card Q = 32) (hsQ : s ∈ Q) (hs2 : s * s = 1)
    (hs1 : s ≠ 1) (hZ : Subgroup.center ↥Q = (Subgroup.zpowers s).subgroupOf Q) :
    ExtraspecialAt Q s := by
  have hsc : ∀ x : ↥Q, x ∈ Subgroup.center ↥Q ↔ (x : G) ∈ Subgroup.zpowers s := fun x => by
    rw [hZ, Subgroup.mem_subgroupOf]
  have hsc' : (⟨s, hsQ⟩ : ↥Q) ∈ Subgroup.center ↥Q := (hsc _).2 (Subgroup.mem_zpowers s)
  refine
    { card_eq := hcard
      mem := hsQ
      ne_one := hs1
      sq_eq := hs2
      central := fun q hq => ?_
      center_le := fun q hq hc => ?_
      sq_mem := fun q hq => ?_
      comm_mem := fun q hq y hy => ?_ }
  · exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hsc' ⟨q, hq⟩)
  · have hqc : (⟨q, hq⟩ : ↥Q) ∈ Subgroup.center ↥Q :=
      Subgroup.mem_center_iff.2 (fun g => Subtype.ext (by
        simp only [Subgroup.coe_mul]; exact (hc g.1 g.2).symm))
    exact S36_zpowers_two hs2 hs1 ((hsc _).1 hqc)
  · have h2 : (⟨q, hq⟩ : ↥Q) ^ 2 ∈ frattini ↥Q :=
      CFSG.GF2Type.Aschbacher1976Full.Width.sq_mem_frattini_two hQ.1 _
    rw [hQ.2.2.1] at h2
    have h3 : q * q ∈ Subgroup.zpowers s := by
      have := (hsc _).1 h2
      simpa [sq] using this
    exact S36_zpowers_two hs2 hs1 h3
  · obtain ⟨c, hc, hcval⟩ : ∃ c ∈ commutator ↥Q, (c : G) = q * y * q⁻¹ * y⁻¹ := by
      refine ⟨_, Subgroup.commutator_mem_commutator (Subgroup.mem_top (⟨q, hq⟩ : ↥Q))
        (Subgroup.mem_top (⟨y, hy⟩ : ↥Q)), ?_⟩
      simp [commutatorElement_def]
    rw [hQ.2.1] at hc
    have h4 := (hsc c).1 hc
    rw [hcval] at h4
    exact S36_zpowers_two hs2 hs1 h4

end CFSG.RankThree.PartTwo.Sec21.FF84.S3

end
