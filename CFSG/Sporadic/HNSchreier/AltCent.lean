module

public import CFSG.Sporadic.HNSchreier.FALocal
public import CFSG.Sporadic.HNSchreier.SplitExt

public noncomputable section

namespace CFSG.Sporadic.HNSchreier

open Equiv Equiv.Perm

theorem tripleNat_one : tripleNat 1 = tri 0 1 2 := by decide

theorem tripleNat_three : tripleNat 3 = tri 0 1 2 * tri 3 4 5 * tri 6 7 8 := by decide

theorem isThreeCycle_tri {a b c : Fin 12} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (tri a b c).IsThreeCycle :=
  isThreeCycle_swap_mul_swap_same hac hab (Ne.symm hbc)

theorem cycleType_tri012 : (tri 0 1 2).cycleType = {3} :=
  isThreeCycle_tri (by decide) (by decide) (by decide)

theorem cycleType_tri3 : (tri 0 1 2 * tri 3 4 5 * tri 6 7 8).cycleType = {3, 3, 3} := by
  rw [Disjoint.cycleType_mul (by show ∀ x, _ ∨ _; unfold tri; decide),
    Disjoint.cycleType_mul (by show ∀ x, _ ∨ _; unfold tri; decide),
    isThreeCycle_tri (by decide) (by decide) (by decide),
    isThreeCycle_tri (by decide) (by decide) (by decide),
    isThreeCycle_tri (by decide) (by decide) (by decide)]
  rfl

theorem card_centralizer_tri012 : Nat.card (Subgroup.centralizer {tri 0 1 2}) = 1088640 := by
  rw [Equiv.Perm.nat_card_centralizer, cycleType_tri012]
  decide

theorem card_centralizer_tri3 :
    Nat.card (Subgroup.centralizer {tri 0 1 2 * tri 3 4 5 * tri 6 7 8}) = 972 := by
  rw [Equiv.Perm.nat_card_centralizer, cycleType_tri3]
  decide

theorem card_inf_alt_of_odd {K : Subgroup (Perm (Fin 12))} {τ : Perm (Fin 12)} (hτ : τ ∈ K)
    (hodd : sign τ = -1) :
    Nat.card (K ⊓ alternatingGroup (Fin 12) : Subgroup (Perm (Fin 12))) * 2 = Nat.card K := by
  let φ : K →* ℤˣ := sign.comp K.subtype
  have hsurj : Function.Surjective φ := by
    intro u
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact ⟨1, map_one φ⟩
    · exact ⟨⟨τ, hτ⟩, hodd⟩
  have hrange : Nat.card φ.range = 2 := by
    rw [MonoidHom.range_eq_top.2 hsurj, Subgroup.card_top, Nat.card_eq_fintype_card,
      Fintype.card_units_int]
  have hker : Nat.card φ.ker = Nat.card (K ⊓ alternatingGroup (Fin 12) : Subgroup _) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1.1, Subgroup.mem_inf.2 ⟨x.1.2, (MonoidHom.mem_ker.1 x.2 :)⟩⟩
        invFun := fun x => ⟨⟨x.1, (Subgroup.mem_inf.1 x.2).1⟩, MonoidHom.mem_ker.2
          (Subgroup.mem_inf.1 x.2).2⟩
        left_inv := fun x => rfl
        right_inv := fun x => rfl }
  rw [← hker, ← hrange, ← Subgroup.index_ker, Subgroup.card_mul_index]

theorem tri012_comm_swap34 : tri 0 1 2 * swap 3 4 = swap 3 4 * tri 0 1 2 := by
  unfold tri; decide

theorem tri3_comm_swap910 : tri 0 1 2 * tri 3 4 5 * tri 6 7 8 * swap 9 10 =
    swap 9 10 * (tri 0 1 2 * tri 3 4 5 * tri 6 7 8) := by
  unfold tri; decide

theorem card_centralizer_tri012_alt :
    Nat.card (Subgroup.centralizer {tri 0 1 2} ⊓ alternatingGroup (Fin 12) :
      Subgroup (Perm (Fin 12))) = 544320 := by
  have h := card_inf_alt_of_odd (K := Subgroup.centralizer {tri 0 1 2}) (τ := swap 3 4)
    (Subgroup.mem_centralizer_singleton_iff.2 tri012_comm_swap34.symm)
    (sign_swap (by decide))
  rw [card_centralizer_tri012] at h
  omega

theorem card_centralizer_tri3_alt :
    Nat.card (Subgroup.centralizer {tri 0 1 2 * tri 3 4 5 * tri 6 7 8} ⊓
      alternatingGroup (Fin 12) : Subgroup (Perm (Fin 12))) = 486 := by
  have h := card_inf_alt_of_odd (K := Subgroup.centralizer {tri 0 1 2 * tri 3 4 5 * tri 6 7 8})
    (τ := swap 9 10) (Subgroup.mem_centralizer_singleton_iff.2 tri3_comm_swap910.symm)
    (sign_swap (by decide))
  rw [card_centralizer_tri3] at h
  omega

theorem card_centralizer_alt (a : alternatingGroup (Fin 12)) :
    Nat.card (Subgroup.centralizer {a}) = Nat.card (Subgroup.centralizer {(a : Perm (Fin 12))} ⊓
      alternatingGroup (Fin 12) : Subgroup (Perm (Fin 12))) := by
  refine Nat.card_congr
    { toFun := fun x => ⟨x.1.1, Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 x.2)), x.1.2⟩⟩
      invFun := fun x => ⟨⟨x.1, (Subgroup.mem_inf.1 x.2).2⟩,
        Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext
          (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 x.2).1))⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl }

@[expose] def alt3 : Subgroup (alternatingGroup (Fin 12)) :=
  (fixingSubgroup (Perm (Fin 12)) {i : Fin 12 | i.val < 3}).comap
    (alternatingGroup (Fin 12)).subtype

theorem mem_alt3 (σ : alternatingGroup (Fin 12)) :
    σ ∈ alt3 ↔ ∀ i : Fin 12, i.val < 3 → (σ : Perm (Fin 12)) i = i := by
  rw [alt3, Subgroup.mem_comap, mem_fixingSubgroup_iff]
  exact ⟨fun h i hi => h i hi, fun h i hi => h i hi⟩

@[expose] def shift3 : Fin 9 ≃ {i : Fin 12 // 3 ≤ i.val} where
  toFun j := ⟨⟨j.val + 3, by omega⟩, by simp⟩
  invFun i := ⟨i.1.val - 3, by have := i.1.isLt; omega⟩
  left_inv j := by ext; simp
  right_inv i := by
    apply Subtype.ext
    apply Fin.ext
    have := i.2
    simp only
    omega

abbrev ext3 : Perm (Fin 9) →* Perm (Fin 12) := extendDomainHom shift3

theorem ext3_fix (τ : Perm (Fin 9)) {i : Fin 12} (hi : i.val < 3) : ext3 τ i = i := by
  rw [extendDomainHom_apply]
  exact extendDomain_apply_not_subtype τ shift3 (by omega)

theorem ext3_mem (τ : alternatingGroup (Fin 9)) : ext3 τ ∈ alternatingGroup (Fin 12) := by
  rw [mem_alternatingGroup, extendDomainHom_apply, sign_extendDomain]
  exact τ.2

@[expose] def alt9Hom : alternatingGroup (Fin 9) →* alt3 where
  toFun τ := ⟨⟨ext3 τ, ext3_mem τ⟩, (mem_alt3 _).2 fun _ hi => ext3_fix τ hi⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp

theorem alt9Hom_injective : Function.Injective alt9Hom := fun _ _ h =>
  Subtype.ext (extendDomainHom_injective shift3 (congrArg (fun x : alt3 =>
    ((x : alternatingGroup (Fin 12)) : Perm (Fin 12))) h))

theorem alt9Hom_surjective : Function.Surjective alt9Hom := by
  rintro ⟨⟨σ, hσ⟩, hfix⟩
  have hfix' := (mem_alt3 _).1 hfix
  have hge : ∀ i : Fin 12, 3 ≤ i.val → 3 ≤ (σ i).val := by
    intro i hi
    by_contra h
    have e := hfix' (σ i) (by omega)
    exact absurd (σ.injective e) (by intro h'; rw [h'] at h; omega)
  have hge' : ∀ i : Fin 12, 3 ≤ i.val → 3 ≤ (σ⁻¹ i).val := by
    intro i hi
    by_contra h
    have e := hfix' (σ⁻¹ i) (by omega)
    rw [Perm.coe_inv, Equiv.apply_symm_apply] at e
    rw [Perm.coe_inv, ← e] at h
    omega
  let τ : Perm (Fin 9) :=
    { toFun := fun j => shift3.symm ⟨σ (shift3 j), hge _ (shift3 j).2⟩
      invFun := fun j => shift3.symm ⟨σ⁻¹ (shift3 j), hge' _ (shift3 j).2⟩
      left_inv := fun j => by simp
      right_inv := fun j => by simp }
  have hτ : ext3 τ = σ := by
    ext i
    by_cases hi : 3 ≤ i.val
    · rw [extendDomainHom_apply]
      have := extendDomain_apply_subtype τ shift3 (b := i) hi
      rw [this]
      simp [τ]
    · rw [ext3_fix τ (by omega), hfix' i (by omega)]
  refine ⟨⟨τ, ?_⟩, ?_⟩
  · rw [mem_alternatingGroup, ← sign_extendDomain τ shift3, ← extendDomainHom_apply, hτ]
    exact hσ
  · apply Subtype.ext
    apply Subtype.ext
    exact hτ

@[expose] def alt9Equiv : alternatingGroup (Fin 9) ≃* alt3 :=
  MulEquiv.ofBijective alt9Hom ⟨alt9Hom_injective, alt9Hom_surjective⟩

theorem alt3_simple : IsSimpleGroup alt3 := by
  have : IsSimpleGroup (alternatingGroup (Fin 9)) := alternatingGroup.isSimpleGroup (by simp)
  exact MulEquiv.isSimpleGroup alt9Equiv.symm

theorem card_alt3 : Nat.card alt3 = 181440 := by
  rw [← Nat.card_congr alt9Equiv.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
    Fintype.card_fin]
  decide

theorem commutator_alt3 : commutator alt3 = ⊤ := by
  have := alt3_simple
  exact commutator_eq_top_of_simple (by rw [card_alt3]; norm_num)

@[expose] def tri012A : alternatingGroup (Fin 12) :=
  ⟨tri 0 1 2, (isThreeCycle_tri (by decide) (by decide) (by decide)).mem_alternatingGroup⟩

theorem tri012A_val : (tri012A : Perm (Fin 12)) = tri 0 1 2 := rfl

theorem tri012_pow_three : tri 0 1 2 ^ 3 = 1 := by unfold tri; decide

theorem comm_tri012_of_fix {σ : Perm (Fin 12)} (h : ∀ i : Fin 12, i.val < 3 → σ i = i) :
    σ * tri 0 1 2 = tri 0 1 2 * σ := by
  ext i
  rw [Perm.mul_apply, Perm.mul_apply]
  by_cases hi : i.val < 3
  · have h1 : (tri 0 1 2 i).val < 3 := by revert i; unfold tri; decide
    rw [h _ h1, h i hi]
  · have h2 : 3 ≤ (σ i).val := by
      by_contra hc
      have e := h (σ i) (by omega)
      exact hi (by rw [← σ.injective e]; omega)
    have h3 : ∀ j : Fin 12, 3 ≤ j.val → tri 0 1 2 j = j := by unfold tri; decide
    rw [h3 i (by omega), h3 _ h2]

theorem exists_tri012_decomp {σ : alternatingGroup (Fin 12)}
    (hσ : σ ∈ Subgroup.centralizer {tri012A}) : ∃ k : ℕ, (tri012A ^ k)⁻¹ * σ ∈ alt3 := by
  have hc := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hσ)
  simp only [Subgroup.coe_mul] at hc
  rw [tri012A_val] at hc
  have h3 : ∀ j : Fin 12, 3 ≤ j.val → tri 0 1 2 j = j := by unfold tri; decide
  have hm : ∀ j : Fin 12, j.val < 3 → tri 0 1 2 j ≠ j := by unfold tri; decide
  have hsupp : ∀ i : Fin 12, i.val < 3 → ((σ : Perm (Fin 12)) i).val < 3 := by
    intro i hi
    by_contra hn
    have e : (σ : Perm (Fin 12)) (tri 0 1 2 i) = tri 0 1 2 ((σ : Perm (Fin 12)) i) := by
      have := congrArg (fun f : Perm (Fin 12) => f i) hc
      simpa only [Perm.mul_apply] using this
    rw [h3 ((σ : Perm (Fin 12)) i) (by omega)] at e
    exact hm i hi ((σ : Perm (Fin 12)).injective e)
  obtain ⟨k, hk⟩ : ∃ k : Fin 3, (σ : Perm (Fin 12)) 0 = (tri 0 1 2 ^ k.val) 0 := by
    have h0 := hsupp 0 (by decide)
    have : ∀ x : Fin 12, x.val < 3 → ∃ k : Fin 3, x = (tri 0 1 2 ^ k.val) 0 := by
      unfold tri; decide
    obtain ⟨k, e⟩ := this _ h0
    exact ⟨k, e⟩
  set ρ : alternatingGroup (Fin 12) := tri012A ^ k.val
  have hρ : (ρ : Perm (Fin 12)) = tri 0 1 2 ^ k.val := by simp [ρ, tri012A]
  have hτ : ρ⁻¹ * σ ∈ alt3 := by
    rw [mem_alt3]
    have hfix0 : ((ρ⁻¹ * σ : alternatingGroup (Fin 12)) : Perm (Fin 12)) 0 = 0 := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Perm.mul_apply, hρ, hk]
      rw [Perm.coe_inv, Equiv.symm_apply_apply]
    have hcomm' : ((ρ⁻¹ * σ : alternatingGroup (Fin 12)) : Perm (Fin 12)) * tri 0 1 2 =
        tri 0 1 2 * ((ρ⁻¹ * σ : alternatingGroup (Fin 12)) : Perm (Fin 12)) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hρ]
      rw [mul_assoc, hc, ← mul_assoc, (Commute.pow_left (Commute.refl _) _).inv_left.eq,
        mul_assoc]
    intro i hi
    have h1 : (1 : Fin 12) = tri 0 1 2 0 := by unfold tri; decide
    have h2 : (2 : Fin 12) = tri 0 1 2 1 := by unfold tri; decide
    interval_cases hv : i.val
    · have : i = 0 := Fin.ext hv; rw [this]; exact hfix0
    · have : i = 1 := Fin.ext hv
      rw [this, h1, ← Perm.mul_apply, hcomm', Perm.mul_apply, hfix0]
    · have : i = 2 := Fin.ext hv
      have hfix1 : ((ρ⁻¹ * σ : alternatingGroup (Fin 12)) : Perm (Fin 12)) 1 = 1 := by
        rw [h1, ← Perm.mul_apply, hcomm', Perm.mul_apply, hfix0]
      rw [this, h2, ← Perm.mul_apply, hcomm', Perm.mul_apply, hfix1]
  exact ⟨k.val, hτ⟩

theorem centralizer_tri012 :
    Subgroup.centralizer {tri012A} = Subgroup.zpowers tri012A ⊔ alt3 ∧
      Subgroup.zpowers tri012A ⊓ alt3 = ⊥ ∧ ∀ σ ∈ alt3, σ * tri012A = tri012A * σ := by
  have hcomm : ∀ σ ∈ alt3, σ * tri012A = tri012A * σ := fun σ hσ =>
    Subtype.ext (comm_tri012_of_fix ((mem_alt3 σ).1 hσ))
  refine ⟨le_antisymm ?_ ?_, ?_, hcomm⟩
  · intro σ hσ
    obtain ⟨k, hτ⟩ := exists_tri012_decomp hσ
    have : σ = tri012A ^ k * ((tri012A ^ k)⁻¹ * σ) := by group
    rw [this]
    exact Subgroup.mul_mem_sup (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _) hτ
  · rw [sup_le_iff]
    constructor
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_singleton_iff.2 rfl
    · intro σ hσ
      exact Subgroup.mem_centralizer_singleton_iff.2 (hcomm σ hσ)
  · have hk : ∀ k : ℤ, (tri 0 1 2 ^ k) 0 = 0 → tri 0 1 2 ^ k = 1 := by
      intro k hk
      have e : tri 0 1 2 ^ k = tri 0 1 2 ^ (k % 3) := by
        rw [← zpow_mod_orderOf, show orderOf (tri 0 1 2) = 3 from
          orderOf_eq_prime tri012_pow_three (by unfold tri; decide)]
        rfl
      have hm : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
      rw [e] at hk ⊢
      rcases hm with h | h | h
      · rw [h, zpow_zero]
      · rw [h] at hk; exfalso; revert hk; unfold tri; decide
      · rw [h] at hk; exfalso; revert hk; unfold tri; decide
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hz, hx3⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    rw [Subgroup.mem_bot]
    have h0 := (mem_alt3 _).1 hx3 0 (by decide)
    apply Subtype.ext
    rw [SubgroupClass.coe_zpow, tri012A_val] at h0 ⊢
    exact hk k h0

open scoped commutatorElement

theorem commutator_mul_mul_of_commute {G : Type*} [Group G] {a b a' b' : G} (h1 : Commute a a')
    (h2 : Commute a b) (h3 : Commute a b') (h4 : Commute a' b) (h5 : Commute a' b') :
    ⁅a * b, a' * b'⁆ = ⁅b, b'⁆ := by
  have hc : Commute (a * a') ⁅b, b'⁆ := by
    rw [commutatorElement_def]
    have hb : Commute (a * a') b := h2.mul_left h4
    have hb' : Commute (a * a') b' := h3.mul_left h5
    exact ((hb.mul_right hb').mul_right hb.inv_right).mul_right hb'.inv_right
  have e : ⁅a * b, a' * b'⁆ = (a * a') * ⁅b, b'⁆ * (a * a')⁻¹ := by
    rw [commutatorElement_def, commutatorElement_def]
    simp only [mul_inv_rev, mul_assoc]
    rw [← mul_assoc b a', ← h4.eq, mul_assoc a' b]
    congr 3
    rw [← mul_assoc a⁻¹ b'⁻¹, h3.inv_inv.eq, mul_assoc b'⁻¹ a⁻¹, h1.inv_inv.eq]
  rw [e, hc.eq, mul_inv_cancel_right]

theorem commutator_centralizer_tri012 :
    ⁅Subgroup.centralizer {tri012A}, Subgroup.centralizer {tri012A}⁆ = alt3 := by
  obtain ⟨hC, -, hcomm⟩ := centralizer_tri012
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro x hx y hy
    obtain ⟨k, hk⟩ := exists_tri012_decomp hx
    obtain ⟨l, hl⟩ := exists_tri012_decomp hy
    have ex : x = tri012A ^ k * ((tri012A ^ k)⁻¹ * x) := by group
    have ey : y = tri012A ^ l * ((tri012A ^ l)⁻¹ * y) := by group
    have hcp : ∀ (m : ℕ) (z : alternatingGroup (Fin 12)), z ∈ alt3 → Commute (tri012A ^ m) z :=
      fun m z hz => (Commute.pow_left (hcomm z hz).symm m)
    rw [ex, ey, commutator_mul_mul_of_commute ((Commute.refl tri012A).pow_pow k l) (hcp k _ hk)
      (hcp k _ hl) (hcp l _ hk) (hcp l _ hl)]
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hk hl) (inv_mem hk)) (inv_mem hl)
  · have h1 : ⁅alt3, alt3⁆ = alt3 := by
      have := congrArg (Subgroup.map alt3.subtype) commutator_alt3
      rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype] at this
      exact this
    rw [← h1]
    refine Subgroup.commutator_mono ?_ ?_ <;> rw [hC] <;> exact le_sup_right

end CFSG.Sporadic.HNSchreier
