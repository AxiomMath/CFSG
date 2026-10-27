module

public import CFSG.OddTranspositions.PartThree.Nine.FiveUnitaryLocal
import CFSG.OddTranspositions.PartThree.Ten.SetupPerfect
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_8_27
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.OddTranspositions.PartThree.Nine

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity CFSG.BenderSuzuki

section Generic

variable {X : Type*} [Group X]

private theorem commute_of_mul_self_eq_one' {a b : X} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b * (a * b) = 1) : a * b = b * a := by
  rw [← inv_eq_of_mul_eq_one_right hab, mul_inv_rev, inv_eq_of_mul_eq_one_right ha,
    inv_eq_of_mul_eq_one_right hb]

private theorem eq_one_or_eq_of_mem_zpowers' {a y : X} (ha : a * a = 1)
    (hy : y ∈ Subgroup.zpowers a) : y = 1 ∨ y = a := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have h2 : a ^ (2 : ℤ) = 1 := by rw [zpow_two, ha]
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
  · left
    rw [zpow_mul, h2, one_zpow]
  · right
    rw [zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

private theorem mem_normalizer_of_forall_conj_mem' [Finite X] {A : Subgroup X} {g : X}
    (h : ∀ a ∈ A, g * a * g⁻¹ ∈ A) : g ∈ Subgroup.normalizer (A : Set X) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩
    exact h a ha
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

private theorem eq_one_of_odd_of_isPGroup {L : Subgroup X} (hL : Odd (Nat.card L)) {x : X}
    (hxL : x ∈ L) (hx : IsPGroup 2 (Subgroup.zpowers x)) : x = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hx ⟨x, Subgroup.mem_zpowers x⟩
  rw [Subgroup.orderOf_mk] at hk
  have hdvd := Subgroup.orderOf_dvd_natCard L hxL
  rw [hk] at hdvd
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · rwa [hk0, pow_zero, orderOf_eq_one_iff] at hk
  · exact absurd (Odd.of_dvd_nat hL hdvd)
      (Nat.not_odd_iff_even.mpr (Nat.even_pow.mpr ⟨even_two, hk0.ne'⟩))

private theorem isPGroup_zpowers_of_pow_eq_one {x : X} {k : ℕ} (hk : x ^ 2 ^ k = 1) :
    IsPGroup 2 (Subgroup.zpowers x) := by
  rintro ⟨y, hy⟩
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  refine ⟨k, Subtype.ext ?_⟩
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]

private theorem commute_of_forall_conj_eq_inv' {L : Subgroup X} {a : X}
    (ha : ∀ l ∈ L, a * l * a⁻¹ = l⁻¹) {l l' : X} (hl : l ∈ L) (hl' : l' ∈ L) :
    Commute l l' := by
  have h1 := ha _ (L.mul_mem hl hl')
  have h2 : a * (l * l') * a⁻¹ = (a * l * a⁻¹) * (a * l' * a⁻¹) := by group
  rw [h2, ha l hl, ha l' hl', mul_inv_rev] at h1
  have h3 := congrArg (·⁻¹) h1
  simp only [mul_inv_rev, inv_inv] at h3
  exact h3.symm

variable [Finite X] {T L L₀ B : Subgroup X}

private theorem inf_eq_bot_of_dihedral (hB : B = T ⊔ L₀)
    (hTn : ∀ b ∈ B, ∀ t ∈ T, b * t * b⁻¹ ∈ T) (hT : IsPGroup 2 T) (hLo : Odd (Nat.card L))
    (hL1 : L ≠ ⊥) (hLL₀ : L ≤ L₀)
    (hL₀ : L₀ = L ∨ ∃ a ∈ L₀, a * a = 1 ∧ a ∉ L ∧ (∀ l ∈ L, a * l * a⁻¹ = l⁻¹) ∧
      L₀ = L ⊔ Subgroup.zpowers a) {y : X} (hyT : y ∈ T) (hyL₀ : y ∈ L₀) : y = 1 := by
  have hL₀B : L₀ ≤ B := by
    rw [hB]
    exact le_sup_right
  have hTp : ∀ x ∈ T, IsPGroup 2 (Subgroup.zpowers x) := fun x hx =>
    hT.to_le (Subgroup.zpowers_le.mpr hx)
  have hLT : ∀ l ∈ L, l ∈ T → l = 1 := fun l hl hlT => eq_one_of_odd_of_isPGroup hLo hl (hTp l hlT)
  rcases hL₀ with hL₀ | ⟨a, -, ha2, -, hainv, hL₀eq⟩
  · exact hLT y (hL₀ ▸ hyL₀) hyT
  · have hzL : Subgroup.zpowers a ≤ Subgroup.normalizer (L : Set X) := by
      rw [Subgroup.zpowers_le]
      exact mem_normalizer_of_forall_conj_mem' fun l hl => by
        rw [hainv l hl]
        exact L.inv_mem hl
    have hy' : y ∈ ((L ⊔ Subgroup.zpowers a : Subgroup X) : Set X) := by
      rw [← hL₀eq]
      exact hyL₀
    rw [Subgroup.coe_mul_of_right_le_normalizer_left L _ hzL] at hy'
    obtain ⟨l, hl, w, hw, hlw⟩ := Set.mem_mul.mp hy'
    rcases eq_one_or_eq_of_mem_zpowers' ha2 hw with hw1 | hwa
    · rw [← hlw, hw1, mul_one] at hyT ⊢
      exact hLT l hl hyT
    · exfalso
      rw [← hlw, hwa] at hyT
      apply hL1
      rw [eq_bot_iff]
      intro l' hl'
      rw [Subgroup.mem_bot]
      have he : l * a * l' * (l * a)⁻¹ * l'⁻¹ = l'⁻¹ * l'⁻¹ := by
        have h1 : a * l' * a⁻¹ = l'⁻¹ := hainv l' hl'
        have h2 : l * l'⁻¹ = l'⁻¹ * l :=
          (commute_of_forall_conj_eq_inv' hainv hl (L.inv_mem hl')).eq
        calc l * a * l' * (l * a)⁻¹ * l'⁻¹ = l * (a * l' * a⁻¹) * l⁻¹ * l'⁻¹ := by group
          _ = l * l'⁻¹ * l⁻¹ * l'⁻¹ := by rw [h1]
          _ = l'⁻¹ * l * l⁻¹ * l'⁻¹ := by rw [h2]
          _ = l'⁻¹ * l'⁻¹ := by group
      have hmem : l'⁻¹ * l'⁻¹ ∈ T := by
        rw [← he]
        have h3 := hTn l' (hL₀B (hLL₀ hl')) _ (T.inv_mem hyT)
        have e : l * a * l' * (l * a)⁻¹ * l'⁻¹ = (l * a) * (l' * (l * a)⁻¹ * l'⁻¹) := by group
        rw [e]
        exact T.mul_mem hyT h3
      have h4 := hLT _ (L.mul_mem (L.inv_mem hl') (L.inv_mem hl')) hmem
      have h5 : l' * l' = 1 := by
        have := congrArg (·⁻¹) h4
        simpa [mul_inv_rev] using this
      have h6 : IsPGroup 2 (Subgroup.zpowers l') :=
        isPGroup_zpowers_of_pow_eq_one (k := 1) (by rw [pow_one, pow_two, h5])
      exact eq_one_of_odd_of_isPGroup hLo hl' h6

private theorem exists_mul_of_mem_centralizer (hB : B = T ⊔ L₀)
    (hTn : ∀ b ∈ B, ∀ t ∈ T, b * t * b⁻¹ ∈ T) (hT : IsPGroup 2 T) (hLo : Odd (Nat.card L))
    (hL1 : L ≠ ⊥) (hLL₀ : L ≤ L₀)
    (hL₀ : L₀ = L ∨ ∃ a ∈ L₀, a * a = 1 ∧ a ∉ L ∧ (∀ l ∈ L, a * l * a⁻¹ = l⁻¹) ∧
      L₀ = L ⊔ Subgroup.zpowers a) {x : X} (hxB : x ∈ B) (hxL : ∀ l ∈ L, Commute x l) :
    ∃ t ∈ T, ∃ l₀ ∈ L, x = t * l₀ ∧ (∀ l ∈ L, Commute t l) ∧ ∀ l ∈ L, Commute l₀ l := by
  have hL₀B : L₀ ≤ B := by
    rw [hB]
    exact le_sup_right
  have hL₀T : L₀ ≤ Subgroup.normalizer (T : Set X) := fun l hl =>
    mem_normalizer_of_forall_conj_mem' (hTn l (hL₀B hl))
  have hx' : x ∈ ((T ⊔ L₀ : Subgroup X) : Set X) := by
    rw [← hB]
    exact hxB
  rw [Subgroup.coe_mul_of_right_le_normalizer_left T L₀ hL₀T] at hx'
  obtain ⟨t, ht, l₀, hl₀, rfl⟩ := Set.mem_mul.mp hx'
  have hl₀c : ∀ l ∈ L, Commute l₀ l := by
    intro l hl
    have hc : l₀ * l * l₀⁻¹ * l⁻¹ ∈ T := by
      have e : l₀ * l * l₀⁻¹ * l⁻¹ = t⁻¹ * (l * t * l⁻¹) := by
        have h1 : t * l₀ * l * (t * l₀)⁻¹ = l := by
          rw [(hxL l hl).eq, mul_inv_cancel_right]
        calc l₀ * l * l₀⁻¹ * l⁻¹ = t⁻¹ * (t * l₀ * l * (t * l₀)⁻¹) * t * l⁻¹ := by group
          _ = t⁻¹ * l * t * l⁻¹ := by rw [h1]
          _ = t⁻¹ * (l * t * l⁻¹) := by group
      rw [e]
      exact T.mul_mem (T.inv_mem ht) (hTn l (hL₀B (hLL₀ hl)) t ht)
    have hc' : l₀ * l * l₀⁻¹ * l⁻¹ ∈ L₀ :=
      L₀.mul_mem (L₀.mul_mem (L₀.mul_mem hl₀ (hLL₀ hl)) (L₀.inv_mem hl₀))
        (L₀.inv_mem (hLL₀ hl))
    have h1 := inf_eq_bot_of_dihedral hB hTn hT hLo hL1 hLL₀ hL₀ hc hc'
    have h2 : l₀ * l * l₀⁻¹ = l := by
      calc l₀ * l * l₀⁻¹ = l₀ * l * l₀⁻¹ * l⁻¹ * l := by group
        _ = l := by rw [h1, one_mul]
    calc l₀ * l = l₀ * l * l₀⁻¹ * l₀ := by group
      _ = l * l₀ := by rw [h2]
  have hl₀L : l₀ ∈ L := by
    rcases hL₀ with hL₀ | ⟨a, -, ha2, -, hainv, hL₀eq⟩
    · exact hL₀ ▸ hl₀
    · have hzL : Subgroup.zpowers a ≤ Subgroup.normalizer (L : Set X) := by
        rw [Subgroup.zpowers_le]
        exact mem_normalizer_of_forall_conj_mem' fun l hl => by
          rw [hainv l hl]
          exact L.inv_mem hl
      have hl₀' : l₀ ∈ ((L ⊔ Subgroup.zpowers a : Subgroup X) : Set X) := by
        rw [← hL₀eq]
        exact hl₀
      rw [Subgroup.coe_mul_of_right_le_normalizer_left L _ hzL] at hl₀'
      obtain ⟨l, hl, w, hw, hlw⟩ := Set.mem_mul.mp hl₀'
      rcases eq_one_or_eq_of_mem_zpowers' ha2 hw with hw1 | hwa
      · rw [← hlw, hw1, mul_one]
        exact hl
      · exfalso
        apply hL1
        rw [eq_bot_iff]
        intro l' hl'
        rw [Subgroup.mem_bot]
        have h1 : l₀ * l' * l₀⁻¹ = l'⁻¹ := by
          rw [← hlw, hwa]
          have h2 : l * l'⁻¹ = l'⁻¹ * l :=
            (commute_of_forall_conj_eq_inv' hainv hl (L.inv_mem hl')).eq
          calc l * a * l' * (l * a)⁻¹ = l * (a * l' * a⁻¹) * l⁻¹ := by group
            _ = l * l'⁻¹ * l⁻¹ := by rw [hainv l' hl']
            _ = l'⁻¹ * l * l⁻¹ := by rw [h2]
            _ = l'⁻¹ := by group
        have h3 : l₀ * l' * l₀⁻¹ = l' := by
          rw [(hl₀c l' hl').eq, mul_inv_cancel_right]
        have h5 : l' * l' = 1 := by
          have h4 : l' = l'⁻¹ := h3.symm.trans h1
          calc l' * l' = l' * l'⁻¹ := by rw [← h4]
            _ = 1 := mul_inv_cancel l'
        exact eq_one_of_odd_of_isPGroup hLo hl'
          (isPGroup_zpowers_of_pow_eq_one (k := 1) (by rw [pow_one, pow_two, h5]))
  refine ⟨t, ht, l₀, hl₀L, rfl, fun l hl => ?_, hl₀c⟩
  have h1 := (hxL l hl).mul_left ((hl₀c l hl).inv_left)
  rwa [mul_inv_cancel_right] at h1

end Generic

section Models

private theorem psl2Model_two_facts {m : ℕ} (hm : 1 ≤ m) :
    (∀ x : PSL2Model m, IsPGroup 2 (Subgroup.zpowers x) → x * x = 1) ∧
      (Nat.card (PSL2Model m)).factorization 2 = m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : Nat.card (GaloisField 2 m) = 2 ^ m := GaloisField.card 2 m (by omega)
  have hsyl : ∀ Q : Sylow 2 (PSL2Model m), (∀ x ∈ (Q : Subgroup (PSL2Model m)), x * x = 1) ∧
      Nat.card (Q : Subgroup (PSL2Model m)) = 2 ^ m := by
    intro Q
    obtain ⟨e⟩ := CFSG.BenderSuzuki.External.huppert_II_8_2_a_sylow_equiv_additive hF Q
    refine ⟨fun x hx => ?_, ?_⟩
    · obtain ⟨a, ha⟩ := e.surjective ⟨x, hx⟩
      have h2 : a * a = 1 := by
        apply Multiplicative.toAdd.injective
        rw [toAdd_mul, toAdd_one, CharTwo.add_self_eq_zero]
      have h3 : (⟨x, hx⟩ : (Q : Subgroup (PSL2Model m))) * ⟨x, hx⟩ = 1 := by
        rw [← ha, ← map_mul, h2, map_one]
      simpa using congrArg Subtype.val h3
    · rw [← Nat.card_congr e.toEquiv, Nat.card_congr Multiplicative.toAdd, hF]
  refine ⟨fun x hx => ?_, ?_⟩
  · obtain ⟨Q, hQ⟩ := hx.exists_le_sylow
    exact (hsyl Q).1 x (hQ (Subgroup.mem_zpowers x))
  · obtain ⟨Q⟩ : Nonempty (Sylow 2 (PSL2Model m)) := Sylow.nonempty
    have h1 := Q.card_eq_multiplicity
    rw [(hsyl Q).2] at h1
    exact (Nat.pow_right_injective le_rfl h1).symm

private theorem psl2Model_pi_two_facts {m : ℕ} (hm : 1 ≤ m) :
    (∀ x : Fin 2 → PSL2Model m, IsPGroup 2 (Subgroup.zpowers x) → x * x = 1) ∧
      (Nat.card (Fin 2 → PSL2Model m)).factorization 2 = 2 * m := by
  obtain ⟨h1, h2⟩ := psl2Model_two_facts hm
  refine ⟨fun x hx => funext fun i => ?_, ?_⟩
  · have hxi : IsPGroup 2 (Subgroup.zpowers (x i)) := by
      have := hx.map (Pi.evalMonoidHom (fun _ : Fin 2 => PSL2Model m) i)
      rwa [MonoidHom.map_zpowers] at this
    exact h1 (x i) hxi
  · rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin,
      Nat.factorization_pow, Finsupp.smul_apply, h2, smul_eq_mul]

private theorem mul_self_eq_one_of_injective {K K' : Type*} [Group K] [Group K'] (f : K →* K')
    (hf : Function.Injective f) (h : ∀ x : K', IsPGroup 2 (Subgroup.zpowers x) → x * x = 1)
    (x : K) (hx : IsPGroup 2 (Subgroup.zpowers x)) : x * x = 1 := by
  have hfx : IsPGroup 2 (Subgroup.zpowers (f x)) := by
    have := hx.map f
    rwa [MonoidHom.map_zpowers] at this
  apply hf
  rw [map_mul, map_one]
  exact h (f x) hfx

private theorem commutator_l2Wreath_two {m : ℕ} (hm : 2 ≤ m) :
    commutator (L2Wreath m 2) = CFSG.OddTranspositions.l2WreathBase m 2 := by
  apply le_antisymm
  · have hcomm : ∀ σ τ : Equiv.Perm (Fin 2), σ * τ = τ * σ := by decide
    have : IsMulCommutative (Equiv.Perm (Fin 2)) := ⟨⟨hcomm⟩⟩
    have h := Abelianization.commutator_subset_ker
      (SemidirectProduct.rightHom : L2Wreath m 2 →* Equiv.Perm (Fin 2))
    rw [← SemidirectProduct.range_inl_eq_ker_rightHom] at h
    exact h
  · calc CFSG.OddTranspositions.l2WreathBase m 2 =
        ⁅CFSG.OddTranspositions.l2WreathBase m 2, CFSG.OddTranspositions.l2WreathBase m 2⁆ :=
          (CFSG.OddTranspositions.PartThree.commutator_l2WreathBase hm 2).symm
      _ ≤ commutator (L2Wreath m 2) := Subgroup.commutator_mono le_top le_top

private theorem quotient_commutator_two_facts {Q : Type*} [Group Q] {m : ℕ} (hm : 2 ≤ m)
    (h : Nonempty (Q ≃* L2Wreath m 2) ∨
      (Nonempty (↥(commutator Q) ≃* PSL2Model (2 * m)) ∧ (commutator Q).index = 2)) :
    commutator Q ≠ ⊤ ∧
      (∀ x : ↥(commutator Q), IsPGroup 2 (Subgroup.zpowers x) → x * x = 1) ∧
      (Nat.card ↥(commutator Q)).factorization 2 = 2 * m := by
  rcases h with he | ⟨he, hidx⟩
  ·
    obtain ⟨e⟩ := he
    have hmap : (commutator Q).map e.toMonoidHom = CFSG.OddTranspositions.l2WreathBase m 2 := by
      rw [← commutator_l2Wreath_two hm, commutator_def, commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ e.surjective]
    have hinl : Function.Injective
        (SemidirectProduct.inl : (Fin 2 → PSL2Model m) →* L2Wreath m 2) :=
      SemidirectProduct.inl_injective
    let ψ : ↥(commutator Q) ≃* (Fin 2 → PSL2Model m) :=
      ((e.subgroupMap (commutator Q)).trans (MulEquiv.subgroupCongr hmap)).trans
        (MonoidHom.ofInjective hinl).symm
    obtain ⟨h1, h2⟩ := psl2Model_pi_two_facts (m := m) (by omega)
    refine ⟨fun htop => ?_, mul_self_eq_one_of_injective ψ.toMonoidHom ψ.injective h1, ?_⟩
    ·
      have hsw : (SemidirectProduct.inr (Equiv.swap (0 : Fin 2) 1) : L2Wreath m 2) ∈
          CFSG.OddTranspositions.l2WreathBase m 2 := by
        rw [← hmap, htop, Subgroup.map_top_of_surjective _ e.surjective]
        exact Subgroup.mem_top _
      have hker := hsw
      rw [CFSG.OddTranspositions.l2WreathBase, SemidirectProduct.range_inl_eq_ker_rightHom,
        MonoidHom.mem_ker, SemidirectProduct.rightHom_inr] at hker
      exact absurd hker (by decide)
    · rw [Nat.card_congr ψ.toEquiv, h2]
  · obtain ⟨e⟩ := he
    obtain ⟨h1, h2⟩ := psl2Model_two_facts (m := 2 * m) (by omega)
    refine ⟨fun htop => ?_, mul_self_eq_one_of_injective e.toMonoidHom e.injective h1, ?_⟩
    · rw [htop, Subgroup.index_top] at hidx
      exact absurd hidx (by decide)
    · rw [Nat.card_congr e.toEquiv, h2]

end Models

section Lift

variable {K : Type*} [Group K] [Finite K]

omit [Finite K] in
private theorem exists_pow_eq_one_of_isPGroup {x : K} (hx : IsPGroup 2 (Subgroup.zpowers x)) :
    ∃ k : ℕ, x ^ 2 ^ k = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hx ⟨x, Subgroup.mem_zpowers x⟩
  rw [Subgroup.orderOf_mk] at hk
  exact ⟨k, by rw [← hk, pow_orderOf_eq_one]⟩

omit [Finite K] in
private theorem eq_one_of_mem_center_of_pCore {x : K} (hO2 : CFSG.pCore 2 K = ⊥)
    (hx : x ∈ Subgroup.center K) (hp : IsPGroup 2 (Subgroup.zpowers x)) : x = 1 := by
  have hn : (Subgroup.zpowers x).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hx)
  have hle : Subgroup.zpowers x ≤ CFSG.pCore 2 K := le_sSup ⟨hn, hp⟩
  rw [hO2] at hle
  exact Subgroup.mem_bot.mp (hle (Subgroup.mem_zpowers x))

private theorem commutator_two_facts_of_quotient {m : ℕ} (hO2 : CFSG.pCore 2 K = ⊥)
    (hQ : commutator (K ⧸ Subgroup.center K) ≠ ⊤ ∧
      (∀ x : ↥(commutator (K ⧸ Subgroup.center K)), IsPGroup 2 (Subgroup.zpowers x) →
        x * x = 1) ∧
      (Nat.card ↥(commutator (K ⧸ Subgroup.center K))).factorization 2 = 2 * m) :
    commutator K ≠ ⊤ ∧
      (∀ x ∈ commutator K, IsPGroup 2 (Subgroup.zpowers x) → x * x = 1) ∧
      ∀ Q : Sylow 2 K, Nat.card ↥((Q : Subgroup K) ⊓ commutator K) = 2 ^ (2 * m) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨htop, hsq, hcard⟩ := hQ
  set π := QuotientGroup.mk' (Subgroup.center K) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hmap : (commutator K).map π = commutator (K ⧸ Subgroup.center K) := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ hπs]
  let f : ↥(commutator K) →* ↥(commutator (K ⧸ Subgroup.center K)) :=
    (π.comp (commutator K).subtype).codRestrict _ fun y => by
      rw [← hmap]
      exact Subgroup.mem_map_of_mem _ y.2
  have hf : Function.Surjective f := by
    rintro ⟨w, hw⟩
    rw [← hmap] at hw
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hw
    exact ⟨⟨y, hy⟩, rfl⟩
  have hfker : ∀ y : ↥(commutator K), f y = 1 → (y : K) ∈ Subgroup.center K := fun y h =>
    (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val h)
  refine ⟨fun h => htop ?_, fun x hx hp => ?_, fun Q => ?_⟩
  · rw [← hmap, h, Subgroup.map_top_of_surjective _ hπs]
  ·
    obtain ⟨k, hk⟩ := exists_pow_eq_one_of_isPGroup hp
    have hfx : IsPGroup 2 (Subgroup.zpowers (f ⟨x, hx⟩)) :=
      isPGroup_zpowers_of_pow_eq_one (k := k) (by
        rw [← map_pow]
        convert map_one f
        exact Subtype.ext hk)
    have h1 := hfker (⟨x, hx⟩ * ⟨x, hx⟩) (by rw [map_mul]; exact hsq _ hfx)
    exact eq_one_of_mem_center_of_pCore hO2 h1
      (isPGroup_zpowers_of_pow_eq_one (k := k) (by
        rw [← pow_two, ← pow_mul, mul_comm, pow_mul, hk, one_pow]))
  ·
    obtain ⟨R, hR⟩ := CFSG.QuasithinUnique.exists_sylow_map_eq_inf_of_normal Q (commutator K)
    have hodd : ¬ 2 ∣ Nat.card f.ker := by
      intro h2
      obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := f.ker) 2 h2
      have hy' : orderOf (((y : ↥(commutator K)) : K)) = 2 := by
        rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hy]
      have h1 := eq_one_of_mem_center_of_pCore hO2 (hfker y y.2)
        (isPGroup_zpowers_of_pow_eq_one (k := 1) (by rw [pow_one, ← hy', pow_orderOf_eq_one]))
      rw [h1, orderOf_one] at hy'
      exact absurd hy' (by decide)
    have hcardK := Subgroup.card_ker_mul_card_range f
    rw [MonoidHom.range_eq_top.mpr hf, Subgroup.card_top] at hcardK
    have hfact : (Nat.card ↥(commutator K)).factorization 2 = 2 * m := by
      rw [← hcardK, Nat.factorization_mul (Nat.card_pos.ne') (Nat.card_pos.ne'),
        Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hodd, hcard, zero_add]
    rw [← hR, Subgroup.card_map_of_injective (commutator K).subtype_injective,
      R.card_eq_multiplicity, hfact]

end Lift

private theorem mul_self_mem_commutator {K : Type*} [Group K] {Θ : Set K} (hS : Setup K Θ)
    (y : K) : y * y ∈ commutator K := by
  have hle : (⊤ : Subgroup K) ≤
      ((powMonoidHom 2 : Abelianization K →* Abelianization K).ker).comap Abelianization.of := by
    rw [← hS.gen, Subgroup.closure_le]
    intro x hx
    show Abelianization.of x ^ 2 = 1
    rw [← map_pow, pow_two, hS.oddT.mul_self_eq_one hx, map_one]
  have h := hle (Subgroup.mem_top y)
  rw [Subgroup.mem_comap, MonoidHom.mem_ker, powMonoidHom_apply, ← map_pow, pow_two] at h
  rw [← Abelianization.ker_of, MonoidHom.mem_ker]
  exact h

section Chain

variable {G : Type} [Group G] [Finite G] {D : Set G} {hC : HypothesisC D}
  {T : Sylow 2 (Halpha D hC.alpha)} {S : Sylow 2 G} {U : Subgroup G} {n : ℕ}

omit [Finite G] in
private theorem sylow_le_normalizer_inter' (hC : HypothesisC D) (S : Sylow 2 G) :
    (S : Subgroup G) ≤ Subgroup.normalizer ((S : Set G) ∩ D) := by
  intro s hs
  rw [Subgroup.mem_set_normalizer_iff]
  intro x
  constructor
  · rintro ⟨hxS, hxD⟩
    exact ⟨(S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem hs hxS)
      ((S : Subgroup G).inv_mem hs), hC.setup.conj_mem s hxD⟩
  · rintro ⟨hxS, hxD⟩
    have e : x = s⁻¹ * (s * x * s⁻¹) * s⁻¹⁻¹ := by group
    rw [e]
    exact ⟨(S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem ((S : Subgroup G).inv_mem hs)
      hxS) ((S : Subgroup G).inv_mem ((S : Subgroup G).inv_mem hs)),
      hC.setup.conj_mem s⁻¹ hxD⟩

theorem exists_translationSubgroup_of_orthogonal {L L₀ : Subgroup G} {Γ : Set G}
    {Y : Subgroup G} (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC) (hU : DeltaSetup hC T S U)
    (hUn : Nat.card U = 2 ^ n) (hL : UnitaryCentralizerData hC T S U n L L₀)
    (hΔΓ : (S : Set G) ∩ D ⊆ Γ) (hYL : Y ≤ Subgroup.centralizer (L : Set G))
    (hS : Setup Y (((↑) : Y → G) ⁻¹' Γ)) (hO2 : CFSG.pCore 2 Y = ⊥)
    (horth : Nonempty (Y ⧸ Subgroup.center Y ≃* L2Wreath n 2) ∨
      (Nonempty (↥(commutator (Y ⧸ Subgroup.center Y)) ≃* PSL2Model (2 * n)) ∧
        (commutator (Y ⧸ Subgroup.center Y)).index = 2))
    (P : Sylow 2 Y)
    (hΔP : (S : Set G) ∩ D ⊆ ((P : Subgroup Y).map Y.subtype : Set G))
    (hPS : (P : Subgroup Y).map Y.subtype ≤ S) :
    ∃ V : Subgroup G, V ≤ (P : Subgroup Y).map Y.subtype ∧ IsTranslationSubgroup hC S U Y V n := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e₀, he₀, hUe⟩ := hU.exists_card
  have hn2 : 2 ≤ n := by
    have h := Nat.pow_right_injective le_rfl (hUn.symm.trans hUe)
    omega
  obtain ⟨hY'top, hY'sq, hY'card⟩ := commutator_two_facts_of_quotient hO2
    (quotient_commutator_two_facts hn2 horth)
  have hu2 : hC.d * hC.d = 1 := hC.setup.oddT.mul_self_eq_one hC.hd
  have hΔ := hU.sylow_inter
  have huΔ : hC.d ∈ (S : Set G) ∩ D := by
    rw [hΔ]
    exact ⟨1, U.one_mem, mul_one _⟩
  have hzΔ : ∀ z ∈ U, hC.d * z ∈ (S : Set G) ∩ D := fun z hz => by
    rw [hΔ]
    exact ⟨z, hz, rfl⟩
  have hΔY : ∀ δ ∈ (S : Set G) ∩ D, δ ∈ Y := fun δ hδ => Subgroup.map_subtype_le _ (hΔP hδ)
  have hΔP' : ∀ δ (hδ : δ ∈ (S : Set G) ∩ D), (⟨δ, hΔY δ hδ⟩ : Y) ∈ (P : Subgroup Y) := by
    intro δ hδ
    obtain ⟨p, hp, hpδ⟩ := Subgroup.mem_map.mp (hΔP hδ)
    have e : p = ⟨δ, hΔY δ hδ⟩ := Subtype.ext hpδ
    rw [← e]
    exact hp
  have hΓY' : ∀ x ∈ ((↑) : Y → G) ⁻¹' Γ, x ∉ commutator Y := by
    rcases hS.subset_or_disjoint (commutator Y) with h | h
    · exact absurd (hS.eq_top_of_subset _ h) hY'top
    · exact h
  have hΔΓ' : ∀ δ (hδ : δ ∈ (S : Set G) ∩ D), (⟨δ, hΔY δ hδ⟩ : Y) ∈ ((↑) : Y → G) ⁻¹' Γ :=
    fun δ hδ => hΔΓ hδ
  have hu'Y' : (⟨hC.d, hΔY _ huΔ⟩ : Y) ∉ commutator Y := hΓY' _ (hΔΓ' _ huΔ)
  have hUY : ∀ z ∈ U, z ∈ Y := fun z hz => by
    have e : z = hC.d⁻¹ * (hC.d * z) := by group
    rw [e]
    exact Y.mul_mem (Y.inv_mem (hΔY _ huΔ)) (hΔY _ (hzΔ z hz))
  have hUY' : ∀ z (hz : z ∈ U), (⟨z, hUY z hz⟩ : Y) ∈ commutator Y ∧
      (⟨z, hUY z hz⟩ : Y) ∈ (P : Subgroup Y) := by
    intro z hz
    have e : (⟨z, hUY z hz⟩ : Y) =
        (⟨hC.d, hΔY _ huΔ⟩ : Y)⁻¹ * ⟨hC.d * z, hΔY _ (hzΔ z hz)⟩ :=
      Subtype.ext (by show z = hC.d⁻¹ * (hC.d * z); group)
    rw [e]
    refine ⟨?_, (P : Subgroup Y).mul_mem ((P : Subgroup Y).inv_mem (hΔP' _ huΔ))
      (hΔP' _ (hzΔ z hz))⟩
    rw [← Abelianization.ker_of, MonoidHom.mem_ker, map_mul, map_inv,
      hS.abelianization_eq (hΔΓ' _ huΔ) (hΔΓ' _ (hzΔ z hz)), inv_mul_cancel]
  set V : Subgroup G := ((P : Subgroup Y) ⊓ commutator Y).map Y.subtype with hVdef
  have hVY : V ≤ Y := Subgroup.map_subtype_le _
  have hVY' : ∀ v (hv : v ∈ V), (⟨v, hVY hv⟩ : Y) ∈ commutator Y := by
    intro v hv
    obtain ⟨y, ⟨-, hy⟩, hyv⟩ := Subgroup.mem_map.mp hv
    have e : y = ⟨v, hVY hv⟩ := Subtype.ext hyv
    rw [← e]
    exact hy
  have hVsq : ∀ v ∈ V, v * v = 1 := by
    rintro _ ⟨y, ⟨hyP, hyY'⟩, rfl⟩
    have h := hY'sq y hyY' (P.isPGroup'.to_le (Subgroup.zpowers_le.mpr hyP))
    simpa using congrArg Subtype.val h
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    commute_of_mul_self_eq_one' (hVsq a ha) (hVsq b hb) (hVsq _ (V.mul_mem ha hb))
  have hVcard : Nat.card V = 2 ^ (2 * n) := by
    rw [hVdef, Subgroup.card_map_of_injective Y.subtype_injective]
    exact hY'card P
  have hUV : U ≤ V := fun z hz =>
    ⟨⟨z, hUY z hz⟩, ⟨(hUY' z hz).2, (hUY' z hz).1⟩, rfl⟩
  have huV : hC.d ∉ V := fun h => hu'Y' (hVY' _ h)
  have hVS : V ≤ S := (Subgroup.map_mono inf_le_left).trans hPS
  have hYY : (commutator Y).map Y.subtype = ⁅Y, Y⁆ := by
    rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hVYY : V ≤ ⁅Y, Y⁆ := by
    rw [← hYY]
    exact Subgroup.map_mono inf_le_right
  have hSN := sylow_le_normalizer_inter' hC S
  have hcomm : ∀ v ∈ V, ∀ z ∈ U, Commute v z := fun v hv z hz => hVc v hv z (hUV hz)
  have hTgB : (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ≤
      Subgroup.centralizer ((S : Set G) ∩ D) := by
    rw [hL.centralizer_eq]
    exact le_sup_left
  have hBN := Subgroup.centralizer_le_normalizer ((S : Set G) ∩ D)
  have hTp : IsPGroup 2 ((T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype) :=
    T.isPGroup'.map _
  have hCB := fun x (hxB : x ∈ Subgroup.centralizer ((S : Set G) ∩ D))
      (hxL : ∀ l ∈ L, Commute x l) =>
    exists_mul_of_mem_centralizer hL.centralizer_eq (fun b hb => hL.sylow_normal b (hBN hb))
      hTp hL.odd_card hL.ne_bot hL.le hL.eq_or_eq_sup hxB hxL
  have hzU : Subgroup.zpowers hC.d ≤ Subgroup.normalizer (U : Set G) := by
    rw [Subgroup.zpowers_le]
    exact mem_normalizer_of_forall_conj_mem' fun z hz => by
      rw [← (Subgroup.mem_centralizer_iff.mp hU.d_mem_centralizer z hz), mul_inv_cancel_right]
      exact hz
  have hTLU : ∀ x ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype,
      (∀ l ∈ L, Commute x l) → ∃ y ∈ Subgroup.zpowers hC.d, ∃ z ∈ U, x = y * z := by
    intro x hx hxL
    have h := (hL.centralizer_inf x hx).mp hxL
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hzU] at h
    obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_mul.mp h
    exact ⟨y, hy, z, hz, rfl⟩
  have hVB : V ⊓ Subgroup.centralizer ((S : Set G) ∩ D) = U := by
    apply le_antisymm
    · rintro v ⟨hv, hvB⟩
      have hvL : ∀ l ∈ L, Commute v l := fun l hl =>
        (Subgroup.mem_centralizer_iff.mp (hYL (hVY hv)) l hl).symm
      obtain ⟨t, ht, l₀, hl₀, rfl, htL, -⟩ := hCB v hvB hvL
      obtain ⟨k, hk⟩ := exists_pow_eq_one_of_isPGroup (hTp.to_le (Subgroup.zpowers_le.mpr ht))
      have hl₀1 : l₀ = 1 := by
        have h1 : (t * l₀) ^ 2 ^ (k + 1) = 1 := by
          rw [pow_succ', pow_mul, pow_two, hVsq _ hv, one_pow]
        have h2 : t ^ 2 ^ (k + 1) = 1 := by rw [pow_succ, pow_mul, hk, one_pow]
        rw [(htL l₀ hl₀).mul_pow, h2, one_mul] at h1
        exact eq_one_of_odd_of_isPGroup hL.odd_card hl₀ (isPGroup_zpowers_of_pow_eq_one h1)
      rw [hl₀1, mul_one] at hv ⊢
      obtain ⟨y, hy, z, hz, rfl⟩ := hTLU t ht fun l hl => htL l hl
      rcases eq_one_or_eq_of_mem_zpowers' hu2 hy with rfl | rfl
      · rw [one_mul]
        exact hz
      · exfalso
        apply huV
        have e : hC.d = hC.d * z * z⁻¹ := by group
        rw [e]
        exact V.mul_mem hv (V.inv_mem (hUV hz))
    · intro z hz
      refine Subgroup.mem_inf.mpr ⟨hUV hz, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro δ hδ
      rw [hΔ] at hδ
      obtain ⟨w, hw, rfl⟩ := hδ
      have h1 : Commute hC.d z := (Subgroup.mem_centralizer_iff.mp hU.d_mem_centralizer z hz).symm
      exact (h1.mul_left (hcomm w (hUV hw) z hz)).eq
  have hcU : ∀ v ∈ V, hC.d⁻¹ * (v * hC.d * v⁻¹) ∈ U := by
    intro v hv
    have h1 := (Subgroup.mem_set_normalizer_iff.mp (hSN (hVS hv)) _).mp huΔ
    rw [hΔ] at h1
    obtain ⟨z, hz, hze : hC.d * z = v * hC.d * v⁻¹⟩ := h1
    rw [← hze, inv_mul_cancel_left]
    exact hz
  let c : ↥V →* ↥U := MonoidHom.mk' (fun v => ⟨hC.d⁻¹ * ((v : G) * hC.d * (v : G)⁻¹),
      hcU v v.2⟩) fun v w => by
    apply Subtype.ext
    show hC.d⁻¹ * ((v : G) * w * hC.d * ((v : G) * w)⁻¹) =
      hC.d⁻¹ * ((v : G) * hC.d * (v : G)⁻¹) * (hC.d⁻¹ * ((w : G) * hC.d * (w : G)⁻¹))
    have h := (hcomm v v.2 _ (hcU w w.2)).eq
    calc hC.d⁻¹ * ((v : G) * w * hC.d * ((v : G) * w)⁻¹) =
        hC.d⁻¹ * ((v : G) * hC.d * (v : G)⁻¹) *
          ((v : G) * (hC.d⁻¹ * ((w : G) * hC.d * (w : G)⁻¹)) * (v : G)⁻¹) := by group
      _ = hC.d⁻¹ * ((v : G) * hC.d * (v : G)⁻¹) *
          ((hC.d⁻¹ * ((w : G) * hC.d * (w : G)⁻¹)) * v * (v : G)⁻¹) := by rw [h]
      _ = hC.d⁻¹ * ((v : G) * hC.d * (v : G)⁻¹) * (hC.d⁻¹ * ((w : G) * hC.d * (w : G)⁻¹)) := by
        group
  have hcker : c.ker = U.subgroupOf V := by
    ext v
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hv
      have h1 : hC.d⁻¹ * ((v : G) * hC.d * (v : G)⁻¹) = 1 := congrArg Subtype.val hv
      have hvu : Commute (v : G) hC.d := by
        have h2 : (v : G) * hC.d * (v : G)⁻¹ = hC.d := by
          calc (v : G) * hC.d * (v : G)⁻¹ = hC.d * (hC.d⁻¹ * ((v : G) * hC.d * (v : G)⁻¹)) := by
                group
            _ = hC.d := by rw [h1, mul_one]
        show (v : G) * hC.d = hC.d * v
        calc (v : G) * hC.d = (v : G) * hC.d * (v : G)⁻¹ * v := by group
          _ = hC.d * v := by rw [h2]
      rw [← hVB]
      refine Subgroup.mem_inf.mpr ⟨v.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro δ hδ
      rw [hΔ] at hδ
      obtain ⟨w, hw, rfl⟩ := hδ
      exact ((hvu.mul_right (hcomm v v.2 w hw)).symm).eq
    · intro hv
      apply Subtype.ext
      show hC.d⁻¹ * ((v : G) * hC.d * (v : G)⁻¹) = 1
      have h1 : Commute (v : G) hC.d :=
        (Subgroup.mem_centralizer_iff.mp hU.d_mem_centralizer _ hv)
      rw [h1.eq, mul_inv_cancel_right, inv_mul_cancel]
  have hcsurj : Function.Surjective c := by
    have h1 := Subgroup.card_ker_mul_card_range c
    rw [hcker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUV).toEquiv, hUn, hVcard,
      two_mul, pow_add] at h1
    have h2 : Nat.card c.range = Nat.card ↥U := by
      rw [hUn]
      exact Nat.eq_of_mul_eq_mul_left (by positivity) h1
    exact MonoidHom.range_eq_top.mp (Subgroup.eq_top_of_card_eq _ h2)
  have htrans : ∀ δ ∈ (S : Set G) ∩ D, ∀ δ' ∈ (S : Set G) ∩ D, ∃ v ∈ V, v * δ * v⁻¹ = δ' := by
    intro δ hδ δ' hδ'
    rw [hΔ] at hδ hδ'
    obtain ⟨z₁, hz₁, rfl⟩ := hδ
    obtain ⟨z₂, hz₂, rfl⟩ := hδ'
    obtain ⟨v, hv⟩ := hcsurj ⟨z₂ * z₁⁻¹, U.mul_mem hz₂ (U.inv_mem hz₁)⟩
    refine ⟨v, v.2, ?_⟩
    have hcv : hC.d⁻¹ * ((v : G) * hC.d * (v : G)⁻¹) = z₂ * z₁⁻¹ := congrArg Subtype.val hv
    have h1 : (v : G) * hC.d * (v : G)⁻¹ = hC.d * (z₂ * z₁⁻¹) := by
      rw [← hcv]
      group
    calc (v : G) * (hC.d * z₁) * (v : G)⁻¹ =
        ((v : G) * hC.d * (v : G)⁻¹) * ((v : G) * z₁ * (v : G)⁻¹) := by group
      _ = hC.d * (z₂ * z₁⁻¹) * z₁ := by
        rw [h1, (hcomm v v.2 z₁ hz₁).eq, mul_inv_cancel_right]
      _ = hC.d * z₂ := by group
  have huniq : ∀ V' : Subgroup G, V' ≤ ⁅Y, Y⁆ → IsPGroup 2 V' → U ≤ V' → V' ≤ V := by
    intro V' hV'Y hV'p hUV' x hx
    have hV'Y' : ∀ y ∈ V', ∃ hy : y ∈ Y, (⟨y, hy⟩ : Y) ∈ commutator Y := by
      intro y hy
      have h := hV'Y hy
      rw [← hYY] at h
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp h
      exact ⟨w.2, hw⟩
    obtain ⟨hxY, hxY'⟩ := hV'Y' x hx
    have hsqV' : ∀ y ∈ V', y * y = 1 := by
      intro y hy
      obtain ⟨hyY, hyY'⟩ := hV'Y' y hy
      have hp : IsPGroup 2 (Subgroup.zpowers (⟨y, hyY⟩ : Y)) :=
        (hV'p.comap_subtype (K := Y)).to_le (Subgroup.zpowers_le.mpr hy)
      simpa using congrArg Subtype.val (hY'sq _ hyY' hp)
    have hxU : ∀ z ∈ U, Commute x z := fun z hz =>
      commute_of_mul_self_eq_one' (hsqV' x hx) (hsqV' z (hUV' hz))
        (hsqV' _ (V'.mul_mem hx (hUV' hz)))
    obtain ⟨⟨z₀, hz₀⟩, hz₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU.ne_bot
    have hxN : x ∈ Subgroup.normalizer ((S : Set G) ∩ D) :=
      DeltaSetup.centralizer_le_normalizer_of_center hH h3 hU hL.center_eq hz₀
        (fun h => hz₀1 (Subtype.ext h))
        (Subgroup.mem_centralizer_singleton_iff.mpr (hxU z₀ hz₀).eq)
    have hcx : hC.d⁻¹ * (x * hC.d * x⁻¹) ∈ U := by
      have h1 := (Subgroup.mem_set_normalizer_iff.mp hxN _).mp huΔ
      rw [hΔ] at h1
      obtain ⟨z, hz, hze : hC.d * z = x * hC.d * x⁻¹⟩ := h1
      rw [← hze, inv_mul_cancel_left]
      exact hz
    obtain ⟨v, hv⟩ := hcsurj ⟨_, hcx⟩
    have hvx : (v : G) * hC.d * (v : G)⁻¹ = x * hC.d * x⁻¹ :=
      mul_left_cancel (congrArg Subtype.val hv)
    have hbB : (v : G)⁻¹ * x ∈ Subgroup.centralizer ((S : Set G) ∩ D) := by
      rw [Subgroup.mem_centralizer_iff]
      intro δ hδ
      rw [hΔ] at hδ
      obtain ⟨w, hw, rfl⟩ := hδ
      have hbu : Commute ((v : G)⁻¹ * x) hC.d := by
        show (v : G)⁻¹ * x * hC.d = hC.d * ((v : G)⁻¹ * x)
        calc (v : G)⁻¹ * x * hC.d = (v : G)⁻¹ * (x * hC.d * x⁻¹) * x := by group
          _ = (v : G)⁻¹ * ((v : G) * hC.d * (v : G)⁻¹) * x := by rw [hvx]
          _ = hC.d * ((v : G)⁻¹ * x) := by group
      have hbw : Commute ((v : G)⁻¹ * x) w :=
        ((hcomm v v.2 w hw).inv_left).mul_left (hxU w hw)
      exact ((hbu.mul_right hbw).symm).eq
    have hbY : (v : G)⁻¹ * x ∈ Y := Y.mul_mem (Y.inv_mem (hVY v.2)) hxY
    have hbL : ∀ l ∈ L, Commute ((v : G)⁻¹ * x) l := fun l hl =>
      (Subgroup.mem_centralizer_iff.mp (hYL hbY) l hl).symm
    obtain ⟨t, ht, l₀, hl₀, hbt, htL, -⟩ := hCB _ hbB hbL
    obtain ⟨y, hy, z, hz, rfl⟩ := hTLU t ht htL
    have hyY : y ∈ Y := by
      rcases eq_one_or_eq_of_mem_zpowers' hu2 hy with rfl | rfl
      · exact Y.one_mem
      · exact hΔY _ huΔ
    have hl₀Y : l₀ ∈ Y := by
      have e : l₀ = (y * z)⁻¹ * ((v : G)⁻¹ * x) := by rw [hbt]; group
      rw [e]
      exact Y.mul_mem (Y.inv_mem (Y.mul_mem hyY (hUY z hz))) hbY
    have hl₀Y' : (⟨l₀, hl₀Y⟩ : Y) ∈ commutator Y := by
      obtain ⟨j, hj⟩ : Odd (orderOf (⟨l₀, hl₀Y⟩ : Y)) := by
        rw [Subgroup.orderOf_mk]
        exact Odd.of_dvd_nat hL.odd_card (Subgroup.orderOf_dvd_natCard L hl₀)
      have e : (⟨l₀, hl₀Y⟩ : Y) = (⟨l₀, hl₀Y⟩ : Y) ^ (j + 1) * (⟨l₀, hl₀Y⟩ : Y) ^ (j + 1) := by
        rw [← pow_add, show j + 1 + (j + 1) = orderOf (⟨l₀, hl₀Y⟩ : Y) + 1 by omega, pow_succ,
          pow_orderOf_eq_one, one_mul]
      rw [e]
      exact mul_self_mem_commutator hS _
    rcases eq_one_or_eq_of_mem_zpowers' hu2 hy with rfl | rfl
    ·
      rw [one_mul] at hbt
      have hvz : (v : G) * z ∈ V := V.mul_mem v.2 (hUV hz)
      have hx' : x = ((v : G) * z) * l₀ := by
        calc x = (v : G) * ((v : G)⁻¹ * x) := by group
          _ = ((v : G) * z) * l₀ := by rw [hbt, mul_assoc]
      have hcl : Commute ((v : G) * z) l₀ :=
        (Subgroup.mem_centralizer_iff.mp (hYL (hVY hvz)) l₀ hl₀).symm
      obtain ⟨k, hk⟩ := exists_pow_eq_one_of_isPGroup (hV'p.to_le (Subgroup.zpowers_le.mpr hx))
      have hl₀1 : l₀ = 1 := by
        have h1 : x ^ 2 ^ (k + 1) = 1 := by rw [pow_succ, pow_mul, hk, one_pow]
        have h2 : ((v : G) * z) ^ 2 ^ (k + 1) = 1 := by
          rw [pow_succ', pow_mul, pow_two, hVsq _ hvz, one_pow]
        rw [hx', hcl.mul_pow, h2, one_mul] at h1
        exact eq_one_of_odd_of_isPGroup hL.odd_card hl₀ (isPGroup_zpowers_of_pow_eq_one h1)
      rw [hx', hl₀1, mul_one]
      exact hvz
    ·
      exfalso
      apply hu'Y'
      have e : (⟨hC.d, hΔY _ huΔ⟩ : Y) = (⟨v, hVY v.2⟩ : Y)⁻¹ * ⟨x, hxY⟩ * (⟨l₀, hl₀Y⟩ : Y)⁻¹ *
          (⟨z, hUY z hz⟩ : Y)⁻¹ := by
        apply Subtype.ext
        show hC.d = (v : G)⁻¹ * x * l₀⁻¹ * z⁻¹
        calc hC.d = (v : G)⁻¹ * x * l₀⁻¹ * z⁻¹ * (z * l₀ * ((v : G)⁻¹ * x)⁻¹ * hC.d) := by group
          _ = (v : G)⁻¹ * x * l₀⁻¹ * z⁻¹ := by rw [hbt]; group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
        (Subgroup.inv_mem _ (hVY' v v.2)) hxY') (Subgroup.inv_mem _ hl₀Y'))
        (Subgroup.inv_mem _ (hUY' z hz).1)
  refine ⟨V, Subgroup.map_mono inf_le_left, ?_⟩
  exact
    { isElementaryAbelian := CFSG.IsElementaryAbelian.two_of_forall_mul_self hVc hVsq
      card_eq := hVcard
      le := hUV
      le_commutator := hVYY
      le_sylow := hVS
      d_not_mem := huV
      inf_centralizer := hVB
      transitive := htrans
      unique := huniq }

end Chain

end CFSG.OddTranspositions.PartThree.Nine
