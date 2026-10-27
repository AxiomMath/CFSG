module

public import CFSG.LieType.BorelTits.Basic
public import CFSG.Quasithin.Background.A1cTransfer

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

section General

instance gold_pCore_normal (p : ℕ) (G : Type*) [Group G] : (pCore p G).Normal := pCore_normal p

theorem gold_orderOf_conj {G : Type*} [Group G] (a x : G) : orderOf (a * x * a⁻¹) = orderOf x :=
  (SemiconjBy.orderOf_eq a (show SemiconjBy a x (a * x * a⁻¹) by
    simp [SemiconjBy, mul_assoc])).symm

theorem gold_relIndex_normalCore_dvd_two {A : Type*} [Group A] {H : Subgroup A}
    (hH : H.index = 3) : H.normalCore.relIndex H ∣ 2 := by
  have : H.FiniteIndex := ⟨by omega⟩
  have h1 : H.normalCore.index ∣ Nat.factorial H.index := H.index_normalCore_dvd_factorial_index
  have h2 := Subgroup.relIndex_mul_index H.normalCore_le
  rw [← h2, hH] at h1
  have h3 : H.normalCore.relIndex H * 3 ∣ 2 * 3 := by
    simpa [Nat.factorial] using h1
  exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) h3

theorem gold_card_perm_fin_three : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
  rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]; rfl

theorem gold_card_multiplicative_zmod_three : Nat.card (Multiplicative (ZMod 3)) = 3 := by
  simp

theorem gold_mem_of_odd_orderOf_of_index_dvd_two {C : Type*} [Group C] {K : Subgroup C} [K.Normal]
    (hK : K.index ∣ 2) {x : C} (hx : Odd (orderOf x)) : x ∈ K := by
  have h1 : orderOf (QuotientGroup.mk x : C ⧸ K) ∣ 2 := by
    refine (orderOf_dvd_natCard _).trans ?_
    rw [← Subgroup.index_eq_card]
    exact hK
  have h2 : orderOf (QuotientGroup.mk x : C ⧸ K) ∣ orderOf x :=
    orderOf_map_dvd (QuotientGroup.mk' K) x
  have hcop : Nat.Coprime (orderOf x) 2 := Nat.coprime_two_right.mpr hx
  have h3 : orderOf (QuotientGroup.mk x : C ⧸ K) = 1 :=
    Nat.eq_one_of_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd h2 h1)
  exact (QuotientGroup.eq_one_iff x).mp (orderOf_eq_one_iff.mp h3)

theorem gold_normalCore_quotient_equiv {A : Type*} [Group A] {H : Subgroup A} (hH : H.index = 3) :
    (H.normalCore.index = 3 ∧ Nonempty (A ⧸ H.normalCore ≃* Multiplicative (ZMod 3))) ∨
    (H.normalCore.index = 6 ∧ Nonempty (A ⧸ H.normalCore ≃* Equiv.Perm (Fin 3))) := by
  have hfin : H.FiniteIndex := ⟨by omega⟩
  have hrel : H.normalCore.relIndex H ∣ 2 := gold_relIndex_normalCore_dvd_two hH
  have hmul := Subgroup.relIndex_mul_index (H.normalCore_le)
  rw [hH] at hmul
  rcases (Nat.dvd_prime Nat.prime_two).mp hrel with h1 | h2
  · left
    have hidx : H.normalCore.index = 3 := by rw [← hmul, h1]
    refine ⟨hidx, ⟨?_⟩⟩
    have hc : Nat.card (A ⧸ H.normalCore) = 3 := by rw [← Subgroup.index_eq_card, hidx]
    refine mulEquivOfPrimeCardEq (p := 3) hc ?_
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  · right
    have hidx : H.normalCore.index = 6 := by rw [← hmul, h2]
    refine ⟨hidx, ⟨?_⟩⟩
    let φ : A →* Equiv.Perm (A ⧸ H) := MulAction.toPermHom A (A ⧸ H)
    have hker : H.normalCore = φ.ker := H.normalCore_eq_ker
    let f : A ⧸ H.normalCore →* Equiv.Perm (A ⧸ H) :=
      QuotientGroup.lift H.normalCore φ hker.le
    have hinj : Function.Injective f := by
      rw [injective_iff_map_eq_one]
      intro q hq
      induction q using QuotientGroup.induction_on with
      | H a =>
        have ha : φ a = 1 := hq
        have : a ∈ H.normalCore := by rw [hker]; exact ha
        exact (QuotientGroup.eq_one_iff a).mpr this
    have hcardQ : Nat.card (A ⧸ H) = 3 := by rw [← Subgroup.index_eq_card, hH]
    have hcardP : Nat.card (Equiv.Perm (A ⧸ H)) = 6 := by
      rw [Nat.card_perm, hcardQ]; rfl
    have hcardN : Nat.card (A ⧸ H.normalCore) = 6 := by rw [← Subgroup.index_eq_card, hidx]
    have : Finite (Equiv.Perm (A ⧸ H)) := Nat.finite_of_card_ne_zero (by rw [hcardP]; norm_num)
    have hbij : Function.Bijective f :=
      hinj.bijective_of_nat_card_le (by rw [hcardP, hcardN])
    let e : (A ⧸ H) ≃ Fin 3 := Finite.equivFinOfCardEq hcardQ
    exact (MulEquiv.ofBijective f hbij).trans e.permCongrHom

theorem gold_sq_mem_of_index_dvd_two {C : Type*} [Group C] {K : Subgroup C} [K.Normal]
    (hK : K.index ∣ 2) (x : C) : x ^ 2 ∈ K := by
  have h1 : orderOf (QuotientGroup.mk x : C ⧸ K) ∣ 2 := by
    refine (orderOf_dvd_natCard _).trans ?_
    rw [← Subgroup.index_eq_card]
    exact hK
  have h2 : (QuotientGroup.mk x : C ⧸ K) ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp h1
  exact (QuotientGroup.eq_one_iff (x ^ 2)).mp (by simpa using h2)

theorem gold_relIndex_normalCore_le_eight {A : Type*} [Group A] [Finite A] {E Q : Subgroup A}
    [E.Normal] (hE : E.index = 3) (hQE : Q ≤ E) (hQ2 : Q.relIndex E = 2) :
    Q.normalCore.relIndex E ≤ 8 := by
  classical
  have hQnormE : ∀ e ∈ E, ∀ q ∈ Q, e * q * e⁻¹ ∈ Q := by
    have hN : (Q.subgroupOf E).Normal := Subgroup.normal_of_index_eq_two hQ2
    intro e he q hq
    have hq' : (⟨q, hQE hq⟩ : E) ∈ Q.subgroupOf E := hq
    have := hN.conj_mem _ hq' ⟨e, he⟩
    exact this
  let F : A → Subgroup A := fun a => Q.map (MulAut.conj a).toMonoidHom
  have hF_mem : ∀ a x, x ∈ F a ↔ a⁻¹ * x * a ∈ Q := by
    intro a x
    constructor
    · rintro ⟨q, hq, rfl⟩
      have : a⁻¹ * (a * q * a⁻¹) * a = q := by group
      show a⁻¹ * (a * q * a⁻¹) * a ∈ Q
      rw [this]
      exact hq
    · intro h
      exact ⟨a⁻¹ * x * a, h, by simp [mul_assoc]⟩
  have hEmap : ∀ a : A, E.map (MulAut.conj a).toMonoidHom = E := by
    intro a
    ext x
    constructor
    · rintro ⟨e, he, rfl⟩
      simpa using (inferInstance : E.Normal).conj_mem e he a
    · intro hx
      exact ⟨a⁻¹ * x * a, by simpa using (inferInstance : E.Normal).conj_mem x hx a⁻¹,
        by simp [mul_assoc]⟩
  have hFrel : ∀ a, (F a).relIndex E = 2 := by
    intro a
    have hinj : Function.Injective (MulAut.conj a).toMonoidHom := (MulAut.conj a).injective
    have := Subgroup.relIndex_map_map_of_injective Q E hinj
    rw [hEmap a] at this
    rw [this]
    exact hQ2
  have hFcoset : ∀ a, ∀ e ∈ E, F (a * e) = F a := by
    intro a e he
    ext x
    rw [hF_mem, hF_mem]
    have hy : a⁻¹ * x * a = e * ((a * e)⁻¹ * x * (a * e)) * e⁻¹ := by group
    constructor
    · intro h
      rw [hy]
      exact hQnormE e he _ h
    · intro h
      have hy' : (a * e)⁻¹ * x * (a * e) = e⁻¹ * (a⁻¹ * x * a) * e⁻¹⁻¹ := by group
      rw [hy']
      exact hQnormE e⁻¹ (inv_mem he) _ h
  have : Fintype (A ⧸ E) := Fintype.ofFinite _
  let G : A ⧸ E → Subgroup A := fun x => F x.out
  have hcard : Fintype.card (A ⧸ E) = 3 := by
    rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card, hE]
  have hG2 : ∀ x, (G x).relIndex E = 2 := fun x => hFrel _
  have hbound : (⨅ x, G x).relIndex E ≤ 8 := by
    refine (Subgroup.relIndex_iInf_le G).trans ?_
    rw [Finset.prod_congr rfl (fun x _ => hG2 x), Finset.prod_const, Finset.card_univ, hcard]
    norm_num
  have hle : (⨅ x, G x) ≤ Q.normalCore := by
    intro w hw b
    obtain ⟨e, he⟩ := QuotientGroup.mk_out_eq_mul E b⁻¹
    have hw' : w ∈ F ((QuotientGroup.mk b⁻¹ : A ⧸ E).out) := Subgroup.mem_iInf.mp hw _
    rw [he, hFcoset _ e e.2, hF_mem] at hw'
    simpa using hw'
  have hne : (⨅ x, G x).relIndex E ≠ 0 :=
    Subgroup.relIndex_iInf_ne_zero fun x => by rw [hG2 x]; norm_num
  exact (Subgroup.relIndex_le_of_le_left hle hne).trans hbound

theorem gold_comm_of_sq_eq_one {G : Type*} [Group G] (h : ∀ x : G, x ^ 2 = 1) (x y : G) :
    x * y = y * x := by
  have hinv : ∀ z : G, z⁻¹ = z := fun z => inv_eq_of_mul_eq_one_right (by simpa [sq] using h z)
  calc x * y = (x * y)⁻¹ := (hinv _).symm
    _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
    _ = y * x := by rw [hinv, hinv]

end General

structure GoldAmalgam (A C B : Type*) [Group A] [Group C] [Group B] where
  toA : C →* A
  toB : C →* B
  toA_injective : Function.Injective toA
  toB_injective : Function.Injective toB

namespace GoldAmalgam

variable {A C B : Type*} [Group A] [Group C] [Group B] (X : GoldAmalgam A C B)

@[expose] def edgeA : Subgroup A := X.toA.range

@[expose] def edgeB : Subgroup B := X.toB.range

@[expose] def IsFaithful : Prop :=
  ∀ K : Subgroup C, (K.map X.toA).Normal → (K.map X.toB).Normal → K = ⊥

@[expose] def IsIndexThree : Prop := X.edgeA.index = 3 ∧ X.edgeB.index = 3

@[expose] def coreA : Subgroup C := X.edgeA.normalCore.comap X.toA

@[expose] def coreB : Subgroup C := X.edgeB.normalCore.comap X.toB

@[expose] def swap : GoldAmalgam B C A := ⟨X.toB, X.toA, X.toB_injective, X.toA_injective⟩

@[simp] theorem swap_toA : X.swap.toA = X.toB := rfl
@[simp] theorem swap_toB : X.swap.toB = X.toA := rfl
@[simp] theorem swap_edgeA : X.swap.edgeA = X.edgeB := rfl
@[simp] theorem swap_edgeB : X.swap.edgeB = X.edgeA := rfl
@[simp] theorem swap_coreA : X.swap.coreA = X.coreB := rfl
@[simp] theorem swap_coreB : X.swap.coreB = X.coreA := rfl

theorem swap_isFaithful_iff : X.swap.IsFaithful ↔ X.IsFaithful := by
  constructor
  · intro h K hA hB
    exact h K hB hA
  · intro h K hB hA
    exact h K hA hB

theorem swap_isIndexThree_iff : X.swap.IsIndexThree ↔ X.IsIndexThree := by
  unfold IsIndexThree
  simp only [swap_edgeA, swap_edgeB]
  exact and_comm

theorem toA_mem_edgeA (c : C) : X.toA c ∈ X.edgeA := ⟨c, rfl⟩

theorem coreA_normal : X.coreA.Normal := Subgroup.Normal.comap (Subgroup.normalCore_normal _) _

theorem coreB_normal : X.coreB.Normal := X.swap.coreA_normal

theorem map_coreA : X.coreA.map X.toA = X.edgeA.normalCore :=
  Subgroup.map_comap_eq_self (X.edgeA.normalCore_le)

theorem map_coreA_normal : (X.coreA.map X.toA).Normal := by
  rw [map_coreA]
  exact Subgroup.normalCore_normal _

theorem le_coreA_of_normal {K : Subgroup C} (hK : (K.map X.toA).Normal) : K ≤ X.coreA := by
  have h : K.map X.toA ≤ X.edgeA.normalCore := by
    rw [Subgroup.normal_le_normalCore]
    exact Subgroup.map_le_range _ _
  exact Subgroup.map_le_iff_le_comap.mp h

theorem le_coreB_of_normal {K : Subgroup C} (hK : (K.map X.toB).Normal) : K ≤ X.coreB :=
  X.swap.le_coreA_of_normal hK

theorem coreA_index_eq : X.coreA.index = X.edgeA.normalCore.relIndex X.edgeA := by
  unfold coreA edgeA
  rw [Subgroup.index_comap]

theorem coreA_index_eq_one_iff_normal : X.coreA.index = 1 ↔ X.edgeA.Normal := by
  rw [coreA_index_eq, Subgroup.relIndex_eq_one]
  constructor
  · intro h
    have : X.edgeA.normalCore = X.edgeA := le_antisymm X.edgeA.normalCore_le h
    rw [← this]
    exact Subgroup.normalCore_normal _
  · intro h
    rw [Subgroup.normalCore_eq_self]

theorem coreB_index_eq_one_iff_normal : X.coreB.index = 1 ↔ X.edgeB.Normal :=
  X.swap.coreA_index_eq_one_iff_normal

theorem coreA_index_dvd_two (hA : X.edgeA.index = 3) : X.coreA.index ∣ 2 := by
  rw [coreA_index_eq]
  exact gold_relIndex_normalCore_dvd_two hA

theorem coreB_index_dvd_two (hB : X.edgeB.index = 3) : X.coreB.index ∣ 2 :=
  X.swap.coreA_index_dvd_two hB

theorem odd_mem_coreA (h2 : X.coreA.index ∣ 2) {x : C} (hx : Odd (orderOf x)) : x ∈ X.coreA := by
  have := X.coreA_normal
  exact gold_mem_of_odd_orderOf_of_index_dvd_two h2 hx

theorem odd_mem_coreB (h2 : X.coreB.index ∣ 2) {x : C} (hx : Odd (orderOf x)) : x ∈ X.coreB :=
  X.swap.odd_mem_coreA h2 hx

theorem oddClosure_map_toA_normal (h2 : X.coreA.index ∣ 2) :
    ((Subgroup.closure {x : C | Odd (orderOf x)}).map X.toA).Normal := by
  rw [MonoidHom.map_closure]
  refine ⟨fun y hy a => ?_⟩
  induction hy using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    have hxK : X.toA x ∈ X.edgeA.normalCore := X.odd_mem_coreA h2 hx
    have h3 : a * X.toA x * a⁻¹ ∈ X.edgeA.normalCore :=
      (Subgroup.normalCore_normal _).conj_mem _ hxK a
    obtain ⟨z, hz⟩ := Subgroup.normalCore_le _ h3
    apply Subgroup.subset_closure
    refine ⟨z, ?_, hz⟩
    show Odd (orderOf z)
    have : orderOf z = orderOf x := by
      rw [← orderOf_injective X.toA X.toA_injective z, hz, gold_orderOf_conj,
        orderOf_injective X.toA X.toA_injective x]
    rw [this]
    exact hx
  | one => simp
  | mul y z _ _ hy hz =>
    have := mul_mem hy hz
    simpa [mul_assoc] using this
  | inv y _ hy =>
    have := inv_mem hy
    simpa [mul_assoc] using this

theorem oddClosure_map_toB_normal (h2 : X.coreB.index ∣ 2) :
    ((Subgroup.closure {x : C | Odd (orderOf x)}).map X.toB).Normal :=
  X.swap.oddClosure_map_toA_normal h2

theorem sqClosure_map_toA_normal (hnorm : X.edgeA.Normal) :
    ((Subgroup.closure {x : C | ∃ y : C, x = y ^ 2}).map X.toA).Normal := by
  rw [MonoidHom.map_closure]
  refine ⟨fun y hy a => ?_⟩
  induction hy using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨x, ⟨z, rfl⟩, rfl⟩ := hy
    have hz : a * X.toA z * a⁻¹ ∈ X.edgeA := hnorm.conj_mem _ (X.toA_mem_edgeA z) a
    obtain ⟨z', hz'⟩ := hz
    apply Subgroup.subset_closure
    refine ⟨z' ^ 2, ⟨z', rfl⟩, ?_⟩
    simp only [map_pow]
    rw [hz', conj_pow]
  | one => simp
  | mul y z _ _ hy hz =>
    have := mul_mem hy hz
    simpa [mul_assoc] using this
  | inv y _ hy =>
    have := inv_mem hy
    simpa [mul_assoc] using this

theorem isPGroup_edgeA (hC : IsPGroup 2 C) : IsPGroup 2 X.edgeA :=
  hC.of_surjective X.toA.rangeRestrict X.toA.rangeRestrict_surjective

theorem isPGroup_edgeB (hC : IsPGroup 2 C) : IsPGroup 2 X.edgeB :=
  X.swap.isPGroup_edgeA hC

theorem eq_one_of_normal_normal (hf : X.IsFaithful) (hA : X.edgeA.Normal) (hB : X.edgeB.Normal)
    (x : C) : x = 1 := by
  have h := hf ⊤ (by rw [Subgroup.map_top]; exact hA) (by rw [Subgroup.map_top]; exact hB)
  have hx : x ∈ (⊤ : Subgroup C) := Subgroup.mem_top x
  rw [h] at hx
  simpa using hx

section Finite

variable [Finite C]

theorem isPGroup_two (hf : X.IsFaithful) (hA : X.edgeA.index = 3) (hB : X.edgeB.index = 3) :
    IsPGroup 2 C := by
  have hR : Subgroup.closure {x : C | Odd (orderOf x)} = ⊥ :=
    hf _ (X.oddClosure_map_toA_normal (X.coreA_index_dvd_two hA))
      (X.oddClosure_map_toB_normal (X.coreB_index_dvd_two hB))
  have hodd : ∀ x : C, Odd (orderOf x) → x = 1 := by
    intro x hx
    have : x ∈ Subgroup.closure {x : C | Odd (orderOf x)} := Subgroup.subset_closure hx
    rw [hR] at this
    simpa using this
  have hprime : ∀ {d : ℕ}, d.Prime → d ∣ Nat.card C → d = 2 := by
    intro d hd hdvd
    by_contra hne
    have : Fact d.Prime := ⟨hd⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' d hdvd
    have hxodd : Odd (orderOf x) := by
      rw [hx]
      exact hd.odd_of_ne_two hne
    have := hodd x hxodd
    rw [this, orderOf_one] at hx
    exact hd.one_lt.ne hx
  exact IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' hprime)

theorem pResidual_eq_bot (hf : X.IsFaithful) (hA : X.edgeA.index = 3) (hB : X.edgeB.index = 3) :
    pResidual 2 C = ⊥ := by
  have hC := X.isPGroup_two hf hA hB
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_bot_iff.mp (pResidual_le (N := (⊥ : Subgroup C)) ?_)
  intro x
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf).mp hC x
  exact ⟨k, by rw [← hk, pow_orderOf_eq_one]; exact one_mem _⟩

variable [Finite A]

theorem normalCore_edgeA_eq_pCore (hf : X.IsFaithful) (hA : X.edgeA.index = 3)
    (hB : X.edgeB.index = 3) : X.edgeA.normalCore = pCore 2 A := by
  have hC := X.isPGroup_two hf hA hB
  have hE : IsPGroup 2 X.edgeA := X.isPGroup_edgeA hC
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · exact le_pCore 2 (Subgroup.normalCore_normal _) (hE.to_le X.edgeA.normalCore_le)
  · have hsyl : ¬ 2 ∣ X.edgeA.index := by rw [hA]; decide
    have hN : (pCore 2 A).Normal := pCore_normal 2
    have h1 : pCore 2 A ≤ hE.toSylow hsyl := (pCore_isPGroup 2).le_sylow_of_normal _
    rw [Subgroup.normal_le_normalCore]
    exact h1

omit [Finite C] [Finite A] in
theorem coreA_index_mul_three (hA : X.edgeA.index = 3) :
    X.coreA.index * 3 = X.edgeA.normalCore.index := by
  rw [coreA_index_eq]
  have := Subgroup.relIndex_mul_index X.edgeA.normalCore_le
  rwa [hA] at this

theorem quotient_pCore_equiv (hf : X.IsFaithful) (hA : X.edgeA.index = 3)
    (hB : X.edgeB.index = 3) :
    (X.coreA.index = 1 ∧ Nonempty (A ⧸ pCore 2 A ≃* Multiplicative (ZMod 3))) ∨
    (X.coreA.index = 2 ∧ Nonempty (A ⧸ pCore 2 A ≃* Equiv.Perm (Fin 3))) := by
  have hcore := X.normalCore_edgeA_eq_pCore hf hA hB
  let q : A ⧸ pCore 2 A ≃* A ⧸ X.edgeA.normalCore := QuotientGroup.quotientMulEquivOfEq hcore.symm
  have hmul := X.coreA_index_mul_three hA
  rcases gold_normalCore_quotient_equiv hA with ⟨h3, ⟨e⟩⟩ | ⟨h6, ⟨e⟩⟩
  · exact Or.inl ⟨by omega, ⟨q.trans e⟩⟩
  · exact Or.inr ⟨by omega, ⟨q.trans e⟩⟩

theorem coreA_index_eq_two_iff (hf : X.IsFaithful) (hA : X.edgeA.index = 3)
    (hB : X.edgeB.index = 3) :
    X.coreA.index = 2 ↔ Nonempty (A ⧸ pCore 2 A ≃* Equiv.Perm (Fin 3)) := by
  rcases X.quotient_pCore_equiv hf hA hB with ⟨h1, ⟨e⟩⟩ | ⟨h2, he⟩
  · refine ⟨fun h => by omega, ?_⟩
    rintro ⟨f⟩
    have h3 := Nat.card_congr e.toEquiv
    have h6 := Nat.card_congr f.toEquiv
    rw [gold_card_multiplicative_zmod_three] at h3
    rw [gold_card_perm_fin_three] at h6
    omega
  · exact ⟨fun _ => he, fun _ => h2⟩

theorem coreA_index_eq_one_iff (hf : X.IsFaithful) (hA : X.edgeA.index = 3)
    (hB : X.edgeB.index = 3) :
    X.coreA.index = 1 ↔ Nonempty (A ⧸ pCore 2 A ≃* Multiplicative (ZMod 3)) := by
  rcases X.quotient_pCore_equiv hf hA hB with ⟨h1, he⟩ | ⟨h2, ⟨e⟩⟩
  · exact ⟨fun _ => he, fun _ => h1⟩
  · refine ⟨fun h => by omega, ?_⟩
    rintro ⟨f⟩
    have h3 := Nat.card_congr e.toEquiv
    have h6 := Nat.card_congr f.toEquiv
    rw [gold_card_multiplicative_zmod_three] at h6
    rw [gold_card_perm_fin_three] at h3
    omega

end Finite

section FiniteB

variable [Finite C] [Finite B]

theorem normalCore_edgeB_eq_pCore (hf : X.IsFaithful) (hA : X.edgeA.index = 3)
    (hB : X.edgeB.index = 3) : X.edgeB.normalCore = pCore 2 B :=
  X.swap.normalCore_edgeA_eq_pCore ((X.swap_isFaithful_iff).mpr hf) hB hA

theorem quotient_pCore_equiv_B (hf : X.IsFaithful) (hA : X.edgeA.index = 3)
    (hB : X.edgeB.index = 3) :
    (X.coreB.index = 1 ∧ Nonempty (B ⧸ pCore 2 B ≃* Multiplicative (ZMod 3))) ∨
    (X.coreB.index = 2 ∧ Nonempty (B ⧸ pCore 2 B ≃* Equiv.Perm (Fin 3))) :=
  X.swap.quotient_pCore_equiv ((X.swap_isFaithful_iff).mpr hf) hB hA

theorem coreB_index_eq_two_iff (hf : X.IsFaithful) (hA : X.edgeA.index = 3)
    (hB : X.edgeB.index = 3) :
    X.coreB.index = 2 ↔ Nonempty (B ⧸ pCore 2 B ≃* Equiv.Perm (Fin 3)) :=
  X.swap.coreA_index_eq_two_iff ((X.swap_isFaithful_iff).mpr hf) hB hA

theorem coreB_index_eq_one_iff (hf : X.IsFaithful) (hA : X.edgeA.index = 3)
    (hB : X.edgeB.index = 3) :
    X.coreB.index = 1 ↔ Nonempty (B ⧸ pCore 2 B ≃* Multiplicative (ZMod 3)) :=
  X.swap.coreA_index_eq_one_iff ((X.swap_isFaithful_iff).mpr hf) hB hA

end FiniteB

section FiniteAB

variable [Finite A] [Finite C] [Finite B]

theorem permutation_cores (hf : X.IsFaithful) (hA : X.edgeA.index = 3) (hB : X.edgeB.index = 3) :
    (X.coreA.index = 1 ∨ X.coreA.index = 2) ∧ (X.coreB.index = 1 ∨ X.coreB.index = 2) ∧
    pResidual 2 C = ⊥ ∧ IsPGroup 2 C ∧
    X.edgeA.normalCore = pCore 2 A ∧ X.edgeB.normalCore = pCore 2 B ∧
    ((X.coreA.index = 1 ∧ Nonempty (A ⧸ pCore 2 A ≃* Multiplicative (ZMod 3))) ∨
      (X.coreA.index = 2 ∧ Nonempty (A ⧸ pCore 2 A ≃* Equiv.Perm (Fin 3)))) ∧
    ((X.coreB.index = 1 ∧ Nonempty (B ⧸ pCore 2 B ≃* Multiplicative (ZMod 3))) ∨
      (X.coreB.index = 2 ∧ Nonempty (B ⧸ pCore 2 B ≃* Equiv.Perm (Fin 3)))) := by
  refine ⟨?_, ?_, X.pResidual_eq_bot hf hA hB, X.isPGroup_two hf hA hB,
    X.normalCore_edgeA_eq_pCore hf hA hB, X.normalCore_edgeB_eq_pCore hf hA hB,
    X.quotient_pCore_equiv hf hA hB, X.quotient_pCore_equiv_B hf hA hB⟩
  · rcases X.quotient_pCore_equiv hf hA hB with ⟨h, _⟩ | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inr h
  · rcases X.quotient_pCore_equiv_B hf hA hB with ⟨h, _⟩ | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inr h

end FiniteAB

section Abelian

variable [Finite A] [Finite C]

theorem pCore_le_center_of_abelian (hC : ∀ x y : C, x * y = y * x) (hf : X.IsFaithful)
    (hA : X.edgeA.index = 3) (hB : X.edgeB.index = 3)
    (hS3 : Nonempty (A ⧸ pCore 2 A ≃* Equiv.Perm (Fin 3))) : pCore 2 A ≤ Subgroup.center A := by
  have hcore := X.normalCore_edgeA_eq_pCore hf hA hB
  have hidx2 : X.coreA.index = 2 := (X.coreA_index_eq_two_iff hf hA hB).mpr hS3
  rw [← hcore]
  have hEZ : X.edgeA ≤ Subgroup.centralizer (X.edgeA.normalCore : Set A) := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    obtain ⟨c0, rfl⟩ := hc
    obtain ⟨n0, rfl⟩ := X.edgeA.normalCore_le hn
    rw [← map_mul, ← map_mul, hC n0 c0]
  have hdvd : (Subgroup.centralizer (X.edgeA.normalCore : Set A)).index ∣ 3 := by
    rw [← hA]
    exact Subgroup.index_dvd_of_le hEZ
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · exact Subgroup.centralizer_eq_top_iff_subset.mp (Subgroup.index_eq_one.mp h1)
  · exfalso
    have hrel := Subgroup.relIndex_mul_index hEZ
    rw [hA, h3] at hrel
    have h1' : X.edgeA.relIndex (Subgroup.centralizer (X.edgeA.normalCore : Set A)) = 1 := by
      omega
    have hZ : Subgroup.centralizer (X.edgeA.normalCore : Set A) ≤ X.edgeA :=
      Subgroup.relIndex_eq_one.mp h1'
    have hEeq : X.edgeA = Subgroup.centralizer (X.edgeA.normalCore : Set A) := le_antisymm hEZ hZ
    have hnormE : X.edgeA.Normal := by
      rw [hEeq]
      exact Subgroup.normal_centralizer
    have hself : X.edgeA.normalCore = X.edgeA := Subgroup.normalCore_eq_self _
    have : X.coreA.index = 1 := by
      rw [coreA_index_eq, hself]
      exact (Subgroup.relIndex_eq_one).mpr le_rfl
    omega

end Abelian

section AbelianB

variable [Finite B] [Finite C]

theorem pCore_le_center_of_abelian_B (hC : ∀ x y : C, x * y = y * x) (hf : X.IsFaithful)
    (hA : X.edgeA.index = 3) (hB : X.edgeB.index = 3)
    (hS3 : Nonempty (B ⧸ pCore 2 B ≃* Equiv.Perm (Fin 3))) : pCore 2 B ≤ Subgroup.center B :=
  X.swap.pCore_le_center_of_abelian hC ((X.swap_isFaithful_iff).mpr hf) hB hA hS3

end AbelianB

section NormalVertex

variable [Finite A] [Finite C] [Finite B]

omit [Finite A] in
theorem sq_eq_one_of_normal_central (hf : X.IsFaithful) (hA : X.edgeA.index = 3)
    (hB : X.edgeB.index = 3) (hnorm : X.edgeA.Normal) (hQB : pCore 2 B ≤ Subgroup.center B)
    (x : C) : x ^ 2 = 1 := by
  have h2 : X.coreB.index ∣ 2 := X.coreB_index_dvd_two hB
  have hSqA := X.sqClosure_map_toA_normal hnorm
  have hcoreB : X.edgeB.normalCore = pCore 2 B := X.normalCore_edgeB_eq_pCore hf hA hB
  have hle : Subgroup.closure {x : C | ∃ y : C, x = y ^ 2} ≤ X.coreB := by
    rw [Subgroup.closure_le]
    rintro z ⟨y, rfl⟩
    have := X.coreB_normal
    exact gold_sq_mem_of_index_dvd_two h2 y
  have hSqB : ((Subgroup.closure {x : C | ∃ y : C, x = y ^ 2}).map X.toB).Normal := by
    apply Subgroup.normal_of_le_center
    calc _ ≤ X.coreB.map X.toB := Subgroup.map_mono hle
      _ = X.edgeB.normalCore := X.swap.map_coreA
      _ = pCore 2 B := hcoreB
      _ ≤ _ := hQB
  have hbot := hf _ hSqA hSqB
  have : x ^ 2 ∈ Subgroup.closure {x : C | ∃ y : C, x = y ^ 2} := Subgroup.subset_closure ⟨x, rfl⟩
  rw [hbot] at this
  simpa using this

theorem card_le_eight_of_normal_central (hf : X.IsFaithful) (hA : X.edgeA.index = 3)
    (hB : X.edgeB.index = 3) (hnorm : X.edgeA.Normal) (hQB : pCore 2 B ≤ Subgroup.center B)
    (h2 : X.coreB.index = 2) : Nat.card C ≤ 8 := by
  have hcoreB : X.edgeB.normalCore = pCore 2 B := X.normalCore_edgeB_eq_pCore hf hA hB
  let Q : Subgroup A := X.coreB.map X.toA
  have hQE : Q ≤ X.edgeA := Subgroup.map_le_range _ _
  have hQ2 : Q.relIndex X.edgeA = 2 := by
    have := Subgroup.relIndex_map_map_of_injective X.coreB ⊤ X.toA_injective
    rw [Subgroup.map_top, Subgroup.relIndex_top_right] at this
    exact this.trans h2
  have hW : Q.normalCore.relIndex X.edgeA ≤ 8 := gold_relIndex_normalCore_le_eight hA hQE hQ2
  have hWle : Q.normalCore ≤ X.edgeA := Q.normalCore_le.trans hQE
  have hKmap : (Q.normalCore.comap X.toA).map X.toA = Q.normalCore :=
    Subgroup.map_comap_eq_self hWle
  have hKA : ((Q.normalCore.comap X.toA).map X.toA).Normal := by
    rw [hKmap]
    exact Subgroup.normalCore_normal _
  have hKle : Q.normalCore.comap X.toA ≤ X.coreB := by
    intro c hc
    obtain ⟨c', hc', hcc'⟩ := Q.normalCore_le hc
    have : c' = c := X.toA_injective hcc'
    rwa [← this]
  have hKB : ((Q.normalCore.comap X.toA).map X.toB).Normal := by
    apply Subgroup.normal_of_le_center
    calc _ ≤ X.coreB.map X.toB := Subgroup.map_mono hKle
      _ = X.edgeB.normalCore := X.swap.map_coreA
      _ = pCore 2 B := hcoreB
      _ ≤ _ := hQB
  have hbot := hf _ hKA hKB
  rw [hbot, Subgroup.map_bot] at hKmap
  rw [← hKmap, Subgroup.relIndex_bot_left] at hW
  have hcard : Nat.card X.edgeA = Nat.card C :=
    Nat.card_congr (MonoidHom.ofInjective X.toA_injective).toEquiv.symm
  rwa [hcard] at hW

theorem elementary_card_le_eight_of_normal_central (hf : X.IsFaithful) (hA : X.edgeA.index = 3)
    (hB : X.edgeB.index = 3) (hQA : pCore 2 A = X.edgeA) (hQB : pCore 2 B ≤ Subgroup.center B) :
    (∀ x y : C, x * y = y * x) ∧ (∀ x : C, x ^ 2 = 1) ∧ Nat.card C ≤ 8 := by
  have hcoreA : X.edgeA.normalCore = X.edgeA :=
    (X.normalCore_edgeA_eq_pCore hf hA hB).trans hQA
  have hnorm : X.edgeA.Normal := by
    rw [← hcoreA]
    exact Subgroup.normalCore_normal _
  rcases (Nat.dvd_prime Nat.prime_two).mp (X.coreB_index_dvd_two hB) with h1 | h2
  · have hx : ∀ x : C, x = 1 :=
      X.eq_one_of_normal_normal hf hnorm ((X.coreB_index_eq_one_iff_normal).mp h1)
    have hsub : Subsingleton C := ⟨fun x y => by rw [hx x, hx y]⟩
    refine ⟨fun x y => by rw [hx x, hx y], fun x => by rw [hx x, one_pow], ?_⟩
    rw [Nat.card_of_subsingleton 1]
    norm_num
  · have hsq := X.sq_eq_one_of_normal_central hf hA hB hnorm hQB
    exact ⟨gold_comm_of_sq_eq_one hsq, hsq, X.card_le_eight_of_normal_central hf hA hB hnorm hQB h2⟩

theorem eq_one_of_pCore_eq_edge (hf : X.IsFaithful) (hA : X.edgeA.index = 3)
    (hB : X.edgeB.index = 3) (hQA : pCore 2 A = X.edgeA) (hQB : pCore 2 B = X.edgeB) (x : C) :
    x = 1 := by
  have hnA : X.edgeA.Normal := by
    rw [← (X.normalCore_edgeA_eq_pCore hf hA hB).trans hQA]
    exact Subgroup.normalCore_normal _
  have hnB : X.edgeB.Normal := by
    rw [← (X.normalCore_edgeB_eq_pCore hf hA hB).trans hQB]
    exact Subgroup.normalCore_normal _
  exact X.eq_one_of_normal_normal hf hnA hnB x

omit [Finite A] in
theorem coreB_index_eq_two_of_pCore_ne (hf : X.IsFaithful) (hA : X.edgeA.index = 3)
    (hB : X.edgeB.index = 3) (hQB : pCore 2 B ≠ X.edgeB) : X.coreB.index = 2 := by
  rcases (Nat.dvd_prime Nat.prime_two).mp (X.coreB_index_dvd_two hB) with h1 | h2
  · exfalso
    apply hQB
    have hn := (X.coreB_index_eq_one_iff_normal).mp h1
    rw [← X.normalCore_edgeB_eq_pCore hf hA hB]
    exact Subgroup.normalCore_eq_self _
  · exact h2

end NormalVertex

section AbelianEdge

variable [Finite A] [Finite C] [Finite B]

theorem card_le_four_of_abelian_S3_S3 (hC : ∀ x y : C, x * y = y * x) (hf : X.IsFaithful)
    (hA : X.edgeA.index = 3) (hB : X.edgeB.index = 3)
    (hSA : Nonempty (A ⧸ pCore 2 A ≃* Equiv.Perm (Fin 3)))
    (hSB : Nonempty (B ⧸ pCore 2 B ≃* Equiv.Perm (Fin 3))) :
    (∀ x : C, x ^ 2 = 1) ∧ Nat.card C ≤ 4 := by
  have hZA := X.pCore_le_center_of_abelian hC hf hA hB hSA
  have hZB := X.pCore_le_center_of_abelian_B hC hf hA hB hSB
  have hcA : X.edgeA.normalCore = pCore 2 A := X.normalCore_edgeA_eq_pCore hf hA hB
  have hcB : X.edgeB.normalCore = pCore 2 B := X.normalCore_edgeB_eq_pCore hf hA hB
  have hKA : ((X.coreA ⊓ X.coreB).map X.toA).Normal := by
    apply Subgroup.normal_of_le_center
    calc _ ≤ X.coreA.map X.toA := Subgroup.map_mono inf_le_left
      _ = X.edgeA.normalCore := X.map_coreA
      _ = pCore 2 A := hcA
      _ ≤ _ := hZA
  have hKB : ((X.coreA ⊓ X.coreB).map X.toB).Normal := by
    apply Subgroup.normal_of_le_center
    calc _ ≤ X.coreB.map X.toB := Subgroup.map_mono inf_le_right
      _ = X.edgeB.normalCore := X.swap.map_coreA
      _ = pCore 2 B := hcB
      _ ≤ _ := hZB
  have hK : X.coreA ⊓ X.coreB = ⊥ := hf _ hKA hKB
  have hidxA : X.coreA.index = 2 := (X.coreA_index_eq_two_iff hf hA hB).mpr hSA
  have hidxB : X.coreB.index = 2 := (X.coreB_index_eq_two_iff hf hA hB).mpr hSB
  refine ⟨fun x => ?_, ?_⟩
  · have h1 : x ^ 2 ∈ X.coreA := by
      have := X.coreA_normal
      exact gold_sq_mem_of_index_dvd_two (by rw [hidxA]) x
    have h2 : x ^ 2 ∈ X.coreB := by
      have := X.coreB_normal
      exact gold_sq_mem_of_index_dvd_two (by rw [hidxB]) x
    have : x ^ 2 ∈ X.coreA ⊓ X.coreB := ⟨h1, h2⟩
    rw [hK] at this
    simpa using this
  · have := Subgroup.index_inf_le (H := X.coreA) (K := X.coreB)
    rw [hK, Subgroup.index_bot, hidxA, hidxB] at this
    exact this

theorem eq_one_of_abelian_C3_C3 (hf : X.IsFaithful) (hA : X.edgeA.index = 3)
    (hB : X.edgeB.index = 3)
    (hCA : Nonempty (A ⧸ pCore 2 A ≃* Multiplicative (ZMod 3)))
    (hCB : Nonempty (B ⧸ pCore 2 B ≃* Multiplicative (ZMod 3))) (x : C) : x = 1 :=
  X.eq_one_of_normal_normal hf ((X.coreA_index_eq_one_iff_normal).mp
    ((X.coreA_index_eq_one_iff hf hA hB).mpr hCA))
    ((X.coreB_index_eq_one_iff_normal).mp ((X.coreB_index_eq_one_iff hf hA hB).mpr hCB)) x

theorem elementary_card_le_eight_of_abelian_C3_S3 (hC : ∀ x y : C, x * y = y * x)
    (hf : X.IsFaithful) (hA : X.edgeA.index = 3) (hB : X.edgeB.index = 3)
    (hCA : Nonempty (A ⧸ pCore 2 A ≃* Multiplicative (ZMod 3)))
    (hSB : Nonempty (B ⧸ pCore 2 B ≃* Equiv.Perm (Fin 3))) :
    (∀ x : C, x ^ 2 = 1) ∧ Nat.card C ≤ 8 := by
  have hQA : pCore 2 A = X.edgeA := by
    have hn := (X.coreA_index_eq_one_iff_normal).mp ((X.coreA_index_eq_one_iff hf hA hB).mpr hCA)
    rw [← X.normalCore_edgeA_eq_pCore hf hA hB]
    exact Subgroup.normalCore_eq_self _
  have hZB := X.pCore_le_center_of_abelian_B hC hf hA hB hSB
  obtain ⟨_, hsq, hcard⟩ := X.elementary_card_le_eight_of_normal_central hf hA hB hQA hZB
  exact ⟨hsq, hcard⟩

theorem elementary_card_le_eight_of_abelian_S3_C3 (hC : ∀ x y : C, x * y = y * x)
    (hf : X.IsFaithful) (hA : X.edgeA.index = 3) (hB : X.edgeB.index = 3)
    (hSA : Nonempty (A ⧸ pCore 2 A ≃* Equiv.Perm (Fin 3)))
    (hCB : Nonempty (B ⧸ pCore 2 B ≃* Multiplicative (ZMod 3))) :
    (∀ x : C, x ^ 2 = 1) ∧ Nat.card C ≤ 8 := by
  have := X.swap.elementary_card_le_eight_of_abelian_C3_S3 hC ((X.swap_isFaithful_iff).mpr hf)
    hB hA hCB hSA
  exact this

theorem abelian_edge_elementary_card_le_eight (hC : ∀ x y : C, x * y = y * x)
    (hf : X.IsFaithful) (hA : X.edgeA.index = 3) (hB : X.edgeB.index = 3) :
    (∀ x : C, x ^ 2 = 1) ∧ Nat.card C ≤ 8 := by
  rcases X.quotient_pCore_equiv hf hA hB with ⟨_, hCA⟩ | ⟨_, hSA⟩ <;>
    rcases X.quotient_pCore_equiv_B hf hA hB with ⟨_, hCB⟩ | ⟨_, hSB⟩
  · have hx := X.eq_one_of_abelian_C3_C3 hf hA hB hCA hCB
    refine ⟨fun x => by rw [hx x, one_pow], ?_⟩
    have hsub : Subsingleton C := ⟨fun x y => by rw [hx x, hx y]⟩
    rw [Nat.card_of_subsingleton 1]
    norm_num
  · exact X.elementary_card_le_eight_of_abelian_C3_S3 hC hf hA hB hCA hSB
  · exact X.elementary_card_le_eight_of_abelian_S3_C3 hC hf hA hB hSA hCB
  · obtain ⟨hsq, hcard⟩ := X.card_le_four_of_abelian_S3_S3 hC hf hA hB hSA hSB
    exact ⟨hsq, by omega⟩

end AbelianEdge

end GoldAmalgam

end CFSG.Quasithin
