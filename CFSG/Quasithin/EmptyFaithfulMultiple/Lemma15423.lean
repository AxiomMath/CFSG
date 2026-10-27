module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Statements2
public import CFSG.Quasithin.Background.A1bBasic
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Quasithin.EmptyFaithfulMultiple.TheoremE

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

section GroupTheory

variable {G : Type*} [Group G]

private theorem mem_normalizer_inf_of_mem {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro x
  simp only [Subgroup.mem_inf]
  rw [hA x, hB x]

private theorem mem_normalizer_sup_of_mem {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

private theorem commutator_le_of_le_normalizer_right {A B : Subgroup G}
    (h : A ≤ Subgroup.normalizer (B : Set G)) : ⁅A, B⁆ ≤ B := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact B.mul_mem ((Subgroup.mem_normalizer_iff.mp (h ha) b).mp hb) (B.inv_mem hb)

private theorem commutator_le_of_le_normalizer_left {A B : Subgroup G}
    (h : B ≤ Subgroup.normalizer (A : Set G)) : ⁅A, B⁆ ≤ A := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have hb' : b * a⁻¹ * b⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (h hb) a⁻¹).mp (A.inv_mem ha)
  have e : a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) := by group
  rw [commutatorElement_def, e]
  exact A.mul_mem ha hb'

private theorem oTwoUpper_sup_eq_of_isPGroup {R Y : Subgroup G} (hR : IsPGroup 2 R)
    (hRY : R ≤ Subgroup.normalizer (Y : Set G)) (hY : Y = oTwoUpper Y) :
    oTwoUpper (Y ⊔ R) = Y := by
  refine (eq_oTwoUpper_of_pow_mem le_sup_left (fun x hx => ?_) hY).symm
  have hx' : x ∈ ((Y ⊔ R : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left Y R hRY] at hx'
  obtain ⟨y, hy, t, ht, rfl⟩ := Set.mem_mul.mp hx'
  obtain ⟨j, hj⟩ := hR ⟨t, ht⟩
  have hj' : t ^ 2 ^ j = 1 := congrArg Subtype.val hj
  obtain ⟨y', hy', hpow⟩ := A4.exists_pow_mul_eq hy (hRY ht) (2 ^ j)
  exact ⟨j, by rw [hpow, hj', mul_one]; exact hy'⟩

private theorem le_normalizer_of_eq_oTwoUpper {M X X₁ Q : Subgroup G} (hXM : X ≤ M)
    (hMX : M ≤ Subgroup.normalizer (X : Set G)) (hX₁X : X₁ ≤ X)
    (hXX₁ : X ≤ Subgroup.normalizer (X₁ : Set G)) (hX₁ : X₁ = oTwoUpper X₁) (hQM : Q ≤ M)
    (hMQ : M ≤ Subgroup.normalizer (Q : Set G)) (hQ : IsPGroup 2 Q) :
    Q ≤ Subgroup.normalizer (X₁ : Set G) := by
  have hR : IsPGroup 2 ↥(X ⊓ Q) := hQ.to_le inf_le_right
  have hW : oTwoUpper (X₁ ⊔ X ⊓ Q) = X₁ :=
    oTwoUpper_sup_eq_of_isPGroup hR (inf_le_left.trans hXX₁) hX₁
  have key : ∀ g ∈ Q, ∀ x ∈ X₁, g * x * g⁻¹ ∈ X₁ := by
    intro g hg x hx
    have hx' : x ∈ oTwoUpper X₁ := by rw [← hX₁]; exact hx
    clear hx
    rw [← hW]
    induction hx' using Subgroup.closure_induction with
    | mem y hy =>
      refine mem_oTwoUpper_of_odd ?_ ?_
      · have hyX : y ∈ X := hX₁X hy.1
        have hc : g * y * g⁻¹ * y⁻¹ ∈ X ⊓ Q := by
          refine ⟨X.mul_mem ((Subgroup.mem_normalizer_iff.mp (hMX (hQM hg)) y).mp hyX)
            (X.inv_mem hyX), ?_⟩
          have h1 : y * g⁻¹ * y⁻¹ ∈ Q :=
            (Subgroup.mem_normalizer_iff.mp (hMQ (hXM hyX)) g⁻¹).mp (Q.inv_mem hg)
          have e : g * y * g⁻¹ * y⁻¹ = g * (y * g⁻¹ * y⁻¹) := by group
          rw [e]
          exact Q.mul_mem hg h1
        have e : g * y * g⁻¹ = (g * y * g⁻¹ * y⁻¹) * y := by group
        rw [e]
        exact (X₁ ⊔ X ⊓ Q).mul_mem (Subgroup.mem_sup_right hc) (Subgroup.mem_sup_left hy.1)
      · rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
        exact hy.2
    | one => simp
    | mul a b _ _ iha ihb =>
      have e : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ iha ihb
    | inv a _ iha =>
      have e : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
      rw [e]
      exact Subgroup.inv_mem _ iha
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun h => ?_⟩
  have := key g⁻¹ (Q.inv_mem hg) _ h
  simpa [mul_assoc] using this

private theorem commutator_le_pCoreOf_of_le {V L Q : Subgroup G}
    (hLQ : L ≤ Subgroup.normalizer (Q : Set G)) (hQ : IsPGroup 2 Q) (hVQ : V ≤ Q)
    (hVL : V ≤ Subgroup.normalizer (L : Set G)) (hLV : L ≤ Subgroup.normalizer (V : Set G)) :
    ⁅V, L⁆ ≤ pCoreOf 2 L := by
  have h1 : ⁅V, L⁆ ≤ L ⊓ Q :=
    le_inf (commutator_le_of_le_normalizer_right hVL)
      ((commutator_le_of_le_normalizer_left hLV).trans hVQ)
  refine h1.trans (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
    (hQ.to_le inf_le_right))
  intro l hl
  exact mem_normalizer_inf_of_mem (Subgroup.le_normalizer hl) (hLQ hl)

private theorem isElemAbelian_sup_of_commute {p : ℕ} {P C : Subgroup G} (hP : IsElemAbelian p P)
    (hC : IsElemAbelian p C) (hPC : ∀ x ∈ P, ∀ y ∈ C, x * y = y * x) :
    IsElemAbelian p (P ⊔ C) := CFSG.Open.IsElemAbelian.sup_of_commute hP hC hPC

private theorem isPGroup_of_isElemAbelian {p : ℕ} {E : Subgroup G} (hE : IsElemAbelian p E) :
    IsPGroup p E := CFSG.Open.IsElemAbelian.isPGroup hE

private theorem isElemAbelian_of_card_eq_three {C : Subgroup G} (hC : Nat.card C = 3) :
    IsElemAbelian 3 C := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : IsCyclic C := isCyclic_of_prime_card hC
  refine ⟨inferInstance, fun x hx => ?_⟩
  have h := pow_card_eq_one' (G := C) (x := ⟨x, hx⟩)
  rw [hC] at h
  exact congrArg Subtype.val h

variable [Finite G]

private theorem pCoreOf_le_pCoreOf_of_le_normalizer {L X : Subgroup G} (hLX : L ≤ X)
    (hXL : X ≤ Subgroup.normalizer (L : Set G)) : pCoreOf 2 L ≤ pCoreOf 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans hLX)
    (hXL.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)

theorem mul_comm_of_le_centralizer {S V : Subgroup G} (hVS : V ≤ S)
    (hVc : S ≤ Subgroup.centralizer (V : Set G)) (hcard : Nat.card S = 2 * Nat.card V) {a b : G}
    (ha : a ∈ S) (hb : b ∈ S) : a * b = b * a := by
  by_cases haV : a ∈ V
  · exact (Subgroup.mem_centralizer_iff.mp (hVc hb) a haV)
  by_cases hbV : b ∈ V
  · exact (Subgroup.mem_centralizer_iff.mp (hVc ha) b hbV).symm
  have hidx : (V.subgroupOf S).index = 2 := by
    have h1 := Subgroup.index_mul_card (V.subgroupOf S)
    have h2 : Nat.card (V.subgroupOf S) = Nat.card V :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVS).toEquiv
    rw [h2, hcard] at h1
    have hpos : 0 < Nat.card V := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos h1
  have hv : (⟨a, ha⟩ : S)⁻¹ * ⟨b, hb⟩ ∈ V.subgroupOf S := by
    rw [Subgroup.mul_mem_iff_of_index_two hidx, Subgroup.inv_mem_iff]
    simp only [Subgroup.mem_subgroupOf]
    exact iff_of_false haV hbV
  rw [Subgroup.mem_subgroupOf] at hv
  have hv' : a⁻¹ * b ∈ V := by simpa using hv
  have hcomm : a⁻¹ * b * a = a * (a⁻¹ * b) :=
    Subgroup.mem_centralizer_iff.mp (hVc ha) _ hv'
  calc a * b = a * (a * (a⁻¹ * b)) := by group
    _ = a * (a⁻¹ * b * a) := by rw [hcomm]
    _ = b * a := by group

private theorem mul_comm_of_card_eq_three {C : Subgroup G} (hC : Nat.card C = 3) {p : G}
    (hp : p ∈ Subgroup.normalizer (C : Set G)) (hp3 : p ^ 3 = 1) {c : G} (hc : c ∈ C) :
    p * c = c * p := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hc1 : c = 1
  · simp [hc1]
  have hc3 : c ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := C) (x := ⟨c, hc⟩)
    rw [hC] at h
    exact congrArg Subtype.val h
  have hoc : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  have hCz : C = Subgroup.zpowers c :=
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hc)
      (by rw [Nat.card_zpowers, hoc, hC])).symm
  have hd : p * c * p⁻¹ ∈ Subgroup.zpowers c := by
    rw [← hCz]
    exact (Subgroup.mem_normalizer_iff.mp hp c).mp hc
  rw [mem_zpowers_iff_mem_range_orderOf, hoc] at hd
  obtain ⟨k, hk, hkc⟩ := Finset.mem_image.mp hd
  have hk3 : k < 3 := Finset.mem_range.mp hk
  interval_cases k
  · exfalso
    apply hc1
    have h1 : p * c * p⁻¹ = 1 := by rw [← hkc, pow_zero]
    have e : c = p⁻¹ * (p * c * p⁻¹) * p := by group
    rw [e, h1]
    group
  · rw [pow_one] at hkc
    calc p * c = p * c * p⁻¹ * p := by group
      _ = c * p := by rw [← hkc]
  · exfalso
    apply hc1
    have h1 : p * c * p⁻¹ = c ^ 2 := hkc.symm
    have h2 : p * c ^ 2 * p⁻¹ = c ^ 4 := by rw [← conj_pow, h1, ← pow_mul]
    have h3 : p * c ^ 4 * p⁻¹ = c ^ 8 := by rw [← conj_pow, h1, ← pow_mul]
    have hp3' : p * p * p = 1 := by rw [← pow_three']; exact hp3
    have h4 : p * (p * (p * c * p⁻¹) * p⁻¹) * p⁻¹ = c :=
      calc _ = (p * p * p) * c * (p * p * p)⁻¹ := by group
        _ = c := by rw [hp3']; group
    have h6 : c ^ 8 = c := by
      rw [← h3, ← h2, ← h1]
      exact h4
    have h8 : c ^ 8 = c ^ 2 := by
      have e : c ^ 8 = (c ^ 3) ^ 2 * c ^ 2 := by rw [← pow_mul, ← pow_add]
      rw [e, hc3, one_pow, one_mul]
    have h5 : c ^ 2 = c := by rw [← h8, h6]
    calc c = c⁻¹ * c ^ 2 := by group
      _ = c⁻¹ * c := by rw [h5]
      _ = 1 := by group

end GroupTheory

namespace AltSix

open Equiv

private def cycA : Perm (Fin 6) := swap 0 1 * swap 1 2

private def cycB : Perm (Fin 6) := swap 3 4 * swap 4 5

private def e9Finset : Finset (Perm (Fin 6)) :=
  {1, cycA, cycA ^ 2, cycB, cycB ^ 2, cycA * cycB, cycA * cycB ^ 2, cycA ^ 2 * cycB,
    cycA ^ 2 * cycB ^ 2}

private def dihR : Perm (Fin 6) := swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5

private def dihS : Perm (Fin 6) := swap 0 2 * swap 4 5

private def d8Finset : Finset (Perm (Fin 6)) :=
  {1, dihR, dihR ^ 2, dihR ^ 3, dihS, dihR * dihS, dihR ^ 2 * dihS, dihR ^ 3 * dihS}

private theorem e9_mul : ∀ a ∈ e9Finset, ∀ b ∈ e9Finset, a * b ∈ e9Finset := by decide +kernel

private theorem e9_one : (1 : Perm (Fin 6)) ∈ e9Finset := by decide +kernel

private theorem e9_inv : ∀ a ∈ e9Finset, a⁻¹ ∈ e9Finset := by decide +kernel

private theorem e9_comm : ∀ a ∈ e9Finset, ∀ b ∈ e9Finset, a * b = b * a := by decide +kernel

private theorem e9_pow : ∀ a ∈ e9Finset, a ^ 3 = 1 := by decide +kernel

private theorem e9_sign : ∀ a ∈ e9Finset, Perm.sign a = 1 := by decide +kernel

private theorem e9_card : e9Finset.card = 9 := by decide +kernel

private theorem d8_mul : ∀ a ∈ d8Finset, ∀ b ∈ d8Finset, a * b ∈ d8Finset := by decide +kernel

private theorem d8_one : (1 : Perm (Fin 6)) ∈ d8Finset := by decide +kernel

private theorem d8_inv : ∀ a ∈ d8Finset, a⁻¹ ∈ d8Finset := by decide +kernel

private theorem d8_sign : ∀ a ∈ d8Finset, Perm.sign a = 1 := by decide +kernel

private theorem d8_card : d8Finset.card = 8 := by decide +kernel

private theorem dihR_mem : dihR ∈ d8Finset := by decide +kernel

private theorem dihS_mem : dihS ∈ d8Finset := by decide +kernel

private theorem dihR_mul_dihS : dihR * dihS ≠ dihS * dihR := by decide +kernel

private def e9Perm : Subgroup (Perm (Fin 6)) where
  carrier := ↑e9Finset
  mul_mem' ha hb := e9_mul _ ha _ hb
  one_mem' := e9_one
  inv_mem' ha := e9_inv _ ha

private def d8Perm : Subgroup (Perm (Fin 6)) where
  carrier := ↑d8Finset
  mul_mem' ha hb := d8_mul _ ha _ hb
  one_mem' := d8_one
  inv_mem' ha := d8_inv _ ha

private theorem e9Perm_le : e9Perm ≤ alternatingGroup (Fin 6) := fun _ ha =>
  Perm.mem_alternatingGroup.mpr (e9_sign _ ha)

private theorem d8Perm_le : d8Perm ≤ alternatingGroup (Fin 6) := fun _ ha =>
  Perm.mem_alternatingGroup.mpr (d8_sign _ ha)

theorem card_eq : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  rfl

theorem isSimpleGroup : IsSimpleGroup (alternatingGroup (Fin 6)) :=
  alternatingGroup.isSimpleGroup (by simp)

theorem exists_isElemAbelian_card_eq_nine :
    ∃ P : Subgroup (alternatingGroup (Fin 6)), IsElemAbelian 3 P ∧ Nat.card P = 9 := by
  refine ⟨e9Perm.subgroupOf (alternatingGroup (Fin 6)), ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · apply Subtype.ext
    apply Subtype.ext
    exact e9_comm _ (Subgroup.mem_subgroupOf.mp a.2) _ (Subgroup.mem_subgroupOf.mp b.2)
  · apply Subtype.ext
    exact e9_pow _ (Subgroup.mem_subgroupOf.mp hx)
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe e9Perm_le).toEquiv]
    exact (Nat.card_eq_finsetCard e9Finset).trans e9_card

theorem exists_mul_ne_of_card_eq_eight' (S : Subgroup (alternatingGroup (Fin 6)))
    (hS : Nat.card S = 8) : ∃ a ∈ S, ∃ b ∈ S, a * b ≠ b * a := by
  have hsyl : ∀ U : Subgroup (alternatingGroup (Fin 6)), Nat.card U = 8 → IsSylowTwoOf U ⊤ := by
    intro U hU
    refine ⟨le_top, IsPGroup.of_card (n := 3) (by rw [hU]; norm_num), ?_⟩
    change ¬ 2 ∣ U.relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    have h := Subgroup.index_mul_card U
    rw [hU, card_eq] at h
    omega
  have hD : Nat.card (d8Perm.subgroupOf (alternatingGroup (Fin 6))) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe d8Perm_le).toEquiv]
    exact (Nat.card_eq_finsetCard d8Finset).trans d8_card
  obtain ⟨h, -, hh⟩ := A4.exists_conj_of_isSylowTwoOf (hsyl S hS) (hsyl _ hD)
  let a : alternatingGroup (Fin 6) := ⟨dihR, d8Perm_le dihR_mem⟩
  let b : alternatingGroup (Fin 6) := ⟨dihS, d8Perm_le dihS_mem⟩
  have ha : a ∈ d8Perm.subgroupOf (alternatingGroup (Fin 6)) :=
    Subgroup.mem_subgroupOf.mpr dihR_mem
  have hb : b ∈ d8Perm.subgroupOf (alternatingGroup (Fin 6)) :=
    Subgroup.mem_subgroupOf.mpr dihS_mem
  refine ⟨h⁻¹ * a * h, (hh a).mp ha, h⁻¹ * b * h, (hh b).mp hb, fun heq => ?_⟩
  have hab : a * b = b * a := by
    have e1 : a * b = h * ((h⁻¹ * a * h) * (h⁻¹ * b * h)) * h⁻¹ := by group
    have e2 : b * a = h * ((h⁻¹ * b * h) * (h⁻¹ * a * h)) * h⁻¹ := by group
    rw [e1, e2, heq]
  exact dihR_mul_dihS (congrArg Subtype.val hab)

theorem exists_mul_ne_of_card_eq_eight {H : Type*} [Group H] (e : H ≃* alternatingGroup (Fin 6))
    (S : Subgroup H) (hS : Nat.card S = 8) : ∃ a ∈ S, ∃ b ∈ S, a * b ≠ b * a := by
  have hS' : Nat.card (S.map e.toMonoidHom) = 8 := by
    rw [Subgroup.card_map_of_injective e.injective, hS]
  obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_ne_of_card_eq_eight' _ hS'
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hb
  refine ⟨x, hx, y, hy, fun hxy => hab ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, ← map_mul, hxy]

theorem card_eq_eight_of_isSylowTwoOf {G : Type*} [Group G] [Finite G] {S K : Subgroup G}
    (hS : IsSylowTwoOf S K) (hK : Nat.card K = 360) : Nat.card S = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hS.2.1
  have h1 := Subgroup.relIndex_mul_card S K
  rw [inf_eq_left.mpr hS.1, hk, hK] at h1
  have hodd : ¬ 2 ∣ S.relIndex K := hS.2.2
  have hpos : 0 < S.relIndex K := by
    rcases Nat.eq_zero_or_pos (S.relIndex K) with h | h
    · rw [h, zero_mul] at h1
      exact absurd h1 (by norm_num)
    · exact h
  have hk8 : k ≤ 8 := by
    by_contra hc
    push Not at hc
    have h2 : 2 ^ 9 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hc
    have h3 : 2 ^ k ≤ 360 := by
      rw [← h1]
      exact Nat.le_mul_of_pos_left _ hpos
    omega
  rw [hk]
  interval_cases k <;> simp_all <;> omega

section Subgroups

variable {G : Type*} [Group G]

theorem card_eq_of_mulEquiv {K : Subgroup G} (ψ : K ≃* alternatingGroup (Fin 6)) :
    Nat.card K = 360 :=
  (Nat.card_congr ψ.toEquiv).trans card_eq

theorem isSimpleGroup_of_mulEquiv {K : Subgroup G} (ψ : K ≃* alternatingGroup (Fin 6)) :
    IsSimpleGroup K :=
  have := isSimpleGroup
  ψ.isSimpleGroup

theorem exists_isElemAbelian_le {K : Subgroup G}
    (ψ : K ≃* alternatingGroup (Fin 6)) :
    ∃ P : Subgroup G, P ≤ K ∧ IsElemAbelian 3 P ∧ Nat.card P = 9 := by
  obtain ⟨P₀, hP₀, hP₀9⟩ := exists_isElemAbelian_card_eq_nine
  refine ⟨(P₀.map ψ.symm.toMonoidHom).map K.subtype, Subgroup.map_subtype_le _,
    CFSG.SectionRank.isElemAbelian_map (CFSG.SectionRank.isElemAbelian_map hP₀ _) _, ?_⟩
  rw [Subgroup.card_map_of_injective K.subtype_injective,
    Subgroup.card_map_of_injective ψ.symm.injective, hP₀9]

theorem exists_mul_ne_of_le {K S : Subgroup G}
    (ψ : K ≃* alternatingGroup (Fin 6)) (hSK : S ≤ K) (hS : Nat.card S = 8) :
    ∃ a ∈ S, ∃ b ∈ S, a * b ≠ b * a := by
  have hS' : Nat.card (S.subgroupOf K) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSK).toEquiv, hS]
  obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_ne_of_card_eq_eight ψ _ hS'
  exact ⟨a, Subgroup.mem_subgroupOf.mp ha, b, Subgroup.mem_subgroupOf.mp hb,
    fun h => hab (Subtype.ext h)⟩

theorem inf_eq_bot_of_le_normalizer {K L : Subgroup G} (ψ : K ≃* alternatingGroup (Fin 6))
    (hKL : K ≤ Subgroup.normalizer (L : Set G)) (hL : ¬ 5 ∣ Nat.card L) : K ⊓ L = ⊥ := by
  have := isSimpleGroup_of_mulEquiv ψ
  have hN : (L.subgroupOf K).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hKL
  rcases Subgroup.Normal.eq_bot_or_eq_top (L.subgroupOf K) with h | h
  · rw [Subgroup.subgroupOf_eq_bot] at h
    rw [inf_comm]
    exact disjoint_iff.mp h
  · rw [Subgroup.subgroupOf_eq_top] at h
    have hdvd := Subgroup.card_dvd_of_le h
    rw [card_eq_of_mulEquiv ψ] at hdvd
    exact absurd (dvd_trans (by norm_num : 5 ∣ 360) hdvd) hL

end Subgroups

end AltSix

section Factors

variable {G : Type*} [Group G]

structure IsSixTwoFactor (T M Y L : Subgroup G) : Prop where
  le : L ≤ Y
  le_normalizer : Y ≤ Subgroup.normalizer (L : Set G)
  eq_oTwoUpper : L = oTwoUpper L
  relIndex_eq : (pCoreOf 2 L).relIndex L = 3
  card_commutator : Nat.card (⁅VZ T M, L⁆ : Subgroup G) = 4

namespace IsSixTwoData

variable {T M Y Y₁ Y₂ : Subgroup G}

private theorem eq_sup (h : IsSixTwoData T M Y Y₁ Y₂) : Y = Y₁ ⊔ Y₂ := h.1

theorem inf_commutator_eq_bot (h : IsSixTwoData T M Y Y₁ Y₂) :
    ⁅VZ T M, Y₁⁆ ⊓ ⁅VZ T M, Y₂⁆ = ⊥ := h.2.2.2.2.2.2.1

private theorem symm (h : IsSixTwoData T M Y Y₁ Y₂) : IsSixTwoData T M Y Y₂ Y₁ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, ⟨t, ht, h14⟩, h15, h16,
    h17⟩ := h
  refine ⟨by rw [h1, sup_comm], h3, h2, h5, h4, by rw [h6, sup_comm], by rw [inf_comm, h7], h9,
    h8, h11, h10, h13, h12, ⟨t⁻¹, T.inv_mem ht, ?_⟩, h15, h17, h16⟩
  rw [h14, Subgroup.map_map]
  conv_lhs => rw [← Subgroup.map_id Y₁]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem factor_left (h : IsSixTwoData T M Y Y₁ Y₂) : IsSixTwoFactor T M Y Y₁ := by
  obtain ⟨h1, h2, -, h4, -, -, -, h8, -, -, -, -, -, -, -, h16, -⟩ := h
  exact ⟨le_of_le_of_eq le_sup_left h1.symm, h16, h2, h4, h8⟩

theorem factor_right (h : IsSixTwoData T M Y Y₁ Y₂) : IsSixTwoFactor T M Y Y₂ :=
  h.symm.factor_left

end IsSixTwoData

namespace IsSixTwoFactor

variable {T M Y L : Subgroup G}

theorem card_eq (hL : IsSixTwoFactor T M Y L) : Nat.card L = 3 * Nat.card (pCoreOf 2 L) := by
  have h := Subgroup.relIndex_mul_card (pCoreOf 2 L) L
  rw [inf_eq_left.mpr (CFSG.LieType.BorelTits.pCoreOf_le 2 L), hL.relIndex_eq] at h
  exact h.symm

theorem commutator_le_vZ (hL : IsSixTwoFactor T M Y L) (hYM : Y ≤ M) :
    ⁅VZ T M, L⁆ ≤ VZ T M :=
  commutator_le_of_le_normalizer_left
    ((hL.le.trans hYM).trans (le_normalizer_conjClosure (quasithinOmegaOneCenter T) M))

end IsSixTwoFactor

namespace Setting15419

variable {T : Subgroup G} (s : Setting15419 G T)

private theorem factor₁ : IsSixTwoFactor T s.M₁ s.X s.L₁ := by
  rcases s.choice₁ with h | h <;> rw [h]
  · exact s.dataX.factor_left
  · exact s.dataX.factor_right

private theorem factor₂ : IsSixTwoFactor T s.M₂ s.Y s.L₂ := by
  rcases s.choice₂ with h | h <;> rw [h]
  · exact s.dataY.factor_left
  · exact s.dataY.factor_right

private theorem T₀_le_normalizer_X₁ : s.T₀ ≤ Subgroup.normalizer (s.X₁ : Set G) := inf_le_right

private theorem T₀_le_normalizer_Y₁ : s.T₀ ≤ Subgroup.normalizer (s.Y₁ : Set G) :=
  inf_le_left.trans inf_le_right

private theorem L₁_le_I : s.L₁ ≤ s.I := le_sup_left.trans le_sup_left

private theorem L₂_le_I : s.L₂ ≤ s.I := le_sup_left.trans le_sup_right

private theorem T₀_le_I : s.T₀ ≤ s.I := le_sup_right.trans le_sup_left

end Setting15419

end Factors

section Hypothesis

variable {G : Type} [Group G] [Finite G] {T : Subgroup G}

theorem vZ_le_pCoreOf (hyp : MultipleCentralizerHypothesis G T) {M : Subgroup G}
    (hM : InM T M) : VZ T M ≤ pCoreOf 2 M ∧ IsElemAbelian 2 (VZ T M) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let T' : Sylow 2 G := IsPGroup.toSylow hyp.sylow.1 hyp.sylow.2
  have hTM : (T' : Subgroup G) ≤ M := hM.2
  have hF := hyp.qtke.2.1 M hM.1.1 ⟨T', hTM⟩
  obtain ⟨h1, h2⟩ := conjClosure_le_centerOf_pCoreOf M T' hTM hF
    (Z := quasithinOmegaOneCenter T) le_rfl
  exact ⟨h1.trans inf_le_left, h2⟩

namespace IsSixTwoFactor

variable {M Y L : Subgroup G}

theorem pCoreOf_le_normalizer (h12 : Stmt15412 G T) (hM : InM T M) (hY : IsYFamily T Y)
    (hYM : Y ≤ M) (hL : IsSixTwoFactor T M Y L) :
    pCoreOf 2 M ≤ Subgroup.normalizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact le_normalizer_of_eq_oTwoUpper hYM ((h12 M hM).2 Y hY hYM).1 hL.le hL.le_normalizer
    hL.eq_oTwoUpper (CFSG.LieType.BorelTits.pCoreOf_le 2 M)
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M)

theorem commutator_le_pCoreOf (hyp : MultipleCentralizerHypothesis G T) (h12 : Stmt15412 G T)
    (hM : InM T M) (hY : IsYFamily T Y) (hYM : Y ≤ M) (hL : IsSixTwoFactor T M Y L) :
    ⁅VZ T M, L⁆ ≤ pCoreOf 2 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hV, -⟩ := vZ_le_pCoreOf hyp hM
  exact commutator_le_pCoreOf_of_le
    ((hL.le.trans hYM).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M) hV
    (hV.trans (hL.pCoreOf_le_normalizer h12 hM hY hYM))
    ((hL.le.trans hYM).trans (le_normalizer_conjClosure (quasithinOmegaOneCenter T) M))

theorem four_le_card (hyp : MultipleCentralizerHypothesis G T) (h12 : Stmt15412 G T)
    (hM : InM T M) (hY : IsYFamily T Y) (hYM : Y ≤ M) (hL : IsSixTwoFactor T M Y L) :
    4 ≤ Nat.card (pCoreOf 2 L) := by
  rw [← hL.card_commutator]
  exact Subgroup.card_le_of_le (hL.commutator_le_pCoreOf hyp h12 hM hY hYM)

theorem pCoreOf_le_pCoreOf (h12 : Stmt15412 G T) (hM : InM T M) (hY : IsYFamily T Y)
    (hYM : Y ≤ M) (hL : IsSixTwoFactor T M Y L) : pCoreOf 2 L ≤ pCoreOf 2 M :=
  (pCoreOf_le_pCoreOf_of_le_normalizer hL.le hL.le_normalizer).trans
    (pCoreOf_le_pCoreOf_of_le_normalizer hYM ((h12 M hM).2 Y hY hYM).1)

end IsSixTwoFactor

end Hypothesis

section Lemma15423

variable {G : Type} [Group G] [Finite G] {T : Subgroup G}

private theorem exists_isElemAbelian_of_le_normalizer {L P : Subgroup G} {a : ℕ}
    (hP : IsElemAbelian 3 P) (hP9 : Nat.card P = 9) (hPN : P ≤ Subgroup.normalizer (L : Set G))
    (hPL : P ⊓ L = ⊥) (hL : Nat.card L = 3 * 2 ^ a) :
    ∃ E : Subgroup G, E ≤ L ⊔ P ∧ IsElemAbelian 3 E ∧ ∃ k : ℕ, Nat.card E = 3 ^ k ∧ 3 ≤ k := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hHL : L ⊔ P ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hPN
  obtain ⟨R, hR, hPR⟩ := exists_isSylowIn_ge 3 (le_sup_right : P ≤ L ⊔ P)
    (isPGroup_of_isElemAbelian hP)
  have hLn : (L.subgroupOf (L ⊔ P)).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hHL
  have hC := hR.inf_normal (le_sup_left : L ≤ L ⊔ P) hLn
  have hCcard : Nat.card (R ⊓ L : Subgroup G) = 3 := by
    rw [hC.card_eq, hL, Nat.factorization_mul (by norm_num) (by positivity), Finsupp.add_apply,
      Nat.Prime.factorization_self Nat.prime_three, Nat.factorization_pow, Finsupp.smul_apply,
      Nat.Prime.factorization Nat.prime_two]
    simp
  have hRC : R ≤ Subgroup.normalizer ((R ⊓ L : Subgroup G) : Set G) := fun r hr =>
    mem_normalizer_inf_of_mem (Subgroup.le_normalizer hr) (hHL (hR.le hr))
  have hPC : ∀ x ∈ P, ∀ y ∈ R ⊓ L, x * y = y * x := fun x hx y hy =>
    mul_comm_of_card_eq_three hCcard (hRC (hPR hx)) (hP.2 x hx) hy
  have hE := isElemAbelian_sup_of_commute hP (isElemAbelian_of_card_eq_three hCcard) hPC
  refine ⟨P ⊔ R ⊓ L, sup_le le_sup_right (inf_le_right.trans le_sup_left), hE, ?_⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (isPGroup_of_isElemAbelian hE)
  refine ⟨k, hk, ?_⟩
  have hlt : P < P ⊔ R ⊓ L := by
    refine lt_of_le_of_ne le_sup_left fun heq => ?_
    have hCP : R ⊓ L ≤ P ⊓ L := le_inf (le_sup_right.trans heq.ge) inf_le_right
    rw [hPL, le_bot_iff] at hCP
    rw [hCP, Subgroup.card_bot] at hCcard
    exact absurd hCcard (by norm_num)
  have h1 := Subgroup.card_lt_of_lt hlt
  rw [hP9, hk] at h1
  by_contra hk3
  push Not at hk3
  interval_cases k <;> norm_num at h1

private theorem false_of_charTwo (hyp : MultipleCentralizerHypothesis G T) (h12 : Stmt15412 G T)
    (h19 : Stmt15419 G T) (h21 : Stmt15421 G T) (h22 : Stmt15422 G T) (s : Setting15419 G T)
    (hI : CharTwo s.I) (L₁' : Subgroup G) (hc : L₁' = s.X₁ ∨ L₁' = s.X₂)
    (hX : s.X ≤ s.L₁ ⊔ L₁') : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let s' : Setting15419 G T := { s with L₁ := L₁', choice₁ := hc }
  obtain ⟨-, hIL₁, -⟩ := h21 s hI
  have hf₁ := s.factor₁
  have hf₁' : IsSixTwoFactor T s.M₁ s.X L₁' := s'.factor₁
  have hT₀ : s.T₀ ≤ Subgroup.normalizer (s.L₁ : Set G) := s.T₀_le_I.trans hIL₁
  have hL₂ : s.L₂ ≤ Subgroup.normalizer (s.L₁ : Set G) := s.L₂_le_I.trans hIL₁
  have hL₁' : L₁' ≤ Subgroup.normalizer (s.L₁ : Set G) := hf₁'.le.trans hf₁.le_normalizer
  have hI' : s'.I ≤ Subgroup.normalizer (s.L₁ : Set G) :=
    sup_le (sup_le hL₁' hT₀) (sup_le hL₂ hT₀)
  by_cases hc' : CharTwo s'.I
  ·
    obtain ⟨-, hI'L₁', -⟩ := h21 s' hc'
    have hL₂' : s.L₂ ≤ Subgroup.normalizer (L₁' : Set G) := s'.L₂_le_I.trans hI'L₁'
    have hXeq : s.X = s.L₁ ⊔ L₁' := le_antisymm hX (sup_le hf₁.le hf₁'.le)
    have hL₂X : s.L₂ ≤ Subgroup.normalizer (s.X : Set G) := fun g hg => by
      rw [hXeq]
      exact mem_normalizer_sup_of_mem (hL₂ hg) (hL₂' hg)
    have hNX := ((h12 s.M₁ s.inM₁).2 s.X s.famX s.le_X).2.1
    exact (h19 s).2.2.2.1 (hL₂X.trans hNX.ge)
  ·
    obtain ⟨K, hK, -, ⟨ψ⟩, -⟩ := h22 s' hc'
    have hKN : K ≤ Subgroup.normalizer (s.L₁ : Set G) := (hK.le.trans (oTwoUpper_le s'.I)).trans hI'
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 s.L₁)
    have hcard : Nat.card s.L₁ = 3 * 2 ^ a := by rw [hf₁.card_eq, ha]
    have h5 : ¬ 5 ∣ Nat.card s.L₁ := by
      rw [hcard]
      intro h
      rcases (Nat.prime_five.dvd_mul).mp h with h' | h'
      · omega
      · have := Nat.prime_five.dvd_of_dvd_pow h'
        omega
    have hKL : K ⊓ s.L₁ = ⊥ := AltSix.inf_eq_bot_of_le_normalizer ψ hKN h5
    obtain ⟨P, hPK, hP, hP9⟩ := AltSix.exists_isElemAbelian_le ψ
    have hPL : P ⊓ s.L₁ = ⊥ := le_bot_iff.mp ((inf_le_inf_right _ hPK).trans hKL.le)
    obtain ⟨E, hE, hEe, k, hk, hk3⟩ :=
      exists_isElemAbelian_of_le_normalizer hP hP9 (hPK.trans hKN) hPL hcard
    have hne : pCoreOf 2 s.L₁ ≠ ⊥ := by
      intro h
      have h4 := hf₁.four_le_card hyp h12 s.inM₁ s.famX s.le_X
      rw [h, Subgroup.card_bot] at h4
      omega
    have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 s.L₁ : Set G)) :=
      ⟨_, hne, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _, rfl⟩
    have hEN : E ≤ Subgroup.normalizer (pCoreOf 2 s.L₁ : Set G) :=
      hE.trans ((sup_le Subgroup.le_normalizer (hPK.trans hKN)).trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 s.L₁))
    have h1 := CFSG.SectionRank.le_pRank (by norm_num) hEN hEe hk
    have h2 := CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank 3 Nat.prime_three
      (by norm_num) _ hloc
    have h3 : CFSG.Open.evenRank G ≤ 2 := hyp.qtke.2.2
    omega

theorem stmt15423_of {G : Type} [Group G] [Finite G] {T : Subgroup G}
    (hyp : MultipleCentralizerHypothesis G T) (h12 : Stmt15412 G T) (h19 : Stmt15419 G T)
    (h21 : Stmt15421 G T) (h22 : Stmt15422 G T) : Stmt15423 G T := by
  intro s hI
  rcases s.choice₁ with hL | hL
  · refine false_of_charTwo hyp h12 h19 h21 h22 s hI s.X₂ (Or.inr rfl) ?_
    rw [hL, ← s.dataX.eq_sup]
  · refine false_of_charTwo hyp h12 h19 h21 h22 s hI s.X₁ (Or.inl rfl) ?_
    rw [hL, sup_comm, ← s.dataX.eq_sup]

end Lemma15423

end CFSG.Quasithin.EmptyFaithfulMultiple
