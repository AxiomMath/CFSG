module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Statements
public import CFSG.Quasithin.Background.F6Basic
public import CFSG.Quasithin.Background.B2FactorizationBridge

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

namespace L15412

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped Pointwise

variable {G : Type*} [Group G]

theorem mem_sup_iff_exists_mul {Y T : Subgroup G} (hTY : T ≤ Subgroup.normalizer (Y : Set G))
    {x : G} : x ∈ Y ⊔ T ↔ ∃ y ∈ Y, ∃ t ∈ T, x = y * t := by
  have h : ((Y ⊔ T : Subgroup G) : Set G) = (Y : Set G) * (T : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left Y T hTY
  constructor
  · intro hx
    have hx' : x ∈ ((Y ⊔ T : Subgroup G) : Set G) := hx
    rw [h] at hx'
    obtain ⟨y, hy, t, ht, rfl⟩ := Set.mem_mul.mp hx'
    exact ⟨y, hy, t, ht, rfl⟩
  · rintro ⟨y, hy, t, ht, rfl⟩
    exact Subgroup.mul_mem_sup hy ht

theorem card_sup_mul_card_inf [Finite G] {Y T : Subgroup G}
    (hTY : T ≤ Subgroup.normalizer (Y : Set G)) :
    Nat.card ↥(Y ⊔ T) * Nat.card ↥(Y ⊓ T) = Nat.card Y * Nat.card T := by
  have h1 := B2F.relIndex_sup_eq_of_le_normalizer' hTY
  have h2 := Subgroup.relIndex_mul_card Y (T ⊔ Y)
  have h3 := Subgroup.relIndex_mul_card Y T
  have h4 : Y ⊓ (T ⊔ Y) = Y := inf_of_le_left le_sup_right
  rw [h4, h1] at h2
  rw [sup_comm] at h2
  rw [← h2, ← h3, inf_comm]
  ring

theorem relIndex_sup_eq [Finite G] {Y T : Subgroup G}
    (hTY : T ≤ Subgroup.normalizer (Y : Set G)) :
    T.relIndex (Y ⊔ T) = (Y ⊓ T).relIndex Y := by
  have e1 := card_sup_mul_card_inf hTY
  have e2 := Subgroup.relIndex_mul_card T (Y ⊔ T)
  rw [inf_eq_left.2 le_sup_right] at e2
  have e3 := Subgroup.relIndex_mul_card (Y ⊓ T) Y
  rw [inf_eq_left.2 inf_le_left] at e3
  have hpos : 0 < Nat.card ↥(Y ⊓ T) := Nat.card_pos
  have hposT : 0 < Nat.card T := Nat.card_pos
  have key : T.relIndex (Y ⊔ T) * Nat.card T * Nat.card ↥(Y ⊓ T) =
      (Y ⊓ T).relIndex Y * Nat.card ↥(Y ⊓ T) * Nat.card T := by
    rw [e2, e1, e3]
  have key' : T.relIndex (Y ⊔ T) * (Nat.card T * Nat.card ↥(Y ⊓ T)) =
      (Y ⊓ T).relIndex Y * (Nat.card T * Nat.card ↥(Y ⊓ T)) := by
    calc T.relIndex (Y ⊔ T) * (Nat.card T * Nat.card ↥(Y ⊓ T))
        = T.relIndex (Y ⊔ T) * Nat.card T * Nat.card ↥(Y ⊓ T) := by ring
      _ = (Y ⊓ T).relIndex Y * Nat.card ↥(Y ⊓ T) * Nat.card T := key
      _ = (Y ⊓ T).relIndex Y * (Nat.card T * Nat.card ↥(Y ⊓ T)) := by ring
  exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hposT hpos) key'

theorem oTwoUpper_sup_eq [Finite G] {T Y : Subgroup G} (hT : IsPGroup 2 T)
    (hTY : T ≤ Subgroup.normalizer (Y : Set G)) (hY : Y = oTwoUpper Y) :
    oTwoUpper (Y ⊔ T) = Y := by
  refine (eq_oTwoUpper_of_pow_mem le_sup_left (fun x hx => ?_) hY).symm
  obtain ⟨y, hy, t, ht, rfl⟩ := (mem_sup_iff_exists_mul hTY).mp hx
  obtain ⟨j, hj⟩ := hT ⟨t, ht⟩
  have hj' : t ^ 2 ^ j = 1 := congrArg Subtype.val hj
  obtain ⟨y', hy', hpow⟩ := A4.exists_pow_mul_eq hy (hTY ht) (2 ^ j)
  exact ⟨j, by rw [hpow, hj', mul_one]; exact hy'⟩

theorem twoResidual_sup_eq [Finite G] {T Y : Subgroup G} (hT : IsPGroup 2 T)
    (hTY : T ≤ Subgroup.normalizer (Y : Set G)) (hY : Y = oTwoUpper Y) :
    twoResidual (Y ⊔ T) = Y := by
  rw [F6.twoResidual_eq_oTwoUpper, oTwoUpper_sup_eq hT hTY hY]

theorem isMaxSubgroupIn_sup {Y T P : Subgroup G} (hTY : T ≤ Subgroup.normalizer (Y : Set G))
    (hP : Y ⊓ T = P) (hYT : ¬ Y ≤ T)
    (hirr : ∀ Y' : Subgroup G, P ≤ Y' → Y' ≤ Y → T ≤ Subgroup.normalizer (Y' : Set G) →
      Y' = P ∨ Y' = Y) :
    IsMaxSubgroupIn (Y ⊔ T) T := by
  refine ⟨lt_of_le_of_ne le_sup_right fun h => hYT (h ▸ le_sup_left), fun K hTK hKH => ?_⟩
  have hTK' : T ≤ K := hTK.le
  have hPK : P ≤ K ⊓ Y := by
    rw [← hP]
    exact le_inf (inf_le_right.trans hTK') inf_le_left
  have hTN : T ≤ Subgroup.normalizer ((K ⊓ Y : Subgroup G) : Set G) :=
    B2F.le_normalizer_inf (hTK'.trans Subgroup.le_normalizer) hTY
  rcases hirr (K ⊓ Y) hPK inf_le_right hTN with h | h
  · exfalso
    apply hTK.ne'
    refine le_antisymm (fun k hk => ?_) hTK'
    obtain ⟨y, hy, t, ht, rfl⟩ := (mem_sup_iff_exists_mul hTY).mp (hKH hk)
    have hyK : y ∈ K := by
      have := K.mul_mem hk (K.inv_mem (hTK' ht))
      simpa using this
    have hyP : y ∈ P := h ▸ (⟨hyK, hy⟩ : y ∈ K ⊓ Y)
    have hyT : y ∈ T := (hP ▸ hyP : y ∈ Y ⊓ T).2
    exact T.mul_mem hyT ht
  · exact le_antisymm hKH (sup_le (h ▸ inf_le_left) hTK')

theorem minParabolic_of_isMaxSubgroupIn {H T : Subgroup G} (hsyl : IsSylowTwoOf T H)
    (hn : ¬ H ≤ Subgroup.normalizer (T : Set G)) (hmax : IsMaxSubgroupIn H T) :
    MinParabolic H T T := by
  refine ⟨hsyl, hn, ?_⟩
  ext N
  simp only [maxOver, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hN, hTN⟩
    by_contra hne
    have hlt : T < N := lt_of_le_of_ne hTN (Ne.symm hne)
    exact hN.1.ne (hmax.2 N hlt hN.1.le)
  · rintro rfl
    exact ⟨hmax, le_rfl⟩

@[expose] noncomputable def conjPermHom (H : Subgroup G) (X : Set G)
    (hX : ∀ h ∈ H, ∀ x ∈ X, h * x * h⁻¹ ∈ X) : H →* Equiv.Perm X where
  toFun h :=
    { toFun := fun x => ⟨h * x * (h : G)⁻¹, hX h h.2 x x.2⟩
      invFun := fun x => ⟨(h : G)⁻¹ * x * h, by simpa using hX h⁻¹ (H.inv_mem h.2) x x.2⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [mul_assoc]) }
  map_one' := by
    ext x
    simp
  map_mul' := fun a b => by
    ext x
    simp [mul_assoc]

theorem conjPermHom_apply (H : Subgroup G) (X : Set G) (hX : ∀ h ∈ H, ∀ x ∈ X, h * x * h⁻¹ ∈ X)
    (h : H) (x : X) : ((conjPermHom H X hX h x : X) : G) = h * x * (h : G)⁻¹ :=
  rfl

theorem mem_ker_conjPermHom (H : Subgroup G) (X : Set G)
    (hX : ∀ h ∈ H, ∀ x ∈ X, h * x * h⁻¹ ∈ X) (h : H) :
    h ∈ (conjPermHom H X hX).ker ↔ ∀ x ∈ X, (h : G) * x * (h : G)⁻¹ = x := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h1 x hx
    have := congrArg (fun σ : Equiv.Perm X => ((σ ⟨x, hx⟩ : X) : G)) h1
    simpa [conjPermHom_apply] using this
  · intro h1
    ext x
    exact h1 x x.2

theorem card_wreathSThreeTwo : Nat.card wreathSThreeTwo = 72 := by
  let _ : DecidablePred (· ∈ wreathSThreeTwo) := fun σ =>
    decidable_of_iff (∀ i j : Fin 6, (i.val / 3 = j.val / 3 ↔ (σ i).val / 3 = (σ j).val / 3))
      Iff.rfl
  rw [Nat.card_eq_fintype_card]
  decide

end L15412

end CFSG.Quasithin.EmptyFaithfulMultiple
