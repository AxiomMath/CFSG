module

public import CFSG.Quasithin.Vol2.Ch12Sec2Inputs
public import CFSG.Quasithin.Vol2.Ch3Sec2Lem328Iso
public import CFSG.Quasithin.Background.A4Aut

public section

namespace CFSG.Quasithin.H13

open CFSG.Open
open scoped IsMulCommutative Pointwise commutatorElement

section Elementary

variable {G : Type*} [Group G]

theorem card_mul_card_le_card_sup_of_inf_eq_bot [Finite G] {A B : Subgroup G}
    (hAB : A ⊓ B = ⊥) : Nat.card A * Nat.card B ≤ Nat.card ↥(A ⊔ B) := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective
    (fun p => ⟨(p.1 : G) * p.2, Subgroup.mul_mem_sup p.1.2 p.2.2⟩) ?_
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  have h' : (a : G) * b = a' * b' := congrArg Subtype.val h
  have hx : (a' : G)⁻¹ * a = b' * (b : G)⁻¹ := by
    calc (a' : G)⁻¹ * a = (a' : G)⁻¹ * (a * b) * (b : G)⁻¹ := by group
      _ = (a' : G)⁻¹ * (a' * b') * (b : G)⁻¹ := by rw [h']
      _ = b' * (b : G)⁻¹ := by group
  have hmem : (a' : G)⁻¹ * a ∈ A ⊓ B :=
    ⟨A.mul_mem (A.inv_mem a'.2) a.2, hx ▸ B.mul_mem b'.2 (B.inv_mem b.2)⟩
  rw [hAB, Subgroup.mem_bot] at hmem
  have ha : (a : G) = a' := by
    calc (a : G) = a' * ((a' : G)⁻¹ * a) := by group
      _ = a' := by rw [hmem, mul_one]
  have hb : (b : G) = b' := by
    rw [ha] at h'
    exact mul_left_cancel h'
  simp only [Prod.mk.injEq]
  exact ⟨Subtype.ext ha, Subtype.ext hb⟩

theorem card_sup_le_mul_of_le_normalizer [Finite G] {A C : Subgroup G}
    (h : A ≤ Subgroup.normalizer (C : Set G)) : Nat.card ↥(A ⊔ C) ≤ Nat.card A * Nat.card C := by
  have hset : ((A ⊔ C : Subgroup G) : Set G) = (A : Set G) * (C : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right A C h
  have : Nat.card ↥(A ⊔ C) = Nat.card ((A : Set G) * (C : Set G)) := by
    rw [← hset]
    rfl
  rw [this]
  exact Set.natCard_mul_le

theorem le_normalizer_of_le_of_commute {V A B : Subgroup G}
    (hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (hAV : A ≤ V) (hBV : B ≤ V) :
    A ≤ Subgroup.normalizer (B : Set G) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro b
  constructor
  · intro hb
    rw [hVc a (hAV ha) b (hBV hb), mul_assoc, mul_inv_cancel, mul_one]
    exact hb
  · intro hb
    have hb' : b = a⁻¹ * (a * b * a⁻¹) * a := by group
    rw [hb']
    have hx : a * b * a⁻¹ ∈ V := hBV hb
    rw [hVc a⁻¹ (V.inv_mem (hAV ha)) _ hx, mul_assoc, inv_mul_cancel, mul_one]
    exact hb

theorem commutator_le_of_le_centralizer {V L A B : Subgroup G}
    (hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (hAV : A ≤ V) (hBV : B ≤ V)
    (hLB : L ≤ Subgroup.normalizer (B : Set G)) (hAC : A ≤ Subgroup.centralizer (L : Set G))
    (hABV : A ⊔ B = V) : ⁅V, L⁆ ≤ B := by
  have hset : ((A ⊔ B : Subgroup G) : Set G) = (A : Set G) * (B : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right A B (le_normalizer_of_le_of_commute hVc hAV hBV)
  rw [Subgroup.commutator_le]
  intro v hv l hl
  rw [← hABV] at hv
  have hv' : v ∈ (A : Set G) * (B : Set G) := hset ▸ hv
  obtain ⟨a, ha, b, hb, rfl⟩ := hv'
  have hal : a * l = l * a := (Subgroup.mem_centralizer_iff.mp (hAC ha) l hl).symm
  have hbl : ⁅b, l⁆ ∈ B := by
    rw [commutatorElement_def]
    have : l * b⁻¹ * l⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp (hLB hl) b⁻¹).mp (B.inv_mem hb)
    rw [mul_assoc, mul_assoc]
    have := B.mul_mem hb (by simpa [mul_assoc] using this)
    simpa [mul_assoc] using this
  have key : ⁅a * b, l⁆ = a * ⁅b, l⁆ * a⁻¹ := by
    simp only [commutatorElement_def]
    have hal' : l * a⁻¹ * l⁻¹ = a⁻¹ := by
      have : a⁻¹ * l = l * a⁻¹ := by
        calc a⁻¹ * l = a⁻¹ * (l * a) * a⁻¹ := by group
          _ = a⁻¹ * (a * l) * a⁻¹ := by rw [hal]
          _ = l * a⁻¹ := by group
      calc l * a⁻¹ * l⁻¹ = a⁻¹ * l * l⁻¹ := by rw [this]
        _ = a⁻¹ := by group
    calc a * b * l * (a * b)⁻¹ * l⁻¹ = a * (b * l * b⁻¹ * l⁻¹) * (l * a⁻¹ * l⁻¹) := by group
      _ = a * (b * l * b⁻¹ * l⁻¹) * a⁻¹ := by rw [hal']
  rw [key, hVc a (hAV ha) _ (hBV hbl), mul_assoc, mul_inv_cancel, mul_one]
  exact hbl

theorem le_normalizer_inf_centralizer {V L : Subgroup G}
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) :
    L ≤ Subgroup.normalizer ((V ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) :=
  (le_inf hLV fun _ hl => A4.mem_normalizer_centralizer (Subgroup.le_normalizer hl)).trans
    Subgroup.inf_normalizer_le_normalizer_inf

end Elementary

theorem l32FourIndecomposable : L32FourIndecomposable := by
  intro G _ _ L V _ hLV hc hV1 hcard hnat hirr
  set C : Subgroup G := V ⊓ Subgroup.centralizer (L : Set G) with hCdef
  have hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (mul_comm (⟨x, hx⟩ : ↥V) ⟨y, hy⟩)
  have hC2 : Nat.card C = 2 := by
    obtain ⟨K, _, _, hK, π, hπ⟩ := hnat
    have h := card_eq_of_realizesVia_nat hπ
    have h' : Nat.card ↥((Subgroup.centralizer (L : Set G)).subgroupOf V) = Nat.card C := by
      rw [← Subgroup.card_map_of_injective V.subtype_injective, Subgroup.subgroupOf_map_subtype,
        inf_comm]
    rw [Subgroup.card_top, hcard, Nat.card_fun, Nat.card_fin, hK, h'] at h
    norm_num at h
    omega
  have hCV : C ≤ V := inf_le_left
  have hLC := le_normalizer_inf_centralizer hLV
  refine ⟨hV1, fun A B hA hB hLA hLB hAB hABV => ?_⟩
  by_contra hne
  push Not at hne
  obtain ⟨hA1, hB1⟩ := hne
  have hsmall : ∀ X Y : Subgroup G, X ≤ V → Y ≤ V → L ≤ Subgroup.normalizer (Y : Set G) →
      X ⊓ Y = ⊥ → X ⊔ Y = V → X ⊔ C = C → X = ⊥ := by
    intro X Y hX hY hLY hXY hXYV hXC
    have hXc : X ≤ Subgroup.centralizer (L : Set G) :=
      (le_sup_left.trans hXC.le).trans inf_le_right
    have hVY : V ≤ Y := by
      have := commutator_le_of_le_centralizer hVc hX hY hLY hXc hXYV
      rwa [hc] at this
    rw [eq_bot_iff, ← hXY]
    exact le_inf le_rfl (hX.trans hVY)
  have hJ : ∀ X : Subgroup G, X ≤ V → L ≤ Subgroup.normalizer (X : Set G) →
      X ⊔ C = C ∨ X ⊔ C = V := fun X hX hLX =>
    hirr (X ⊔ C) le_sup_right (sup_le hX hCV)
      ((le_inf hLX hLC).trans (Subgroup.inf_normalizer_le_normalizer_sup X C))
  rcases hJ A hA hLA with hAC | hAC
  · exact hA1 (hsmall A B hA hB hLB hAB hABV hAC)
  rcases hJ B hB hLB with hBC | hBC
  · exact hB1 (hsmall B A hB hA hLA (by rw [inf_comm]; exact hAB) (by rw [sup_comm]; exact hABV)
      hBC)
  have h1 := card_sup_le_mul_of_le_normalizer (le_normalizer_of_le_of_commute hVc hA hCV)
  have h2 := card_sup_le_mul_of_le_normalizer (le_normalizer_of_le_of_commute hVc hB hCV)
  have h3 := card_mul_card_le_card_sup_of_inf_eq_bot hAB
  have h16 : Nat.card V = 16 := by rw [hcard]; norm_num
  rw [hAC, h16, hC2] at h1
  rw [hBC, h16, hC2] at h2
  rw [hABV, h16] at h3
  have h8A : 8 ≤ Nat.card A := by omega
  have h8B : 8 ≤ Nat.card B := by omega
  have := Nat.mul_le_mul h8A h8B
  omega

end CFSG.Quasithin.H13
