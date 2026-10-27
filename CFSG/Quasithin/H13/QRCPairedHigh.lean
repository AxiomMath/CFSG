module

public import CFSG.Quasithin.H13.QRCPairedRank
public import CFSG.Quasithin.H13.QRCBenderSection

public section

namespace CFSG.Quasithin.H13.QRC

open Subgroup CFSG.ABGLocalTools CFSG.Quasithin.SteinbergBS CFSG.ShultStronglyClosedTI
  CFSG.BenderSuzuki.MatrixGroups CFSG.GorensteinWalter
  CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField
open scoped MatrixGroups commutatorElement

variable {A : Type*} [Group A] {K₁ K₂ : Subgroup A}

section Pair

variable (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a)
include hc

theorem sup_conjugate_le {E : Subgroup A} {x₁ : A} (hEK : E ≤ K₁ ⊔ K₂) (hx₁ : x₁ ∈ K₁) :
    E ⊔ conjugate E x₁ ≤
      ((E ⊔ K₂) ⊓ K₁ ⊔ conjugate ((E ⊔ K₂) ⊓ K₁) x₁) ⊔ (E ⊔ K₁) ⊓ K₂ := by
  refine sup_le ((le_sup_projections hc hEK).trans (sup_le_sup_right le_sup_left _)) ?_
  intro y hy
  rw [mem_conjugate_iff] at hy
  obtain ⟨e₁, he₁, e₂, he₂, he⟩ := exists_proj_mul hc hEK hy
  have hy' : y = (x₁⁻¹ * e₁ * x₁) * e₂ := by
    have h1 : x₁⁻¹ * e₂ * x₁ = e₂ := by
      rw [mul_assoc, ← hc x₁ hx₁ e₂ he₂.2, inv_mul_cancel_left]
    calc y = x₁⁻¹ * (x₁ * y * x₁⁻¹) * x₁ := by group
      _ = x₁⁻¹ * e₁ * x₁ * (x₁⁻¹ * e₂ * x₁) := by rw [← he]; group
      _ = (x₁⁻¹ * e₁ * x₁) * e₂ := by rw [h1]
  rw [hy']
  refine mul_mem_sup (mem_sup_right ?_) he₂
  rw [mem_conjugate_iff]
  rwa [show x₁ * (x₁⁻¹ * e₁ * x₁) * x₁⁻¹ = e₁ by group]

theorem sup_conjugate_eq_of_perfect {E L₁ : Subgroup A} {x₁ : A} (hEK : E ≤ K₁ ⊔ K₂)
    (hx₁ : x₁ ∈ K₁) (hL₁ : L₁ = (E ⊔ K₂) ⊓ K₁ ⊔ conjugate ((E ⊔ K₂) ⊓ K₁) x₁)
    [Group.IsPerfect L₁]
    (hE₂ : ∀ a ∈ (E ⊔ K₁) ⊓ K₂, ∀ b ∈ (E ⊔ K₁) ⊓ K₂, a * b = b * a) :
    E ⊔ conjugate E x₁ = L₁ ⊔ (E ⊔ K₁) ⊓ K₂ := by
  set E₁ := (E ⊔ K₂) ⊓ K₁ with hE₁
  set E₂ := (E ⊔ K₁) ⊓ K₂ with hE₂def
  set L := E ⊔ conjugate E x₁ with hL
  have hc' : ∀ a ∈ K₂, ∀ b ∈ K₁, a * b = b * a := fun a ha b hb => (hc b hb a ha).symm
  refine le_antisymm (hL₁ ▸ sup_conjugate_le hc hEK hx₁) ?_
  let P : Subgroup A :=
    { carrier := {a | a ∈ K₁ ∧ ∃ a₂ ∈ E₂, a * a₂ ∈ L}
      one_mem' := ⟨K₁.one_mem, 1, E₂.one_mem, by rw [mul_one]; exact L.one_mem⟩
      mul_mem' := by
        rintro a b ⟨ha, a₂, ha₂, haL⟩ ⟨hb, b₂, hb₂, hbL⟩
        refine ⟨K₁.mul_mem ha hb, a₂ * b₂, E₂.mul_mem ha₂ hb₂, ?_⟩
        have h1 := L.mul_mem haL hbL
        rwa [show a * a₂ * (b * b₂) = a * (a₂ * b) * b₂ by group, ← hc b hb a₂ ha₂.2,
          show a * (b * a₂) * b₂ = a * b * (a₂ * b₂) by group] at h1
      inv_mem' := by
        rintro a ⟨ha, a₂, ha₂, haL⟩
        refine ⟨K₁.inv_mem ha, a₂⁻¹, E₂.inv_mem ha₂, ?_⟩
        have h1 := L.inv_mem haL
        rwa [mul_inv_rev, hc' _ (K₂.inv_mem ha₂.2) _ (K₁.inv_mem ha)] at h1 }
  have hE₁P : E₁ ≤ P := fun e₁ he₁ => by
    obtain ⟨e₂, he₂, he⟩ := exists_mul_mem_of_mem_proj hc hEK he₁
    exact ⟨he₁.2, e₂, he₂, le_sup_left (a := E) he⟩
  have hE₁xP : conjugate E₁ x₁ ≤ P := fun y hy => by
    rw [mem_conjugate_iff] at hy
    obtain ⟨e₂, he₂, he⟩ := exists_mul_mem_of_mem_proj hc hEK hy
    have hyK : y ∈ K₁ := by
      have := K₁.mul_mem (K₁.mul_mem (K₁.inv_mem hx₁) hy.2) hx₁
      rwa [show x₁⁻¹ * (x₁ * y * x₁⁻¹) * x₁ = y by group] at this
    refine ⟨hyK, e₂, he₂, le_sup_right (a := E) ?_⟩
    rw [mem_conjugate_iff]
    rwa [show x₁ * (y * e₂) * x₁⁻¹ = x₁ * y * x₁⁻¹ * (x₁ * e₂ * x₁⁻¹) by group,
      hc x₁ hx₁ e₂ he₂.2, mul_inv_cancel_right]
  have hL₁P : L₁ ≤ P := hL₁ ▸ sup_le hE₁P hE₁xP
  have hL₁L : L₁ ≤ L := by
    rw [← commutator_eq_self (H := L₁), commutator_le]
    intro a ha b hb
    obtain ⟨haK, a₂, ha₂, haL⟩ := hL₁P ha
    obtain ⟨hbK, b₂, hb₂, hbL⟩ := hL₁P hb
    have h1 : ⁅a * a₂, b * b₂⁆ ∈ L := by
      rw [commutatorElement_def]
      exact L.mul_mem (L.mul_mem (L.mul_mem haL hbL) (L.inv_mem haL)) (L.inv_mem hbL)
    have h2 : ⁅a * a₂, b * b₂⁆ = ⁅a, b⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      have e1 : a₂ * b = b * a₂ := hc' a₂ ha₂.2 b hbK
      have e2 : b₂ * a = a * b₂ := hc' b₂ hb₂.2 a haK
      have e3 : a₂ * b₂ = b₂ * a₂ := hE₂ a₂ ha₂ b₂ hb₂
      calc a * a₂ * (b * b₂) * (a * a₂)⁻¹ * (b * b₂)⁻¹
          = a * (a₂ * b) * b₂ * a₂⁻¹ * a⁻¹ * b₂⁻¹ * b⁻¹ := by group
        _ = a * (b * a₂) * b₂ * a₂⁻¹ * a⁻¹ * b₂⁻¹ * b⁻¹ := by rw [e1]
        _ = a * b * (a₂ * b₂) * a₂⁻¹ * a⁻¹ * b₂⁻¹ * b⁻¹ := by group
        _ = a * b * (b₂ * a₂) * a₂⁻¹ * a⁻¹ * b₂⁻¹ * b⁻¹ := by rw [e3]
        _ = a * b * b₂ * a⁻¹ * b₂⁻¹ * b⁻¹ := by group
        _ = a * b * a⁻¹ * (a * b₂ * a⁻¹) * b₂⁻¹ * b⁻¹ := by group
        _ = a * b * a⁻¹ * (b₂ * a * a⁻¹) * b₂⁻¹ * b⁻¹ := by rw [← e2]
        _ = a * b * a⁻¹ * b⁻¹ := by group
    rwa [h2] at h1
  have hE₂L : E₂ ≤ L := fun e₂ he₂ => by
    have hEK' : E ≤ K₂ ⊔ K₁ := sup_comm K₁ K₂ ▸ hEK
    obtain ⟨e₁, he₁, he⟩ := exists_mul_mem_of_mem_proj hc' hEK' he₂
    have h1 : e₁ ∈ L := hL₁L (hL₁ ▸ le_sup_left (a := E₁) he₁)
    have h2 := L.mul_mem (le_sup_left (a := E) he) (L.inv_mem h1)
    rwa [mul_inv_cancel_right] at h2
  exact sup_le hL₁L hE₂L

end Pair

section High

variable [Finite A] {k : Type} [Field k] [CharP k 2] [Finite k] {n : ℕ}

theorem paired_high
    (hk : Nat.card k = 2 ^ n) {θ₁ : K₁ ≃* SL(2, k)} {S B E : Subgroup A}
    (hSK₁ : S ⊓ K₁ = stdSub θ₁ (sl2UpperUnipotentSubgroup k))
    (hBK₁ : B ⊓ K₁ = stdSub θ₁ (sl2Borel k))
    (hE₁U : (E ⊔ K₂) ⊓ K₁ ≤ stdSub θ₁ (sl2UpperUnipotentSubgroup k))
    (hE₁4 : 4 ≤ Nat.card ↥((E ⊔ K₂) ⊓ K₁)) :
    ∃ (x₁ : A) (L₁ : Subgroup A), x₁ ∈ K₁ ∧
      L₁ = (E ⊔ K₂) ⊓ K₁ ⊔ conjugate ((E ⊔ K₂) ⊓ K₁) x₁ ∧ x₁ ∈ L₁ ∧ L₁ ≤ K₁ ∧
      IsSylowOf 2 (S ⊓ L₁) L₁ ∧ kerIn (B ⊓ L₁) L₁ = ⊥ ∧ inSubgroup (pCore 2) L₁ = ⊥ ∧
      inSubgroup (pCore 2) (B ⊓ L₁) = S ⊓ L₁ ∧
      ∃ f : ℕ, 2 ≤ f ∧ f ∣ n ∧ Nat.card ↥((E ⊔ K₂) ⊓ K₁) ≤ 2 ^ f ∧
        ∃ e : L₁ ≃* PSL2MatrixGroup (GaloisField 2 f),
          ((B ⊓ L₁).subgroupOf L₁).map e.toMonoidHom = psl2Borel (GaloisField 2 f) ∧
          ((S ⊓ L₁).subgroupOf L₁).map e.toMonoidHom =
            psl2UpperUnipotentSubgroup (GaloisField 2 f) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set E₁ := (E ⊔ K₂) ⊓ K₁ with hE₁def
  set Ū := sl2UpperUnipotentSubgroup k with hŪ
  have hE₁K : E₁ ≤ K₁ := inf_le_right
  have : IsElementaryAbelian 2 E₁ := isElementaryAbelian_of_le hE₁U
    (fun u hu v hv => stdSub_upperUnipotent_comm θ₁ hu hv)
    (fun u hu => stdSub_upperUnipotent_sq θ₁ hu)
  set U₁ : Subgroup K₁ := (S ⊓ K₁).subgroupOf K₁ with hU₁
  have hU₁' : U₁ = Ū.map θ₁.symm.toMonoidHom := by
    rw [hU₁, hSK₁, stdSub, ← comap_subtype, comap_map_eq_self_of_injective K₁.subtype_injective]
  have hD : BenderData K₁ U₁ n := by
    rw [hU₁']
    exact (benderData_sl2 hk).map θ₁.symm
  have hBK : B ⊓ K₁ = (normalizer (U₁ : Set K₁)).map K₁.subtype := by
    rw [hBK₁, hU₁', ← map_equiv_normalizer_eq, sl2_normalizer_upperUnipotent]
    rfl
  have hEU : E₁ ≤ S ⊓ K₁ := hSK₁ ▸ hE₁U
  have hab : ∀ u ∈ U₁, ∀ v ∈ U₁, u * v = v * u := by
    intro u hu v hv
    have hu' : (u : A) ∈ stdSub θ₁ Ū := hSK₁ ▸ (hu : (u : A) ∈ S ⊓ K₁)
    have hv' : (v : A) ∈ stdSub θ₁ Ū := hSK₁ ▸ (hv : (v : A) ∈ S ⊓ K₁)
    exact Subtype.ext (stdSub_upperUnipotent_comm θ₁ hu' hv')
  have : IsElementaryAbelian 2 (E₁.subgroupOf K₁) := IsElementaryAbelian.subgroupOf hE₁K
  have hE'U : E₁.subgroupOf K₁ ≤ U₁ := by
    rw [hU₁]
    exact fun y hy => hEU hy
  have hE'4 : 4 ≤ Nat.card (E₁.subgroupOf K₁) := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hE₁K).toEquiv]
  obtain ⟨x, hxN, -, hxL, hLeq, hLK, hSF, hcore, hO2, hO2P, hBL, hSL⟩ :=
    bender_pair_in_quotient hU₁ hD hBK hEU hE₁4
  have hmodel := bender_pair_linear hD hab hE'U hE'4 hxN
  generalize hL'def : E₁.subgroupOf K₁ ⊔ conjugate (E₁.subgroupOf K₁) x = L' at *
  obtain ⟨f, hf, hfn, hEf, e₁, he₁B, he₁U⟩ := hmodel
  refine ⟨x, L'.map K₁.subtype, x.2, hLeq, hxL, hLK, hSF, hcore, hO2, hO2P, f, hf, hfn, ?_,
    (L'.equivMapOfInjective K₁.subtype K₁.subtype_injective).symm.trans e₁, ?_, ?_⟩
  · rwa [← Nat.card_congr (subgroupOfEquivOfLe hE₁K).toEquiv]
  · rw [hBL, map_mulEquiv_trans, map_subgroupOf_equivMapOfInjective, he₁B]
  · rw [hSL, map_mulEquiv_trans, map_subgroupOf_equivMapOfInjective, he₁U]

end High

end CFSG.Quasithin.H13.QRC
