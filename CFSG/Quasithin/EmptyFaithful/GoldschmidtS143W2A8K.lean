module

public import CFSG.Quasithin.EmptyFaithful.S143UE

public section

namespace CFSG.Quasithin

open scoped MatrixGroups

namespace S143

namespace InspW2

theorem card_order_three_sl23 :
    (Finset.univ.filter fun x : SL(2, ZMod 3) => x ^ 3 = 1 ∧ x ≠ 1).card = 8 := by
  decide +kernel

theorem no_nine_order_three {P : Type*} [Group P] [Finite P] (hP : IsZ4StarSL23 P) (f : Fin 9 → P)
    (hf : Function.Injective f) (h3 : ∀ i, f i ^ 3 = 1 ∧ f i ≠ 1) : False := by
  obtain ⟨hcard, A, B, ⟨hAB, hsup⟩, hA4, -, ⟨eB⟩⟩ := hP
  have hB24 : Nat.card B = 24 := by
    rw [Nat.card_congr eB.toEquiv]
    exact SL23.card_sl3
  have hprod := card_sup_mul_card_inf_of_le_centralizer hAB
  rw [hsup, Subgroup.card_top, hcard, hA4, hB24] at hprod
  have hinf : Nat.card ↥(A ⊓ B) = 2 := by omega
  have hcomm : ∀ (a : A) (b : B), Commute (A.subtype a) (B.subtype b) := fun a b =>
    (Subgroup.mem_centralizer_iff.mp (hAB a.2) b b.2).symm
  let φ : A × B →* P := MonoidHom.noncommCoprod A.subtype B.subtype hcomm
  have hφ : φ.range = A ⊔ B := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  have hmem : ∀ g : P, g ^ 3 = 1 → g ∈ B := by
    intro g hg
    have hg' : g ∈ φ.range := by rw [hφ, hsup]; trivial
    obtain ⟨⟨a, b⟩, hab⟩ := hg'
    rw [MonoidHom.noncommCoprod_apply] at hab
    have hab' : (a : P) * (b : P) = g := hab
    have hc : Commute (a : P) (b : P) := hcomm a b
    have hg3 : (a : P) ^ 3 * (b : P) ^ 3 = 1 := by rw [← hc.mul_pow, hab', hg]
    have ha3B : (a : P) ^ 3 ∈ B := by
      have : (a : P) ^ 3 = ((b : P) ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left hg3
      rw [this]
      exact B.inv_mem (B.pow_mem b.2 3)
    have ha3 : (a : P) ^ 3 ∈ A ⊓ B := ⟨A.pow_mem a.2 3, ha3B⟩
    have h1 : (a : P) ^ 4 = 1 := by
      have := pow_card_eq_one' (x := a)
      rw [hA4] at this
      exact congrArg Subtype.val this
    have h2 : ((a : P) ^ 3) ^ 2 = 1 := by
      have := pow_card_eq_one' (x := (⟨(a : P) ^ 3, ha3⟩ : ↥(A ⊓ B)))
      rw [hinf] at this
      exact congrArg Subtype.val this
    have h3 : (a : P) ^ 2 = 1 := by
      calc (a : P) ^ 2 = (a : P) ^ 4 * (a : P) ^ 2 := by rw [h1, one_mul]
        _ = ((a : P) ^ 3) ^ 2 := by rw [← pow_add, ← pow_mul]
        _ = 1 := h2
    have haB : (a : P) ∈ B := by
      have : (a : P) = (a : P) ^ 3 := by
        calc (a : P) = (a : P) * (a : P) ^ 2 := by rw [h3, mul_one]
          _ = (a : P) ^ 3 := by rw [← pow_succ']
      rw [this]
      exact ha3.2
    rw [← hab']
    exact B.mul_mem haB b.2
  let f' : Fin 9 → B := fun i => ⟨f i, hmem _ (h3 i).1⟩
  have hf' : Function.Injective f' := fun i j h => hf (congrArg Subtype.val h)
  have hcount := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset (Fin 9)))
    (t := Finset.univ.filter fun x : SL(2, ZMod 3) => x ^ 3 = 1 ∧ x ≠ 1) (fun i => eB (f' i))
    (fun i _ => by
      simp only [Finset.coe_filter, Finset.mem_univ, true_and]
      refine ⟨?_, fun h => (h3 i).2 ?_⟩
      · rw [← map_pow]
        have : f' i ^ 3 = 1 := Subtype.ext (by simpa using (h3 i).1)
        rw [this, map_one]
      · have := eB.injective (h.trans (map_one eB).symm)
        exact congrArg Subtype.val this)
    (fun i _ j _ h => hf' (eB.injective h))
  rw [card_order_three_sl23] at hcount
  simp at hcount

theorem mem_of_pow_three {G : Type*} [Group G] {C K : Subgroup G} (hnorm : (K.subgroupOf C).Normal)
    (hidx : K.relIndex C = 4) {g : G} (hg : g ∈ C) (h3 : g ^ 3 = 1) : g ∈ K := by
  have : (K.subgroupOf C).Normal := hnorm
  have hQ : Nat.card (C ⧸ K.subgroupOf C) = 4 := hidx
  let x : C ⧸ K.subgroupOf C := QuotientGroup.mk ⟨g, hg⟩
  have h3' : x ^ 3 = 1 := by
    show (QuotientGroup.mk ⟨g, hg⟩ : C ⧸ K.subgroupOf C) ^ 3 = 1
    rw [← QuotientGroup.mk_pow]
    have : (⟨g, hg⟩ : C) ^ 3 = 1 := Subtype.ext h3
    rw [this, QuotientGroup.mk_one]
  have h4' : x ^ 4 = 1 := by
    have := pow_card_eq_one' (x := x)
    rwa [hQ] at this
  have hx : x = 1 := by
    calc x = x ^ 4 * (x ^ 3)⁻¹ := by group
      _ = 1 := by rw [h4', h3']; simp
  exact (QuotientGroup.eq_one_iff (⟨g, hg⟩ : C)).mp hx

end InspW2

end S143

end CFSG.Quasithin
