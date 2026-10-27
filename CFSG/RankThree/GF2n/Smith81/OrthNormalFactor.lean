module

public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.Subgroup.Simple

public section

namespace CFSG.RankThree.GF2n.Smith81

structure IsInternalProd {H : Type*} [Group H] (H₁ H₂ : Subgroup H) : Prop where
  normal₁ : H₁.Normal
  normal₂ : H₂.Normal
  inf_eq : H₁ ⊓ H₂ = ⊥
  sup_eq : H₁ ⊔ H₂ = ⊤

variable {H : Type*} [Group H]

theorem commute_of_normal_inf_eq_bot {A B : Subgroup H} [nA : A.Normal] [nB : B.Normal]
    (hAB : A ⊓ B = ⊥) {a b : H} (ha : a ∈ A) (hb : b ∈ B) : a * b = b * a := by
  have hcA : a⁻¹ * b⁻¹ * a * b ∈ A := by
    have h1 := nA.conj_mem a ha b⁻¹
    rw [inv_inv] at h1
    have h2 := A.mul_mem (A.inv_mem ha) h1
    simpa only [mul_assoc] using h2
  have hcB : a⁻¹ * b⁻¹ * a * b ∈ B := by
    have h1 := nB.conj_mem b⁻¹ (B.inv_mem hb) a⁻¹
    rw [inv_inv] at h1
    exact B.mul_mem h1 hb
  have hc : a⁻¹ * b⁻¹ * a * b = 1 := by
    have hmem : a⁻¹ * b⁻¹ * a * b ∈ A ⊓ B := Subgroup.mem_inf.mpr ⟨hcA, hcB⟩
    rw [hAB, Subgroup.mem_bot] at hmem
    exact hmem
  have h4 : (b * a)⁻¹ * (a * b) = 1 := by
    simpa only [mul_inv_rev, mul_assoc] using hc
  exact (inv_mul_eq_one.mp h4).symm

namespace IsInternalProd

variable {H₁ H₂ : Subgroup H}

theorem commute (h : IsInternalProd H₁ H₂) {a b : H} (ha : a ∈ H₁) (hb : b ∈ H₂) :
    a * b = b * a := by
  have := h.normal₁
  have := h.normal₂
  exact commute_of_normal_inf_eq_bot h.inf_eq ha hb

theorem centralizer_eq (h : IsInternalProd H₁ H₂)
    (hZ : ∀ b ∈ H₂, (∀ c ∈ H₂, b * c = c * b) → b = 1) :
    Subgroup.centralizer (H₂ : Set H) = H₁ := by
  have := h.normal₁
  ext x
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro hx
    have hx' : x ∈ H₁ ⊔ H₂ := by
      rw [h.sup_eq]
      exact Subgroup.mem_top x
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hx'
    have key : ∀ c ∈ H₂, c * b = b * c := by
      intro c hc
      have h1 : c * (a * b) = a * b * c := hx c hc
      have h2 : a * c = c * a := h.commute ha hc
      have h3 : a * (c * b) = a * (b * c) :=
        calc a * (c * b) = a * c * b := (mul_assoc a c b).symm
          _ = c * a * b := by rw [h2]
          _ = c * (a * b) := mul_assoc c a b
          _ = a * b * c := h1
          _ = a * (b * c) := mul_assoc a b c
      exact mul_left_cancel h3
    have hb1 : b = 1 := hZ b hb (fun c hc => (key c hc).symm)
    rw [hb1, mul_one]
    exact ha
  · intro hx c hc
    exact (h.commute hx hc).symm

theorem le_left_of_inf_eq_bot (h : IsInternalProd H₁ H₂)
    (hZ : ∀ b ∈ H₂, (∀ c ∈ H₂, b * c = c * b) → b = 1) {N : Subgroup H} [N.Normal]
    (hbot : N ⊓ H₂ = ⊥) : N ≤ H₁ := by
  have := h.normal₂
  have hcen : N ≤ Subgroup.centralizer (H₂ : Set H) := by
    intro n hn
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact (commute_of_normal_inf_eq_bot hbot hn hc).symm
  rw [h.centralizer_eq hZ] at hcen
  exact hcen

theorem normal_eq_left [Finite H] (h : IsInternalProd H₁ H₂)
    (hs : ∀ N : Subgroup H, N.Normal → N ≤ H₂ → N = ⊥ ∨ N = H₂)
    (hZ : ∀ b ∈ H₂, (∀ c ∈ H₂, b * c = c * b) → b = 1)
    (hlt : Nat.card H₁ < Nat.card H₂) {N : Subgroup H} (hN : N.Normal)
    (hcard : Nat.card N = Nat.card H₁) : N = H₁ := by
  have := h.normal₂
  rcases hs (N ⊓ H₂) inferInstance inf_le_right with hbot | htop
  · exact Subgroup.eq_of_le_of_card_ge (h.le_left_of_inf_eq_bot hZ hbot) hcard.ge
  · exfalso
    have hle : H₂ ≤ N := by
      have hsub : N ⊓ H₂ ≤ N := inf_le_left
      rwa [htop] at hsub
    have hcardle : Nat.card H₂ ≤ Nat.card N := Subgroup.card_le_of_le hle
    omega

end IsInternalProd

section Product

theorem ker_snd_eq_range_inl (A B : Type*) [Group A] [Group B] :
    (MonoidHom.snd A B).ker = (MonoidHom.inl A B).range := by
  ext ⟨a, b⟩
  rw [MonoidHom.mem_ker, MonoidHom.mem_range]
  constructor
  · intro hb
    have hb' : b = 1 := hb
    exact ⟨a, Prod.ext rfl hb'.symm⟩
  · rintro ⟨c, hc⟩
    have hb : (1 : B) = b := congrArg Prod.snd hc
    exact hb.symm

theorem ker_fst_eq_range_inr (A B : Type*) [Group A] [Group B] :
    (MonoidHom.fst A B).ker = (MonoidHom.inr A B).range := by
  ext ⟨a, b⟩
  rw [MonoidHom.mem_ker, MonoidHom.mem_range]
  constructor
  · intro ha
    have ha' : a = 1 := ha
    exact ⟨b, Prod.ext ha'.symm rfl⟩
  · rintro ⟨c, hc⟩
    have ha : (1 : A) = a := congrArg Prod.fst hc
    exact ha.symm

theorem card_range_inl (A B : Type*) [Group A] [Group B] :
    Nat.card (MonoidHom.inl A B).range = Nat.card A := by
  have hinj : Function.Injective (MonoidHom.inl A B) := by
    intro a b h
    exact congrArg Prod.fst h
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem card_range_inr (A B : Type*) [Group A] [Group B] :
    Nat.card (MonoidHom.inr A B).range = Nat.card B := by
  have hinj : Function.Injective (MonoidHom.inr A B) := by
    intro a b h
    exact congrArg Prod.snd h
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem isInternalProd_range_inl_inr (A B : Type*) [Group A] [Group B] :
    IsInternalProd (MonoidHom.inl A B).range (MonoidHom.inr A B).range where
  normal₁ := by
    rw [← ker_snd_eq_range_inl A B]
    infer_instance
  normal₂ := by
    rw [← ker_fst_eq_range_inr A B]
    infer_instance
  inf_eq := by
    rw [eq_bot_iff]
    rintro x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hx1
    obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp hx2
    have ha : (1 : A) = a := congrArg Prod.fst hb
    have hb1 : b = 1 := congrArg Prod.snd hb
    rw [Subgroup.mem_bot]
    subst ha
    subst hb1
    simp
  sup_eq := by
    rw [eq_top_iff]
    rintro ⟨a, b⟩ -
    have hab : ((a, b) : A × B) = MonoidHom.inl A B a * MonoidHom.inr A B b := by
      simp
    rw [hab]
    exact Subgroup.mul_mem_sup (MonoidHom.mem_range.mpr ⟨a, rfl⟩)
      (MonoidHom.mem_range.mpr ⟨b, rfl⟩)

theorem eq_bot_or_eq_range_inr (A B : Type*) [Group A] [Group B] [IsSimpleGroup B]
    {N : Subgroup (A × B)} (hN : N.Normal) (hle : N ≤ (MonoidHom.inr A B).range) :
    N = ⊥ ∨ N = (MonoidHom.inr A B).range := by
  have hK : (N.comap (MonoidHom.inr A B)).Normal := by
    refine ⟨fun k hk g => ?_⟩
    rw [Subgroup.mem_comap] at hk ⊢
    have h1 := hN.conj_mem _ hk (MonoidHom.inr A B g)
    simpa using h1
  have hmap := Subgroup.map_comap_eq_self hle
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.comap (MonoidHom.inr A B)) with h0 | h1
  · left
    rw [h0, Subgroup.map_bot] at hmap
    exact hmap.symm
  · right
    rw [h1] at hmap
    rw [MonoidHom.range_eq_map]
    exact hmap.symm

theorem eq_one_of_mem_centralizer_range_inr (A B : Type*) [Group A] [Group B] [IsSimpleGroup B]
    (hB : ∃ b c : B, b * c ≠ c * b) {b : A × B} (hb : b ∈ (MonoidHom.inr A B).range)
    (hcomm : ∀ c ∈ (MonoidHom.inr A B).range, b * c = c * b) : b = 1 := by
  have hinj : Function.Injective (MonoidHom.inr A B) := by
    intro a₁ a₂ h
    exact congrArg Prod.snd h
  obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hb
  have hcen : y ∈ Subgroup.center B := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 := hcomm (MonoidHom.inr A B g) (MonoidHom.mem_range.mpr ⟨g, rfl⟩)
    have h2 : (MonoidHom.inr A B) (g * y) = (MonoidHom.inr A B) (y * g) := by
      rw [map_mul, map_mul]
      exact h1.symm
    exact hinj h2
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center B) with h0 | h1
  · rw [h0, Subgroup.mem_bot] at hcen
    rw [hcen, map_one]
  · exfalso
    obtain ⟨b, c, hbc⟩ := hB
    have hbz : b ∈ Subgroup.center B := by
      rw [h1]
      exact Subgroup.mem_top b
    rw [Subgroup.mem_center_iff] at hbz
    exact hbc (hbz c).symm

theorem normal_eq_range_inl {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    [IsSimpleGroup B] (hB : ∃ b c : B, b * c ≠ c * b) (hlt : Nat.card A < Nat.card B)
    {N : Subgroup (A × B)} (hN : N.Normal) (hcard : Nat.card N = Nat.card A) :
    N = (MonoidHom.inl A B).range := by
  have hI : IsInternalProd (MonoidHom.inl A B).range (MonoidHom.inr A B).range :=
    isInternalProd_range_inl_inr A B
  have hlt' : Nat.card (MonoidHom.inl A B).range < Nat.card (MonoidHom.inr A B).range := by
    rw [card_range_inl, card_range_inr]
    exact hlt
  refine hI.normal_eq_left (fun N' hN' hle => eq_bot_or_eq_range_inr A B hN' hle)
    (fun b hb hcomm => eq_one_of_mem_centralizer_range_inr A B hB hb hcomm) hlt' hN ?_
  rw [card_range_inl]
  exact hcard

end Product

end CFSG.RankThree.GF2n.Smith81
