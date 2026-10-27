module

public import CFSG.Quasithin.EmptyFaithful.S153YT3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245Single
public import CFSG.Quasithin.EmptyFaithful.S153WJOff

public section

namespace CFSG.Quasithin.YG

open scoped Pointwise commutatorElement
open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.Quasithin.W153

variable {G : Type} [Group G] {I S K₀ K₁ : Subgroup G}

namespace A3Pair

variable [Finite G] (c : A3Pair I S K₀ K₁)
include c

theorem four_mul_card_le {a : G} (h : B6.conjSub a K₁ = K₀) {W : Subgroup G} (hW₁ : blockU K₁ ≤ W)
    (hW : W ≤ blockU K₀ ⊔ blockU K₁) :
    4 * Nat.card ↥(W ⊓ Subgroup.centralizer ({a} : Set G)) ≤ Nat.card W := by
  set C := W ⊓ Subgroup.centralizer ({a} : Set G) with hC
  have hUe := c.isElemAbelian_blockU_sup
  have hcomm : ∀ x ∈ blockU K₁, ∀ y ∈ C, x * y = y * x := fun x hx y hy =>
    B2F.isElemAbelian_comm hUe (Subgroup.mem_sup_right hx) (hW hy.1)
  have hinf : blockU K₁ ⊓ C = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
    have hax : a * x = x * a := Subgroup.mem_centralizer_iff.1 hx.2.2 a (Set.mem_singleton a)
    have hx₀ : x ∈ blockU K₀ := by
      have := mem_blockU_conj_of_conjSub_eq h hx.1
      have e : a * x * a⁻¹ = x := by rw [hax]; group
      rwa [e] at this
    have : x ∈ blockU K₀ ⊓ blockU K₁ := ⟨hx₀, hx.1⟩
    rw [c.blockU_inf] at this
    exact this
  have h1 := B2F.card_sup_mul_card_inf_of_commute hcomm
  rw [hinf, Subgroup.card_bot, mul_one, c.card_blockU₁] at h1
  have h2 : Nat.card ↥(blockU K₁ ⊔ C) ≤ Nat.card W :=
    Subgroup.card_le_of_le (sup_le hW₁ inf_le_left)
  omega

theorem card_le_two_mul_normalizer {A : Subgroup G} (hA : IsMaxElemAbelian S A) {a : G} (haA : a ∈ A)
    (hn : a ∉ Subgroup.normalizer (K₀ : Set G)) :
    Nat.card A ≤ 2 * Nat.card ↥(A ⊓ Subgroup.normalizer (K₀ : Set G)) := by
  have haS : a ∈ S := hA.1 haA
  have hconj₁ : B6.conjSub a K₀ = K₁ := c.conjSub_eq₁_of_not_mem haS hn
  have ha2 : a * a = 1 := by
    have := hA.2.1.2 a haA
    rwa [pow_two] at this
  have haInv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hconj₂ : B6.conjSub a K₁ = K₀ := by
    rw [← hconj₁, ← B6.conjSub_mul, ha2, B6.conjSub_one]
  have hcommA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    B2F.isElemAbelian_comm hA.2.1 hx hy
  refine card_le_two_mul_of_forall inf_le_left hcommA haA ha2 fun x hx => ?_
  by_cases hxN : x ∈ Subgroup.normalizer (K₀ : Set G)
  · exact Or.inl ⟨hx, hxN⟩
  · right
    refine ⟨A.mul_mem (A.inv_mem haA) hx, ?_⟩
    have hx' := c.conjSub_eq₁_of_not_mem (hA.1 hx) hxN
    apply ModF.mem_normalizer_of_conjSub_eq
    rw [B6.conjSub_mul, hx', haInv, hconj₂]

theorem inf_centralizer_le {A : Subgroup G} (hA : IsMaxElemAbelian S A) {a : G} (haA : a ∈ A)
    (hn : a ∉ Subgroup.normalizer (K₀ : Set G)) :
    (A ⊓ Subgroup.normalizer (K₀ : Set G)) ⊓ Subgroup.centralizer (blockU K₀ : Set G) ≤
      A ⊓ Subgroup.centralizer ((blockU K₀ ⊔ blockU K₁ : Subgroup G) : Set G) := by
  have haS : a ∈ S := hA.1 haA
  have hconj₁ : B6.conjSub a K₀ = K₁ := c.conjSub_eq₁_of_not_mem haS hn
  have ha2 : a * a = 1 := by
    have := hA.2.1.2 a haA
    rwa [pow_two] at this
  have haInv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hconj₂ : B6.conjSub a K₁ = K₀ := by
    rw [← hconj₁, ← B6.conjSub_mul, ha2, B6.conjSub_one]
  intro x hx
  refine ⟨hx.1.1, ?_⟩
  have hxa : Commute x a := B2F.isElemAbelian_comm hA.2.1 hx.1.1 haA
  have hxU₀ : ∀ u ∈ blockU K₀, x * u = u * x := fun u hu =>
    (Subgroup.mem_centralizer_iff.1 hx.2 u hu).symm
  have hxU₁ : ∀ u ∈ blockU K₁, x * u = u * x := by
    intro u hu
    have hw : a * u * a⁻¹ ∈ blockU K₀ := mem_blockU_conj_of_conjSub_eq hconj₂ hu
    have hu' : u = a * (a * u * a⁻¹) * a⁻¹ := by
      calc u = (a * a) * u * (a * a) := by rw [ha2]; simp
        _ = a * (a * u * a) * a := by group
        _ = a * (a * u * a⁻¹) * a⁻¹ := by rw [haInv]
    have hxw : Commute x (a * u * a⁻¹) := hxU₀ _ hw
    rw [hu']
    exact ((hxa.mul_right hxw).mul_right hxa.inv_right).eq
  refine Subgroup.mem_centralizer_iff.2 fun u hu => ?_
  obtain ⟨u₀, hu₀, u₁, hu₁, rfl⟩ := c.exists_mul_of_mem_blockU_sup hu
  have hx₀ : Commute x u₀ := hxU₀ u₀ hu₀
  have hx₁ : Commute x u₁ := hxU₁ u₁ hu₁
  exact (hx₀.mul_right hx₁).eq.symm

omit [Finite G] c in
theorem inf_blockU_sup_le {A : Subgroup G} (hA : IsMaxElemAbelian S A) {a : G} (haA : a ∈ A) :
    A ⊓ (blockU K₀ ⊔ blockU K₁) ≤
      (blockU K₀ ⊔ blockU K₁) ⊓ Subgroup.centralizer ({a} : Set G) := fun x hx =>
  ⟨hx.2, Subgroup.mem_centralizer_iff.2 fun y hy => by
    rw [Set.mem_singleton_iff.1 hy]
    exact B2F.isElemAbelian_comm hA.2.1 haA hx.1⟩

theorem card_inf_blockU_le_two {A : Subgroup G} (hA : IsMaxElemAbelian S A) {a : G} (haA : a ∈ A)
    (hn : a ∉ Subgroup.normalizer (K₀ : Set G)) {b : G} (hbA : b ∈ A)
    (hbN : b ∈ Subgroup.normalizer (K₀ : Set G)) {z : G} (hzU : z ∈ blockU K₀) (hz1 : z ≠ 1)
    (hz : ∀ u ∈ blockU K₀, u ∈ Subgroup.zpowers z ↔ u * b = b * u) :
    Nat.card ↥(A ⊓ (blockU K₀ ⊔ blockU K₁)) ≤ 2 := by
  have haS : a ∈ S := hA.1 haA
  have hconj₁ : B6.conjSub a K₀ = K₁ := c.conjSub_eq₁_of_not_mem haS hn
  have ha2 : a * a = 1 := by
    have := hA.2.1.2 a haA
    rwa [pow_two] at this
  have hconj₂ : B6.conjSub a K₁ = K₀ := by
    rw [← hconj₁, ← B6.conjSub_mul, ha2, B6.conjSub_one]
  have hbN₁ : b ∈ Subgroup.normalizer (K₁ : Set G) := c.mem_normalizer₁_of_mem (hA.1 hbA) hbN
  have hzle : Subgroup.zpowers z ≤ blockU K₀ := Subgroup.zpowers_le.2 hzU
  set W : Subgroup G := Subgroup.zpowers z ⊔ blockU K₁ with hWdef
  have hW₁ : blockU K₁ ≤ W := le_sup_right
  have hWU : W ≤ blockU K₀ ⊔ blockU K₁ := sup_le (hzle.trans le_sup_left) le_sup_right
  have hsub : A ⊓ (blockU K₀ ⊔ blockU K₁) ≤ W ⊓ Subgroup.centralizer ({a} : Set G) := by
    intro u hu
    refine ⟨?_, (inf_blockU_sup_le (K₀ := K₀) (K₁ := K₁) hA haA hu).2⟩
    obtain ⟨u₀, hu₀, u₁, hu₁, rfl⟩ := c.exists_mul_of_mem_blockU_sup hu.2
    have hbu : b * (u₀ * u₁) = (u₀ * u₁) * b := B2F.isElemAbelian_comm hA.2.1 hbA hu.1
    have hv₀ : b * u₀ * b⁻¹ ∈ blockU K₀ :=
      (Subgroup.mem_normalizer_iff.1 (C1.mem_normalizer_blockU hbN) u₀).1 hu₀
    have hv₁ : b * u₁ * b⁻¹ ∈ blockU K₁ :=
      (Subgroup.mem_normalizer_iff.1 (C1.mem_normalizer_blockU hbN₁) u₁).1 hu₁
    have heq : (b * u₀ * b⁻¹) * (b * u₁ * b⁻¹) = u₀ * u₁ := by
      calc (b * u₀ * b⁻¹) * (b * u₁ * b⁻¹) = b * (u₀ * u₁) * b⁻¹ := by group
        _ = u₀ * u₁ := by rw [hbu]; group
    have hkey : u₀⁻¹ * (b * u₀ * b⁻¹) = u₁ * (b * u₁ * b⁻¹)⁻¹ := by
      calc u₀⁻¹ * (b * u₀ * b⁻¹)
          = u₀⁻¹ * ((b * u₀ * b⁻¹) * (b * u₁ * b⁻¹)) * (b * u₁ * b⁻¹)⁻¹ := by group
        _ = u₁ * (b * u₁ * b⁻¹)⁻¹ := by rw [heq]; group
    have hin : u₀⁻¹ * (b * u₀ * b⁻¹) ∈ blockU K₀ ⊓ blockU K₁ := by
      refine ⟨(blockU K₀).mul_mem ((blockU K₀).inv_mem hu₀) hv₀, ?_⟩
      rw [hkey]
      exact (blockU K₁).mul_mem hu₁ ((blockU K₁).inv_mem hv₁)
    rw [c.blockU_inf, Subgroup.mem_bot] at hin
    have hcu : u₀ * b = b * u₀ := by
      have h1 : b * u₀ * b⁻¹ = u₀ := by
        calc b * u₀ * b⁻¹ = u₀ * (u₀⁻¹ * (b * u₀ * b⁻¹)) := by group
          _ = u₀ := by rw [hin, mul_one]
      calc u₀ * b = (b * u₀ * b⁻¹) * b := by rw [h1]
        _ = b * u₀ := by group
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ((hz u₀ hu₀).2 hcu)) (Subgroup.mem_sup_right hu₁)
  have h4 := c.four_mul_card_le hconj₂ hW₁ hWU
  have h8 : Nat.card ↥W ≤ 8 := by
    have hc : ∀ x ∈ Subgroup.zpowers z, ∀ y ∈ blockU K₁, x * y = y * x := fun x hx y hy =>
      c.comm x (c.U₀_le (hzle hx)) y (c.U₁_le hy)
    have h1 : Nat.card ↥W * Nat.card ↥(Subgroup.zpowers z ⊓ blockU K₁) =
        Nat.card ↥(Subgroup.zpowers z) * Nat.card ↥(blockU K₁) :=
      B2F.card_sup_mul_card_inf_of_commute hc
    have hz2 : z ^ 2 = 1 := c.a4₀.sq_U z hzU
    have hcz : Nat.card ↥(Subgroup.zpowers z) = 2 := by
      rw [Nat.card_zpowers, orderOf_eq_prime hz2 hz1]
    rw [hcz, c.card_blockU₁] at h1
    have hpos : 0 < Nat.card ↥(Subgroup.zpowers z ⊓ blockU K₁) := Nat.card_pos
    calc Nat.card ↥W ≤ Nat.card ↥W * Nat.card ↥(Subgroup.zpowers z ⊓ blockU K₁) :=
          Nat.le_mul_of_pos_right _ hpos
      _ = 8 := by rw [h1]
  have hle := Subgroup.card_le_of_le hsub
  omega

theorem isMaxElemAbelian_le_normalizer {A : Subgroup G} (hA : IsMaxElemAbelian S A) :
    A ≤ Subgroup.normalizer (K₀ : Set G) := by
  intro a haA
  by_contra hn
  have haS : a ∈ S := hA.1 haA
  have hconj₁ : B6.conjSub a K₀ = K₁ := c.conjSub_eq₁_of_not_mem haS hn
  have ha2 : a * a = 1 := by
    have := hA.2.1.2 a haA
    rwa [pow_two] at this
  have hconj₂ : B6.conjSub a K₁ = K₀ := by
    rw [← hconj₁, ← B6.conjSub_mul, ha2, B6.conjSub_one]
  have hcommA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    B2F.isElemAbelian_comm hA.2.1 hx hy
  have hi := card_mul_le_of_isMaxElemAbelian hA c.isElemAbelian_blockU_sup c.blockU_sup_le_S
  rw [c.card_blockU_sup] at hi
  have hp : 0 < Nat.card ↥(A ⊓ Subgroup.centralizer
      ((blockU K₀ ⊔ blockU K₁ : Subgroup G) : Set G)) := Nat.card_pos
  have h2 := c.card_le_two_mul_normalizer hA haA hn
  by_cases hcase :
      A ⊓ Subgroup.normalizer (K₀ : Set G) ≤ Subgroup.centralizer (blockU K₀ : Set G)
  ·
    have hle : A ⊓ Subgroup.normalizer (K₀ : Set G) ≤
        A ⊓ Subgroup.centralizer ((blockU K₀ ⊔ blockU K₁ : Subgroup G) : Set G) := fun x hx =>
      c.inf_centralizer_le hA haA hn ⟨hx, hcase hx⟩
    have h3 := Subgroup.card_le_of_le hle
    have h4 := c.four_mul_card_le hconj₂ (W := blockU K₀ ⊔ blockU K₁) le_sup_right le_rfl
    rw [c.card_blockU_sup] at h4
    have h5 := Subgroup.card_le_of_le (inf_blockU_sup_le (K₀ := K₀) (K₁ := K₁) hA haA)
    have h6 : Nat.card ↥(A ⊓ (blockU K₀ ⊔ blockU K₁)) ≤ 4 := by omega
    have h7 := Nat.mul_le_mul
      (show Nat.card A ≤ 2 * Nat.card ↥(A ⊓ Subgroup.centralizer
        ((blockU K₀ ⊔ blockU K₁ : Subgroup G) : Set G)) by omega) h6
    nlinarith
  ·
    obtain ⟨b, hbA₀, hbC⟩ := IsConcreteLE.not_le_iff_exists.1 hcase
    have hbA : b ∈ A := hbA₀.1
    have hbN : b ∈ Subgroup.normalizer (K₀ : Set G) := hbA₀.2
    have hA₀S : A ⊓ Subgroup.normalizer (K₀ : Set G) ≤ S := inf_le_left.trans hA.1
    have hBS : (A ⊓ Subgroup.normalizer (K₀ : Set G)) ⊔ blockU K₀ ≤ S := sup_le hA₀S c.U₀_le_S
    have hBN : (A ⊓ Subgroup.normalizer (K₀ : Set G)) ⊔ blockU K₀ ≤
        Subgroup.normalizer (blockU K₀ : Set G) :=
      sup_le (fun g hg => C1.mem_normalizer_blockU hg.2) Subgroup.le_normalizer
    have hnt : ¬ (A ⊓ Subgroup.normalizer (K₀ : Set G)) ⊔ blockU K₀ ≤
        Subgroup.centralizer (blockU K₀ : Set G) := fun h => hbC (h (Subgroup.mem_sup_left hbA₀))
    obtain ⟨z, hzU, hz1, hrel, -, -, hcenty⟩ :=
      klein_structure c.card_blockU₀ c.a4₀.sq_U le_sup_right hBN (c.sylow.isPGroup.to_le hBS) hnt
    have hbB : b ∈ (A ⊓ Subgroup.normalizer (K₀ : Set G)) ⊔ blockU K₀ :=
      Subgroup.mem_sup_left hbA₀
    have hbnC : b ∉ ((A ⊓ Subgroup.normalizer (K₀ : Set G)) ⊔ blockU K₀) ⊓
        Subgroup.centralizer (blockU K₀ : Set G) := fun h => hbC h.2
    have hforall : ∀ x ∈ A ⊓ Subgroup.normalizer (K₀ : Set G),
        x ∈ (A ⊓ Subgroup.normalizer (K₀ : Set G)) ⊓ Subgroup.centralizer (blockU K₀ : Set G) ∨
          b⁻¹ * x ∈ (A ⊓ Subgroup.normalizer (K₀ : Set G)) ⊓
            Subgroup.centralizer (blockU K₀ : Set G) := by
      intro x hx
      rcases mem_or_inv_mul_mem_of_relIndex_two hrel hbB hbnC (Subgroup.mem_sup_left hx) with h | h
      · exact Or.inl ⟨hx, h.2⟩
      · exact Or.inr ⟨(A ⊓ Subgroup.normalizer (K₀ : Set G)).mul_mem
          ((A ⊓ Subgroup.normalizer (K₀ : Set G)).inv_mem hbA₀) hx, h.2⟩
    have hb2 : b * b = 1 := by
      have := hA.2.1.2 b hbA
      rwa [pow_two] at this
    have h3 : Nat.card ↥(A ⊓ Subgroup.normalizer (K₀ : Set G)) ≤
        2 * Nat.card ↥((A ⊓ Subgroup.normalizer (K₀ : Set G)) ⊓
          Subgroup.centralizer (blockU K₀ : Set G)) :=
      card_le_two_mul_of_forall inf_le_left (fun x hx y hy => hcommA x hx.1 y hy.1) hbA₀ hb2 hforall
    have hle : (A ⊓ Subgroup.normalizer (K₀ : Set G)) ⊓ Subgroup.centralizer (blockU K₀ : Set G) ≤
        A ⊓ Subgroup.centralizer ((blockU K₀ ⊔ blockU K₁ : Subgroup G) : Set G) :=
      c.inf_centralizer_le hA haA hn
    have h4 := Subgroup.card_le_of_le hle
    have h6 := c.card_inf_blockU_le_two hA haA hn hbA hbN hzU hz1
      (fun u hu => hcenty b hbB hbC u hu)
    have h7 := Nat.mul_le_mul
      (show Nat.card A ≤ 4 * Nat.card ↥(A ⊓ Subgroup.centralizer
        ((blockU K₀ ⊔ blockU K₁ : Subgroup G) : Set G)) by omega) h6
    nlinarith

theorem thompsonJ_le_normalizer : thompsonJ S ≤ Subgroup.normalizer (K₀ : Set G) :=
  GammaExtra.thompsonJ_le fun _ hA => c.isMaxElemAbelian_le_normalizer hA

end A3Pair

end CFSG.Quasithin.YG
