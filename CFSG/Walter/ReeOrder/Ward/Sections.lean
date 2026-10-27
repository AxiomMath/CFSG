module

public import CFSG.Walter.ReeOrder.Ward.Setup
public import CFSG.CharacterTheory.PSL2Table.DirectProduct

public section

open scoped BigOperators Classical

namespace CFSG.Walter.Ward

open CFSG.SmallDefect CFSG.BlockSectionOrthogonality.Helpers CFSG.DirectProduct
open CFSG.PSL2Table

namespace WardSetup

variable {G : Type} [Group G] [Fintype G] {L : Type} [Group L] [Fintype L] {q : ℕ} {e : ℤ}
  {IV : Bool} (S : WardSetup G L q e IV)

theorem commute_zpowers (z : Subgroup.zpowers S.J) (y : L) : Commute (z : G) (S.κ y) := by
  obtain ⟨k, hk⟩ := z.2
  rw [← hk]
  exact Commute.zpow_left (S.κ_comm' y) k

@[expose] noncomputable def ι : Subgroup.zpowers S.J × L →* G :=
  MonoidHom.noncommCoprod (Subgroup.zpowers S.J).subtype S.κ S.commute_zpowers

theorem ι_apply (z : Subgroup.zpowers S.J) (y : L) : S.ι (z, y) = (z : G) * S.κ y := rfl

@[expose] def Jz : Subgroup.zpowers S.J := ⟨S.J, Subgroup.mem_zpowers _⟩

theorem card_Z : Nat.card (Subgroup.zpowers S.J) = 2 := by
  rw [Nat.card_zpowers, S.orderOf_J]

theorem one_ne_Jz : (1 : Subgroup.zpowers S.J) ≠ S.Jz := by
  intro h
  apply S.J_ne
  have := congrArg Subtype.val h
  exact this.symm

theorem Z_cases (z : Subgroup.zpowers S.J) : z = 1 ∨ z = S.Jz := by
  by_cases hz : z = 1
  · exact Or.inl hz
  · exact Or.inr (eq_of_ne_one_of_card_two S.card_Z hz (Ne.symm S.one_ne_Jz))

theorem sum_Z {M : Type*} [AddCommMonoid M] (f : Subgroup.zpowers S.J → M) :
    ∑ z, f z = f 1 + f S.Jz := by
  have huniv : (Finset.univ : Finset (Subgroup.zpowers S.J)) = {1, S.Jz} := by
    ext z
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact S.Z_cases z
  rw [huniv, Finset.sum_pair S.one_ne_Jz]

theorem signChar_Jz : signChar (Subgroup.zpowers S.J) S.Jz = -1 := by
  simp [signChar, (Ne.symm S.one_ne_Jz)]

@[expose] def σ (χ : G → ℂ) : L → ℂ := fun y => χ (S.J * S.κ y)

@[expose] def τ (χ : G → ℂ) : L → ℂ := fun y => χ (S.κ y)

theorem commJ (y : L) : Commute S.J (S.κ y) := S.κ_comm' y

theorem σ_class {χ : G → ℂ} (hχ : BlocksIsClassFunction χ) : BlocksIsClassFunction (S.σ χ) := by
  intro y g
  simp only [σ, map_mul, map_inv]
  have h : S.J * (S.κ g * S.κ y * (S.κ g)⁻¹) = S.κ g * (S.J * S.κ y) * (S.κ g)⁻¹ := by
    rw [← mul_assoc, ← mul_assoc, S.κ_comm' g]
    group
  rw [h, hχ]

theorem τ_class {χ : G → ℂ} (hχ : BlocksIsClassFunction χ) : BlocksIsClassFunction (S.τ χ) := by
  intro y g
  simp only [τ, map_mul, map_inv]
  exact hχ (S.κ y) (S.κ g)

theorem card_prod : Nat.card (Subgroup.zpowers S.J × L) = 2 * Nat.card L := by
  rw [Nat.card_prod, S.card_Z]

theorem inner_ι (f : G → ℂ) (ε : Subgroup.zpowers S.J → ℂ) (hε : ε 1 = 1) (θ : L → ℂ) :
    BlocksInnerProduct (f ∘ S.ι) (outerProductCharacter ε θ) =
      (BlocksInnerProduct (S.τ f) θ + starRingEnd ℂ (ε S.Jz) * BlocksInnerProduct (S.σ f) θ) /
        2 := by
  unfold BlocksInnerProduct
  rw [S.card_prod, Fintype.sum_prod_type, S.sum_Z]
  simp only [Function.comp_apply, ι_apply, outerProductCharacter_apply, OneMemClass.coe_one,
    one_mul, hε, map_mul, τ, σ, Jz]
  have hL : (Nat.card L : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  push_cast
  field_simp
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  ring

theorem mult {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) {θ : L → ℂ} (hθ : θ ∈ BlocksIrr L) :
    ∃ a b : ℕ, BlocksInnerProduct (S.τ χ) θ = a + b ∧
      BlocksInnerProduct (S.σ χ) θ = (a : ℂ) - b := by
  have h1 : outerProductCharacter (1 : Subgroup.zpowers S.J → ℂ) θ ∈
      BlocksIrr (Subgroup.zpowers S.J × L) :=
    outerProductCharacter_mem_blocksIrr (one_mem_blocksIrr _) hθ
  have h2 : outerProductCharacter (signChar (Subgroup.zpowers S.J)) θ ∈
      BlocksIrr (Subgroup.zpowers S.J × L) :=
    outerProductCharacter_mem_blocksIrr (signChar_mem_blocksIrr S.card_Z) hθ
  obtain ⟨a, ha⟩ := exists_natCast_restrict S.ι hχ h1
  obtain ⟨b, hb⟩ := exists_natCast_restrict S.ι hχ h2
  rw [S.inner_ι χ 1 rfl θ] at ha
  rw [S.inner_ι χ _ (by simp [signChar]) θ, S.signChar_Jz] at hb
  simp only [Pi.one_apply, map_one, one_mul, map_neg, neg_mul] at ha hb
  refine ⟨a, b, ?_, ?_⟩
  · linear_combination ha + hb
  · linear_combination ha - hb

theorem orderOf_κ (y : L) : orderOf (S.κ y) = orderOf y := orderOf_injective S.κ S.κ_inj y

theorem orderOf_J_mul {y : L} (hy : Odd (orderOf y)) :
    orderOf (S.J * S.κ y) = 2 * orderOf y := by
  have hcop : Nat.Coprime (orderOf S.J) (orderOf (S.κ y)) := by
    rw [S.orderOf_J, S.orderOf_κ]
    exact Nat.coprime_two_left.mpr hy
  rw [(S.commJ y).orderOf_mul_eq_mul_orderOf_of_coprime hcop, S.orderOf_J, S.orderOf_κ]

theorem pow_J_mul {y : L} (hy : Odd (orderOf y)) : (S.J * S.κ y) ^ orderOf y = S.J := by
  rw [(S.commJ y).mul_pow, ← S.orderOf_κ, pow_orderOf_eq_one, mul_one, S.orderOf_κ]
  obtain ⟨k, hk⟩ := hy
  rw [hk, pow_succ, pow_mul, sq, S.J_mul, one_pow, one_mul]

theorem pow_J_mul' {y : L} (hy : Odd (orderOf y)) :
    (S.J * S.κ y) ^ (orderOf y + 1) = S.κ y := by
  rw [pow_succ, S.pow_J_mul hy, ← mul_assoc, S.J_mul, one_mul]

omit [Fintype G] in
theorem orderOf_conj (g x : G) : orderOf (g * x * g⁻¹) = orderOf x := by
  rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]

theorem isConj_J_mul_iff {y z : L} (hy : Odd (orderOf y)) (hz : Odd (orderOf z)) :
    IsConj (S.J * S.κ y) (S.J * S.κ z) ↔ IsConj y z := by
  constructor
  · intro h
    obtain ⟨g, hg⟩ := isConj_iff.mp h
    have hord : orderOf y = orderOf z := by
      have := orderOf_conj g (S.J * S.κ y)
      rw [hg, S.orderOf_J_mul hy, S.orderOf_J_mul hz] at this
      omega
    have hgJ : g * S.J * g⁻¹ = S.J := by
      have h1 := congrArg (· ^ orderOf y) hg
      rw [conj_pow, S.pow_J_mul hy, hord, S.pow_J_mul hz] at h1
      exact h1
    have hgc : g * S.J = S.J * g := by
      calc g * S.J = g * S.J * g⁻¹ * g := by group
        _ = S.J * g := by rw [hgJ]
    have hkey : ∀ w : L, (g = S.κ w ∨ g = S.J * S.κ w) →
        g * (S.J * S.κ y) * g⁻¹ = S.J * S.κ (w * y * w⁻¹) := by
      intro w hw
      rw [map_mul, map_mul, map_inv]
      rcases hw with rfl | rfl
      · calc S.κ w * (S.J * S.κ y) * (S.κ w)⁻¹ = (S.κ w * S.J) * S.κ y * (S.κ w)⁻¹ := by group
          _ = (S.J * S.κ w) * S.κ y * (S.κ w)⁻¹ := by rw [S.κ_comm w]
          _ = S.J * (S.κ w * S.κ y * (S.κ w)⁻¹) := by group
      · rw [mul_inv_rev, S.J_inv]
        calc S.J * S.κ w * (S.J * S.κ y) * ((S.κ w)⁻¹ * S.J) =
            S.J * (S.κ w * S.J) * S.κ y * (S.κ w)⁻¹ * S.J := by group
          _ = S.J * (S.J * S.κ w) * S.κ y * (S.κ w)⁻¹ * S.J := by rw [S.κ_comm w]
          _ = S.κ w * S.κ y * (S.κ w)⁻¹ * S.J := by rw [← mul_assoc, S.J_mul, one_mul]
          _ = S.κ (w * y * w⁻¹) * S.J := by rw [map_mul, map_mul, map_inv]
          _ = S.J * S.κ (w * y * w⁻¹) := S.κ_comm _
          _ = S.J * (S.κ w * S.κ y * (S.κ w)⁻¹) := by rw [map_mul, map_mul, map_inv]
    obtain ⟨w, hw⟩ := S.centralizer g hgc
    refine isConj_iff.mpr ⟨w, ?_⟩
    have h2 := hkey w hw
    rw [hg] at h2
    exact ((S.J_κ_eq_iff _ _).mp h2.symm)
  · intro h
    obtain ⟨g, hg⟩ := isConj_iff.mp h
    refine isConj_iff.mpr ⟨S.κ g, ?_⟩
    rw [← hg, map_mul, map_mul, map_inv]
    calc S.κ g * (S.J * S.κ y) * (S.κ g)⁻¹ = S.κ g * S.J * S.κ y * (S.κ g)⁻¹ := by group
      _ = S.J * S.κ g * S.κ y * (S.κ g)⁻¹ := by rw [S.κ_comm]
      _ = S.J * (S.κ g * S.κ y * (S.κ g)⁻¹) := by group

theorem commute_of_commute_J_mul {z : L} (hz : Odd (orderOf z)) {x : G}
    (hx : x * (S.J * S.κ z) = S.J * S.κ z * x) :
    x * S.J = S.J * x ∧ x * S.κ z = S.κ z * x := by
  have hc : Commute x (S.J * S.κ z) := hx
  constructor
  · have := hc.pow_right (orderOf z)
    rw [S.pow_J_mul hz] at this
    exact this
  · have := hc.pow_right (orderOf z + 1)
    rw [S.pow_J_mul' hz] at this
    exact this

theorem card_centralizer_J_mul {z : L} (hz : Odd (orderOf z)) :
    Nat.card (Subgroup.centralizer ({S.J * S.κ z} : Set G)) =
      2 * Nat.card (Subgroup.centralizer ({z} : Set L)) := by
  have hmap : Subgroup.centralizer ({S.J * S.κ z} : Set G) =
      ((⊤ : Subgroup (Subgroup.zpowers S.J)).prod (Subgroup.centralizer ({z} : Set L))).map
        S.ι := by
    ext x
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_map]
    constructor
    · intro hx
      obtain ⟨hJ, hκ⟩ := S.commute_of_commute_J_mul hz hx
      obtain ⟨w, rfl | rfl⟩ := S.centralizer x hJ
      · refine ⟨(1, w), ⟨Subgroup.mem_top _, ?_⟩, by simp [ι_apply]⟩
        show w ∈ Subgroup.centralizer ({z} : Set L)
        rw [Subgroup.mem_centralizer_singleton_iff]
        apply S.κ_inj
        rw [map_mul, map_mul]
        exact hκ
      · refine ⟨(S.Jz, w), ⟨Subgroup.mem_top _, ?_⟩, by simp [ι_apply, Jz]⟩
        show w ∈ Subgroup.centralizer ({z} : Set L)
        rw [Subgroup.mem_centralizer_singleton_iff]
        apply S.κ_inj
        rw [map_mul, map_mul]
        have h1 : S.J * S.κ w * S.κ z = S.κ z * (S.J * S.κ w) := hκ
        have h2 : S.J * (S.κ w * S.κ z) = S.J * (S.κ z * S.κ w) := by
          rw [← mul_assoc, h1, ← mul_assoc, ← S.κ_comm' z, mul_assoc]
        exact mul_left_cancel h2
    · rintro ⟨⟨u, w⟩, ⟨-, hw⟩, rfl⟩
      have hw' : w ∈ Subgroup.centralizer ({z} : Set L) := hw
      rw [Subgroup.mem_centralizer_singleton_iff] at hw'
      have hκw : S.κ w * S.κ z = S.κ z * S.κ w := by rw [← map_mul, hw', map_mul]
      rw [ι_apply]
      have hu := S.commute_zpowers u w
      have hu' := S.commute_zpowers u z
      have huJ : Commute (u : G) S.J := by
        obtain ⟨k, hk⟩ := u.2
        rw [← hk]
        exact Commute.zpow_left (Commute.refl S.J) k
      calc (u : G) * S.κ w * (S.J * S.κ z) = (u : G) * (S.κ w * S.J) * S.κ z := by group
        _ = (u : G) * (S.J * S.κ w) * S.κ z := by rw [S.κ_comm]
        _ = (u : G) * S.J * (S.κ w * S.κ z) := by group
        _ = (u : G) * S.J * (S.κ z * S.κ w) := by rw [hκw]
        _ = S.J * (u : G) * S.κ z * S.κ w := by rw [huJ.eq]; group
        _ = S.J * S.κ z * (u : G) * S.κ w := by rw [mul_assoc S.J, hu'.eq]; group
        _ = S.J * S.κ z * ((u : G) * S.κ w) := by group
  have hinj : Function.Injective S.ι := by
    rintro ⟨u, w⟩ ⟨u', w'⟩ h
    rw [ι_apply, ι_apply] at h
    rcases S.Z_cases u with rfl | rfl <;> rcases S.Z_cases u' with rfl | rfl
    · simp only [OneMemClass.coe_one, one_mul] at h
      rw [S.κ_inj h]
    · simp only [OneMemClass.coe_one, one_mul, Jz] at h
      exact absurd h.symm (S.J_mul_ne w' w)
    · simp only [OneMemClass.coe_one, one_mul, Jz] at h
      exact absurd h (S.J_mul_ne w w')
    · simp only [Jz, mul_right_inj] at h
      rw [S.κ_inj h]
  rw [hmap, Subgroup.card_map_of_injective hinj,
    Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, Subgroup.card_top, S.card_Z]

theorem sum_σ_mul_conj {y z : L} (hy : Odd (orderOf y)) (hz : Odd (orderOf z)) :
    ∑ χ ∈ (irreducibles_finite G).toFinset, S.σ χ y * starRingEnd ℂ (S.σ χ z) =
      if IsConj y z then 2 * (Nat.card (Subgroup.centralizer ({z} : Set L)) : ℂ) else 0 := by
  have h := sum_irr_mul_conj (S.J * S.κ y) (S.J * S.κ z)
  simp only [σ]
  rw [h]
  by_cases hc : IsConj y z
  · have hc' := (S.isConj_J_mul_iff hy hz).mpr hc
    simp only [hc, hc', ↓reduceIte, S.card_centralizer_J_mul hz]
    push_cast
    ring
  · have hc' : ¬ IsConj (S.J * S.κ y) (S.J * S.κ z) := fun h => hc ((S.isConj_J_mul_iff hy hz).mp h)
    simp only [hc, hc', ↓reduceIte]

theorem gram {Φ Ψ : L → ℂ} (hΦ : ∀ y : L, Even (orderOf y) → Φ y = 0)
    (hΨ : ∀ y : L, Even (orderOf y) → Ψ y = 0) (hΦc : BlocksIsClassFunction Φ) :
    ∑ χ ∈ (irreducibles_finite G).toFinset,
        BlocksInnerProduct (S.σ χ) Φ * starRingEnd ℂ (BlocksInnerProduct (S.σ χ) Ψ) =
      2 * BlocksInnerProduct Ψ Φ := by
  have hL : (Nat.card L : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  set c : L → ℂ := fun z => (Nat.card (Subgroup.centralizer ({z} : Set L)) : ℂ) with hc
  have hterm : ∀ y z : L, starRingEnd ℂ (Φ y) * Ψ z *
      ∑ χ ∈ (irreducibles_finite G).toFinset, S.σ χ y * starRingEnd ℂ (S.σ χ z) =
      (if IsConj y z then (1 : ℂ) else 0) * starRingEnd ℂ (Φ y) * (Ψ z * (2 * c z)) := by
    intro y z
    by_cases hy : Odd (orderOf y)
    · by_cases hz : Odd (orderOf z)
      · rw [S.sum_σ_mul_conj hy hz]
        by_cases hcz : IsConj y z
        · simp only [hcz, ↓reduceIte, hc]
          ring
        · simp only [hcz, ↓reduceIte, mul_zero, zero_mul]
      · rw [Nat.not_odd_iff_even] at hz
        simp [hΨ z hz]
    · rw [Nat.not_odd_iff_even] at hy
      simp [hΦ y hy]
  have hΦc' : BlocksIsClassFunction (fun y => starRingEnd ℂ (Φ y)) := by
    intro y g
    dsimp only
    rw [hΦc y g]
  have hsum_y : ∀ z : L, ∑ y : L, (if IsConj y z then (1 : ℂ) else 0) * starRingEnd ℂ (Φ y) =
      (Nat.card (ConjClasses.mk z).carrier : ℂ) * starRingEnd ℂ (Φ z) :=
    fun z => sum_isConj_mul hΦc' z
  have hcz : ∀ z : L, (Nat.card (ConjClasses.mk z).carrier : ℂ) * c z = Nat.card L := by
    intro z
    simp only [hc]
    exact_mod_cast card_conjClass_mul_card_centralizer z
  calc ∑ χ ∈ (irreducibles_finite G).toFinset,
        BlocksInnerProduct (S.σ χ) Φ * starRingEnd ℂ (BlocksInnerProduct (S.σ χ) Ψ)
      = ∑ χ ∈ (irreducibles_finite G).toFinset, (Nat.card L : ℂ)⁻¹ * (Nat.card L : ℂ)⁻¹ *
          ∑ y : L, ∑ z : L,
            starRingEnd ℂ (Φ y) * Ψ z * (S.σ χ y * starRingEnd ℂ (S.σ χ z)) := by
        refine Finset.sum_congr rfl fun χ _ => ?_
        unfold BlocksInnerProduct
        rw [map_mul, map_inv₀, Complex.conj_natCast, map_sum, mul_mul_mul_comm,
          Finset.sum_mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => ?_
        simp only [map_mul, Complex.conj_conj]
        ring
    _ = (Nat.card L : ℂ)⁻¹ * (Nat.card L : ℂ)⁻¹ * ∑ y : L, ∑ z : L,
          starRingEnd ℂ (Φ y) * Ψ z *
            ∑ χ ∈ (irreducibles_finite G).toFinset, S.σ χ y * starRingEnd ℂ (S.σ χ z) := by
        rw [← Finset.mul_sum]
        congr 1
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [Finset.mul_sum]
    _ = (Nat.card L : ℂ)⁻¹ * (Nat.card L : ℂ)⁻¹ * ∑ z : L, (Ψ z * (2 * c z)) *
          ∑ y : L, (if IsConj y z then (1 : ℂ) else 0) * starRingEnd ℂ (Φ y) := by
        congr 1
        simp_rw [hterm]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        ring
    _ = (Nat.card L : ℂ)⁻¹ * (Nat.card L : ℂ)⁻¹ * ∑ z : L,
          2 * (Nat.card L : ℂ) * (Ψ z * starRingEnd ℂ (Φ z)) := by
        congr 1
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [hsum_y z, ← hcz z]
        ring
    _ = 2 * BlocksInnerProduct Ψ Φ := by
        unfold BlocksInnerProduct
        rw [← Finset.mul_sum]
        field_simp

theorem degree_orth (Φ : L → ℂ) {x : G} (hx : Odd (orderOf x)) :
    ∑ χ ∈ (irreducibles_finite G).toFinset,
        BlocksInnerProduct (S.σ χ) Φ * starRingEnd ℂ (χ x) = 0 := by
  have hterm : ∀ y : L, ∑ χ ∈ (irreducibles_finite G).toFinset,
      S.σ χ y * starRingEnd ℂ (χ x) = 0 := by
    intro y
    simp only [σ]
    rw [sum_irr_mul_conj, ite_eq_right_iff]
    intro hc
    obtain ⟨g, hg⟩ := isConj_iff.mp hc
    have h1 := orderOf_conj g (S.J * S.κ y)
    rw [hg] at h1
    have hJpow : Even (orderOf (S.J * S.κ y)) := by
      by_contra hodd
      rw [Nat.not_even_iff_odd] at hodd
      have hcomm : Commute S.J (S.κ y) := S.commJ y
      have h2 : orderOf S.J ∣ orderOf (S.J * S.κ y) := by
        have := hcomm.orderOf_mul_dvd_mul_orderOf
        have hdiv : orderOf S.J ∣ orderOf (S.J * S.κ y) := by
          apply orderOf_dvd_of_pow_eq_one
          have hp := pow_orderOf_eq_one (S.J * S.κ y)
          rw [hcomm.mul_pow] at hp
          obtain ⟨k, hk⟩ := hodd
          rw [hk] at hp ⊢
          rw [pow_succ, pow_mul, sq, S.J_mul, one_pow, one_mul] at hp
          exfalso
          apply S.J_mul_ne (y ^ (2 * k + 1)) 1
          rw [map_pow, map_one, hp]
        exact hdiv
      rw [S.orderOf_J] at h2
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
    rw [← h1] at hJpow
    exact absurd hJpow (Nat.not_even_iff_odd.mpr hx)
  unfold BlocksInnerProduct
  have hre : ∀ χ : G → ℂ, (Nat.card L : ℂ)⁻¹ * (∑ y : L, S.σ χ y * starRingEnd ℂ (Φ y)) *
      starRingEnd ℂ (χ x) =
      (Nat.card L : ℂ)⁻¹ * ∑ y : L, starRingEnd ℂ (Φ y) * (S.σ χ y * starRingEnd ℂ (χ x)) := by
    intro χ
    rw [mul_assoc, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun y _ => ?_
    ring
  simp_rw [hre]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hterm]
  simp

end WardSetup

end CFSG.Walter.Ward
