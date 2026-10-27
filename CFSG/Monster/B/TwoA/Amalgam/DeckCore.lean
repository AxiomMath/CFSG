module

public import CFSG.Monster.B.Generic.SylowAutomorphism
public import CFSG.Monster.B.Generic.PRadical
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Monster.B.TwoA.Amalgam

open Subgroup

section Conj

variable {G : Type*} [Group G]

abbrev deckCent (Ht K : Subgroup G) : Subgroup G := Ht ⊓ Subgroup.centralizer (K : Set G)

theorem conj_mem_of_normalizes {Ht K : Subgroup G} (hKn : ∀ g ∈ Ht, ∀ k ∈ K, g * k * g⁻¹ ∈ K)
    {g : G} (hg : g ∈ Ht) {k : G} (hk : k ∈ K) : g⁻¹ * k * g ∈ K := by
  have h := hKn g⁻¹ (Ht.inv_mem hg) k hk
  rwa [inv_inv] at h

theorem deckCent_normal {Ht K : Subgroup G} (hKn : ∀ g ∈ Ht, ∀ k ∈ K, g * k * g⁻¹ ∈ K) :
    ((deckCent Ht K).subgroupOf Ht).Normal := by
  refine ⟨fun c hc g => ?_⟩
  have hc' := Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hc)
  have hcC := Subgroup.mem_centralizer_iff.1 hc'.2
  refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨(g * c * g⁻¹).2,
    Subgroup.mem_centralizer_iff.2 fun k hk => ?_⟩)
  have hk' := conj_mem_of_normalizes hKn g.2 hk
  have h := hcC _ hk'
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  calc k * ((g : G) * c * (g : G)⁻¹) = g * (((g : G)⁻¹ * k * g) * c) * (g : G)⁻¹ := by group
    _ = g * (c * ((g : G)⁻¹ * k * g)) * (g : G)⁻¹ := by rw [h]
    _ = (g : G) * c * (g : G)⁻¹ * k := by group

@[expose] def conjOn {S K : Subgroup G} (hS : ∀ g ∈ S, ∀ k ∈ K, g * k * g⁻¹ ∈ K) :
    S →* MulAut K where
  toFun g :=
    { toFun := fun k => ⟨g * k * (g : G)⁻¹, hS g g.2 k k.2⟩
      invFun := fun k => ⟨(g : G)⁻¹ * k * g, conj_mem_of_normalizes hS g.2 k.2⟩
      left_inv := fun k => Subtype.ext (by simp [mul_assoc])
      right_inv := fun k => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun k k' => Subtype.ext (by simp [mul_assoc]) }
  map_one' := MulEquiv.ext fun k => Subtype.ext (by simp)
  map_mul' g g' := MulEquiv.ext fun k => Subtype.ext (by simp [mul_assoc])

theorem coe_conjOn_apply {S K : Subgroup G} (hS : ∀ g ∈ S, ∀ k ∈ K, g * k * g⁻¹ ∈ K) (g : S)
    (k : K) : ((conjOn hS g k : K) : G) = g * k * (g : G)⁻¹ := rfl

theorem ker_conjOn {Ht S K : Subgroup G} (hS : ∀ g ∈ S, ∀ k ∈ K, g * k * g⁻¹ ∈ K)
    (hSH : S ≤ Ht) : (conjOn hS).ker = (deckCent Ht K).subgroupOf S := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    refine ⟨hSH g.2, fun k hk => ?_⟩
    have h1 := congrArg (fun σ : MulAut K => ((σ ⟨k, hk⟩ : K) : G)) h
    simp only [coe_conjOn_apply, MulAut.one_apply] at h1
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  · rintro ⟨-, h⟩
    refine MulEquiv.ext fun k => Subtype.ext ?_
    rw [coe_conjOn_apply, MulAut.one_apply, ← h k k.2, mul_inv_cancel_right]

end Conj

theorem comap_le_ker_of_surjective {P U A : Type*} [Group P] [Group U] [Group A] [Finite P]
    [Finite A] {p r : ℕ} (hp : p.Prime) (α : P →* U) (hα : Function.Surjective α)
    (hN : IsPGroup p α.ker) (hNc : ⁅α.ker, ⊤⁆ = α.ker) (L : Subgroup U) [L.Normal]
    (hLs : IsSimpleGroup L) (hrL : r ∣ Nat.card L) (hUL : Nat.card (U ⧸ L) ∣ p)
    (hrA : ¬ r ∣ Nat.card A) (f : P →* A) :
    L.comap α ≤ f.ker ∧ Nat.card f.range ∣ p := by
  set e : P ⧸ α.ker ≃* U := QuotientGroup.quotientKerEquivOfSurjective α hα with he
  set L' : Subgroup (P ⧸ α.ker) := L.comap e.toMonoidHom with hL'
  have : L'.Normal := Subgroup.Normal.comap inferInstance _
  have hmap : L'.map e.toMonoidHom = L := Subgroup.map_comap_eq_self_of_surjective e.surjective L
  let eL : L' ≃* L :=
    (L'.equivMapOfInjective e.toMonoidHom e.injective).trans (MulEquiv.subgroupCongr hmap)
  have hLs' : IsSimpleGroup L' := eL.isSimpleGroup
  have hcard : Nat.card L' = Nat.card L := Nat.card_congr eL.toEquiv
  have hq : Nat.card ((P ⧸ α.ker) ⧸ L') = Nat.card (U ⧸ L) :=
    Nat.card_congr (QuotientGroup.congr L' L e hmap).toEquiv
  obtain ⟨h1, -, h3, -⟩ := CFSG.Monster.B.Generic.p_radical_perfect_action_quotient_test hp
    α.ker hN hNc L' hLs' (hcard ▸ hrL) (hq ▸ hUL) hrA f
  have hcomap : L'.comap (QuotientGroup.mk' α.ker) = L.comap α := by
    rw [hL', Subgroup.comap_comap]
    rfl
  exact ⟨hcomap ▸ h1, h3⟩

section Core

variable {G U O : Type*} [Group G] [Group U] [Group O]

theorem eq_one_of_pow_five_of_pow_two {M : Type*} [Group M] {z : M} (h5 : z ^ 5 = 1)
    (h2 : z ^ 2 = 1) : z = 1 := by
  have : z = z ^ 5 * ((z ^ 2)⁻¹) ^ 2 := by group
  rw [this, h5, h2]
  simp

theorem deck_centralizer_core {Ht K P₁ P₄ Bt : Subgroup G} [Finite K] [Finite P₁]
    (hKn : ∀ g ∈ Ht, ∀ k ∈ K, g * k * g⁻¹ ∈ K) (hK : Nat.card K ∣ 3968055)
    (hP₁ : P₁ ≤ Ht) (hP₄ : P₄ ≤ Ht)
    (α₁ : P₁ →* U) (hα₁ : Function.Surjective α₁) (hN₁ : IsPGroup 2 α₁.ker)
    (hN₁c : ⁅α₁.ker, ⊤⁆ = α₁.ker) (L : Subgroup U) [L.Normal] (hLs : IsSimpleGroup L)
    (hL11 : 11 ∣ Nat.card L) (hUL : Nat.card (U ⧸ L) ∣ 2)
    (α₄ : P₄ →* O) (hα₄ : Function.Surjective α₄) (hM : IsPGroup 2 α₄.ker)
    (D : Subgroup O) (hDs : IsSimpleGroup D) (hsq : ∀ x : O, x ^ 2 ∈ D)
    {y : G} (hy₁ : y ∈ P₁) (hy₄ : y ∈ P₄) (hy1 : y ≠ 1) (hy5 : y ^ 5 = 1)
    (SU : Subgroup U) (SO : Subgroup O)
    (hBU : Bt.subgroupOf P₁ = SU.comap α₁) (hBO : Bt.subgroupOf P₄ = SO.comap α₄) :
    ((deckCent Ht K).subgroupOf Ht).Normal ∧
      L.comap α₁ ≤ (deckCent Ht K).subgroupOf P₁ ∧
      Nat.card (conjOn fun g hg => hKn g (hP₁ hg)).range ∣ 2 ∧
      D ≤ ((deckCent Ht K).subgroupOf P₄).map α₄ ∧
      L ⊓ SU ≤ ((deckCent Ht K ⊓ Bt).subgroupOf P₁).map α₁ ∧
      D ⊓ SO ≤ ((deckCent Ht K ⊓ Bt).subgroupOf P₄).map α₄ := by
  have hCn := deckCent_normal hKn
  have hconj₁ : ∀ g ∈ P₁, ∀ k ∈ K, g * k * g⁻¹ ∈ K := fun g hg => hKn g (hP₁ hg)
  have : Finite (MulAut K) := Finite.of_injective (fun σ : MulAut K => (σ : K → K))
    fun σ τ h => MulEquiv.ext (congrFun h)
  have hA : ¬ 11 ∣ Nat.card (MulAut K) :=
    CFSG.Monster.B.Generic.not_eleven_dvd_card_mulAut.2 K hK
  obtain ⟨hLker, hcard⟩ := comap_le_ker_of_surjective Nat.prime_two α₁ hα₁ hN₁ hN₁c L hLs hL11
    hUL hA (conjOn hconj₁)
  have hker₁ := ker_conjOn hconj₁ hP₁
  rw [hker₁] at hLker
  have hyC : y ∈ deckCent Ht K := by
    set z : MulAut K := conjOn hconj₁ ⟨y, hy₁⟩ with hz
    have hz2 : z ^ 2 = 1 := by
      have hord : orderOf (⟨z, ⟨y, hy₁⟩, rfl⟩ : (conjOn hconj₁).range) ∣ 2 :=
        (_root_.orderOf_dvd_natCard _).trans hcard
      have h := orderOf_dvd_iff_pow_eq_one.1 hord
      exact congrArg Subtype.val h
    have hz5 : z ^ 5 = 1 := by
      have hy5' : (⟨y, hy₁⟩ : P₁) ^ 5 = 1 := Subtype.ext (by simpa using hy5)
      rw [hz, ← map_pow, hy5', map_one]
    have hz1 := eq_one_of_pow_five_of_pow_two hz5 hz2
    have hmem : (⟨y, hy₁⟩ : P₁) ∈ (conjOn hconj₁).ker := hz1
    rw [hker₁] at hmem
    exact hmem
  set z : O := α₄ ⟨y, hy₄⟩ with hzdef
  have hz5 : z ^ 5 = 1 := by
    have hy5' : (⟨y, hy₄⟩ : P₄) ^ 5 = 1 := Subtype.ext (by simpa using hy5)
    rw [hzdef, ← map_pow, hy5', map_one]
  have hz1 : z ≠ 1 := by
    intro h
    have hmem : (⟨y, hy₄⟩ : P₄) ∈ α₄.ker := h
    obtain ⟨n, hn⟩ := hM ⟨_, hmem⟩
    have hyn : y ^ 2 ^ n = 1 := by
      have := congrArg (fun w : α₄.ker => ((w : P₄) : G)) hn
      simpa using this
    have hd : orderOf y ∣ Nat.gcd (2 ^ n) 5 :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hyn) (orderOf_dvd_of_pow_eq_one hy5)
    have hg : Nat.gcd (2 ^ n) 5 = 1 :=
      Nat.Coprime.pow_left n (by norm_num : Nat.Coprime 2 5)
    rw [hg, Nat.dvd_one, orderOf_eq_one_iff] at hd
    exact hy1 hd
  have hzD : z ∈ D := by
    have h6 : z = (z ^ 2) ^ 3 := by
      rw [← pow_mul, show 2 * 3 = 5 + 1 from rfl, pow_succ, hz5, one_mul]
    rw [h6]
    exact pow_mem (hsq z) 3
  set M : Subgroup O := ((deckCent Ht K).subgroupOf P₄).map α₄ with hMdef
  have hCn₄ : ((deckCent Ht K).subgroupOf P₄).Normal := by
    refine ⟨fun c hc g => ?_⟩
    have h := hCn.conj_mem ⟨c, hP₄ c.2⟩ hc ⟨g, hP₄ g.2⟩
    exact h
  have hMn : M.Normal := Subgroup.Normal.map hCn₄ α₄ hα₄
  have hzM : z ∈ M := ⟨⟨y, hy₄⟩, hyC, rfl⟩
  have hDM : D ≤ M := by
    have hn : (M.subgroupOf D).Normal := Subgroup.Normal.subgroupOf hMn D
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hDs _ hn with h | h
    · exfalso
      have hmem : (⟨z, hzD⟩ : D) ∈ M.subgroupOf D := hzM
      rw [h, Subgroup.mem_bot] at hmem
      exact hz1 (congrArg Subtype.val hmem)
    · intro d hd
      have hmem : (⟨d, hd⟩ : D) ∈ M.subgroupOf D := h ▸ Subgroup.mem_top _
      exact hmem
  refine ⟨hCn, hLker, hcard, hDM, ?_, ?_⟩
  · rintro u ⟨huL, huS⟩
    obtain ⟨x, rfl⟩ := hα₁ u
    have hxB : x ∈ Bt.subgroupOf P₁ := hBU ▸ huS
    exact ⟨x, ⟨hLker huL, hxB⟩, rfl⟩
  · rintro d ⟨hdD, hdS⟩
    obtain ⟨x, hxC, rfl⟩ := hDM hdD
    have hxB : x ∈ Bt.subgroupOf P₄ := hBO ▸ hdS
    exact ⟨x, ⟨hxC, hxB⟩, rfl⟩

end Core

end CFSG.Monster.B.TwoA.Amalgam
