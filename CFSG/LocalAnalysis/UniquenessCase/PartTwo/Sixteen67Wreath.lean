module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefsB
public import CFSG.GroupTheory.KleinFourAutomorphism
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.MinimalFixed

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem exists_notMem_of_not_le {A N : Subgroup G} (h : ¬ A ≤ N) :
    ∃ a ∈ A, a ∉ N := by
  by_contra h'
  apply h
  intro a ha
  by_contra haN
  exact h' ⟨a, ha, haN⟩

private theorem mem_centralizer_sup {W₁ W₂ V : Subgroup G} (hsup : W₁ ⊔ W₂ = V) {a : G}
    (h₁ : a ∈ Subgroup.centralizer (W₁ : Set G))
    (h₂ : a ∈ Subgroup.centralizer (W₂ : Set G)) :
    a ∈ Subgroup.centralizer (V : Set G) := by
  have h1 : W₁ ≤ Subgroup.centralizer ({a} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp h₁ y hy
  have h2 : W₂ ≤ Subgroup.centralizer ({a} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp h₂ y hy
  have hV : V ≤ Subgroup.centralizer ({a} : Set G) := hsup ▸ sup_le h1 h2
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hv' := hV hv
  rwa [Subgroup.mem_centralizer_singleton_iff] at hv'

private theorem centralizer_inf_eq_of_swap {X Y V A : Subgroup G} (hsup : X ⊔ Y = V)
    (hA : IsElemAbelian 2 A) {s : G} (hsA : s ∈ A) (hsXY : conjSubgroup X s = Y) :
    A ⊓ Subgroup.centralizer (X : Set G) = A ⊓ Subgroup.centralizer (V : Set G) := by
  have hXV : (X : Set G) ⊆ (V : Set G) := by
    intro y hy
    rw [← hsup]
    exact Subgroup.mem_sup_left hy
  apply le_antisymm
  · rintro a ⟨haA, haX⟩
    refine ⟨haA, mem_centralizer_sup hsup haX ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hxX : s * y * s⁻¹ ∈ X := mem_conjSubgroup_iff.mp (hsXY.symm ▸ hy)
    have hcomm : s * a = a * s :=
      Subtype.ext_iff.mp ((hA.1).is_comm.comm ⟨s, hsA⟩ ⟨a, haA⟩)
    have hca : Commute a s := (commute_iff_eq a s).mpr hcomm.symm
    have hasi : a * s⁻¹ = s⁻¹ * a := hca.inv_right.eq
    have hsai : s * a⁻¹ = a⁻¹ * s := hca.inv_left.eq.symm
    have hax : a * (s * y * s⁻¹) * a⁻¹ = s * y * s⁻¹ := by
      rw [mul_inv_eq_iff_eq_mul]
      exact (Subgroup.mem_centralizer_iff.mp haX (s * y * s⁻¹) hxX).symm
    have hmain : a * y * a⁻¹ = y := by
      calc a * y * a⁻¹ = a * (s⁻¹ * (s * y * s⁻¹) * s) * a⁻¹ := by group
        _ = (a * s⁻¹) * (s * y * s⁻¹) * (s * a⁻¹) := by group
        _ = (s⁻¹ * a) * (s * y * s⁻¹) * (a⁻¹ * s) := by rw [hasi, hsai]
        _ = s⁻¹ * (a * (s * y * s⁻¹) * a⁻¹) * s := by group
        _ = s⁻¹ * (s * y * s⁻¹) * s := by rw [hax]
        _ = y := by group
    exact (mul_inv_eq_iff_eq_mul.mp hmain).symm
  · rintro a ⟨haA, haV⟩
    exact ⟨haA, Subgroup.centralizer_le hXV haV⟩

private theorem zpowers_eq_pair_of_sq_eq_one {x : G} (hx : x ^ 2 = 1) {y : G}
    (hy : y ∈ Subgroup.zpowers x) : y = 1 ∨ y = x := by
  rw [Subgroup.zpowers_eq_closure] at hy
  refine Subgroup.closure_induction (p := fun y _ => y = 1 ∨ y = x) ?_ ?_ ?_ ?_ hy
  · rintro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    exact Or.inr rfl
  · exact Or.inl rfl
  · rintro y₁ y₂ _ _ hy₁ hy₂
    rcases hy₁ with h₁ | h₁
    · rw [h₁, one_mul]
      exact hy₂
    · rw [h₁]
      rcases hy₂ with h₂ | h₂
      · rw [h₂, mul_one]
        exact Or.inr rfl
      · rw [h₂]
        exact Or.inl (by rw [← pow_two]; exact hx)
  · rintro y _ hy
    rcases hy with h | h
    · rw [h]
      exact Or.inl inv_one
    · rw [h]
      exact Or.inr (inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hx))

private theorem exists_mul_of_mem_sup {W₁ W₂ : Subgroup G}
    (hcomm : ∀ a ∈ W₁, ∀ b ∈ W₂, a * b = b * a) {v : G}
    (hv : v ∈ W₁ ⊔ W₂) : ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, w₁ * w₂ = v := by
  rw [Subgroup.sup_eq_closure] at hv
  refine Subgroup.closure_induction (p := fun v _ => ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, w₁ * w₂ = v)
    ?_ ?_ ?_ ?_ hv
  · rintro x (hx | hx)
    · exact ⟨x, hx, 1, W₂.one_mem, by simp⟩
    · exact ⟨1, W₁.one_mem, x, hx, by simp⟩
  · exact ⟨1, W₁.one_mem, 1, W₂.one_mem, by simp⟩
  · rintro x y hx hy ⟨a₁, ha₁, a₂, ha₂, rfl⟩ ⟨b₁, hb₁, b₂, hb₂, rfl⟩
    exact ⟨a₁ * b₁, W₁.mul_mem ha₁ hb₁, a₂ * b₂, W₂.mul_mem ha₂ hb₂, by
      calc a₁ * b₁ * (a₂ * b₂) = a₁ * (b₁ * a₂) * b₂ := by group
        _ = a₁ * (a₂ * b₁) * b₂ := by rw [hcomm b₁ hb₁ a₂ ha₂]
        _ = a₁ * a₂ * (b₁ * b₂) := by group⟩
  · rintro x hx ⟨a₁, ha₁, a₂, ha₂, rfl⟩
    exact ⟨a₁⁻¹, W₁.inv_mem ha₁, a₂⁻¹, W₂.inv_mem ha₂,
      by rw [← mul_inv_rev a₂ a₁, hcomm a₁ ha₁ a₂ ha₂]⟩

private theorem mul_eq_mul_iff {W₁ W₂ : Subgroup G} (hinf : W₁ ⊓ W₂ = ⊥)
    {a₁ a₂ b₁ b₂ : G} (ha₁ : a₁ ∈ W₁) (ha₂ : a₂ ∈ W₂) (hb₁ : b₁ ∈ W₁) (hb₂ : b₂ ∈ W₂) :
    a₁ * a₂ = b₁ * b₂ ↔ a₁ = b₁ ∧ a₂ = b₂ := by
  constructor
  · intro h
    have hmem : b₁⁻¹ * a₁ = b₂ * a₂⁻¹ := by
      calc b₁⁻¹ * a₁ = b₁⁻¹ * (a₁ * a₂) * a₂⁻¹ := by group
        _ = b₁⁻¹ * (b₁ * b₂) * a₂⁻¹ := by rw [h]
        _ = b₂ * a₂⁻¹ := by group
    have h1 : b₁⁻¹ * a₁ ∈ W₁ := W₁.mul_mem (W₁.inv_mem hb₁) ha₁
    have h2 : b₂ * a₂⁻¹ ∈ W₂ := W₂.mul_mem hb₂ (W₂.inv_mem ha₂)
    have hbot : b₁⁻¹ * a₁ = 1 := by
      have : b₁⁻¹ * a₁ ∈ W₁ ⊓ W₂ := ⟨h1, by rw [hmem]; exact h2⟩
      rw [hinf] at this
      exact Subgroup.mem_bot.mp this
    have ha₁eq : a₁ = b₁ := by
      have h' : b₁ * (b₁⁻¹ * a₁) = b₁ * 1 := congrArg (fun t => b₁ * t) hbot
      calc a₁ = b₁ * (b₁⁻¹ * a₁) := by group
        _ = b₁ * 1 := h'
        _ = b₁ := by rw [mul_one]
    have h2' : a₁ * a₂ = a₁ * b₂ := by rw [h, ha₁eq]
    exact ⟨ha₁eq, mul_left_cancel h2'⟩
  · rintro ⟨rfl, rfl⟩
    rfl

private theorem card_sup_of_commute_of_inf_eq_bot (L R : Subgroup G)
    (hcomm : ∀ x ∈ L, ∀ y ∈ R, x * y = y * x) (hinf : L ⊓ R = ⊥) :
    Nat.card (L ⊔ R : Subgroup G) = Nat.card L * Nat.card R := by
  let f : ↥L × ↥R → ↥(L ⊔ R) := fun p =>
    ⟨(p.1 : G) * (p.2 : G),
      mul_mem (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)⟩
  have hf : Function.Bijective f := by
    refine ⟨?_, ?_⟩
    · rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ h
      have hG : (x₁ : G) * (y₁ : G) = (x₂ : G) * (y₂ : G) := congrArg Subtype.val h
      have huniq := (mul_eq_mul_iff hinf x₁.2 y₁.2 x₂.2 y₂.2).mp hG
      exact Prod.ext (Subtype.ext huniq.1) (Subtype.ext huniq.2)
    · intro z
      obtain ⟨x, hx, y, hy, hxy⟩ := exists_mul_of_mem_sup hcomm z.2
      exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), Subtype.ext hxy⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod]

private theorem card_inf_centralizer_zpowers_eq_two {W : Subgroup G} {t : G}
    (hcard : Nat.card W = 4) (ht2 : t ^ 2 = 1) (htN : t ∈ Subgroup.normalizer (W : Set G))
    (htC : t ∉ Subgroup.centralizer (W : Set G)) :
    Nat.card (W ⊓ Subgroup.centralizer (Subgroup.zpowers t : Set G) : Subgroup G) = 2 := by
  set F : Subgroup G := W ⊓ Subgroup.centralizer (Subgroup.zpowers t : Set G) with hF
  have hFW : F ≤ W := inf_le_left
  have hW2 : IsPGroup 2 ↥W := IsPGroup.of_card (n := 2) (by rw [hcard]; norm_num)
  have hWne : W ≠ ⊥ := by
    intro h; rw [h] at hcard; simp at hcard
  have hS2 : IsPGroup 2 ↥(Subgroup.zpowers t) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one ht2
  have hSN : Subgroup.zpowers t ≤ Subgroup.normalizer (W : Set G) :=
    Subgroup.zpowers_le.mpr htN
  obtain ⟨x, hxW, hx1, hxcent⟩ :=
    CFSG.AGLEmbeddingD2.McLaughlin.exists_ne_one_centralized_of_isPGroup_two hS2 hSN hW2 hWne
  have hFne : F ≠ ⊥ := by
    intro hbot
    have hxF : x ∈ F := by
      refine ⟨hxW, Subgroup.mem_centralizer_iff.mpr ?_⟩
      exact hxcent
    rw [hbot] at hxF
    exact hx1 (Subgroup.mem_bot.mp hxF)
  have hFWne : F ≠ W := by
    intro hEq
    have htcent : t ∈ Subgroup.centralizer (W : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have hwF : w ∈ F := hEq ▸ hw
      exact (Subgroup.mem_centralizer_iff.mp hwF.2 t (Subgroup.mem_zpowers t)).symm
    exact htC htcent
  have hdvd : Nat.card F ∣ 4 := by
    have h := Subgroup.relIndex_mul_card F W
    rw [inf_eq_left.mpr hFW, hcard] at h
    exact ⟨F.relIndex W, by rw [← h, mul_comm]⟩
  have hle : Nat.card F ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  have hne1 : Nat.card F ≠ 1 := by
    intro h1
    exact hFne (Subgroup.eq_bot_of_card_le (H := F) (by omega))
  have hne4 : Nat.card F ≠ 4 := by
    intro h4
    exact hFWne (Subgroup.eq_of_le_of_card_ge hFW (by rw [hcard, h4]))
  have hpos : 0 < Nat.card F := Nat.card_pos
  interval_cases Nat.card F
  · exact absurd rfl hne1
  · rfl
  · exact absurd hdvd (by norm_num)
  · exact absurd rfl hne4

private theorem isPGroup_of_isElemAbelian {p : ℕ} {A : Subgroup G} (hA : IsElemAbelian p A) :
    IsPGroup p ↥A := by
  rw [isPGroup_iff_exists_orderOf_dvd_pow]
  refine ⟨1, fun x => ?_⟩
  rw [pow_one, orderOf_dvd_iff_pow_eq_one]
  exact Subtype.ext (by simpa using hA.2 (x : G) x.2)

private theorem padicValNat_two_le_one_of_le_two {n : ℕ} (h : n ≤ 2) : padicValNat 2 n ≤ 1 := by
  interval_cases n
  · simp
  · simp
  · exact le_of_eq padicValNat_self

private theorem isKleinFour_of_card_four_of_sq {W : Subgroup G} (hcard : Nat.card W = 4)
    (hsq : ∀ x ∈ W, x ^ 2 = 1) : IsKleinFour ↥W where
  card_four := hcard
  exponent_two := by
    haveI : Fintype ↥W := Fintype.ofFinite ↥W
    haveI : Nontrivial ↥W := by
      rw [← Fintype.one_lt_card_iff_nontrivial, ← Nat.card_eq_fintype_card, hcard]
      norm_num
    rw [Monoid.exponent_eq_prime_iff (by norm_num : Nat.Prime 2)]
    intro x hx
    refine orderOf_eq_prime ?_ hx
    apply Subtype.ext
    simpa using hsq (x : G) x.2

private theorem relIndex_centralizer_le_two_of_kleinFour {W R : Subgroup G}
    (hW : IsKleinFour ↥W) (hRW : R ≤ Subgroup.normalizer (W : Set G)) (hR : IsPGroup 2 ↥R) :
    (Subgroup.centralizer (W : Set G)).relIndex R ≤ 2 := by
  haveI : IsKleinFour ↥W := hW
  let ψ : ↥R →* MulAut ↥W :=
    (Subgroup.normalizerMonoidHom (H := W)).comp (Subgroup.inclusion hRW)
  have hker : ψ.ker = (Subgroup.centralizer (W : Set G)).subgroupOf R := by
    ext x
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    change Subgroup.normalizerMonoidHom (H := W) (Subgroup.inclusion hRW x) = 1 ↔
      (x : G) ∈ Subgroup.centralizer (W : Set G)
    rw [← MonoidHom.mem_ker (f := Subgroup.normalizerMonoidHom (H := W)),
      Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]
    exact Iff.rfl
  have hrange : Nat.card ψ.range ≤ 2 := by
    have hr2 : IsPGroup 2 ↥ψ.range :=
      hR.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
    have hd6 : Nat.card ψ.range ∣ 6 := by
      have := Subgroup.card_subgroup_dvd_card ψ.range
      rwa [CFSG.kleinFour_automorphism_card ↥W] at this
    obtain ⟨n, hn⟩ := hr2.exists_card_eq
    rw [hn] at hd6 ⊢
    have hn1 : n ≤ 1 := by
      by_contra hcon
      have h4 : 4 ∣ 2 ^ n := by
        have : 2 ^ 2 ∣ 2 ^ n := pow_dvd_pow 2 (by omega)
        simpa using this
      have := h4.trans hd6
      omega
    calc 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hn1
      _ = 2 := by norm_num
  rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
  exact hrange

private theorem inf_normalizer_relIndex_le_two {W₁ W₂ A : Subgroup G}
    (hA : IsElemAbelian 2 A)
    (hperm : ∀ a ∈ A, (conjSubgroup W₁ a = W₁ ∧ conjSubgroup W₂ a = W₂) ∨
      (conjSubgroup W₁ a = W₂ ∧ conjSubgroup W₂ a = W₁)) :
    (A ⊓ Subgroup.normalizer (W₁ : Set G)).relIndex A ≤ 2 := by
  have key : ((A ⊓ Subgroup.normalizer (W₁ : Set G)).subgroupOf A).index ∣ 2 := by
    by_cases hle : A ≤ Subgroup.normalizer (W₁ : Set G)
    · have htop : (A ⊓ Subgroup.normalizer (W₁ : Set G)).subgroupOf A = ⊤ := by
        ext x
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
        constructor
        · intro _; trivial
        · intro _; exact ⟨x.2, hle x.2⟩
      rw [htop, Subgroup.index_top]
      exact one_dvd 2
    · obtain ⟨a, ha, hanorm⟩ := exists_notMem_of_not_le hle
      have hswap : conjSubgroup W₁ a = W₂ := by
        rcases hperm a ha with h | h
        · exact absurd (conjSubgroup_eq_iff_mem_normalizer.mp h.1) hanorm
        · exact h.1
      have hWa : conjSubgroup W₂ a = W₁ := by
        rw [← hswap, conjSubgroup_conjSubgroup, ← pow_two, hA.2 a ha, conjSubgroup_one]
      refine Subgroup.index_dvd_two_iff.mpr ⟨⟨a, ha⟩, fun b => ?_⟩
      by_cases hb : (b : G) ∈ Subgroup.normalizer (W₁ : Set G)
      · exact Or.inr (Subgroup.mem_subgroupOf.mpr ⟨b.2, hb⟩)
      · refine Or.inl (Subgroup.mem_subgroupOf.mpr ⟨A.mul_mem b.2 ha, ?_⟩)
        have hbW : conjSubgroup W₁ (b : G) = W₂ := by
          rcases hperm b b.2 with h | h
          · exact absurd (conjSubgroup_eq_iff_mem_normalizer.mp h.1) hb
          · exact h.1
        have hmem : conjSubgroup W₁ ((b : G) * a) = W₁ := by
          rw [← conjSubgroup_conjSubgroup W₁ (b : G) a, hbW, hWa]
        show (b : G) * a ∈ Subgroup.normalizer (W₁ : Set G)
        exact conjSubgroup_eq_iff_mem_normalizer.mp hmem
  rw [Subgroup.relIndex]
  exact Nat.le_of_dvd (by norm_num) key

theorem s1667_forall_conj_eq_of_odd {W₁ W₂ E : Subgroup G} (hne : W₁ ≠ W₂)
    (hodd : Odd (Nat.card E))
    (hperm : ∀ a ∈ E, (conjSubgroup W₁ a = W₁ ∧ conjSubgroup W₂ a = W₂) ∨
      (conjSubgroup W₁ a = W₂ ∧ conjSubgroup W₂ a = W₁)) :
    ∀ a ∈ E, conjSubgroup W₁ a = W₁ ∧ conjSubgroup W₂ a = W₂ := by
  intro a ha
  rcases hperm a ha with h | h
  · exact h
  · exfalso
    obtain ⟨h1, h2⟩ := h
    have hfix : conjSubgroup W₁ (a ^ 2) = W₁ := by
      rw [pow_two, ← conjSubgroup_conjSubgroup W₁ a a, h1, h2]
    have hswap : conjSubgroup W₂ (a ^ 2) = W₂ := by
      rw [pow_two, ← conjSubgroup_conjSubgroup W₂ a a, h2, h1]
    have hpow : ∀ k : ℕ, conjSubgroup W₁ (a ^ (2 * k)) = W₁ ∧
        conjSubgroup W₁ (a ^ (2 * k + 1)) = W₂ := by
      intro k
      induction k with
      | zero =>
        refine ⟨?_, ?_⟩
        · rw [mul_zero, pow_zero, conjSubgroup_one]
        · rw [mul_zero, Nat.zero_add, pow_one]; exact h1
      | succ k ih =>
        refine ⟨?_, ?_⟩
        · have hp : a ^ (2 * (k + 1)) = a ^ (2 * k) * a ^ 2 := by
            rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add]
          rw [hp, ← conjSubgroup_conjSubgroup W₁ (a ^ (2 * k)) (a ^ 2), ih.1, hfix]
        · have hp : a ^ (2 * (k + 1) + 1) = a ^ (2 * k + 1) * a ^ 2 := by
            rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by ring, pow_add]
          rw [hp, ← conjSubgroup_conjSubgroup W₁ (a ^ (2 * k + 1)) (a ^ 2), ih.2, hswap]
    have hdvd : orderOf a ∣ Nat.card E := by
      have h := orderOf_dvd_natCard (⟨a, ha⟩ : E)
      rw [← Subgroup.orderOf_coe (⟨a, ha⟩ : E)] at h
      simpa using h
    obtain ⟨k, hk⟩ := hodd.of_dvd_nat hdvd
    have hk' : conjSubgroup W₁ (a ^ (orderOf a)) = W₂ := by
      rw [hk]; exact (hpow k).2
    rw [pow_orderOf_eq_one, conjSubgroup_one] at hk'
    exact hne hk'

theorem s1667_relIndex_centralizer_le_four {V W₁ W₂ A : Subgroup G} (hV : IsElemAbelian 2 V)
    (hsup : W₁ ⊔ W₂ = V) (hinf : W₁ ⊓ W₂ = ⊥) (hW₁ : Nat.card W₁ = 4) (hW₂ : Nat.card W₂ = 4)
    (hA : IsElemAbelian 2 A)
    (hperm : ∀ a ∈ A, (conjSubgroup W₁ a = W₁ ∧ conjSubgroup W₂ a = W₂) ∨
      (conjSubgroup W₁ a = W₂ ∧ conjSubgroup W₂ a = W₁)) :
    (centralizer (V : Set G)).relIndex A ≤ 4 := by
  have hW₁V : (W₁ : Set G) ⊆ (V : Set G) := by
    intro y hy
    rw [← hsup]
    exact Subgroup.mem_sup_left hy
  have hW₂V : (W₂ : Set G) ⊆ (V : Set G) := by
    intro y hy
    rw [← hsup]
    exact Subgroup.mem_sup_right hy
  have hK₁ : IsKleinFour ↥W₁ :=
    isKleinFour_of_card_four_of_sq hW₁ fun x hx => hV.2 x (hW₁V hx)
  have hK₂ : IsKleinFour ↥W₂ :=
    isKleinFour_of_card_four_of_sq hW₂ fun x hx => hV.2 x (hW₂V hx)
  have hA2 : IsPGroup 2 ↥A := isPGroup_of_isElemAbelian hA
  have hne : W₁ ≠ W₂ := by
    intro heq
    have h1 : W₁ = ⊥ := by simpa [heq] using hinf
    have : Nat.card W₁ = 1 := by rw [h1]; simp
    omega
  have hA₀2 : IsPGroup 2 ↥(A ⊓ Subgroup.normalizer (W₁ : Set G)) := by
    rw [isPGroup_iff_exists_orderOf_dvd_pow]
    refine ⟨1, fun x => ?_⟩
    rw [pow_one, orderOf_dvd_iff_pow_eq_one]
    exact Subtype.ext (by simpa using hA.2 (x : G) (Subgroup.mem_inf.mp x.2).1)
  have hA₀index : (A ⊓ Subgroup.normalizer (W₁ : Set G)).relIndex A ≤ 2 :=
    inf_normalizer_relIndex_le_two hA hperm
  by_cases hfix : A ≤ Subgroup.normalizer (W₁ : Set G)
  · have hfix₂ : A ≤ Subgroup.normalizer (W₂ : Set G) := by
      intro a ha
      rcases hperm a ha with h | h
      · exact conjSubgroup_eq_iff_mem_normalizer.mp h.2
      · exact absurd (h.1.symm.trans (conjSubgroup_eq_iff_mem_normalizer.mpr (hfix ha))).symm hne
    have hC : Subgroup.centralizer (V : Set G)
        = Subgroup.centralizer (W₁ : Set G) ⊓ Subgroup.centralizer (W₂ : Set G) := by
      apply le_antisymm
      · intro x hx
        exact ⟨Subgroup.centralizer_le hW₁V hx, Subgroup.centralizer_le hW₂V hx⟩
      · intro x hx
        exact mem_centralizer_sup hsup hx.1 hx.2
    calc (Subgroup.centralizer (V : Set G)).relIndex A
        = (Subgroup.centralizer (W₁ : Set G) ⊓
            Subgroup.centralizer (W₂ : Set G)).relIndex A := by rw [hC]
      _ ≤ (Subgroup.centralizer (W₁ : Set G)).relIndex A *
            (Subgroup.centralizer (W₂ : Set G)).relIndex A := Subgroup.relIndex_inf_le
      _ ≤ 2 * 2 := Nat.mul_le_mul
          (relIndex_centralizer_le_two_of_kleinFour hK₁ hfix hA2)
          (relIndex_centralizer_le_two_of_kleinFour hK₂ hfix₂ hA2)
      _ = 4 := by norm_num
  · obtain ⟨s, hsA, hsN⟩ := exists_notMem_of_not_le hfix
    have hsW₁ : conjSubgroup W₁ s = W₂ := by
      rcases hperm s hsA with h | h
      · exact absurd (conjSubgroup_eq_iff_mem_normalizer.mp h.1) hsN
      · exact h.1
    have hsW₂ : conjSubgroup W₂ s = W₁ := by
      rw [← hsW₁, conjSubgroup_conjSubgroup, ← pow_two, hA.2 s hsA, conjSubgroup_one]
    have hCA₀ : Subgroup.centralizer (V : Set G) ⊓ (A ⊓ Subgroup.normalizer (W₁ : Set G))
        = Subgroup.centralizer (W₁ : Set G) ⊓ (A ⊓ Subgroup.normalizer (W₁ : Set G)) := by
      apply le_antisymm
      · intro x hx
        exact ⟨Subgroup.centralizer_le hW₁V hx.1, hx.2⟩
      · intro x hx
        obtain ⟨hxC₁, hxA₀⟩ := hx
        have hxA : x ∈ A := (Subgroup.mem_inf.mp hxA₀).1
        have hxs : x * s = s * x :=
          Subtype.ext_iff.mp ((hA.1).is_comm.comm ⟨x, hxA⟩ ⟨s, hsA⟩)
        have hcomm : Commute x s := (commute_iff_eq x s).mpr hxs
        have hxs' : x * s⁻¹ = s⁻¹ * x := hcomm.inv_right.eq
        have hsx' : s * x⁻¹ = x⁻¹ * s := hcomm.inv_left.eq.symm
        refine ⟨mem_centralizer_sup hsup hxC₁ ?_, hxA₀⟩
        rw [Subgroup.mem_centralizer_iff]
        intro w₂ hw₂
        have hw₁ : s * w₂ * s⁻¹ ∈ W₁ := by
          have : w₂ ∈ conjSubgroup W₁ s := by rw [hsW₁]; exact hw₂
          exact mem_conjSubgroup_iff.mp this
        have hcentral : (s * w₂ * s⁻¹) * x = x * (s * w₂ * s⁻¹) :=
          Subgroup.mem_centralizer_iff.mp hxC₁ (s * w₂ * s⁻¹) hw₁
        have hxw₁ : x * (s * w₂ * s⁻¹) * x⁻¹ = s * w₂ * s⁻¹ := by
          rw [mul_inv_eq_iff_eq_mul]
          exact hcentral.symm
        have hxw₂ : x * w₂ * x⁻¹ = w₂ := by
          calc x * w₂ * x⁻¹
              = x * (s⁻¹ * (s * w₂ * s⁻¹) * s) * x⁻¹ := by group
            _ = (x * s⁻¹) * (s * w₂ * s⁻¹) * (s * x⁻¹) := by group
            _ = (s⁻¹ * x) * (s * w₂ * s⁻¹) * (x⁻¹ * s) := by rw [hxs', hsx']
            _ = s⁻¹ * (x * (s * w₂ * s⁻¹) * x⁻¹) * s := by group
            _ = s⁻¹ * (s * w₂ * s⁻¹) * s := by rw [hxw₁]
            _ = w₂ := by group
        exact (mul_inv_eq_iff_eq_mul.mp hxw₂).symm
    have htower : (Subgroup.centralizer (V : Set G)).relIndex A
        = (Subgroup.centralizer (V : Set G)).relIndex (A ⊓ Subgroup.normalizer (W₁ : Set G))
          * (A ⊓ Subgroup.normalizer (W₁ : Set G)).relIndex A := by
      have h := Subgroup.relIndex_inf_mul_relIndex (Subgroup.centralizer (V : Set G))
        (A ⊓ Subgroup.normalizer (W₁ : Set G)) A
      rw [inf_eq_left.mpr (show A ⊓ Subgroup.normalizer (W₁ : Set G) ≤ A from
        fun x hx => (Subgroup.mem_inf.mp hx).1)] at h
      have hCA : Subgroup.centralizer (V : Set G) ⊓ (A ⊓ Subgroup.normalizer (W₁ : Set G))
          = Subgroup.centralizer (V : Set G) ⊓ A := by
        apply le_antisymm
        · intro x hx
          exact ⟨hx.1, (Subgroup.mem_inf.mp hx.2).1⟩
        · intro x hx
          exact ⟨hx.1, ⟨hx.2,
            Subgroup.centralizer_le_normalizer (W₁ : Set G) (Subgroup.centralizer_le hW₁V hx.1)⟩⟩
      rw [hCA, Subgroup.inf_relIndex_right] at h
      exact h.symm
    have hCrel : (Subgroup.centralizer (V : Set G)).relIndex
          (A ⊓ Subgroup.normalizer (W₁ : Set G))
        = (Subgroup.centralizer (W₁ : Set G)).relIndex
          (A ⊓ Subgroup.normalizer (W₁ : Set G)) := by
      rw [← Subgroup.inf_relIndex_right (Subgroup.centralizer (V : Set G))
            (A ⊓ Subgroup.normalizer (W₁ : Set G)), hCA₀,
        Subgroup.inf_relIndex_right (Subgroup.centralizer (W₁ : Set G))
          (A ⊓ Subgroup.normalizer (W₁ : Set G))]
    calc (Subgroup.centralizer (V : Set G)).relIndex A
        = (Subgroup.centralizer (V : Set G)).relIndex
            (A ⊓ Subgroup.normalizer (W₁ : Set G))
          * (A ⊓ Subgroup.normalizer (W₁ : Set G)).relIndex A := htower
      _ ≤ 2 * 2 := by
          rw [hCrel]
          exact Nat.mul_le_mul
            (relIndex_centralizer_le_two_of_kleinFour hK₁
              (fun x hx => (Subgroup.mem_inf.mp hx).2) hA₀2)
            hA₀index
      _ = 4 := by norm_num

theorem s1667_relIndex_gammaOneBar_le_two {V W₁ W₂ A : Subgroup G} (hV : IsElemAbelian 2 V)
    (hsup : W₁ ⊔ W₂ = V) (hinf : W₁ ⊓ W₂ = ⊥) (hW₁ : Nat.card W₁ = 4) (hW₂ : Nat.card W₂ = 4)
    (hA : IsElemAbelian 2 A)
    (hperm : ∀ a ∈ A, (conjSubgroup W₁ a = W₁ ∧ conjSubgroup W₂ a = W₂) ∨
      (conjSubgroup W₁ a = W₂ ∧ conjSubgroup W₂ a = W₁))
    (h4 : (centralizer (V : Set G)).relIndex A = 4) :
    (gammaOneBar V A).relIndex V ≤ 2 := by
  have hW₁V : (W₁ : Set G) ⊆ (V : Set G) := by
    intro y hy
    rw [← hsup]
    exact Subgroup.mem_sup_left hy
  have hW₂V : (W₂ : Set G) ⊆ (V : Set G) := by
    intro y hy
    rw [← hsup]
    exact Subgroup.mem_sup_right hy
  have hcommV : ∀ x ∈ W₁, ∀ y ∈ W₂, x * y = y * x := by
    intro x hx y hy
    exact Subtype.ext_iff.mp ((hV.1).is_comm.comm ⟨x, hW₁V hx⟩ ⟨y, hW₂V hy⟩)
  have hVcard : Nat.card V = 16 := by
    have h := card_sup_of_commute_of_inf_eq_bot W₁ W₂ hcommV hinf
    rw [hW₁, hW₂] at h
    rw [← hsup, h]
  have hK₁ : IsKleinFour ↥W₁ :=
    isKleinFour_of_card_four_of_sq hW₁ fun x hx => hV.2 x (hW₁V hx)
  have hK₂ : IsKleinFour ↥W₂ :=
    isKleinFour_of_card_four_of_sq hW₂ fun x hx => hV.2 x (hW₂V hx)
  have hA2 : IsPGroup 2 ↥A := isPGroup_of_isElemAbelian hA
  have hUV : gammaOneBar V A ≤ V :=
    iSup₂_le fun B _ => iSup_le fun _ => inf_le_left
  have hmem_g : ∀ (B : Subgroup G), B ≤ A → E3.mQuot A B ≤ 1 →
      V ⊓ Subgroup.centralizer (B : Set G) ≤ gammaOneBar V A := by
    intro B hBA hB
    rw [gammaOneBar]
    exact le_iSup₂_of_le B hBA (le_iSup_of_le hB le_rfl)
  suffices ∃ H : Subgroup G, H ≤ gammaOneBar V A ∧ H.relIndex V ≤ 2 by
    obtain ⟨H, hH, hHV⟩ := this
    exact (Subgroup.relIndex_le_of_le_left hH (E3.relIndex_ne_zero' V H)).trans hHV
  by_cases hfix : A ≤ Subgroup.normalizer (W₁ : Set G)
  · have hne : W₁ ≠ W₂ := by
      intro heq
      have h1 : W₁ = ⊥ := by simpa [heq] using hinf
      have : Nat.card W₁ = 1 := by rw [h1]; simp
      omega
    have hfix₂ : A ≤ Subgroup.normalizer (W₂ : Set G) := by
      intro a ha
      rcases hperm a ha with h | h
      · exact conjSubgroup_eq_iff_mem_normalizer.mp h.2
      · exact absurd (h.1.symm.trans (conjSubgroup_eq_iff_mem_normalizer.mpr (hfix ha))).symm hne
    have hB₁ : E3.mQuot A (Subgroup.centralizer (W₁ : Set G) ⊓ A) ≤ 1 := by
      rw [E3.mQuot, Subgroup.inf_relIndex_right]
      exact padicValNat_two_le_one_of_le_two
        (relIndex_centralizer_le_two_of_kleinFour hK₁ hfix hA2)
    have hB₂ : E3.mQuot A (Subgroup.centralizer (W₂ : Set G) ⊓ A) ≤ 1 := by
      rw [E3.mQuot, Subgroup.inf_relIndex_right]
      exact padicValNat_two_le_one_of_le_two
        (relIndex_centralizer_le_two_of_kleinFour hK₂ hfix₂ hA2)
    have hW₁g : W₁ ≤ gammaOneBar V A := by
      refine le_trans ?_ (hmem_g (Subgroup.centralizer (W₁ : Set G) ⊓ A)
        (fun x hx => (Subgroup.mem_inf.mp hx).2) hB₁)
      intro w hw
      refine ⟨hW₁V hw, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro b hb
      exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hb).1 w hw).symm
    have hW₂g : W₂ ≤ gammaOneBar V A := by
      refine le_trans ?_ (hmem_g (Subgroup.centralizer (W₂ : Set G) ⊓ A)
        (fun x hx => (Subgroup.mem_inf.mp hx).2) hB₂)
      intro w hw
      refine ⟨hW₂V hw, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro b hb
      exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hb).1 w hw).symm
    have hVg : V ≤ gammaOneBar V A := by
      calc V = W₁ ⊔ W₂ := hsup.symm
        _ ≤ gammaOneBar V A := sup_le hW₁g hW₂g
    exact ⟨V, hVg, by rw [Subgroup.relIndex_self]; norm_num⟩
  · obtain ⟨s, hsA, hsN⟩ := exists_notMem_of_not_le hfix
    have hsW₁ : conjSubgroup W₁ s = W₂ := by
      rcases hperm s hsA with h | h
      · exact absurd (conjSubgroup_eq_iff_mem_normalizer.mp h.1) hsN
      · exact h.1
    have hsW₂ : conjSubgroup W₂ s = W₁ := by
      rw [← hsW₁, conjSubgroup_conjSubgroup, ← pow_two, hA.2 s hsA, conjSubgroup_one]
    have hne : W₁ ≠ W₂ := by
      intro heq
      have h1 : W₁ = ⊥ := by simpa [heq] using hinf
      have : Nat.card W₁ = 1 := by rw [h1]; simp
      omega
    have hA₀leA : A ⊓ Subgroup.normalizer (W₁ : Set G) ≤ A :=
      fun x hx => (Subgroup.mem_inf.mp hx).1
    have hA₀norm₂ : A ⊓ Subgroup.normalizer (W₁ : Set G) ≤
        Subgroup.normalizer (W₂ : Set G) := by
      intro x hx
      rcases hperm x (Subgroup.mem_inf.mp hx).1 with h | h
      · exact conjSubgroup_eq_iff_mem_normalizer.mp h.2
      · exact absurd (h.1.symm.trans (conjSubgroup_eq_iff_mem_normalizer.mpr
          (Subgroup.mem_inf.mp hx).2)).symm hne
    have hA₀relA : (A ⊓ Subgroup.normalizer (W₁ : Set G)).relIndex A = 2 := by
      have hle := inf_normalizer_relIndex_le_two hA hperm
      have hne1 : (A ⊓ Subgroup.normalizer (W₁ : Set G)).relIndex A ≠ 1 := by
        intro h1
        have hleA : A ≤ A ⊓ Subgroup.normalizer (W₁ : Set G) := Subgroup.relIndex_eq_one.mp h1
        exact hsN (Subgroup.mem_inf.mp (hleA hsA)).2
      have hne0 : (A ⊓ Subgroup.normalizer (W₁ : Set G)).relIndex A ≠ 0 :=
        E3.relIndex_ne_zero' A _
      omega
    have hA₀mQuot : E3.mQuot A (A ⊓ Subgroup.normalizer (W₁ : Set G)) ≤ 1 := by
      rw [E3.mQuot, hA₀relA]
      exact le_of_eq padicValNat_self
    have hC_le_A₀ : A ⊓ Subgroup.centralizer (V : Set G) ≤
        A ⊓ Subgroup.normalizer (W₁ : Set G) := by
      refine fun x hx => ⟨(Subgroup.mem_inf.mp hx).1, ?_⟩
      exact Subgroup.centralizer_le_normalizer (W₁ : Set G)
        (Subgroup.centralizer_le hW₁V (Subgroup.mem_inf.mp hx).2)
    have hCrelA : (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A = 4 := by
      rw [inf_comm, Subgroup.inf_relIndex_right]
      exact h4
    have hCrelA₀ : (A ⊓ Subgroup.centralizer (V : Set G)).relIndex
        (A ⊓ Subgroup.normalizer (W₁ : Set G)) = 2 := by
      have htower := Subgroup.relIndex_mul_relIndex
        (A ⊓ Subgroup.centralizer (V : Set G))
        (A ⊓ Subgroup.normalizer (W₁ : Set G)) A hC_le_A₀ hA₀leA
      rw [hCrelA, hA₀relA] at htower
      omega
    obtain ⟨t, htA₀, htC, htcase⟩ :=
      Subgroup.relIndex_eq_two_iff_exists_notMem_and.mp hCrelA₀
    have htA : t ∈ A := hA₀leA htA₀
    have ht2 : t ^ 2 = 1 := hA.2 t htA
    have hCW₁ : A ⊓ Subgroup.centralizer (W₁ : Set G) =
        A ⊓ Subgroup.centralizer (V : Set G) :=
      centralizer_inf_eq_of_swap hsup hA hsA hsW₁
    have hCW₂ : A ⊓ Subgroup.centralizer (W₂ : Set G) =
        A ⊓ Subgroup.centralizer (V : Set G) :=
      centralizer_inf_eq_of_swap (by rw [sup_comm]; exact hsup) hA hsA hsW₂
    have htN₁ : t ∈ Subgroup.normalizer (W₁ : Set G) := (Subgroup.mem_inf.mp htA₀).2
    have htN₂ : t ∈ Subgroup.normalizer (W₂ : Set G) := hA₀norm₂ htA₀
    have htC₁ : t ∉ Subgroup.centralizer (W₁ : Set G) := by
      intro htc
      exact htC (by rw [← hCW₁]; exact ⟨htA, htc⟩)
    have htC₂ : t ∉ Subgroup.centralizer (W₂ : Set G) := by
      intro htc
      exact htC (by rw [← hCW₂]; exact ⟨htA, htc⟩)
    have hF₁ : Nat.card (W₁ ⊓ Subgroup.centralizer (Subgroup.zpowers t : Set G)
        : Subgroup G) = 2 :=
      card_inf_centralizer_zpowers_eq_two hW₁ ht2 htN₁ htC₁
    have hF₂ : Nat.card (W₂ ⊓ Subgroup.centralizer (Subgroup.zpowers t : Set G)
        : Subgroup G) = 2 :=
      card_inf_centralizer_zpowers_eq_two hW₂ ht2 htN₂ htC₂
    have hFcomm : ∀ x ∈ W₁ ⊓ Subgroup.centralizer (Subgroup.zpowers t : Set G),
        ∀ y ∈ W₂ ⊓ Subgroup.centralizer (Subgroup.zpowers t : Set G), x * y = y * x := by
      intro x hx y hy
      exact Subtype.ext_iff.mp ((hV.1).is_comm.comm
        ⟨x, hW₁V (Subgroup.mem_inf.mp hx).1⟩ ⟨y, hW₂V (Subgroup.mem_inf.mp hy).1⟩)
    have hFinf : (W₁ ⊓ Subgroup.centralizer (Subgroup.zpowers t : Set G)) ⊓
        (W₂ ⊓ Subgroup.centralizer (Subgroup.zpowers t : Set G)) = ⊥ := by
      apply le_antisymm _ bot_le
      intro x hx
      have hxW₁ : x ∈ W₁ := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hx).1).1
      have hxW₂ : x ∈ W₂ := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hx).2).1
      have hx' : x ∈ W₁ ⊓ W₂ := ⟨hxW₁, hxW₂⟩
      rwa [hinf] at hx'
    have hFcard : Nat.card ((W₁ ⊓ Subgroup.centralizer (Subgroup.zpowers t : Set G)) ⊔
        (W₂ ⊓ Subgroup.centralizer (Subgroup.zpowers t : Set G)) : Subgroup G) = 4 := by
      have h := card_sup_of_commute_of_inf_eq_bot _ _ hFcomm hFinf
      rw [hF₁, hF₂] at h
      norm_num at h
      exact h
    have hF₁_le_X : W₁ ⊓ Subgroup.centralizer (Subgroup.zpowers t : Set G) ≤
        V ⊓ Subgroup.centralizer
          ((A ⊓ Subgroup.normalizer (W₁ : Set G) : Subgroup G) : Set G) := by
      intro u hu
      obtain ⟨huW₁, hut⟩ := Subgroup.mem_inf.mp hu
      refine ⟨hW₁V huW₁, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro b hb
      have hut' : t * u = u * t := Subgroup.mem_centralizer_iff.mp hut t (Subgroup.mem_zpowers t)
      have ht2' : t * t = 1 := by rw [← pow_two]; exact ht2
      have hbt : (b * t) * t = b := by rw [mul_assoc, ht2', mul_one]
      rcases htcase b hb with h | h
      · have hbv : (b * t) * u = u * (b * t) :=
          (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp h).2 u (hW₁V huW₁)).symm
        calc b * u = ((b * t) * t) * u := by rw [hbt]
          _ = (b * t) * (t * u) := by group
          _ = (b * t) * (u * t) := by rw [hut']
          _ = ((b * t) * u) * t := by group
          _ = (u * (b * t)) * t := by rw [hbv]
          _ = u * ((b * t) * t) := by group
          _ = u * b := by rw [hbt]
      · exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp h).2 u (hW₁V huW₁)).symm
    have hF₂_le_X : W₂ ⊓ Subgroup.centralizer (Subgroup.zpowers t : Set G) ≤
        V ⊓ Subgroup.centralizer
          ((A ⊓ Subgroup.normalizer (W₁ : Set G) : Subgroup G) : Set G) := by
      intro u hu
      obtain ⟨huW₂, hut⟩ := Subgroup.mem_inf.mp hu
      refine ⟨hW₂V huW₂, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro b hb
      have hut' : t * u = u * t := Subgroup.mem_centralizer_iff.mp hut t (Subgroup.mem_zpowers t)
      have ht2' : t * t = 1 := by rw [← pow_two]; exact ht2
      have hbt : (b * t) * t = b := by rw [mul_assoc, ht2', mul_one]
      rcases htcase b hb with h | h
      · have hbv : (b * t) * u = u * (b * t) :=
          (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp h).2 u (hW₂V huW₂)).symm
        calc b * u = ((b * t) * t) * u := by rw [hbt]
          _ = (b * t) * (t * u) := by group
          _ = (b * t) * (u * t) := by rw [hut']
          _ = ((b * t) * u) * t := by group
          _ = (u * (b * t)) * t := by rw [hbv]
          _ = u * ((b * t) * t) := by group
          _ = u * b := by rw [hbt]
      · exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp h).2 u (hW₂V huW₂)).symm
    have hXge : 4 ≤ Nat.card (V ⊓ Subgroup.centralizer
        ((A ⊓ Subgroup.normalizer (W₁ : Set G) : Subgroup G) : Set G) : Subgroup G) := by
      have hinj := Nat.card_le_card_of_injective
        (Subgroup.inclusion (show ((W₁ ⊓ Subgroup.centralizer (Subgroup.zpowers t : Set G)) ⊔
          (W₂ ⊓ Subgroup.centralizer (Subgroup.zpowers t : Set G)) : Subgroup G) ≤
          V ⊓ Subgroup.centralizer
            ((A ⊓ Subgroup.normalizer (W₁ : Set G) : Subgroup G) : Set G) from
          sup_le hF₁_le_X hF₂_le_X))
        (Subgroup.inclusion_injective _)
      rw [hFcard] at hinj
      exact hinj
    have hXleV : V ⊓ Subgroup.centralizer
        ((A ⊓ Subgroup.normalizer (W₁ : Set G) : Subgroup G) : Set G) ≤ V :=
      fun x hx => (Subgroup.mem_inf.mp hx).1
    have hXrel : (V ⊓ Subgroup.centralizer
        ((A ⊓ Subgroup.normalizer (W₁ : Set G) : Subgroup G) : Set G)).relIndex V ≤ 4 := by
      have h := Subgroup.relIndex_mul_card
        (V ⊓ Subgroup.centralizer ((A ⊓ Subgroup.normalizer (W₁ : Set G) : Subgroup G) : Set G)) V
      rw [inf_eq_left.mpr hXleV, hVcard] at h
      nlinarith [h, hXge]
    have hsC : s ∉ A ⊓ Subgroup.centralizer (V : Set G) := by
      rintro ⟨-, hsV⟩
      have hsN₁ : s ∈ Subgroup.normalizer (W₁ : Set G) :=
        Subgroup.centralizer_le_normalizer (W₁ : Set G) (Subgroup.centralizer_le hW₁V hsV)
      have hconj : conjSubgroup W₁ s = W₁ := conjSubgroup_eq_iff_mem_normalizer.mpr hsN₁
      exact hne (hconj.symm.trans hsW₁)
    have hcommB : ∀ x ∈ A ⊓ Subgroup.centralizer (V : Set G),
        ∀ y ∈ Subgroup.zpowers s, x * y = y * x := by
      intro x hx y hy
      exact Subtype.ext_iff.mp ((hA.1).is_comm.comm
        ⟨x, (Subgroup.mem_inf.mp hx).1⟩ ⟨y, Subgroup.zpowers_le.mpr hsA hy⟩)
    have hCrelB₂ : (A ⊓ Subgroup.centralizer (V : Set G)).relIndex
        ((A ⊓ Subgroup.centralizer (V : Set G)) ⊔ Subgroup.zpowers s : Subgroup G) = 2 := by
      refine Subgroup.relIndex_eq_two_iff_exists_notMem_and.mpr
        ⟨s, Subgroup.mem_sup_right (Subgroup.mem_zpowers s), hsC, ?_⟩
      intro b hb
      obtain ⟨c, hc, d, hd, rfl⟩ := exists_mul_of_mem_sup hcommB hb
      rcases zpowers_eq_pair_of_sq_eq_one (hA.2 s hsA) hd with hd1 | hd1
      · rw [hd1]
        exact Or.inr (by simpa using hc)
      · rw [hd1]
        refine Or.inl ?_
        rw [mul_assoc, ← pow_two, hA.2 s hsA, mul_one]
        exact hc
    have hB₂relA : ((A ⊓ Subgroup.centralizer (V : Set G)) ⊔
        Subgroup.zpowers s : Subgroup G).relIndex A = 2 := by
      have hB₂A : (A ⊓ Subgroup.centralizer (V : Set G)) ⊔ Subgroup.zpowers s ≤ A :=
        sup_le (fun x hx => (Subgroup.mem_inf.mp hx).1) (Subgroup.zpowers_le.mpr hsA)
      have htower := Subgroup.relIndex_mul_relIndex
        (A ⊓ Subgroup.centralizer (V : Set G))
        ((A ⊓ Subgroup.centralizer (V : Set G)) ⊔ Subgroup.zpowers s) A
        (show A ⊓ Subgroup.centralizer (V : Set G) ≤
          (A ⊓ Subgroup.centralizer (V : Set G)) ⊔ Subgroup.zpowers s from
          fun x hx => Subgroup.mem_sup_left hx) hB₂A
      rw [hCrelB₂, hCrelA] at htower
      omega
    have hB₂mQuot : E3.mQuot A ((A ⊓ Subgroup.centralizer (V : Set G)) ⊔
        Subgroup.zpowers s) ≤ 1 := by
      rw [E3.mQuot, hB₂relA]
      exact le_of_eq padicValNat_self
    have hXg : V ⊓ Subgroup.centralizer
        ((A ⊓ Subgroup.normalizer (W₁ : Set G) : Subgroup G) : Set G) ≤ gammaOneBar V A :=
      hmem_g (A ⊓ Subgroup.normalizer (W₁ : Set G)) hA₀leA hA₀mQuot
    have hYg : V ⊓ Subgroup.centralizer
        (((A ⊓ Subgroup.centralizer (V : Set G)) ⊔ Subgroup.zpowers s : Subgroup G) : Set G) ≤
        gammaOneBar V A :=
      hmem_g ((A ⊓ Subgroup.centralizer (V : Set G)) ⊔ Subgroup.zpowers s)
        (sup_le (fun x hx => (Subgroup.mem_inf.mp hx).1) (Subgroup.zpowers_le.mpr hsA)) hB₂mQuot
    have htNc : ∃ w ∈ W₁, w * t ≠ t * w := by
      by_contra h
      apply htC₁
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      by_contra hwt
      exact h ⟨w, hw, hwt⟩
    obtain ⟨w, hwW₁, hwt⟩ := htNc
    have htw : t * w * t⁻¹ ≠ w := fun h => hwt (mul_inv_eq_iff_eq_mul.mp h).symm
    have hss : s * s = 1 := by rw [← pow_two]; exact hA.2 s hsA
    have hss' : s⁻¹ * s⁻¹ = 1 := by rw [← mul_inv_rev, hss, inv_one]
    have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
    have hssgen : ∀ x : G, s * (s * x * s⁻¹) * s⁻¹ = x := by
      intro x
      calc s * (s * x * s⁻¹) * s⁻¹ = (s * s) * x * (s⁻¹ * s⁻¹) := by group
        _ = x := by rw [hss, hss', one_mul, mul_one]
    have hswW₂ : s * w * s⁻¹ ∈ W₂ := by
      have hmem : s * w * s⁻¹ ∈ conjSubgroup W₁ s :=
        mem_conjSubgroup_iff.mpr (by rw [hssgen w]; exact hwW₁)
      rwa [hsW₁] at hmem
    set y : G := w * (s * w * s⁻¹) with hy_def
    have hyV : y ∈ V := by
      rw [hy_def]
      exact V.mul_mem (hW₁V hwW₁) (hW₂V hswW₂)
    have hsys : s * y * s⁻¹ = y := by
      have h1 : s * (w * (s * w * s⁻¹)) * s⁻¹ =
          (s * w * s⁻¹) * (s * (s * w * s⁻¹) * s⁻¹) := by group
      rw [hy_def, h1, hssgen w]
      exact Subtype.ext_iff.mp ((hV.1).is_comm.comm
        ⟨s * w * s⁻¹, hW₂V hswW₂⟩ ⟨w, hW₁V hwW₁⟩)
    have hsy : y ∈ Subgroup.centralizer (Subgroup.zpowers s : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      rcases zpowers_eq_pair_of_sq_eq_one (by rw [pow_two]; exact hss) hu with h1 | h1
      · rw [h1]; simp
      · rw [h1]; exact mul_inv_eq_iff_eq_mul.mp hsys
    have hyY : y ∈ V ⊓ Subgroup.centralizer
        (((A ⊓ Subgroup.centralizer (V : Set G)) ⊔ Subgroup.zpowers s : Subgroup G) : Set G) := by
      refine ⟨hyV, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro b hb
      obtain ⟨c, hc, u, hu, rfl⟩ := exists_mul_of_mem_sup hcommB hb
      have hcy : c * y = y * c :=
        (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2 y hyV).symm
      have huy : u * y = y * u := Subgroup.mem_centralizer_iff.mp hsy u hu
      calc (c * u) * y = c * (u * y) := by group
        _ = c * (y * u) := by rw [huy]
        _ = (c * y) * u := by group
        _ = (y * c) * u := by rw [hcy]
        _ = y * (c * u) := by group
    have hyX : y ∉ V ⊓ Subgroup.centralizer
        ((A ⊓ Subgroup.normalizer (W₁ : Set G) : Subgroup G) : Set G) := by
      rintro ⟨-, hyC⟩
      have hty : t * y * t⁻¹ = y := by
        rw [mul_inv_eq_iff_eq_mul]
        exact Subgroup.mem_centralizer_iff.mp hyC t htA₀
      have hts : t * s = s * t :=
        Subtype.ext_iff.mp ((hA.1).is_comm.comm ⟨t, htA⟩ ⟨s, hsA⟩)
      have hcomm_ts : t * (s * w * s⁻¹) * t⁻¹ = s * (t * w * t⁻¹) * s⁻¹ := by
        have htisi : s⁻¹ * t⁻¹ = t⁻¹ * s⁻¹ := by
          have hc : Commute t s := (commute_iff_eq t s).mpr hts
          exact (hc.inv_left.inv_right.eq).symm
        calc t * (s * w * s⁻¹) * t⁻¹ = (t * s) * w * (s⁻¹ * t⁻¹) := by group
          _ = (s * t) * w * (t⁻¹ * s⁻¹) := by rw [hts, htisi]
          _ = s * (t * w * t⁻¹) * s⁻¹ := by group
      have hcomp : t * y * t⁻¹ = (t * w * t⁻¹) * (s * (t * w * t⁻¹) * s⁻¹) := by
        rw [hy_def]
        calc t * (w * (s * w * s⁻¹)) * t⁻¹
            = (t * w * t⁻¹) * (t * (s * w * s⁻¹) * t⁻¹) := by group
          _ = (t * w * t⁻¹) * (s * (t * w * t⁻¹) * s⁻¹) := by rw [hcomm_ts]
      have h1 : t * w * t⁻¹ ∈ W₁ := mem_conjSubgroup_iff.mp
        (by rw [conjSubgroup_eq_iff_mem_normalizer.mpr htN₁]; exact hwW₁)
      have h2 : s * (t * w * t⁻¹) * s⁻¹ ∈ W₂ := by
        have hmem : s * (t * w * t⁻¹) * s⁻¹ ∈ conjSubgroup W₁ s :=
          mem_conjSubgroup_iff.mpr (by rw [hssgen (t * w * t⁻¹)]; exact h1)
        rwa [hsW₁] at hmem
      have heq : (t * w * t⁻¹) * (s * (t * w * t⁻¹) * s⁻¹) = w * (s * w * s⁻¹) := by
        rw [← hcomp, hty, hy_def]
      exact htw ((mul_eq_mul_iff hinf h1 h2 hwW₁ hswW₂).mp heq).1
    let H : Subgroup G := (V ⊓ Subgroup.centralizer
        ((A ⊓ Subgroup.normalizer (W₁ : Set G) : Subgroup G) : Set G)) ⊔
        (V ⊓ Subgroup.centralizer
          (((A ⊓ Subgroup.centralizer (V : Set G)) ⊔ Subgroup.zpowers s : Subgroup G) : Set G))
    have hXltH : V ⊓ Subgroup.centralizer
        ((A ⊓ Subgroup.normalizer (W₁ : Set G) : Subgroup G) : Set G) < H := by
      refine lt_of_le_of_ne (fun x hx => Subgroup.mem_sup_left hx) ?_
      intro heq
      exact hyX (heq.symm ▸ (Subgroup.mem_sup_right hyY : y ∈ H))
    have hHleV : H ≤ V := sup_le hXleV (fun x hx => (Subgroup.mem_inf.mp hx).1)
    refine ⟨H, sup_le hXg hYg, ?_⟩
    have htowerH := Subgroup.relIndex_mul_relIndex
      (V ⊓ Subgroup.centralizer
        ((A ⊓ Subgroup.normalizer (W₁ : Set G) : Subgroup G) : Set G)) H V
      (show V ⊓ Subgroup.centralizer
          ((A ⊓ Subgroup.normalizer (W₁ : Set G) : Subgroup G) : Set G) ≤ H from
        fun x hx => Subgroup.mem_sup_left hx) hHleV
    have hXrelH_ne : (V ⊓ Subgroup.centralizer
        ((A ⊓ Subgroup.normalizer (W₁ : Set G) : Subgroup G) : Set G)).relIndex H ≠ 1 := by
      intro h1
      exact hXltH.2 (Subgroup.relIndex_eq_one.mp h1)
    have hXrelH_ge : 2 ≤ (V ⊓ Subgroup.centralizer
        ((A ⊓ Subgroup.normalizer (W₁ : Set G) : Subgroup G) : Set G)).relIndex H := by
      have hne0 : (V ⊓ Subgroup.centralizer
          ((A ⊓ Subgroup.normalizer (W₁ : Set G) : Subgroup G) : Set G)).relIndex H ≠ 0 :=
        E3.relIndex_ne_zero' H _
      have hne1 := hXrelH_ne
      omega
    have hsmall : 2 * H.relIndex V ≤ 4 := by
      calc 2 * H.relIndex V ≤ (V ⊓ Subgroup.centralizer
            ((A ⊓ Subgroup.normalizer (W₁ : Set G) : Subgroup G) : Set G)).relIndex H *
            H.relIndex V := Nat.mul_le_mul_right _ hXrelH_ge
        _ = (V ⊓ Subgroup.centralizer
            ((A ⊓ Subgroup.normalizer (W₁ : Set G) : Subgroup G) : Set G)).relIndex V := htowerH
        _ ≤ 4 := hXrel
    omega

private theorem card_V_eq_sixteen {V W₁ W₂ : Subgroup G} (hV : IsElemAbelian 2 V)
    (hsup : W₁ ⊔ W₂ = V) (hinf : W₁ ⊓ W₂ = ⊥) (hW₁ : Nat.card W₁ = 4)
    (hW₂ : Nat.card W₂ = 4) : Nat.card V = 16 := by
  have hW₁V : (W₁ : Set G) ⊆ (V : Set G) := by
    intro y hy
    rw [← hsup]
    exact Subgroup.mem_sup_left hy
  have hW₂V : (W₂ : Set G) ⊆ (V : Set G) := by
    intro y hy
    rw [← hsup]
    exact Subgroup.mem_sup_right hy
  have hcomm : ∀ x ∈ W₁, ∀ y ∈ W₂, x * y = y * x := by
    intro x hx y hy
    exact Subtype.ext_iff.mp ((hV.1).is_comm.comm ⟨x, hW₁V hx⟩ ⟨y, hW₂V hy⟩)
  have h := card_sup_of_commute_of_inf_eq_bot W₁ W₂ hcomm hinf
  rw [hW₁, hW₂] at h
  rw [← hsup, h]

private theorem sup_eq_V_of_card_four {V W₂ U' : Subgroup G} (hV : IsElemAbelian 2 V)
    (hW₂V : W₂ ≤ V) (hcardV : Nat.card V = 16) (hW₂ : Nat.card W₂ = 4) (hU'V : U' ≤ V)
    (hU' : Nat.card U' = 4) (hinf' : U' ⊓ W₂ = ⊥) : U' ⊔ W₂ = V := by
  have hcomm : ∀ x ∈ U', ∀ y ∈ W₂, x * y = y * x := by
    intro x hx y hy
    exact Subtype.ext_iff.mp ((hV.1).is_comm.comm ⟨x, hU'V hx⟩ ⟨y, hW₂V hy⟩)
  have hcard : Nat.card (U' ⊔ W₂ : Subgroup G) = 16 := by
    have h := card_sup_of_commute_of_inf_eq_bot U' W₂ hcomm hinf'
    rw [hU', hW₂] at h
    rw [h]
  exact Subgroup.eq_of_le_of_card_ge (sup_le hU'V hW₂V)
    (le_of_eq (by rw [hcardV, hcard]))

private noncomputable def graphPt (W₂ U' : Subgroup G) (w : G) : G := by
  classical
  exact if h : ∃ t, t ∈ W₂ ∧ w * t ∈ U' then h.choose else 1

private theorem graphPt_mem {W₂ U' : Subgroup G} {w : G}
    (h : ∃ t, t ∈ W₂ ∧ w * t ∈ U') : graphPt W₂ U' w ∈ W₂ := by
  unfold graphPt
  rw [dif_pos h]
  exact (Exists.choose_spec h).1

private theorem graphPt_spec {W₂ U' : Subgroup G} {w : G}
    (h : ∃ t, t ∈ W₂ ∧ w * t ∈ U') : w * graphPt W₂ U' w ∈ U' := by
  unfold graphPt
  rw [dif_pos h]
  exact (Exists.choose_spec h).2

private theorem exists_graphPt {V W₁ W₂ U' : Subgroup G} (hV : IsElemAbelian 2 V)
    (hU'V : U' ≤ V) (hW₂V : W₂ ≤ V) (hsup' : U' ⊔ W₂ = V) (hW₁V : W₁ ≤ V) {w : G}
    (hw : w ∈ W₁) : ∃ t, t ∈ W₂ ∧ w * t ∈ U' := by
  have hcomm : ∀ x ∈ U', ∀ y ∈ W₂, x * y = y * x := by
    intro x hx y hy
    exact Subtype.ext_iff.mp ((hV.1).is_comm.comm ⟨x, hU'V hx⟩ ⟨y, hW₂V hy⟩)
  have hwV : w ∈ V := hW₁V hw
  rw [← hsup'] at hwV
  obtain ⟨u, hu, y, hy, huy⟩ := exists_mul_of_mem_sup (W₁ := U') (W₂ := W₂) hcomm hwV
  refine ⟨y⁻¹, W₂.inv_mem hy, ?_⟩
  rw [← huy]
  simpa using hu

private theorem graphPt_ne_one {W₁ W₂ U' : Subgroup G} (hinf' : U' ⊓ W₁ = ⊥) {w : G}
    (hw : w ∈ W₁) (hw1 : w ≠ 1) (h : ∃ t, t ∈ W₂ ∧ w * t ∈ U') :
    graphPt W₂ U' w ≠ 1 := by
  intro hgt
  have hspec := graphPt_spec h
  rw [hgt, mul_one] at hspec
  have : w ∈ U' ⊓ W₁ := ⟨hspec, hw⟩
  rw [hinf'] at this
  exact hw1 (Subgroup.mem_bot.mp this)

private theorem graphPt_ne_of_ne {V W₁ W₂ U' : Subgroup G} (hV : IsElemAbelian 2 V)
    (hU'V : U' ≤ V) (hW₁V : W₁ ≤ V) (hW₂V : W₂ ≤ V) (hinf' : U' ⊓ W₁ = ⊥)
    (hsup' : U' ⊔ W₂ = V) {a b : G} (ha : a ∈ W₁) (hb : b ∈ W₁) (hab : a ≠ b) :
    graphPt W₂ U' a ≠ graphPt W₂ U' b := by
  intro heq
  have haex := exists_graphPt hV hU'V hW₂V hsup' hW₁V ha
  have hbex := exists_graphPt hV hU'V hW₂V hsup' hW₁V hb
  have h1 : a * graphPt W₂ U' a ∈ U' := graphPt_spec haex
  have h2 : b * graphPt W₂ U' b ∈ U' := graphPt_spec hbex
  rw [heq] at h1
  have hy : graphPt W₂ U' b ∈ W₂ := graphPt_mem hbex
  have hab' : a⁻¹ * b ∈ W₁ := W₁.mul_mem (W₁.inv_mem ha) hb
  have hmem : a⁻¹ * b ∈ U' ⊓ W₁ := by
    refine ⟨?_, hab'⟩
    have hdiff : (a * graphPt W₂ U' b)⁻¹ * (b * graphPt W₂ U' b) ∈ U' :=
      U'.mul_mem (U'.inv_mem h1) h2
    have hcomm : (a⁻¹ * b) * graphPt W₂ U' b = graphPt W₂ U' b * (a⁻¹ * b) :=
      Subtype.ext_iff.mp ((hV.1).is_comm.comm ⟨a⁻¹ * b, hW₁V hab'⟩
        ⟨graphPt W₂ U' b, hW₂V hy⟩)
    have heq2 : (a * graphPt W₂ U' b)⁻¹ * (b * graphPt W₂ U' b) = a⁻¹ * b := by
      calc (a * graphPt W₂ U' b)⁻¹ * (b * graphPt W₂ U' b)
          = (graphPt W₂ U' b)⁻¹ * (a⁻¹ * b) * graphPt W₂ U' b := by group
        _ = (graphPt W₂ U' b)⁻¹ * ((a⁻¹ * b) * graphPt W₂ U' b) := by group
        _ = (graphPt W₂ U' b)⁻¹ * (graphPt W₂ U' b * (a⁻¹ * b)) := by rw [hcomm]
        _ = a⁻¹ * b := by group
    rwa [heq2] at hdiff
  rw [hinf'] at hmem
  exact hab (inv_mul_eq_one.mp (Subgroup.mem_bot.mp hmem))

private theorem conjSubgroup_V_eq {V W₁ W₂ E : Subgroup G} (hsup : W₁ ⊔ W₂ = V)
    (hE₁ : ∀ e ∈ E, conjSubgroup W₁ e = W₁) (hE₂ : ∀ e ∈ E, conjSubgroup W₂ e = W₂)
    {e : G} (he : e ∈ E) : conjSubgroup V e = V := by
  rw [← hsup]
  show conjSubgroup (W₁ ⊔ W₂ : Subgroup G) e = W₁ ⊔ W₂
  rw [conjSubgroup, Subgroup.map_sup, ← conjSubgroup, ← conjSubgroup, hE₁ e he, hE₂ e he]

private theorem conjSubgroup_U_inf_eq_bot {Wᵢ E U : Subgroup G}
    (hEᵢ : ∀ e ∈ E, conjSubgroup Wᵢ e = Wᵢ) (hUᵢ : U ⊓ Wᵢ = ⊥) {e : G} (he : e ∈ E) :
    conjSubgroup U e⁻¹ ⊓ Wᵢ = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  rw [Subgroup.mem_bot]
  obtain ⟨hxU, hxW⟩ := Subgroup.mem_inf.mp hx
  have hxU' : e⁻¹ * x * e ∈ U := by simpa using mem_conjSubgroup_iff.mp hxU
  have hxW' : e⁻¹ * x * e ∈ Wᵢ := by
    have : x ∈ conjSubgroup Wᵢ e⁻¹ := by
      rw [hEᵢ e⁻¹ (E.inv_mem he)]
      exact hxW
    simpa using mem_conjSubgroup_iff.mp this
  have hbot : e⁻¹ * x * e ∈ U ⊓ Wᵢ := ⟨hxU', hxW'⟩
  rw [hUᵢ] at hbot
  have h1 : e⁻¹ * x * e = 1 := Subgroup.mem_bot.mp hbot
  have := congrArg (fun t => e * t * e⁻¹) h1
  simpa [mul_assoc] using this

private theorem conjSubgroup_U_props {V W₁ W₂ E U : Subgroup G} (hV : IsElemAbelian 2 V)
    (hsup : W₁ ⊔ W₂ = V) (hE₁ : ∀ e ∈ E, conjSubgroup W₁ e = W₁)
    (hE₂ : ∀ e ∈ E, conjSubgroup W₂ e = W₂) (hUV : U ≤ V) (hU : Nat.card U = 4)
    (hU₁ : U ⊓ W₁ = ⊥) (hU₂ : U ⊓ W₂ = ⊥) {e : G} (he : e ∈ E) :
    conjSubgroup U e⁻¹ ≤ V ∧ Nat.card (conjSubgroup U e⁻¹) = 4 ∧
      conjSubgroup U e⁻¹ ⊓ W₁ = ⊥ ∧ conjSubgroup U e⁻¹ ⊓ W₂ = ⊥ := by
  have he' : e⁻¹ ∈ E := E.inv_mem he
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine (E3.conjSubgroup_mono_left e⁻¹ hUV).trans ?_
    rw [conjSubgroup_V_eq hsup hE₁ hE₂ he']
  · rw [E3.card_conjSubgroup, hU]
  · exact conjSubgroup_U_inf_eq_bot (Wᵢ := W₁) hE₁ hU₁ he
  · exact conjSubgroup_U_inf_eq_bot (Wᵢ := W₂) hE₂ hU₂ he

private theorem complement_rigidity {W₁ W₂ U' U'' : Subgroup G} (hinf : W₁ ⊓ W₂ = ⊥)
    (hU' : Nat.card U' = 4) (hU'' : Nat.card U'' = 4)
    {a b y₁ y₂ : G} (ha : a ∈ W₁) (hb : b ∈ W₁) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b)
    (hy₁ : y₁ ∈ W₂) (hy₂ : y₂ ∈ W₂)
    (hmem₁ : a * y₁ ∈ U' ⊓ U'') (hmem₂ : b * y₂ ∈ U' ⊓ U'') : U' = U'' := by
  have hne1a : a * y₁ ≠ 1 := by
    intro h
    have haeq : a = y₁⁻¹ := by
      calc a = a * y₁ * y₁⁻¹ := by group
        _ = 1 * y₁⁻¹ := by rw [h]
        _ = y₁⁻¹ := by rw [one_mul]
    have : a ∈ W₁ ⊓ W₂ := ⟨ha, haeq.symm ▸ W₂.inv_mem hy₁⟩
    rw [hinf] at this
    exact ha1 (Subgroup.mem_bot.mp this)
  have hne1b : b * y₂ ≠ 1 := by
    intro h
    have hbeq : b = y₂⁻¹ := by
      calc b = b * y₂ * y₂⁻¹ := by group
        _ = 1 * y₂⁻¹ := by rw [h]
        _ = y₂⁻¹ := by rw [one_mul]
    have : b ∈ W₁ ⊓ W₂ := ⟨hb, hbeq.symm ▸ W₂.inv_mem hy₂⟩
    rw [hinf] at this
    exact hb1 (Subgroup.mem_bot.mp this)
  have hneab : a * y₁ ≠ b * y₂ := by
    intro h
    exact hab ((mul_eq_mul_iff hinf ha hy₁ hb hy₂).mp h).1
  have h3 : 3 ≤ Nat.card (U' ⊓ U'' : Subgroup G) := by
    let g : Fin 3 → ↥(U' ⊓ U'') :=
      Fin.cases (⟨1, U'.one_mem, U''.one_mem⟩ : ↥(U' ⊓ U''))
        (Fin.cases (⟨a * y₁, hmem₁⟩ : ↥(U' ⊓ U'')) (fun _ => ⟨b * y₂, hmem₂⟩))
    have hf : Function.Injective g := by
      intro i j hij
      fin_cases i <;> fin_cases j
      all_goals first
        | rfl
        | (exfalso; exact hne1a (Subtype.ext_iff.mp hij))
        | (exfalso; exact hne1a (Subtype.ext_iff.mp hij).symm)
        | (exfalso; exact hne1b (Subtype.ext_iff.mp hij))
        | (exfalso; exact hne1b (Subtype.ext_iff.mp hij).symm)
        | (exfalso; exact hneab (Subtype.ext_iff.mp hij))
        | (exfalso; exact hneab (Subtype.ext_iff.mp hij).symm)
    have := Nat.card_le_card_of_injective g hf
    simpa using this
  have hdvd : Nat.card (U' ⊓ U'' : Subgroup G) ∣ 4 := by
    have h := Subgroup.relIndex_mul_card (U' ⊓ U'') U'
    rw [inf_eq_left.mpr inf_le_left, hU'] at h
    exact ⟨(U' ⊓ U'').relIndex U', by rw [mul_comm]; exact h.symm⟩
  have hI : Nat.card (U' ⊓ U'' : Subgroup G) = 4 := by
    have hle : Nat.card (U' ⊓ U'' : Subgroup G) ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    rcases Nat.lt_or_eq_of_le hle with hlt | heq
    · have h3' : Nat.card (U' ⊓ U'' : Subgroup G) = 3 := by omega
      rw [h3'] at hdvd
      norm_num at hdvd
    · exact heq
  have hIeqU' : U' ⊓ U'' = U' := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hI, hU'])
  have hIeqU'' : U' ⊓ U'' = U'' := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hI, hU''])
  exact hIeqU'.symm.trans hIeqU''

theorem s1667_relIndex_normalizer_le_three {V W₁ W₂ E U : Subgroup G} (hV : IsElemAbelian 2 V)
    (hsup : W₁ ⊔ W₂ = V) (hinf : W₁ ⊓ W₂ = ⊥) (hW₁ : Nat.card W₁ = 4) (hW₂ : Nat.card W₂ = 4)
    (hE : IsPGroup 3 E) (hE₁ : ∀ e ∈ E, conjSubgroup W₁ e = W₁)
    (hE₂ : ∀ e ∈ E, conjSubgroup W₂ e = W₂) (hUV : U ≤ V) (hU : Nat.card U = 4)
    (hU₁ : U ⊓ W₁ = ⊥) (hU₂ : U ⊓ W₂ = ⊥) :
    (normalizer (U : Set G)).relIndex E ≤ 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hW₁V : W₁ ≤ V := by rw [← hsup]; exact le_sup_left
  have hW₂V : W₂ ≤ V := by rw [← hsup]; exact le_sup_right
  have hcardV : Nat.card V = 16 := card_V_eq_sixteen hV hsup hinf hW₁ hW₂
  haveI : IsKleinFour ↥W₁ := isKleinFour_of_card_four_of_sq hW₁ fun t ht => hV.2 t (hW₁V ht)
  haveI : IsKleinFour ↥W₂ := isKleinFour_of_card_four_of_sq hW₂ fun t ht => hV.2 t (hW₂V ht)
  let X : Type := {x : ↥W₂ // x ≠ 1}
  have hXcard : Nat.card X = 3 := CFSG.kleinFour_nonidentity_card ↥W₂
  have hsub1 : Nat.card {x : ↥W₁ // x ≠ 1} = 3 := CFSG.kleinFour_nonidentity_card ↥W₁
  haveI : Fintype {x : ↥W₁ // x ≠ 1} := Fintype.ofFinite _
  haveI : Nontrivial {x : ↥W₁ // x ≠ 1} := by
    rw [← Fintype.one_lt_card_iff_nontrivial, ← Nat.card_eq_fintype_card, hsub1]
    norm_num
  obtain ⟨xA, xB, hxy⟩ := exists_pair_ne {x : ↥W₁ // x ≠ 1}
  let A : G := (xA.1 : G)
  let B : G := (xB.1 : G)
  have hA : A ∈ W₁ := xA.1.2
  have hB : B ∈ W₁ := xB.1.2
  have hA1 : A ≠ 1 := fun h => xA.2 (Subtype.ext h)
  have hB1 : B ≠ 1 := fun h => xB.2 (Subtype.ext h)
  have hAB : A ≠ B := fun h => hxy (Subtype.ext (Subtype.ext h))
  let Ue : ↥E → Subgroup G := fun e => conjSubgroup U ((e : G)⁻¹)
  have hUp : ∀ e : ↥E, Ue e ≤ V ∧ Nat.card (Ue e) = 4 ∧ Ue e ⊓ W₁ = ⊥ ∧ Ue e ⊓ W₂ = ⊥ :=
    fun e => conjSubgroup_U_props hV hsup hE₁ hE₂ hUV hU hU₁ hU₂ e.2
  have hsupUe : ∀ e : ↥E, Ue e ⊔ W₂ = V := fun e =>
    sup_eq_V_of_card_four hV hW₂V hcardV hW₂ (hUp e).1 (hUp e).2.1 (hUp e).2.2.2
  have hAex : ∀ e : ↥E, ∃ t, t ∈ W₂ ∧ A * t ∈ Ue e := fun e =>
    exists_graphPt hV (hUp e).1 hW₂V (hsupUe e) hW₁V hA
  have hBex : ∀ e : ↥E, ∃ t, t ∈ W₂ ∧ B * t ∈ Ue e := fun e =>
    exists_graphPt hV (hUp e).1 hW₂V (hsupUe e) hW₁V hB
  let N : Subgroup ↥E := (Subgroup.normalizer (U : Set G)).subgroupOf E
  change N.index ≤ 3
  let f : ↥E → X × X := fun e =>
    (⟨⟨graphPt W₂ (Ue e) A, graphPt_mem (hAex e)⟩,
      fun h => graphPt_ne_one (hUp e).2.2.1 hA hA1 (hAex e) (congrArg Subtype.val h)⟩,
     ⟨⟨graphPt W₂ (Ue e) B, graphPt_mem (hBex e)⟩,
      fun h => graphPt_ne_one (hUp e).2.2.1 hB hB1 (hBex e) (congrArg Subtype.val h)⟩)
  have hUe_eq : ∀ e e' : ↥E, (e⁻¹ * e' : ↥E) ∈ N → Ue e = Ue e' := by
    intro e e' hmem
    have hmemG : ((e⁻¹ * e' : ↥E) : G) ∈ Subgroup.normalizer (U : Set G) :=
      Subgroup.mem_subgroupOf.mp hmem
    have hmemG' : (e : G)⁻¹ * (e' : G) ∈ Subgroup.normalizer (U : Set G) := by
      simpa using hmemG
    have hconj : conjSubgroup (conjSubgroup U (e : G)⁻¹) (e' : G) = U := by
      rw [conjSubgroup_conjSubgroup]
      exact conjSubgroup_eq_iff_mem_normalizer.mpr hmemG'
    have h2 : conjSubgroup (conjSubgroup U (e' : G)⁻¹) (e' : G) = U := by
      rw [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
    have hinj : Function.Injective (fun S : Subgroup G => conjSubgroup S (e' : G)) := by
      intro S T hST
      have hh := congrArg (fun R : Subgroup G => conjSubgroup R (e' : G)⁻¹) hST
      simpa [conjSubgroup_conjSubgroup, conjSubgroup_one] using hh
    exact hinj (hconj.trans h2.symm)
  have hfwell : ∀ e e' : ↥E, QuotientGroup.leftRel N e e' → f e = f e' := by
    intro e e' hrel
    have hUe := hUe_eq e e' (QuotientGroup.leftRel_apply.mp hrel)
    have hvA : graphPt W₂ (Ue e) A = graphPt W₂ (Ue e') A := by rw [hUe]
    have hvB : graphPt W₂ (Ue e) B = graphPt W₂ (Ue e') B := by rw [hUe]
    dsimp only [f]
    apply Prod.ext
    · apply Subtype.ext
      apply Subtype.ext
      exact hvA
    · apply Subtype.ext
      apply Subtype.ext
      exact hvB
  let Φ : (↥E ⧸ N) → X × X := Quotient.lift f hfwell
  have hΦinj : Function.Injective Φ := by
    intro q₁ q₂ hq
    revert hq
    refine Quotient.inductionOn₂ q₁ q₂ (fun e e' => ?_)
    intro hq'
    change f e = f e' at hq'
    have hAy : graphPt W₂ (Ue e) A =
        graphPt W₂ (Ue e') A := by
      have h1 := congrArg (fun p : X × X => (p.1 : X)) hq'
      have h2 := congrArg (fun x : X => (x : ↥W₂)) h1
      exact congrArg Subtype.val h2
    have hBy : graphPt W₂ (Ue e) B =
        graphPt W₂ (Ue e') B := by
      have h1 := congrArg (fun p : X × X => (p.2 : X)) hq'
      have h2 := congrArg (fun x : X => (x : ↥W₂)) h1
      exact congrArg Subtype.val h2
    have hmA : A * graphPt W₂ (Ue e) A ∈ Ue e ⊓ Ue e' := by
      refine ⟨graphPt_spec (hAex e), ?_⟩
      rw [hAy]
      exact graphPt_spec (hAex e')
    have hmB : B * graphPt W₂ (Ue e) B ∈ Ue e ⊓ Ue e' := by
      refine ⟨graphPt_spec (hBex e), ?_⟩
      rw [hBy]
      exact graphPt_spec (hBex e')
    have hUeeq : Ue e = Ue e' :=
      complement_rigidity hinf (hUp e).2.1 (hUp e').2.1 hA hB hA1 hB1 hAB
        (graphPt_mem (hAex e)) (graphPt_mem (hBex e)) hmA hmB
    have hconj : conjSubgroup U ((e : G)⁻¹ * (e' : G)) = U := by
      have hUeeq' : conjSubgroup U (e : G)⁻¹ = conjSubgroup U (e' : G)⁻¹ := hUeeq
      rw [← conjSubgroup_conjSubgroup U (e : G)⁻¹ (e' : G), hUeeq',
        conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
    have hmemN : (e⁻¹ * e' : ↥E) ∈ N := by
      rw [Subgroup.mem_subgroupOf]
      exact conjSubgroup_eq_iff_mem_normalizer.mp hconj
    exact Quotient.sound' (QuotientGroup.leftRel_apply.mpr hmemN)
  have hdiag : ∀ q : (↥E ⧸ N), (Φ q).1 ≠ (Φ q).2 := by
    intro q
    induction q using Quotient.inductionOn with
    | h e =>
      dsimp only [Φ, f]
      intro h
      have h1 := congrArg (fun x : X => (x : ↥W₂)) h
      have h2 := congrArg Subtype.val h1
      exact graphPt_ne_of_ne hV (hUp e).1 hW₁V hW₂V (hUp e).2.2.1 (hsupUe e) hA hB hAB h2
  have hN9 : N.index ≤ 9 := by
    rw [Subgroup.index_eq_card]
    calc Nat.card (↥E ⧸ N) ≤ Nat.card (X × X) := Nat.card_le_card_of_injective Φ hΦinj
      _ = 9 := by rw [Nat.card_prod, hXcard]
  obtain ⟨n, hn⟩ := hE.index N
  have hle2 : n ≤ 2 := by
    by_contra h
    have h3 : 3 ^ 3 ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [hn] at hN9
    norm_num at h3
    omega
  interval_cases n
  · rw [hn]; norm_num
  · rw [hn]; norm_num
  · exfalso
    have h9 : N.index = 9 := by rw [hn]; norm_num
    have hcard9 : Nat.card (X × X) ≤ Nat.card (↥E ⧸ N) := by
      have h1 : Nat.card (↥E ⧸ N) = 9 := by rw [← Subgroup.index_eq_card]; exact h9
      rw [h1, Nat.card_prod, hXcard]
    have hbij := hΦinj.bijective_of_nat_card_le hcard9
    haveI : Fintype X := Fintype.ofFinite X
    haveI : Nonempty X := Fintype.card_pos_iff.mp (by
      rw [← Nat.card_eq_fintype_card, hXcard]
      decide)
    obtain ⟨q, hq⟩ := hbij.2 (Classical.arbitrary X, Classical.arbitrary X)
    exact hdiag q (by rw [hq])

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
