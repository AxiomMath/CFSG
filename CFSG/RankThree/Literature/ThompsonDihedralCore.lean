module

public import Mathlib.GroupTheory.Nilpotent
public import CFSG.GroupTheory.OddInversion

public section

namespace CFSG.RankThree.Literature.Thompson534

open Subgroup CFSG.OddInversion

variable {G : Type*} [Group G]

theorem mem_normalizer_of_involutive {H : Subgroup G} {s : G} (hs : s * s = 1)
    (h : ∀ x ∈ H, s * x * s⁻¹ ∈ H) : s ∈ normalizer (H : Set G) := by
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  rw [mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  have := h _ hx
  have hx' : s * (s * x * s⁻¹) * s⁻¹ = x := by
    calc s * (s * x * s⁻¹) * s⁻¹ = (s * s) * x * (s * s)⁻¹ := by group
      _ = x := by rw [hs, inv_one, one_mul, mul_one]
  rwa [hx'] at this

theorem conj_mem_of_mem_normalizer' {H : Subgroup G} {s x : G}
    (hs : s ∈ normalizer (H : Set G)) (hx : x ∈ H) : s * x * s⁻¹ ∈ H :=
  (mem_normalizer_iff.mp hs x).mp hx

theorem eq_one_of_eq_inv {A : Subgroup G} (hA : Odd (Nat.card A)) {x : G} (hx : x ∈ A)
    (h : x = x⁻¹) : x = 1 := by
  have h2 : x ^ 2 = (1 : G) ^ 2 := by
    rw [one_pow, sq]
    nth_rewrite 2 [h]
    exact mul_inv_cancel x
  exact sq_injOn hA hx A.one_mem h2

theorem conj_mod_trivial_or_inv {A M T : Subgroup G} (hAodd : Odd (Nat.card A)) (hMA : M ≤ A)
    (hMn : A ≤ normalizer (M : Set G)) (hTA : T ≤ normalizer (A : Set G))
    (hTM : T ≤ normalizer (M : Set G)) (hTcomm : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s)
    (hmax : ∀ H : Subgroup G, M ≤ H → H ≤ A → T ≤ normalizer (H : Set G) → H = M ∨ H = A)
    {t : G} (ht : t ∈ T) (ht2 : t * t = 1) :
    (∀ x ∈ A, x⁻¹ * (t * x * t⁻¹) ∈ M) ∨ (∀ x ∈ A, x * (t * x * t⁻¹) ∈ M) := by
  have hnA : ∀ a ∈ A, ∀ m ∈ M, a * m * a⁻¹ ∈ M := fun a ha m hm =>
    conj_mem_of_mem_normalizer' (hMn ha) hm
  have htA : ∀ a ∈ A, t * a * t⁻¹ ∈ A := fun a ha => conj_mem_of_mem_normalizer' (hTA ht) ha
  have htM : ∀ m ∈ M, t * m * t⁻¹ ∈ M := fun m hm => conj_mem_of_mem_normalizer' (hTM ht) hm
  let C : Subgroup G :=
    { carrier := {x | x ∈ A ∧ x⁻¹ * (t * x * t⁻¹) ∈ M}
      one_mem' := ⟨A.one_mem, by simp [M.one_mem]⟩
      mul_mem' := by
        rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
        refine ⟨A.mul_mem hx hy, ?_⟩
        have h1 := hnA y⁻¹ (A.inv_mem hy) _ hx'
        have : (x * y)⁻¹ * (t * (x * y) * t⁻¹) =
            (y⁻¹ * (x⁻¹ * (t * x * t⁻¹)) * y⁻¹⁻¹) * (y⁻¹ * (t * y * t⁻¹)) := by group
        rw [this]
        exact M.mul_mem h1 hy'
      inv_mem' := by
        rintro x ⟨hx, hx'⟩
        refine ⟨A.inv_mem hx, ?_⟩
        have h1 := hnA x hx _ (M.inv_mem hx')
        have : x⁻¹⁻¹ * (t * x⁻¹ * t⁻¹) = x * (x⁻¹ * (t * x * t⁻¹))⁻¹ * x⁻¹ := by group
        rw [this]
        exact h1 }
  have hMC : M ≤ C := fun m hm => ⟨hMA hm, M.mul_mem (M.inv_mem hm) (htM m hm)⟩
  have hCA : C ≤ A := fun x hx => hx.1
  have hTC : T ≤ normalizer (C : Set G) := by
    intro s hs
    have key : ∀ s ∈ T, ∀ x, x ∈ C → s * x * s⁻¹ ∈ C := by
      intro s hs x ⟨hx, hx'⟩
      refine ⟨conj_mem_of_mem_normalizer' (hTA hs) hx, ?_⟩
      have hst : t * s = s * t := (hTcomm s hs t ht).symm
      have : (s * x * s⁻¹)⁻¹ * (t * (s * x * s⁻¹) * t⁻¹) =
          s * (x⁻¹ * (t * x * t⁻¹)) * s⁻¹ := by
        calc (s * x * s⁻¹)⁻¹ * (t * (s * x * s⁻¹) * t⁻¹)
            = s * x⁻¹ * s⁻¹ * (t * s) * x * (t * s)⁻¹ := by group
          _ = s * x⁻¹ * s⁻¹ * (s * t) * x * (s * t)⁻¹ := by rw [hst]
          _ = s * (x⁻¹ * (t * x * t⁻¹)) * s⁻¹ := by group
      rw [this]
      exact conj_mem_of_mem_normalizer' (hTM hs) hx'
    rw [mem_normalizer_iff]
    intro x
    refine ⟨key s hs x, fun h => ?_⟩
    have := key s⁻¹ (T.inv_mem hs) _ h
    simpa [mul_assoc] using this
  rcases hmax C hMC hCA hTC with hCM | hCA'
  ·
    right
    by_cases ht1 : t = 1
    · intro x hx
      have hxC : x ∈ C := ⟨hx, by simp [ht1, M.one_mem]⟩
      rw [hCM] at hxC
      simpa [ht1] using M.mul_mem hxC hxC
    have hord : orderOf t = 2 := orderOf_eq_prime (by rw [sq]; exact ht2) ht1
    intro u hu
    obtain ⟨⟨c, j⟩, ⟨hc, hj⟩, rfl⟩ := (fixed_mul_inverted_bijOn hAodd hord (hTA ht)).surjOn hu
    have hcA : c ∈ A := (mem_inf.mp hc).1
    have hct : t * c * t⁻¹ = c := by
      have := mem_centralizer_singleton_iff.mp (mem_inf.mp hc).2
      rw [← this]
      group
    have hcM : c ∈ M := by
      have : c ∈ C := ⟨hcA, by rw [hct, inv_mul_cancel]; exact M.one_mem⟩
      rwa [hCM] at this
    have hjt : t * j * t⁻¹ = j⁻¹ := hj.2
    have : c * j * (t * (c * j) * t⁻¹) = c * (j * c * j⁻¹) := by
      calc c * j * (t * (c * j) * t⁻¹) = c * j * (t * c * t⁻¹) * (t * j * t⁻¹) := by group
        _ = c * (j * c * j⁻¹) := by rw [hct, hjt]; group
    rw [this]
    exact M.mul_mem hcM (hnA j hj.1 c hcM)
  · left
    intro x hx
    have : x ∈ C := hCA' ▸ hx
    exact this.2

theorem le_normalizer_of_le_of_le {A M T : Subgroup G}
    (hmod : ∀ t ∈ T, (∀ x ∈ A, x⁻¹ * (t * x * t⁻¹) ∈ M) ∨ (∀ x ∈ A, x * (t * x * t⁻¹) ∈ M))
    (hT2 : ∀ t ∈ T, t * t = 1) {H : Subgroup G} (hMH : M ≤ H) (hHA : H ≤ A) :
    T ≤ normalizer (H : Set G) := by
  intro s hs
  refine mem_normalizer_of_involutive (hT2 s hs) fun h hh => ?_
  rcases hmod s hs with h1 | h1
  · have := H.mul_mem hh (hMH (h1 h (hHA hh)))
    simpa [mul_assoc] using this
  · have := H.mul_mem (H.inv_mem hh) (hMH (h1 h (hHA hh)))
    simpa [mul_assoc] using this

theorem relIndex_le_card_of_sup_eq {A M H : Subgroup G} [Finite H] (hMA : M ≤ A) (hHA : H ≤ A)
    (hMn : A ≤ normalizer (M : Set G)) (hsup : M ⊔ H = A) : M.relIndex A ≤ Nat.card H := by
  have hN : (M.subgroupOf A).Normal := (normal_subgroupOf_iff_le_normalizer hMA).mpr hMn
  have htop : H.subgroupOf A ⊔ M.subgroupOf A = ⊤ := by
    rw [← subgroupOf_sup hHA hMA, sup_comm, hsup, subgroupOf_self]
  have h1 : M.relIndex A = (M.subgroupOf A).relIndex (H.subgroupOf A) := by
    calc M.relIndex A = (M.subgroupOf A).index := rfl
      _ = (M.subgroupOf A).relIndex (H.subgroupOf A ⊔ M.subgroupOf A) := by
        rw [htop, relIndex_top_right]
      _ = (M.subgroupOf A).relIndex (H.subgroupOf A) := relIndex_sup_right _ _
  have h2 : Nat.card (H.subgroupOf A) = Nat.card H :=
    Nat.card_congr (subgroupOfEquivOfLe hHA).toEquiv
  have : Finite (H.subgroupOf A) := Finite.of_equiv _ (subgroupOfEquivOfLe hHA).symm.toEquiv
  rw [h1, ← h2]
  exact Nat.le_of_dvd Nat.card_pos (relIndex_dvd_card _ _)

theorem card_prime_of_forall {B : Subgroup G} [Finite B] (hB : B ≠ ⊥)
    (h : ∀ H : Subgroup G, H ≤ B → H = ⊥ ∨ H = B) : (Nat.card B).Prime := by
  have hne : Nat.card B ≠ 1 := by
    intro h1
    exact hB (Subgroup.eq_bot_of_card_eq B h1)
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hne
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := B) q hqd
  have hgne : (g : G) ≠ 1 := by
    intro h1
    have : g = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hg
    exact hq.one_lt.ne' hg.symm
  rcases h (zpowers (g : G)) ((zpowers_le).mpr g.2) with h0 | h0
  · exact absurd ((zpowers_eq_bot).mp h0) hgne
  · have hcard : Nat.card (zpowers (g : G)) = q := by
      rw [Nat.card_zpowers, orderOf_submonoid, hg]
    rw [← h0, hcard]
    exact hq

theorem eq_bot_or_eq_of_card_prime {B : Subgroup G} (hB : (Nat.card B).Prime) {H : Subgroup G}
    (hHB : H ≤ B) : H = ⊥ ∨ H = B := by
  have : Fact (Nat.card B).Prime := ⟨hB⟩
  rcases Subgroup.eq_bot_or_eq_top_of_prime_card (H.subgroupOf B) with h | h
  · left
    rwa [subgroupOf_eq_bot, disjoint_iff, inf_eq_left.mpr hHB] at h
  · right
    rw [subgroupOf_eq_top] at h
    exact le_antisymm hHB h

theorem mem_centralizer_of_le {H : Subgroup G} {s : G} (h : H ≤ centralizer ({s} : Set G)) :
    s ∈ centralizer (H : Set G) := by
  rw [mem_centralizer_iff]
  intro x hx
  exact mem_centralizer_singleton_iff.mp (h hx)

theorem conj_eq_of_mem_centralizer {H : Subgroup G} {s x : G}
    (hs : s ∈ centralizer (H : Set G)) (hx : x ∈ H) : s * x * s⁻¹ = x := by
  have := (mem_centralizer_iff.mp hs) x hx
  rw [← this]
  group

theorem mem_centralizer_of_conj_eq {H : Subgroup G} {s : G} (h : ∀ x ∈ H, s * x * s⁻¹ = x) :
    s ∈ centralizer (H : Set G) := by
  rw [mem_centralizer_iff]
  intro x hx
  have := h x hx
  calc x * s = (s * x * s⁻¹) * s := by rw [this]
    _ = s * x := by group

theorem exists_step [Finite G] {X T : Subgroup G} {n : ℕ}
    (hnil : ∀ H : Subgroup G, H ≤ X → Group.IsNilpotent H) (hXodd : Odd (Nat.card X))
    (hTcomm : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s) (hT2 : ∀ t ∈ T, t * t = 1)
    (hTcard : Nat.card T = 2 ^ (n + 1)) (hTX : T ≤ normalizer (X : Set G))
    (hfaith : T ⊓ centralizer (X : Set G) = ⊥) :
    ∃ (A₁ M : Subgroup G) (I : G),
      A₁ ≤ X ∧ T ≤ normalizer (A₁ : Set G) ∧ (Nat.card A₁).Prime ∧ I ∈ T ∧
      (∀ a ∈ A₁, I * a * I⁻¹ = a⁻¹) ∧ M ≤ X ∧ T ≤ normalizer (M : Set G) ∧
      I ∈ centralizer (M : Set G) ∧ (∀ x ∈ A₁, ∀ y ∈ M, Commute x y) ∧
      Nat.card (T ⊓ centralizer (A₁ : Set G) : Subgroup G) = 2 ^ n ∧
      (∀ s ∈ T, s ∈ centralizer (A₁ : Set G) ∨ s * I ∈ centralizer (A₁ : Set G)) ∧
      T ⊓ centralizer (A₁ : Set G) ⊓ centralizer (M : Set G) = ⊥ := by
  classical
  have hnormbot : T ≤ normalizer ((⊥ : Subgroup G) : Set G) := by
    rw [normalizer_eq_top_iff.mpr inferInstance]
    exact le_top
  let S : Set (Subgroup G) :=
    {B | B ≤ X ∧ T ≤ normalizer (B : Set G) ∧ T ⊓ centralizer (B : Set G) = ⊥}
  obtain ⟨A, ⟨hAX, hTA, hAfaith⟩, hAmin⟩ :=
    (Set.toFinite S).exists_minimal ⟨X, le_rfl, hTX, hfaith⟩
  have hAodd : Odd (Nat.card A) := Odd.of_dvd_nat hXodd (card_dvd_of_le hAX)
  have hTne : T ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hTcard
    have : 2 ≤ 2 ^ (n + 1) := Nat.le_self_pow (Nat.succ_ne_zero n) 2
    omega
  have hAne : A ≠ ⊥ := by
    intro h
    apply hTne
    rw [h, coe_bot, centralizer_eq_top_iff_subset.mpr (Set.singleton_subset_iff.mpr
      (one_mem _)), inf_top_eq] at hAfaith
    exact hAfaith
  let S' : Set (Subgroup G) := {B | B < A ∧ T ≤ normalizer (B : Set G)}
  obtain ⟨M, ⟨hMA, hTM⟩, hMmax⟩ :=
    (Set.toFinite S').exists_maximal ⟨⊥, bot_lt_iff_ne_bot.mpr hAne, hnormbot⟩
  have hMleA : M ≤ A := hMA.le
  have hmax : ∀ H : Subgroup G, M ≤ H → H ≤ A → T ≤ normalizer (H : Set G) →
      H = M ∨ H = A := by
    intro H hMH hHA hTH
    by_cases hHA' : H = A
    · exact Or.inr hHA'
    · exact Or.inl (le_antisymm (hMmax ⟨lt_of_le_of_ne hHA hHA', hTH⟩ hMH) hMH)
  have hMn : A ≤ normalizer (M : Set G) := by
    have hnilA : Group.IsNilpotent A := hnil A hAX
    have hlt : M.subgroupOf A < ⊤ := by
      rw [lt_top_iff_ne_top, Ne, subgroupOf_eq_top]
      exact fun h => hMA.not_ge h
    obtain ⟨a, ha, haM⟩ :=
      IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
    have haN : (a : G) ∈ normalizer (M : Set G) := by
      rw [mem_normalizer_iff]
      intro g
      by_cases hg : g ∈ A
      · have := mem_normalizer_iff.mp ha ⟨g, hg⟩
        simpa [mem_subgroupOf] using this
      · have h1 : g ∉ M := fun h => hg (hMleA h)
        have h2 : (a : G) * g * (a : G)⁻¹ ∉ M := by
          intro h
          apply hg
          have := A.mul_mem (A.mul_mem (A.inv_mem a.2) (hMleA h)) a.2
          simpa [mul_assoc] using this
        exact ⟨fun h => absurd h h1, fun h => absurd h h2⟩
    let N : Subgroup G := A ⊓ normalizer (M : Set G)
    have hMN : M < N := by
      refine lt_of_le_of_ne (le_inf hMleA le_normalizer) ?_
      intro h
      apply haM
      have : (a : G) ∈ N := ⟨a.2, haN⟩
      rw [← h] at this
      exact this
    have hTN : T ≤ normalizer (N : Set G) := by
      intro s hs
      refine mem_normalizer_of_involutive (hT2 s hs) fun x hx =>
        ⟨conj_mem_of_mem_normalizer' (hTA hs) hx.1, ?_⟩
      exact (normalizer (M : Set G)).mul_mem ((normalizer (M : Set G)).mul_mem (hTM hs) hx.2)
        ((normalizer (M : Set G)).inv_mem (hTM hs))
    rcases hmax N hMN.le inf_le_left hTN with h | h
    · exact absurd h hMN.ne'
    · rw [← h]
      exact inf_le_right
  obtain ⟨I, hIT, hIne⟩ : ∃ I ∈ T ⊓ centralizer (M : Set G), I ≠ 1 := by
    have hne : T ⊓ centralizer (M : Set G) ≠ ⊥ := fun hbot =>
      hMA.not_ge (hAmin ⟨hMleA.trans hAX, hTM, hbot⟩ hMleA)
    obtain ⟨⟨I, hI⟩, hI1⟩ := ne_bot_iff_exists_ne_one.mp hne
    exact ⟨I, hI, fun h => hI1 (Subtype.ext h)⟩
  have hIT' : I ∈ T := (mem_inf.mp hIT).1
  have hIM : I ∈ centralizer (M : Set G) := (mem_inf.mp hIT).2
  have hI2 : I * I = 1 := hT2 I hIT'
  have hIord : orderOf I = 2 := orderOf_eq_prime (by rw [sq]; exact hI2) hIne
  have hCAM : A ⊓ centralizer {I} = M := by
    have hTC : T ≤ normalizer ((A ⊓ centralizer {I} : Subgroup G) : Set G) := by
      intro s hs
      refine mem_normalizer_of_involutive (hT2 s hs) fun x hx =>
        mem_inf.mpr ⟨conj_mem_of_mem_normalizer' (hTA hs) (mem_inf.mp hx).1, ?_⟩
      rw [mem_centralizer_singleton_iff]
      have hx2 : x * I = I * x := mem_centralizer_singleton_iff.mp (mem_inf.mp hx).2
      have hsI : Commute s I := hTcomm s hs I hIT'
      have hsI' : s⁻¹ * I = I * s⁻¹ := hsI.inv_left.eq
      calc s * x * s⁻¹ * I = s * x * (s⁻¹ * I) := by group
        _ = s * (x * I) * s⁻¹ := by rw [hsI']; group
        _ = (s * I) * x * s⁻¹ := by rw [hx2]; group
        _ = I * (s * x * s⁻¹) := by rw [hsI.eq]; group
    have hMCA : M ≤ A ⊓ centralizer {I} := fun m hm =>
      ⟨hMleA hm, mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp hIM) m hm)⟩
    rcases hmax _ hMCA inf_le_left hTC with h | h
    · exact h
    · exfalso
      apply hIne
      have hIA : I ∈ T ⊓ centralizer (A : Set G) := by
        refine ⟨hIT', mem_centralizer_iff.mpr fun a ha => ?_⟩
        have : a ∈ A ⊓ centralizer {I} := h.symm ▸ ha
        exact mem_centralizer_singleton_iff.mp this.2
      rw [hAfaith] at hIA
      exact hIA
  have hKcard : Nat.card (invertedSet A I) = M.relIndex A := by
    rw [(odd_inversion_coset_count hAodd (hTA hIT') (notMem_of_odd_card hAodd hIord)
      hIord).2.2, ← hCAM, relIndex, relIndex, inf_subgroupOf_left]
  have hKM : ∀ z ∈ invertedSet A I, z ∈ M → z = 1 := by
    intro z hz hzM
    have hzc : I * z * I⁻¹ = z := by
      have := (mem_centralizer_iff.mp hIM) z hzM
      rw [← this]
      group
    exact eq_one_of_eq_inv hAodd hz.1 (hzc.symm.trans hz.2)
  have hrel2 : 1 < M.relIndex A := by
    have h1 : M.relIndex A ≠ 1 := fun h => hMA.not_ge (relIndex_eq_one.mp h)
    have h0 : M.relIndex A ≠ 0 := fun h => by
      have := relIndex_dvd_card M A
      rw [h, zero_dvd_iff] at this
      exact Nat.card_pos.ne' this
    omega
  obtain ⟨y, hyK, hy1⟩ : ∃ y ∈ invertedSet A I, y ≠ 1 := by
    apply Set.exists_ne_of_one_lt_ncard
    rw [← Nat.card_coe_set_eq, hKcard]
    exact hrel2
  have hyA : y ∈ A := hyK.1
  have hyM : y ∉ M := fun h => hy1 (hKM y hyK h)
  have hmod := fun s (hs : s ∈ T) =>
    conj_mod_trivial_or_inv hAodd hMleA hMn hTA hTM hTcomm hmax hs (hT2 s hs)
  have hdich : ∀ H : Subgroup G, M ≤ H → H ≤ A → H = M ∨ H = A := fun H hMH hHA =>
    hmax H hMH hHA (le_normalizer_of_le_of_le hmod hT2 hMH hHA)
  have hsupy : M ⊔ zpowers y = A := by
    rcases hdich (M ⊔ zpowers y) le_sup_left (sup_le hMleA (zpowers_le.mpr hyA)) with h | h
    · exfalso
      apply hyM
      have : y ∈ M ⊔ zpowers y := mem_sup_right (mem_zpowers y)
      rwa [h] at this
    · exact h
  have hzK : ∀ z ∈ zpowers y, z ∈ invertedSet A I := by
    intro z hz
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hz
    refine ⟨A.zpow_mem hyA k, ?_⟩
    rw [← conj_zpow, hyK.2, inv_zpow]
  have hKeq : ((zpowers y : Subgroup G) : Set G) = invertedSet A I := by
    refine Set.eq_of_subset_of_ncard_le hzK ?_ (Set.toFinite _)
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, hKcard]
    exact relIndex_le_card_of_sup_eq hMleA (zpowers_le.mpr hyA) hMn hsupy
  have hA₁card : Nat.card (zpowers y) = M.relIndex A := by
    rw [← hKcard, ← hKeq]
    rfl
  have hA₁A : zpowers y ≤ A := zpowers_le.mpr hyA
  have hA₁dich : ∀ H : Subgroup G, H ≤ zpowers y → H = ⊥ ∨ H = zpowers y := by
    intro H hH
    rcases hdich (M ⊔ H) le_sup_left (sup_le hMleA (hH.trans hA₁A)) with h | h
    · left
      rw [eq_bot_iff]
      intro z hz
      have hzM : z ∈ M := by
        rw [← h]
        exact mem_sup_right hz
      exact (mem_bot).mpr (hKM z (hzK z (hH hz)) hzM)
    · right
      refine Subgroup.eq_of_le_of_card_ge hH ?_
      rw [hA₁card]
      exact relIndex_le_card_of_sup_eq hMleA (hH.trans hA₁A) hMn h
  have hA₁ne : zpowers y ≠ ⊥ := fun h => hy1 (zpowers_eq_bot.mp h)
  have hA₁prime : (Nat.card (zpowers y)).Prime := card_prime_of_forall hA₁ne hA₁dich
  have hKT : ∀ s ∈ T, ∀ z ∈ invertedSet A I, s * z * s⁻¹ ∈ invertedSet A I := by
    intro s hs z hz
    refine ⟨conj_mem_of_mem_normalizer' (hTA hs) hz.1, ?_⟩
    have e1 : I * s = s * I := (hTcomm s hs I hIT').symm
    calc I * (s * z * s⁻¹) * I⁻¹ = (I * s) * z * (I * s)⁻¹ := by group
      _ = (s * I) * z * (s * I)⁻¹ := by rw [e1]
      _ = s * (I * z * I⁻¹) * s⁻¹ := by group
      _ = (s * z * s⁻¹)⁻¹ := by rw [hz.2]; group
  have hTA₁ : T ≤ normalizer ((zpowers y : Subgroup G) : Set G) := by
    intro s hs
    refine mem_normalizer_of_involutive (hT2 s hs) fun z hz => ?_
    have h2 := hKT s hs z (hzK z hz)
    rw [← hKeq] at h2
    exact h2
  have hMA₁ : M ≤ normalizer ((zpowers y : Subgroup G) : Set G) := by
    have key : ∀ m ∈ M, ∀ z ∈ zpowers y, m * z * m⁻¹ ∈ zpowers y := by
      intro m hm z hz
      have hz' : z ∈ invertedSet A I := hzK z hz
      have hmI : m * I = I * m := (mem_centralizer_iff.mp hIM) m hm
      have : m * z * m⁻¹ ∈ invertedSet A I := by
        refine ⟨A.mul_mem (A.mul_mem (hMleA hm) hz'.1) (A.inv_mem (hMleA hm)), ?_⟩
        calc I * (m * z * m⁻¹) * I⁻¹ = (I * m) * z * (I * m)⁻¹ := by group
          _ = (m * I) * z * (m * I)⁻¹ := by rw [hmI]
          _ = m * (I * z * I⁻¹) * m⁻¹ := by group
          _ = (m * z * m⁻¹)⁻¹ := by rw [hz'.2]; group
      rw [← hKeq] at this
      exact this
    intro m hm
    rw [mem_normalizer_iff]
    intro z
    refine ⟨key m hm z, fun h => ?_⟩
    have := key m⁻¹ (M.inv_mem hm) _ h
    simpa [mul_assoc] using this
  have hAA₁ : A ≤ normalizer ((zpowers y : Subgroup G) : Set G) := by
    rw [← hsupy]
    exact sup_le hMA₁ le_normalizer
  have hcentral : ∀ a ∈ A, ∀ z ∈ zpowers y, a * z = z * a := by
    have hnilA : Group.IsNilpotent A := hnil A hAX
    have hN : ((zpowers y).subgroupOf A).Normal :=
      (normal_subgroupOf_iff_le_normalizer hA₁A).mpr hAA₁
    have hne : (zpowers y).subgroupOf A ≠ ⊥ := by
      intro h
      rw [subgroupOf_eq_bot, disjoint_iff, inf_eq_left.mpr hA₁A] at h
      exact hA₁ne h
    obtain ⟨⟨w, hwmem⟩, hw1⟩ :=
      ne_bot_iff_exists_ne_one.mp (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
    have hwA₁ : (w : G) ∈ zpowers y := (mem_inf.mp hwmem).1
    have hwc : w ∈ center A := (mem_inf.mp hwmem).2
    have hw1' : (w : G) ≠ 1 := fun h => hw1 (Subtype.ext (Subtype.ext h))
    have hzp : zpowers (w : G) = zpowers y := by
      rcases hA₁dich (zpowers (w : G)) (zpowers_le.mpr hwA₁) with h | h
      · exact absurd (zpowers_eq_bot.mp h) hw1'
      · exact h
    intro a ha z hz
    rw [← hzp] at hz
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hz
    have hcomm : Commute a (w : G) := congrArg Subtype.val (mem_center_iff.mp hwc ⟨a, ha⟩)
    exact (hcomm.zpow_right k).eq
  have hA₁odd : Odd (Nat.card (zpowers y)) := Odd.of_dvd_nat hAodd (card_dvd_of_le hA₁A)
  have hpm : ∀ s ∈ T, (∀ z ∈ zpowers y, s * z * s⁻¹ = z) ∨
      (∀ z ∈ zpowers y, s * z * s⁻¹ = z⁻¹) := by
    intro s hs
    have hbotn : zpowers y ≤ normalizer ((⊥ : Subgroup G) : Set G) := by
      rw [normalizer_eq_top_iff.mpr inferInstance]
      exact le_top
    rcases conj_mod_trivial_or_inv hA₁odd bot_le hbotn hTA₁ hnormbot hTcomm
      (fun H _ hH _ => hA₁dich H hH) hs (hT2 s hs) with h | h
    · left
      intro z hz
      exact (inv_mul_eq_one.mp ((mem_bot).mp (h z hz))).symm
    · right
      intro z hz
      exact eq_inv_of_mul_eq_one_right ((mem_bot).mp (h z hz))
  have hyy : y ≠ y⁻¹ := fun h => hy1 (eq_one_of_eq_inv hAodd hyA h)
  have hxor : ∀ s ∈ T, s ∈ centralizer ((zpowers y : Subgroup G) : Set G) ∨
      s * I ∈ centralizer ((zpowers y : Subgroup G) : Set G) := by
    intro s hs
    rcases hpm s hs with h | h
    · exact Or.inl (mem_centralizer_of_conj_eq h)
    · right
      refine mem_centralizer_of_conj_eq fun z hz => ?_
      have hzK' := hzK z hz
      calc s * I * z * (s * I)⁻¹ = s * (I * z * I⁻¹) * s⁻¹ := by group
        _ = (s * z * s⁻¹)⁻¹ := by rw [hzK'.2]; group
        _ = z := by rw [h z hz, inv_inv]
  have hT₁card : Nat.card (T ⊓ centralizer ((zpowers y : Subgroup G) : Set G) : Subgroup G) =
      2 ^ n := by
    have h2 : (T ⊓ centralizer ((zpowers y : Subgroup G) : Set G)).relIndex T = 2 := by
      rw [relIndex_eq_two_iff]
      refine ⟨I, hIT', fun b hb => ?_⟩
      have hbI : b * I ∈ T := T.mul_mem hb hIT'
      rcases hpm b hb with h | h
      · right
        refine ⟨⟨hb, mem_centralizer_of_conj_eq h⟩, fun hc => hyy ?_⟩
        have h1 := conj_eq_of_mem_centralizer (mem_inf.mp hc).2 (mem_zpowers y)
        calc y = b * I * y * (b * I)⁻¹ := h1.symm
          _ = b * (I * y * I⁻¹) * b⁻¹ := by group
          _ = y⁻¹ := by rw [hyK.2, h y⁻¹ (inv_mem (mem_zpowers y))]
      · left
        refine ⟨⟨hbI, ?_⟩, fun hc => hyy ?_⟩
        · refine mem_centralizer_of_conj_eq fun z hz => ?_
          calc b * I * z * (b * I)⁻¹ = b * (I * z * I⁻¹) * b⁻¹ := by group
            _ = (b * z * b⁻¹)⁻¹ := by rw [(hzK z hz).2]; group
            _ = z := by rw [h z hz, inv_inv]
        · have h1 := conj_eq_of_mem_centralizer (mem_inf.mp hc).2 (mem_zpowers y)
          rw [h y (mem_zpowers y)] at h1
          exact h1.symm
    have h3 := relIndex_mul_card (T ⊓ centralizer ((zpowers y : Subgroup G) : Set G)) T
    rw [h2, inf_eq_left.mpr inf_le_left, hTcard, pow_succ] at h3
    omega
  have hT₁M : T ⊓ centralizer ((zpowers y : Subgroup G) : Set G) ⊓ centralizer (M : Set G) =
      ⊥ := by
    rw [eq_bot_iff]
    intro s hs
    obtain ⟨⟨hsT, hsA₁⟩, hsM⟩ := hs
    have hAs : A ≤ centralizer ({s} : Set G) := by
      rw [← hsupy]
      refine sup_le (fun m hm => ?_) (fun z hz => ?_)
      · exact mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp hsM) m hm)
      · exact mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp hsA₁) z hz)
    have : s ∈ T ⊓ centralizer (A : Set G) := ⟨hsT, mem_centralizer_of_le hAs⟩
    rw [hAfaith] at this
    exact this
  refine ⟨zpowers y, M, I, hA₁A.trans hAX, hTA₁, hA₁prime, hIT', fun a ha => (hzK a ha).2,
    hMleA.trans hAX, hTM, hIM, fun x hx y' hy' => (hcentral y' (hMleA hy') x hx).symm, hT₁card,
    hxor, hT₁M⟩

structure DihedralBasis (X T : Subgroup G) {n : ℕ} (A : Fin n → Subgroup G) (t : Fin n → G) :
    Prop where
  le : ∀ i, A i ≤ X
  le_normalizer : ∀ i, T ≤ normalizer (A i : Set G)
  prime : ∀ i, (Nat.card (A i)).Prime
  mem : ∀ i, t i ∈ T
  inv : ∀ i, ∀ a ∈ A i, t i * a * (t i)⁻¹ = a⁻¹
  mem_centralizer : ∀ i j, i ≠ j → t i ∈ centralizer (A j : Set G)
  comm : Pairwise fun i j => ∀ x ∈ A i, ∀ y ∈ A j, Commute x y
  faithful : T ⊓ centralizer ((⨆ i, A i : Subgroup G) : Set G) = ⊥

theorem exists_dihedral_basis [Finite G] (n : ℕ) : ∀ {X T : Subgroup G},
    (∀ H : Subgroup G, H ≤ X → Group.IsNilpotent H) → Odd (Nat.card X) →
    (∀ s ∈ T, ∀ t ∈ T, s * t = t * s) → (∀ t ∈ T, t * t = 1) → Nat.card T = 2 ^ n →
    T ≤ normalizer (X : Set G) → T ⊓ centralizer (X : Set G) = ⊥ →
    ∃ (A : Fin n → Subgroup G) (t : Fin n → G), DihedralBasis X T A t := by
  induction n with
  | zero =>
    intro X T _ _ _ _ hTcard _ _
    have hT : T = ⊥ := Subgroup.eq_bot_of_card_eq T (by rw [hTcard, pow_zero])
    refine ⟨fun i => i.elim0, fun i => i.elim0, ⟨fun i => i.elim0, fun i => i.elim0,
      fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
      by rw [hT, bot_inf_eq]⟩⟩
  | succ n ih =>
    intro X T hnil hXodd hTcomm hT2 hTcard hTX hfaith
    obtain ⟨A₁, M, I, hA₁X, hTA₁, hA₁p, hIT, hIinv, hMX, hTM, hIM, hA₁M, hT₁card, hxor,
      hT₁M⟩ := exists_step hnil hXodd hTcomm hT2 hTcard hTX hfaith
    set T₁ := T ⊓ centralizer (A₁ : Set G) with hT₁
    have hT₁T : T₁ ≤ T := inf_le_left
    obtain ⟨A', t', hB⟩ := ih (X := M) (T := T₁) (fun H hH => hnil H (hH.trans hMX))
      (Odd.of_dvd_nat hXodd (card_dvd_of_le hMX))
      (fun s hs t ht => hTcomm s (hT₁T hs) t (hT₁T ht)) (fun t ht => hT2 t (hT₁T ht))
      hT₁card (hT₁T.trans hTM) hT₁M
    have hIcent : ∀ j, I ∈ centralizer (A' j : Set G) := fun j =>
      centralizer_le (SetLike.coe_subset_coe.mpr (hB.le j)) hIM
    refine ⟨Fin.cons A₁ A', Fin.cons I t', ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · refine Fin.cases ?_ ?_
      · exact hA₁X
      · intro j
        exact (hB.le j).trans hMX
    · refine Fin.cases ?_ ?_
      · exact hTA₁
      · intro j s hs
        simp only [Fin.cons_succ]
        rcases hxor s hs with h | h
        · exact hB.le_normalizer j ⟨hs, h⟩
        · have h1 : s * I ∈ normalizer (A' j : Set G) :=
            hB.le_normalizer j ⟨T.mul_mem hs hIT, h⟩
          have h2 : I ∈ normalizer (A' j : Set G) := centralizer_le_normalizer _ (hIcent j)
          have := (normalizer (A' j : Set G)).mul_mem h1 ((normalizer (A' j : Set G)).inv_mem h2)
          simpa using this
    · refine Fin.cases ?_ ?_
      · exact hA₁p
      · exact hB.prime
    · refine Fin.cases ?_ ?_
      · exact hIT
      · intro j
        exact hT₁T (hB.mem j)
    · refine Fin.cases ?_ ?_
      · exact hIinv
      · exact hB.inv
    · intro i j hij
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => exact absurd rfl hij
        | succ j => exact hIcent j
      | succ i =>
        induction j using Fin.cases with
        | zero => exact (mem_inf.mp (hB.mem i)).2
        | succ j => exact hB.mem_centralizer i j (Fin.succ_inj.not.mp hij)
    · intro i j hij
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => exact absurd rfl hij
        | succ j =>
          intro x hx y hy
          exact hA₁M x hx y (hB.le j hy)
      | succ i =>
        induction j using Fin.cases with
        | zero =>
          intro x hx y hy
          exact (hA₁M y hy x (hB.le i hx)).symm
        | succ j => exact hB.comm (Fin.succ_inj.not.mp hij)
    · rw [eq_bot_iff]
      intro s hs
      obtain ⟨hsT, hsc⟩ := mem_inf.mp hs
      have hle0 : A₁ ≤ ⨆ i, (Fin.cons A₁ A' : Fin (n + 1) → Subgroup G) i :=
        le_iSup_of_le 0 (by simp)
      have hle' : (⨆ j, A' j) ≤ ⨆ i, (Fin.cons A₁ A' : Fin (n + 1) → Subgroup G) i :=
        iSup_le fun j => le_iSup_of_le j.succ (by simp)
      have hsA₁ : s ∈ centralizer (A₁ : Set G) :=
        centralizer_le (SetLike.coe_subset_coe.mpr hle0) hsc
      have hsA' : s ∈ centralizer ((⨆ j, A' j : Subgroup G) : Set G) :=
        centralizer_le (SetLike.coe_subset_coe.mpr hle') hsc
      have : s ∈ T₁ ⊓ centralizer ((⨆ j, A' j : Subgroup G) : Set G) := ⟨⟨hsT, hsA₁⟩, hsA'⟩
      rw [hB.faithful] at this
      exact this

end CFSG.RankThree.Literature.Thompson534
