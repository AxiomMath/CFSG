module

public import CFSG.Monster.GroupTheory
public import CFSG.Monster.NormalChain
public import Mathlib.Data.ZMod.QuotientGroup

public section

namespace CFSG.Monster

variable {G : Type*} [Group G]

theorem mem_zpowers_iff_of_orderOf_eq_two {z x : G} (hz : orderOf z = 2) :
    x ∈ Subgroup.zpowers z ↔ x = 1 ∨ x = z := by
  constructor
  · intro hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [← zpow_mod_orderOf, hz]
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left
      rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h, zpow_zero]
    · right
      rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h, zpow_one]
  · rintro (h | h)
    · rw [h]; exact one_mem _
    · rw [h]; exact Subgroup.mem_zpowers z

theorem isConj_of_conj_fixedPointFree {E : Subgroup G} (hE4 : Nat.card E = 4) {z τ : G}
    (hzE : z ∈ E) (hz1 : z ≠ 1) (hτE : ∀ e ∈ E, τ⁻¹ * e * τ ∈ E)
    (hτcyc : ∀ e ∈ E, e ≠ 1 → τ⁻¹ * e * τ ≠ e) {e : G} (he : e ∈ E) (he1 : e ≠ 1) :
    IsConj z e := by
  classical
  have : Finite E := Nat.finite_of_card_ne_zero (by rw [hE4]; norm_num)
  have := Fintype.ofFinite E
  have hcardE : Fintype.card E = 4 := by rw [← Nat.card_eq_fintype_card, hE4]
  have hσ1 : ∀ x : G, τ⁻¹ * x * τ = 1 → x = 1 := by
    intro x hx
    calc x = τ * (τ⁻¹ * x * τ) * τ⁻¹ := by group
      _ = 1 := by rw [hx]; group
  have hσinj : ∀ x y : G, τ⁻¹ * x * τ = τ⁻¹ * y * τ → x = y := by
    intro x y h
    simpa using h
  set z₁ := τ⁻¹ * z * τ with hz₁
  set z₂ := τ⁻¹ * z₁ * τ with hz₂
  have hz₁E : z₁ ∈ E := hτE z hzE
  have hz₂E : z₂ ∈ E := hτE z₁ hz₁E
  have hz₁1 : z₁ ≠ 1 := fun h => hz1 (hσ1 z h)
  have hz₂1 : z₂ ≠ 1 := fun h => hz₁1 (hσ1 z₁ h)
  have hzz₁ : z₁ ≠ z := hτcyc z hzE hz1
  have hz₁z₂ : z₂ ≠ z₁ := hτcyc z₁ hz₁E hz₁1
  have hzz₂ : z₂ ≠ z := by
    intro hz₂z
    let t : Finset E := {1, ⟨z, hzE⟩, ⟨z₁, hz₁E⟩}
    have ht : t.card = 3 := by
      have h1 : (1 : E) ≠ ⟨z, hzE⟩ := fun h => hz1 (congrArg Subtype.val h).symm
      have h2 : (1 : E) ≠ ⟨z₁, hz₁E⟩ := fun h => hz₁1 (congrArg Subtype.val h).symm
      have h3 : (⟨z, hzE⟩ : E) ≠ ⟨z₁, hz₁E⟩ := fun h => hzz₁ (congrArg Subtype.val h).symm
      simp [t, Finset.card_insert_of_notMem, h1, h2, h3]
    have hc : (Finset.univ \ t).card = 1 := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hcardE, ht]
    obtain ⟨a, ha⟩ := Finset.card_eq_one.1 hc
    have hat : a ∉ t := (Finset.mem_sdiff.1 (ha ▸ Finset.mem_singleton_self a)).2
    have ha1 : (a : G) ≠ 1 := fun h => hat (by simp [t, Subtype.ext_iff, h])
    have haz : (a : G) ≠ z := fun h => hat (by simp [t, Subtype.ext_iff, h])
    have haz₁ : (a : G) ≠ z₁ := fun h => hat (by simp [t, Subtype.ext_iff, h])
    have hσa : (⟨τ⁻¹ * a * τ, hτE a a.2⟩ : E) ∈ Finset.univ \ t := by
      refine Finset.mem_sdiff.2 ⟨Finset.mem_univ _, ?_⟩
      simp only [t, Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff,
        OneMemClass.coe_one, not_or]
      refine ⟨fun h => ha1 (hσ1 _ h), fun h => haz₁ (hσinj _ _ (h.trans hz₂z.symm)),
        fun h => haz (hσinj _ _ h)⟩
    rw [ha, Finset.mem_singleton] at hσa
    exact hτcyc a a.2 ha1 (congrArg Subtype.val hσa)
  have hall : e = z ∨ e = z₁ ∨ e = z₂ := by
    by_contra hne
    simp only [not_or] at hne
    obtain ⟨hez, hez₁, hez₂⟩ := hne
    let s : Finset E := {1, ⟨z, hzE⟩, ⟨z₁, hz₁E⟩, ⟨z₂, hz₂E⟩, ⟨e, he⟩}
    have hs : s.card = 5 := by
      simp [s, Finset.card_insert_of_notMem, Subtype.ext_iff, hz1.symm, hz₁1.symm, hz₂1.symm,
        he1.symm, Ne.symm hzz₁, Ne.symm hzz₂, Ne.symm hz₁z₂, Ne.symm hez, Ne.symm hez₁,
        Ne.symm hez₂]
    have := Finset.card_le_univ s
    omega
  rcases hall with h | h | h <;> rw [h]
  · exact isConj_iff.2 ⟨τ⁻¹, by rw [hz₁, inv_inv]⟩
  · exact isConj_iff.2 ⟨τ⁻¹ * τ⁻¹, by rw [hz₂, hz₁]; simp only [mul_inv_rev, inv_inv, mul_assoc]⟩

theorem isSimpleGroup_of_triality [Finite G] {H Q : Subgroup G} (hQH : Q ≤ H)
    [hQn : (Q.subgroupOf H).Normal] {z : G} (hzQ : z ∈ Q) (hz2 : orderOf z = 2)
    (hZ : ∀ q ∈ Q, (∀ x ∈ Q, x * q = q * x) ↔ q ∈ Subgroup.zpowers z)
    (hcomm : ∀ x ∈ Q, ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.zpowers z)
    (hQz : ∃ q ∈ Q, q ∉ Subgroup.zpowers z) (hsimple : IsSimpleGroup (H ⧸ Q.subgroupOf H))
    (hfaith : ∀ h ∈ H, (∀ x ∈ Q, h * x * h⁻¹ * x⁻¹ ∈ Subgroup.zpowers z) → h ∈ Q)
    (hirr : ∀ R : Subgroup G, (∀ h ∈ H, ∀ r ∈ R, h * r * h⁻¹ ∈ R) →
      Subgroup.zpowers z ≤ R → R ≤ Q → R = Subgroup.zpowers z ∨ R = Q)
    (hCz : Subgroup.centralizer {z} = H) {E : Subgroup G} (hEH : E ≤ H)
    (hE4 : Nat.card E = 4) (hEexp : ∀ e ∈ E, e * e = 1) (hzE : z ∈ E) {τ : G}
    (hτE : ∀ e ∈ E, τ⁻¹ * e * τ ∈ E) (hτcyc : ∀ e ∈ E, e ≠ 1 → τ⁻¹ * e * τ ≠ e)
    (hgen : Subgroup.closure (insert τ (H : Set G)) = ⊤) {u : G} (hu : u ∈ Q)
    (huH : τ⁻¹ * u * τ ∈ H) (huQ : τ⁻¹ * u * τ ∉ Q) {h : G} (hh : h ∈ H)
    (hhτ : τ⁻¹ * h * τ * h = τ) : Nontrivial G ∧ IsSimpleGroup G := by
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz2
    exact absurd hz2 (by decide)
  have hzH : z ∈ H := hQH hzQ
  have hzpQ : Subgroup.zpowers z ≤ Q := (Subgroup.zpowers_le).2 hzQ
  have hzpH : Subgroup.zpowers z ≤ H := (Subgroup.zpowers_le).2 hzH
  have hntriv : Nontrivial G := ⟨⟨z, 1, hz1⟩⟩
  refine ⟨hntriv, ⟨fun N hN => ?_⟩⟩
  set Q₀ := Q.subgroupOf H with hQ₀
  set Z₀ := (Subgroup.zpowers z).subgroupOf H with hZ₀def
  have hQ₀n : Q₀.Normal := hQn
  have hZ₀ : ∀ x : H, x ∈ Z₀ ↔ x ∈ Q₀ ∧ ∀ y ∈ Q₀, y * x = x * y := by
    intro x
    rw [hZ₀def, hQ₀, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have hxQ : (x : G) ∈ Q := hzpQ hx
      refine ⟨hxQ, fun y hy => Subtype.ext ?_⟩
      rw [Subgroup.mem_subgroupOf] at hy
      exact ((hZ x hxQ).2 hx) y hy
    · rintro ⟨hxQ, hx⟩
      refine (hZ x hxQ).1 fun y hy => ?_
      have := hx ⟨y, hQH hy⟩ (by rw [Subgroup.mem_subgroupOf]; exact hy)
      exact congrArg Subtype.val this
  have hZ₀p : Nat.card Z₀ = 2 := by
    rw [hZ₀def, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzpH).toEquiv, Nat.card_zpowers, hz2]
  have hcomm₀ : ∀ x ∈ Q₀, ∀ y ∈ Q₀, x * y * x⁻¹ * y⁻¹ ∈ Z₀ := by
    intro x hx y hy
    rw [hQ₀, Subgroup.mem_subgroupOf] at hx hy
    rw [hZ₀def, Subgroup.mem_subgroupOf]
    simpa using hcomm x hx y hy
  have hQZ₀ : Z₀ ≠ Q₀ := by
    obtain ⟨q, hq, hqz⟩ := hQz
    intro heq
    apply hqz
    have hq₀ : (⟨q, hQH hq⟩ : H) ∈ Q₀ := by rw [hQ₀, Subgroup.mem_subgroupOf]; exact hq
    rw [← heq, hZ₀def, Subgroup.mem_subgroupOf] at hq₀
    exact hq₀
  have hfaith₀ : ∀ x : H, (∀ y ∈ Q₀, x * y * x⁻¹ * y⁻¹ ∈ Z₀) → x ∈ Q₀ := by
    intro x hx
    rw [hQ₀, Subgroup.mem_subgroupOf]
    refine hfaith x x.2 fun y hy => ?_
    have := hx ⟨y, hQH hy⟩ (by rw [hQ₀, Subgroup.mem_subgroupOf]; exact hy)
    rw [hZ₀def, Subgroup.mem_subgroupOf] at this
    simpa using this
  have hirr₀ : ∀ R : Subgroup H, R.Normal → Z₀ ≤ R → R ≤ Q₀ → R = Z₀ ∨ R = Q₀ := by
    intro R hR hZR hRQ
    have hR' := hirr (R.map H.subtype) ?_ ?_ ?_
    · have hback : (R.map H.subtype).subgroupOf H = R := by
        ext x
        rw [Subgroup.mem_subgroupOf]
        constructor
        · rintro ⟨y, hy, hyx⟩
          rwa [Subtype.ext hyx] at hy
        · intro hx
          exact ⟨x, hx, rfl⟩
      rcases hR' with h1 | h1
      · left
        rw [← hback, h1]
      · right
        rw [← hback, h1]
    · rintro g hg _ ⟨r, hr, rfl⟩
      exact ⟨⟨g, hg⟩ * r * ⟨g, hg⟩⁻¹, hR.conj_mem r hr ⟨g, hg⟩, rfl⟩
    · intro x hx
      refine ⟨⟨x, hzpH hx⟩, hZR ?_, rfl⟩
      rw [hZ₀def, Subgroup.mem_subgroupOf]
      exact hx
    · rintro _ ⟨r, hr, rfl⟩
      have := hRQ hr
      rw [hQ₀, Subgroup.mem_subgroupOf] at this
      exact this
  obtain ⟨-, -, -, -, hchain⟩ := normal_eq_of_prime_central_irreducible' Nat.prime_two hZ₀
    hZ₀p hcomm₀ hQZ₀ hsimple hfaith₀ hirr₀
  rcases eq_or_ne N ⊥ with hNb | hNb
  · exact .inl hNb
  right
  have hNH : N ⊓ H ≠ ⊥ := by
    intro h0
    rw [← hCz] at h0
    exact hNb (eq_bot_of_inf_centralizer_eq_bot hE4 hEexp
      (fun e he he1 => isConj_of_conj_fixedPointFree hE4 hzE hz1 hτE hτcyc he he1) h0)
  have hmem : ∀ {x : G} (hx : x ∈ H), x ∈ N ↔ (⟨x, hx⟩ : H) ∈ N.subgroupOf H := fun hx => by
    rw [Subgroup.mem_subgroupOf]
  rcases hchain (N.subgroupOf H) (Subgroup.Normal.subgroupOf hN H) with h0 | h0 | h0 | h0
  ·
    exfalso
    apply hNH
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxN, hxH⟩ := Subgroup.mem_inf.1 hx
    have := (hmem hxH).1 hxN
    rw [h0, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
  ·
    exfalso
    have hzN : z ∈ N := by
      rw [hmem hzH, h0, hZ₀def, Subgroup.mem_subgroupOf]
      exact Subgroup.mem_zpowers z
    have hzτN : τ⁻¹ * z * τ ∈ N := by simpa using hN.conj_mem z hzN τ⁻¹
    have hzτH : τ⁻¹ * z * τ ∈ H := hEH (hτE z hzE)
    rw [hmem hzτH, h0, hZ₀def, Subgroup.mem_subgroupOf] at hzτN
    rcases (mem_zpowers_iff_of_orderOf_eq_two hz2).1 hzτN with h1 | h1
    · have h1' : τ⁻¹ * z * τ = 1 := h1
      apply hz1
      calc z = τ * (τ⁻¹ * z * τ) * τ⁻¹ := by group
        _ = 1 := by rw [h1']; group
    · exact hτcyc z hzE hz1 h1
  ·
    exfalso
    have huN : u ∈ N := by
      rw [hmem (hQH hu), h0, hQ₀, Subgroup.mem_subgroupOf]
      exact hu
    have huτN : τ⁻¹ * u * τ ∈ N := by simpa using hN.conj_mem u huN τ⁻¹
    rw [hmem huH, h0, hQ₀, Subgroup.mem_subgroupOf] at huτN
    exact huQ huτN
  ·
    have hHN : H ≤ N := fun x hx => by
      rw [hmem hx, h0]
      exact Subgroup.mem_top _
    have hτN : τ ∈ N := by
      have h1 : τ⁻¹ * h * τ ∈ N := by simpa using hN.conj_mem h (hHN hh) τ⁻¹
      rw [← hhτ]
      exact mul_mem h1 (hHN hh)
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    rintro x (rfl | hx)
    · exact hτN
    · exact hHN hx

end CFSG.Monster
