module

public import CFSG.Quasithin.H13.KGFact68CSTrans
public import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Basic

public section

namespace CFSG.Quasithin.H13.KG68.Singer

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Semidihedral.Principal.CoprimeFixedPoint (exists_fixed_of_invariant quotientAction
  quotientAction_mk)

variable {S : Type} [Group S] {K : Type} [Field K]

@[expose] def ActsBy (z : K → S) (n : S) (u : Kˣ) : Prop :=
  ∀ c : K, n * z c * n⁻¹ = z (u * c)

theorem ActsBy.mul {z : K → S} {n n' : S} {u u' : Kˣ} (h : ActsBy z n u) (h' : ActsBy z n' u') :
    ActsBy z (n * n') (u * u') := fun c => by
  calc n * n' * z c * (n * n')⁻¹ = n * (n' * z c * n'⁻¹) * n⁻¹ := by group
    _ = z ((u * u' : Kˣ) * c) := by rw [h' c, h, Units.val_mul, mul_assoc]

theorem ActsBy.inv {z : K → S} {n : S} {u : Kˣ} (h : ActsBy z n u) : ActsBy z n⁻¹ u⁻¹ :=
  fun c => by
    have h1 := h ((u⁻¹ : Kˣ) * c)
    rw [← mul_assoc, Units.mul_inv, one_mul] at h1
    rw [inv_inv, ← h1]
    group

theorem ActsBy.one {z : K → S} {n : S} (h : ∀ c, n * z c = z c * n) : ActsBy z n 1 := fun c => by
  rw [h c, mul_inv_cancel_right, Units.val_one, one_mul]

theorem ActsBy.unique {z : K → S} (hinj : Function.Injective z) {n : S} {u u' : Kˣ}
    (h : ActsBy z n u) (h' : ActsBy z n u') : u = u' := by
  have h1 := hinj ((h 1).symm.trans (h' 1))
  rw [mul_one, mul_one] at h1
  exact Units.ext h1

theorem mem_normalizer_of_normalizes {P : Subgroup S} {ρ : MulAut S} (h1 : ∀ p ∈ P, ρ p ∈ P)
    (h2 : ∀ p ∈ P, ρ⁻¹ p ∈ P) {n : S} (hn : n ∈ Subgroup.normalizer (P : Set S)) :
    ρ n ∈ Subgroup.normalizer (P : Set S) := by
  have hP : ∀ t, t ∈ P ↔ ρ t ∈ P := fun t =>
    ⟨h1 t, fun ht => by simpa using h2 _ ht⟩
  rw [Subgroup.mem_normalizer_iff] at hn ⊢
  intro t
  have e : ρ n * t * (ρ n)⁻¹ = ρ (n * ρ⁻¹ t * n⁻¹) := by
    rw [map_mul, map_mul, map_inv, MulAut.apply_inv_self]
  rw [e, ← hP, ← hn, hP (ρ⁻¹ t), MulAut.apply_inv_self]

theorem exists_odd_fixed_lift [Finite S] {P N : Subgroup S} (hP : IsSylowTwoOf P ⊤)
    (hPN : P ≤ N) (hNP : N ≤ Subgroup.normalizer (P : Set S)) {𝓡 : Subgroup (MulAut S)}
    (h𝓡 : IsPGroup 2 𝓡) (hnorm : ∀ ρ ∈ 𝓡, ∀ p ∈ P, ρ p ∈ P) (hρN : ∀ ρ ∈ 𝓡, ∀ n ∈ N, ρ n ∈ N)
    {D : Type} [Group D] (ψ : ↥N →* D) (hψP : ∀ n : ↥N, (n : S) ∈ P → ψ n = 1) (n₀ : ↥N)
    (hinv : ∀ ρ ∈ 𝓡, ∀ (n : ↥N) (h : ρ n ∈ N), ψ n = ψ n₀ → ψ ⟨ρ n, h⟩ = ψ n₀) :
    ∃ x : ↥N, ψ x = ψ n₀ ∧ Odd (orderOf (x : S)) ∧ ∀ ρ ∈ 𝓡, ρ x * (x : S)⁻¹ ∈ P := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P' : Subgroup ↥N := P.subgroupOf N with hP'def
  have : P'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hPN).2 hNP
  have hP'ker : P' ≤ ψ.ker := fun p hp => (MonoidHom.mem_ker).2 (hψP p hp)
  let ψ' : ↥N ⧸ P' →* D := QuotientGroup.lift P' ψ hP'ker
  have hψmk : ∀ n : ↥N, ψ' (n : ↥N ⧸ P') = ψ n := fun n => rfl
  let α₀ : ↥𝓡 →* MulAut ↥N :=
    { toFun := fun ρ =>
        { toFun := fun n => ⟨(ρ : MulAut S) n, hρN ρ ρ.2 n n.2⟩
          invFun := fun n => ⟨(ρ : MulAut S)⁻¹ n, hρN _ (inv_mem ρ.2) n n.2⟩
          left_inv := fun n => Subtype.ext (MulAut.inv_apply_self _ _ _)
          right_inv := fun n => Subtype.ext (MulAut.apply_inv_self _ _ _)
          map_mul' := fun a b => Subtype.ext (map_mul _ _ _) }
      map_one' := MulEquiv.ext fun n => Subtype.ext rfl
      map_mul' := fun ρ σ => MulEquiv.ext fun n => Subtype.ext rfl }
  have hP'inv : ∀ ρ : ↥𝓡, ∀ n ∈ P', α₀ ρ n ∈ P' := fun ρ n hn => hnorm ρ ρ.2 _ hn
  let act : ↥𝓡 →* MulAut (↥N ⧸ P') := quotientAction α₀ P' hP'inv
  let Y : Set (↥N ⧸ P') := {q | ψ' q = ψ n₀}
  have hY : ∀ ρ : ↥𝓡, ∀ q ∈ Y, act ρ q ∈ Y := by
    intro ρ q hq
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective q
    change ψ' (act ρ (n : ↥N ⧸ P')) = ψ n₀
    rw [quotientAction_mk, hψmk]
    exact hinv ρ ρ.2 n (hρN ρ ρ.2 n n.2) ((hψmk n).symm.trans hq)
  set q₀ : ↥N ⧸ P' := ((n₀ : ↥N) : ↥N ⧸ P') with hq₀
  have hq₀Y : ψ' q₀ = ψ n₀ := rfl
  have hYker : Nat.card Y = Nat.card ψ'.ker := by
    refine Nat.card_congr
      { toFun := fun q => ⟨q₀⁻¹ * q, by
          rw [MonoidHom.mem_ker, map_mul, map_inv, hq₀Y, show ψ' q = ψ n₀ from q.2,
            inv_mul_cancel]⟩
        invFun := fun k => ⟨q₀ * k, by
          change ψ' (q₀ * k) = ψ n₀
          rw [map_mul, hq₀Y, (MonoidHom.mem_ker).1 k.2, mul_one]⟩
        left_inv := fun q => Subtype.ext (by simp)
        right_inv := fun k => Subtype.ext (by simp) }
  have hodd : ¬ 2 ∣ Nat.card (↥N ⧸ P') := by
    have h1 : Nat.card (↥N ⧸ P') = P.relIndex N := rfl
    have h2 : P.relIndex N ∣ P.index := Subgroup.relIndex_dvd_index_of_le hPN
    have h3 : ¬ 2 ∣ P.index := by
      have := hP.2.2
      rwa [← Subgroup.relIndex, Subgroup.relIndex_top_right] at this
    rw [h1]
    exact fun h => h3 (h.trans h2)
  have hYodd : ¬ 2 ∣ Nat.card Y := by
    rw [hYker]
    exact fun h => hodd (h.trans (Subgroup.card_subgroup_dvd_card _))
  obtain ⟨q, hqY, hqfix⟩ := exists_fixed_of_invariant 2 h𝓡 act Y hY hYodd
  obtain ⟨n₁, rfl⟩ := QuotientGroup.mk_surjective q
  set m := orderOf ((n₁ : ↥N) : ↥N ⧸ P') with hm
  have hm_odd : Odd m := Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 fun h =>
    hodd (h.trans (orderOf_dvd_natCard _)))
  have hmpos : 0 < m := hm_odd.pos
  obtain ⟨k, hk⟩ := hP.2.1.exists_card_eq
  have hcop : Nat.Coprime (Nat.card ↥P) m := by
    rw [hk]
    exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hm_odd)
  set e := Nat.card ↥P ^ Nat.totient m with he
  have hemod : e ≡ 1 [MOD m] := Nat.ModEq.pow_totient hcop
  set xN : ↥N := n₁ ^ e with hxN
  have hxq : ((xN : ↥N) : ↥N ⧸ P') = (n₁ : ↥N ⧸ P') := by
    rw [hxN, QuotientGroup.mk_pow]
    conv_rhs => rw [← pow_one ((n₁ : ↥N) : ↥N ⧸ P')]
    exact pow_eq_pow_iff_modEq.2 hemod
  have hxm : (xN : S) ^ m = 1 := by
    have h1 : n₁ ^ m ∈ P' := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hm, pow_orderOf_eq_one]
    have h2 : ((n₁ ^ m : ↥N) : S) ^ Nat.card ↥P = 1 := by
      have := pow_card_eq_one' (G := ↥P) (x := ⟨((n₁ ^ m : ↥N) : S), h1⟩)
      exact congrArg Subtype.val this
    have htot : Nat.totient m = (Nat.totient m - 1) + 1 :=
      (Nat.sub_add_cancel (Nat.totient_pos.2 hmpos)).symm
    rw [hxN, Subgroup.coe_pow, ← pow_mul, mul_comm, pow_mul, he, htot, pow_succ, pow_mul',
      ← Subgroup.coe_pow, h2, one_pow]
  have hxodd : Odd (orderOf (xN : S)) := Odd.of_dvd_nat hm_odd (orderOf_dvd_of_pow_eq_one hxm)
  have hxfix : ∀ ρ ∈ 𝓡, ρ (xN : S) * (xN : S)⁻¹ ∈ P := by
    intro ρ hρ
    have h1 := hqfix ⟨ρ, hρ⟩
    rw [← hxq, quotientAction_mk, QuotientGroup.eq] at h1
    have h2 : (xN : S)⁻¹ * ρ (xN : S) ∈ P := by
      have h3 : xN⁻¹ * α₀ ⟨ρ, hρ⟩ xN ∈ P' := by simpa using inv_mem h1
      exact Subgroup.mem_subgroupOf.1 h3
    have h3 := (Subgroup.mem_normalizer_iff.1 (hNP xN.2) _).1 h2
    simpa [mul_assoc] using h3
  refine ⟨xN, ?_, hxodd, hxfix⟩
  rw [← hψmk, hxq]
  exact hqY

theorem _root_.CFSG.Quasithin.H13.KG68.CartanSingerHyp.apply_mem_normalizer {P : Subgroup S}
    {𝓡 : Subgroup (MulAut S)} {G : Subgroup S} (hG : CartanSingerHyp P 𝓡 G) {ρ : MulAut S}
    (hρ : ρ ∈ 𝓡) {n : S} (hn : n ∈ Subgroup.normalizer (P : Set S)) :
    ρ n ∈ Subgroup.normalizer (P : Set S) :=
  mem_normalizer_of_normalizes (hG.normalizes ρ hρ) (hG.normalizes ρ⁻¹ (inv_mem hρ)) hn

theorem cartanSingerConcl_of_hom [Finite S] {P N : Subgroup S} (hP : IsSylowTwoOf P ⊤)
    (hPN : P ≤ N) (hNP : N ≤ Subgroup.normalizer (P : Set S)) {D : Type} [Group D]
    (ψ : ↥N →* D) (hψ : Function.Surjective ψ) {𝓡 : Subgroup (MulAut S)} {G : Subgroup S}
    (hG : CartanSingerHyp P 𝓡 G) (hρN : ∀ ρ ∈ 𝓡, ∀ n ∈ N, ρ n ∈ N) {g₀ : S} (hg₀ : g₀ ∈ G)
    (hg₀1 : g₀ ≠ 1)
    (hcancel : ∀ n n' : ↥N, (n : S) * g₀ * (n : S)⁻¹ = n' * g₀ * (n' : S)⁻¹ → ψ n = ψ n')
    (htrans : ∀ g ∈ G, g ≠ 1 → ∃ n : ↥N, (n : S) * g₀ * (n : S)⁻¹ = g)
    (hker : ∀ n : ↥N, ψ n = 1 → ∀ g ∈ G, (n : S) * g = g * n)
    (hcyc : ∀ Λ : Subgroup D, (∀ n : ↥N, ψ n ∈ Λ → (n : S) * g₀ * (n : S)⁻¹ ∈ G) →
      IsCyclic Λ) :
    CartanSingerConcl P 𝓡 G := by
  classical
  have hDfin : Finite D := Finite.of_surjective ψ hψ
  have hB : ∀ ρ ∈ 𝓡, ∀ n : S, n * g₀ * n⁻¹ ∈ G →
      ρ n * g₀ * (ρ n)⁻¹ = n * g₀ * n⁻¹ := by
    intro ρ hρ n hn
    have h1 := hG.fixed ρ hρ _ hn
    rw [map_mul, map_mul, map_inv, hG.fixed ρ hρ _ hg₀] at h1
    exact h1
  have hconj : ∀ n n' : ↥N, ψ n = ψ n' →
      (n : S) * g₀ * (n : S)⁻¹ = n' * g₀ * (n' : S)⁻¹ := by
    intro n n' h
    have h1 := hker (n'⁻¹ * n) (by rw [map_mul, map_inv, h, inv_mul_cancel]) g₀ hg₀
    rw [Subgroup.coe_mul, Subgroup.coe_inv] at h1
    calc (n : S) * g₀ * (n : S)⁻¹ = n' * ((n' : S)⁻¹ * n * g₀) * (n : S)⁻¹ := by group
      _ = n' * (g₀ * ((n' : S)⁻¹ * n)) * (n : S)⁻¹ := by rw [h1]
      _ = n' * g₀ * (n' : S)⁻¹ := by group
  have hψP : ∀ n : ↥N, (n : S) ∈ P → ψ n = 1 := by
    intro n hn
    have h1 : (n : S) * g₀ * (n : S)⁻¹ = ((1 : ↥N) : S) * g₀ * ((1 : ↥N) : S)⁻¹ := by
      rw [← (hG.le g₀ hg₀).2 _ hn, mul_inv_cancel_right, OneMemClass.coe_one, one_mul, inv_one,
        mul_one]
    rw [hcancel n 1 h1, map_one]
  let Λ₀ : Subgroup D :=
    { carrier := {d | ∀ n : ↥N, ψ n = d → ∀ ρ (hρ : ρ ∈ 𝓡), ψ ⟨ρ n, hρN ρ hρ n n.2⟩ = d}
      one_mem' := by
        intro n hn ρ hρ
        have h2 : (n : S) * g₀ * (n : S)⁻¹ = g₀ := by
          have := hconj n 1 (by rw [hn, map_one])
          simpa using this
        have h3 := hB ρ hρ n (by rw [h2]; exact hg₀)
        rw [h2] at h3
        have h4 := hcancel ⟨ρ n, hρN ρ hρ n n.2⟩ 1 (by simpa using h3)
        rwa [map_one] at h4
      mul_mem' := by
        intro a b ha hb n hn ρ hρ
        obtain ⟨n₁, hn₁⟩ := hψ a
        have hn₂ : ψ (n₁⁻¹ * n) = b := by
          rw [map_mul, map_inv, hn₁, hn, inv_mul_cancel_left]
        have h1 := ha n₁ hn₁ ρ hρ
        have h2 := hb (n₁⁻¹ * n) hn₂ ρ hρ
        have e : (⟨ρ n, hρN ρ hρ n n.2⟩ : ↥N) = ⟨ρ n₁, hρN ρ hρ n₁ n₁.2⟩ *
            ⟨ρ (n₁⁻¹ * n : ↥N), hρN ρ hρ _ (n₁⁻¹ * n).2⟩ := Subtype.ext (by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, mul_inv_cancel_left])
        rw [e, map_mul, h1, h2]
      inv_mem' := by
        intro a ha n hn ρ hρ
        have h1 := ha n⁻¹ (by rw [map_inv, hn, inv_inv]) ρ hρ
        have e : (⟨ρ n, hρN ρ hρ n n.2⟩ : ↥N) =
            (⟨ρ (n⁻¹ : ↥N), hρN ρ hρ _ (n⁻¹).2⟩ : ↥N)⁻¹ := Subtype.ext (by
          simp only [Subgroup.coe_inv, map_inv, inv_inv])
        rw [e, map_inv, h1] }
  have hmemΛ : ∀ d : D, d ∈ Λ₀ ↔
      ∀ n : ↥N, ψ n = d → ∀ ρ (hρ : ρ ∈ 𝓡), ψ ⟨ρ n, hρN ρ hρ n n.2⟩ = d :=
    fun d => Iff.rfl
  have hlift : ∀ n₀ : ↥N, ψ n₀ ∈ Λ₀ → ∃ x : ↥N, ψ x = ψ n₀ ∧ Odd (orderOf (x : S)) ∧
      ∀ ρ ∈ 𝓡, ρ x * (x : S)⁻¹ ∈ P := fun n₀ hn₀ =>
    exists_odd_fixed_lift hP hPN hNP hG.isPGroup hG.normalizes hρN ψ hψP n₀
      fun ρ hρ n _ hn => (hmemΛ _).1 hn₀ n hn ρ hρ
  have hGsub : ∀ g ∈ G, g ≠ 1 → ∃ n : ↥N, ψ n ∈ Λ₀ ∧ (n : S) * g₀ * (n : S)⁻¹ = g := by
    intro g hg hg1
    obtain ⟨n, hn⟩ := htrans g hg hg1
    refine ⟨n, (hmemΛ _).2 fun n' hn' ρ hρ => ?_, hn⟩
    have h1 := hconj n' n hn'
    have h2 := hB ρ hρ n' (by rw [h1, hn]; exact hg)
    rw [← hn']
    exact hcancel _ _ h2
  by_cases hcase : ∃ n : ↥N, ψ n ∈ Λ₀ ∧ (n : S) * g₀ * (n : S)⁻¹ ∉ G
  ·
    obtain ⟨n, hnΛ, hnG⟩ := hcase
    obtain ⟨x, hxψ, hxodd, hxfix⟩ := hlift n hnΛ
    refine ⟨x, hNP x.2, hxodd, hxfix, fun hnorm => absurd ?_ hnG⟩
    rw [← hconj x n hxψ]
    exact hnorm g₀ hg₀
  push Not at hcase
  have : IsCyclic ↥Λ₀ := hcyc Λ₀ fun n hn => hcase n hn
  obtain ⟨d₀, hd₀⟩ := IsCyclic.exists_generator (α := ↥Λ₀)
  obtain ⟨n₀, hn₀⟩ := hψ d₀
  obtain ⟨x, hxψ, hxodd, hxfix⟩ := hlift n₀ (by rw [hn₀]; exact d₀.2)
  rw [hn₀] at hxψ
  refine ⟨x, hNP x.2, hxodd, hxfix, fun _ j => ?_⟩
  have hcardG : Nat.card G = Nat.card Λ₀ + 1 := by
    let c : ↥Λ₀ → ↥N := fun d => (hψ d).choose
    have hc : ∀ d : ↥Λ₀, ψ (c d) = d := fun d => (hψ d).choose_spec
    let f : Option ↥Λ₀ → ↥G := fun o => match o with
      | none => 1
      | some d => ⟨(c d : S) * g₀ * (c d : S)⁻¹, hcase (c d) (by rw [hc]; exact d.2)⟩
    have hf : Function.Bijective f := by
      refine ⟨fun a b hab => ?_, fun g => ?_⟩
      · have hne : ∀ d : ↥Λ₀, (c d : S) * g₀ * (c d : S)⁻¹ ≠ 1 := fun d h => hg₀1 (by
          rw [mul_inv_eq_one, mul_eq_left] at h
          exact h)
        rcases a with _ | a <;> rcases b with _ | b
        · rfl
        · exact absurd (congrArg Subtype.val hab).symm (hne b)
        · exact absurd (congrArg Subtype.val hab) (hne a)
        · have h1 := hcancel _ _ (congrArg Subtype.val hab)
          rw [hc, hc] at h1
          exact congrArg some (Subtype.ext h1)
      · by_cases hg1 : (g : S) = 1
        · exact ⟨none, Subtype.ext hg1.symm⟩
        · obtain ⟨n, hnΛ, hn⟩ := hGsub g g.2 hg1
          refine ⟨some ⟨ψ n, hnΛ⟩, Subtype.ext ?_⟩
          change (c ⟨ψ n, hnΛ⟩ : S) * g₀ * (c ⟨ψ n, hnΛ⟩ : S)⁻¹ = (g : S)
          rw [hconj _ n (hc _), hn]
    have := Fintype.ofFinite ↥Λ₀
    rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_fintype_card,
      Fintype.card_option, ← Nat.card_eq_fintype_card]
  have hord : orderOf (d₀ : D) = Nat.card Λ₀ := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_card_of_forall_mem_zpowers hd₀
  rw [hcardG, Nat.add_sub_cancel, ← hord, orderOf_dvd_iff_pow_eq_one, ← hxψ, ← map_pow]
  constructor
  · intro h
    have h1 : ((x ^ j : ↥N) : S) * g₀ * ((x ^ j : ↥N) : S)⁻¹ =
        ((1 : ↥N) : S) * g₀ * ((1 : ↥N) : S)⁻¹ := by
      rw [Subgroup.coe_pow, h g₀ hg₀, mul_inv_cancel_right, OneMemClass.coe_one, one_mul,
        inv_one, mul_one]
    rw [hcancel _ _ h1, map_one]
  · intro h g hg
    have h1 := hker (x ^ j) h g hg
    rwa [Subgroup.coe_pow] at h1

theorem cartanSingerConcl_of_rootGroup [Finite S] [Finite K] {P : Subgroup S}
    (hP : IsSylowTwoOf P ⊤) {z : K → S} (hinj : Function.Injective z) (hz0 : z 0 = 1)
    (hscalar : ∀ n ∈ Subgroup.normalizer (P : Set S), ∃ u : Kˣ, ActsBy z n u)
    (honto : ∀ u : Kˣ, ∃ n ∈ Subgroup.normalizer (P : Set S), ActsBy z n u)
    {𝓡 : Subgroup (MulAut S)} {G : Subgroup S} (hG : CartanSingerHyp P 𝓡 G)
    (hGz : ∀ g ∈ G, ∃ c, z c = g) :
    CartanSingerConcl P 𝓡 G := by
  classical
  set N := Subgroup.normalizer (P : Set S) with hNdef
  obtain ⟨g₀, hg₀G, hg₀⟩ : ∃ g ∈ G, g ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : G = ⊥ := (Subgroup.eq_bot_iff_forall G).2 hcon
    have := hG.four_le
    rw [hbot, Subgroup.card_bot] at this
    omega
  obtain ⟨c₀, rfl⟩ := hGz g₀ hg₀G
  have hc₀ : c₀ ≠ 0 := fun h => hg₀ (by rw [h, hz0])
  have hsc : ∀ n : ↥N, ∃ u : Kˣ, ActsBy z n u := fun n => hscalar n n.2
  let sc : ↥N → Kˣ := fun n => (hsc n).choose
  have hsc_spec : ∀ n : ↥N, ActsBy z (n : S) (sc n) := fun n => (hsc n).choose_spec
  have hsc_eq : ∀ (n : ↥N) (u : Kˣ), ActsBy z (n : S) u → sc n = u := fun n u h =>
    ActsBy.unique hinj (hsc_spec n) h
  let ψ : ↥N →* Kˣ :=
    { toFun := sc
      map_one' := hsc_eq 1 1 (ActsBy.one fun c => by simp)
      map_mul' := fun a b => hsc_eq (a * b) _ ((hsc_spec a).mul (hsc_spec b)) }
  have hψ : ∀ n : ↥N, ψ n = sc n := fun n => rfl
  refine cartanSingerConcl_of_hom hP Subgroup.le_normalizer le_rfl ψ (fun u => ?_) hG
    (fun ρ hρ n hn => hG.apply_mem_normalizer hρ hn) hg₀G hg₀ (fun n n' h => ?_)
    (fun g hg hg1 => ?_) (fun n hn g hg => ?_) fun Λ _ => inferInstance
  · obtain ⟨n, hn, hnu⟩ := honto u
    exact ⟨⟨n, hn⟩, hsc_eq _ _ hnu⟩
  · rw [hsc_spec n c₀, hsc_spec n' c₀] at h
    exact Units.ext (mul_right_cancel₀ hc₀ (hinj h))
  · obtain ⟨c, rfl⟩ := hGz g hg
    have hc : c ≠ 0 := fun h => hg1 (by rw [h, hz0])
    obtain ⟨n, hn, hnu⟩ := honto (Units.mk0 (c / c₀) (div_ne_zero hc hc₀))
    refine ⟨⟨n, hn⟩, ?_⟩
    rw [hnu c₀, Units.val_mk0, div_mul_cancel₀ _ hc₀]
  · obtain ⟨c, rfl⟩ := hGz g hg
    have h1 := hsc_spec n c
    rw [← hψ, hn, Units.val_one, one_mul] at h1
    calc (n : S) * z c = (n : S) * z c * (n : S)⁻¹ * n := by group
      _ = z c * n := by rw [h1]

theorem cartanSingerConcl_of_rootCenter [Finite S] [Finite K] {P : Subgroup S}
    (hP : IsSylowTwoOf P ⊤) {z : K → S} (hinj : Function.Injective z) (hz0 : z 0 = 1)
    (hcenter : ∀ g ∈ P, (∀ t ∈ P, g * t = t * g) → ∃ c, z c = g)
    (hscalar : ∀ n ∈ Subgroup.normalizer (P : Set S), ∃ u : Kˣ, ActsBy z n u)
    (honto : ∀ u : Kˣ, ∃ n ∈ Subgroup.normalizer (P : Set S), ActsBy z n u)
    {𝓡 : Subgroup (MulAut S)} {G : Subgroup S} (hG : CartanSingerHyp P 𝓡 G) :
    CartanSingerConcl P 𝓡 G :=
  cartanSingerConcl_of_rootGroup hP hinj hz0 hscalar honto hG fun g hg =>
    hcenter g (hG.le g hg).1 (hG.le g hg).2

theorem cartanSingerCover_of_rootCenter [Finite S] [Finite K] (P : Sylow 2 S) {z : K → S}
    (hinj : Function.Injective z) (hz0 : z 0 = 1)
    (hcenter : ∀ g ∈ (P : Subgroup S), (∀ t ∈ (P : Subgroup S), g * t = t * g) → ∃ c, z c = g)
    (hscalar : ∀ n ∈ Subgroup.normalizer ((P : Subgroup S) : Set S), ∃ u : Kˣ, ActsBy z n u)
    (honto : ∀ u : Kˣ, ∃ n ∈ Subgroup.normalizer ((P : Subgroup S) : Set S), ActsBy z n u) :
    CartanSingerCover S :=
  cartanSingerCover_of_sylow P fun _ _ hG =>
    cartanSingerConcl_of_rootCenter (isSylowTwoOf_top_of_sylow P) hinj hz0 hcenter hscalar honto
      hG

@[expose] def actsBySubgroup (z : K → S) : Subgroup S where
  carrier := {n | ∃ u : Kˣ, ActsBy z n u}
  one_mem' := ⟨1, ActsBy.one fun c => by simp⟩
  mul_mem' := fun ⟨u, hu⟩ ⟨v, hv⟩ => ⟨u * v, hu.mul hv⟩
  inv_mem' := fun ⟨u, hu⟩ => ⟨u⁻¹, hu.inv⟩

theorem exists_actsBy_of_mem_sup {U H : Subgroup S} {z : K → S}
    (hcomm : ∀ c, ∀ t ∈ U, z c * t = t * z c) (hact : ∀ h ∈ H, ∃ u : Kˣ, ActsBy z h u) {n : S}
    (hn : n ∈ U ⊔ H) : ∃ u : Kˣ, ActsBy z n u := by
  have hUA : U ≤ actsBySubgroup z := fun t ht => ⟨1, ActsBy.one fun c => (hcomm c t ht).symm⟩
  have hHA : H ≤ actsBySubgroup z := fun h hh => hact h hh
  exact sup_le hUA hHA hn

theorem cartanSingerCover_of_le {X : Type} [Group X] [Finite X] [Finite K] {C U H : Subgroup X}
    (hUC : U ≤ C) (hU : IsSylowTwoOf U C) (hHC : H ≤ C)
    (hHN : H ≤ Subgroup.normalizer (U : Set X))
    (hNH : C ⊓ Subgroup.normalizer (U : Set X) ≤ U ⊔ H) {z : K → X}
    (hinj : Function.Injective z) (hz0 : z 0 = 1) (hzC : ∀ c, z c ∈ C)
    (hcomm : ∀ c, ∀ t ∈ U, z c * t = t * z c)
    (hcenter : ∀ g ∈ U, (∀ t ∈ U, g * t = t * g) → ∃ c, z c = g)
    (hact : ∀ h ∈ H, ∃ u : Kˣ, ActsBy z h u) (honto : ∀ u : Kˣ, ∃ h ∈ H, ActsBy z h u) :
    CartanSingerCover ↥C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsSylowTwoOf (U.subgroupOf C) ⊤ :=
    CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_subgroupOf_top hU
  set z' : K → ↥C := fun c => ⟨z c, hzC c⟩ with hz'
  have hact' : ∀ (n : ↥C) (u : Kˣ), ActsBy z (n : X) u → ActsBy z' n u := fun n u h c =>
    Subtype.ext (h c)
  refine cartanSingerCover_of_sylow (hP.2.1.toSylow ?_) fun _ _ hG =>
    cartanSingerConcl_of_rootCenter hP (z := z') (fun c d h => hinj (congrArg Subtype.val h))
      (Subtype.ext hz0) (fun g hg hgc => ?_) (fun n hn => ?_) (fun u => ?_) hG
  · exact hU.2.2
  · obtain ⟨c, hc⟩ := hcenter g hg fun t ht => congrArg Subtype.val (hgc ⟨t, hUC ht⟩ ht)
    exact ⟨c, Subtype.ext hc⟩
  · have hn' : (n : X) ∈ C ⊓ Subgroup.normalizer (U : Set X) := by
      refine ⟨n.2, ?_⟩
      have : n ∈ (Subgroup.normalizer (U : Set X)).subgroupOf C := by
        rw [Subgroup.subgroupOf_normalizer_eq hUC]
        exact hn
      exact this
    obtain ⟨u, hu⟩ := exists_actsBy_of_mem_sup hcomm hact (hNH hn')
    exact ⟨u, hact' n u hu⟩
  · obtain ⟨h, hh, hhu⟩ := honto u
    refine ⟨⟨h, hHC hh⟩, ?_, hact' _ u hhu⟩
    have : (⟨h, hHC hh⟩ : ↥C) ∈ (Subgroup.normalizer (U : Set X)).subgroupOf C := hHN hh
    rwa [Subgroup.subgroupOf_normalizer_eq hUC] at this

end CFSG.Quasithin.H13.KG68.Singer
