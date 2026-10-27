module

public import CFSG.RankThree.PartOne.SolD3.Main1

public section

namespace CFSG.RankThree.PartOne.SolD3

open CFSG CFSG.Assembly CFSG.CGT.PushingUpLit.SolK CFSG.GH74
open scoped commutatorElement

namespace Hyp3

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} (h : Hyp3 G M X) {a : G}
include h

omit h in
theorem exists_P0 (hb : Blk3 X a) {R₀ : Subgroup G}
    (hRC : R₀ ≤ Subgroup.centralizer (X : Set G)) (hR2 : IsPGroup 2 R₀) :
    ∃ P₀ : Subgroup G, IsPGroup 2 P₀ ∧ Nat.card ↥P₀ = 4 * Nat.card ↥R₀ ∧
      (∀ x, x ∈ P₀ ↔ ∃ w ∈ pCoreOf 2 X, ∃ r ∈ R₀, x = w * r) ∧
      pCoreOf 2 X ≤ P₀ ∧ R₀ ≤ P₀ := by
  classical
  have hcomm : ∀ (w : ↥(pCoreOf 2 X)) (r : ↥R₀),
      Commute ((pCoreOf 2 X).subtype w) (R₀.subtype r) := by
    intro w r
    exact Subgroup.mem_centralizer_iff.1 (hRC r.2) w (pCoreOf_le_self X w.2)
  let φ : ↥(pCoreOf 2 X) × ↥R₀ →* G :=
    MonoidHom.noncommCoprod (pCoreOf 2 X).subtype R₀.subtype hcomm
  have hφ : ∀ p, φ p = (p.1 : G) * (p.2 : G) := fun p => by
    simp [φ, MonoidHom.noncommCoprod_apply]
  have hinj : Function.Injective φ := by
    rintro ⟨⟨w, hw⟩, ⟨r, hr⟩⟩ ⟨⟨w', hw'⟩, ⟨r', hr'⟩⟩ heq
    have h1 : w * r = w' * r' := by simpa [hφ] using heq
    have h2 : w'⁻¹ * w = r' * r⁻¹ := by
      calc w'⁻¹ * w = w'⁻¹ * (w * r) * r⁻¹ := by group
        _ = w'⁻¹ * (w' * r') * r⁻¹ := by rw [h1]
        _ = r' * r⁻¹ := by group
    have hW : w'⁻¹ * w ∈ pCoreOf 2 X := (pCoreOf 2 X).mul_mem ((pCoreOf 2 X).inv_mem hw') hw
    have hRt : w'⁻¹ * w ∈ R₀ := h2 ▸ R₀.mul_mem hr' (R₀.inv_mem hr)
    have h3 : w'⁻¹ * w = 1 := Hyp3.W_inf_C hb hW (hRC hRt)
    have hww : w = w' := by
      calc w = w' * (w'⁻¹ * w) := by group
        _ = w' := by rw [h3, mul_one]
    subst hww
    have : r = r' := mul_left_cancel h1
    subst this
    rfl
  have hcard : Nat.card ↥φ.range = 4 * Nat.card ↥R₀ := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod, hb.card]
  have hpg : IsPGroup 2 ↥φ.range := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hR2
    exact IsPGroup.of_card (n := k + 2) (by rw [hcard, hk]; ring)
  refine ⟨φ.range, hpg, hcard, fun x => ?_, ?_, ?_⟩
  · constructor
    · rintro ⟨p, rfl⟩
      exact ⟨p.1, p.1.2, p.2, p.2.2, (hφ p).symm⟩
    · rintro ⟨w, hw, r, hr, rfl⟩
      exact ⟨(⟨w, hw⟩, ⟨r, hr⟩), hφ _⟩
  · intro w hw
    exact ⟨(⟨w, hw⟩, 1), by simp [hφ]⟩
  · intro r hr
    exact ⟨(1, ⟨r, hr⟩), by simp [hφ]⟩

end Hyp3

theorem gen4_of_outcome_four {G : Type} [Group G] [Finite G] {X : Subgroup G} {a : G}
    (hb : Blk3 X a) (hb64 : ∀ P : Subgroup G, IsPGroup 2 P → Nat.card ↥P ≤ 64)
    {R₀ H : Subgroup G} (hRC : R₀ ≤ Subgroup.centralizer (X : Set G)) (hR2 : IsPGroup 2 R₀)
    (hHR : H ≤ R₀) (hHe : ↥H ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) :
    SectionalTwoRankLE G 4 := by
  classical
  have hH16 : Nat.card ↥H = 16 := by
    rw [Nat.card_congr hHe.toEquiv, Nat.card_prod,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 4) ≃ ZMod 4), Nat.card_zmod]
  obtain ⟨P₀, hP₀2, hP₀card, hP₀mem, hWP, hRP⟩ := Hyp3.exists_P0 hb hRC hR2
  have hR16 : Nat.card ↥R₀ ≤ 16 := by
    have := hb64 P₀ hP₀2
    omega
  have hle16 : 16 ≤ Nat.card ↥R₀ := hH16 ▸ Subgroup.card_le_of_le hHR
  have hHeq : H = R₀ := Subgroup.eq_of_le_of_card_ge hHR (by omega)
  subst hHeq
  have hP64 : Nat.card ↥P₀ = 64 := by omega
  obtain ⟨T, hT⟩ := hP₀2.exists_le_sylow
  have hTP : P₀ = (T : Subgroup G) :=
    Subgroup.eq_of_le_of_card_ge hT (by have := hb64 T T.isPGroup'; omega)
  refine sectionalTwoRankLE_four_of_noE32G T ?_
  rw [← hTP]
  have hΩ : Nat.card {r : ↥H // r * r = 1} = 4 := by
    have e : {r : ↥H // r * r = 1} ≃
        {z : Multiplicative (ZMod 4) × Multiplicative (ZMod 4) // z * z = 1} :=
      hHe.toEquiv.subtypeEquiv (fun r => by
        change r * r = 1 ↔ hHe r * hHe r = 1
        constructor
        · intro h
          rw [← map_mul, h, map_one]
        · intro h
          apply hHe.injective
          rw [map_mul, h, map_one])
    rw [Nat.card_congr e, Nat.card_eq_fintype_card]
    decide
  refine noE32G_of_card_le_64 (by omega) ?_ ?_
  · intro B hBP hB32
    by_contra hcon
    push Not at hcon
    have hdec : ∀ x : ↥B, ∃ w ∈ pCoreOf 2 X, ∃ r ∈ H, (x : G) = w * r :=
      fun x => (hP₀mem x).1 (hBP x.2)
    choose f hfW r hrR hxr using hdec
    have hr2 : ∀ x : ↥B, r x * r x = 1 := by
      intro x
      have h1 := (hcon x x.2 x x.2).2
      rw [hxr x] at h1
      have hcomm : f x * r x = r x * f x :=
        Subgroup.mem_centralizer_iff.1 (hRC (hrR x)) (f x) (pCoreOf_le_self X (hfW x))
      have hw2 := hb.sq (f x) (hfW x)
      calc r x * r x = (f x * f x) * (r x * r x) := by rw [hw2, one_mul]
        _ = f x * (f x * r x) * r x := by group
        _ = f x * (r x * f x) * r x := by rw [hcomm]
        _ = (f x * r x) * (f x * r x) := by group
        _ = 1 := h1
    let g : ↥B → ↥(pCoreOf 2 X) × {r : ↥H // r * r = 1} := fun x =>
      (⟨f x, hfW x⟩, ⟨⟨r x, hrR x⟩, Subtype.ext (hr2 x)⟩)
    have hginj : Function.Injective g := by
      intro x y hxy
      have e1 : f x = f y := congrArg (fun z => (z.1 : G)) hxy
      have e2 : r x = r y := congrArg (fun z => ((z.2 : {r : ↥H // r * r = 1}) : ↥H).1) hxy
      exact Subtype.ext (by rw [hxr x, hxr y, e1, e2])
    have := Nat.card_le_card_of_injective g hginj
    rw [Nat.card_prod, hb.card, hΩ] at this
    omega
  · intro _
    let i₁ : ↥H := hHe.symm (Multiplicative.ofAdd 1, 1)
    let i₂ : ↥H := hHe.symm (1, Multiplicative.ofAdd 1)
    have k1 : ((Multiplicative.ofAdd (1 : ZMod 4), (1 : Multiplicative (ZMod 4))) :
        Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) ^ 2 ≠ 1 := by decide
    have k2 : (((1 : Multiplicative (ZMod 4)), Multiplicative.ofAdd (1 : ZMod 4)) :
        Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) ^ 2 ≠ 1 := by decide
    have k3 : ((Multiplicative.ofAdd (1 : ZMod 4), (1 : Multiplicative (ZMod 4))) :
        Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) ^ 2 ≠
        (((1 : Multiplicative (ZMod 4)), Multiplicative.ofAdd (1 : ZMod 4)) :
        Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) ^ 2 := by decide
    have hi1 : i₁ ^ 2 ≠ 1 := fun h => k1 (by simpa [i₁] using congrArg hHe h)
    have hi2 : i₂ ^ 2 ≠ 1 := fun h => k2 (by simpa [i₂] using congrArg hHe h)
    have hi12 : i₁ ^ 2 ≠ i₂ ^ 2 := fun h => k3 (by simpa [i₁, i₂] using congrArg hHe h)
    refine ⟨(i₁ : G) ^ 2, (i₂ : G) ^ 2, fun h => hi1 (Subtype.ext (by simpa using h)),
      fun h => hi2 (Subtype.ext (by simpa using h)),
      fun h => hi12 (Subtype.ext (by simpa using h)), Or.inl ⟨i₁, hRP i₁.2, rfl⟩,
      Or.inl ⟨i₂, hRP i₂.2, rfl⟩⟩

theorem gen4_of_outcome_three {G : Type} [Group G] [Finite G] {M X : Subgroup G} {a : G}
    (h : Hyp3 G M X) (hb : Blk3 X a)
    (hb64 : ∀ P : Subgroup G, IsPGroup 2 P → Nat.card ↥P ≤ 64) {R₀ : Subgroup G}
    (hRC : R₀ ≤ Subgroup.centralizer (X : Set G)) (hR2 : IsPGroup 2 R₀)
    (hRmax : ∀ U : Subgroup G, U ≤ Subgroup.centralizer (X : Set G) → IsPGroup 2 U →
      R₀ ≤ U → U = R₀)
    (hQ8 : Nonempty (↥R₀ ≃* QuaternionGroup 2)) : SectionalTwoRankLE G 4 := by
  classical
  obtain ⟨e⟩ := hQ8
  have hR8 : Nat.card ↥R₀ = 8 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  obtain ⟨P₀, hP₀2, hP₀card, hP₀mem, hWP, hRP⟩ := Hyp3.exists_P0 hb hRC hR2
  have hP32 : Nat.card ↥P₀ = 32 := by omega
  have hP₀M : P₀ ≤ M := by
    intro x hx
    obtain ⟨w, hw, r, hr, rfl⟩ := (hP₀mem x).1 hx
    exact M.mul_mem (h.le (pCoreOf_le_self X hw)) (h.centralizer_X_le_M hb (hRC hr))
  obtain ⟨S, T, hPS, hSM, hS2, hSmax, hST, hTM⟩ := exists_sylow_pair hP₀2 hP₀M
  have hT64 : Nat.card ↥(T : Subgroup G) ≤ 64 := hb64 T T.isPGroup'
  have hPT : P₀ ≤ (T : Subgroup G) := hPS.trans hST
  let z : ↥R₀ := e.symm (QuaternionGroup.a 2)
  have hzz : z * z = 1 := by
    have : (QuaternionGroup.a 2 : QuaternionGroup 2) * QuaternionGroup.a 2 = 1 := by decide
    show e.symm (QuaternionGroup.a 2) * e.symm (QuaternionGroup.a 2) = 1
    rw [← map_mul, this, map_one]
  have hz1 : z ≠ 1 := by
    intro hz
    have : (QuaternionGroup.a 2 : QuaternionGroup 2) ≠ 1 := by decide
    exact this (e.symm.injective (by rw [map_one]; exact hz))
  have hinv : ∀ r : ↥R₀, r * r = 1 → r = 1 ∨ r = z := by
    have key : ∀ x : QuaternionGroup 2, x * x = 1 → x = 1 ∨ x = QuaternionGroup.a 2 := by decide
    intro r hr
    have h1 : e r * e r = 1 := by rw [← map_mul, hr, map_one]
    rcases key _ h1 with h2 | h2
    · left
      exact e.injective (by rw [h2, map_one])
    · right
      exact e.injective (by rw [h2]; simp [z])
  let i₀ : ↥R₀ := e.symm (QuaternionGroup.a 1)
  have hi₀ : i₀ ^ 2 = z := by
    have : (QuaternionGroup.a 1 : QuaternionGroup 2) ^ 2 = QuaternionGroup.a 2 := by decide
    show e.symm (QuaternionGroup.a 1) ^ 2 = e.symm (QuaternionGroup.a 2)
    rw [← map_pow, this]
  have hzG1 : (z : G) ≠ 1 := fun hh => hz1 (Subtype.ext hh)
  refine sectionalTwoRankLE_four_of_noE32G T ?_
  refine noE32G_of_card_le_64 hT64 ?_ ?_
  ·
    intro B hBT hB32
    by_contra hcon
    push Not at hcon
    have hB' : Nat.card ↥(B ⊓ P₀ : Subgroup G) ≤ 8 := by
      have hdec : ∀ x : ↥(B ⊓ P₀ : Subgroup G), ∃ w ∈ pCoreOf 2 X, ∃ r ∈ R₀, (x : G) = w * r :=
        fun x => (hP₀mem x).1 (Subgroup.mem_inf.1 x.2).2
      choose f hfW r hrR hxr using hdec
      have hr2 : ∀ x : ↥(B ⊓ P₀ : Subgroup G), r x * r x = 1 := by
        intro x
        have h1 := (hcon x (Subgroup.mem_inf.1 x.2).1 x (Subgroup.mem_inf.1 x.2).1).2
        rw [hxr x] at h1
        have hcomm : f x * r x = r x * f x :=
          Subgroup.mem_centralizer_iff.1 (hRC (hrR x)) (f x) (pCoreOf_le_self X (hfW x))
        have hw2 := hb.sq (f x) (hfW x)
        calc r x * r x = (f x * f x) * (r x * r x) := by rw [hw2, one_mul]
          _ = f x * (f x * r x) * r x := by group
          _ = f x * (r x * f x) * r x := by rw [hcomm]
          _ = (f x * r x) * (f x * r x) := by group
          _ = 1 := h1
      let g : ↥(B ⊓ P₀ : Subgroup G) → ↥(pCoreOf 2 X) × Fin 2 := fun x =>
        (⟨f x, hfW x⟩, if r x = 1 then 0 else 1)
      have hginj : Function.Injective g := by
        intro x y hxy
        have e1 : f x = f y := congrArg (fun q => (q.1 : G)) hxy
        have e2 : (if r x = 1 then (0 : Fin 2) else 1) = (if r y = 1 then 0 else 1) :=
          congrArg Prod.snd hxy
        have e3 : r x = r y := by
          have hx := hinv ⟨r x, hrR x⟩ (Subtype.ext (hr2 x))
          have hy := hinv ⟨r y, hrR y⟩ (Subtype.ext (hr2 y))
          by_cases hrx : r x = 1 <;> by_cases hry : r y = 1
          · rw [hrx, hry]
          · simp [hrx, hry] at e2
          · simp [hrx, hry] at e2
          · have h1 : (⟨r x, hrR x⟩ : ↥R₀) = z := by
              rcases hx with h' | h'
              · exact absurd (congrArg Subtype.val h') hrx
              · exact h'
            have h2 : (⟨r y, hrR y⟩ : ↥R₀) = z := by
              rcases hy with h' | h'
              · exact absurd (congrArg Subtype.val h') hry
              · exact h'
            have := congrArg Subtype.val (h1.trans h2.symm)
            exact this
        exact Subtype.ext (by rw [hxr x, hxr y, e1, e3])
      have := Nat.card_le_card_of_injective g hginj
      rw [Nat.card_prod, hb.card] at this
      simpa using this
    have hB2 : Nat.card ↥B ≤ 2 * Nat.card ↥(B ⊓ P₀ : Subgroup G) := by
      by_cases hBP : B ≤ P₀
      · have : B ⊓ P₀ = B := inf_eq_left.2 hBP
        rw [this]
        omega
      · obtain ⟨u, huB, huP⟩ := Set.not_subset.1 hBP
        have hne : P₀ ≠ (T : Subgroup G) := fun hh => huP (hh ▸ hBT huB)
        have hidx := index_two_of_lt hPT hne (by omega)
        exact card_le_two_mul_inf hidx hBT huB huP
    omega
  ·
    intro hT64'
    by_cases hs : ∃ s ∈ S, ¬ ∀ w ∈ pCoreOf 2 X, s * w * s⁻¹ = w
    · obtain ⟨s, hsS, hns⟩ := hs
      push Not at hns
      obtain ⟨w₁, hw₁, hsw⟩ := hns
      have hvW : s * w₁ * s⁻¹ * w₁⁻¹ ∈ pCoreOf 2 X :=
        (pCoreOf 2 X).mul_mem (h.W_normalized (hSM hsS) hw₁) ((pCoreOf 2 X).inv_mem hw₁)
      have hv1 : s * w₁ * s⁻¹ * w₁⁻¹ ≠ 1 := by
        intro hv
        apply hsw
        calc s * w₁ * s⁻¹ = (s * w₁ * s⁻¹ * w₁⁻¹) * w₁ := by group
          _ = w₁ := by rw [hv, one_mul]
      have hu1 : ((i₀ : G)) ^ 2 ≠ 1 := by
        intro hh
        have : i₀ ^ 2 = 1 := Subtype.ext (by simpa using hh)
        rw [hi₀] at this
        exact hz1 this
      have huv : ((i₀ : G)) ^ 2 ≠ s * w₁ * s⁻¹ * w₁⁻¹ := by
        intro hh
        have hu : ((i₀ : G)) ^ 2 ∈ pCoreOf 2 X := hh ▸ hvW
        have huC : ((i₀ : G)) ^ 2 ∈ Subgroup.centralizer (X : Set G) :=
          (Subgroup.centralizer (X : Set G)).pow_mem (hRC i₀.2) 2
        exact hu1 (Hyp3.W_inf_C hb hu huC)
      exact ⟨(i₀ : G) ^ 2, s * w₁ * s⁻¹ * w₁⁻¹, hu1, hv1, huv,
        Or.inl ⟨i₀, hPT (hRP i₀.2), rfl⟩,
        Or.inr ⟨s, hST hsS, w₁, hPT (hWP hw₁), by simp [commutatorElement_def]⟩⟩
    · exfalso
      push Not at hs
      have hSP : S ≤ P₀ := by
        intro s hsS
        obtain ⟨w, hw, hwC⟩ := h.exists_mul_centralizer hb (hSM hsS) (hs s hsS)
        have hcS : w⁻¹ * s ∈ S := S.mul_mem (S.inv_mem (hPS (hWP hw))) hsS
        have hcR : w⁻¹ * s ∈ R₀ := by
          have h1 := hRmax (Subgroup.centralizer (X : Set G) ⊓ S) inf_le_left
            (hS2.of_injective (Subgroup.inclusion (inf_le_right :
              Subgroup.centralizer (X : Set G) ⊓ S ≤ S)) (Subgroup.inclusion_injective _))
            (fun r hr => Subgroup.mem_inf.2 ⟨hRC hr, hPS (hRP hr)⟩)
          rw [← h1]
          exact Subgroup.mem_inf.2 ⟨hwC, hcS⟩
        have : s = w * (w⁻¹ * s) := by group
        rw [this]
        exact (hP₀mem _).2 ⟨w, hw, w⁻¹ * s, hcR, rfl⟩
      have hSeq : S = P₀ := le_antisymm hSP hPS
      have hne : S ≠ (T : Subgroup G) := by
        intro heq
        rw [← heq, hSeq] at hT64'
        omega
      obtain ⟨t, htT, htS, htN⟩ := exists_mem_normalizer_of_lt T.isPGroup' hST hne
      have htM : t ∉ M := fun htM => htS (hTM ▸ Subgroup.mem_inf.2 ⟨htT, htM⟩)
      have hzC : (z : G) ∈ Subgroup.centralizer (X : Set G) := hRC z.2
      have hzord : orderOf (z : G) = 2 := by
        refine orderOf_eq_prime (by simpa [pow_two] using congrArg Subtype.val hzz) hzG1
      have hZ2 : IsPGroup 2 (Subgroup.zpowers (z : G)) :=
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzord]; simp)
      have hZC : Subgroup.zpowers (z : G) ≤ Subgroup.centralizer (X : Set G) :=
        (Subgroup.zpowers_le).2 hzC
      obtain ⟨A, hA2, -, hAmem, hWA, hZA⟩ := Hyp3.exists_P0 hb hZC hZ2
      have hAne : A ≠ ⊥ := fun hbot => hb.W_ne_bot (le_bot_iff.1 (hbot ▸ hWA))
      have hr2 : ∀ r ∈ Subgroup.zpowers (z : G), r * r = 1 := by
        intro r hr
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hr
        have hzz' : (z : G) * (z : G) = 1 := by simpa using congrArg Subtype.val hzz
        have hz2 : (z : G) ^ 2 = 1 := by rw [pow_two]; exact hzz'
        calc (z : G) ^ k * (z : G) ^ k = (z : G) ^ (k + k) := by rw [zpow_add]
          _ = ((z : G) ^ 2) ^ k := by rw [← two_mul, zpow_mul]; norm_cast
          _ = 1 := by rw [hz2, one_zpow]
      have hAS : A ≤ S := by
        intro y hy
        obtain ⟨w, hw, r, hr, rfl⟩ := (hAmem y).1 hy
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hr
        rw [hSeq]
        exact (hP₀mem _).2 ⟨w, hw, (z : G) ^ k, (zpow_mem z.2 k), rfl⟩
      have hXA : ∀ x' ∈ X, ∀ y ∈ A, x' * y * x'⁻¹ ∈ A := by
        intro x' hx' y hy
        obtain ⟨w, hw, r, hr, rfl⟩ := (hAmem y).1 hy
        have hrC := hZC hr
        have hcomm : x' * r = r * x' := Subgroup.mem_centralizer_iff.1 hrC x' hx'
        rw [hAmem]
        refine ⟨x' * w * x'⁻¹, pCoreOf_normalized X hx' hw, r, hr, ?_⟩
        calc x' * (w * r) * x'⁻¹ = (x' * w * x'⁻¹) * (x' * r * x'⁻¹) := by group
          _ = (x' * w * x'⁻¹) * r := by
            congr 1
            rw [hcomm]
            group
      have hXN : X ≤ Subgroup.normalizer (A : Set G) := by
        intro x' hx'
        rw [Subgroup.mem_normalizer_iff]
        intro y
        exact ⟨fun hy => hXA x' hx' y hy, fun hy => by
          have := hXA x'⁻¹ (X.inv_mem hx') _ hy
          simpa [mul_assoc] using this⟩
      have hloc : IsPLocal 2 (Subgroup.normalizer (A : Set G)) := ⟨A, hAne, hA2, rfl⟩
      have hle := local_le_of_unique h.unique hloc hXN
      have hnormA : ∀ t' ∈ Subgroup.normalizer (S : Set G), ∀ y ∈ A, t' * y * t'⁻¹ ∈ A := by
        intro t' ht' y hy
        obtain ⟨w, hw, r, hr, rfl⟩ := (hAmem y).1 hy
        have hy2 : (w * r) * (w * r) = 1 := by
          have hcomm : w * r = r * w :=
            Subgroup.mem_centralizer_iff.1 (hZC hr) w (pCoreOf_le_self X hw)
          have hw2 := hb.sq w hw
          calc (w * r) * (w * r) = w * (r * w) * r := by group
            _ = w * (w * r) * r := by rw [← hcomm]
            _ = (w * w) * (r * r) := by group
            _ = 1 := by rw [hw2, hr2 r hr, one_mul]
        have hyS : w * r ∈ S := hAS hy
        have h1 : t' * (w * r) * t'⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.1 ht' _).1 hyS
        have h2 : (t' * (w * r) * t'⁻¹) * (t' * (w * r) * t'⁻¹) = 1 := by
          calc (t' * (w * r) * t'⁻¹) * (t' * (w * r) * t'⁻¹)
              = t' * ((w * r) * (w * r)) * t'⁻¹ := by group
            _ = 1 := by rw [hy2]; group
        have h1' : t' * (w * r) * t'⁻¹ ∈ P₀ := hSeq ▸ h1
        obtain ⟨w', hw', r', hr', hq⟩ := (hP₀mem _).1 h1'
        have hr'2 : r' * r' = 1 := by
          have hcomm : w' * r' = r' * w' :=
            Subgroup.mem_centralizer_iff.1 (hRC hr') w' (pCoreOf_le_self X hw')
          have hw2 := hb.sq w' hw'
          rw [hq] at h2
          calc r' * r' = (w' * w') * (r' * r') := by rw [hw2, one_mul]
            _ = w' * (w' * r') * r' := by group
            _ = w' * (r' * w') * r' := by rw [hcomm]
            _ = (w' * r') * (w' * r') := by group
            _ = 1 := h2
        have hr'z : r' ∈ Subgroup.zpowers (z : G) := by
          rcases hinv ⟨r', hr'⟩ (Subtype.ext hr'2) with h' | h'
          · have : r' = 1 := congrArg Subtype.val h'
            rw [this]
            exact Subgroup.one_mem _
          · have : r' = (z : G) := congrArg Subtype.val h'
            rw [this]
            exact Subgroup.mem_zpowers _
        rw [hAmem]
        exact ⟨w', hw', r', hr'z, hq⟩
      have htA : t ∈ Subgroup.normalizer (A : Set G) := by
        rw [Subgroup.mem_normalizer_iff]
        intro y
        refine ⟨fun hy => hnormA t htN y hy, fun hy => ?_⟩
        have hinvN : t⁻¹ ∈ Subgroup.normalizer (S : Set G) := (Subgroup.normalizer _).inv_mem htN
        have := hnormA t⁻¹ hinvN _ hy
        simpa [mul_assoc] using this
      exact htM (hle htA)

end CFSG.RankThree.PartOne.SolD3
