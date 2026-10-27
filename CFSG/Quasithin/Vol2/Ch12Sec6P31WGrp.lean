module

public import Mathlib.GroupTheory.Sylow

public section

open scoped Pointwise

namespace CFSG.Quasithin.H13.P31Grp

variable {G : Type*} [Group G]

theorem eq_or_eq_of_isCoatom_subgroupOf {K B X : Subgroup G} (hB : IsCoatom (B.subgroupOf K))
    (hBX : B ≤ X) (hXK : X ≤ K) : X = B ∨ X = K := by
  by_cases hXK' : X = K
  · exact Or.inr hXK'
  left
  have hle : B.subgroupOf K ≤ X.subgroupOf K := by
    intro k hk
    exact hBX (Subgroup.mem_subgroupOf.mp hk)
  have hne : X.subgroupOf K ≠ ⊤ := by
    intro htop
    apply hXK'
    apply le_antisymm hXK
    intro k hk
    have hkX : (⟨k, hk⟩ : K) ∈ X.subgroupOf K := by
      rw [htop]
      exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp hkX
  have hnlt : ¬ B.subgroupOf K < X.subgroupOf K := by
    intro hlt
    have htop := hB.2 _ hlt
    exact hne (by simpa using htop)
  have heq : B.subgroupOf K = X.subgroupOf K := by
    rcases eq_or_lt_of_le hle with h | h
    · exact h
    · exact absurd h hnlt
  ext x
  constructor
  · intro hx
    have hkX : (⟨x, hXK hx⟩ : K) ∈ X.subgroupOf K := Subgroup.mem_subgroupOf.mpr hx
    rw [← heq] at hkX
    exact Subgroup.mem_subgroupOf.mp hkX
  · exact fun hx => hBX hx

theorem exists_pSubgroup_permuting [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {T L M Nh Q TL : Subgroup G} (hT : IsPGroup 2 T)
    (hLM : M ≤ Subgroup.normalizer L) (hNhM : Nh ≤ M) (hTNh : T ≤ Subgroup.normalizer Nh)
    (hTLn : T ≤ Subgroup.normalizer L) (hTLdef : TL = T ⊓ L) (hQT : Q ≤ T) (hQNh : Q ≤ Nh)
    (hNhQ : Nh ≤ Subgroup.normalizer Q) (hNhQp : ∀ x ∈ Nh, ∃ n : ℕ, x ^ (p ^ n) ∈ Q)
    (hW : ¬ ⁅Nh, TL⁆ ≤ Q) :
    ∃ P : Subgroup G, P ≤ L ∧ P ≠ ⊥ ∧ IsPGroup p P ∧
      (P : Set G) * (T : Set G) = (T : Set G) * (P : Set G) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨W, hWdef⟩ : ∃ W : Subgroup G, W = ⁅Nh, TL⁆ := ⟨_, rfl⟩
  have hTL_mem : ∀ s ∈ TL, s ∈ T ∧ s ∈ L := by
    intro s hs
    rw [hTLdef] at hs
    exact Subgroup.mem_inf.mp hs
  have hWNh : W ≤ Nh := by
    rw [hWdef, Subgroup.commutator_le]
    intro n hn s hs
    rw [commutatorElement_def]
    have h1 : s * n⁻¹ * s⁻¹ ∈ Nh :=
      (Subgroup.mem_normalizer_iff.mp (hTNh (hTL_mem s hs).1) n⁻¹).mp (Nh.inv_mem hn)
    have h2 : n * s * n⁻¹ * s⁻¹ = n * (s * n⁻¹ * s⁻¹) := by group
    rw [h2]
    exact Nh.mul_mem hn h1
  have hWL : W ≤ L := by
    rw [hWdef, Subgroup.commutator_le]
    intro n hn s hs
    rw [commutatorElement_def]
    have h1 : n * s * n⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hLM (hNhM hn)) s).mp (hTL_mem s hs).2
    exact L.mul_mem h1 (L.inv_mem (hTL_mem s hs).2)
  have hTW : ∀ t ∈ T, ∀ w ∈ W, t * w * t⁻¹ ∈ W := by
    intro t ht w hw
    have hle : ⁅Nh, TL⁆ ≤ ⁅Nh, TL⁆.comap (MulAut.conj t).toMonoidHom := by
      rw [Subgroup.commutator_le]
      intro n hn s hs
      rw [Subgroup.mem_comap]
      show t * (n * s * n⁻¹ * s⁻¹) * t⁻¹ ∈ ⁅Nh, TL⁆
      have hn' : t * n * t⁻¹ ∈ Nh := (Subgroup.mem_normalizer_iff.mp (hTNh ht) n).mp hn
      have hs' : t * s * t⁻¹ ∈ TL := by
        rw [hTLdef]
        exact Subgroup.mem_inf.mpr
          ⟨T.mul_mem (T.mul_mem ht (hTL_mem s hs).1) (T.inv_mem ht),
            (Subgroup.mem_normalizer_iff.mp (hTLn ht) s).mp (hTL_mem s hs).2⟩
      have h3 : t * (n * s * n⁻¹ * s⁻¹) * t⁻¹ =
          (t * n * t⁻¹) * (t * s * t⁻¹) * (t * n * t⁻¹)⁻¹ * (t * s * t⁻¹)⁻¹ := by
        group
      rw [h3]
      exact Subgroup.commutator_mem_commutator hn' hs'
    rw [hWdef] at hw ⊢
    exact hle hw
  haveI hDn : (Q.subgroupOf W).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hgN : (g : G) ∈ Nh := hWNh g.2
    have h1 := (Subgroup.mem_normalizer_iff.mp (hNhQ hgN) (n : G)).mp hn
    simpa using h1⟩
  have hquot : ∀ x : W ⧸ Q.subgroupOf W, ∃ k : ℕ, x ^ (p ^ k) = 1 := by
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨k, hk⟩ := hNhQp (y : G) (hWNh y.2)
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa using hk
  have hTopP : IsPGroup p (⊤ : Subgroup (W ⧸ Q.subgroupOf W)) := by
    intro g
    obtain ⟨k, hk⟩ := hquot (g : W ⧸ Q.subgroupOf W)
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  obtain ⟨S0⟩ : Nonempty (Sylow p W) := inferInstance
  let φ : W →* W ⧸ Q.subgroupOf W := QuotientGroup.mk' (Q.subgroupOf W)
  have hφ : Function.Surjective φ := QuotientGroup.mk_surjective
  have hS1 : (⊤ : Subgroup (W ⧸ Q.subgroupOf W)) = (Sylow.mapSurjective hφ S0).toSubgroup :=
    (Sylow.mapSurjective hφ S0).is_maximal' hTopP le_top
  have hmap : S0.toSubgroup.map φ = ⊤ := by
    calc S0.toSubgroup.map φ = (Sylow.mapSurjective hφ S0).toSubgroup := rfl
      _ = ⊤ := hS1.symm
  obtain ⟨P, hPdef⟩ : ∃ P : Subgroup G, P = S0.toSubgroup.map W.subtype := ⟨_, rfl⟩
  have hPW : P ≤ W := by
    intro x hx
    rw [hPdef] at hx
    obtain ⟨s, _, rfl⟩ := Subgroup.mem_map.mp hx
    exact s.2
  have hPpg : IsPGroup p P := by
    rw [hPdef]
    exact S0.isPGroup'.map W.subtype
  have hdec : ∀ w ∈ W, ∃ p₀ ∈ P, ∃ d ∈ Q, w = p₀ * d := by
    intro w hw
    have hmem : φ ⟨w, hw⟩ ∈ S0.toSubgroup.map φ := by
      rw [hmap]
      exact Subgroup.mem_top _
    obtain ⟨s, hs, hsφ⟩ := Subgroup.mem_map.mp hmem
    have hsφ' : ((s : W) : W ⧸ Q.subgroupOf W) = ((⟨w, hw⟩ : W) : W ⧸ Q.subgroupOf W) := hsφ
    have hq : (s⁻¹ * ⟨w, hw⟩ : W) ∈ Q.subgroupOf W := QuotientGroup.eq.mp hsφ'
    refine ⟨(s : G), ?_, (s : G)⁻¹ * w, ?_, (mul_inv_cancel_left (s : G) w).symm⟩
    · rw [hPdef]
      exact Subgroup.mem_map.mpr ⟨s, hs, rfl⟩
    · have h := Subgroup.mem_subgroupOf.mp hq
      simpa using h
  have hPne : P ≠ ⊥ := by
    intro hP
    apply hW
    intro w hw
    have hwW : w ∈ W := by
      rw [hWdef]
      exact hw
    obtain ⟨p₀, hp₀, d, hd, hwd⟩ := hdec w hwW
    rw [hP, Subgroup.mem_bot] at hp₀
    rw [hwd, hp₀, one_mul]
    exact hd
  have hPD : ∀ w ∈ W, ∃ p₁ ∈ P, ∃ d ∈ T, w = p₁ * d := by
    intro w hw
    obtain ⟨p₁, hp₁, d, hd, hwd⟩ := hdec w hw
    exact ⟨p₁, hp₁, d, hQT hd, hwd⟩
  have hDP : ∀ w ∈ W, ∃ d ∈ T, ∃ p₁ ∈ P, w = d * p₁ := by
    intro w hw
    obtain ⟨p₁, hp₁, d, hd, hwd⟩ := hPD w⁻¹ (W.inv_mem hw)
    refine ⟨d⁻¹, T.inv_mem hd, p₁⁻¹, P.inv_mem hp₁, ?_⟩
    rw [← inv_inv w, hwd, mul_inv_rev]
  refine ⟨P, hPW.trans hWL, hPne, hPpg, ?_⟩
  ext x
  constructor
  · rintro ⟨p₀, hp₀, t, ht, rfl⟩
    have hw : t⁻¹ * p₀ * t ∈ W := by
      have h := hTW t⁻¹ (T.inv_mem ht) p₀ (hPW hp₀)
      rwa [inv_inv] at h
    obtain ⟨d, hd, q, hq, hdq⟩ := hDP (t⁻¹ * p₀ * t) hw
    refine ⟨t * d, T.mul_mem ht hd, q, hq, ?_⟩
    calc t * d * q = t * (d * q) := mul_assoc _ _ _
      _ = t * (t⁻¹ * p₀ * t) := by rw [← hdq]
      _ = p₀ * t := by group
  · rintro ⟨t, ht, p₀, hp₀, rfl⟩
    have hw : t * p₀ * t⁻¹ ∈ W := hTW t ht p₀ (hPW hp₀)
    obtain ⟨p₁, hp₁, d, hd, hpd⟩ := hPD (t * p₀ * t⁻¹) hw
    refine ⟨p₁, hp₁, d * t, T.mul_mem hd ht, ?_⟩
    calc p₁ * (d * t) = p₁ * d * t := (mul_assoc _ _ _).symm
      _ = t * p₀ * t⁻¹ * t := by rw [← hpd]
      _ = t * p₀ := by group

theorem eq_of_le_prod_of_maximal {K₁ K₂ B₁ B₂ Y : Subgroup G}
    [IsSimpleGroup K₁] [IsSimpleGroup K₂]
    (hcomm : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) (hK : K₁ ⊓ K₂ = ⊥)
    (hB₁le : B₁ ≤ K₁) (hB₂le : B₂ ≤ K₂)
    (hB₁ : IsCoatom (B₁.subgroupOf K₁)) (hB₂ : IsCoatom (B₂.subgroupOf K₂))
    (hB₁ne : B₁ ≠ ⊥) (hBY : B₁ ⊔ B₂ ≤ Y) (hYK : Y ≤ K₁ ⊔ K₂) :
    (Y ⊓ K₁ = B₁ ∨ Y ⊓ K₁ = K₁) ∧ (Y ⊓ K₂ = B₂ ∨ Y ⊓ K₂ = K₂) ∧
      Y = (Y ⊓ K₁) ⊔ (Y ⊓ K₂) := by
  have hB₁Y : B₁ ≤ Y := le_trans le_sup_left hBY
  have hB₂Y : B₂ ≤ Y := le_trans le_sup_right hBY
  have hY1 : Y ⊓ K₁ = B₁ ∨ Y ⊓ K₁ = K₁ :=
    eq_or_eq_of_isCoatom_subgroupOf hB₁ (le_inf hB₁Y hB₁le) inf_le_right
  have hY2 : Y ⊓ K₂ = B₂ ∨ Y ⊓ K₂ = K₂ :=
    eq_or_eq_of_isCoatom_subgroupOf hB₂ (le_inf hB₂Y hB₂le) inf_le_right
  have hconj : ∀ b ∈ K₂, ∀ h ∈ K₁, b * h * b⁻¹ = h := by
    intro b hb h hh
    rw [← hcomm h hh b hb, mul_inv_cancel_right]
  have hK2N : K₂ ≤ Subgroup.normalizer K₁ := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [hconj b hb h hh]
      exact hh
    · intro hh
      have h1 : b⁻¹ * (b * h * b⁻¹) * b⁻¹⁻¹ = b * h * b⁻¹ :=
        hconj b⁻¹ (K₂.inv_mem hb) _ hh
      have h2 : h = b⁻¹ * (b * h * b⁻¹) * b⁻¹⁻¹ := by group
      rw [h2, h1]
      exact hh
  have hprod : ∀ y ∈ K₁ ⊔ K₂, ∃ a ∈ K₁, ∃ b ∈ K₂, a * b = y := by
    intro y hy
    have h := Subgroup.coe_mul_of_right_le_normalizer_left K₁ K₂ hK2N
    have hy' : y ∈ ((K₁ ⊔ K₂ : Subgroup G) : Set G) := hy
    rw [h] at hy'
    obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hy'
    exact ⟨a, ha, b, hb, hab⟩
  have hmain : ∀ y ∈ Y, ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = y → a ∈ Y := by
    intro y hy a ha b hb hab
    rcases hY1 with h1 | h1
    · rcases hY2 with h2 | h2
      ·
        have hnorm : ∀ n ∈ K₁, (n ∈ B₁ ↔ a * n * a⁻¹ ∈ B₁) := by
          intro n hn
          have hbn : b * n * b⁻¹ = n := by
            rw [← hcomm n hn b hb, mul_inv_cancel_right]
          have hbn' : b⁻¹ * n * b = n := by
            rw [mul_assoc, hcomm n hn b hb, inv_mul_cancel_left]
          have e1 : y * n * y⁻¹ = a * n * a⁻¹ := by
            rw [← hab]
            calc a * b * n * (a * b)⁻¹ = a * (b * n * b⁻¹) * a⁻¹ := by group
              _ = a * n * a⁻¹ := by rw [hbn]
          have e2 : y⁻¹ * (a * n * a⁻¹) * y = n := by
            rw [← hab]
            calc (a * b)⁻¹ * (a * n * a⁻¹) * (a * b) = b⁻¹ * n * b := by group
              _ = n := hbn'
          constructor
          · intro hnB
            have hmY : a * n * a⁻¹ ∈ Y ⊓ K₁ := by
              refine Subgroup.mem_inf.mpr ⟨?_, K₁.mul_mem (K₁.mul_mem ha hn) (K₁.inv_mem ha)⟩
              rw [← e1]
              exact Y.mul_mem (Y.mul_mem hy (hB₁Y hnB)) (Y.inv_mem hy)
            rw [h1] at hmY
            exact hmY
          · intro hnB
            have hmY : n ∈ Y ⊓ K₁ := by
              refine Subgroup.mem_inf.mpr ⟨?_, hn⟩
              rw [← e2]
              exact Y.mul_mem (Y.mul_mem (Y.inv_mem hy) (hB₁Y hnB)) hy
            rw [h1] at hmY
            exact hmY
        have hNa : (⟨a, ha⟩ : K₁) ∈
            Subgroup.normalizer ((B₁.subgroupOf K₁ : Subgroup K₁) : Set K₁) := by
          rw [Subgroup.mem_normalizer_iff]
          intro h
          rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
          exact hnorm (h : G) h.2
        have hA_le : B₁.subgroupOf K₁ ≤
            Subgroup.normalizer ((B₁.subgroupOf K₁ : Subgroup K₁) : Set K₁) :=
          Subgroup.le_normalizer
        have haB₁ : a ∈ B₁ := by
          rcases eq_or_lt_of_le hA_le with hA | hA
          · rw [← hA] at hNa
            exact Subgroup.mem_subgroupOf.mp hNa
          ·
            have hNtop : Subgroup.normalizer ((B₁.subgroupOf K₁ : Subgroup K₁) : Set K₁) = ⊤ := by
              simpa using hB₁.2 _ hA
            have hall : ∀ g : K₁,
                g ∈ Subgroup.normalizer ((B₁.subgroupOf K₁ : Subgroup K₁) : Set K₁) := by
              intro g
              rw [hNtop]
              exact Subgroup.mem_top g
            haveI hNorm : (B₁.subgroupOf K₁).Normal :=
              ⟨fun n hn g => (Subgroup.mem_normalizer_iff.mp (hall g) n).mp hn⟩
            rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (B₁.subgroupOf K₁) with hbot | htop
            · exfalso
              apply hB₁ne
              apply eq_bot_iff.mpr
              intro x hx
              have hxK : x ∈ K₁ := hB₁le hx
              have hx' : (⟨x, hxK⟩ : K₁) ∈ B₁.subgroupOf K₁ := Subgroup.mem_subgroupOf.mpr hx
              rw [hbot, Subgroup.mem_bot] at hx'
              have hx1 : x = 1 := by simpa using congrArg Subtype.val hx'
              rw [hx1]
              exact Subgroup.one_mem _
            · exact absurd htop hB₁.1
        exact hB₁Y haB₁
      ·
        have hbY' : b ∈ Y ⊓ K₂ := by
          rw [h2]
          exact hb
        have hbY : b ∈ Y := (Subgroup.mem_inf.mp hbY').1
        have hay : a = y * b⁻¹ := by
          rw [← hab]
          group
        rw [hay]
        exact Y.mul_mem hy (Y.inv_mem hbY)
    ·
      have haY' : a ∈ Y ⊓ K₁ := by
        rw [h1]
        exact ha
      exact (Subgroup.mem_inf.mp haY').1
  have hdecomp : Y = (Y ⊓ K₁) ⊔ (Y ⊓ K₂) := by
    apply le_antisymm
    · intro y hy
      obtain ⟨a, ha, b, hb, hab⟩ := hprod y (hYK hy)
      have haY : a ∈ Y := hmain y hy a ha b hb hab
      have hbY : b ∈ Y := by
        have hb' : b = a⁻¹ * y := by
          rw [← hab]
          group
        rw [hb']
        exact Y.mul_mem (Y.inv_mem haY) hy
      have h1 : a ∈ (Y ⊓ K₁) ⊔ (Y ⊓ K₂) :=
        Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨haY, ha⟩)
      have h2 : b ∈ (Y ⊓ K₁) ⊔ (Y ⊓ K₂) :=
        Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨hbY, hb⟩)
      have h3 := ((Y ⊓ K₁) ⊔ (Y ⊓ K₂)).mul_mem h1 h2
      rwa [hab] at h3
    · exact sup_le inf_le_left inf_le_left
  exact ⟨hY1, hY2, hdecomp⟩

end CFSG.Quasithin.H13.P31Grp
