module

public import CFSG.Quasithin.Vol2.E2SevenKG1
public import CFSG.Quasithin.Vol2.E2SevenBender
public import CFSG.Walter.PSL2Facts.Even
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderLinearBorel

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6

namespace E2

open scoped MatrixGroups

section Borel

variable {Y : Type} [Group Y] [Finite Y]

omit [Finite Y] in
theorem mem_sylow_of_mem_normalizer (S : Sylow 2 Y) {R : Subgroup Y} (hR : IsPGroup 2 R) {g : Y}
    (hgR : g ∈ R) (hgN : g ∈ Subgroup.normalizer ((S : Subgroup Y) : Set Y)) :
    g ∈ (S : Subgroup Y) := by
  have h2 : IsPGroup 2 ↥(Subgroup.zpowers g ⊔ (S : Subgroup Y)) :=
    IsPGroup.to_sup_of_normal_right' (hR.to_le (Subgroup.zpowers_le.mpr hgR)) S.isPGroup'
      (Subgroup.zpowers_le.mpr hgN)
  have := S.is_maximal' h2 le_sup_right
  rw [← this]
  exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)

theorem exists_smul_eq_of_ne (P : Sylow 2 Y)
    (hsyl : Nat.card (Sylow 2 Y) = Nat.card (P : Subgroup Y) + 1)
    (hTI : ∀ y : Y, y ∉ Subgroup.normalizer ((P : Subgroup Y) : Set Y) →
      (P : Subgroup Y) ⊓ ((y • P : Sylow 2 Y) : Subgroup Y) = ⊥)
    {S S' : Sylow 2 Y} (hSP : S ≠ P) (hS'P : S' ≠ P) :
    ∃ g ∈ (P : Subgroup Y), g • S = S' := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := (P : Subgroup Y) with hQ
  have hstab : MulAction.stabilizer Q S = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    rw [MulAction.mem_stabilizer_iff] at hg
    have hg' : (g : Y) • S = S := hg
    have hgS := mem_sylow_of_mem_normalizer S P.isPGroup' g.2
      (Sylow.smul_eq_iff_mem_normalizer.mp hg')
    obtain ⟨y, rfl⟩ := MulAction.exists_smul_eq Y P S
    have hyN : y ∉ Subgroup.normalizer (Q : Set Y) := fun h =>
      hSP (Sylow.smul_eq_iff_mem_normalizer.mpr h)
    have : (g : Y) ∈ Q ⊓ ((y • P : Sylow 2 Y) : Subgroup Y) := ⟨g.2, hgS⟩
    rw [hTI y hyN] at this
    exact (Subgroup.mem_bot).mpr (Subtype.ext ((Subgroup.mem_bot).mp this))
  have hcard : Set.ncard (MulAction.orbit Q S) = Nat.card Q := by
    rw [← Nat.card_coe_set_eq, Nat.card_congr (MulAction.orbitEquivQuotientStabilizer _ S)]
    show (MulAction.stabilizer Q S).index = _
    rw [hstab, Subgroup.index_bot]
  have hsub : MulAction.orbit Q S ⊆ {P}ᶜ := by
    rintro _ ⟨g, rfl⟩ h
    apply hSP
    have h' : (g : Y) • S = P := h
    calc S = (g : Y)⁻¹ • ((g : Y) • S) := by rw [inv_smul_smul]
      _ = (g : Y)⁻¹ • P := by rw [h']
      _ = P := Sylow.smul_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer (Q.inv_mem g.2))
  have hcompl : Set.ncard ({P}ᶜ : Set (Sylow 2 Y)) = Nat.card Q := by
    rw [Set.ncard_compl, Set.ncard_singleton, hsyl]
    omega
  have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [hcompl, hcard]) (Set.toFinite _)
  have hS' : S' ∈ MulAction.orbit Q S := heq ▸ hS'P
  obtain ⟨g, hg⟩ := hS'
  exact ⟨g, g.2, hg⟩

theorem one_lt_card_normalizer_inf (P : Sylow 2 Y)
    (hsyl : Nat.card (Sylow 2 Y) = Nat.card (P : Subgroup Y) + 1)
    (hTI : ∀ y : Y, y ∉ Subgroup.normalizer ((P : Subgroup Y) : Set Y) →
      (P : Subgroup Y) ⊓ ((y • P : Sylow 2 Y) : Subgroup Y) = ⊥)
    (hB : Nat.card (Subgroup.normalizer ((P : Subgroup Y) : Set Y)) =
      Nat.card (P : Subgroup Y) * (Nat.card (P : Subgroup Y) - 1))
    (hP4 : 4 ≤ Nat.card (P : Subgroup Y)) {S : Sylow 2 Y} (hSP : S ≠ P) :
    1 < Nat.card ↥(Subgroup.normalizer ((P : Subgroup Y) : Set Y) ⊓
      Subgroup.normalizer ((S : Subgroup Y) : Set Y)) := by
  classical
  set Q := (P : Subgroup Y) with hQ
  set N := Subgroup.normalizer (Q : Set Y) with hN
  have horbN : MulAction.orbit N S = {P}ᶜ := by
    apply le_antisymm
    · rintro _ ⟨g, rfl⟩ h
      apply hSP
      have h' : (g : Y) • S = P := h
      calc S = (g : Y)⁻¹ • ((g : Y) • S) := by rw [inv_smul_smul]
        _ = (g : Y)⁻¹ • P := by rw [h']
        _ = P := Sylow.smul_eq_iff_mem_normalizer.mpr (N.inv_mem g.2)
    · intro S' hS'
      obtain ⟨g, hg, hgS⟩ := exists_smul_eq_of_ne P hsyl hTI hSP hS'
      exact ⟨⟨g, Subgroup.le_normalizer hg⟩, hgS⟩
  have hindex : (MulAction.stabilizer N S).index = Nat.card Q := by
    have h1 := Nat.card_congr (MulAction.orbitEquivQuotientStabilizer N S)
    show Nat.card (↥N ⧸ MulAction.stabilizer N S) = _
    rw [← h1, horbN, Nat.card_coe_set_eq, Set.ncard_compl, Set.ncard_singleton, hsyl]
    omega
  have hmul := (MulAction.stabilizer N S).card_mul_index
  rw [hindex, hB] at hmul
  have hQpos : 0 < Nat.card Q := Nat.card_pos
  have hst : Nat.card (MulAction.stabilizer N S) = Nat.card Q - 1 :=
    Nat.eq_of_mul_eq_mul_right hQpos (hmul.trans (mul_comm _ _))
  have hle : (MulAction.stabilizer N S).map N.subtype ≤
      N ⊓ Subgroup.normalizer ((S : Subgroup Y) : Set Y) := by
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨g.2, Sylow.smul_eq_iff_mem_normalizer.mp hg⟩
  have h1 := Subgroup.card_le_of_le hle
  rw [Subgroup.card_map_of_injective N.subtype_injective, hst] at h1
  omega

theorem eq_one_of_fix_normalizer (P : Sylow 2 Y)
    (hcent : ∀ t ∈ (P : Subgroup Y), t ≠ 1 → ∀ y : Y, y * t = t * y → y ∈ (P : Subgroup Y))
    (hsyl : Nat.card (Sylow 2 Y) = Nat.card (P : Subgroup Y) + 1)
    (hB : Nat.card (Subgroup.normalizer ((P : Subgroup Y) : Set Y)) =
      Nat.card (P : Subgroup Y) * (Nat.card (P : Subgroup Y) - 1))
    (hP4 : 4 ≤ Nat.card (P : Subgroup Y)) (hs : IsSimpleGroup Y)
    (hTI : ∀ y : Y, y ∉ Subgroup.normalizer ((P : Subgroup Y) : Set Y) →
      (P : Subgroup Y) ⊓ ((y • P : Sylow 2 Y) : Subgroup Y) = ⊥)
    (α : MulAut Y) (hα : ∀ b ∈ Subgroup.normalizer ((P : Subgroup Y) : Set Y), α b = b) :
    α = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := (P : Subgroup Y) with hQ
  set N := Subgroup.normalizer (Q : Set Y) with hN
  have hQN : Q ≤ N := Subgroup.le_normalizer
  have hαN : ∀ y, α y ∈ N ↔ y ∈ N := by
    intro y
    constructor
    · intro h
      have h1 := hα _ h
      have h2 : y = α y := α.injective h1.symm
      rw [h2]
      exact h
    · intro h
      rw [hα y h]
      exact h
  have hsmul_coe : ∀ y : Y, ((y • P : Sylow 2 Y) : Subgroup Y) =
      Q.map (MulAut.conj y).toMonoidHom := fun y => by
    rw [Sylow.coe_subgroup_smul]
    rfl
  have hfix : ∀ y : Y, y⁻¹ * α y ∈ N := by
    intro y
    by_cases hyN : y ∈ N
    · rw [hα y hyN, inv_mul_cancel]
      exact N.one_mem
    have hαyN : α y ∉ N := fun h => hyN ((hαN y).mp h)
    set S := y • P with hSdef
    have hSP : S ≠ P := fun h => hyN (Sylow.smul_eq_iff_mem_normalizer.mp h)
    have hS'P : α y • P ≠ P := fun h => hαyN (Sylow.smul_eq_iff_mem_normalizer.mp h)
    obtain ⟨t, htQ, ht⟩ := exists_smul_eq_of_ne P hsyl hTI hSP hS'P
    have h0 : Q ⊓ (S : Subgroup Y) = ⊥ := hTI y hyN
    have hαS : ((α y • P : Sylow 2 Y) : Subgroup Y) = (S : Subgroup Y).map α.toMonoidHom := by
      rw [hsmul_coe, hSdef, hsmul_coe, Subgroup.map_map]
      ext z
      simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MonoidHom.coe_comp,
        Function.comp_apply, MulAut.conj_apply]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, hx, by rw [map_mul, map_mul, map_inv, hα x (hQN hx)]⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, hx, by rw [map_mul, map_mul, map_inv, hα x (hQN hx)]⟩
    have hE : ∀ e ∈ N ⊓ Subgroup.normalizer ((S : Subgroup Y) : Set Y), e * t = t * e := by
      rintro e ⟨heN, heS⟩
      have hts : ((t • S : Sylow 2 Y) : Subgroup Y) =
          (S : Subgroup Y).map (MulAut.conj t).toMonoidHom := by
        rw [Sylow.coe_subgroup_smul]
        rfl
      have heS0 : e ∈ Subgroup.normalizer (((t • S : Sylow 2 Y) : Subgroup Y) : Set Y) := by
        rw [ht, hαS, ← hα e heN, ← Subgroup.map_equiv_normalizer_eq]
        exact Subgroup.mem_map_of_mem _ heS
      rw [hts, ← Subgroup.map_equiv_normalizer_eq] at heS0
      obtain ⟨z, hz, hze⟩ := heS0
      have hze' : t * z * t⁻¹ = e := hze
      have hz' : t⁻¹ * e * t ∈ Subgroup.normalizer ((S : Subgroup Y) : Set Y) := by
        rw [← hze']
        simpa [mul_assoc] using hz
      have hcN : e⁻¹ * (t⁻¹ * e * t) ∈ Subgroup.normalizer ((S : Subgroup Y) : Set Y) :=
        Subgroup.mul_mem _ (Subgroup.inv_mem _ heS) hz'
      have hcQ : e⁻¹ * (t⁻¹ * e * t) ∈ Q := by
        have h1 : e⁻¹ * t⁻¹ * e ∈ Q := by
          have := (Subgroup.mem_normalizer_iff.mp (N.inv_mem heN) t⁻¹).mp (Q.inv_mem htQ)
          simpa using this
        have := Q.mul_mem h1 htQ
        simpa [mul_assoc] using this
      have hcS := mem_sylow_of_mem_normalizer S P.isPGroup' hcQ hcN
      have hmem : e⁻¹ * (t⁻¹ * e * t) ∈ Q ⊓ (S : Subgroup Y) := ⟨hcQ, hcS⟩
      rw [h0, Subgroup.mem_bot] at hmem
      have := congrArg (fun w => t * e * w) hmem
      simp only [mul_one] at this
      rw [← this]
      group
    have ht1 : t = 1 := by
      by_contra ht1
      have hle : N ⊓ Subgroup.normalizer ((S : Subgroup Y) : Set Y) ≤ ⊥ := by
        intro e he
        have heQ : e ∈ Q := hcent _ htQ ht1 e (hE e he)
        have heS := mem_sylow_of_mem_normalizer S P.isPGroup' heQ he.2
        have hmem : e ∈ Q ⊓ (S : Subgroup Y) := ⟨heQ, heS⟩
        rw [h0] at hmem
        exact hmem
      have h1 := Subgroup.card_le_of_le hle
      rw [Subgroup.card_bot] at h1
      have h2 : 1 < Nat.card ↥(N ⊓ Subgroup.normalizer ((S : Subgroup Y) : Set Y)) :=
        one_lt_card_normalizer_inf P hsyl hTI hB hP4 hSP
      omega
    rw [ht1, one_smul] at ht
    apply Sylow.smul_eq_iff_mem_normalizer.mp
    rw [mul_smul, ← ht, hSdef, inv_smul_smul]
  have hcore : ∀ x, x⁻¹ * α x ∈ N.normalCore := by
    intro x b
    have h1 := hfix (b⁻¹)
    have h2 := hfix (x * b⁻¹)
    have e : b * (x⁻¹ * α x) * b⁻¹ = (x * b⁻¹)⁻¹ * α (x * b⁻¹) * (b⁻¹⁻¹ * α b⁻¹)⁻¹ := by
      rw [map_mul]
      group
    rw [e]
    exact N.mul_mem h2 (N.inv_mem h1)
  have hNtop : N ≠ ⊤ := by
    intro h
    have hnorm : Q.Normal := Subgroup.normalizer_eq_top_iff.mp h
    have hu : Unique (Sylow 2 Y) := Sylow.unique_of_normal P hnorm
    have h1 : Nat.card (Sylow 2 Y) = 1 := Nat.card_unique
    omega
  have hcorebot : N.normalCore = ⊥ := by
    rcases hs.eq_bot_or_eq_top_of_normal N.normalCore with h | h
    · exact h
    · exact absurd (top_le_iff.mp (h ▸ N.normalCore_le)) hNtop
  ext x
  have h1 := hcore x
  rw [hcorebot, Subgroup.mem_bot, inv_mul_eq_one] at h1
  exact h1.symm

theorem eq_conj_of_borel (P : Sylow 2 Y) {D : Subgroup Y}
    (hab : ∀ x ∈ (P : Subgroup Y), ∀ y ∈ (P : Subgroup Y), x * y = y * x)
    (hcent : ∀ t ∈ (P : Subgroup Y), t ≠ 1 → ∀ y : Y, y * t = t * y → y ∈ (P : Subgroup Y))
    (hDcyc : IsCyclic D) (hDodd : Odd (Nat.card D))
    (hsup : (P : Subgroup Y) ⊔ D = Subgroup.normalizer ((P : Subgroup Y) : Set Y))
    (hreg : ∀ x ∈ (P : Subgroup Y), x ≠ 1 → ∀ y ∈ (P : Subgroup Y), y ≠ 1 →
      ∃! d : D, (d : Y) * x * (d : Y)⁻¹ = y)
    (hsyl : Nat.card (Sylow 2 Y) = Nat.card (P : Subgroup Y) + 1)
    (hB : Nat.card (Subgroup.normalizer ((P : Subgroup Y) : Set Y)) =
      Nat.card (P : Subgroup Y) * (Nat.card (P : Subgroup Y) - 1))
    (hP4 : 4 ≤ Nat.card (P : Subgroup Y)) (hs : IsSimpleGroup Y)
    (hTI : ∀ y : Y, y ∉ Subgroup.normalizer ((P : Subgroup Y) : Set Y) →
      (P : Subgroup Y) ⊓ ((y • P : Sylow 2 Y) : Subgroup Y) = ⊥)
    (α : MulAut Y)
    (hαB : ∀ b ∈ Subgroup.normalizer ((P : Subgroup Y) : Set Y), α b * b⁻¹ ∈ (P : Subgroup Y))
    {m : ℕ} (hαm : α ^ (2 ^ m) = 1) :
    ∃ t ∈ (P : Subgroup Y), α = MulAut.conj t := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := (P : Subgroup Y) with hQ
  set N := Subgroup.normalizer (Q : Set Y) with hN
  have hQN : Q ≤ N := Subgroup.le_normalizer
  have hDN : D ≤ N := hsup ▸ le_sup_right
  have hαQ : ∀ x ∈ Q, α x ∈ Q := fun x hx => by
    have := Q.mul_mem (hαB x (hQN hx)) hx
    simpa using this
  have hconjQ : ∀ d ∈ N, ∀ x ∈ Q, d * x * d⁻¹ ∈ Q := fun d hd x hx =>
    (Subgroup.mem_normalizer_iff.mp hd x).mp hx
  have hQ1 : Q ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hP4
    omega
  obtain ⟨x₀', hx₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hQ1
  set x₀ := (x₀' : Y) with hx₀def
  have hx₀Q : x₀ ∈ Q := x₀'.2
  have hx₀1' : x₀ ≠ 1 := fun h => hx₀1 (Subtype.ext h)
  obtain ⟨y₀, hy₀Q, hy₀1, hy₀x⟩ : ∃ y₀ ∈ Q, y₀ ≠ 1 ∧ y₀ ≠ x₀ := by
    by_contra hall
    push Not at hall
    have hsub : (Q : Set Y) ⊆ {1, x₀} := fun y hy => by
      by_cases h1 : y = 1
      · exact Or.inl h1
      · exact Or.inr (hall y hy h1)
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 : ({1, x₀} : Set Y).ncard ≤ 2 :=
      (Set.ncard_insert_le 1 {x₀}).trans (by rw [Set.ncard_singleton])
    have h3 : Nat.card Q = (Q : Set Y).ncard := Nat.card_coe_set_eq _
    omega
  obtain ⟨d', hd'⟩ := (hreg _ hx₀Q hx₀1' _ hy₀Q hy₀1).exists
  have hd'1 : d' ≠ 1 := by
    intro h
    apply hy₀x
    rw [← hd', h]
    simp
  have hαD : ∀ d ∈ D, α d * d⁻¹ ∈ Q := fun d hd => hαB d (hDN hd)
  have hcommute : ∀ x ∈ Q, ∀ d ∈ D, α (d * x * d⁻¹) = d * α x * d⁻¹ := by
    intro x hx d hd
    set s := α d * d⁻¹ with hs
    have hsQ : s ∈ Q := hαD d hd
    have hαd : α d = s * d := by rw [hs, inv_mul_cancel_right]
    have hmem : d * α x * d⁻¹ ∈ Q := hconjQ d (hDN hd) _ (hαQ x hx)
    rw [map_mul, map_mul, map_inv, hαd, mul_inv_rev]
    calc s * d * α x * (d⁻¹ * s⁻¹) = s * (d * α x * d⁻¹) * s⁻¹ := by group
      _ = (d * α x * d⁻¹) * s * s⁻¹ := by rw [hab s hsQ _ hmem]
      _ = d * α x * d⁻¹ := by group
  have hαx₀ : α x₀ ∈ Q := hαQ _ hx₀Q
  have hαx₀1 : α x₀ ≠ 1 := fun h => hx₀1' (by simpa using congrArg α.symm h)
  obtain ⟨d₀, hd₀⟩ := (hreg _ hx₀Q hx₀1' _ hαx₀ hαx₀1).exists
  obtain ⟨g₁, hg₁⟩ := hDcyc.exists_generator
  have hDcomm : ∀ a b : D, a * b = b * a := fun a b => by
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg₁ a)
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg₁ b)
    exact (Commute.zpow_zpow_self g₁ i j).eq
  have hfix0 : ∀ y ∈ Q, α y = (d₀ : Y) * y * (d₀ : Y)⁻¹ := by
    intro y hy
    by_cases hy1 : y = 1
    · rw [hy1, map_one]
      simp
    obtain ⟨d, hd⟩ := (hreg _ hx₀Q hx₀1' _ hy hy1).exists
    rw [← hd, hcommute _ hx₀Q _ d.2, ← hd₀]
    have h1 := congrArg Subtype.val (hDcomm d d₀)
    simp only [Subgroup.coe_mul] at h1
    calc (d : Y) * ((d₀ : Y) * x₀ * (d₀ : Y)⁻¹) * (d : Y)⁻¹ =
        ((d : Y) * d₀) * x₀ * ((d : Y) * d₀)⁻¹ := by group
      _ = ((d₀ : Y) * d) * x₀ * ((d₀ : Y) * d)⁻¹ := by rw [h1]
      _ = (d₀ : Y) * ((d : Y) * x₀ * (d : Y)⁻¹) * (d₀ : Y)⁻¹ := by group
  have hiter : ∀ j : ℕ, ∀ y ∈ Q, (α ^ j) y = (d₀ : Y) ^ j * y * ((d₀ : Y) ^ j)⁻¹ := by
    intro j
    induction j with
    | zero => intro y _; simp
    | succ j ih =>
      intro y hy
      rw [pow_succ', MulAut.mul_apply, ih y hy]
      have hmem : (d₀ : Y) ^ j * y * ((d₀ : Y) ^ j)⁻¹ ∈ Q :=
        hconjQ _ (N.pow_mem (hDN d₀.2) j) y hy
      rw [hfix0 _ hmem]
      group
  have hd₀m : d₀ ^ (2 ^ m) = 1 := by
    have h1 := hiter (2 ^ m) x₀ hx₀Q
    rw [hαm, MulAut.one_apply] at h1
    have h2 := hreg _ hx₀Q hx₀1' _ hx₀Q hx₀1'
    have e1 : ((1 : D) : Y) * x₀ * ((1 : D) : Y)⁻¹ = x₀ := by simp
    have e2 : ((d₀ ^ (2 ^ m) : D) : Y) * x₀ * ((d₀ ^ (2 ^ m) : D) : Y)⁻¹ = x₀ := by
      simp only [Subgroup.coe_pow]
      exact h1.symm
    exact h2.unique e2 e1
  have hd₀1 : d₀ = 1 := by
    have h1 : orderOf d₀ ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hd₀m
    have h2 : orderOf d₀ ∣ Nat.card D := orderOf_dvd_natCard d₀
    have hcop : Nat.Coprime (2 ^ m) (Nat.card D) :=
      Nat.Coprime.pow_left m (Nat.coprime_two_left.mpr hDodd)
    exact orderOf_eq_one_iff.mp ((hcop.coprime_dvd_left h1).eq_one_of_dvd h2)
  have hfixQ : ∀ y ∈ Q, α y = y := fun y hy => by
    rw [hfix0 y hy, hd₀1]
    simp
  set d₁ := (g₁ : Y) with hd₁
  have hg₁1 : g₁ ≠ 1 := by
    intro h
    apply hd'1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg₁ d')
    rw [← hk, h, one_zpow]
  have hcentd₁ : ∀ c ∈ Q, d₁ * c * d₁⁻¹ = c → c = 1 := by
    intro c hc hcd
    by_contra hc1
    apply hg₁1
    have h2 := hreg c hc hc1 c hc hc1
    have e1 : ((1 : D) : Y) * c * ((1 : D) : Y)⁻¹ = c := by simp
    exact h2.unique hcd e1
  let φ : Q → Q := fun t => ⟨t * (d₁ * (t : Y)⁻¹ * d₁⁻¹),
    Q.mul_mem t.2 (hconjQ _ (hDN g₁.2) _ (Q.inv_mem t.2))⟩
  have hφ : Function.Injective φ := by
    intro t s h
    have h' : (t : Y) * (d₁ * (t : Y)⁻¹ * d₁⁻¹) = (s : Y) * (d₁ * (s : Y)⁻¹ * d₁⁻¹) :=
      congrArg Subtype.val h
    have hc : d₁ * ((s : Y)⁻¹ * t) * d₁⁻¹ = (s : Y)⁻¹ * t := by
      symm
      calc (s : Y)⁻¹ * t = (s : Y)⁻¹ * ((t : Y) * (d₁ * (t : Y)⁻¹ * d₁⁻¹)) *
            (d₁ * (t : Y)⁻¹ * d₁⁻¹)⁻¹ := by group
        _ = (s : Y)⁻¹ * ((s : Y) * (d₁ * (s : Y)⁻¹ * d₁⁻¹)) *
            (d₁ * (t : Y)⁻¹ * d₁⁻¹)⁻¹ := by rw [h']
        _ = d₁ * ((s : Y)⁻¹ * t) * d₁⁻¹ := by group
    have := hcentd₁ _ (Q.mul_mem (Q.inv_mem s.2) t.2) hc
    exact (Subtype.ext (inv_mul_eq_one.mp this)).symm
  obtain ⟨t, ht⟩ := (Finite.injective_iff_surjective.mp hφ) ⟨α d₁ * d₁⁻¹, hαD _ g₁.2⟩
  have htd₁ : α d₁ = (t : Y) * d₁ * (t : Y)⁻¹ := by
    have h1 : (t : Y) * (d₁ * (t : Y)⁻¹ * d₁⁻¹) = α d₁ * d₁⁻¹ := congrArg Subtype.val ht
    have h2 := congrArg (· * d₁) h1
    simp only [inv_mul_cancel_right] at h2
    rw [← h2]
    group
  have hagree : N ≤ (α.toMonoidHom).eqLocus (MulAut.conj (t : Y)).toMonoidHom := by
    rw [← hsup]
    refine sup_le (fun x hx => ?_) (fun d hd => ?_)
    · change α x = (t : Y) * x * (t : Y)⁻¹
      rw [hfixQ x hx, hab _ t.2 _ hx]
      group
    · change α d = (t : Y) * d * (t : Y)⁻¹
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg₁ ⟨d, hd⟩)
      have hk' : (g₁ : Y) ^ k = d := congrArg Subtype.val hk
      rw [← hk', map_zpow, ← hd₁, htd₁]
      exact conj_zpow
  refine ⟨t, t.2, ?_⟩
  have h1 := eq_one_of_fix_normalizer P hcent hsyl hB hP4 hs hTI ((MulAut.conj (t : Y))⁻¹ * α)
    (fun b hb => by
      have h2 : α b = (t : Y) * b * (t : Y)⁻¹ := hagree hb
      rw [MulAut.mul_apply, h2, MulAut.inv_def, MulAut.conj_symm_apply]
      group)
  calc α = MulAut.conj (t : Y) * ((MulAut.conj (t : Y))⁻¹ * α) := by group
    _ = MulAut.conj (t : Y) := by rw [h1, mul_one]

end Borel

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem mem_normalizer_inf_of_mem'' {A B : Subgroup G} {x : G}
    (hA : x ∈ Subgroup.normalizer (A : Set G)) (hB : x ∈ Subgroup.normalizer (B : Set G)) :
    x ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro z
  exact and_congr (hA z) (hB z)

omit [Finite G] in
private theorem mem_normalizer_of_mem_normalizer_subgroupOf {K S : Subgroup G} (hSK : S ≤ K)
    {k : ↥K} (hk : k ∈ Subgroup.normalizer ((S.subgroupOf K : Subgroup ↥K) : Set ↥K)) :
    (k : G) ∈ Subgroup.normalizer (S : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    have h1 := (Subgroup.mem_normalizer_iff.mp hk ⟨z, hSK hz⟩).mp (Subgroup.mem_subgroupOf.mpr hz)
    exact Subgroup.mem_subgroupOf.mp h1
  · intro hz
    have hzK : z ∈ K := by
      have := K.mul_mem (K.mul_mem (K.inv_mem k.2) (hSK hz)) k.2
      simpa [mul_assoc] using this
    have h1 := (Subgroup.mem_normalizer_iff.mp hk ⟨z, hzK⟩).mpr (Subgroup.mem_subgroupOf.mpr hz)
    exact Subgroup.mem_subgroupOf.mp h1

theorem comm_of_isPSL_two {K S : Subgroup G} {n : ℕ} (hn : 2 ≤ n) (hK : IsPSL 2 2 n ↥K)
    (hS : IsSylowTwoOf S K) : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, F, _, _, hF, ⟨e₀⟩⟩ := hK
  let e : ↥K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n) :=
    e₀.trans (CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL F 2 2 n (by omega) hF)
  have : Finite (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n)) :=
    Finite.of_equiv ↥K e.toEquiv
  set P' := toSylow2 hS
  have hP'c : (P' : Subgroup ↥K) = S.subgroupOf K := toSylow2_coe hS
  set P : Sylow 2 (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n)) :=
    P'.mapSurjective (f := e.toMonoidHom) e.surjective
  have hPc : (P : Subgroup PSL(2, GaloisField 2 n)) = (P' : Subgroup ↥K).map e.toMonoidHom :=
    Sylow.coe_mapSurjective _ _
  have hmemP : ∀ k : ↥K, e k ∈ (P : Subgroup PSL(2, GaloisField 2 n)) ↔ (k : G) ∈ S := by
    intro k
    rw [hPc, ← MulEquiv.coe_toMonoidHom, Subgroup.mem_map_equiv, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply, hP'c, Subgroup.mem_subgroupOf]
  obtain ⟨hPel, -⟩ := CFSG.Walter.psl2_even_sylow_two hn P
  intro x hx y hy
  have hxP := (hmemP ⟨x, hS.1 hx⟩).mpr hx
  have hyP := (hmemP ⟨y, hS.1 hy⟩).mpr hy
  have h1 := congrArg Subtype.val (hPel.toIsMulCommutative.is_comm.comm ⟨_, hxP⟩ ⟨_, hyP⟩)
  simp only [Subgroup.coe_mul] at h1
  rw [← map_mul, ← map_mul] at h1
  exact congrArg Subtype.val (e.injective h1)

theorem not_isPGroup_normalizer_of_isPSL_two {K S : Subgroup G} {n : ℕ} (hn : 2 ≤ n)
    (hK : IsPSL 2 2 n ↥K) (hS : IsSylowTwoOf S K) :
    ¬ IsPGroup 2 ↥(K ⊓ Subgroup.normalizer (S : Set G)) := by
  intro hp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, F, _, _, hF, ⟨e₀⟩⟩ := hK
  let e : ↥K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n) :=
    e₀.trans (CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL F 2 2 n (by omega) hF)
  have : Finite (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n)) :=
    Finite.of_equiv ↥K e.toEquiv
  set P' := toSylow2 hS
  have hP'c : (P' : Subgroup ↥K) = S.subgroupOf K := toSylow2_coe hS
  set P : Sylow 2 (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n)) :=
    P'.mapSurjective (f := e.toMonoidHom) e.surjective
  have hPc : (P : Subgroup PSL(2, GaloisField 2 n)) = (P' : Subgroup ↥K).map e.toMonoidHom :=
    Sylow.coe_mapSurjective _ _
  obtain ⟨D, -, hDcard, -, hsup, -⟩ := CFSG.Walter.psl2_even_normalizer_sylow_two hn P
  have hDN : D ≤ Subgroup.normalizer ((P : Subgroup PSL(2, GaloisField 2 n)) :
      Set PSL(2, GaloisField 2 n)) := hsup ▸ le_sup_right
  have hD2 : IsPGroup 2 D := by
    intro d
    have hd := hDN d.2
    rw [hPc, ← Subgroup.map_equiv_normalizer_eq] at hd
    obtain ⟨k, hk, hke⟩ := hd
    rw [hP'c] at hk
    have hkN := mem_normalizer_of_mem_normalizer_subgroupOf hS.1 hk
    obtain ⟨j, hj⟩ := hp ⟨(k : G), k.2, hkN⟩
    refine ⟨j, Subtype.ext ?_⟩
    have hj' : (k : G) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    have hk1 : k ^ 2 ^ j = 1 := Subtype.ext (by simpa using hj')
    have : (d : PSL(2, GaloisField 2 n)) = e k := hke.symm
    simp only [Subgroup.coe_pow, Subgroup.coe_one, this, ← map_pow, hk1, map_one]
  obtain ⟨j, hj⟩ := hD2.exists_card_eq
  have h2n : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
  have h4n : 4 ≤ 2 ^ n :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  rw [hDcard] at hj
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · rw [pow_zero] at hj
    omega
  · have : 2 ∣ 2 ^ j := dvd_pow_self 2 (by omega)
    omega

omit [Finite G] in
theorem isSimpleGroup_of_isPSL_two {K : Subgroup G} {n : ℕ} (hn : 2 ≤ n)
    (hK : IsPSL 2 2 n ↥K) : IsSimpleGroup ↥K := by
  obtain ⟨-, F, _, _, hF, ⟨e₀⟩⟩ := hK
  let e : ↥K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n) :=
    e₀.trans (CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL F 2 2 n (by omega) hF)
  have h4 : 4 ≤ Nat.card (GaloisField 2 n) := by
    rw [GaloisField.card 2 n (by omega)]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  exact (MulEquiv.isSimpleGroup_congr e).mpr this

theorem exists_mul_ne_mul_of_isPSL_two {K : Subgroup G} {n : ℕ} (hn : 2 ≤ n)
    (hK : IsPSL 2 2 n ↥K) : ∃ a b : ↥K, a * b ≠ b * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn0 : n ≠ 0 := by omega
  obtain ⟨-, F, _, _, hF, ⟨e₀⟩⟩ := hK
  let e : ↥K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n) :=
    e₀.trans (CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL F 2 2 n (by omega) hF)
  have : Finite (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n)) :=
    Finite.of_equiv ↥K e.toEquiv
  by_contra hab
  push Not at hab
  obtain ⟨P⟩ : Nonempty (Sylow 2 (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n))) :=
    inferInstance
  obtain ⟨-, hPcard⟩ := CFSG.Walter.psl2_even_sylow_two hn P
  have hP1 : (P : Subgroup PSL(2, GaloisField 2 n)) ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hPcard
    have : 2 ∣ 2 ^ n := dvd_pow_self 2 hn0
    omega
  obtain ⟨t, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hP1
  have h1 := CFSG.Walter.psl2_even_centralizer_involution hn P t.2 (fun h => ht1 (Subtype.ext h))
  have htop : (P : Subgroup PSL(2, GaloisField 2 n)) = ⊤ := by
    rw [← h1, eq_top_iff]
    intro y _
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := hab (e.symm y) (e.symm t)
    apply e.symm.injective
    rw [map_mul, map_mul, this]
  have hcard := CFSG.Walter.psl2_even_card hn0
  rw [← Subgroup.card_top, ← htop, hPcard] at hcard
  have h4n : 4 ≤ 2 ^ n :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h2 : 2 ≤ (2 ^ n) ^ 2 - 1 := by
    have : 16 ≤ (2 ^ n) ^ 2 := by nlinarith
    omega
  nlinarith

theorem exists_conj_agree_of_isPSL_two {K S : Subgroup G} {n : ℕ} (hn : 2 ≤ n)
    (hK : IsPSL 2 2 n ↥K) (hS : IsSylowTwoOf S K) {u : G}
    (huK : u ∈ Subgroup.normalizer (K : Set G)) {m : ℕ} (hum : u ^ 2 ^ m = 1)
    (hcomm : ∀ b ∈ K ⊓ Subgroup.normalizer (S : Set G), u * b * u⁻¹ * b⁻¹ ∈ S) :
    ∃ k ∈ S, ∀ x ∈ K, u * x * u⁻¹ = k * x * k⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn0 : n ≠ 0 := by omega
  obtain ⟨-, F, _, _, hF, ⟨e₀⟩⟩ := hK
  let e : ↥K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n) :=
    e₀.trans (CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL F 2 2 n (by omega) hF)
  have : Finite (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n)) :=
    Finite.of_equiv ↥K e.toEquiv
  set P' := toSylow2 hS with hP'def
  have hP'c : (P' : Subgroup ↥K) = S.subgroupOf K := toSylow2_coe hS
  set P : Sylow 2 (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n)) :=
    P'.mapSurjective (f := e.toMonoidHom) e.surjective with hPdef
  set Q := (P : Subgroup PSL(2, GaloisField 2 n)) with hQdef
  have hPc : Q = (P' : Subgroup ↥K).map e.toMonoidHom := Sylow.coe_mapSurjective _ _
  have hmemP : ∀ k : ↥K, e k ∈ Q ↔ (k : G) ∈ S := by
    intro k
    rw [hPc, ← MulEquiv.coe_toMonoidHom, Subgroup.mem_map_equiv, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply, hP'c, Subgroup.mem_subgroupOf]
  obtain ⟨hPel, hPcard⟩ := CFSG.Walter.psl2_even_sylow_two hn P
  have hab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hPel.toIsMulCommutative.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hcent : ∀ t ∈ Q, t ≠ 1 → ∀ y, y * t = t * y → y ∈ Q := by
    intro t ht ht1 y hy
    have h1 := CFSG.Walter.psl2_even_centralizer_involution hn P ht ht1
    have h2 : y ∈ Subgroup.centralizer ({t} : Set PSL(2, GaloisField 2 n)) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hy
    rw [h1] at h2
    exact h2
  obtain ⟨D, hDcyc, hDcard, -, hsup, hreg⟩ := CFSG.Walter.psl2_even_normalizer_sylow_two hn P
  have h2n : 2 ∣ 2 ^ n := dvd_pow_self 2 hn0
  have h1n : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have h4n : 4 ≤ 2 ^ n :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hDodd : Odd (Nat.card D) := by
    rw [hDcard]
    exact Nat.odd_iff.mpr (by omega)
  have hsyl : Nat.card (Sylow 2 (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n))) =
      Nat.card Q + 1 := by
    rw [CFSG.Walter.psl2_even_card_sylow hn0, hPcard]
  have hB : Nat.card (Subgroup.normalizer (Q : Set PSL(2, GaloisField 2 n))) =
      Nat.card Q * (Nat.card Q - 1) := by
    rw [CFSG.Walter.psl2_even_card_normalizer_sylow_two hn0, hPcard]
  have hP4 : 4 ≤ Nat.card Q := hPcard ▸ h4n
  have hs : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [GaloisField.card 2 n hn0]; omega)
  have hTI := fun y hy =>
    sylow_inf_smul_eq_bot (CFSG.Open.bender_psl2_borel_full n hn) P (y := y) hy
  have hmapK : K.map (MulAut.conj u).toMonoidHom = K := by
    ext x
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp huK k).mp hk
    · intro hx
      refine ⟨u⁻¹ * x * u, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ huK) x).mp hx
      simpa using this
  let β : ↥K ≃* ↥K := ((MulAut.conj u).subgroupMap K).trans (MulEquiv.subgroupCongr hmapK)
  have hβ : ∀ k : ↥K, ((β k : ↥K) : G) = u * k * u⁻¹ := fun k => rfl
  let α : MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n)) :=
    (e.symm.trans β).trans e
  have hα : ∀ y, α y = e (β (e.symm y)) := fun y => rfl
  have hβpow : ∀ j : ℕ, ∀ k : ↥K, (((β ^ j) k : ↥K) : G) = u ^ j * k * (u ^ j)⁻¹ := by
    intro j
    induction j with
    | zero => intro k; simp
    | succ j ih =>
      intro k
      rw [pow_succ']
      change ((β ((β ^ j) k) : ↥K) : G) = _
      rw [hβ, ih k]
      group
  have hαpow : ∀ j : ℕ, ∀ y, (α ^ j) y = e ((β ^ j) (e.symm y)) := by
    intro j
    induction j with
    | zero => intro y; simp
    | succ j ih =>
      intro y
      rw [pow_succ', MulAut.mul_apply, ih y, hα, MulEquiv.symm_apply_apply, pow_succ']
      rfl
  have hαm : α ^ (2 ^ m) = 1 := by
    ext y
    rw [hαpow, MulAut.one_apply]
    have : (β ^ (2 ^ m)) (e.symm y) = e.symm y := by
      apply Subtype.ext
      rw [hβpow, hum, one_mul, inv_one, mul_one]
    rw [this, MulEquiv.apply_symm_apply]
  have hαB : ∀ b ∈ Subgroup.normalizer (Q : Set PSL(2, GaloisField 2 n)), α b * b⁻¹ ∈ Q := by
    intro b hb
    rw [hPc, ← Subgroup.map_equiv_normalizer_eq] at hb
    obtain ⟨k, hk, rfl⟩ := hb
    rw [hP'c] at hk
    have hkN := mem_normalizer_of_mem_normalizer_subgroupOf hS.1 hk
    have hc := hcomm k ⟨k.2, hkN⟩
    rw [MulEquiv.coe_toMonoidHom, hα, MulEquiv.symm_apply_apply, ← map_inv, ← map_mul]
    apply (hmemP _).mpr
    simpa [hβ, mul_assoc] using hc
  obtain ⟨t, htP, hαt⟩ := eq_conj_of_borel P hab hcent hDcyc hDodd hsup hreg hsyl hB hP4 hs
    hTI α hαB hαm
  set k₀ := e.symm t with hk₀
  have hk₀S : (k₀ : G) ∈ S := (hmemP k₀).mp (by rw [hk₀, MulEquiv.apply_symm_apply]; exact htP)
  refine ⟨k₀, hk₀S, fun x hx => ?_⟩
  have h1 : α (e ⟨x, hx⟩) = t * e ⟨x, hx⟩ * t⁻¹ := by rw [hαt]; rfl
  rw [hα, MulEquiv.symm_apply_apply] at h1
  have h2 : β ⟨x, hx⟩ = k₀ * ⟨x, hx⟩ * k₀⁻¹ := by
    apply e.injective
    rw [h1, map_mul, map_mul, map_inv, hk₀, MulEquiv.apply_symm_apply]
  have h3 := congrArg Subtype.val h2
  rw [hβ] at h3
  simpa using h3

theorem kgBenderInnerL2_holds : KGBenderInnerL2 := by
  intro G _ _ X T M K n hP hJ hKX hXN hC hKT hn hK hMK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTK : IsSylowTwoOf (T ⊓ K) K := A4.isSylowTwoOf_inf_normal hP.isSylow hKX hXN
  refine ⟨?_, fun x hx _ => ?_⟩
  swap
  ·
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact comm_of_isPSL_two hn hK hTK y hy x hx
  intro u hu
  obtain ⟨hMmax, hTM⟩ : IsMaxSubgroupIn X M ∧ T ≤ M := by
    have : M ∈ maxOver X T := by rw [hP.uniqueMax]; exact rfl
    exact this
  have hMX : M ≤ X := hMmax.le
  have huM : u ∈ M := CFSG.LieType.BorelTits.pCoreOf_le 2 M hu
  have hO2 : IsPGroup 2 (pCoreOf 2 M) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  have hTsylM : IsSylowTwoOf T M := isSylowTwoOf_mono hP.isSylow hTM hMX
  have hO2T : pCoreOf 2 M ≤ T := A4.le_of_normal_of_isSylowTwoOf hTsylM
    (CFSG.LieType.BorelTits.pCoreOf_le 2 M)
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (CFSG.LieType.BorelTits.pCoreOf_le 2 M)).mpr
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)) hO2
  have huT : u ∈ T := hO2T hu
  have huNK : u ∈ Subgroup.normalizer (K : Set G) := hXN (hMX huM)
  have huNTK : u ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) :=
    mem_normalizer_inf_of_mem'' (Subgroup.le_normalizer huT) huNK
  obtain ⟨m, hm⟩ := hO2 ⟨u, hu⟩
  have hum : u ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hcomm : ∀ b ∈ K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G),
      u * b * u⁻¹ * b⁻¹ ∈ T ⊓ K := by
    intro b hb
    have hbM : b ∈ M := (hMK ▸ hb : b ∈ M ⊓ K).1
    have hc1 : u * b * u⁻¹ * b⁻¹ ∈ pCoreOf 2 M := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf
        2 M hbM) u⁻¹).mp ((pCoreOf 2 M).inv_mem hu)
      have := (pCoreOf 2 M).mul_mem hu h1
      simpa [mul_assoc] using this
    have hc2 : u * b * u⁻¹ * b⁻¹ ∈ K := by
      have h1 := (Subgroup.mem_normalizer_iff.mp huNK b).mp hb.1
      exact K.mul_mem h1 (K.inv_mem hb.1)
    have hc3 : u * b * u⁻¹ * b⁻¹ ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ huNTK hb.2)
        (Subgroup.inv_mem _ huNTK)) (Subgroup.inv_mem _ hb.2)
    have hz : IsPGroup 2 (Subgroup.zpowers (u * b * u⁻¹ * b⁻¹)) :=
      hO2.to_le (Subgroup.zpowers_le.mpr hc1)
    exact le_of_le_normalizer_of_isSylowTwoOf hTK hz (Subgroup.zpowers_le.mpr hc2)
      (Subgroup.zpowers_le.mpr hc3) (Subgroup.mem_zpowers _)
  obtain ⟨k₀, hk₀T, hagree⟩ := exists_conj_agree_of_isPSL_two hn hK hTK huNK hum hcomm
  have hk₀K : k₀ ∈ K := hk₀T.2
  have hc : k₀⁻¹ * u ∈ X ⊓ Subgroup.centralizer (K : Set G) := by
    refine ⟨X.mul_mem (X.inv_mem (hKX hk₀K)) (hMX huM), ?_⟩
    show k₀⁻¹ * u ∈ Subgroup.centralizer (K : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have h1 := hagree k hk
    calc k * (k₀⁻¹ * u) = k₀⁻¹ * (k₀ * k * k₀⁻¹) * u := by group
      _ = k₀⁻¹ * (u * k * u⁻¹) * u := by rw [h1]
      _ = k₀⁻¹ * u * k := by group
  rw [hC, Subgroup.mem_bot, inv_mul_eq_one] at hc
  rw [← hc]
  exact hk₀K

end E2

end CFSG.Quasithin
