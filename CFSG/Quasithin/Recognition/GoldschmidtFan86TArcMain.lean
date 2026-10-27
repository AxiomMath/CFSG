module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86TArc
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Edge
public import CFSG.Quasithin.Recognition.GoldschmidtFan86TwoFix

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V} (T : Track Γ G)

theorem Track.exists_zpow_smul_iff (hT : Γ.IsTree) (a b : ℤ) :
    (∃ k : ℤ, T.τ ^ k • T.line.vert a = T.line.vert b) ↔ a % 2 = b % 2 := by
  constructor
  · rintro ⟨k, hk⟩
    rw [T.zpow_smul_vert] at hk
    have := Line.vert_injective hT T.line hk
    omega
  · intro h
    refine ⟨(b - a) / 2, ?_⟩
    rw [T.zpow_smul_vert]
    congr 1
    omega

theorem Track.omega1_fixer_conj (k : ℤ) (y : G) :
    y ∈ omega1 T.fixer ↔ T.τ ^ k * y * (T.τ ^ k)⁻¹ ∈ omega1 T.fixer := by
  constructor
  · exact fun hy => omega1_conj_mem (fun h hh => (T.conj_mem_fixer k).2 hh) hy
  · intro hy
    have := omega1_conj_mem (g := (T.τ ^ k)⁻¹) (H := T.fixer) (H' := T.fixer) (fun h hh => by
      have := (T.conj_mem_fixer (-k)).2 hh
      simpa [zpow_neg] using this) hy
    simpa [mul_assoc] using this

theorem Track.zpow_mem_normalizer (k : ℤ) :
    T.τ ^ k ∈ Subgroup.normalizer (omega1 T.fixer : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  exact T.omega1_fixer_conj k y

theorem locTrans_of_quasiTArcs (F : FanTree Γ G) {a b d : ℤ} (h₁ : IsQuasiTArc T a b)
    (h₂ : IsQuasiTArc T b d) (x y : V) (hx : Γ.Adj (T.line.vert b) x)
    (hy : Γ.Adj (T.line.vert b) y) :
    ∃ m ∈ Subgroup.normalizer (omega1 T.fixer : Set G),
      m • T.line.vert b = T.line.vert b ∧ m • x = y := by
  have hN₁ := (IsQuasiTArc.fixer_normal T F h₁).2
  have hN₂ := (IsQuasiTArc.fixer_normal T F h₂).2
  obtain ⟨hab, -, hR, -⟩ := h₁
  obtain ⟨hbd, hL, -, -⟩ := h₂
  obtain ⟨g₁, hg₁, hg₁'⟩ := IsConcreteLE.not_le_iff_exists.1 hR
  obtain ⟨g₂, hg₂, hg₂'⟩ := IsConcreteLE.not_le_iff_exists.1 hL
  have f₁ := (T.mem_subFixer).1 hg₁
  have f₂ := (T.mem_subFixer).1 hg₂
  have m₁ : g₁ • T.line.vert (b + 1) ≠ T.line.vert (b + 1) := fun hfix => hg₁' <|
    (T.mem_subFixer).2 fun i h1 h2 => by
      by_cases hi : i = b + 1
      · subst hi
        exact hfix
      · exact f₁ i h1 (by omega)
  have m₂ : g₂ • T.line.vert (b - 1) ≠ T.line.vert (b - 1) := fun hfix => hg₂' <|
    (T.mem_subFixer).2 fun i h1 h2 => by
      by_cases hi : i = b - 1
      · subst hi
        exact hfix
      · exact f₂ i (by omega) h2
  obtain ⟨m, hm, hmα, hmx⟩ := F.transitive_of_two_fixers (T.adj_pred b) (T.line.adj b)
    (T.ne_pred_succ b) (MulAction.mem_stabilizer_iff.2 (f₁ b hab.le le_rfl))
    (MulAction.mem_stabilizer_iff.2 (f₂ b le_rfl hbd.le)) (f₁ (b - 1) (by omega) (by omega)) m₁
    (f₂ (b + 1) (by omega) (by omega)) m₂ hx hy
  refine ⟨m, ?_, hmα, hmx⟩
  have : Subgroup.closure ({g₁, g₂} : Set G) ≤
      Subgroup.normalizer (omega1 T.fixer : Set G) := by
    rw [Subgroup.closure_le]
    rintro g (rfl | rfl)
    · exact hN₁ hg₁
    · exact hN₂ (by simpa using hg₂)
  exact this hm

theorem locTrans_translate (F : FanTree Γ G) (k : ℤ) {i : ℤ}
    (h : ∀ x y, Γ.Adj (T.line.vert i) x → Γ.Adj (T.line.vert i) y →
      ∃ m ∈ Subgroup.normalizer (omega1 T.fixer : Set G),
        m • T.line.vert i = T.line.vert i ∧ m • x = y) :
    ∀ x y, Γ.Adj (T.line.vert (i + 2 * k)) x → Γ.Adj (T.line.vert (i + 2 * k)) y →
      ∃ m ∈ Subgroup.normalizer (omega1 T.fixer : Set G),
        m • T.line.vert (i + 2 * k) = T.line.vert (i + 2 * k) ∧ m • x = y := by
  intro x y hx hy
  have hg : (T.τ ^ k)⁻¹ • T.line.vert (i + 2 * k) = T.line.vert i := by
    rw [inv_smul_eq_iff, T.zpow_smul_vert]
  have hx' : Γ.Adj (T.line.vert i) ((T.τ ^ k)⁻¹ • x) := by
    have := (F.adj_smul (T.τ ^ k)⁻¹ _ _).2 hx
    rwa [hg] at this
  have hy' : Γ.Adj (T.line.vert i) ((T.τ ^ k)⁻¹ • y) := by
    have := (F.adj_smul (T.τ ^ k)⁻¹ _ _).2 hy
    rwa [hg] at this
  obtain ⟨m, hm, hmi, hmx⟩ := h _ _ hx' hy'
  refine ⟨T.τ ^ k * m * (T.τ ^ k)⁻¹, ?_, ?_, ?_⟩
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (T.zpow_mem_normalizer k) hm)
      (Subgroup.inv_mem _ (T.zpow_mem_normalizer k))
  · rw [mul_smul, mul_smul, hg, hmi, T.zpow_smul_vert]
  · rw [mul_smul, mul_smul, hmx, smul_inv_smul]

theorem Track.exists_involution_of_fixer_ne_bot (F : FanTree Γ G) (hT : T.fixer ≠ ⊥) :
    ∃ x ∈ T.fixer, x ≠ 1 ∧ x * x = 1 := by
  have hle : T.fixer ≤ MulAction.stabilizer G (T.line.vert 0) ⊓
      MulAction.stabilizer G (T.line.vert 1) := fun g hg =>
    ⟨MulAction.mem_stabilizer_iff.2 ((T.mem_fixer).1 hg 0),
      MulAction.mem_stabilizer_iff.2 ((T.mem_fixer).1 hg 1)⟩
  have hpg : IsPGroup 2 T.fixer := (F.edge_two _ _ (T.line.adj 0)).to_le hle
  have hfin : Finite T.fixer :=
    haveI := F.loc_finite (T.line.vert 0)
    Finite.of_injective (Subgroup.inclusion (hle.trans inf_le_left))
      (Subgroup.inclusion_injective _)
  obtain ⟨n, hn⟩ := hpg.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hT ((Subgroup.card_eq_one).1 (by simpa using hn))
  have hdvd : 2 ∣ Nat.card T.fixer := by
    rw [hn]
    exact dvd_pow_self 2 hn0
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := T.fixer) 2 hdvd
  refine ⟨x, x.2, ?_, ?_⟩
  · intro h1
    have : x = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hx
    omega
  · have := pow_orderOf_eq_one x
    rw [hx, sq] at this
    exact congrArg Subtype.val this

theorem fan_4_3_1 (F : FanTree Γ G) (hT : T.fixer ≠ ⊥) {a₁ b₁ a₂ b₂ : ℤ}
    (h₁ : IsQuasiTArc T a₁ b₁) (h₂ : IsQuasiTArc T a₂ b₂) :
    (∃ k : ℤ, T.τ ^ k • T.line.vert a₁ = T.line.vert a₂) ∨
      (∃ k : ℤ, T.τ ^ k • T.line.vert b₁ = T.line.vert b₂) := by
  by_contra hcon
  rw [not_or, T.exists_zpow_smul_iff F.isTree, T.exists_zpow_smul_iff F.isTree] at hcon
  obtain ⟨hl, hr⟩ := hcon
  have loc : ∀ {a b : ℤ}, IsQuasiTArc T a b →
      (∃ a' b' : ℤ, IsQuasiTArc T a' b' ∧ a' % 2 = b % 2) →
      ∀ x y, Γ.Adj (T.line.vert b) x → Γ.Adj (T.line.vert b) y →
        ∃ m ∈ Subgroup.normalizer (omega1 T.fixer : Set G),
          m • T.line.vert b = T.line.vert b ∧ m • x = y := by
    rintro a b hab ⟨a', b', ha', hpar⟩
    obtain ⟨k, hk⟩ : ∃ k : ℤ, a' + 2 * k = b := ⟨(b - a') / 2, by omega⟩
    have := ha'.translate T k
    rw [hk] at this
    exact locTrans_of_quasiTArcs T F hab this
  have hmatch : ∀ b : ℤ, ∃ a' b' : ℤ, IsQuasiTArc T a' b' ∧ a' % 2 = b % 2 := by
    intro b
    by_cases hb : a₁ % 2 = b % 2
    · exact ⟨a₁, b₁, h₁, hb⟩
    · exact ⟨a₂, b₂, h₂, by omega⟩
  have loc₁ := loc h₁ (hmatch b₁)
  have loc₂ := loc h₂ (hmatch b₂)
  obtain ⟨k, hk⟩ : ∃ k : ℤ, b₂ + 2 * k = b₁ + 1 := ⟨(b₁ + 1 - b₂) / 2, by omega⟩
  have loc₂' := locTrans_translate T F k loc₂
  rw [hk] at loc₂'
  have hbot := F.eq_bot_of_locTrans (Subgroup.normalizer (omega1 T.fixer : Set G))
    (U := omega1 T.fixer) (T.line.adj b₁)
    (fun u hu => ⟨(T.mem_fixer).1 (omega1_le _ hu) b₁, (T.mem_fixer).1 (omega1_le _ hu) (b₁ + 1)⟩)
    le_rfl (fun x y hx hy => loc₁ x y hx hy)
    (fun x y hx hy => loc₂' x y hx hy)
  obtain ⟨x, hx, hx1, hx2⟩ := T.exists_involution_of_fixer_ne_bot F hT
  have : x ∈ omega1 T.fixer := Subgroup.subset_closure ⟨hx, hx2⟩
  rw [hbot] at this
  exact hx1 (Subgroup.mem_bot.1 this)

end CFSG.Quasithin.Fan86
