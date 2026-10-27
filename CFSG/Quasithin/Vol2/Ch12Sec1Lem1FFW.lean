module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1Mat

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique Matrix
open CFSG.ComponentClassification.CatalogueBGraphForm (slGraphAut slGraphAut_matrix)
open scoped Matrix

namespace Sec1211Ns

variable {G : Type} [Group G]

theorem exists_mul_of_mem_sup {X Y : Subgroup G} (hXY : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) {g : G}
    (hg : g ∈ X ⊔ Y) : ∃ x ∈ X, ∃ y ∈ Y, g = x * y := by
  have hN : X ≤ Subgroup.normalizer (Y : Set G) := fun x hx => by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [hXY x hx y hy, mul_inv_cancel_right]
      exact hy
    · intro hy
      have h2 : x * y * x⁻¹ = y := mul_left_cancel (a := x) (by rw [hXY x hx _ hy]; group)
      exact h2 ▸ hy
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right X Y hN] at hg
  obtain ⟨x, hx, y, hy, rfl⟩ := hg
  exact ⟨x, hx, y, hy, rfl⟩

namespace Setting

variable [Finite G] {T L V V₁ V₂ : Subgroup G} {n : ℕ} {a₀ c₀ : G}
  {S : Setting T L V V₁ V₂ n a₀ c₀} (F : Frame S 3)

theorem psi_eq_one_iff {Y : Subgroup G} (hY : Y ≤ Xv L V₁ (a₀ * c₀)) (a : ↥Y) :
    psi F hY a = 1 ↔ (a : G) ∈ Subgroup.centralizer ((S.W₁ ⊔ S.W₂ : Subgroup G) : Set G) := by
  constructor
  · intro h1
    have h1' : frameMat F (psi F hY a) = 1 := by
      rw [h1]
      simp [frameMat]
    have hle : S.W₁ ⊔ S.W₂ ≤ Subgroup.centralizer ({(a : G)} : Set G) := by
      refine sup_le (fun x hx => ?_) (fun y hy => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        have h2 := psi_spec₁ F hY a hx.1
        rw [h1', Matrix.SpecialLinearGroup.coe_one, one_mulVec] at h2
        exact ((conj_eq_iff₁ (hY a.2).1.2 hx.1 (g := 1)
          (by rw [Matrix.SpecialLinearGroup.coe_one, one_mulVec]; exact h2)).mpr
          (by rw [Matrix.SpecialLinearGroup.coe_one, one_mulVec])).symm
      · rw [Subgroup.mem_centralizer_singleton_iff]
        have h2 := psi_spec₂ F hY a hy.1
        rw [h1', map_one, Matrix.SpecialLinearGroup.coe_one, one_mulVec] at h2
        exact ((conj_eq_iff₂ (S.Xv_le_normalizer₂ (hY a.2)) hy.1 (g := 1)
          (by rw [Matrix.SpecialLinearGroup.coe_one, one_mulVec]; exact h2)).mpr
          (by rw [Matrix.SpecialLinearGroup.coe_one, one_mulVec])).symm
    exact Subgroup.mem_centralizer_iff.mpr fun w hw =>
      Subgroup.mem_centralizer_singleton_iff.mp (hle hw)
  · intro h
    refine PairStab.eq_of_mulVec_eq fun ξ => ?_
    rw [Matrix.SpecialLinearGroup.coe_one, one_mulVec]
    have hx : S.C₁.inv ((F.s : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ PairStab.emb F.h ξ) ∈ S.W₁ :=
      ⟨S.C₁.inv_mem _, by
        show S.C₁.E (S.C₁.inv _) ⬝ᵥ S.C₂.E c₀ = 0
        rw [S.C₁.E_inv]
        exact s_emb_dot F _⟩
    have h1 := psi_spec₁ F hY a hx.1
    have h2 := (conj_eq_iff₁ (hY a.2).1.2 hx.1 h1).mp
      (Subgroup.mem_centralizer_iff.mp h _ (Subgroup.mem_sup_left hx)).symm
    rw [S.C₁.E_inv, frameMat_mulVec_emb] at h2
    have h3 := congrArg (fun z => ((F.s⁻¹ : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ z) h2
    simp only [VecStab.inv_mulVec_mulVec] at h3
    exact PairStab.emb_injective F.h h3

theorem relIndex_eq {Y : Subgroup G} (hY : Y ≤ Xv L V₁ (a₀ * c₀)) :
    (Y ⊓ Subgroup.centralizer ((S.W₁ ⊔ S.W₂ : Subgroup G) : Set G)).relIndex Y =
      Nat.card (psi F hY).range := by
  have hker : (Y ⊓ Subgroup.centralizer ((S.W₁ ⊔ S.W₂ : Subgroup G) : Set G)).subgroupOf Y =
      (psi F hY).ker := by
    ext a
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, psi_eq_one_iff]
    exact ⟨fun h => h.2, fun h => ⟨a.2, h⟩⟩
  rw [Subgroup.relIndex, hker, Subgroup.index_ker]

theorem card_W_inf {Y : Subgroup G} (hY : Y ≤ Xv L V₁ (a₀ * c₀)) :
    Nat.card ↥((S.W₁ ⊔ S.W₂) ⊓ Subgroup.centralizer (Y : Set G)) =
      Nat.card ↥(S.W₁ ⊓ Subgroup.centralizer (Y : Set G)) *
        Nat.card ↥(S.W₂ ⊓ Subgroup.centralizer (Y : Set G)) := by
  rw [← Nat.card_prod]
  symm
  refine Nat.card_eq_of_bijective (fun p => ⟨(p.1 : G) * p.2,
    Subgroup.mul_mem_sup p.1.2.1 p.2.2.1, Subgroup.mul_mem _ p.1.2.2 p.2.2.2⟩) ⟨?_, ?_⟩
  · rintro ⟨x, y⟩ ⟨x', y'⟩ h
    have h1 : (x : G) * y = x' * y' := congrArg Subtype.val h
    obtain ⟨h2, h3⟩ := S.decomp_unique x.2.1.1 x'.2.1.1 y.2.1.1 y'.2.1.1 h1
    exact Prod.ext (Subtype.ext h2) (Subtype.ext h3)
  · rintro ⟨w, hwW, hwC⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := exists_mul_of_mem_sup
      (fun x (hx : x ∈ S.W₁) y (hy : y ∈ S.W₂) => S.comm (S.le₁ hx.1) (S.le₂ hy.1)) hwW
    have hfix : ∀ a ∈ Y, a * x * a⁻¹ = x ∧ a * y * a⁻¹ = y := by
      intro a ha
      have e : a * x * a⁻¹ * (a * y * a⁻¹) = x * y := by
        calc a * x * a⁻¹ * (a * y * a⁻¹) = a * (x * y) * a⁻¹ := by group
          _ = x * y := by rw [Subgroup.mem_centralizer_iff.mp hwC a ha, mul_inv_cancel_right]
      exact S.decomp_unique ((Subgroup.mem_normalizer_iff.mp (hY ha).1.2 x).mp hx.1) hx.1
        ((Subgroup.mem_normalizer_iff.mp (S.Xv_le_normalizer₂ (hY ha)) y).mp hy.1) hy.1 e
    have hxC : x ∈ Subgroup.centralizer (Y : Set G) := Subgroup.mem_centralizer_iff.mpr
      fun a ha => by
        calc a * x = a * x * a⁻¹ * a := by group
          _ = x * a := by rw [(hfix a ha).1]
    have hyC : y ∈ Subgroup.centralizer (Y : Set G) := Subgroup.mem_centralizer_iff.mpr
      fun a ha => by
        calc a * y = a * y * a⁻¹ * a := by group
          _ = y * a := by rw [(hfix a ha).2]
    exact ⟨(⟨x, hx, hxC⟩, ⟨y, hy, hyC⟩), rfl⟩

theorem psi_bot_range : (psi F (bot_le : (⊥ : Subgroup G) ≤ Xv L V₁ (a₀ * c₀))).range = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨a, rfl⟩
  have ha : a = 1 := Subtype.ext (Subgroup.mem_bot.mp a.2)
  rw [ha, map_one]
  exact Subgroup.one_mem _

theorem card_fixS_bot : Nat.card (FF3.fixS (⊥ : Subgroup (Matrix.SpecialLinearGroup (Fin 3)
    (ZMod 2)))) = 8 := by
  have : FF3.fixS (⊥ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))) = ⊤ := by
    rw [eq_top_iff]
    intro ξ _ g hg
    rw [Subgroup.mem_bot.mp hg, Matrix.SpecialLinearGroup.coe_one, one_mulVec]
  rw [this, AddSubgroup.card_top, FF3.card_vec3]

theorem card_fixT_bot : Nat.card (FF3.fixT (⊥ : Subgroup (Matrix.SpecialLinearGroup (Fin 3)
    (ZMod 2)))) = 8 := by
  have : FF3.fixT (⊥ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))) = ⊤ := by
    rw [eq_top_iff]
    intro ξ _ g hg
    rw [Subgroup.mem_bot.mp hg, Matrix.SpecialLinearGroup.coe_one, transpose_one, one_mulVec]
  rw [this, AddSubgroup.card_top, FF3.card_vec3]

theorem card_W₁ (F : Frame S 3) : Nat.card S.W₁ = 8 := by
  have h := card_W₁_inf F (bot_le : (⊥ : Subgroup G) ≤ Xv L V₁ (a₀ * c₀))
  rw [psi_bot_range, card_fixS_bot, Subgroup.coe_bot, Subgroup.centralizer_singleton_one,
    inf_top_eq] at h
  exact h

theorem card_W₂ (F : Frame S 3) : Nat.card S.W₂ = 8 := by
  have h := card_W₂_inf F (bot_le : (⊥ : Subgroup G) ≤ Xv L V₁ (a₀ * c₀))
    (fun a ha => by rw [Subgroup.mem_bot.mp ha, one_mul])
  rw [psi_bot_range, card_fixT_bot, Subgroup.coe_bot, Subgroup.centralizer_singleton_one,
    inf_top_eq] at h
  exact h

theorem card_W (F : Frame S 3) : Nat.card ↥(S.W₁ ⊔ S.W₂) = 64 := by
  have h := card_W_inf (S := S) (bot_le : (⊥ : Subgroup G) ≤ Xv L V₁ (a₀ * c₀))
  rw [Subgroup.coe_bot, Subgroup.centralizer_singleton_one, inf_top_eq, inf_top_eq,
    inf_top_eq, card_W₁ F, card_W₂ F] at h
  exact h

theorem card_mul_card_le_of_le (F : Frame S 3) {A : Subgroup G} (hA : A ≤ Xv L V₁ (a₀ * c₀))
    (hAe : IsElemAbelian 2 A)
    (hAW : ¬ A ≤ Subgroup.centralizer ((S.W₁ ⊔ S.W₂ : Subgroup G) : Set G)) :
    (A ⊓ Subgroup.centralizer ((S.W₁ ⊔ S.W₂ : Subgroup G) : Set G)).relIndex A *
      Nat.card ↥((S.W₁ ⊔ S.W₂) ⊓ Subgroup.centralizer (A : Set G)) ≤ 32 := by
  have hA2 : ∀ a ∈ A, a * a = 1 := fun a ha => by rw [← pow_two]; exact hAe.2 a ha
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hAe.1.1.comm ⟨a, ha⟩ ⟨b, hb⟩)
  set B := (psi F hA).range with hB
  have hB2 : ∀ g ∈ B, g * g = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_mul, show a * a = 1 from Subtype.ext (hA2 a a.2), map_one]
  have hBc : ∀ g ∈ B, ∀ h ∈ B, g * h = h * g := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul, show a * b = b * a from Subtype.ext (hcomm a a.2 b b.2)]
  have hB1 : B ≠ ⊥ := by
    intro h
    apply hAW
    intro a ha
    have h1 : psi F hA ⟨a, ha⟩ = 1 := by
      have : psi F hA ⟨a, ha⟩ ∈ (⊥ : Subgroup _) := h ▸ ⟨⟨a, ha⟩, rfl⟩
      exact Subgroup.mem_bot.mp this
    exact (psi_eq_one_iff F hA ⟨a, ha⟩).mp h1
  obtain ⟨hcore, -, -⟩ := FF3.card_mul_card_mul_card_le hB2 hBc hB1
  rw [relIndex_eq F hA, card_W_inf hA, card_W₁_inf F hA, card_W₂_inf F hA hA2, ← mul_assoc]
  exact hcore

theorem card_mul_card_le_of_swap (F : Frame S 3) {A : Subgroup G}
    (hAM : A ≤ Subgroup.normalizer (L : Set G))
    (hAv : A ≤ Subgroup.centralizer ({a₀ * c₀} : Set G)) (hAe : IsElemAbelian 2 A)
    (hA1 : ¬ A ≤ Subgroup.normalizer (V₁ : Set G)) :
    (A ⊓ Subgroup.centralizer ((S.W₁ ⊔ S.W₂ : Subgroup G) : Set G)).relIndex A *
      Nat.card ↥((S.W₁ ⊔ S.W₂) ⊓ Subgroup.centralizer (A : Set G)) ≤ 32 := by
  have := S.hVe.1
  set A₀ := A ⊓ Subgroup.normalizer (V₁ : Set G) with hA₀
  have hA₀X : A₀ ≤ Xv L V₁ (a₀ * c₀) := fun a ha => ⟨⟨hAM ha.1, ha.2⟩, hAv ha.1⟩
  obtain ⟨t, htA, ht1⟩ : ∃ t ∈ A, t ∉ Subgroup.normalizer (V₁ : Set G) := by
    by_contra h
    push Not at h
    exact hA1 h
  obtain ⟨hs₁, hs₂⟩ := Sec121Swap.swap_of_hyp121 S.hyp (hAM htA) ht1
  have hCA : A ⊓ Subgroup.centralizer ((S.W₁ ⊔ S.W₂ : Subgroup G) : Set G) =
      A₀ ⊓ Subgroup.centralizer ((S.W₁ ⊔ S.W₂ : Subgroup G) : Set G) := by
    refine le_antisymm (fun a ha => ⟨⟨ha.1, ?_⟩, ha.2⟩) (inf_le_inf_right _ inf_le_left)
    by_contra hn
    obtain ⟨h₁, -⟩ := Sec121Swap.swap_of_hyp121 S.hyp (hAM ha.1) hn
    obtain ⟨x, hx, hx1⟩ : ∃ x ∈ S.W₁, x ≠ 1 := by
      by_contra h
      push Not at h
      have h2 := card_W₁ F
      have h3 : S.W₁ = ⊥ := eq_bot_iff.mpr fun x hx => Subgroup.mem_bot.mpr (h x hx)
      rw [h3, Subgroup.card_bot] at h2
      omega
    have hax : a * x * a⁻¹ = x := by
      rw [← Subgroup.mem_centralizer_iff.mp ha.2 x (Subgroup.mem_sup_left hx),
        mul_inv_cancel_right]
    have h3 : x ∈ V₁ ⊓ V₂ := ⟨hx.1, hax ▸ h₁ x hx.1⟩
    rw [S.hyp.inf, Subgroup.mem_bot] at h3
    exact hx1 h3
  have hidx : A₀.relIndex A = 2 := by
    have h1 := Sec1215.two_mul_card_inf_normalizer S.hyp hAM htA ht1
    have h2 := Subgroup.relIndex_mul_card A₀ A
    rw [inf_of_le_left inf_le_left] at h2
    rw [← h1] at h2
    have hpos : 0 < Nat.card A₀ := Nat.card_pos
    nlinarith
  have hrel : (A ⊓ Subgroup.centralizer ((S.W₁ ⊔ S.W₂ : Subgroup G) : Set G)).relIndex A =
      2 * (A₀ ⊓ Subgroup.centralizer ((S.W₁ ⊔ S.W₂ : Subgroup G) : Set G)).relIndex A₀ := by
    rw [hCA, ← Subgroup.relIndex_mul_relIndex _ A₀ A inf_le_left (inf_le_left : A₀ ≤ A), hidx,
      mul_comm]
  have hproj : ∀ w ∈ (S.W₁ ⊔ S.W₂) ⊓ Subgroup.centralizer (A : Set G),
      ∃ x ∈ S.W₁ ⊓ Subgroup.centralizer (A₀ : Set G), w = x * (t * x * t⁻¹) := by
    rintro w ⟨hwW, hwC⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := exists_mul_of_mem_sup
      (fun x (hx : x ∈ S.W₁) y (hy : y ∈ S.W₂) => S.comm (S.le₁ hx.1) (S.le₂ hy.1)) hwW
    have hty : t * y * t⁻¹ = x ∧ t * x * t⁻¹ = y := by
      have e : t * y * t⁻¹ * (t * x * t⁻¹) = x * y := by
        calc t * y * t⁻¹ * (t * x * t⁻¹) = t * (y * x) * t⁻¹ := by group
          _ = t * (x * y) * t⁻¹ := by rw [S.comm (S.le₂ hy.1) (S.le₁ hx.1)]
          _ = x * y := by rw [Subgroup.mem_centralizer_iff.mp hwC t htA, mul_inv_cancel_right]
      exact S.decomp_unique (hs₂ y hy.1) hx.1 (hs₁ x hx.1) hy.1 e
    refine ⟨x, ⟨hx, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩, by rw [hty.2]⟩
    have e : a * x * a⁻¹ * (a * y * a⁻¹) = x * y := by
      calc a * x * a⁻¹ * (a * y * a⁻¹) = a * (x * y) * a⁻¹ := by group
        _ = x * y := by rw [Subgroup.mem_centralizer_iff.mp hwC a ha.1, mul_inv_cancel_right]
    have h1 := (S.decomp_unique ((Subgroup.mem_normalizer_iff.mp ha.2 x).mp hx.1) hx.1
      ((Subgroup.mem_normalizer_iff.mp (S.Xv_le_normalizer₂ (hA₀X ha)) y).mp hy.1) hy.1 e).1
    calc a * x = a * x * a⁻¹ * a := by group
      _ = x * a := by rw [h1]
  have hcard : Nat.card ↥((S.W₁ ⊔ S.W₂) ⊓ Subgroup.centralizer (A : Set G)) ≤
      Nat.card ↥(S.W₁ ⊓ Subgroup.centralizer (A₀ : Set G)) := by
    refine Nat.card_le_card_of_injective
      (fun w => ⟨Classical.choose (hproj w w.2), (Classical.choose_spec (hproj w w.2)).1⟩) ?_
    intro w w' h
    have h1 : Classical.choose (hproj w w.2) = Classical.choose (hproj w' w'.2) :=
      congrArg Subtype.val h
    apply Subtype.ext
    rw [(Classical.choose_spec (hproj w w.2)).2, (Classical.choose_spec (hproj w' w'.2)).2, h1]
  rw [hrel]
  by_cases hA₀W : A₀ ≤ Subgroup.centralizer ((S.W₁ ⊔ S.W₂ : Subgroup G) : Set G)
  · rw [inf_of_le_left hA₀W, Subgroup.relIndex_self, mul_one]
    have h1 : Nat.card ↥(S.W₁ ⊓ Subgroup.centralizer (A₀ : Set G)) ≤ 8 :=
      (Subgroup.card_le_of_le inf_le_left).trans (card_W₁ F).le
    omega
  ·
    have hA₀e : IsElemAbelian 2 A₀ := Sec1216Gen.isElemAbelian_of_le hAe inf_le_left
    have hA2 : ∀ a ∈ A₀, a * a = 1 := fun a ha => by rw [← pow_two]; exact hA₀e.2 a ha
    have hcomm : ∀ a ∈ A₀, ∀ b ∈ A₀, a * b = b * a := fun a ha b hb =>
      congrArg Subtype.val (hA₀e.1.1.comm ⟨a, ha⟩ ⟨b, hb⟩)
    set B := (psi F hA₀X).range with hB
    have hB2 : ∀ g ∈ B, g * g = 1 := by
      rintro _ ⟨a, rfl⟩
      rw [← map_mul, show a * a = 1 from Subtype.ext (hA2 a a.2), map_one]
    have hBc : ∀ g ∈ B, ∀ h ∈ B, g * h = h * g := by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      rw [← map_mul, ← map_mul, show a * b = b * a from Subtype.ext (hcomm a a.2 b b.2)]
    have hB1 : B ≠ ⊥ := by
      intro h
      apply hA₀W
      intro a ha
      have h1 : psi F hA₀X ⟨a, ha⟩ = 1 := by
        have : psi F hA₀X ⟨a, ha⟩ ∈ (⊥ : Subgroup _) := h ▸ ⟨⟨a, ha⟩, rfl⟩
        exact Subgroup.mem_bot.mp this
      exact (psi_eq_one_iff F hA₀X ⟨a, ha⟩).mp h1
    obtain ⟨hcore, -, hT2⟩ := FF3.card_mul_card_mul_card_le hB2 hBc hB1
    rw [relIndex_eq F hA₀X]
    rw [card_W₁_inf F hA₀X] at hcard
    have h16 : Nat.card B * Nat.card (FF3.fixS B) ≤ 16 := by
      by_contra h
      push Not at h
      have : 17 * 2 ≤ Nat.card B * Nat.card (FF3.fixS B) * Nat.card (FF3.fixT B) :=
        Nat.mul_le_mul h hT2
      omega
    calc 2 * Nat.card B * Nat.card ↥((S.W₁ ⊔ S.W₂) ⊓ Subgroup.centralizer (A : Set G)) ≤
          2 * Nat.card B * Nat.card (FF3.fixS B) := Nat.mul_le_mul_left _ hcard
      _ = 2 * (Nat.card B * Nat.card (FF3.fixS B)) := by ring
      _ ≤ 2 * 16 := Nat.mul_le_mul_left _ h16
      _ = 32 := by norm_num

end Setting

end Sec1211Ns

end CFSG.Quasithin.H13
