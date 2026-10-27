module

public import CFSG.RankThree.GF2n.Tim78S48EndPts
import CFSG.RankThree.PartTwo.Sec6.Item612Plus

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n
open scoped commutatorElement Matrix

variable {G : Type} [Group G]

namespace EndHelp

theorem conj_sup (r : G) (A A' : Subgroup G) :
    conjSubgroup r (A ⊔ A') = conjSubgroup r A ⊔ conjSubgroup r A' := Subgroup.map_sup _ _ _

theorem inducesNaturalSL2_conj {n : ℕ} {H W : Subgroup G} (h : InducesNaturalSL2 n H W)
    (r : G) : InducesNaturalSL2 n (conjSubgroup r H) (conjSubgroup r W) := by
  obtain ⟨φ, ψ, hφs, hφk, hφψ⟩ := h
  let eH : ↥(conjSubgroup r H) →* ↥H :=
    { toFun := fun z => ⟨r⁻¹ * z * r, mem_conjSubgroup.mp z.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  let eW : ↥(conjSubgroup r W) ≃* ↥W :=
    { toFun := fun z => ⟨r⁻¹ * z * r, mem_conjSubgroup.mp z.2⟩
      invFun := fun w => ⟨r * w * r⁻¹, mem_conjSubgroup.mpr (by simpa [mul_assoc] using w.2)⟩
      left_inv := fun z => Subtype.ext (by show r * (r⁻¹ * (z : G) * r) * r⁻¹ = z; group)
      right_inv := fun w => Subtype.ext (by show r⁻¹ * (r * (w : G) * r⁻¹) * r = w; group)
      map_mul' := fun a b => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  refine ⟨φ.comp eH, eW.trans ψ, ?_, ?_, ?_⟩
  · intro m
    obtain ⟨z, hz⟩ := hφs m
    refine ⟨⟨r * z * r⁻¹, mem_conjSubgroup.mpr (by simpa [mul_assoc] using z.2)⟩, ?_⟩
    rw [MonoidHom.comp_apply, ← hz]
    congr 1
    exact Subtype.ext (by show r⁻¹ * (r * (z : G) * r⁻¹) * r = z; group)
  · ext z
    have hz : z ∈ (φ.comp eH).ker ↔ eH z ∈ φ.ker := by simp [MonoidHom.mem_ker]
    rw [hz, hφk, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff,
      Subgroup.mem_centralizer_iff]
    change (∀ w ∈ (W : Set G), w * (r⁻¹ * z * r) = (r⁻¹ * z * r) * w) ↔
      ∀ w ∈ (conjSubgroup r W : Set G), w * (z : G) = (z : G) * w
    constructor
    · intro hc w hw
      have hw' : r⁻¹ * w * r ∈ W := mem_conjSubgroup.mp hw
      have := hc _ hw'
      calc w * z = r * ((r⁻¹ * w * r) * (r⁻¹ * z * r)) * r⁻¹ := by group
        _ = r * ((r⁻¹ * z * r) * (r⁻¹ * w * r)) * r⁻¹ := by rw [this]
        _ = z * w := by group
    · intro hc w hw
      have hw' : r * w * r⁻¹ ∈ conjSubgroup r W :=
        mem_conjSubgroup.mpr (by simpa [mul_assoc] using hw)
      have := hc _ hw'
      calc w * (r⁻¹ * z * r) = r⁻¹ * ((r * w * r⁻¹) * z) * r := by group
        _ = r⁻¹ * (z * (r * w * r⁻¹)) * r := by rw [this]
        _ = (r⁻¹ * z * r) * w := by group
  · intro z w w' hww
    refine hφψ (eH z) (eW w) (eW w') ?_
    change r⁻¹ * (w' : G) * r = (r⁻¹ * z * r) * (r⁻¹ * w * r) * (r⁻¹ * z * r)⁻¹
    rw [hww]; group

end EndHelp

open EndHelp

namespace EndgameData

variable [Finite G] {M B Q P T : Subgroup G} {g : G}
  {C L : Subgroup G} (E : EndgameData M B Q P T g C L) (H : Hyp4 M B Q P T)
include E H

omit H in
theorem conj_inv_mem_L {r l : G} (hr : r ∈ Subgroup.normalizer (L : Set G)) (hl : l ∈ L) :
    r⁻¹ * l * r ∈ L := by
  have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hr) l).mp hl
  simpa using this

theorem conjT_comm_conjC {r x y : G} (hx : x ∈ conjSubgroup r T) (hy : y ∈ conjSubgroup r C) :
    x * y = y * x := by
  rw [mem_conjSubgroup] at hx hy
  have := Subgroup.mem_centralizer_iff.mp (H.T_le_centralizer_P hx) _ (E.C_le_P hy)
  calc x * y = r * ((r⁻¹ * x * r) * (r⁻¹ * y * r)) * r⁻¹ := by group
    _ = r * ((r⁻¹ * y * r) * (r⁻¹ * x * r)) * r⁻¹ := by rw [this]
    _ = y * x := by group

omit H in
theorem conjT_comm_L {r l x : G} (hr : r ∈ Subgroup.normalizer (L : Set G)) (hl : l ∈ L)
    (hx : x ∈ conjSubgroup r T) : ⁅l, x⁆ ∈ conjSubgroup r B := by
  rw [mem_conjSubgroup] at hx ⊢
  have h1 := E.T_comm _ hx _ (E.conj_inv_mem_L hr hl)
  have e : r⁻¹ * ⁅l, x⁆ * r = ⁅r⁻¹ * l * r, r⁻¹ * x * r⁆ := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact h1

theorem conjT_le_normalizer_L {r : G} (hr : r ∈ Subgroup.normalizer (L : Set G)) :
    conjSubgroup r T ≤ Subgroup.normalizer (L : Set G) := by
  intro x hx
  rw [mem_conjSubgroup] at hx
  have h1 : r⁻¹ * x * r ∈ Subgroup.normalizer (L : Set G) := E.Q_norm (H.T_le_Q hx)
  have : x = r * (r⁻¹ * x * r) * r⁻¹ := by group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hr h1) (Subgroup.inv_mem _ hr)

omit H in
theorem conjT_normalizes {r x : G} (hr : r ∈ Subgroup.normalizer (L : Set G))
    (hx : x ∈ conjSubgroup r T) {N : Subgroup G} (hNL : N ≤ L) (hB : conjSubgroup r B ≤ N) :
    x ∈ Subgroup.normalizer (N : Set G) := by
  refine Subgroup.mem_normalizer_fintype fun n hn => ?_
  have h1 : ⁅n, x⁆ ∈ N := hB (E.conjT_comm_L hr (hNL hn) hx)
  have : x * n * x⁻¹ = ⁅n, x⁆⁻¹ * n := by simp only [commutatorElement_def]; group
  rw [this]
  exact N.mul_mem (N.inv_mem h1) hn

theorem hyp48_of_mem {g' : G} (hg' : g' ∈ Subgroup.normalizer (L : Set G)) :
    Hyp48 M B T g' where
  leM := by
    rw [← H.normalizer_B]
    exact le_normalizer_of_comm fun x hx y hy =>
      E.comm_L (conj_le_of_mem_normalizer hg' E.B_le_L hx) (E.B_le_L hy)
  comm_T := fun a ha t ht => E.T_comm t ht a (conj_le_of_mem_normalizer hg' E.B_le_L ha)
  comm_Tg := by
    intro b hb t ht
    rw [mem_conjSubgroup] at ht ⊢
    have h1 := E.T_comm _ ht _ (E.conj_inv_mem_L hg' (E.B_le_L hb))
    have e : g'⁻¹ * ⁅b, t⁆ * g' = ⁅g'⁻¹ * b * g', g'⁻¹ * t * g'⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact h1

theorem not_le_P_pair {r₁ r₂ : G} (hr₁ : r₁ ∈ Subgroup.normalizer (L : Set G))
    (hr₂ : r₂ ∈ Subgroup.normalizer (L : Set G))
    (hnp : ¬ conjSubgroup r₂ B ≤ conjSubgroup r₁ C) : ¬ conjSubgroup (r₁⁻¹ * r₂) B ≤ P := by
  intro h
  apply hnp
  have h1 : conjSubgroup r₂ B ≤ conjSubgroup r₁ P := by
    have := (conj_le_conj_iff r₁).mpr h
    rwa [← conjSubgroup_mul, mul_inv_cancel_left] at this
  rw [← E.conj_inf_P H hr₁]
  exact le_inf (conj_le_of_mem_normalizer hr₂ E.B_le_L) h1

omit H in
theorem card_le_mul_inf {A : Subgroup G} (hA : A ≤ L) {r : G}
    (hr : r ∈ Subgroup.normalizer (L : Set G)) :
    Nat.card A ≤ Nat.card B * Nat.card (A ⊓ conjSubgroup r C : Subgroup G) := by
  have hK := E.conjC_le_L hr
  have hnorm : A ≤ Subgroup.normalizer (conjSubgroup r C : Set G) :=
    le_normalizer_of_comm fun x hx y hy => E.comm_L (hA hx) (hK hy)
  have h := PartTwo.Sec6.card_sup_mul_card_inf hnorm
  have h1 : Nat.card (A ⊔ conjSubgroup r C : Subgroup G) ≤ Nat.card L :=
    Subgroup.card_le_of_le (sup_le hA hK)
  rw [card_conjSubgroup] at h
  rw [E.card_L] at h1
  have hc : 0 < Nat.card C := Nat.card_pos
  refine Nat.le_of_mul_le_mul_right ?_ hc
  calc Nat.card A * Nat.card C = Nat.card (A ⊔ conjSubgroup r C : Subgroup G) *
        Nat.card (A ⊓ conjSubgroup r C : Subgroup G) := h.symm
    _ ≤ (Nat.card C * Nat.card B) * Nat.card (A ⊓ conjSubgroup r C : Subgroup G) :=
        Nat.mul_le_mul_right _ h1
    _ = (Nat.card B * Nat.card (A ⊓ conjSubgroup r C : Subgroup G)) * Nat.card C := by ring

theorem inf_pair_le (h45 : Meet45 B Q P) {r : G} (hr : r ∈ Subgroup.normalizer (L : Set G))
    {D₁ D₂ : Subgroup G} (hD₁ : D₁ ∈ classIn B L) (hD₂ : D₂ ∈ classIn B L)
    (h₁ : D₁ ≤ conjSubgroup r C) (h₂ : ¬ D₂ ≤ conjSubgroup r C) :
    (D₁ ⊔ D₂) ⊓ conjSubgroup r C ≤ D₁ := by
  intro n hn
  have hnorm : D₂ ≤ Subgroup.normalizer (D₁ : Set G) :=
    le_normalizer_of_comm fun x hx y hy => E.comm_L (hD₂.2 hx) (hD₁.2 hy)
  obtain ⟨d₁, hd₁, d₂, hd₂, rfl⟩ := exists_mul_of_mem_sup hnorm hn.1
  have hd₂C : d₂ ∈ conjSubgroup r C := by
    have := (conjSubgroup r C).mul_mem ((conjSubgroup r C).inv_mem (h₁ hd₁)) hn.2
    simpa using this
  by_cases hd : d₂ = 1
  · rw [hd, mul_one]
    exact hd₁
  · exfalso
    apply h₂
    refine E.pt_le_conjC H h45 hr hD₂ ?_
    intro hbot
    have : d₂ ∈ D₂ ⊓ conjSubgroup r C := ⟨hd₂, hd₂C⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact hd this

theorem L₀_le_sup (h45 : Meet45 B Q P) (hg : g ∈ Subgroup.normalizer (L : Set G)) {r₁ r₂ : G}
    (hr₁ : r₁ ∈ Subgroup.normalizer (L : Set G)) (hr₂ : r₂ ∈ Subgroup.normalizer (L : Set G))
    (hD₁ : conjSubgroup r₁ B ≤ C ⊓ conjSubgroup g C)
    (hD₂ : conjSubgroup r₂ B ≤ C ⊓ conjSubgroup g C)
    (hnp : ¬ conjSubgroup r₂ B ≤ conjSubgroup r₁ C) :
    C ⊓ conjSubgroup g C ≤ (conjSubgroup r₁ B ⊔ conjSubgroup r₂ B) ⊔
      (C ⊓ conjSubgroup g C ⊓ conjSubgroup r₁ C ⊓ conjSubgroup r₂ C) := by
  have hL₀L : C ⊓ conjSubgroup g C ≤ L := inf_le_left.trans E.C_le_L
  have hD₁L : conjSubgroup r₁ B ≤ L := conj_le_of_mem_normalizer hr₁ E.B_le_L
  have hD₂L : conjSubgroup r₂ B ≤ L := conj_le_of_mem_normalizer hr₂ E.B_le_L
  have hD₁cls : conjSubgroup r₁ B ∈ classIn B L := ⟨⟨r₁, rfl⟩, hD₁L⟩
  have hD₂cls : conjSubgroup r₂ B ∈ classIn B L := ⟨⟨r₂, rfl⟩, hD₂L⟩
  have hD₁C : conjSubgroup r₁ B ≤ conjSubgroup r₁ C := (conj_le_conj_iff r₁).mpr E.B_le_C
  have hD₂C : conjSubgroup r₂ B ≤ conjSubgroup r₂ C := (conj_le_conj_iff r₂).mpr E.B_le_C
  have hne : conjSubgroup r₁ B ≠ conjSubgroup r₂ B := fun h => hnp (h ▸ hD₁C)
  have hnp' : ¬ conjSubgroup r₁ B ≤ conjSubgroup r₂ C := by
    intro h
    apply hnp
    have h1 : conjSubgroup r₁ B ≤ conjSubgroup r₂ Q :=
      h.trans ((conj_le_conj_iff r₂).mpr (E.C_le_Q H))
    have h2 := E.symm_Q H (r := r₂) (r' := r₁) h1 hne
    rw [← E.conj_inf_Q H hr₁]
    exact le_inf hD₂L h2
  have hi₁ : (conjSubgroup r₁ B ⊔ conjSubgroup r₂ B) ⊓ conjSubgroup r₁ C ≤ conjSubgroup r₁ B :=
    E.inf_pair_le H h45 hr₁ hD₁cls hD₂cls hD₁C hnp
  have hi₂ : (conjSubgroup r₁ B ⊔ conjSubgroup r₂ B) ⊓ conjSubgroup r₂ C ≤ conjSubgroup r₂ B := by
    rw [sup_comm]
    exact E.inf_pair_le H h45 hr₂ hD₂cls hD₁cls hD₂C hnp'
  have hND : (conjSubgroup r₁ B ⊔ conjSubgroup r₂ B) ⊓
      (C ⊓ conjSubgroup g C ⊓ conjSubgroup r₁ C ⊓ conjSubgroup r₂ C) = ⊥ := by
    rw [eq_bot_iff]
    intro n hn
    have h1 : n ∈ conjSubgroup r₁ B := hi₁ ⟨hn.1, hn.2.1.2⟩
    have h2 : n ∈ conjSubgroup r₂ B := hi₂ ⟨hn.1, hn.2.2⟩
    have : n ∈ conjSubgroup r₁ B ⊓ conjSubgroup r₂ B := ⟨h1, h2⟩
    rwa [inf_conj_eq_bot_of_ne H hne] at this
  have hq : Nat.card (conjSubgroup r₁ B ⊔ conjSubgroup r₂ B : Subgroup G) = Nat.card B ^ 2 := by
    have hnorm : conjSubgroup r₁ B ≤ Subgroup.normalizer (conjSubgroup r₂ B : Set G) :=
      le_normalizer_of_comm fun x hx y hy => E.comm_L (hD₁L hx) (hD₂L hy)
    have h := PartTwo.Sec6.card_sup_mul_card_inf hnorm
    rw [inf_conj_eq_bot_of_ne H hne, Subgroup.card_bot, mul_one, card_conjSubgroup,
      card_conjSubgroup] at h
    rw [h, pow_two]
  have hc1 := E.card_le_mul_inf hL₀L hr₁
  have hc2 := E.card_le_mul_inf (A := C ⊓ conjSubgroup g C ⊓ conjSubgroup r₁ C)
    (inf_le_left.trans hL₀L) hr₂
  have hL₁L₀ : C ⊓ conjSubgroup g C ⊓ conjSubgroup r₁ C ⊓ conjSubgroup r₂ C ≤
      C ⊓ conjSubgroup g C := inf_le_left.trans inf_le_left
  have hnormL₁ : conjSubgroup r₁ B ⊔ conjSubgroup r₂ B ≤ Subgroup.normalizer
      ((C ⊓ conjSubgroup g C ⊓ conjSubgroup r₁ C ⊓ conjSubgroup r₂ C : Subgroup G) : Set G) :=
    le_normalizer_of_comm fun x hx y hy => E.comm_L
      ((sup_le hD₁L hD₂L) hx) (hL₀L (hL₁L₀ hy))
  have hprod := PartTwo.Sec6.card_sup_mul_card_inf hnormL₁
  rw [hND, Subgroup.card_bot, mul_one, hq] at hprod
  have hle : (conjSubgroup r₁ B ⊔ conjSubgroup r₂ B) ⊔
      (C ⊓ conjSubgroup g C ⊓ conjSubgroup r₁ C ⊓ conjSubgroup r₂ C) ≤ C ⊓ conjSubgroup g C :=
    sup_le (sup_le hD₁ hD₂) hL₁L₀
  have heq := Subgroup.eq_of_le_of_card_ge hle (by
    rw [hprod]
    calc Nat.card (C ⊓ conjSubgroup g C : Subgroup G)
        ≤ Nat.card B * Nat.card (C ⊓ conjSubgroup g C ⊓ conjSubgroup r₁ C : Subgroup G) := hc1
      _ ≤ Nat.card B * (Nat.card B *
          Nat.card (C ⊓ conjSubgroup g C ⊓ conjSubgroup r₁ C ⊓ conjSubgroup r₂ C : Subgroup G)) :=
        Nat.mul_le_mul_left _ hc2
      _ = Nat.card B ^ 2 *
          Nat.card (C ⊓ conjSubgroup g C ⊓ conjSubgroup r₁ C ⊓ conjSubgroup r₂ C : Subgroup G) := by
        ring)
  exact heq.ge

end EndgameData

end CFSG.RankThree.GF2n.Tim78
