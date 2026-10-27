module

public import CFSG.CGT.Timmesfeld75.ConjCentralizer
import all CFSG.Timmesfeld.RootInvolutions.RootInvolutionSetting
public import CFSG.RankThree.GF2n.Tim77.Cor2Hyp
public import CFSG.RankThree.GF2n.Tim77.Defs

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.RootInvolutions Subgroup

variable {G : Type} [Group G]

theorem conjSubgroup_conj_twist (g h : G) (T : Subgroup G) :
    conjSubgroup h (conjSubgroup g T) = conjSubgroup g (conjSubgroup (g⁻¹ * h * g) T) := by
  rw [← conjSubgroup_mul, ← conjSubgroup_mul]
  congr 1
  group

theorem conjSubgroup_inv_conj_cancel (g : G) (T : Subgroup G) :
    conjSubgroup g⁻¹ (conjSubgroup g T) = T := by
  rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]

theorem conjSubgroup_conj_inv_cancel (g : G) (T : Subgroup G) :
    conjSubgroup g (conjSubgroup g⁻¹ T) = T := by
  rw [← conjSubgroup_mul, mul_inv_cancel, conjSubgroup_one]

theorem conjSubgroup_le_conj_iff (g : G) {S T : Subgroup G} :
    conjSubgroup g S ≤ conjSubgroup g T ↔ S ≤ T := by
  unfold conjSubgroup
  exact Subgroup.map_le_map_iff_of_injective (MulAut.conj g).injective

theorem conjSubgroup_inj_t77 (g : G) {S T : Subgroup G}
    (h : conjSubgroup g S = conjSubgroup g T) : S = T :=
  le_antisymm ((conjSubgroup_le_conj_iff g).1 h.le) ((conjSubgroup_le_conj_iff g).1 h.ge)

theorem conjSubgroup_bot_t77 (g : G) : conjSubgroup g (⊥ : Subgroup G) = ⊥ :=
  Subgroup.map_bot _

theorem conjSubgroup_top_t77 (g : G) : conjSubgroup g (⊤ : Subgroup G) = ⊤ :=
  Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective

theorem conjSubgroup_sup_t77 (g : G) (U V : Subgroup G) :
    conjSubgroup g (U ⊔ V) = conjSubgroup g U ⊔ conjSubgroup g V :=
  Subgroup.map_sup U V _

theorem conjSubgroup_eq_bot_t77 (g : G) (T : Subgroup G) : conjSubgroup g T = ⊥ ↔ T = ⊥ :=
  ⟨fun e => conjSubgroup_inj_t77 g (e.trans (conjSubgroup_bot_t77 g).symm),
    fun e => by rw [e, conjSubgroup_bot_t77]⟩

theorem conjSubgroup_map_normalizer (g : G) (T : Subgroup G) :
    conjSubgroup g (Subgroup.normalizer (T : Set G)) =
      Subgroup.normalizer (conjSubgroup g T : Set G) :=
  Subgroup.map_equiv_normalizer_eq T (MulAut.conj g)

theorem normalizerIn_conjSubgroup_t77 (g : G) (A B : Subgroup G) :
    normalizerIn (conjSubgroup g A) (conjSubgroup g B) = conjSubgroup g (normalizerIn A B) := by
  unfold normalizerIn
  rw [← conjSubgroup_map_normalizer, conjSubgroup_inf]

theorem relIndex_conjSubgroup_t77 (g : G) (H K : Subgroup G) :
    (conjSubgroup g H).relIndex (conjSubgroup g K) = H.relIndex K :=
  Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom) H K
    (MulAut.conj g).injective

theorem weakClosure_conjSubgroup_t77 (g : G) (X C : Subgroup G) :
    weakClosure (conjSubgroup g X) (conjSubgroup g C) = conjSubgroup g (weakClosure X C) := by
  have hset : {x : G | ∃ h : G, conjSubgroup h (conjSubgroup g X) ≤ conjSubgroup g C ∧
      x ∈ conjSubgroup h (conjSubgroup g X)} =
      (MulAut.conj g).toMonoidHom ''
        {x : G | ∃ k : G, conjSubgroup k X ≤ C ∧ x ∈ conjSubgroup k X} := by
    ext x
    constructor
    · rintro ⟨h, hle, hx⟩
      rw [conjSubgroup_conj_twist g h X] at hle hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      exact ⟨y, ⟨g⁻¹ * h * g, (conjSubgroup_le_conj_iff g).1 hle, hy⟩, rfl⟩
    · rintro ⟨y, ⟨k, hkC, hy⟩, rfl⟩
      refine ⟨g * k * g⁻¹, ?_, ?_⟩
      · rw [conjSubgroup_conj_twist g (g * k * g⁻¹) X,
          show g⁻¹ * (g * k * g⁻¹) * g = k by group]
        exact (conjSubgroup_le_conj_iff g).2 hkC
      · rw [conjSubgroup_conj_twist g (g * k * g⁻¹) X,
          show g⁻¹ * (g * k * g⁻¹) * g = k by group]
        exact Subgroup.mem_map_of_mem _ hy
  unfold weakClosure
  rw [hset, ← MonoidHom.map_closure]
  rfl

theorem isPGroup_conj_map_t77 {p : ℕ} {S : Subgroup G} (hS : IsPGroup p S) (g : G) :
    IsPGroup p (conjSubgroup g S) :=
  hS.map (MulAut.conj g).toMonoidHom

theorem isRootTypeIn_conjSubgroup_t77 {p : ℕ} {H A : Subgroup G} (g : G)
    (h : IsRootTypeIn p H A) : IsRootTypeIn p (conjSubgroup g H) (conjSubgroup g A) := by
  obtain ⟨hAH, hel, hdis, hnorm⟩ := h
  refine ⟨(conjSubgroup_le_conj_iff g).2 hAH, isElemAbelian_conj hel g, ?_, ?_⟩
  · intro k hk
    have hj := mem_conjSubgroup.mp hk
    rw [conjSubgroup_conj_twist g k A, ← conjSubgroup_inf]
    rcases hdis _ hj with h1 | h1
    · left
      rw [h1]
    · right
      rw [h1, conjSubgroup_bot_t77]
  · intro k hk hne a ha b hb
    have hj := mem_conjSubgroup.mp hk
    rw [conjSubgroup_conj_twist g k A] at hne hb
    rw [normalizerIn_conjSubgroup_t77] at hne
    have hne' : normalizerIn A (conjSubgroup (g⁻¹ * k * g) A) ≠ ⊥ := fun e =>
      hne (by rw [e, conjSubgroup_bot_t77])
    have key := hnorm _ hj hne' (g⁻¹ * a * g) (mem_conjSubgroup.mp ha) (g⁻¹ * b * g)
      (mem_conjSubgroup.mp hb)
    calc a * b = g * ((g⁻¹ * a * g) * (g⁻¹ * b * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * b * g) * (g⁻¹ * a * g)) * g⁻¹ := by rw [key]
      _ = b * a := by group

theorem isRootTypeIn_conjSubgroup_iff_t77 {p : ℕ} {H A : Subgroup G} (g : G) :
    IsRootTypeIn p (conjSubgroup g H) (conjSubgroup g A) ↔ IsRootTypeIn p H A := by
  refine ⟨fun h => ?_, isRootTypeIn_conjSubgroup_t77 g⟩
  have h' := isRootTypeIn_conjSubgroup_t77 g⁻¹ h
  rwa [conjSubgroup_inv_conj_cancel, conjSubgroup_inv_conj_cancel] at h'

theorem isRootType_conjSubgroup_iff_t77 {p : ℕ} (A : Subgroup G) (g : G) :
    IsRootType p (conjSubgroup g A) ↔ IsRootType p A := by
  have h := isRootTypeIn_conjSubgroup_iff_t77 (p := p) (H := ⊤) (A := A) g
  rw [conjSubgroup_top_t77] at h
  exact h

theorem isPGroup_maximal_conj_t77 (g : G) (S : Subgroup G) (hS : IsPGroup 2 S) (N : Subgroup G)
    (hmax : ∀ T : Subgroup G, IsPGroup 2 T → T ≤ N → S ≤ T → T = S) :
    IsPGroup 2 (conjSubgroup g S) ∧
      ∀ T : Subgroup G, IsPGroup 2 T → T ≤ conjSubgroup g N → conjSubgroup g S ≤ T →
        T = conjSubgroup g S := by
  refine ⟨isPGroup_conj_map_t77 hS g, fun T hT hTN hST => ?_⟩
  have hTN' : conjSubgroup g⁻¹ T ≤ N := by
    have h1 := (conjSubgroup_le_conj_iff g⁻¹).2 hTN
    rwa [conjSubgroup_inv_conj_cancel] at h1
  have hST' : S ≤ conjSubgroup g⁻¹ T := by
    have h1 := (conjSubgroup_le_conj_iff g⁻¹).2 hST
    rwa [conjSubgroup_inv_conj_cancel] at h1
  have e := hmax _ (isPGroup_conj_map_t77 hT g⁻¹) hTN' hST'
  rw [← conjSubgroup_conj_inv_cancel g T, e]

theorem orderOf_conjugate_t77 (g y : G) : orderOf (g * y * g⁻¹) = orderOf y :=
  orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective y

theorem mem_conjSubgroup_conj_t77 (g y : G) (T : Subgroup G) :
    g * y * g⁻¹ ∈ conjSubgroup g T ↔ y ∈ T := by
  rw [mem_conjSubgroup, show g⁻¹ * (g * y * g⁻¹) * g = y by group]

theorem mem_conjSubgroup_exists_t77 (g : G) (T : Subgroup G) (x : G) :
    x ∈ conjSubgroup g T ↔ ∃ y ∈ T, g * y * g⁻¹ = x :=
  Subgroup.mem_map

theorem conj_eq_one_iff_t77 (g x : G) : g * x * g⁻¹ = 1 ↔ x = 1 := by
  constructor
  · intro e
    calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
      _ = 1 := by rw [e]; group
  · intro e
    rw [e]
    group

theorem conj_mul_comm_t77 (g x y : G) :
    g * x * g⁻¹ * (g * y * g⁻¹) = g * y * g⁻¹ * (g * x * g⁻¹) ↔ x * y = y * x := by
  constructor
  · intro h
    calc x * y = g⁻¹ * (g * x * g⁻¹ * (g * y * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * y * g⁻¹ * (g * x * g⁻¹)) * g := by rw [h]
      _ = y * x := by group
  · intro h
    calc g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ := by group
      _ = g * (y * x) * g⁻¹ := by rw [h]
      _ = g * y * g⁻¹ * (g * x * g⁻¹) := by group

theorem mem_map_subtype_center_t77 (H : Subgroup G) (x : G) :
    x ∈ (Subgroup.center H).map H.subtype ↔ x ∈ H ∧ ∀ y ∈ H, x * y = y * x := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z.2, fun y hy => ?_⟩
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨y, hy⟩)).symm
  · rintro ⟨hx, hcomm⟩
    exact Subgroup.mem_map.mpr ⟨⟨x, hx⟩, Subgroup.mem_center_iff.mpr fun g =>
      Subtype.ext (hcomm g.1 g.2).symm, rfl⟩

theorem elementaryAbelianTIRootCentralizerHypothesis_conj_t77 {A : Subgroup G}
    (h : ElementaryAbelianTIRootCentralizerHypothesis A) (g : G) :
    ElementaryAbelianTIRootCentralizerHypothesis (conjSubgroup g A) where
  elemAbelian := isElemAbelian_conj h.elemAbelian g
  ti := isTI_conjSubgroup h.ti g
  sylow := by
    obtain ⟨S, hS, hmax, hle⟩ := h.sylow
    obtain ⟨hS', hmax'⟩ :=
      isPGroup_maximal_conj_t77 g S hS ⊤ (fun T hT _ hST => hmax T hT hST)
    refine ⟨conjSubgroup g S, hS', ?_, ?_⟩
    · intro T hT hST
      exact hmax' T hT (by rw [conjSubgroup_top_t77]; exact le_top) hST
    · rw [← conjSubgroup_map_normalizer]
      exact (conjSubgroup_le_conj_iff g).2 hle
  rootTypeInCentralizer := fun k hk => by
    rw [conjSubgroup_conj_twist g k A, centralizer_conjSubgroup_eq] at hk ⊢
    exact isRootTypeIn_conjSubgroup_t77 g
      (h.rootTypeInCentralizer _ ((conjSubgroup_le_conj_iff g).1 hk))

theorem section3_A0_conj (A Abar : Subgroup G) (g : G) :
    Section3.A0 (conjSubgroup g A) (conjSubgroup g Abar) =
      conjSubgroup g (Section3.A0 A Abar) := by
  unfold Section3.A0
  exact normalizerIn_conjSubgroup_t77 g A Abar

theorem section3_Abar0_conj (A Abar : Subgroup G) (g : G) :
    Section3.Abar0 (conjSubgroup g A) (conjSubgroup g Abar) =
      conjSubgroup g (Section3.Abar0 A Abar) := by
  unfold Section3.Abar0
  exact normalizerIn_conjSubgroup_t77 g Abar A

theorem section3_q_conj (A Abar : Subgroup G) (g : G) :
    Section3.q (conjSubgroup g A) (conjSubgroup g Abar) = Section3.q A Abar := by
  unfold Section3.q
  rw [section3_Abar0_conj, relIndex_conjSubgroup_t77]

theorem section5_H_conj (A Abar : Subgroup G) (g : G) :
    Section5.H (conjSubgroup g A) (conjSubgroup g Abar) = conjSubgroup g (Section5.H A Abar) := by
  unfold Section5.H
  rw [section3_A0_conj, ← conjSubgroup_map_normalizer, weakClosure_conjSubgroup_t77]

theorem notation_conj_t77 {A Abar S₀ B : Subgroup G} (h : Section3.Notation A Abar S₀ B)
    (g : G) :
    Section3.Notation (conjSubgroup g A) (conjSubgroup g Abar) (conjSubgroup g S₀)
      (conjSubgroup g B) := by
  obtain ⟨hch, hsyl, hcont, hconj, hne, hle⟩ := h
  have choice : Section3.IsChoice (conjSubgroup g A) (conjSubgroup g Abar) := by
    unfold Section3.IsChoice at hch ⊢
    obtain ⟨⟨g0, hg0⟩, ⟨hA0, hA1⟩, hmax⟩ := hch
    refine ⟨⟨g * g0 * g⁻¹, ?_⟩, ⟨?_, ?_⟩, ?_⟩
    · rw [conjSubgroup_conj_twist g (g * g0 * g⁻¹) A,
        show g⁻¹ * (g * g0 * g⁻¹) * g = g0 by group, hg0]
    · rw [normalizerIn_conjSubgroup_t77]
      exact fun e => hA0 ((conjSubgroup_eq_bot_t77 g _).1 e)
    · rw [normalizerIn_conjSubgroup_t77]
      exact fun e => hA1 (conjSubgroup_inj_t77 g e)
    · intro g' hg'
      have e := conjSubgroup_conj_twist g g' A
      rw [e] at hg' ⊢
      rw [normalizerIn_conjSubgroup_t77] at hg'
      obtain ⟨hg'0, hg'1⟩ := hg'
      have hX0 : normalizerIn (conjSubgroup (g⁻¹ * g' * g) A) A ≠ ⊥ := fun h0 =>
        hg'0 (by rw [h0, conjSubgroup_bot_t77])
      have hX1 : normalizerIn (conjSubgroup (g⁻¹ * g' * g) A) A ≠
          conjSubgroup (g⁻¹ * g' * g) A :=
        fun h1 => hg'1 (by rw [h1])
      have hc := hmax (g⁻¹ * g' * g) ⟨hX0, hX1⟩
      rw [normalizerIn_conjSubgroup_t77, normalizerIn_conjSubgroup_t77, card_conjSubgroup,
        card_conjSubgroup]
      exact hc
  have sylow : IsPGroup 2 (conjSubgroup g S₀) ∧
      conjSubgroup g S₀ ≤ Subgroup.normalizer (conjSubgroup g A : Set G) ∧
      ∀ T : Subgroup G, IsPGroup 2 T → T ≤ Subgroup.normalizer (conjSubgroup g A : Set G) →
        conjSubgroup g S₀ ≤ T → T = conjSubgroup g S₀ := by
    obtain ⟨hS0, hN, hmaxS⟩ := hsyl
    obtain ⟨h1, h2⟩ := isPGroup_maximal_conj_t77 g S₀ hS0 (Subgroup.normalizer (A : Set G)) hmaxS
    refine ⟨h1, ?_, ?_⟩
    · rw [← conjSubgroup_map_normalizer]
      exact (conjSubgroup_le_conj_iff g).2 hN
    · intro T hT hTN hST
      rw [← conjSubgroup_map_normalizer] at hTN
      exact h2 T hT hTN hST
  have contains : conjSubgroup g A ⊔ Section3.Abar0 (conjSubgroup g A) (conjSubgroup g Abar) ≤
      conjSubgroup g S₀ := by
    rw [section3_Abar0_conj, ← conjSubgroup_sup_t77]
    exact (conjSubgroup_le_conj_iff g).2 hcont
  have hconj' : ∃ g' : G, conjSubgroup g B = conjSubgroup g' (conjSubgroup g A) := by
    obtain ⟨g0, hg0⟩ := hconj
    refine ⟨g * g0 * g⁻¹, ?_⟩
    rw [hg0, conjSubgroup_conj_twist g (g * g0 * g⁻¹) A,
      show g⁻¹ * (g * g0 * g⁻¹) * g = g0 by group]
  have hne' : conjSubgroup g B ≠ conjSubgroup g A := fun e => hne (conjSubgroup_inj_t77 g e)
  have hle' : conjSubgroup g B ≤ conjSubgroup g S₀ ⊓ centralizer (conjSubgroup g A : Set G) := by
    rw [centralizer_conjSubgroup_eq, ← conjSubgroup_inf]
    exact (conjSubgroup_le_conj_iff g).2 hle
  exact ⟨choice, sylow, contains, hconj', hne', hle'⟩

theorem sec4A0LeCenterH_iff_forall_t77 (A Abar : Subgroup G) :
    Sec4A0LeCenterH A Abar ↔ ∀ x ∈ Section3.A0 A Abar,
      x ∈ Section5.H A Abar ∧ ∀ y ∈ Section5.H A Abar, x * y = y * x := by
  unfold Sec4A0LeCenterH
  exact ⟨fun h x hx => (mem_map_subtype_center_t77 _ x).1 (h hx),
    fun h x hx => (mem_map_subtype_center_t77 _ x).2 (h x hx)⟩

theorem sec4A0LeCenterH_conj_iff (A Abar : Subgroup G) (g : G) :
    Sec4A0LeCenterH (conjSubgroup g A) (conjSubgroup g Abar) ↔ Sec4A0LeCenterH A Abar := by
  rw [sec4A0LeCenterH_iff_forall_t77, sec4A0LeCenterH_iff_forall_t77, section3_A0_conj,
    section5_H_conj]
  constructor
  · intro h x hx
    have hz := h (g * x * g⁻¹) ((mem_conjSubgroup_conj_t77 g x _).2 hx)
    refine ⟨(mem_conjSubgroup_conj_t77 g x _).1 hz.1, fun y hy => ?_⟩
    have hc := hz.2 (g * y * g⁻¹) ((mem_conjSubgroup_conj_t77 g y _).2 hy)
    exact (conj_mul_comm_t77 g x y).1 hc
  · intro h z hz
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hz
    obtain ⟨hxH, hcomm⟩ := h x hx
    refine ⟨(mem_conjSubgroup_conj_t77 g x _).2 hxH, fun y' hy' => ?_⟩
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hy'
    exact (conj_mul_comm_t77 g x y).2 (hcomm y hy)

namespace Sec3Ctx

theorem conj {A Abar S₀ B : Subgroup G} (h : Sec3Ctx A Abar S₀ B) (g : G) :
    Sec3Ctx (conjSubgroup g A) (conjSubgroup g Abar) (conjSubgroup g S₀)
      (conjSubgroup g B) where
  hyp := elementaryAbelianTIRootCentralizerHypothesis_conj_t77 h.hyp g
  not_root := fun hr => h.not_root ((isRootType_conjSubgroup_iff_t77 A g).1 hr)
  not_wc := by
    intro hall
    apply h.not_wc
    intro k hk
    have e := hall (g * k * g⁻¹) (by
      rw [conjSubgroup_conj_twist g (g * k * g⁻¹) A,
        show g⁻¹ * (g * k * g⁻¹) * g = k by group, centralizer_conjSubgroup_eq]
      exact (conjSubgroup_le_conj_iff g).2 hk)
    rw [conjSubgroup_conj_twist g (g * k * g⁻¹) A,
      show g⁻¹ * (g * k * g⁻¹) * g = k by group] at e
    exact conjSubgroup_inj_t77 g e
  nota := notation_conj_t77 h.nota g

end Sec3Ctx

end CFSG.RankThree.GF2n.Tim77
