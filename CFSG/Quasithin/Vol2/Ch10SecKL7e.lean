module

public import CFSG.Quasithin.Vol2.Ch10SecKL7d

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.KL7

open CFSG.Quasithin CFSG.Assembly.LowTwoRank

variable {W : Type} [CommGroup W]

theorem mem_map_conj_iff {x y : MulAut W} {L : Subgroup (MulAut W)} :
    y ∈ L.map (MulAut.conj x).toMonoidHom ↔ x⁻¹ * y * x ∈ L := by
  constructor
  · rintro ⟨l, hl, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hl
  · intro hy
    refine ⟨x⁻¹ * y * x, hy, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

theorem mem_normalizer_iff_map {x : MulAut W} {L : Subgroup (MulAut W)} :
    x ∈ Subgroup.normalizer (L : Set (MulAut W)) ↔ L.map (MulAut.conj x).toMonoidHom = L := by
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · intro hx
    ext y
    rw [mem_map_conj_iff, hx (x⁻¹ * y * x)]
    simp [mul_assoc]
  · intro hx y
    constructor
    · intro hy
      rw [← hx]
      exact ⟨y, hy, rfl⟩
    · intro hy
      rw [← hx] at hy
      obtain ⟨l, hl, hle⟩ := hy
      have hly : l = y := (MulAut.conj x).injective hle
      rw [← hly]
      exact hl

theorem conj_apply_eq {x y : MulAut W} (w : W) : y (x w) = x ((x⁻¹ * y * x) w) := by
  simp [MulAut.mul_apply]

namespace Coord

variable {L : Subgroup (MulAut W)} {U : Subgroup W} (c : Coord L U)

include c in
theorem eq_one_of_central {a : MulAut W} (ha : a ∈ L) (h : ∀ l ∈ L, a * l = l * a) : a = 1 := by
  have hγ := eq_one_of_commute_all (c.π.symm ⟨a, ha⟩) fun δ => by
    apply c.π.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact Subtype.ext (h _ (c.π δ).2)
  have := congrArg (fun γ => ((c.π γ : ↥L) : MulAut W)) hγ
  simpa using this

include c in
theorem card_L : Nat.card L = 168 := by
  rw [← Nat.card_congr c.π.toEquiv, card_SL32]

include c in
theorem isSimpleGroup_L : IsSimpleGroup ↥L := by
  have := isSimpleGroup_SL32
  exact c.π.symm.isSimpleGroup

end Coord

namespace Hyp

variable {Mb L₁ L₂ : Subgroup (MulAut W)} {W₁ W₂ : Subgroup W} {τ : MulAut W}
variable (h : Hyp Mb L₁ L₂ W₁ W₂ τ)
include h

theorem comm' {a b : MulAut W} (ha : a ∈ L₁) (hb : b ∈ L₂) : a * b = b * a :=
  Subgroup.mem_centralizer_iff.1 (h.comm hb) a ha

theorem mem_sup_iff {y : MulAut W} : y ∈ L₁ ⊔ L₂ ↔ ∃ a ∈ L₁, ∃ b ∈ L₂, a * b = y := by
  constructor
  · intro hy
    have hcomm : ∀ (a : ↥L₁) (b : ↥L₂), Commute (L₁.subtype a) (L₂.subtype b) :=
      fun a b => h.comm' a.2 b.2
    have hr : (L₁.subtype.noncommCoprod L₂.subtype hcomm).range = L₁ ⊔ L₂ := by
      rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
    rw [← hr] at hy
    obtain ⟨⟨a, b⟩, rfl⟩ := hy
    exact ⟨a, a.2, b, b.2, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hb)

theorem conj_mem_L₁ {y l : MulAut W} (hy : y ∈ L₁ ⊔ L₂) (hl : l ∈ L₁) : y * l * y⁻¹ ∈ L₁ := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (h.mem_sup_iff).1 hy
  have : a * b * l * (a * b)⁻¹ = a * l * a⁻¹ := by
    calc a * b * l * (a * b)⁻¹ = a * (b * l) * b⁻¹ * a⁻¹ := by group
      _ = a * (l * b) * b⁻¹ * a⁻¹ := by rw [h.comm' hl hb]
      _ = a * l * a⁻¹ := by group
  rw [this]
  exact mul_mem (mul_mem ha hl) (inv_mem ha)

theorem mem_L₂_of_comm {y : MulAut W} (hy : y ∈ L₁ ⊔ L₂) (hc : ∀ l ∈ L₁, y * l = l * y) :
    y ∈ L₂ := by
  obtain ⟨c⟩ := h.coord
  obtain ⟨a, ha, b, hb, rfl⟩ := (h.mem_sup_iff).1 hy
  have ha1 : a = 1 := c.eq_one_of_central ha fun l hl => by
    have h1 := hc l hl
    have h2 : a * l * b = l * a * b := by
      calc a * l * b = a * (l * b) := by group
        _ = a * (b * l) := by rw [h.comm' hl hb]
        _ = a * b * l := by group
        _ = l * (a * b) := h1
        _ = l * a * b := by group
    exact mul_right_cancel h2
  rw [ha1, one_mul]
  exact hb

theorem ne_L : L₁ ≠ L₂ := by
  intro heq
  obtain ⟨c⟩ := h.coord
  have h0 : L₁ = ⊥ := by rw [← h.inf_L, ← heq, inf_idem]
  have hc := c.card_L
  rw [h0, Subgroup.card_bot] at hc
  norm_num at hc

theorem card_L₂ : Nat.card L₂ = Nat.card L₁ := by
  rw [← h.mapL]
  exact Subgroup.card_map_of_injective (MulAut.conj τ).injective

theorem map_conj_eq {x : MulAut W} (hx : x ∈ Mb) :
    L₁.map (MulAut.conj x).toMonoidHom = L₁ ∨ L₁.map (MulAut.conj x).toMonoidHom = L₂ := by
  obtain ⟨c⟩ := h.coord
  have : Finite ↥L₁ := Nat.finite_of_card_ne_zero (by rw [c.card_L]; norm_num)
  have : Finite ↥L₂ := Nat.finite_of_card_ne_zero (by rw [h.card_L₂, c.card_L]; norm_num)
  set N := L₁.map (MulAut.conj x).toMonoidHom with hN
  have hxn := h.norm hx
  have hxn' := inv_mem hxn
  have hNsup : N ≤ L₁ ⊔ L₂ := by
    rintro _ ⟨l, hl, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 hxn l).1 (Subgroup.mem_sup_left hl)
  have hNnorm : ∀ y ∈ L₁ ⊔ L₂, ∀ n ∈ N, y * n * y⁻¹ ∈ N := by
    intro y hy n hn
    rw [hN, mem_map_conj_iff] at hn ⊢
    have hy' : x⁻¹ * y * x⁻¹⁻¹ ∈ L₁ ⊔ L₂ := (Subgroup.mem_normalizer_iff.1 hxn' y).1 hy
    have := h.conj_mem_L₁ hy' hn
    convert this using 1
    group
  have hcardN : Nat.card N = Nat.card L₁ :=
    Subgroup.card_map_of_injective (MulAut.conj x).injective
  have hNs : IsSimpleGroup ↥N := by
    have := c.isSimpleGroup_L
    exact (MulEquiv.subgroupMap (MulAut.conj x) L₁).symm.isSimpleGroup
  have hnormal : ((N ⊓ L₁).subgroupOf N).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).2 fun n hn => ?_
    rw [Subgroup.mem_normalizer_iff]
    intro m
    constructor
    · rintro ⟨hm1, hm2⟩
      exact ⟨mul_mem (mul_mem hn hm1) (N.inv_mem hn), h.conj_mem_L₁ (hNsup hn) hm2⟩
    · rintro ⟨hm1, hm2⟩
      refine ⟨?_, ?_⟩
      · have := mul_mem (mul_mem (N.inv_mem hn) hm1) hn
        simpa [mul_assoc] using this
      · have := h.conj_mem_L₁ ((L₁ ⊔ L₂).inv_mem (hNsup hn)) hm2
        simpa [mul_assoc] using this
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N ⊓ L₁).subgroupOf N) with hb | ht
  · right
    have hdisj : N ⊓ L₁ = ⊥ := by
      rw [Subgroup.subgroupOf_eq_bot] at hb
      exact eq_bot_iff.2 fun g hg => (Subgroup.disjoint_def.1 hb) hg hg.1
    have hle : N ≤ L₂ := fun n hn => h.mem_L₂_of_comm (hNsup hn) fun l hl => by
      have hcomm : n * l * n⁻¹ * l⁻¹ ∈ N ⊓ L₁ := by
        refine ⟨?_, mul_mem (h.conj_mem_L₁ (hNsup hn) hl) (L₁.inv_mem hl)⟩
        have := hNnorm l (Subgroup.mem_sup_left hl) _ (N.inv_mem hn)
        rw [show n * l * n⁻¹ * l⁻¹ = n * (l * n⁻¹ * l⁻¹) by group]
        exact mul_mem hn this
      rw [hdisj, Subgroup.mem_bot] at hcomm
      calc n * l = n * l * n⁻¹ * l⁻¹ * (l * n) := by group
        _ = l * n := by rw [hcomm, one_mul]
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcardN, h.card_L₂])
  · left
    have hle : N ≤ L₁ := by
      rw [Subgroup.subgroupOf_eq_top] at ht
      exact fun n hn => (ht hn).2
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcardN])

theorem map_conj_L₂_of {x : MulAut W} (hx : x ∈ Mb) (h1 : L₁.map (MulAut.conj x).toMonoidHom = L₁) :
    L₂.map (MulAut.conj x).toMonoidHom = L₂ := by
  rcases h.swap.map_conj_eq hx with h2 | h2
  · exact h2
  · exact absurd (Subgroup.map_injective (MulAut.conj x).injective (h1.trans h2.symm)) h.ne_L

theorem map_conj_L₂_of' {x : MulAut W} (hx : x ∈ Mb)
    (h1 : L₁.map (MulAut.conj x).toMonoidHom = L₂) : L₂.map (MulAut.conj x).toMonoidHom = L₁ := by
  rcases h.swap.map_conj_eq hx with h2 | h2
  · exact absurd (Subgroup.map_injective (MulAut.conj x).injective (h1.trans h2.symm)) h.ne_L
  · exact h2

theorem map_mem_W₁ {x : MulAut W} (hx : x ∈ Mb) (h1 : L₁.map (MulAut.conj x).toMonoidHom = L₁)
    {w : W} (hw : w ∈ W₁) : x w ∈ W₁ := by
  rw [h.mem_W₁_iff] at hw ⊢
  intro y hy
  have hy' : x⁻¹ * y * x ∈ L₂ := mem_map_conj_iff.1 ((h.map_conj_L₂_of hx h1).symm ▸ hy)
  rw [conj_apply_eq, hw _ hy']

theorem map_mem_W₂ {x : MulAut W} (hx : x ∈ Mb) (h1 : L₁.map (MulAut.conj x).toMonoidHom = L₁)
    {w : W} (hw : w ∈ W₂) : x w ∈ W₂ :=
  h.swap.map_mem_W₁ hx (h.map_conj_L₂_of hx h1) hw

theorem map_mem_W₂_of_swap {x : MulAut W} (hx : x ∈ Mb)
    (h1 : L₁.map (MulAut.conj x).toMonoidHom = L₂) {w : W} (hw : w ∈ W₁) : x w ∈ W₂ := by
  rw [h.mem_W₂_iff]
  intro y hy
  have hy' : x⁻¹ * y * x ∈ L₂ := mem_map_conj_iff.1 ((h.map_conj_L₂_of' hx h1).symm ▸ hy)
  rw [conj_apply_eq, h.fix₂ _ hy' w hw]

end Hyp

end CFSG.Quasithin.Vol2.Ch10.SecB.KL7
