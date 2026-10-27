module

public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalTransfer

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.LieType.BorelTits
open scoped commutatorElement

namespace GGOppRad

section Ascent

variable {H : Type*} [Group H] [Finite H] {G : Type*} [Group G] [Finite G] (ψ : H →* G)

theorem liftTwo_map_conj (hker : ψ.ker ≤ Subgroup.center H)
    (hinv : ∀ z ∈ ψ.ker, z ^ 2 = 1 → z = 1) {W : Subgroup G} (hW : IsPGroup 2 W)
    (hWr : W ≤ ψ.range) (u : H) :
    liftTwo ψ (W.map (MulAut.conj (ψ u)).toMonoidHom) =
      (liftTwo ψ W).map (MulAut.conj u).toMonoidHom := by
  have h2 : IsPGroup 2 ((liftTwo ψ W).map (MulAut.conj u).toMonoidHom) :=
    (isPGroup_liftTwo ψ W).map _
  rw [← liftTwo_map ψ hker hinv h2, map_map_conj, map_liftTwo ψ hker hW hWr]

omit [Finite H] in
theorem commutatorElement_mul_mul_center (a b : H) {z w : H} (hz : z ∈ Subgroup.center H)
    (hw : w ∈ Subgroup.center H) : ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
  have h1 : ∀ g, z * g * z⁻¹ = g := fun g => by
    rw [← Subgroup.mem_center_iff.1 hz g, mul_inv_cancel_right]
  have h2 : ∀ g, w * g * w⁻¹ = g := fun g => by
    rw [← Subgroup.mem_center_iff.1 hw g, mul_inv_cancel_right]
  calc ⁅a * z, b * w⁆ = a * (z * (b * w) * z⁻¹) * a⁻¹ * (b * w)⁻¹ := by
        rw [commutatorElement_def]; group
    _ = a * b * (w * a⁻¹ * w⁻¹) * b⁻¹ := by rw [h1]; group
    _ = ⁅a, b⁆ := by rw [h2, commutatorElement_def]

omit [Finite H] in
theorem eq_top_of_sup_eq_top_of_le_center (hperf : commutator H = ⊤) {A Z : Subgroup H}
    (hZ : Z ≤ Subgroup.center H) (h : A ⊔ Z = ⊤) : A = ⊤ := by
  have hZn : Z.Normal := ⟨fun z hz g => by
    rw [Subgroup.mem_center_iff.1 (hZ hz) g, mul_inv_cancel_right]
    exact hz⟩
  have hmul : ∀ x : H, ∃ a ∈ A, ∃ z ∈ Z, a * z = x := by
    intro x
    have hx : x ∈ ((A ⊔ Z : Subgroup H) : Set H) := by rw [h]; exact Subgroup.mem_top x
    rw [Subgroup.mul_normal] at hx
    obtain ⟨a, ha, z, hz, e⟩ := hx
    exact ⟨a, ha, z, hz, e⟩
  rw [eq_top_iff, ← hperf, commutator_def, Subgroup.commutator_le]
  intro x _ y _
  obtain ⟨a, ha, z, hz, rfl⟩ := hmul x
  obtain ⟨b, hb, w, hw, rfl⟩ := hmul y
  rw [commutatorElement_mul_mul_center a b (hZ hz) (hZ hw)]
  rw [commutatorElement_def]
  exact A.mul_mem (A.mul_mem (A.mul_mem ha hb) (A.inv_mem ha)) (A.inv_mem hb)

theorem GGOppRadGood.of_map (hker : ψ.ker ≤ Subgroup.center H)
    (hinv : ∀ z ∈ ψ.ker, z ^ 2 = 1 → z = 1)
    (hgen : ∀ A : Subgroup H, A ⊔ ψ.ker = ⊤ → A = ⊤)
    {Q : Subgroup H} (hQ : GGRadicalTwo ⊤ Q) (h : GGOppRadGood ψ.range (Q.map ψ)) :
    GGOppRadGood ⊤ Q := by
  have hQ2 : IsPGroup 2 Q := hQ.isPGroup
  have hLQ : liftTwo ψ (Q.map ψ) = Q := liftTwo_map ψ hker hinv hQ2
  have hX2 : IsPGroup 2 (Q.map ψ) := hQ2.map ψ
  have hXr : Q.map ψ ≤ ψ.range := Subgroup.map_le_range ψ Q
  have hN := normalizer_liftTwo ψ hker hX2 hXr
  rw [hLQ] at hN
  obtain ⟨W₀, hW₀, hgen₀, hconj⟩ := h
  have hW₀2 : IsPGroup 2 W₀ := hW₀.1.isPGroup
  have hW₀r : W₀ ≤ ψ.range := hW₀.1.le
  have hLW₀ : (liftTwo ψ W₀).map ψ = W₀ := map_liftTwo ψ hker hW₀2 hW₀r
  refine ⟨liftTwo ψ W₀, ⟨radicalTwo_liftTwo ψ hker hW₀.1, ?_, ?_⟩, ?_, fun V hV => ?_⟩
  · rw [← card_map_eq ψ hinv (isPGroup_liftTwo ψ W₀), hLW₀, hW₀.2.1, card_map_eq ψ hinv hQ2]
  · rw [hN]
    have hZ2 : IsPGroup 2 ((liftTwo ψ W₀ ⊓
        (ψ.range ⊓ Subgroup.normalizer ((Q.map ψ : Subgroup G) : Set G)).comap ψ :
          Subgroup H)) :=
      (isPGroup_liftTwo ψ W₀).to_le inf_le_left
    have hZmap : (liftTwo ψ W₀ ⊓ (ψ.range ⊓
        Subgroup.normalizer ((Q.map ψ : Subgroup G) : Set G)).comap ψ).map ψ ≤
        W₀ ⊓ (ψ.range ⊓ Subgroup.normalizer ((Q.map ψ : Subgroup G) : Set G)) :=
      le_inf ((Subgroup.map_mono inf_le_left).trans hLW₀.le)
        (Subgroup.map_le_iff_le_comap.mpr inf_le_right)
    rw [hW₀.2.2, le_bot_iff, Subgroup.map_eq_bot_iff] at hZmap
    have := ker_inf_eq_bot ψ hinv hZ2
    rwa [inf_eq_right.mpr hZmap] at this
  · apply hgen
    have hmap : (Q ⊔ liftTwo ψ W₀).map ψ = ψ.range := by
      rw [Subgroup.map_sup, hLW₀, hgen₀]
    rw [← Subgroup.comap_map_eq, hmap]
    exact eq_top_iff.mpr fun x _ => Subgroup.mem_comap.mpr (MonoidHom.mem_range.mpr ⟨x, rfl⟩)
  · have hV2 : IsPGroup 2 V := hV.1.isPGroup
    have hLV : liftTwo ψ (V.map ψ) = V := liftTwo_map ψ hker hinv hV2
    have hVmem : V.map ψ ∈ ggOppositeRadicals ψ.range (Q.map ψ) := by
      refine ⟨radicalTwo_of_liftTwo ψ hker (hV2.map ψ) (Subgroup.map_le_range ψ V)
        (by rw [hLV]; exact hV.1), ?_, ?_⟩
      · rw [card_map_eq ψ hinv hV2, hV.2.1, card_map_eq ψ hinv hQ2]
      · refine eq_bot_iff.mpr fun y hy => ?_
        obtain ⟨hyV, hyN⟩ := Subgroup.mem_inf.mp hy
        obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hyV
        have hv' : v ∈ V ⊓ ((⊤ : Subgroup H) ⊓ Subgroup.normalizer (Q : Set H)) := by
          refine Subgroup.mem_inf.mpr ⟨hv, ?_⟩
          rw [hN]
          exact hyN
        rw [hV.2.2, Subgroup.mem_bot] at hv'
        rw [hv', map_one]
        exact Subgroup.one_mem _
    obtain ⟨x, hx, hxV⟩ := hconj _ hVmem
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
    refine ⟨u, hu, ?_⟩
    rw [← hLV, hxV, liftTwo_map_conj ψ hker hinv hW₀2 hW₀r u]

theorem GGOppRadGood.of_map_perfect (hperf : commutator H = ⊤)
    (hker : ψ.ker ≤ Subgroup.center H) (hinv : ∀ z ∈ ψ.ker, z ^ 2 = 1 → z = 1)
    {Q : Subgroup H} (hQ : GGRadicalTwo ⊤ Q) (h : GGOppRadGood ψ.range (Q.map ψ)) :
    GGOppRadGood ⊤ Q :=
  GGOppRadGood.of_map ψ hker hinv (fun _ hA => eq_top_of_sup_eq_top_of_le_center hperf hker hA)
    hQ h

theorem radicalTwo_map (hker : ψ.ker ≤ Subgroup.center H)
    (hinv : ∀ z ∈ ψ.ker, z ^ 2 = 1 → z = 1) {Q : Subgroup H} (hQ : GGRadicalTwo ⊤ Q) :
    GGRadicalTwo ψ.range (Q.map ψ) :=
  radicalTwo_of_liftTwo ψ hker (hQ.isPGroup.map ψ) (Subgroup.map_le_range ψ Q)
    (by rw [liftTwo_map ψ hker hinv hQ.isPGroup]; exact hQ)

end Ascent

end GGOppRad

end CFSG.StandardType
