module

public import CFSG.Quasithin.Vol2.Ch10SecQ9H39
public import CFSG.Quasithin.Vol2.Ch10SecQ9H40

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open Matrix

@[expose] def actQ1 {X : Subgroup (Matrix.SpecialLinearGroup (Fin (1 + 4)) (ZMod 2))}
    (hX1 : X ≤ stabStd 1 4) : ↥X →* Matrix.SpecialLinearGroup (Fin (3 + 1)) (ZMod 2) :=
  (botH 1 4).comp (Subgroup.inclusion hX1)

theorem actQ1_apply {X : Subgroup (Matrix.SpecialLinearGroup (Fin (1 + 4)) (ZMod 2))}
    (hX1 : X ≤ stabStd 1 4) (x : ↥X) : actQ1 hX1 x = botH 1 4 ⟨x.1, hX1 x.2⟩ := rfl

theorem botH_mem_stabStd31 {g : Matrix.SpecialLinearGroup (Fin (1 + 4)) (ZMod 2)}
    (hg : g ∈ stabStd 1 4) (h4 : ∀ v ∈ stdE (1 + 4) 4, g • v ∈ stdE (1 + 4) 4) :
    botH 1 4 ⟨g, hg⟩ ∈ stabStd 3 1 := by
  rw [mem_stabStd]
  intro i j
  have hc : Pi.single (Fin.natAdd 1 (Fin.castAdd 1 j)) (1 : ZMod 2) ∈ stdE (1 + 4) 4 :=
    single_mem_stdE (by simp; omega)
  have h := h4 _ hc (Fin.natAdd 1 (Fin.natAdd 3 i)) (by simp)
  rw [smul_eq_mulVec', mulVec_single_one] at h
  exact h

theorem mem_range_actQ1 {X : Subgroup (Matrix.SpecialLinearGroup (Fin (1 + 4)) (ZMod 2))}
    (h1 : InvStd X 1) (h4 : InvStd X 4) (hcard : Nat.card X = Nat.card (o2G X) * 168)
    (hU : uniSL (1 + 4) ≤ Subgroup.normalizer
      (X : Set (Matrix.SpecialLinearGroup (Fin (1 + 4)) (ZMod 2))))
    {g : Matrix.SpecialLinearGroup (Fin (3 + 1)) (ZMod 2)} (hg : g ∈ stabStd 3 1) :
    g ∈ (actQ1 (le_stabStd_of_invStd h1)).range := by
  set hX1 : X ≤ stabStd 1 4 := le_stabStd_of_invStd h1
  set φ := actQ1 hX1
  have hφS : ∀ x : ↥X, φ x ∈ stabStd 3 1 := fun x =>
    botH_mem_stabStd31 (hX1 x.2) (h4 x.1 x.2)
  have hX' : φ.range ≤ stabStd 3 1 := by
    rintro _ ⟨x, rfl⟩
    exact hφS x
  obtain ⟨φ₃, hφ₃⟩ : ∃ φ₃ : ↥X →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
      φ₃ = (topH 3 1).comp (φ.codRestrict (stabStd 3 1) hφS) := ⟨_, rfl⟩
  have hφ₃x : ∀ x : ↥X, φ₃ x = topH 3 1 ⟨φ x, hφS x⟩ := fun x => by rw [hφ₃]; rfl
  have hker : ∀ x, φ₃ x = 1 → ∃ k : ℕ, x ^ 2 ^ k = 1 := by
    intro x hx
    rw [hφ₃x] at hx
    have h2 : φ x * φ x = 1 := sq_eq_one_of_blocks (hφS x) (congrArg Subtype.val hx)
      (botB_eq_one_of_one ⟨φ x, hφS x⟩)
    have hxx : x.1 * x.1 ∈ stabStd 1 4 := hX1 (X.mul_mem x.2 x.2)
    have h3 : (x.1 * x.1) * (x.1 * x.1) = 1 := by
      refine sq_eq_one_of_blocks hxx (topB_eq_one_of_one ⟨_, hxx⟩) ?_
      have : φ (x * x) = 1 := by rw [map_mul, h2]
      exact congrArg Subtype.val this
    exact ⟨2, Subtype.ext (by rw [SubmonoidClass.coe_pow, pow_four_eq, h3, Subgroup.coe_one])⟩
  have hle : φ₃.range ≤ (φ.range.subgroupOf (stabStd 3 1)).map (topH 3 1) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨⟨φ x, hφS x⟩, Subgroup.mem_subgroupOf.mpr ⟨x, rfl⟩, (hφ₃x x).symm⟩
  have himg : (φ.range.subgroupOf (stabStd 3 1)).map (topH 3 1) = ⊤ :=
    Subgroup.eq_top_of_le_card _ (by
      rw [card_SL_three_two]
      exact (card_range_ge φ₃ hker hcard).trans (Subgroup.card_le_of_le hle))
  have hfwd : ∀ B : Matrix (Fin 3) (Fin 1) (ZMod 2), ∀ z ∈ φ.range,
      utSL B * z * (utSL B)⁻¹ ∈ φ.range := by
    rintro B _ ⟨x, rfl⟩
    have ht5 : blkSL 1 (utSL B) ∈ uniSL (1 + 4) :=
      blkSL_mem_uniSL (uniSL 1).one_mem (utSL_mem_uniSL B)
    have hxt : blkSL 1 (utSL B) * x.1 * (blkSL 1 (utSL B))⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp (hU ht5) _).mp x.2
    refine ⟨⟨_, hxt⟩, ?_⟩
    rw [actQ1_apply, actQ1_apply, show (⟨blkSL 1 (utSL B) * x.1 * (blkSL 1 (utSL B))⁻¹,
      hX1 hxt⟩ : ↥(stabStd 1 4)) = ⟨blkSL 1 (utSL B), blkSL_mem 1 (utSL B)⟩ * ⟨x.1, hX1 x.2⟩ *
        (⟨blkSL 1 (utSL B), blkSL_mem 1 (utSL B)⟩)⁻¹ from rfl, map_mul, map_mul, map_inv,
      botH_blkSL]
  have hN : ∀ B : Matrix (Fin 3) (Fin 1) (ZMod 2), utSL B ∈ Subgroup.normalizer
      (φ.range : Set (Matrix.SpecialLinearGroup (Fin (3 + 1)) (ZMod 2))) := fun B => by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    refine ⟨hfwd B z, fun hz => ?_⟩
    have := hfwd B _ hz
    rwa [utSL_inv, show utSL B * (utSL B * z * utSL B) * utSL B =
      (utSL B * utSL B) * z * (utSL B * utSL B) by group, utSL_mul_self, one_mul, mul_one] at this
  have hg7 : a7 ∈ (φ.range.subgroupOf (stabStd 3 1)).map (topH 3 1) := by rw [himg]; trivial
  obtain ⟨l, hl, hla⟩ := hg7
  have hlR : l.1 ∈ φ.range := Subgroup.mem_subgroupOf.mp hl
  have hrad : ∀ B : Matrix (Fin 3) (Fin 1) (ZMod 2), utSL B ∈ φ.range := fun B => by
    have hc := comm_utSL_mem (m := 3) (k := 1) hlR (hN (m7 * B))
    have hA : topB ((l.1 : Matrix.SpecialLinearGroup (Fin (3 + 1)) (ZMod 2)) :
        Matrix (Fin (3 + 1)) (Fin (3 + 1)) (ZMod 2)) = (a7 : Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
      congrArg Subtype.val hla
    rwa [comm_utSL_top l.2 (botB_eq_one_of_one l), hA, ← Matrix.mul_assoc, one_add_a7_mul_m7,
      Matrix.one_mul] at hc
  have hgx : topH 3 1 ⟨g, hg⟩ ∈ (φ.range.subgroupOf (stabStd 3 1)).map (topH 3 1) := by
    rw [himg]; trivial
  obtain ⟨x, hx, hxt⟩ := hgx
  have hxR : x.1 ∈ φ.range := Subgroup.mem_subgroupOf.mp hx
  obtain ⟨s, hs⟩ : ∃ s : ↥(stabStd 3 1), s = ⟨g, hg⟩ * x⁻¹ := ⟨_, rfl⟩
  have ht : topH 3 1 s = 1 := by rw [hs, map_mul, map_inv, hxt, mul_inv_cancel]
  have hsR : s.1 ∈ φ.range := by
    rw [eq_utSL_of_blocks s.2 (congrArg Subtype.val ht) (botB_eq_one_of_one s)]
    exact hrad _
  have hg' : g = s.1 * x.1 := by
    rw [hs, Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_cancel_right]
  rw [hg']
  exact φ.range.mul_mem hsR hxR

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
