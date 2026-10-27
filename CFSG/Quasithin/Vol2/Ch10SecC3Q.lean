module

public import CFSG.Quasithin.Vol2.Ch10SecC3P
public import CFSG.Quasithin.Vol2.Ch10SecC3H

public section

namespace CFSG.Quasithin.Vol2.Ch10.C3.Om

open CFSG.Quasithin CFSG.Assembly.LowTwoRank
open scoped Matrix

variable {K : Type} [Field K] [CharP K 2] [Finite K]

theorem comap_props {B : Subgroup (MulAut (WM K))} (hBi : B ≤ img K) (hB : IsElemAbelian2 B) :
    Nat.card B = Nat.card (B.comap (rho K)) ∧
      (∀ x ∈ B.comap (rho K), x * x = 1) ∧
      Nat.card ((B.comap (rho K)).map (MonoidHom.fst (SL K) (SL K))) ≤ Nat.card K ∧
      Nat.card ((B.comap (rho K)).map (MonoidHom.snd (SL K) (SL K))) ≤ Nat.card K := by
  have hcard : Nat.card B = Nat.card (B.comap (rho K)) := by
    have hm := Subgroup.map_comap_eq_self (f := rho K) hBi
    calc Nat.card B = Nat.card ((B.comap (rho K)).map (rho K)) := by rw [hm]
      _ = Nat.card (B.comap (rho K)) := Subgroup.card_map_of_injective rho_injective
  have h2 : ∀ x ∈ B.comap (rho K), x * x = 1 := fun x hx =>
    rho_injective (by rw [map_mul, map_one, ← sq]; exact hB.2 _ hx)
  refine ⟨hcard, h2, card_le_of_sq_eq_one ?_, card_le_of_sq_eq_one ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact congrArg Prod.fst (h2 x hx)
  · rintro _ ⟨x, hx, rfl⟩
    exact congrArg Prod.snd (h2 x hx)

theorem card_le_of_le_img {B : Subgroup (MulAut (WM K))} (hBi : B ≤ img K)
    (hB : IsElemAbelian2 B) : Nat.card B ≤ Nat.card K ^ 2 := by
  obtain ⟨hcard, -, hP₁, hP₂⟩ := comap_props hBi hB
  set B' := B.comap (rho K)
  have hle : B' ≤ (B'.map (MonoidHom.fst (SL K) (SL K))).prod
      (B'.map (MonoidHom.snd (SL K) (SL K))) := fun x hx => ⟨⟨x, hx, rfl⟩, ⟨x, hx, rfl⟩⟩
  rw [hcard, sq]
  calc Nat.card B' ≤ Nat.card ((B'.map (MonoidHom.fst (SL K) (SL K))).prod
        (B'.map (MonoidHom.snd (SL K) (SL K)))) := Subgroup.card_le_of_le hle
    _ = Nat.card (B'.map (MonoidHom.fst (SL K) (SL K))) *
        Nat.card (B'.map (MonoidHom.snd (SL K) (SL K))) := by
      rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod]
    _ ≤ Nat.card K * Nat.card K := Nat.mul_le_mul hP₁ hP₂

theorem card_mul_card_fixV_le_of_le_img {B : Subgroup (MulAut (WM K))} (hBi : B ≤ img K)
    (hB : IsElemAbelian2 B) (hne : B ≠ ⊥) :
    Nat.card B * Nat.card ↥(fixV B) ≤ Nat.card K ^ 3 := by
  obtain ⟨hcard, h2, hP₁, hP₂⟩ := comap_props hBi hB
  set B' := B.comap (rho K) with hB'
  by_cases hb : (∃ c : SL K, c ≠ 1 ∧ (c, 1) ∈ B') ∧ ∃ d : SL K, d ≠ 1 ∧ ((1 : SL K), d) ∈ B'
  · obtain ⟨⟨c, hc1, hcB⟩, d, hd1, hdB⟩ := hb
    have hq : Nat.card ↥(fixV B) ≤ Nat.card K := by
      rw [← card_fixMat]
      refine card_fixSet_pair_le hc1 hd1 _ (fun X hX => ⟨?_, ?_⟩)
        (fun X hX Y hY => sub_mem_fixMat hX hY)
      · have h := fix_of_mem_fixMat hX hcB
        simpa using h
      · have h := fix_of_mem_fixMat hX hdB
        simpa using h
    calc Nat.card B * Nat.card ↥(fixV B) ≤ Nat.card K ^ 2 * Nat.card K :=
          Nat.mul_le_mul (card_le_of_le_img hBi hB) hq
      _ = Nat.card K ^ 3 := by ring
  obtain ⟨b, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  obtain ⟨g, hg⟩ := hBi b.2
  have hgB : g ∈ B' := by
    change rho K g ∈ B
    rw [hg]
    exact b.2
  have hg1 : g ≠ 1 := fun h => hb1 (Subtype.ext (by rw [← hg, h, map_one]; rfl))
  have hgg := h2 g hgB
  have hgg1 : g.1 * g.1 = 1 := congrArg Prod.fst hgg
  have hgg2 : g.2 * g.2 = 1 := congrArg Prod.snd hgg
  have hgB' : rho K (g.1, g.2) ∈ B := hgB
  have hB'q : Nat.card B' ≤ Nat.card K ∧ Nat.card ↥(fixV B) ≤ Nat.card K ^ 2 := by
    by_cases h1 : ∃ c : SL K, c ≠ 1 ∧ (c, 1) ∈ B'
    ·
      have h1' : ∀ d : SL K, ((1 : SL K), d) ∈ B' → d = 1 := fun d hd => by
        by_contra hd1
        exact hb ⟨h1, d, hd1, hd⟩
      refine ⟨le_trans (Nat.card_le_card_of_injective
        (fun x : ↥B' => (⟨x.1.1, x.1, x.2, rfl⟩ :
          ↥(B'.map (MonoidHom.fst (SL K) (SL K))))) ?_) hP₁, ?_⟩
      · intro x y hxy
        have hfst : x.1.1 = y.1.1 := congrArg Subtype.val hxy
        have hmem : x.1 * y.1⁻¹ ∈ B' := B'.mul_mem x.2 (B'.inv_mem y.2)
        have e : x.1 * y.1⁻¹ = (1, x.1.2 * y.1.2⁻¹) := Prod.ext (by simp [hfst]) rfl
        rw [e] at hmem
        exact Subtype.ext (Prod.ext hfst (mul_inv_eq_one.mp (h1' _ hmem)))
      · have hc : g.1 ≠ 1 := fun h => hg1 (Prod.ext h (h1' g.2 (by rw [← h]; exact hgB)))
        exact card_fixV_le_sq_left hgB' hc hgg2
    ·
      have h1' : ∀ c : SL K, (c, (1 : SL K)) ∈ B' → c = 1 := fun c hc => by
        by_contra hc1
        exact h1 ⟨c, hc1, hc⟩
      refine ⟨le_trans (Nat.card_le_card_of_injective
        (fun x : ↥B' => (⟨x.1.2, x.1, x.2, rfl⟩ :
          ↥(B'.map (MonoidHom.snd (SL K) (SL K))))) ?_) hP₂, ?_⟩
      · intro x y hxy
        have hsnd : x.1.2 = y.1.2 := congrArg Subtype.val hxy
        have hmem : x.1 * y.1⁻¹ ∈ B' := B'.mul_mem x.2 (B'.inv_mem y.2)
        have e : x.1 * y.1⁻¹ = (x.1.1 * y.1.1⁻¹, 1) := Prod.ext rfl (by simp [hsnd])
        rw [e] at hmem
        exact Subtype.ext (Prod.ext (mul_inv_eq_one.mp (h1' _ hmem)) hsnd)
      · have hd : g.2 ≠ 1 := fun h => hg1 (Prod.ext (h1' g.1 (by rw [← h]; exact hgB)) h)
        exact card_fixV_le_sq_right hgB' hd hgg1
  rw [hcard]
  calc Nat.card B' * Nat.card ↥(fixV B) ≤ Nat.card K * Nat.card K ^ 2 :=
        Nat.mul_le_mul hB'q.1 hB'q.2
    _ = Nat.card K ^ 3 := by ring

end CFSG.Quasithin.Vol2.Ch10.C3.Om
