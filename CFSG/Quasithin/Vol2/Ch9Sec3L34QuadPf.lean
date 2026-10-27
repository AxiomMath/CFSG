module

public import CFSG.Quasithin.Vol2.Ch9Sec3L34KGM
public import CFSG.Quasithin.Vol2.Ch9Sec3L34KG
public import CFSG.Quasithin.Vol2.Ch9L34Norm9
public import CFSG.Quasithin.Vol2.Ch9L34Norm16
public import CFSG.Quasithin.Vol2.Ch9L34Norm18
public import CFSG.Quasithin.Vol2.Ch9L34Norm64

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Quasithin CFSG.Quasithin.H.Mathieu

theorem L34M.cube_of_equiv {V M : Type} [CommGroup V] [Finite V] [CommGroup M]
    (hV2 : ∀ v : V, v ^ 2 = 1) (e : V ≃* M) {n : ℕ} (hM : Nat.card M = 2 ^ n)
    {R : Subgroup (MulAut M)}
    (hcube : ∀ B : Subgroup (MulAut M), B ≤ R → B ≠ ⊥ → (∀ s ∈ B, s * s = 1) →
      (∀ s ∈ B, ∀ t ∈ B, ∀ w, s (t w * w) = t w * w) →
        Nat.card B ^ 3 * Nat.card (fixV B) ≤ 2 ^ n)
    {A : Subgroup (MulAut V)} (hAR : A.map (MulAut.congr e).toMonoidHom ≤ R) (hA1 : A ≠ ⊥)
    (hAel : IsElemAbelian2 A) (hAq : IsQuadratic A) :
    Nat.card A ^ 3 * Nat.card (fixV A) ≤ Nat.card V := by
  have hinj : Function.Injective (MulAut.congr e).toMonoidHom := (MulAut.congr e).injective
  have hB1 : A.map (MulAut.congr e).toMonoidHom ≠ ⊥ := fun h =>
    hA1 ((Subgroup.map_eq_bot_iff_of_injective _ hinj).1 h)
  have hsq : ∀ s ∈ A.map (MulAut.congr e).toMonoidHom, s * s = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, ← sq, hAel.2 a ha, map_one]
  have hq : ∀ s ∈ A.map (MulAut.congr e).toMonoidHom, ∀ t ∈ A.map (MulAut.congr e).toMonoidHom,
      ∀ w, s (t w * w) = t w * w := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ w
    have hv : (e.symm w)⁻¹ = e.symm w := by
      have h2 := hV2 (e.symm w)
      rw [sq] at h2
      exact inv_eq_of_mul_eq_one_right h2
    have hmem : b (e.symm w) * (e.symm w)⁻¹ ∈ commV A :=
      Subgroup.subset_closure ⟨b, hb, e.symm w, rfl⟩
    have hfix := hAq hmem a ha
    rw [hv] at hfix
    show e (a (e.symm (e (b (e.symm w)) * w))) = e (b (e.symm w)) * w
    rw [map_mul e.symm, MulEquiv.symm_apply_apply, hfix, map_mul, MulEquiv.apply_symm_apply]
  have key := hcube _ hAR hB1 hsq hq
  rw [Subgroup.card_map_of_injective hinj, E3.fixV_map_congr,
    Subgroup.card_map_of_injective e.injective] at key
  rwa [Nat.card_congr e.toEquiv, hM]

theorem L34M.map_congr_trans {V M : Type} [CommGroup V] [CommGroup M] (e : V ≃* M)
    (n : MulAut M) (A : Subgroup (MulAut V)) :
    A.map (MulAut.congr (e.trans n)).toMonoidHom =
      (A.map (MulAut.congr e).toMonoidHom).map (MulAut.conj n).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1

theorem L34M.map_le_normalizer {V M : Type} [CommGroup V] [CommGroup M] (e : V ≃* M)
    {X L : Subgroup (MulAut V)} (hXN : X ≤ Subgroup.normalizer (L : Set (MulAut V)))
    {S : Subgroup (MulAut M)} (he : L.map (MulAut.congr e).toMonoidHom = S) :
    X.map (MulAut.congr e).toMonoidHom ≤ Subgroup.normalizer (S : Set (MulAut M)) := by
  rw [← he, ← Subgroup.map_equiv_normalizer_eq]
  exact Subgroup.map_mono hXN

theorem factL34QuadThree_holds
    (hMod : FactL34Modules) : FactL34QuadThree := by
  intro V _ _ hV2 X hirr L hLX hXN hPSL hC hX2 A hAX hA1 hAel hAq
  have hA2 : IsPGroup 2 A := fun a => ⟨1, Subtype.ext (by simpa using hAel.2 a.1 a.2)⟩
  rcases hMod V hV2 X hirr L hLX hXN hPSL hC hX2 with ⟨e, he⟩ | ⟨e, he⟩ | ⟨e, he⟩ | ⟨e, he⟩
  · have hAN := (Subgroup.map_mono hAX).trans (L34M.map_le_normalizer e hXN he)
    exact L34M.cube_of_equiv hV2 e (L34M.card_of_coords (MaskCoords.std 9))
      (fun B hB hB1 hsq hq => L34M.cube9 hB hB1 hsq hq)
      (hAN.trans L34N.normalizer_img9_le) hA1 hAel hAq
  · have hAN := (Subgroup.map_mono hAX).trans (L34M.map_le_normalizer e hXN he)
    obtain ⟨n, -, hn⟩ := L34N.exists_conj_le18 hAN (hA2.map _)
    refine L34M.cube_of_equiv hV2 (e.trans n) (L34M.card_of_coords L34M.coords18)
      (fun B hB hB1 hsq hq => L34M.cube18 hB hB1 hsq hq) ?_ hA1 hAel hAq
    exact (L34M.map_congr_trans e n A).le.trans hn
  · have hAN := (Subgroup.map_mono hAX).trans (L34M.map_le_normalizer e hXN he)
    obtain ⟨n, -, hn⟩ := L34N.exists_conj_le16 hAN (hA2.map _)
    refine L34M.cube_of_equiv hV2 (e.trans n) (L34M.card_of_coords (MaskCoords.std 16))
      (fun B hB hB1 hsq hq => L34M.cube16 hB hB1 hsq hq) ?_ hA1 hAel hAq
    exact (L34M.map_congr_trans e n A).le.trans hn
  · have hAN := (Subgroup.map_mono hAX).trans (L34M.map_le_normalizer e hXN he)
    obtain ⟨n, -, hn⟩ := L34N.exists_conj_le64 hAN (hA2.map _)
    refine L34M.cube_of_equiv hV2 (e.trans n) (L34M.card_of_coords (MaskCoords.std 64))
      (fun B hB hB1 hsq hq => L34M.cube64 hB hB1 hsq hq) ?_ hA1 hAel hAq
    exact (L34M.map_congr_trans e n A).le.trans hn

end CFSG.Quasithin.H13.Ch9
