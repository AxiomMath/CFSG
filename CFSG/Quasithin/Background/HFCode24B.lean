module

public import CFSG.Quasithin.Background.HFCode24

public section

namespace CFSG.Quasithin.H.Mathieu

open CFSG.Monster.Code CFSG.QuasithinUnique.Setup.X1

variable {V : Type*} [CommGroup V] {L M : Subgroup (MulAut V)}

theorem mem_fixV_sup {A Y : Subgroup (MulAut V)} {v : V} :
    v ∈ fixV (A ⊔ Y) ↔ v ∈ fixV A ∧ v ∈ fixV Y := by
  constructor
  · intro hv
    exact ⟨fun x hx => hv x (le_sup_left (a := A) hx), fun x hx => hv x (le_sup_right (b := Y) hx)⟩
  · rintro ⟨hA, hY⟩
    have hle : A ⊔ Y ≤ MulAction.stabilizer (MulAut V) v :=
      sup_le (fun x hx => MulAction.mem_stabilizer_iff.2 (hA x hx))
        (fun x hx => MulAction.mem_stabilizer_iff.2 (hY x hx))
    exact fun x hx => MulAction.mem_stabilizer_iff.1 (hle hx)

theorem card_fixV_sup_modEq [Finite V] {A Y : Subgroup (MulAut V)}
    (hYA : Y ≤ Subgroup.normalizer (A : Set (MulAut V))) (hY : Nat.card Y = 3) :
    Nat.card (fixV A) ≡ Nat.card (fixV (A ⊔ Y)) [MOD 3] := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hYp : IsPGroup 3 Y := IsPGroup.of_card (n := 1) (by rw [hY]; norm_num)
  have hpres : ∀ y ∈ Y, ∀ v ∈ fixV A, y v ∈ fixV A := by
    intro y hy v hv a ha
    have h1 : y⁻¹ * a * y ∈ A := by
      have := (Subgroup.mem_normalizer_iff.1 (hYA (Y.inv_mem hy)) a).1 ha
      simpa using this
    have h2 := hv _ h1
    have h3 : (y⁻¹ * a * y) v = y⁻¹ (a (y v)) := rfl
    rw [h3] at h2
    have := congrArg y h2
    simpa using this
  let _ : MulAction ↥Y ↥(fixV A) :=
    { smul := fun y v => ⟨(y : MulAut V) v, hpres _ y.2 _ v.2⟩
      one_smul := fun v => Subtype.ext rfl
      mul_smul := fun a b v => Subtype.ext rfl }
  have hmod := hYp.card_modEq_card_fixedPoints ↥(fixV A)
  have hfix : Nat.card (MulAction.fixedPoints ↥Y ↥(fixV A)) = Nat.card (fixV (A ⊔ Y)) := by
    refine Nat.card_congr
      { toFun := fun v => ⟨v.1.1, mem_fixV_sup.2 ⟨v.1.2, fun y hy =>
          congrArg Subtype.val (v.2 ⟨y, hy⟩)⟩⟩
        invFun := fun v => ⟨⟨v.1, (mem_fixV_sup.1 v.2).1⟩, fun y => Subtype.ext
          ((mem_fixV_sup.1 v.2).2 y y.2)⟩
        left_inv := fun v => rfl
        right_inv := fun v => rfl }
  rwa [hfix] at hmod

theorem code24_h1607
    [Finite V] (hLM : IsOver L M) (h : MathieuCode24 L ⊤ ⊥) {s : ℕ} (hs : s = 2 ∨ s = 3)
    {A Y : Subgroup (MulAut V)} (hAM : A ≤ M) (hAe : IsElemAbelian2 A)
    (hAc : Nat.card A = 2 ^ (2 * s)) (hYc : Nat.card Y = 3) (hAY : ⁅A, Y⁆ = A) :
    rkIdx (fixV (A ⊔ Y)) ≠ 2 * (s + 1) := by
  have hle : rkIdx (fixV A) ≤ rkIdx (fixV (A ⊔ Y)) :=
    rkIdx_le_rkIdx_of_le fun v hv x hx => hv x (le_sup_left (a := A) hx)
  rcases hs with rfl | rfl
  · have h7 := code24_seven_le_rkIdx_E16 hLM h hAM hAe hAc
    omega
  · intro h8
    obtain ⟨d, hd, hdc⟩ := code24_even_E64 hLM h hAM hAe hAc
    have hYA : Y ≤ Subgroup.normalizer (A : Set (MulAut V)) := by
      have := Subgroup.normalizer_commutator_ge_right A Y
      rwa [hAY] at this
    have hmod := card_fixV_sup_modEq hYA hYc
    obtain ⟨e, -⟩ := code24_std h
    set c := MaskCoords.ofEquiv e
    have hrk := rk_add_rkIdx (fixV (A ⊔ Y))
    rw [c.rk_eq, h8] at hrk
    have hc3 : Nat.card (fixV (A ⊔ Y)) = 2 ^ 3 := by
      rw [card_eq_two_pow c.sq_eq_one]
      congr 1
      omega
    rw [hdc, hc3] at hmod
    obtain ⟨k, rfl⟩ : ∃ k, d = 2 * k := ⟨d / 2, by omega⟩
    have h1 : 2 ^ (2 * k) % 3 = 1 := by
      rw [pow_mul, Nat.pow_mod]
      norm_num
    unfold Nat.ModEq at hmod
    rw [h1] at hmod
    norm_num at hmod

theorem hP24 :
    ∀ B : Subgroup T24s2.Elem, (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) →
      Nat.card B = 2 ^ 6 → ∀ t : T24s2.Elem, ∀ b ∈ B, t * b * t⁻¹ ∈ B :=
  fun B hc hs hcard t _ hb => conj_mem_E64 B hc hs hcard t hb

theorem le_normalizer_of_map {W : Type*} [CommGroup W] (e : V ≃* W) {S A : Subgroup (MulAut V)}
    (h : S.map (congrHom e) ≤
      Subgroup.normalizer ((A.map (congrHom e) : Subgroup (MulAut W)) : Set (MulAut W))) :
    S ≤ Subgroup.normalizer (A : Set (MulAut V)) := by
  rw [← Subgroup.map_equiv_normalizer_eq A (MulAut.congr e)] at h
  exact (map_congrHom_le_iff e).1 h

theorem code24_le_normalizer
    (hLM : IsOver L M) (h : MathieuCode24 L ⊤ ⊥) {S A : Subgroup (MulAut V)} (hSM : S ≤ M)
    (hS : IsPGroup 2 S) (hAS : A ≤ S) (hAe : IsElemAbelian2 A) (hcard : Nat.card A = 2 ^ 6) :
    S ≤ Subgroup.normalizer (A : Set (MulAut V)) := by
  obtain ⟨e, he⟩ := code24_std h
  apply le_normalizer_of_map e
  have hAe' := (isElemAbelian2_map_congrHom e).2 hAe
  exact le_normalizer_of_sylow psiC24 (rhoC11_injective _ _) phi24 (T24s2.toSub_injective _ _)
    card_T24s2 hP24 (map_le_rangeC24 hLM he hSM)
    (hS.map (congrHom e)) (Subgroup.map_mono hAS) (fun x hx y hy => hAe'.1 x hx y hy)
    (fun x hx => by rw [← sq]; exact hAe'.2 x hx) ((card_map_congrHom e A).trans hcard)

theorem cocode24_le_normalizer
    (hLM : IsOver L M) (h : MathieuCocode24 L ⊤ ⊥) {S A : Subgroup (MulAut V)} (hSM : S ≤ M)
    (hS : IsPGroup 2 S) (hAS : A ≤ S) (hAe : IsElemAbelian2 A) (hcard : Nat.card A = 2 ^ 6) :
    S ≤ Subgroup.normalizer (A : Set (MulAut V)) := by
  obtain ⟨e, he, -⟩ := cocode24_stdO h
  apply le_normalizer_of_map e
  have hAe' := (isElemAbelian2_map_congrHom e).2 hAe
  exact le_normalizer_of_sylow rhoM24 (rho11_injective _ _) phi24 (T24s2.toSub_injective _ _)
    card_T24s2 hP24 (map_le_range24 hLM he hSM)
    (hS.map (congrHom e)) (Subgroup.map_mono hAS) (fun x hx y hy => hAe'.1 x hx y hy)
    (fun x hx => by rw [← sq]; exact hAe'.2 x hx) ((card_map_congrHom e A).trans hcard)

end CFSG.Quasithin.H.Mathieu
