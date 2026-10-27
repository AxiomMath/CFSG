module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC34Unique

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem s16h_card_map_mul_card_inf_ker {H N : Type*} [Group H] [Group N]
    (f : H →* N) (E : Subgroup H) :
    Nat.card ↥(E.map f) * Nat.card ↥(E ⊓ f.ker) = Nat.card ↥E := by
  have h1 : Nat.card ↥(f.ker.subgroupOf E) * Nat.card ↥(E.map f) = Nat.card ↥E := by
    have h := Subgroup.card_ker_mul_card_range (f.domRestrict E)
    rw [MonoidHom.ker_domRestrict, MonoidHom.domRestrict_range] at h
    exact h
  have h2 : Nat.card ↥(f.ker.subgroupOf E) = Nat.card ↥(E ⊓ f.ker) := by
    rw [← Subgroup.inf_subgroupOf_left (H := f.ker) (K := E)]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : E ⊓ f.ker ≤ E)).toEquiv
  rw [h2, mul_comm] at h1
  exact h1

private theorem s16h_card_le_mul_card_comap {H N : Type*} [Group H] [Group N]
    (f : H →* N) (E : Subgroup H) (K : Subgroup N) {k : ℕ}
    (h : Nat.card ↥(E.map f) ≤ k * Nat.card ↥(E.map f ⊓ K)) :
    Nat.card ↥E ≤ k * Nat.card ↥(E ⊓ K.comap f) := by
  have hA : Nat.card ↥E = Nat.card ↥(E.map f) * Nat.card ↥(E ⊓ f.ker) :=
    (s16h_card_map_mul_card_inf_ker f E).symm
  have hB : Nat.card ↥(E ⊓ K.comap f)
      = Nat.card ↥(E.map f ⊓ K) * Nat.card ↥(E ⊓ f.ker) := by
    have h1 := s16h_card_map_mul_card_inf_ker f (E ⊓ K.comap f)
    have hker : (E ⊓ K.comap f) ⊓ f.ker = E ⊓ f.ker := by
      rw [inf_assoc]
      congr 1
      exact inf_eq_right.2 (Subgroup.ker_le_comap f K)
    rw [Subgroup.map_inf_comap E K f, hker] at h1
    exact h1.symm
  rw [hA, hB]
  calc Nat.card ↥(E.map f) * Nat.card ↥(E ⊓ f.ker)
      ≤ (k * Nat.card ↥(E.map f ⊓ K)) * Nat.card ↥(E ⊓ f.ker) :=
        Nat.mul_le_mul_right _ h
    _ = k * (Nat.card ↥(E.map f ⊓ K) * Nat.card ↥(E ⊓ f.ker)) := by
        rw [mul_assoc]

theorem s16h_card_le_mul_card_preBarSub {M V₀ V E : Subgroup G} (hV : IsElemAbelian 2 V)
    (hEM : E ≤ M) (hEs : E ≤ stabTil V₀ V) (Xbar : Subgroup (MulAut (Vtil V₀ V hV))) {k : ℕ}
    (h : Nat.card ↥(barSub V₀ V hV E) ≤ k * Nat.card ↥(barSub V₀ V hV E ⊓ Xbar)) :
    Nat.card ↥E ≤ k * Nat.card ↥(E ⊓ preBarSub M V₀ V hV Xbar) := by
  have h' : Nat.card ↥((E.subgroupOf (stabTil V₀ V)).map (actTil V₀ V hV)) ≤
      k * Nat.card ↥((E.subgroupOf (stabTil V₀ V)).map (actTil V₀ V hV) ⊓ Xbar) := by
    simpa only [barSub] using h
  have hgen := s16h_card_le_mul_card_comap (actTil V₀ V hV)
    (E.subgroupOf (stabTil V₀ V)) Xbar h'
  have hpre : E ⊓ preBarSub M V₀ V hV Xbar
      = ((E.subgroupOf (stabTil V₀ V)) ⊓ Xbar.comap (actTil V₀ V hV)).map
          (stabTil V₀ V).subtype := by
    unfold preBarSub
    rw [← inf_assoc, inf_eq_left.2 hEM]
    rw [Subgroup.map_inf _ _ (stabTil V₀ V).subtype (Subgroup.subtype_injective _)]
    rw [Subgroup.map_subgroupOf_eq_of_le hEs]
  have hcard4 : Nat.card ↥(E ⊓ preBarSub M V₀ V hV Xbar)
      = Nat.card ↥((E.subgroupOf (stabTil V₀ V)) ⊓ Xbar.comap (actTil V₀ V hV)) := by
    rw [hpre, Subgroup.card_map_of_injective (f := (stabTil V₀ V).subtype)
      (K := (E.subgroupOf (stabTil V₀ V)) ⊓ Xbar.comap (actTil V₀ V hV))
      (Subgroup.subtype_injective _)]
  have hcardE : Nat.card ↥E = Nat.card ↥(E.subgroupOf (stabTil V₀ V)) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEs).toEquiv).symm
  calc Nat.card ↥E = Nat.card ↥(E.subgroupOf (stabTil V₀ V)) := hcardE
    _ ≤ k * Nat.card ↥((E.subgroupOf (stabTil V₀ V)) ⊓
        Xbar.comap (actTil V₀ V hV)) := hgen
    _ = k * Nat.card ↥(E ⊓ preBarSub M V₀ V hV Xbar) := by rw [hcard4]

private theorem s16h_ncard_conj_eq_index {A : Type*} [Group A] (E L : Subgroup A) :
    ({F : Subgroup A | ∃ x ∈ E, F = L.map (MulAut.conj x).toMonoidHom} :
        Set (Subgroup A)).ncard
      = ((normalizer (L : Set A)).subgroupOf E).index := by
  let φ : ↥E →* MulAut A := MulAut.conj.comp E.subtype
  let _ : MulAction ↥E (Subgroup A) := MulAction.compHom (Subgroup A) φ
  have hsmul : ∀ (h : ↥E) (X : Subgroup A),
      h • X = X.map (MulAut.conj (h : A)).toMonoidHom := fun _ _ => rfl
  have hstab : MulAction.stabilizer ↥E L = (Subgroup.normalizer (L : Set A)).subgroupOf E := by
    ext h
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, hsmul,
      Subgroup.mem_normalizer_iff_map_conj_eq]
    exact Iff.rfl
  have horb : MulAction.orbit ↥E L
      = {F : Subgroup A | ∃ x ∈ E, F = L.map (MulAut.conj x).toMonoidHom} := by
    ext F
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨h, h.2, hsmul h L⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, hsmul ⟨x, hx⟩ L⟩
  rw [← hstab, MulAction.index_stabilizer, horb]

theorem s16h_card_le_three_mul_card_inf_normalizer {A : Type*} [Group A] [Finite A]
    {E : Subgroup A} {S : Set (Subgroup A)} (hS : S.ncard ≤ 3)
    (hE : ∀ x ∈ E, ∀ T ∈ S, T.map (MulAut.conj x).toMonoidHom ∈ S) {L : Subgroup A}
    (hL : L ∈ S) : Nat.card ↥E ≤ 3 * Nat.card ↥(E ⊓ normalizer (L : Set A)) := by
  let C : Set (Subgroup A) := {F | ∃ x ∈ E, F = L.map (MulAut.conj x).toMonoidHom}
  have hCS : C ⊆ S := by
    rintro F ⟨x, hx, rfl⟩
    exact hE x hx L hL
  haveI : Finite (Subgroup A) :=
    Finite.of_injective (fun H : Subgroup A => (H : Set A)) SetLike.coe_injective
  have hCn : C.ncard ≤ 3 := le_trans (Set.ncard_le_ncard hCS (Set.toFinite S)) hS
  have hCindex : C.ncard = ((normalizer (L : Set A)).subgroupOf E).index :=
    s16h_ncard_conj_eq_index E L
  have hcard : Nat.card ↥((normalizer (L : Set A)).subgroupOf E) * C.ncard = Nat.card ↥E := by
    rw [hCindex]
    exact Subgroup.card_mul_index (H := (normalizer (L : Set A)).subgroupOf E)
  have hcard_sub : Nat.card ↥((normalizer (L : Set A)).subgroupOf E)
      = Nat.card ↥(E ⊓ normalizer (L : Set A)) := by
    rw [← Subgroup.inf_subgroupOf_left (H := normalizer (L : Set A)) (K := E)]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : E ⊓ normalizer (L : Set A) ≤ E)).toEquiv
  calc Nat.card ↥E = Nat.card ↥((normalizer (L : Set A)).subgroupOf E) * C.ncard :=
        hcard.symm
    _ ≤ Nat.card ↥((normalizer (L : Set A)).subgroupOf E) * 3 :=
        Nat.mul_le_mul_left _ hCn
    _ = 3 * Nat.card ↥(E ⊓ normalizer (L : Set A)) := by rw [hcard_sub, mul_comm]

theorem s16h_centSub_inf_le_centSub_sup {W : Type*} [CommGroup W] (Y₁ Y₂ : Subgroup W) :
    centSub Y₁ ⊓ centSub Y₂ ≤ centSub (Y₁ ⊔ Y₂) := by
  intro g hg u hu
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hu
  rw [map_mul, (mem_centSub.mp (Subgroup.mem_inf.mp hg).1) a ha,
    (mem_centSub.mp (Subgroup.mem_inf.mp hg).2) b hb]

theorem s16h_preBarSub_le_cElt_of_le_centSub {M V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    {Y : Subgroup (Vtil V₀ V hV)} {K : Subgroup (MulAut (Vtil V₀ V hV))} (hK : K ≤ centSub Y)
    {w : G} (hw : w ∈ preTil V₀ V hV Y) :
    preBarSub M V₀ V hV K ≤ F11.CElt M V₀ w := by
  obtain ⟨y, rfl, hy⟩ := (mem_preTil V₀ V hV Y).1 hw
  exact s16c34_preBarSub_le_cElt hV (mem_fixV.2 fun φ hφ => (mem_centSub.1 (hK hφ)) _ hy)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
