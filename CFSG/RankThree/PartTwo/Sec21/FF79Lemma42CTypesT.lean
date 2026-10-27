module

public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab
public import CFSG.Open.StatedZModTwo
import CFSG.GroupTheory.Fitting.LayerTopBot

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.Open CFSG.Open.StatedAPI

theorem card_of_isLnq_three_two_one {G : Type} [Group G] {Y : Subgroup G} (h : IsLnq 3 2 1 Y) :
    Nat.card Y = 168 := by
  obtain ⟨-, K, hK, hKf, hcard, ⟨e⟩⟩ := h
  have hcard' : Nat.card K = 2 := by simpa using hcard
  rw [Nat.card_congr e.toEquiv]
  have hb : (StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K) = ⊥ := by
    rw [statedScalars_eq_bot_of_card_two hcard', Subgroup.bot_subgroupOf]
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((⊥ : Subgroup ↥(StatedSL 3 K)))
  rw [Subgroup.card_bot, mul_one, card_statedSL_three_of_card_eq_two hcard'] at h1
  exact (Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hb).toEquiv).trans h1.symm

theorem card_dvd_of_isLnq_two_two_two {G : Type} [Group G] {Y : Subgroup G}
    (h : IsLnq 2 2 2 Y) : Nat.card Y ∣ 60 := by
  obtain ⟨-, K, hK, hKf, hcard, ⟨e⟩⟩ := h
  have hcard' : Nat.card K = 4 := by simpa using hcard
  rw [Nat.card_congr e.toEquiv]
  have h60 : Nat.card (StatedSL 2 K) = 60 := by
    rw [card_statedSL_two, hcard']
    norm_num
  rw [← h60]
  exact Subgroup.card_quotient_dvd_card _

theorem not_isLnq_both {G : Type} [Group G] (Y : Subgroup G) :
    ¬ (IsLnq 2 2 2 Y ∧ IsLnq 3 2 1 Y) := by
  rintro ⟨h1, h2⟩
  have := card_dvd_of_isLnq_two_two_two h1
  rw [card_of_isLnq_three_two_one h2] at this
  omega

section Transport

variable {G H : Type} [Group G] [Group H]

theorem mem_lay_iff {A : Subgroup G} {B : Subgroup H} (φ : ↥A ≃* ↥B) (z : G) :
    z ∈ Lay A ↔ ∃ hz : z ∈ A, ((φ ⟨z, hz⟩ : ↥B) : H) ∈ Lay B := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hmem : φ w ∈ CFSG.layer ↥B := by
      rw [← WholeGroup.layer_map_mulEquiv φ]
      exact ⟨w, hw, rfl⟩
    exact ⟨w.2, φ w, hmem, rfl⟩
  · rintro ⟨hz, v, hv, hvz⟩
    have hv' : v = φ ⟨z, hz⟩ := Subtype.ext hvz
    have hmem : φ.symm v ∈ CFSG.layer ↥A := by
      rw [← WholeGroup.layer_map_mulEquiv φ.symm]
      exact ⟨v, hv, rfl⟩
    refine ⟨φ.symm v, hmem, ?_⟩
    rw [hv']
    simp

noncomputable def layEquiv {A : Subgroup G} {B : Subgroup H} (φ : ↥A ≃* ↥B) :
    ↥(Lay A) ≃* ↥(Lay B) :=
  ((Subgroup.equivMapOfInjective (CFSG.layer ↥A) A.subtype A.subtype_injective).symm.trans
    ((φ.subgroupMap (CFSG.layer ↥A)).trans
      (MulEquiv.subgroupCongr (WholeGroup.layer_map_mulEquiv φ)))).trans
    (Subgroup.equivMapOfInjective (CFSG.layer ↥B) B.subtype B.subtype_injective)

theorem isLnq_lay_iff {A : Subgroup G} {B : Subgroup H} (φ : ↥A ≃* ↥B) {n p f : ℕ} :
    IsLnq n p f (Lay A) ↔ IsLnq n p f (Lay B) :=
  ⟨fun h => CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv (layEquiv φ) h,
   fun h => CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv (layEquiv φ).symm h⟩

@[expose] noncomputable def cenEquiv {J : Subgroup G} (e : ↥J ≃* H) (x : G) (hx : x ∈ J) :
    ↥(J ⊓ Cen x) ≃* ↥(Cen (e ⟨x, hx⟩)) where
  toFun w := ⟨e ⟨w, w.2.1⟩, by
    have h := Subgroup.mem_centralizer_singleton_iff.mp w.2.2
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext h)⟩
  invFun v := ⟨((e.symm v : ↥J) : G), (e.symm v).2, by
    have h := Subgroup.mem_centralizer_singleton_iff.mp v.2
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have h' := congrArg e.symm h
    simp only [map_mul, MulEquiv.symm_apply_apply] at h'
    exact congrArg Subtype.val h'⟩
  left_inv w := by
    apply Subtype.ext
    simp
  right_inv v := by
    apply Subtype.ext
    simp
  map_mul' a b := by
    apply Subtype.ext
    change e ⟨((a * b : ↥(J ⊓ Cen x)) : G), _⟩ = e ⟨(a : G), _⟩ * e ⟨(b : G), _⟩
    rw [← map_mul]
    rfl

theorem mem_lay_cen_iff {J : Subgroup G} (e : ↥J ≃* H) (x : G) (hx : x ∈ J) (z : G) :
    z ∈ Lay (J ⊓ Cen x) ↔ ∃ hz : z ∈ J, e ⟨z, hz⟩ ∈ Lay (Cen (e ⟨x, hx⟩)) := by
  rw [mem_lay_iff (cenEquiv e x hx) z]
  constructor
  · rintro ⟨hz, h⟩
    exact ⟨hz.1, h⟩
  · rintro ⟨hz, h⟩
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp
      (Subgroup.map_subtype_le _ h : _ ∈ Cen (e ⟨x, hx⟩))
    rw [← map_mul, ← map_mul] at h1
    have h2 := congrArg Subtype.val (e.injective h1)
    exact ⟨⟨hz, Subgroup.mem_centralizer_singleton_iff.mpr h2⟩, h⟩

theorem isLnq_lay_cen_iff {J : Subgroup G} (e : ↥J ≃* H) (x : G) (hx : x ∈ J) {n p f : ℕ} :
    IsLnq n p f (Lay (J ⊓ Cen x)) ↔ IsLnq n p f (Lay (Cen (e ⟨x, hx⟩))) :=
  isLnq_lay_iff (cenEquiv e x hx)

end Transport

end CFSG.RankThree.PartTwo.Sec21.FF79
