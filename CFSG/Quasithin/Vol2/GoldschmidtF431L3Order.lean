module

public import CFSG.Quasithin.Vol2.GoldschmidtF431L3Transport
public import CFSG.Quasithin.Vol2.GoldschmidtF431L3Weyl
public import CFSG.Quasithin.Vol2.GoldschmidtF431Setting

public section

namespace CFSG.Quasithin.H13.F431

open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open
open CFSG.Quasithin.H13.F431.L3

@[expose] def F431L3Lie (f : ℕ) : Prop :=
  2 ≤ f → ∀ (D : Type) [Group D], LieModel D .PSL 3 2 f → ∀ A : LieAmalgamExt D,
    Odd (Nat.card ↥A.K / Nat.card D) → Nonempty (L3Datum A.Mb1 A.Mb2)

theorem LieExt.mem_range_β1 {D : Type} [Group D] {G : Type} [Group G] {M1 M2 : Subgroup G}
    (E : LieExt D M1 M2) {y : ↥(M1 ⊔ M2)} : y ∈ E.β1.range ↔ (y : G) ∈ M1 := by
  constructor
  · rintro ⟨x, rfl⟩
    exact (E.phi1.symm x).2
  · intro h
    exact ⟨E.phi1 ⟨y, h⟩, Subtype.ext (by simp [LieExt.β1])⟩

theorem LieExt.mem_range_β2 {D : Type} [Group D] {G : Type} [Group G] {M1 M2 : Subgroup G}
    (E : LieExt D M1 M2) {y : ↥(M1 ⊔ M2)} : y ∈ E.β2.range ↔ (y : G) ∈ M2 := by
  constructor
  · rintro ⟨x, rfl⟩
    exact (E.phi2.symm x).2
  · intro h
    exact ⟨E.phi2 ⟨y, h⟩, Subtype.ext (by simp [LieExt.β2])⟩

theorem f431L3Order_of_inputs {f : ℕ} (hf : 2 ≤ f)
    (hm : F431ModelFacts .PSL 3 f) (h45 : F431Facts45 .PSL 3 f hm) (hOut : F431Out .PSL 3 f)
    (hLie : F431L3Lie f) : F431L3Order f := by
  intro G _ _ hG hnab M1 M2 hyps D _ hD E
  have hodd := hOut G hG hnab M1 M2 hyps D hD E
  have hKne : Nat.card ↥E.K ≠ 0 := by
    intro h
    rw [h, Nat.zero_div] at hodd
    exact absurd hodd (by decide)
  have : Finite ↥E.K := Nat.finite_of_card_ne_zero hKne
  obtain ⟨Dat⟩ := hLie hf D hD E.toLieAmalgamExt hodd
  obtain ⟨Dg⟩ := Dat.nonempty_transport E.amalgIso
  have := hG
  obtain ⟨z, hz, hz2, hzC⟩ := hyps.2.2.1 ⟨rfl, rfl⟩
  have hz' : z ∈ centerOf Dg.S := by rw [Dg.S_eq]; exact hz
  have hz1 : z ≠ 1 := by
    intro h; rw [h, orderOf_one] at hz2; omega
  have hGood : Dg.Good := L3Datum.Good.of_hyp hz' hz1 hzC
  have htop : M1 ⊔ M2 = ⊤ := hGood.eq_top hz' hz1 hzC
  have hr3 : (Dg.s₁ * Dg.s₂) ^ 3 ∈ M1 ⊓ M2 := Dg.B_le hGood.r_cube_mem_B
  have hfinD : Finite D := (hm D hD).1
  let S := E.toLieAmalgamExt.setting hfinD (polyNumber .PSL) (three_le_polyNumber .PSL)
  have hS : S.Facts45L := h45 D hD E.toLieAmalgamExt
  let β := completionOf E.toLieAmalgamExt E.β1 E.β2 E.β_agree E.β_inter E.β_gen
  have hβ : β.IsFaithful :=
    ⟨E.β1_injective, E.β1_injective.comp (Subgroup.inclusion_injective _), E.β2_injective⟩
  have F := hS.facts46 β hβ
  have hsup : β.φ1.range ⊔ β.φ2.range = ⊤ := E.β_gen
  let s : ↥(β.φ1.range ⊔ β.φ2.range) :=
    ⟨⟨Dg.s₁, Subgroup.mem_sup_left Dg.s₁_mem⟩, by rw [hsup]; trivial⟩
  let t : ↥(β.φ1.range ⊔ β.φ2.range) :=
    ⟨⟨Dg.s₂, Subgroup.mem_sup_right Dg.s₂_mem⟩, by rw [hsup]; trivial⟩
  have hs : s * s = 1 := Subtype.ext (Subtype.ext Dg.s₁_sq)
  have ht : t * t = 1 := Subtype.ext (Subtype.ext Dg.s₂_sq)
  have hs1 : ((s : ↥(β.φ1.range ⊔ β.φ2.range)) : ↥(M1 ⊔ M2)) ∈ β.φ1.range :=
    (E.mem_range_β1).mpr Dg.s₁_mem
  have hs12 : ((s : ↥(β.φ1.range ⊔ β.φ2.range)) : ↥(M1 ⊔ M2)) ∉ β.φ1.range ⊓ β.φ2.range :=
    fun h => Dg.s₁_not ((E.mem_range_β2).mp h.2)
  have ht2 : ((t : ↥(β.φ1.range ⊔ β.φ2.range)) : ↥(M1 ⊔ M2)) ∈ β.φ2.range :=
    (E.mem_range_β2).mpr Dg.s₂_mem
  have ht12 : ((t : ↥(β.φ1.range ⊔ β.φ2.range)) : ↥(M1 ⊔ M2)) ∉ β.φ1.range ⊓ β.φ2.range :=
    fun h => Dg.s₂_not ((E.mem_range_β1).mp h.1)
  have hst : ((((s * t) ^ 3 : ↥(β.φ1.range ⊔ β.φ2.range)) : ↥(M1 ⊔ M2)) : ↥(M1 ⊔ M2)) ∈
      β.φ1.range ⊓ β.φ2.range := by
    refine ⟨(E.mem_range_β1).mpr ?_, (E.mem_range_β2).mpr ?_⟩
    · simpa [s, t] using hr3.1
    · simpa [s, t] using hr3.2
  have hmS : S.m = 3 := rfl
  have hpoly := (CosetGeom.lemma_F36 (G₁ := β.φ1.range) (G₂ := β.φ2.range) (m := S.m)
    (by rw [hmS]; norm_num) F.uniqueGeod hs ht hs1 hs12 ht2 ht12 (n := 3) (by norm_num)
    (by rw [hmS]) hst).2.1
  have hsmall : β.IsSmall S.m := F.isSmall_of_polygon hpoly
  have hcard := hS.lemma_F413_2 β hβ hsmall
  have hY : Nat.card ↥(M1 ⊔ M2) = Nat.card G := (Subgroup.card_eq_iff_eq_top (M1 ⊔ M2)).mpr htop
  exact le_of_eq (hY.symm.trans hcard)

end CFSG.Quasithin.H13.F431
