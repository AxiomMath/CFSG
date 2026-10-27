module

public import CFSG.Quasithin.Background.FFStarOffenderFF
public import CFSG.Quasithin.Background.B1MoreNineB
public import CFSG.Quasithin.Background.B1MoreNineC

public section

namespace CFSG.Quasithin

open CFSG.Open B19Aux

variable {V : Type*} [CommGroup V]

theorem isFFModule_of_offender {M : Type*} [CommGroup M] [Finite M] {X A : Subgroup (MulAut M)}
    (hA : IsFFStarOffender X A) : IsFFModule X :=
  CFSG.Quasithin.IsFFStarOffender.isFFModule hA

theorem autSub_conj_mem {X Y : Subgroup (MulAut V)} {W : Subgroup V}
    (h : ∀ x ∈ X, ∀ y ∈ Y, x * y * x⁻¹ ∈ Y) {φ ψ : MulAut ↥W} (hφ : φ ∈ autSub X W)
    (hψ : ψ ∈ autSub Y W) : φ * ψ * φ⁻¹ ∈ autSub Y W := by
  obtain ⟨g, hgX, rfl⟩ := mem_autSub.1 hφ
  obtain ⟨k, hkY, rfl⟩ := mem_autSub.1 hψ
  refine mem_autSub.2 ⟨g * k * g⁻¹, ?_, ?_⟩
  · simpa using h _ hgX _ hkY
  · simp [map_mul, map_inv]

theorem isFFStarMin_of_le {M : Type*} [CommGroup M] {X Y A : Subgroup (MulAut M)}
    (hA : IsFFStarMin X A) (hAY : A ≤ Y) (hYX : Y ≤ X) : IsFFStarMin Y A := by
  have hoff : ∀ B, IsFFStarOffender Y B → IsFFStarOffender X B := fun B hB =>
    ⟨hB.1.trans hYX, hB.2.1, hB.2.2.1, hB.2.2.2⟩
  refine ⟨⟨hAY, hA.1.2.1, hA.1.2.2.1, hA.1.2.2.2⟩, fun B hB hBA => ?_⟩
  refine hA.2 B (hoff B hB) ⟨?_, ?_, hBA.2.2.1, hBA.2.2.2⟩
  · exact ⟨hB.1.trans hYX, hB.2.1, hB.2.2.1⟩
  · exact ⟨hA.1.1, hA.1.2.1, hA.1.2.2.1⟩

namespace B19Loc

variable {G A : Subgroup (MulAut V)}

theorem FA_le_stab (G A : Subgroup (MulAut V)) : FAsub G A ≤ stabSub (Wsub G A) :=
  B1.le_stabSub_of_invariant fun _ hf w hw => W_inv_FA hf w hw

theorem A_le_stab (P : B19Loc G A) : A ≤ stabSub (Wsub G A) :=
  B1.le_stabSub_of_invariant fun _ ha w hw => P.W_inv_A ha w hw

@[expose] noncomputable def Fbar (G A : Subgroup (MulAut V)) : Subgroup (MulAut ↥(Wsub G A)) :=
  autSub (FAsub G A) (Wsub G A)

@[expose] noncomputable def Abar (G A : Subgroup (MulAut V)) : Subgroup (MulAut ↥(Wsub G A)) :=
  autSub A (Wsub G A)

@[expose] noncomputable def Hbar (G A : Subgroup (MulAut V)) : Subgroup (MulAut ↥(Wsub G A)) :=
  Fbar G A ⊔ Abar G A

theorem FA_inf_cent_W [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (P : B19Loc G A) :
    FAsub G A ⊓ centSub (Wsub G A) = ⊥ :=
  (Subgroup.eq_bot_iff_forall _).2 fun _ hf => P.FA_faithful_W hV hf.1 hf.2

theorem Fbar_card [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (P : B19Loc G A) :
    Nat.card ↥(Fbar G A) = Nat.card ↥(FAsub G A) := by
  have h := card_autSub_mul (FA_le_stab G A)
  rw [P.FA_inf_cent_W hV, Subgroup.card_bot, mul_one] at h
  exact h

theorem Fbar_odd [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (P : B19Loc G A) :
    ∀ x ∈ Fbar G A, Odd (orderOf x) := by
  intro x hx
  have hodd : Odd (Nat.card ↥(Fbar G A)) := by
    rw [P.Fbar_card hV]
    exact P.odd_card_FA
  have h1 : orderOf x ∣ Nat.card ↥(Fbar G A) := by
    have := orderOf_dvd_natCard (⟨x, hx⟩ : ↥(Fbar G A))
    rwa [Subgroup.orderOf_mk] at this
  exact hodd.of_dvd_nat h1

theorem offender_Abar [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (P : B19Loc G A) :
    IsFFStarOffender (autSub G (Wsub G A)) (Abar G A) :=
  P.offender_autSub_W hV

theorem Abar_sq [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (P : B19Loc G A) :
    ∀ a ∈ Abar G A, a ^ 2 = 1 :=
  (P.offender_Abar hV).2.2.1.2

theorem Abar_comm [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (P : B19Loc G A) :
    ∀ a ∈ Abar G A, ∀ b ∈ Abar G A, a * b = b * a :=
  (P.offender_Abar hV).2.2.1.1

theorem Abar_normalizes_Fbar (G A : Subgroup (MulAut V)) :
    Abar G A ≤ Subgroup.normalizer (Fbar G A : Set (MulAut ↥(Wsub G A))) :=
  le_normalizer_of_conj fun _ hφ _ hψ => autSub_conj_mem (fun _ hx _ hy => conj_FA hx hy) hφ hψ

theorem Fbar_le_Hbar : Fbar G A ≤ Hbar G A := le_sup_left

theorem Abar_le_Hbar : Abar G A ≤ Hbar G A := le_sup_right

theorem FA_solvable [Finite V] (P : B19Loc G A) : Group.IsSolvable ↥(FAsub G A) := by
  have h1 : Group.IsNilpotent ↥(fittingOf G) := fittingOf_nilpotent G
  have h2 : Group.IsSolvable ↥(fittingOf G) := inferInstance
  exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion P.FA_le)
    (Subgroup.inclusion_injective _)

theorem Fbar_solvable [Finite V] (P : B19Loc G A) : Group.IsSolvable ↥(Fbar G A) := by
  let fr : ↥(FAsub G A) →* MulAut ↥(Wsub G A) :=
    (resHom (Wsub G A)).comp (Subgroup.inclusion (FA_le_stab G A))
  have hrange : fr.range = Fbar G A := by
    ext φ
    constructor
    · rintro ⟨f, rfl⟩
      exact mem_autSub.2 ⟨Subgroup.inclusion (FA_le_stab G A) f, f.2, rfl⟩
    · intro hφ
      obtain ⟨g, hg, rfl⟩ := mem_autSub.1 hφ
      exact ⟨⟨g.1, hg⟩, rfl⟩
  have := P.FA_solvable
  have h : Group.IsSolvable ↥fr.range :=
    Group.isSolvable_of_surjective (f := fr.rangeRestrict) fr.rangeRestrict_surjective
  rw [hrange] at h
  exact h

theorem Hbar_solvable [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (P : B19Loc G A) :
    Group.IsSolvable ↥(Hbar G A) := by
  have := P.Fbar_solvable
  exact isSolvable_sup_of_le_normalizer (Abar_normalizes_Fbar G A) (P.Abar_comm hV)

theorem offender_Hbar [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (P : B19Loc G A) :
    IsFFStarOffender (Hbar G A) (Abar G A) := by
  have h := P.offender_Abar hV
  exact ⟨Abar_le_Hbar, h.2.1, h.2.2.1, h.2.2.2⟩

theorem isFFModule_Hbar [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (P : B19Loc G A) :
    IsFFModule (Hbar G A) :=
  isFFModule_of_offender (P.offender_Hbar hV)

theorem FA_le_G (P : B19Loc G A) : FAsub G A ≤ G := P.FA_le.trans (fittingOf_le G)

theorem Hbar_le_autSub [Finite V] (P : B19Loc G A) : Hbar G A ≤ autSub G (Wsub G A) :=
  sup_le (autSub_mono P.FA_le_G _) (autSub_mono P.A_le _)

theorem O2_Hbar [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (P : B19Loc G A) :
    ∀ Q : Subgroup (MulAut ↥(Wsub G A)), Q ≤ Hbar G A → (Q.subgroupOf (Hbar G A)).Normal →
      IsPGroup 2 ↥Q → Q = ⊥ := by
  intro Q hQ hQn hQ2
  have key := normal_two_subgroup_le (F := Fbar G A) (A' := Abar G A) (Q := Q)
    (Abar_normalizes_Fbar G A) (P.Fbar_odd hV) (P.Abar_sq hV) hQ hQn (fun q hq => by
      obtain ⟨k, hk⟩ := hQ2 ⟨q, hq⟩
      exact ⟨k, congrArg Subtype.val hk⟩)
  refine (Subgroup.eq_bot_iff_forall _).2 fun q hq => ?_
  obtain ⟨hqA, hqcomm⟩ := key q hq
  obtain ⟨g, hgA, rfl⟩ := mem_autSub.1 hqA
  have hgB : (g : MulAut V) ∈ Bsub G A := by
    refine ⟨hgA, Subgroup.mem_centralizer_iff.2 fun f hf => ?_⟩
    have hfbar : resHom (Wsub G A) ⟨f, FA_le_stab G A hf⟩ ∈ Fbar G A :=
      mem_autSub.2 ⟨⟨f, FA_le_stab G A hf⟩, hf, rfl⟩
    have hc := hqcomm _ hfbar
    have hcw : ∀ w : ↥(Wsub G A), (g : MulAut V) (f (w : V)) = f ((g : MulAut V) (w : V)) := by
      intro w
      have := congrArg (fun φ : MulAut ↥(Wsub G A) => ((φ w : ↥(Wsub G A)) : V)) hc
      simpa [resHom_apply, MulAut.mul_apply] using this
    have hconj : (g : MulAut V) * f * (g : MulAut V)⁻¹ * f⁻¹ ∈ FAsub G A :=
      (FAsub G A).mul_mem (conj_FA hgA hf) ((FAsub G A).inv_mem hf)
    have hfix : ∀ w ∈ Wsub G A, ((g : MulAut V) * f * (g : MulAut V)⁻¹ * f⁻¹) w = w := by
      intro w hw
      have hw' : (g : MulAut V)⁻¹ (f⁻¹ w) ∈ Wsub G A :=
        P.W_inv_A (A.inv_mem hgA) _ (W_inv_FA ((FAsub G A).inv_mem hf) w hw)
      have h1 := hcw ⟨_, hw'⟩
      simp only [MulAut.mul_apply]
      simp only at h1
      rw [h1]
      simp
    have h2 := P.FA_faithful_W hV hconj hfix
    have h3 : (g : MulAut V) * f * (g : MulAut V)⁻¹ = f := mul_inv_eq_one.1 h2
    have h4 : (g : MulAut V) * f = f * (g : MulAut V) := by
      calc (g : MulAut V) * f = ((g : MulAut V) * f * (g : MulAut V)⁻¹) * (g : MulAut V) := by group
        _ = f * (g : MulAut V) := by rw [h3]
    exact h4.symm
  ext w
  exact W_le_C w.2 g hgB

end B19Loc

end CFSG.Quasithin
