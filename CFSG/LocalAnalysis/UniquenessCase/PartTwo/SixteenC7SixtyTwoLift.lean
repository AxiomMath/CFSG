module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeY2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7SixtyTwoComp
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22vg
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22d
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214c
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

section Bridge

theorem s16c7_le_stabTil_bot {M V : Subgroup G} (hMV : M ≤ normalizer (V : Set G)) :
    M ≤ stabTil ⊥ V := by
  refine le_stabTil hMV ?_
  intro m _
  rw [Subgroup.mem_normalizer_iff]
  intro h
  simp only [SetLike.mem_coe, Subgroup.mem_bot]
  constructor
  · rintro rfl
    simp
  · intro hh
    calc h = m⁻¹ * (m * h * m⁻¹) * m := by group
      _ = 1 := by rw [hh]; group

theorem s16c7_exists_mbar_equiv (D : Data G) {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMV : D.M ≤ normalizer (V : Set G)) :
    ∃ e : MBar D.M V ≃* ↥(Mbar D.M ⊥ V hV), ∀ X : Subgroup G, X ≤ D.M →
      (mbarImage D.M V X).map e.toMonoidHom =
        (barSub ⊥ V hV X).subgroupOf (Mbar D.M ⊥ V hV) := by
  have hMs : D.M ≤ stabTil ⊥ V := s16c7_le_stabTil_bot hMV
  haveI : ((F11.CTilde D.M ⊥ V).subgroupOf D.M).Normal := cTilde_bot_normal D.M V hMV
  obtain ⟨e₂, he₂⟩ := s15_Three_barImage_equiv (D := D) (V₀ := ⊥) (V := V) hV hMs
  refine ⟨(mbarEquiv D.M V).trans e₂, fun X hX => ?_⟩
  have h1 : ((mbarEquiv D.M V).trans e₂).toMonoidHom =
      e₂.toMonoidHom.comp (mbarEquiv D.M V).toMonoidHom := rfl
  rw [h1, ← Subgroup.map_map, map_mbarImage]
  exact he₂ X hX

end Bridge

section Helpers

theorem s16c7_normal_subgroupOf {Γ : Type*} [Group Γ] {H A : Subgroup Γ} (_hHA : H ≤ A)
    (hn : ∀ a ∈ A, ∀ h ∈ H, a * h * a⁻¹ ∈ H) : (H.subgroupOf A).Normal :=
  ⟨fun x hx b => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simpa using hn (b : Γ) b.2 (x : Γ) hx⟩

theorem s16c7_eq_of_subgroupOf_eq {Γ : Type*} [Group Γ] {B H H' : Subgroup Γ} (hH : H ≤ B)
    (hH' : H' ≤ B) (h : H.subgroupOf B = H'.subgroupOf B) : H = H' := by
  have h1 := Subgroup.subgroupOf_inj.1 h
  rwa [inf_eq_left.2 hH, inf_eq_left.2 hH'] at h1

theorem s16c7_isComponentOf_map {Γ : Type*} [Group Γ] {B : Subgroup Γ} {Q : Type*} [Group Q]
    (e : Q ≃* ↥B) {H : Subgroup Γ} (hHB : H ≤ B) (hsub : CFSG.Open.IsSubnormal H B)
    (hq : CFSG.Open.IsQuasisimple ↥H) :
    CFSG.Open.IsComponentOf ((H.subgroupOf B).map e.symm.toMonoidHom) (⊤ : Subgroup Q) := by
  refine ⟨le_top, ?_, ?_⟩
  · have h1 := (hsub.comap B.subtype).map e.symm.toMonoidHom
    rw [Subgroup.comap_subtype, Subgroup.comap_subtype, Subgroup.subgroupOf_self,
      Subgroup.map_top_of_surjective _ e.symm.surjective] at h1
    exact h1
  · let ι : ↥((H.subgroupOf B).map e.symm.toMonoidHom) ≃* ↥H :=
      ((H.subgroupOf B).equivMapOfInjective e.symm.toMonoidHom e.symm.injective).symm.trans
        (Subgroup.subgroupOfEquivOfLe hHB)
    exact CFSG.Open.IsQuasisimple.of_mulEquiv ι hq

theorem s16c7_barSub_sup (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) {X₁ X₂ : Subgroup G}
    (h₁ : X₁ ≤ stabTil V₀ V) (h₂ : X₂ ≤ stabTil V₀ V) :
    barSub V₀ V hV (X₁ ⊔ X₂) = barSub V₀ V hV X₁ ⊔ barSub V₀ V hV X₂ := by
  unfold barSub
  rw [Subgroup.subgroupOf_sup h₁ h₂, Subgroup.map_sup]

theorem s16c7_barSub_map_conj (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) {m : G}
    (hm : m ∈ stabTil V₀ V) (X : Subgroup G) :
    barSub V₀ V hV (X.map (MulAut.conj m).toMonoidHom) =
      (barSub V₀ V hV X).map (MulAut.conj (actTil V₀ V hV ⟨m, hm⟩)).toMonoidHom := by
  have h1 := s15_Infra_barSub_conjSubgroup V₀ V hV ((stabTil V₀ V).inv_mem hm) X
  have h2 : conjSubgroup X m⁻¹ = X.map (MulAut.conj m).toMonoidHom := by
    unfold conjSubgroup
    rw [inv_inv]
  have h3 : (actTil V₀ V hV ⟨m⁻¹, (stabTil V₀ V).inv_mem hm⟩)⁻¹ =
      actTil V₀ V hV ⟨m, hm⟩ := by
    rw [← map_inv]
    congr 1
    exact Subtype.ext (inv_inv m)
  rw [h2, h3] at h1
  exact h1

end Helpers

section Lift

theorem s16c7_lift_factors (D : Data G) (h119 : R119W D) {V : Subgroup G}
    (hV : IsElemAbelian 2 V) (hMV : D.M ≤ normalizer (V : Set G)) (hH : F11.Hyp11 D ⊥ V)
    {A : Subgroup (MulAut (Vtil ⊥ V hV))} (hAM : A ≤ Mbar D.M ⊥ V hV)
    (hMA : Mbar D.M ⊥ V hV ≤ normalizer (A : Set (MulAut (Vtil ⊥ V hV))))
    {X : Type} [Group X] (hX : IsL3 X 1) (φ : ↥A ≃* X × X) :
    ∃ K₁ K₂ : Subgroup G, K₁ ∈ calC D.M ∧ K₂ ∈ calC D.M ∧ K₁ ≠ K₂ ∧
      barSub ⊥ V hV (K₁ ⊔ K₂) = A ∧ D.M ≤ normalizer ((K₁ ⊔ K₂ : Subgroup G) : Set G) ∧
      IsL3 ↥(barSub ⊥ V hV K₁) 1 ∧ IsL3 ↥(barSub ⊥ V hV K₂) 1 ∧
      K₁ ≤ normalizer (K₂ : Set G) ∧ K₂ ≤ normalizer (K₁ : Set G) := by
  have hMs : D.M ≤ stabTil ⊥ V := s16c7_le_stabTil_bot hMV
  obtain ⟨e, he⟩ := s16c7_exists_mbar_equiv D hV hMV
  obtain ⟨H₁, H₂, hH₁A, hH₂A, hsup, hinf, hL₁, hL₂, hn₁, hn₂, hperm⟩ := s16c7_components hX φ
  haveI : Finite X := s16c7_finite_of_psi φ
  have hAsub : CFSG.Open.IsSubnormal A (Mbar D.M ⊥ V hV) :=
    CFSG.Open.IsSubnormal.step hAM
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hAM).2 hMA) (CFSG.Open.IsSubnormal.refl _)
  have hsub₁ : CFSG.Open.IsSubnormal H₁ (Mbar D.M ⊥ V hV) :=
    CFSG.Open.IsSubnormal.step hH₁A (s16c7_normal_subgroupOf hH₁A hn₁) hAsub
  have hsub₂ : CFSG.Open.IsSubnormal H₂ (Mbar D.M ⊥ V hV) :=
    CFSG.Open.IsSubnormal.step hH₂A (s16c7_normal_subgroupOf hH₂A hn₂) hAsub
  have hH₁M : H₁ ≤ Mbar D.M ⊥ V hV := hH₁A.trans hAM
  have hH₂M : H₂ ≤ Mbar D.M ⊥ V hV := hH₂A.trans hAM
  have hcomp₁ := s16c7_isComponentOf_map e hH₁M hsub₁ (s16c7_isQuasisimple_of_isL3 hL₁)
  have hcomp₂ := s16c7_isComponentOf_map e hH₂M hsub₂ (s16c7_isQuasisimple_of_isL3 hL₂)
  obtain ⟨K₁, hK₁, hK₁bar⟩ := uc22p22vg_exists_calC_image D hMV hH h119 hcomp₁
  obtain ⟨K₂, hK₂, hK₂bar⟩ := uc22p22vg_exists_calC_image D hMV hH h119 hcomp₂
  have hK₁M : K₁ ≤ D.M := uc22p22a_le_of_isSubnormal hK₁.1
  have hK₂M : K₂ ≤ D.M := uc22p22a_le_of_isSubnormal hK₂.1
  have hmapmap : ∀ S : Subgroup ↥(Mbar D.M ⊥ V hV),
      (S.map e.symm.toMonoidHom).map e.toMonoidHom = S := by
    intro S
    rw [Subgroup.map_map]
    have : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id _ := by
      ext x
      simp
    rw [this, Subgroup.map_id]
  have hbar₁ : barSub ⊥ V hV K₁ = H₁ := by
    have h1 : (barSub ⊥ V hV K₁).subgroupOf (Mbar D.M ⊥ V hV) =
        H₁.subgroupOf (Mbar D.M ⊥ V hV) := by
      rw [← he K₁ hK₁M, hK₁bar, hmapmap]
    exact s16c7_eq_of_subgroupOf_eq (barSub_mono ⊥ V hV hK₁M) hH₁M h1
  have hbar₂ : barSub ⊥ V hV K₂ = H₂ := by
    have h1 : (barSub ⊥ V hV K₂).subgroupOf (Mbar D.M ⊥ V hV) =
        H₂.subgroupOf (Mbar D.M ⊥ V hV) := by
      rw [← he K₂ hK₂M, hK₂bar, hmapmap]
    exact s16c7_eq_of_subgroupOf_eq (barSub_mono ⊥ V hV hK₂M) hH₂M h1
  have hH₁ne : H₁ ≠ ⊥ := by
    intro h
    have := card_eq_of_isL3 hL₁
    rw [h, Subgroup.card_bot] at this
    omega
  have hH₂ne : H₂ ≠ ⊥ := by
    intro h
    have := card_eq_of_isL3 hL₂
    rw [h, Subgroup.card_bot] at this
    omega
  have hK₁₂ : K₁ ≠ K₂ := by
    intro h
    have h1 : H₁ = H₂ := by rw [← hbar₁, ← hbar₂, h]
    apply hH₁ne
    rw [← inf_idem H₁]
    nth_rewrite 2 [h1]
    exact hinf
  have hpermK : ∀ m ∈ D.M, ∀ K ∈ calC D.M, (barSub ⊥ V hV K = H₁ ∨ barSub ⊥ V hV K = H₂) →
      K.map (MulAut.conj m).toMonoidHom = K₁ ∨ K.map (MulAut.conj m).toMonoidHom = K₂ := by
    intro m hm K hK hKbar
    have hKM : K ≤ D.M := uc22p22a_le_of_isSubnormal hK.1
    have hK' : K.map (MulAut.conj m).toMonoidHom ∈ calC D.M :=
      uc22p2214_calC_of_mem_conjSetOf hK ⟨m, hm, rfl⟩
    have hK'M : K.map (MulAut.conj m).toMonoidHom ≤ D.M :=
      uc22p22a_le_of_isSubnormal hK'.1
    have hmst : m ∈ stabTil ⊥ V := hMs hm
    have hmb : actTil ⊥ V hV ⟨m, hmst⟩ ∈ Mbar D.M ⊥ V hV :=
      actTil_mem_barSub ⊥ V hV hm hmst
    have hbarK' := s16c7_barSub_map_conj ⊥ V hV hmst K
    have himg : barSub ⊥ V hV (K.map (MulAut.conj m).toMonoidHom) = H₁ ∨
        barSub ⊥ V hV (K.map (MulAut.conj m).toMonoidHom) = H₂ := by
      rw [hbarK']
      exact hperm _ (hMA hmb) _ hKbar
    have key : ∀ (Kj : Subgroup G), Kj ∈ calC D.M → Kj ≤ D.M → barSub ⊥ V hV Kj ≠ ⊥ →
        barSub ⊥ V hV (K.map (MulAut.conj m).toMonoidHom) = barSub ⊥ V hV Kj →
        K.map (MulAut.conj m).toMonoidHom = Kj := by
      intro Kj hKj hKjM hne heq
      by_contra hne'
      have hbot : mbarImage D.M V (K.map (MulAut.conj m).toMonoidHom) ≠ ⊥ := by
        intro hb
        have h1 := he _ hK'M
        rw [hb, Subgroup.map_bot, heq] at h1
        apply hne
        refine s16c7_eq_of_subgroupOf_eq (barSub_mono ⊥ V hV hKjM) (bot_le) ?_
        rw [← h1, Subgroup.bot_subgroupOf]
      refine uc22p22d_mbarImage_ne D.M V hK' (uc22p20e_cComp_of_calC hKj) hne' hbot ?_
      apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      rw [he _ hK'M, he _ hKjM, heq]
    rcases himg with h | h
    · left
      exact key K₁ hK₁ hK₁M (by rw [hbar₁]; exact hH₁ne) (h.trans hbar₁.symm)
    · right
      exact key K₂ hK₂ hK₂M (by rw [hbar₂]; exact hH₂ne) (h.trans hbar₂.symm)
  have hmapself : ∀ (K : Subgroup G) (k : G), k ∈ K →
      K.map (MulAut.conj k).toMonoidHom = K := fun K k hk =>
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (Subgroup.le_normalizer hk)
  have hn₁ : K₁ ≤ normalizer (K₂ : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    show K₂.map (MulAut.conj k).toMonoidHom = K₂
    rcases hpermK k (hK₁M hk) K₂ hK₂ (Or.inr hbar₂) with h | h
    · exfalso
      apply hK₁₂
      have h2 : K₂.map (MulAut.conj k).toMonoidHom = K₁.map (MulAut.conj k).toMonoidHom := by
        rw [h, hmapself K₁ k hk]
      exact (Subgroup.map_injective (MulAut.conj k).injective h2).symm
    · exact h
  have hn₂ : K₂ ≤ normalizer (K₁ : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    show K₁.map (MulAut.conj k).toMonoidHom = K₁
    rcases hpermK k (hK₂M hk) K₁ hK₁ (Or.inl hbar₁) with h | h
    · exact h
    · exfalso
      apply hK₁₂
      have h2 : K₁.map (MulAut.conj k).toMonoidHom = K₂.map (MulAut.conj k).toMonoidHom := by
        rw [h, hmapself K₂ k hk]
      exact Subgroup.map_injective (MulAut.conj k).injective h2
  refine ⟨K₁, K₂, hK₁, hK₂, hK₁₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [s16c7_barSub_sup ⊥ V hV (hK₁M.trans hMs) (hK₂M.trans hMs), hbar₁, hbar₂, hsup]
  · intro m hm
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    show (K₁ ⊔ K₂).map (MulAut.conj m).toMonoidHom = K₁ ⊔ K₂
    rw [Subgroup.map_sup]
    have h1 := hpermK m hm K₁ hK₁ (Or.inl hbar₁)
    have h2 := hpermK m hm K₂ hK₂ (Or.inr hbar₂)
    have hne : K₁.map (MulAut.conj m).toMonoidHom ≠ K₂.map (MulAut.conj m).toMonoidHom :=
      fun h => hK₁₂ (Subgroup.map_injective (MulAut.conj m).injective h)
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact absurd (h1.trans h2.symm) hne
    · rw [h1, h2]
    · rw [h1, h2, sup_comm]
    · exact absurd (h1.trans h2.symm) hne
  · rw [hbar₁]
    exact hL₁
  · rw [hbar₂]
    exact hL₂
  · exact hn₁
  · exact hn₂

end Lift

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
