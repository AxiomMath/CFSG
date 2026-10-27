module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec7.FinalAux1
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec7.FinalAuxRemak

public section

open CFSG.Open CFSG.SignalizerFunctorTheorem.McBride
open scoped Pointwise

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Sec7S35

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

section Admits

omit [Finite G] in
theorem admits_of_le_centralizer {Q X : Subgroup G}
    (h : X ≤ Subgroup.centralizer (Q : Set G)) : Admits Q X :=
  (Subgroup.le_centralizer_iff.mpr h).trans (Subgroup.centralizer_le_normalizer _)

omit [Finite G] in
theorem admits_centralizer_of_le_centralizer {Q X : Subgroup G}
    (h : X ≤ Subgroup.centralizer (Q : Set G)) : Admits Q (Subgroup.centralizer (X : Set G)) :=
  fun q hq => Subgroup.le_normalizer (Subgroup.mem_centralizer_iff.mpr fun _ hx =>
    (Subgroup.mem_centralizer_iff.mp (h hx) q hq).symm)

omit [Finite G] in
theorem admits_dsub_of_le {X : Subgroup G} (hθ : NearFunctor p A θ) (h : X ≤ dsub A θ) :
    Admits A X :=
  admits_of_le_centralizer (h.trans (dsub_le_centralizer hθ))

omit [Finite G] in
theorem admits_sThree (hθ : NearFunctor p A θ) : Admits A (sThree p A θ) := by
  have hD1 : Admits A (dOne p A θ) :=
    admits_dsub_of_le hθ ((Subgroup.map_subtype_le _).trans (iSup₂_le fun _ _ => inf_le_left))
  have hD0 : Admits A (dZero p A θ) :=
    admits_dsub_of_le hθ (iSup₂_le fun _ _ => inf_le_left)
  have hS1 : Admits A (sOne p A θ) :=
    (Admits.iSup fun Y => Admits.iSup fun hY => hY.1.1 : Admits A (thetaN p A θ _)).inf
      (admits_centralizer_of_le_centralizer ((Subgroup.map_subtype_le _).trans
        ((iSup₂_le fun _ _ => inf_le_left : dZero p A θ ≤ dsub A θ).trans
          (dsub_le_centralizer hθ))))
  refine (Admits.iSup fun Y => Admits.iSup fun hY => hY.1.1 : Admits A (thetaN p A θ _)).inf
    (Thm36.admits_sectionCentralizer hS1 (hD0.sup hS1))

end Admits

section Family

abbrev Ff (p : ℕ) (A : Subgroup G) (θ : G → Subgroup G) (E L : Subgroup G) : Subgroup G :=
  L ⊓ sThree p A θ ⊓ thetaOf θ E

omit [Finite G] in
theorem cj_Ff (hθ : NearFunctor p A θ) {E : Subgroup G} (hE : E ≤ A) {a : G} (ha : a ∈ A)
    (L : Subgroup G) : cj a (Ff p A θ E L) = Ff p A θ E (cj a L) := by
  unfold Ff
  rw [cj_inf, cj_inf, cj_eq_of_mem_normalizer (admits_sThree hθ ha),
    cj_eq_of_mem_normalizer (hθ.isFunctor.normalizes_thetaOf hE ha)]

omit [Finite G] in
theorem Ff_le_left (E L : Subgroup G) : Ff p A θ E L ≤ L := inf_le_left.trans inf_le_left

theorem Data.Tsub_ne_bot {h : Counterexample p A θ} {E B : Subgroup G} (D : Data h E)
    (hS : Setting p A E B) {b : G} (hb : b ∈ B) (hbE : b ∉ E) :
    sThree p A θ ⊓ thetaOf θ B ≠ ⊥ := by
  obtain ⟨e⟩ := (D.decomp B hS.hB hS.hEB _ (hS.isDirectPair h hb hbE)).2
  have hd : dTwo p A θ ≠ ⊥ := fun hbot =>
    D.frob.1 (le_bot_iff.mp (hbot ▸ D.frob.2.1))
  have : Nontrivial ↥(dTwo p A θ) := (Subgroup.nontrivial_iff_ne_bot _).mpr hd
  have : Nonempty (Fin p) := ⟨⟨0, h.hyp.prime.pos⟩⟩
  obtain ⟨x, y, hxy⟩ := exists_pair_ne (Fin p → ↥(dTwo p A θ))
  have hne : e.symm x ≠ e.symm y := fun hh => hxy (e.symm.injective hh)
  have : Nontrivial ↥(sThree p A θ ⊓ thetaOf θ B) := ⟨⟨e.symm x, e.symm y, hne⟩⟩
  exact (Subgroup.nontrivial_iff_ne_bot _).mp this

theorem Data.isDirectProduct_Ff {h : Counterexample p A θ} {E B : Subgroup G} (D : Data h E)
    (hS : Setting p A E B) {b : G} (hb : b ∈ B) (hbE : b ∉ E) :
    IsDirectProduct {S | ∃ L ∈ lcal (θ b), S = Ff p A θ E L} (sThree p A θ ⊓ thetaOf θ B) := by
  have hθ := h.hyp.nearFunctor
  have := (D.decomp B hS.hB hS.hEB _ (hS.isDirectPair h hb hbE)).1
  rwa [hθ.isFunctor.thetaOf_zpowers (hS.mem_A hb) (ne_one_of_not_mem hbE)] at this

theorem Data.Ff_ne_bot
    {h : Counterexample p A θ} {E B : Subgroup G} (D : Data h E)
    (hS : Setting p A E B) {b : G} (hb : b ∈ B) (hbE : b ∉ E) {L : Subgroup G}
    (hL : L ∈ lcal (θ b)) : Ff p A θ E L ≠ ⊥ := by
  intro hbot
  have hθ := h.hyp.nearFunctor
  have hbA := hS.mem_A hb
  have hdp := D.isDirectProduct_Ff hS hb hbE
  have hall : ∀ L' ∈ lcal (θ b), Ff p A θ E L' = ⊥ := by
    intro L' hL'
    obtain ⟨a, ha, rfl⟩ := D.exists_cj_eq hbA hbE hL hL'
    rw [← cj_Ff hθ hS.hE.1 ha, hbot, cj_bot]
  refine D.Tsub_ne_bot hS hb hbE ?_
  rw [← hdp.sSup_eq]
  refine le_bot_iff.mp (sSup_le ?_)
  rintro S ⟨L', hL', rfl⟩
  exact (hall L' hL').le

theorem Data.Ff_injective
    {h : Counterexample p A θ} {E B : Subgroup G} (D : Data h E)
    (hS : Setting p A E B) {b : G} (hb : b ∈ B) (hbE : b ∉ E) :
    Function.Injective (fun L : ↥(lcal (θ b)) => Ff p A θ E L) := by
  intro L L' hLL'
  by_contra hne
  have hbA := hS.mem_A hb
  have hdisj := (D.isDirectProduct_lcal hbA hbE).indep.pairwiseDisjoint L.2 L'.2
    (fun e => hne (Subtype.ext e))
  have h1 : Ff p A θ E L ⊓ Ff p A θ E L' ≤ (L : Subgroup G) ⊓ (L' : Subgroup G) :=
    inf_le_inf (Ff_le_left E L) (Ff_le_left E L')
  have h2 : Ff p A θ E L ≤ ⊥ := by
    have : Ff p A θ E L ⊓ Ff p A θ E L' = Ff p A θ E L := by
      simp only at hLL'
      rw [← hLL', inf_idem]
    rw [← this]
    exact h1.trans (disjoint_iff.mp hdisj).le
  exact D.Ff_ne_bot hS hb hbE L.2 (le_bot_iff.mp h2)

theorem Data.isIDP_Ff
    {h : Counterexample p A θ} {E B : Subgroup G} (D : Data h E)
    (hS : Setting p A E B) {b : G} (hb : b ∈ B) (hbE : b ∉ E) :
    IsIDP (fun L : ↥(lcal (θ b)) => Ff p A θ E L) (sThree p A θ ⊓ thetaOf θ B) := by
  refine IsIDP.of_isDirectProduct_range ?_ (D.Ff_injective hS hb hbE)
  have := D.isDirectProduct_Ff hS hb hbE
  convert this using 2
  ext S
  constructor
  · rintro ⟨L, rfl⟩
    exact ⟨L, L.2, rfl⟩
  · rintro ⟨L, hL, rfl⟩
    exact ⟨⟨L, hL⟩, rfl⟩

theorem Data.exists_Y
    {h : Counterexample p A θ} {E B : Subgroup G} (D : Data h E)
    (hS : Setting p A E B) :
    ∃ Y : Fin p → Subgroup G, ∀ b ∈ B, b ∉ E →
      ∃ e : ↥(lcal (θ b)) ≃ Fin p, ∀ L : ↥(lcal (θ b)), Ff p A θ E L = Y (e L) := by
  obtain ⟨b₀, hb₀, hb₀E⟩ := hS.exists_mem_not_mem h
  obtain ⟨φ⟩ := (D.decomp B hS.hB hS.hEB _ (hS.isDirectPair h hb₀ hb₀E)).2
  have hfp := frobenius_props D.frob
  have := hfp.1
  let Φ : (Fin p → ↥(dTwo p A θ)) →* G :=
    (sThree p A θ ⊓ thetaOf θ B).subtype.comp φ.symm.toMonoidHom
  have hΦ : Function.Injective Φ := Subtype.val_injective.comp φ.symm.injective
  have hrange : Φ.range = sThree p A θ ⊓ thetaOf θ B := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr φ.symm.surjective,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  refine ⟨fun k => (coordSub (Fin p) _ k).map Φ, fun b hb hbE => ?_⟩
  obtain ⟨e, he⟩ := exists_equiv_coordSub hfp.2.1 hfp.2.2 Φ hΦ hrange
    (fun L : ↥(lcal (θ b)) => Ff p A θ E L) (D.isIDP_Ff hS hb hbE)
    (fun L => D.Ff_ne_bot hS hb hbE L.2) (by rw [D.card_lcal hS hb hbE, Fintype.card_fin])
  exact ⟨e, he⟩

structure Decomp (p : ℕ) (A : Subgroup G) (θ : G → Subgroup G) (E B : Subgroup G)
    (Y : Fin p → Subgroup G) : Prop where
  isIDP : IsIDP Y (sThree p A θ ⊓ thetaOf θ B)
  ne_bot : ∀ i, Y i ≠ ⊥
  perm : ∀ a ∈ A, ∀ i, ∃ j, cj a (Y i) = Y j
  trans : ∀ i j, ∃ a ∈ A, cj a (Y i) = Y j
  fixed : ∀ β ∈ B, ∀ i, cj β (Y i) = Y i
  stab : ∀ a ∈ A, ∀ i, cj a (Y i) = Y i → a ∈ B
  comp : ∀ b ∈ B, b ∉ E → ∃ e : ↥(lcal (θ b)) ≃ Fin p,
    ∀ L : ↥(lcal (θ b)), Ff p A θ E L = Y (e L)

theorem Data.exists_decomp
    {h : Counterexample p A θ} {E B : Subgroup G} (D : Data h E)
    (hS : Setting p A E B) : ∃ Y : Fin p → Subgroup G, Decomp p A θ E B Y := by
  have hθ := h.hyp.nearFunctor
  obtain ⟨Y, hY⟩ := D.exists_Y hS
  obtain ⟨b₀, hb₀, hb₀E⟩ := hS.exists_mem_not_mem h
  have hb₀A := hS.mem_A hb₀
  have hb₁ := ne_one_of_not_mem hb₀E
  obtain ⟨e, he⟩ := hY b₀ hb₀ hb₀E
  have hYe : ∀ j, Y j = Ff p A θ E (e.symm j) := fun j => by
    rw [he (e.symm j), Equiv.apply_symm_apply]
  have hcj : ∀ a (ha : a ∈ A) (L : ↥(lcal (θ b₀))), cj a (Ff p A θ E L) =
      Y (e ⟨cj a L, map_conj_mem_lcal_apply hθ hb₀A hb₁ L.2 ha⟩) := fun a ha L => by
    rw [cj_Ff hθ hS.hE.1 ha]
    exact he ⟨cj a L, map_conj_mem_lcal_apply hθ hb₀A hb₁ L.2 ha⟩
  refine ⟨Y, ?_, ?_, ?_, ?_, ?_, ?_, hY⟩
  · have := (D.isIDP_Ff hS hb₀ hb₀E).comp e.symm
    convert this using 1
    funext j
    exact hYe j
  · intro i
    rw [hYe]
    exact D.Ff_ne_bot hS hb₀ hb₀E (e.symm i).2
  · intro a ha i
    refine ⟨e ⟨cj a (e.symm i), map_conj_mem_lcal_apply hθ hb₀A hb₁ (e.symm i).2 ha⟩, ?_⟩
    rw [hYe i, hcj a ha]
  · intro i j
    obtain ⟨a, ha, hLL⟩ := D.exists_cj_eq hb₀A hb₀E (e.symm i).2 (e.symm j).2
    refine ⟨a, ha, ?_⟩
    rw [hYe, hYe, cj_Ff hθ hS.hE.1 ha, ← hLL]
  · intro β hβ i
    rw [hYe, cj_Ff hθ hS.hE.1 (hS.hB.1 hβ),
      cj_eq_of_mem_normalizer (D.B_le_normalizer_lcal hS hb₀ hb₀E (e.symm i).2 hβ)]
  · intro a ha i hai
    rw [hYe, cj_Ff hθ hS.hE.1 ha] at hai
    have hmem := map_conj_mem_lcal_apply hθ hb₀A hb₁ (e.symm i).2 ha
    have hinj := D.Ff_injective hS hb₀ hb₀E (a₁ := ⟨cj a (e.symm i), hmem⟩) (a₂ := e.symm i) hai
    have hfix : cj a (e.symm i : Subgroup G) = e.symm i := congrArg Subtype.val hinj
    rw [← D.inf_normalizer_lcal hS hb₀ hb₀E (e.symm i).2]
    exact ⟨ha, Subgroup.mem_normalizer_iff_map_conj_eq.mpr hfix⟩

end Family

end CFSG.SignalizerFunctorTheorem.McBride.Near.Sec7S35
