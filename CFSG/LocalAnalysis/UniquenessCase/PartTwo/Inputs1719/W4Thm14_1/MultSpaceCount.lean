module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_1.MultSpaceSemisimple
public import CFSG.Quasithin.Background.HPair
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.MultSpace

open CFSG.Quasithin CFSG.LocalAnalysis.WeakClosure81

variable {W : Type} [CommGroup W]

private theorem rk_sup_of_disjoint [Finite W] {A B : Subgroup W} (h : A ⊓ B = ⊥) :
    rk ↥(A ⊔ B) = rk ↥A + rk ↥B := by
  have h1 := rk_sup_add_rk_inf A B
  rw [h, rk_bot] at h1
  omega

private theorem rk_inf_fixV_sup_of_disjoint [Finite W] {X : Subgroup (MulAut W)}
    {A B : Subgroup W} (hA : StableUnder X A) (hB : StableUnder X B) (h : A ⊓ B = ⊥) :
    rk ↥((A ⊔ B) ⊓ fixV X) = rk ↥(A ⊓ fixV X) + rk ↥(B ⊓ fixV X) := by
  have hcard := card_inf_fixV_sup hA hB h
  unfold rk
  rw [hcard, padicValNat.mul (Nat.card_pos.ne') (Nat.card_pos.ne')]

private theorem rk_eq_of_isoMod {L : Subgroup (MulAut W)} {J I : Subgroup W}
    (h : CFSG.Quasithin.H.Pair.IsoMod L J I) : rk ↥J = rk ↥I := by
  obtain ⟨e, _⟩ := h
  unfold rk
  exact congrArg (padicValNat 2) (Nat.card_congr e.toEquiv)

private theorem card_inf_fixV_eq_of_isoMod [Finite W] {L : Subgroup (MulAut W)}
    {J I : Subgroup W} (hJ : StableUnder L J)
    (hIso : CFSG.Quasithin.H.Pair.IsoMod L J I) {X : Subgroup (MulAut W)} (hX : X ≤ L) :
    Nat.card ↥(J ⊓ fixV X) = Nat.card ↥(I ⊓ fixV X) := by
  obtain ⟨e, he⟩ := hIso
  let f : ↥(J ⊓ fixV X) → ↥(I ⊓ fixV X) := fun j =>
    ⟨e ⟨(j : W), j.2.1⟩, (e ⟨(j : W), j.2.1⟩).2, by
      intro x hx
      have hxj : x (j : W) = (j : W) := mem_fixV.mp j.2.2 x hx
      have hxJ : x (j : W) ∈ J := by rw [hxj]; exact j.2.1
      have h := he x (hX hx) ⟨(j : W), j.2.1⟩ hxJ
      have hw : (⟨x (j : W), hxJ⟩ : J) = ⟨(j : W), j.2.1⟩ := Subtype.ext hxj
      rw [hw] at h
      exact h.symm⟩
  have hfinj : Function.Injective f := by
    intro a b hab
    have h1 : (e ⟨(a : W), a.2.1⟩ : W) = (e ⟨(b : W), b.2.1⟩ : W) :=
      congrArg (fun z : ↥(I ⊓ fixV X) => (z : W)) hab
    have h2 : (⟨(a : W), a.2.1⟩ : J) = ⟨(b : W), b.2.1⟩ :=
      e.injective (Subtype.ext h1)
    exact Subtype.ext (congrArg (fun z : J => (z : W)) h2)
  have hfsurj : Function.Surjective f := by
    intro i
    let j : J := e.symm ⟨(i : W), i.2.1⟩
    have hxj : ∀ x ∈ X, x (j : W) = (j : W) := by
      intro x hx
      have hxjJ : x (j : W) ∈ J := hJ x (hX hx) (j : W) j.2
      have h := he x (hX hx) j hxjJ
      have hej : (e j : W) = (i : W) := by
        dsimp [j]
        exact congrArg (fun z : I => (z : W)) (e.apply_symm_apply ⟨(i : W), i.2.1⟩)
      have hxi : x (i : W) = (i : W) := mem_fixV.mp i.2.2 x hx
      have h2 : (e ⟨x (j : W), hxjJ⟩ : W) = (e j : W) := by
        rw [h, hej, hxi]
      exact Subtype.ext_iff.mp (e.injective (Subtype.ext h2))
    refine ⟨⟨(j : W), j.2, hxj⟩, ?_⟩
    apply Subtype.ext
    dsimp [f, j]
    exact congrArg (fun z : I => (z : W)) (e.apply_symm_apply ⟨(i : W), i.2.1⟩)
  exact Nat.card_congr (Equiv.ofBijective f ⟨hfinj, hfsurj⟩)

theorem exists_invariant_compl_lt [Finite W] {L : Subgroup (MulAut W)}
    (hfix : fixV L = ⊥) (hspan : (⨆ I ∈ irrSet L, I) = ⊤) {T : Subgroup W}
    (hT : StableUnder L T) (hTbot : T ≠ ⊥) {n : ℕ} (hcard : Nat.card T = n) :
    ∃ (I D : Subgroup W), I ∈ irrSet L ∧ I ≤ T ∧ D ≤ T ∧ StableUnder L D ∧
      I ⊓ D = ⊥ ∧ I ⊔ D = T ∧ Nat.card D < n := by
  obtain ⟨I, hI, hIle⟩ := exists_mem_irrSet_le hfix hT hTbot
  have hIstab : StableUnder L I := stableUnder_of_mem_irrSet hI
  have hIbot : I ≠ ⊥ := ne_bot_of_mem_irrSet hI
  obtain ⟨D, hDle, hDstab, hIDbot, hIDsup⟩ :=
    exists_stableUnder_compl_le hfix hspan hIstab hT hIle
  have hDne : D ≠ T := by
    intro hDT
    apply hIbot
    rw [eq_bot_iff]
    intro x hx
    have hxD : x ∈ D := by rw [hDT]; exact hIle hx
    have hxbot : x ∈ I ⊓ D := ⟨hx, hxD⟩
    rw [hIDbot] at hxbot
    exact hxbot
  have hDltT : Nat.card D < Nat.card T := by
    have hssub : (D : Set W) ⊂ (T : Set W) := by
      refine ⟨SetLike.coe_subset_coe.mpr hDle, ?_⟩
      intro hTD
      exact hDne (le_antisymm hDle (SetLike.coe_subset_coe.mp hTD))
    simpa [Nat.card_coe_set_eq] using
      (Set.Finite.card_lt_card (Set.toFinite (T : Set W)) hssub)
  exact ⟨I, D, hI, hIle, hDle, hDstab, hIDbot, hIDsup, by rw [← hcard]; exact hDltT⟩

theorem rk_inf_fixV_mul_rk [Finite W] {L : Subgroup (MulAut W)} (hfix : fixV L = ⊥)
    (hspan : (⨆ I ∈ irrSet L, I) = ⊤) {J : Subgroup W} (hJ : StableUnder L J)
    (hhom : ∀ I ∈ irrSet L, CFSG.Quasithin.H.Pair.IsoMod L J I) {X : Subgroup (MulAut W)}
    (hX : X ≤ L) {S : Subgroup W} (hS : StableUnder L S) :
    rk ↥(S ⊓ fixV X) * rk ↥J = rk ↥(J ⊓ fixV X) * rk ↥S := by
  suffices h : ∀ n, ∀ T : Subgroup W, Nat.card T = n → StableUnder L T →
      rk ↥(T ⊓ fixV X) * rk ↥J = rk ↥(J ⊓ fixV X) * rk ↥T by
    exact h (Nat.card S) S rfl hS
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro T hcard hT
    by_cases hTbot : T = ⊥
    · rw [hTbot]
      rw [bot_inf_eq, rk_bot]
      simp
    · obtain ⟨I, D, hI, _, _, hDstab, hIDbot, hIDsup, hDlt⟩ :=
        exists_invariant_compl_lt hfix hspan hT hTbot hcard
      have hIstab : StableUnder L I := stableUnder_of_mem_irrSet hI
      have hXistab : StableUnder X I := fun x hx i hi => hIstab x (hX hx) i hi
      have hXdstab : StableUnder X D := fun x hx d hd => hDstab x (hX hx) d hd
      have hTfixrank : rk ↥(T ⊓ fixV X) =
          rk ↥(I ⊓ fixV X) + rk ↥(D ⊓ fixV X) := by
        rw [← hIDsup]
        exact rk_inf_fixV_sup_of_disjoint hXistab hXdstab hIDbot
      have hTrank : rk ↥T = rk ↥I + rk ↥D := by
        rw [← hIDsup]
        exact rk_sup_of_disjoint hIDbot
      have hIso := hhom I hI
      have hJrk : rk ↥J = rk ↥I := rk_eq_of_isoMod hIso
      have hIfix : Nat.card ↥(J ⊓ fixV X) = Nat.card ↥(I ⊓ fixV X) :=
        card_inf_fixV_eq_of_isoMod hJ hIso hX
      have hIfix_rk : rk ↥(I ⊓ fixV X) = rk ↥(J ⊓ fixV X) := by
        unfold rk
        rw [← hIfix]
      have hDih := ih (Nat.card D) hDlt D rfl hDstab
      have hTrank' : rk ↥T = rk ↥J + rk ↥D := by
        rw [hTrank, ← hJrk]
      calc
        rk ↥(T ⊓ fixV X) * rk ↥J
            = (rk ↥(I ⊓ fixV X) + rk ↥(D ⊓ fixV X)) * rk ↥J := by rw [hTfixrank]
        _ = rk ↥(I ⊓ fixV X) * rk ↥J + rk ↥(D ⊓ fixV X) * rk ↥J := by ring
        _ = rk ↥(I ⊓ fixV X) * rk ↥J + rk ↥(J ⊓ fixV X) * rk ↥D := by rw [hDih]
        _ = rk ↥(J ⊓ fixV X) * rk ↥J + rk ↥(J ⊓ fixV X) * rk ↥D := by rw [hIfix_rk]
        _ = rk ↥(J ⊓ fixV X) * (rk ↥J + rk ↥D) := by ring
        _ = rk ↥(J ⊓ fixV X) * rk ↥T := by rw [hTrank']

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.MultSpace
