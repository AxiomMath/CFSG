module

public import CFSG.Quasithin.EmptyFaithful.S151cFDec

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

section Six151c

variable {V : Type*} [CommGroup V] [Finite V] {X Tb Xc : Subgroup (MulAut V)}

@[expose] def Shape6 {W : Type*} [CommGroup W] [Finite W] (Y : Subgroup (MulAut W)) (r : ℚ) :
    Prop :=
  IsElemAbelian 3 (fittingOf Y) ∧ Nat.card (fittingOf Y) = 27 ∧
    (∃ A : Subgroup (MulAut W), A ≤ Y ∧ IsElemAbelian2 A ∧ Nat.card A = 4 ∧
      Y = fittingOf Y ⊔ A) ∧ rk W = 6 ∧ r = 3 / 2

open Classical in
theorem not_isCyclic_fittingOf_block (h : Setting151c X Tb Xc) {I : Finset (Subgroup (MulAut V))}
    (hI : IsBlocks216 (Jhat X) I) {L : Subgroup (MulAut V)} (hL : L ∈ I)
    (hnc : ¬ IsCyclic ↥(fittingOf (autSub L (commV L)))) : ¬ IsCyclic ↥(fittingOf L) := by
  intro hcyc
  have hs := suppData_block h hI hL
  have hmem : ∀ g : ↥(fittingOf L), resHom (commV L) ⟨(g : MulAut V), hs.stab (fittingOf_le L g.2)⟩ ∈
      fittingOf (autSub L (commV L)) := fun g =>
    fittingOf_autSub_le hs.stab (mem_autSub.mpr ⟨⟨g, hs.stab (fittingOf_le L g.2)⟩, g.2, rfl⟩)
  let f : ↥(fittingOf L) →* ↥(fittingOf (autSub L (commV L))) :=
    { toFun := fun g => ⟨resHom (commV L) ⟨(g : MulAut V), hs.stab (fittingOf_le L g.2)⟩, hmem g⟩
      map_one' := Subtype.ext (by
        have : (⟨((1 : ↥(fittingOf L)) : MulAut V),
            hs.stab (fittingOf_le L (1 : ↥(fittingOf L)).2)⟩ : stabSub (commV L)) = 1 := rfl
        simp only [this, map_one]
        rfl)
      map_mul' := fun a b => Subtype.ext (by
        have : (⟨((a * b : ↥(fittingOf L)) : MulAut V),
            hs.stab (fittingOf_le L (a * b : ↥(fittingOf L)).2)⟩ : stabSub (commV L)) =
            ⟨(a : MulAut V), hs.stab (fittingOf_le L a.2)⟩ *
              ⟨(b : MulAut V), hs.stab (fittingOf_le L b.2)⟩ := rfl
        simp only [this, map_mul]
        rfl) }
  have hsurj : Function.Surjective f := by
    rintro ⟨ψ, hψ⟩
    have hψ' : ψ ∈ autSub (fittingOf L) (commV L) := by rw [hs.autSub_fittingOf]; exact hψ
    obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hψ'
    exact ⟨⟨(g : MulAut V), hg⟩, rfl⟩
  exact hnc (isCyclic_of_surjective f hsurj)

open Classical in
theorem block_normalized_of_noncyclic (h : Setting151c X Tb Xc) {r : ℚ}
    (hr : qhatOf X = (r : WithTop ℚ)) (hr2 : r ≤ 2) {I : Finset (Subgroup (MulAut V))}
    (hI : IsBlocks216 (Jhat X) I) {L : Subgroup (MulAut V)} (hL : L ∈ I)
    (hnc : ¬ IsCyclic ↥(fittingOf L)) : ∀ x ∈ X, conjBy x L = L := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x, hx, hne⟩ := hcon
  obtain ⟨L₂, hL₂, hne₂, ⟨x₂, hx₂, e₂⟩, -⟩ := orbit_le_two h hr hr2 hI hL ⟨x, hx, hne⟩
  exact hnc (orbit_two_fitting_cyclic h hr hr2 hI hL hL₂ (Ne.symm hne₂) e₂.symm)

omit [Finite V] in
theorem conj_resHom_mem_autSub {L : Subgroup (MulAut V)} {U : Subgroup V} (hX : X ≤ stabSub U)
    (hLX : L ≤ X) (hL : NormalIn X L) {x : MulAut V} (hx : x ∈ X) {y : MulAut U}
    (hy : y ∈ autSub L U) :
    resHom U ⟨x, hX hx⟩ * y * (resHom U ⟨x, hX hx⟩)⁻¹ ∈ autSub L U := by
  obtain ⟨l, hl, rfl⟩ := mem_autSub.mp hy
  have hxl : x * (l : MulAut V) * x⁻¹ ∈ L := hL x hx l hl
  have hxlX : x * (l : MulAut V) * x⁻¹ ∈ stabSub U :=
    hX (X.mul_mem (X.mul_mem hx (hLX hl)) (X.inv_mem hx))
  refine mem_autSub.mpr ⟨⟨x * l * x⁻¹, hxlX⟩, hxl, ?_⟩
  rw [← map_inv, ← map_mul, ← map_mul]
  rfl

omit [Finite V] in
theorem resHom_mem_normalizer_autSub {L : Subgroup (MulAut V)} {U : Subgroup V}
    (hX : X ≤ stabSub U) (hLX : L ≤ X) (hL : NormalIn X L) {x : MulAut V} (hx : x ∈ X) :
    resHom U ⟨x, hX hx⟩ ∈ Subgroup.normalizer (autSub L U : Set (MulAut U)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => conj_resHom_mem_autSub hX hLX hL hx hy, fun hy => ?_⟩
  have := conj_resHom_mem_autSub hX hLX hL (X.inv_mem hx) hy
  have e : resHom U ⟨x⁻¹, hX (X.inv_mem hx)⟩ = (resHom U ⟨x, hX hx⟩)⁻¹ := by
    rw [← map_inv]
    rfl
  rw [e] at this
  simpa [mul_assoc] using this

open Classical in
theorem block_not_shape_six (h : Setting151c X Tb Xc) {r : ℚ}
    (hr : qhatOf X = (r : WithTop ℚ)) (hr2 : r ≤ 2) {I : Finset (Subgroup (MulAut V))}
    (hI : IsBlocks216 (Jhat X) I) {L : Subgroup (MulAut V)} (hL : L ∈ I)
    (h6 : Shape6 (autSub L (commV L)) r) : False := by
  have hs := suppData_block h hI hL
  have hH := block_d217hyp h hr hr2 hI hL
  have hsyl := (block_d217 h hr hr2 hI hL).1
  have hUsq : ∀ v : ↥(commV L), v ^ 2 = 1 := fun v => Subtype.ext (h.sq v)
  have hLX : L ≤ X := (block_le_J hI hL).trans (Jhat_le X)
  obtain ⟨hE, hF27, ⟨A', hA'X, hA'2, hA'4, hXeq⟩, -, -⟩ := h6
  have hnorm : A' ≤ Subgroup.normalizer (fittingOf (autSub L (commV L)) : Set (MulAut ↥(commV L))) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => conj_mem_fittingOf (hA'X ha) hy, fun hy => ?_⟩
    have := conj_mem_fittingOf (Subgroup.inv_mem _ (hA'X ha)) hy
    simpa [mul_assoc] using this
  have hinf : fittingOf (autSub L (commV L)) ⊓ A' = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
    have h3 : x ^ 3 = 1 := hE.2 x hx.1
    have h2 : x ^ 2 = 1 := hA'2.2 x hx.2
    calc x = x ^ 3 * (x ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3, h2]; group
  have hcard := card_sup_of_normalizes hnorm hinf
  rw [← hXeq, hF27, hA'4] at hcard
  have hA'mem : A' ∈ QhatStar (autSub L (commV L)) := by
    rw [hsyl]
    exact mem_sylow2Of_of_card hA'X hA'2.isPGroup (m := 27) ⟨13, rfl⟩ (by rw [hcard, hA'4])
  have hrk : 1 < rk A' := by
    have h1 := card_eq_two_pow_of_isPGroup hA'2.isPGroup
    rw [hA'4] at h1
    have h2 : 2 ^ rk A' = 2 ^ 2 := by omega
    have := Nat.pow_right_injective (le_refl 2) h2
    omega
  obtain ⟨-, hFp, -, -, -, hW, hcases⟩ := d217_noncyclic_structure hUsq hH hA'mem hrk
  rcases hcases with ⟨Pi, d, hrg, hc9⟩ | ⟨Pi, d, hrg, hc27⟩
  · omega
  ·
    have hnc' : ¬ IsCyclic ↥(fittingOf (autSub L (commV L))) := by
      intro hcyc
      obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥(fittingOf (autSub L (commV L))))
      have h3 : g ^ 3 = 1 := Subtype.ext (hE.2 (g : MulAut ↥(commV L)) g.2)
      have : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one h3
      rw [hg, hF27] at this
      omega
    have hLnorm : ∀ x ∈ X, conjBy x L = L :=
      block_normalized_of_noncyclic h hr hr2 hI hL (not_isCyclic_fittingOf_block h hI hL hnc')
    have hLn : NormalIn X L := fun x hx k hk => by
      have := mem_conjBy_of_mem (g := x) hk
      rwa [hLnorm x hx] at this
    have hUinv : ∀ x ∈ X, ∀ u ∈ commV L, x u ∈ commV L := fun x hx u hu => hLn.commV_invariant hx hu
    have hUS := h.uStar hUinv
    have hXs : X ≤ stabSub (commV L) := le_stabSub_of_invariant hUinv
    have hfd : FDec (autSub L (commV L)) Pi :=
      { mem := fun i => ⟨by rw [hFp]; exact d.le_P i, by simpa using d.card_eq i,
          by simpa using d.rk_eq i⟩
        vindep := d.vindep
        vsup := iSup_commV_eq_top hUsq d hW
        triv := d.triv }
    have hperm : ∀ τ ∈ autSub Tb (commV L), ∀ i, ∃ j, conjBy τ (Pi i) = Pi j := by
      intro τ hτ i
      obtain ⟨t, htT, rfl⟩ := mem_autSub.mp hτ
      have hnormτ := resHom_mem_normalizer_autSub hXs hLX hLn (h.syl.1 htT)
      have hPi : Pi i ∈ Pfam (autSub L (commV L)) := hrg ▸ ⟨i, rfl⟩
      have := Pfam_conj_of_mem_normalizer hnormτ hPi
      rw [← hrg] at this
      obtain ⟨j, hj⟩ := this
      exact ⟨j, hj.symm⟩
    have hPiX : ∀ i, Pi i ≤ autSub X (commV L) := fun i =>
      (d.le_P i).trans ((pCoreOf_le 3 _).trans (autSub_mono hLX _))
    exact hfd.false_of_three hUsq hUS hPiX hperm

end Six151c

end CFSG.Quasithin
