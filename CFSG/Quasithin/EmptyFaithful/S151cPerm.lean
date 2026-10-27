module

public import CFSG.Quasithin.EmptyFaithful.S151cBlk

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

section Perm151c

variable {V : Type*} [CommGroup V] [Finite V] {X Tb Xc : Subgroup (MulAut V)}

theorem exists_conjBy_of_mem_sylow2Of {Y A B : Subgroup (MulAut V)} (hA : A ∈ sylow2Of Y)
    (hB : B ∈ sylow2Of Y) : ∃ g ∈ Y, B = conjBy g A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₁, hP₁⟩ := exists_sylow_of_mem_sylow2Of hA
  obtain ⟨P₂, hP₂⟩ := exists_sylow_of_mem_sylow2Of hB
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥Y) P₁ P₂
  have hgS : (g • P₁ : Sylow 2 ↥Y) = P₂ := hg
  have h1 : ((g • P₁ : Sylow 2 ↥Y) : Subgroup ↥Y) =
      (P₁ : Subgroup ↥Y).map (MulAut.conj g).toMonoidHom := rfl
  have h2 : (B.subgroupOf Y) = ((A.subgroupOf Y).map (MulAut.conj g).toMonoidHom) := by
    rw [← hP₂, ← hgS, h1, hP₁]
  refine ⟨(g : MulAut V), g.2, ?_⟩
  ext x
  constructor
  · intro hx
    have hxY : x ∈ Y := hB.1 hx
    have : (⟨x, hxY⟩ : ↥Y) ∈ B.subgroupOf Y := hx
    rw [h2] at this
    obtain ⟨y, hy, hyx⟩ := this
    refine ⟨(y : MulAut V), hy, ?_⟩
    have := congrArg Subtype.val hyx
    simpa [MulAut.conj_apply] using this
  · rintro ⟨y, hy, rfl⟩
    have hyY : y ∈ Y := hA.1 hy
    have : (⟨y, hyY⟩ : ↥Y) ∈ A.subgroupOf Y := hy
    have h3 : (MulAut.conj g) ⟨y, hyY⟩ ∈ B.subgroupOf Y := by
      rw [h2]
      exact ⟨_, this, rfl⟩
    exact h3

open Classical in
theorem block_le_J {I : Finset (Subgroup (MulAut V))} (hI : IsBlocks216 (Jhat X) I)
    {L : Subgroup (MulAut V)} (hL : L ∈ I) : L ≤ Jhat X :=
  hI.sup_eq ▸ le_iSup₂ (f := fun L' (_ : L' ∈ I) => L') L hL

open Classical in
theorem block_normalizer {I : Finset (Subgroup (MulAut V))} (hI : IsBlocks216 (Jhat X) I)
    {L : Subgroup (MulAut V)} (hL : L ∈ I) : Jhat X ≤ Subgroup.normalizer (L : Set (MulAut V)) := by
  rw [hI.sup_eq]
  refine iSup₂_le fun L' hL' => ?_
  by_cases hLL : L' = L
  · rw [hLL]; exact Subgroup.le_normalizer
  · refine le_trans ?_ (Subgroup.centralizer_le_normalizer (s := (L : Set (MulAut V))))
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (hI.comm L' hL' L hL hLL g hg x hx).symm

open Classical in
theorem block_inf_eq_bot {I : Finset (Subgroup (MulAut V))} (hI : IsBlocks216 (Jhat X) I)
    {L L' : Subgroup (MulAut V)} (hL : L ∈ I) (hL' : L' ∈ I) (hne : L ≠ L') : L ⊓ L' = ⊥ := by
  have h1 := hI.indep L hL
  refine le_bot_iff.mp ?_
  rw [← h1]
  exact inf_le_inf_left _ (le_iSup₂ (f := fun L'' (_ : L'' ∈ I.erase L) => L'') L'
    (Finset.mem_erase.mpr ⟨Ne.symm hne, hL'⟩))

open Classical in
theorem block_eq_of_le {I : Finset (Subgroup (MulAut V))} (hI : IsBlocks216 (Jhat X) I)
    {L L' : Subgroup (MulAut V)} (hL : L ∈ I) (hL' : L' ∈ I) (hle : L ≤ L') : L = L' := by
  by_contra hne
  have := block_inf_eq_bot hI hL hL' hne
  rw [inf_eq_left.mpr hle] at this
  exact hI.ne_bot L hL this

open Classical in
theorem block_qstar_nonempty {I : Finset (Subgroup (MulAut V))} (hI : IsBlocks216 (Jhat X) I)
    {L : Subgroup (MulAut V)} (hL : L ∈ I) : (QhatStar L).Nonempty := by
  by_contra hcon
  rw [Set.not_nonempty_iff_eq_empty] at hcon
  apply hI.ne_bot L hL
  have := (hI.indec L hL).1
  rw [this]
  unfold Jhat
  rw [hcon]
  simp

open Classical in
theorem block_qstar_eq_sylow (h : Setting151c X Tb Xc) {r : ℚ} (hr : qhatOf X = (r : WithTop ℚ))
    (hr2 : r ≤ 2) {I : Finset (Subgroup (MulAut V))} (hI : IsBlocks216 (Jhat X) I)
    {L : Subgroup (MulAut V)} (hL : L ∈ I) : QhatStar L = sylow2Of L := by
  have hs := suppData_block h hI hL
  have hd := (block_d217 h hr hr2 hI hL).1
  refine qhatStar_eq_sylow2Of (block_qstar_nonempty hI hL) fun A hA => ?_
  have hAL : A ≤ L := le_of_mem_QhatStar216 hA
  have hA' : autSub A (commV L) ∈ QhatStar (autSub L (commV L)) :=
    (hs.mem_QhatStar_iff hAL).mpr hA
  rw [hd] at hA'
  refine ⟨hAL, isPGroup_of_mem_QhatStar_aux hA, ?_⟩
  have := hA'.2.2
  rwa [hs.index_autSub hAL] at this

open Classical in
theorem block_conj_le (h : Setting151c X Tb Xc) {r : ℚ} (hr : qhatOf X = (r : WithTop ℚ))
    (hr2 : r ≤ 2) {I : Finset (Subgroup (MulAut V))} (hI : IsBlocks216 (Jhat X) I)
    {L : Subgroup (MulAut V)} (hL : L ∈ I) {x : MulAut V} (hx : x ∈ X) :
    ∃ L' ∈ I, conjBy x L ≤ L' := by
  have hsyl := block_qstar_eq_sylow h hr hr2 hI hL
  obtain ⟨A₀, hA₀⟩ := block_qstar_nonempty hI hL
  have hqs := (block_qhat hr hr2 hI hL).1
  have hA₀X : A₀ ∈ QhatStar X := by
    have : A₀ ∈ {A | A ∈ QhatStar X ∧ A ≤ L} := hqs ▸ hA₀
    exact this.1
  have hcov : ∀ A ∈ QhatStar X, ∃ L' ∈ I, A ≤ L' := by
    intro A hA
    rw [← QhatStar_Jhat hr hr2] at hA
    exact hI.cover A hA
  obtain ⟨L', hL', hA₀L'⟩ := hcov (conjBy x A₀) (conjBy_mem_QhatStar hA₀X hx)
  refine ⟨L', hL', ?_⟩
  have hLle : L ≤ L'.comap (MulAut.conj x).toMonoidHom := by
    calc L = Jhat L := (hI.indec L hL).1
      _ ≤ L'.comap (MulAut.conj x).toMonoidHom := by
        refine iSup₂_le fun A hA a ha => ?_
        obtain ⟨g, hgL, hAg⟩ := exists_conjBy_of_mem_sylow2Of (hsyl ▸ hA₀ : A₀ ∈ sylow2Of L)
          (hsyl ▸ hA : A ∈ sylow2Of L)
        have hj : x * g * x⁻¹ ∈ Jhat X := Jhat_conj_mem hx (block_le_J hI hL hgL)
        have hnorm : conjBy (x * g * x⁻¹) L' = L' :=
          conjBy_eq_of_mem_normalizer (block_normalizer hI hL' hj)
        have hxA : conjBy x A ≤ L' := by
          have e : conjBy x A = conjBy (x * g * x⁻¹) (conjBy x A₀) := by
            rw [hAg, conjBy_conjBy, conjBy_conjBy]
            congr 1
            group
          rw [e]
          calc conjBy (x * g * x⁻¹) (conjBy x A₀) ≤ conjBy (x * g * x⁻¹) L' :=
                conjBy_mono hA₀L'
            _ = L' := hnorm
        exact hxA (mem_conjBy_of_mem ha)
  exact Subgroup.map_le_iff_le_comap.mpr hLle

open Classical in
theorem block_conj_mem (h : Setting151c X Tb Xc) {r : ℚ} (hr : qhatOf X = (r : WithTop ℚ))
    (hr2 : r ≤ 2) {I : Finset (Subgroup (MulAut V))} (hI : IsBlocks216 (Jhat X) I)
    {L : Subgroup (MulAut V)} (hL : L ∈ I) {x : MulAut V} (hx : x ∈ X) : conjBy x L ∈ I := by
  obtain ⟨L', hL', h1⟩ := block_conj_le h hr hr2 hI hL hx
  obtain ⟨L'', hL'', h2⟩ := block_conj_le h hr hr2 hI hL' (X.inv_mem hx)
  have h3 : L ≤ L'' := by
    calc L = conjBy x⁻¹ (conjBy x L) := by rw [conjBy_conjBy, inv_mul_cancel, conjBy_one]
      _ ≤ conjBy x⁻¹ L' := conjBy_mono h1
      _ ≤ L'' := h2
  have h4 : L = L'' := block_eq_of_le hI hL hL'' h3
  have h5 : conjBy x⁻¹ L' ≤ L := h4 ▸ h2
  have h6 : L' ≤ conjBy x L := by
    calc L' = conjBy x (conjBy x⁻¹ L') := by rw [conjBy_conjBy, mul_inv_cancel, conjBy_one]
      _ ≤ conjBy x L := conjBy_mono h5
  have h7 : conjBy x L = L' := le_antisymm h1 h6
  rw [h7]
  exact hL'

end Perm151c

end CFSG.Quasithin
