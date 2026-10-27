module

public import CFSG.Quasithin.Background.B2FactorizationOffender

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

universe u

variable {G : Type u} [Group G]

namespace C124

section Offender

variable [Finite G] {V : Subgroup G} (hV : IsElemAbelian 2 V)

@[expose] def offenderImagesConjIn (X R : Subgroup G) :
    Set (Subgroup (MulAut (IntMod V hV))) :=
  {B | B ≠ ⊥ ∧ ∃ A : Subgroup G, B = autI hV A ∧ ∃ g ∈ X, IsMaxElemAbelian R (cjSub g⁻¹ A)}

omit [Finite G] in
theorem mem_offenderImagesConjIn_iff {X R : Subgroup G}
    (hXN : X ≤ Subgroup.normalizer (V : Set G)) (hRX : R ≤ X)
    {B : Subgroup (MulAut (IntMod V hV))} :
    B ∈ offenderImagesConjIn hV X R ↔
      ∃ g : G, ∃ hg : g ∈ X, ∃ B' ∈ offenderImages hV R,
        B = B'.map (MulAut.conj (convI hV ⟨g, hXN hg⟩)).toMonoidHom := by
  constructor
  · rintro ⟨hB0, A, rfl, g, hg, hgA⟩
    refine ⟨g, hg, autI hV (cjSub g⁻¹ A), ⟨cjSub g⁻¹ A, ⟨hgA, ?_⟩, rfl⟩, ?_⟩
    · intro h
      apply hB0
      have h1 : cjSub g (cjSub g⁻¹ A) ≤ Subgroup.centralizer (V : Set G) :=
        cjSub_le (B2F.normalizer_le_normalizer_centralizer V (hXN hg)) h
      rw [cjSub_cjSub_inv] at h1
      exact autI_eq_bot_of_le_centralizer hV h1
    · have := autI_cjSub hV (hXN hg) (cjSub g⁻¹ A)
      rw [cjSub_cjSub_inv] at this
      exact this.symm
  · rintro ⟨g, hg, B', ⟨A', ⟨hA', hA'C⟩, rfl⟩, rfl⟩
    have hA'N : A' ≤ Subgroup.normalizer (V : Set G) := hA'.1.trans (hRX.trans hXN)
    have hnb : autI hV A' ≠ ⊥ := fun h => hA'C ((autI_eq_bot_iff hV hA'N).1 h)
    refine ⟨?_, cjSub g A', autI_cjSub hV (hXN hg) A', g, hg, ?_⟩
    · rw [← conjAut_eq_map]
      exact B1.conjAut_ne_bot hnb
    · rw [cjSub_inv_cjSub]
      exact hA'

theorem B2_10_1_stable_in {X R : Subgroup G} (hXN : X ≤ Subgroup.normalizer (V : Set G))
    (hRX : R ≤ X) (hVR : V ≤ R) (hJ : ¬ thompsonJ R ≤ Subgroup.centralizer (V : Set G)) :
    IsStableFF (autI hV X) (offenderImagesConjIn hV X R) ∧
      ffJP (offenderImagesConjIn hV X R) (autI hV X) ≤ ffJ (autI hV X) := by
  have hRN : R ≤ Subgroup.normalizer (V : Set G) := hRX.trans hXN
  have hne : (offenderImages hV R).Nonempty := (offenderImages_nonempty_iff_not_le hV).2 hJ
  have hRst := B2_5 hV hVR hRN hne
  have hoff : ∀ B ∈ offenderImagesConjIn hV X R, IsFFStarOffender (autI hV X) B := by
    intro B hB
    obtain ⟨g, hg, B', hB', rfl⟩ := (mem_offenderImagesConjIn_iff hV hXN hRX).1 hB
    have h1 : IsFFStarOffender (autI hV X) B' :=
      isFFStarOffender_mono (autI_mono hV hRX) (offenderImages_isFFStarOffender hV hVR hRN hB')
    rw [← conjAut_eq_map]
    exact B1.isFFStarOffender_conjAut h1 (convI_mem_autI hV hg (hXN hg))
  refine ⟨⟨?_, hoff, ?_, ?_⟩, ?_⟩
  · obtain ⟨B', hB'⟩ := hne
    exact ⟨_, (mem_offenderImagesConjIn_iff hV hXN hRX).2 ⟨1, X.one_mem, B', hB', rfl⟩⟩
  · intro B hB h hh
    obtain ⟨g, hg, B', hB', rfl⟩ := (mem_offenderImagesConjIn_iff hV hXN hRX).1 hB
    obtain ⟨k, hk, rfl⟩ := (mem_autI hV).1 hh
    refine (mem_offenderImagesConjIn_iff hV hXN hRX).2
      ⟨(k : G) * g, X.mul_mem hk hg, B', hB', ?_⟩
    rw [map_conj_map_conj, ← map_mul]
    rfl
  · intro B hB B₁ hB₁
    obtain ⟨g, hg, B', hB', rfl⟩ := (mem_offenderImagesConjIn_iff hV hXN hRX).1 hB
    set a : MulAut (IntMod V hV) := convI hV ⟨g, hXN hg⟩ with ha
    have haG : a ∈ autI hV X := convI_mem_autI hV hg (hXN hg)
    have hle : FFLe (autI hV X) (B1.conjAut a⁻¹ B₁) B' := by
      rw [← conjAut_eq_map] at hB₁
      have := B1.ffLe_conjAut hB₁ ((autI hV X).inv_mem haG)
      rwa [B1.conjAut_inv_conjAut] at this
    have hB'off := offenderImages_isFFStarOffender hV hVR hRN hB'
    have hle' : FFLe (autI hV R) (B1.conjAut a⁻¹ B₁) B' :=
      ⟨⟨hle.2.2.1.trans hB'off.1, hle.1.2.1, hle.1.2.2⟩, hB'off.isA2, hle.2.2.1, hle.2.2.2⟩
    obtain ⟨D, hD, hDeq⟩ : B1.conjAut a⁻¹ B₁ ∈ offenderImages hV R := hRst.2.2.2 B' hB' _ hle'
    refine (mem_offenderImagesConjIn_iff hV hXN hRX).2 ⟨g, hg, autI hV D, ⟨D, hD, rfl⟩, ?_⟩
    rw [← hDeq, ← conjAut_eq_map]
    exact (B1.conjAut_conjAut_inv a B₁).symm
  · exact iSup_le fun B => iSup_le fun hB => iSup_le fun _ => le_iSup₂_of_le B (hoff B hB) le_rfl

end Offender

end C124

end CFSG.Quasithin
