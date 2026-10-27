module

public import CFSG.Quasithin.Background.B2FactorizationBaumannAux
public import CFSG.Quasithin.EmptyFaithful.S151Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

theorem autI_thompsonJi_eq_iSup151b {T V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hTN : T ≤ Subgroup.normalizer (V : Set G)) (i : ℕ) :
    autI hV (thompsonJi T i) = ⨆ (A : Subgroup G) (_ : IsElemAbelianCorank T i A), autI hV A := by
  unfold thompsonJi
  exact autI_iSup₂ hV (fun A hA => hA.1.trans hTN)

theorem pRank_two_eq_of_sylow151b {T M : Subgroup G} (hT : IsSylowTwoOf T M) :
    CFSG.Open.pRank 2 M = CFSG.Open.pRank 2 T := by
  have hle : CFSG.Open.pRank 2 T ≤ CFSG.Open.pRank 2 M :=
    CFSG.SectionRank.pRank_mono Nat.one_lt_two hT.1
  refine le_antisymm ?_ hle
  obtain ⟨E, hEM, hE, hcard⟩ := CFSG.SectionRank.exists_pRank Nat.one_lt_two M
  have hEp : IsPGroup 2 E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  obtain ⟨h, -, hh⟩ := exists_conj_le_of_isSylowTwoOf hT hEM hEp
  refine CFSG.SectionRank.le_pRank Nat.one_lt_two hh (isElemAbelian_cjSub hE) ?_
  rw [card_cjSub, hcard]

theorem exists_conj_corank151b {T M A : Subgroup G} (hT : IsSylowTwoOf T M) {i : ℕ}
    (hA : IsElemAbelianCorank M i A) : ∃ x ∈ M, IsElemAbelianCorank T i (cjSub x A) := by
  have hAp : IsPGroup 2 A := fun x => ⟨1, Subtype.ext (by simpa using hA.2.1.2 x x.2)⟩
  obtain ⟨x, hx, hxA⟩ := exists_conj_le_of_isSylowTwoOf hT hA.1 hAp
  refine ⟨x, hx, hxA, isElemAbelian_cjSub hA.2.1, ?_⟩
  rw [card_cjSub, ← pRank_two_eq_of_sylow151b hT]
  exact hA.2.2

theorem normal_autI_thompsonJi151b {M V : Subgroup G} (hV : IsElemAbelian 2 V) (i : ℕ) :
    ∀ y ∈ autI hV M, ∀ z ∈ autI hV (thompsonJi M i), y * z * y⁻¹ ∈ autI hV (thompsonJi M i) := by
  intro y hy z hz
  obtain ⟨g, hgM, rfl⟩ := (mem_autI hV).1 hy
  have hgJ : (g : G) ∈ Subgroup.normalizer (thompsonJi M i : Set G) :=
    normalizer_le_normalizer_thompsonJi151 M i (Subgroup.le_normalizer hgM)
  have hcj : cjSub (g : G) (thompsonJi M i) = thompsonJi M i := B2F.cjSub_eq_of_mem_normalizer hgJ
  have hmap := autI_cjSub hV g.2 (thompsonJi M i)
  rw [hcj] at hmap
  have : (MulAut.conj (convI hV ⟨(g : G), g.2⟩)).toMonoidHom z ∈ autI hV (thompsonJi M i) := by
    rw [← hmap]
    exact ⟨z, hz, rfl⟩
  simpa using this

theorem autI_thompsonJi_le151b {T M V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMN : M ≤ Subgroup.normalizer (V : Set G)) (hT : IsSylowTwoOf T M) (i : ℕ)
    {Y : Subgroup (MulAut (IntMod V hV))}
    (hY : ∀ y ∈ autI hV M, ∀ z ∈ Y, y * z * y⁻¹ ∈ Y) (hJ : autI hV (thompsonJi T i) ≤ Y) :
    autI hV (thompsonJi M i) ≤ Y := by
  have hTN : T ≤ Subgroup.normalizer (V : Set G) := hT.1.trans hMN
  rw [autI_thompsonJi_eq_iSup151b hV hMN i]
  refine iSup_le fun A => iSup_le fun hA => ?_
  obtain ⟨x, hxM, hxA⟩ := exists_conj_corank151b hT hA
  have hxN : x ∈ Subgroup.normalizer (V : Set G) := hMN hxM
  have hle : autI hV (cjSub x A) ≤ Y := by
    refine le_trans ?_ hJ
    rw [autI_thompsonJi_eq_iSup151b hV hTN i]
    exact le_iSup₂_of_le (cjSub x A) hxA le_rfl
  have hmap := autI_cjSub hV hxN A
  have hxbar : convI hV ⟨x, hxN⟩ ∈ autI hV M := convI_mem_autI hV hxM hxN
  intro ψ hψ
  have h1 : (MulAut.conj (convI hV ⟨x, hxN⟩)).toMonoidHom ψ ∈ autI hV (cjSub x A) := by
    rw [← hmap]
    exact ⟨ψ, hψ, rfl⟩
  have h1' : convI hV ⟨x, hxN⟩ * ψ * (convI hV ⟨x, hxN⟩)⁻¹ ∈ Y := by
    have := hle h1
    simpa using this
  have h2 := hY _ ((autI hV M).inv_mem hxbar) _ h1'
  simpa [mul_assoc] using h2

theorem jhat_le_of_inf_le151b {W : Type*} [CommGroup W] [Finite W]
    {X Tb J Y : Subgroup (MulAut W)} (hT : IsSylowTwoOf Tb X) (hJ : Tb ⊓ Jhat X ≤ J)
    (hJY : J ≤ Y) (hY : ∀ y ∈ X, ∀ z ∈ Y, y * z * y⁻¹ ∈ Y) : Jhat X ≤ Y := by
  unfold Jhat
  refine iSup_le fun A => iSup_le fun hA => ?_
  obtain ⟨r, -, -, ⟨⟨hA2, -⟩, -⟩, -⟩ := QhatStar_spec hA
  have hAJ : A ≤ Jhat X := le_iSup₂_of_le A hA le_rfl
  have hAp : IsPGroup 2 A := hA2.isElemAbelian2.isPGroup
  obtain ⟨h, hhX, hcj⟩ := exists_conj_le_of_isSylowTwoOf hT hA2.1 hAp
  intro a ha
  have hmem : h * a * h⁻¹ ∈ cjSub h A := by
    rw [mem_cjSub]
    have : h⁻¹ * (h * a * h⁻¹) * h = a := by group
    rw [this]
    exact ha
  have hJhat : h * a * h⁻¹ ∈ Jhat X := mem_Jhat_conj hhX (hAJ ha)
  have hY1 : h * a * h⁻¹ ∈ Y := hJY (hJ ⟨hcj hmem, hJhat⟩)
  have := hY h⁻¹ (X.inv_mem hhX) _ hY1
  simpa [mul_assoc] using this

end CFSG.Quasithin
