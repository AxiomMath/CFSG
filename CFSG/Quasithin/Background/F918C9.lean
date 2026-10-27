module

public import CFSG.Quasithin.Background.F918P3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped Pointwise commutatorElement

section Dictionary2

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] {V₁ IH H : Subgroup G}

theorem eq_of_secImg_eq {A B : Subgroup G} [(B.subgroupOf A).Normal] {X Y : Subgroup G}
    (hBX : B ≤ X) (hBY : B ≤ Y) (hXA : X ≤ A) (hYA : Y ≤ A)
    (h : secImg A B X = secImg A B Y) : X = Y := by
  apply le_antisymm
  · intro x hx
    have h1 : secMk A B ⟨x, hXA hx⟩ ∈ secImg A B Y := h ▸ secMk_mem_secImg (A := A) (B := B) hx
    exact (secMk_mem_secImg_iff hBY).1 h1
  · intro y hy
    have h1 : secMk A B ⟨y, hYA hy⟩ ∈ secImg A B X := h.symm ▸ secMk_mem_secImg (A := A) (B := B) hy
    exact (secMk_mem_secImg_iff hBX).1 h1

omit [Group G] in
theorem tildeOf_sup' {G : Type} [Group G] {V₁ X Y : Subgroup G}
    (hX : X ≤ Subgroup.normalizer (V₁ : Set G)) (hY : Y ≤ Subgroup.normalizer (V₁ : Set G)) :
    tildeOf V₁ (X ⊔ Y) = tildeOf V₁ X ⊔ tildeOf V₁ Y := by
  unfold tildeOf secImg
  rw [Subgroup.subgroupOf_sup hX hY, Subgroup.map_sup]

theorem subM_sup (hIHN : IH ≤ Subgroup.normalizer (V₁ : Set G)) {J J' : Subgroup G}
    (hJ : J ≤ IH) (hJ' : J' ≤ IH) :
    subM V₁ IH (J ⊔ J') = subM V₁ IH J ⊔ subM V₁ IH J' := by
  have hA : tildeOf V₁ J ≤ tildeOf V₁ IH := secImg_mono hJ
  have hA' : tildeOf V₁ J' ≤ tildeOf V₁ IH := secImg_mono hJ'
  unfold subM
  rw [tildeOf_sup' (hJ.trans hIHN) (hJ'.trans hIHN), Subgroup.subgroupOf_sup hA hA']

variable [Fact (IsElemAbelian 2 (tildeOf V₁ IH))]

theorem map_actH_subM (hV₁ : H ≤ Subgroup.normalizer (V₁ : Set G))
    (hIHN : IH ≤ Subgroup.normalizer (V₁ : Set G)) (hIH : H ≤ Subgroup.normalizer (IH : Set G))
    {J : Subgroup G} (hV₁J : V₁ ≤ J) (hJI : J ≤ IH) (x : ↥H) :
    (subM V₁ IH J).map (actH hV₁ hIH x).toMonoidHom = subM V₁ IH (conjSub (x : G) J) := by
  have hV₁Jx : V₁ ≤ conjSub (x : G) J := by
    intro v hv
    rw [mem_conjSub]
    exact hV₁J ((Subgroup.mem_normalizer_iff''.mp (hV₁ x.2) v).mp hv)
  have hJxI : conjSub (x : G) J ≤ IH := by
    intro y hy
    rw [mem_conjSub] at hy
    have h1 := hJI hy
    have := (Subgroup.mem_normalizer_iff.mp (hIH x.2) ((x : G)⁻¹ * y * (x : G))).mp h1
    simpa [mul_assoc] using this
  ext w
  obtain ⟨a, haIH, hau⟩ := exists_mk_of_mem_tilde w
  have hw : w = modMk hIHN (a : G) haIH := Subtype.ext hau.symm
  subst hw
  have hxa : (x : G)⁻¹ * (a : G) * (x : G) ∈ IH := by
    have := (Subgroup.mem_normalizer_iff.mp (hIH (H.inv_mem x.2)) (a : G)).mp haIH
    simpa [mul_assoc] using this
  rw [Subgroup.mem_map_equiv]
  have hsymm : (actH hV₁ hIH x).symm (modMk hIHN (a : G) haIH) =
      modMk hIHN ((x : G)⁻¹ * (a : G) * (x : G)) hxa := by
    have h1 : (actH hV₁ hIH x).symm = actH hV₁ hIH x⁻¹ := by
      rw [map_inv]
      rfl
    rw [h1, actH_modMk hV₁ hIHN hIH x⁻¹ haIH]
    simp
  rw [hsymm, modMk_mem_subM_iff hIHN hV₁J hxa, modMk_mem_subM_iff hIHN hV₁Jx haIH, mem_conjSub]

omit [Fact (IsElemAbelian 2 (tildeOf V₁ IH))] in
theorem eq_sup_of_subM_sup_eq_top (hIHN : IH ≤ Subgroup.normalizer (V₁ : Set G)) {J J' : Subgroup G}
    (hV₁J : V₁ ≤ J) (hJ : J ≤ IH) (hJ' : J' ≤ IH)
    (htop : subM V₁ IH J ⊔ subM V₁ IH J' = ⊤) : IH = J ⊔ J' := by
  have hV₁IH : V₁ ≤ IH := hV₁J.trans hJ
  symm
  refine le_antisymm (sup_le hJ hJ') ?_
  have hsub : tildeOf V₁ IH ≤ tildeOf V₁ (J ⊔ J') := by
    intro y hy
    have hmem : (⟨y, hy⟩ : ↥(tildeOf V₁ IH)) ∈ subM V₁ IH (J ⊔ J') := by
      rw [subM_sup hIHN hJ hJ', htop]
      trivial
    exact hmem
  have heq : tildeOf V₁ (J ⊔ J') = tildeOf V₁ IH :=
    le_antisymm (secImg_mono (sup_le hJ hJ')) hsub
  exact (eq_of_secImg_eq (A := Subgroup.normalizer (V₁ : Set G)) (B := V₁)
    (le_sup_of_le_left hV₁J) hV₁IH ((sup_le hJ hJ').trans hIHN) hIHN heq).ge

end Dictionary2

end CFSG.Quasithin
