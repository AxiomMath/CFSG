module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Diag.Block
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Diag.Fixed

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

variable {G : Type*} [Group G] [Finite G]

structure DiagSetting (p : ℕ) (A K : Subgroup G) : Prop where
  prime : p.Prime
  elemAbelian : IsElemAbelian p A
  normalizes : A ≤ Subgroup.normalizer (K : Set G)
  direct : IsDirectProduct (lcal K) K
  nonempty : (lcal K).Nonempty
  transitive : ∀ J ∈ lcal K, ∀ J' ∈ lcal K,
    ∃ a ∈ A, J' = J.map (MulAut.conj a).toMonoidHom

theorem DiagSetting.eq_or_eq_top {p : ℕ} {A K : Subgroup G} (h : DiagSetting p A K)
    {N : Subgroup G} (hN : ∀ J ∈ lcal K, N = A ⊓ Subgroup.normalizer (J : Set G))
    {a : G} (ha : a ∈ A) (haN : a ∉ N) {Y : Subgroup G} (hYK : Y ≤ K)
    (hY : K ⊓ Subgroup.centralizer {a} ≤ Y) (hAY : A ≤ Subgroup.normalizer (Y : Set G)) :
    Y = K ⊓ Subgroup.centralizer {a} ∨ Y = K := by
  have hK : IsSemisimple K := Diag.isSemisimple_of_isDirectProduct_lcal h.direct
  have hap : a ^ p = 1 := h.elemAbelian.2 a ha
  have haK : a ∈ Subgroup.normalizer (K : Set G) := h.normalizes ha
  have hperm : ∀ c ∈ A, ∀ J ∈ lcal K, J.map (MulAut.conj c).toMonoidHom ∈ lcal K :=
    fun c hc _ hJ => map_conj_mem_lcal hJ (h.normalizes hc)
  have haJ : ∀ J ∈ lcal K, a ∉ Subgroup.normalizer (J : Set G) := fun J hJ hJa =>
    haN ((hN J hJ).symm ▸ Subgroup.mem_inf.mpr ⟨ha, hJa⟩)
  have hprojC : ∀ J ∈ lcal K, projIn (lcal K) J (K ⊓ Subgroup.centralizer {a}) = J :=
    fun J hJ => Diag.projIn_inf_centralizer_eq_self h.prime h.direct haK hap hJ (haJ J hJ)
  have hproj : ∀ J ∈ lcal K, projIn (lcal K) J Y = J := fun J hJ =>
    le_antisymm (projIn_le _ _) ((hprojC J hJ).symm.le.trans (Diag.projIn_mono J hY))
  have hcomm : ∀ c ∈ A, c * a = a * c := by
    have := h.elemAbelian.1
    intro c hc
    exact congrArg Subtype.val (mul_comm' (⟨c, hc⟩ : A) ⟨a, ha⟩)
  obtain ⟨J₀, hJ₀⟩ := h.nonempty
  rcases Diag.exists_le_or_sameBlock hK hYK hproj hJ₀ with hle | ⟨J₁, hJ₁, hne, hsame⟩
  ·
    right
    refine le_antisymm hYK ?_
    rw [← h.direct.sSup_eq]
    refine sSup_le fun J hJ => ?_
    obtain ⟨c, hc, rfl⟩ := h.transitive J₀ hJ₀ J hJ
    rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hAY hc) x).mp (hle hx)
  ·
    left
    obtain ⟨g, hg, hJ₁g⟩ := Diag.mem_conjOrbit_of_sameBlock h.prime h.direct haK hap hJ₀
      (haJ J₀ hJ₀) hY hJ₁ hsame
    have hgne : J₀.map (MulAut.conj g).toMonoidHom ≠ J₀ := by
      rw [← hJ₁g]
      exact hne
    have hsame_a := Diag.sameBlock_map_conj_of_ne h.prime ha hap hperm hAY hg hgne
      (by rw [← hJ₁g]; exact hsame)
    have hall : ∀ J ∈ lcal K,
        Diag.SameBlock (lcal K) Y J (J.map (MulAut.conj a).toMonoidHom) := by
      intro J hJ
      obtain ⟨c, hc, rfl⟩ := h.transitive J₀ hJ₀ J hJ
      have h1 := Diag.SameBlock.map_conj (hperm c hc) (hperm c⁻¹ (inv_mem hc)) (hAY hc) hsame_a
      rw [L514.map_conj_map_conj, hcomm c hc, ← L514.map_conj_map_conj] at h1
      exact h1
    exact le_antisymm (le_inf hYK (Diag.le_centralizer_of_forall_sameBlock h.direct (hperm a ha)
      (hperm a⁻¹ (inv_mem ha)) hYK hY hprojC hall)) hY

theorem DiagSetting.sup_eq_top {p : ℕ} {A K : Subgroup G} (h : DiagSetting p A K)
    {N : Subgroup G} (hN : ∀ J ∈ lcal K, N = A ⊓ Subgroup.normalizer (J : Set G))
    {a b : G} (ha : a ∈ A) (hb : b ∈ A) (haN : a ∉ N) (hbN : b ∉ N)
    (hab : (Subgroup.zpowers a ⊔ N) ⊓ (Subgroup.zpowers b ⊔ N) = N) :
    (K ⊓ Subgroup.centralizer {a}) ⊔ (K ⊓ Subgroup.centralizer {b}) = K := by
  have hK : IsSemisimple K := Diag.isSemisimple_of_isDirectProduct_lcal h.direct
  have hap : a ^ p = 1 := h.elemAbelian.2 a ha
  have hbp : b ^ p = 1 := h.elemAbelian.2 b hb
  have haK : a ∈ Subgroup.normalizer (K : Set G) := h.normalizes ha
  have hbK : b ∈ Subgroup.normalizer (K : Set G) := h.normalizes hb
  have haJ : ∀ J ∈ lcal K, a ∉ Subgroup.normalizer (J : Set G) := fun J hJ hJa =>
    haN ((hN J hJ).symm ▸ Subgroup.mem_inf.mpr ⟨ha, hJa⟩)
  have hbJ : ∀ J ∈ lcal K, b ∉ Subgroup.normalizer (J : Set G) := fun J hJ hJb =>
    hbN ((hN J hJ).symm ▸ Subgroup.mem_inf.mpr ⟨hb, hJb⟩)
  set Y := (K ⊓ Subgroup.centralizer {a}) ⊔ (K ⊓ Subgroup.centralizer {b}) with hYdef
  have hCa : K ⊓ Subgroup.centralizer {a} ≤ Y := le_sup_left
  have hCb : K ⊓ Subgroup.centralizer {b} ≤ Y := le_sup_right
  have hYK : Y ≤ K := sup_le inf_le_left inf_le_left
  have hproj : ∀ J ∈ lcal K, projIn (lcal K) J Y = J := fun J hJ =>
    le_antisymm (projIn_le _ _)
      ((Diag.projIn_inf_centralizer_eq_self h.prime h.direct haK hap hJ (haJ J hJ)).symm.le.trans
        (Diag.projIn_mono J hCa))
  refine le_antisymm hYK ?_
  rw [← h.direct.sSup_eq]
  refine sSup_le fun J₀ hJ₀ => ?_
  rcases Diag.exists_le_or_sameBlock hK hYK hproj hJ₀ with hle | ⟨J₁, hJ₁, hne, hsame⟩
  · exact hle
  ·
    exfalso
    obtain ⟨g, hg, hJ₁g⟩ := Diag.mem_conjOrbit_of_sameBlock h.prime h.direct haK hap hJ₀
      (haJ J₀ hJ₀) hCa hJ₁ hsame
    obtain ⟨g', hg', hJ₁g'⟩ := Diag.mem_conjOrbit_of_sameBlock h.prime h.direct hbK hbp hJ₀
      (hbJ J₀ hJ₀) hCb hJ₁ hsame
    have hgA : g ∈ A := Subgroup.zpowers_le.mpr ha hg
    have hg'A : g' ∈ A := Subgroup.zpowers_le.mpr hb hg'
    have hnorm : g'⁻¹ * g ∈ Subgroup.normalizer (J₀ : Set G) :=
      Diag.mem_normalizer_of_map_conj_eq (hJ₁g.symm.trans hJ₁g')
    have hmemN : g'⁻¹ * g ∈ N := by
      rw [hN J₀ hJ₀]
      exact Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hg'A) hgA, hnorm⟩
    have hgmem : g ∈ (Subgroup.zpowers a ⊔ N) ⊓ (Subgroup.zpowers b ⊔ N) := by
      refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_left hg, ?_⟩
      have hg_eq : g = g' * (g'⁻¹ * g) := by group
      rw [hg_eq]
      exact Subgroup.mul_mem_sup hg' hmemN
    rw [hab, hN J₀ hJ₀] at hgmem
    exact hne (hJ₁g.trans (L514.map_conj_eq_of_mem_normalizer (Subgroup.mem_inf.mp hgmem).2))

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
