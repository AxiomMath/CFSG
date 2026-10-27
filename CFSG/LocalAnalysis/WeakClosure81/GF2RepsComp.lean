module

public import CFSG.Open.Defs
import CFSG.Goldschmidt.Steps.G37CoreSetup
import CFSG.LocalAnalysis.GLTheoremA.CatA.I142NTrans

public section

namespace CFSG.LocalAnalysis.WeakClosure81

variable {G : Type*} [Group G]

private theorem gf2_Comp_map_conj_self {Y : Subgroup G} {φ : G} (hφ : φ ∈ Y) :
    Y.map (MulAut.conj φ).toMonoidHom = Y := by
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using
      Y.mul_mem (Y.mul_mem hφ hy) (Y.inv_mem hφ)
  · intro z hz
    refine ⟨φ⁻¹ * z * φ, Y.mul_mem (Y.mul_mem (Y.inv_mem hφ) hz) hφ, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem isComponentOf_map_conj_of_mem {Y L : Subgroup G} (hL : CFSG.Open.IsComponentOf L Y)
    {φ : G} (hφ : φ ∈ Y) :
    CFSG.Open.IsComponentOf (L.map (MulAut.conj φ).toMonoidHom) Y := by
  have h := CFSG.Goldschmidt.G37.open_isComponentOf_map (MulAut.conj φ) hL
  rwa [gf2_Comp_map_conj_self hφ] at h

theorem eq_or_commute_of_isComponentOf [Finite G] {Y K K' : Subgroup G}
    (hK : CFSG.Open.IsComponentOf K Y) (hK' : CFSG.Open.IsComponentOf K' Y) :
    K = K' ∨ ∀ k ∈ K, ∀ k' ∈ K', k * k' = k' * k := by
  rcases CFSG.LocalAnalysis.GLTheoremA.I142N.isComponent_commute_or_eq hK hK' with h | h
  · exact Or.inl h
  · right
    intro k hk k' hk'
    exact (Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h hk) k' hk').symm

theorem le_or_commute_of_isComponentOf_of_normal [Finite G] {Y K M : Subgroup G}
    (hK : CFSG.Open.IsComponentOf K Y) (hMY : M ≤ Y)
    (hMn : ∀ y ∈ Y, ∀ m ∈ M, y * m * y⁻¹ ∈ M) :
    K ≤ M ∨ ∀ k ∈ K, ∀ m ∈ M, k * m = m * k := by
  have hgw : CFSG.GorensteinWalter.IsComponentOf K Y :=
    CFSG.LocalAnalysis.GLTheoremA.I142N.gw_isComponentOf_of_open hK
  have hVW : M ≤ Subgroup.normalizer (Y : Set G) := hMY.trans Subgroup.le_normalizer
  have hKV : K ≤ Subgroup.normalizer (M : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact hMn k (hK.1 hk) h hh
    · intro hh
      have hmem := hMn k⁻¹ (Y.inv_mem (hK.1 hk)) (k * h * k⁻¹) hh
      have h2 : k⁻¹ * (k * h * k⁻¹) * k⁻¹⁻¹ = h := by group
      rwa [h2] at hmem
  rcases CFSG.Goldschmidt.G37.le_or_commutator_eq_bot_of_le_normalizer hgw hVW hKV with h | h
  · exact Or.inl h
  · right
    intro k hk m hm
    exact (Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h hk) m hm).symm

theorem le_of_eq_biSup_conj {Y L H : Subgroup G}
    (hH : H = ⨆ φ ∈ Y, L.map (MulAut.conj φ).toMonoidHom) : L ≤ H := by
  rw [hH]
  refine le_iSup₂_of_le (1 : G) Y.one_mem ?_
  intro x hx
  exact ⟨x, hx, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩

theorem biSup_conj_le_of_normal {Y L M H : Subgroup G}
    (hH : H = ⨆ φ ∈ Y, L.map (MulAut.conj φ).toMonoidHom)
    (hMn : ∀ y ∈ Y, ∀ m ∈ M, y * m * y⁻¹ ∈ M) (hLM : L ≤ M) : H ≤ M := by
  rw [hH]
  refine iSup₂_le fun φ hφ => ?_
  rintro x ⟨l, hl, rfl⟩
  simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hMn φ hφ l (hLM hl)

theorem commute_of_normal_of_not_le [Finite G] {Y L M H : Subgroup G}
    (hL : CFSG.Open.IsComponentOf L Y)
    (hH : H = ⨆ φ ∈ Y, L.map (MulAut.conj φ).toMonoidHom) (hMY : M ≤ Y)
    (hMn : ∀ y ∈ Y, ∀ m ∈ M, y * m * y⁻¹ ∈ M) (hLM : ¬ L ≤ M) :
    ∀ m ∈ M, ∀ h ∈ H, m * h = h * m := by
  have hHZ : H ≤ Subgroup.centralizer (M : Set G) := by
    rw [hH]
    refine iSup₂_le fun φ hφ => ?_
    have hL' : CFSG.Open.IsComponentOf (L.map (MulAut.conj φ).toMonoidHom) Y :=
      isComponentOf_map_conj_of_mem hL hφ
    rcases le_or_commute_of_isComponentOf_of_normal hL' hMY hMn with h | h
    · exfalso
      apply hLM
      intro l hl
      have hmem : (MulAut.conj φ).toMonoidHom l ∈ M := h ⟨l, hl, rfl⟩
      have h2 := hMn φ⁻¹ (Y.inv_mem hφ) ((MulAut.conj φ).toMonoidHom l) hmem
      have h3 : φ⁻¹ * (MulAut.conj φ).toMonoidHom l * φ⁻¹⁻¹ = l := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rwa [h3] at h2
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      exact (h x hx m hm).symm
  intro m hm h hh
  exact Subgroup.mem_centralizer_iff.mp (hHZ hh) m hm

theorem conj_mem_of_eq_biSup_conj [Finite G] {Y L H : Subgroup G}
    (hL : CFSG.Open.IsComponentOf L Y)
    (hH : H = ⨆ φ ∈ Y, L.map (MulAut.conj φ).toMonoidHom) :
    ∀ h ∈ H, ∀ l ∈ L, h * l * h⁻¹ ∈ L := by
  have hHN : H ≤ Subgroup.normalizer (L : Set G) := by
    rw [hH]
    refine iSup₂_le fun φ hφ => ?_
    have hL' : CFSG.Open.IsComponentOf (L.map (MulAut.conj φ).toMonoidHom) Y :=
      isComponentOf_map_conj_of_mem hL hφ
    rcases eq_or_commute_of_isComponentOf hL' hL with h | h
    · rw [h]
      exact Subgroup.le_normalizer
    · apply le_trans _ (Subgroup.centralizer_le_normalizer (L : Set G))
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      exact (h x hx l hl).symm
  intro h hh l hl
  exact (Subgroup.mem_normalizer_iff.mp (hHN hh) l).mp hl

end CFSG.LocalAnalysis.WeakClosure81
