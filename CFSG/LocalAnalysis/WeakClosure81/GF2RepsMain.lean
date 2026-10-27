module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsKernel
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsSec

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin Subgroup

variable {W : Type*} [CommGroup W] [Finite W]

theorem exists_secIsoOn_of_le_biSup_irrSet (hW : ∀ w : W, w ^ 2 = 1) {H : Subgroup (MulAut W)}
    {S : Set (Subgroup W)} (hS : S ⊆ irrSet H) {I : Subgroup W} (hI : I ∈ irrSet H)
    (hle : I ≤ ⨆ K ∈ S, K) :
    ∃ K ∈ S, SecIsoOn H (I ⊔ fixV H) (fixV H) (K ⊔ fixV H) (fixV H) ∧
      SecIsoOn H (K ⊔ fixV H) (fixV H) (I ⊔ fixV H) (fixV H) := by
  haveI : Finite S := Set.toFinite S
  have hle' : I ⊔ fixV H ≤ fixV H ⊔ ⨆ K : S, ((K : Subgroup W) ⊔ fixV H) := by
    refine sup_le (le_trans hle ?_) le_sup_left
    exact iSup₂_le fun K hK => le_sup_of_le_right (le_iSup_of_le ⟨K, hK⟩ le_sup_left)
  obtain ⟨K, hK1, hK2⟩ := exists_secIsoOn_of_le_iSup hW (H := H) (C := fixV H)
    (A := I ⊔ fixV H) (B := fun K : S => (K : Subgroup W) ⊔ fixV H) (isIrrOn_sup_fixV hI)
    (fun K => isIrrOn_sup_fixV (hS K.2)) hle'
  exact ⟨K, K.2, hK1, hK2⟩

theorem secIsoOn_map_sup_fixV {H : Subgroup (MulAut W)} {g : MulAut W}
    (hg : ∀ x ∈ H, g * x * g⁻¹ ∈ H) (hg' : ∀ x ∈ H, g⁻¹ * x * g ∈ H) {I K : Subgroup W}
    (h : SecIsoOn H (I ⊔ fixV H) (fixV H) (K ⊔ fixV H) (fixV H)) :
    SecIsoOn H (I.map g.toMonoidHom ⊔ fixV H) (fixV H) (K.map g.toMonoidHom ⊔ fixV H)
      (fixV H) := by
  have h1 := secIsoOn_map hg hg' h
  rw [Subgroup.map_sup, Subgroup.map_sup, map_fixV_of_normalizes hg hg'] at h1
  exact h1

private theorem gf2_Main_map_map_comp (y g : MulAut W) (I : Subgroup W) :
    (I.map y.toMonoidHom).map (g * y⁻¹).toMonoidHom = I.map g.toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext w
  simp

private theorem gf2_Main_map_one (I : Subgroup W) : I.map (1 : MulAut W).toMonoidHom = I := by
  ext w
  simp

private theorem gf2_Main_map_map_inv (y : MulAut W) (I : Subgroup W) :
    (I.map y.toMonoidHom).map (y⁻¹).toMonoidHom = I := by
  have := gf2_Main_map_map_comp y 1 I
  rw [one_mul, gf2_Main_map_one] at this
  exact this

theorem exists_secIsoOn_conj_of_iSup_irrSet_eq_top (hW : ∀ w : W, w ^ 2 = 1)
    {Y H : Subgroup (MulAut W)} (hind : IsIndivisible Y)
    (hn : ∀ y ∈ Y, ∀ h ∈ H, y * h * y⁻¹ ∈ H) (hU : (⨆ I ∈ irrSet H, I) = ⊤) :
    ∀ I ∈ irrSet H, ∀ J ∈ irrSet H, ∃ g ∈ Y,
      SecIsoOn H (I.map (g : MulAut W).toMonoidHom ⊔ fixV H) (fixV H) (J ⊔ fixV H) (fixV H) := by
  intro I₀ hI₀ J hJ
  have hn2 : ∀ y ∈ Y, ∀ x ∈ H, y⁻¹ * x * y ∈ H := by
    intro y hy x hx
    simpa using hn y⁻¹ (Y.inv_mem hy) x hx
  let S : Set (Subgroup W) := {I | I ∈ irrSet H ∧ ∃ g ∈ Y,
    SecIsoOn H (I.map g.toMonoidHom ⊔ fixV H) (fixV H) (J ⊔ fixV H) (fixV H)}
  let S' : Set (Subgroup W) := {I | I ∈ irrSet H ∧ I ∉ S}
  have hSclosed : ∀ I ∈ S, ∀ y ∈ Y, I.map y.toMonoidHom ∈ S := by
    rintro I ⟨hI, g, hg, hsec⟩ y hy
    refine ⟨map_mem_irrSet (hn y hy) (hn2 y hy) hI, g * y⁻¹, Y.mul_mem hg (Y.inv_mem hy), ?_⟩
    rw [gf2_Main_map_map_comp]
    exact hsec
  have hS'closed : ∀ I ∈ S', ∀ y ∈ Y, I.map y.toMonoidHom ∈ S' := by
    rintro I ⟨hI, hIS⟩ y hy
    refine ⟨map_mem_irrSet (hn y hy) (hn2 y hy) hI, fun hmem => hIS ?_⟩
    have := hSclosed _ hmem y⁻¹ (Y.inv_mem hy)
    rwa [gf2_Main_map_map_inv] at this
  have hU₁ : StableUnder Y (⨆ K ∈ S, K) := stableUnder_iSup_of_map_mem hSclosed
  have hU₂ : StableUnder Y (⨆ K ∈ S', K) := stableUnder_iSup_of_map_mem hS'closed
  have htop : (⨆ K ∈ S, K) ⊔ (⨆ K ∈ S', K) = ⊤ := by
    rw [eq_top_iff, ← hU]
    refine iSup₂_le fun I hI => ?_
    by_cases hIS : I ∈ S
    · exact le_sup_of_le_left (le_iSup₂_of_le I hIS le_rfl)
    · exact le_sup_of_le_right (le_iSup₂_of_le I ⟨hI, hIS⟩ le_rfl)
  rcases hind _ _ hU₁ hU₂ htop with h1 | h2
  · have hle : I₀ ≤ ⨆ K ∈ S, K := by rw [h1]; exact le_top
    obtain ⟨K, hKS, hsec, -⟩ :=
      exists_secIsoOn_of_le_biSup_irrSet hW (fun K hK => hK.1) hI₀ hle
    obtain ⟨-, g, hg, hKg⟩ := hKS
    exact ⟨g, hg, secIsoOn_trans (secIsoOn_map_sup_fixV (hn g hg) (hn2 g hg) hsec) hKg⟩
  · exfalso
    have hle : J ≤ ⨆ K ∈ S', K := by rw [h2]; exact le_top
    obtain ⟨K, hKS', -, hsec⟩ :=
      exists_secIsoOn_of_le_biSup_irrSet hW (fun K hK => hK.1) hJ hle
    refine hKS'.2 ⟨hKS'.1, 1, Y.one_mem, ?_⟩
    rw [gf2_Main_map_one]
    exact hsec

theorem w4Lem12_5_holds : W4Lem12_5 := by
  intro W _ _ hW Y hO hbasic H hne hHY hHnorm
  have hn : ∀ y ∈ Y, ∀ h ∈ H, y * h * y⁻¹ ∈ H := conj_mem_of_normal_subgroupOf hHY hHnorm
  refine ⟨fun hodd => ?_, fun L hL hH => ?_⟩
  · have h1 := iSup_irrSet_sup_fixV_eq_top_of_odd hW hodd
    have h2 := iSup_irrSet_eq_top_of_sup_fixV_eq_top hbasic.1 hn hne h1
    exact ⟨h2, exists_secIsoOn_conj_of_iSup_irrSet_eq_top hW hbasic.1 hn h2⟩
  · have hstab : StableUnder Y ((⨆ I ∈ irrSet H, I) ⊔ fixV H) :=
      stableUnder_sup (stableUnder_iSup_irrSet hn) (stableUnder_fixV hn)
    have h1 : (⨆ I ∈ irrSet H, I) ⊔ fixV H = ⊤ :=
      hbasic.2 _ hstab (faithful_on_sup_fixV hW hO hL hH hne hHY hn)
    have h2 := iSup_irrSet_eq_top_of_sup_fixV_eq_top hbasic.1 hn hne h1
    refine ⟨⟨h2, exists_secIsoOn_conj_of_iSup_irrSet_eq_top hW hbasic.1 hn h2⟩, ?_⟩
    have h3 := le_iSup_irrSet_sup_fixV hL hH
    rw [h2] at h3
    exact top_le_iff.mp h3

end CFSG.LocalAnalysis.WeakClosure81
