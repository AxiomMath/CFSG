module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.L83.Comm

public section

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace L83

variable {G : Type*} [Group G]

theorem zOf_le_centralizer {X Y : Subgroup G} (hXY : X ≤ Y) :
    zOf Y ≤ Subgroup.centralizer (X : Set G) := by
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  exact (mem_zOf_iff.mp hz).2 w (hXY hw)

@[expose] def vOf (S E : Subgroup G) : Subgroup G :=
  zOf S ⊔ zOf (S ⊓ Subgroup.centralizer (E : Set G))

theorem zOf_le_vOf (S E : Subgroup G) : zOf S ≤ vOf S E :=
  le_sup_left

theorem zOf_inf_centralizer_le_vOf (S E : Subgroup G) :
    zOf (S ⊓ Subgroup.centralizer (E : Set G)) ≤ vOf S E :=
  le_sup_right

theorem vOf_le_centralizer (S E : Subgroup G) :
    vOf S E ≤ Subgroup.centralizer ((vOf S E : Subgroup G) : Set G) := by
  have hPS : zOf (S ⊓ Subgroup.centralizer (E : Set G)) ≤ S := (zOf_le _).trans inf_le_left
  have hSP : zOf S ≤ Subgroup.centralizer
      ((zOf (S ⊓ Subgroup.centralizer (E : Set G)) : Subgroup G) : Set G) :=
    zOf_le_centralizer hPS
  rw [vOf, CFSG.SignalizerFunctorTheorem.centralizer_sup]
  exact sup_le (le_inf (zOf_le_centralizer (zOf_le S)) hSP)
    (le_inf (Subgroup.le_centralizer_iff.mp hSP) (zOf_le_centralizer (zOf_le _)))

theorem inf_centralizer_le_zOf (S E : Subgroup G) :
    zOf S ⊓ Subgroup.centralizer (E : Set G) ≤ zOf (S ⊓ Subgroup.centralizer (E : Set G)) :=
  fun _ hx => mem_zOf_iff.mpr ⟨⟨zOf_le S hx.1, hx.2⟩, fun w hw => (mem_zOf_iff.mp hx.1).2 w hw.1⟩

theorem le_iSup_vK {Ω : Set (Subgroup G)} {V K X : Subgroup G} (hK : K ∈ Ω) (hX : X ≤ vK Ω V K) :
    X ≤ ⨆ K' ∈ Ω, vK Ω V K' :=
  hX.trans (le_iSup₂_of_le K hK le_rfl)

end L83

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
