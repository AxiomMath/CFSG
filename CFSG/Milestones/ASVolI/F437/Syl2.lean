module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.Milestones.ASVolI.F4L3

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.ASVolI.ChF CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

section Transport

variable {E : Type} [Group E] {M₁ M₂ : Subgroup E} {Y : Type} [Group Y] {M : Type} [Group M]

theorem burnsideF437_bM_eq (β : Cpl M₁ M₂ Y) (ε : Y →* M) (fb : ↥(M₁ ⊓ M₂)) :
    bM β ε fb = burnsideF4d_bOne β ε ⟨(fb : E), fb.2.1⟩ := rfl

theorem burnsideF437_imB_eq (β : Cpl M₁ M₂ Y) (ε : Y →* M) {K : Subgroup E} (hK : K ≤ M₁ ⊓ M₂) :
    imB β ε K = subImg (burnsideF4d_bOne β ε) K := by
  ext g
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact mem_subImg.mpr ⟨(k : E), k.2.1, hk, rfl⟩
  · intro hg
    obtain ⟨x, hx, hxK, rfl⟩ := mem_subImg.mp hg
    exact ⟨⟨x, hK hxK⟩, hxK, rfl⟩

theorem burnsideF437_MiOne_eq (β : Cpl M₁ M₂ Y) (ε : Y →* M) :
    MiOne β ε = subImg (burnsideF4d_bOne β ε) M₁ := by
  rw [subImg_self]
  unfold MiOne burnsideF4d_bOne
  rw [MonoidHom.map_range]
  rfl

end Transport

end CFSG.ASVolI
