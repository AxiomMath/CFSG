module

public import CFSG.Quasithin.EmptyFaithful.SzPS8Excl2Defs
public import CFSG.Quasithin.EmptyFaithful.SzPS8S6Normal
public import CFSG.Quasithin.Background.P4InspSpEmbed
public import CFSG.Quasithin.EmptyFaithful.SzN28PDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.G11

namespace SzPS8

theorem img_le_spSub {G : Type} [Group G] [Finite G] {T M : Subgroup G} (D : HatModel T M) :
    D.img (mcOf T) ≤ spSub D.B := by
  intro γ hγ
  obtain ⟨x, -, hx, rfl⟩ := HatModel.mem_img.mp hγ
  intro v w
  exact D.B_rho ⟨x, hx⟩ v w

theorem excl2_of_parts (hA5 : Excl2NoNormalA5) (hA6 : Excl2NoNormalA6) : Lemma14315Excl2 := by
  intro G _ _ T M hyp hnot hnab D hc2
  by_contra hns
  have hd : Module.finrank (ZMod 2) D.V = 4 := hc2.1
  have hsymp : IsSymplectic D.B := ⟨D.B_isAlt, D.B_nondegenerate⟩
  obtain ⟨Mo⟩ := P4InspSp.p4inspsp_exists_model hsymp hd
  obtain ⟨ρ, hinj, -, -, hrange⟩ := P4InspSp.p4inspsp_exists_embedding hsymp hd Mo
  have hle : D.img (mcOf T) ≤ ρ.range := (img_le_spSub D).trans hrange
  let φ : ↥(D.img (mcOf T)) →* Equiv.Perm (Fin 6) :=
    (MonoidHom.ofInjective hinj).symm.toMonoidHom.comp (Subgroup.inclusion hle)
  have hφ : Function.Injective φ :=
    (MonoidHom.ofInjective hinj).symm.injective.comp (Subgroup.inclusion_injective hle)
  rcases S6Class.exists_normal_alt_of_not_isSolvable φ hφ hns with h5 | h6
  · exact hA5 G T M hyp hnot hnab D hd h5
  · exact hA6 G T M hyp hnot hnab D hd h6

end SzPS8

end CFSG.Quasithin
