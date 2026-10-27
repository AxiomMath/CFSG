module

public import CFSG.Quasithin.EmptyFaithful.S143EC
public import CFSG.Quasithin.EmptyFaithful.S1421Defs
public import CFSG.Quasithin.Vol2.Ch12Sec8NonabEleven
public import CFSG.Quasithin.Vol2.Ch12Sec8NonabHatImg

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143V

variable {G : Type} [Group G] [Finite G] {T M L : Subgroup G}

@[expose] noncomputable def rhoH (h : Hyp1281Two G T M L) (D : HatModel T M) :
    ↥(mcOf T) →* (D.V ≃ₗ[ZMod 2] D.V) :=
  D.rho.comp (Subgroup.inclusion h.g1_le_normalizer_uOfL22)

theorem rhoH_apply (h : Hyp1281Two G T M L) (D : HatModel T M) (x : ↥(mcOf T))
    (hx : (x : G) ∈ Subgroup.normalizer (uOfL22 T M : Set G)) :
    rhoH h D x = D.rho ⟨x, hx⟩ := rfl

theorem range_rhoH (h : Hyp1281Two G T M L) (D : HatModel T M) :
    (rhoH h D).range = D.img (mcOf T) := by
  ext γ
  rw [MonoidHom.mem_range, HatModel.mem_img]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, x.2, h.g1_le_normalizer_uOfL22 x.2, rfl⟩
  · rintro ⟨x, hxH, hxN, rfl⟩
    exact ⟨⟨x, hxH⟩, rfl⟩

theorem map_rhoH (h : Hyp1281Two G T M L) (D : HatModel T M) {K : Subgroup G} (hK : K ≤ mcOf T) :
    (K.subgroupOf (mcOf T)).map (rhoH h D) = D.img K := by
  ext γ
  rw [Subgroup.mem_map, HatModel.mem_img]
  constructor
  · rintro ⟨x, hxK, rfl⟩
    exact ⟨x, Subgroup.mem_subgroupOf.mp hxK, h.g1_le_normalizer_uOfL22 x.2, rfl⟩
  · rintro ⟨x, hxK, hxN, rfl⟩
    exact ⟨⟨x, hK hxK⟩, Subgroup.mem_subgroupOf.mpr hxK, rfl⟩

theorem mem_ker_rhoH (h : Hyp1281Two G T M L) (D : HatModel T M) (x : ↥(mcOf T)) :
    x ∈ (rhoH h D).ker ↔ (x : G) ∈ Hyp1281Two.centralizerHat T M := by
  have hxN : (x : G) ∈ Subgroup.normalizer (uOfL22 T M : Set G) :=
    h.g1_le_normalizer_uOfL22 x.2
  rw [MonoidHom.mem_ker, rhoH_apply h D x hxN, D.rho_eq_one_iff]
  constructor
  · intro h1
    exact ⟨x.2, normalizer_le_normalizer_centerOf _ hxN, h1⟩
  · intro h1
    exact h1.2.2

theorem isSylowTwoOf_img_T (h : Hyp1281Two G T M L) (D : HatModel T M) :
    IsSylowTwoOf (D.img T) (D.img (mcOf T)) := by
  have hT : T ≤ mcOf T := h.almostSpecialHyp_g1.T_le_H
  have := S143.isSylowTwoOf_map_range' h.almostSpecialHyp_g1.sylow_H (rhoH h D)
  rwa [map_rhoH h D hT, range_rhoH h D] at this

end S143V

end CFSG.Quasithin
