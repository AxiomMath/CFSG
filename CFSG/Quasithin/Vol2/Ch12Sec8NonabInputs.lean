module

public import CFSG.Quasithin.Vol2.Ch12Sec8NonabG112Def
public import CFSG.Quasithin.Vol2.Ch12Sec8NonabHatImg

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped commutatorElement Pointwise

namespace Hyp1281Two

variable {G : Type} [Group G] [Finite G] {T M L : Subgroup G}

theorem isQuotientOfSQTK_img (h : Hyp1281Two G T M L) (D : HatModel T M) :
    IsQuotientOfSQTKTauCeti
      ↥(D.img (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))) := by
  have hV1T : quasithinOmegaOneCenter T ≤ T :=
    (omegaOneCenter_le_VZ T M).trans h.isTwoReducedIn.2
  have hV1p : IsPGroup 2 (quasithinOmegaOneCenter T) := h.sylow.1.to_le hV1T
  have hV1H : quasithinOmegaOneCenter T ≤
      Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := fun w hw =>
    Subgroup.mem_centralizer_iff.mpr fun v hv =>
      Subgroup.mem_centralizer_iff.mp (h.omegaOneCenter_le_centerOf_uOfL22 hw).2 v
        (VZ_le_uOfL22 T M (omegaOneCenter_le_VZ T M hv))
  have hHnorm : Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤
      Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    h.normalizer_Z_eq_centralizer.symm.le
  have hle : quasithinOmegaOneCenter T ≤
      pCoreOf 2 (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) :=
    le_pCoreOf_of_le_normalizer 2 hV1H hHnorm hV1p
  obtain ⟨z, hzZ, hz1, -⟩ := h.exists_zgen
  have hHc : pCoreOf 2 (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ≠ ⊥ := by
    intro hbot
    have hz : z ∈ pCoreOf 2 (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) := hle hzZ
    rw [hbot, Subgroup.mem_bot] at hz
    exact hz1 hz
  have hHN : Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤
      Subgroup.normalizer (uOfL22 T M : Set G) := fun x hx => h.g1_le_normalizer_uOfL22 hx
  let f : ↥(Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) →*
      (D.V ≃ₗ[ZMod 2] D.V) := D.rho.comp (Subgroup.inclusion hHN)
  let φ : ↥(Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) →*
      ↥(D.img (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))) :=
    f.codRestrict _ (fun x => HatModel.rho_mem_img x.2 (hHN x.2))
  refine ⟨↥(Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)), inferInstance,
    inferInstance, stronglyQuasithin_of_pCoreOf_ne_bot h.qtke hHc,
    kGroup_of_pCoreOf_ne_bot h.qtke h.simple h.nonabelian hHc, φ, ?_⟩
  intro γ
  obtain ⟨x, hxK, hxN, hγ⟩ := HatModel.mem_img.mp γ.2
  exact ⟨⟨x, hxK⟩, Subtype.ext hγ⟩

end Hyp1281Two

end CFSG.Quasithin
