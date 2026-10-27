module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21f
public import CFSG.LieType.SteinbergBRMulEquivCores

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Semidihedral.Principal.CoprimeFixedPoint (quotientAction quotientAction_mk)

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def inducedBarInfAutHom (L : Subgroup G) :
    Subgroup.normalizer (L : Set G) →* MulAut (BarInf L) :=
  quotientAction L.normalizerMonoidHom (CFSG.solvableRadical ↥L) fun x n hn => by
    rw [← CFSG.LieType.SteinbergBR.solvableRadical_map_equiv (L.normalizerMonoidHom x)]
    exact Subgroup.mem_map_of_mem _ hn

@[expose] noncomputable def inducedQuotInfAutHom (L : Subgroup G) :
    Subgroup.normalizer (L : Set G) →* MulAut (BarInf L ⧸ Subgroup.center (BarInf L)) :=
  quotientAction (inducedBarInfAutHom L) (Subgroup.center (BarInf L)) fun x z hz => by
    rw [← Subgroup.map_center_eq (inducedBarInfAutHom L x)]
    exact Subgroup.mem_map_of_mem _ hz

@[expose] noncomputable def inducedQuotInfAut (L : Subgroup G) (x : G)
    (hx : x ∈ Subgroup.normalizer (L : Set G)) :
    MulAut (BarInf L ⧸ Subgroup.center (BarInf L)) :=
  inducedQuotInfAutHom L ⟨x, hx⟩

theorem inducedQuotInfAut_mk (L : Subgroup G) (x : G)
    (hx : x ∈ Subgroup.normalizer (L : Set G)) (l : ↥L) :
    inducedQuotInfAut L x hx (QuotientGroup.mk (QuotientGroup.mk l)) =
      QuotientGroup.mk (QuotientGroup.mk
        (⟨x * (l : G) * x⁻¹, (Subgroup.mem_normalizer_iff.mp hx l).mp l.2⟩ : ↥L)) := by
  rw [inducedQuotInfAut, inducedQuotInfAutHom, quotientAction_mk, inducedBarInfAutHom,
    quotientAction_mk]
  congr 2

theorem inducedQuotInf_inducedQuotInfAut (L : Subgroup G) (x : G)
    (hx : x ∈ Subgroup.normalizer (L : Set G)) :
    InducedQuotInf L x (inducedQuotInfAut L x hx) := by
  intro l l' hll'
  rw [inducedQuotInfAut_mk,
    show (⟨x * (l : G) * x⁻¹, (Subgroup.mem_normalizer_iff.mp hx l).mp l.2⟩ : ↥L) = l' from
      Subtype.ext hll'.symm]

theorem inducedQuotInfAut_mul (L : Subgroup G) {x y : G}
    (hx : x ∈ Subgroup.normalizer (L : Set G)) (hy : y ∈ Subgroup.normalizer (L : Set G))
    (hxy : x * y ∈ Subgroup.normalizer (L : Set G)) :
    inducedQuotInfAut L (x * y) hxy = inducedQuotInfAut L x hx * inducedQuotInfAut L y hy := by
  change inducedQuotInfAutHom L ⟨x * y, hxy⟩ =
    inducedQuotInfAutHom L ⟨x, hx⟩ * inducedQuotInfAutHom L ⟨y, hy⟩
  rw [← map_mul]
  exact congrArg _ (Subtype.ext rfl)

theorem orderOf_inducedQuotInfAut_dvd (L : Subgroup G) {x : G}
    (hx : x ∈ Subgroup.normalizer (L : Set G)) :
    orderOf (inducedQuotInfAut L x hx) ∣ orderOf x := by
  have h := orderOf_map_dvd (inducedQuotInfAutHom L) (⟨x, hx⟩ : Subgroup.normalizer (L : Set G))
  rwa [Subgroup.orderOf_mk] at h

theorem inducedQuotInf_unique (L : Subgroup G) {x : G}
    (hx : x ∈ Subgroup.normalizer (L : Set G))
    {θ θ' : MulAut (BarInf L ⧸ Subgroup.center (BarInf L))}
    (hθ : InducedQuotInf L x θ) (hθ' : InducedQuotInf L x θ') : θ = θ' := by
  ext z
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective z
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective w
  let v' : ↥L := ⟨x * (v : G) * x⁻¹, (Subgroup.mem_normalizer_iff.mp hx v).mp v.2⟩
  rw [hθ v v' rfl, hθ' v v' rfl]

@[expose] noncomputable def piBarInf (L : Subgroup G) :
    ↥L →* BarInf L ⧸ Subgroup.center (BarInf L) :=
  (QuotientGroup.mk' (Subgroup.center (BarInf L))).comp
    (QuotientGroup.mk' (CFSG.solvableRadical ↥L))

theorem inducedQuotInfAut_piBarInf (L : Subgroup G) (x : G)
    (hx : x ∈ Subgroup.normalizer (L : Set G)) (l : ↥L) :
    inducedQuotInfAut L x hx (piBarInf L l) =
      piBarInf L ⟨x * (l : G) * x⁻¹, (Subgroup.mem_normalizer_iff.mp hx l).mp l.2⟩ :=
  inducedQuotInfAut_mk L x hx l

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
