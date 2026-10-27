module

public import CFSG.RankThree.GF2n.Tim78RootType
public import CFSG.CGT.Timmesfeld75.CentralQuotient
public import CFSG.GroupTheory.QuasiDihedralFusion.Transport

public section

namespace CFSG.RankThree.GF2n

open CFSG.CGT.Timmesfeld75

theorem maximal_abelianNormal_map_mulEquiv {H K : Type*} [Group H] [Group K] (e : H ≃* K)
    {M V : Subgroup H} (h : Maximal (fun U : Subgroup H => U ≤ M ∧
      M ≤ Subgroup.normalizer (U : Set H) ∧ IsMulCommutative U) V) :
    Maximal (fun U : Subgroup K => U ≤ M.map e.toMonoidHom ∧
      M.map e.toMonoidHom ≤ Subgroup.normalizer (U : Set K) ∧ IsMulCommutative U)
      (V.map e.toMonoidHom) := by
  have hcomm : ∀ U : Subgroup H, IsMulCommutative U →
      IsMulCommutative (U.map e.toMonoidHom) := fun U hU =>
    CFSG.QuasiDihedralFusion.isMulCommutative_of_mulEquiv
      (Subgroup.equivMapOfInjective U e.toMonoidHom e.injective) hU
  have hcomm' : ∀ U : Subgroup K, IsMulCommutative U →
      IsMulCommutative (U.map e.symm.toMonoidHom) := fun U hU =>
    CFSG.QuasiDihedralFusion.isMulCommutative_of_mulEquiv
      (Subgroup.equivMapOfInjective U e.symm.toMonoidHom e.symm.injective) hU
  have hforward : ∀ U : Subgroup K, (U.map e.symm.toMonoidHom).map e.toMonoidHom = U := by
    intro U
    rw [Subgroup.map_map]
    have hcomp : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id K :=
      MonoidHom.ext e.apply_symm_apply
    rw [hcomp, Subgroup.map_id]
  have hback : ∀ U : Subgroup H, (U.map e.toMonoidHom).map e.symm.toMonoidHom = U := by
    intro U
    rw [Subgroup.map_map]
    have hcomp : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id H :=
      MonoidHom.ext e.symm_apply_apply
    rw [hcomp, Subgroup.map_id]
  refine ⟨⟨Subgroup.map_mono h.1.1, ?_, hcomm V h.1.2.2⟩, ?_⟩
  · rw [← Subgroup.map_equiv_normalizer_eq V e]
    exact Subgroup.map_mono h.1.2.1
  · intro U hU hVU
    have hUM : U.map e.symm.toMonoidHom ≤ M := by
      refine (Subgroup.map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp ?_
      simpa only [hforward] using hU.1
    have hMU : M ≤ Subgroup.normalizer (U.map e.symm.toMonoidHom : Subgroup H) := by
      refine (Subgroup.map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp ?_
      rw [Subgroup.map_equiv_normalizer_eq (U.map e.symm.toMonoidHom) e]
      simpa only [hforward] using hU.2.1
    have hle : V ≤ U.map e.symm.toMonoidHom := by
      have := Subgroup.map_mono (f := e.symm.toMonoidHom) hVU
      simpa only [hback] using this
    have hmax := h.2 ⟨hUM, hMU, hcomm' U hU.2.2⟩ hle
    have := Subgroup.map_mono (f := e.toMonoidHom) hmax
    simpa only [hforward] using this

theorem weaklyClosedIn_map_mulEquiv {H K : Type*} [Group H] [Group K] (e : H ≃* K)
    {R Z : Subgroup H} (h : WeaklyClosedIn R Z) :
    WeaklyClosedIn (R.map e.toMonoidHom) (Z.map e.toMonoidHom) := by
  refine ⟨Subgroup.map_mono h.1, fun g' hg' => ?_⟩
  obtain ⟨g, rfl⟩ := e.surjective g'
  have hconj : conjSubgroup (e g) (R.map e.toMonoidHom) =
      (conjSubgroup g R).map e.toMonoidHom := by
    simpa only [MulEquiv.coe_toMonoidHom] using
      (CFSG.CGT.Timmesfeld75.map_conjSubgroup e.toMonoidHom g R).symm
  rw [hconj] at hg' ⊢
  have hle : conjSubgroup g R ≤ Z :=
    (Subgroup.map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp hg'
  rw [h.2 g hle]

end CFSG.RankThree.GF2n

namespace CFSG.RankThree.GF2n.Tim78

open CFSG.CGT.Timmesfeld75

variable {G : Type*} [Group G]

theorem isRootTypeTI_conjSubgroup {V : Subgroup G} (h : IsRootTypeTI V) (g : G) :
    IsRootTypeTI (conjSubgroup g V) := by
  refine ⟨CFSG.RankThree.GF2n.isTI_conjSubgroup h.1 g, fun k hk a ha b hb => ?_⟩
  rw [conjSubgroup_conjSubgroup] at hk hb
  exact commute_of_isRootTypeTI h (g := g) (h := k * g) hk a ha b hb

end CFSG.RankThree.GF2n.Tim78
