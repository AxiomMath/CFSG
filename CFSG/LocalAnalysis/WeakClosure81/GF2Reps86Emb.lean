module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Statement
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps86

open CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Fstar)
open CFSG.Open (genFittingFStar)

section FStar

variable {G : Type} [Group G]

private theorem fstar_le (Y : Subgroup G) : Fstar Y ≤ Y :=
  Subgroup.map_subtype_le _

private theorem fstar_subgroupOf (Y : Subgroup G) :
    (Fstar Y).subgroupOf Y = genFittingFStar ↥Y :=
  Subgroup.comap_map_eq_self_of_injective Y.subtype_injective _

private theorem le_normalizer_fstar (Y : Subgroup G) :
    Y ≤ Subgroup.normalizer (Fstar Y : Set G) := by
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer (fstar_le Y)).1 ?_
  rw [fstar_subgroupOf]
  exact CFSG.ComponentClassification.GeneralizedFitting.normal ↥Y

variable [Finite G]

private theorem centralizer_fstar_le (Y : Subgroup G) :
    Y ⊓ Subgroup.centralizer (Fstar Y : Set G) ≤ Fstar Y := by
  intro x hx
  have hy : (⟨x, hx.1⟩ : ↥Y) ∈ Subgroup.centralizer (genFittingFStar ↥Y : Set ↥Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx.2 (u : G) ⟨u, hu, rfl⟩)
  exact ⟨_, CFSG.ComponentClassification.GeneralizedFitting.centralizer_le ↥Y hy, rfl⟩

end FStar

theorem exists_embedding_of_fstar {W : Type} [CommGroup W] [Finite W] {Y L : Subgroup (MulAut W)}
    (hLY : L ≤ Y) (hF : Fstar Y = L) {n : ℕ} (hn5 : 5 ≤ n) (hn6 : n ≠ 6)
    (ι : ↥L ≃* alternatingGroup (Fin n)) :
    ∃ ψ : ↥Y →* Equiv.Perm (Fin n), Function.Injective ψ ∧ alternatingGroup (Fin n) ≤ ψ.range ∧
      altPre ψ = L ∧ ∀ l : ↥L, ψ (Subgroup.inclusion hLY l) = (ι l : Equiv.Perm (Fin n)) := by
  have hYN : Y ≤ Subgroup.normalizer (L : Set (MulAut W)) := by
    rw [← hF]; exact le_normalizer_fstar Y
  have hcent : Y ⊓ Subgroup.centralizer (L : Set (MulAut W)) ≤ L := by
    rw [← hF]; exact centralizer_fstar_le Y
  set cY : ↥Y →* MulAut ↥L := L.normalizerMonoidHom.comp (Subgroup.inclusion hYN)
  have hcY_apply : ∀ (y : ↥Y) (l : ↥L),
      ((cY y l : ↥L) : MulAut W) = (y : MulAut W) * l * (y : MulAut W)⁻¹ := fun _ _ => rfl
  have hb := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn5 hn6
  set cA : Equiv.Perm (Fin n) ≃* MulAut (alternatingGroup (Fin n)) :=
    MulEquiv.ofBijective _ hb
  set ψ : ↥Y →* Equiv.Perm (Fin n) :=
    cA.symm.toMonoidHom.comp ((MulAut.congr ι).toMonoidHom.comp cY)
  have hcAψ : ∀ y : ↥Y, cA (ψ y) = MulAut.congr ι (cY y) := fun y => cA.apply_symm_apply _
  have hext : ∀ l : ↥L, ψ (Subgroup.inclusion hLY l) = (ι l : Equiv.Perm (Fin n)) := by
    intro l
    apply cA.injective
    rw [hcAψ]
    refine MulEquiv.ext fun a => Subtype.ext ?_
    obtain ⟨y, rfl⟩ := ι.surjective a
    have hy : cY (Subgroup.inclusion hLY l) y = l * y * l⁻¹ := Subtype.ext rfl
    rw [show cA (ι l : Equiv.Perm (Fin n)) = MulAut.conjNormal (ι l : Equiv.Perm (Fin n)) from rfl,
      MulAut.conjNormal_apply, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      ι.symm_apply_apply, hy, map_mul, map_mul, map_inv]
    rfl
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro y hy1
    have hc : cY y = 1 := by
      have h2 : MulAut.congr ι (cY y) = MulAut.congr ι 1 := by
        rw [← hcAψ, hy1, map_one, map_one]
      exact (MulAut.congr ι).injective h2
    have hmem : (y : MulAut W) ∈ Y ⊓ Subgroup.centralizer (L : Set (MulAut W)) := by
      refine Subgroup.mem_inf.2 ⟨y.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have h2 : (y : MulAut W) * l * (y : MulAut W)⁻¹ = l := by
        rw [← hcY_apply y ⟨l, hl⟩, hc]
        rfl
      calc l * (y : MulAut W) = (y : MulAut W) * l * (y : MulAut W)⁻¹ * y := by rw [h2]
        _ = y * l := by group
    have hyL : (y : MulAut W) ∈ L := hcent hmem
    have h2 := hext ⟨y, hyL⟩
    rw [show Subgroup.inclusion hLY ⟨(y : MulAut W), hyL⟩ = y from rfl, hy1] at h2
    have h3 : ι ⟨y, hyL⟩ = 1 := Subtype.ext h2.symm
    have h4 : (⟨y, hyL⟩ : ↥L) = 1 := ι.injective (h3.trans (map_one ι).symm)
    exact Subtype.ext (congrArg (fun z : ↥L => (z : MulAut W)) h4)
  refine ⟨ψ, hinj, fun σ hσ => ?_, altPre_eq_of_restrict hLY hinj ι.toMonoidHom ι.surjective hext,
    hext⟩
  obtain ⟨l, hl⟩ := ι.surjective ⟨σ, hσ⟩
  exact ⟨Subgroup.inclusion hLY l, by rw [hext, hl]⟩

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps86

end
