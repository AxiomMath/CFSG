module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelModuleM
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelEFrame
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelLiftE

public section

namespace CFSG.StandardType.E6ThreeModel

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc.E6Three
  CFSG.RankThree.CentralCover CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {K : Type} [Field K] [Finite K]

omit [Finite K]
  in
@[expose] noncomputable def eFrameCartanGen [CharP K 2] {ζ : Kˣ} (hζ : ζ ^ 3 = 1) :
    CartanGen (eFrame K ζ hζ) Kˣ := by
  have hTA : torusGroup .E6 K ≤ adjointGroup .E6 K :=
    (Subgroup.closure_le _).2 (by
      rintro _ ⟨⟨i, t⟩, rfl⟩
      exact torusElt_mem_adjointGroup (τ := .E6) (K := K) i t)
  let d : Fin 6 → Kˣ →* adjointGroup .E6 K := fun j => {
    toFun := fun s => ⟨torusElt .E6 K j s, torusElt_mem_adjointGroup (τ := .E6) (K := K) j s⟩
    map_one' := Subtype.ext (torusElt_one (τ := .E6) (R := K) j)
    map_mul' := fun s t => Subtype.ext (torusElt_mul (τ := .E6) (R := K) j s t) }
  refine { d := d, tor_eq := ?_, comm := ?_, conj := ?_ }
  · show (torusGroup .E6 K).subgroupOf (adjointGroup .E6 K) = ⨆ j, (d j).range
    have hkey : (⨆ j, (d j).range).map (adjointGroup .E6 K).subtype = torusGroup .E6 K := by
      rw [Subgroup.map_iSup]
      simp only [MonoidHom.map_range]
      refine le_antisymm (iSup_le fun j => ?_) ?_
      · rintro y ⟨s, rfl⟩
        exact torusElt_mem_torusGroup (τ := .E6) (R := K) j s
      · refine (Subgroup.closure_le _).2 ?_
        rintro _ ⟨⟨j, s⟩, rfl⟩
        exact Subgroup.mem_iSup_of_mem j (MonoidHom.mem_range.mpr ⟨s, rfl⟩)
    have hsub : Subgroup.map (adjointGroup .E6 K).subtype
        ((torusGroup .E6 K).subgroupOf (adjointGroup .E6 K)) = torusGroup .E6 K := by
      rw [show (torusGroup .E6 K).subgroupOf (adjointGroup .E6 K) =
          Subgroup.comap (adjointGroup .E6 K).subtype (torusGroup .E6 K) from rfl,
        Subgroup.map_comap_eq, Subgroup.range_subtype]
      exact le_antisymm inf_le_right (le_inf hTA le_rfl)
    apply Subgroup.map_injective (Subgroup.subtype_injective (adjointGroup .E6 K))
    rw [hkey, hsub]
  · intro j k s t
    apply Subtype.ext
    exact torusElt_mul_comm (τ := .E6) (R := K) j k s t
  · intro i j s
    apply Subtype.ext
    exact weylElt_one_mul_torusElt_mul_inv (τ := .E6) (R := K) i j s

omit [Finite K]
  in
theorem eFrame_cartanGen [CharP K 2] {ζ : Kˣ} (hζ : ζ ^ 3 = 1) :
    Nonempty (CartanGen (eFrame K ζ hζ) Kˣ) :=
  ⟨eFrameCartanGen hζ⟩

theorem eFrame_modules [CharP K 2] {ζ : Kˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1) :
    (eFrame K ζ hζ).ModuleOK := by
  obtain ⟨G⟩ := eFrame_cartanGen (K := K) hζ
  exact moduleOK_of_cartanGen _ eFrame_center (eFrame_faithful hζo hζ) (eFrame_weyl hζo hζ) G

end CFSG.StandardType.E6ThreeModel
