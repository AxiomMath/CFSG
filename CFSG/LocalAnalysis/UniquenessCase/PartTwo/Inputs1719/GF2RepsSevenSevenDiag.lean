module

public import CFSG.LargeExtraspecial.S5Comp
import CFSG.HardMathSupport.Solomon.Coordinator.I2_5
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {W : Type} [CommGroup W] [Finite W]

theorem mulAut_conj_comp {G : Type} [Group G] (a b : G) :
    (MulAut.conj a).toMonoidHom.comp (MulAut.conj b).toMonoidHom =
      (MulAut.conj (a * b)).toMonoidHom := by
  ext x
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  group

@[expose] def conjSub77 {W : Type} [CommGroup W] (K : Subgroup (MulAut W))
    (d : MulAut W) : Subgroup (MulAut W) :=
  K.map (MulAut.conj d).toMonoidHom

@[expose] def orbitJoin77 {W : Type} [CommGroup W] (K D : Subgroup (MulAut W)) :
    Subgroup (MulAut W) :=
  ⨆ d : ↥D, conjSub77 K (d : MulAut W)

variable {Y K D : Subgroup (MulAut W)}
variable [Fintype ↥D] [DecidableEq ↥D]

@[expose] noncomputable def diagCoord77 {W : Type} [CommGroup W]
    (K D : Subgroup (MulAut W)) (d : ↥D) : ↥K →* MulAut W :=
  (MulAut.conj (d : MulAut W)).toMonoidHom.comp K.subtype

theorem diagCoord_range {W : Type} [CommGroup W] (K D : Subgroup (MulAut W)) (d : ↥D) :
    (diagCoord77 K D d).range = conjSub77 K (d : MulAut W) := by
  rw [diagCoord77, MonoidHom.range_comp, Subgroup.range_subtype, conjSub77]

theorem inv_mul_mem_normalizer_of_conjSub_eq
    (hDreg : D ⊓ Subgroup.normalizer (K : Set (MulAut W)) = ⊥)
    {d e : ↥D} (h : conjSub77 K (d : MulAut W) = conjSub77 K (e : MulAut W)) :
    (e : MulAut W)⁻¹ * (d : MulAut W) = 1 := by
  have h1 := congrArg (fun L : Subgroup (MulAut W) =>
    L.map (MulAut.conj (e : MulAut W)⁻¹).toMonoidHom) h
  simp only [conjSub77] at h1
  rw [Subgroup.map_map, Subgroup.map_map, mulAut_conj_comp, mulAut_conj_comp] at h1
  rw [inv_mul_cancel, map_one] at h1
  rw [show (MulEquiv.toMonoidHom (1 : MulAut (MulAut W))) = MonoidHom.id _ from rfl,
    Subgroup.map_id] at h1
  have hmap : K.map (MulAut.conj ((e : MulAut W)⁻¹ * (d : MulAut W))).toMonoidHom = K := h1
  have hnorm : (e : MulAut W)⁻¹ * (d : MulAut W) ∈
      Subgroup.normalizer (K : Set (MulAut W)) :=
    (Subgroup.mem_normalizer_iff_map_conj_eq).2 hmap
  have hmemD : (e : MulAut W)⁻¹ * (d : MulAut W) ∈ D :=
    D.mul_mem (D.inv_mem e.2) d.2
  have hbot : (e : MulAut W)⁻¹ * (d : MulAut W) ∈ (⊥ : Subgroup (MulAut W)) := by
    rw [← hDreg]
    exact ⟨hmemD, hnorm⟩
  exact Subgroup.mem_bot.mp hbot

theorem conjSub_commute_of_ne (hK : IsComponentOf K Y) (hDY : D ≤ Y)
    (hDreg : D ⊓ Subgroup.normalizer (K : Set (MulAut W)) = ⊥)
    {d e : ↥D} (hne : d ≠ e) :
    ⁅conjSub77 K (d : MulAut W), conjSub77 K (e : MulAut W)⁆ = ⊥ := by
  have hd : IsComponentOf (conjSub77 K (d : MulAut W)) Y :=
    CFSG.LargeExtraspecial.S5.isComponentOf_map_conj hK (hDY d.2)
  have he : IsComponentOf (conjSub77 K (e : MulAut W)) Y :=
    CFSG.LargeExtraspecial.S5.isComponentOf_map_conj hK (hDY e.2)
  have hne' : conjSub77 K (d : MulAut W) ≠ conjSub77 K (e : MulAut W) := by
    intro h
    have h1 := inv_mul_mem_normalizer_of_conjSub_eq hDreg h
    exact hne (Subtype.ext (inv_mul_eq_one.mp h1).symm)
  exact CFSG.LargeExtraspecial.S5.commute_of_isComponentOf_ne hd he hne'

theorem diag_comm77 (hK : IsComponentOf K Y) (hDY : D ≤ Y)
    (hDreg : D ⊓ Subgroup.normalizer (K : Set (MulAut W)) = ⊥) :
    Pairwise fun d e : ↥D => ∀ x y : ↥K,
      Commute (diagCoord77 K D d x) (diagCoord77 K D e y) := by
  intro d e hne x y
  have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    (conjSub_commute_of_ne hK hDY hDreg hne)
  have hxd : diagCoord77 K D d x ∈ conjSub77 K (d : MulAut W) := by
    rw [← diagCoord_range]
    exact MonoidHom.mem_range.mpr ⟨x, rfl⟩
  have hye : diagCoord77 K D e y ∈ conjSub77 K (e : MulAut W) := by
    rw [← diagCoord_range]
    exact MonoidHom.mem_range.mpr ⟨y, rfl⟩
  exact (Subgroup.mem_centralizer_iff.mp (hle hxd) _ hye).symm

@[expose] noncomputable def diagHom77 (hK : IsComponentOf K Y) (hDY : D ≤ Y)
    (hDreg : D ⊓ Subgroup.normalizer (K : Set (MulAut W)) = ⊥) : ↥K →* MulAut W :=
  (MonoidHom.noncommPiCoprod (fun d : ↥D => diagCoord77 K D d) (diag_comm77 hK hDY hDreg)).comp
    (Pi.constMonoidHom ↥D ↥K)

theorem diagHom_apply77 (hK : IsComponentOf K Y) (hDY : D ≤ Y)
    (hDreg : D ⊓ Subgroup.normalizer (K : Set (MulAut W)) = ⊥) (x : ↥K) :
    diagHom77 hK hDY hDreg x =
      Finset.univ.noncommProd (fun d : ↥D => diagCoord77 K D d x)
        (by
          intro d _ e _ hde
          exact diag_comm77 hK hDY hDreg hde x x) := by
  classical
  rw [diagHom77, MonoidHom.comp_apply, MonoidHom.noncommPiCoprod_apply]
  exact Finset.noncommProd_congr rfl (fun i _ => rfl) _

theorem diagHom_conj_mem_D (hK : IsComponentOf K Y) (hDY : D ≤ Y)
    (hDreg : D ⊓ Subgroup.normalizer (K : Set (MulAut W)) = ⊥)
    {e : MulAut W} (he : e ∈ D) (x : ↥K) :
    MulAut.conj e (diagHom77 hK hDY hDreg x) = diagHom77 hK hDY hDreg x := by
  classical
  rw [diagHom_apply77]
  rw [Finset.map_noncommProd]
  have hfun : (fun d : ↥D => MulAut.conj e (diagCoord77 K D d x)) =
      fun d : ↥D => diagCoord77 K D (Equiv.mulLeft ⟨e, he⟩ d) x := by
    funext d
    ext w
    simp only [diagCoord77, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, Subgroup.coe_subtype, Subgroup.coe_mul, Equiv.coe_mulLeft]
    group
  refine (Finset.noncommProd_congr rfl (fun d _ => congrFun hfun d) _).trans ?_
  exact CFSG.HardMathSupport.Solomon.Coordinator.i25_noncommProd_equiv (Equiv.mulLeft ⟨e, he⟩)
    (fun d : ↥D => diagCoord77 K D d x) _ _

theorem diagHom_conj_mem_normalizer (hK : IsComponentOf K Y) (hDY : D ≤ Y)
    (hDreg : D ⊓ Subgroup.normalizer (K : Set (MulAut W)) = ⊥)
    {b : MulAut W} (hbK : b ∈ Subgroup.normalizer (K : Set (MulAut W)))
    (hbD : ∀ d ∈ D, b * d = d * b) (x : ↥K) :
    MulAut.conj b (diagHom77 hK hDY hDreg x) =
      diagHom77 hK hDY hDreg ⟨b * (x : MulAut W) * b⁻¹,
        (Subgroup.mem_normalizer_iff.mp hbK (x : MulAut W)).mp x.2⟩ := by
  classical
  rw [diagHom_apply77]
  rw [Finset.map_noncommProd]
  have hmem : b * (x : MulAut W) * b⁻¹ ∈ K :=
    (Subgroup.mem_normalizer_iff.mp hbK (x : MulAut W)).mp x.2
  have hfun : (fun d : ↥D => MulAut.conj b (diagCoord77 K D d x)) =
      fun d : ↥D => diagCoord77 K D d ⟨b * (x : MulAut W) * b⁻¹, hmem⟩ := by
    funext d
    have hbd : b * (d : MulAut W) = (d : MulAut W) * b := hbD d d.2
    simp only [diagCoord77, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      Subgroup.coe_subtype]
    calc MulAut.conj b (MulAut.conj (d : MulAut W) (x : MulAut W))
        = MulAut.conj (b * (d : MulAut W)) (x : MulAut W) := by
          simp only [MulAut.conj_apply]
          group
      _ = MulAut.conj ((d : MulAut W) * b) (x : MulAut W) := by rw [hbd]
      _ = MulAut.conj (d : MulAut W) (MulAut.conj b (x : MulAut W)) :=
          by simp only [MulAut.conj_apply]; group
      _ = MulAut.conj (d : MulAut W) (b * (x : MulAut W) * b⁻¹) := by
          simp only [MulAut.conj_apply]
  refine (Finset.noncommProd_congr rfl (fun d _ => congrFun hfun d) _).trans ?_
  exact (diagHom_apply77 hK hDY hDreg _).symm

theorem diagHom_conj_mem_centralizer (hK : IsComponentOf K Y) (hDY : D ≤ Y)
    (hDreg : D ⊓ Subgroup.normalizer (K : Set (MulAut W)) = ⊥)
    {c : MulAut W} (hcK : c ∈ Subgroup.centralizer (K : Set (MulAut W)))
    (hcD : ∀ d ∈ D, c * d = d * c) (x : ↥K) :
    MulAut.conj c (diagHom77 hK hDY hDreg x) = diagHom77 hK hDY hDreg x := by
  classical
  rw [diagHom_apply77]
  rw [Finset.map_noncommProd]
  have hcx : c * (x : MulAut W) = (x : MulAut W) * c :=
    (Subgroup.mem_centralizer_iff.mp hcK (x : MulAut W) x.2).symm
  have hfun : (fun d : ↥D => MulAut.conj c (diagCoord77 K D d x)) =
      fun d : ↥D => diagCoord77 K D d x := by
    funext d
    have hcd : c * (d : MulAut W) = (d : MulAut W) * c := hcD d d.2
    have hcx' : MulAut.conj c (x : MulAut W) = (x : MulAut W) := by
      rw [MulAut.conj_apply, hcx]
      group
    simp only [diagCoord77, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      Subgroup.coe_subtype]
    calc MulAut.conj c (MulAut.conj (d : MulAut W) (x : MulAut W))
        = MulAut.conj (c * (d : MulAut W)) (x : MulAut W) := by
          simp only [MulAut.conj_apply]
          group
      _ = MulAut.conj ((d : MulAut W) * c) (x : MulAut W) := by rw [hcd]
      _ = MulAut.conj (d : MulAut W) (MulAut.conj c (x : MulAut W)) :=
          by simp only [MulAut.conj_apply]; group
      _ = MulAut.conj (d : MulAut W) (x : MulAut W) := by rw [hcx']
  refine (Finset.noncommProd_congr rfl (fun d _ => congrFun hfun d) _).trans ?_
  exact (diagHom_apply77 hK hDY hDreg x).symm

theorem iSup_erase_centralizes (hK : IsComponentOf K Y) (hDY : D ≤ Y)
    (hDreg : D ⊓ Subgroup.normalizer (K : Set (MulAut W)) = ⊥) :
    (⨆ d ∈ (Finset.univ.erase (1 : ↥D)), conjSub77 K (d : MulAut W)) ≤
      Subgroup.centralizer (K : Set (MulAut W)) := by
  classical
  refine iSup₂_le fun d hd => ?_
  have hdne : d ≠ (1 : ↥D) := (Finset.mem_erase.mp hd).1
  have hneq : conjSub77 K (d : MulAut W) ≠ K := by
    intro h
    have hmap : K.map (MulAut.conj (d : MulAut W)).toMonoidHom = K := h
    have hnorm : (d : MulAut W) ∈ Subgroup.normalizer (K : Set (MulAut W)) :=
      (Subgroup.mem_normalizer_iff_map_conj_eq).2 hmap
    have hbot : (d : MulAut W) ∈ (⊥ : Subgroup (MulAut W)) := by
      rw [← hDreg]
      exact ⟨d.2, hnorm⟩
    exact hdne (Subtype.ext (Subgroup.mem_bot.mp hbot))
  have hcomm := CFSG.LargeExtraspecial.S5.commute_of_isComponentOf_ne
    (CFSG.LargeExtraspecial.S5.isComponentOf_map_conj hK (hDY d.2)) hK hneq
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm

theorem diagHom_eq_one_mem_centralizer (hK : IsComponentOf K Y) (hDY : D ≤ Y)
    (hDreg : D ⊓ Subgroup.normalizer (K : Set (MulAut W)) = ⊥) {x : ↥K}
    (hx : diagHom77 hK hDY hDreg x = 1) :
    (x : MulAut W) ∈ Subgroup.centralizer (K : Set (MulAut W)) := by
  classical
  rw [diagHom_apply77] at hx
  set P : MulAut W := (Finset.univ.erase (1 : ↥D)).noncommProd
    (fun d : ↥D => diagCoord77 K D d x)
    (by
      intro d _ e _ hde
      exact diag_comm77 hK hDY hDreg hde x x) with hP
  have hsplit := Finset.mul_noncommProd_erase (s := (Finset.univ : Finset ↥D))
    (a := (1 : ↥D)) (Finset.mem_univ _) (fun d : ↥D => diagCoord77 K D d x)
    (by
      intro d _ e _ hde
      exact diag_comm77 hK hDY hDreg hde x x)
  have hcoord1 : diagCoord77 K D (1 : ↥D) x = (x : MulAut W) := by
    ext w
    simp [diagCoord77]
  have hprod : (x : MulAut W) * P = 1 := by
    rw [← hcoord1, hP, hsplit]
    exact hx
  have hPmem : P ∈ (⨆ d ∈ (Finset.univ.erase (1 : ↥D)), conjSub77 K (d : MulAut W)) := by
    refine Subgroup.noncommProd_mem _ (by
      intro d _ e _ hde
      exact diag_comm77 hK hDY hDreg hde x x) (fun d _ => ?_)
    refine Subgroup.mem_iSup_of_mem d (Subgroup.mem_iSup_of_mem ‹d ∈ Finset.univ.erase 1› ?_)
    rw [← diagCoord_range]
    exact MonoidHom.mem_range.mpr ⟨x, rfl⟩
  have hPcent : P ∈ Subgroup.centralizer (K : Set (MulAut W)) :=
    iSup_erase_centralizes hK hDY hDreg hPmem
  have hxinv : (x : MulAut W) = P⁻¹ := eq_inv_of_mul_eq_one_left hprod
  rw [hxinv]
  exact (Subgroup.centralizer (K : Set (MulAut W))).inv_mem hPcent

theorem diagHom_ker_ne_top (hK : IsComponentOf K Y) (hDY : D ≤ Y)
    (hDreg : D ⊓ Subgroup.normalizer (K : Set (MulAut W)) = ⊥) :
    (diagHom77 hK hDY hDreg).ker ≠ ⊤ := by
  intro htop
  have hKq : CFSG.IsQuasisimple ↥K := (CFSG.Quasithin.A3.isQuasisimple_iff_open).2 hK.2.2
  have hKnt : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hKq
  have hKperf : Group.IsPerfect ↥K := hKq.1
  apply Group.IsPerfect.not_isMulCommutative (G := ↥K)
  refine ⟨⟨fun a b => ?_⟩⟩
  have ha : a ∈ (diagHom77 hK hDY hDreg).ker := htop ▸ Subgroup.mem_top a
  have hcent := diagHom_eq_one_mem_centralizer hK hDY hDreg (MonoidHom.mem_ker.mp ha)
  exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hcent b b.2).symm

theorem diagHom_ker_le_center77 (hK : IsComponentOf K Y) (hDY : D ≤ Y)
    (hDreg : D ⊓ Subgroup.normalizer (K : Set (MulAut W)) = ⊥) :
    (diagHom77 hK hDY hDreg).ker ≤ Subgroup.center ↥K := by
  have hnormal : (diagHom77 hK hDY hDreg).ker.Normal := MonoidHom.normal_ker _
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hK.2.2
    (diagHom77 hK hDY hDreg).ker with h | h
  · exact h
  · exact (diagHom_ker_ne_top hK hDY hDreg h).elim

theorem diagHom_range_isQuasisimple (hK : IsComponentOf K Y) (hDY : D ≤ Y)
    (hDreg : D ⊓ Subgroup.normalizer (K : Set (MulAut W)) = ⊥) :
    CFSG.IsQuasisimple ↥(diagHom77 hK hDY hDreg).range := by
  have hKq : CFSG.IsQuasisimple ↥K := (CFSG.Quasithin.A3.isQuasisimple_iff_open).2 hK.2.2
  have hker : (diagHom77 hK hDY hDreg).rangeRestrict.ker ≤ Subgroup.center ↥K := by
    rw [MonoidHom.ker_rangeRestrict]
    exact diagHom_ker_le_center77 hK hDY hDreg
  exact CFSG.LocalCores.isQuasisimple_of_surjective hKq _
    (MonoidHom.rangeRestrict_surjective _) hker

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
