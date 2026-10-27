module

public import CFSG.Quasithin.Vol2.Ch3T325I
public import CFSG.Quasithin.Background.InternalSecB51
public import CFSG.Quasithin.Vol2.Ch3T325B
public import CFSG.Quasithin.Vol2.Ch3T325E
public import CFSG.Quasithin.Vol2.Ch3T325H
public import CFSG.Quasithin.Vol2.Ch5Sec1L34SzComp

public section

namespace CFSG.Quasithin.H13.T325

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped IsMulCommutative Pointwise

namespace Ctx

variable {G : Type} [Group G] [Finite G] {T L V₀ : Subgroup G} (c : Ctx T L V₀)
include c

theorem d3Std (h316 : Theorem316Statement) [IsMulCommutative ↥(conjClosure V₀ T)]
    [IsMulCommutative ↥(conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G)))] :
    D3Std (autOn (Subgroup.normalizer (L : Set G))
        (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G))))
      (autOn L (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G))))
      (autOn T (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G))))
      (autOn L (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G))))
      (V₀.subgroupOf (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G)))) := by
  set M := Subgroup.normalizer (L : Set G) with hMdef
  set V := conjClosure V₀ T with hVdef
  set VM := conjClosure V M with hVMdef
  set K := autOn L VM with hKdef
  set X := autOn M VM with hXdef
  set S := autOn T VM with hSdef
  set I := V₀.subgroupOf VM with hIdef
  have hMW : M ≤ Subgroup.normalizer (VM : Set G) := M_le_NVM T L V₀
  have hLW : L ≤ Subgroup.normalizer (VM : Set G) := Subgroup.le_normalizer.trans hMW
  have hTW : T ≤ Subgroup.normalizer (VM : Set G) := c.T_le_M.trans hMW
  have hexpW : ∀ w : ↥VM, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using c.elemVM.2 w w.2)
  have hKq : CFSG.IsQuasisimple ↥K := c.quasi_LVM
  have hKX : K ≤ X := InternalSec.autOn_le_autOn_of_le Subgroup.le_normalizer
  have hSX : S ≤ X := InternalSec.autOn_le_autOn_of_le c.T_le_M
  have hXK : X ≤ Subgroup.normalizer (K : Set (MulAut ↥VM)) := autOn_le_normalizer hLW hMW le_rfl
  have hSK : S ≤ Subgroup.normalizer (K : Set (MulAut ↥VM)) := hSX.trans hXK
  have hqsqtk : IsQuotientOfSQTKTC ↥X :=
    ⟨↥M, inferInstance, inferInstance, fun p hp hp2 => c.sqtkM.1 p hp hp2, c.sqtkM.2,
      InternalSec.autOnHom hMW, InternalSec.autOnHom_surjective hMW⟩
  have hsyl : IsSylowTwoOf S X := by
    have := isSylowTwoOf_map_subgroupOf ((conjAct VM).comp (Subgroup.inclusion hMW)) c.sylowM
    rwa [map_subgroupOf_conjAct c.T_le_M hMW, map_subgroupOf_conjAct le_rfl hMW] at this
  have hcomp : K ∈ cComp X := mem_cComp_of_quasisimple hKq
    (A3.subnormal_of_normal hKX ((Subgroup.normal_subgroupOf_iff_le_normalizer hKX).mpr hXK))
  have hMpeq : K = conjClosure K S :=
    (le_antisymm (conjClosure_le fun t ht x hx =>
      (Subgroup.mem_normalizer_iff.mp (hSK ht) x).mp hx) (le_conjClosure _ _)).symm
  have hirrT : I ∈ IrrPlusOn K (orbSup S I) S := c.irrT
  have hgen : (⨆ m ∈ X, I.map m.toMonoidHom) = ⊤ := by
    change orbSup X I = ⊤
    rw [orbSup_eq_biSup_smul, biSup_smul_eq_of_actCompat (actCompat_autOn_onA M)]
    apply Subgroup.map_injective VM.subtype_injective
    rw [map_biSup_smul hMW, Subgroup.map_subgroupOf_eq_of_le ((V₀_le_V T V₀).trans
      (V_le_VM T L V₀)), map_subtype_top, hVMdef, c.VM_eq]
  have hKS : K ≤ K ⊔ S := le_sup_left
  have hcompKS : K ∈ cComp (K ⊔ S) := mem_cComp_of_quasisimple hKq
    (A3.subnormal_of_normal hKS ((Subgroup.normal_subgroupOf_iff_le_normalizer hKS).mpr
      (sup_le Subgroup.le_normalizer hSK)))
  have hSylF : IsSylowTwoOf S (K ⊔ S) := F7.isSylowTwoOf_mono_right hsyl le_sup_right
    (sup_le hKX hSX)
  have hWT : ∀ t ∈ S, ∀ w ∈ orbSup S I, t • w ∈ orbSup S I := fun t ht w hw =>
    mem_orbSup_of_mem_map ht hw
  have ho2 : ∀ g ∈ pCoreOf 2 (K ⊔ S), ∀ v ∈ I, g v ∈ I := by
    intro g hg v hv
    have hgS : g ∈ S := F7.isSylowTwoOf_pCoreOf_le hSylF hg
    have hiso := iso_tilde_smul_of_commute hSK hWT hgS
      (fun m hm => commute_of_mem_pCoreOf_of_mem_cComp hcompKS hKq hg hm) I
    have hstab :=
      (forall_smul_eq_iff_mem_irrPlusOn hSK hWT hirrT.1).mpr hirrT g ⟨hgS, hiso⟩
    have h2 : g • v ∈ g • I := Subgroup.smul_mem_pointwise_smul v g _ hv
    rw [hstab] at h2
    exact h2
  have hqhat : qhatOf (autSub (K ⊔ S) (orbSup S I)) ≤ ((2 : ℚ) : WithTop ℚ) := by
    rw [qhatOf_autSub_congr c.orbSup_eq, hKdef, hSdef, ← autOn_sup hLW hTW]
    have h1 := qhatOf_autSub_autOn_le (X := L ⊔ T) (V_le_VM T L V₀)
      (sup_le c.L_le_NV (T_le_NV T V₀)) (sup_le hLW hTW)
    have h2 : qhatInt (L ⊔ T) V c.elemV ≤ ((2 : ℚ) : WithTop ℚ) := by
      exact_mod_cast qhatInt_V_le h316 c
    exact h1.trans h2
  exact ⟨⟨hexpW, hqsqtk, hsyl, hcomp, hKq, hMpeq, hXK, ⟨le_top, hirrT.1.2⟩, ho2, hgen⟩, hqhat,
    hirrT⟩

end Ctx

end CFSG.Quasithin.H13.T325
