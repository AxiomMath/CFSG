module

public import CFSG.Quasithin.Vol2.Ch3T326B
public import CFSG.Quasithin.Vol2.Ch3T326E
public import CFSG.Quasithin.Vol2.Ch3T326F
public import CFSG.Quasithin.Background.InternalSecB51
public import CFSG.Quasithin.Vol2.Ch3T325E
public import CFSG.Quasithin.Vol2.Ch3T325I
public import CFSG.Quasithin.Vol2.Ch5Sec1L34SzComp

public section

namespace CFSG.Quasithin.H13.T326

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped IsMulCommutative Pointwise
open T325 (V₀_le_V V_le_VM T_le_NV M_le_NVM mem_cComp_of_quasisimple map_subgroupOf_conjAct
  biSup_smul_eq_of_actCompat actCompat_autOn_onA qhatOf_autSub_autOn_le)

namespace Ctx

variable {G : Type} [Group G] [Finite G] {T L V₀ : Subgroup G} (c : Ctx T L V₀)
include c

theorem d3Std (h316 : Theorem316Statement) [IsMulCommutative ↥(conjClosure V₀ T)]
    [IsMulCommutative ↥(conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G)))] :
    D3Std (autOn (Subgroup.normalizer (conjClosure L T : Set G))
        (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))))
      (autOn (conjClosure L T)
        (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))))
      (autOn T (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))))
      (autOn L (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))))
      (V₀.subgroupOf
        (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)))) := by
  set L₀ := conjClosure L T with hL₀def
  set M := Subgroup.normalizer (L₀ : Set G) with hMdef
  set V := conjClosure V₀ T with hVdef
  set VM := conjClosure V M with hVMdef
  set K := autOn L VM with hKdef
  set K₀ := autOn L₀ VM with hK₀def
  set X := autOn M VM with hXdef
  set S := autOn T VM with hSdef
  set I := V₀.subgroupOf VM with hIdef
  have hMW : M ≤ Subgroup.normalizer (VM : Set G) := M_le_NVM T L₀ V₀
  have hL₀W : L₀ ≤ Subgroup.normalizer (VM : Set G) := Subgroup.le_normalizer.trans hMW
  have hLW : L ≤ Subgroup.normalizer (VM : Set G) := c.L_le_L₀.trans hL₀W
  have hTW : T ≤ Subgroup.normalizer (VM : Set G) := c.T_le_M.trans hMW
  have hexpW : ∀ w : ↥VM, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using c.elemVM.2 w w.2)
  have hKq : CFSG.IsQuasisimple ↥K := c.quasi_LVM
  have hKK₀ : K ≤ K₀ := InternalSec.autOn_le_autOn_of_le c.L_le_L₀
  have hK₀X : K₀ ≤ X := InternalSec.autOn_le_autOn_of_le Subgroup.le_normalizer
  have hSX : S ≤ X := InternalSec.autOn_le_autOn_of_le c.T_le_M
  have hXK₀ : X ≤ Subgroup.normalizer (K₀ : Set (MulAut ↥VM)) :=
    H13.autOn_le_normalizer hL₀W hMW le_rfl
  have hSK₀ : S ≤ Subgroup.normalizer (K₀ : Set (MulAut ↥VM)) := hSX.trans hXK₀
  have hK₀K : K₀ ≤ Subgroup.normalizer (K : Set (MulAut ↥VM)) :=
    H13.autOn_le_normalizer hLW hL₀W (Vol2.Ch10.SecA.fsuL0_le_normalizer c.fsu.maximal.1)
  have hqsqtk : IsQuotientOfSQTKTC ↥X :=
    ⟨↥M, inferInstance, inferInstance, fun p hp hp2 => c.sqtkM.1 p hp hp2, c.sqtkM.2,
      InternalSec.autOnHom hMW, InternalSec.autOnHom_surjective hMW⟩
  have hsyl : IsSylowTwoOf S X := by
    have := isSylowTwoOf_map_subgroupOf ((conjAct VM).comp (Subgroup.inclusion hMW)) c.sylowM
    rwa [map_subgroupOf_conjAct c.T_le_M hMW, map_subgroupOf_conjAct le_rfl hMW] at this
  have hKsubK₀ : IsSubnormal K K₀ :=
    A3.subnormal_of_normal hKK₀ ((Subgroup.normal_subgroupOf_iff_le_normalizer hKK₀).mpr hK₀K)
  have hcomp : K ∈ cComp X := mem_cComp_of_quasisimple hKq (A3.subnormal_trans hKsubK₀
    (A3.subnormal_of_normal hK₀X ((Subgroup.normal_subgroupOf_iff_le_normalizer hK₀X).mpr hXK₀)))
  have hK₀S : K₀ ≤ K₀ ⊔ S := le_sup_left
  have hcompKS : K ∈ cComp (K₀ ⊔ S) := mem_cComp_of_quasisimple hKq (A3.subnormal_trans hKsubK₀
    (A3.subnormal_of_normal hK₀S ((Subgroup.normal_subgroupOf_iff_le_normalizer hK₀S).mpr
      (sup_le Subgroup.le_normalizer hSK₀))))
  have hMpeq : K₀ = conjClosure K S := autOn_conjClosure hLW hTW
  have hirrT : I ∈ IrrPlusOn K₀ (orbSup S I) S := c.irrT
  have hgen : (⨆ m ∈ X, I.map m.toMonoidHom) = ⊤ := by
    change orbSup X I = ⊤
    rw [orbSup_eq_biSup_smul, biSup_smul_eq_of_actCompat (actCompat_autOn_onA M)]
    apply Subgroup.map_injective VM.subtype_injective
    rw [map_biSup_smul hMW, Subgroup.map_subgroupOf_eq_of_le ((V₀_le_V T V₀).trans
      (V_le_VM T L₀ V₀)), map_subtype_top, hVMdef, c.VM_eq]
  have hSylF : IsSylowTwoOf S (K₀ ⊔ S) := F7.isSylowTwoOf_mono_right hsyl le_sup_right
    (sup_le hK₀X hSX)
  have hWT : ∀ t ∈ S, ∀ w ∈ orbSup S I, t • w ∈ orbSup S I := fun t ht w hw =>
    mem_orbSup_of_mem_map ht hw
  have hcomm : ∀ g ∈ pCoreOf 2 (K₀ ⊔ S), ∀ m ∈ K₀, g * m = m * g := by
    intro g hg
    have key : K₀ ≤ Subgroup.centralizer ({g} : Set (MulAut ↥VM)) := by
      rw [hMpeq]
      refine conjClosure_le fun s hs k hk => ?_
      have hs' : s⁻¹ ∈ K₀ ⊔ S := Subgroup.mem_sup_right (S.inv_mem hs)
      have hg' : s⁻¹ * g * s ∈ pCoreOf 2 (K₀ ⊔ S) := by
        have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ hs') g).mp hg
        rwa [inv_inv] at this
      have hc := commute_of_mem_pCoreOf_of_mem_cComp hcompKS hKq hg' hk
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.mp hh]
      calc g * (s * k * s⁻¹) = s * (s⁻¹ * g * s * k) * s⁻¹ := by group
        _ = s * (k * (s⁻¹ * g * s)) * s⁻¹ := by rw [hc]
        _ = s * k * s⁻¹ * g := by group
    intro m hm
    exact Subgroup.mem_centralizer_iff.mp (key hm) g (Set.mem_singleton g)
  have ho2 : ∀ g ∈ pCoreOf 2 (K₀ ⊔ S), ∀ v ∈ I, g v ∈ I := by
    intro g hg v hv
    have hgS : g ∈ S := F7.isSylowTwoOf_pCoreOf_le hSylF hg
    have hiso := iso_tilde_smul_of_commute hSK₀ hWT hgS (hcomm g hg) I
    have hstab :=
      (forall_smul_eq_iff_mem_irrPlusOn hSK₀ hWT hirrT.1).mpr hirrT g ⟨hgS, hiso⟩
    have h2 : g • v ∈ g • I := Subgroup.smul_mem_pointwise_smul v g _ hv
    rw [hstab] at h2
    exact h2
  have hqhat : qhatOf (autSub (K₀ ⊔ S) (orbSup S I)) ≤ ((2 : ℚ) : WithTop ℚ) := by
    rw [qhatOf_autSub_congr c.orbSup_eq, hK₀def, hSdef, ← H13.autOn_sup hL₀W hTW]
    have h1 := qhatOf_autSub_autOn_le (X := L₀ ⊔ T) (V_le_VM T L₀ V₀)
      (sup_le c.L₀_le_NV (T_le_NV T V₀)) (sup_le hL₀W hTW)
    have h2 : qhatInt (L₀ ⊔ T) V c.elemV ≤ ((2 : ℚ) : WithTop ℚ) := by
      exact_mod_cast qhatInt_V_le h316 c
    exact h1.trans h2
  exact ⟨⟨hexpW, hqsqtk, hsyl, hcomp, hKq, hMpeq, hXK₀, ⟨le_top, hirrT.1.2⟩, ho2, hgen⟩, hqhat,
    hirrT⟩

end Ctx

end CFSG.Quasithin.H13.T326
