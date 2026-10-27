module

public import CFSG.Quasithin.H13.L32A72g

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

namespace Ctx72

variable {T L V : Subgroup G} {l₀ : G} (C : Ctx72 G T L V l₀)
include C

theorem sL_le_T : sL T L V ≤ T :=
  (sL_le_pCoreOf C.setting C.hF C.hMod).trans (pCoreOf_sup_le C.hyp)

theorem comm_mem_L {t l : G} (ht : t ∈ T) (hl : l ∈ L) : l * t * l⁻¹ * t⁻¹ ∈ L := by
  have htL := C.hyp.normalizes C.h13322 ht
  rw [show l * t * l⁻¹ * t⁻¹ = l * (t * l⁻¹ * t⁻¹) by group]
  exact mul_mem hl ((Subgroup.mem_normalizer_iff.mp htL _).mp (inv_mem hl))

theorem v_le_L : V ≤ L := by
  obtain ⟨-, -, hLTV, -, -⟩ := C.hMod G T L V C.hyp.hyp C.hyp.fsu
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans hLTV
  have hVT : V ≤ T := v_le_fsuU.trans ((le_conjClosure _ _).trans C.sL_le_T)
  obtain ⟨x, hxL1, -, -, hxV⟩ := C.exists_x3
  have hxL : x ∈ L := (L32NSet14.Setting.L1_le.trans inf_le_left) hxL1
  obtain ⟨v, hv, hxv⟩ : ∃ v ∈ V, x * v * x⁻¹ * v⁻¹ ≠ 1 := by
    by_contra hc
    push Not at hc
    apply hxV
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have h1 := hc v hv
    calc v * x = (x * v * x⁻¹ * v⁻¹)⁻¹ * (x * v) := by group
      _ = x * v := by rw [h1, inv_one, one_mul]
  have heq := eq_of_le_of_ne_bot (C.hyp.hyp1281One C.h13322 C.hMod) (W := V ⊓ L) inf_le_left
    (fun l hl w hw => Subgroup.mem_inf.mpr
      ⟨(Subgroup.mem_normalizer_iff.mp (hLV hl) w).mp (Subgroup.mem_inf.mp hw).1,
        mul_mem (mul_mem hl (Subgroup.mem_inf.mp hw).2) (inv_mem hl)⟩)
    (fun hbot => hxv (by
      have h1 : x * v * x⁻¹ * v⁻¹ ∈ V ⊓ L := Subgroup.mem_inf.mpr
        ⟨mul_mem ((Subgroup.mem_normalizer_iff.mp (hLV hxL) v).mp hv) (inv_mem hv),
          C.comm_mem_L (hVT hv) hxL⟩
      rw [hbot] at h1
      exact h1))
  exact fun v hv => (Subgroup.mem_inf.mp (heq.symm ▸ hv : v ∈ V ⊓ L)).2

theorem fsuU_le_L (hu0 : u0 T V = fsuV1 T V) : fsuU T V ≤ L := by
  obtain ⟨x, hxL1, hx3, hx1, -⟩ := C.exists_x3
  have hxL : x ∈ L := (L32NSet14.Setting.L1_le.trans inf_le_left) hxL1
  obtain ⟨m, hmU, hmV⟩ := C.exists_mem_fsuU hu0
  have hmT : m ∈ T := (le_conjClosure _ _).trans C.sL_le_T hmU
  have hxm : x * m * x⁻¹ * m⁻¹ ∈ fsuU T V :=
    mul_mem ((Subgroup.mem_normalizer_iff.mp (C.l1_le_normalizer hxL1) m).mp hmU) (inv_mem hmU)
  have hxmV := C.comm_not_mem hu0 hxL1 hx3 hx1 hmU hmV
  have hxmL : x * m * x⁻¹ * m⁻¹ ∈ L := C.comm_mem_L hmT hxL
  exact C.fsuU_le_of_mem hu0 C.v_le_L hxm hxmV hxmL hxL1 hx3 hx1
    (mul_mem (mul_mem hxL hxmL) (inv_mem hxL))

theorem sL_le_L (hu0 : u0 T V = fsuV1 T V) : sL T L V ≤ L :=
  conjClosure_le fun _ hl _ hu => mul_mem (mul_mem hl (C.fsuU_le_L hu0 hu)) (inv_mem hl)

theorem sL_le_pCoreOf_L (hu0 : u0 T V = fsuV1 T V) : sL T L V ≤ pCoreOf 2 L := by
  obtain ⟨V₂, hV2⟩ := C.hyp.exists_V2 C.h13322 C.hMod C.h1222
  have : IsMulCommutative ↥V := (C.hMod G T L V C.hyp.hyp C.hyp.fsu).1.1
  have S14 := C.hyp.set14 C.h1222 C.h1332 C.h1334 hV2
  rw [← S14.cent_eq]
  intro s hs
  refine Subgroup.mem_inf.mpr ⟨C.sL_le_L hu0 hs, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (C.v_le_centerOf hv)).2 s hs).symm

end Ctx72

end CFSG.Quasithin.H13.L32A
