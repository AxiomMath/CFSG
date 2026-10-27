module

public import CFSG.Quasithin.H13.L32A774b
public import CFSG.Quasithin.H13.L32A774c

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Ctx73

variable {T L V : Subgroup G} {l₀ : G} (C : Ctx73 G T L V l₀)
include C

theorem comm_eq_one_of_mem_Y {p y : G} (hp : p ∈ pCoreOf 2 L) (hy : y ∈ pCoreOf 2 L)
    (hyL : ∀ l ∈ L, l * y * l⁻¹ * y⁻¹ ∈ V) : p * y = y * p := by
  have hδ : p * y * p⁻¹ * y⁻¹ ∈ V := C.comm_mem_v_of_mem_pCoreOf hp hy
  have hfix : ∀ l ∈ L, l * (p * y * p⁻¹ * y⁻¹) = (p * y * p⁻¹ * y⁻¹) * l := by
    intro l hl
    set s := l * p * l⁻¹ * p⁻¹ with hs
    have hsS : s ∈ sL T L V := C.comm_mem_sL_of_mem_pCoreOf hp hl
    have hsP : s ∈ pCoreOf 2 L := C.sL_le_P hsS
    set v := l * y * l⁻¹ * y⁻¹ with hv
    have hvV : v ∈ V := hyL l hl
    have hys : y * s = s * y := C.comm_sL_eq_one hy hyL hsS
    have hvc : ∀ g ∈ pCoreOf 2 L, v * g = g * v := fun g hg => (C.comm_v_pCoreOf hg hvV).symm
    have hδs : (p * y * p⁻¹ * y⁻¹) * s = s * (p * y * p⁻¹ * y⁻¹) :=
      (C.comm_v_pCoreOf hsP hδ).symm
    have e : l * (p * y * p⁻¹ * y⁻¹) * l⁻¹ = p * y * p⁻¹ * y⁻¹ := by
      calc l * (p * y * p⁻¹ * y⁻¹) * l⁻¹ =
          (l * p * l⁻¹) * (l * y * l⁻¹) * (l * p * l⁻¹)⁻¹ * (l * y * l⁻¹)⁻¹ := by group
        _ = (s * p) * (v * y) * (s * p)⁻¹ * (v * y)⁻¹ := by rw [hs, hv]; group
        _ = s * (p * v) * y * p⁻¹ * s⁻¹ * y⁻¹ * v⁻¹ := by group
        _ = s * (v * p) * y * p⁻¹ * s⁻¹ * y⁻¹ * v⁻¹ := by rw [hvc p hp]
        _ = (s * v) * ((p * y * p⁻¹ * y⁻¹) * y) * s⁻¹ * y⁻¹ * v⁻¹ := by group
        _ = (v * s) * ((p * y * p⁻¹ * y⁻¹) * y) * s⁻¹ * y⁻¹ * v⁻¹ := by rw [hvc s hsP]
        _ = v * (s * (p * y * p⁻¹ * y⁻¹)) * y * s⁻¹ * y⁻¹ * v⁻¹ := by group
        _ = v * ((p * y * p⁻¹ * y⁻¹) * s) * y * s⁻¹ * y⁻¹ * v⁻¹ := by rw [hδs]
        _ = v * (p * y * p⁻¹ * y⁻¹) * (s * y) * s⁻¹ * y⁻¹ * v⁻¹ := by group
        _ = v * (p * y * p⁻¹ * y⁻¹) * (y * s) * s⁻¹ * y⁻¹ * v⁻¹ := by rw [hys]
        _ = v * (p * y * p⁻¹ * y⁻¹) * v⁻¹ := by group
        _ = p * y * p⁻¹ * y⁻¹ := by
            rw [hvc _ (C.sL_le_P (v_le_sL hδ)), mul_inv_cancel_right]
    calc l * (p * y * p⁻¹ * y⁻¹) = (l * (p * y * p⁻¹ * y⁻¹) * l⁻¹) * l := by group
      _ = (p * y * p⁻¹ * y⁻¹) * l := by rw [e]
  have h1 : p * y * p⁻¹ * y⁻¹ ∈ V ⊓ Subgroup.centralizer (L : Set G) :=
    Subgroup.mem_inf.mpr ⟨hδ, Subgroup.mem_centralizer_iff.mpr hfix⟩
  rw [C.hyp.inf_centralizer_eq_bot C.h13322 C.hMod, Subgroup.mem_bot] at h1
  calc p * y = (p * y * p⁻¹ * y⁻¹) * y * p := by group
    _ = y * p := by rw [h1, one_mul]

theorem Q_le_centralizer : pCoreOf 2 (L ⊔ T) ≤ Subgroup.centralizer (V : Set G) := by
  rw [← C.hF.cT]
  exact inf_le_right

theorem exists_mul_of_mem_T {t : G} (ht : t ∈ T) :
    ∃ l ∈ L, ∃ q ∈ pCoreOf 2 (L ⊔ T), t = l * q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hLTV, -, -⟩ := C.hMod G T L V C.hyp.hyp C.hyp.fsu
  have h1281 := C.hyp.hyp1281One C.h13322 C.hMod
  obtain ⟨V₂, hV2⟩ := C.hyp.exists_V2 C.h13322 C.hMod C.h1222
  have : IsMulCommutative ↥V := (C.hMod G T L V C.hyp.hyp C.hyp.fsu).1.1
  have S14 := C.hyp.set14 C.h1222 C.h1332 C.h1334 hV2
  have htV : t ∈ Subgroup.normalizer (V : Set G) := hLTV (Subgroup.mem_sup_right ht)
  let φ : MulAut ↥V :=
    { toFun := fun v => ⟨t * v * t⁻¹, (Subgroup.mem_normalizer_iff.mp htV v).mp v.2⟩
      invFun := fun v => ⟨t⁻¹ * v * t, by
        have := (Subgroup.mem_normalizer_iff.mp (inv_mem htV) v).mp v.2
        simpa using this⟩
      left_inv := fun v => Subtype.ext (by simp [mul_assoc])
      right_inv := fun v => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun v w => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  obtain ⟨l, hl, hlφ⟩ := exists_conj_of_autOn_eq_top (autOn_eq_top_of_hyp1281One h1281) φ
  refine ⟨l, hl, l⁻¹ * t, ?_, by group⟩
  have hc : l⁻¹ * t ∈ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨mul_mem (Subgroup.mem_sup_left (inv_mem hl))
      (Subgroup.mem_sup_right ht), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have h1 := hlφ ⟨v, hv⟩
    have h2 : l * v * l⁻¹ = t * v * t⁻¹ := h1
    calc v * (l⁻¹ * t) = l⁻¹ * (l * v * l⁻¹) * t := by group
      _ = l⁻¹ * (t * v * t⁻¹) * t := by rw [h2]
      _ = l⁻¹ * t * v := by group
  have hXn : L ⊔ T ≤ Subgroup.normalizer
      (((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) :=
    le_normalizer_of_conj_mem' fun g hg x hx => Subgroup.mem_inf.mpr
      ⟨mul_mem (mul_mem hg (Subgroup.mem_inf.mp hx).1) (inv_mem hg),
        conj_mem_centralizer_of_mem_normalizer (hLTV hg) (Subgroup.mem_inf.mp hx).2⟩
  exact le_pCoreOf_of_le_normalizer 2 inf_le_left hXn S14.isPGroup_cent_sup hc

theorem comm_Q_eq_one_of_mem_Y {c : G} (hc : c ∈ pCoreOf 2 L)
    (hcL : ∀ l ∈ L, l * c * l⁻¹ * c⁻¹ ∈ V) {q : G} (hq : q ∈ pCoreOf 2 (L ⊔ T)) :
    q * c = c * q := by
  have hPL : pCoreOf 2 L ≤ L := pCoreOf_le 2 L
  have hQV := C.Q_le_centralizer
  have hQL : ∀ l ∈ L, l * q * l⁻¹ * q⁻¹ ∈ sL T L V := by
    intro l hl
    have h := (C.l71 G T L V C.hyp).2.2 (Subgroup.commutator_mem_commutator hq hl)
    have := inv_mem h
    rwa [commutatorElement_def, show (q * l * q⁻¹ * l⁻¹)⁻¹ = l * q * l⁻¹ * q⁻¹ by group] at this
  have hcS : ∀ s ∈ sL T L V, c * s = s * c := fun s hs => C.comm_sL_eq_one hc hcL hs
  have hqcS : q * c * q⁻¹ * c⁻¹ ∈ sL T L V := by
    have h := hQL c (hPL hc)
    have := inv_mem h
    rwa [show (c * q * c⁻¹ * q⁻¹)⁻¹ = q * c * q⁻¹ * c⁻¹ by group] at this
  have key : ∀ l ∈ L, l * (q * c * q⁻¹ * c⁻¹) * l⁻¹ =
      (l * q * l⁻¹ * q⁻¹) * (q * c * q⁻¹ * c⁻¹) * (l * q * l⁻¹ * q⁻¹)⁻¹ := by
    intro l hl
    set s := l * q * l⁻¹ * q⁻¹ with hs
    have hsS : s ∈ sL T L V := hQL l hl
    set w := l * c * l⁻¹ * c⁻¹ with hw
    have hwV : w ∈ V := hcL l hl
    have hwq : w * q = q * w := Subgroup.mem_centralizer_iff.mp (hQV hq) w hwV
    have hws : w * s = s * w :=
      (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (C.v_le_centerOf hwV)).2 s hsS).symm
    have hwc : c * w = w * c := C.comm_v_pCoreOf hc hwV
    have hcs : c * s = s * c := hcS s hsS
    have h1 : l * q * l⁻¹ = s * q := by rw [hs]; group
    have h2 : l * c * l⁻¹ = w * c := by rw [hw]; group
    calc l * (q * c * q⁻¹ * c⁻¹) * l⁻¹ =
        (l * q * l⁻¹) * (l * c * l⁻¹) * (l * q * l⁻¹)⁻¹ * (l * c * l⁻¹)⁻¹ := by group
      _ = (s * q) * (w * c) * (s * q)⁻¹ * (w * c)⁻¹ := by rw [h1, h2]
      _ = s * (q * w) * c * q⁻¹ * s⁻¹ * c⁻¹ * w⁻¹ := by group
      _ = s * (w * q) * c * q⁻¹ * s⁻¹ * c⁻¹ * w⁻¹ := by rw [hwq]
      _ = (s * w) * q * c * q⁻¹ * s⁻¹ * c⁻¹ * w⁻¹ := by group
      _ = (w * s) * q * c * q⁻¹ * s⁻¹ * c⁻¹ * w⁻¹ := by rw [hws]
      _ = w * (s * (q * c * q⁻¹ * c⁻¹) * (c * s⁻¹ * c⁻¹)) * w⁻¹ := by group
      _ = w * (s * (q * c * q⁻¹ * c⁻¹) * s⁻¹) * w⁻¹ := by
          rw [show c * s⁻¹ * c⁻¹ = s⁻¹ by
            calc c * s⁻¹ * c⁻¹ = (c * s * c⁻¹)⁻¹ := by group
              _ = s⁻¹ := by rw [hcs, mul_inv_cancel_right]]
      _ = s * (q * c * q⁻¹ * c⁻¹) * s⁻¹ := by
          have hδ := C.comm_mem C.u0_eq hsS hqcS
          have hc' : w * (s * (q * c * q⁻¹ * c⁻¹) * s⁻¹) =
              (s * (q * c * q⁻¹ * c⁻¹) * s⁻¹) * w :=
            (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (C.v_le_centerOf hwV)).2 _
              (mul_mem (mul_mem hsS hqcS) (inv_mem hsS))).symm
          rw [hc', mul_inv_cancel_right]
  have hqcV : q * c * q⁻¹ * c⁻¹ ∈ V := by
    refine C.mem_v_of_comm_mem hqcS fun l hl => ?_
    rw [key l hl]
    exact C.comm_mem C.u0_eq (hQL l hl) hqcS
  have hfix : ∀ l ∈ L, l * (q * c * q⁻¹ * c⁻¹) = (q * c * q⁻¹ * c⁻¹) * l := by
    intro l hl
    have h1 := key l hl
    have hc' : (l * q * l⁻¹ * q⁻¹) * (q * c * q⁻¹ * c⁻¹) =
        (q * c * q⁻¹ * c⁻¹) * (l * q * l⁻¹ * q⁻¹) :=
      (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (C.v_le_centerOf hqcV)).2 _
        (hQL l hl))
    rw [hc', mul_inv_cancel_right] at h1
    calc l * (q * c * q⁻¹ * c⁻¹) = (l * (q * c * q⁻¹ * c⁻¹) * l⁻¹) * l := by group
      _ = (q * c * q⁻¹ * c⁻¹) * l := by rw [h1]
  have h1 : q * c * q⁻¹ * c⁻¹ ∈ V ⊓ Subgroup.centralizer (L : Set G) :=
    Subgroup.mem_inf.mpr ⟨hqcV, Subgroup.mem_centralizer_iff.mpr hfix⟩
  rw [C.hyp.inf_centralizer_eq_bot C.h13322 C.hMod, Subgroup.mem_bot] at h1
  calc q * c = (q * c * q⁻¹ * c⁻¹) * c * q := by group
    _ = c * q := by rw [h1, one_mul]

theorem comm_T_mem_v_of_mem_Y {c : G} (hc : c ∈ pCoreOf 2 L)
    (hcL : ∀ l ∈ L, l * c * l⁻¹ * c⁻¹ ∈ V) {t : G} (ht : t ∈ T) :
    t * c * t⁻¹ * c⁻¹ ∈ V := by
  obtain ⟨l, hl, q, hq, rfl⟩ := C.exists_mul_of_mem_T ht
  have hqc := C.comm_Q_eq_one_of_mem_Y hc hcL hq
  have e : l * q * c * (l * q)⁻¹ * c⁻¹ = l * c * l⁻¹ * c⁻¹ := by
    calc l * q * c * (l * q)⁻¹ * c⁻¹ = l * (q * c) * q⁻¹ * l⁻¹ * c⁻¹ := by group
      _ = l * (c * q) * q⁻¹ * l⁻¹ * c⁻¹ := by rw [hqc]
      _ = l * c * l⁻¹ * c⁻¹ := by group
  rw [e]
  exact hcL l hl

end Ctx73

end CFSG.Quasithin.H13.L32A
