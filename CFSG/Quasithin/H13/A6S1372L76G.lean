module

public import CFSG.Quasithin.H13.A6S1372L76F
public import CFSG.Quasithin.H13.A6S1372KeyData

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative

namespace A6L76G

theorem w4_facts : InW2 (dv 0 1) ∧ dv (0 : Fin 6) 1 ≠ 1 ∧ dv (0 : Fin 6) 1 ≠ e0123 ∧
    dv (0 : Fin 6) 1 * dv 1 2 = dv 0 2 ∧ InW3 (dv 0 1) ∧ InW3 (dv 1 2) ∧ InW3 (dv 0 2) ∧
    (swap (0 : Fin 6) 1 * swap 1 2 : Perm (Fin 6)) 0 = 1 ∧
    (swap (0 : Fin 6) 1 * swap 1 2 : Perm (Fin 6)) 1 = 2 ∧
    ((swap (0 : Fin 6) 1 * swap 1 2) ^ 2 : Perm (Fin 6)) 0 = 2 ∧
    ((swap (0 : Fin 6) 1 * swap 1 2) ^ 2 : Perm (Fin 6)) 1 = 0 ∧
    dv (2 : Fin 6) 0 = dv 0 2 := by
  decide +kernel

@[expose] def InV1 (x : P6) : Prop := x = 1 ∨ x = e0123

instance : DecidablePred InV1 := fun x => by unfold InV1; infer_instance

theorem w3_cosets : ∀ x : P6, InW4 x → InW3 x →
    InV1 x ∨ InV1 (x * dv 0 1) ∨ InV1 (x * dv 1 2) ∨ InV1 (x * dv 0 2) := by
  decide +kernel

theorem k4_w3 : ∀ σ ∈ K4L, ∀ x : P6, InW4 x → InW3 x → InV1 (act4f σ x * x⁻¹) := by
  decide +kernel

end A6L76G

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem mem_V1_iff_inV1 {x : G} (hx : x ∈ V) :
    x ∈ fsuV1 T V ↔ A6L76G.InV1 ((S.frame.ψ ⟨x, hx⟩ : ↥W4) : P6) := by
  rw [S.mem_V1_iff]
  constructor
  · rintro (rfl | rfl)
    · left
      have : S.frame.ψ ⟨1, hx⟩ = 1 := by
        rw [show (⟨1, hx⟩ : ↥V) = 1 from rfl, map_one]
      rw [this]
      rfl
    · right
      rw [S.psi_z]
  · rintro (h | h)
    · left
      have h1 : S.frame.ψ ⟨x, hx⟩ = 1 := Subtype.ext h
      rw [MulEquiv.map_eq_one_iff] at h1
      exact congrArg Subtype.val h1
    · right
      have h1 : S.frame.ψ ⟨x, hx⟩ = S.frame.ψ ⟨S.z, S.z_mem_V⟩ := by
        rw [S.psi_z]
        exact Subtype.ext h
      exact congrArg Subtype.val (S.frame.ψ.injective h1)

@[expose] noncomputable def v2 : G := (S.frame.ψ.symm ⟨dv 0 1, dv_mem 0 1⟩ : ↥V)

theorem v2_mem_V : S.v2 ∈ V := (S.frame.ψ.symm _).2

theorem psi_v2 : S.frame.ψ ⟨S.v2, S.v2_mem_V⟩ = ⟨dv 0 1, dv_mem 0 1⟩ :=
  S.frame.ψ.apply_symm_apply _

theorem v2_mem_V2 : S.v2 ∈ S.V2 :=
  S.mem_pre.2 ⟨S.v2_mem_V, by rw [S.psi_v2]; exact A6L76G.w4_facts.1⟩

theorem v2_mem_UH (H : Subgroup G) : S.v2 ∈ conjClosure S.V3 H :=
  le_conjClosure _ _ (S.V2_le_V3 S.v2_mem_V2)

theorem v2_not_mem_V1 : S.v2 ∉ fsuV1 T V := by
  rw [S.mem_V1_iff_inV1 S.v2_mem_V, S.psi_v2]
  rintro (h | h)
  · exact A6L76G.w4_facts.2.1 h
  · exact A6L76G.w4_facts.2.2.1 h

theorem exists_g012 : ∃ g : ↥(Subgroup.normalizer (V : Set G)), (g : G) ∈ S.L1 ∧
    S.frame.ρ g = swap 0 1 * swap 1 2 := by
  obtain ⟨h1, h2, h3, h4⟩ := A6L76F.conj_c012.2.2
  exact S.exists_L1_of_three h1 (A6L76F.conj_c012.2.2.2.2.2.2.1)
    (A6L76F.conj_c012.2.2.2.2.2.2.2) h2

theorem conj_v2_mem_V (g : ↥(Subgroup.normalizer (V : Set G))) :
    (g : G) * S.v2 * (g : G)⁻¹ ∈ V :=
  (Subgroup.mem_normalizer_iff.mp g.2 _).mp S.v2_mem_V

theorem psi_conj_v2 (g : ↥(Subgroup.normalizer (V : Set G))) :
    ((S.frame.ψ ⟨(g : G) * S.v2 * (g : G)⁻¹, S.conj_v2_mem_V g⟩ : ↥W4) : P6) =
      dv (S.frame.ρ g 0) (S.frame.ρ g 1) := by
  rw [S.psi_conj g ⟨S.v2, S.v2_mem_V⟩, S.psi_v2, act4_coe]
  exact act4f_dv _ 0 1

theorem v2_mul_conj {g : ↥(Subgroup.normalizer (V : Set G))}
    (hg : S.frame.ρ g = swap 0 1 * swap 1 2) :
    S.v2 * ((g : G) * S.v2 * (g : G)⁻¹) = ((g ^ 2 : ↥(Subgroup.normalizer (V : Set G))) : G) *
      S.v2 * ((g ^ 2 : ↥(Subgroup.normalizer (V : Set G))) : G)⁻¹ := by
  obtain ⟨-, -, -, h3, -, -, -, h01, h12, h20, h21, h02⟩ := A6L76G.w4_facts
  have hl : S.v2 * ((g : G) * S.v2 * (g : G)⁻¹) ∈ V :=
    V.mul_mem S.v2_mem_V (S.conj_v2_mem_V g)
  have e : S.frame.ψ ⟨_, hl⟩ = S.frame.ψ ⟨_, S.conj_v2_mem_V (g ^ 2)⟩ := by
    apply Subtype.ext
    have e1 : (⟨_, hl⟩ : ↥V) = ⟨S.v2, S.v2_mem_V⟩ * ⟨_, S.conj_v2_mem_V g⟩ := rfl
    rw [e1, map_mul, Subgroup.coe_mul, S.psi_v2, S.psi_conj_v2, S.psi_conj_v2, map_pow, hg,
      h01, h12, h20, h21, h02]
    exact h3
  exact congrArg Subtype.val (S.frame.ψ.injective e)

theorem mem_V3_cases {g : ↥(Subgroup.normalizer (V : Set G))}
    (hg : S.frame.ρ g = swap 0 1 * swap 1 2) {u : G} (hu : u ∈ S.V3) :
    u ∈ fsuV1 T V ∨ u * S.v2 ∈ fsuV1 T V ∨ u * ((g : G) * S.v2 * (g : G)⁻¹) ∈ fsuV1 T V ∨
      u * (((g ^ 2 : ↥(Subgroup.normalizer (V : Set G))) : G) * S.v2 *
        ((g ^ 2 : ↥(Subgroup.normalizer (V : Set G))) : G)⁻¹) ∈ fsuV1 T V := by
  obtain ⟨-, -, -, -, -, -, -, h01, h12, h20, h21, h02⟩ := A6L76G.w4_facts
  obtain ⟨huV, huW⟩ := S.mem_pre.1 hu
  have hc := A6L76G.w3_cosets _ (S.frame.ψ ⟨u, huV⟩).2 huW
  have hmem : ∀ w (hw : w ∈ V), u * w ∈ fsuV1 T V ↔
      A6L76G.InV1 (((S.frame.ψ ⟨u, huV⟩ : ↥W4) : P6) * ((S.frame.ψ ⟨w, hw⟩ : ↥W4) : P6)) := by
    intro w hw
    rw [S.mem_V1_iff_inV1 (V.mul_mem huV hw)]
    have e : (⟨u * w, V.mul_mem huV hw⟩ : ↥V) = ⟨u, huV⟩ * (⟨w, hw⟩ : ↥V) := rfl
    rw [e, map_mul, Subgroup.coe_mul]
  rcases hc with h | h | h | h
  · exact Or.inl ((S.mem_V1_iff_inV1 huV).2 h)
  · right; left
    rw [hmem _ S.v2_mem_V, S.psi_v2]
    exact h
  · right; right; left
    rw [hmem _ (S.conj_v2_mem_V g), S.psi_conj_v2, hg, h01, h12]
    exact h
  · right; right; right
    rw [hmem _ (S.conj_v2_mem_V (g ^ 2)), S.psi_conj_v2, map_pow, hg, h20, h21, h02]
    exact h

theorem comm_O2L1_V3 {o u : G} (ho : o ∈ pCoreOf 2 S.L1)
    (hu : u ∈ S.V3) : o * u * o⁻¹ * u⁻¹ ∈ fsuV1 T V := by
  have hoN : o ∈ Subgroup.normalizer (V : Set G) :=
    S.frame.L_le (S.L1_le_L (pCoreOf_le 2 S.L1 ho))
  have hK4 := S.rho_O2L1_mem_K4 ho hoN
  obtain ⟨huV, huW⟩ := S.mem_pre.1 hu
  have hm : o * u * o⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hoN u).mp huV
  have hw : o * u * o⁻¹ * u⁻¹ ∈ V := V.mul_mem hm (V.inv_mem huV)
  rw [S.mem_V1_iff_inV1 hw]
  have e : (⟨o * u * o⁻¹ * u⁻¹, hw⟩ : ↥V) = ⟨_, hm⟩ * (⟨u, huV⟩ : ↥V)⁻¹ := rfl
  rw [e, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
  have e2 : S.frame.ψ ⟨o * u * o⁻¹, hm⟩ = act4 (S.frame.ρ ⟨o, hoN⟩) (S.frame.ψ ⟨u, huV⟩) :=
    S.psi_conj ⟨o, hoN⟩ ⟨u, huV⟩
  rw [e2, act4_coe]
  exact A6L76G.k4_w3 _ hK4 _ (S.frame.ψ ⟨u, huV⟩).2 huW

structure Ctx76 (H K : Subgroup G) [IsMulCommutative ↥(conjClosure S.V3 H)] (D : FFModel) where
  hNS : ¬ LieModel G .PSp 3 2 1
  h13315 : Stmt13_3_15
  h1356two : Input1356Two
  hH : H ∈ S.Hz
  hab : IsElemAbelian 2 (conjClosure S.V3 H)
  hK : K ∈ cComp H
  hL1K : S.L1 ≤ K
  hHK : H ≤ Subgroup.normalizer (K : Set G)
  hUK : ⁅conjClosure S.V3 H, K⁆ = conjClosure S.V3 H
  π : D.Gam →* ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
    ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
  β : ↥(commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
    ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) →* ↥D.sec ⧸ D.ker.subgroupOf D.sec
  hR : CFSG.Quasithin.H.Mathieu.RealizesBy D
    (autSec (autOn K (conjClosure S.V3 H)) ⊤ ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
    (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
    (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
      commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) π β
  hπ : Function.Injective π

namespace Ctx76

variable {S} {H K : Subgroup G} [IsMulCommutative ↥(conjClosure S.V3 H)] {D : FFModel}
  (C : S.Ctx76 H K D)
include C

theorem hKH : K ≤ H := le_of_mem_cComp C.hK

theorem hTH : T ≤ H := le_sup_right.trans C.hH.1.1

theorem hL1H : S.L1 ≤ H := C.hL1K.trans C.hKH

theorem top : commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
    ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) = ⊤ :=
  Conf.commV_tilde_eq_top C.hH C.hKH C.hUK

@[expose] noncomputable def ι : ↥(conjClosure S.V3 H) →* ↥(commV (autSec
    (autOn K (conjClosure S.V3 H)) ⊤ ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) :=
  (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))).codRestrict _
    fun _ => (Subgroup.eq_top_iff' _).1 C.top _

theorem ι_coe (u : ↥(conjClosure S.V3 H)) :
    ((C.ι u : ↥(commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))) :
        Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) =
      InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) u := rfl

@[expose] noncomputable def βU : ↥(conjClosure S.V3 H) →* ↥D.sec ⧸ D.ker.subgroupOf D.sec :=
  C.β.comp C.ι

@[expose] noncomputable def κ : ↥K →* ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
    ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) :=
  ((A6Mod.secAct (le_normalizer_conjClosure S.V3 H) (S.le_normalizer_UV1 C.hH)).comp
    (Subgroup.inclusion C.hKH)).codRestrict _
    fun k => (A6Mod.mem_autSec_iff (le_normalizer_conjClosure S.V3 H)
      (S.le_normalizer_UV1 C.hH) C.hKH).2 ⟨_, k.2, rfl⟩

theorem κ_coe (k : ↥K) : ((C.κ k : ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
    ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) : MulAut _) =
      A6Mod.secAct (le_normalizer_conjClosure S.V3 H) (S.le_normalizer_UV1 C.hH)
        ⟨k, C.hKH k.2⟩ := rfl

theorem κ_surj : Function.Surjective C.κ := by
  intro x
  obtain ⟨h, hhK, hx⟩ := (A6Mod.mem_autSec_iff (le_normalizer_conjClosure S.V3 H)
    (S.le_normalizer_UV1 C.hH) C.hKH).1 x.2
  exact ⟨⟨h, hhK⟩, Subtype.ext hx⟩

@[expose] noncomputable def eπ : D.Gam ≃* ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
    ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) :=
  MulEquiv.ofBijective C.π ⟨C.hπ, C.hR.1⟩

@[expose] noncomputable def α : ↥K →* D.Gam := C.eπ.symm.toMonoidHom.comp C.κ

theorem π_α (k : ↥K) : C.π (C.α k) = C.κ k := C.eπ.apply_symm_apply (C.κ k)

theorem α_surj : Function.Surjective C.α := C.eπ.symm.surjective.comp C.κ_surj

theorem κ_ι (k : ↥K) (u : ↥(conjClosure S.V3 H))
    (hku : (k : G) * u * (k : G)⁻¹ ∈ conjClosure S.V3 H) :
    ((C.κ k : ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) : MulAut _) (C.ι u).1 =
      (C.ι ⟨_, hku⟩).1 := by
  rw [C.κ_coe, C.ι_coe, C.ι_coe, A6Mod.secAct_secMk]
  rfl

theorem βU_equiv (k : ↥K) (u : ↥(conjClosure S.V3 H))
    (hku : (k : G) * u * (k : G)⁻¹ ∈ conjClosure S.V3 H) {m : D.Amb} (hm : m ∈ D.sec)
    (h : C.βU u = QuotientGroup.mk ⟨m, hm⟩) :
    C.βU ⟨_, hku⟩ = QuotientGroup.mk ⟨D.act (C.α k) m, C.hR.2.2.2.2.2.1 _ _ hm⟩ := by
  obtain ⟨-, -, -, -, -, hsec, -, -, -, hβe⟩ := C.hR
  have hu' : ((C.π (C.α k) : ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) : MulAut _)
      (C.ι u).1 ∈ commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) :=
    (Subgroup.eq_top_iff' _).1 C.top _
  have h1 := hβe (C.α k) (C.ι u) ⟨m, hm⟩ hu' (hsec _ _ hm) h
  have h2 : (⟨((C.π (C.α k) : ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) : MulAut _) (C.ι u).1, hu'⟩ :
        ↥(commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))) = C.ι ⟨_, hku⟩ := by
    apply Subtype.ext
    show ((C.π (C.α k) : ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) : MulAut _) (C.ι u).1 = (C.ι ⟨_, hku⟩).1
    rw [C.π_α]
    exact C.κ_ι k u hku
  rw [h2] at h1
  exact h1

theorem βU_eq_one_iff (u : ↥(conjClosure S.V3 H)) :
    C.βU u = 1 ↔ ∀ k ∈ K, k * (u : G) * k⁻¹ * (u : G)⁻¹ ∈ fsuV1 T V := by
  have hHU := le_normalizer_conjClosure S.V3 H
  have hHV := S.le_normalizer_UV1 C.hH
  obtain ⟨-, -, -, -, -, -, -, -, hβk, -⟩ := C.hR
  rw [βU, MonoidHom.comp_apply, hβk]
  constructor
  · rintro ⟨hfix, -⟩ k hk
    have h1 : A6Mod.secAct hHU hHV ⟨k, C.hKH hk⟩
        (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) u) =
        InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) u :=
      hfix _ ((A6Mod.mem_autSec_iff hHU hHV C.hKH).2 ⟨⟨k, C.hKH hk⟩, hk, rfl⟩)
    have h2 : A6Mod.secAct hHU hHV ⟨k, C.hKH hk⟩
        (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) u) *
        (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) u)⁻¹ = 1 := by
      rw [h1, mul_inv_cancel]
    rw [A6Mod.secAct_secMk, ← map_inv, ← map_mul, A6Mod.secMk_eq_one_iff] at h2
    simpa [Setup.rho_apply_coe] using h2
  · intro h
    refine ⟨fun x hx => ?_, (C.ι u).2⟩
    obtain ⟨⟨k, hkH⟩, hk, rfl⟩ := (A6Mod.mem_autSec_iff hHU hHV C.hKH).1 hx
    show A6Mod.secAct hHU hHV ⟨k, hkH⟩
        (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) u) =
      InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) u
    rw [← mul_inv_eq_one, A6Mod.secAct_secMk, ← map_inv, ← map_mul, A6Mod.secMk_eq_one_iff]
    simpa [Setup.rho_apply_coe] using h k hk

theorem α_eq_one_iff (k : ↥K) :
    C.α k = 1 ↔ (k : G) ∈ pCoreOf 2 H := by
  rw [show C.α k = C.eπ.symm (C.κ k) from rfl, MulEquiv.map_eq_one_iff,
    S.mem_QH_iff_tilde C.hNS C.h13315 C.h1356two C.hH (C.hKH k.2),
    ← A6Mod.secAct_eq_one_iff (le_normalizer_conjClosure S.V3 H) (S.le_normalizer_UV1 C.hH)
      ⟨(k : G), C.hKH k.2⟩, ← C.κ_coe]
  exact Subtype.ext_iff

theorem not_three_dvd_ker : ¬ 3 ∣ Nat.card C.α.ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have e : C.α.ker = (pCoreOf 2 H).subgroupOf K := by
    ext k
    rw [MonoidHom.mem_ker, C.α_eq_one_iff, Subgroup.mem_subgroupOf]
  rw [e]
  have h1 : Nat.card ((pCoreOf 2 H).subgroupOf K) = Nat.card (pCoreOf 2 H ⊓ K : Subgroup G) := by
    rw [← Subgroup.subgroupOf_map_subtype, Subgroup.card_map_of_injective K.subtype_injective]
  rw [h1]
  obtain ⟨j, hj⟩ := ((pCoreOf_isPGroup 2 H).to_le inf_le_left).exists_card_eq
  rw [hj]
  intro h
  have := Nat.prime_three.dvd_of_dvd_pow h
  omega

theorem not_e9 (h13314 : Stmt13_3_14) {m : D.Amb}
    (hm : m ∈ D.sec) (hxm : C.βU ⟨S.v2, S.v2_mem_UH H⟩ = QuotientGroup.mk ⟨m, hm⟩)
    {a b : D.Gam}
    (hE : A6L76B.E9Pair a b) (ha : D.act a m * m⁻¹ ∈ D.ker) (hb : D.act b m * m⁻¹ ∈ D.ker) :
    False :=
  not_e9_model_fix_V2 C.hNS C.h13315 C.h1356two C.hH h13314 C.hab C.hKH C.hR C.hπ
    S.v2_mem_V2 S.v2_not_mem_V1 (C.ι ⟨S.v2, S.v2_mem_UH H⟩).2 hm hxm hE ha hb

end Ctx76

end Setting4

end CFSG.Quasithin.H13.A6
