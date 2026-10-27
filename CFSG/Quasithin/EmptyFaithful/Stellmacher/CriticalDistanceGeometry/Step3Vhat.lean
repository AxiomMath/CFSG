module

public import CFSG.Quasithin.Background.Equivariance
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtX1512WrBase
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.Step3Base

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53 Equiv

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

section Generic

variable {n : ℕ} {M5 : Model n} {K L X : Subgroup G} [(L.subgroupOf X).Normal]
  {Ψ : ↥K →* Perm (Fin n)} {β : M5.W →* ↥X ⧸ L.subgroupOf X}

theorem secData_mem_fixW_iff (h : SecData M5 K L X Ψ β) (hLX : L ≤ X) {A : Subgroup G}
    (hAK : A ≤ K) {u : M5.W} {x : ↥X} (hux : β u = QuotientGroup.mk x) :
    u ∈ fixW M5 ((A.subgroupOf K).map Ψ) ↔ (x : G) ∈ fixSecIn A L X := by
  rw [X1512.mem_fixSecIn hLX]
  constructor
  · intro hu
    refine ⟨x.2, fun a ha => ?_⟩
    have haK : a ∈ K := hAK ha
    obtain ⟨_, h'⟩ := h.equiv ⟨a, haK⟩ u x hux
    have hfix := hu (Ψ ⟨a, haK⟩) ⟨⟨a, haK⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
    rw [hfix, hux] at h'
    exact (X1512.mk_eq_iff hLX).mp h'
  · rintro ⟨-, hx⟩ σ ⟨a', ha', rfl⟩
    obtain ⟨_, h'⟩ := h.equiv a' u x hux
    apply h.inj
    rw [h', hux]
    exact ((X1512.mk_eq_iff hLX).mpr (hx a' (Subgroup.mem_subgroupOf.mp ha'))).symm

theorem secData_isInvSub_fixW (h : SecData M5 K L X Ψ β) (hLX : L ≤ X) {A K₀ : Subgroup G}
    (hAK : A ≤ K)
    (hn : ∀ k ∈ K₀, ∀ x ∈ fixSecIn A L X, k * x * k⁻¹ ∈ fixSecIn A L X) :
    IsInvSub M5 ((K₀.subgroupOf K).map Ψ) (fixW M5 ((A.subgroupOf K).map Ψ)) := by
  rintro _ ⟨k, hk, rfl⟩ u hu
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (β u)
  have hxF := (secData_mem_fixW_iff h hLX hAK hx.symm).mp hu
  obtain ⟨_, h1⟩ := h.equiv k u x hx.symm
  exact (secData_mem_fixW_iff h hLX hAK h1).mpr (hn k (Subgroup.mem_subgroupOf.mp hk) x hxF)

end Generic

structure VhatData (γ : Geo H M) where
  M5 : Model 5
  ψ : ↥(stab γ) →* Perm (Fin 5)
  surj : Function.Surjective ψ
  ker : ∀ x : ↥(stab γ), ψ x = 1 ↔ (x : G) ∈ Qv γ
  norm : ((Zv γ).subgroupOf (Vn γ)).Normal
  β : M5.W →* ↥(Vn γ) ⧸ (Zv γ).subgroupOf (Vn γ)
  secData : SecData M5 (stab γ) (Zv γ) (Vn γ) ψ β
  faithful : M5.Faithful

namespace Step3Ctx

variable {α β α' : Geo H M} (C : Step3Ctx H M S α β α')

include C

theorem isSec_Vn (γ : Geo H M) : IsSec (stab γ) (Zv γ) (Vn γ) where
  le := Zv_le_Vn_self C.hA γ
  normN := stab_le_normalizer_Vn γ
  normL := stab_le_normalizer_Zv C.hA γ
  comm := fun x hx y hy => by
    have h := isMulCommutative_subgroup_iff.mp (C.isElemAbelian_Vn' γ).1 x hx y hy
    rw [h]; simp
  sq := fun x hx => by
    rw [isElemAbelian_pow_eq_one (C.isElemAbelian_Vn' γ) hx]; exact one_mem _

theorem ker_le_cSec {γ : Geo H M} {n : ℕ} (ψ : ↥(stab γ) →* Perm (Fin n))
    (hker : ∀ x : ↥(stab γ), ψ x = 1 ↔ (x : G) ∈ Qv γ) (hγ : vtype γ = false) :
    ψ.ker ≤ (cSecIn (stab γ) (Zv γ) (Vn γ)).subgroupOf (stab γ) := by
  intro x hx
  rw [Subgroup.mem_subgroupOf]
  refine Subgroup.subset_closure ⟨x.2, fun v hv => ?_⟩
  have hxQ : (x : G) ∈ Qv γ := (hker x).mp hx
  have h1 := Subgroup.commutator_mem_commutator hxQ hv
  rw [Subgroup.commutator_comm, C.comm_Vn_Qv_eq hγ] at h1
  simpa [commutatorElement_def] using h1

theorem cSec_le_Qv {γ : Geo H M} (hγ : vtype γ = false) :
    cSecIn (stab γ) (Zv γ) (Vn γ) ≤ Qv γ := by
  rw [cSecIn, Subgroup.closure_le]
  rintro f ⟨hf, hfc⟩
  exact hss114_e C.hA (C.Zv_eq_omega hγ) f hf hfc

theorem nonempty_vhatData {γ : Geo H M} (hγ : vtype γ = false) : Nonempty (VhatData γ) := by
  obtain ⟨n, ψ, hn, hψ, hker⟩ := exists_quotHom C.hA γ
  rcases hn with ⟨rfl, -⟩ | ⟨-, hv⟩
  swap
  · rw [hγ] at hv; exact absurd hv (by decide)
  have hs := C.isSec_Vn γ
  have hN := hs.normal_subgroupOf
  have hk := C.ker_le_cSec ψ hker hγ
  refine ⟨⟨secModule hs ψ hψ hk, ψ, hψ, hker, hN, MonoidHom.id _, ?_, ?_⟩⟩
  · refine ⟨fun x => ⟨x, rfl⟩, fun x y h => h, ?_⟩
    intro k u x hux
    have hu : u = hs.proj x := hux
    subst hu
    refine ⟨hs.conj_mem_N k x, ?_⟩
    exact secModule_act_proj hs ψ hψ hk k x
  · rw [secModule_faithful_iff]
    intro f hf
    rw [MonoidHom.mem_ker, hker]
    exact C.cSec_le_Qv hγ (Subgroup.mem_subgroupOf.mp hf)

end Step3Ctx

end F53.Stellmacher

end CFSG.Quasithin
