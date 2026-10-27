module

public import CFSG.Quasithin.MS93.S37Lift

public section

namespace CFSG.Quasithin.MS93.S37

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.MSP
open CFSG.QuasithinUnique
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G]

structure Cfg (M T L : Subgroup G) (F : Type) [Field F] [Fintype F] where
  h : PUHyp M T L
  hVU : Vq M L = Uq M T L
  k : ℕ
  hk : 2 ≤ k
  hF : Fintype.card F = 2 ^ k
  α : ↥L →* ↥(StatedSp 2 F)
  hα : Function.Surjective α
  hnat : IsSumOfNaturalModulesVia L (Uq M T L) (Uq M T L ⊓ Subgroup.centralizer (L : Set G)) α
    false 1

namespace Cfg

variable {M T L : Subgroup G} {F : Type} [Field F] [Fintype F] (C : Cfg M T L F)
include C

noncomputable abbrev N : Sp4NatData L (Uq M T L) (Uq M T L ⊓ Subgroup.centralizer (L : Set G)) F :=
  Sp4NatData.ofIsSum C.hα C.hnat

theorem N_α : C.N.α = C.α := Sp4NatData.ofIsSum_α _ _

theorem hMU : M ≤ Subgroup.normalizer (Uq M T L : Set G) := le_normalizer_Uq C.h.le_normalizer

theorem hMA : M ≤ Subgroup.normalizer
    ((Uq M T L ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) :=
  le_normalizer_inf C.hMU (le_normalizer_centralizer C.h.le_normalizer)

noncomputable abbrev act {x : G} (hx : x ∈ M) : V4 F →+ V4 F := C.N.act C.hMU C.hMA hx

theorem act_of_mem_pCore {x : G} (hx : x ∈ pCoreOf 2 M) (v : V4 F) :
    C.act (pCoreOf_le' M hx) v = v := by
  obtain ⟨u, rfl⟩ := C.N.co_surj v
  refine C.N.act_co C.hMU C.hMA _ ?_
  have hc := Subgroup.mem_centralizer_iff.1 (Subgroup.centralizer_le (Uq_le_Z0q C.h.L_le)
    (C.h.pCoreOf_le_centralizer_Z0q hx)) (u : G) u.2
  rw [← hc, mul_inv_cancel_right]

theorem le_sup_normalizer : L ≤ Subgroup.normalizer (pCoreOf 2 M : Set G) :=
  C.h.L_le.trans (le_normalizer_pCoreOf M)

theorem exists_mul_of_mem_sup {x : G} (hx : x ∈ L ⊔ pCoreOf 2 M) :
    ∃ l ∈ L, ∃ q ∈ pCoreOf 2 M, l * q = x := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right L _ C.le_sup_normalizer]
    at hx
  obtain ⟨l, hl, q, hq, rfl⟩ := hx
  exact ⟨l, hl, q, hq, rfl⟩

theorem sup_le_M : L ⊔ pCoreOf 2 M ≤ M := sup_le C.h.L_le (pCoreOf_le' M)

theorem exists_act_eq_mat {x : G} (hx : x ∈ L ⊔ pCoreOf 2 M) :
    ∃ g : Sp4 F, ∀ v : V4 F, C.act (C.sup_le_M hx) v = mat g *ᵥ v := by
  obtain ⟨l, hl, q, hq, rfl⟩ := C.exists_mul_of_mem_sup hx
  refine ⟨C.α ⟨l, hl⟩, fun v => ?_⟩
  have h1 := congrArg (fun f => f v) (C.N.act_mul C.hMU C.hMA (C.h.L_le hl) (pCoreOf_le' M hq))
  simp only [AddMonoidHom.comp_apply] at h1
  rw [show C.act (C.sup_le_M hx) = C.N.act C.hMU C.hMA (M.mul_mem (C.h.L_le hl)
      (pCoreOf_le' M hq)) from C.N.act_congr C.hMU C.hMA rfl _ _]
  rw [h1, C.act_of_mem_pCore hq, C.N.act_of_mem C.hMU C.hMA (C.h.L_le hl) hl, C.N_α]

noncomputable def rhoFun (x : ↥(L ⊔ pCoreOf 2 M)) : Sp4 F :=
  Classical.choose (C.exists_act_eq_mat x.2)

theorem rhoFun_spec (x : ↥(L ⊔ pCoreOf 2 M)) (v : V4 F) :
    C.act (C.sup_le_M x.2) v = mat (C.rhoFun x) *ᵥ v :=
  Classical.choose_spec (C.exists_act_eq_mat x.2) v

noncomputable def rho : ↥(L ⊔ pCoreOf 2 M) →* Sp4 F where
  toFun := C.rhoFun
  map_one' := ext_mulVec fun v => by
    rw [← C.rhoFun_spec, mat_one, Matrix.one_mulVec]
    exact congrArg (fun f => f v) (C.N.act_one C.hMU C.hMA)
  map_mul' := fun x y => ext_mulVec fun v => by
    rw [← C.rhoFun_spec, mat_mul_mulVec, ← C.rhoFun_spec, ← C.rhoFun_spec]
    have h1 := congrArg (fun f => f v)
      (C.N.act_mul C.hMU C.hMA (C.sup_le_M x.2) (C.sup_le_M y.2))
    simp only [AddMonoidHom.comp_apply] at h1
    rw [← h1]

theorem rho_spec (x : ↥(L ⊔ pCoreOf 2 M)) (v : V4 F) :
    C.act (C.sup_le_M x.2) v = mat (C.rho x) *ᵥ v :=
  C.rhoFun_spec x v

theorem co_conj (x : ↥(L ⊔ pCoreOf 2 M)) {u v : ↥(Uq M T L)}
    (huv : (v : G) = x * u * (x : G)⁻¹) : C.N.co v = mat (C.rho x) *ᵥ C.N.co u := by
  rw [← C.rho_spec, C.N.act_co C.hMU C.hMA _ huv]

theorem rho_of_mem_L {l : G} (hl : l ∈ L) :
    C.rho ⟨l, Subgroup.mem_sup_left hl⟩ = C.α ⟨l, hl⟩ :=
  ext_mulVec fun v => by
    rw [← C.rho_spec, ← C.N_α]
    exact C.N.act_of_mem C.hMU C.hMA (C.h.L_le hl) hl v

theorem rho_of_mem_pCore {q : G} (hq : q ∈ pCoreOf 2 M) :
    C.rho ⟨q, Subgroup.mem_sup_right hq⟩ = 1 :=
  ext_mulVec fun v => by
    rw [← C.rho_spec, mat_one, Matrix.one_mulVec]
    exact C.act_of_mem_pCore hq v

theorem rho_mul {l q : G} (hl : l ∈ L) (hq : q ∈ pCoreOf 2 M) (hx : l * q ∈ L ⊔ pCoreOf 2 M) :
    C.rho ⟨l * q, hx⟩ = C.α ⟨l, hl⟩ := by
  have e : (⟨l * q, hx⟩ : ↥(L ⊔ pCoreOf 2 M)) =
      ⟨l, Subgroup.mem_sup_left hl⟩ * ⟨q, Subgroup.mem_sup_right hq⟩ := rfl
  rw [e, map_mul, C.rho_of_mem_L hl, C.rho_of_mem_pCore hq, mul_one]

theorem rho_eq_one_iff (x : ↥(L ⊔ pCoreOf 2 M)) : C.rho x = 1 ↔ (x : G) ∈ pCoreOf 2 M := by
  constructor
  · intro hx
    obtain ⟨l, hl, q, hq, e⟩ := C.exists_mul_of_mem_sup x.2
    have hxe : x = ⟨l * q, e ▸ x.2⟩ := Subtype.ext e.symm
    rw [hxe, C.rho_mul hl hq] at hx
    have hlQ := mem_pCoreOf_of_alpha_eq_one C.N C.h C.hVU hl (by rw [C.N_α]; exact hx)
    rw [← e]
    exact mul_mem hlQ hq
  · intro hx
    have e : x = ⟨(x : G), Subgroup.mem_sup_right hx⟩ := rfl
    rw [e, C.rho_of_mem_pCore hx]

theorem conj_eq_of_fix (x : ↥(L ⊔ pCoreOf 2 M)) {u : G} (hu : u ∈ Uq M T L)
    (hfix : mat (C.rho x) *ᵥ C.N.co ⟨u, hu⟩ = C.N.co ⟨u, hu⟩) : (x : G) * u * (x : G)⁻¹ = u := by
  obtain ⟨l, hl, q, hq, e⟩ := C.exists_mul_of_mem_sup x.2
  have hqu : q * u * q⁻¹ = u := by
    have hc := Subgroup.mem_centralizer_iff.1 (Subgroup.centralizer_le (Uq_le_Z0q C.h.L_le)
      (C.h.pCoreOf_le_centralizer_Z0q hq)) u hu
    rw [← hc, mul_inv_cancel_right]
  have hxu : (x : G) * u * (x : G)⁻¹ = l * u * l⁻¹ := by
    rw [← e, show l * q * u * (l * q)⁻¹ = l * (q * u * q⁻¹) * l⁻¹ by group, hqu]
  rw [hxu]
  have hlu : l * u * l⁻¹ ∈ Uq M T L := (Subgroup.mem_normalizer_iff.1 (C.hnat.1 hl) u).1 hu
  have hco : C.N.co ⟨u, hu⟩ = C.N.co ⟨l * u * l⁻¹, hlu⟩ := by
    have hxe : x = ⟨l * q, e ▸ x.2⟩ := Subtype.ext e.symm
    rw [hxe, C.rho_mul hl hq] at hfix
    have := C.N.β_equiv ⟨l, hl⟩ ⟨u, hu⟩ ⟨l * u * l⁻¹, hlu⟩ rfl
    rw [C.N_α] at this
    rw [hfix.symm]
    exact this.symm
  have hA := (C.N.co_eq_co_iff _ _).1 hco
  have hmem : l * u * l⁻¹ * u⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
    have hc : l * u * l⁻¹ * u⁻¹ = u⁻¹ * (l * u * l⁻¹) := by
      rw [Sp4L.uq_comm C.h hlu (inv_mem hu)]
    rw [hc]
    exact hA.2
  exact (lift_L C.h C.hα C.hnat C.hVU (by have := C.hk; omega) C.hF).2 l hl u hu hmem

end Cfg

end CFSG.Quasithin.MS93.S37
