module

public import CFSG.Quasithin.H13.L32A773j

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

theorem sl24_fix : ∀ v : Fin 2 → RuType.F4,
    (∀ A : Matrix.SpecialLinearGroup (Fin 2) RuType.F4,
      (A : Matrix (Fin 2) (Fin 2) RuType.F4).mulVec v = v) → v = 0 := by
  decide +kernel

omit [Finite G] in
theorem IsL24Section.mem_of_comm {K X Y : Subgroup G} (h : IsL24Section K X Y) {x : G}
    (hx : x ∈ X) (hxK : ∀ k ∈ K, k * x * k⁻¹ * x⁻¹ ∈ Y) : x ∈ Y := by
  obtain ⟨hKX, π, β, hπs, -, -, hβk, hβe⟩ := h
  have hβ1 : ∀ y : ↥X, β y = 1 ↔ (y : G) ∈ Y := fun y => by
    rw [← MonoidHom.mem_ker, hβk, Subgroup.mem_subgroupOf]
  have hfix : ∀ A : Matrix.SpecialLinearGroup (Fin 2) RuType.F4,
      (A : Matrix (Fin 2) (Fin 2) RuType.F4).mulVec (Multiplicative.toAdd (β ⟨x, hx⟩)) =
        Multiplicative.toAdd (β ⟨x, hx⟩) := by
    intro A
    obtain ⟨k, rfl⟩ := hπs A
    have hkx : (k : G) * x * (k : G)⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (hKX k.2) x).mp hx
    have h1 := hβe k ⟨x, hx⟩ ⟨_, hkx⟩ rfl
    have hy : (k : G) * x * (k : G)⁻¹ * x⁻¹ ∈ Y := hxK k k.2
    have h2 : β ⟨_, hkx⟩ = β ⟨x, hx⟩ := by
      have e : (⟨_, hkx⟩ : ↥X) = ⟨_, mul_mem hkx (inv_mem hx)⟩ * ⟨x, hx⟩ :=
        Subtype.ext (by simp)
      rw [e, map_mul, (hβ1 _).mpr hy, one_mul]
    rw [h2] at h1
    have := congrArg Multiplicative.toAdd h1
    rw [toAdd_ofAdd] at this
    exact this.symm
  have h0 := sl24_fix _ hfix
  have h1 : β ⟨x, hx⟩ = 1 := by
    rw [← ofAdd_toAdd (β ⟨x, hx⟩), h0]
    rfl
  exact (hβ1 ⟨x, hx⟩).mp h1

namespace Ctx73

variable {T L V : Subgroup G} {l₀ : G} (C : Ctx73 G T L V l₀)
include C

theorem CU_le_sL : pCoreOf 2 (hz T V) ⊓ Subgroup.centralizer (fsuU T V : Set G) ≤ sL T L V := by
  have hTH : T ≤ hz T V := le_sup_right.trans C.hF.L₁T_le_H
  intro c hc
  obtain ⟨hcQ, hcU⟩ := Subgroup.mem_inf.mp hc
  rw [← C.pCoreOf_sup_eq_sL, ← C.hF.cT]
  refine Subgroup.mem_inf.mpr ⟨pCoreOf_le_of_le C.hyp hTH hcQ, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact Subgroup.mem_centralizer_iff.mp hcU v (v_le_fsuU hv)

theorem hz_le_normalizer_CU : hz T V ≤ Subgroup.normalizer
    ((pCoreOf 2 (hz T V) ⊓ Subgroup.centralizer (fsuU T V : Set G) : Subgroup G) : Set G) :=
  le_normalizer_of_conj_mem' fun _ hh c hc => Subgroup.mem_inf.mpr
    ⟨(Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ hh) c).mp
      (Subgroup.mem_inf.mp hc).1,
      conj_mem_centralizer_of_mem_normalizer (C.hz_le_normalizer_fsuU hh)
        (Subgroup.mem_inf.mp hc).2⟩

theorem fsuU_le_CU :
    fsuU T V ≤ pCoreOf 2 (hz T V) ⊓ Subgroup.centralizer (fsuU T V : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUe := isElemAbelian_fsuU_of C.hyp C.hMod
  have hUH : fsuU T V ≤ hz T V := fun u hu => by
    show u ∈ Subgroup.centralizer (fsuV1 T V : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact F7.isElemAbelian_comm hUe (v_le_fsuU (Subgroup.mem_inf.mp hw).1) hu
  have hUp : IsPGroup 2 ↥(fsuU T V) := fun x => ⟨1, Subtype.ext (by
    simpa using F7.isElemAbelian_pow_eq_one hUe x.2)⟩
  refine le_inf (le_pCoreOf_of_le_normalizer 2 hUH C.hz_le_normalizer_fsuU hUp) ?_
  intro u hu
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  exact F7.isElemAbelian_comm hUe hw hu

variable {k : G} (hk : k ∈ kz T V) (hkM : k ∉ m1 T L V)
include hk

theorem fsuU_le_conj : fsuU T V ≤ (sL T L V).map (MulAut.conj k).toMonoidHom := fun u hu => by
  have hkH : k ∈ hz T V := oTwoUpper_le _ hk
  rw [show (sL T L V).map (MulAut.conj k).toMonoidHom = conjSub k (sL T L V) from rfl,
    mem_conjSub]
  refine le_conjClosure _ _ ?_
  have := (Subgroup.mem_normalizer_iff.mp (C.hz_le_normalizer_fsuU (inv_mem hkH)) u).mp hu
  simpa using this

include hkM

theorem comm_mem_fsuU_of_mem_inf {x : G}
    (hx : x ∈ sL T L V ⊓ (sL T L V).map (MulAut.conj k).toMonoidHom) {g : G} (hg : g ∈ kz T V) :
    g * x * g⁻¹ * x⁻¹ ∈ fsuU T V := by
  have hkH : k ∈ hz T V := oTwoUpper_le _ hk
  obtain ⟨hxS, hxSk⟩ := Subgroup.mem_inf.mp hx
  have hxSk' : k⁻¹ * x * k ∈ sL T L V := by
    rw [show (sL T L V).map (MulAut.conj k).toMonoidHom = conjSub k (sL T L V) from rfl,
      mem_conjSub] at hxSk
    exact hxSk
  let Y : Subgroup G :=
    { carrier := {g | g ∈ hz T V ∧ g * x * g⁻¹ * x⁻¹ ∈ fsuU T V}
      one_mem' := ⟨one_mem _, by simp⟩
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by
        rw [show a * b * x * (a * b)⁻¹ * x⁻¹ =
          (a * (b * x * b⁻¹ * x⁻¹) * a⁻¹) * (a * x * a⁻¹ * x⁻¹) by group]
        exact mul_mem ((Subgroup.mem_normalizer_iff.mp (C.hz_le_normalizer_fsuU ha.1) _).mp hb.2)
          ha.2⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by
        rw [show a⁻¹ * x * a⁻¹⁻¹ * x⁻¹ = a⁻¹ * (a * x * a⁻¹ * x⁻¹)⁻¹ * a⁻¹⁻¹ by group]
        exact (Subgroup.mem_normalizer_iff.mp (C.hz_le_normalizer_fsuU (inv_mem ha.1)) _).mp
          (inv_mem ha.2)⟩ }
  have hSY : sL T L V ≤ Y := fun s hs => ⟨oTwoUpper_le _ (C.sL_le_kz hs),
    v_le_fsuU (C.comm_mem C.u0_eq hs hxS)⟩
  have hSkY : (sL T L V).map (MulAut.conj k).toMonoidHom ≤ Y := by
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨mul_mem (mul_mem hkH (oTwoUpper_le _ (C.sL_le_kz hs))) (inv_mem hkH), ?_⟩
    have h1 : s * (k⁻¹ * x * k) * s⁻¹ * (k⁻¹ * x * k)⁻¹ ∈ fsuU T V :=
      v_le_fsuU (C.comm_mem C.u0_eq hs hxSk')
    have h2 := (Subgroup.mem_normalizer_iff.mp (C.hz_le_normalizer_fsuU hkH) _).mp h1
    show k * s * k⁻¹ * x * (k * s * k⁻¹)⁻¹ * x⁻¹ ∈ fsuU T V
    convert h2 using 1
    group
  have hKY : kz T V ≤ Y := by
    rw [C.kz_eq_sup hk hkM]
    exact sup_le hSY hSkY
  exact (hKY hg).2

theorem sL_inf_conj_eq : sL T L V ⊓ (sL T L V).map (MulAut.conj k).toMonoidHom =
    pCoreOf 2 (kz T V) ⊓ Subgroup.centralizer (fsuU T V : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hkH : k ∈ hz T V := oTwoUpper_le _ hk
  rw [← C.pCoreOf_hz_eq]
  refine le_antisymm (fun x hx => ?_) (fun c hc => Subgroup.mem_inf.mpr ⟨C.CU_le_sL hc, ?_⟩)
  ·
    have hUle : fsuU T V ≤ sL T L V ⊓ (sL T L V).map (MulAut.conj k).toMonoidHom :=
      le_inf (le_conjClosure _ _) (C.fsuU_le_conj hk)
    have hxQ : x ∈ pCoreOf 2 (kz T V) := by
      refine le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans C.sL_le_kz)
        (le_normalizer_of_conj_mem' fun g hg y hy => ?_)
        ((pCoreOf_isPGroup 2 (L ⊔ T)).to_le (inf_le_left.trans C.sL_le_Q)) hx
      have h1 := hUle (C.comm_mem_fsuU_of_mem_inf hk hkM hy hg)
      rw [show g * y * g⁻¹ = (g * y * g⁻¹ * y⁻¹) * y by group]
      exact mul_mem h1 hy
    rw [← C.pCoreOf_hz_eq] at hxQ
    exact ((C.l71 G T L V C.hyp).1.1).mem_of_comm hxQ fun g hg =>
      C.fsuU_le_CU (C.comm_mem_fsuU_of_mem_inf hk hkM hx hg)
  ·
    have h1 : k⁻¹ * c * k ∈ pCoreOf 2 (hz T V) ⊓ Subgroup.centralizer (fsuU T V : Set G) := by
      have := (Subgroup.mem_normalizer_iff.mp (C.hz_le_normalizer_CU (inv_mem hkH)) c).mp hc
      simpa using this
    rw [show (sL T L V).map (MulAut.conj k).toMonoidHom = conjSub k (sL T L V) from rfl,
      mem_conjSub]
    exact C.CU_le_sL h1

end Ctx73

end CFSG.Quasithin.H13.L32A
