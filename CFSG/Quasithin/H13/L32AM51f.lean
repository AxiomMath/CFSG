module

public import CFSG.Quasithin.H13.L32AM51d
public import CFSG.Quasithin.H13.L32AM51e
public import CFSG.Quasithin.EmptyFaithful.S146F4
public import CFSG.Quasithin.EmptyFaithful.S152He4Core
public import CFSG.Quasithin.EmptyFaithful.S152He4Par
public import CFSG.Quasithin.EmptyFaithful.S152He4Quot
public import CFSG.Quasithin.H13.L32AC51i
public import CFSG.Quasithin.H13.L32AM51b
public import CFSG.Quasithin.H13.L32AM51c

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Equiv Equiv.Perm
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

namespace Top51

variable {W K : Subgroup G} {π : ↥H →* Perm (Fin 8)} (C : Top51 T L V H W K π)
  [IsMulCommutative ↥(conjClosure V H)]
include C

omit [IsMulCommutative ↥(conjClosure V H)] in
theorem mem_pCoreOf_K_iff {k : G} (hk : k ∈ K) : k ∈ pCoreOf 2 K ↔ k ∈ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hHN : H ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
    C.hKn.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)
  have hHO : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    Subgroup.le_normalizer.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 H)
  constructor
  · intro h
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer (r := 2)
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans C.hKH) hHN
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K) h
  · intro h
    have hN : K ≤ Subgroup.normalizer ((K ⊓ pCoreOf 2 H : Subgroup G) : Set G) := by
      intro x hx
      have hxK := Subgroup.mem_normalizer_iff.mp (C.hKn (C.hKH hx))
      have hxO := Subgroup.mem_normalizer_iff.mp (hHO (C.hKH hx))
      rw [Subgroup.mem_normalizer_iff]
      intro y
      simp only [Subgroup.mem_inf]
      exact ⟨fun h => ⟨(hxK y).mp h.1, (hxO y).mp h.2⟩,
        fun h => ⟨(hxK y).mpr h.1, (hxO y).mpr h.2⟩⟩
    have hX : K ⊓ pCoreOf 2 H ≤ pCoreOf 2 K :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer (r := 2) inf_le_left hN
        ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le inf_le_right)
    exact hX ⟨hk, h⟩

@[expose] noncomputable def thetaK : ↥K →* ↥C.autK :=
  (C.act.comp (Subgroup.inclusion C.hKH)).codRestrict C.autK fun k =>
    ⟨Subgroup.inclusion C.hKH k, Subgroup.mem_subgroupOf.mpr k.2, rfl⟩

theorem thetaK_apply (k : ↥K) :
    (C.thetaK k : MulAut (Hat V H W)) = C.act (Subgroup.inclusion C.hKH k) := rfl

theorem thetaK_surjective : Function.Surjective C.thetaK := by
  rintro ⟨_, ⟨h, hh, rfl⟩⟩
  exact ⟨⟨h, Subgroup.mem_subgroupOf.mp hh⟩, rfl⟩

theorem thetaK_eq_one_iff (k : ↥K) : C.thetaK k = 1 ↔ (k : G) ∈ pCoreOf 2 K := by
  rw [← Subtype.coe_inj, OneMemClass.coe_one, C.thetaK_apply, C.act_eq_one_iff, C.pi_eq_one_iff,
    C.mem_pCoreOf_K_iff k.2]
  rfl

variable {πK : ↥K →* Lin.SLn 4} (hπs : Function.Surjective πK)
  (hkerK : ∀ k : ↥K, πK k = 1 ↔ (k : G) ∈ pCoreOf 2 K)

include hkerK in
theorem ker_thetaK : C.thetaK.ker = πK.ker := by
  ext k
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, C.thetaK_eq_one_iff, hkerK]

@[expose] noncomputable def psi : ↥C.autK ≃* Lin.SLn 4 :=
  (QuotientGroup.quotientKerEquivOfSurjective C.thetaK C.thetaK_surjective).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (C.ker_thetaK hkerK)).trans
      (QuotientGroup.quotientKerEquivOfSurjective πK hπs))

theorem psi_thetaK (k : ↥K) : C.psi hπs hkerK (C.thetaK k) = πK k := by
  have h1 : (QuotientGroup.quotientKerEquivOfSurjective C.thetaK C.thetaK_surjective).symm
      (C.thetaK k) = (k : ↥K ⧸ C.thetaK.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  simp only [psi, MulEquiv.trans_apply, h1]
  rfl

include hπs hkerK in
theorem fixP13_of_irr (hA21 : AsA21SQTKSection) (hirr : C.IrrK) {B : Subgroup G}
    (hB : QCrit (fsuV1 T V) V H B)
    (hD : (T.subgroupOf K).map πK = unitriangular 4 (ZMod 2)) {v : Hat V H W}
    (hv : ∀ k : ↥K, (k : G) ∈ T → C.act (Subgroup.inclusion C.hKH k) v = v) (k : ↥K)
    (hk : πK k ∈ stabilizer (flagSpace 4 (ZMod 2) 2)) :
    C.act (Subgroup.inclusion C.hKH k) v = v := by
  let _ : Module (ZMod 2) (Additive (Hat V H W)) := AddCommGroup.zmodModule (n := 2) fun x => by
    have h3 : Additive.toMul (2 • x) = 1 := by
      rw [toMul_nsmul]
      exact C.sq_eq_one _
    exact toMul_eq_one.1 h3
  set ψ := C.psi hπs hkerK with hψ
  set e : ↥C.autK ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2)) := ψ.trans B42Ln.E4 with he
  have hφ : ∀ l, B42Ln.phiOf4 e l = ψ l := fun l => by
    simp [B42Ln.phiOf4, he]
  obtain ⟨β, hβ⟩ := C.exists_wedge hA21 hirr hB e
  have hβl : ∀ (l : ↥C.autK) (x : Hat V H W), β (Additive.ofMul ((l : MulAut (Hat V H W)) x)) =
      B42Ln.wedgeRep4' (ψ l) (β (Additive.ofMul x)) := by
    intro l x
    rw [← hφ l, ← hβ, B42Ln.repOf4_apply_iso]
  have hU : ∀ u ∈ unitriangular 4 (ZMod 2),
      B42Ln.wedgeRep4' u (β (Additive.ofMul v)) = β (Additive.ofMul v) := by
    intro u hu
    rw [← hD] at hu
    obtain ⟨t, ht, rfl⟩ := hu
    rw [← C.psi_thetaK hπs hkerK t, ← hβl, C.thetaK_apply, hv t (Subgroup.mem_subgroupOf.mp ht)]
  have h1 := Lin.wedge_fix_of_fixU hU hk
  rw [← C.psi_thetaK hπs hkerK k, ← hβl, C.thetaK_apply] at h1
  exact Additive.ofMul.injective (β.injective h1)

end Top51

end CFSG.Quasithin.H13.L32A.C
