module

public import CFSG.Quasithin.H13.L32AM51g
public import CFSG.Quasithin.H13.L32AM51f

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Equiv Equiv.Perm
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

namespace Top51

variable {W K : Subgroup G} {π : ↥H →* Perm (Fin 8)} {C : Top51 T L V H W K π}
  [IsMulCommutative ↥(conjClosure V H)]
  {πK : ↥K →* Lin.SLn 4} (hπs : Function.Surjective πK)
  (hkerK : ∀ k : ↥K, πK k = 1 ↔ (k : G) ∈ pCoreOf 2 K)

namespace SplitData

variable {J J' : Subgroup (Hat V H W)} (S : C.SplitData J J')
include S hπs hkerK

theorem types (hA21 : AsA21SQTKSection) {B : Subgroup G} (hB : QCrit (fsuV1 T V) V H B)
    (hD : (T.subgroupOf K).map πK = unitriangular 4 (ZMod 2)) :
    (Nat.card J = 16 ∧ ∀ x ∈ J,
      (∀ k : ↥K, (k : G) ∈ T → C.act (Subgroup.inclusion C.hKH k) x = x) →
        ∀ k : ↥K, πK k ∈ Lin.par 4 2 → C.act (Subgroup.inclusion C.hKH k) x = x) ∨
    (Nat.card J = 64 ∧ ∀ x ∈ J,
      (∀ k : ↥K, (k : G) ∈ T → C.act (Subgroup.inclusion C.hKH k) x = x) →
        ∀ k : ↥K, πK k ∈ stabilizer (flagSpace 4 (ZMod 2) 2) →
          C.act (Subgroup.inclusion C.hKH k) x = x) := by
  let _ : Module (ZMod 2) (Additive ↥J) := AddCommGroup.zmodModule (n := 2) fun x => by
    have h3 : Additive.toMul (2 • x) = 1 := by
      rw [toMul_nsmul]
      exact Subtype.ext (C.sq_eq_one _)
    exact toMul_eq_one.1 h3
  set e : ↥C.autK ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2)) :=
    (C.psi hπs hkerK).trans B42Ln.E4 with he
  have hφ : ∀ t : ↥K, B42Ln.phiOf4 e (C.thetaK t) = πK t := fun t => by
    rw [← C.psi_thetaK hπs hkerK t]
    simp [B42Ln.phiOf4, he]
  obtain ⟨E₁, hE₁K, hE₁1, hE₁ab, hE₁J⟩ := S.offender hB
  have hX := C.sqtkGroup_range hA21
  have hfix : ∀ x (hx : x ∈ J), (∀ k : ↥K, (k : G) ∈ T →
      C.act (Subgroup.inclusion C.hKH k) x = x) → ∀ t : ↥K, (t : G) ∈ T →
      (⟨((C.thetaK t : ↥C.autK) : MulAut (Hat V H W)) x, S.inv _ (C.thetaK t).2 x hx⟩ : ↥J) =
        ⟨x, hx⟩ := fun x hx hxT t ht => Subtype.ext (hxT t ht)
  rcases classify_sub hA21 hX (Hs := C.autK.subgroupOf C.act.range)
      (Subgroup.subgroupOfEquivOfLe C.autK_le).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe C.autK_le).surjective e S.inv S.min S.nt hE₁K hE₁1 hE₁ab
      hE₁J with ⟨κ, β, hβ⟩ | ⟨β, hβ⟩
  · left
    refine ⟨?_, fun x hx hxT k hk => ?_⟩
    · rw [show Nat.card ↥J = Nat.card (Additive ↥J) from rfl, Nat.card_congr β.toEquiv]
      simp [Nat.card_eq_fintype_card]
    · have hU : ∀ u ∈ unitriangular 4 (ZMod 2),
          B42Ln.natRep4 (κ u) (β (Additive.ofMul ⟨x, hx⟩)) = β (Additive.ofMul ⟨x, hx⟩) := by
        intro u hu
        rw [← hD] at hu
        obtain ⟨t, ht, rfl⟩ := hu
        have h1 := hβ (C.thetaK t) ⟨x, hx⟩
        rw [hφ, hfix x hx hxT t (Subgroup.mem_subgroupOf.mp ht)] at h1
        exact h1.symm
      have h2 := Lin.nat_fix_of_fixU κ hU hk
      have h3 := hβ (C.thetaK k) ⟨x, hx⟩
      rw [hφ, h2] at h3
      have h4 := Additive.ofMul.injective (β.injective h3)
      exact congrArg Subtype.val h4
  · right
    refine ⟨?_, fun x hx hxT k hk => ?_⟩
    · rw [show Nat.card ↥J = Nat.card (Additive ↥J) from rfl, Nat.card_congr β.toEquiv]
      simp [Nat.card_eq_fintype_card]
    · have hU : ∀ u ∈ unitriangular 4 (ZMod 2),
          B42Ln.wedgeRep4' u (β (Additive.ofMul ⟨x, hx⟩)) = β (Additive.ofMul ⟨x, hx⟩) := by
        intro u hu
        rw [← hD] at hu
        obtain ⟨t, ht, rfl⟩ := hu
        have h1 := hβ (C.thetaK t) ⟨x, hx⟩
        rw [hφ, hfix x hx hxT t (Subgroup.mem_subgroupOf.mp ht)] at h1
        exact h1.symm
      have h2 := Lin.wedge_fix_of_fixU hU hk
      have h3 := hβ (C.thetaK k) ⟨x, hx⟩
      rw [hφ, h2] at h3
      have h4 := Additive.ofMul.injective (β.injective h3)
      exact congrArg Subtype.val h4

end SplitData

variable (C)

include hπs hkerK in
theorem fix_cases (hA21 : AsA21SQTKSection) {B : Subgroup G} (hB : QCrit (fsuV1 T V) V H B)
    (hD : (T.subgroupOf K).map πK = unitriangular 4 (ZMod 2)) {v : Hat V H W}
    (hv : ∀ k : ↥K, (k : G) ∈ T → C.act (Subgroup.inclusion C.hKH k) v = v) :
    (∀ k : ↥K, πK k ∈ stabilizer (flagSpace 4 (ZMod 2) 2) →
      C.act (Subgroup.inclusion C.hKH k) v = v) ∨
    ∀ k : ↥K, πK k ∈ Lin.par 4 2 → C.act (Subgroup.inclusion C.hKH k) v = v := by
  by_cases hirr : C.IrrK
  · exact Or.inl (C.fixP13_of_irr hπs hkerK hA21 hirr hB hD hv)
  obtain ⟨J, J', S⟩ := C.exists_split hirr
  have hv' : v ∈ J ⊔ J' := by
    rw [S.sup]
    exact Subgroup.mem_top v
  obtain ⟨j, hj, j', hj', rfl⟩ := Subgroup.mem_sup.mp hv'
  have hmemK : ∀ k : ↥K, C.act (Subgroup.inclusion C.hKH k) ∈ C.autK := fun k => (C.thetaK k).2
  have hcomp : ∀ k : ↥K, (k : G) ∈ T →
      C.act (Subgroup.inclusion C.hKH k) j = j ∧ C.act (Subgroup.inclusion C.hKH k) j' = j' := by
    intro k hk
    have he := hv k hk
    rw [map_mul] at he
    exact Split.eq_of_mul_eq S.inf (S.inv _ (hmemK k) j hj) hj (S.inv' _ (hmemK k) j' hj') hj' he
  have hcard := S.card_eq
  rcases S.types hπs hkerK hA21 hB hD with ⟨h16, hJ⟩ | ⟨h64, hJ⟩ <;>
    rcases S.symm.types hπs hkerK hA21 hB hD with ⟨h16', hJ'⟩ | ⟨h64', hJ'⟩
  · right
    intro k hk
    rw [map_mul, hJ j hj (fun k hk => (hcomp k hk).1) k hk,
      hJ' j' hj' (fun k hk => (hcomp k hk).2) k hk]
  · exfalso
    omega
  · exfalso
    omega
  · left
    intro k hk
    rw [map_mul, hJ j hj (fun k hk => (hcomp k hk).1) k hk,
      hJ' j' hj' (fun k hk => (hcomp k hk).2) k hk]

end Top51

end CFSG.Quasithin.H13.L32A.C
