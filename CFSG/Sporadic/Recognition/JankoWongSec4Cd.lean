module

public import CFSG.Sporadic.Recognition.JankoWongSec4Struct

public section

namespace CFSG.Sporadic.Recognition.JankoWong

open Equiv Equiv.Perm Subgroup CFSG.GH74 CFSG.GH74.GLS

namespace Setup

variable {G : Type} [Group G] [Finite G] {S : Setup G}

structure IsCd (c : Ctx S) (a₁ v φ₁ : G) (cd : G → Fin 4 → ZMod 3) : Prop where
  add : ∀ m ∈ c.MG, ∀ n ∈ c.MG, cd (m * n) = cd m + cd n
  zero_iff : ∀ m ∈ c.MG, cd m = 0 ↔ m ∈ zpowers (c.a : G)
  phi1 : cd φ₁ = Pi.single 0 1
  phi2 : cd (cj φ₁ v) = Pi.single 1 1
  phi3 : cd (phi3 c a₁ φ₁) = Pi.single 2 1
  phi4 : cd (phi4 c a₁ v φ₁) = Pi.single 3 1

section Certs


namespace Phi1

variable {c : Ctx S} {a₁ v v₁ φ₁ : G} {W : Subgroup G} (hφ : Phi1 c φ₁)
  (h : Sec4Hyp c a₁ v v₁) (hW : c.IsW W)

include hφ h hW in
theorem exists_cd : ∃ cd : G → Fin 4 → ZMod 3, IsCd c a₁ v φ₁ cd := by
  classical
  obtain ⟨crd, -, hker, h1, h2, h3, h4⟩ := hφ.exists_crd h hW
  refine ⟨fun m => if hm : m ∈ c.MG then Multiplicative.toAdd (crd ⟨m, hm⟩) else 0,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m hm n hn
    have e : (⟨m * n, c.MG.mul_mem hm hn⟩ : c.MG) = ⟨m, hm⟩ * ⟨n, hn⟩ := rfl
    simp only [hm, hn, c.MG.mul_mem hm hn, ↓reduceDIte, e, map_mul, toAdd_mul]
  · intro m hm
    simp only [hm, ↓reduceDIte, toAdd_eq_zero]
    exact hker ⟨m, hm⟩
  · simp [hφ.phi1_mem_MG, h1]
  · simp [hφ.phi2_mem_MG h, h2]
  · simp [hφ.phi3_mem_MG h, h3]
  · simp [hφ.phi4_mem_MG h, h4]

end Phi1

end Certs

section NoCerts

namespace IsCd

variable {c : Ctx S} {a₁ v φ₁ : G} {cd : G → Fin 4 → ZMod 3} (hcd : IsCd c a₁ v φ₁ cd)

include hcd in
theorem one : cd 1 = 0 := by
  have := hcd.add 1 c.MG.one_mem 1 c.MG.one_mem
  simp only [mul_one] at this
  have h0 : cd 1 + cd 1 = cd 1 + 0 := by rw [add_zero]; exact this.symm
  exact add_left_cancel h0

include hcd in
theorem inv {m : G} (hm : m ∈ c.MG) : cd m⁻¹ = -cd m := by
  have := hcd.add m hm m⁻¹ (c.MG.inv_mem hm)
  rw [mul_inv_cancel, hcd.one] at this
  exact eq_neg_of_add_eq_zero_right this.symm

include hcd in
theorem zpow {m : G} (hm : m ∈ c.MG) (p : ℤ) : cd (m ^ p) = (p : ZMod 3) • cd m := by
  induction p using Int.induction_on with
  | zero => simp [hcd.one]
  | succ n ih =>
    rw [zpow_add_one, hcd.add _ (c.MG.zpow_mem hm n) _ hm, ih]
    push_cast
    module
  | pred n ih =>
    rw [zpow_sub_one, hcd.add _ (c.MG.zpow_mem hm _) _ (c.MG.inv_mem hm), ih, hcd.inv hm]
    push_cast
    module

include hcd in
theorem eq_zero_of_mem_zpowers {m : G} (hm : m ∈ zpowers (c.a : G)) (hmM : m ∈ c.MG) :
    cd m = 0 := (hcd.zero_iff m hmM).mpr hm

include hcd in
theorem cd_five {x₁ x₂ x₃ x₄ : G} (h₁ : x₁ ∈ c.MG) (h₂ : x₂ ∈ c.MG) (h₃ : x₃ ∈ c.MG)
    (h₄ : x₄ ∈ c.MG) (k q₁ q₂ q₃ q₄ : ℤ) :
    cd ((c.a : G) ^ k * x₁ ^ q₁ * x₂ ^ q₂ * x₃ ^ q₃ * x₄ ^ q₄) =
      (q₁ : ZMod 3) • cd x₁ + (q₂ : ZMod 3) • cd x₂ + (q₃ : ZMod 3) • cd x₃ +
        (q₄ : ZMod 3) • cd x₄ := by
  have ha : (c.a : G) ^ k ∈ c.MG := c.MG.zpow_mem c.a_mem_MG k
  have m1 := c.MG.zpow_mem h₁ q₁
  have m2 := c.MG.zpow_mem h₂ q₂
  have m3 := c.MG.zpow_mem h₃ q₃
  have m4 := c.MG.zpow_mem h₄ q₄
  rw [hcd.add _ (c.MG.mul_mem (c.MG.mul_mem (c.MG.mul_mem ha m1) m2) m3) _ m4,
    hcd.add _ (c.MG.mul_mem (c.MG.mul_mem ha m1) m2) _ m3,
    hcd.add _ (c.MG.mul_mem ha m1) _ m2, hcd.add _ ha _ m1, hcd.zpow h₁, hcd.zpow h₂,
    hcd.zpow h₃, hcd.zpow h₄,
    hcd.eq_zero_of_mem_zpowers (Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k) ha]
  simp only [zero_add, add_assoc]

end IsCd

end NoCerts

end Setup

end CFSG.Sporadic.Recognition.JankoWong
