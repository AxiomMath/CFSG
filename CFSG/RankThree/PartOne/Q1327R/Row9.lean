module

public import CFSG.RankThree.PartOne.Q1327R.Block9
public import CFSG.RankThree.PartOne.Q1327R.Refl9

public section

namespace CFSG.RankThree.PartOne.Q1327R

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.Sec12Three
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.GroupTheory

variable {G : Type} [Group G] [Finite G]

theorem exists_frame {p f : ℕ} {X F : Subgroup G} (hp : p.Prime) (hp5 : 5 ≤ p) (hf2 : 2 ≤ f)
    (hpf : p ∣ 2 ^ f + 1) (hZ : Subgroup.center ↥X = ⊥)
    (hmodel : StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) .PSU 4 2 f)
    (hFel : IsElementaryAbelian p ↥F) (hFX : F ≤ X) (hFcard : Nat.card F = p ^ 3) :
    ∃ (K : Type) (_ : Field K), Nonempty (U4Frame p f K X F) := by
  obtain ⟨-, K, hKf, hKfin, hK, ⟨e⟩⟩ := hmodel
  have hU : UnitaryFieldData 2 f K := ⟨Nat.prime_two, by omega, by rw [hK, ← pow_mul, mul_comm]⟩
  have hFexp : ∀ x ∈ F.subgroupOf X, x ^ p = 1 := by
    intro x hx
    have hxF : (x : G) ∈ F := Subgroup.mem_subgroupOf.mp hx
    apply Subtype.ext
    have := hFel
    simpa using elemPow_eq_one_of_isElementaryAbelian (x : G) hxF
  have hFcomm : ∀ x ∈ F.subgroupOf X, ∀ y ∈ F.subgroupOf X, x * y = y * x := by
    intro x hx y hy
    apply Subtype.ext
    show (x : G) * (y : G) = (y : G) * (x : G)
    exact congrArg Subtype.val (hFel.is_comm.comm ⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩
      ⟨(y : G), Subgroup.mem_subgroupOf.mp hy⟩)
  have hFcard' : Nat.card (F.subgroupOf X) = p ^ 3 := by
    rw [← hFcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFX).toEquiv
  obtain ⟨ψ, hψ⟩ := exists_diag_iso (K := K) (by omega) hK hp hpf hZ e _ hFexp hFcomm hFcard'
  exact ⟨K, inferInstance, ⟨⟨hp, hp5, hU, hf2, hpf, hFX, ψ, fun g => by
    have h1 := hψ g
    rwa [Subgroup.mem_subgroupOf] at h1⟩⟩⟩

theorem kf1327Row9_holds : Q1327.KF1327Row9 := by
  intro G _ _ p f X F hp hp5 hf2 hpf _ hZ hmodel hFel hFX hFcard t K ht hrefl hKC hKθ hmov
  obtain ⟨K0, _, ⟨C⟩⟩ := exists_frame hp hp5 hf2 hpf hZ hmodel hFel hFX hFcard
  obtain ⟨w, hwX, hwN, hwt⟩ := Sec12Three.mem_torusImage_iff.1 ht
  obtain ⟨g, τ, hg, hτ⟩ := C.exists_perm hwX hwN
  subst hwt
  obtain ⟨a, b, hab, rfl⟩ := C.exists_swap_of_reflection hwN hg hτ hrefl
  exact (U4Frame.Refl.mk (C := C) w hwN g hg a b hab hτ).model hrefl hKC hKθ hmov

end CFSG.RankThree.PartOne.Q1327R
