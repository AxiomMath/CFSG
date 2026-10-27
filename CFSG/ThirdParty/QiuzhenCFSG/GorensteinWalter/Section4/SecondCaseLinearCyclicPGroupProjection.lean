module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearEquationElevenData
import Mathlib.GroupTheory.Sylow
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Injectivity on a cyclic p-group from its prime-order subgroup

A homomorphism out of a finite cyclic `p`-group is injective as soon as its
unique order-`p` subgroup is not contained in the kernel.  This is the
projection argument used to show that the graph line in an equation-(11)
centralizer is already Sylow.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u v

/-- A homomorphism from a cyclic finite `p`-group is injective when its
restriction to a specified order-`p` subgroup is nontrivial. -/
public theorem cyclic_pGroup_hom_injective_of_prime_subgroup_not_le_ker
    {S : Type u} {T : Type v} [Group S] [Group T] [Finite S]
    {p : ℕ} [Fact p.Prime]
    (hSp : IsPGroup p S) (hScyc : IsCyclic S)
    (X : Subgroup S) (hXcard : Nat.card X = p)
    (f : S →* T) (hXker : ¬ X ≤ f.ker) :
    Function.Injective f := by
  rw [← MonoidHom.ker_eq_bot_iff]
  by_contra hker
  have hkerp : IsPGroup p f.ker := hSp.to_subgroup f.ker
  have hkcardge : p ≤ Nat.card f.ker := by
    obtain ⟨n, hn⟩ := hkerp.exists_card_eq
    have hn0 : n ≠ 0 := by
      intro hnzero
      subst n
      have hkone : Nat.card f.ker = 1 := by simpa using hn
      exact hker (Subgroup.card_eq_one.mp hkone)
    rw [hn]
    calc
      p = p ^ 1 := by simp
      _ ≤ p ^ n := Nat.pow_le_pow_right (Fact.out : Nat.Prime p).pos
        (Nat.one_le_iff_ne_zero.mpr hn0)
  obtain ⟨Y, hYcard⟩ :=
    Sylow.exists_subgroup_card_pow_prime_of_le_card
      (G := f.ker) (n := 1) (Fact.out : Nat.Prime p) hkerp
        (by simpa using hkcardge)
  let YS : Subgroup S := Y.map f.ker.subtype
  have hYScard : Nat.card YS = p := by
    dsimp [YS]
    rw [Subgroup.card_map_of_injective f.ker.subtype_injective, hYcard, pow_one]
  have hYSleKer : YS ≤ f.ker := by
    dsimp [YS]
    exact Subgroup.map_subtype_le Y
  have hpS : p ∣ Nat.card S := by
    rw [← hXcard]
    simpa using (Subgroup.card_dvd_of_le
      (H := X) (K := (⊤ : Subgroup S)) le_top)
  have hpTop : p ∣ Nat.card (⊤ : Subgroup S) := by simpa using hpS
  let : IsCyclic S := hScyc
  have htopcyc : IsCyclic (⊤ : Subgroup S) := Subgroup.isCyclic_of_le le_top
  obtain ⟨H0, hH0, huniq⟩ :=
    secondCase_unique_order_p_subgroup_of_cyclic
      (G := S) (T := (⊤ : Subgroup S)) htopcyc rfl hpTop
  have hXeq : X = H0 := huniq X ⟨le_top, hXcard⟩
  have hYeq : YS = H0 := huniq YS ⟨le_top, hYScard⟩
  apply hXker
  rw [hXeq, ← hYeq]
  exact hYSleKer

end CFSG.GorensteinWalter
