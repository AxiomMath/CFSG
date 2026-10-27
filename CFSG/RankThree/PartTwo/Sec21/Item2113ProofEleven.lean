module

public import CFSG.RankThree.PartTwo.Sec12.Coordinates
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item2113Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

variable {G : Type} [Group G]

section Coords

variable {A : Subgroup G} {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]

@[expose] def ofCoords (f : Multiplicative V ≃* A) (τ : V ≃ₗ[ZMod 3] V) : MulAut A :=
  (f.symm.trans (AddEquiv.toMultiplicative τ.toAddEquiv)).trans f

theorem ofCoords_apply (f : Multiplicative V ≃* A) (τ : V ≃ₗ[ZMod 3] V) (x : A) :
    ofCoords f τ x = f (Multiplicative.ofAdd (τ (Multiplicative.toAdd (f.symm x)))) :=
  rfl

theorem coordHom_ofCoords (f : Multiplicative V ≃* A) (τ : V ≃ₗ[ZMod 3] V) :
    Sec12.coordHom f (ofCoords f τ) = τ := by
  ext v
  simp [Sec12.coordHom_apply, ofCoords_apply]

theorem coords_smul (f : Multiplicative V ≃* A) (a : ZMod 3) (v : V) :
    f (Multiplicative.ofAdd (a • v)) = f (Multiplicative.ofAdd v) ^ a.val := by
  have h : a • v = a.val • v := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod 3), ZMod.natCast_zmod_val]
  rw [h, ofAdd_nsmul, map_pow]

end Coords

theorem mem_zpowers_pow {A : Type*} [Group A] {d : A} (h3 : d ^ 3 = 1) {n : ℕ} (hn : ¬ 3 ∣ n) :
    d ∈ Subgroup.zpowers (d ^ n) := by
  have hmod : d ^ n = d ^ (n % 3) := by
    calc d ^ n = d ^ (3 * (n / 3) + n % 3) := by rw [Nat.div_add_mod]
      _ = d ^ (n % 3) := by rw [pow_add, pow_mul, h3, one_pow, one_mul]
  have h1 : n % 3 = 1 ∨ n % 3 = 2 := by omega
  rw [hmod]
  rcases h1 with h | h
  · rw [h, pow_one]
    exact Subgroup.mem_zpowers d
  · rw [h]
    have hsq : (d ^ 2) ^ 2 = d := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, h3, one_mul, pow_one]
    have h' : (d ^ 2) ^ 2 ∈ Subgroup.zpowers (d ^ 2) := pow_mem (Subgroup.mem_zpowers _) 2
    rwa [hsq] at h'

end CFSG.RankThree.PartTwo.Sec21.Item2113Proof
