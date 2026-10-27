module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4F94M3

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

theorem units5_inj : ∀ x : (ZMod 5)ˣ, x * x ≠ 1 → ∀ i j : Fin 4, x ^ (i : ℕ) = x ^ (j : ℕ) →
    i = j := by
  decide

theorem pow_inj_two {a b : Fin 3 → (ZMod 5)ˣ} (ha0 : a 0 * a 0 ≠ 1) (ha2 : a 2 = 1)
    (hb0 : b 0 = 1) (hb2 : b 2 * b 2 ≠ 1) :
    Function.Injective (fun p : Fin 4 × Fin 4 => a ^ (p.1 : ℕ) * b ^ (p.2 : ℕ)) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  have h0 := congrFun h 0
  have h2 := congrFun h 2
  simp only [Pi.mul_apply, Pi.pow_apply, hb0, ha2, one_pow, mul_one, one_mul] at h0 h2
  exact Prod.ext (units5_inj _ ha0 _ _ h0) (units5_inj _ hb2 _ _ h2)

theorem pow_inj_three {a b cc : Fin 3 → (ZMod 5)ˣ} (ha0 : a 0 * a 0 ≠ 1) (ha2 : a 2 = 1)
    (hb0 : b 0 = 1) (hb2 : b 2 * b 2 ≠ 1) (hc0 : cc 0 = 1) (hc2 : cc 2 = 1) (hc1 : cc 1 = -1) :
    Function.Injective
      (fun p : Fin 4 × Fin 4 × Fin 2 => a ^ (p.1 : ℕ) * b ^ (p.2.1 : ℕ) * cc ^ (p.2.2 : ℕ)) := by
  rintro ⟨i, j, k⟩ ⟨i', j', k'⟩ h
  have h0 := congrFun h 0
  have h2 := congrFun h 2
  simp only [Pi.mul_apply, Pi.pow_apply, hb0, ha2, hc0, hc2, one_pow, mul_one, one_mul] at h0 h2
  have hi := units5_inj _ ha0 _ _ h0
  have hj := units5_inj _ hb2 _ _ h2
  subst hi
  subst hj
  have h1 := congrFun h 1
  simp only [Pi.mul_apply, Pi.pow_apply, hc1, mul_right_inj] at h1
  have hk : ∀ k k' : Fin 2, (-1 : (ZMod 5)ˣ) ^ (k : ℕ) = (-1) ^ (k' : ℕ) → k = k' := by decide
  exact by rw [hk _ _ h1]

theorem card_le_relIndex {G P : Type*} [Group G] [Group P] {N H : Subgroup G} [Finite H]
    (Ψ : H →* P) (hker : ∀ h : H, (h : G) ∈ N → Ψ h = 1) {ι : Type*} [Finite ι]
    (f : ι → H) (hf : Function.Injective fun x => Ψ (f x)) : Nat.card ι ≤ N.relIndex H := by
  have : Finite Ψ.range := Finite.of_surjective Ψ.rangeRestrict Ψ.rangeRestrict_surjective
  have h1 : Nat.card ι ≤ Nat.card Ψ.range :=
    Nat.card_le_card_of_injective (fun x => (⟨Ψ (f x), ⟨f x, rfl⟩⟩ : Ψ.range))
      fun x y hxy => hf (congrArg Subtype.val hxy)
  have h2 : N.subgroupOf H ≤ Ψ.ker := fun h hh => by
    rw [MonoidHom.mem_ker]
    exact hker h (Subgroup.mem_subgroupOf.1 hh)
  exact h1.trans (card_range_le_index_of_le_ker Ψ h2)

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Sec9Cfg

variable {L : ZLab Γ G} (S : Sec9Cfg L)

theorem exists_arm_hom (F : FanTree Γ G) :
    ∃ Φ : ↥(nbrStab Γ G S.beta) →* (Fin 3 → (ZMod 5)ˣ),
      ∀ (g : ↥(nbrStab Γ G S.beta)) (i : Fin 3),
        Φ g i = 1 ↔ (g : G) ∈ nbrStab Γ G (S.alphaV i) := by
  choose φ hφ using S.exists_arm_char F
  have hle : ∀ i, nbrStab Γ G S.beta ≤
      MulAction.stabilizer G (S.alphaV i) ⊓ MulAction.stabilizer G S.beta := fun i g hg =>
    ⟨MulAction.mem_stabilizer_iff.2 (mem_nbrStab.1 hg _ (S.adj_beta_alphaV F i)),
      F.nbrStab_le_stabilizer S.beta hg⟩
  refine ⟨MonoidHom.pi fun i => (φ i).comp (Subgroup.inclusion (hle i)), fun g i => ?_⟩
  exact (hφ i (Subgroup.inclusion (hle i) g)).symm

end Sec9Cfg

end CFSG.Quasithin.Fan86
