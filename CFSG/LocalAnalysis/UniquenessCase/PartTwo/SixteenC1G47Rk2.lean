module

public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup
open scoped commutatorElement

private theorem mulAut_mul_comm_of_isCyclic {C : Type*} [Group C] [IsCyclic C]
    (σ τ : MulAut C) : σ * τ = τ * σ := by
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic σ.toMonoidHom
  obtain ⟨n, hn⟩ := MonoidHom.map_cyclic τ.toMonoidHom
  ext g
  change σ (τ g) = τ (σ g)
  have h1 : σ (τ g) = (τ g) ^ m := hm (τ g)
  have h2 : τ (σ g) = (σ g) ^ n := hn (σ g)
  have h3 : τ g = g ^ n := hn g
  have h4 : σ g = g ^ m := hm g
  rw [h1, h2, h3, h4, ← zpow_mul, ← zpow_mul, mul_comm]

theorem s16c1_G47_comm_card_le {Hs : Type} [Group Hs] [Finite Hs] {q : ℕ} (hq : q.Prime)
    {S : Subgroup Hs} (hS : ∀ s ∈ S, s ^ q = 1)
    (hcl : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ⁅⁅a, b⁆, c⁆ = 1)
    (hr : CFSG.Open.pRank q (⊤ : Subgroup Hs) ≤ 2) : IsCyclic ↥⁅S, S⁆ := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  set C : Subgroup Hs := S ⊓ centralizer (S : Set Hs) with hCdef
  have hcomm_le : ⁅S, S⁆ ≤ C := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [commutatorElement_def]
      exact S.mul_mem (S.mul_mem (S.mul_mem ha hb) (S.inv_mem ha)) (S.inv_mem hb)
    · refine Subgroup.mem_centralizer_iff.2 fun c hc => ?_
      exact (commutatorElement_eq_one_iff_mul_comm.mp (hcl a ha b hb c hc)).symm
  by_cases hSle : S ≤ centralizer (S : Set Hs)
  ·
    have hbot : ⁅S, S⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro a ha b hb
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_centralizer_iff.1 (hSle ha) b hb).symm
    rw [hbot]
    infer_instance
  ·
    have hex : ∃ w ∈ S, w ∉ centralizer (S : Set Hs) := by
      by_contra h
      refine hSle ?_
      intro x hx
      by_contra hx'
      exact h ⟨x, hx, hx'⟩
    obtain ⟨w, hwS, hwC⟩ := hex
    set E : Subgroup Hs := C ⊔ Subgroup.zpowers w with hEdef
    have hES : E ≤ S := sup_le inf_le_left (Subgroup.zpowers_le.2 hwS)
    have hEw : E ≤ Subgroup.centralizer ({w} : Set Hs) := by
      refine sup_le ?_ ?_
      · intro c hc
        have hcw : w * c = c * w :=
          Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2 w hwS
        exact Subgroup.mem_centralizer_iff.mpr fun y hy => by
          rw [Set.mem_singleton_iff] at hy
          rw [hy]
          exact hcw
      · rw [Subgroup.zpowers_le]
        exact Subgroup.mem_centralizer_iff.mpr fun y hy => by
          rw [Set.mem_singleton_iff] at hy
          rw [hy]
    have hEa : ∀ a ∈ E, E ≤ Subgroup.centralizer ({a} : Set Hs) := by
      intro a ha
      refine sup_le ?_ ?_
      · intro c hc
        have hca : a * c = c * a :=
          Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2 a (hES ha)
        exact Subgroup.mem_centralizer_iff.mpr fun y hy => by
          rw [Set.mem_singleton_iff] at hy
          rw [hy]
          exact hca
      · rw [Subgroup.zpowers_le]
        have hwa : a * w = w * a :=
          (Subgroup.mem_centralizer_iff.mp (hEw ha) w (Set.mem_singleton w)).symm
        exact Subgroup.mem_centralizer_iff.mpr fun y hy => by
          rw [Set.mem_singleton_iff] at hy
          rw [hy]
          exact hwa
    have hEcomm : IsMulCommutative E :=
      IsMulCommutative.of_comm fun a b =>
        Subtype.ext (Subgroup.mem_centralizer_iff.mp (hEa a a.2 b.2) (a : Hs)
          (Set.mem_singleton (a : Hs)))
    have hEpow : ∀ x ∈ E, x ^ q = 1 := fun x hx => hS x (hES hx)
    have hEelem : CFSG.Open.IsElemAbelian q E := ⟨hEcomm, hEpow⟩
    have hEp : IsPGroup q E := fun x => ⟨1, by
      rw [pow_one]
      exact Subtype.ext (by simpa using hEpow x x.2)⟩
    have hCp : IsPGroup q C := fun x => ⟨1, by
      rw [pow_one]
      exact Subtype.ext (by simpa using hS x (Subgroup.mem_inf.1 x.2).1)⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := q) (G := E)).mp hEp
    obtain ⟨j, hj⟩ := (IsPGroup.iff_card (p := q) (G := C)).mp hCp
    have hCE : C ≤ E := le_sup_left
    have hne : C ≠ E := by
      intro hEq
      have hwE : w ∈ E := Subgroup.mem_sup_right (Subgroup.mem_zpowers w)
      rw [← hEq] at hwE
      exact hwC (Subgroup.mem_inf.1 hwE).2
    have hcard_lt : Nat.card C < Nat.card E := by
      refine lt_of_le_of_ne (Subgroup.card_le_of_le hCE) fun heq => hne ?_
      exact Subgroup.eq_of_le_of_card_ge hCE heq.ge
    have hjk : j < k := by
      have hlt : q ^ j < q ^ k := by rw [← hj, ← hk]; exact hcard_lt
      exact (Nat.pow_lt_pow_iff_right hq.one_lt).mp hlt
    have hk_le : k ≤ CFSG.Open.pRank q (⊤ : Subgroup Hs) :=
      CFSG.SectionRank.le_pRank (H := ⊤) (E := E) hq.one_lt le_top hEelem hk
    have hk2 : k ≤ 2 := hk_le.trans hr
    have hj1 : j ≤ 1 := by omega
    have hCcard : Nat.card C ≤ q := by
      rw [hj]
      calc q ^ j ≤ q ^ 1 := Nat.pow_le_pow_right hq.pos hj1
        _ = q := pow_one q
    have hcomm_card_le : Nat.card ↥⁅S, S⁆ ≤ Nat.card C := Subgroup.card_le_of_le hcomm_le
    have hcomm_p : IsPGroup q ↥⁅S, S⁆ := fun x => ⟨1, by
      rw [pow_one]
      exact Subtype.ext (by simpa using hS x (Subgroup.mem_inf.1 (hcomm_le x.2)).1)⟩
    obtain ⟨i, hi⟩ := (IsPGroup.iff_card (p := q) (G := ↥⁅S, S⁆)).mp hcomm_p
    have hi1 : i ≤ 1 := by
      have hle : q ^ i ≤ q := by
        rw [← hi]
        exact hcomm_card_le.trans hCcard
      exact (Nat.pow_le_pow_iff_right hq.one_lt).mp (by simpa using hle)
    have hdvd : Nat.card ↥⁅S, S⁆ ∣ q := by
      rw [hi]
      simpa using pow_dvd_pow q hi1
    exact isCyclic_of_card_dvd_prime hdvd

theorem s16c1_G47_perfect_cyclic {Γ : Type*} [Group Γ] {X C : Subgroup Γ} [Finite C]
    (hX : Group.IsPerfect X) (hXC : X ≤ normalizer (C : Set Γ)) (hC : IsCyclic C) :
    ∀ x ∈ X, ∀ c ∈ C, x * c * x⁻¹ = c := by
  intro x hx c hc
  let ρ : X →* MulAut C :=
    (MulDistribMulAction.toMulAut (normalizer (C : Set Γ)) C).comp (Subgroup.inclusion hXC)
  haveI : Group.IsPerfect X := hX
  haveI : Group.IsPerfect ρ.range := Group.IsPerfect.range ρ
  haveI : IsMulCommutative ρ.range :=
    IsMulCommutative.of_comm fun a b =>
      Subtype.ext (mulAut_mul_comm_of_isCyclic (a : MulAut C) (b : MulAut C))
  have h1 : ρ ⟨x, hx⟩ = 1 := by
    have := Subsingleton.elim (⟨ρ ⟨x, hx⟩, ⟨x, hx⟩, rfl⟩ : ρ.range) 1
    simpa using congrArg Subtype.val this
  have h2 := congrArg (fun σ : MulAut C => ((σ ⟨c, hc⟩ : C) : Γ)) h1
  exact h2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
