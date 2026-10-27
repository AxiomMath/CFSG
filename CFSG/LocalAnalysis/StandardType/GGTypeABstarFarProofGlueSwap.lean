module

public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofGlueRefl
public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofRefl

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal.SpecialLinear Matrix

section Swap

variable {G : Type} [Group G] {p : ℕ} {Bs : Subgroup G} {n : ℕ} {F : Type} [Field F] [Finite F]
  {φ₁ φ₂ : SpecialLinearGroup (Fin (n + 1)) F →* G} {x y : G}

theorem GGFarCtx.permAut₁_swap_fix_iff (hC : GGFarCtx p Bs φ₁ φ₂ x y) {i j : Fin n} (hij : i ≠ j)
    (b : ↥Bs) :
    hC.permAut₁ (Equiv.swap i.succ j.succ) b = b ↔ hC.lamHom i.succ j.succ b = 1 := by
  classical
  set π : Equiv.Perm (Fin (n + 1)) := Equiv.swap i.succ j.succ with hπ
  set π' : Equiv.Perm (Fin (n + 1)) := Equiv.swap i.castSucc j.castSucc with hπ'
  have hsymm0 : π.symm (0 : Fin (n + 1)) = 0 := by
    rw [hπ, Equiv.symm_apply_eq]
    exact (Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero i).symm
      (Fin.succ_ne_zero j).symm).symm
  have hsymmi : π.symm i.succ = j.succ := by
    rw [hπ, Equiv.symm_apply_eq]
    exact (Equiv.swap_apply_right i.succ j.succ).symm
  have hsymmj : π.symm j.succ = i.succ := by
    rw [hπ, Equiv.symm_apply_eq]
    exact (Equiv.swap_apply_left i.succ j.succ).symm
  have hsymm'i : π'.symm i.castSucc = j.castSucc := by
    rw [hπ', Equiv.symm_apply_eq]
    exact (Equiv.swap_apply_right i.castSucc j.castSucc).symm
  have hsymm'j : π'.symm j.castSucc = i.castSucc := by
    rw [hπ', Equiv.symm_apply_eq]
    exact (Equiv.swap_apply_left i.castSucc j.castSucc).symm
  constructor
  · intro hfix
    obtain ⟨h, ha⟩ := hC.lifts.diag₁ (b : G) b.2
    have hconj : φ₁ (slPerm hC.two π) * (b : G) * (φ₁ (slPerm hC.two π))⁻¹ = (b : G) := by
      have h1 := hC.permAut₁_apply π b
      rw [hfix] at h1
      exact h1.symm
    have hconjvec : GGActsVec φ₁ (b : G) (h ∘ π.symm) := by
      have h2 := GGActsVec.conj_perm hC.two (φ := φ₁) ha π
      rwa [hconj] at h2
    have e : GGVecEq h (h ∘ π.symm) := GGActsVec.vecEq hC.lifts.ker₁ ha hconjvec
    obtain ⟨c, hc⟩ := ggVecEq_iff_exists.mp e
    have hc0 : c = 1 := by
      have h0 := hc (0 : Fin (n + 1))
      simp only [Function.comp_apply, hsymm0] at h0
      exact mul_right_cancel (by rw [one_mul]; exact h0.symm)
    have hji : h j.succ = h i.succ := by
      have hi := hc i.succ
      simp only [Function.comp_apply, hsymmi, hc0, one_mul] at hi
      exact hi.symm
    rw [hC.lamHom_apply, hC.lamFun_eq i.succ j.succ ha, hji, mul_inv_cancel]
  · intro hlam
    obtain ⟨h, ha⟩ := hC.lifts.diag₁ (b : G) b.2
    obtain ⟨h₂, ha₂⟩ := hC.lifts.diag₂ (b : G) b.2
    have hji : h j.succ = h i.succ := by
      have h1 := hC.lamFun_eq i.succ j.succ ha
      rw [hC.lamHom_apply] at hlam
      rw [hlam] at h1
      exact mul_inv_eq_one.mp h1.symm
    have hcomp : h ∘ π.symm = h := by
      funext k
      by_cases hki : k = i.succ
      · subst hki
        rw [Function.comp_apply, hsymmi, hji]
      · by_cases hkj : k = j.succ
        · subst hkj
          rw [Function.comp_apply, hsymmj, hji]
        · have hk : π.symm k = k := by
            rw [hπ, Equiv.symm_apply_eq]
            exact (Equiv.swap_apply_of_ne_of_ne hki hkj).symm
          rw [Function.comp_apply, hk]
    have hbc : GGVecEq (h ∘ Fin.succ) (h₂ ∘ Fin.castSucc) :=
      GGActsVec.block_compat hC.lifts.ker₁ hC.lifts.compat ha ha₂
    obtain ⟨c, hc⟩ := ggVecEq_iff_exists.mp hbc
    have h2ij : h₂ i.castSucc = h₂ j.castSucc := by
      have hi := hc i
      have hj := hc j
      simp only [Function.comp_apply] at hi hj
      rw [hji] at hj
      rw [hi] at hj
      exact mul_left_cancel hj
    have h2comp : h₂ ∘ π'.symm = h₂ := by
      funext k
      by_cases hki : k = i.castSucc
      · subst hki
        rw [Function.comp_apply, hsymm'i, h2ij]
      · by_cases hkj : k = j.castSucc
        · subst hkj
          rw [Function.comp_apply, hsymm'j, h2ij]
        · have hk : π'.symm k = k := by
            rw [hπ', Equiv.symm_apply_eq]
            exact (Equiv.swap_apply_of_ne_of_ne hki hkj).symm
          rw [Function.comp_apply, hk]
    have hb'1 : GGActsVec φ₁ (hC.permAut₁ π b : G) h := by
      have h2 := GGActsVec.conj_perm hC.two (φ := φ₁) ha π
      rw [← hC.permAut₁_apply π b, hcomp] at h2
      exact h2
    have hb'2 : GGActsVec φ₂ (hC.permAut₁ π b : G) h₂ := by
      have h2 := GGActsVec.conj_perm hC.two (φ := φ₂) ha₂ π'
      have ht : φ₁ (slPerm hC.two π) = φ₂ (slPerm hC.two π') := by
        rw [hπ, hπ']
        exact hC.map_slPerm_swap_compat i j
      have heq : (hC.permAut₁ π b : G) =
          φ₂ (slPerm hC.two π') * (b : G) * (φ₂ (slPerm hC.two π'))⁻¹ := by
        rw [hC.permAut₁_apply π b, ht]
      rw [← heq, h2comp] at h2
      exact h2
    exact Subtype.ext (hC.eq_of_vecEq (b := (hC.permAut₁ π b : G)) (b' := (b : G))
      (hC.permAut₁ π b).2 b.2 hb'1 ha hb'2 ha₂
      (GGVecEq.refl h) (GGVecEq.refl h₂))

theorem GGFarCtx.exists_lamHom_ne_one (hC : GGFarCtx p Bs φ₁ φ₂ x y) {k l : Fin (n + 1)}
    (hkl : k ≠ l) : ∃ b : ↥Bs, hC.lamHom k l b ≠ 1 := by
  obtain ⟨τ, hτ, hvecs⟩ := hC.exists_vecs₁
  obtain ⟨z, hz, hzvec⟩ := hvecs k
  refine ⟨⟨z, hz⟩, ?_⟩
  rw [hC.lamHom_apply, hC.lamFun_eq k l hzvec, diagAt_apply_of_ne hkl.symm τ,
    diagAt_apply_self]
  simpa using inv_ne_one.mpr hτ

theorem GGFarCtx.natCard_range_lamHom (hC : GGFarCtx p Bs φ₁ φ₂ x y) {k l : Fin (n + 1)}
    (hkl : k ≠ l) : Nat.card (hC.lamHom k l).range = p := by
  have hRle : (hC.lamHom k l).range ≤ (powMonoidHom p : Fˣ →* Fˣ).ker := by
    rintro r ⟨b, rfl⟩
    rw [MonoidHom.mem_ker, powMonoidHom_apply, ← map_pow]
    rw [show b ^ p = 1 from Subtype.ext (by simpa using hC.exp (b : G) b.2), map_one]
  have hdvd : Nat.card (hC.lamHom k l).range ∣ p := by
    refine dvd_trans (Subgroup.card_dvd_of_le hRle) ?_
    rw [IsCyclic.card_powMonoidHom_ker (G := Fˣ) p]
    exact Nat.gcd_dvd_right _ _
  have hne : (hC.lamHom k l).range ≠ ⊥ := by
    obtain ⟨b, hb⟩ := hC.exists_lamHom_ne_one hkl
    intro hbot
    have hmem : hC.lamHom k l b ∈ (hC.lamHom k l).range := ⟨b, rfl⟩
    rw [hbot] at hmem
    exact hb (Subgroup.mem_bot.mp hmem)
  have hgt : 1 < Nat.card (hC.lamHom k l).range :=
    (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
  rcases hC.prime.eq_one_or_self_of_dvd _ hdvd with h1 | hp
  · omega
  · exact hp

theorem GGFarCtx.permAut₁_swap_succ_isReflection (hC : GGFarCtx p Bs φ₁ φ₂ x y) {i j : Fin n}
    (hij : i ≠ j) : GGIsReflection p (hC.permAut₁ (Equiv.swap i.succ j.succ)) := by
  have hij' : i.succ ≠ j.succ := fun h => hij (Fin.succ_injective n h)
  refine ⟨?_, ?_⟩
  · show (hC.permAut₁ (Equiv.swap i.succ j.succ)) ^ 2 = 1
    rw [← map_pow, show Equiv.swap i.succ j.succ ^ 2 = 1 by
      rw [pow_two, Equiv.swap_mul_self], map_one]
  · have hcard : Nat.card {b : ↥Bs // hC.permAut₁ (Equiv.swap i.succ j.succ) b = b} =
        Nat.card (hC.lamHom i.succ j.succ).ker :=
      Nat.card_congr (Equiv.subtypeEquivRight
        (fun b => hC.permAut₁_swap_fix_iff hij b))
    rw [hcard]
    have hci := Subgroup.card_mul_index (hC.lamHom i.succ j.succ).ker
    rw [Subgroup.index_ker, hC.natCard_range_lamHom hij'] at hci
    exact hci

theorem GGFarCtx.permAut₁_swap_isReflection (hC : GGFarCtx p Bs φ₁ φ₂ x y)
    {a b : Fin (n + 1)} (hab : a ≠ b) : GGIsReflection p (hC.permAut₁ (Equiv.swap a b)) := by
  have hn : 3 ≤ n := hC.three_le
  have h0 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by
    intro h
    have h1 : (0 : ℕ) = 1 := congrArg Fin.val h
    omega
  exact ggIsReflection_swap_of_swap hC.permAut₁
    (a := (⟨0, by omega⟩ : Fin n).succ) (b := (⟨1, by omega⟩ : Fin n).succ)
    (by intro h; exact h0 (Fin.succ_injective n h))
    (hC.permAut₁_swap_succ_isReflection (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩) h0)
    hab

theorem GGFarCtx.permAut₂_swap_isReflection (hC : GGFarCtx p Bs φ₁ φ₂ x y)
    {a b : Fin (n + 1)} (hab : a ≠ b) : GGIsReflection p (hC.permAut₂ (Equiv.swap a b)) := by
  have hn : 3 ≤ n := hC.three_le
  have h0 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by
    intro h
    have h1 : (0 : ℕ) = 1 := congrArg Fin.val h
    omega
  have hbase : GGIsReflection p (hC.permAut₂
      (Equiv.swap (⟨0, by omega⟩ : Fin n).castSucc (⟨1, by omega⟩ : Fin n).castSucc)) := by
    rw [← hC.permAut_compat (⟨0, by omega⟩) (⟨1, by omega⟩)]
    exact hC.permAut₁_swap_succ_isReflection h0
  exact ggIsReflection_swap_of_swap hC.permAut₂
    (a := (⟨0, by omega⟩ : Fin n).castSucc) (b := (⟨1, by omega⟩ : Fin n).castSucc)
    (by intro h; exact h0 (Fin.castSucc_injective n h)) hbase hab

end Swap

end CFSG.StandardType
