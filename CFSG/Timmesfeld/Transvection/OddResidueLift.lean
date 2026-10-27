module

public import CFSG.Timmesfeld.Transvection.OddSU3Chord
public import CFSG.LocalAnalysis.UniquenessCase.Lie.Cover
public import CFSG.Timmesfeld.Transvection.ResidueBender

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg
open CFSG.LieType.BorelTits CFSG.LocalAnalysis.UniquenessCase CFSG.LieType.Steinberg.CentralExt
open scoped commutatorElement CharTwo

variable {H : Type} [Group H] {Δ : Set (Subgroup H)} {r : ℕ} {P Q : Fin r → Subgroup H}
  {k : Fin r} {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

private theorem commutator_sup_eq_self_of_opposite [Finite H]
    (hΔ : IsTransvectionClass Δ)
    {X Y : Subgroup H} (hX : X ∈ Δ) (hopp : Opposite X Y) (hq : 4 ≤ Nat.card X) :
    (⁅X ⊔ Y, X ⊔ Y⁆ : Subgroup H) = X ⊔ Y := by
  obtain ⟨m, hm, -, φ, -, -⟩ := hopp.exists_mulEquiv_SL2 hΔ.root hX hq
  classical
  have hG4 : 4 ≤ Nat.card (GaloisField 2 m) := by
    rw [GaloisField.card (p := 2) (n := m) (ne_of_gt (lt_of_lt_of_le (by norm_num) hm))]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  haveI : Fintype (GaloisField 2 m) := Fintype.ofFinite _
  have hfin : ∃ s : Finset (GaloisField 2 m), s.card = 4 := by
    have h : 4 ≤ (Finset.univ : Finset (GaloisField 2 m)).card := by
      rwa [Finset.card_univ, ← Nat.card_eq_fintype_card]
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq h
    exact ⟨s, hs⟩
  haveI : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 m)) :=
    CFSG.LinearGroups.special_linear_dimension_two_perfect hfin
  haveI : Group.IsPerfect ↥(X ⊔ Y) :=
    Group.IsPerfect.ofSurjective (f := φ.symm.toMonoidHom) φ.symm.surjective
  exact Subgroup.commutator_eq_self

theorem commutator_residueGroup_eq_top [Finite H]
    (hΔ : IsTransvectionClass Δ) (hML : MeetsLines Δ) (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A)
    (hF : IsMaxFrame Δ P Q) : commutator ↥(residueGroup Δ P Q k) = ⊤ := by
  classical
  let L : Subgroup H := residueGroup Δ P Q k
  have hpair : ∀ X ∈ frameResidue Δ P Q k, X ≤ (⁅L, L⁆ : Subgroup H) := by
    intro X hX
    obtain ⟨Y, hY, hYX⟩ := exists_mem_frameResidue_ne hF X
    have hopp : Opposite X Y := hF.opposite_of_mem_frameResidue hΔ hML hX hY hYX.symm
    have hperf : (⁅X ⊔ Y, X ⊔ Y⁆ : Subgroup H) = X ⊔ Y :=
      commutator_sup_eq_self_of_opposite hΔ hX.1 hopp (hq X hX.1)
    calc X ≤ X ⊔ Y := le_sup_left
      _ = ⁅X ⊔ Y, X ⊔ Y⁆ := hperf.symm
      _ ≤ ⁅L, L⁆ :=
        Subgroup.commutator_mono
          (sup_le (frameResidue_le_residueGroup hX) (frameResidue_le_residueGroup hY))
          (sup_le (frameResidue_le_residueGroup hX) (frameResidue_le_residueGroup hY))
  have hle : L ≤ (⁅L, L⁆ : Subgroup H) := by
    change (⨆ X ∈ frameResidue Δ P Q k, X) ≤ (⁅L, L⁆ : Subgroup H)
    exact iSup₂_le hpair
  have htop : (⁅(⊤ : Subgroup ↥L), ⊤⁆ : Subgroup ↥L) = ⊤ := by
    apply Subgroup.map_injective (f := L.subtype) L.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
    refine le_antisymm ?_ hle
    rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [commutatorElement_def]
    exact L.mul_mem (L.mul_mem (L.mul_mem hx hy) (L.inv_mem hx)) (L.inv_mem hy)
  show commutator ↥L = ⊤
  exact htop

theorem su3Top_mul_self {x : SU (unitaryInvolution F 2 n) 3}
    (hx : x ∈ su3Top (unitaryInvolution F 2 n)) : x * x = 1 := by
  obtain ⟨β, hβ, rfl⟩ := (mem_su3Top_iff_Y (σ := unitaryInvolution F 2 n)).1 hx
  refine SUExtras.mat_injective ?_
  rw [map_mul, UC22.uc22pwsu3_mat_Y, map_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem IsMaxFrame.exists_su3_cover [Finite H]
    (h : TransvectionHyp H Δ) (hML : MeetsLines Δ) (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A)
    (hF : IsMaxFrame Δ P Q) (hns : ¬ IsSmallFrame Δ P Q k)
    (hFn : Nat.card F = (2 ^ n) ^ 2) (hcard : ∀ A ∈ Δ, Nat.card A = 2 ^ n) :
    ∃ α : SU (unitaryInvolution F 2 n) 3 →* ↥(residueGroup Δ P Q k),
      Function.Surjective α ∧ α.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 n) 3) ∧
        Odd (Nat.card α.ker) ∧
        ((QuotientGroup.mk' (Subgroup.center ↥(residueGroup Δ P Q k))).comp α).ker ≤
          Subgroup.center (SU (unitaryInvolution F 2 n) 3) ∧
        Odd (Nat.card
          ((QuotientGroup.mk' (Subgroup.center ↥(residueGroup Δ P Q k))).comp α).ker) := by
  classical
  haveI : Finite H := h.finite
  obtain ⟨n', hn', hcard', ⟨e⟩⟩ := hF.residueGroup_quotient_psu3 h hML hq hns
  have hn'n : n' = n := by
    have h1 : Nat.card (P k) = 2 ^ n' := hcard' (P k) (hF.toIsFrame.memP k)
    have h2 : Nat.card (P k) = 2 ^ n := hcard (P k) (hF.toIsFrame.memP k)
    rw [h2] at h1
    exact (Nat.pow_right_injective (by norm_num) h1).symm
  have hn : 2 ≤ n := hn'n ▸ hn'
  rw [hn'n] at e
  obtain ⟨e'⟩ := CFSG.RankTwoShapes.nonempty_statedProj_statedSU_equiv_PSU3Model F n hn hFn
  let ρ : SU (unitaryInvolution F 2 n) 3 →* residueQuotient Δ P Q k :=
    e.symm.toMonoidHom.comp (e'.toMonoidHom.comp (SUOdd.toPSU (p := 2) (f := n) hFn 3))
  have hker : ρ.ker = (SUOdd.toPSU (p := 2) (f := n) hFn 3).ker := by
    rw [show ρ = e.symm.toMonoidHom.comp (e'.toMonoidHom.comp
      (SUOdd.toPSU (p := 2) (f := n) hFn 3)) from rfl,
      MonoidHom.ker_comp_of_injective _ _ e.symm.injective,
      MonoidHom.ker_comp_of_injective _ _ e'.injective]
  have hsurj : Function.Surjective ρ :=
    e.symm.surjective.comp (e'.surjective.comp
      (SUOdd.toPSU_surjective (p := 2) (f := n) hFn 3))
  have hρker : ρ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 n) 3) :=
    hker.trans_le (SUOdd.toPSU_ker_le_center (p := 2) (f := n) hFn 3)
  have hρodd : Odd (Nat.card ρ.ker) := by
    rw [hker]
    exact odd_card_ker_toPSU hFn hn
  have hXp : commutator ↥(residueGroup Δ P Q k) = ⊤ :=
    commutator_residueGroup_eq_top h.cls hML hq hF
  obtain ⟨α, hαsurj, hαker, hαπ⟩ :=
    UC22.uc22pwlie_exists_cover_of_closed_fin
      (S := SU (unitaryInvolution F 2 n) 3) (X := ↥(residueGroup Δ P Q k))
      (Q := residueQuotient Δ P Q k)
      (fun E _ _ π hπ hc => su3_exists_section hFn hn E π hπ hc)
      hXp (QuotientGroup.mk' (Subgroup.center ↥(residueGroup Δ P Q k)))
      (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']) ρ hsurj hρker
  have hcomp_ker :
      ((QuotientGroup.mk' (Subgroup.center ↥(residueGroup Δ P Q k))).comp α).ker = ρ.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, hαπ x]
  refine ⟨α, hαsurj, hαker, ?_, ?_, ?_⟩
  · have hle : α.ker ≤ ρ.ker := by
      intro x hx
      rw [MonoidHom.mem_ker] at hx ⊢
      have h := hαπ x
      rw [hx, map_one] at h
      exact h.symm
    exact Odd.of_dvd_nat hρodd (Subgroup.card_dvd_of_le hle)
  · rw [hcomp_ker]
    exact hρker
  · rw [hcomp_ker]
    exact hρodd

end CFSG.Timmesfeld.Transvection
