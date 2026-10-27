module

public import CFSG.LocalAnalysis.UniquenessCase.GL3Excl.GL3ExclBasic
import CFSG.RankThree.PartOne.N1322.CaseA5
import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.AutFactsA6Perm
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSixCount
import CFSG.CGT.Timmesfeld75.A6Basic
public import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms

public section

namespace CFSG.LocalAnalysis.UniquenessCase.GL3Excl

open Matrix CFSG.RepresentationTheory

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem neg_one_ne_one_zmod {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2) : (-1 : ZMod r) ≠ 1 :=
  haveI : Fact (2 < r) := ⟨lt_of_le_of_ne (Fact.out : r.Prime).two_le (Ne.symm hr2)⟩
  ZMod.neg_one_ne_one

private theorem commute_of_diagonal {r : ℕ} {g h : GL (Fin 3) (ZMod r)} {d d' : Fin 3 → ZMod r}
    (hg : (g : Matrix (Fin 3) (Fin 3) (ZMod r)) = diagonal d)
    (hh : (h : Matrix (Fin 3) (Fin 3) (ZMod r)) = diagonal d') : g * h = h * g := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hg, hh, diagonal_mul_diagonal, diagonal_mul_diagonal]
  simp only [mul_comm]

private theorem eq_of_diagonal_of_centralizes {r : ℕ} [Fact r.Prime]
    {K : Subgroup (GL (Fin 3) (ZMod r))} (hK : IsIrreducibleMatrixRep K.subtype)
    {g : GL (Fin 3) (ZMod r)} {d : Fin 3 → ZMod r}
    (hg : (g : Matrix (Fin 3) (Fin 3) (ZMod r)) = diagonal d) (hc : ∀ x ∈ K, g * x = x * g)
    (i j : Fin 3) : d i = d j :=
  diagonal_apply_eq_of_commute_irreducible hK (fun k hk => by
    have h := congrArg (fun x : GL (Fin 3) (ZMod r) => (x : Matrix (Fin 3) (Fin 3) (ZMod r)))
      (hc k hk)
    simp only [Units.val_mul, hg] at h
    exact h.symm) i j

private theorem pow_eq_one_of_diagonal {r n : ℕ} {y : GL (Fin 3) (ZMod r)} {α : Fin 3 → ZMod r}
    (hyd : (y : Matrix (Fin 3) (Fin 3) (ZMod r)) = diagonal α) (hy : y ^ n = 1) (i : Fin 3) :
    α i ^ n = 1 := by
  have h := congrArg (fun x : GL (Fin 3) (ZMod r) => (x : Matrix (Fin 3) (Fin 3) (ZMod r)) i i) hy
  simpa [Units.val_pow_eq_pow_val, hyd, diagonal_pow] using h

private theorem sq_eq_one_of_diagonal {r : ℕ} {g : GL (Fin 3) (ZMod r)} {d : Fin 3 → ZMod r}
    (hg : (g : Matrix (Fin 3) (Fin 3) (ZMod r)) = diagonal d) (hd : ∀ i, d i ^ 2 = 1) :
    g ^ 2 = 1 := by
  apply Units.ext
  have h : d ^ 2 = fun _ => 1 := funext hd
  rw [Units.val_pow_eq_pow_val, hg, diagonal_pow, h, diagonal_one, Units.val_one]

theorem false_of_alternating_five {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2)
    {W K : Subgroup (GL (Fin 3) (ZMod r))} (hKW : K ≤ W) (hK : IsIrreducibleMatrixRep K.subtype)
    (e : Nonempty (K ≃* alternatingGroup (Fin 5)))
    (hprod : ∀ g ∈ W, ∃ h ∈ K, ∃ z ∈ W, (∀ x ∈ W, z * x = x * z) ∧ g = h * z)
    {t₁ y : GL (Fin 3) (ZMod r)} (ht₁ : t₁ ∈ W)
    (ht₁d : (t₁ : Matrix (Fin 3) (Fin 3) (ZMod r)) = diagonal ![-1, 1, 1]) (hy : y ∈ W)
    (hy5 : y ^ 5 = 1) {α : Fin 3 → ZMod r}
    (hyd : (y : Matrix (Fin 3) (Fin 3) (ZMod r)) = diagonal α) (hyns : ∃ i j, α i ≠ α j) :
    False := by
  obtain ⟨e⟩ := e
  have hneg := neg_one_ne_one_zmod hr2
  have hα5 := pow_eq_one_of_diagonal hyd hy5
  set β : Fin 3 → ZMod r := fun i => ![-1, 1, 1] i * α i with hβ
  have hgd : ((t₁ * y : GL (Fin 3) (ZMod r)) : Matrix (Fin 3) (Fin 3) (ZMod r)) = diagonal β := by
    rw [Units.val_mul, ht₁d, hyd, diagonal_mul_diagonal]
  obtain ⟨h, hh, z, -, hzc, hg⟩ := hprod (t₁ * y) (W.mul_mem ht₁ hy)
  have key : ∀ n : ℕ, h ^ n = 1 → ∀ i j, β i ^ n = β j ^ n := by
    intro n hn i j
    have hgn : (t₁ * y) ^ n = z ^ n := by
      rw [hg, (show Commute h z from (hzc h (hKW hh)).symm).mul_pow, hn, one_mul]
    refine diagonal_apply_eq_of_commute_irreducible hK (α := β ^ n) (fun k hk => ?_) i j
    have hc : z ^ n * k = k * z ^ n := (show Commute z k from hzc k (hKW hk)).pow_left n
    have hm := congrArg (fun x : GL (Fin 3) (ZMod r) => (x : Matrix (Fin 3) (Fin 3) (ZMod r))) hc
    simp only [Units.val_mul] at hm
    rw [← hgn, Units.val_pow_eq_pow_val, hgd, diagonal_pow] at hm
    exact hm.symm
  have hpow : ∀ n : ℕ, e ⟨h, hh⟩ ^ n = 1 → h ^ n = 1 := fun n hn => by
    have h1 : (⟨h, hh⟩ : K) ^ n = 1 := e.injective (by rw [map_pow, hn, map_one])
    simpa using congrArg Subtype.val h1
  have hβ0 : β 0 = -α 0 := by simp [hβ]
  have hβ1 : β 1 = α 1 := by simp [hβ]
  rcases CFSG.RankThree.PartOne.N1322.A5_pow (e ⟨h, hh⟩) with h5 | h5 | h5
  · obtain ⟨i, j, hij⟩ := hyns
    have hsq : ∀ k, β k ^ 2 = α k ^ 2 := by
      intro k
      simp only [hβ, mul_pow]
      fin_cases k <;> simp
    have h6 : ∀ k, α k = (α k ^ 2) ^ 3 := fun k => by
      rw [← pow_mul]
      calc α k = α k ^ 5 * α k := by rw [hα5 k, one_mul]
        _ = α k ^ (2 * 3) := by ring
    exact hij (by rw [h6 i, h6 j, ← hsq i, ← hsq j, key 2 (hpow 2 h5) i j])
  · have h' := congrArg (· ^ 5) (key 3 (hpow 3 h5) 0 1)
    simp only [hβ0, hβ1] at h'
    have e1 : ((-α 0) ^ 3) ^ 5 = -(α 0 ^ 5) ^ 3 := by ring
    have e2 : (α 1 ^ 3) ^ 5 = (α 1 ^ 5) ^ 3 := by ring
    rw [e1, e2, hα5, hα5] at h'
    exact hneg (by simpa using h')
  · have h' := key 5 (hpow 5 h5) 0 1
    have e3 : (-α 0) ^ 5 = -(α 0 ^ 5) := by ring
    rw [hβ0, hβ1, e3, hα5, hα5] at h'
    exact hneg h'

private theorem perm_six_false {σ τ : Equiv.Perm (Fin 6)} (hσ : σ ^ 2 = 1) (hσ1 : σ ≠ 1)
    (hτ : τ ^ 5 = 1) (hτ1 : τ ≠ 1) (hστ : σ * τ = τ * σ) : False := by
  have hc : Commute σ τ := hστ
  have h10 : (σ * τ) ^ 10 = 1 := by
    rw [hc.mul_pow, show σ ^ 10 = (σ ^ 2) ^ 5 by rw [← pow_mul],
      show τ ^ 10 = (τ ^ 5) ^ 2 by rw [← pow_mul], hσ, hτ, one_pow, one_pow, one_mul]
  rcases CFSG.CGT.Timmesfeld75.perm_six_no_order_ten (σ * τ) h10 with h | h
  · rw [hc.mul_pow, hσ, one_mul] at h
    exact hτ1 (calc τ = τ ^ 5 * (τ ^ 2)⁻¹ * (τ ^ 2)⁻¹ := by group
      _ = 1 := by rw [hτ, h]; group)
  · rw [hc.mul_pow, hτ, mul_one] at h
    exact hσ1 (calc σ = σ ^ 5 * (σ ^ 2)⁻¹ * (σ ^ 2)⁻¹ := by group
      _ = 1 := by rw [h, hσ]; group)

theorem false_of_mulAut_alternating_six {a a' v : MulAut (alternatingGroup (Fin 6))}
    (ha : a ^ 2 = 1) (ha1 : a ≠ 1) (ha' : a' ^ 2 = 1) (ha'1 : a' ≠ 1) (haa' : a * a' = a' * a)
    (haa'1 : a * a' ≠ 1) (hv : v ^ 5 = 1) (hv1 : v ≠ 1) (hav : a * v = v * a)
    (ha'v : a' * v = v * a') : False := by
  have : Finite (MulAut (alternatingGroup (Fin 6))) :=
    Finite.of_injective (fun f : MulAut (alternatingGroup (Fin 6)) =>
      (f : alternatingGroup (Fin 6) → alternatingGroup (Fin 6))) DFunLike.coe_injective
  set S := CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.permAut with hS
  have hS720 : Nat.card S = 720 := by
    rw [← Nat.card_congr
      CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.permAutEquiv.toEquiv, Nat.card_perm,
      Nat.card_fin]
    decide
  have hidx := S.index_mul_card
  have hle : Nat.card (MulAut (alternatingGroup (Fin 6))) ≤ 1440 :=
    CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix.automorphism_card_le
  have hpos : 0 < Nat.card (MulAut (alternatingGroup (Fin 6))) := Nat.card_pos
  rw [hS720] at hidx
  have hS : ∀ s ∈ S, s ^ 2 = 1 → s ≠ 1 → s * v = v * s → v ∈ S → False := by
    rintro _ ⟨σ, rfl⟩ hs hs1 hsv ⟨τ, rfl⟩
    have hinj := CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.conjNormal_injective_alt6
    refine perm_six_false (σ := σ) (τ := τ) (hinj (by rw [map_pow, hs, map_one])) (fun h => ?_)
      (hinj (by rw [map_pow, hv, map_one])) (fun h => hv1 (by rw [h, map_one]))
      (hinj (by rw [map_mul, map_mul, hsv]))
    exact hs1 (by rw [h, map_one])
  rcases (show S.index = 1 ∨ S.index = 2 by
    rcases Nat.lt_or_ge S.index 3 with h | h
    · interval_cases h' : S.index <;> simp_all
    · omega) with h1 | h2
  · rw [Subgroup.index_eq_one] at h1
    exact hS a (h1 ▸ Subgroup.mem_top a) ha ha1 hav (h1 ▸ Subgroup.mem_top v)
  · have hvS : v ∈ S := by
      have h4 : v ^ 4 ∈ S := by
        rw [show v ^ 4 = (v ^ 2) ^ 2 by rw [← pow_mul]]
        exact Subgroup.sq_mem_of_index_two h2 _
      have h5 : v ^ 4 * v ∈ S := by rw [← pow_succ, hv]; exact S.one_mem
      exact (Subgroup.mul_mem_iff_of_index_two h2).mp h5 |>.mp h4
    by_cases haS : a ∈ S
    · exact hS a haS ha ha1 hav hvS
    by_cases ha'S : a' ∈ S
    · exact hS a' ha'S ha' ha'1 ha'v hvS
    exact hS _ ((Subgroup.mul_mem_iff_of_index_two h2).mpr (iff_of_false haS ha'S))
      (by rw [(show Commute a a' from haa').mul_pow, ha, ha', one_mul]) haa'1
      (by rw [mul_assoc, ha'v, ← mul_assoc, hav, mul_assoc]) hvS

private theorem exists_hom_mulAut_of_perfect {G Q : Type*} [Group G] [Group Q] {K W : Subgroup G}
    [Group.IsPerfect K] (hWN : W ≤ Subgroup.normalizer (K : Set G))
    (e : (K ⧸ Subgroup.center K) ≃* Q) :
    ∃ θ : W →* MulAut Q, ∀ g : W, θ g = 1 → ∀ x ∈ K, (g : G) * x = x * g := by
  refine ⟨(MulAut.congr e).toMonoidHom.comp
    ((CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom K).comp
      (K.normalizerMonoidHom.comp (Subgroup.inclusion hWN))), fun g hg x hx => ?_⟩
  have h1 : Subgroup.inclusion hWN g ∈ K.normalizerMonoidHom.ker := by
    rw [MonoidHom.mem_ker]
    apply CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective K
    apply (MulAut.congr e).injective
    rw [map_one, map_one]
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] using hg
  rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf,
    Subgroup.mem_centralizer_iff] at h1
  exact (h1 x hx).symm

theorem false_of_three_alt_six {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2)
    {W K : Subgroup (GL (Fin 3) (ZMod r))} (hnorm : ∀ g ∈ W, ∀ x ∈ K, g * x * g⁻¹ ∈ K)
    (hK : IsIrreducibleMatrixRep K.subtype) (hperf : Group.IsPerfect K)
    (e : Nonempty ((K ⧸ Subgroup.center K) ≃* alternatingGroup (Fin 6)))
    {t₁ t₂ y : GL (Fin 3) (ZMod r)} (ht₁ : t₁ ∈ W)
    (ht₁d : (t₁ : Matrix (Fin 3) (Fin 3) (ZMod r)) = diagonal ![-1, 1, 1]) (ht₂ : t₂ ∈ W)
    (ht₂d : (t₂ : Matrix (Fin 3) (Fin 3) (ZMod r)) = diagonal ![1, -1, 1]) (hy : y ∈ W)
    (hy5 : y ^ 5 = 1) {α : Fin 3 → ZMod r}
    (hyd : (y : Matrix (Fin 3) (Fin 3) (ZMod r)) = diagonal α) (hyns : ∃ i j, α i ≠ α j) :
    False := by
  obtain ⟨e⟩ := e
  have hneg := neg_one_ne_one_zmod hr2
  have hWN : W ≤ Subgroup.normalizer (K : Set (GL (Fin 3) (ZMod r))) := fun g hg =>
    Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => hnorm g hg x hx, fun hx => by
      have h := hnorm g⁻¹ (W.inv_mem hg) _ hx
      rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at h⟩
  obtain ⟨θ, hθ⟩ := exists_hom_mulAut_of_perfect hWN e
  have hpow : ∀ (g : GL (Fin 3) (ZMod r)) (hg : g ∈ W) (n : ℕ), g ^ n = 1 →
      θ ⟨g, hg⟩ ^ n = 1 := fun g hg n hn => by
    have h1 : (⟨g, hg⟩ : W) ^ n = 1 := Subtype.ext (by simpa using hn)
    rw [← map_pow θ, h1, map_one]
  have hne : ∀ (g : GL (Fin 3) (ZMod r)) (hg : g ∈ W) (d : Fin 3 → ZMod r),
      (g : Matrix (Fin 3) (Fin 3) (ZMod r)) = diagonal d → ∀ i j, d i ≠ d j →
      θ ⟨g, hg⟩ ≠ 1 := fun g hg d hgd i j hij h =>
    hij (eq_of_diagonal_of_centralizes hK hgd (hθ ⟨g, hg⟩ h) i j)
  have hcomm : ∀ (g h : GL (Fin 3) (ZMod r)) (hg : g ∈ W) (hh : h ∈ W), g * h = h * g →
      θ ⟨g, hg⟩ * θ ⟨h, hh⟩ = θ ⟨h, hh⟩ * θ ⟨g, hg⟩ := fun g h hg hh hgh => by
    rw [← map_mul θ, ← map_mul θ]
    congr 1
    exact Subtype.ext hgh
  have hd₁₂ : ((t₁ * t₂ : GL (Fin 3) (ZMod r)) : Matrix (Fin 3) (Fin 3) (ZMod r)) =
      diagonal ![-1, -1, 1] := by
    rw [Units.val_mul, ht₁d, ht₂d, diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> simp
  have hmul : θ ⟨t₁, ht₁⟩ * θ ⟨t₂, ht₂⟩ = θ ⟨t₁ * t₂, W.mul_mem ht₁ ht₂⟩ := by
    rw [← map_mul θ]
    rfl
  obtain ⟨i, j, hij⟩ := hyns
  exact false_of_mulAut_alternating_six
    (hpow t₁ ht₁ 2 (sq_eq_one_of_diagonal ht₁d (by intro i; fin_cases i <;> simp)))
    (hne t₁ ht₁ _ ht₁d 0 1 (by simp [hneg]))
    (hpow t₂ ht₂ 2 (sq_eq_one_of_diagonal ht₂d (by intro i; fin_cases i <;> simp)))
    (hne t₂ ht₂ _ ht₂d 1 0 (by simp [hneg]))
    (hcomm t₁ t₂ ht₁ ht₂ (commute_of_diagonal ht₁d ht₂d))
    (hmul ▸ hne _ (W.mul_mem ht₁ ht₂) _ hd₁₂ 0 2 (by simp [hneg]))
    (hpow y hy 5 hy5) (hne y hy α hyd i j hij)
    (hcomm t₁ y ht₁ hy (commute_of_diagonal ht₁d hyd))
    (hcomm t₂ y ht₂ hy (commute_of_diagonal ht₂d hyd))

end CFSG.LocalAnalysis.UniquenessCase.GL3Excl
