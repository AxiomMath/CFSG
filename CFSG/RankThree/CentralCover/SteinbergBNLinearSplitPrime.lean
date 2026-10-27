module

public import CFSG.RankThree.CentralCover.SteinbergBNLinearTorus
public import CFSG.RankThree.CentralCover.SteinbergBNCoverPairingCore

public section

namespace CFSG.RankThree.CentralCover

open Matrix CFSG.Assembly CFSG.Assembly.RankThreeEven
open scoped MatrixGroups

theorem linear_split_prime_central_cover_two_local_rank {G : Type*} [Group G] [Finite G]
    (K : Subgroup G) {k : Type} [Field k] [Fintype k] {ℓ : ℕ} (hℓ : ℓ.Prime) [CharP k ℓ]
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpq : p ∣ Fintype.card k - 1) {n : ℕ} (hn : 3 ≤ n)
    (φ : K →* PSL(n, k)) (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center K) :
    ∃ u : G, u ∈ K ∧ orderOf u = 2 ∧ ∃ V : Subgroup G, V ≤ K ⊓ Subgroup.centralizer {u} ∧
      IsElemAbelian p V ∧
      Nat.card V = p ^ (if ℓ = 2 then n - 2 - (if p ∣ n then 1 else 0) else
        n - 1 - (if p ∣ n then 1 else 0)) ∧
      (if ℓ = 2 then n - 2 - (if p ∣ n then 1 else 0) else n - 1 - (if p ∣ n then 1 else 0)) ≤
        localRank p G := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hp2 : p ≠ 2 := by omega
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm1 : 1 ≤ m := by omega
  have hm2 : 2 ≤ m := by omega
  have hcard : p ∣ Nat.card kˣ := by
    rw [Nat.card_units, Nat.card_eq_fintype_card]
    exact hpq
  obtain ⟨ζ, hζo⟩ := exists_prime_orderOf_dvd_card' p hcard
  have hζ : ζ ^ p = 1 := by rw [← hζo, pow_orderOf_eq_one]
  obtain ⟨hDp, hF, hDcard⟩ := torusPSL_package (Y := K) hp hp2 hζo hζ hm1 hφ hker
  set i₀ : Fin (m + 1) := ⟨0, by omega⟩
  set i₁ : Fin (m + 1) := ⟨1, by omega⟩
  have h01 : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
  by_cases hℓ2 : ℓ = 2
  ·
    subst hℓ2
    simp only [↓reduceIte]
    set V' := (coordDiffHom (p := p) (⟨0, by omega⟩ : Fin m) ⟨1, by omega⟩).ker
    have hV'card := card_map_ker_coordDiffHom (k := k) hp hζo hζ hm2
    set z₀ := rootElem (k := k) h01 1
    set z : PSL(m + 1, k) := QuotientGroup.mk' _ z₀
    have htwo : (2 : k) = 0 := by
      have := CharP.cast_eq_zero k 2
      exact_mod_cast this
    have hz : orderOf z = 2 := by
      refine orderOf_eq_prime ?_ ?_
      · rw [← map_pow, pow_two, ← rootElem_add, one_add_one_eq_two, htwo, rootElem_zero,
          map_one]
      · intro h
        exact rootElem_not_mem_center h01 one_ne_zero ((QuotientGroup.eq_one_iff _).1 h)
    have hzD : ∀ x ∈ V'.map (torusPSL ζ hζ m), Commute z x := by
      rintro _ ⟨a, ha, rfl⟩
      have ha' : Multiplicative.toAdd a ⟨0, by omega⟩ = Multiplicative.toAdd a ⟨1, by omega⟩ :=
        sub_eq_zero.1 (congrArg Multiplicative.toAdd ha)
      have hc : torusSL ζ hζ m a * z₀ * (torusSL ζ hζ m a)⁻¹ = z₀ := by
        rw [diag_conj_rootElem h01 (torusEntries ζ hζ (Multiplicative.toAdd a)) 1 _ rfl]
        congr 1
        simp only [torusEntries, mul_one]
        have : torusExp (Multiplicative.toAdd a) i₀ = torusExp (Multiplicative.toAdd a) i₁ := by
          have e0 := torusExp_castSucc (Multiplicative.toAdd a) ⟨0, by omega⟩
          have e1 := torusExp_castSucc (Multiplicative.toAdd a) ⟨1, by omega⟩
          simp only [Fin.castSucc_mk] at e0 e1
          rw [e0, e1, ha']
        rw [this, mul_inv_cancel₀ (Units.ne_zero _)]
      have hc' : Commute (torusSL ζ hζ m a) z₀ := mul_inv_eq_iff_eq_mul.1 hc
      exact (hc'.map (QuotientGroup.mk' _)).symm
    obtain ⟨u, huK, hu, A, hA, hAab, hAcard, -, -, hrank⟩ :=
      central_cover_involution_witness K hφ hker hp hp2
        (fun x hx => hDp x (Subgroup.map_le_range _ _ hx))
        (fun x hx y hy => hF x (Subgroup.comap_mono (Subgroup.map_le_range _ _) hx) y
          (Subgroup.comap_mono (Subgroup.map_le_range _ _) hy)) hV'card hz hzD
    refine ⟨u, huK, hu, A, hA, hAab, ?_, ?_⟩
    · rw [hAcard]
      congr 1
    · convert hrank using 1
      omega
  ·
    simp only [hℓ2, ↓reduceIte]
    have hk2 : ringChar k ≠ 2 := by
      rw [ringChar.eq k ℓ]
      exact hℓ2
    set i₂ : Fin (m + 1) := ⟨2, by omega⟩
    set z₀ := negPairElem (k := k) h01
    set z : PSL(m + 1, k) := QuotientGroup.mk' _ z₀
    have hz : orderOf z = 2 := by
      refine orderOf_eq_prime ?_ ?_
      · rw [← map_pow, negPairElem_sq, map_one]
      · intro h
        exact negPairElem_not_mem_center hk2 h01 (i'' := i₂) (by simp [i₀, i₂, Fin.ext_iff])
          (by simp [i₁, i₂, Fin.ext_iff]) ((QuotientGroup.eq_one_iff _).1 h)
    have hzD : ∀ x ∈ (torusPSL ζ hζ m).range, Commute z x := by
      rintro _ ⟨a, rfl⟩
      have hc : Commute z₀ (torusSL ζ hζ m a) :=
        commute_of_coe_diagonal (coe_negPairElem h01) (coe_torusElem ζ hζ _)
      exact hc.map (QuotientGroup.mk' _)
    obtain ⟨u, huK, hu, A, hA, hAab, hAcard, -, -, hrank⟩ :=
      central_cover_involution_witness K hφ hker hp hp2 hDp hF hDcard hz hzD
    refine ⟨u, huK, hu, A, hA, hAab, ?_, ?_⟩
    · rw [hAcard]
      congr 1
    · convert hrank using 1
      omega

end CFSG.RankThree.CentralCover
