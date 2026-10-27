module

public import CFSG.SignalizerFunctorTheorem.NonLocal.Orbit4
public import CFSG.SignalizerFunctorTheorem.NonLocal.GLOrder
public import CFSG.RankThree.PartOne.KC.SymplecticSubfieldFixed

public section

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.RankThree.PartOne.KCSpComm
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  (subfieldSpHom subfieldSpHom_injective)
open scoped IsMulCommutative

namespace CFSG.SignalizerFunctorTheorem.NonLocal

theorem four_le_of_frobenius_pair {X : Type*} [Group X] (C : Subgroup X) [Finite C]
    (V : Subgroup X) [Finite V] [IsMulCommutative V] {s m : ℕ} (hs : s.Prime) (hs5 : s ≠ 5)
    (hexp : ∀ v ∈ V, v ^ s = 1) (hcard : Nat.card V = s ^ m)
    (hnorm : ∀ c ∈ C, ∀ v ∈ V, c * v * c⁻¹ ∈ V)
    (hfaith : ∀ c ∈ C, (∀ v ∈ V, c * v * c⁻¹ = v) → c = 1)
    (c g : C) (hc1 : c ≠ 1) (hc5 : c ^ 5 = 1) (hg : g * c * g⁻¹ = c ^ 2) : 4 ≤ m := by
  classical
  have : Fact s.Prime := ⟨hs⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hchar : CharP (AlgebraicClosure (ZMod s)) s :=
    charP_of_injective_algebraMap (algebraMap (ZMod s) (AlgebraicClosure (ZMod s))).injective s
  obtain ⟨m', ρ, hcard', hρ1⟩ := exists_rep_of_elementary_abelian C.subtype V hs hexp
    (fun c v hv => hnorm c c.2 v hv) (AlgebraicClosure (ZMod s))
  have hmm : m' = m := by
    have h : s ^ m' = s ^ m := by rw [← hcard', hcard]
    exact Nat.pow_right_injective hs.two_le h
  have hord : orderOf c = 5 := orderOf_eq_prime hc5 hc1
  have hEcard : Nat.card (Subgroup.zpowers c) = 5 := by
    rw [Nat.card_zpowers, hord]
  have hinv : ((Nat.card (Subgroup.zpowers c) : ℕ) : AlgebraicClosure (ZMod s)) ≠ 0 := by
    intro h
    have h1 : s ∣ Nat.card (Subgroup.zpowers c) :=
      (CharP.cast_eq_zero_iff (AlgebraicClosure (ZMod s)) s _).mp h
    rw [hEcard] at h1
    exact hs5 ((Nat.prime_dvd_prime_iff_eq hs (by norm_num)).mp h1)
  have hinj : ∀ e ∈ Subgroup.zpowers c, ρ e = 1 → e = 1 :=
    fun e _ he => Subtype.ext (hfaith e e.2 (hρ1 e he))
  have hodd : ∀ e ∈ Subgroup.zpowers c, e * e = 1 → e = 1 := by
    intro e he hee
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
    have h1 : (orderOf c : ℤ) ∣ n + n :=
      orderOf_dvd_iff_zpow_eq_one.mpr (by rw [zpow_add]; exact hee)
    have h2 : (orderOf c : ℤ) ∣ n := by
      rw [hord] at h1 ⊢
      omega
    exact orderOf_dvd_iff_zpow_eq_one.mp h2
  have hconj : ∀ n : ℤ, g * c ^ n * g⁻¹ = c ^ (2 * n) := by
    intro n
    rw [← conj_zpow, hg, ← zpow_natCast, ← zpow_mul]
    norm_num
  have hgE : ∀ e ∈ Subgroup.zpowers c, g * e * g⁻¹ ∈ Subgroup.zpowers c := by
    intro e he
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
    rw [hconj]
    exact Subgroup.zpow_mem_zpowers c _
  have hg2 : ∀ e ∈ Subgroup.zpowers c, g * g * e * (g * g)⁻¹ = e⁻¹ := by
    intro e he
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
    have h1 : g * g * c ^ n * (g * g)⁻¹ = g * (g * c ^ n * g⁻¹) * g⁻¹ := by group
    have h5 : c ^ ((5 : ℤ) * n) = 1 := by
      rw [zpow_mul]
      simp [hc5]
    rw [h1, hconj, hconj]
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← zpow_add]
    have h6 : 2 * (2 * n) + n = 5 * n := by ring
    rw [h6]
    exact h5
  have h4 := four_le_finrank_of_inverting ρ (Subgroup.zpowers c) inferInstance hinv hinj hodd
    (fun h => hc1 (Subgroup.zpowers_eq_bot.mp h)) g hgE hg2
  rw [Module.finrank_fin_fun] at h4
  omega

private def spFiveElt : GL (Fin 2 ⊕ Fin 2) (ZMod 3) :=
  ⟨Matrix.fromBlocks !![0, 0; 1, 0] !![0, 1; 0, 0] !![2, 2; 2, 0] !![0, 0; 1, 2],
   Matrix.fromBlocks !![0, 1; 0, 2] !![0, 0; 2, 0] !![1, 1; 1, 0] !![0, 1; 0, 0],
   by decide, by decide⟩

private def spFourElt : GL (Fin 2 ⊕ Fin 2) (ZMod 3) :=
  ⟨Matrix.fromBlocks !![1, 0; 1, 2] !![1, 1; 0, 1] !![0, 2; 1, 0] !![0, 1; 1, 0],
   Matrix.fromBlocks !![0, 1; 1, 0] !![2, 0; 2, 2] !![0, 2; 1, 0] !![1, 1; 0, 2],
   by decide, by decide⟩

private theorem spFiveElt_mem : spFiveElt ∈ StatedSp 2 (ZMod 3) := by
  rw [SymplecticTorusWeyl.mem_statedSp_iff]
  decide

private theorem spFourElt_mem : spFourElt ∈ StatedSp 2 (ZMod 3) := by
  rw [SymplecticTorusWeyl.mem_statedSp_iff]
  decide

private theorem exists_frobenius_pair_zmod3 :
    ∃ c g : StatedSp 2 (ZMod 3), c ≠ 1 ∧ c ^ 5 = 1 ∧ g * c * g⁻¹ = c ^ 2 := by
  refine ⟨⟨spFiveElt, spFiveElt_mem⟩, ⟨spFourElt, spFourElt_mem⟩, ?_, ?_, ?_⟩
  · intro h
    have h1 := congrArg (fun x : StatedSp 2 (ZMod 3) =>
      ((x : GL (Fin 2 ⊕ Fin 2) (ZMod 3)) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3))) h
    revert h1
    decide
  · refine SymplecticTorusWeyl.statedSp_ext ?_
    decide
  · refine SymplecticTorusWeyl.statedSp_ext ?_
    decide

private def spMap {F L : Type} [Field F] [Field L] (ι : F →+* L) (r : ℕ) :
    StatedSp r F →* StatedSp r L :=
  ((Matrix.GeneralLinearGroup.map ι).comp (StatedSp r F).subtype).codRestrict (StatedSp r L)
    fun g => UnitaryHigher.map_mem_statedSp ι g.2

private theorem spMap_injective {F L : Type} [Field F] [Field L] (ι : F →+* L) (r : ℕ) :
    Function.Injective (spMap ι r) := by
  intro g h hgh
  have h1 : ((g : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F).map ι =
      ((h : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F).map ι :=
    congrArg (fun x : StatedSp r L =>
      ((x : GL (Fin r ⊕ Fin r) L) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) L)) hgh
  exact Subtype.ext (Units.ext (Matrix.map_injective ι.injective h1))

theorem exists_frobenius_pair_subfield {k : Type} [Field k] (hk : Nat.card k = 3) :
    ∃ c g : StatedSp 2 k, c ≠ 1 ∧ c ^ 5 = 1 ∧ g * c * g⁻¹ = c ^ 2 := by
  have hfin : Finite k := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype k := Fintype.ofFinite k
  have hk' : Fintype.card k = 3 := by rw [← Nat.card_eq_fintype_card]; exact hk
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hchar : CharP k 3 := charP_of_card_eq_prime hk'
  obtain ⟨c₀, g₀, hc1, hc5, hg⟩ := exists_frobenius_pair_zmod3
  refine ⟨spMap (ZMod.castHom (dvd_refl 3) k) 2 c₀, spMap (ZMod.castHom (dvd_refl 3) k) 2 g₀,
    ?_, ?_, ?_⟩
  · intro h
    exact hc1 (spMap_injective (ZMod.castHom (dvd_refl 3) k) 2 (by rw [h, map_one]))
  · rw [← map_pow, hc5, map_one]
  · rw [← map_inv, ← map_mul, ← map_mul, hg, map_pow]

theorem proj_subfieldSpHom_eq_one_iff {r : ℕ} [NeZero r] {K : Type} [Field K] (k : Subfield K)
    (g : StatedSp r k) : proj r K (subfieldSpHom r k g) = 1 ↔ g ∈ spScalars r k := by
  constructor
  · intro h
    have hz : subfieldSpHom r k g ∈ spScalars r K := by
      rw [← ker_proj, MonoidHom.mem_ker]
      exact h
    obtain ⟨c, hc2, hc⟩ := exists_scalar_of_mem_spScalars hz
    have h1 : (c : K) * c = 1 := by
      have := congrArg Units.val hc2
      simpa [sq] using this
    have hck : (c : K) ∈ k := by
      rcases mul_self_eq_one_iff.mp h1 with h | h
      · rw [h]
        exact one_mem _
      · rw [h]
        exact neg_mem (one_mem _)
    let d : kˣ := Units.mk0 ⟨(c : K), hck⟩ (fun h0 => c.ne_zero (by
      simpa using congrArg Subtype.val h0))
    have hd2 : d ^ 2 = 1 := by
      refine Units.ext (Subtype.ext ?_)
      change (c : K) ^ 2 = 1
      rw [sq, h1]
    have hjd : subfieldSpHom r k (scalarSp d hd2) = subfieldSpHom r k g := by
      refine Subtype.ext ?_
      rw [hc]
      change Matrix.GeneralLinearGroup.map k.subtype
        (Matrix.GeneralLinearGroup.scalar (Fin r ⊕ Fin r) d) = _
      rw [Matrix.GeneralLinearGroup.map_scalar]
      congr 1
      exact Units.ext rfl
    have := subfieldSpHom_injective (r := r) k hjd
    rw [← this]
    exact scalarSp_mem d hd2
  · intro hg
    obtain ⟨d, hd2, hd⟩ := exists_scalar_of_mem_spScalars hg
    have hz : subfieldSpHom r k g ∈ spScalars r K := by
      refine ⟨Units.map k.subtype.toMonoidHom d, ?_⟩
      change Matrix.GeneralLinearGroup.scalar (Fin r ⊕ Fin r) _ =
        Matrix.GeneralLinearGroup.map k.subtype (g : GL (Fin r ⊕ Fin r) _)
      rw [hd, Matrix.GeneralLinearGroup.map_scalar]
      rfl
    rw [← MonoidHom.mem_ker, ker_proj]
    exact hz

theorem card_range_proj_subfield {K : Type} [Field K] [Finite K] (k : Subfield K)
    (hk : Nat.card k = 3) :
    Nat.card ((proj 2 K).comp (subfieldSpHom 2 k)).range = 25920 := by
  have hker : ((proj 2 K).comp (subfieldSpHom 2 k)).ker = spScalars 2 k := by
    ext g
    rw [MonoidHom.mem_ker]
    exact proj_subfieldSpHom_eq_one_iff k g
  have h1 := Subgroup.card_ker_mul_card_range ((proj 2 K).comp (subfieldSpHom 2 k))
  rw [hker, card_spScalars_eq_gcd k (by norm_num), SymplecticFlag.card_statedSp, hk] at h1
  have h2 : Nat.gcd 2 (3 - 1) = 2 := by norm_num
  have h3 : (3 : ℕ) ^ (2 ^ 2) * ∏ j ∈ Finset.Icc 1 2, (3 ^ (2 * j) - 1) = 51840 := by decide
  rw [h2, h3] at h1
  omega

theorem sp_two_three_closing {K : Type} [Field K] [Finite K] (k : Subfield K)
    (hk : Nat.card k = 3) {s m : ℕ} (hs : s.Prime) (hs3 : s ≠ 3)
    (V : Subgroup (StatedProj (StatedSp 2 K))) [Finite V] [IsMulCommutative V]
    (hVexp : ∀ v ∈ V, v ^ s = 1) (hcard : Nat.card V = s ^ m)
    (hVnorm : ∀ g : StatedSp 2 k, ∀ v ∈ V,
      proj 2 K (subfieldSpHom 2 k g) * v * (proj 2 K (subfieldSpHom 2 k g))⁻¹ ∈ V)
    (hfaith : ∀ g : StatedSp 2 k, (∀ v ∈ V, proj 2 K (subfieldSpHom 2 k g) * v *
      (proj 2 K (subfieldSpHom 2 k g))⁻¹ = v) → proj 2 K (subfieldSpHom 2 k g) = 1)
    (hm : 3 ≤ m) (hup : m ≤ 3 ∨ (s = 2 ∧ m ≤ 4)) : False := by
  classical
  have _ := hs3
  have : Finite (StatedProj (StatedSp 2 K)) :=
    Finite.of_surjective (proj 2 K) (proj_surjective (r := 2) (K := K))
  let φ : StatedSp 2 k →* StatedProj (StatedSp 2 K) := (proj 2 K).comp (subfieldSpHom 2 k)
  let C : Subgroup (StatedProj (StatedSp 2 K)) := φ.range
  have hCcard : Nat.card C = 25920 := card_range_proj_subfield k hk
  have hnorm : ∀ c ∈ C, ∀ v ∈ V, c * v * c⁻¹ ∈ V := by
    rintro _ ⟨g, rfl⟩ v hv
    exact hVnorm g v hv
  have hfaithC : ∀ c ∈ C, (∀ v ∈ V, c * v * c⁻¹ = v) → c = 1 := by
    rintro _ ⟨g, rfl⟩ h
    exact hfaith g h
  by_cases h2 : s = 2
  ·
    subst h2
    have hdvd := card_dvd_of_faithful C V hs hVexp hcard hnorm hfaithC
    rw [hCcard] at hdvd
    have hm4 : m ≤ 4 := by omega
    obtain rfl | rfl : m = 3 ∨ m = 4 := by omega
    · revert hdvd
      decide
    · revert hdvd
      decide
  · have hm3 : m = 3 := by
      rcases hup with h | ⟨h, -⟩
      · omega
      · exact absurd h h2
    subst hm3
    by_cases h5 : s = 5
    ·
      subst h5
      have hdvd := card_dvd_of_faithful C V hs hVexp hcard hnorm hfaithC
      rw [hCcard] at hdvd
      revert hdvd
      decide
    ·
      obtain ⟨c₀, g₀, hc1, hc5, hg⟩ := exists_frobenius_pair_subfield (k := k) hk
      have hc1' : c₀ ∉ spScalars 2 k := by
        intro hc
        have hsq := sq_eq_one_of_mem_spScalars hc
        apply hc1
        calc c₀ = c₀ ^ 5 * (c₀ ^ 2)⁻¹ * (c₀ ^ 2)⁻¹ := by group
          _ = 1 := by rw [hc5, hsq]; simp
      have hne : φ c₀ ≠ 1 := fun h => hc1' ((proj_subfieldSpHom_eq_one_iff k c₀).mp h)
      have := four_le_of_frobenius_pair C V hs h5 hVexp hcard hnorm hfaithC ⟨φ c₀, c₀, rfl⟩
        ⟨φ g₀, g₀, rfl⟩ (fun h => hne (congrArg Subtype.val h))
        (Subtype.ext (by
          show φ c₀ ^ 5 = 1
          rw [← map_pow, hc5, map_one]))
        (Subtype.ext (by
          show φ g₀ * φ c₀ * (φ g₀)⁻¹ = φ c₀ ^ 2
          rw [← map_inv, ← map_mul, ← map_mul, hg, map_pow]))
      omega

end CFSG.SignalizerFunctorTheorem.NonLocal
