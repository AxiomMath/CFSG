module

public import CFSG.RankThree.PartOne.KC.NilpotentChains
public import CFSG.RankThree.PartOne.KC.LinearSplitInner
public import CFSG.RankThree.SteinbergR3ELinearNonregularUnipotent

public section

namespace CFSG.RankThree.PartOne

open Matrix Subgroup CFSG CFSG.RankThree.LocalRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.RankThree.RegularUnipotent
open CFSG.RankThree.NonregularUnipotent CFSG.ComponentClassification

theorem exists_lift_pow_eq_one {G H : Type*} [Group G] [Finite G] [Group H] (ρ : G →* H) {p : ℕ}
    (hp : p.Prime) (hker : ¬ p ∣ Nat.card ρ.ker) {y : H} (hy : y ∈ ρ.range) (hyp : y ^ p = 1) :
    ∃ g : G, ρ g = y ∧ g ^ p = 1 := by
  obtain ⟨g₀, rfl⟩ := hy
  have hz : g₀ ^ p ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_pow, hyp]
  have hm : orderOf (g₀ ^ p) ∣ Nat.card ρ.ker := Subgroup.orderOf_dvd_natCard ρ.ker hz
  have hcop : Nat.Coprime (orderOf (g₀ ^ p)) p :=
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr fun h => hker (h.trans hm))
  obtain ⟨c, -, hc⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  set m := orderOf (g₀ ^ p) with hm'
  refine ⟨g₀ ^ (m * c), ?_, ?_⟩
  · have h1 : ρ g₀ ^ (m * c) = ρ g₀ := by
      conv_lhs => rw [← Nat.div_add_mod (m * c) p, hc, pow_add, pow_mul, hyp, one_pow, one_mul,
        pow_one]
    rw [map_pow, h1]
  · have h2 : (g₀ ^ p) ^ m = 1 := pow_orderOf_eq_one _
    calc (g₀ ^ (m * c)) ^ p = ((g₀ ^ p) ^ m) ^ c := by
          simp only [← pow_mul]
          congr 1
          ring
      _ = 1 := by rw [h2, one_pow]

theorem normalPrimeComplements_of_conj {T : Type*} [Group T] (p : ℕ) (ψ a : MulAut T)
    (h : ∀ B S : Subgroup (MulAut T), (MulAut.conj : T →* MulAut T).range ≤ B →
      S ≤ B ⊓ Subgroup.centralizer {ψ * a * ψ⁻¹} →
      (S.subgroupOf (B ⊓ Subgroup.centralizer {ψ * a * ψ⁻¹})).Normal → ¬ p ∣ Nat.card S →
      S = ⊥)
    (B S : Subgroup (MulAut T)) (hB : (MulAut.conj : T →* MulAut T).range ≤ B)
    (hSC : S ≤ B ⊓ Subgroup.centralizer {a})
    (hSn : (S.subgroupOf (B ⊓ Subgroup.centralizer {a})).Normal) (hSp : ¬ p ∣ Nat.card S) :
    S = ⊥ := by
  set φ : MulAut (MulAut T) := MulAut.conj ψ with hφ
  have hφapp : ∀ x, φ.toMonoidHom x = ψ * x * ψ⁻¹ := fun x => rfl
  set B' : Subgroup (MulAut T) := B.map φ.toMonoidHom with hB'
  have hB'conj : (MulAut.conj : T →* MulAut T).range ≤ B' := by
    rintro _ ⟨x, rfl⟩
    refine Subgroup.mem_map.mpr ⟨MulAut.conj (ψ⁻¹ x), hB ⟨ψ⁻¹ x, rfl⟩, ?_⟩
    rw [hφapp, ← CFSG.RankThree.GroupTheory.SteinbergBY.mulAut_conj_apply_eq]
    simp
  have hC : (B ⊓ Subgroup.centralizer {a}).map φ.toMonoidHom =
      B' ⊓ Subgroup.centralizer {ψ * a * ψ⁻¹} := by
    rw [Subgroup.map_inf _ _ _ φ.injective, map_centralizer_singleton_mulEquiv φ a]
    rfl
  have hSC' : S.map φ.toMonoidHom ≤ B' ⊓ Subgroup.centralizer {ψ * a * ψ⁻¹} := by
    rw [← hC]
    exact Subgroup.map_mono hSC
  have hSn' : ((S.map φ.toMonoidHom).subgroupOf
      (B' ⊓ Subgroup.centralizer {ψ * a * ψ⁻¹})).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hSC']
    intro s' c' hs' hc'
    rw [← hC] at hc'
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hs'
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hc'
    have := (Subgroup.normal_subgroupOf_iff hSC).mp hSn s c hs hc
    exact ⟨c * s * c⁻¹, this, by simp⟩
  have hSp' : ¬ p ∣ Nat.card (S.map φ.toMonoidHom) := by
    rwa [Subgroup.card_map_of_injective φ.injective]
  have h1 := h B' (S.map φ.toMonoidHom) hB'conj hSC' hSn' hSp'
  exact (Subgroup.map_eq_bot_iff_of_injective S φ.injective).mp h1

theorem inSubgroup_theta_normal_prime_complement {M : Type*} [Group M] [Finite M] {p : ℕ}
    (hp : p.Prime) (C : Subgroup M) :
    inSubgroup (aschbacherSolvableCore p) C ≤ C ∧
      ((inSubgroup (aschbacherSolvableCore p) C).subgroupOf C).Normal ∧
      ¬ p ∣ Nat.card (inSubgroup (aschbacherSolvableCore p) C) := by
  have hchar := solvable_prime_complement_core_characterization (H := C) hp
  refine ⟨Subgroup.map_subtype_le _, ?_, ?_⟩
  · rw [inSubgroup, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective C.subtype_injective]
    exact @Subgroup.normal_of_characteristic _ _ _ hchar.2.1
  · rw [inSubgroup, Subgroup.card_map_of_injective C.subtype_injective]
    exact hchar.2.2.1

theorem exists_isUnit_mul_eq_of_chain {n : ℕ} {k : Type*} [Field k]
    (M N : Matrix (Fin n) (Fin n) k) (c : Fin n → (Fin n → k)) (hli : LinearIndependent k c)
    (h : ∀ j, M.mulVec (c j) = ∑ l, N l j • c l) :
    ∃ A : Matrix (Fin n) (Fin n) k, IsUnit A ∧ M * A = A * N := by
  refine ⟨Matrix.of fun i j => c j i, ?_, ?_⟩
  · rw [← Matrix.linearIndependent_cols_iff_isUnit]
    exact hli
  · ext i j
    have := congrFun (h j) i
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    simp only [Matrix.mul_apply, Matrix.of_apply]
    rw [this]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _

theorem pow_dim_eq_zero_of_pow_eq_zero {n m : ℕ} {k : Type*} [Field k]
    {M : Matrix (Fin n) (Fin n) k} (hM : M ^ m = 0) : M ^ n = 0 := by
  have h1 : LinearMap.ker (Matrix.toLin' M ^ m) = ⊤ := by
    rw [← Matrix.toLin'_pow, hM, map_zero]
    exact LinearMap.ker_zero
  have h2 := Module.End.ker_pow_le_ker_pow_finrank (Matrix.toLin' M) m
  rw [h1, top_le_iff, Module.finrank_fin_fun] at h2
  have h3 : Matrix.toLin' M ^ n = 0 := LinearMap.ker_eq_top.mp h2
  rw [← Matrix.toLin'_pow] at h3
  exact (Matrix.toLin'.map_eq_zero_iff).mp h3

theorem exists_unit_mul_eq_nilpotent_three {k : Type*} [Field k] {M : Matrix (Fin 3) (Fin 3) k}
    (hM : M ^ 3 = 0) (hne : M ≠ 0) :
    ∃ A : Matrix (Fin 3) (Fin 3) k, IsUnit A ∧
      (M * A = A * regN 3 k ∨ M * A = A * Matrix.single 0 2 (1 : k)) := by
  have hdim : Module.finrank k (Fin 3 → k) = 3 := by simp
  have hf : (Matrix.toLin' M) ^ 3 = 0 := by rw [← Matrix.toLin'_pow, hM, map_zero]
  have hfne : Matrix.toLin' M ≠ 0 := fun h => hne ((Matrix.toLin'.map_eq_zero_iff).mp h)
  obtain ⟨c, hli, hc⟩ := KCNilpotent.exists_chain_three hdim (Matrix.toLin' M) hf hfne
  simp only [Matrix.toLin'_apply] at hc
  rcases hc with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
  · obtain ⟨A, hA, hMA⟩ := exists_isUnit_mul_eq_of_chain M (regN 3 k) c hli (by
      intro j
      fin_cases j <;> simp [Fin.sum_univ_three, regN_apply, h0, h1, h2])
    exact ⟨A, hA, Or.inl hMA⟩
  · obtain ⟨A, hA, hMA⟩ := exists_isUnit_mul_eq_of_chain M (Matrix.single 0 2 (1 : k)) c hli (by
      intro j
      fin_cases j <;> simp [Matrix.single_apply, h0, h1, h2])
    exact ⟨A, hA, Or.inr hMA⟩

theorem exists_unit_mul_eq_nilpotent_four {k : Type*} [Field k] {M : Matrix (Fin 4) (Fin 4) k}
    (hM : M ^ 4 = 0) (hne : M ≠ 0) :
    ∃ A : Matrix (Fin 4) (Fin 4) k, IsUnit A ∧
      (M * A = A * regN 4 k ∨ M * A = A * Matrix.single 0 3 (1 : k) ∨
        M * A = A * (Matrix.single 0 2 (1 : k) + Matrix.single 1 3 (1 : k)) ∨
        M * A = A * (Matrix.single 0 1 (1 : k) + Matrix.single 1 2 (1 : k))) := by
  have hdim : Module.finrank k (Fin 4 → k) = 4 := by simp
  have hf : (Matrix.toLin' M) ^ 4 = 0 := by rw [← Matrix.toLin'_pow, hM, map_zero]
  have hfne : Matrix.toLin' M ≠ 0 := fun h => hne ((Matrix.toLin'.map_eq_zero_iff).mp h)
  obtain ⟨c, hli, hc⟩ := KCNilpotent.exists_chain_four hdim (Matrix.toLin' M) hf hfne
  simp only [Matrix.toLin'_apply] at hc
  rcases hc with ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩
  · obtain ⟨A, hA, hMA⟩ := exists_isUnit_mul_eq_of_chain M (regN 4 k) c hli (by
      intro j
      fin_cases j <;> simp [Fin.sum_univ_four, regN_apply, h0, h1, h2, h3])
    exact ⟨A, hA, Or.inl hMA⟩
  · obtain ⟨A, hA, hMA⟩ := exists_isUnit_mul_eq_of_chain M (Matrix.single 0 3 (1 : k)) c hli (by
      intro j
      fin_cases j <;> simp [Matrix.single_apply, h0, h1, h2, h3])
    exact ⟨A, hA, Or.inr (Or.inl hMA)⟩
  · obtain ⟨A, hA, hMA⟩ := exists_isUnit_mul_eq_of_chain M
      (Matrix.single 0 2 (1 : k) + Matrix.single 1 3 (1 : k)) c hli (by
      intro j
      fin_cases j <;> simp [Matrix.single_apply, h0, h1, h2, h3])
    exact ⟨A, hA, Or.inr (Or.inr (Or.inl hMA))⟩
  · obtain ⟨A, hA, hMA⟩ := exists_isUnit_mul_eq_of_chain M
      (Matrix.single 0 1 (1 : k) + Matrix.single 1 2 (1 : k)) c hli (by
      intro j
      fin_cases j <;> simp [Matrix.single_apply, h0, h1, h2, h3])
    exact ⟨A, hA, Or.inr (Or.inr (Or.inr hMA))⟩

theorem exists_conjAut_of_mul_eq {n : ℕ} {k : Type*} [Field k]
    (u v : SpecialLinearGroup (Fin n) k) {A N : Matrix (Fin n) (Fin n) k} (hA : IsUnit A)
    (hMA : ((u : Matrix (Fin n) (Fin n) k) - 1) * A = A * N)
    (hv : (v : Matrix (Fin n) (Fin n) k) = 1 + N) :
    ∃ Ag : GL (Fin n) k, conjAut n k Ag (proj n k u) = proj n k v := by
  refine ⟨hA.unit⁻¹, ?_⟩
  rw [conjAut_proj]
  congr 1
  apply Subtype.ext
  have hU : ((hA.unit : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = A := hA.unit_spec
  have hUA : ((hA.unit⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * A = 1 := by
    have h1 : ((hA.unit⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) *
        ((hA.unit : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rwa [hU] at h1
  have hu : (u : Matrix (Fin n) (Fin n) k) = 1 + ((u : Matrix (Fin n) (Fin n) k) - 1) := by
    abel
  rw [coe_slConjugation, inv_inv, hU, hv]
  set X := ((hA.unit⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) with hX
  calc X * (u : Matrix (Fin n) (Fin n) k) * A
      = X * (1 + ((u : Matrix (Fin n) (Fin n) k) - 1)) * A := by rw [← hu]
    _ = X * A + X * (((u : Matrix (Fin n) (Fin n) k) - 1) * A) := by
        rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_assoc]
    _ = 1 + N := by rw [hMA, ← Matrix.mul_assoc, hUA, Matrix.one_mul]

theorem exists_good_conjugate {p f n : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hf : 1 ≤ f)
    (hn : n = 3 ∨ n = 4) {k : Type*} [Field k] [Finite k] [CharP k p] (hk : Nat.card k = p ^ f)
    (u : SpecialLinearGroup (Fin n) k) (hu : u ^ p = 1) (hu1 : u ≠ 1) :
    ∃ (v : SpecialLinearGroup (Fin n) k) (Ag : GL (Fin n) k),
      NormalPrimeComplementsTrivial p v ∧ conjAut n k Ag (proj n k u) = proj n k v := by
  have : Fact p.Prime := ⟨hp⟩
  have hn0 : NeZero n := ⟨by omega⟩
  have hMp : ((u : Matrix (Fin n) (Fin n) k) - 1) ^ p = 0 := by
    rw [sub_pow_char_of_commute p (Commute.one_right _), one_pow,
      ← Matrix.SpecialLinearGroup.coe_pow, hu, Matrix.SpecialLinearGroup.coe_one, sub_self]
  have hne : (u : Matrix (Fin n) (Fin n) k) - 1 ≠ 0 := by
    intro h
    apply hu1
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_one]
    exact sub_eq_zero.mp h
  have hMn := pow_dim_eq_zero_of_pow_eq_zero hMp
  have h34 := linear_three_four_nonregular_unipotent_centralizer_normal_prime_complements_trivial
    (k := k) hp hp3 hf hk
  have hreg : ∀ m : ℕ, 3 ≤ m → m ≤ p → NormalPrimeComplementsTrivial p (regU m k) :=
    fun m hm3 hmp B S hB hSC hSn hSp =>
      linear_regular_unipotent_centralizer_normal_prime_complements_trivial hp hp3 hf hm3 hmp hk
        B hB S hSC hSn hSp
  rcases hn with rfl | rfl
  · obtain ⟨A, hA, hMA | hMA⟩ := exists_unit_mul_eq_nilpotent_three hMn hne
    · obtain ⟨Ag, hAg⟩ := exists_conjAut_of_mul_eq u (regU 3 k) hA hMA coe_regU
      exact ⟨regU 3 k, Ag, hreg 3 le_rfl (by omega), hAg⟩
    · obtain ⟨Ag, hAg⟩ := exists_conjAut_of_mul_eq u (uA k) hA hMA (coe_oneAdd _ _)
      exact ⟨uA k, Ag, h34.1, hAg⟩
  · obtain ⟨A, hA, hMA | hMA | hMA | hMA⟩ := exists_unit_mul_eq_nilpotent_four hMn hne
    · obtain ⟨Ag, hAg⟩ := exists_conjAut_of_mul_eq u (regU 4 k) hA hMA coe_regU
      exact ⟨regU 4 k, Ag, hreg 4 (by omega) (by omega), hAg⟩
    · obtain ⟨Ag, hAg⟩ := exists_conjAut_of_mul_eq u (uB k) hA hMA (coe_oneAdd _ _)
      exact ⟨uB k, Ag, h34.2.1, hAg⟩
    · obtain ⟨Ag, hAg⟩ := exists_conjAut_of_mul_eq u (uC k) hA hMA (coe_oneAdd _ _)
      exact ⟨uC k, Ag, h34.2.2.1, hAg⟩
    · obtain ⟨Ag, hAg⟩ := exists_conjAut_of_mul_eq u (uD k) hA hMA (coe_oneAdd _ _)
      exact ⟨uD k, Ag, h34.2.2.2, hAg⟩

theorem linear_three_four_inner_defining_centralizer_local_cores_trivial {p f n : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hf : 1 ≤ f) (hn : n = 3 ∨ n = 4) {k : Type*} [Field k]
    [Finite k] [CharP k p] (hk : Nat.card k = p ^ f)
    (B : Subgroup (MulAut (projectiveSL n k)))
    (hB : (MulAut.conj : projectiveSL n k →* MulAut (projectiveSL n k)).range ≤ B)
    {a : MulAut (projectiveSL n k)}
    (ha : a ∈ (MulAut.conj : projectiveSL n k →* MulAut (projectiveSL n k)).range)
    (hord : orderOf a = p) :
    (∀ S : Subgroup (MulAut (projectiveSL n k)), S ≤ B ⊓ Subgroup.centralizer {a} →
      (S.subgroupOf (B ⊓ Subgroup.centralizer {a})).Normal → ¬ p ∣ Nat.card S → S = ⊥) ∧
      inSubgroup (aschbacherSolvableCore p) (B ⊓ Subgroup.centralizer {a}) = ⊥ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp5 : 5 ≤ p := by
    by_contra h
    have h4 : p = 4 := by omega
    rw [h4] at hp
    exact absurd hp (by norm_num)
  have hn3 : 3 ≤ n := by omega
  have hnp : n < p := by omega
  have hne : a ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hord
    exact hp.one_lt.ne hord
  have hap : a ^ p = 1 := hord ▸ pow_orderOf_eq_one a
  have ha' : a ∈ (innerOfSL n k).range := by
    obtain ⟨y, rfl⟩ := ha
    obtain ⟨g, rfl⟩ := proj_surjective n k y
    exact ⟨g, rfl⟩
  obtain ⟨u, hua, hup⟩ := exists_lift_pow_eq_one (innerOfSL n k) hp
    (not_dvd_card_ker_innerOfSL hp hn3 hnp) ha' hap
  have hu1 : u ≠ 1 := by
    rintro rfl
    apply hne
    rw [← hua, map_one]
  obtain ⟨v, Ag, hv, hAg⟩ := exists_good_conjugate hp hp3 hf hn hk u hup hu1
  set ψ : MulAut (projectiveSL n k) := conjAut n k Ag with hψ
  have hconj : ψ * a * ψ⁻¹ = MulAut.conj (proj n k v) := by
    rw [← hAg, CFSG.RankThree.GroupTheory.SteinbergBY.mulAut_conj_apply_eq, ← hua]
    rfl
  have hmain : ∀ S : Subgroup (MulAut (projectiveSL n k)), S ≤ B ⊓ Subgroup.centralizer {a} →
      (S.subgroupOf (B ⊓ Subgroup.centralizer {a})).Normal → ¬ p ∣ Nat.card S → S = ⊥ :=
    fun S hSC hSn hSp => normalPrimeComplements_of_conj p ψ a
      (by rw [hconj]; exact hv) B S hB hSC hSn hSp
  refine ⟨hmain, ?_⟩
  obtain ⟨h1, h2, h3⟩ := inSubgroup_theta_normal_prime_complement hp
    (B ⊓ Subgroup.centralizer {a})
  exact hmain _ h1 h2 h3

end CFSG.RankThree.PartOne
