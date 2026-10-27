module

public import CFSG.Quasithin.Background.F6CatRecogTools
public import CFSG.Quasithin.Background.F6CatTransport
import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.Quasithin.Background.F6SQTK
public import CFSG.Quasithin.EmptyFaithfulMultiple.FFLinearGroup

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

namespace F618Comp

open CFSG.Assembly.LowTwoRank

@[expose] def NotSL2 (M : Type*) [Group M] : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], ¬ Nonempty (M ≃* ↥(StatedSL 2 K))

theorem NotSL2.of_mulEquiv {M M' : Type*} [Group M] [Group M'] (e : M ≃* M') (h : NotSL2 M') :
    NotSL2 M := fun K _ _ _ ⟨f⟩ => h K ⟨e.symm.trans f⟩

theorem odd_four_pow_sub_one {n : ℕ} (hn : 1 ≤ n) : Odd (4 ^ n - 1) :=
  Nat.Even.sub_odd (Nat.one_le_pow _ _ (by norm_num))
    (Nat.even_pow.mpr ⟨by decide, by omega⟩) odd_one

theorem ne_two_pow_mul {N a : ℕ} (h1 : N % 2 ^ (a + 1) = 2 ^ a) (h2 : N ≠ 2 ^ a * (4 ^ a - 1))
    {n : ℕ} (hn : 1 ≤ n) : N ≠ 2 ^ n * (4 ^ n - 1) := by
  intro hN
  rcases lt_trichotomy n a with h | rfl | h
  · have hd1 : 2 ^ (n + 1) ∣ N := by
      have hdecomp := Nat.div_add_mod N (2 ^ (a + 1))
      rw [h1] at hdecomp
      rw [← hdecomp]
      exact dvd_add (Dvd.dvd.mul_right (pow_dvd_pow 2 (by omega)) _) (pow_dvd_pow 2 (by omega))
    rw [hN, pow_succ] at hd1
    have h2d : 2 ∣ 4 ^ n - 1 := Nat.dvd_of_mul_dvd_mul_left (by positivity) hd1
    exact (Nat.not_even_iff_odd.mpr (odd_four_pow_sub_one hn)) (even_iff_two_dvd.mpr h2d)
  · exact h2 hN
  · have hd : 2 ^ (a + 1) ∣ N := hN ▸ Dvd.dvd.mul_right (pow_dvd_pow 2 (by omega)) _
    rw [Nat.mod_eq_zero_of_dvd hd] at h1
    exact absurd h1.symm (by positivity)

theorem exists_card_statedSL_two (K : Type) [Field K] [Finite K] [CharP K 2] :
    ∃ n : ℕ, 1 ≤ n ∧ Nat.card ↥(StatedSL 2 K) = 2 ^ n * (4 ^ n - 1) := by
  have := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  refine ⟨n, n.pos, ?_⟩
  rw [FFL.card_statedSL_two, hn, ← pow_mul, mul_comm (n : ℕ) 2, pow_mul]
  norm_num

theorem notSL2_of_card {M : Type*} [Group M] (a : ℕ) (h1 : Nat.card M % 2 ^ (a + 1) = 2 ^ a)
    (h2 : Nat.card M ≠ 2 ^ a * (4 ^ a - 1)) : NotSL2 M := by
  intro K _ _ _ ⟨e⟩
  obtain ⟨n, hn, hc⟩ := exists_card_statedSL_two K
  exact ne_two_pow_mul h1 h2 hn ((Nat.card_congr e.toEquiv).trans hc)

theorem sq_eq_one_of_pow_four_eq_one {K : Type} [Field K] [CharP K 2]
    (A : Matrix.SpecialLinearGroup (Fin 2) K) (h : A ^ 4 = 1) : A ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M : Matrix (Fin 2) (Fin 2) K := (A : Matrix (Fin 2) (Fin 2) K) with hMdef
  have hM4 : M ^ 4 = 1 := by
    have := congrArg (fun B : Matrix.SpecialLinearGroup (Fin 2) K =>
      (B : Matrix (Fin 2) (Fin 2) K)) h
    simpa [hMdef] using this
  have hnil : IsNilpotent (M - 1) := by
    refine ⟨4, ?_⟩
    have := sub_pow_char_pow_of_commute (R := Matrix (Fin 2) (Fin 2) K) 2 2
      (Commute.one_right M)
    norm_num at this
    rw [this, hM4, sub_self]
  have htr : Matrix.trace (M - 1) = 0 := (Matrix.isNilpotent_trace_of_isNilpotent hnil).eq_zero
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have ht : M 0 0 + M 1 1 = 0 := by
    rw [Matrix.trace_sub, Matrix.trace_one, Matrix.trace_fin_two] at htr
    simpa [h2] using htr
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    have := A.2
    rwa [Matrix.det_fin_two] at this
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hMdef.symm, sq, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination M 0 0 * ht - hdet - h2
  · linear_combination M 0 1 * ht
  · linear_combination M 1 0 * ht
  · linear_combination M 1 1 * ht - hdet - h2

theorem notSL2_of_pow {M : Type*} [Group M] (x : M) (h4 : x ^ 4 = 1) (h2 : x ^ 2 ≠ 1) :
    NotSL2 M := by
  intro K _ _ _ ⟨e⟩
  set ε := e.trans (specialLinearGroupEquivStatedSL 2 K).symm
  apply h2
  apply ε.injective
  rw [map_pow, map_one]
  exact sq_eq_one_of_pow_four_eq_one _ (by rw [← map_pow, h4, map_one])

theorem card_alternating_six : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

section Socle

variable {G G' : Type*} [Group G] [Group G']

theorem map_centralizer_mulEquiv (e : G ≃* G') (N : Subgroup G) :
    (Subgroup.centralizer (N : Set G)).map e.toMonoidHom =
      Subgroup.centralizer ((N.map e.toMonoidHom : Subgroup G') : Set G') := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff] at hy
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨n, hn, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hy n hn]
  · intro hx
    refine ⟨e.symm x, ?_, by simp⟩
    rw [Subgroup.mem_centralizer_iff] at hx
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro n hn
    apply e.injective
    have := hx (e n) ⟨n, hn, rfl⟩
    simpa only [map_mul, MulEquiv.apply_symm_apply] using this

structure GoodSocle (N : Subgroup G) : Prop where
  normal : N.Normal
  quasisimple : CFSG.IsQuasisimple ↥N
  odd_card : Odd (Nat.card ↥(Subgroup.centralizer (N : Set G)))
  notSL2 : NotSL2 ↥N
  alt6 : Nonempty (↥N ≃* ↥(alternatingGroup (Fin 6))) → Subgroup.centralizer (N : Set G) = ⊥

theorem GoodSocle.map (e : G ≃* G') {N : Subgroup G} (h : GoodSocle N) :
    GoodSocle (N.map e.toMonoidHom) := by
  have eN : ↥N ≃* ↥(N.map e.toMonoidHom) := N.equivMapOfInjective e.toMonoidHom e.injective
  refine ⟨h.normal.map e.toMonoidHom e.surjective,
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eN h.quasisimple, ?_,
    h.notSL2.of_mulEquiv eN.symm, ?_⟩
  · rw [← map_centralizer_mulEquiv, Subgroup.card_map_of_injective e.injective]
    exact h.odd_card
  · rintro ⟨f⟩
    rw [← map_centralizer_mulEquiv, h.alt6 ⟨eN.trans f⟩, Subgroup.map_bot]

theorem eq_of_isComponent [Finite G] {N M : Subgroup G} (hN : CFSG.IsComponent N)
    (hC : Group.IsSolvable ↥(Subgroup.centralizer (N : Set G))) (hM : CFSG.IsComponent M) :
    M = N := by
  rcases CFSG.LocalCores.distinct_components_commute hM hN with h | h
  · exact h
  · exfalso
    have hle : M ≤ Subgroup.centralizer (N : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
    have : Group.IsSolvable ↥M :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
    have : Nontrivial ↥M := CFSG.LocalCores.isQuasisimple_nontrivial hM.1
    have : Group.IsPerfect ↥M := hM.1.1
    exact Group.IsPerfect.not_isSolvable ↥M ‹_›

@[expose] def Socle (G : Type*) [Group G] : Prop :=
  (∀ M : Subgroup G, ¬ CFSG.IsComponent M) ∨ ∃ N : Subgroup G, GoodSocle N

theorem Socle.of_mulEquiv (e : G ≃* G') (h : Socle G') : Socle G := by
  rcases h with h | ⟨N, hN⟩
  · exact Or.inl fun M hM => h _ (CFSG.LocalCores.isComponent_map_mulEquiv e hM)
  · exact Or.inr ⟨_, hN.map e.symm⟩

theorem goodSocle_of_centralizer_le {N : Subgroup G} (hn : N.Normal)
    (hq : CFSG.IsQuasisimple ↥N) (hC : Subgroup.centralizer (N : Set G) ≤ N)
    (hZ : Odd (Nat.card ↥(Subgroup.center ↥N))) (hS : NotSL2 ↥N) : GoodSocle N := by
  have heq : Subgroup.centralizer (N : Set G) = (Subgroup.center ↥N).map N.subtype := by
    ext x
    constructor
    · intro hx
      refine ⟨⟨x, hC hx⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hx) y y.2)
    · rintro ⟨y, hy, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro n hn
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy ⟨n, hn⟩)
  refine ⟨hn, hq, ?_, hS, ?_⟩
  · rw [heq, Subgroup.card_map_of_injective N.subtype_injective]
    exact hZ
  · rintro ⟨f⟩
    have hc : Subgroup.center ↥N = ⊥ := by
      have h1 : (Subgroup.center ↥N).map f.toMonoidHom = ⊥ := by
        rw [← alternatingGroup.center_eq_bot (by simp), ← Subgroup.map_center_eq f]
        rfl
      exact (Subgroup.map_eq_bot_iff_of_injective _ f.injective).mp h1
    rw [heq, hc, Subgroup.map_bot]

theorem goodSocle_top (hq : CFSG.IsQuasisimple G) (hZ : Odd (Nat.card ↥(Subgroup.center G)))
    (hS : NotSL2 G) : GoodSocle (⊤ : Subgroup G) := by
  refine goodSocle_of_centralizer_le Subgroup.normal_top
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hq) le_top ?_
    (hS.of_mulEquiv Subgroup.topEquiv)
  have h1 := Subgroup.map_center_eq (Subgroup.topEquiv (G := G))
  have h2 : Nat.card ↥((Subgroup.center ↥(⊤ : Subgroup G)).map
      (Subgroup.topEquiv (G := G) : ↥(⊤ : Subgroup G) →* G)) =
      Nat.card ↥(Subgroup.center ↥(⊤ : Subgroup G)) :=
    Subgroup.card_map_of_injective (Subgroup.topEquiv (G := G)).injective
  rw [h1] at h2
  rw [← h2]
  exact hZ

theorem socle_of_isQuasisimple (hq : CFSG.IsQuasisimple G)
    (hZ : Odd (Nat.card ↥(Subgroup.center G))) (hS : NotSL2 G) : Socle G :=
  Or.inr ⟨⊤, goodSocle_top hq hZ hS⟩

theorem center_eq_bot_of_isSimpleGroup [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) :
    Subgroup.center G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · exact h
  · obtain ⟨a, b, hab⟩ := hnonab
    exact absurd (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a) hab

theorem isQuasisimple_of_isSimpleGroup [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) :
    CFSG.IsQuasisimple G := by
  have hc := center_eq_bot_of_isSimpleGroup hnonab
  let e : G ⧸ Subgroup.center G ≃* G :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  refine ⟨F6.isPerfect_of_isSimpleGroup hnonab, e.isSimpleGroup, ?_⟩
  obtain ⟨a, b, hab⟩ := hnonab
  exact ⟨e.symm a, e.symm b, fun h => hab (e.symm.injective (by rw [map_mul, map_mul, h]))⟩

theorem socle_of_isSimpleGroup [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hS : NotSL2 G) : Socle G := by
  refine socle_of_isQuasisimple (isQuasisimple_of_isSimpleGroup hnonab) ?_ hS
  rw [center_eq_bot_of_isSimpleGroup hnonab, Subgroup.card_bot]
  exact odd_one

theorem not_isComponent_of_isSolvable [Group.IsSolvable G] (M : Subgroup G) :
    ¬ CFSG.IsComponent M := by
  intro hM
  have : Nontrivial ↥M := CFSG.LocalCores.isQuasisimple_nontrivial hM.1
  have : Group.IsPerfect ↥M := hM.1.1
  exact Group.IsPerfect.not_isSolvable ↥M inferInstance

theorem socle_of_isSolvable [Group.IsSolvable G] : Socle G :=
  Or.inl not_isComponent_of_isSolvable

theorem not_isComponent_of_card_sylow [Finite G] (T : Sylow 2 G)
    (hT : Nat.card (T : Subgroup G) = 2) (M : Subgroup G) : ¬ CFSG.IsComponent M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rintro ⟨⟨-, hs, a, b, hab⟩, -⟩
  have : IsSimpleGroup (↥M ⧸ Subgroup.center ↥M) := hs
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 (↥M ⧸ Subgroup.center ↥M)))
  have h4 := (F6.not_isCyclic_sylow_two ⟨a, b, hab⟩ P).2
  have h4G : 2 ^ 2 ∣ Nat.card G :=
    h4.trans ((P.card_subgroup_dvd_card).trans
      ((Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_subgroup_dvd_card M)))
  have := Sylow.pow_dvd_card_of_pow_dvd_card (P := T) h4G
  rw [hT] at this
  exact absurd (Nat.le_of_dvd (by norm_num) this) (by norm_num)

theorem isSolvable_of_caseTwo {D : Type} [Group D] [Finite D] (h : F6.IsF618CaseTwo D) :
    Group.IsSolvable D := by
  rcases h with e | ⟨φ, hφ, hN⟩
  · have := F6.isSolvable_perm_three
    exact Group.isSolvable_of_surjective (f := e.some.symm.toMonoidHom) e.some.symm.surjective
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h27 : Nat.card ↥φ.ker = 3 ^ 3 := hN.2.1
    have := (IsPGroup.of_card h27).isNilpotent
    exact Group.isSolvable_of_ker_le_range φ.ker.subtype φ (by rw [Subgroup.range_subtype])

end Socle

section Aut

variable {M : Type*} [Group M]

theorem mul_conj_mul_inv (φ : MulAut M) (g : M) :
    φ * MulAut.conj g * φ⁻¹ = MulAut.conj (φ g) := by
  ext x
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]

theorem conj_injective_of_center_eq_bot (h : Subgroup.center M = ⊥) :
    Function.Injective (MulAut.conj : M →* MulAut M) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  rw [← h, Subgroup.mem_center_iff]
  intro x
  have := congrArg (fun φ : MulAut M => φ x) (MonoidHom.mem_ker.mp hg)
  simp only [MulAut.conj_apply, MulAut.one_apply] at this
  calc x * g = g * x * g⁻¹ * g := by rw [this]
    _ = g * x := by group

theorem socle_mulAut [IsSimpleGroup M] (hnab : ∃ a b : M, a * b ≠ b * a) (hS : NotSL2 M) :
    Socle (MulAut M) := by
  have hc := center_eq_bot_of_isSimpleGroup hnab
  have hinj := conj_injective_of_center_eq_bot hc
  set N := (MulAut.conj : M →* MulAut M).range
  have ψ : M ≃* ↥N := MonoidHom.ofInjective hinj
  have hN : N.Normal := by
    refine ⟨fun x hx φ => ?_⟩
    obtain ⟨g, rfl⟩ := hx
    exact ⟨φ g, (mul_conj_mul_inv φ g).symm⟩
  have hC : Subgroup.centralizer (N : Set (MulAut M)) = ⊥ := by
    rw [eq_bot_iff]
    intro φ hφ
    rw [Subgroup.mem_centralizer_iff] at hφ
    rw [Subgroup.mem_bot]
    ext g
    have h1 := hφ (MulAut.conj g) ⟨g, rfl⟩
    have h2 : MulAut.conj (φ g) = MulAut.conj g := by
      rw [← mul_conj_mul_inv, ← h1, mul_inv_cancel_right]
    exact hinj h2
  refine Or.inr ⟨N, hN,
    CFSG.LocalCores.isQuasisimple_of_mulEquiv ψ (isQuasisimple_of_isSimpleGroup hnab), ?_,
    hS.of_mulEquiv ψ.symm, fun _ => hC⟩
  rw [hC, Subgroup.card_bot]
  exact odd_one

end Aut

@[expose] def Conclusion {D : Type} [Group D] (M : Subgroup D) : Prop :=
  (∀ (K : Type) [Field K] [Finite K] [CharP K 2], ¬ Nonempty (↥M ≃* ↥(StatedSL 2 K))) ∧
    Odd (Nat.card ↥(Subgroup.centralizer (M : Set D))) ∧
    (Nonempty (↥M ≃* ↥(alternatingGroup (Fin 6))) → Subgroup.centralizer (M : Set D) = ⊥)

theorem GoodSocle.conclusion {D : Type} [Group D] [Finite D] {N M : Subgroup D}
    (h : GoodSocle N) (hM : CFSG.IsComponent M) : Conclusion M := by
  have hN : CFSG.IsComponent N := ⟨h.quasisimple, h.normal.isSubnormal⟩
  have hC : Group.IsSolvable ↥(Subgroup.centralizer (N : Set D)) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ h.odd_card
  obtain rfl := eq_of_isComponent hN hC hM
  exact ⟨h.notSL2, h.odd_card, h.alt6⟩

theorem conclusion_of_socle {D : Type} [Group D] [Finite D] (h : Socle D) {M : Subgroup D}
    (hM : CFSG.IsComponent M) : Conclusion M := by
  rcases h with h | ⟨N, hN⟩
  · exact absurd hM (h M)
  · exact hN.conclusion hM

end F618Comp

end CFSG.Quasithin.EmptyFaithfulMultiple
