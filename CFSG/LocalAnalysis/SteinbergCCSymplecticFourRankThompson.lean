module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bCent
public import CFSG.LocalAnalysis.PreuniquenessRankFour.GeneratorRank

public section

namespace CFSG.LocalAnalysis

open CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.QuasithinUnique.Setup.X7b

section RankThompson

variable (G : Type*) [Group G] [Finite G]

@[expose] noncomputable def maxAbelianRank : ℕ :=
  sSup {r : ℕ | ∃ A : Subgroup G, IsMulCommutative A ∧ Group.rank A = r}

@[expose] def maxRankAbelianFamily : Set (Subgroup G) :=
  {A | IsMulCommutative A ∧ Group.rank A = maxAbelianRank G}

@[expose] noncomputable def rankThompson : Subgroup G :=
  sSup (maxRankAbelianFamily G)

end RankThompson

namespace SymplecticFourRankThompson

section Invariance

variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]

omit [Finite H] in
theorem rank_map_equiv (e : G ≃* H) (A : Subgroup G) :
    Group.rank (A.map e.toMonoidHom) = Group.rank A :=
  (Group.rank_congr (A.equivMapOfInjective e.toMonoidHom e.injective)).symm

theorem rankSet_subset (e : G ≃* H) :
    {r : ℕ | ∃ A : Subgroup G, IsMulCommutative A ∧ Group.rank A = r} ⊆
      {r : ℕ | ∃ A : Subgroup H, IsMulCommutative A ∧ Group.rank A = r} := by
  rintro r ⟨A, hA, rfl⟩
  exact ⟨A.map e.toMonoidHom, inferInstance, rank_map_equiv e A⟩

theorem maxAbelianRank_congr (e : G ≃* H) : maxAbelianRank G = maxAbelianRank H := by
  unfold maxAbelianRank
  rw [(rankSet_subset e).antisymm (rankSet_subset e.symm)]

theorem map_rankThompson_le (e : G ≃* H) :
    (rankThompson G).map e.toMonoidHom ≤ rankThompson H := by
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun A hA => ?_
  obtain ⟨hAc, hAr⟩ := hA
  rw [← Subgroup.map_le_iff_le_comap]
  refine le_sSup ⟨inferInstance, ?_⟩
  rw [rank_map_equiv, hAr, maxAbelianRank_congr e]

theorem map_rankThompson (e : G ≃* H) :
    (rankThompson G).map e.toMonoidHom = rankThompson H := by
  refine le_antisymm (map_rankThompson_le e) ?_
  have h := Subgroup.map_mono (f := e.toMonoidHom) (map_rankThompson_le e.symm)
  rwa [Subgroup.map_map, show e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id H from
    MonoidHom.ext e.apply_symm_apply, Subgroup.map_id] at h

theorem rankThompson_characteristic : (rankThompson G).Characteristic :=
  Subgroup.characteristic_iff_map_eq.mpr fun φ => map_rankThompson φ

end Invariance

section Rank

open CFSG.PreuniquenessRankFour.Helpers

@[expose] def omegaOneOf {G : Type*} [Group G] (A : Subgroup G) [IsMulCommutative A] :
    Subgroup G where
  carrier := {x | x ∈ A ∧ x * x = 1}
  one_mem' := ⟨A.one_mem, mul_one 1⟩
  mul_mem' := by
    rintro x y ⟨hx, hx2⟩ ⟨hy, hy2⟩
    refine ⟨A.mul_mem hx hy, ?_⟩
    have hxy : y * x = x * y := setLike_mul_comm hy hx
    calc x * y * (x * y) = x * (y * x) * y := by simp only [mul_assoc]
      _ = 1 := by rw [hxy, ← mul_assoc, hx2, one_mul, hy2]
  inv_mem' := by
    rintro x ⟨hx, hx2⟩
    exact ⟨A.inv_mem hx, by rw [← mul_inv_rev, hx2, inv_one]⟩

theorem omegaOneOf_le {G : Type*} [Group G] (A : Subgroup G) [IsMulCommutative A] :
    omegaOneOf A ≤ A := fun _ hx => hx.1

theorem card_frattini_quotient_eq {X : Type*} [Group X] [Finite X] (hX : IsPGroup 2 X) :
    Nat.card (X ⧸ frattini X) = 2 ^ Group.rank X := by
  let : IsMulCommutative (X ⧸ frattini X) := pGroup_frattini_quotient_isMulCommutative 2 hX
  let : CommGroup (X ⧸ frattini X) := IsMulCommutative.instCommGroup
  let := pGroup_binary_frattini_quotient_module hX
  rw [← twoGroup_frattini_finrank_eq_group_rank hX]
  exact (FiniteField.pow_finrank_eq_natCard 2 (Additive (X ⧸ frattini X))).symm

theorem two_pow_rank_le_card_omegaOneOf {G : Type*} [Group G] [Finite G] (A : Subgroup G)
    [IsMulCommutative A] (hA : IsPGroup 2 A) : 2 ^ Group.rank A ≤ Nat.card (omegaOneOf A) := by
  have hcomm : ∀ x y : A, x * y = y * x := fun x y => Subtype.ext (setLike_mul_comm x.2 y.2)
  let sq : A →* A :=
    { toFun := fun x => x * x
      map_one' := mul_one 1
      map_mul' := fun x y => by
        calc x * y * (x * y) = x * (y * x) * y := by simp only [mul_assoc]
          _ = x * x * (y * y) := by rw [hcomm y x]; simp only [mul_assoc] }
  have hrange : sq.range ≤ frattini A := by
    rintro _ ⟨x, rfl⟩
    have h := pGroup_frattini_quotient_pow_eq_one 2 hA (x : A ⧸ frattini A)
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, pow_two] at h
    exact h
  have hker : Nat.card sq.ker = Nat.card (omegaOneOf A) := by
    have hmap : sq.ker.map A.subtype = omegaOneOf A := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x.2, congrArg Subtype.val (hx : x * x = 1)⟩
      · rintro ⟨hyA, hy⟩
        exact ⟨⟨y, hyA⟩, Subtype.ext hy, rfl⟩
    rw [← hmap, Subgroup.card_map_of_injective A.subtype_injective]
  have h1 : Nat.card sq.ker * Nat.card sq.range = Nat.card A := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  have h2 : Nat.card (frattini A) * Nat.card (A ⧸ frattini A) = Nat.card A :=
    (frattini A).card_mul_index
  have h3 : Nat.card sq.range ≤ Nat.card (frattini A) := Subgroup.card_le_of_le hrange
  have hpos : 0 < Nat.card sq.range := Nat.card_pos
  rw [← card_frattini_quotient_eq hA, ← hker]
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc Nat.card (A ⧸ frattini A) * Nat.card sq.range
      ≤ Nat.card (A ⧸ frattini A) * Nat.card (frattini A) := Nat.mul_le_mul_left _ h3
    _ = Nat.card sq.ker * Nat.card sq.range := by rw [h1, mul_comm, h2]

theorem two_pow_rank_eq_card_of_elementary {G : Type*} [Group G] [Finite G] (E : Subgroup G)
    [IsMulCommutative E] (hE : ∀ x ∈ E, x * x = 1) : 2 ^ Group.rank E = Nat.card E := by
  have hEp : IsPGroup 2 E := fun x => ⟨1, by rw [pow_one, pow_two]; exact Subtype.ext (hE x x.2)⟩
  have hΩ : omegaOneOf E = E := le_antisymm (omegaOneOf_le E) fun x hx => ⟨hx, hE x hx⟩
  refine le_antisymm ?_ ?_
  · have h := two_pow_rank_le_card_omegaOneOf E hEp
    rwa [hΩ] at h
  · let _ : CommGroup E := IsMulCommutative.instCommGroup
    exact Nat.le_of_dvd (pow_pos two_pos _)
      (card_dvd_exponent_pow_rank' E fun x => by rw [pow_two]; exact Subtype.ext (hE x x.2))

theorem card_le_two_mul_card_inf {G : Type*} [Group G] [Finite G] (N : Subgroup G) [N.Normal]
    [IsCyclic (G ⧸ N)] (E : Subgroup G) (hE : ∀ x ∈ E, x * x = 1) :
    Nat.card E ≤ 2 * Nat.card ↥(E ⊓ N) := by
  let f : E →* G ⧸ N := (QuotientGroup.mk' N).comp E.subtype
  have hker : Nat.card f.ker = Nat.card ↥(E ⊓ N) := by
    have hmap : f.ker.map E.subtype = E ⊓ N := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x.2, (QuotientGroup.eq_one_iff _).mp hx⟩
      · rintro ⟨hyE, hyN⟩
        exact ⟨⟨y, hyE⟩, (QuotientGroup.eq_one_iff _).mpr hyN, rfl⟩
    rw [← hmap, Subgroup.card_map_of_injective E.subtype_injective]
  have hrange : Nat.card f.range ≤ 2 := by
    have hexp : Monoid.exponent f.range ∣ 2 := Monoid.exponent_dvd_of_forall_pow_eq_one fun y => by
      obtain ⟨_, x, rfl⟩ := y
      apply Subtype.ext
      show f x ^ 2 = 1
      rw [← map_pow, pow_two, show x * x = 1 from Subtype.ext (hE x x.2), map_one]
    rw [← IsCyclic.exponent_eq_card]
    exact Nat.le_of_dvd two_pos hexp
  have h1 : Nat.card f.ker * Nat.card f.range = Nat.card E := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  calc Nat.card E = Nat.card f.ker * Nat.card f.range := h1.symm
    _ ≤ Nat.card f.ker * 2 := Nat.mul_le_mul_left _ hrange
    _ = 2 * Nat.card ↥(E ⊓ N) := by rw [hker, mul_comm]

end Rank

section Model

variable {K : Type} [Field K] [CharP K 2]

theorem mem_antiUnipotent_of_commute {g : antiSp K} (hc1 : uElt 0 0 1 0 * g = g * uElt 0 0 1 0)
    (hc2 : uElt 0 1 0 0 * g = g * uElt 0 1 0 0) : g ∈ antiUnipotent K := by
  have h1 := congrArg (fun h : antiSp K => glMat (h : GL (Fin 4) K)) hc1
  have h2 := congrArg (fun h : antiSp K => glMat (h : GL (Fin 4) K)) hc2
  simp only [Subgroup.coe_mul, Units.val_mul, glMat_uElt] at h1 h2
  set M : Matrix (Fin 4) (Fin 4) K := ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hM
  have e1 : ∀ i j : Fin 4, (uMat (0 : K) 0 1 0 * M) i j = (M * uMat (0 : K) 0 1 0) i j :=
    fun i j => by rw [h1]
  have e2 : ∀ i j : Fin 4, (uMat (0 : K) 1 0 0 * M) i j = (M * uMat (0 : K) 1 0 0) i j :=
    fun i j => by rw [h2]
  have t13 := e1 1 3
  have t23 := e1 2 3
  have t33 := e1 3 3
  have t01 := e1 0 1
  have t02 := e1 0 2
  have t03 := e1 0 3
  have u01 := e2 0 1
  have u02 := e2 0 2
  have u13 := e2 1 3
  simp [Matrix.mul_apply, Fin.sum_univ_four, uMat] at t13 t23 t33 t01 t02 t03 u01 u02 u13
  have m33 : M 3 3 = M 0 0 := by linear_combination t03
  have m22 : M 2 2 = M 0 0 := by linear_combination u02
  have m11 : M 1 1 = M 0 0 := by linear_combination m33 - u13
  have hJ := congrFun (congrFun (mem_antiSp.mp g.2) 0) 3
  rw [transpose_mul_minorJ_mul_apply, minorJ_apply] at hJ
  change M 0 0 * M 3 3 + M 1 0 * M 2 3 + M 2 0 * M 1 3 + M 3 0 * M 0 3 = _ at hJ
  rw [t13, t23, t33, m33] at hJ
  norm_num at hJ
  have h2' : (2 : K) = 0 := CharTwo.two_eq_zero
  have hsq : (M 0 0 - 1) ^ 2 = 0 := by linear_combination hJ - (M 0 0 - 1) * h2'
  have m00 : M 0 0 = 1 := sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hsq)
  rw [mem_antiUnipotent_iff_upper]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j
    all_goals first
      | exact absurd hij (by decide)
      | exact t13
      | exact t23
      | exact u01
      | exact t33
      | exact t01
      | exact t02
  · fin_cases i
    · exact m00
    · exact m11.trans m00
    · exact m22.trans m00
    · exact m33.trans m00

theorem mem_radA1_of_commute {g : antiSp K} (hg : g ∈ antiUnipotent K)
    (hc : g * uElt 0 0 0 1 = uElt 0 0 0 1 * g) : g ∈ radA1 K := by
  obtain ⟨a, b, c, d, rfl⟩ := hg
  rw [uElt_mul, uElt_mul] at hc
  have hb := (uElt_inj hc).2.1
  have ha : a = 0 := by
    have : a * 1 = 0 := by linear_combination hb
    simpa using this
  exact ⟨b, c, d, by rw [ha]⟩

theorem mem_radA2_of_commute {g : antiSp K} (hg : g ∈ antiUnipotent K)
    (hc : g * uElt 1 0 0 0 = uElt 1 0 0 0 * g) : g ∈ radA2 K := by
  obtain ⟨a, b, c, d, rfl⟩ := hg
  rw [uElt_mul, uElt_mul] at hc
  have hb := (uElt_inj hc).2.1
  have hd : d = 0 := by
    have : 1 * d = 0 := by linear_combination -hb
    simpa using this
  exact ⟨a, b, c, by rw [hd]⟩

theorem mul_uElt_ne (g : antiSp K) : g * uElt 0 1 0 0 ≠ uElt 0 0 1 0 * g := by
  intro h
  have hm := congrArg (fun x : antiSp K => glMat (x : GL (Fin 4) K)) h
  have hinv := congrArg (fun x : antiSp K => glMat (x : GL (Fin 4) K)) (inv_mul_cancel g)
  simp only [Subgroup.coe_mul, Units.val_mul, glMat_uElt, OneMemClass.coe_one,
    Units.val_one] at hm hinv
  set G : Matrix (Fin 4) (Fin 4) K := ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hG
  set G' : Matrix (Fin 4) (Fin 4) K :=
    (((g⁻¹ : antiSp K) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hG'
  have e : ∀ i j : Fin 4, (G * uMat (0 : K) 1 0 0) i j = (uMat (0 : K) 0 1 0 * G) i j :=
    fun i j => by rw [hm]
  have f : ∀ i j : Fin 4, (G' * G) i j = (1 : Matrix (Fin 4) (Fin 4) K) i j :=
    fun i j => by rw [hinv]
  have e12 := e 1 2
  have e22 := e 2 2
  have e32 := e 3 2
  have e13 := e 1 3
  have e23 := e 2 3
  have e33 := e 3 3
  simp [Matrix.mul_apply, Fin.sum_univ_four, uMat] at e12 e22 e32 e13 e23 e33
  have f00 := f 0 0
  have f10 := f 1 0
  have f11 := f 1 1
  simp [Matrix.mul_apply, Fin.sum_univ_four, e12, e22, e32, e13, e23, e33] at f00 f10 f11
  rcases f10 with h0 | h0
  · rw [h0, zero_mul] at f11
    exact zero_ne_one f11
  · rw [h0, mul_zero] at f00
    exact zero_ne_one f00

variable [Finite K]

theorem minorAut_sq_pow_uElt (m : ℕ) (a b c d : K) :
    ((minorAut K ^ 2) ^ m) (uElt a b c d) =
      uElt (a ^ 2 ^ m) (b ^ 2 ^ m) (c ^ 2 ^ m) (d ^ 2 ^ m) :=
  antiSp_ext (by rw [glMat_minorAut_sq_pow, glMat_uElt, uMat_map_pow, glMat_uElt])

theorem minorAut_odd_pow_uElt (m : ℕ) :
    (minorAut K ^ (2 * m + 1)) (uElt 0 0 1 0) = uElt 0 1 0 0 := by
  apply antiSp_ext
  have h0 : (0 : K) ^ 2 ^ m = 0 := zero_pow (pow_ne_zero m two_ne_zero)
  rw [glMat_eta, glMat_uElt, uMat_map_pow, h0, one_pow, minorMap_uMat, glMat_uElt]
  congr 1 <;> ring

variable {n : ℕ}

theorem exists_eq_conj_mul_sq_pow (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {α : MulAut (antiSp K)} (hx : α (uElt 0 0 1 0) = uElt 0 0 1 0) :
    ∃ (g : antiSp K) (m : ℕ), α = MulAut.conj g * (minorAut K ^ 2) ^ m := by
  obtain ⟨g, j, -, rfl⟩ := aut_eq_conj_mul_pow hn hK α
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' j
  · exact ⟨g, m, by rw [pow_mul]⟩
  · rw [MulAut.mul_apply, minorAut_odd_pow_uElt, MulAut.conj_apply] at hx
    exact absurd (mul_inv_eq_iff_eq_mul.mp hx) (mul_uElt_ne g)

theorem sq_pow_eq_one {m : ℕ}
    (h : ∀ t : K, ((minorAut K ^ 2) ^ m) (uElt 0 t 0 0) = uElt 0 t 0 0) :
    (minorAut K ^ 2) ^ m = 1 := by
  have ht : ∀ t : K, t ^ 2 ^ m = t := fun t => by
    have h1 := h t
    rw [minorAut_sq_pow_uElt] at h1
    exact (uElt_inj h1).2.1
  refine MulEquiv.ext fun y => antiSp_ext ?_
  rw [glMat_minorAut_sq_pow, MulAut.one_apply]
  ext i j
  simp [ht]

theorem exists_mem_radA1_eq_conj (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {α : MulAut (antiSp K)} (hα : ∀ a ∈ radA1 K, α a = a) :
    ∃ g ∈ radA1 K, α = MulAut.conj g := by
  obtain ⟨g, m, rfl⟩ := exists_eq_conj_mul_sq_pow hn hK (hα _ ⟨0, 1, 0, rfl⟩)
  have h0 : (0 : K) ^ 2 ^ m = 0 := zero_pow (pow_ne_zero m two_ne_zero)
  have hcomm : ∀ a ∈ radA1 K, ((minorAut K ^ 2) ^ m) a = a → g * a = a * g := by
    intro a ha hΦa
    have h1 := hα a ha
    rw [MulAut.mul_apply, hΦa, MulAut.conj_apply] at h1
    exact mul_inv_eq_iff_eq_mul.mp h1
  have hfix : ∀ b c d : K, b ^ 2 ^ m = b → c ^ 2 ^ m = c → d ^ 2 ^ m = d →
      ((minorAut K ^ 2) ^ m) (uElt 0 b c d) = uElt 0 b c d := by
    intro b c d hb hc hd
    rw [minorAut_sq_pow_uElt, h0, hb, hc, hd]
  have h1' := hcomm _ ⟨0, 1, 0, rfl⟩ (hfix 0 1 0 h0 (one_pow _) h0)
  have h2' := hcomm _ ⟨1, 0, 0, rfl⟩ (hfix 1 0 0 (one_pow _) h0 h0)
  have h3' := hcomm _ ⟨0, 0, 1, rfl⟩ (hfix 0 0 1 h0 h0 (one_pow _))
  have hgA := mem_radA1_of_commute (mem_antiUnipotent_of_commute h1'.symm h2'.symm) h3'
  refine ⟨g, hgA, ?_⟩
  have hΦ : (minorAut K ^ 2) ^ m = 1 := by
    refine sq_pow_eq_one fun t => ?_
    have hmem : ((minorAut K ^ 2) ^ m) (uElt 0 t 0 0) ∈ radA1 K := by
      rw [minorAut_sq_pow_uElt, h0]
      exact ⟨_, _, _, rfl⟩
    have ht := hα (uElt 0 t 0 0) ⟨t, 0, 0, rfl⟩
    rw [MulAut.mul_apply, MulAut.conj_apply, radA1_comm hgA hmem, mul_inv_cancel_right] at ht
    exact ht
  rw [hΦ, mul_one]

theorem exists_mem_radA2_eq_conj (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {α : MulAut (antiSp K)} (hα : ∀ a ∈ radA2 K, α a = a) :
    ∃ g ∈ radA2 K, α = MulAut.conj g := by
  obtain ⟨g, m, rfl⟩ := exists_eq_conj_mul_sq_pow hn hK (hα _ ⟨0, 0, 1, rfl⟩)
  have h0 : (0 : K) ^ 2 ^ m = 0 := zero_pow (pow_ne_zero m two_ne_zero)
  have hcomm : ∀ a ∈ radA2 K, ((minorAut K ^ 2) ^ m) a = a → g * a = a * g := by
    intro a ha hΦa
    have h1 := hα a ha
    rw [MulAut.mul_apply, hΦa, MulAut.conj_apply] at h1
    exact mul_inv_eq_iff_eq_mul.mp h1
  have hfix : ∀ a b c : K, a ^ 2 ^ m = a → b ^ 2 ^ m = b → c ^ 2 ^ m = c →
      ((minorAut K ^ 2) ^ m) (uElt a b c 0) = uElt a b c 0 := by
    intro a b c ha hb hc
    rw [minorAut_sq_pow_uElt, h0, ha, hb, hc]
  have h1' := hcomm _ ⟨0, 0, 1, rfl⟩ (hfix 0 0 1 h0 h0 (one_pow _))
  have h2' := hcomm _ ⟨0, 1, 0, rfl⟩ (hfix 0 1 0 h0 (one_pow _) h0)
  have h3' := hcomm _ ⟨1, 0, 0, rfl⟩ (hfix 1 0 0 (one_pow _) h0 h0)
  have hgA := mem_radA2_of_commute (mem_antiUnipotent_of_commute h1'.symm h2'.symm) h3'
  refine ⟨g, hgA, ?_⟩
  have hΦ : (minorAut K ^ 2) ^ m = 1 := by
    refine sq_pow_eq_one fun t => ?_
    have hmem : ((minorAut K ^ 2) ^ m) (uElt 0 t 0 0) ∈ radA2 K := by
      rw [minorAut_sq_pow_uElt, h0]
      exact ⟨_, _, _, rfl⟩
    have ht := hα (uElt 0 t 0 0) ⟨0, t, 0, rfl⟩
    rw [MulAut.mul_apply, MulAut.conj_apply, radA2_comm hgA hmem, mul_inv_cancel_right] at ht
    exact ht
  rw [hΦ, mul_one]

omit [Finite K] in
theorem centralizer_map_conj (A : Subgroup (antiSp K)) (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hA : ∀ α : MulAut (antiSp K), (∀ a ∈ A, α a = a) → ∃ g ∈ A, α = MulAut.conj g) :
    Subgroup.centralizer ((A.map MulAut.conj : Subgroup (MulAut (antiSp K))) :
      Set (MulAut (antiSp K))) = A.map MulAut.conj := by
  apply le_antisymm
  · intro α hα
    rw [Subgroup.mem_centralizer_iff] at hα
    obtain ⟨g, hg, rfl⟩ := hA α fun a ha => by
      have h1 : MulAut.conj a * α = α * MulAut.conj a := hα _ ⟨a, ha, rfl⟩
      apply conj_injective (K := K)
      rw [conj_apply_eq' α a, ← h1, mul_inv_cancel_right]
    exact ⟨g, hg, rfl⟩
  · rintro _ ⟨g, hg, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, ← map_mul, hAc a ha g hg]

theorem inf_inner_eq (R : Subgroup (MulAut (antiSp K))) (hR : IsPGroup 2 R)
    (hUR : (antiUnipotent K).map MulAut.conj ≤ R) :
    R ⊓ inner (antiSp K) = (antiUnipotent K).map MulAut.conj := by
  refine le_antisymm ?_ (le_inf hUR (Subgroup.map_le_range _ _))
  set W := (R ⊓ inner (antiSp K)).comap (MulAut.conj : antiSp K →* MulAut (antiSp K)) with hW
  have hWp : IsPGroup 2 W := (hR.to_le inf_le_left).comap_of_injective _ conj_injective
  have hUW : antiUnipotent K ≤ W := fun u hu =>
    ⟨hUR ⟨u, hu, rfl⟩, MonoidHom.mem_range.mpr ⟨u, rfl⟩⟩
  obtain ⟨-, -, hodd⟩ := (card_and_isSylowTwoOf_antiUnipotent (K := K)).2
  rw [show ((antiUnipotent K).subgroupOf ⊤).index = (antiUnipotent K).index from
    Subgroup.relIndex_top_right _] at hodd
  have hWU : W ≤ antiUnipotent K := by
    obtain ⟨k, hk⟩ := hWp.exists_card_eq
    have hdvd : (antiUnipotent K).relIndex W ∣ 2 ^ k := by
      rw [← hk]
      exact Subgroup.index_dvd_card _
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    rcases j with _ | j
    · exact Subgroup.relIndex_eq_one.mp (by rw [hj, pow_zero])
    · exfalso
      apply hodd
      rw [← Subgroup.relIndex_mul_index hUW, hj]
      exact Dvd.dvd.mul_right (dvd_pow_self 2 (Nat.succ_ne_zero j)) _
  rintro x ⟨hxR, hxi⟩
  obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hxi
  exact ⟨y, hWU ⟨hxR, MonoidHom.mem_range.mpr ⟨y, rfl⟩⟩, rfl⟩

theorem abelian_rank_bound (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (R : Subgroup (MulAut (antiSp K))) (hR : IsPGroup 2 R)
    (hUR : (antiUnipotent K).map MulAut.conj ≤ R) (A : Subgroup (MulAut (antiSp K)))
    (hAR : A ≤ R) [IsMulCommutative A] :
    Group.rank A ≤ 3 * n ∧ (Group.rank A = 3 * n →
      A = (radA1 K).map MulAut.conj ∨ A = (radA2 K).map MulAut.conj) := by
  obtain ⟨-, hcyc, -, hθ⟩ := even_symplectic_four_outer_involution_rank_and_perfect_residual hn hK
  have hn1 : 1 ≤ n := by omega
  have hAp : IsPGroup 2 A := hR.to_le hAR
  have hrE : 2 ^ Group.rank A ≤ Nat.card (omegaOneOf A) := two_pow_rank_le_card_omegaOneOf A hAp
  have hq3 : Nat.card K ^ 3 = 2 ^ (3 * n) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨-, ⟨-, -, hA1card⟩, ⟨-, -, hA2card⟩, -⟩ :=
    even_symplectic_four_Sylow_involution_radicals hK
  by_cases hEi : omegaOneOf A ≤ inner (antiSp K)
  · have hEU : omegaOneOf A ≤ (antiUnipotent K).map MulAut.conj := by
      rw [← inf_inner_eq R hR hUR]
      exact le_inf ((omegaOneOf_le A).trans hAR) hEi
    set E₀ := (omegaOneOf A).comap (MulAut.conj : antiSp K →* MulAut (antiSp K)) with hE₀
    have hE₀map : E₀.map MulAut.conj = omegaOneOf A := Subgroup.map_comap_eq_self hEi
    have hE₀card : Nat.card E₀ = Nat.card (omegaOneOf A) := by
      rw [← hE₀map, Subgroup.card_map_of_injective conj_injective]
    have hE₀U : E₀ ≤ antiUnipotent K := by
      intro y hy
      obtain ⟨u, hu, huy⟩ := hEU hy
      rwa [← conj_injective huy]
    have hE₀el : ∀ y ∈ E₀, y * y = 1 := fun y hy =>
      conj_injective (by rw [map_mul, map_one]; exact hy.2)
    have hcase : ∀ B : Subgroup (antiSp K), E₀ ≤ B → Nat.card B = 2 ^ (3 * n) →
        Subgroup.centralizer ((B.map MulAut.conj : Subgroup (MulAut (antiSp K))) :
          Set (MulAut (antiSp K))) = B.map MulAut.conj →
        Group.rank A ≤ 3 * n ∧ (Group.rank A = 3 * n → A = B.map MulAut.conj) := by
      intro B hE₀B hBcard hBcent
      have hle : Nat.card (omegaOneOf A) ≤ 2 ^ (3 * n) := by
        rw [← hE₀card, ← hBcard]
        exact Subgroup.card_le_of_le hE₀B
      refine ⟨(Nat.pow_le_pow_iff_right (by norm_num)).mp (hrE.trans hle), fun hr => ?_⟩
      have hEB : E₀ = B := Subgroup.eq_of_le_of_card_ge hE₀B
        (by rw [hBcard, hE₀card, ← hr]; exact hrE)
      have hEeq : omegaOneOf A = B.map MulAut.conj := by rw [← hE₀map, hEB]
      apply le_antisymm
      · rw [← hBcent, ← hEeq]
        intro a ha
        rw [Subgroup.mem_centralizer_iff]
        intro e he
        exact setLike_mul_comm (omegaOneOf_le A he) ha
      · rw [← hEeq]
        exact omegaOneOf_le A
    rcases elementary_le_radA1_or_radA2 hE₀U hE₀el with h1 | h1
    · obtain ⟨hr, hr'⟩ := hcase _ h1 (hA1card.trans hq3)
        (centralizer_map_conj _ (fun x hx y hy => radA1_comm hx hy)
          fun α hα => exists_mem_radA1_eq_conj hn1 hK hα)
      exact ⟨hr, fun h => Or.inl (hr' h)⟩
    · obtain ⟨hr, hr'⟩ := hcase _ h1 (hA2card.trans hq3)
        (centralizer_map_conj _ (fun x hx y hy => radA2_comm hx hy)
          fun α hα => exists_mem_radA2_eq_conj hn1 hK hα)
      exact ⟨hr, fun h => Or.inr (hr' h)⟩
  · obtain ⟨θ, hθE, hθi⟩ := IsConcreteLE.not_le_iff_exists.mp hEi
    obtain ⟨-, hbound, -⟩ := hθ θ hθE.2 hθi
    have := hcyc
    have h2E := card_le_two_mul_card_inf (inner (antiSp K)) (omegaOneOf A) (fun x hx => hx.2)
    set E₁ := (omegaOneOf A ⊓ inner (antiSp K)).comap
      (MulAut.conj : antiSp K →* MulAut (antiSp K)) with hE₁
    have hE₁card : Nat.card E₁ = Nat.card ↥(omegaOneOf A ⊓ inner (antiSp K)) := by
      rw [← Subgroup.card_map_of_injective conj_injective, hE₁,
        Subgroup.map_comap_eq_self (show omegaOneOf A ⊓ inner (antiSp K) ≤
          (MulAut.conj : antiSp K →* MulAut (antiSp K)).range from inf_le_right)]
    have hE₁fix : E₁ ≤ fixedSubgroup θ := by
      intro y hy
      have hc : θ * MulAut.conj y = MulAut.conj y * θ := setLike_mul_comm hθE.1 hy.1.1
      rw [mem_fixedSubgroup]
      apply conj_injective (K := K)
      rw [conj_apply_eq', hc, mul_inv_cancel_right]
    have hE₁el : ∀ y ∈ E₁, y * y = 1 := fun y hy =>
      conj_injective (by rw [map_mul, map_one]; exact hy.1.2)
    have hb := hbound E₁ hE₁fix hE₁el
    have hlt : (if Even n then 3 * (n / 2) else 2 * n) + 1 < 3 * n := by split_ifs <;> omega
    generalize (if Even n then 3 * (n / 2) else 2 * n) = b at hb hlt
    have hle : 2 ^ Group.rank A ≤ 2 ^ (b + 1) := by
      calc 2 ^ Group.rank A ≤ Nat.card (omegaOneOf A) := hrE
        _ ≤ 2 * Nat.card ↥(omegaOneOf A ⊓ inner (antiSp K)) := h2E
        _ = 2 * Nat.card E₁ := by rw [hE₁card]
        _ ≤ 2 * 2 ^ b := Nat.mul_le_mul_left 2 hb
        _ = 2 ^ (b + 1) := by rw [pow_succ, mul_comm]
    have hrb := (Nat.pow_le_pow_iff_right (by norm_num)).mp hle
    exact ⟨by omega, fun h => absurd h (by omega)⟩

end Model

end SymplecticFourRankThompson

open SymplecticFourRankThompson in
theorem even_symplectic_four_rank_Thompson_subgroup
    {K : Type} [Field K] [CharP K 2] [Finite K]
    {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) :
    Function.Injective (MulAut.conj : antiSp K →* MulAut (antiSp K)) ∧
    Subgroup.centralizer (((radA1 K).map MulAut.conj : Subgroup (MulAut (antiSp K))) :
        Set (MulAut (antiSp K))) = (radA1 K).map MulAut.conj ∧
    Subgroup.centralizer (((radA2 K).map MulAut.conj : Subgroup (MulAut (antiSp K))) :
        Set (MulAut (antiSp K))) = (radA2 K).map MulAut.conj ∧
    (∀ R : Subgroup (MulAut (antiSp K)), IsPGroup 2 R → (antiUnipotent K).map MulAut.conj ≤ R →
      (∀ A : Subgroup (MulAut (antiSp K)), A ≤ R → IsMulCommutative A →
        Group.rank A ≤ 3 * n ∧
          (Group.rank A = 3 * n ↔
            A = (radA1 K).map MulAut.conj ∨ A = (radA2 K).map MulAut.conj)) ∧
      maxAbelianRank R = 3 * n ∧
      (rankThompson R).map R.subtype = (antiUnipotent K).map MulAut.conj ∧
      (rankThompson R).Characteristic) ∧
    ∀ (G H : Type*) [Group G] [Finite G] [Group H] [Finite H] (e : G ≃* H),
      (rankThompson G).map e.toMonoidHom = rankThompson H := by
  have hn1 : 1 ≤ n := by omega
  have hq3 : Nat.card K ^ 3 = 2 ^ (3 * n) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨-, ⟨-, -, hA1card⟩, ⟨-, -, hA2card⟩, -⟩ :=
    even_symplectic_four_Sylow_involution_radicals hK
  have hA1c : IsMulCommutative (radA1 K) :=
    isMulCommutative_iff_of_setLike.mpr fun x hx y hy => radA1_comm hx hy
  have hA2c : IsMulCommutative (radA2 K) :=
    isMulCommutative_iff_of_setLike.mpr fun x hx y hy => radA2_comm hx hy
  have hC1 := centralizer_map_conj (radA1 K) (fun x hx y hy => radA1_comm hx hy)
    fun α hα => exists_mem_radA1_eq_conj hn1 hK hα
  have hC2 := centralizer_map_conj (radA2 K) (fun x hx y hy => radA2_comm hx hy)
    fun α hα => exists_mem_radA2_eq_conj hn1 hK hα
  have hrank1 : Group.rank ((radA1 K).map MulAut.conj) = 3 * n := by
    have h := two_pow_rank_eq_card_of_elementary ((radA1 K).map MulAut.conj) (by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_mul, mul_self_of_mem_radA1 hx, map_one])
    rw [Subgroup.card_map_of_injective conj_injective, hA1card, hq3] at h
    exact Nat.pow_right_injective le_rfl h
  have hrank2 : Group.rank ((radA2 K).map MulAut.conj) = 3 * n := by
    have h := two_pow_rank_eq_card_of_elementary ((radA2 K).map MulAut.conj) (by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_mul, mul_self_of_mem_radA2 hx, map_one])
    rw [Subgroup.card_map_of_injective conj_injective, hA2card, hq3] at h
    exact Nat.pow_right_injective le_rfl h
  refine ⟨conj_injective, hC1, hC2, fun R hR hUR => ?_, fun G H _ _ _ _ e => map_rankThompson e⟩
  have hA1R : (radA1 K).map MulAut.conj ≤ R :=
    (Subgroup.map_mono radA1_le_antiUnipotent).trans hUR
  have hA2R : (radA2 K).map MulAut.conj ≤ R :=
    (Subgroup.map_mono radA2_le_antiUnipotent).trans hUR
  have hiff : ∀ A : Subgroup (MulAut (antiSp K)), A ≤ R → IsMulCommutative A →
      Group.rank A ≤ 3 * n ∧
        (Group.rank A = 3 * n ↔
          A = (radA1 K).map MulAut.conj ∨ A = (radA2 K).map MulAut.conj) := by
    intro A hAR hA
    obtain ⟨h1, h2⟩ := abelian_rank_bound hn hK R hR hUR A hAR
    refine ⟨h1, h2, ?_⟩
    rintro (rfl | rfl)
    · exact hrank1
    · exact hrank2
  have hrankSub : ∀ B : Subgroup R, Group.rank (B.map R.subtype) = Group.rank B := fun B =>
    (Group.rank_congr (B.equivMapOfInjective R.subtype R.subtype_injective)).symm
  have hsubOf : ∀ A : Subgroup (MulAut (antiSp K)), A ≤ R →
      Group.rank (A.subgroupOf R) = Group.rank A :=
    fun A hAR => Group.rank_congr (Subgroup.subgroupOfEquivOfLe hAR)
  have hmax : maxAbelianRank R = 3 * n := by
    unfold maxAbelianRank
    refine IsGreatest.csSup_eq ⟨⟨((radA1 K).map MulAut.conj).subgroupOf R, inferInstance, by
      rw [hsubOf _ hA1R, hrank1]⟩, ?_⟩
    rintro r ⟨B, hB, rfl⟩
    rw [← hrankSub B]
    exact (hiff _ (Subgroup.map_subtype_le B) inferInstance).1
  refine ⟨hiff, hmax, ?_, rankThompson_characteristic⟩
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun B hB => ?_
    obtain ⟨hBc, hBr⟩ := hB
    rw [← Subgroup.map_le_iff_le_comap]
    have hr : Group.rank (B.map R.subtype) = 3 * n := by rw [hrankSub, hBr, hmax]
    rcases (hiff _ (Subgroup.map_subtype_le B) inferInstance).2.mp hr with h | h
    · rw [h]
      exact Subgroup.map_mono radA1_le_antiUnipotent
    · rw [h]
      exact Subgroup.map_mono radA2_le_antiUnipotent
  · rw [antiUnipotent_eq_radA1_sup_radA2, Subgroup.map_sup]
    have hmem : ∀ A : Subgroup (MulAut (antiSp K)), A ≤ R → IsMulCommutative A →
        Group.rank A = 3 * n → A ≤ (rankThompson R).map R.subtype := by
      intro A hAR hA hAr
      have hfam : A.subgroupOf R ∈ maxRankAbelianFamily R :=
        ⟨inferInstance, by rw [hsubOf A hAR, hAr, hmax]⟩
      calc A = (A.subgroupOf R).map R.subtype := by
            rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hAR]
        _ ≤ _ := Subgroup.map_mono (le_sSup hfam)
    exact sup_le (hmem _ hA1R inferInstance hrank1) (hmem _ hA2R inferInstance hrank2)

end CFSG.LocalAnalysis
