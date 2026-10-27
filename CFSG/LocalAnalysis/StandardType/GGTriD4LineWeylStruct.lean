module

public import CFSG.LocalAnalysis.StandardType.GGTriD4LineWeylData
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestTri
public import CFSG.LieType.Chevalley.EvenTrialityAutomorphismNormalForm
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTriality
import CFSG.LocalAnalysis.StandardType.GGTriD4NoneAutRank
import CFSG.LocalAnalysis.StandardType.GGL45FixA2Arith
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem triD4Line_center_bot
    {n : ℕ} (hn : 1 ≤ n) (K : Type) [Field K] (hK : Nat.card K = (2 ^ n) ^ 3) :
    Subgroup.center (GGTriD4R n K) = ⊥ := by
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have hchar : CharP K 2 := charP_two_of_card (m := n * 3) (by rw [hK, pow_mul])
  set σ := iterateFrobeniusEquiv K 2 n with hσdef
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => by
    rw [hσdef, iterateFrobeniusEquiv_apply, iterateFrobenius_def]
  obtain ⟨e⟩ := TableBExcSmallRest.nonempty_triD4_equiv hn K hK σ hσ
  obtain ⟨-, -, -, -, -, -, hZC, -⟩ := even_triality_exact_automorphism_normal_form hn K hK σ hσ
  exact TableBExcSmallRest.center_eq_bot_of_mulEquiv e hZC

theorem triD4Line_E_isElemAbelian {n : ℕ} (K : Type) [Field K]
    (hZ : Subgroup.center (GGTriD4R n K) = ⊥) (A : Subgroup (MulAut (GGTriD4R n K)))
    (hA : IsElemAbelian 3 A) : IsElemAbelian 3 (triD4LineE n K A) := by
  exact CFSG.Open.IsElemAbelian.comap hA (conj_injective_of_center_eq_bot hZ)

theorem triD4Line_conj_mem_zpowers_iff {n : ℕ} (K : Type) [Field K]
    (hZ : Subgroup.center (GGTriD4R n K) = ⊥) (x e : GGTriD4R n K) :
    MulAut.conj x ∈ Subgroup.zpowers (MulAut.conj e) ↔ x ∈ Subgroup.zpowers e := by
  rw [Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, conj_injective_of_center_eq_bot hZ (by rw [map_zpow, hk])⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [← map_zpow, hk]⟩

theorem triD4Line_E_map_conj {n : ℕ} (K : Type) [Field K] (g : GGTriD4R n K)
    (A : Subgroup (MulAut (GGTriD4R n K))) :
    triD4LineE n K (A.map (MulAut.conj (MulAut.conj g)).toMonoidHom) =
      (triD4LineE n K A).map (MulAut.conj g).toMonoidHom := by
  have hrel : ∀ x : GGTriD4R n K,
      (MulAut.conj (MulAut.conj g)) (MulAut.conj x)
        = MulAut.conj ((MulAut.conj g) x) := by
    intro x
    rw [MulAut.conj_apply, MulAut.conj_apply]
    rw [map_mul, map_mul, map_inv]
  ext y
  constructor
  · intro hy
    change MulAut.conj y ∈ A.map (MulAut.conj (MulAut.conj g)).toMonoidHom at hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨a, ha, hφa⟩ := hy
    refine ⟨(MulAut.conj g)⁻¹ y, ?_, ?_⟩
    · change MulAut.conj ((MulAut.conj g)⁻¹ y) ∈ A
      have h1 : (MulAut.conj (MulAut.conj g)) (MulAut.conj ((MulAut.conj g)⁻¹ y))
          = MulAut.conj y := by
        rw [hrel]
        congr 1
        rw [MulAut.inv_apply]
        exact MulEquiv.apply_symm_apply (MulAut.conj g) y
      have h2 : (MulAut.conj (MulAut.conj g)) a = MulAut.conj y := hφa
      have hcb : MulAut.conj ((MulAut.conj g)⁻¹ y) = a :=
        (MulAut.conj (MulAut.conj g)).injective (h1.trans h2.symm)
      rw [hcb]
      exact ha
    · change (MulAut.conj g) ((MulAut.conj g)⁻¹ y) = y
      rw [MulAut.inv_apply]
      exact MulEquiv.apply_symm_apply (MulAut.conj g) y
  · rintro ⟨b, hb, hby⟩
    change MulAut.conj b ∈ A at hb
    change MulAut.conj y ∈ A.map (MulAut.conj (MulAut.conj g)).toMonoidHom
    rw [Subgroup.mem_map]
    refine ⟨MulAut.conj b, hb, ?_⟩
    change (MulAut.conj (MulAut.conj g)) (MulAut.conj b) = MulAut.conj y
    rw [hrel b]
    simpa using congrArg MulAut.conj hby

private lemma triD4Line_conj_mul_conj {R : Type*} [Group R] (β : MulAut R) (e : R) :
    β * MulAut.conj e * β⁻¹ = MulAut.conj (β e) := by
  ext r
  simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_apply, map_mul, map_inv,
    MulEquiv.apply_symm_apply]

private lemma triD4Line_pow_mul_inv {R : Type*} [Group R] (f : MulAut R) (m : R)
    (hf : f (m * (f m)⁻¹) = m * (f m)⁻¹) (j : ℕ) :
    (m * (f m)⁻¹) ^ j = m * ((f ^ j) m)⁻¹ := by
  have hfuj : ∀ k : ℕ, (f ^ k) (m * (f m)⁻¹) = m * (f m)⁻¹ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, MulAut.mul_apply, hf, ih]
  induction j with
  | zero => simp
  | succ j ih =>
      rw [pow_succ, ih, ← hfuj j, map_mul, map_inv]
      have hfm : (f ^ j) (f m) = (f ^ (j + 1)) m := by
        rw [← MulAut.mul_apply, ← pow_succ]
      rw [hfm]
      group

private theorem triD4Line_R_rank_le
    {n : ℕ} (hn : 1 ≤ n) (h3 : 3 ∣ 2 ^ n - 1) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 3) :
    ∀ E : Subgroup (GGTriD4R n K), IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 2 := by
  have : CharP K 2 := charP_two_of_card (m := n * 3) (by rw [hK, pow_mul])
  set σ := iterateFrobeniusEquiv K 2 n with hσdef
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => by
    rw [hσdef, iterateFrobeniusEquiv_apply, iterateFrobenius_def]
  obtain ⟨e⟩ := TableBExcSmallRest.nonempty_triD4_equiv hn K hK σ hσ
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have : Finite (GGTriD4R n K) := Finite.of_equiv _ e.symm.toEquiv
  intro E hE
  have h1 := TableBExcSmallRanks.ggTriD4ThreeRankInput_holds n hn (Or.inl h3) K hK σ hσ
    (E.map e.toMonoidHom) (CFSG.Open.IsElemAbelian.map hE e.toMonoidHom)
  rw [Subgroup.card_map_of_injective e.injective] at h1
  obtain ⟨k, hk⟩ := (CFSG.Open.IsElemAbelian.isPGroup hE).exists_card_eq
  rw [hk] at h1 ⊢
  exact Nat.pow_le_pow_right (by norm_num)
    (Nat.lt_succ_iff.mp ((Nat.pow_lt_pow_iff_right (by norm_num)).mp h1))

private theorem triD4Line_E_card_and_gens {R : Type} [Group R] [Finite R]
    (hZ : Subgroup.center R = ⊥) (hOut : GGOutCyclic R)
    (hR : ∀ E : Subgroup R, IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 2)
    (A : Subgroup (MulAut R)) (hA : IsElemAbelian 3 A) (h27 : 27 ≤ Nat.card A) :
    Nat.card (A.comap (MulAut.conj : R →* MulAut R)) = 9 ∧
      ∃ f ∈ A, f ∉ Set.range (MulAut.conj : R →* MulAut R) ∧ f ^ 3 = 1 ∧
        ∀ a ∈ A, ∃ e ∈ A.comap (MulAut.conj : R →* MulAut R), ∃ j : ℕ,
          a = MulAut.conj e * f ^ j := by
  classical
  haveI : ((MulAut.conj : R →* MulAut R).range).Normal := normal_range_conj_mulAut
  set Inn : Subgroup (MulAut R) := (MulAut.conj : R →* MulAut R).range with hInn
  let π : A →* MulAut R ⧸ Inn := (QuotientGroup.mk' Inn).comp A.subtype
  obtain ⟨φ₀, hφ₀⟩ := hOut
  haveI hcyc : IsCyclic (MulAut R ⧸ Inn) := by
    refine ⟨⟨QuotientGroup.mk φ₀, fun q => ?_⟩⟩
    obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨i, hi, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 (hφ₀ α)
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff i).2 hi, one_mul, QuotientGroup.mk_zpow]
  haveI : Finite π.range := Finite.of_surjective _ π.rangeRestrict_surjective
  have hrange_le : Nat.card π.range ≤ 3 := by
    refine TableB.card_le_of_isCyclic (by norm_num) (Subgroup.isCyclic π.range) ?_
    rintro _ ⟨a, rfl⟩
    rw [← map_pow]
    have : a ^ 3 = 1 := Subtype.ext (by simpa using hA.2 a a.2)
    rw [this, map_one]
  have hinj : Function.Injective (MulAut.conj : R →* MulAut R) :=
    conj_injective_of_center_eq_bot hZ
  have hk : π.ker = (A ⊓ Inn).subgroupOf A := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    change (QuotientGroup.mk (a : MulAut R) : MulAut R ⧸ Inn) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    exact ⟨fun h => ⟨a.2, h⟩, fun h => h.2⟩
  have hEmap : (A.comap (MulAut.conj : R →* MulAut R)).map (MulAut.conj : R →* MulAut R)
      = A ⊓ Inn := by
    rw [Subgroup.map_comap_eq, ← hInn, inf_comm]
  have hEab : IsElemAbelian 3 (A.comap (MulAut.conj : R →* MulAut R)) :=
    CFSG.Open.IsElemAbelian.comap hA hinj
  have hEcard : Nat.card (A.comap (MulAut.conj : R →* MulAut R)) = Nat.card π.ker := by
    rw [hk, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : A ⊓ Inn ≤ A)).toEquiv,
      ← hEmap]
    exact (Subgroup.card_map_of_injective hinj).symm
  have hker_le : Nat.card π.ker ≤ 3 ^ 2 := by
    rw [← hEcard]
    exact hR _ hEab
  have hprod : Nat.card A = Nat.card π.range * Nat.card π.ker :=
    (TableB.card_range_mul_card_ker π).symm
  have hAeq : Nat.card A = 27 := by
    have hle : Nat.card A ≤ 27 := by
      rw [hprod]
      calc Nat.card π.range * Nat.card π.ker ≤ 3 * 9 := Nat.mul_le_mul hrange_le hker_le
        _ = 27 := by norm_num
    omega
  have hker9 : Nat.card π.ker = 9 := by
    have h1 : 27 ≤ 3 * Nat.card π.ker := by
      calc 27 = Nat.card A := hAeq.symm
        _ = Nat.card π.range * Nat.card π.ker := hprod
        _ ≤ 3 * Nat.card π.ker := Nat.mul_le_mul_right _ hrange_le
    omega
  have hrange3 : Nat.card π.range = 3 := by
    rw [hker9] at hprod
    omega
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hexists : ∃ a : A, π a ≠ 1 := by
    by_contra h
    have hbot : π.range = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨a, rfl⟩
      exact Subgroup.mem_bot.mpr (not_not.mp (fun hne => h ⟨a, hne⟩))
    rw [hbot] at hrange3
    simp at hrange3
  obtain ⟨a, ha⟩ := hexists
  have ha3 : a ^ 3 = 1 := Subtype.ext (by simpa using hA.2 (a : MulAut R) a.2)
  have horder : orderOf (π a) = 3 := by
    refine orderOf_eq_prime ?_ ha
    rw [← map_pow, ha3, map_one]
  have hzpow : Subgroup.zpowers (π a) = π.range := by
    refine Subgroup.eq_of_le_of_card_ge
      (Subgroup.zpowers_le.mpr (show π a ∈ π.range from ⟨a, rfl⟩)) ?_
    rw [Nat.card_zpowers, horder, hrange3]
  refine ⟨?_, (a : MulAut R), a.2, ?_, hA.2 _ a.2, ?_⟩
  · rw [hEcard, hker9]
  · intro hf
    apply ha
    change (↑(a : MulAut R) : MulAut R ⧸ Inn) = 1
    rw [QuotientGroup.eq_one_iff, hInn]
    exact hf
  · intro a' ha'
    have hmem : π ⟨a', ha'⟩ ∈ Subgroup.zpowers (π a) := by
      rw [hzpow]
      exact ⟨⟨a', ha'⟩, rfl⟩
    obtain ⟨k, hk'⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hk3 : (π a) ^ 3 = 1 := by
      rw [← map_pow, ha3, map_one]
    set j : ℕ := (k % 3).toNat with hjdef
    have hkey : (π a) ^ j = π ⟨a', ha'⟩ := by
      rw [hjdef, ← zpow_natCast,
        Int.toNat_of_nonneg (Int.emod_nonneg k (by norm_num : (3 : ℤ) ≠ 0))]
      exact (zpow_eq_zpow_emod' k hk3).symm.trans hk'
    have hmemker : (⟨a', ha'⟩ : A) * (a ^ j)⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_pow, hkey, mul_inv_cancel]
    have hmeminf : a' * ((a : MulAut R) ^ j)⁻¹ ∈ A ⊓ Inn := by
      rw [hk] at hmemker
      rw [Subgroup.mem_subgroupOf] at hmemker
      simpa using hmemker
    rw [← hEmap] at hmeminf
    obtain ⟨e, he, hee⟩ := Subgroup.mem_map.mp hmeminf
    exact ⟨e, he, j, by rw [hee]; group⟩

theorem triD4Line_A_structure
    {n : ℕ} (hn : 1 ≤ n) (hev : Even n) (K : Type) [Field K] (hK : Nat.card K = (2 ^ n) ^ 3)
    (A : Subgroup (MulAut (GGTriD4R n K))) (hA : IsElemAbelian 3 A) (h27 : 27 ≤ Nat.card A) :
    Nat.card (triD4LineE n K A) = 9 ∧
      ∃ f ∈ A, f ∉ Set.range (MulAut.conj : GGTriD4R n K →* MulAut (GGTriD4R n K)) ∧
        f ^ 3 = 1 ∧ ∀ a ∈ A, ∃ e ∈ triD4LineE n K A, ∃ j : ℕ, a = MulAut.conj e * f ^ j := by
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K 2 := charP_two_of_card (m := n * 3) (by rw [hK, pow_mul])
  set σ := iterateFrobeniusEquiv K 2 n with hσdef
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => by
    rw [hσdef, iterateFrobeniusEquiv_apply, iterateFrobenius_def]
  obtain ⟨e⟩ := TableBExcSmallRest.nonempty_triD4_equiv hn K hK σ hσ
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  haveI : Finite (GGTriD4R n K) := Finite.of_equiv _ e.symm.toEquiv
  have hZ : Subgroup.center (GGTriD4R n K) = ⊥ := triD4Line_center_bot hn K hK
  have hOut : GGOutCyclic (GGTriD4R n K) := ggOutCyclic_triD4 hn K hK
  have h3 : 3 ∣ 2 ^ n - 1 := (gffa2_three_dvd_pow_sub_one_iff n).mpr hev
  have hR := triD4Line_R_rank_le hn h3 K hK
  exact triD4Line_E_card_and_gens hZ hOut hR A hA h27

theorem triD4Line_clause_of_gens {n : ℕ} (K : Type) [Field K]
    (hZ : Subgroup.center (GGTriD4R n K) = ⊥) (A : Subgroup (MulAut (GGTriD4R n K)))
    (hA : IsElemAbelian 3 A) (f : MulAut (GGTriD4R n K)) (hfA : f ∈ A)
    (hdec : ∀ a ∈ A, ∃ e ∈ triD4LineE n K A, ∃ j : ℕ, a = MulAut.conj e * f ^ j)
    (m : GGTriD4R n K) (hm : ∀ e ∈ triD4LineE n K A, m * e * m⁻¹ ∈ triD4LineE n K A)
    (hmf : m * (f m)⁻¹ ∈ triD4LineE n K A) :
    ∀ a ∈ A, (m * (a m)⁻¹) ^ 3 = 1 ∧ ∀ a' ∈ A, a' (m * (a m)⁻¹) = m * (a m)⁻¹ := by
  have hE : IsElemAbelian 3 (triD4LineE n K A) := triD4Line_E_isElemAbelian K hZ A hA
  have hfix : ∀ a' ∈ A, ∀ e ∈ triD4LineE n K A, a' e = e := by
    intro a' ha' e he
    have h1 : a' * MulAut.conj e * a'⁻¹ = MulAut.conj e := by
      rw [CFSG.Open.IsElemAbelian.comm hA ha' (mem_triD4LineE.mp he)]
      group
    have h2 : a' * MulAut.conj e * a'⁻¹ = MulAut.conj (a' e) :=
      triD4Line_conj_mul_conj a' e
    exact conj_injective_of_center_eq_bot hZ (by rw [← h2, h1])
  intro a ha
  obtain ⟨e, he, j, rfl⟩ := hdec a ha
  have htele := triD4Line_pow_mul_inv f m (hfix f hfA _ hmf) j
  have hxeq : m * (((MulAut.conj e) * f ^ j) m)⁻¹
      = (m * e * m⁻¹) * (m * ((f ^ j) m)⁻¹) * e⁻¹ := by
    rw [MulAut.mul_apply, MulAut.conj_apply]
    group
  have hxmem : m * (((MulAut.conj e) * f ^ j) m)⁻¹ ∈ triD4LineE n K A := by
    rw [hxeq]
    have hme : m * e * m⁻¹ ∈ triD4LineE n K A := hm e he
    have hu : m * ((f ^ j) m)⁻¹ ∈ triD4LineE n K A := by
      rw [← htele]
      exact Subgroup.pow_mem _ hmf j
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hme hu) (Subgroup.inv_mem _ he)
  exact ⟨hE.2 _ hxmem, fun a' ha' => hfix a' ha' _ hxmem⟩

end CFSG.StandardType
