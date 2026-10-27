module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection9.theorem_9_1
import Mathlib.GroupTheory.Schreier
import Mathlib.GroupTheory.Subgroup.Centralizer

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# Corollary 9.2 from BG Section 9

This file contains the support package and proof of Corollary 9.2 from `docs/section9.tex`.
-/

section Section9

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

public theorem CFSG.section9_c92_generatorRank_le_natCard
    (R : Type*) [Group R] [Finite R] :
    generatorRank R ≤ Nat.card R := by
  letI : Fintype R := Fintype.ofFinite R
  obtain ⟨S, hS_card, _hS_top⟩ := Group.rank_spec R
  calc
    generatorRank R = Group.rank R := generatorRank_eq_group_rank R
    _ = S.card := by rw [← hS_card]
    _ ≤ Fintype.card R := by simpa using Finset.card_le_univ S
    _ = Nat.card R := by simp [Nat.card_eq_fintype_card]

public theorem CFSG.section9_c92_primeRank_le_natCard
    {p : ℕ} (R : Type*) [Group R] [Finite R] :
    primeRank p R ≤ Nat.card R := by
  rw [primeRank]
  refine csSup_le ?_ ?_
  · exact ⟨0, ⊥, IsPGroup.of_bot (p := p) (G := R), inferInstance, Nat.zero_le _⟩
  · intro n hn
    rcases hn with ⟨A, _hApA, _hAcomm, hnA⟩
    exact hnA.trans <|
      (section9_c92_generatorRank_le_natCard A).trans (Subgroup.card_le_card_group A)

private theorem CFSG.section9_c92_exists_pSubgroup_two_le_generatorRank_of_two_le_groupRank
    {R : Type*} [Group R] [Finite R] (hrank : 2 ≤ groupRank R) :
    ∃ p : Nat.Primes, ∃ A : Subgroup R,
      IsPGroup p.val A ∧ IsMulCommutative A ∧ 2 ≤ generatorRank A := by
  let S : Set ℕ := {n : ℕ | ∃ q : ℕ, Nat.Prime q ∧ n ≤ primeRank q R}
  have hrank' : 1 < sSup S := by
    exact lt_of_lt_of_le (by decide : 1 < 2) (by simpa [groupRank, S] using hrank)
  have hSbdd : BddAbove S := by
    refine ⟨Nat.card R, ?_⟩
    intro n hn
    rcases hn with ⟨q, _hqprime, hnq⟩
    exact hnq.trans (section9_c92_primeRank_le_natCard (p := q) R)
  have hSnonempty : S.Nonempty := by
    by_contra hS
    have hSempty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
    have : ¬ 1 < sSup S := by simp [hSempty]
    exact this hrank'
  have hsSup_mem : sSup S ∈ S := Nat.sSup_mem hSnonempty hSbdd
  rcases hsSup_mem with ⟨q, hqprime, hsSup_le⟩
  have hqrank : 1 < primeRank q R := lt_of_lt_of_le hrank' hsSup_le
  let T : Set ℕ :=
    {n : ℕ | ∃ A : Subgroup R, IsPGroup q A ∧ IsMulCommutative A ∧ n ≤ generatorRank A}
  have hqrank' : 1 < sSup T := by
    simpa [primeRank, T] using hqrank
  have hTbdd : BddAbove T := by
    refine ⟨Nat.card R, ?_⟩
    intro n hn
    rcases hn with ⟨A, _hAq, _hAcomm, hnA⟩
    exact hnA.trans <|
      (section9_c92_generatorRank_le_natCard A).trans (Subgroup.card_le_card_group A)
  have hTnonempty : T.Nonempty := by
    by_contra hT
    have hTempty : T = ∅ := Set.not_nonempty_iff_eq_empty.mp hT
    have : ¬ 1 < sSup T := by simp [hTempty]
    exact this hqrank'
  have htSup_mem : sSup T ∈ T := Nat.sSup_mem hTnonempty hTbdd
  rcases htSup_mem with ⟨A, hAq, hAcomm, htSup_le⟩
  exact ⟨⟨q, hqprime⟩, A, hAq, hAcomm,
    Nat.succ_le_of_lt (lt_of_lt_of_le hqrank' htSup_le)⟩

public theorem CFSG.section9_c92_elementaryAbelian_card_ge_pow_generatorRank
    {p : ℕ} [Fact p.Prime]
    (R : Type*) [Group R] [Finite R] [IsElementaryAbelian p R] :
    p ^ generatorRank R ≤ Nat.card R := by
  letI : CommGroup R := IsMulCommutative.instCommGroup
  letI : AddCommGroup (Additive R) := Additive.addCommGroup
  have hcard : Nat.card R = p ^ Module.finrank (ZMod p) (Additive R) := by
    calc
      Nat.card R = Nat.card (Additive R) := (Nat.card_congr Additive.toMul).symm
      _ = p ^ Module.finrank (ZMod p) (Additive R) := by
        simpa using Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive R)
  have hgr_le_finrank : generatorRank R ≤ Module.finrank (ZMod p) (Additive R) :=
    generatorRank_le_finrank_of_elementaryAbelian (p := p) R
  rw [hcard]
  exact Nat.pow_le_pow_right (Nat.Prime.pos (Fact.out : Nat.Prime p)) hgr_le_finrank

public theorem CFSG.section9_c92_omega1_isElementaryAbelian_of_commutative
    {p : ℕ} [Fact p.Prime]
    (R : Type*) [Group R] [IsMulCommutative R] :
    IsElementaryAbelian p (omega₁ (G := R) (p := p)) := by
  letI : CommGroup R := IsMulCommutative.instCommGroup
  refine
    { toIsMulCommutative := by infer_instance
      exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
  intro x
  apply Subtype.ext
  exact
    Subgroup.closure_induction (k := {y : R | y ^ (p ^ 1) = 1})
      (p := fun z _hz => z ^ p = 1) (x := x) (by
        intro y hy
        simpa [pow_one] using hy) (by simp) (by
        intro y z _ _ hy hz
        calc
          (y * z) ^ p = y ^ p * z ^ p := by
            simpa using mul_pow y z p
          _ = 1 := by simp [hy, hz]) (by
        intro y _ hy
        simp [hy]) x.property

public theorem CFSG.section9_c92_omega1_card_eq_card_quotient_frattini_of_commutative
    {p : ℕ} [Fact p.Prime]
    (R : Type*) [Group R] [Finite R] [IsMulCommutative R] [Fact (IsPGroup p R)] :
    Nat.card (omega₁ (G := R) (p := p)) = Nat.card (R ⧸ frattini R) := by
  classical
  letI : CommGroup R := IsMulCommutative.instCommGroup
  let φ : R →* R := powMonoidHom p
  have hφker : φ.ker = omega₁ (G := R) (p := p) := by
    ext x
    constructor
    · intro hx
      change x ∈ Subgroup.closure {y : R | y ^ (p ^ 1) = 1}
      refine Subgroup.subset_closure ?_
      simpa [φ, pow_one] using hx
    · intro hx
      refine
        Subgroup.closure_induction (k := {y : R | y ^ (p ^ 1) = 1})
          (p := fun z _hz => z ∈ φ.ker) (x := x) (by
            intro y hy
            simpa [φ, pow_one] using hy) (by simp [φ]) (by
            intro y z _ _ hy hz
            have hy' : y ^ p = 1 := by simpa [φ] using hy
            have hz' : z ^ p = 1 := by simpa [φ] using hz
            simp [φ, mul_pow, hy', hz']) (by
            intro y _ hy
            exact φ.ker.inv_mem hy) hx
  have hφrange : φ.range = frattini R := by
    have hcomm_top :
        (⊤ : Subgroup R) ≤ Subgroup.centralizer (((⊤ : Subgroup R) : Set R)) := by
      intro x _hx
      rw [Subgroup.mem_centralizer_iff]
      intro y _hy
      exact mul_comm y x
    have hcomm_bot : _root_.commutator R = ⊥ := by
      have htop_comm_bot : ⁅(⊤ : Subgroup R), (⊤ : Subgroup R)⁆ = ⊥ :=
        (Subgroup.commutator_eq_bot_iff_le_centralizer).2 hcomm_top
      simpa [_root_.commutator_def] using htop_comm_bot
    have hderived_bot : derivedSubgroup R = ⊥ := by
      change derivedSeries R 1 = ⊥
      rw [derivedSeries_one]
      exact hcomm_bot
    have hrange :
        Set.range (fun x : R => x ^ p) = ((φ.range : Subgroup R) : Set R) := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨x, by simp [φ]⟩
      · rintro ⟨x, hx⟩
        exact ⟨x, by simpa [φ] using hx⟩
    have hfrattini : frattini R = φ.range := by
      calc
        frattini R =
            Subgroup.closure ((derivedSubgroup R : Set R) ∪ Set.range (fun x : R => x ^ p)) := by
              simpa using (lemma_1_7_d (R := R) (p := p))
        _ = Subgroup.closure (Set.range (fun x : R => x ^ p)) := by
              rw [hderived_bot]
              simp
        _ = Subgroup.closure ((φ.range : Subgroup R) : Set R) := by rw [hrange]
        _ = φ.range := by simpa using (Subgroup.closure_eq (K := φ.range))
    exact hfrattini.symm
  have hcard_range :
      Nat.card (R ⧸ φ.ker) = Nat.card φ.range := by
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
  have hmul_ker :
      Nat.card R = Nat.card (frattini R) * Nat.card (omega₁ (G := R) (p := p)) := by
    calc
      Nat.card R = Nat.card (R ⧸ φ.ker) * Nat.card φ.ker :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup (s := φ.ker)
      _ = Nat.card φ.range * Nat.card φ.ker := by rw [hcard_range]
      _ = Nat.card (frattini R) * Nat.card (omega₁ (G := R) (p := p)) := by
        rw [hφrange, hφker]
  have hmul_frattini :
      Nat.card R = Nat.card (frattini R) * Nat.card (R ⧸ frattini R) := by
    calc
      Nat.card R = Nat.card (R ⧸ frattini R) * Nat.card (frattini R) :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup (s := frattini R)
      _ = Nat.card (frattini R) * Nat.card (R ⧸ frattini R) := by
        rw [Nat.mul_comm]
  have hΦpos : 0 < Nat.card (frattini R) := Nat.card_pos (α := frattini R)
  have hmul_eq :
      Nat.card (frattini R) * Nat.card (omega₁ (G := R) (p := p)) =
        Nat.card (frattini R) * Nat.card (R ⧸ frattini R) :=
    hmul_ker.symm.trans hmul_frattini
  exact Nat.eq_of_mul_eq_mul_left hΦpos hmul_eq

public theorem CFSG.section9_c92_isElementaryAbelian_of_le
    {p : ℕ} [Fact p.Prime]
    {R : Type*} [Group R] {H K : Subgroup R}
    [IsElementaryAbelian p K] (hHK : H ≤ K) :
    IsElementaryAbelian p H := by
  refine
    { toIsMulCommutative := by
        exact
          { is_comm := ⟨fun x y =>
              Subtype.ext <|
                setLike_mul_comm (s := K)
                  (hHK x.2) (hHK y.2)⟩ }
      exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
  intro x
  apply Subtype.ext
  let xK : K := ⟨(x : R), hHK x.2⟩
  have hxpow : xK ^ p = 1 := by
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p K) xK
  simpa [xK] using congrArg Subtype.val hxpow

public theorem CFSG.section9_c92_isElementaryAbelian_map_of_injective
    {p : ℕ} [Fact p.Prime]
    {R S : Type*} [Group R] [Group S] {A : Subgroup R}
    [IsElementaryAbelian p A] (f : R →* S) :
    IsElementaryAbelian p (A.map f) := by
  refine
    { toIsMulCommutative := by
        simpa using (Subgroup.map_isMulCommutative (f := f) (H := A))
      exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
  intro x
  apply Subtype.ext
  rcases Subgroup.mem_map.mp x.2 with ⟨y, hyA, hyx⟩
  let yA : A := ⟨y, hyA⟩
  have hypow : yA ^ p = 1 := by
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p A) yA
  have hx_eq : (x : S) = f y := by simpa using hyx.symm
  calc
    (x : S) ^ p = (f y) ^ p := by simp [hx_eq]
    _ = f (y ^ p) := by simp
    _ = 1 := by simpa using congrArg f (congrArg Subtype.val hypow)

public theorem CFSG.section9_c92_generatorRank_map_injective_eq
    {R S : Type*} [Group R] [Finite R] [Group S] [Finite S]
    (A : Subgroup R) (f : R →* S) (hf : Function.Injective f) :
    generatorRank (A.map f) = generatorRank A := by
  rw [generatorRank_eq_group_rank, generatorRank_eq_group_rank]
  let e : A ≃* A.map f := Subgroup.equivMapOfInjective (f := f) A hf
  exact (Group.rank_congr e).symm

public theorem CFSG.section9_c92_generatorRank_at_least_two_of_elementaryAbelian_card_p_sq
    {p : ℕ} [Fact p.Prime] {A : Type*} [Group A] [Finite A]
    [IsElementaryAbelian p A] (hA : Nat.card A = p ^ 2) :
    2 ≤ generatorRank A := by
  letI : CommGroup A := IsMulCommutative.instCommGroup
  have hcard_dvd : Nat.card A ∣ p ^ Group.rank A := by
    simpa using card_dvd_exponent_pow_rank' (G := A) (n := p) (fun a =>
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (show Monoid.exponent A ∣ p by simpa using IsElementaryAbelian.exponent_dvd_p p A) a)
  rw [hA] at hcard_dvd
  have hle_rank : 2 ≤ Group.rank A := by
    exact (Nat.pow_dvd_pow_iff_le_right (Nat.Prime.one_lt (Fact.out : Nat.Prime p))).mp hcard_dvd
  simpa [generatorRank_eq_group_rank] using hle_rank

omit [IsMinCE G] in
private theorem CFSG.section9_c92_exists_elementaryAbelian_noncyclic_subgroup_of_two_le_groupRank
    {K : Subgroup G} (hKrank : 2 ≤ groupRank K) :
    ∃ p : ℕ, p.Prime ∧ ∃ B : Subgroup G,
      B ≤ K ∧ IsElementaryAbelian p B ∧ ¬ IsCyclic B := by
  classical
  obtain ⟨p0, A0, hA0p, hA0comm, hA0gen⟩ :=
    section9_c92_exists_pSubgroup_two_le_generatorRank_of_two_le_groupRank (R := K) hKrank
  let p : ℕ := p0.val
  have hp : p.Prime := p0.property
  letI : Fact p.Prime := ⟨hp⟩
  let Ωsub : Subgroup A0 := omega₁ (G := A0) (p := p)
  haveI : Fact (IsPGroup p A0) := ⟨hA0p⟩
  have hΩelem : IsElementaryAbelian p Ωsub := by
    letI : IsMulCommutative A0 := hA0comm
    simpa [Ωsub] using section9_c92_omega1_isElementaryAbelian_of_commutative (p := p) A0
  have hΩcard :
      Nat.card Ωsub = Nat.card (A0 ⧸ frattini A0) := by
    letI : IsMulCommutative A0 := hA0comm
    simpa [Ωsub] using
      section9_c92_omega1_card_eq_card_quotient_frattini_of_commutative (p := p) A0
  have hquot_rank : 2 ≤ generatorRank (A0 ⧸ frattini A0) :=
    hA0gen.trans (generatorRank_le_generatorRank_quotient_frattini (p := p) A0)
  have hpow_le_quot : p ^ 2 ≤ Nat.card (A0 ⧸ frattini A0) := by
    letI : IsElementaryAbelian p (A0 ⧸ frattini A0) :=
      isElementaryAbelian_quotient_frattini (R := A0) (p := p)
    calc
      p ^ 2 ≤ p ^ generatorRank (A0 ⧸ frattini A0) := by
        exact Nat.pow_le_pow_right (Nat.Prime.pos (Fact.out : Nat.Prime p)) hquot_rank
      _ ≤ Nat.card (A0 ⧸ frattini A0) := by
        exact section9_c92_elementaryAbelian_card_ge_pow_generatorRank
          (p := p) (A0 ⧸ frattini A0)
  have hpow_le_Ω : p ^ 2 ≤ Nat.card Ωsub := by
    rw [hΩcard]
    exact hpow_le_quot
  have hΩp : IsPGroup p Ωsub := IsElementaryAbelian.isPGroup p Ωsub
  rcases hΩp.exists_card_eq with ⟨k, hk⟩
  have hk2 : 2 ≤ k := by
    rw [hk] at hpow_le_Ω
    exact
      (Nat.pow_le_pow_iff_right (Nat.Prime.one_lt (Fact.out : Nat.Prime p))).mp hpow_le_Ω
  haveI : Ωsub.Normal := by
    letI : Ωsub.Characteristic := by
      simpa [Ωsub] using (omega₁_characteristic (G := A0) (p := p))
    infer_instance
  haveI : Fact (IsPGroup p A0) := ⟨hA0p⟩
  obtain ⟨C, _hCnorm, hCΩ, hCcard⟩ :=
    lemma_1_22 (G := A0) p Ωsub inferInstance k hk 2 hk2
  have hCelem : IsElementaryAbelian p C := by
    letI : IsElementaryAbelian p Ωsub := hΩelem
    exact section9_c92_isElementaryAbelian_of_le (p := p) hCΩ
  let f : A0 →* G := K.subtype.comp A0.subtype
  let B : Subgroup G := C.map f
  have hf_inj : Function.Injective f := by
    intro x y hxy
    exact Subtype.ext <| Subtype.ext <| by
      simpa [f] using hxy
  have hB_le_K : B ≤ K := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨c, _hc, rfl⟩
    exact ((c : A0) : K).2
  have hBelem : IsElementaryAbelian p B := by
    letI : IsElementaryAbelian p C := hCelem
    simpa [B, f] using section9_c92_isElementaryAbelian_map_of_injective (p := p) (A := C) f
  have hBgen_eq : generatorRank B = generatorRank C := by
    simpa [B, f] using section9_c92_generatorRank_map_injective_eq (A := C) f hf_inj
  have hCgen : 2 ≤ generatorRank C := by
    letI : IsElementaryAbelian p C := hCelem
    exact section9_c92_generatorRank_at_least_two_of_elementaryAbelian_card_p_sq (p := p) hCcard
  have hBnoncyc : ¬ IsCyclic B := by
    intro hcyc
    have hle : generatorRank B ≤ 1 := generatorRank_le_one_of_isCyclic (G := B) hcyc
    omega
  exact ⟨p, hp, B, hB_le_K, hBelem, hBnoncyc⟩

private theorem CFSG.section9_c92_not_isCyclic_min_ce :
    ¬ IsCyclic G := by
  intro hcyc
  letI : IsCyclic G := hcyc
  letI : CommGroup G := IsCyclic.commGroup
  exact IsMinCE.not_solvable (G := G) (isSolvable_of_comm (fun a b : G => mul_comm a b))

private theorem CFSG.section9_c92_bot_not_unique :
    (⊥ : Subgroup G) ∉ section9UniqueSubgroups G := by
  classical
  intro hbot
  rcases hbot with ⟨_hproper, M, hMuniq⟩
  have hMcont : M ∈ section9MaximalSubgroupsContaining (⊥ : Subgroup G) := by
    rw [hMuniq]
    simp
  have hMtop : M = ⊤ := by
    apply top_le_iff.mp
    intro g _hg
    by_cases hgcyc : Subgroup.zpowers g = ⊤
    · exact False.elim <|
        section9_c92_not_isCyclic_min_ce
          ((isCyclic_iff_exists_zpowers_eq_top (α := G)).2 ⟨g, hgcyc⟩)
    · rcases eq_top_or_exists_le_coatom (Subgroup.zpowers g) with htop | ⟨N, hNcoatom, hgN⟩
      · exact False.elim (hgcyc htop)
      · have hNmax : N ∈ section9MaximalSubgroups G := hNcoatom
        have hNcont : N ∈ section9MaximalSubgroupsContaining (⊥ : Subgroup G) :=
          ⟨hNmax, bot_le⟩
        have hNM : N = M := by
          have hNsingle : N ∈ ({M} : Set (Subgroup G)) := by
            simpa [hMuniq] using hNcont
          simpa using hNsingle
        exact hNM ▸ hgN (Subgroup.mem_zpowers g)
  exact hMcont.1.1 hMtop

public theorem CFSG.section9_c92_unique_ne_bot
    {L : Subgroup G} (hL : L ∈ section9UniqueSubgroups G) :
    L ≠ ⊥ := by
  intro hLbot
  exact section9_c92_bot_not_unique (by simpa [hLbot] using hL)

omit [IsMinCE G] in
public theorem CFSG.section9_c92_le_unique_maximal_of_le
    {Y X M : Subgroup G} (hYX : Y ≤ X) (hXproper : X ≠ ⊤)
    (hMuniq : section9MaximalSubgroupsContaining Y = {M}) :
    X ≤ M := by
  classical
  rcases eq_top_or_exists_le_coatom X with hXtop | ⟨N, hNcoatom, hXN⟩
  · exact False.elim (hXproper hXtop)
  have hNmax : N ∈ section9MaximalSubgroups G := hNcoatom
  have hNcont : N ∈ section9MaximalSubgroupsContaining Y := ⟨hNmax, hYX.trans hXN⟩
  have hNM : N = M := by
    have hNsingle : N ∈ ({M} : Set (Subgroup G)) := by
      simpa [hMuniq] using hNcont
    simpa using hNsingle
  simpa [hNM] using hXN

public theorem CFSG.section9_c92_centralizer_singleton_ne_top
    {b : G} (hb : b ≠ 1) :
    Subgroup.centralizer ({b} : Set G) ≠ ⊤ := by
  intro htop
  have hb_center : b ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro x
    have hxcent : x ∈ Subgroup.centralizer ({b} : Set G) := by
      rw [htop]
      exact Subgroup.mem_top x
    have hcomm := (Subgroup.mem_centralizer_iff.mp hxcent) b (by simp)
    exact hcomm.symm
  have hb_one : b = 1 := by
    simpa [center_eq_bot_of_min_ce (G := G)] using hb_center
  exact hb hb_one

private theorem CFSG.section9_c92_proper_of_le_centralizer_unique
    {L K : Subgroup G} (hL : L ∈ section9UniqueSubgroups G)
    (hK : K ≤ Subgroup.centralizer (L : Set G)) :
    K ≠ ⊤ := by
  intro hKtop
  have hLbot : L = ⊥ := by
    apply le_bot_iff.mp
    intro l hl
    have hl_center : l ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro x
      have hxK : x ∈ K := by
        rw [hKtop]
        exact Subgroup.mem_top x
      have hxcent : x ∈ Subgroup.centralizer (L : Set G) := hK hxK
      exact ((Subgroup.mem_centralizer_iff.mp hxcent) l hl).symm
    simpa [center_eq_bot_of_min_ce (G := G)] using hl_center
  exact section9_c92_unique_ne_bot hL hLbot

/-- Corollary 9.2. -/
public theorem CFSG.corollary_9_2
    {L K : Subgroup G} (hL : L ∈ section9UniqueSubgroups G)
    (hK : K ≤ Subgroup.centralizer (L : Set G)) (hKrank : 2 ≤ groupRank K) :
    K ∈ section9UniqueSubgroups G := by
  classical
  have hLunique := hL
  rcases hL with ⟨_hLproper, M, hMuniq⟩
  have hMcont : M ∈ section9MaximalSubgroupsContaining L := by
    rw [hMuniq]
    simp
  have hMmax : M ∈ section9MaximalSubgroups G := hMcont.1
  have hKproper : K ≠ ⊤ :=
    section9_c92_proper_of_le_centralizer_unique hLunique hK
  obtain ⟨p, hp, B, hBK, hBelem, hBnoncyc⟩ :=
    section9_c92_exists_elementaryAbelian_noncyclic_subgroup_of_two_le_groupRank
      (K := K) hKrank
  letI : Fact p.Prime := ⟨hp⟩
  have hcentralizer_le_M :
      ∀ b : G, b ∈ B → b ≠ 1 → Subgroup.centralizer ({b} : Set G) ≤ M := by
    intro b hb hbne
    have hL_le_cent : L ≤ Subgroup.centralizer ({b} : Set G) := by
      intro l hl
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hyb : y = b := by simpa using hy
      subst y
      have hbK : b ∈ K := hBK hb
      have hbcentL : b ∈ Subgroup.centralizer (L : Set G) := hK hbK
      exact ((Subgroup.mem_centralizer_iff.mp hbcentL) l hl).symm
    exact section9_c92_le_unique_maximal_of_le
      hL_le_cent (section9_c92_centralizer_singleton_ne_top hbne) hMuniq
  have hB_le_M : B ≤ M := by
    intro b hb
    by_cases hbne : b ≠ 1
    · have hbcent : b ∈ Subgroup.centralizer ({b} : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hyb : y = b := by simpa using hy
        subst y
        rfl
      exact hcentralizer_le_M b hb hbne hbcent
    · have hb1 : b = 1 := not_not.mp hbne
      simp [hb1]
  have hBunique : B ∈ section9UniqueSubgroups G :=
    theorem_9_1 (p := p) (M := M) (B := B) hMmax
      ⟨hB_le_M, hBelem⟩ hBnoncyc (Or.inl hcentralizer_le_M)
  exact section9_unique_of_le hBK hKproper hBunique

end Section9
