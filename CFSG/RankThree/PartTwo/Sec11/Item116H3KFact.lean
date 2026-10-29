module

public import CFSG.RankThree.PartTwo.Sec11.Item116H3Rank
public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.RankThree.PartTwo.KFacts.AutKindsUnique
public import CFSG.RankThree.PartTwo.Sec11.Item116ResidueT
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)

@[expose] def fixedSub {X : Type*} [Group X] (α : MulAut X) : Subgroup X :=
  MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id X)

@[expose] def HasPRank {X : Type*} [Group X] (S : Subgroup X) (r k : ℕ) : Prop :=
  ∃ R : Subgroup X, R ≤ S ∧ IsPGroup r R ∧
    ∃ f : R →* Multiplicative (Fin k → ZMod r), Function.Surjective f

@[expose] def SimpleFixedRank (X : Type) [Group X] [Finite X] (α : MulAut X) (r k : ℕ) : Prop :=
  IsSimpleGroup (inSubgroup perfectResidual (fixedSub α)) ∧
    ¬ (∀ x y : inSubgroup perfectResidual (fixedSub α), x * y = y * x) ∧
    HasPRank (inSubgroup perfectResidual (fixedSub α)) r k

@[expose] def FactFieldCentralizerL2Odd : Prop :=
  ∀ (p e : ℕ) [Fact p.Prime], 5 ≤ p → 1 ≤ e → ∀ (X : Type) [Group X] [Finite X],
    Nonempty (X ≃* projSL 2 (GaloisField p (3 * e))) →
    ∀ α : MulAut X, orderOf α = 3 → α ∉ (MulAut.conj : X →* MulAut X).range →
      SimpleFixedRank X α p e

@[expose] def FactFieldCentralizerL3 : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ (X : Type) [Group X] [Finite X], Sec8.IsoLThreeMinusPi X 2 (3 * m) →
    ∀ α : MulAut X, orderOf α = 3 → α ∉ (MulAut.conj : X →* MulAut X).range →
      ∃ (r : ℕ) (_ : Fact r.Prime), 5 ≤ r ∧ SimpleFixedRank X α r (if 2 ≤ m then 2 else 1)

abbrev Fibre {H : Type*} [Group H] (N : Subgroup H) (y : H) : Type _ :=
  {l : H // (l : H ⧸ N) = (y : H ⧸ N)}

theorem exists_fixed_on_fibre {H : Type*} [Group H] [Finite H] (N : Subgroup H)
    (hN : ¬ 3 ∣ Nat.card N) (φ : MulAut H) (hφ3 : φ ^ 3 = 1) (z : H ⧸ N)
    (hφz : ∀ l : H, (l : H ⧸ N) = z → ((φ l : H) : H ⧸ N) = z) :
    ∃ s : H, (s : H ⧸ N) = z ∧ φ s = s := by
  obtain ⟨y0, rfl⟩ := QuotientGroup.mk_surjective z
  obtain ⟨f, hf_def⟩ : ∃ f : Function.End (Fibre N y0), ∀ s, (f s).1 = φ s.1 :=
    ⟨fun s => ⟨φ s.1, hφz s.1 s.2⟩, fun s => rfl⟩
  have hk : ∀ (k : ℕ) (s : Fibre N y0), ((f ^ k) s).1 = (φ ^ k) s.1 := by
    intro k
    induction k with
    | zero => intro s; rfl
    | succ k ih =>
      intro s
      rw [pow_succ', pow_succ']
      exact (hf_def _).trans (congrArg φ (ih s))
  have hf3 : f ^ 3 = 1 := by
    funext s
    apply Subtype.ext
    have h := hk 3 s
    rw [hφ3] at h
    exact h
  have hmem : ∀ t : N, ((y0 * (t : H) : H) : H ⧸ N) = (y0 : H ⧸ N) := by
    intro t
    apply QuotientGroup.eq.mpr
    have h : (y0 * (t : H))⁻¹ * y0 = (t : H)⁻¹ := by group
    rw [h]
    exact N.inv_mem t.2
  have hcard : Nat.card (Fibre N y0) = Nat.card N := by
    refine (Nat.card_congr ?_).symm
    exact
      { toFun := fun t => ⟨y0 * (t : H), hmem t⟩
        invFun := fun s => ⟨y0⁻¹ * s.1, QuotientGroup.eq.mp s.2.symm⟩
        left_inv := fun t => Subtype.ext (by simp)
        right_inv := fun s => Subtype.ext (by simp) }
  letI hdec : DecidableEq (Fibre N y0) := Classical.decEq _
  letI : Fintype (Fibre N y0) := Fintype.ofFinite _
  letI hdp : DecidablePred (fun x : Fibre N y0 => x ∈ Function.fixedPoints f) :=
    fun x => @Function.fixedPoints.decidable _ hdec f x
  letI : Fintype (Function.fixedPoints f) := Subtype.fintype _
  have hfix : ∃ s : Fibre N y0, f s = s := by
    by_contra hno
    push Not at hno
    haveI : IsEmpty (Function.fixedPoints f) := ⟨fun x => hno x.1 x.2⟩
    have h0 : Nat.card (Function.fixedPoints f) = 0 := Nat.card_of_isEmpty
    have hmod := Equiv.Perm.card_fixedPoints_modEq (α := Fibre N y0) (f := f) (p := 3) (n := 1)
      (by simpa using hf3)
    rw [← @Nat.card_eq_fintype_card _ _, ← @Nat.card_eq_fintype_card _ _, h0, hcard] at hmod
    exact hN ((Nat.modEq_zero_iff_dvd).mp hmod)
  obtain ⟨s, hs⟩ := hfix
  exact ⟨s.1, s.2, (hf_def s).symm.trans (congrArg Subtype.val hs)⟩

theorem k4_map_eq_one_of_solvable_normal {P X : Type} [Group P] [Group X] (π : P →* X)
    {K N : Subgroup P} (hNK : N ≤ K) (hN : ∀ k ∈ K, ∀ n ∈ N, k * n * k⁻¹ ∈ N)
    {S : Subgroup X} (hπK : K.map π = S) [IsSimpleGroup S]
    (hnc : ¬ ∀ x y : S, x * y = y * x) [Group.IsSolvable N] {n : P} (hn : n ∈ N) :
    π n = 1 := by
  have hTS : N.map π ≤ S := by
    rw [← hπK]
    exact Subgroup.map_mono hNK
  have hsK : ∀ s : S, ∃ k ∈ K, π k = (s : X) := by
    intro s
    have h : (s : X) ∈ K.map π := by
      rw [hπK]
      exact s.2
    exact Subgroup.mem_map.mp h
  haveI : ((N.map π).subgroupOf S).Normal :=
    ⟨fun t ht g => by
      rw [Subgroup.mem_subgroupOf] at ht ⊢
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      obtain ⟨m, hm, hmt⟩ := Subgroup.mem_map.mp ht
      obtain ⟨k, hk, hkg⟩ := hsK g
      refine Subgroup.mem_map.mpr ⟨k * m * k⁻¹, hN k hk m hm, ?_⟩
      rw [map_mul, map_mul, map_inv, hkg, hmt]⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N.map π).subgroupOf S) with hbot | htop
  ·
    have hmem : (⟨π n, hTS (Subgroup.mem_map_of_mem π hn)⟩ : S) ∈ (N.map π).subgroupOf S :=
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map_of_mem π hn)
    rw [hbot, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  ·
    exfalso
    let ρ : N →* S := MonoidHom.mk'
      (fun m : N => (⟨π m, hTS (Subgroup.mem_map_of_mem π m.2)⟩ : S))
      (fun a b => Subtype.ext (map_mul π (a : P) (b : P)))
    have hρ : Function.Surjective ρ := by
      intro s
      have hs : s ∈ (N.map π).subgroupOf S := by
        rw [htop]
        exact Subgroup.mem_top s
      obtain ⟨m, hm, hms⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hs)
      exact ⟨⟨m, hm⟩, Subtype.ext hms⟩
    exact hnc ((IsSimpleGroup.comm_iff_isSolvable).mpr (Group.isSolvable_of_surjective hρ))

theorem k4_eq_one_of_central_of_simple {S : Type} [Group S] [IsSimpleGroup S]
    (hnc : ¬ ∀ x y : S, x * y = y * x) {z : S} (hz : ∀ g : S, g * z = z * g) : z = 1 := by
  rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center S) with hbot | htop
  · have hz' : z ∈ Subgroup.center S := Subgroup.mem_center_iff.mpr hz
    rw [hbot, Subgroup.mem_bot] at hz'
    exact hz'
  · exfalso
    apply hnc
    intro x y
    have hx : x ∈ Subgroup.center S := by
      rw [htop]
      exact Subgroup.mem_top x
    exact (Subgroup.mem_center_iff.mp hx y).symm

theorem k4_comm_of_comm_one {X : Type} [Group X] {A B : X} (h : A * B * A⁻¹ * B⁻¹ = 1) :
    B * A = A * B := by
  have h2 : A * B * A⁻¹ = B := by
    calc A * B * A⁻¹ = (A * B * A⁻¹ * B⁻¹) * B := by group
      _ = B := by rw [h, one_mul]
  calc B * A = (A * B * A⁻¹) * A := by rw [h2]
    _ = A * B := by group

theorem k4_sec11K_le {G : Type} [Group G] (L : Subgroup G) (a : G) :
    sec11K L a ≤ L ⊓ Subgroup.centralizer ({a} : Set G) := by
  intro x hx
  unfold sec11K inSubgroup at hx
  obtain ⟨y, _, rfl⟩ := Subgroup.mem_map.mp hx
  exact y.2

theorem k4_inSubgroup_pr_conj {G : Type} [Group G] {M : Subgroup G} {k n : G}
    (hk : k ∈ M) (hn : n ∈ inSubgroup perfectResidual M) :
    k * n * k⁻¹ ∈ inSubgroup perfectResidual M := by
  unfold inSubgroup at hn ⊢
  obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hn
  refine Subgroup.mem_map.mpr ⟨(⟨k, hk⟩ : M) * m * (⟨k, hk⟩ : M)⁻¹,
    Subgroup.Normal.conj_mem inferInstance m hm _, ?_⟩
  simp

theorem k4_thetaCent_conj {G : Type} [Group G] [Finite G] {a k n : G}
    (hk : k ∈ Subgroup.centralizer ({a} : Set G)) (hn : n ∈ thetaCent a) :
    k * n * k⁻¹ ∈ thetaCent a := by
  unfold thetaCent inSubgroup at hn ⊢
  obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hn
  refine Subgroup.mem_map.mpr ⟨(⟨k, hk⟩ : Subgroup.centralizer ({a} : Set G)) * c *
    (⟨k, hk⟩ : Subgroup.centralizer ({a} : Set G))⁻¹,
    Subgroup.Normal.conj_mem inferInstance c hc _, ?_⟩
  simp

theorem k4_isSolvable_thetaCent {G : Type} [Group G] [Finite G] (a : G) :
    Group.IsSolvable (thetaCent a) := by
  have hsol : Group.IsSolvable (aschbacherSolvableCore 3 (Subgroup.centralizer ({a} : Set G))) :=
    (solvable_prime_complement_core_characterization Nat.prime_three).1
  let e := Subgroup.equivMapOfInjective
    (aschbacherSolvableCore 3 (Subgroup.centralizer ({a} : Set G)))
    (Subgroup.centralizer ({a} : Set G)).subtype (Subgroup.subtype_injective _)
  exact Group.isSolvable_of_isSolvable_injective (f := e.symm.toMonoidHom) e.symm.injective

theorem k4_isSolvable_of_map_le {G : Type} [Group G] (L : Subgroup G) (Θ : Subgroup G)
    [Group.IsSolvable Θ] (N : Subgroup L) (hN : N.map L.subtype ≤ Θ) :
    Group.IsSolvable N := by
  let f : N →* Θ := MonoidHom.mk'
    (fun n : N => (⟨((n : L) : G), hN (Subgroup.mem_map_of_mem L.subtype n.2)⟩ : Θ))
    (fun a b => Subtype.ext (by simp))
  refine Group.isSolvable_of_isSolvable_injective (f := f) ?_
  intro x y hxy
  have h : ((f x : Θ) : G) = ((f y : Θ) : G) := congrArg Subtype.val hxy
  apply Subtype.ext
  apply Subtype.ext
  exact h

section Bridge

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def inducedAutOn (L : Subgroup G) (a : G)
    (ha : a ∈ Subgroup.normalizer (L : Set G)) {X : Type} [Group X]
    (e₀ : L ⧸ aschbacherSolvableCore 3 L ≃* X) : MulAut X :=
  MulAut.congr e₀ (Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨a, ha⟩))

theorem inducedAutOn_spec {L : Subgroup G} {a : G} (ha : a ∈ Subgroup.normalizer (L : Set G))
    (ha3 : a ^ 3 = 1) (hout : Sec4.InducesOuterTheta a L) {X : Type} [Group X]
    (e₀ : L ⧸ aschbacherSolvableCore 3 L ≃* X) :
    orderOf (inducedAutOn L a ha e₀) = 3 ∧
      inducedAutOn L a ha e₀ ∉ (MulAut.conj : X →* MulAut X).range := by
  obtain ⟨_, hnot⟩ := hout
  have hpow : (⟨a, ha⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
    Subtype.ext (by simpa using ha3)
  have hτ3 : (Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨a, ha⟩)) ^ 3 = 1 := by
    rw [← map_pow, ← map_pow, hpow, map_one, map_one]
  have hα3 : (inducedAutOn L a ha e₀) ^ 3 = 1 := by
    unfold inducedAutOn
    rw [← map_pow, hτ3, map_one]
  have hnot' : inducedAutOn L a ha e₀ ∉ (MulAut.conj : X →* MulAut X).range := by
    intro h
    exact hnot ((KFacts.isInnerAut_congr e₀
      (Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨a, ha⟩))).mp h)
  have hne : inducedAutOn L a ha e₀ ≠ 1 := by
    intro h
    apply hnot'
    rw [h]
    exact (MulAut.conj : X →* MulAut X).range.one_mem
  exact ⟨orderOf_eq_prime hα3 hne, hnot'⟩

theorem exists_mem_centralizer_of_fixed {L : Subgroup G} {a : G}
    (ha : a ∈ Subgroup.normalizer (L : Set G)) (ha3 : a ^ 3 = 1) {X : Type} [Group X]
    (e₀ : L ⧸ aschbacherSolvableCore 3 L ≃* X) {x : X}
    (hx : x ∈ fixedSub (inducedAutOn L a ha e₀)) :
    ∃ y : L, (y : G) ∈ Subgroup.centralizer ({a} : Set G) ∧
      e₀ (y : L ⧸ aschbacherSolvableCore 3 L) = x := by
  classical
  have h1 : e₀ (Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨a, ha⟩) (e₀.symm x)) = x := hx
  have hτz : Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨a, ha⟩) (e₀.symm x) = e₀.symm x := by
    apply e₀.injective
    rw [h1, MulEquiv.apply_symm_apply]
  have hpow : (⟨a, ha⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
    Subtype.ext (by simpa using ha3)
  have hφ3 : (Sec4.compAction L ⟨a, ha⟩) ^ 3 = 1 := by
    rw [← map_pow, hpow, map_one]
  have hθ : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 L) :=
    (solvable_prime_complement_core_characterization Nat.prime_three).2.2.1
  have hφz : ∀ l : L, (l : L ⧸ aschbacherSolvableCore 3 L) = e₀.symm x →
      ((Sec4.compAction L ⟨a, ha⟩ l : L) : L ⧸ aschbacherSolvableCore 3 L) = e₀.symm x := by
    intro l hl
    have hm := Sec4.thetaQuotMulAut_mk (Sec4.compAction L ⟨a, ha⟩) l
    rw [hl, hτz] at hm
    exact hm.symm
  obtain ⟨s, hs, hsφ⟩ := exists_fixed_on_fibre (aschbacherSolvableCore 3 L) hθ
    (Sec4.compAction L ⟨a, ha⟩) hφ3 (e₀.symm x) hφz
  have hc : ((Sec4.compAction L ⟨a, ha⟩ s : L) : G) = (s : G) := by rw [hsφ]
  have h2 : ((Sec4.compAction L ⟨a, ha⟩ s : L) : G) = a * (s : G) * a⁻¹ :=
    Sec4.normalizerMonoidHom_apply_coe ha s
  rw [h2] at hc
  refine ⟨s, Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hc).symm, ?_⟩
  rw [hs]
  exact e₀.apply_symm_apply x

theorem inSubgroup_perfectResidual_subgroupOf_map_eq {H : Type} [Group H] [Finite H] {X : Type}
    [Group X] [Finite X] {M L : Subgroup H} (hML : M ≤ L) (π : L →* X) :
    ((inSubgroup perfectResidual M).subgroupOf L).map π =
      inSubgroup perfectResidual ((M.subgroupOf L).map π) := by
  have hJ : (inSubgroup perfectResidual M).subgroupOf L =
      (perfectResidual ↥M).map (Subgroup.inclusion hML) := by
    ext l
    rw [Subgroup.mem_subgroupOf]
    unfold inSubgroup
    rw [Subgroup.mem_map, Subgroup.mem_map]
    constructor
    · rintro ⟨m, hm, hmeq⟩
      exact ⟨m, hm, Subtype.ext hmeq⟩
    · rintro ⟨m, hm, hmeq⟩
      exact ⟨m, hm, congrArg Subtype.val hmeq⟩
  have hR : (M.subgroupOf L).map π = (π.comp (Subgroup.inclusion hML)).range := by
    ext x
    rw [Subgroup.mem_map, MonoidHom.mem_range]
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact ⟨⟨(l : H), Subgroup.mem_subgroupOf.mp hl⟩, rfl⟩
    · rintro ⟨m, rfl⟩
      exact ⟨Subgroup.inclusion hML m, Subgroup.mem_subgroupOf.mpr m.2, rfl⟩
  rw [hJ, Subgroup.map_map, hR]
  exact (perfect_residual_transport (π.comp (Subgroup.inclusion hML))).1

theorem map_sec11K_eq {L : Subgroup G} {a : G} (ha : a ∈ Subgroup.normalizer (L : Set G))
    (ha3 : a ^ 3 = 1) {X : Type} [Group X] [Finite X]
    (e₀ : L ⧸ aschbacherSolvableCore 3 L ≃* X) :
    ((sec11K L a).subgroupOf L).map
        (e₀.toMonoidHom.comp (QuotientGroup.mk' (aschbacherSolvableCore 3 L))) =
      inSubgroup perfectResidual (fixedSub (inducedAutOn L a ha e₀)) := by
  have hpi : ((L ⊓ Subgroup.centralizer ({a} : Set G)).subgroupOf L).map
      (e₀.toMonoidHom.comp (QuotientGroup.mk' (aschbacherSolvableCore 3 L))) =
        fixedSub (inducedAutOn L a ha e₀) := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨l, hl, rfl⟩
      have hlC : ((l : L) : G) ∈ Subgroup.centralizer ({a} : Set G) :=
        (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hl)).2
      have hmC : ((l : L) : G) * a = a * ((l : L) : G) := Subgroup.mem_centralizer_singleton_iff.mp hlC
      have hσ : Sec4.compAction L ⟨a, ha⟩ l = l := by
        apply Subtype.ext
        have h2 : ((Sec4.compAction L ⟨a, ha⟩ l : L) : G) = a * ((l : L) : G) * a⁻¹ :=
          Sec4.normalizerMonoidHom_apply_coe ha l
        rw [h2, ← hmC, mul_inv_cancel_right]
      show e₀ (Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨a, ha⟩)
          (e₀.symm (e₀ (QuotientGroup.mk l)))) = e₀ (QuotientGroup.mk l)
      rw [MulEquiv.symm_apply_apply, Sec4.thetaQuotMulAut_mk, hσ]
    · intro hx
      obtain ⟨y, hy, hyx⟩ := exists_mem_centralizer_of_fixed ha ha3 e₀ hx
      exact ⟨y, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨y.2, hy⟩), hyx⟩
  unfold sec11K
  rw [inSubgroup_perfectResidual_subgroupOf_map_eq
    (inf_le_left : L ⊓ Subgroup.centralizer ({a} : Set G) ≤ L), hpi]

theorem sec11K_inf_thetaCent_le {L : Subgroup G} {a : G}
    (ha : a ∈ Subgroup.normalizer (L : Set G)) (ha3 : a ^ 3 = 1) {X : Type} [Group X] [Finite X]
    (e₀ : L ⧸ aschbacherSolvableCore 3 L ≃* X) {r k : ℕ}
    (hS : SimpleFixedRank X (inducedAutOn L a ha e₀) r k) :
    sec11K L a ⊓ thetaCent a ≤ (aschbacherSolvableCore 3 L).map L.subtype := by
  intro x hx
  obtain ⟨hxK, hxθ⟩ := Subgroup.mem_inf.mp hx
  have hxL : x ∈ L := (Subgroup.mem_inf.mp (k4_sec11K_le L a hxK)).1
  obtain ⟨x', rfl⟩ : ∃ x' : L, (x' : G) = x := ⟨⟨x, hxL⟩, rfl⟩
  unfold SimpleFixedRank at hS
  obtain ⟨hsimp, hnc, -⟩ := hS
  obtain ⟨S, hSdef⟩ : ∃ S : Subgroup X,
      S = inSubgroup perfectResidual (fixedSub (inducedAutOn L a ha e₀)) := ⟨_, rfl⟩
  rw [← hSdef] at hsimp hnc
  obtain ⟨π, hπdef⟩ : ∃ π : L →* X,
      π = e₀.toMonoidHom.comp (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) := ⟨_, rfl⟩
  have hπK : ((sec11K L a).subgroupOf L).map π = S := by
    rw [hπdef, hSdef]
    exact map_sec11K_eq ha ha3 e₀
  have hπapp : ∀ n : L, π n = e₀ (n : L ⧸ aschbacherSolvableCore 3 L) := by
    intro n
    subst hπdef
    rfl
  haveI := k4_isSolvable_thetaCent a
  have hNmem : ∀ n : L, n ∈ ((sec11K L a).subgroupOf L) ⊓ (thetaCent a).subgroupOf L ↔
      ((n : G) ∈ sec11K L a ∧ (n : G) ∈ thetaCent a) := fun n => by
    rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  have hNconj : ∀ kk ∈ (sec11K L a).subgroupOf L,
      ∀ nn ∈ ((sec11K L a).subgroupOf L) ⊓ (thetaCent a).subgroupOf L,
        kk * nn * kk⁻¹ ∈ ((sec11K L a).subgroupOf L) ⊓ (thetaCent a).subgroupOf L := by
    intro kk hk nn hn
    have hkK : (kk : G) ∈ sec11K L a := Subgroup.mem_subgroupOf.mp hk
    have hkM := k4_sec11K_le L a hkK
    obtain ⟨hnK, hnθ⟩ := (hNmem nn).mp hn
    rw [hNmem]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact ⟨k4_inSubgroup_pr_conj hkM hnK, k4_thetaCent_conj (Subgroup.mem_inf.mp hkM).2 hnθ⟩
  have hNθ : (((sec11K L a).subgroupOf L) ⊓ (thetaCent a).subgroupOf L).map L.subtype ≤
      thetaCent a := by
    intro y hy
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hy
    exact ((hNmem n).mp hn).2
  haveI : Group.IsSolvable ↥(((sec11K L a).subgroupOf L) ⊓ (thetaCent a).subgroupOf L) :=
    k4_isSolvable_of_map_le L (thetaCent a) _ hNθ
  have hxN : x' ∈ ((sec11K L a).subgroupOf L) ⊓ (thetaCent a).subgroupOf L :=
    (hNmem x').mpr ⟨hxK, hxθ⟩
  have hπ1 : π x' = 1 :=
    k4_map_eq_one_of_solvable_normal π inf_le_left hNconj hπK hnc hxN
  have h1 : e₀ ((x' : L) : L ⧸ aschbacherSolvableCore 3 L) = 1 :=
    (hπapp x').symm.trans hπ1
  have h2 : ((x' : L) : L ⧸ aschbacherSolvableCore 3 L) = 1 :=
    e₀.injective (h1.trans (map_one e₀).symm)
  have h3 : x' ∈ aschbacherSolvableCore 3 L := (QuotientGroup.eq_one_iff _).mp h2
  exact Subgroup.mem_map.mpr ⟨x', h3, rfl⟩

theorem mem_theta_of_centralizes {L : Subgroup G} {a : G}
    (ha : a ∈ Subgroup.normalizer (L : Set G)) (ha3 : a ^ 3 = 1) {X : Type} [Group X] [Finite X]
    (e₀ : L ⧸ aschbacherSolvableCore 3 L ≃* X) {r k : ℕ}
    (hS : SimpleFixedRank X (inducedAutOn L a ha e₀) r k) {Y : Subgroup G}
    (hKY : sec11K L a ≤ Y) {x : G} (hx : x ∈ sec11K L a)
    (hxY : ∀ y ∈ Y, x * y * x⁻¹ * y⁻¹ ∈ thetaCent a) :
    x ∈ (aschbacherSolvableCore 3 L).map L.subtype := by
  have hxL : x ∈ L := (Subgroup.mem_inf.mp (k4_sec11K_le L a hx)).1
  obtain ⟨x', rfl⟩ : ∃ x' : L, (x' : G) = x := ⟨⟨x, hxL⟩, rfl⟩
  have hK4 := sec11K_inf_thetaCent_le ha ha3 e₀ hS
  unfold SimpleFixedRank at hS
  obtain ⟨hsimp, hnc, -⟩ := hS
  obtain ⟨S, hSdef⟩ : ∃ S : Subgroup X,
      S = inSubgroup perfectResidual (fixedSub (inducedAutOn L a ha e₀)) := ⟨_, rfl⟩
  rw [← hSdef] at hsimp hnc
  obtain ⟨π, hπdef⟩ : ∃ π : L →* X,
      π = e₀.toMonoidHom.comp (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) := ⟨_, rfl⟩
  have hπK : ((sec11K L a).subgroupOf L).map π = S := by
    rw [hπdef, hSdef]
    exact map_sec11K_eq ha ha3 e₀
  have hπapp : ∀ n : L, π n = e₀ (n : L ⧸ aschbacherSolvableCore 3 L) := by
    intro n
    subst hπdef
    rfl
  have hxK' : x' ∈ (sec11K L a).subgroupOf L := Subgroup.mem_subgroupOf.mpr hx
  have hzS : π x' ∈ S := by
    rw [← hπK]
    exact Subgroup.mem_map_of_mem π hxK'
  obtain ⟨z, hz⟩ : ∃ z : S, (z : X) = π x' := ⟨⟨π x', hzS⟩, rfl⟩
  have hcent : ∀ g : S, g * z = z * g := by
    intro g
    obtain ⟨s, hs⟩ := g
    have hsK : s ∈ ((sec11K L a).subgroupOf L).map π := by
      rw [hπK]
      exact hs
    obtain ⟨y, hyK, hys⟩ := Subgroup.mem_map.mp hsK
    have hy' : (y : G) ∈ sec11K L a := Subgroup.mem_subgroupOf.mp hyK
    have hx'K : (x' : G) ∈ sec11K L a := Subgroup.mem_subgroupOf.mp hxK'
    have hcK : (x' : G) * (y : G) * (x' : G)⁻¹ * (y : G)⁻¹ ∈ sec11K L a :=
      (sec11K L a).mul_mem ((sec11K L a).mul_mem ((sec11K L a).mul_mem hx'K hy')
        ((sec11K L a).inv_mem hx'K)) ((sec11K L a).inv_mem hy')
    have hcθ : (x' : G) * (y : G) * (x' : G)⁻¹ * (y : G)⁻¹ ∈ thetaCent a :=
      hxY _ (hKY hy')
    obtain ⟨n, hn, hnc'⟩ := Subgroup.mem_map.mp (hK4 (Subgroup.mem_inf.mpr ⟨hcK, hcθ⟩))
    have hnn : x' * y * x'⁻¹ * y⁻¹ = n :=
      Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; exact hnc'.symm)
    have hq : ((x' * y * x'⁻¹ * y⁻¹ : L) : L ⧸ aschbacherSolvableCore 3 L) = 1 := by
      rw [hnn]
      exact (QuotientGroup.eq_one_iff n).mpr hn
    have hπc : π (x' * y * x'⁻¹ * y⁻¹) = 1 := by
      rw [hπapp, hq, map_one]
    simp only [map_mul, map_inv] at hπc
    have hcomm := k4_comm_of_comm_one hπc
    apply Subtype.ext
    show s * (z : X) = (z : X) * s
    rw [hz, ← hys]
    exact hcomm
  have hz1 : z = 1 := k4_eq_one_of_central_of_simple hnc hcent
  have hπx : π x' = 1 := by
    have h := congrArg Subtype.val hz1
    rw [hz] at h
    exact h
  have h1 : e₀ ((x' : L) : L ⧸ aschbacherSolvableCore 3 L) = 1 :=
    (hπapp x').symm.trans hπx
  have h2 : ((x' : L) : L ⧸ aschbacherSolvableCore 3 L) = 1 :=
    e₀.injective (h1.trans (map_one e₀).symm)
  have h3 : x' ∈ aschbacherSolvableCore 3 L := (QuotientGroup.eq_one_iff _).mp h2
  exact Subgroup.mem_map.mpr ⟨x', h3, rfl⟩

theorem pRankData_of_simpleFixedRank {L : Subgroup G} {a : G}
    (ha : a ∈ Subgroup.normalizer (L : Set G)) (ha3 : a ^ 3 = 1) {X : Type} [Group X] [Finite X]
    (e₀ : L ⧸ aschbacherSolvableCore 3 L ≃* X) {r k : ℕ} [Fact r.Prime]
    (hS : SimpleFixedRank X (inducedAutOn L a ha e₀) r k) {Y : Subgroup G}
    (hKY : sec11K L a ≤ Y) : PRankData r a Y k := by
  have hK4 := sec11K_inf_thetaCent_le ha ha3 e₀ hS
  have hK6 : ∀ {x : G}, x ∈ sec11K L a → (∀ y ∈ Y, x * y * x⁻¹ * y⁻¹ ∈ thetaCent a) →
      x ∈ (aschbacherSolvableCore 3 L).map L.subtype :=
    fun hx hxY => mem_theta_of_centralizes ha ha3 e₀ hS hKY hx hxY
  unfold SimpleFixedRank at hS
  obtain ⟨-, -, hPR⟩ := hS
  unfold HasPRank at hPR
  obtain ⟨R, hRS, hRp, fR, hfR⟩ := hPR
  obtain ⟨S, hSdef⟩ : ∃ S : Subgroup X,
      S = inSubgroup perfectResidual (fixedSub (inducedAutOn L a ha e₀)) := ⟨_, rfl⟩
  rw [← hSdef] at hRS
  obtain ⟨π, hπdef⟩ : ∃ π : L →* X,
      π = e₀.toMonoidHom.comp (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) := ⟨_, rfl⟩
  have hπapp : ∀ n : L, π n = e₀ (n : L ⧸ aschbacherSolvableCore 3 L) := by
    intro n
    subst hπdef
    rfl
  obtain ⟨KL, hKLdef⟩ : ∃ KL : Subgroup L, KL = (sec11K L a).subgroupOf L := ⟨_, rfl⟩
  have hKLmem : ∀ m : L, m ∈ KL ↔ (m : G) ∈ sec11K L a := fun m => by
    rw [hKLdef, Subgroup.mem_subgroupOf]
  have hπK : KL.map π = S := by
    rw [hKLdef, hπdef, hSdef]
    exact map_sec11K_eq ha ha3 e₀
  obtain ⟨M, hMdef⟩ : ∃ M : Subgroup L, M = KL ⊓ R.comap π := ⟨_, rfl⟩
  have hMmem : ∀ m : L, m ∈ M ↔ (m ∈ KL ∧ π m ∈ R) := fun m => by
    rw [hMdef, Subgroup.mem_inf, Subgroup.mem_comap]
  have hfM : ∀ m : M, π (m : L) ∈ R := fun m => ((hMmem (m : L)).mp m.2).2
  let f : M →* R := MonoidHom.mk' (fun m : M => (⟨π (m : L), hfM m⟩ : R))
    (fun m1 m2 => Subtype.ext (by simp))
  have hf : Function.Surjective f := by
    rintro ⟨x, hx⟩
    have hxS : x ∈ KL.map π := by
      rw [hπK]
      exact hRS hx
    obtain ⟨k', hkK, hπk⟩ := Subgroup.mem_map.mp hxS
    have hkM : k' ∈ M := (hMmem k').mpr ⟨hkK, by rw [hπk]; exact hx⟩
    exact ⟨⟨k', hkM⟩, Subtype.ext hπk⟩
  have hRtop : IsPGroup r (⊤ : Subgroup R) := by
    intro g
    obtain ⟨k₁, hk₁⟩ := hRp g.1
    exact ⟨k₁, Subtype.ext hk₁⟩
  obtain ⟨Q, hQ⟩ := Sylow.mapSurjective_surjective hf r
    (⟨⊤, hRtop, fun _ h => top_le_iff.mp h⟩ : Sylow r R)
  have hQmap : Q.toSubgroup.map f = ⊤ := congrArg Sylow.toSubgroup hQ
  let g1 : M →* G := L.subtype.comp M.subtype
  have hg1inj : Function.Injective g1 := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact h
  let e1 : Q.toSubgroup ≃* (Q.toSubgroup.map g1) :=
    Subgroup.equivMapOfInjective Q.toSubgroup g1 hg1inj
  let φ : Q.toSubgroup →* Multiplicative (Fin k → ZMod r) := fR.comp (f.comp Q.toSubgroup.subtype)
  let ψ : (Q.toSubgroup.map g1) →* Multiplicative (Fin k → ZMod r) := φ.comp e1.symm.toMonoidHom
  have hθL : ∀ l : L, (l : G) ∈ (aschbacherSolvableCore 3 L).map L.subtype →
      l ∈ aschbacherSolvableCore 3 L := by
    intro l hl
    obtain ⟨x, hx, hxl⟩ := Subgroup.mem_map.mp hl
    have hxeq : x = l := Subtype.ext hxl
    rw [← hxeq]
    exact hx
  have hkill : ∀ q : M, (q : L) ∈ aschbacherSolvableCore 3 L → f q = 1 := by
    intro q hq
    apply Subtype.ext
    show π (q : L) = 1
    rw [hπapp, (QuotientGroup.eq_one_iff (q : L)).mpr hq, map_one]
  have hqsec : ∀ q : M, ((q : L) : G) ∈ sec11K L a := fun q =>
    (hKLmem (q : L)).mp ((hMmem (q : L)).mp q.2).1
  have hψ_of : ∀ q : Q.toSubgroup, f q.1 = 1 → ψ (e1 q) = 1 := by
    intro q hq
    show φ (e1.symm (e1 q)) = 1
    rw [MulEquiv.symm_apply_apply]
    show fR (f q.1) = 1
    rw [hq, map_one]
  have hψsurj : Function.Surjective ψ := by
    intro z
    obtain ⟨w, hw⟩ := hfR z
    have hwtop : w ∈ Q.toSubgroup.map f := by
      rw [hQmap]
      exact Subgroup.mem_top w
    obtain ⟨q, hq, hqw⟩ := Subgroup.mem_map.mp hwtop
    refine ⟨e1 ⟨q, hq⟩, ?_⟩
    show φ (e1.symm (e1 ⟨q, hq⟩)) = z
    rw [MulEquiv.symm_apply_apply]
    show fR (f q) = z
    rw [hqw, hw]
  have hUle : Q.toSubgroup.map g1 ≤ Y ⊓ Subgroup.centralizer ({a} : Set G) := by
    intro u hu
    obtain ⟨q, -, rfl⟩ := Subgroup.mem_map.mp hu
    exact Subgroup.mem_inf.mpr ⟨hKY (hqsec q),
      (Subgroup.mem_inf.mp (k4_sec11K_le L a (hqsec q))).2⟩
  have hUp : IsPGroup r (Q.toSubgroup.map g1) := Q.isPGroup'.map g1
  unfold PRankData
  refine ⟨Q.toSubgroup.map g1, ψ, hUle, hUp, hψsurj, ?_, ?_⟩
  · intro u hu
    obtain ⟨q, hqQ, hqu⟩ := Subgroup.mem_map.mp u.2
    have hue : e1 ⟨q, hqQ⟩ = u := Subtype.ext hqu
    rw [← hue]
    apply hψ_of ⟨q, hqQ⟩
    have hθq : ((q : L) : G) ∈ thetaCent a := by
      rw [show ((q : L) : G) = (u : G) from hqu]
      exact hu
    exact hkill q (hθL (q : L) (hK4 (Subgroup.mem_inf.mpr ⟨hqsec q, hθq⟩)))
  · intro u hu
    obtain ⟨q, hqQ, hqu⟩ := Subgroup.mem_map.mp u.2
    have hue : e1 ⟨q, hqQ⟩ = u := Subtype.ext hqu
    rw [← hue]
    apply hψ_of ⟨q, hqQ⟩
    have hxY' : ∀ y ∈ Y, ((q : L) : G) * y * ((q : L) : G)⁻¹ * y⁻¹ ∈ thetaCent a := by
      intro y hy
      rw [show ((q : L) : G) = (u : G) from hqu]
      exact hu y hy
    exact hkill q (hθL (q : L) (hK6 (hqsec q) hxY'))

variable {A : Subgroup G} {c : G} {L : Subgroup G} {a : G} {R Y : Subgroup G}

theorem five_le_of_three_lt_fact {p : ℕ} [hp : Fact p.Prime] (h3 : 3 < p) : 5 ≤ p := by
  have hne : p ≠ 4 := by
    rintro rfl
    exact absurd hp.out (by norm_num)
  omega

theorem normalizer_of_inducesOuterTheta {x : G} {M : Subgroup G}
    (hout : Sec4.InducesOuterTheta x M) : x ∈ Subgroup.normalizer (M : Set G) := by
  obtain ⟨hx, -⟩ := hout
  exact hx

theorem standing_of_stdLocal (h : Sec11StdLocal G A c L a R Y) :
    Sec4.InducesOuterTheta a L ∧ a ^ 3 = 1 := by
  refine ⟨?_, h.mem_partTwoF.1.2 a h.a_mem⟩
  rcases h.inducesStdKind with hf | hg
  · exact KFacts.InducesStdKind.inducesOuterTheta L hf (by intro hc; cases hc)
  · exact KFacts.InducesStdKind.inducesOuterTheta L hg (by intro hc; cases hc)

theorem pRankData_of_l2Odd (hFC : FactFieldCentralizerL2Odd) (h : Sec11StdLocal G A c L a R Y)
    {p e : ℕ} [Fact p.Prime] (hp : 3 < p) (he : 1 ≤ e)
    (hL : Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 2 (GaloisField p (3 * e)))) :
    PRankData p a Y e := by
  obtain ⟨hout, ha3⟩ := standing_of_stdLocal h
  have ha : a ∈ Subgroup.normalizer (L : Set G) := normalizer_of_inducesOuterTheta hout
  obtain ⟨hα3, hαout⟩ :=
    inducedAutOn_spec ha ha3 hout (MulEquiv.refl (L ⧸ aschbacherSolvableCore 3 L))
  have hS := hFC p e (five_le_of_three_lt_fact hp) he (L ⧸ aschbacherSolvableCore 3 L) hL
    (inducedAutOn L a ha (MulEquiv.refl (L ⧸ aschbacherSolvableCore 3 L))) hα3 hαout
  exact pRankData_of_simpleFixedRank ha ha3 (MulEquiv.refl (L ⧸ aschbacherSolvableCore 3 L))
    hS h.sec11K_le

theorem pRankData_of_l3 (hFC : FactFieldCentralizerL3) (h : Sec11StdLocal G A c L a R Y)
    {m : ℕ} (hm : 1 ≤ m) (hL : Sec8.IsoLThreeMinusPi (L ⧸ aschbacherSolvableCore 3 L) 2 (3 * m)) :
    ∃ (r : ℕ) (_ : Fact r.Prime), 5 ≤ r ∧ PRankData r a Y (if 2 ≤ m then 2 else 1) := by
  obtain ⟨hout, ha3⟩ := standing_of_stdLocal h
  have ha : a ∈ Subgroup.normalizer (L : Set G) := normalizer_of_inducesOuterTheta hout
  obtain ⟨hα3, hαout⟩ :=
    inducedAutOn_spec ha ha3 hout (MulEquiv.refl (L ⧸ aschbacherSolvableCore 3 L))
  obtain ⟨r, hr, h5, hS⟩ := hFC m hm (L ⧸ aschbacherSolvableCore 3 L) hL
    (inducedAutOn L a ha (MulEquiv.refl (L ⧸ aschbacherSolvableCore 3 L))) hα3 hαout
  exact ⟨r, hr, h5, pRankData_of_simpleFixedRank ha ha3
    (MulEquiv.refl (L ⧸ aschbacherSolvableCore 3 L)) hS h.sec11K_le⟩

end Bridge

end CFSG.RankThree.PartTwo.Sec11
