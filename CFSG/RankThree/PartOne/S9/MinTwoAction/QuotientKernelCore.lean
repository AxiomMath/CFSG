module

public import CFSG.RankThree.PartOne.S9.MinTwoAction.QuotientRep
public import CFSG.RankThree.GroupTheory.SteinbergCESmallBinaryOrbitCounts
public import CFSG.RankThree.PartTwo.ExponentPrimeSmallRank
public import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting

public section

namespace CFSG.RankThree.PartOne.Quotient36

open CFSG CFSG.RankThree.GroupTheory CFSG.RankThree.GroupTheory.SteinbergBY
  CFSG.RankThree.LocalRank
open scoped IsMulCommutative commutatorElement

section Fixed

variable {E X : Type*} [Group E] [Group X] [Finite X] [MulDistribMulAction E X]

omit [Finite X] in
theorem mem_fixedPointSubgroup_zpowers_iff (e : E) (x : X) :
    x ∈ fixedPointSubgroup (Subgroup.zpowers e) X ↔ e • x = x := by
  constructor
  · intro h
    exact h ⟨e, Subgroup.mem_zpowers e⟩
  · intro h g
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp g.2
    have h1 : e ∈ MulAction.stabilizer E x := h
    have h2 := (MulAction.stabilizer E x).zpow_mem h1 n
    show (g : E) • x = x
    rw [← hn]
    exact h2

theorem fixed_mk_eq_image {q : ℕ} [Fact q.Prime] [Fact (IsPGroup q X)] (hq2 : q ≠ 2) (e : E)
    [Finite (Subgroup.zpowers e)] (he : IsPGroup 2 (Subgroup.zpowers e)) :
    letI := frattiniQuotientAction E X
    {v : X ⧸ frattini X | e • v = v} =
      (QuotientGroup.mk' (frattini X)) '' {c : X | e • c = c} := by
  let _ := frattiniQuotientAction E X
  let α : ↥(Subgroup.zpowers e) →* MulAut X :=
    MulDistribMulAction.toMulAut ↥(Subgroup.zpowers e) X
  have hinv : CFSG.IsInvariant E X (frattini X) := isInvariant_of_characteristic _
  have hN : ∀ a : ↥(Subgroup.zpowers e), ∀ n ∈ frattini X, α a n ∈ frattini X :=
    fun a n hn => (hinv.invariant (a : E) n).mp hn
  have hcop : ¬ 2 ∣ Nat.card (frattini X) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp ((Fact.out : IsPGroup q X).to_subgroup (frattini X))
    rw [hk]
    intro h2
    have := (Nat.prime_two.dvd_of_dvd_pow h2)
    have h3 := (Nat.prime_dvd_prime_iff_eq Nat.prime_two (Fact.out : q.Prime)).mp this
    exact hq2 h3.symm
  have key := Semidihedral.Principal.coprime_fixed_point_lifting 2 he α (frattini X) hN hcop
  have hfix : ∀ v : X ⧸ frattini X,
      (∀ a : ↥(Subgroup.zpowers e),
        Semidihedral.Principal.CoprimeFixedPoint.quotientAction α (frattini X) hN a v = v) ↔
        e • v = v := by
    intro v
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective v
    constructor
    · intro h
      have := h ⟨e, Subgroup.mem_zpowers e⟩
      exact this
    · intro h a
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp a.2
      have h1 : e ∈ MulAction.stabilizer E (x : X ⧸ frattini X) := h
      have h2 := (MulAction.stabilizer E (x : X ⧸ frattini X)).zpow_mem h1 n
      rw [Semidihedral.Principal.CoprimeFixedPoint.quotientAction_mk]
      change (((a : E) • x : X) : X ⧸ frattini X) = _
      have h3 : (a : E) • (x : X ⧸ frattini X) = (x : X ⧸ frattini X) := by
        rw [← hn]; exact h2
      exact h3
  have hfix2 : ∀ c : X, (∀ a : ↥(Subgroup.zpowers e), α a c = c) ↔ e • c = c := by
    intro c
    rw [← mem_fixedPointSubgroup_zpowers_iff]
    exact Iff.rfl
  ext v
  have := Set.ext_iff.mp key v
  simp only [Set.mem_ofPred_eq, hfix, Set.mem_image, hfix2] at this
  simpa using this


theorem card_fixed_le {q : ℕ} [Fact q.Prime] [Fact (IsPGroup q X)] (hq2 : q ≠ 2) (e : E)
    [Finite (Subgroup.zpowers e)] (he : IsPGroup 2 (Subgroup.zpowers e)) :
    Nat.card {v : X ⧸ frattini X // (letI := frattiniQuotientAction E X; e • v = v)} ≤
      Nat.card (↥(fixedPointSubgroup (Subgroup.zpowers e) X) ⧸
        commutator ↥(fixedPointSubgroup (Subgroup.zpowers e) X)) := by
  classical
  set Y : Subgroup X := fixedPointSubgroup (Subgroup.zpowers e) X with hY
  have hcomm : IsMulCommutative (X ⧸ frattini X) :=
    (isElementaryAbelian_quotient_frattini (p := q) (R := X)).toIsMulCommutative
  let f : ↥Y →* X ⧸ frattini X := (QuotientGroup.mk' (frattini X)).comp Y.subtype
  have hker : commutator ↥Y ≤ f.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm.is_comm.comm _ _
  let g : ↥Y ⧸ commutator ↥Y →* X ⧸ frattini X := QuotientGroup.lift (commutator ↥Y) f hker
  have hrange : (g.range : Set (X ⧸ frattini X)) = {v | (letI := frattiniQuotientAction E X;
      e • v = v)} := by
    rw [fixed_mk_eq_image hq2 e he]
    ext v
    constructor
    · rintro ⟨w, rfl⟩
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective w
      exact ⟨(y : X), (mem_fixedPointSubgroup_zpowers_iff e _).mp y.2, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨(⟨c, (mem_fixedPointSubgroup_zpowers_iff e c).mpr hc⟩ : ↥Y), rfl⟩
  have h2 : Nat.card {v : X ⧸ frattini X // (letI := frattiniQuotientAction E X; e • v = v)} =
      Nat.card g.range :=
    (Nat.card_congr (Equiv.subtypeEquivRight fun v => by
      have := Set.ext_iff.mp hrange v
      simpa using this.symm))
  rw [h2]
  exact Nat.card_le_card_of_surjective g.rangeRestrict g.rangeRestrict_surjective


theorem card_eigenspace_eq (q : ℕ) [Fact q.Prime] [Fact (IsPGroup q X)] (e : E) :
    Nat.card ↥(Module.End.eigenspace (frattiniRep (E := E) (X := X) q e) 1) =
      Nat.card {v : X ⧸ frattini X // (letI := frattiniQuotientAction E X; e • v = v)} := by
  refine Nat.card_congr (Equiv.subtypeEquiv (Additive.toMul : Additive (X ⧸ frattini X) ≃
    X ⧸ frattini X) fun w => ?_)
  rw [Module.End.mem_eigenspace_iff, one_smul]
  obtain ⟨v, rfl⟩ : ∃ v : X ⧸ frattini X, Additive.ofMul v = w := ⟨Additive.toMul w, rfl⟩
  rw [frattiniRep_apply]
  exact ⟨fun h => Additive.ofMul.injective h, fun h => congrArg Additive.ofMul h⟩

theorem finrank_eigenspace_le_pRank (q : ℕ) [Fact q.Prime] [Fact (IsPGroup q X)] (hq2 : q ≠ 2)
    (hXexp : ∀ x : X, x ^ q = 1) (e : E) [Finite (Subgroup.zpowers e)]
    (he : IsPGroup 2 (Subgroup.zpowers e)) :
    Module.finrank (ZMod q) ↥(Module.End.eigenspace (frattiniRep (E := E) (X := X) q e) 1) ≤
      CFSG.pRank q (↥(fixedPointSubgroup (Subgroup.zpowers e) X) ⧸
        commutator ↥(fixedPointSubgroup (Subgroup.zpowers e) X)) := by
  set Y : Subgroup X := fixedPointSubgroup (Subgroup.zpowers e) X with hY
  have hq : q.Prime := Fact.out
  have hYq : IsPGroup q (↥Y ⧸ commutator ↥Y) :=
    ((Fact.out : IsPGroup q X).to_subgroup Y).to_quotient (commutator ↥Y)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hYq
  have hexp : ∀ x : ↥Y, x ^ q = 1 := fun x => Subtype.ext (by simpa using hXexp x)
  have hrank := (CFSG.RankThree.PartTwo.quotient_commutator_rank hq hexp hk).2
  have h1 : q ^ Module.finrank (ZMod q) ↥(Module.End.eigenspace
      (frattiniRep (E := E) (X := X) q e) 1) ≤ q ^ k := by
    have h2 : Nat.card ↥(Module.End.eigenspace (frattiniRep (E := E) (X := X) q e) 1) =
        q ^ Module.finrank (ZMod q) ↥(Module.End.eigenspace
          (frattiniRep (E := E) (X := X) q e) 1) := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod q), Nat.card_zmod]
    rw [← h2, ← hk, card_eigenspace_eq]
    exact card_fixed_le hq2 e he
  rw [hrank]
  exact (Nat.pow_le_pow_iff_right hq.one_lt).mp h1

end Fixed

section Rank

variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
theorem commutator_le_center_of_le (hXcl : commutator X ≤ Subgroup.center X) (Y : Subgroup X) :
    commutator ↥Y ≤ Subgroup.center ↥Y := by
  rw [commutator_def, Subgroup.commutator_le]
  intro a _ b _
  rw [Subgroup.mem_center_iff]
  intro z
  apply Subtype.ext
  have h1 : ⁅(a : X), (b : X)⁆ ∈ Subgroup.center X := by
    apply hXcl
    rw [commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have h2 := Subgroup.mem_center_iff.mp h1 (z : X)
  have e : ((⁅a, b⁆ : ↥Y) : X) = ⁅(a : X), (b : X)⁆ := by simp [commutatorElement_def]
  rw [Subgroup.coe_mul, Subgroup.coe_mul, e]
  exact h2

variable (q : ℕ) [Fact q.Prime] [Fact (IsPGroup q X)]

theorem pRank_quotient_commutator_le (hXexp : ∀ x : X, x ^ q = 1)
    (hXcl : commutator X ≤ Subgroup.center X) (Y : Subgroup X) :
    (CFSG.pRank q ↥Y ≤ 3 → CFSG.pRank q (↥Y ⧸ commutator ↥Y) ≤ 4) ∧
      (CFSG.pRank q ↥Y ≤ 2 → CFSG.pRank q (↥Y ⧸ commutator ↥Y) ≤ 2) := by
  have hYq : IsPGroup q ↥Y := (Fact.out : IsPGroup q X).to_subgroup Y
  have hexp : ∀ x : ↥Y, x ^ q = 1 := fun x => Subtype.ext (by simpa using hXexp x)
  obtain ⟨h1, -, h3⟩ := CFSG.RankThree.PartTwo.class_two_small_rank_order_bounds hYq hexp
    (commutator_le_center_of_le hXcl Y)
  exact ⟨h3, h1⟩

theorem card_frattini_quotient_le (hXexp : ∀ x : X, x ^ q = 1) :
    Nat.card (X ⧸ frattini X) ≤ q ^ CFSG.pRank q (X ⧸ commutator X) := by
  have hcomm : IsMulCommutative (X ⧸ frattini X) :=
    (isElementaryAbelian_quotient_frattini (p := q) (R := X)).toIsMulCommutative
  have hker : commutator X ≤ (QuotientGroup.mk' (frattini X)).ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm.is_comm.comm _ _
  let g : X ⧸ commutator X →* X ⧸ frattini X :=
    QuotientGroup.lift (commutator X) (QuotientGroup.mk' (frattini X)) hker
  have hsurj : Function.Surjective g := by
    intro v
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective v
    exact ⟨(x : X ⧸ commutator X), rfl⟩
  have hXq : IsPGroup q (X ⧸ commutator X) := (Fact.out : IsPGroup q X).to_quotient _
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hXq
  have hrank := (CFSG.RankThree.PartTwo.quotient_commutator_rank (Fact.out : q.Prime) hXexp hk).2
  rw [hrank, ← hk]
  exact Nat.card_le_card_of_surjective g hsurj

end Rank

section Main

open SemidirectProduct

theorem kernel_elimination_core
    {p q d : ℕ} (hp : p.Prime) (hq : q.Prime) (hp3 : 3 < p) (hq2 : q ≠ 2) (hpq : p ≠ q)
    (hpd : (p = 7 ∧ d = 3) ∨ (p = 5 ∧ d = 4))
    {X : Type*} [Group X] [Finite X] (hXq : IsPGroup q X) (hXexp : ∀ x : X, x ^ q = 1)
    (hXcl : commutator X ≤ Subgroup.center X)
    {S : Type*} [Group S] [Finite S] [IsElementaryAbelian 2 S] (hS : Nat.card S = 2 ^ d)
    {A : Type*} [Group A] [Finite A] [IsElementaryAbelian p A] (φ : A →* MulAut S)
    (hφ : Nat.card φ.range = p)
    (hirr : ∀ U : Subgroup S, (∀ a : A, ∀ x ∈ U, φ a x ∈ U) → U = ⊥ ∨ U = ⊤)
    [MulDistribMulAction (S ⋊[φ] A) X]
    (hfaith : ∀ s : S, (∀ x : X, (inl s : S ⋊[φ] A) • x = x) → s = 1)
    (hirrX : IrredFrattini (S ⋊[φ] A) X)
    (hrank : ∀ s : S, s ≠ 1 →
      CFSG.pRank q (fixedPointSubgroup (Subgroup.zpowers (inl s : S ⋊[φ] A)) X) ≤ 3) :
    Nat.card (X ⧸ frattini X) = q ^ p ∧ 4 ≤ CFSG.pRank q X ∧
    (∃ s : S, s ≠ 1 ∧
      CFSG.pRank q (fixedPointSubgroup (Subgroup.zpowers (inl s : S ⋊[φ] A)) X) = 3) ∧
    (p = 7 → ∀ s : S, s ≠ 1 →
      CFSG.pRank q (fixedPointSubgroup (Subgroup.zpowers (inl s : S ⋊[φ] A)) X) = 3) ∧
    (p = 5 → 10 ≤ Set.ncard {s : S | s ≠ 1 ∧
      CFSG.pRank q (fixedPointSubgroup (Subgroup.zpowers (inl s : S ⋊[φ] A)) X) = 3}) ∧
    ((∀ b : A, (∀ s : S, φ b s = s) → ∀ x : X, (inr b : S ⋊[φ] A) • x = x) ∨ q % p = 1) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact q.Prime := ⟨hq⟩
  have : Fact (IsPGroup q X) := ⟨hXq⟩
  have hq2' : (2 : ZMod q) ≠ 0 := by
    intro h
    have h1 : ((2 : ℕ) : ZMod q) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h1
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h1)
  let _ : CommGroup S := IsMulCommutative.instCommGroup
  let _ : Module (ZMod 2) (Additive S) := IsElementaryAbelian.isVectorSpace 2
  let ρ : Representation (ZMod q) (S ⋊[φ] A) (Additive (X ⧸ frattini X)) :=
    frattiniRep (E := S ⋊[φ] A) (X := X) q
  have hρ : ρ.IsIrreducible := isIrreducible_frattiniRep q hirrX
  have hord : ∀ s : S, orderOf (inl s : S ⋊[φ] A) ∣ 2 ^ d := by
    intro s
    rw [orderOf_injective (inl : S →* S ⋊[φ] A) inl_injective]
    exact hS ▸ orderOf_dvd_natCard s
  have hinj : Function.Injective (ρ.comp (inl : S →* S ⋊[φ] A)) := by
    rw [injective_iff_map_eq_one]
    intro s hs
    apply hfaith
    have hs' : ρ (inl s) = 1 := hs
    have htriv : ∀ x : X, (((inl s : S ⋊[φ] A) • x : X) : X ⧸ frattini X) =
        (x : X ⧸ frattini X) := by
      intro x
      have h1 := frattiniRep_apply_mk (E := S ⋊[φ] A) (X := X) q (inl s) x
      have h2 : ρ (inl s) (Additive.ofMul (x : X ⧸ frattini X)) =
          Additive.ofMul (x : X ⧸ frattini X) := by rw [hs']; rfl
      exact Additive.ofMul.injective (h1.symm.trans h2)
    refine smul_eq_of_smul_mk_eq hXq (inl s) (fun hdvd => ?_) htriv
    have h2 : q ∣ 2 := hq.dvd_of_dvd_pow (hdvd.trans (hord s))
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h2)
  have hfin : ∀ s : S, Finite (Subgroup.zpowers (inl s : S ⋊[φ] A)) := by
    intro s
    refine finite_zpowers.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨Nat.card S, Nat.card_pos, ?_⟩)
    rw [← map_pow, pow_card_eq_one', map_one]
  have hp2 : ∀ s : S, IsPGroup 2 (Subgroup.zpowers (inl s : S ⋊[φ] A)) := by
    intro s
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (hord s)
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers]; exact hj)
  have hfd : ∀ s : S, Module.finrank (ZMod q) ↥(Module.End.eigenspace (ρ (inl s)) 1) ≤
      CFSG.pRank q (↥(fixedPointSubgroup (Subgroup.zpowers (inl s : S ⋊[φ] A)) X) ⧸
        commutator ↥(fixedPointSubgroup (Subgroup.zpowers (inl s : S ⋊[φ] A)) X)) := by
    intro s
    have := hfin s
    exact finrank_eigenspace_le_pRank q hq2 hXexp (inl s) (hp2 s)
  have h4 : ∀ s : S, s ≠ 1 →
      Module.finrank (ZMod q) ↥(Module.End.eigenspace (ρ (inl s)) 1) ≤ 4 := fun s hs =>
    (hfd s).trans ((pRank_quotient_commutator_le q hXexp hXcl _).1 (hrank s hs))
  obtain ⟨-, -, e, -, hwt, hdimW, h7, h5, hle⟩ :=
    small_binary_prime_orbit_fixed_space_counts hpd hS hφ hirr hq2' ρ hρ hinj
  obtain ⟨hdim, he⟩ : e = 1 ∧ Module.finrank (ZMod q) (Additive (X ⧸ frattini X)) = p :=
    hle h4
  have hcardV : Nat.card (X ⧸ frattini X) = q ^ p := by
    have h1 : Nat.card (Additive (X ⧸ frattini X)) = q ^ p := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod q), Nat.card_zmod, he]
    exact h1
  have hY3 : ∀ s : S, s ≠ 1 →
      Module.finrank (ZMod q) ↥(Module.End.eigenspace (ρ (inl s)) 1) = 3 →
      CFSG.pRank q (fixedPointSubgroup (Subgroup.zpowers (inl s : S ⋊[φ] A)) X) = 3 := by
    intro s hs hf
    refine le_antisymm (hrank s hs) ?_
    by_contra hlt
    have h2 := (pRank_quotient_commutator_le q hXexp hXcl
      (fixedPointSubgroup (Subgroup.zpowers (inl s : S ⋊[φ] A)) X)).2 (by omega)
    have h3 := hfd s
    omega
  refine ⟨hcardV, ?_, ?_, ?_, ?_, ?_⟩
  · by_contra hlt
    have h3 : CFSG.pRank q X ≤ 3 := by omega
    obtain ⟨-, -, h34⟩ := CFSG.RankThree.PartTwo.class_two_small_rank_order_bounds hXq hXexp hXcl
    have h4' := h34 h3
    have h5' := card_frattini_quotient_le q hXexp
    rw [hcardV] at h5'
    have h6 : q ^ p ≤ q ^ 4 := h5'.trans (Nat.pow_le_pow_right hq.pos h4')
    have := (Nat.pow_le_pow_iff_right hq.one_lt).mp h6
    omega
  · rcases hpd with ⟨hp7, hd⟩ | ⟨hp5, hd⟩
    · have : Nontrivial S := Finite.one_lt_card_iff_nontrivial.mp (by rw [hS, hd]; norm_num)
      obtain ⟨s, hs⟩ := exists_ne (1 : S)
      exact ⟨s, hs, hY3 s hs (by rw [h7 hp7 s hs, hdim])⟩
    · obtain ⟨hcnt, -, -⟩ := h5 hp5
      obtain ⟨s, hs, hf⟩ := Set.nonempty_of_ncard_ne_zero (by rw [hcnt]; norm_num)
      exact ⟨s, hs, hY3 s hs (by rw [hf, hdim])⟩
  · intro hp7 s hs
    exact hY3 s hs (by rw [h7 hp7 s hs, hdim])
  · intro hp5
    obtain ⟨hcnt, -, -⟩ := h5 hp5
    rw [← hcnt]
    refine Set.ncard_le_ncard (fun s hs => ⟨hs.1, hY3 s hs.1 (by rw [hs.2, hdim])⟩)
      (Set.toFinite _)
  · by_cases hqp : q % p = 1
    · exact Or.inr hqp
    left
    intro b hb
    have hbp : (inr b : S ⋊[φ] A) ^ p = 1 := by
      rw [← map_pow, Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p p A) b, map_one]
    have hT : ρ (inr b) ^ p = 1 := by rw [← map_pow, hbp, map_one]
    have hcomm : ∀ s : S, ρ (inr b) * ρ (inl s) = ρ (inl s) * ρ (inr b) := by
      intro s
      have h1 := inl_aut (φ := φ) b s
      rw [hb s, map_inv] at h1
      have h2 : (inr b : S ⋊[φ] A) * inl s = inl s * inr b := by
        calc (inr b : S ⋊[φ] A) * inl s = (inr b * inl s * (inr b)⁻¹) * inr b := by group
          _ = inl s * inr b := by rw [← h1]
      rw [← map_mul, ← map_mul, h2]
    have hmaps : ∀ χ, ∀ w ∈ signWeightSpace (ρ.comp (inl : S →* S ⋊[φ] A)) χ,
        ρ (inr b) w ∈ signWeightSpace (ρ.comp (inl : S →* S ⋊[φ] A)) χ := by
      intro χ w hw
      rw [mem_signWeightSpace] at hw ⊢
      intro s
      have h1 := hw s
      have h2 : (ρ.comp (inl : S →* S ⋊[φ] A)) s (ρ (inr b) w) =
          ρ (inr b) ((ρ.comp (inl : S →* S ⋊[φ] A)) s w) := by
        have := congrArg (fun f : Module.End (ZMod q) (Additive (X ⧸ frattini X)) => f w)
          (hcomm s)
        exact this.symm
      rw [h2, h1, map_smul]
    have hscalar : ∀ χ, ∃ c : ZMod q,
        ∀ w ∈ signWeightSpace (ρ.comp (inl : S →* S ⋊[φ] A)) χ, ρ (inr b) w = c • w := by
      intro χ
      by_cases hχ : signWeightSpace (ρ.comp (inl : S →* S ⋊[φ] A)) χ = ⊥
      · exact ⟨0, fun w hw => by rw [hχ, Submodule.mem_bot] at hw; simp [hw]⟩
      · have h1 : Module.finrank (ZMod q)
            ↥(signWeightSpace (ρ.comp (inl : S →* S ⋊[φ] A)) χ) = 1 := by rw [hwt χ hχ, hdim]
        obtain ⟨v, hv0, hspan⟩ := finrank_eq_one_iff'.mp h1
        have hTv : ρ (inr b) (v : Additive (X ⧸ frattini X)) ∈
            signWeightSpace (ρ.comp (inl : S →* S ⋊[φ] A)) χ := hmaps χ v v.2
        obtain ⟨c, hc⟩ := hspan ⟨_, hTv⟩
        refine ⟨c, fun w hw => ?_⟩
        obtain ⟨a, ha⟩ := hspan ⟨w, hw⟩
        have hc' : c • (v : Additive (X ⧸ frattini X)) = ρ (inr b) (v : Additive _) :=
          congrArg Subtype.val hc
        have ha' : a • (v : Additive (X ⧸ frattini X)) = w := congrArg Subtype.val ha
        rw [← ha', map_smul, ← hc', smul_comm]
    have hone : ∀ χ, ∀ w ∈ signWeightSpace (ρ.comp (inl : S →* S ⋊[φ] A)) χ,
        ρ (inr b) w = w := by
      intro χ w hw
      obtain ⟨c, hc⟩ := hscalar χ
      by_cases hχ : signWeightSpace (ρ.comp (inl : S →* S ⋊[φ] A)) χ = ⊥
      · rw [hχ, Submodule.mem_bot] at hw
        simp [hw]
      · obtain ⟨w₀, hw₀, hw₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hχ
        have hcw0 : ρ (inr b) w₀ = c • w₀ := hc w₀ hw₀
        have hpow : (ρ (inr b) ^ p) w₀ = c ^ p • w₀ :=
          Module.End.HasEigenvector.pow_apply
            ⟨Module.End.mem_eigenspace_iff.mpr hcw0, hw₀0⟩ p
        rw [hT] at hpow
        have hcp : c ^ p = 1 := by
          refine smul_left_injective (ZMod q) hw₀0 ?_
          simpa using hpow.symm
        by_cases hc1 : c = 1
        · rw [hc w hw, hc1, one_smul]
        · exfalso
          apply hqp
          have hc0 : c ≠ 0 := by
            intro h
            rw [h, zero_pow hp.ne_zero] at hcp
            exact zero_ne_one hcp
          have hord : orderOf c = p := orderOf_eq_prime hcp hc1
          have hdvd : orderOf c ∣ q - 1 :=
            orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one hc0)
          rw [hord] at hdvd
          obtain ⟨m, hm⟩ := hdvd
          have hq1 : q = p * m + 1 := by have := hq.one_lt; omega
          rw [hq1, Nat.mul_add_mod, Nat.mod_eq_of_lt hp.one_lt]
    have hT1 : ρ (inr b) = 1 := by
      have : Fintype S := Fintype.ofFinite S
      have hfinD : Finite (Module.Dual (ZMod 2) (Additive S)) :=
        Finite.of_injective (fun f : Module.Dual (ZMod 2) (Additive S) => (f : Additive S → ZMod 2))
          DFunLike.coe_injective
      have : Fintype (Module.Dual (ZMod 2) (Additive S)) := Fintype.ofFinite _
      have htop : ⨆ χ, signWeightSpace (ρ.comp (inl : S →* S ⋊[φ] A)) χ = ⊤ :=
        iSup_signWeightSpace_eq_top (ρ.comp (inl : S →* S ⋊[φ] A)) hq2'
      have hle : (⨆ χ, signWeightSpace (ρ.comp (inl : S →* S ⋊[φ] A)) χ) ≤
          LinearMap.ker (ρ (inr b) - 1) := by
        refine iSup_le fun χ w hw => ?_
        simp only [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply]
        rw [hone χ w hw, sub_self]
      refine LinearMap.ext fun w => ?_
      have hw : w ∈ ⨆ χ, signWeightSpace (ρ.comp (inl : S →* S ⋊[φ] A)) χ := by
        rw [htop]
        exact Submodule.mem_top
      have h1 := hle hw
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply] at h1
      rw [Module.End.one_apply]
      exact sub_eq_zero.mp h1
    have htriv : ∀ x : X, (((inr b : S ⋊[φ] A) • x : X) : X ⧸ frattini X) =
        (x : X ⧸ frattini X) := by
      intro x
      have h1 := frattiniRep_apply_mk (E := S ⋊[φ] A) (X := X) q (inr b) x
      have h2 : ρ (inr b) (Additive.ofMul (x : X ⧸ frattini X)) =
          Additive.ofMul (x : X ⧸ frattini X) := by rw [hT1]; rfl
      exact Additive.ofMul.injective (h1.symm.trans h2)
    intro x
    refine smul_eq_of_smul_mk_eq hXq (inr b) (fun hdvd => ?_) htriv x
    have h2 : orderOf (inr b : S ⋊[φ] A) ∣ p := orderOf_dvd_of_pow_eq_one hbp
    exact hpq ((Nat.prime_dvd_prime_iff_eq hq hp).mp (hdvd.trans h2)).symm

end Main

end CFSG.RankThree.PartOne.Quotient36
