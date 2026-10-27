module

public import CFSG.LocalAnalysis.WeakClosure81.OddTranspCompFactorDerivedEq
public import CFSG.OddTranspositions.PartFour.Thirteen
import CFSG.OddTranspositions.PartFour.ThirteenList
import CFSG.OddTranspositions.WidthOne
import CFSG.OddTranspositions.PartThree.EightOne.Quotient
import CFSG.LocalAnalysis.WeakClosure81.W18ASNineCF
import CFSG.LocalAnalysis.SeitzReduction.RankOneU3StarLocal
public import CFSG.Quasithin.Vol2.Ch8Sec2L829LN0
public import CFSG.Quasithin.Vol2.Ch8Sec2L829LN1
public import CFSG.Timmesfeld.Bridge.OddTranspBasic

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.LocalAnalysis.WeakClosure81 CFSG.Quasithin CFSG.Quasithin.H13.L829N

theorem isCompositionFactor_comm_of_isSolvable {X : Type} [Group X] (hX : Group.IsSolvable X)
    {L : Type} [Group L] (h : E1.IsCompositionFactor X L) : ∀ a b : L, a * b = b * a := by
  obtain ⟨N, M, hN, -, -, -, hs, ⟨e⟩⟩ := h
  haveI := hN
  haveI := hs
  haveI := hX
  have hc := IsSimpleGroup.comm_iff_isSolvable.mpr
    (inferInstance : Group.IsSolvable (↥M ⧸ N.subgroupOf M))
  intro a b
  apply e.symm.injective
  rw [map_mul, map_mul, hc]

theorem isCompositionFactor_perm {r : ℕ} {T : Type} [Group T]
    (h : E1.IsCompositionFactor (Equiv.Perm (Fin r)) T) (hnab : ∃ a b : T, a * b ≠ b * a) :
    5 ≤ r ∧ Nonempty (T ≃* alternatingGroup (Fin r)) := by
  obtain ⟨a, b, hab⟩ := hnab
  by_cases hr : r ≤ 4
  · exact absurd (isCompositionFactor_comm_of_isSolvable
      (Equiv.Perm.isSolvable (by simpa using hr)) h a b) hab
  have hr5 : 5 ≤ r := by omega
  haveI : IsSimpleGroup (alternatingGroup (Fin r)) :=
    alternatingGroup.isSimpleGroup (by simpa using hr5)
  rcases isCompositionFactor_of_normal (alternatingGroup (Fin r)) h with hA | hQ
  · obtain ⟨e⟩ := isCompositionFactor_mulEquiv_of_isSimpleGroup hA
    exact ⟨hr5, ⟨e.symm⟩⟩
  · exfalso
    have hcomm : ∀ x y : Equiv.Perm (Fin r) ⧸ alternatingGroup (Fin r), x * y = y * x := by
      intro x y
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
        Equiv.Perm.mem_alternatingGroup]
      simp [mul_comm]
    exact hab (isCompositionFactor_commute hcomm hQ a b)

noncomputable def evalZeroKerEquiv (L : Type) [Group L] (r : ℕ) :
    ↥(Pi.evalMonoidHom (fun _ : Fin (r + 1) => L) 0).ker ≃* (Fin r → L) :=
  MulEquiv.ofBijective
    ({ toFun := fun x i => (x : Fin (r + 1) → L) i.succ
       map_one' := rfl
       map_mul' := fun _ _ => rfl } :
      ↥(Pi.evalMonoidHom (fun _ : Fin (r + 1) => L) 0).ker →* (Fin r → L))
    ⟨fun x y hxy => by
      apply Subtype.ext
      funext i
      refine Fin.cases ?_ (fun j => congrFun hxy j) i
      have hx := x.2
      have hy := y.2
      rw [MonoidHom.mem_ker] at hx hy
      exact hx.trans hy.symm,
    fun y => ⟨⟨Fin.cons 1 y, by simp [MonoidHom.mem_ker]⟩, by funext i; simp⟩⟩

theorem isCompositionFactor_pi {L : Type} [Group L] [IsSimpleGroup L] (r : ℕ) :
    ∀ {T : Type} [Group T], E1.IsCompositionFactor (Fin r → L) T → Nonempty (T ≃* L) := by
  induction r with
  | zero =>
    intro T _ h
    exfalso
    obtain ⟨N, M, hN, -, -, -, hs, -⟩ := h
    haveI := hN
    haveI := hs
    obtain ⟨q, hq⟩ := exists_ne (1 : ↥M ⧸ N.subgroupOf M)
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    exact hq (by rw [Subsingleton.elim x 1, QuotientGroup.mk_one])
  | succ r ih =>
    intro T _ h
    have hev : Function.Surjective (Pi.evalMonoidHom (fun _ : Fin (r + 1) => L) 0) :=
      fun l => ⟨fun _ => l, rfl⟩
    rcases isCompositionFactor_of_normal (Pi.evalMonoidHom (fun _ : Fin (r + 1) => L) 0).ker h with
      hA | hQ
    · exact ih ((isCompositionFactor_congr (evalZeroKerEquiv L r)).mp hA)
    · obtain ⟨e⟩ := isCompositionFactor_mulEquiv_of_isSimpleGroup
        ((isCompositionFactor_congr (QuotientGroup.quotientKerEquivOfSurjective _ hev)).mp hQ)
      exact ⟨e.symm⟩

theorem oddTranspFactor_of_isCompositionFactor_l2Wreath {f r : ℕ} (hf : 2 ≤ f) {T : Type}
    [Group T] (h : E1.IsCompositionFactor (L2Wreath f r) T) (hnab : ∃ a b : T, a * b ≠ b * a) :
    OddTranspFactor T := by
  haveI : IsSimpleGroup (CFSG.Theory.Comparator.PSL2Model f) :=
    IsBenderGroup.isSimpleGroup (.isPSL2 f hf (MulEquiv.refl _))
  haveI hN : (SemidirectProduct.inl : (Fin r → CFSG.Theory.Comparator.PSL2Model f) →*
      L2Wreath f r).range.Normal := by
    rw [SemidirectProduct.range_inl_eq_ker_rightHom]
    infer_instance
  rcases isCompositionFactor_of_normal (SemidirectProduct.inl :
      (Fin r → CFSG.Theory.Comparator.PSL2Model f) →* L2Wreath f r).range h with hB | hQ
  · obtain ⟨e⟩ := isCompositionFactor_pi r
      ((isCompositionFactor_congr (MonoidHom.ofInjective SemidirectProduct.inl_injective).symm).mp
        hB)
    exact Or.inr (Or.inl ⟨0, f, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (CFSG.SeitzReduction.RankOne.lieModel_psl2_of_mulEquiv hf e)))))⟩)
  · have e : L2Wreath f r ⧸ (SemidirectProduct.inl : (Fin r → CFSG.Theory.Comparator.PSL2Model f) →*
        L2Wreath f r).range ≃* Equiv.Perm (Fin r) :=
      (QuotientGroup.quotientMulEquivOfEq SemidirectProduct.range_inl_eq_ker_rightHom).trans
        (QuotientGroup.quotientKerEquivOfSurjective _ SemidirectProduct.rightHom_surjective)
    obtain ⟨hr, ⟨e'⟩⟩ := isCompositionFactor_perm ((isCompositionFactor_congr e).mp hQ) hnab
    exact Or.inl ⟨r, hr, ⟨e'⟩⟩

section AlmostSimple

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem oddTranspFactor_of_almostSimpleCase (hD : OddTranspositionCompFactorDerivedEq)
    (hS : Setup G D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hA : AlmostSimpleCase G D) {T : Type} [Group T] (hT : E1.IsCompositionFactor G T)
    (hnab : ∃ a b : T, a * b ≠ b * a) : OddTranspFactor T := by
  obtain ⟨M, hMn, hM, -, hMs, hcent, hidx, hW, hcls⟩ := hA
  obtain ⟨a, b, hab⟩ := hnab
  have hdisj : ∀ x ∈ D, x ∉ M := by
    rcases hS.subset_or_disjoint M with hDM | hdisj
    · rw [hS.eq_top_of_subset M hDM, Subgroup.index_top] at hidx
      omega
    · exact hdisj
  have hSQ := hS.map (QuotientGroup.mk' M) (QuotientGroup.mk'_surjective M)
    (fun d hd h => hdisj d hd ((QuotientGroup.eq_one_iff d).mp h))
  have h2 : Nat.card ((G ⧸ M) ⧸ CFSG.oddCore (G ⧸ M)) = 2 :=
    index_oddCore_eq_two_of_widthOne hSQ hW
  have hsolvQ : Group.IsSolvable (G ⧸ M) := by
    haveI : Group.IsSolvable (CFSG.oddCore (G ⧸ M)) :=
      CFSG.FeitThompson.isSolvable_of_odd_natCard _ PartThree.EightOne.odd_card_oddCore
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : IsCyclic ((G ⧸ M) ⧸ CFSG.oddCore (G ⧸ M)) := isCyclic_of_prime_card h2
    haveI : Group.IsSolvable ((G ⧸ M) ⧸ CFSG.oddCore (G ⧸ M)) := by
      letI := IsCyclic.commGroup (α := (G ⧸ M) ⧸ CFSG.oddCore (G ⧸ M))
      exact Group.isSolvable_of_comm fun x y => mul_comm x y
    exact Group.isSolvable_of_subgroup_quotient (CFSG.oddCore (G ⧸ M))
  rcases isCompositionFactor_of_normal M hT with hTM | hTQ
  ·
    obtain ⟨u, hu⟩ := hS.nonempty
    obtain ⟨hord, hodd, hncl, -, -, hradL, hder⟩ :=
      sup_zpowers_hyps hS hrad hM hMs hcent hu (hcls u hu)
    haveI := hMs
    obtain ⟨e⟩ := isCompositionFactor_mulEquiv_of_isSimpleGroup hTM
    haveI : IsSimpleGroup T := e.symm.isSimpleGroup
    haveI : (M.subgroupOf (M ⊔ Subgroup.zpowers u)).Normal := Subgroup.normal_subgroupOf
    let ψ : ↥(M.subgroupOf (M ⊔ Subgroup.zpowers u)) ≃* T :=
      (Subgroup.subgroupOfEquivOfLe le_sup_left).trans e
    have hTL : E1.IsCompositionFactor ↥(M ⊔ Subgroup.zpowers u) T :=
      isCompositionFactor_of_subnormal_surjection
        (inferInstance : (M.subgroupOf (M ⊔ Subgroup.zpowers u)).Normal).isSubnormal
        inferInstance ψ.toMonoidHom ψ.surjective
    exact hD _ _ hord hodd hncl hradL hder T hTL ⟨a, b, hab⟩
  · exact absurd (isCompositionFactor_comm_of_isSolvable hsolvQ hTQ a b) hab

end AlmostSimple

theorem oddTranspositionCompFactorInput_of_derivedEq
    (hD : OddTranspositionCompFactorDerivedEq) :
    OddTranspositionCompFactorInput := by
  intro X _ _ s hord hodd hncl T _ hT hnab
  obtain ⟨a, b, hab⟩ := hnab
  haveI hRn : (CFSG.solvableRadical X).Normal := Subgroup.sSup_normal _ fun _ hN => hN.1
  have hRs : Group.IsSolvable (CFSG.solvableRadical X) :=
    CFSG.Timmesfeld.Bridge.OddTransp.isSolvable_solvableRadical
  rcases isCompositionFactor_of_normal (CFSG.solvableRadical X) hT with hTR | hTY
  · exact absurd (isCompositionFactor_comm_of_isSolvable hRs hTR a b) hab
  have hS0 := setup_setOf_isConj hodd hncl
  by_cases hsR : s ∈ CFSG.solvableRadical X
  ·
    exfalso
    have hDR : {x : X | IsConj s x} ⊆ CFSG.solvableRadical X := fun x hx => by
      obtain ⟨g, rfl⟩ := isConj_iff.mp hx
      exact hRn.conj_mem s hsR g
    have htop := hS0.eq_top_of_subset _ hDR
    have hXs : Group.IsSolvable X :=
      solvable_of_surjective (f := (CFSG.solvableRadical X).subtype)
        (fun x => ⟨⟨x, htop ▸ Subgroup.mem_top x⟩, rfl⟩)
    exact hab (isCompositionFactor_comm_of_isSolvable hXs hT a b)
  have h1 : ∀ d ∈ {x : X | IsConj s x}, QuotientGroup.mk' (CFSG.solvableRadical X) d ≠ 1 := by
    intro d hd h
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
    apply hsR
    obtain ⟨g, rfl⟩ := isConj_iff.mp hd
    have := hRn.conj_mem _ h g⁻¹
    simpa [mul_assoc] using this
  have hSY := hS0.map (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _) h1
  rw [hSY.eq_setOf_isConj ⟨s, IsConj.refl s, rfl⟩] at hSY
  have hradY : ∀ N : Subgroup (X ⧸ CFSG.solvableRadical X), N.Normal → Group.IsSolvable N →
      N = ⊥ := fun N hN hNs =>
    CFSG.Timmesfeld.Bridge.OddTransp.eq_bot_of_quotient_solvableRadical N hN hNs
  rcases derivedSeries_eq_or_l2Wreath_or_almostSimpleCase hSY hradY with
    hder | ⟨f, r, hf, -, Φ, -⟩ | hA
  · exact hD _ _ (hSY.oddT.1 _ (IsConj.refl _)) hSY.oddT
      (by rw [← closure_setOf_isConj_eq_normalClosure]; exact hSY.gen) hradY hder T hTY
      ⟨a, b, hab⟩
  · exact oddTranspFactor_of_isCompositionFactor_l2Wreath hf
      ((isCompositionFactor_congr Φ).mp hTY) ⟨a, b, hab⟩
  · exact oddTranspFactor_of_almostSimpleCase hD hSY hradY hA hTY ⟨a, b, hab⟩

end CFSG.OddTranspositions.PartFour
