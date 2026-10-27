module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.proposition_4_11
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_1
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_b
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_10
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.ElementaryAbelianAction

namespace CFSG
end CFSG
open CFSG

open scoped FixedPoints IsMulCommutative commutatorElement

/-! # Infrastructure for Theorem 4.12(a) from BG Section 4 -/

universe u

section Main

open scoped FixedPoints IsMulCommutative commutatorElement

private theorem CFSG.derivedSubgroup_isCyclic_of_isMetacyclic
    {R : Type*} [Group R] [Finite R] (hmeta : IsMetacyclic R) :
    IsCyclic (derivedSubgroup R) := by
  classical
  obtain ⟨S, hSnorm, hScyc, hquotcyc⟩ := hmeta
  let : S.Normal := hSnorm
  have hquotcomm : IsMulCommutative (R ⧸ S) := hquotcyc.isMulCommutative
  have hder_le_S : derivedSubgroup R ≤ S := by
    simpa [derivedSubgroup, derivedSeries_one, commutator] using
      (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := S)).1 hquotcomm
  exact Subgroup.isCyclic_of_le hder_le_S

private theorem CFSG.exists_maximal_cyclic_invariant_subgroup_containing_derived
    {R A : Type*} [Group R] [Finite R] [Group A] [Finite A] [MulDistribMulAction A R]
    (hdercyc : IsCyclic (derivedSubgroup R)) :
    ∃ S : Subgroup R,
      derivedSubgroup R ≤ S ∧ IsCyclic S ∧ IsInvariant A R S ∧
        ∀ T : Subgroup R, derivedSubgroup R ≤ T → IsCyclic T → IsInvariant A R T →
          S ≤ T → T = S := by
  classical
  let s : Set (Subgroup R) := {S | derivedSubgroup R ≤ S ∧ IsCyclic S ∧ IsInvariant A R S}
  have hsfin : s.Finite := Set.toFinite s
  have hsne : s.Nonempty := by
    refine ⟨derivedSubgroup R, ?_⟩
    refine ⟨le_rfl, hdercyc, ?_⟩
    exact isInvariant_of_characteristic (A := A) (G := R) (derivedSubgroup R)
  obtain ⟨S, hSmax⟩ := hsfin.exists_maximal hsne
  refine ⟨S, hSmax.1.1, hSmax.1.2.1, hSmax.1.2.2, ?_⟩
  intro T hderT hTcyc hTinv hST
  exact le_antisymm (hSmax.2 ⟨hderT, hTcyc, hTinv⟩ hST) hST

private theorem CFSG.mulAut_isMulCommutative_of_isCyclic
    {G : Type*} [Group G] [IsCyclic G] : IsMulCommutative (MulAut G) := by
  classical
  let e := IsCyclic.mulAutMulEquiv (G := G)
  refine ⟨⟨fun a b => ?_⟩⟩
  apply e.injective
  simp [mul_comm]

private noncomputable def CFSG.conjugationMulAutOfNormal
    {G : Type*} [Group G] (S : Subgroup G) [S.Normal] (g : G) : MulAut S :=
  {
    toFun := fun s => ⟨g * (s : G) * g⁻¹, (inferInstance : S.Normal).conj_mem (s : G) s.2 g⟩
    invFun := fun s =>
      ⟨g⁻¹ * (s : G) * (g⁻¹)⁻¹, (inferInstance : S.Normal).conj_mem (s : G) s.2 g⁻¹⟩
    left_inv := by
      intro s
      ext
      simp [mul_assoc]
    right_inv := by
      intro s
      ext
      simp [mul_assoc]
    map_mul' := by
      intro x y
      ext
      simp [mul_assoc]
  }

private noncomputable def CFSG.actionMulAutOfInvariant
    {G A : Type*} [Group G] [Group A] [MulDistribMulAction A G]
    (S : Subgroup G) [IsInvariant A G S] (a : A) : MulAut S :=
  {
    toFun := fun s =>
      ⟨a • (s : G), (IsInvariant.invariant (A := A) (G := G) (H := S) a (s : G)).1 s.2⟩
    invFun := fun s =>
      ⟨a⁻¹ • (s : G),
        (IsInvariant.invariant (A := A) (G := G) (H := S) a⁻¹ (s : G)).1 s.2⟩
    left_inv := by
      intro s
      ext
      simp
    right_inv := by
      intro s
      ext
      simp
    map_mul' := by
      intro x y
      ext
      simp [smul_mul']
  }

private theorem CFSG.action_commutator_generator_le_centralizer_of_cyclic_invariant
    {G A : Type*} [Group G] [Group A] [MulDistribMulAction A G]
    {S : Subgroup G} [S.Normal] [IsInvariant A G S] (hScyc : IsCyclic S)
    (a : A) (g : G) :
    g⁻¹ * (a • g) ∈ Subgroup.centralizer (S : Set G) := by
  classical
  let : IsCyclic S := hScyc
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  let cg : MulAut S := conjugationMulAutOfNormal S g
  let ca : MulAut S := conjugationMulAutOfNormal S (a • g)
  let aa : MulAut S := actionMulAutOfInvariant S a
  have hca : ca = aa * cg * aa⁻¹ := by
    ext x
    simp [ca, aa, cg, conjugationMulAutOfNormal, actionMulAutOfInvariant, mul_assoc, smul_mul',
      smul_inv_smul]
  let : IsMulCommutative (MulAut S) := mulAut_isMulCommutative_of_isCyclic
  have hcomm_aut : aa * cg = cg * aa := IsMulCommutative.is_comm.comm aa cg
  have hca_eq : ca = cg := by
    rw [hca]
    calc
      aa * cg * aa⁻¹ = cg * aa * aa⁻¹ := by rw [hcomm_aut]
      _ = cg := by simp [mul_assoc]
  have happ := congrArg (fun f : MulAut S => f ⟨s, hs⟩) hca_eq
  have hconj_eq : (a • g) * s * (a • g)⁻¹ = g * s * g⁻¹ := by
    simpa [ca, cg, conjugationMulAutOfNormal] using congrArg Subtype.val happ
  have hmul := congrArg (fun t : G => g⁻¹ * t * (a • g)) hconj_eq
  simpa [mul_assoc] using hmul.symm

private theorem CFSG.commutatorAction_le_centralizer_of_cyclic_invariant
    {G A : Type*} [Group G] [Group A] [MulDistribMulAction A G]
    {S : Subgroup G} [S.Normal] [IsInvariant A G S] (hScyc : IsCyclic S) :
    commutatorAction (A := A) (G := G) ≤ Subgroup.centralizer (S : Set G) := by
  rw [commutatorAction_eq_closure (G := G) (A := A)]
  refine (Subgroup.closure_le (K := Subgroup.centralizer (S : Set G))).2 ?_
  intro x hx
  rcases hx with ⟨a, g, rfl⟩
  exact action_commutator_generator_le_centralizer_of_cyclic_invariant (S := S) hScyc a g

private theorem CFSG.le_center_of_commutatorAction_eq_top_of_cyclic_invariant
    {R A : Type*} [Group R] [Group A] [MulDistribMulAction A R]
    {S : Subgroup R} [S.Normal] [IsInvariant A R S] (hScyc : IsCyclic S)
    (hcommtop : commutatorAction (A := A) (G := R) = ⊤) :
    S ≤ Subgroup.center R := by
  have hcomm_le_cent :
      commutatorAction (A := A) (G := R) ≤ Subgroup.centralizer (S : Set R) :=
    commutatorAction_le_centralizer_of_cyclic_invariant (S := S) hScyc
  have htop_le_cent : (⊤ : Subgroup R) ≤ Subgroup.centralizer (S : Set R) := by
    simpa [hcommtop] using hcomm_le_cent
  intro s hs
  rw [Subgroup.mem_center_iff]
  intro r
  have hr_cent : r ∈ Subgroup.centralizer (S : Set R) := htop_le_cent (by simp)
  have hs_comm : s * r = r * s := Subgroup.mem_centralizer_iff.mp hr_cent s hs
  exact hs_comm.symm

private theorem CFSG.isMetacyclic_subgroup_of_isMetacyclic
    {G : Type*} [Group G] [Finite G] (hmeta : IsMetacyclic G) (H : Subgroup G) :
    IsMetacyclic H := by
  classical
  obtain ⟨N, hNnorm, hNcyc, hQcyc⟩ := hmeta
  let K : Subgroup H := N.subgroupOf H
  have hKcyc : IsCyclic K := by
    let L : Subgroup N := (H ⊓ N).subgroupOf N
    let e : K ≃* L :=
      { toFun := fun x => ⟨⟨(x : G), (show (x : G) ∈ N from x.2)⟩, by
          exact ⟨(show (x : G) ∈ H from x.1.2), (show (x : G) ∈ N from x.2)⟩⟩
        invFun := fun y => ⟨⟨(y : G), y.2.1⟩, y.2.2⟩
        left_inv := by intro x; ext; rfl
        right_inv := by intro y; ext; rfl
        map_mul' := by intro x y; ext; rfl }
    exact e.isCyclic.2 (Subgroup.isCyclic_of_le (H := L) (H' := ⊤) (by simp))
  let : N.Normal := hNnorm
  have hKnorm : K.Normal := by
    exact Subgroup.Normal.subgroupOf (G := G) (H := N) (K := H) hNnorm
  let : K.Normal := hKnorm
  let e : (H ⧸ K) ≃* H.map (QuotientGroup.mk' N) := quotientSubgroupRangeEquiv H N
  have hHmap_cyc : IsCyclic (H.map (QuotientGroup.mk' N)) := by
    let : IsCyclic (G ⧸ N) := hQcyc
    exact Subgroup.isCyclic_of_le (H := H.map (QuotientGroup.mk' N)) (H' := ⊤) (by simp)
  have hquot_cyc : IsCyclic (H ⧸ K) := e.isCyclic.2 hHmap_cyc
  exact ⟨K, hKnorm, hKcyc, hquot_cyc⟩

private theorem CFSG.natCard_subgroup_lt_of_ne_top
    {G : Type*} [Group G] [Finite G] (H : Subgroup G) (hH : H ≠ ⊤) :
    Nat.card H < Nat.card G := by
  have hle : Nat.card H ≤ Nat.card G := Subgroup.card_le_card_group H
  exact lt_of_le_of_ne hle (fun hEq => hH (Subgroup.eq_top_of_card_eq (H := H) hEq))


public theorem CFSG.exists_isCompl_isInvariant_of_elementaryAbelian_coprime
    {G A : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    [IsElementaryAbelian p G] [Group A] [Finite A] [MulDistribMulAction A G]
    (hcop : Nat.Coprime p (Nat.card A)) (B : Subgroup G) [IsInvariant A G B] :
    ∃ C : Subgroup G, IsCompl B C ∧ IsInvariant A G C := by
  classical
  let : CommGroup G := IsMulCommutative.instCommGroup
  let : AddCommGroup (Additive G) := Additive.addCommGroup
  let ρ : Representation (ZMod p) A (Additive G) :=
    Theory.Representation.ofElementaryAbelianAction (A := A) (G := G) (p := p)
  let instAdd : AddCommGroup ρ.asModule := Representation.instAddCommGroupAsModule ρ
  let : AddCommGroup ρ.asModule := instAdd
  let instMod : Module (MonoidAlgebra (ZMod p) A) ρ.asModule :=
    Representation.instModuleMonoidAlgebraAsModule ρ
  let : Module (MonoidAlgebra (ZMod p) A) ρ.asModule := instMod
  let η : Subgroup G ≃o Submodule (ZMod p) (Additive G) :=
    Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule (n := p))
  have hBinv : η B ∈ ρ.invtSubmodule := by
    rw [Representation.mem_invtSubmodule]
    intro a
    rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
    intro x hx
    have hxB : Additive.toMul x ∈ B := by simpa [η] using hx
    simpa [ρ, η] using
      (IsInvariant.invariant (A := A) (G := G) (H := B) a (Additive.toMul x)).1 hxB
  let Bpack : ρ.invtSubmodule := ⟨η B, hBinv⟩
  have : Fintype A := Fintype.ofFinite A
  have : NeZero (Fintype.card A : ZMod p) := by
    constructor
    intro hzero
    have hdiv : p ∣ Fintype.card A :=
      (ZMod.natCast_eq_zero_iff (Fintype.card A) p).1 hzero
    have hnot : ¬ p ∣ Fintype.card A := by
      exact ((Fact.out : Nat.Prime p).coprime_iff_not_dvd).1
        (by simpa [Nat.card_eq_fintype_card] using hcop)
    exact hnot hdiv
  let Bmod : @Submodule (MonoidAlgebra (ZMod p) A) ρ.asModule _ instAdd.toAddCommMonoid instMod :=
    ρ.mapSubmodule Bpack
  obtain ⟨Cmod, hBCmod⟩ := @MonoidAlgebra.Submodule.exists_isCompl'
    (ZMod p) inferInstance A inferInstance inferInstance ρ.asModule instAdd instMod inferInstance Bmod
  let Cpack : ρ.invtSubmodule := ρ.mapSubmodule.symm Cmod
  let C : Subgroup G := η.symm (Cpack : Submodule (ZMod p) (Additive G))
  have hCinv : IsInvariant A G C := by
    refine ⟨?_⟩
    intro a g
    constructor
    · intro hg
      have hgC : Additive.ofMul g ∈ (Cpack : Submodule (ZMod p) (Additive G)) := by
        simpa [C, η] using hg
      have hmem := (Representation.mem_invtSubmodule (ρ := ρ)).1 Cpack.2 a
      have hsmul :=
        (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem (ρ a)).1 hmem
          (Additive.ofMul g) hgC
      simpa [ρ, C, η] using hsmul
    · intro hg
      have hgC : Additive.ofMul (a • g) ∈ (Cpack : Submodule (ZMod p) (Additive G)) := by
        simpa [C, η] using hg
      have hmem := (Representation.mem_invtSubmodule (ρ := ρ)).1 Cpack.2 a⁻¹
      have hsmul :=
        (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem (ρ a⁻¹)).1 hmem
          (Additive.ofMul (a • g)) hgC
      simpa [ρ, C, η, inv_smul_smul] using hsmul
  refine ⟨C, ?_, hCinv⟩
  have hcompl_sub : IsCompl (η B) (η C) := by
    have hcompl_pack : IsCompl Bpack Cpack := by
      exact (ρ.mapSubmodule.isCompl_iff).2 (by simpa [Bmod, Cpack] using hBCmod)
    rw [isCompl_iff, disjoint_iff, codisjoint_iff] at hcompl_pack ⊢
    constructor
    · simpa [Bpack, Cpack, C] using congrArg Subtype.val hcompl_pack.1
    · simpa [Bpack, Cpack, C] using congrArg Subtype.val hcompl_pack.2
  exact (OrderIso.isCompl_iff (f := η) (x := B) (y := C)).2 hcompl_sub


private theorem CFSG.map_top_subtype_eq
    {G : Type*} [Group G] (H : Subgroup G) :
    (⊤ : Subgroup H).map H.subtype = H := by
  ext x
  constructor
  · rintro ⟨y, _hy, rfl⟩
    exact y.2
  · intro hx
    exact ⟨⟨x, hx⟩, by simp, rfl⟩

private theorem CFSG.isMulCommutative_of_top_map_eq_top
    {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hmap : (⊤ : Subgroup G).map f = (⊤ : Subgroup H))
    (hcomm : IsMulCommutative G) :
    IsMulCommutative H := by
  refine ⟨⟨fun x y => ?_⟩⟩
  have hx : x ∈ (⊤ : Subgroup H) := by simp
  have hy : y ∈ (⊤ : Subgroup H) := by simp
  rw [← hmap] at hx hy
  rcases Subgroup.mem_map.mp hx with ⟨x0, _hx0, rfl⟩
  rcases Subgroup.mem_map.mp hy with ⟨y0, _hy0, rfl⟩
  simpa using congrArg f ((IsMulCommutative.is_comm (M := G)).comm x0 y0)

private theorem CFSG.isMulCommutative_of_subgroup_eq_top
    {G : Type*} [Group G] {H : Subgroup G} (_hH : H = ⊤)
    (hcomm : IsMulCommutative G) :
    IsMulCommutative H := by
  refine ⟨⟨fun x y => ?_⟩⟩
  exact Subtype.ext <| (IsMulCommutative.is_comm (M := G)).comm (x : G) (y : G)


public theorem CFSG.comap_le_of_le_map_quotient_of_le
    {G : Type*} [Group G] {N K : Subgroup G} [N.Normal] (hN_le_K : N ≤ K)
    {Y : Subgroup (G ⧸ N)} (hY_le : Y ≤ K.map (QuotientGroup.mk' N)) :
    Y.comap (QuotientGroup.mk' N) ≤ K := by
  have hcomap_le :
      Y.comap (QuotientGroup.mk' N) ≤
        (K.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) :=
    Subgroup.comap_mono hY_le
  have hker_le : (QuotientGroup.mk' N).ker ≤ K := by
    simpa [QuotientGroup.ker_mk'] using hN_le_K
  have hcomap_eq :
      (K.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) = K := by
    calc
      (K.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) =
          K ⊔ (QuotientGroup.mk' N).ker := Subgroup.comap_map_eq (f := QuotientGroup.mk' N) (H := K)
      _ = K := sup_eq_left.2 hker_le
  simpa [hcomap_eq] using hcomap_le

private theorem CFSG.omega₁_ne_bot_of_nontrivial_pGroup_early
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    [Fact (IsPGroup p G)] [Nontrivial G] :
    omega₁ (G := G) (p := p) ≠ ⊥ := by
  classical
  have hp_dvd_card : p ∣ Nat.card G := by
    rcases (Fact.out : IsPGroup p G).card_eq_or_dvd with hcard_one | hp_dvd
    · have hcard_gt : 1 < Nat.card G :=
        Finite.one_lt_card_iff_nontrivial.mpr inferInstance
      omega
    · exact hp_dvd
  let : Fintype G := Fintype.ofFinite G
  have hp_dvd_fintype : p ∣ Fintype.card G := by
    simpa [Nat.card_eq_fintype_card] using hp_dvd_card
  obtain ⟨x, hx_order⟩ := _root_.exists_prime_orderOf_dvd_card (G := G) p hp_dvd_fintype
  have hx_ne_one : x ≠ 1 := by
    intro hx
    have h1p : 1 = p := by simpa [hx] using hx_order
    exact (Fact.out : Nat.Prime p).ne_one h1p.symm
  have hx_pow : x ^ p = 1 := by
    simpa [hx_order] using pow_orderOf_eq_one x
  have hx_mem : x ∈ omega₁ (G := G) (p := p) := by
    change x ∈ Subgroup.closure {y : G | y ^ (p ^ 1) = 1}
    exact Subgroup.subset_closure (by simpa [pow_one] using hx_pow)
  intro hbot
  have hx_bot : x ∈ (⊥ : Subgroup G) := by simpa [hbot] using hx_mem
  exact hx_ne_one (by simpa using hx_bot)

public theorem CFSG.prime_le_natCard_omega₁_of_nontrivial_pGroup_early
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    [Fact (IsPGroup p G)] [Nontrivial G] :
    p ≤ Nat.card (omega₁ (G := G) (p := p)) := by
  have hΩ_ne_bot : omega₁ (G := G) (p := p) ≠ ⊥ :=
    omega₁_ne_bot_of_nontrivial_pGroup_early (G := G) (p := p)
  have hΩ_nontriv : Nontrivial (omega₁ (G := G) (p := p)) :=
    (Subgroup.nontrivial_iff_ne_bot (omega₁ (G := G) (p := p))).2 hΩ_ne_bot
  have hΩp : IsPGroup p (omega₁ (G := G) (p := p)) :=
    (Fact.out : IsPGroup p G).to_subgroup (omega₁ (G := G) (p := p))
  obtain ⟨n, hn_pos, hcard⟩ :=
    (IsPGroup.nontrivial_iff_card (p := p)
      (G := omega₁ (G := G) (p := p)) hΩp).mp hΩ_nontriv
  calc
    p = p ^ 1 := by simp
    _ ≤ p ^ n := (Nat.pow_le_pow_iff_right (Fact.out : Nat.Prime p).one_lt).2 hn_pos
    _ = Nat.card (omega₁ (G := G) (p := p)) := hcard.symm

public theorem CFSG.isCyclic_of_natCard_omega₁_eq_prime_early
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hpodd : p ≠ 2) [Fact (IsPGroup p G)]
    (hΩcard : Nat.card (omega₁ (G := G) (p := p)) = p) :
    IsCyclic G := by
  classical
  by_contra hncyc
  obtain ⟨E, _hE_normal, hEcard, _hEelem⟩ :=
    lemma_4_5_a (R := G) (p := p) hpodd hncyc
  have hE_le_Ω : E ≤ omega₁ (G := G) (p := p) := elementaryAbelian_le_omega₁
  have hcard_le : Nat.card E ≤ Nat.card (omega₁ (G := G) (p := p)) :=
    Subgroup.card_le_of_le hE_le_Ω
  have hp_sq_le_p : p ^ 2 ≤ p := by
    simpa [hEcard, hΩcard] using hcard_le
  have hp_lt_sq : p < p ^ 2 := pow_two_gt_prime
  exact (not_le_of_gt hp_lt_sq) hp_sq_le_p


private theorem CFSG.omega₁_sup_map_quotient_le_omega₁_quotient
    {G : Type*} [Group G] {p : ℕ} (S : Subgroup G) [S.Normal] :
    ((omega₁ (G := G) (p := p) ⊔ S).map (QuotientGroup.mk' S)) ≤
      omega₁ (G := G ⧸ S) (p := p) := by
  let qS : G →* G ⧸ S := QuotientGroup.mk' S
  intro y hy
  rcases Subgroup.mem_map.mp hy with ⟨x, hx, rfl⟩
  rw [Subgroup.sup_eq_closure] at hx
  change qS x ∈ Subgroup.closure {z : G ⧸ S | z ^ (p ^ 1) = 1}
  refine Subgroup.closure_induction
    (p := fun x _ => qS x ∈ Subgroup.closure {z : G ⧸ S | z ^ (p ^ 1) = 1})
    (x := x) ?_ ?_ ?_ ?_ hx
  · intro z hz
    rcases hz with hz | hz
    · have hmap_le : (omega₁ (G := G) (p := p)).map qS ≤ omega₁ (G := G ⧸ S) (p := p) := by
        rw [omega₁, omega, MonoidHom.map_closure]
        refine (Subgroup.closure_le (K := omega₁ (G := G ⧸ S) (p := p))).2 ?_
        rintro _ ⟨u, hu, rfl⟩
        refine Subgroup.subset_closure ?_
        simpa [pow_one, map_pow] using congrArg qS hu
      exact hmap_le (Subgroup.mem_map_of_mem qS hz)
    · have hz_one : qS z = 1 := (QuotientGroup.eq_one_iff (N := S) (x := z)).2 hz
      simp [hz_one]
  · simp
  · intro x y _ _ hx hy
    simpa [map_mul] using (Subgroup.mul_mem _ hx hy)
  · intro x _ hx
    simpa [map_inv] using (Subgroup.inv_mem _ hx)

private theorem CFSG.quotient_isMulCommutative_of_derived_le
    {G : Type*} [Group G] {S : Subgroup G} [S.Normal]
    (hD_le_S : derivedSubgroup G ≤ S) :
    IsMulCommutative (G ⧸ S) := by
  classical
  let qS : G →* G ⧸ S := QuotientGroup.mk' S
  refine ⟨⟨fun x y => ?_⟩⟩
  rcases QuotientGroup.mk'_surjective S x with ⟨r, rfl⟩
  rcases QuotientGroup.mk'_surjective S y with ⟨s, rfl⟩
  have hrs_mem : ⁅r, s⁆ ∈ S := by
    exact hD_le_S (by
      simpa [derivedSubgroup, derivedSeries_one] using
        (Subgroup.commutator_mem_commutator
          (H₁ := (⊤ : Subgroup G)) (H₂ := (⊤ : Subgroup G))
          (by simp) (by simp)))
  have hcomm_one : ⁅qS r, qS s⁆ = 1 := by
    rw [← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff (N := S) (x := ⁅r, s⁆)).2 hrs_mem
  exact (commutatorElement_eq_one_iff_mul_comm).1 hcomm_one

public theorem CFSG.theorem_4_12_a_aux (n : ℕ)
    {R A : Type*} [Group R] [Finite R] [Group A] [Finite A]
    {p : ℕ} [Fact p.Prime] (hcard : Nat.card R = n) (hpodd : p ≠ 2)
    [Fact (IsPGroup p R)] [MulDistribMulAction A R]
    (hcop : Nat.Coprime p (Nat.card A)) (hmeta : IsMetacyclic R) :
    IsMulCommutative (commutatorAction (A := A) (G := R)) := by
  classical
  induction n using Nat.strong_induction_on generalizing R A p with
  | h n ih =>
    let H : Subgroup R := commutatorAction (A := A) (G := R)
    by_cases hHtop : H = ⊤
    · have hdercyc : IsCyclic (derivedSubgroup R) :=
        derivedSubgroup_isCyclic_of_isMetacyclic (R := R) hmeta
      obtain ⟨S, hD_le_S, hS_cyc, hS_inv, hS_max_inv⟩ :=
        exists_maximal_cyclic_invariant_subgroup_containing_derived
          (R := R) (A := A) hdercyc
      have hS_normal : S.Normal := normal_of_derivedSubgroup_le S hD_le_S
      let : S.Normal := hS_normal
      let : IsInvariant A R S := hS_inv
      have hS_center : S ≤ Subgroup.center R := by
        exact le_center_of_commutatorAction_eq_top_of_cyclic_invariant
          (A := A) (S := S) hS_cyc (by simpa [H] using hHtop)
      have hOmega_le : Nat.card (omega₁ (G := R) (p := p)) ≤ p ^ 2 := by
        by_cases hRcyc : IsCyclic R
        · by_cases hRsub : Subsingleton R
          · have hcard_le_one : Nat.card (omega₁ (G := R) (p := p)) ≤ 1 :=
              Finite.card_le_one_iff_subsingleton.2 inferInstance
            exact hcard_le_one.trans (by
              exact Nat.succ_le_iff.mp (pow_pos (Nat.Prime.pos Fact.out) 2))
          · have : Nontrivial R := not_subsingleton_iff_nontrivial.mp hRsub
            have hΩ_card : Nat.card (omega₁ (G := R) (p := p)) = p :=
              natCard_omega₁_cyclic_quotient_eq_prime (G := R) (p := p) hRcyc
            rw [hΩ_card]
            exact le_of_lt pow_two_gt_prime
        · exact (lemma_4_10 (R := R) (p := p) hpodd hmeta hRcyc).1.le
      by_cases hRcomm_direct : IsMulCommutative R
      · exact isMulCommutative_of_subgroup_eq_top (H := H) hHtop hRcomm_direct
      have hS_ne_bot : S ≠ ⊥ := by
        intro hSbot
        have hD_le_bot : derivedSubgroup R ≤ (⊥ : Subgroup R) := by
          simpa [hSbot] using hD_le_S
        have hRcomm_from_D : IsMulCommutative R := by
          refine ⟨⟨fun x y => ?_⟩⟩
          have hcomm_mem : ⁅x, y⁆ ∈ derivedSubgroup R := by
            simpa [derivedSubgroup, derivedSeries_one] using
              (Subgroup.commutator_mem_commutator
                (H₁ := (⊤ : Subgroup R)) (H₂ := (⊤ : Subgroup R))
                (by simp) (by simp))
          have hcomm_bot : ⁅x, y⁆ ∈ (⊥ : Subgroup R) := hD_le_bot hcomm_mem
          have hcomm_one : ⁅x, y⁆ = 1 := by simpa using hcomm_bot
          exact (commutatorElement_eq_one_iff_mul_comm).1 hcomm_one
        exact hRcomm_direct hRcomm_from_D
      have hquot_cyc : IsCyclic (R ⧸ S) := by
        by_cases hS_top : S = ⊤
        · subst hS_top
          have hsub : Subsingleton (R ⧸ (⊤ : Subgroup R)) := by
            constructor
            intro x y
            rcases QuotientGroup.mk'_surjective (⊤ : Subgroup R) x with ⟨a, rfl⟩
            rcases QuotientGroup.mk'_surjective (⊤ : Subgroup R) y with ⟨b, rfl⟩
            apply QuotientGroup.eq.mpr
            simp
          exact @isCyclic_of_subsingleton (R ⧸ (⊤ : Subgroup R)) _ hsub
        let qS : R →* R ⧸ S := QuotientGroup.mk' S
        let : MulDistribMulAction A (R ⧸ S) :=
          quotientMulDistribMulAction (A := A) (G := R) S hS_inv
        let : Fact (IsPGroup p (R ⧸ S)) := ⟨(Fact.out : IsPGroup p R).to_quotient S⟩
        have hQ_comm : IsMulCommutative (R ⧸ S) :=
          quotient_isMulCommutative_of_derived_le (G := R) (S := S) hD_le_S
        let : IsMulCommutative (R ⧸ S) := hQ_comm
        let ΩQ : Subgroup (R ⧸ S) := omega₁ (G := R ⧸ S) (p := p)
        let : ΩQ.Characteristic := by
          simpa [ΩQ] using omega₁_characteristic (G := R ⧸ S) (p := p)
        let : IsInvariant A (R ⧸ S) ΩQ :=
          isInvariant_of_characteristic (A := A) (G := R ⧸ S) ΩQ
        let : MulDistribMulAction A ΩQ := inferInstance
        have hΩQ_pow : ∀ x : ΩQ, x ^ p = 1 := by
          intro x
          apply Subtype.ext
          change (x : R ⧸ S) ^ p = 1
          refine Subgroup.closure_induction (k := {z : R ⧸ S | z ^ (p ^ 1) = 1})
            (x := x.1) ?_ ?_ ?_ ?_ x.2
          · intro z hz
            simpa [pow_one] using hz
          · simp
          · intro z₁ z₂ _ _ hz₁ hz₂
            simp [mul_pow, hz₁, hz₂]
          · intro z _ hz
            simpa [inv_pow] using congrArg Inv.inv hz
        have hΩQ_elem : IsElementaryAbelian p ΩQ := by
          refine { exponent_dvd_p := ?_ }
          rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
          exact hΩQ_pow
        let ΩR : Subgroup R := omega₁ (G := R) (p := p)
        let : ΩR.Characteristic := by
          simpa [ΩR] using omega₁_characteristic (G := R) (p := p)
        let : IsInvariant A R ΩR :=
          isInvariant_of_characteristic (A := A) (G := R) ΩR
        let B0 : Subgroup (R ⧸ S) := (ΩR ⊔ S).map qS
        have hB0_le_ΩQ : B0 ≤ ΩQ := by
          simpa [B0, ΩR, ΩQ, qS] using
            omega₁_sup_map_quotient_le_omega₁_quotient (G := R) (p := p) S
        let B : Subgroup ΩQ := B0.subgroupOf ΩQ
        have : IsInvariant A R (ΩR ⊔ S) := isInvariant_sup ΩR S
        have : IsInvariant A (R ⧸ S) B0 := by
          simpa [B0, qS] using
            isInvariant_map_quotient (A := A) (G := R) (N := S) (H := ΩR ⊔ S)
        have : IsInvariant A ΩQ B := by
          simpa [B, B0, ΩQ] using isInvariant_subgroupOf B0 ΩQ
        have : IsElementaryAbelian p ΩQ := hΩQ_elem
        obtain ⟨C, hBC, hCinv⟩ :=
          exists_isCompl_isInvariant_of_elementaryAbelian_coprime
            (G := ΩQ) (A := A) (p := p) hcop B
        let Cbar : Subgroup (R ⧸ S) := C.map ΩQ.subtype
        let X : Subgroup R := Cbar.comap qS
        have hC_bot : C = ⊥ := by
          by_contra hC_ne_bot
          let Cbar : Subgroup (R ⧸ S) := C.map ΩQ.subtype
          let X : Subgroup R := Cbar.comap qS
          have hCbar_ne_bot : Cbar ≠ ⊥ := by
            intro hbot
            have hC_le_ker : C ≤ ΩQ.subtype.ker := by
              simpa [Cbar] using (Subgroup.map_eq_bot_iff (H := C) (f := ΩQ.subtype)).mp hbot
            have hker_bot : ΩQ.subtype.ker = ⊥ := by
              ext x
              constructor
              · intro hx
                have hx1 : ΩQ.subtype x = 1 := by simpa [MonoidHom.mem_ker] using hx
                exact Subtype.ext hx1
              · intro hx
                simp [hx]
            exact hC_ne_bot (le_bot_iff.mp (by simpa [hker_bot] using hC_le_ker))
          have hS_le_X : S ≤ X := by
            intro s hs
            change qS s ∈ Cbar
            have hs1 : qS s = 1 := (QuotientGroup.eq_one_iff (N := S) (x := s)).2 hs
            simp [Cbar, hs1]
          have : IsInvariant A ΩQ C := hCinv
          have : IsInvariant A (R ⧸ S) Cbar := by
            simpa [Cbar, ΩQ] using isInvariant_map_subtype (A := A) (G := R ⧸ S) ΩQ C
          have : IsInvariant A R X := by
            refine isInvariant_comap_quotient (A := A) (G := R) (N := S) Cbar ?_
            intro a g
            simp [MulAction.Quotient.smul_mk]
          have hD_le_X : derivedSubgroup R ≤ X := hD_le_S.trans hS_le_X
          have hX_cyc : IsCyclic X := by
            let ΩX : Subgroup X := omega₁ (G := X) (p := p)
            have hΩX_le_S : ΩX ≤ S.subgroupOf X := by
              intro z hz
              change ((z : X) : R) ∈ S
              refine Subgroup.closure_induction
                (p := fun x _ => ((x : X) : R) ∈ S) (x := z) ?_ ?_ ?_ ?_ hz
              · intro y hy
                have hy_pow_R : ((y : X) : R) ^ p = 1 := by
                  have hy' := congrArg X.subtype hy
                  simpa [pow_one] using hy'
                have hyΩR : ((y : X) : R) ∈ ΩR := by
                  change ((y : X) : R) ∈ Subgroup.closure {u : R | u ^ (p ^ 1) = 1}
                  exact Subgroup.subset_closure (by simpa [pow_one] using hy_pow_R)
                have hyB0 : qS ((y : X) : R) ∈ B0 := by
                  exact Subgroup.mem_map_of_mem qS (show ((y : X) : R) ∈ ΩR ⊔ S from (le_sup_left : ΩR ≤ ΩR ⊔ S) hyΩR)
                have hyΩQ : qS ((y : X) : R) ∈ ΩQ := hB0_le_ΩQ hyB0
                let yΩ : ΩQ := ⟨qS ((y : X) : R), hyΩQ⟩
                have hyB : yΩ ∈ B := by
                  change (yΩ : R ⧸ S) ∈ B0
                  exact hyB0
                have hyCbar : qS ((y : X) : R) ∈ Cbar := y.2
                rcases Subgroup.mem_map.mp hyCbar with ⟨c, hcC, hc_eq⟩
                have hc_eq_yΩ : c = yΩ := by
                  apply Subtype.ext
                  exact hc_eq
                have hyC : yΩ ∈ C := by
                  simpa [hc_eq_yΩ] using hcC
                have hyΩ_one : yΩ = 1 :=
                  (Subgroup.disjoint_def.mp hBC.disjoint) hyB hyC
                have hyq_one : qS ((y : X) : R) = 1 := by
                  simpa [yΩ] using congrArg ΩQ.subtype hyΩ_one
                exact (QuotientGroup.eq_one_iff (N := S) (x := ((y : X) : R))).1 hyq_one
              · simp
              · intro x y _ _ hx hy
                exact S.mul_mem hx hy
              · intro x _ hx
                exact S.inv_mem hx
            by_contra hX_not_cyc
            let : Fact (IsPGroup p X) := ⟨(Fact.out : IsPGroup p R).to_subgroup X⟩
            obtain ⟨E, _hE_normal, hEcard, hEelem⟩ :=
              lemma_4_5_a (R := X) (p := p) hpodd hX_not_cyc
            let : IsElementaryAbelian p E := hEelem
            have hE_le_ΩX : E ≤ ΩX := by
              simpa [ΩX] using (elementaryAbelian_le_omega₁ (p := p) (G := X) (E := E))
            have hE_le_SX : E ≤ S.subgroupOf X := hE_le_ΩX.trans hΩX_le_S
            let : IsCyclic (S.subgroupOf X) :=
              (Subgroup.subgroupOfEquivOfLe (G := R) (H := S) (K := X) hS_le_X).isCyclic.2 hS_cyc
            have hE_cyc : IsCyclic E := Subgroup.isCyclic_of_le hE_le_SX
            have hexp_dvd : Monoid.exponent E ∣ p :=
              IsElementaryAbelian.exponent_dvd_p p E
            rw [hE_cyc.exponent_eq_card, hEcard] at hexp_dvd
            have hp_lt_sq : p < p ^ 2 := pow_two_gt_prime
            exact (Nat.not_dvd_of_pos_of_lt (Fact.out : Nat.Prime p).pos hp_lt_sq) hexp_dvd
          have hX_eq_S : X = S := hS_max_inv X hD_le_X hX_cyc inferInstance hS_le_X
          have hCbar_bot : Cbar = ⊥ := by
            apply le_bot_iff.mp
            intro y hy
            rcases hy with ⟨x, hxC, rfl⟩
            have hxX : (x : R ⧸ S) ∈ Cbar := ⟨x, hxC, rfl⟩
            rcases QuotientGroup.mk'_surjective S (x : R ⧸ S) with ⟨r, hr⟩
            have hrX : r ∈ X := by
              change qS r ∈ Cbar
              simpa [qS, hr] using hxX
            have hrS : r ∈ S := by
              simpa [hX_eq_S] using hrX
            have hx1 : (x : R ⧸ S) = 1 := by
              rw [← hr]
              exact (QuotientGroup.eq_one_iff (N := S) (x := r)).2 hrS
            simp [hx1]
          exact hCbar_ne_bot hCbar_bot
        have hB_top : B = ⊤ := by
          exact eq_top_of_isCompl_bot (by simpa [hC_bot] using hBC)
        have hB0_eq_ΩQ : B0 = ΩQ := by
          apply le_antisymm hB0_le_ΩQ
          intro y hy
          have hyB : (⟨y, hy⟩ : ΩQ) ∈ B := by
            simp [hB_top]
          change y ∈ B0
          simpa [B, Subgroup.mem_subgroupOf] using hyB
        have hB0_eq_mapΩR : B0 = ΩR.map qS := by
          calc
            B0 = (ΩR ⊔ S).map qS := rfl
            _ = ΩR.map qS ⊔ S.map qS := by rw [Subgroup.map_sup]
            _ = ΩR.map qS ⊔ ⊥ := by
              have hSmap_bot : S.map qS = (⊥ : Subgroup (R ⧸ S)) := by
                apply le_bot_iff.mp
                intro y hy
                rcases hy with ⟨s, hs, rfl⟩
                have hs1 : qS s = 1 := (QuotientGroup.eq_one_iff (N := S) (x := s)).2 hs
                simp [hs1]
              rw [hSmap_bot]
            _ = ΩR.map qS := by simp
        have hker_eq : qS.ker.subgroupOf ΩR = S.subgroupOf ΩR := by
          simp [qS, QuotientGroup.ker_mk']
        have hker_card_ge : p ≤ Nat.card (qS.ker.subgroupOf ΩR) := by
          rw [hker_eq]
          have hSp : IsPGroup p S := (Fact.out : IsPGroup p R).to_subgroup S
          have hS_nontriv : Nontrivial S := (Subgroup.nontrivial_iff_ne_bot S).2 hS_ne_bot
          have hp_dvd_S : p ∣ Nat.card S := by
            rcases hSp.card_eq_or_dvd with h1 | hdvd
            · have hcard_gt : 1 < Nat.card S := Finite.one_lt_card_iff_nontrivial.mpr hS_nontriv
              omega
            · exact hdvd
          obtain ⟨s0, hs0_order⟩ := exists_prime_orderOf_dvd_card' (G := S) p hp_dvd_S
          have hs0_pow_R : ((s0 : S) : R) ^ p = 1 := by
            simpa [hs0_order] using congrArg S.subtype (pow_orderOf_eq_one s0)
          have hs0_ΩR : ((s0 : S) : R) ∈ ΩR := by
            change ((s0 : S) : R) ∈ Subgroup.closure {x : R | x ^ (p ^ 1) = 1}
            exact Subgroup.subset_closure (by simpa [pow_one] using hs0_pow_R)
          let sΩ : S.subgroupOf ΩR := ⟨⟨(s0 : R), hs0_ΩR⟩, s0.2⟩
          have hsΩ_order : orderOf sΩ = p := by
            have h1 : orderOf ((S.subgroupOf ΩR).subtype sΩ) = orderOf sΩ :=
              orderOf_injective (S.subgroupOf ΩR).subtype (S.subgroupOf ΩR).subtype_injective sΩ
            have h2 : orderOf (ΩR.subtype ((S.subgroupOf ΩR).subtype sΩ)) = orderOf ((S.subgroupOf ΩR).subtype sΩ) :=
              orderOf_injective ΩR.subtype ΩR.subtype_injective ((S.subgroupOf ΩR).subtype sΩ)
            have h3 : orderOf (S.subtype s0) = orderOf s0 :=
              orderOf_injective S.subtype S.subtype_injective s0
            have hR : orderOf (ΩR.subtype ((S.subgroupOf ΩR).subtype sΩ)) = p := by
              simpa [sΩ] using h3.trans hs0_order
            exact h1.symm.trans (h2.symm.trans hR)
          have hU_card : Nat.card (Subgroup.zpowers sΩ) = p := by
            rw [Nat.card_zpowers, hsΩ_order]
          calc
            p = Nat.card (Subgroup.zpowers sΩ) := hU_card.symm
            _ ≤ Nat.card (S.subgroupOf ΩR) := Subgroup.card_le_card_group (H := Subgroup.zpowers sΩ)
        have hB0_card_le_p : Nat.card B0 ≤ p := by
          rw [hB0_eq_mapΩR]
          have hcard_map : Nat.card (ΩR.map qS) = Nat.card (ΩR ⧸ qS.ker.subgroupOf ΩR) := by
            let φ : ΩR →* R ⧸ S := qS.comp ΩR.subtype
            have hφker : φ.ker = qS.ker.subgroupOf ΩR := by
              ext x
              simp [φ, Subgroup.mem_subgroupOf]
            have hφrange : φ.range = ΩR.map qS := by
              ext y
              constructor
              · rintro ⟨x, -, rfl⟩
                exact ⟨x, x.property, rfl⟩
              · rintro ⟨x, hx, rfl⟩
                exact ⟨⟨x, hx⟩, rfl⟩
            have hcard := Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
            simpa [hφker, hφrange] using hcard.symm
          have hmul : Nat.card (ΩR.map qS) * Nat.card (qS.ker.subgroupOf ΩR) = Nat.card ΩR := by
            rw [hcard_map]
            simpa [Nat.mul_comm] using
              (Subgroup.card_eq_card_quotient_mul_card_subgroup (α := ΩR) (s := qS.ker.subgroupOf ΩR)).symm
          have hmul_le : Nat.card (ΩR.map qS) * p ≤ p ^ 2 := by
            calc
              Nat.card (ΩR.map qS) * p ≤ Nat.card (ΩR.map qS) * Nat.card (qS.ker.subgroupOf ΩR) :=
                Nat.mul_le_mul_left _ hker_card_ge
              _ = Nat.card ΩR := hmul
              _ ≤ p ^ 2 := by simpa [ΩR] using hOmega_le
          have hmul_le' : Nat.card (ΩR.map qS) * p ≤ p * p := by
            simpa [pow_two] using hmul_le
          exact Nat.le_of_mul_le_mul_right hmul_le' (Fact.out : Nat.Prime p).pos
        have hΩQ_card_le_p : Nat.card ΩQ ≤ p := by
          rw [← hB0_eq_ΩQ]
          exact hB0_card_le_p
        have hQ_card_ne_one : Nat.card (R ⧸ S) ≠ 1 := by
          intro hQ1
          have hR_eq_S : Nat.card R = Nat.card S := by
            calc
              Nat.card R = Nat.card (R ⧸ S) * Nat.card S := by
                simpa using (Subgroup.card_eq_card_quotient_mul_card_subgroup (α := R) (s := S))
              _ = Nat.card S := by rw [hQ1]; simp
          exact hS_top ((Subgroup.card_eq_iff_eq_top S).1 hR_eq_S.symm)
        have hQ_nontriv : Nontrivial (R ⧸ S) := by
          rw [← not_subsingleton_iff_nontrivial]
          intro hsub
          let : Subsingleton (R ⧸ S) := hsub
          exact hQ_card_ne_one (Nat.card_eq_one_iff_unique.2 ⟨hsub, ⟨1⟩⟩)
        have hΩQ_ge : p ≤ Nat.card ΩQ := by
          let : Nontrivial (R ⧸ S) := hQ_nontriv
          simpa [ΩQ] using prime_le_natCard_omega₁_of_nontrivial_pGroup_early (G := R ⧸ S) (p := p)
        have hΩQ_card : Nat.card (omega₁ (G := R ⧸ S) (p := p)) = p := by
          simpa [ΩQ] using le_antisymm hΩQ_card_le_p hΩQ_ge
        exact isCyclic_of_natCard_omega₁_eq_prime_early (G := R ⧸ S) (p := p) hpodd hΩQ_card
      have hcenter_quot_cyc : IsCyclic (R ⧸ Subgroup.center R) := by
        let qS : R →* R ⧸ S := QuotientGroup.mk' S
        let qZ : R →* R ⧸ Subgroup.center R := QuotientGroup.mk' (Subgroup.center R)
        let phi : R ⧸ S →* R ⧸ Subgroup.center R :=
          QuotientGroup.map S (Subgroup.center R) (MonoidHom.id R) hS_center
        have hphi_surj : Function.Surjective phi := by
          intro z
          rcases QuotientGroup.mk'_surjective (Subgroup.center R) z with ⟨r, rfl⟩
          exact ⟨qS r, rfl⟩
        exact isCyclic_of_surjective phi hphi_surj
      have hRcomm : IsMulCommutative R := lemma_4_1 (G := R) hcenter_quot_cyc
      exact isMulCommutative_of_subgroup_eq_top (H := H) hHtop hRcomm
    · let : IsInvariant A R H := by
        simpa [H] using commutatorAction_isInvariant (G := R) (A := A)
      let : MulDistribMulAction A H := inferInstance
      have hHp : IsPGroup p H := (Fact.out : IsPGroup p R).to_subgroup H
      let : Fact (IsPGroup p H) := ⟨hHp⟩
      have hHmeta : IsMetacyclic H := isMetacyclic_subgroup_of_isMetacyclic hmeta H
      have hHlt : Nat.card H < n := by
        rw [← hcard]
        exact natCard_subgroup_lt_of_ne_top H hHtop
      have hcommH : IsMulCommutative (commutatorAction (A := A) (G := H)) :=
        ih (Nat.card H) hHlt rfl hpodd hcop hHmeta
      have hRsolv : Group.IsSolvable R := by
        let : Group.IsNilpotent R := (Fact.out : IsPGroup p R).isNilpotent
        infer_instance
      have hcop' : Nat.Coprime (Nat.card A) (Nat.card R) := by
        obtain ⟨m, hm⟩ := (Fact.out : IsPGroup p R).exists_card_eq
        rw [hm]
        exact hcop.symm.pow_right m
      have hcomm₂_eq : commutatorAction₂ (A := A) (G := R) = H := by
        simpa [H] using proposition_1_6_b (G := R) (A := A) hRsolv hcop'
      have hmapH : (commutatorAction (A := A) (G := H)).map H.subtype = H := by
        calc
          (commutatorAction (A := A) (G := H)).map H.subtype
              = commutatorAction₂ (A := A) (G := R) := by
                simpa [H] using commutatorAction_map_subtype_eq_commutatorAction₂ (G := R) (A := A)
          _ = H := hcomm₂_eq
      have hcomm_top : commutatorAction (A := A) (G := H) = ⊤ := by
        apply eq_top_iff.2
        intro x _hx
        have hxmap : (x : R) ∈ (commutatorAction (A := A) (G := H)).map H.subtype := by
          rw [hmapH]
          exact x.2
        rcases Subgroup.mem_map.mp hxmap with ⟨y, hy, hyx⟩
        have hy_eq_x : y = x := H.subtype_injective hyx
        simpa [hy_eq_x] using hy
      have hmapTop :
          (⊤ : Subgroup (commutatorAction (A := A) (G := H))).map
              (commutatorAction (A := A) (G := H)).subtype = (⊤ : Subgroup H) := by
        rw [map_top_subtype_eq, hcomm_top]
      exact isMulCommutative_of_top_map_eq_top
        (commutatorAction (A := A) (G := H)).subtype hmapTop hcommH

/-! # Theorem 4.12(a) from BG Section 4 -/

section Main

open scoped FixedPoints
public theorem CFSG.theorem_4_12_a {R A : Type*} [Group R] [Finite R] [Group A] [Finite A]
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2) [Fact (IsPGroup p R)]
    [MulDistribMulAction A R] (hcop : Nat.Coprime p (Nat.card A))
    (hmeta : IsMetacyclic R) :
    IsMulCommutative (commutatorAction (A := A) (G := R)) := by
  exact theorem_4_12_a_aux (Nat.card R) (R := R) (A := A) (p := p) rfl hpodd hcop hmeta
