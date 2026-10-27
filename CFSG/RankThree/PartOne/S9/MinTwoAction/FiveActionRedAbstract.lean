module

public import CFSG.RankThree.PartOne.S9.MinTwoAction.FiveActionRedSetup
public import CFSG.RankThree.PartOne.S9.MinTwoAction.QuotientBM
public import CFSG.RankThree.PartOne.S9.MinTwoAction.FiveActionDefs
public import CFSG.RankThree.PartOne.S9.MinTwoAction.QuotientKernelElimination

public section

namespace CFSG.RankThree.PartOne.FiveAction.Red

open CFSG CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne.Quotient36 SemidirectProduct
open scoped IsMulCommutative commutatorElement

section Data

variable {G : Type*} [Group G]

structure SFData (A R X : Subgroup G) : Prop where
  irr : IsFrattiniIrreducibleFor (R ⊔ A) X
  ker_le : R ⊓ Subgroup.centralizer (X : Set G) ≤ inSubgroup frattini R
  nontriv : ∃ a ∈ A, ∃ r ∈ R, ⁅a, r⁆ ∉ inSubgroup frattini R
  irrA : ∀ Y : Subgroup G, inSubgroup frattini R ≤ Y → Y ≤ R →
    A ≤ Subgroup.normalizer (Y : Set G) → Y = inSubgroup frattini R ∨ Y = R
  shape : (⁅R, R⁆ ≤ R ⊓ Subgroup.centralizer (X : Set G) ∧
      (∀ r ∈ R, r ^ 2 ∈ R ⊓ Subgroup.centralizer (X : Set G)) ∧
      (R ⊓ Subgroup.centralizer (X : Set G)).relIndex R = 16) ∨
    (∃ φ : ↥R →* QD32, Function.Surjective φ ∧
      φ.ker = (R ⊓ Subgroup.centralizer (X : Set G)).subgroupOf R)
  card_B : Nat.card (A ⊓ Subgroup.centralizer (R : Set G) : Subgroup G) = 5
  ker_A : ∀ a ∈ A, (∀ r ∈ R, ⁅a, r⁆ ∈ R ⊓ Subgroup.centralizer (X : Set G)) →
    a ∈ Subgroup.centralizer (R : Set G)

end Data

section Obtain

variable {G : Type} [Group G] [Finite G]

theorem exists_sfdata {q : ℕ} {A D R : Subgroup G} (hset : MinTwoActionSetting 5 q A D R)
    (hrk : ∀ r ∈ R, r ≠ 1 → CFSG.pRank q ↥(D ⊓ Subgroup.centralizer ({r} : Set G)) ≤ 3) :
    ∃ X : Subgroup G, X ≤ D ∧ X ⊓ inSubgroup frattini D = inSubgroup frattini X ∧
      SFData A R X := by
  obtain ⟨X, hXD, -, hirr, hfrat, hKΦ, hnt, hirrA, -, hshape, hB, hkerS, -, -⟩ :=
    minimalTwoActionSmallFaithfulQuotient G 5 q A D R hset hrk
  refine ⟨X, hXD, hfrat, ⟨hirr, hKΦ, hnt, hirrA, ?_, hB, hkerS⟩⟩
  rcases hshape with ⟨h7, -⟩ | ⟨-, h⟩ | ⟨-, h⟩
  · omega
  · exact Or.inl h
  · exact Or.inr h

end Obtain

section Abstract

variable {G : Type} [Group G] [Finite G] {A R X : Subgroup G}

omit [Finite G] in
theorem range_card_five (hAR : A ≤ Subgroup.normalizer (R : Set G))
    (hRX : R ≤ Subgroup.normalizer (X : Set G)) (hAX : A ≤ Subgroup.normalizer (X : Set G))
    (hAcard : Nat.card A = 5 ^ 2) (hd : SFData A R X) :
    Nat.card (Compat.ofSubgroups hAR hRX hAX).φ.range = 5 := by
  let C := Compat.ofSubgroups hAR hRX hAX
  have hker : ∀ r : ↥R, r ∈ C.fR.ker ↔ (r : G) ∈ Subgroup.centralizer (X : Set G) :=
    fun r => mem_ker_conjHom hRX r
  have hkereq : C.φ.ker = (A ⊓ Subgroup.centralizer (R : Set G)).subgroupOf A := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro h
      refine ⟨a.2, hd.ker_A a a.2 fun r hr => ?_⟩
      have h1 := congrArg (fun f : MulAut C.Q => f ((⟨r, hr⟩ : ↥R) : C.Q)) h
      simp only [MulAut.one_apply] at h1
      rw [Compat.φ_mk] at h1
      have h2 : C.ψ a ⟨r, hr⟩ / ⟨r, hr⟩ ∈ C.fR.ker := QuotientGroup.eq_iff_div_mem.mp h1
      have h3 : (((C.ψ a ⟨r, hr⟩ / ⟨r, hr⟩ : ↥R)) : G) = ⁅(a : G), r⁆ := by
        rw [div_eq_mul_inv, Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
        rfl
      rw [← h3]
      exact ⟨(C.ψ a ⟨r, hr⟩ / ⟨r, hr⟩ : ↥R).2, (hker _).mp h2⟩
    · rintro ⟨-, h⟩
      exact MulEquiv.ext fun s => phi_eq_of_mem_centralizer hAR hRX hAX a h s
  have h3 := Subgroup.card_ker_mul_card_range C.φ
  have hB' : Nat.card ((A ⊓ Subgroup.centralizer (R : Set G)).subgroupOf A) = 5 := by
    rw [← hd.card_B]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left : A ⊓ Subgroup.centralizer (R : Set G) ≤ A)).toEquiv)
  rw [hkereq, hB', hAcard] at h3
  show Nat.card C.φ.range = 5
  have h4 : 5 * Nat.card C.φ.range = 5 * 5 := h3.trans (by norm_num)
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h4

theorem shape_of_sfdata (hR2 : IsPGroup 2 R) (hAR : A ≤ Subgroup.normalizer (R : Set G))
    (hRX : R ≤ Subgroup.normalizer (X : Set G)) (hAX : A ≤ Subgroup.normalizer (X : Set G))
    (hd : SFData A R X) :
    FiveAction.Shape (Compat.ofSubgroups hAR hRX hAX).Q ↥A (Compat.ofSubgroups hAR hRX hAX).φ := by
  let C := Compat.ofSubgroups hAR hRX hAX
  have hker : ∀ r : ↥R, r ∈ C.fR.ker ↔ (r : G) ∈ Subgroup.centralizer (X : Set G) :=
    fun r => mem_ker_conjHom hRX r
  have hKsub : (R ⊓ Subgroup.centralizer (X : Set G)).subgroupOf R = C.fR.ker := by
    ext r
    rw [Subgroup.mem_subgroupOf, hker, Subgroup.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨r.2, h⟩⟩
  rcases hd.shape with ⟨hcomm, hsq, hrel⟩ | ⟨φ, hφs, hφk⟩
  · left
    have hcomm' : commutator ↥R ≤ C.fR.ker := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [hker]
      have e : ((⁅a, b⁆ : ↥R) : G) = ⁅(a : G), (b : G)⁆ := by simp [commutatorElement_def]
      rw [e]
      exact (hcomm (Subgroup.commutator_mem_commutator a.2 b.2)).2
    have hsq' : ∀ r : ↥R, r ^ 2 ∈ C.fR.ker := fun r => by
      rw [hker, Subgroup.coe_pow]
      exact (hsq r r.2).2
    have hSel : IsElementaryAbelian 2 C.Q := isElementaryAbelian_two_quotient C.fR.ker hcomm' hsq'
    have hSd : Nat.card C.Q = 16 := by
      rw [← hrel]
      have : Nat.card C.Q = C.fR.ker.index := rfl
      rw [this, ← hKsub]
      rfl
    have hS2 : IsPGroup 2 C.Q := hR2.to_quotient _
    have : Fact (IsPGroup 2 C.Q) := ⟨hS2⟩
    have hΦ : frattini C.Q = ⊥ := frattini_eq_bot_of_isElementaryAbelian (R := C.Q) (p := 2)
    have hKeq : R ⊓ Subgroup.centralizer (X : Set G) = inSubgroup frattini R := by
      refine le_antisymm hd.ker_le ?_
      rintro g ⟨ρ, hρ, rfl⟩
      have h1 : (QuotientGroup.mk' C.fR.ker) ρ ∈ frattini C.Q :=
        frattini_le_comap_frattini_of_surjective (QuotientGroup.mk'_surjective _) hρ
      rw [hΦ, Subgroup.mem_bot] at h1
      exact ⟨ρ.2, (hker ρ).mp ((QuotientGroup.eq_one_iff ρ).mp h1)⟩
    have hAirr : ∀ Y : Subgroup G, R ⊓ Subgroup.centralizer (X : Set G) ≤ Y → Y ≤ R →
        A ≤ Subgroup.normalizer (Y : Set G) →
        Y = R ⊓ Subgroup.centralizer (X : Set G) ∨ Y = R := by
      rw [hKeq]
      exact hd.irrA
    exact ⟨hSel, hSd, irreducible_phi_ofSubgroups hAR hRX hAX hAirr⟩
  · right
    have hker' : φ.ker = C.fR.ker := hφk.trans hKsub
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hker'.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφs)⟩

theorem rep_irreducible {q : ℕ} [Fact q.Prime] [Fact (IsPGroup q ↥X)]
    (hAR : A ≤ Subgroup.normalizer (R : Set G)) (hLX : R ⊔ A ≤ Subgroup.normalizer (X : Set G))
    (hirr : IsFrattiniIrreducibleFor (R ⊔ A) X) :
    letI C := Compat.ofSubgroups hAR (le_trans le_sup_left hLX) (le_trans le_sup_right hLX)
    letI := C.actE
    (frattiniRep (E := C.Q ⋊[C.φ] ↥A) (X := ↥X) q).IsIrreducible := by
  let C := Compat.ofSubgroups hAR (le_trans le_sup_left hLX) (le_trans le_sup_right hLX)
  let _ := C.actE
  exact isIrreducible_frattiniRep q (irredFrattini_ofSubgroups hAR hLX hirr)

theorem rep_injective {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) [hXq : Fact (IsPGroup q ↥X)]
    (hR2 : IsPGroup 2 R) (hAR : A ≤ Subgroup.normalizer (R : Set G))
    (hRX : R ≤ Subgroup.normalizer (X : Set G)) (hAX : A ≤ Subgroup.normalizer (X : Set G)) :
    letI C := Compat.ofSubgroups hAR hRX hAX
    letI := C.actE
    Function.Injective ((frattiniRep (E := C.Q ⋊[C.φ] ↥A) (X := ↥X) q).comp
      (SemidirectProduct.inl : C.Q →* C.Q ⋊[C.φ] ↥A)) := by
  let C := Compat.ofSubgroups hAR hRX hAX
  let _ := C.actE
  rw [injective_iff_map_eq_one]
  intro s hs
  have hs' : frattiniRep (E := C.Q ⋊[C.φ] ↥A) (X := ↥X) q (inl s) = 1 := hs
  have htriv : ∀ x : ↥X, (((inl s : C.Q ⋊[C.φ] ↥A) • x : ↥X) : ↥X ⧸ frattini ↥X) =
      (x : ↥X ⧸ frattini ↥X) := by
    intro x
    have h1 := frattiniRep_apply_mk (E := C.Q ⋊[C.φ] ↥A) (X := ↥X) q (inl s) x
    have h2 : frattiniRep (E := C.Q ⋊[C.φ] ↥A) (X := ↥X) q (inl s)
        (Additive.ofMul (x : ↥X ⧸ frattini ↥X)) = Additive.ofMul (x : ↥X ⧸ frattini ↥X) := by
      rw [hs']
      rfl
    exact Additive.ofMul.injective (h1.symm.trans h2)
  have hS2 : IsPGroup 2 C.Q := hR2.to_quotient _
  have hord : ¬ q ∣ orderOf (inl s : C.Q ⋊[C.φ] ↥A) := by
    rw [orderOf_injective (inl : C.Q →* C.Q ⋊[C.φ] ↥A) inl_injective]
    exact not_dvd_orderOf_of_two_group (Fact.out) hq2 hS2 s
  have hfix := smul_eq_of_smul_mk_eq hXq.out (inl s) hord htriv
  have h1 : C.fS s = 1 := MulEquiv.ext fun x => by
    rw [← C.actE_inl]
    exact hfix x
  exact (injective_iff_map_eq_one C.fS).mp C.fS_injective s h1

theorem exists_fixed_vector (hFV : FiveAction.FixedVector) {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2)
    [hXq : Fact (IsPGroup q ↥X)] (hR2 : IsPGroup 2 R) (hAcard : Nat.card A = 5 ^ 2)
    (hAR : A ≤ Subgroup.normalizer (R : Set G)) (hd : SFData A R X) :
    ∃ r : ↥R, (r : G) ∉ Subgroup.centralizer (X : Set G) ∧ ∃ x : ↥X,
      (x : ↥X ⧸ frattini ↥X) ≠ 1 ∧
      ((conjHom (le_trans le_sup_left hd.irr.1) r x : ↥X) : ↥X ⧸ frattini ↥X) =
        (x : ↥X ⧸ frattini ↥X) := by
  have hLX := hd.irr.1
  have hRX : R ≤ Subgroup.normalizer (X : Set G) := le_trans le_sup_left hLX
  have hAX : A ≤ Subgroup.normalizer (X : Set G) := le_trans le_sup_right hLX
  let C := Compat.ofSubgroups hAR hRX hAX
  let _ := C.actE
  have hW : FiniteDimensional (ZMod q) (Additive (↥X ⧸ frattini ↥X)) :=
    Module.Finite.of_finite
  obtain ⟨s, hs1, hs⟩ := hFV q hq2 C.Q ↥A C.φ (range_card_five hAR hRX hAX hAcard hd)
    (shape_of_sfdata hR2 hAR hRX hAX hd) (Additive (↥X ⧸ frattini ↥X))
    (frattiniRep (E := C.Q ⋊[C.φ] ↥A) (X := ↥X) q) (rep_irreducible hAR hLX hd.irr)
    (rep_injective hq2 hR2 hAR hRX hAX)
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (Submodule.one_le_finrank_iff.mp hs)
  rw [Module.End.mem_eigenspace_iff, one_smul] at hw
  obtain ⟨y, rfl⟩ : ∃ y, Additive.ofMul y = w := ⟨Additive.toMul w, rfl⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective s
  refine ⟨r, fun hr => hs1 ?_, x, fun h => hw0 (by rw [h]; rfl), ?_⟩
  · exact (QuotientGroup.eq_one_iff r).mpr ((mem_ker_conjHom hRX r).mpr hr)
  · have h1 := frattiniRep_apply_mk (E := C.Q ⋊[C.φ] ↥A) (X := ↥X) q (inl (r : C.Q)) x
    rw [h1, Compat.actE_inl] at hw
    exact Additive.ofMul.injective hw

theorem false_of_nontrivial_central (hSB : FiveAction.ScalarBound) {q : ℕ} [Fact q.Prime]
    (hq2 : q ≠ 2) (hq5 : q % 5 = 2 ∨ q % 5 = 3) {D : Subgroup G} [hXq : Fact (IsPGroup q ↥X)]
    (hR2 : IsPGroup 2 R) (hAcard : Nat.card A = 5 ^ 2) (hAel : IsElementaryAbelian 5 A)
    (hAR : A ≤ Subgroup.normalizer (R : Set G)) (hXD : X ≤ D) (hDexp : ∀ x ∈ D, x ^ q = 1)
    (hDcl : ⁅⁅D, D⁆, D⁆ = ⊥)
    (hrk : ∀ r ∈ R, r ≠ 1 → CFSG.pRank q ↥(D ⊓ Subgroup.centralizer ({r} : Set G)) ≤ 3)
    (hd : SFData A R X) (b : ↥A) (hbR : (b : G) ∈ Subgroup.centralizer (R : Set G))
    (hbnt : ∃ x : ↥X, ((conjHom (le_trans le_sup_right hd.irr.1) b x : ↥X) : ↥X ⧸ frattini ↥X) ≠
      (x : ↥X ⧸ frattini ↥X)) : False := by
  have hLX := hd.irr.1
  have hRX : R ≤ Subgroup.normalizer (X : Set G) := le_trans le_sup_left hLX
  have hAX : A ≤ Subgroup.normalizer (X : Set G) := le_trans le_sup_right hLX
  have hq : q.Prime := Fact.out
  have hq1 : 1 < q := hq.one_lt
  let C := Compat.ofSubgroups hAR hRX hAX
  let _ := C.actE
  have hW : FiniteDimensional (ZMod q) (Additive (↥X ⧸ frattini ↥X)) :=
    Module.Finite.of_finite
  have hS2 : IsPGroup 2 C.Q := hR2.to_quotient _
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hb5 : b ^ 5 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 5 ↥A) b
  have hb1 : b ≠ 1 := by
    rintro rfl
    obtain ⟨x, hx⟩ := hbnt
    apply hx
    simp
  have hbord : orderOf b = 5 := orderOf_eq_prime hb5 hb1
  have hρb : frattiniRep (E := C.Q ⋊[C.φ] ↥A) (X := ↥X) q (inr b) ≠ 1 := by
    intro h
    obtain ⟨x, hx⟩ := hbnt
    apply hx
    have h1 := frattiniRep_apply_mk (E := C.Q ⋊[C.φ] ↥A) (X := ↥X) q (inr b) x
    have h2 : frattiniRep (E := C.Q ⋊[C.φ] ↥A) (X := ↥X) q (inr b)
        (Additive.ofMul (x : ↥X ⧸ frattini ↥X)) = Additive.ofMul (x : ↥X ⧸ frattini ↥X) := by
      rw [h]
      rfl
    rw [Compat.actE_inr] at h1
    exact Additive.ofMul.injective (h1.symm.trans h2)
  obtain ⟨s, hs1, hs8⟩ := hSB q hq2 hq5 C.Q ↥A C.φ (range_card_five hAR hRX hAX hAcard hd)
    (shape_of_sfdata hR2 hAR hRX hAX hd) b
    (fun s => phi_eq_of_mem_centralizer hAR hRX hAX b hbR s)
    (fun a => hAel.toIsMulCommutative.is_comm.comm a b) hbord (Additive (↥X ⧸ frattini ↥X))
    (frattiniRep (E := C.Q ⋊[C.φ] ↥A) (X := ↥X) q) (rep_irreducible hAR hLX hd.irr)
    (rep_injective hq2 hR2 hAR hRX hAX) hρb
  have hXexp := pow_eq_one_of_le hXD hDexp
  have hXcl := commutator_le_center_of_le hXD hDcl
  have hp2 : ∀ s : C.Q, IsPGroup 2 (Subgroup.zpowers (inl s : C.Q ⋊[C.φ] ↥A)) := by
    intro s
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hS2
    have hdv : orderOf (inl s : C.Q ⋊[C.φ] ↥A) ∣ 2 ^ a := by
      rw [orderOf_injective (inl : C.Q →* C.Q ⋊[C.φ] ↥A) inl_injective]
      exact ha ▸ orderOf_dvd_natCard s
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdv
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers]; exact hj)
  have hfin : ∀ s : C.Q, Finite (Subgroup.zpowers (inl s : C.Q ⋊[C.φ] ↥A)) := by
    intro s
    refine finite_zpowers.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨Nat.card C.Q, Nat.card_pos, ?_⟩)
    rw [← map_pow, pow_card_eq_one', map_one]
  have hrank : ∀ s : C.Q, s ≠ 1 → CFSG.pRank q ↥(fixedPointSubgroup
      (Subgroup.zpowers (inl s : C.Q ⋊[C.φ] ↥A)) ↥X) ≤ 3 := by
    intro s hs
    obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective s
    rw [← pRank_map_subtype hq1, fixed_map_eq hAR hRX hAX r]
    refine (pRank_mono_subgroup hq1 (inf_le_inf_right _ hXD)).trans (hrk r r.2 ?_)
    intro h1
    apply hs
    have : r = 1 := Subtype.ext h1
    rw [this]
    rfl
  have h4 : Module.finrank (ZMod q) ↥(Module.End.eigenspace
      (frattiniRep (E := C.Q ⋊[C.φ] ↥A) (X := ↥X) q (inl s)) 1) ≤ 4 := by
    have := hfin s
    exact (finrank_eigenspace_le_pRank q hq2 hXexp (inl s) (hp2 s)).trans
      ((pRank_quotient_commutator_le q hXexp hXcl _).1 (hrank s hs1))
  omega

end Abstract

end CFSG.RankThree.PartOne.FiveAction.Red
