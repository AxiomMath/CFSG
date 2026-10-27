module

public import Mathlib.GroupTheory.Frattini
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.ElementaryAbelian.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.ElementaryAbelian.VectorSpace
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.PGroup

namespace CFSG
end CFSG
open CFSG

/-!
# Frattini facts for finite p-groups

This module collects Mathlib-only consequences about the Frattini subgroup
`Φ(R) = frattini R` for finite p-groups.

Public items:
- `frattini_nongenerating_of_isPGroup`
- `commutator_le_frattini_of_isPGroup`
- `pth_power_mem_frattini_of_isPGroup`
- `isElementaryAbelian_quotient_frattini`
- `frattini_eq_bot_of_isElementaryAbelian`
- `frattini_eq_bot_iff_isElementaryAbelian`
- `frattini_eq_closure_commutator_union_powers`
- `frattiniQuotientEquivOfIsElementaryAbelian` and its `_mk'`/`_coe` lemmas
-/

namespace CFSG.Theory.Frattini

open scoped IsMulCommutative
open Theory.ElementaryAbelian
open Theory.PGroup

/-- The p-group specialization of `frattini_nongenerating`: if `H ⊔ Φ(R) = ⊤`,
then `H = ⊤`. -/
public theorem frattini_nongenerating_of_isPGroup {R : Type*} [Group R] [Finite R]
    {p : ℕ} [Fact p.Prime]
    [Fact (IsPGroup p R)] : ∀ H : Subgroup R, H ⊔ frattini R = ⊤ → H = ⊤ := by
  intro H hsup
  simpa using (frattini_nongenerating (G := R) hsup)

/-- For a finite `p`-group, the commutator subgroup is contained in the Frattini subgroup:
`[R,R] ≤ Φ(R)`. -/
public lemma commutator_le_frattini_of_isPGroup {R : Type*} [Group R] [Finite R]
    {p : ℕ} [Fact p.Prime] [Fact (IsPGroup p R)] :
    _root_.commutator R ≤ frattini R := by
  intro x hx
  unfold frattini Order.radical
  simp only [Subgroup.mem_iInf]
  intro M hM
  letI : M.Normal := coatom_normal_of_isPGroup (p := p) (K := M) hM
  letI : IsCyclic (R ⧸ M) := isCyclic_of_prime_card (α := R ⧸ M)
    (card_quotient_coatom_eq_prime (p := p) (K := M) hM)
  exact ((Subgroup.Normal.quotient_commutative_iff_commutator_le (N := M)).1
    (IsCyclic.isMulCommutative (α := R ⧸ M))) hx

/-- In a finite `p`-group, every `p`-th power lies in the Frattini subgroup. -/
public lemma pth_power_mem_frattini_of_isPGroup {R : Type*} [Group R] [Finite R]
    {p : ℕ} [Fact p.Prime] [Fact (IsPGroup p R)] (x : R) : x ^ p ∈ frattini R := by
  unfold frattini Order.radical
  simp only [Subgroup.mem_iInf]
  intro M hM
  letI : M.Normal := coatom_normal_of_isPGroup (p := p) (K := M) hM
  exact (QuotientGroup.eq_one_iff (N := M) (x := x ^ p)).1 (by
    simpa [MonoidHom.map_pow, card_quotient_coatom_eq_prime (p := p) (K := M) hM] using
      (pow_card_eq_one' (x := (QuotientGroup.mk' M x : R ⧸ M))))

/-- The Frattini quotient of a finite `p`-group is elementary abelian. -/
public theorem isElementaryAbelian_quotient_frattini {R : Type*} [Group R] [Finite R]
    {p : ℕ} [Fact p.Prime] [Fact (IsPGroup p R)] :
    IsElementaryAbelian p (R ⧸ frattini R) := by
  refine {
    toIsMulCommutative := ?_,
    exponent_dvd_p := ?_
  }
  · exact (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := frattini R)).2
      (commutator_le_frattini_of_isPGroup (R := R) (p := p))
  · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
    intro q
    refine QuotientGroup.induction_on q ?_
    intro x
    change ((QuotientGroup.mk' (frattini R) x : R ⧸ frattini R) ^ p = 1)
    exact (QuotientGroup.eq_one_iff (N := frattini R) (x := x ^ p)).2
      (pth_power_mem_frattini_of_isPGroup (R := R) (p := p) x)

/-- An elementary abelian finite `p`-group has trivial Frattini subgroup. -/
public theorem frattini_eq_bot_of_isElementaryAbelian {R : Type*} [Group R] [Finite R]
    {p : ℕ} [Fact p.Prime] [Fact (IsPGroup p R)] [IsElementaryAbelian p R] :
    frattini R = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  by_cases hx1 : x = 1
  · simp [hx1]
  · let B : Subgroup R := Subgroup.zpowers x
    have hB_card : Nat.card B = p :=
      (Nat.card_zpowers x).trans (by
        rcases (Nat.dvd_prime (Fact.out : Nat.Prime p)).1
          ((orderOf_dvd_of_pow_eq_one (Monoid.pow_exponent_eq_one x)).trans
            (IsElementaryAbelian.exponent_dvd_p p R)) with h1 | hp
        · exact False.elim (hx1 (orderOf_eq_one_iff.mp h1))
        · exact hp)
    obtain ⟨C, hcompl⟩ := IsElementaryAbelian.exists_isCompl (p := p) (A := R) B
    have hx_not_C : x ∉ C := by
      intro hxC
      exact hx1 (by
        have hx_bot : x ∈ (⊥ : Subgroup R) := by
          rw [← hcompl.inf_eq_bot]
          exact ⟨(Subgroup.mem_zpowers x : x ∈ B), hxC⟩
        simpa using hx_bot)
    have hC_coatom : IsCoatom C := by
      refine ⟨?_, ?_⟩
      · intro hCtop
        exact hx_not_C (by simp [hCtop])
      · intro D hCD
        rcases SetLike.exists_of_lt hCD with ⟨d, hdD, hdnotC⟩
        rcases (Subgroup.mem_sup (s := B) (t := C) (x := d)).1 (by
          simp [(by simpa [sup_comm] using hcompl.sup_eq_top : B ⊔ C = ⊤)]) with
          ⟨b, hbB, c, hcC, hbc_eq⟩
        have hbD : b ∈ D := by
          simpa [mul_assoc, ← hbc_eq] using
            (D.mul_mem hdD (D.inv_mem ((le_of_lt hCD) hcC)))
        have hb_ne_one : b ≠ 1 := by
          intro hb1
          exact hdnotC (by simpa [← hbc_eq, hb1] using hcC)
        let E : Subgroup B := (B ⊓ D).subgroupOf B
        have hbE : (⟨b, hbB⟩ : B) ∈ E := by
          change b ∈ B ⊓ D
          exact ⟨hbB, hbD⟩
        have hE_ne_bot : E ≠ ⊥ := by
          intro hEbot
          have hbE_bot : (⟨b, hbB⟩ : B) ∈ (⊥ : Subgroup B) := by simpa [hEbot] using hbE
          have hb_eq_one : (⟨b, hbB⟩ : B) = 1 := by simpa using hbE_bot
          exact hb_ne_one (Subtype.ext_iff.mp hb_eq_one)
        haveI : Fact (Nat.card B).Prime := ⟨by simpa [hB_card] using (Fact.out : Nat.Prime p)⟩
        have hB_le_D : B ≤ D :=
          fun y hy => ((Subgroup.subgroupOf_eq_top).1
            ((Subgroup.eq_bot_or_eq_top_of_prime_card (G := B) E).resolve_left hE_ne_bot) hy).2
        exact top_le_iff.mp (by
          rw [← hcompl.sup_eq_top]
          exact sup_le hB_le_D (le_of_lt hCD))
    exact False.elim (hx_not_C ((frattini_le_coatom hC_coatom) hx))

/-- The Frattini quotient of an elementary abelian finite `p`-group is isomorphic to the group. -/
public noncomputable def frattiniQuotientEquivOfIsElementaryAbelian
    {R : Type*} [Group R] [Finite R]
    {p : ℕ} [Fact p.Prime] [Fact (IsPGroup p R)] [IsElementaryAbelian p R] :
    R ⧸ frattini R ≃* R :=
  (QuotientGroup.quotientMulEquivOfEq
    (frattini_eq_bot_of_isElementaryAbelian (R := R) (p := p))).trans
    (QuotientGroup.quotientBot (G := R))

public theorem frattiniQuotientEquivOfIsElementaryAbelian_mk'
    {R : Type*} [Group R] [Finite R]
    {p : ℕ} [Fact p.Prime] [Fact (IsPGroup p R)] [IsElementaryAbelian p R]
    (r : R) :
    frattiniQuotientEquivOfIsElementaryAbelian (R := R) (p := p)
      (QuotientGroup.mk' (frattini R) r) = r := by
  rfl

public theorem frattiniQuotientEquivOfIsElementaryAbelian_coe
    {R : Type*} [Group R] [Finite R]
    {p : ℕ} [Fact p.Prime] [Fact (IsPGroup p R)] [IsElementaryAbelian p R]
    (r : R) :
    frattiniQuotientEquivOfIsElementaryAbelian (R := R) (p := p)
      (r : R ⧸ frattini R) = r :=
  frattiniQuotientEquivOfIsElementaryAbelian_mk' (R := R) (p := p) r

/-- For a finite `p`-group, `Φ(R) = ⊥` iff `R` is elementary abelian. -/
public theorem frattini_eq_bot_iff_isElementaryAbelian {R : Type*} [Group R] [Finite R]
    {p : ℕ} [Fact p.Prime] [Fact (IsPGroup p R)] :
    frattini R = ⊥ ↔ IsElementaryAbelian p R := by
  constructor
  · intro hphi
    refine {
      toIsMulCommutative := ?_,
      exponent_dvd_p := ?_
    }
    · exact {
        is_comm := ⟨by
          intro a b
          exact ((Subgroup.mem_centralizer_iff (g := a) (s := ((⊤ : Subgroup R) : Set R))).1
            ((Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := (⊤ : Subgroup R))
              (H₂ := (⊤ : Subgroup R))).1 (by
              rw [← _root_.commutator_def]
              exact (le_antisymm (by simpa [hphi] using
                (commutator_le_frattini_of_isPGroup (R := R) (p := p))) bot_le)) (by simp))
            b (by simp)).symm⟩
      }
    · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
      intro x
      simpa [hphi] using (pth_power_mem_frattini_of_isPGroup (R := R) (p := p) x)
  · intro hElem
    letI : IsElementaryAbelian p R := hElem
    exact frattini_eq_bot_of_isElementaryAbelian (R := R) (p := p)

/-- For a finite `p`-group, `Φ(R)` is generated by commutators and `p`-th powers. -/
public theorem frattini_eq_closure_commutator_union_powers {R : Type*} [Group R] [Finite R]
    {p : ℕ} [Fact p.Prime] [Fact (IsPGroup p R)] :
    frattini R =
      Subgroup.closure (((_root_.commutator R : Subgroup R) : Set R) ∪
        Set.range (fun x : R => x ^ p)) := by
  let K : Subgroup R :=
    Subgroup.closure (((_root_.commutator R : Subgroup R) : Set R) ∪
      Set.range (fun x : R => x ^ p))
  letI : K.Normal := by
    refine ⟨fun n hn g => ?_⟩
    refine Subgroup.closure_induction (fun x hx => ?_) ?_ (fun x y _ _ ihx ihy => ?_)
      (fun x _ ihx => ?_) hn
    · rcases hx with hxcomm | ⟨y, rfl⟩
      · exact Subgroup.subset_closure
          (Or.inl (((Subgroup.commutator_normal (⊤ : Subgroup R) (⊤ : Subgroup R)).conj_mem
            x hxcomm g)))
      · exact Subgroup.subset_closure
          (Or.inr ⟨g * y * g⁻¹, conj_pow (a := g) (b := y) (i := p)⟩)
    · simp
    · rw [← conj_mul]
      exact K.mul_mem ihx ihy
    · rw [← conj_inv]
      exact K.inv_mem ihx
  haveI : Fact (IsPGroup p (R ⧸ K)) := ⟨(Fact.out : IsPGroup p R).to_quotient K⟩
  have hphi_quot : frattini (R ⧸ K) = ⊥ :=
    (frattini_eq_bot_iff_isElementaryAbelian (R := R ⧸ K) (p := p)).2 (by
      refine {
        toIsMulCommutative := ?_,
        exponent_dvd_p := ?_
      }
      · exact (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := K)).2 (by
          intro x hx
          exact Subgroup.subset_closure (Or.inl hx))
      · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
        intro q
        refine QuotientGroup.induction_on q ?_
        intro x
        change ((QuotientGroup.mk' K x : R ⧸ K) ^ p = 1)
        exact (QuotientGroup.eq_one_iff (N := K) (x := x ^ p)).2
          (Subgroup.subset_closure (Or.inr ⟨x, rfl⟩)))
  exact le_antisymm
    (by
      simpa [hphi_quot, K] using
        (frattini_le_comap_frattini_of_surjective (G := R) (H := R ⧸ K)
          (φ := QuotientGroup.mk' K) (QuotientGroup.mk'_surjective K)))
    (by
      refine (Subgroup.closure_le (K := frattini R)).2 ?_
      intro x hx
      rcases hx with hxcomm | ⟨y, rfl⟩
      · exact commutator_le_frattini_of_isPGroup (R := R) (p := p) hxcomm
      · exact pth_power_mem_frattini_of_isPGroup (R := R) (p := p) y)

end CFSG.Theory.Frattini
