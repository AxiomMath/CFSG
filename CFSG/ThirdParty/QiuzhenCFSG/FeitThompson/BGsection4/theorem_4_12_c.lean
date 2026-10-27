module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.theorem_4_12_b
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_10

namespace CFSG
end CFSG
open CFSG

open scoped FixedPoints

/-! # Infrastructure for Theorem 4.12(c) from BG Section 4 -/

section Main

open scoped FixedPoints

private theorem CFSG.omega₁_ne_bot_of_nontrivial_pGroup
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
  have hx_bot : x ∈ (⊥ : Subgroup G) := by
    simpa [hbot] using hx_mem
  exact hx_ne_one (by simpa using hx_bot)

public theorem CFSG.prime_le_natCard_omega₁_of_nontrivial_pGroup
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    [Fact (IsPGroup p G)] [Nontrivial G] :
    p ≤ Nat.card (omega₁ (G := G) (p := p)) := by
  have hΩ_ne_bot : omega₁ (G := G) (p := p) ≠ ⊥ :=
    omega₁_ne_bot_of_nontrivial_pGroup (G := G) (p := p)
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

public theorem CFSG.isCyclic_of_natCard_omega₁_eq_prime
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hpodd : p ≠ 2) [Fact (IsPGroup p G)]
    (hΩcard : Nat.card (omega₁ (G := G) (p := p)) = p) :
    IsCyclic G := by
  classical
  by_contra hncyc
  obtain ⟨E, _hE_normal, hEcard, hEelem⟩ :=
    lemma_4_5_a (R := G) (p := p) hpodd hncyc
  have hE_le_Ω : E ≤ omega₁ (G := G) (p := p) := elementaryAbelian_le_omega₁
  have hcard_le : Nat.card E ≤ Nat.card (omega₁ (G := G) (p := p)) :=
    Subgroup.card_le_of_le hE_le_Ω
  have hp_sq_le_p : p ^ 2 ≤ p := by
    simpa [hEcard, hΩcard] using hcard_le
  have hp_lt_sq : p < p ^ 2 := pow_two_gt_prime
  exact (not_le_of_gt hp_lt_sq) hp_sq_le_p

public theorem CFSG.omega₁_subgroups_card_mul_le_of_disjoint
    {R : Type*} [Group R] [Finite R]
    (H K Ω : Subgroup R)
    (hHΩ : H ≤ Ω) (hKΩ : K ≤ Ω) (hdisj : Disjoint H K) :
    Nat.card H * Nat.card K ≤ Nat.card Ω := by
  let f : H × K → Ω := fun x => ⟨(x.1 : R) * (x.2 : R),
    Ω.mul_mem (hHΩ x.1.2) (hKΩ x.2.2)⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have hxyR : (x.1 : R) * (x.2 : R) = (y.1 : R) * (y.2 : R) :=
      congrArg Subtype.val hxy
    exact Subgroup.mul_injective_of_disjoint hdisj hxyR
  have hcard := Nat.card_le_card_of_injective f hf
  simpa [Nat.card_prod] using hcard

/-! # Theorem 4.12(c) from BG Section 4 -/

section Main

open scoped FixedPoints

public theorem CFSG.theorem_4_12_c {R A : Type*} [Group R] [Finite R] [Group A] [Finite A]
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2) [Fact (IsPGroup p R)]
    [MulDistribMulAction A R] (hcop : Nat.Coprime p (Nat.card A))
    (hmeta : IsMetacyclic R) (hnab : ¬ IsMulCommutative R) (hntriv : ¬ ActsTrivially A R) :
    (commutatorAction (A := A) (G := R)) ≠ ⊥ ∧
      IsCyclic (commutatorAction (A := A) (G := R)) ∧
      fixedPointSubgroup A R ≠ ⊥ ∧
      IsCyclic (fixedPointSubgroup A R) ∧
      derivedSubgroup R ≤ commutatorAction (A := A) (G := R) := by
  classical
  let T : Subgroup R := commutatorAction (A := A) (G := R)
  let C : Subgroup R := fixedPointSubgroup A R
  have hRsolv : Group.IsSolvable R := by
    let : Group.IsNilpotent R := (Fact.out : IsPGroup p R).isNilpotent
    infer_instance
  have hcop' : Nat.Coprime (Nat.card A) (Nat.card R) := by
    obtain ⟨n, hn⟩ := (Fact.out : IsPGroup p R).exists_card_eq
    rw [hn]
    exact hcop.symm.pow_right n
  have hT_ne_bot : T ≠ ⊥ := by
    intro hbot
    have hcomm₂_bot : commutatorAction₂ (A := A) (G := R) = ⊥ := by
      rw [proposition_1_6_b (G := R) (A := A) hRsolv hcop']
      simpa [T] using hbot
    exact hntriv <| proposition_1_6_c (G := R) (A := A) hRsolv hcop' hcomm₂_bot
  have hTcomm : IsMulCommutative T := by
    simpa [T] using theorem_4_12_a (R := R) (A := A) (p := p) hpodd hcop hmeta
  have hT_ne_top : T ≠ ⊤ := by
    intro htop
    apply hnab
    refine ⟨⟨fun x y => ?_⟩⟩
    have hxT : x ∈ T := by rw [htop]; simp
    have hyT : y ∈ T := by rw [htop]; simp
    exact congrArg Subtype.val
      ((IsMulCommutative.is_comm (M := T)).comm ⟨x, hxT⟩ ⟨y, hyT⟩)
  obtain ⟨hsup, hdisj⟩ :=
    theorem_4_12_b (R := R) (A := A) (p := p) hpodd hcop hmeta
  have hsupTC : T ⊔ C = ⊤ := by simpa [T, C] using hsup
  have hdisjTC : Disjoint T C := by simpa [T, C] using hdisj
  have hC_ne_bot : C ≠ ⊥ := by
    intro hCbot
    have hTtop : T = ⊤ := by
      simpa [hCbot] using hsupTC
    exact hT_ne_top hTtop
  have hncycR : ¬ IsCyclic R := by
    intro hcyc
    exact hnab hcyc.isMulCommutative
  have hΩR_card : Nat.card (omega₁ (G := R) (p := p)) = p ^ 2 :=
    (lemma_4_10 (R := R) (p := p) hpodd hmeta hncycR).1
  let ΩT : Subgroup R := (omega₁ (G := T) (p := p)).map T.subtype
  let ΩC : Subgroup R := (omega₁ (G := C) (p := p)).map C.subtype
  let ΩR : Subgroup R := omega₁ (G := R) (p := p)
  have hΩT_le_ΩR : ΩT ≤ ΩR := by
    simpa [ΩT, ΩR] using omega₁_map_subtype_le (G := R) (p := p) T
  have hΩC_le_ΩR : ΩC ≤ ΩR := by
    simpa [ΩC, ΩR] using omega₁_map_subtype_le (G := R) (p := p) C
  have hΩT_le_T : ΩT ≤ T := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.2
  have hΩC_le_C : ΩC ≤ C := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.2
  have hΩdisj : Disjoint ΩT ΩC := by
    apply (disjoint_iff).2
    apply eq_bot_iff.2
    intro x hx
    have hxTC : x ∈ T ⊓ C := ⟨hΩT_le_T hx.1, hΩC_le_C hx.2⟩
    have hinf_bot : T ⊓ C = ⊥ := (disjoint_iff).1 hdisjTC
    simpa [hinf_bot] using hxTC
  have hΩprod_le : Nat.card ΩT * Nat.card ΩC ≤ p ^ 2 := by
    have hle := omega₁_subgroups_card_mul_le_of_disjoint
      (H := ΩT) (K := ΩC) (Ω := ΩR) hΩT_le_ΩR hΩC_le_ΩR hΩdisj
    simpa [ΩR, hΩR_card] using hle
  have hΩT_card_map : Nat.card ΩT = Nat.card (omega₁ (G := T) (p := p)) := by
    exact Subgroup.card_map_of_injective
      (K := omega₁ (G := T) (p := p)) (f := T.subtype) T.subtype_injective
  have hΩC_card_map : Nat.card ΩC = Nat.card (omega₁ (G := C) (p := p)) := by
    exact Subgroup.card_map_of_injective
      (K := omega₁ (G := C) (p := p)) (f := C.subtype) C.subtype_injective
  have hTp : IsPGroup p T := (Fact.out : IsPGroup p R).to_subgroup T
  have hCp : IsPGroup p C := (Fact.out : IsPGroup p R).to_subgroup C
  let : Fact (IsPGroup p T) := ⟨hTp⟩
  let : Fact (IsPGroup p C) := ⟨hCp⟩
  let : Nontrivial T := (Subgroup.nontrivial_iff_ne_bot T).2 hT_ne_bot
  let : Nontrivial C := (Subgroup.nontrivial_iff_ne_bot C).2 hC_ne_bot
  have hΩT_ge : p ≤ Nat.card ΩT := by
    rw [hΩT_card_map]
    exact prime_le_natCard_omega₁_of_nontrivial_pGroup (G := T) (p := p)
  have hΩC_ge : p ≤ Nat.card ΩC := by
    rw [hΩC_card_map]
    exact prime_le_natCard_omega₁_of_nontrivial_pGroup (G := C) (p := p)
  have hΩT_le_p : Nat.card ΩT ≤ p := by
    have hmul : Nat.card ΩT * p ≤ p * p := by
      calc
        Nat.card ΩT * p ≤ Nat.card ΩT * Nat.card ΩC :=
          Nat.mul_le_mul_left _ hΩC_ge
        _ ≤ p ^ 2 := hΩprod_le
        _ = p * p := by rw [pow_two]
    exact Nat.le_of_mul_le_mul_right hmul (Fact.out : Nat.Prime p).pos
  have hΩC_le_p : Nat.card ΩC ≤ p := by
    have hmul : Nat.card ΩC * p ≤ p * p := by
      calc
        Nat.card ΩC * p ≤ Nat.card ΩC * Nat.card ΩT :=
          Nat.mul_le_mul_left _ hΩT_ge
        _ = Nat.card ΩT * Nat.card ΩC := by rw [Nat.mul_comm]
        _ ≤ p ^ 2 := hΩprod_le
        _ = p * p := by rw [pow_two]
    exact Nat.le_of_mul_le_mul_right hmul (Fact.out : Nat.Prime p).pos
  have hΩT_card_eq_p : Nat.card (omega₁ (G := T) (p := p)) = p := by
    rw [← hΩT_card_map]
    exact le_antisymm hΩT_le_p hΩT_ge
  have hΩC_card_eq_p : Nat.card (omega₁ (G := C) (p := p)) = p := by
    rw [← hΩC_card_map]
    exact le_antisymm hΩC_le_p hΩC_ge
  have hTcyc : IsCyclic T :=
    isCyclic_of_natCard_omega₁_eq_prime (G := T) (p := p) hpodd hΩT_card_eq_p
  have hCcyc : IsCyclic C :=
    isCyclic_of_natCard_omega₁_eq_prime (G := C) (p := p) hpodd hΩC_card_eq_p
  have hder_le_T : derivedSubgroup R ≤ T := by
    let : T.Normal := by
      simpa [T] using commutatorAction_normal (G := R) (A := A)
    let : IsCyclic C := hCcyc
    have hCcomm : IsMulCommutative C := inferInstance
    have hcomm_le : _root_.commutator R ≤ T :=
      Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top
        (N := T) (H := C) hsupTC hCcomm
    change _root_.commutator R ≤ T
    exact hcomm_le
  exact ⟨by simpa [T] using hT_ne_bot, by simpa [T] using hTcyc,
    by simpa [C] using hC_ne_bot, by simpa [C] using hCcyc,
    by simpa [T] using hder_le_T⟩
