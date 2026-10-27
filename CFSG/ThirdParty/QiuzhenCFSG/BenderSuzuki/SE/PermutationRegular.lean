module


public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixII.proposition_1
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Compat

namespace CFSG
end CFSG
open CFSG

/-!
# Regular normal subgroups in doubly transitive actions

This file extracts the generic checked content of the source citation
`[II1; 2.9]` used in Section 10.  It also records the affine factorization
forced by a regular abelian normal subgroup and a uniquely fixed involution.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1
open scoped IsMulCommutative

universe u v

/-- In a faithful transitive action, the rank-one factorization for a
nontrivial involution forces the odd core to be nontrivial. -/
public theorem pPrimeCore_two_ne_bot_of_factorization
    {G : Type u} {Omega : Type v} [Group G] [Finite G] [MulAction G Omega]
    [FaithfulSMul G Omega]
    (htrans : MulAction.IsPretransitive G Omega)
    {u0 : G} (hu : IsInvolution u0) (alpha : Omega)
    (hualpha : u0 • alpha = alpha)
    (hfactor : pPrimeCore 2 G ⊔
      Subgroup.centralizer ({u0} : Set G) = ⊤) :
    pPrimeCore 2 G ≠ ⊥ := by
  intro hcore
  have hCtop : Subgroup.centralizer ({u0} : Set G) = ⊤ := by
    simpa [hcore] using hfactor
  apply hu.ne_one
  apply @FaithfulSMul.eq_of_smul_eq_smul G Omega inferInstance inferInstance
  intro omega
  obtain ⟨g, hg⟩ := htrans.exists_smul_eq alpha omega
  have hgu : g * u0 = u0 * g := by
    have hgC : g ∈ Subgroup.centralizer ({u0} : Set G) := by
      rw [hCtop]
      trivial
    exact Subgroup.mem_centralizer_singleton_iff.mp hgC
  calc
    u0 • omega = u0 • (g • alpha) := by rw [hg]
    _ = (u0 * g) • alpha := by rw [mul_smul]
    _ = (g * u0) • alpha := by rw [hgu]
    _ = g • (u0 • alpha) := by rw [mul_smul]
    _ = g • alpha := by rw [hualpha]
    _ = omega := hg
    _ = (1 : G) • omega := (one_smul G omega).symm

/-- Generic core of `[II1; 2.9]`: a nontrivial solvable normal subgroup in a
faithful doubly transitive action contains a regular elementary-abelian
minimal normal subgroup. -/
public theorem exists_regular_elementaryAbelian_normal_of_solvable_normal
    {G : Type u} {Omega : Type v}
    [Group G] [Finite G] [MulAction G Omega] [Finite Omega]
    [FaithfulSMul G Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (N : Subgroup G) (hNnormal : N.Normal)
    (hN_ne_bot : N ≠ ⊥) (hNsolv : Group.IsSolvable N) :
    ∃ (F : Subgroup G) (p : ℕ), F.Normal ∧ p.Prime ∧
      IsElementaryAbelian p F ∧ F ≠ ⊥ ∧
      MulAction.IsPretransitive F Omega ∧
      (∀ omega : Omega, MulAction.stabilizer F omega = ⊥) := by
  classical
  obtain ⟨F, hFnorm, hF_le_N, hF_ne_bot, hFmin⟩ :=
    exists_minimal_normal_le (G := G) N hNnormal hN_ne_bot
  letI : F.Normal := hFnorm
  letI : IsMinimalNormal F := {
    minimal := by
      intro K hKnormal hKle
      by_cases hKbot : K = ⊥
      · exact Or.inl hKbot
      · exact Or.inr (hFmin K hKnormal hKle hKbot)
  }
  let FN : Subgroup N := F.subgroupOf N
  let eFN : FN ≃* F := Subgroup.subgroupOfEquivOfLe hF_le_N
  letI : Group.IsSolvable N := hNsolv
  have hFNsolv : Group.IsSolvable FN := inferInstance
  letI : Group.IsSolvable FN := hFNsolv
  have hFsolv : Group.IsSolvable F :=
    Group.isSolvable_of_surjective (f := eFN.toMonoidHom) eFN.surjective
  letI : Group.IsSolvable F := hFsolv
  obtain ⟨p, hp, hFelem⟩ :=
    minimalNormal_solvable_exists_isElementaryAbelian F
  letI : IsElementaryAbelian p F := hFelem
  letI : MulAction.IsPreprimitive G Omega :=
    MulAction.isPreprimitive_of_is_two_pretransitive htwo
  letI : MulAction.IsQuasiPreprimitive G Omega :=
    MulAction.IsPreprimitive.isQuasiPreprimitive
  have hfixed_ne_univ : MulAction.fixedPoints F Omega ≠ Set.univ := by
    intro hfixed
    apply hF_ne_bot
    rw [eq_bot_iff]
    intro f hf
    have hfix_all : ∀ omega : Omega, f • omega = omega := by
      intro omega
      have homega : omega ∈ MulAction.fixedPoints F Omega := by
        rw [hfixed]
        trivial
      exact MulAction.mem_fixedPoints.mp homega ⟨f, hf⟩
    have hf_one : f = 1 :=
      FaithfulSMul.eq_of_smul_eq_smul (m₁ := f) (m₂ := (1 : G)) (by
        intro omega
        calc
          f • omega = omega := hfix_all omega
          _ = (1 : G) • omega := (one_smul G omega).symm)
    exact Subgroup.mem_bot.mpr hf_one
  have hFtrans : MulAction.IsPretransitive F Omega :=
    MulAction.IsQuasiPreprimitive.isPretransitive_of_normal hfixed_ne_univ
  letI : MulAction.IsPretransitive F Omega := hFtrans
  have hFregular : ∀ omega : Omega, MulAction.stabilizer F omega = ⊥ := by
    intro omega
    rw [eq_bot_iff]
    intro f hf
    have hfix_all : ∀ eta : Omega, f • eta = eta := by
      intro eta
      obtain ⟨a, ha⟩ :=
        @MulAction.IsPretransitive.exists_smul_eq F Omega inferInstance
          inferInstance omega eta
      have hcomm : f * a = a * f := Std.Commutative.comm f a
      calc
        f • eta = f • (a • omega) := by rw [ha]
        _ = (f * a) • omega := by rw [mul_smul]
        _ = (a * f) • omega := by rw [hcomm]
        _ = a • (f • omega) := by rw [mul_smul]
        _ = a • omega := by rw [show f • omega = omega from hf]
        _ = eta := ha
    have hf_one_G : (f : G) = 1 :=
      FaithfulSMul.eq_of_smul_eq_smul
        (m₁ := (f : G)) (m₂ := (1 : G)) (by
          intro eta
          calc
            (f : G) • eta = eta := hfix_all eta
            _ = (1 : G) • eta := (one_smul G eta).symm)
    apply Subgroup.mem_bot.mpr
    exact Subtype.ext hf_one_G
  exact ⟨F, p, hFnorm, hp, hFelem, hF_ne_bot, hFtrans, hFregular⟩

/-- A regular abelian normal subgroup and an involution with a unique fixed
point give the affine factorization by that subgroup and the involution
centralizer. -/
public theorem regular_normal_sup_centralizer_eq_top
    {G : Type u} {Omega : Type v}
    [Group G] [Finite G] [MulAction G Omega] [Finite Omega]
    [FaithfulSMul G Omega]
    (Q : Subgroup G) (hQnormal : Q.Normal) (hQcomm : IsMulCommutative Q)
    (hQtrans : MulAction.IsPretransitive Q Omega)
    (hQregular : ∀ omega : Omega, MulAction.stabilizer Q omega = ⊥)
    {u0 : G} (hu : IsInvolution u0) (alpha : Omega)
    (hualpha : u0 • alpha = alpha)
    (huunique : ∀ omega : Omega, u0 • omega = omega → omega = alpha) :
    Q ⊔ Subgroup.centralizer ({u0} : Set G) = ⊤ := by
  classical
  letI : Q.Normal := hQnormal
  letI : IsMulCommutative Q := hQcomm
  letI : MulAction.IsPretransitive Q Omega := hQtrans
  have hconj_fixed_one {q : G} (hq : q ∈ Q)
      (hqu : rightConjugateElem q u0 = q) : q = 1 := by
    let qQ : Q := ⟨q, hq⟩
    change u0⁻¹ * q * u0 = q at hqu
    have hcomm : Commute q u0 := by
      rw [commute_iff_eq]
      calc
        q * u0 = u0 * (u0⁻¹ * q * u0) := by group
        _ = u0 * q := by rw [hqu]
    have hfix : u0 • (qQ • alpha) = qQ • alpha := by
      change u0 • (q • alpha) = q • alpha
      calc
        u0 • (q • alpha) = (u0 * q) • alpha := by rw [mul_smul]
        _ = (q * u0) • alpha := by rw [hcomm.eq]
        _ = q • (u0 • alpha) := by rw [mul_smul]
        _ = q • alpha := by rw [hualpha]
    have hqfix : qQ • alpha = alpha := huunique (qQ • alpha) hfix
    have hqstab : qQ ∈ MulAction.stabilizer Q alpha := hqfix
    rw [hQregular alpha] at hqstab
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hqstab)
  have hu_inverts : ∀ q : G, q ∈ Q → rightConjugateElem q u0 = q⁻¹ := by
    intro q hq
    let qu : G := rightConjugateElem q u0
    have hquQ : qu ∈ Q := by
      dsimp [qu, rightConjugateElem]
      simpa [hu.inv_eq_self] using hQnormal.conj_mem q hq u0
    have htwice : rightConjugateElem qu u0 = q := by
      have huu : u0 * u0 = 1 := by simpa [pow_two] using hu.sq_eq_one
      dsimp [qu, rightConjugateElem]
      rw [hu.inv_eq_self]
      calc
        u0 * (u0 * q * u0) * u0 = (u0 * u0) * q * (u0 * u0) := by group
        _ = q := by rw [huu]; simp
    have hcomm : q * qu = qu * q :=
      congrArg Subtype.val
        (mul_comm (⟨q, hq⟩ : Q) (⟨qu, hquQ⟩ : Q))
    have hprod_fixed : rightConjugateElem (q * qu) u0 = q * qu := by
      calc
        rightConjugateElem (q * qu) u0 =
            rightConjugateElem q u0 * rightConjugateElem qu u0 := by
              simp [rightConjugateElem, mul_assoc]
        _ = qu * q := by rw [htwice]
        _ = q * qu := hcomm.symm
    have hprod_one : q * qu = 1 :=
      hconj_fixed_one (Q.mul_mem hq hquQ) hprod_fixed
    calc
      rightConjugateElem q u0 = qu := rfl
      _ = q⁻¹ * (q * qu) := by group
      _ = q⁻¹ := by rw [hprod_one]; simp
  let H : Subgroup G := MulAction.stabilizer G alpha
  have hHcentral : H ≤ Subgroup.centralizer ({u0} : Set G) := by
    intro h hh
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hhfix : h • alpha = alpha := hh
    let uh : G := rightConjugateElem u0 h
    have huh : IsInvolution uh := isInvolution_rightConjugateElem hu
    have huhfix : uh • alpha = alpha := by
      dsimp [uh, rightConjugateElem]
      calc
        (h⁻¹ * u0 * h) • alpha = h⁻¹ • (u0 • (h • alpha)) := by
          simp only [mul_smul]
        _ = h⁻¹ • (u0 • alpha) := by rw [hhfix]
        _ = h⁻¹ • alpha := by rw [hualpha]
        _ = h⁻¹ • (h • alpha) :=
          congrArg (fun omega => h⁻¹ • omega) hhfix.symm
        _ = alpha := inv_smul_smul h alpha
    have huh_inverts : ∀ q : G, q ∈ Q → rightConjugateElem q uh = q⁻¹ := by
      intro q hq
      let r : G := h * q * h⁻¹
      have hrQ : r ∈ Q := by
        dsimp [r]
        exact hQnormal.conj_mem q hq h
      have hrInv := hu_inverts r hrQ
      change u0⁻¹ * r * u0 = r⁻¹ at hrInv
      calc
        rightConjugateElem q uh = h⁻¹ * (u0⁻¹ * r * u0) * h := by
          simp [uh, r, rightConjugateElem]
          group
        _ = h⁻¹ * r⁻¹ * h := by rw [hrInv]
        _ = q⁻¹ := by simp [r]
    have hacts_inversely
        {v : G} (hv : IsInvolution v) (hvalpha : v • alpha = alpha)
        (hvinv : ∀ q : G, q ∈ Q → rightConjugateElem q v = q⁻¹)
        (q : Q) :
        v • ((q : G) • alpha) = (q : G)⁻¹ • alpha := by
      have hconj := hvinv (q : G) q.property
      have hmove : v * (q : G) = (q : G)⁻¹ * v := by
        have hvv : v * v = 1 := by simpa [pow_two] using hv.sq_eq_one
        calc
          v * (q : G) = (v * (q : G) * v) * v := by
            rw [mul_assoc, hvv, mul_one]
          _ = (q : G)⁻¹ * v := by
            simpa [rightConjugateElem, hv.inv_eq_self] using
              congrArg (fun z : G => z * v) hconj
      calc
        v • ((q : G) • alpha) = (v * (q : G)) • alpha := by rw [mul_smul]
        _ = ((q : G)⁻¹ * v) • alpha := by rw [hmove]
        _ = (q : G)⁻¹ • (v • alpha) := by rw [mul_smul]
        _ = (q : G)⁻¹ • alpha := by rw [hvalpha]
    have huh_eq : uh = u0 := by
      apply @FaithfulSMul.eq_of_smul_eq_smul G Omega inferInstance inferInstance
      intro omega
      obtain ⟨q, hq⟩ :=
        @MulAction.IsPretransitive.exists_smul_eq Q Omega inferInstance
          inferInstance alpha omega
      rw [← hq]
      exact (hacts_inversely huh huhfix huh_inverts q).trans
        (hacts_inversely hu hualpha hu_inverts q).symm
    have hcomm : u0 * h = h * u0 := by
      calc
        u0 * h = h * (h⁻¹ * u0 * h) := by group
        _ = h * u0 := by
          simpa [uh, rightConjugateElem] using congrArg (fun z => h * z) huh_eq
    exact hcomm.symm
  have hQH : Q ⊔ H = ⊤ := by
    rw [eq_top_iff]
    intro g _hg
    obtain ⟨q, hq⟩ :=
      @MulAction.IsPretransitive.exists_smul_eq Q Omega inferInstance
        inferInstance alpha (g • alpha)
    have hqgH : (q : G)⁻¹ * g ∈ H := by
      change ((q : G)⁻¹ * g) • alpha = alpha
      rw [mul_smul, inv_smul_eq_iff]
      exact hq.symm
    have hprod : (q : G) * ((q : G)⁻¹ * g) ∈ Q ⊔ H :=
      Subgroup.mul_mem_sup q.property hqgH
    simpa using hprod
  apply le_antisymm le_top
  rw [← hQH]
  exact sup_le le_sup_left (hHcentral.trans le_sup_right)

/-- A transitive action with trivial point stabilizer has the same cardinality
as its acting group. -/
public theorem natCard_eq_of_pretransitive_stabilizer_bot
    {G : Type u} {Omega : Type v}
    [Group G] [Finite G] [MulAction G Omega] [Finite Omega]
    (htrans : MulAction.IsPretransitive G Omega)
    (hregular : ∀ omega : Omega, MulAction.stabilizer G omega = ⊥)
    (alpha : Omega) :
    Nat.card G = Nat.card Omega := by
  classical
  let orbitMap : G → Omega := fun g => g • alpha
  have horbit_surj : Function.Surjective orbitMap := by
    intro omega
    exact htrans.exists_smul_eq alpha omega
  have horbit_inj : Function.Injective orbitMap := by
    intro g h hgh
    have hstab : h⁻¹ * g ∈ MulAction.stabilizer G alpha := by
      change (h⁻¹ * g) • alpha = alpha
      rw [mul_smul, inv_smul_eq_iff]
      exact hgh
    rw [hregular alpha] at hstab
    have hone : h⁻¹ * g = 1 := Subgroup.mem_bot.mp hstab
    exact (inv_mul_eq_one.mp hone).symm
  exact Nat.card_congr (Equiv.ofBijective orbitMap ⟨horbit_inj, horbit_surj⟩)

/-- An elementary-abelian subgroup of cardinality at least three has odd order
inside a finite group of 2-rank at most one. -/
public theorem elementaryAbelian_card_odd_of_not_twoRank_of_three_le
    {G : Type u} [Group G] [Finite G]
    (hG : ¬ TwoRankAtLeastTwo G)
    {Q : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hQelem : IsElementaryAbelian p Q)
    (hQcard : 3 ≤ Nat.card Q) :
    Odd (Nat.card Q) := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  letI : IsElementaryAbelian p Q := hQelem
  have hp_ne_two : p ≠ 2 := by
    intro hp2
    subst p
    have hQp : IsPGroup 2 Q := IsElementaryAbelian.isPGroup 2 Q
    obtain ⟨n, hn⟩ := hQp.exists_card_eq
    have hfour : 2 ^ 2 ≤ Nat.card Q := by
      cases n with
      | zero =>
          exfalso
          have hcard_one : Nat.card Q = 1 := by simpa using hn
          omega
      | succ n =>
          cases n with
          | zero =>
              exfalso
              have hcard_two : Nat.card Q = 2 := by simpa using hn
              omega
          | succ n =>
              rw [hn]
              exact Nat.pow_le_pow_right (by omega) (by omega)
    obtain ⟨E, hEcard⟩ :=
      Sylow.exists_subgroup_card_pow_prime_of_le_card
        (G := Q) (n := 2) Nat.prime_two hQp hfour
    have hQrank : TwoRankAtLeastTwo Q := by
      refine ⟨E, by simpa using hEcard, ?_⟩
      intro x
      apply Subtype.ext
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 Q) (x : Q)
    exact hG (hQrank.map_of_injective Q.subtype Q.subtype_injective)
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup p Q).exists_card_eq
  rw [hn]
  exact (hp.odd_of_ne_two hp_ne_two).pow

end CFSG.BenderSuzuki
