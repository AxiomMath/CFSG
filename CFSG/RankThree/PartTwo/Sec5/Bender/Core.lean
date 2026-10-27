module

public import CFSG.RankThree.PartTwo.Sec5.Bender.Norm
public import CFSG.RankThree.PartTwo.Sec5.Bender.Abelianization
import CFSG.LocalAnalysis.SectionRank.Ccomm.OddCritical
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.RankThree.PartTwo.Sec5.Bender

open CFSG
open scoped commutatorElement

variable {X : Type*} [Group X]

theorem eq_one_of_orderOf_dvd_of_pPow {M : Type*} [Group M] {p : ℕ} (hp : p.Prime) {φ : M}
    {k : ℕ}
    (hφ : ∃ n, φ ^ (p ^ n) = 1) (hdvd : orderOf φ ∣ k) (hk : ¬ p ∣ k) : φ = 1 := by
  obtain ⟨n, hn⟩ := hφ
  have h1 : orderOf φ ∣ p ^ n := orderOf_dvd_of_pow_eq_one hn
  have hcop : Nat.Coprime (p ^ n) k :=
    Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd hp).mpr hk)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 hdvd)

theorem exists_critical_faithful [Finite X] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {P : Subgroup X} (hP : IsPGroup p P) (hPbot : P ≠ ⊥) :
    ∃ D : Subgroup X, D ≤ P ∧
      (∀ g ∈ Subgroup.normalizer (P : Set X), g ∈ Subgroup.normalizer (D : Set X)) ∧
      (∀ x ∈ D, x ^ p = 1) ∧ ⁅D, P⁆ ≤ Subgroup.centralizer (D : Set X) ∧
      ∀ K : Subgroup X, ¬ p ∣ Nat.card K → K ≤ Subgroup.normalizer (P : Set X) →
        K ≤ Subgroup.centralizer (D : Set X) → K ≤ Subgroup.centralizer (P : Set X) := by
  have : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).mpr hPbot
  obtain ⟨D₀, hchar, -, hcomm, hexp, hfix⟩ :=
    CFSG.SectionRank.Ccomm.odd_critical_exponent_subgroup (p := p) hp2 hP
  refine ⟨D₀.map P.subtype, Subgroup.map_subtype_le D₀, ?_, ?_, ?_, ?_⟩
  · intro g hgP
    set φ := P.normalizerMonoidHom ⟨g, hgP⟩
    have hφ : D₀.map φ.toMonoidHom = D₀ := Subgroup.characteristic_iff_map_eq.mp hchar φ
    have hφs : D₀.map φ.symm.toMonoidHom = D₀ := Subgroup.characteristic_iff_map_eq.mp hchar _
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨d, hd, rfl⟩
      have hmem : φ d ∈ D₀ := hφ ▸ Subgroup.mem_map_of_mem φ.toMonoidHom hd
      exact ⟨φ d, hmem, rfl⟩
    · intro hh
      obtain ⟨e, he, hee⟩ := Subgroup.mem_map.mp hh
      have hhP : h ∈ P := by
        have h1 : g * h * g⁻¹ ∈ P := hee ▸ e.2
        exact (Subgroup.mem_normalizer_iff.mp hgP h).mpr h1
      have hmem : φ.symm e ∈ D₀ := hφs ▸ Subgroup.mem_map_of_mem φ.symm.toMonoidHom he
      refine ⟨φ.symm e, hmem, ?_⟩
      have hφe : φ ⟨h, hhP⟩ = e := Subtype.ext hee.symm
      rw [← hφe, MulEquiv.symm_apply_apply]
      rfl
  · rintro _ ⟨d, hd, rfl⟩
    change ((d ^ p : P) : X) = 1
    rw [hexp d hd, Subgroup.coe_one]
  · have hmap : ⁅D₀.map P.subtype, P⁆ = (⁅D₀, (⊤ : Subgroup P)⁆ : Subgroup P).map P.subtype := by
      rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [hmap]
    rintro _ ⟨c, hc, rfl⟩
    have hc' := hcomm hc
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨d, hd, rfl⟩
    exact congrArg Subtype.val
      (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc').2 d hd)
  · intro K hK hKP hKD k hk
    set φ := P.normalizerMonoidHom ⟨k, hKP hk⟩
    have hφfix : φ ∈ fixingSubgroup (MulAut P) (D₀ : Set P) := by
      rw [mem_fixingSubgroup_iff]
      intro d hd
      apply Subtype.ext
      change k * (d : X) * k⁻¹ = d
      have hdD : (d : X) ∈ D₀.map P.subtype := Subgroup.mem_map_of_mem P.subtype hd
      rw [← Subgroup.mem_centralizer_iff.mp (hKD hk) _ hdD, mul_inv_cancel_right]
    have hφ1 : (⟨φ, hφfix⟩ : fixingSubgroup (MulAut P) (D₀ : Set P)) = 1 := by
      refine eq_one_of_orderOf_dvd_of_pPow (Fact.out) (k := Nat.card K) (hfix _) ?_ hK
      have h2 : orderOf φ ∣ orderOf (⟨k, hKP hk⟩ : Subgroup.normalizer (P : Set X)) :=
        orderOf_map_dvd _ _
      have h3 : orderOf (⟨k, hKP hk⟩ : Subgroup.normalizer (P : Set X)) = orderOf k :=
        Subgroup.orderOf_mk k _
      have h4 : orderOf (⟨φ, hφfix⟩ : fixingSubgroup (MulAut P) (D₀ : Set P)) = orderOf φ :=
        Subgroup.orderOf_mk φ _
      rw [h4]
      exact h2.trans (h3 ▸ Subgroup.orderOf_dvd_natCard K hk)
    have hφ1' : φ = 1 := congrArg Subtype.val hφ1
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have h6 := DFunLike.congr_fun hφ1' ⟨q, hq⟩
    have h5 : k * q * k⁻¹ = q := congrArg Subtype.val h6
    calc q * k = k * q * k⁻¹ * k := by rw [h5]
      _ = k * q := by group

theorem commutator_le_commutator_commutator (W R : Subgroup X)
    (hRW : R ≤ Subgroup.normalizer (W : Set X)) (hcop : Nat.Coprime (Nat.card R) (Nat.card W)) :
    ⁅W, R⁆ ≤ ⁅⁅W, R⁆, R⁆ := by
  classical
  have : Subgroup.Normalizes R W := ⟨hRW⟩
  have h2 : CFSG.commutatorAction₂ (A := R) (G := W) = CFSG.commutatorAction (A := R) (G := W) :=
    CFSG.commutatorAction₂_eq_commutatorAction_of_coprime (G := W) (A := R) hcop
  have hmap : (CFSG.commutatorAction (A := R) (G := W)).map W.subtype = ⁅W, R⁆ := by
    simpa using CFSG.commutatorAction_subgroup_conj_map_eq_commutator W R hRW
  have hmap2 : (CFSG.commutatorAction₂ (A := R) (G := W)).map W.subtype ≤ ⁅⁅W, R⁆, R⁆ := by
    let C : Subgroup W := CFSG.commutatorAction (A := R) (G := W)
    let S : Set W := {x : W | ∃ a : R, ∃ h : W, h ∈ C ∧ x = h⁻¹ * (a • h)}
    calc (CFSG.commutatorAction₂ (A := R) (G := W)).map W.subtype =
          (Subgroup.closure S).map W.subtype := rfl
      _ = Subgroup.closure (W.subtype '' S) := by
        simpa using (MonoidHom.map_closure (f := W.subtype) S)
      _ ≤ ⁅⁅W, R⁆, R⁆ := by
        refine (Subgroup.closure_le (K := ⁅⁅W, R⁆, R⁆)).2 ?_
        rintro _ ⟨y, hy, rfl⟩
        rcases hy with ⟨a, h, hhC, rfl⟩
        have hhcomm : (h : X) ∈ ⁅W, R⁆ := by
          rw [← hmap]
          exact Subgroup.mem_map_of_mem W.subtype hhC
        have hcomm : ⁅(h : X)⁻¹, (a : X)⁆ ∈ ⁅⁅W, R⁆, R⁆ :=
          Subgroup.commutator_mem_commutator ((⁅W, R⁆ : Subgroup X).inv_mem hhcomm) a.2
        simpa [commutatorElement_def, Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe,
          hRW, mul_assoc] using hcomm
  intro x hx
  rw [← hmap, ← h2] at hx
  exact hmap2 hx

theorem bender_core [Finite X] {p : ℕ} [hpF : Fact p.Prime] (hp2 : p ≠ 2) {P S : Subgroup X}
    {a : X} (hP : IsPGroup p P) (hexp : ∀ x ∈ P, x ^ p = 1)
    (hcl : ⁅P, P⁆ ≤ Subgroup.centralizer (P : Set X)) (hS : ¬ p ∣ Nat.card S)
    (hSP : S ≤ Subgroup.normalizer (P : Set X)) (hPS : ⁅P, S⁆ = P)
    (ha : a ∈ Subgroup.normalizer (P : Set X)) (haS : a ∈ Subgroup.normalizer (S : Set X))
    (hap : a ^ p = 1)
    (hCS : S ⊓ Subgroup.centralizer ({a} : Set X) ≤ Subgroup.centralizer (P : Set X))
    (hCP : P ⊓ Subgroup.centralizer ({a} : Set X) ≤ Subgroup.centralizer (S : Set X)) :
    P = ⊥ := by
  classical
  have hp : p.Prime := hpF.out
  have hV : ∀ v : Abelianization P, v ^ p = 1 := by
    intro v
    refine QuotientGroup.induction_on v fun y => ?_
    change (Abelianization.of y) ^ p = 1
    rw [← map_pow, show y ^ p = 1 from Subtype.ext (by simpa using hexp y y.2), map_one]
  have : Fintype (abImage P S) := Fintype.ofFinite _
  have hT : Nat.Coprime p (Nat.card (abImage P S)) := by
    refine (Nat.Prime.coprime_iff_not_dvd hp).mpr fun hdvd => hS ?_
    have h1 : Nat.card (abImage P S) ∣
        Nat.card (S.subgroupOf (Subgroup.normalizer (P : Set X))) :=
      Subgroup.card_map_dvd _ _
    have h2 : Nat.card (S.subgroupOf (Subgroup.normalizer (P : Set X))) = Nat.card S :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSP).toEquiv
    exact hdvd.trans (h2 ▸ h1)
  set a' : Subgroup.normalizer (P : Set X) := ⟨a, ha⟩ with ha'
  set β := abConj P a' with hβ
  have hconjT : ∀ b : Subgroup.normalizer (P : Set X),
      (b : X) ∈ Subgroup.normalizer (S : Set X) →
      ∀ t ∈ abImage P S, abConj P b * t * (abConj P b)⁻¹ ∈ abImage P S := by
    rintro b hb _ ⟨g, hg, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hg
    refine ⟨b * g * b⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by rw [map_mul, map_mul, map_inv]⟩
    exact (Subgroup.mem_normalizer_iff.mp hb g).mp hg
  have hβT : β ∈ Subgroup.normalizer (abImage P S : Set (MulAut (Abelianization P))) := by
    rw [Subgroup.mem_normalizer_iff]
    intro t
    refine ⟨hconjT a' haS t, fun ht => ?_⟩
    have := hconjT a'⁻¹ (Subgroup.inv_mem _ haS) _ ht
    rwa [map_inv, inv_inv, show β⁻¹ * (β * t * β⁻¹) * β = t by group] at this
  have hβp : β ^ p = 1 := by
    rw [hβ, ← map_pow, show a' ^ p = 1 from Subtype.ext (by simpa using hap), map_one]
  set K : Subgroup X := S ⊓ (abConj P).ker.map (Subgroup.normalizer (P : Set X)).subtype
    with hK
  have hKS : ¬ p ∣ Nat.card K := fun h => hS (h.trans (Subgroup.card_dvd_of_le inf_le_left))
  have haK : a ∈ Subgroup.normalizer (K : Set X) :=
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨haS, mem_normalizer_map_subtype_of_normal (abConj P).normal_ker a'⟩
  have hfpf : ∀ t ∈ abImage P S, ∀ i : ℕ, 0 < i → i < p → t * β ^ i = β ^ i * t → t = 1 := by
    rintro _ ⟨g, hg, rfl⟩ i hi0 hip hcomm
    have hcomm1 : abConj P g * β = β * abConj P g := commute_of_commute_pow hp hβp hi0 hip hcomm
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hg
    have hmemK : (g : X)⁻¹ * a * g * a⁻¹ ∈ K := by
      refine ⟨?_, ⟨g⁻¹ * a' * g * a'⁻¹, ?_, rfl⟩⟩
      · have h1 : a * (g : X) * a⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp haS g).mp hg
        have := S.mul_mem (S.inv_mem hg) h1
        simpa [mul_assoc] using this
      · rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, ← hβ]
        calc (abConj P g)⁻¹ * β * abConj P g * β⁻¹
            = (abConj P g)⁻¹ * (β * abConj P g) * β⁻¹ := by group
          _ = (abConj P g)⁻¹ * (abConj P g * β) * β⁻¹ := by rw [hcomm1]
          _ = 1 := by group
    obtain ⟨k, hkK, hgk⟩ := exists_mul_mem_centralizer hKS hap haK hmemK
    obtain ⟨hkS, k', hk', hkk'⟩ := hkK
    have hgkP : (g : X) * k ∈ Subgroup.centralizer (P : Set X) := hCS ⟨S.mul_mem hg hkS, hgk⟩
    have h1 : abConj P (g * k') = 1 := by
      apply abConj_eq_one_of_mem_centralizer
      change (g : X) * (k' : X) ∈ _
      rw [show (k' : X) = k from hkk']
      exact hgkP
    rw [map_mul, MonoidHom.mem_ker.mp hk', mul_one] at h1
    exact h1
  have hprod : ∀ x (hx : x ∈ P) (k : ℕ), ∃ hk : (x * a) ^ k * (a ^ k)⁻¹ ∈ P,
      Abelianization.of (⟨(x * a) ^ k * (a ^ k)⁻¹, hk⟩ : P) =
        ∏ i ∈ Finset.range k, (β ^ i) (Abelianization.of ⟨x, hx⟩) := by
    intro x hx k
    induction k with
    | zero =>
      have h0 : (x * a) ^ 0 * (a ^ 0)⁻¹ ∈ P := by
        rw [pow_zero, pow_zero, inv_one, mul_one]
        exact P.one_mem
      refine ⟨h0, ?_⟩
      have : (⟨(x * a) ^ 0 * (a ^ 0)⁻¹, h0⟩ : P) = 1 := Subtype.ext (by simp)
      rw [this, map_one, Finset.prod_range_zero]
    | succ k ih =>
      obtain ⟨hk, hkeq⟩ := ih
      have hak : a ^ k * x * (a ^ k)⁻¹ ∈ P :=
        (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ ha k) x).mp hx
      have heq : (x * a) ^ (k + 1) * (a ^ (k + 1))⁻¹ =
          ((x * a) ^ k * (a ^ k)⁻¹) * (a ^ k * x * (a ^ k)⁻¹) := by
        rw [pow_succ, pow_succ]
        group
      refine ⟨heq ▸ P.mul_mem hk hak, ?_⟩
      rw [Finset.prod_range_succ, ← hkeq]
      have h2 : (β ^ k) (Abelianization.of ⟨x, hx⟩) =
          Abelianization.of ⟨a ^ k * x * (a ^ k)⁻¹, hak⟩ := by
        rw [hβ, ← map_pow, abConj_of]
        rfl
      rw [h2, ← map_mul]
      congr 1
      exact Subtype.ext heq
  have hNβ : ∀ v : Abelianization P, ∏ i ∈ Finset.range p, (β ^ i) v = 1 := by
    intro v
    refine QuotientGroup.induction_on v fun y => ?_
    change ∏ i ∈ Finset.range p, (β ^ i) (Abelianization.of y) = 1
    obtain ⟨hk, hkeq⟩ := hprod y y.2 p
    have hkeq' : Abelianization.of (⟨((y : X) * a) ^ p * (a ^ p)⁻¹, hk⟩ : P) =
        ∏ i ∈ Finset.range p, (β ^ i) (Abelianization.of y) := hkeq
    rw [← hkeq']
    obtain ⟨hnP, z, hz, hnz⟩ := norm_trick hp2 hp hcl ha hap y.2
    have hn : (⟨((y : X) * a) ^ p * (a ^ p)⁻¹, hk⟩ : P) = ⟨((y : X) * a) ^ p, hnP⟩ :=
      Subtype.ext (by simp only [hap, inv_one, mul_one])
    rw [hn]
    have hzP : z ∈ P := Subgroup.commutator_le.mpr (fun g hg h hh => by
      rw [commutatorElement_def]
      exact P.mul_mem (P.mul_mem (P.mul_mem hg hh) (P.inv_mem hg)) (P.inv_mem hh)) hz
    have hnzP : ((y : X) * a) ^ p * z ∈ P := P.mul_mem hnP hzP
    have hfix : Abelianization.of (⟨((y : X) * a) ^ p * z, hnzP⟩ : P) = 1 := by
      apply eq_one_of_forall_abImage_fixed hSP hPS hT (hV _)
      rintro _ ⟨g, hg, rfl⟩
      rw [abConj_of]
      congr 1
      apply Subtype.ext
      change (g : X) * (((y : X) * a) ^ p * z) * (g : X)⁻¹ = ((y : X) * a) ^ p * z
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hg
      have hc := Subgroup.mem_centralizer_iff.mp (hCP ⟨hnzP, hnz⟩) g hg
      rw [hc, mul_inv_cancel_right]
    have hz1 : Abelianization.of (⟨z, hzP⟩ : P) = 1 := of_eq_one_of_mem_commutator P hz hzP
    have hsplit : (⟨((y : X) * a) ^ p * z, hnzP⟩ : P) = ⟨((y : X) * a) ^ p, hnP⟩ * ⟨z, hzP⟩ :=
      rfl
    rw [hsplit, map_mul, hz1, mul_one] at hfix
    exact hfix
  have hall := frobenius_norm_trivial hp.pos hV (abImage P S) hT β hβT hfpf
    (norm_abImage_eq_one hSP hPS) hNβ
  by_contra hPbot
  have : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).mpr hPbot
  have : Group.IsNilpotent P := hP.isNilpotent
  have htop : commutator P = ⊤ := by
    rw [eq_top_iff]
    intro y _
    rw [← Abelianization.ker_of, MonoidHom.mem_ker]
    exact hall _
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial (G := P)).ne htop

end CFSG.RankThree.PartTwo.Sec5.Bender
