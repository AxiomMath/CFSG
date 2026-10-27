module

public import CFSG.Foundations.Basic
public import CFSG.GroupTheory.FrattiniQuotient
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.Nilpotent
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBM

open Subgroup CFSG CFSG.OrderReductions.FrattiniAutomorphisms
open scoped commutatorElement

theorem card_le_four_of_closure_pair {X : Type*} [Group X] (hcomm : ∀ a b : X, a * b = b * a)
    (hsq : ∀ a : X, a ^ 2 = 1) {u v : X} (huv : closure ({u, v} : Set X) = ⊤) :
    Nat.card X ≤ 4 := by
  let f₁ : Multiplicative (ZMod 2) →* X := CFSG.LocalAnalysis.ComponentInitial.zmodHom 2 u (hsq u)
  let f₂ : Multiplicative (ZMod 2) →* X := CFSG.LocalAnalysis.ComponentInitial.zmodHom 2 v (hsq v)
  let f : Multiplicative (ZMod 2) × Multiplicative (ZMod 2) →* X :=
    MonoidHom.noncommCoprod f₁ f₂ fun a b => hcomm _ _
  have hsurj : Function.Surjective f := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← huv, closure_le]
    rintro w (rfl | rfl)
    · refine ⟨(Multiplicative.ofAdd 1, 1), ?_⟩
      change f₁ (Multiplicative.ofAdd 1) * f₂ 1 = w
      rw [map_one f₂, mul_one]
      exact CFSG.LocalAnalysis.ComponentInitial.zmodHom_ofAdd_one 2 w (hsq w)
    · refine ⟨(1, Multiplicative.ofAdd 1), ?_⟩
      change f₁ 1 * f₂ (Multiplicative.ofAdd 1) = w
      rw [map_one f₁, one_mul]
      exact CFSG.LocalAnalysis.ComponentInitial.zmodHom_ofAdd_one 2 w (hsq w)
  have : Finite X := Finite.of_surjective f hsurj
  calc Nat.card X ≤ Nat.card (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :=
        Nat.card_le_card_of_surjective f hsurj
    _ = 4 := by
        rw [Nat.card_prod, Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 2) ≃ ZMod 2),
          Nat.card_zmod]

theorem mulAut_eq_one_of_card_le_four {X : Type*} [Group X] [Finite X] (hX : Nat.card X ≤ 4)
    {p : ℕ} [Fact p.Prime] (hp : 4 < p) {τ : MulAut X} (hτ : IsPGroup p (zpowers τ)) : τ = 1 := by
  have hcong := hτ.card_modEq_card_fixedPoints X
  have hle : Nat.card (MulAction.fixedPoints (zpowers τ) X) ≤ Nat.card X :=
    Nat.card_le_card_of_injective _ Subtype.val_injective
  have hpos : 1 ≤ Nat.card (MulAction.fixedPoints (zpowers τ) X) := by
    have : Nonempty (MulAction.fixedPoints (zpowers τ) X) := ⟨⟨1, fun g => map_one (g : MulAut X)⟩⟩
    exact Nat.card_pos
  have heq : Nat.card (MulAction.fixedPoints (zpowers τ) X) = Nat.card X := by
    have h := (Nat.modEq_iff_dvd' hle).mp hcong.symm
    by_contra hne
    have hlt : Nat.card X - Nat.card (MulAction.fixedPoints (zpowers τ) X) < p := by omega
    have hpos' : 0 < Nat.card X - Nat.card (MulAction.fixedPoints (zpowers τ) X) := by omega
    exact absurd (Nat.le_of_dvd hpos' h) (by omega)
  have hall : ∀ x : X, x ∈ MulAction.fixedPoints (zpowers τ) X := by
    have : Fintype X := Fintype.ofFinite X
    have hset : MulAction.fixedPoints (zpowers τ) X = Set.univ := by
      apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _)
      · rw [Set.ncard_univ, ← Nat.card_coe_set_eq]
        exact heq.ge
    intro x
    rw [hset]
    exact Set.mem_univ x
  ext x
  exact hall x ⟨τ, mem_zpowers τ⟩

variable {G : Type*} [Group G]

theorem conj_trivial_mod_odd_core [Finite G] {Q : Subgroup G} [Q.Normal]
    (hQab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x)
    (hgen : ∃ T : Sylow 2 Q, ∃ x y : Q, closure ({x, y} : Set Q) = (T : Subgroup Q))
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {a : G} (ha : IsPGroup p (zpowers a)) :
    quotientAutomorphism (pPrimeCore 2 Q) (MulAut.conjNormal a) = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  set P := Q ⧸ pPrimeCore 2 Q
  set mk := QuotientGroup.mk' (pPrimeCore 2 Q)
  have hQab' : ∀ x y : Q, x * y = y * x := fun x y => Subtype.ext (hQab x x.2 y y.2)
  have hnil : Group.IsNilpotent Q := by
    have : IsMulCommutative Q := ⟨⟨hQab'⟩⟩
    infer_instance
  have htop := CFSG.nilpotent_top_le_pCore_sup_pPrimeCore (p := 2) hnil
  have hmk2 : (pCore 2 Q).map mk = ⊤ := by
    rw [eq_top_iff]
    rintro q -
    obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective _ q
    obtain ⟨t, ht, o, ho, rfl⟩ := mem_sup_of_normal_right.mp (htop (mem_top q))
    refine ⟨t, ht, ?_⟩
    rw [map_mul, show mk o = 1 from (QuotientGroup.eq_one_iff o).mpr ho, mul_one]
  have hP2 : IsPGroup 2 P := by
    refine (CFSG.pCore_isPGroup (p := 2) (G := Q)).of_surjective (mk.comp (pCore 2 Q).subtype)
      fun q => ?_
    have hq : q ∈ (pCore 2 Q).map mk := hmk2 ▸ mem_top q
    obtain ⟨t, ht, rfl⟩ := hq
    exact ⟨⟨t, ht⟩, rfl⟩
  obtain ⟨T, x, y, hxy⟩ := hgen
  have hPgen : closure ({mk x, mk y} : Set P) = ⊤ := by
    have hle : pCore 2 Q ≤ (T : Subgroup Q) :=
      (CFSG.pCore_isPGroup (p := 2) (G := Q)).le_sylow_of_normal T
    rw [eq_top_iff, ← hmk2]
    refine (map_mono (hle.trans hxy.ge)).trans ?_
    rw [MonoidHom.map_closure, Set.image_pair]
  obtain ⟨-, hXcomm, hXexp, -, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hP2
  obtain ⟨-, hker2⟩ := CFSG.GroupTheory.frattini_automorphism_kernel hP2
  have hXcard : Nat.card (P ⧸ frattini P) ≤ 4 := by
    refine card_le_four_of_closure_pair (fun a b => hXcomm.is_comm.comm a b) hXexp
      (u := QuotientGroup.mk' (frattini P) (mk x)) (v := QuotientGroup.mk' (frattini P) (mk y)) ?_
    rw [← Set.image_pair, ← MonoidHom.map_closure, hPgen,
      map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  set Ψ : G →* MulAut P := (quotientAutomorphism (pPrimeCore 2 Q)).comp MulAut.conjNormal
  set σ := Ψ a with hσ
  have hσp : IsPGroup p (zpowers σ) := by
    have h := ha.map Ψ
    rwa [MonoidHom.map_zpowers] at h
  set Ψ' := quotientAutomorphism (frattini P)
  have hτ : Ψ' σ = 1 := by
    have : Finite (P ⧸ frattini P) := inferInstance
    have hp4 : 4 < p := by
      rcases Nat.lt_or_ge 4 p with h | h
      · exact h
      · interval_cases p
        exact absurd hp (by norm_num)
    refine mulAut_eq_one_of_card_le_four (p := p) hXcard hp4 ?_
    have h := hσp.map Ψ'
    rwa [MonoidHom.map_zpowers] at h
  have hσker : σ ∈ Ψ'.ker := hτ
  obtain ⟨i, hi⟩ := (hker2.to_le (zpowers_le.mpr hσker)).exists_card_eq
  obtain ⟨j, hj⟩ := hσp.exists_card_eq
  rw [Nat.card_zpowers] at hi hj
  have hσ1 : orderOf σ = 1 := by
    rw [hi] at hj
    rcases i with _ | i
    · rwa [pow_zero] at hi
    · exfalso
      have h2 : 2 ∣ p ^ j := hj ▸ dvd_pow_self 2 (Nat.succ_ne_zero i)
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp (Nat.prime_two.dvd_of_dvd_pow h2)
      omega
  exact orderOf_eq_one_iff.mp hσ1

theorem abelian_two_generator_two_part_commutators_odd [Finite G] {Q : Subgroup G} [Q.Normal]
    (hQab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x)
    (hgen : ∃ T : Sylow 2 Q, ∃ x y : Q, closure ({x, y} : Set Q) = (T : Subgroup Q))
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {A : Subgroup G} (hA : IsPGroup p A) {S : Subgroup G}
    (hSA : ⁅S, A⁆ ≤ Q) : Odd (Nat.card (⁅S, A⁆ : Subgroup G)) := by
  have : Fact p.Prime := ⟨hp⟩
  set mk := QuotientGroup.mk' (pPrimeCore 2 Q)
  have hkey : ∀ a ∈ A, ∀ s ∈ S, ∀ hd : ⁅a, s⁆ ∈ Q, (⟨⁅a, s⁆, hd⟩ : Q) ∈ pPrimeCore 2 Q := by
    intro a ha s hs hd
    have hap : IsPGroup p (zpowers a) := hA.to_le (zpowers_le.mpr ha)
    have htriv := conj_trivial_mod_odd_core hQab hgen hp hp3 hap
    have hconj : ∀ q : Q, mk ⟨a * q * a⁻¹, (inferInstance : Q.Normal).conj_mem q q.2 a⟩ = mk q := by
      intro q
      have h := congrArg (fun σ : MulAut (Q ⧸ pPrimeCore 2 Q) =>
        σ (QuotientGroup.mk' (pPrimeCore 2 Q) q)) htriv
      simp only [MulAut.one_apply] at h
      rw [quotientAutomorphism_apply] at h
      have e : (MulAut.conjNormal a) q =
          ⟨a * q * a⁻¹, (inferInstance : Q.Normal).conj_mem q q.2 a⟩ :=
        Subtype.ext (MulAut.conjNormal_apply a q)
      rw [e] at h
      exact h
    set d : Q := ⟨⁅a, s⁆, hd⟩ with hddef
    have hiter : ∀ k : ℕ, ∃ e : Q, a ^ k * s * (a ^ k)⁻¹ = e * s ∧ mk e = mk d ^ k := by
      intro k
      induction k with
      | zero => exact ⟨1, by simp, by simp⟩
      | succ k ih =>
        obtain ⟨e, he, hek⟩ := ih
        refine ⟨⟨a * e * a⁻¹, (inferInstance : Q.Normal).conj_mem e e.2 a⟩ * d, ?_, ?_⟩
        · change a ^ (k + 1) * s * (a ^ (k + 1))⁻¹ = a * e * a⁻¹ * ⁅a, s⁆ * s
          calc a ^ (k + 1) * s * (a ^ (k + 1))⁻¹ = a * (a ^ k * s * (a ^ k)⁻¹) * a⁻¹ := by
                rw [pow_succ']
                group
            _ = a * (e * s) * a⁻¹ := by rw [he]
            _ = a * e * a⁻¹ * ⁅a, s⁆ * s := by rw [commutatorElement_def]; group
        · rw [map_mul, hconj, hek, pow_succ]
    obtain ⟨e, he, hek⟩ := hiter (orderOf a)
    rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at he
    have he1 : e = 1 := Subtype.ext (by
      have := congrArg (· * s⁻¹) he
      simpa using this.symm)
    rw [he1, map_one] at hek
    have hP2 : IsPGroup 2 (Q ⧸ pPrimeCore 2 Q) := by
      have hnil : Group.IsNilpotent Q := by
        have : IsMulCommutative Q := ⟨⟨fun x y => Subtype.ext (hQab x x.2 y y.2)⟩⟩
        infer_instance
      have htop := CFSG.nilpotent_top_le_pCore_sup_pPrimeCore (p := 2) hnil
      refine (CFSG.pCore_isPGroup (p := 2) (G := Q)).of_surjective
        (mk.comp (pCore 2 Q).subtype) fun q => ?_
      obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective _ q
      obtain ⟨t, ht, o, ho, rfl⟩ := mem_sup_of_normal_right.mp (htop (mem_top q))
      refine ⟨⟨t, ht⟩, ?_⟩
      change mk t = mk (t * o)
      rw [map_mul, show mk o = 1 from (QuotientGroup.eq_one_iff o).mpr ho, mul_one]
    obtain ⟨i, hi⟩ := hP2 (mk d)
    obtain ⟨j, hj⟩ := hap.exists_card_eq
    rw [Nat.card_zpowers] at hj
    have hdvd : orderOf (mk d) ∣ 2 ^ i := orderOf_dvd_of_pow_eq_one hi
    have hdvd' : orderOf (mk d) ∣ p ^ j := hj ▸ orderOf_dvd_of_pow_eq_one hek.symm
    have hcop : Nat.Coprime (2 ^ i) (p ^ j) :=
      Nat.Coprime.pow i j ((Nat.coprime_primes Nat.prime_two hp).mpr (by omega))
    have h1 : orderOf (mk d) = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd hdvd'
    exact (QuotientGroup.eq_one_iff d).mp (orderOf_eq_one_iff.mp h1)
  have hle : ⁅S, A⁆ ≤ inSubgroup (pPrimeCore 2) Q := by
    rw [commutator_le]
    intro s hs a ha
    have hd : ⁅a, s⁆ ∈ Q := hSA (by
      rw [commutator_comm]
      exact commutator_mem_commutator ha hs)
    have hsa : ⁅s, a⁆ = ⁅a, s⁆⁻¹ := (commutatorElement_inv a s).symm
    rw [hsa]
    exact inv_mem ⟨⟨⁅a, s⁆, hd⟩, hkey a ha s hs hd, rfl⟩
  have hodd : Nat.Coprime 2 (Nat.card (inSubgroup (pPrimeCore 2) Q)) := by
    rw [inSubgroup, card_map_of_injective Q.subtype_injective]
    exact CFSG.pPrimeCore_coprime_card (p := 2) (G := Q)
  have h := card_dvd_of_le hle
  exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun h2 =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp hodd (h2.trans h))

end CFSG.RankThree.GroupTheory.SteinbergBM
