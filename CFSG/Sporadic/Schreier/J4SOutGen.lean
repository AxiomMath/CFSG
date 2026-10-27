module

public import CFSG.GroupTheory.FrattiniQuotient
public import CFSG.LocalAnalysis.ComponentInitial.SelfCentralizingCoreAutomorphisms
public import CFSG.Sporadic.FischerOddCore.AlmostSimple

public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.LocalAnalysis.ComponentInitial

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Metacyclic

variable {G : Type*} [Group G]

theorem mem_closure_metacyclic {u w : G} {n r : ℕ} (hn : 0 < n) (hu : u ^ n = 1) (hw : w ^ 2 = 1)
    (hwu : w * u * w⁻¹ = u ^ r) {g : G} (hg : g ∈ Subgroup.closure ({u, w} : Set G)) :
    ∃ i j : ℕ, i < n ∧ j < 2 ∧ g = u ^ i * w ^ j := by
  let P : G → Prop := fun g => ∃ i j : ℕ, j < 2 ∧ g = u ^ i * w ^ j
  have hc : ∀ i : ℕ, w * u ^ i = u ^ (r * i) * w := fun i => by
    rw [pow_mul, ← hwu, conj_pow, inv_mul_cancel_right]
  have huP : ∀ g, P g → P (u * g) := by
    rintro g ⟨i, j, hj, rfl⟩
    exact ⟨i + 1, j, hj, by rw [pow_succ', mul_assoc]⟩
  have hwP : ∀ g, P g → P (w * g) := by
    rintro g ⟨i, j, hj, rfl⟩
    interval_cases j
    · exact ⟨r * i, 1, by norm_num, by rw [← mul_assoc, hc, pow_zero, mul_one, pow_one]⟩
    · refine ⟨r * i, 0, by norm_num, ?_⟩
      rw [← mul_assoc, hc, pow_one, mul_assoc, ← sq, hw, pow_zero]
  have hpowP : ∀ (s : G), (∀ g, P g → P (s * g)) → ∀ k g, P g → P (s ^ k * g) := by
    intro s hs k
    induction k with
    | zero => intro g hg; simpa using hg
    | succ k ih => intro g hg; rw [pow_succ', mul_assoc]; exact hs _ (ih g hg)
  have huinv : u⁻¹ = u ^ (n - 1) := by
    rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, Nat.sub_add_cancel hn, hu]
  have hwinv : w⁻¹ = w := by
    rw [inv_eq_iff_mul_eq_one, ← sq, hw]
  have hP : P g := by
    induction hg using Subgroup.closure_induction_left with
    | one => exact ⟨0, 0, by norm_num, by simp⟩
    | mul_left s hs g _ ih =>
      rcases hs with rfl | rfl
      · exact huP _ ih
      · exact hwP _ ih
    | inv_mul_cancel s hs g _ ih =>
      rcases hs with rfl | rfl
      · rw [huinv]
        exact hpowP _ huP _ _ ih
      · rw [hwinv]
        exact hwP _ ih
  obtain ⟨i, j, hj, rfl⟩ := hP
  exact ⟨i % n, j, Nat.mod_lt _ hn, hj, by rw [← pow_eq_pow_mod _ hu]⟩

theorem card_closure_metacyclic {u w : G} {n r : ℕ} (hn : 0 < n) (hu : u ^ n = 1)
    (hw : w ^ 2 = 1) (hwu : w * u * w⁻¹ = u ^ r)
    (hinj : Function.Injective fun t : Fin n × Fin 2 => u ^ (t.1 : ℕ) * w ^ (t.2 : ℕ)) :
    Nat.card (Subgroup.closure ({u, w} : Set G)) = n * 2 := by
  set R := Subgroup.closure ({u, w} : Set G)
  have huR : u ∈ R := Subgroup.subset_closure (Set.mem_insert _ _)
  have hwR : w ∈ R := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  let F : Fin n × Fin 2 → R := fun t =>
    ⟨u ^ (t.1 : ℕ) * w ^ (t.2 : ℕ), R.mul_mem (R.pow_mem huR _) (R.pow_mem hwR _)⟩
  have hF : Function.Bijective F := by
    refine ⟨fun s t hst => hinj (congrArg Subtype.val hst), fun g => ?_⟩
    obtain ⟨i, j, hi, hj, hg⟩ := mem_closure_metacyclic hn hu hw hwu g.2
    exact ⟨(⟨i, hi⟩, ⟨j, hj⟩), Subtype.ext hg.symm⟩
  rw [← Nat.card_eq_of_bijective F hF, Nat.card_prod, Nat.card_fin, Nat.card_fin]

end Metacyclic

section AutBound

theorem card_GL_two_eleven : Nat.card (GL (Fin 2) (ZMod 11)) = 13200 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  rw [Matrix.card_GL_field, ZMod.card, Fin.prod_univ_two]
  norm_num

theorem card_mulAut_of_addEquiv {E : Type*} [Group E] (e : Additive E ≃+ (Fin 2 → ZMod 11)) :
    Nat.card (MulAut E) = 13200 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have e1 : MulAut E ≃ AddAut (Additive E) := MulEquiv.toAdditive
  have e2 : AddAut (Additive E) ≃ AddAut (Fin 2 → ZMod 11) :=
    { toFun := fun f => (e.symm.trans f).trans e
      invFun := fun g => (e.trans g).trans e.symm
      left_inv := fun f => by ext x; simp
      right_inv := fun g => by ext x; simp }
  have e3 : AddAut (Fin 2 → ZMod 11) ≃ ((Fin 2 → ZMod 11) ≃ₗ[ZMod 11] (Fin 2 → ZMod 11)) :=
    { toFun := fun f => f.toLinearEquiv fun c x => ZMod.map_smul f c x
      invFun := fun L => L.toAddEquiv
      left_inv := fun f => by ext x; rfl
      right_inv := fun L => by ext x; rfl }
  have e4 : ((Fin 2 → ZMod 11) ≃ₗ[ZMod 11] (Fin 2 → ZMod 11)) ≃ GL (Fin 2) (ZMod 11) :=
    (Matrix.GeneralLinearGroup.toLin.trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv _ _)).toEquiv.symm
  rw [Nat.card_congr (e1.trans (e2.trans (e3.trans e4))), card_GL_two_eleven]

theorem card_mulAut_frattini_quot {Q : Type*} [Group Q] [Finite Q]
    (hQ : IsExtraspecialPGroup 11 Q) (hcard : Nat.card Q = 11 ^ 3) :
    Nat.card (MulAut (Q ⧸ frattini Q)) = 13200 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨-, -, -, -, d, hd, ⟨e⟩⟩ := CFSG.GroupTheory.frattini_elementary_quotient hQ.1
  have hc : Nat.card (frattini Q) = 11 := by rw [hQ.2.2.1]; exact hQ.2.2.2
  have h121 : Nat.card (Q ⧸ frattini Q) = 11 ^ 2 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (frattini Q)
    rw [hc, hcard] at h
    norm_num at h ⊢
    omega
  have hd2 : d = 2 := Nat.pow_right_injective (by norm_num : 2 ≤ 11) (hd.symm.trans h121)
  subst hd2
  exact card_mulAut_of_addEquiv e

theorem factorization_two_13200 : (13200 : ℕ).factorization 2 = 4 := by
  rw [show (13200 : ℕ) = 2 ^ 4 * 825 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
    Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]

theorem factorization_two_card_mulAut {Q : Type*} [Group Q] [Finite Q]
    (hQ : IsExtraspecialPGroup 11 Q) (hcard : Nat.card Q = 11 ^ 3) :
    (Nat.card (MulAut Q)).factorization 2 ≤ 4 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have : Finite (MulAut Q) := Finite.of_injective _ (DFunLike.coe_injective (F := MulAut Q))
  set f := CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism (frattini Q)
  obtain ⟨-, hker⟩ := CFSG.GroupTheory.frattini_automorphism_kernel hQ.1
  obtain ⟨a, ha⟩ := hker.exists_card_eq
  have h1 : Nat.card (MulAut Q) = Nat.card f.ker * Nat.card f.range := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker, mul_comm,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  have h2 : Nat.card f.range ∣ 13200 := by
    rw [← card_mulAut_frattini_quot hQ hcard]
    exact Subgroup.card_subgroup_dvd_card _
  have h3 : (Nat.card f.range).factorization 2 ≤ 4 := by
    have := (Nat.factorization_le_iff_dvd Nat.card_pos.ne' (by norm_num)).2 h2 2
    rwa [factorization_two_13200] at this
  have h0 : (Finsupp.single 11 a) 2 = 0 := by
    rw [Finsupp.single_apply]
    simp
  rw [h1, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply, ha,
    Nat.Prime.factorization_pow (Fact.out : Nat.Prime 11), h0, zero_add]
  exact h3

end AutBound

section OuterOdd

variable {G : Type*} [Group G]

@[expose] def autStab (Q : Subgroup G) : Subgroup (MulAut G) where
  carrier := {α | ∀ g, α g ∈ Q ↔ g ∈ Q}
  one_mem' g := by rw [MulAut.one_apply]
  mul_mem' {α β} hα hβ g := by rw [MulAut.mul_apply, hα, hβ]
  inv_mem' {α} hα g := by
    have h := hα (α⁻¹ g)
    rw [MulAut.apply_inv_self] at h
    exact h.symm

@[expose] def autRes (Q : Subgroup G) : autStab Q →* MulAut Q where
  toFun α :=
    { toFun := fun q => ⟨α.1 q, (α.2 q).2 q.2⟩
      invFun := fun q => ⟨α.1⁻¹ q, ((autStab Q).inv_mem α.2 q).2 q.2⟩
      left_inv := fun q => Subtype.ext (MulAut.inv_apply_self G α.1 q)
      right_inv := fun q => Subtype.ext (MulAut.apply_inv_self G α.1 q)
      map_mul' := fun p q => Subtype.ext (map_mul α.1 (p : G) q) }
  map_one' := MulEquiv.ext fun _ => Subtype.ext rfl
  map_mul' _ _ := MulEquiv.ext fun _ => Subtype.ext rfl

theorem factorization_two_le_of_dvd {m n : ℕ} (hn : n ≠ 0) (h : m ∣ n) :
    m.factorization 2 ≤ n.factorization 2 :=
  (Nat.factorization_le_iff_dvd (ne_zero_of_dvd_ne_zero hn h) hn).2 h 2

theorem odd_of_factorization_two {n : ℕ} (hn : n ≠ 0) (h : n.factorization 2 = 0) : Odd n := by
  rw [Nat.odd_iff]
  rcases (Nat.factorization_eq_zero_iff n 2).1 h with h | h | h
  · exact absurd Nat.prime_two h
  · omega
  · exact absurd h hn

theorem odd_card_outer_of_sylow [Finite G] (hZ : Subgroup.center G = ⊥) {p : ℕ} [Fact p.Prime]
    (Q : Sylow p G) (hC : Odd (Nat.card (pointwiseFixingAut (Q : Subgroup G))))
    (hAut : (Nat.card (MulAut (Q : Subgroup G))).factorization 2 ≤
      (Nat.card (Subgroup.normalizer ((Q : Subgroup G) : Set G))).factorization 2) :
    Odd (Nat.card (Outer G)) := by
  have : Finite (MulAut G) := Finite.of_injective _ (DFunLike.coe_injective (F := MulAut G))
  have : Finite (MulAut (Q : Subgroup G)) :=
    Finite.of_injective _ (DFunLike.coe_injective (F := MulAut (Q : Subgroup G)))
  set D := autStab (Q : Subgroup G)
  set ρ := autRes (Q : Subgroup G)
  have hker : Odd (Nat.card ρ.ker) := by
    have hle : ρ.ker.map D.subtype ≤ pointwiseFixingAut (Q : Subgroup G) := by
      rintro _ ⟨α, hα, rfl⟩ q hq
      have e := congrArg (fun f : MulAut (Q : Subgroup G) => ((f ⟨q, hq⟩ : Q) : G)) hα
      exact e
    have h := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective D.subtype_injective] at h
    exact Odd.of_dvd_nat hC h
  have hD : (Nat.card D).factorization 2 ≤
      (Nat.card (MulAut (Q : Subgroup G))).factorization 2 := by
    have h1 : Nat.card D = Nat.card ρ.ker * Nat.card ρ.range := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker, mul_comm,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv]
    have h2 : (Nat.card ρ.ker).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (by have := Nat.odd_iff.1 hker; omega)
    rw [h1, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply, h2,
      zero_add]
    exact factorization_two_le_of_dvd Nat.card_pos.ne' (Subgroup.card_subgroup_dvd_card _)
  set φ : D →* Outer G :=
    (QuotientGroup.mk' (ComponentClassification.OuterAutomorphisms.inner G)).comp D.subtype
  have hsurj : Function.Surjective φ := by
    intro x
    obtain ⟨α, rfl⟩ :=
      QuotientGroup.mk'_surjective (ComponentClassification.OuterAutomorphisms.inner G) x
    have hcard : Nat.card ((Q : Subgroup G).map α.toMonoidHom) =
        p ^ (Nat.card G).factorization p := by
      rw [Subgroup.card_map_of_injective α.injective, Sylow.card_eq_multiplicity]
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q (Sylow.ofCard _ hcard)
    have hPg : (Q : Subgroup G).map α.toMonoidHom =
        (Q : Subgroup G).map (MulAut.conj g).toMonoidHom := by
      have h1 := congrArg (fun P : Sylow p G => (P : Subgroup G)) hg
      simp only [Sylow.coe_ofCard] at h1
      rw [← h1, Sylow.coe_subgroup_smul]
      rfl
    have key : ∀ y, y ∈ (Q : Subgroup G).map (MulAut.conj g).toMonoidHom ↔
        g⁻¹ * y * g ∈ (Q : Subgroup G) := by
      intro y
      constructor
      · rintro ⟨q, hq, rfl⟩
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rwa [show g⁻¹ * (g * q * g⁻¹) * g = q by group]
      · intro h
        refine ⟨g⁻¹ * y * g, h, ?_⟩
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
    have key2 : ∀ x, α x ∈ (Q : Subgroup G).map α.toMonoidHom ↔ x ∈ (Q : Subgroup G) := by
      intro x
      constructor
      · rintro ⟨q, hq, e⟩
        rwa [← α.injective e]
      · intro h
        exact ⟨x, h, rfl⟩
    have hβ : (MulAut.conj g)⁻¹ * α ∈ D := by
      intro x
      rw [MulAut.mul_apply, MulAut.conj_inv_apply, ← key, ← hPg, key2]
    refine ⟨⟨(MulAut.conj g)⁻¹ * α, hβ⟩, ?_⟩
    have hg' : MulAut.conj g ∈ ComponentClassification.OuterAutomorphisms.inner G :=
      MonoidHom.mem_range.2 ⟨g, rfl⟩
    have hg1 : QuotientGroup.mk' (ComponentClassification.OuterAutomorphisms.inner G)
        (MulAut.conj g) = 1 := (QuotientGroup.eq_one_iff _).2 hg'
    show QuotientGroup.mk' (ComponentClassification.OuterAutomorphisms.inner G)
      ((MulAut.conj g)⁻¹ * α) =
        QuotientGroup.mk' (ComponentClassification.OuterAutomorphisms.inner G) α
    rw [map_mul, map_inv, hg1, inv_one, one_mul]
  have hDφ : Nat.card D = Nat.card (Outer G) * Nat.card φ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hsurj).toEquiv]
  have hN : (Nat.card (Subgroup.normalizer ((Q : Subgroup G) : Set G))).factorization 2 ≤
      (Nat.card φ.ker).factorization 2 := by
    have hmem : ∀ n : Subgroup.normalizer ((Q : Subgroup G) : Set G),
        MulAut.conj (n : G) ∈ D := by
      intro n x
      rw [MulAut.conj_apply]
      exact (Subgroup.mem_normalizer_iff.1 n.2 x).symm
    have hmemK : ∀ n : Subgroup.normalizer ((Q : Subgroup G) : Set G),
        (⟨MulAut.conj (n : G), hmem n⟩ : D) ∈ φ.ker := by
      intro n
      rw [MonoidHom.mem_ker]
      have hn' : MulAut.conj (n : G) ∈ ComponentClassification.OuterAutomorphisms.inner G :=
        MonoidHom.mem_range.2 ⟨n, rfl⟩
      exact (QuotientGroup.eq_one_iff _).2 hn'
    let ψ : Subgroup.normalizer ((Q : Subgroup G) : Set G) →* φ.ker :=
      { toFun := fun n => ⟨⟨MulAut.conj (n : G), hmem n⟩, hmemK n⟩
        map_one' := Subtype.ext (Subtype.ext (map_one MulAut.conj))
        map_mul' := fun m n => Subtype.ext (Subtype.ext (map_mul MulAut.conj (m : G) n)) }
    have hψ : Function.Injective ψ := by
      refine (injective_iff_map_eq_one ψ).2 fun n hn => ?_
      have h1 : MulAut.conj (n : G) = 1 := congrArg (fun k : φ.ker => ((k : D) : MulAut G)) hn
      have h2 : (n : G) ∈ Subgroup.center G := by
        rw [Subgroup.mem_center_iff]
        intro y
        have h3 := congrArg (fun f : MulAut G => f y) h1
        simp only [MulAut.conj_apply, MulAut.one_apply] at h3
        calc y * (n : G) = (n : G) * y * (n : G)⁻¹ * n := by rw [h3]
          _ = n * y := by group
      rw [hZ, Subgroup.mem_bot] at h2
      exact Subtype.ext h2
    exact factorization_two_le_of_dvd Nat.card_pos.ne' (Subgroup.card_dvd_of_injective ψ hψ)
  have hfin : Nat.card (Outer G) ≠ 0 := Nat.card_pos.ne'
  refine odd_of_factorization_two hfin ?_
  have h1 : (Nat.card D).factorization 2 =
      (Nat.card (Outer G) * Nat.card φ.ker).factorization 2 := by rw [hDφ]
  rw [Nat.factorization_mul hfin Nat.card_pos.ne', Finsupp.add_apply] at h1
  omega

end OuterOdd

theorem mem_of_sq_eq_one_of_odd_outer {X : Type*} [Group X] {S : Subgroup X} [S.Normal]
    {Q : Type*} [Group Q] (θ : S ≃* Q) (hC : Subgroup.centralizer (S : Set X) = ⊥)
    (hout : Odd (Nat.card (Outer Q))) {t : X} (ht : t ^ 2 = 1) : t ∈ S := by
  set c := FischerOddCore.conjTransport θ t
  have h1 : QuotientGroup.mk' (ComponentClassification.OuterAutomorphisms.inner Q) c ^ 2 = 1 := by
    rw [← map_pow, ← map_pow, ht, map_one, map_one]
  have h2 : QuotientGroup.mk' (ComponentClassification.OuterAutomorphisms.inner Q) c = 1 := by
    have hdvd := orderOf_dvd_of_pow_eq_one h1
    have hodd : Odd (orderOf
        (QuotientGroup.mk' (ComponentClassification.OuterAutomorphisms.inner Q) c)) :=
      Odd.of_dvd_nat hout (orderOf_dvd_natCard _)
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact orderOf_eq_one_iff.1 h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  obtain ⟨g, hg⟩ := (QuotientGroup.eq_one_iff c).1 h2
  have e : FischerOddCore.conjTransport θ ((θ.symm g : S) : X) = c := by
    rw [FischerOddCore.conjTransport_of_mem, MulEquiv.apply_symm_apply, hg]
  rw [← FischerOddCore.conjTransport_injective θ hC e]
  exact (θ.symm g).2

end CFSG.Sporadic.J4Schreier
