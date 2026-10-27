module

public import CFSG.RankThree.SteinbergR3ECALinearTwoFixedTheta
public import CFSG.RankThree.SteinbergR3ELinearTwoOddFieldFixed
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearTwoEven
public import CFSG.RankThree.SteinbergR3ELinearTwoPrimeCentralizer

public section

namespace CFSG.RankThree.LinearTwoPlaneCore

open scoped commutatorElement

section Cyclic

theorem odd_geom_sum {t : ℤ} (ht : Odd t) {j : ℕ} (hj : Odd j) :
    Odd (∑ i ∈ Finset.range j, t ^ i) := by
  obtain ⟨k, rfl⟩ := hj
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, add_assoc]
    refine ih.add_even ?_
    rw [pow_succ t (2 * k + 1), ← mul_one_add]
    exact (odd_one.add_odd ht).mul_left _

theorem two_pow_dvd_sub_one {e j : ℕ} (hj : Odd j) {t : ℤ} (h : (2 : ℤ) ^ e ∣ t ^ j - 1) :
    (2 : ℤ) ^ e ∣ t - 1 := by
  rcases Int.even_or_odd t with ht | ht
  · rcases e with _ | e
    · simp
    · exfalso
      have hj0 : j ≠ 0 := by
        rintro rfl
        exact (Nat.not_odd_zero hj)
      have h2 : (2 : ℤ) ∣ t ^ j - 1 := (dvd_pow_self 2 (Nat.succ_ne_zero e)).trans h
      have hodd : Odd (t ^ j - 1) := (ht.pow_of_ne_zero hj0).sub_odd odd_one
      exact (Int.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  · have hgeom : t ^ j - 1 = (t - 1) * ∑ i ∈ Finset.range j, t ^ i := by
      rw [mul_comm, geom_sum_mul]
    rw [hgeom] at h
    have hcop : IsCoprime ((2 : ℤ) ^ e) (∑ i ∈ Finset.range j, t ^ i) :=
      (Int.isCoprime_two_left.mpr (odd_geom_sum ht hj)).pow_left
    exact hcop.dvd_of_dvd_mul_right h

theorem fixes_pow_odd_part {Q : Type*} [CommGroup Q] [Finite Q] [IsCyclic Q] {σ : Q →* Q}
    {j : ℕ} (hj : Odd j) (hσ : ∀ q, σ^[j] q = q) {e m : ℕ} (hQ : Nat.card Q = 2 ^ e * m)
    (q : Q) : σ (q ^ m) = q ^ m := by
  obtain ⟨t, ht⟩ := σ.map_cyclic
  have hit : ∀ (i : ℕ) (q : Q), σ^[i] q = q ^ (t ^ i) := by
    intro i
    induction i with
    | zero => intro q; simp
    | succ i ih =>
      intro q
      rw [Function.iterate_succ_apply', ih, map_zpow, ht, ← zpow_mul, pow_succ, mul_comm]
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Q)
  have hog : orderOf g = Nat.card Q := orderOf_eq_card_of_forall_mem_zpowers hg
  have h1 : g ^ (t ^ j - 1) = 1 := by
    have h := hσ g
    rw [hit] at h
    rw [zpow_sub, zpow_one, h, mul_inv_cancel]
  have h2 : ((Nat.card Q : ℕ) : ℤ) ∣ t ^ j - 1 := by
    rw [← hog]
    exact orderOf_dvd_iff_zpow_eq_one.mpr h1
  have h3 : (2 : ℤ) ^ e ∣ t - 1 := by
    refine two_pow_dvd_sub_one hj (Dvd.dvd.trans ?_ h2)
    rw [hQ]
    push_cast
    exact Dvd.intro _ rfl
  have h4 : q ^ ((m : ℤ) * (t - 1)) = 1 := by
    obtain ⟨c, hc⟩ := h3
    rw [hc, show (m : ℤ) * (2 ^ e * c) = ((2 ^ e * m : ℕ) : ℤ) * c by push_cast; ring, zpow_mul,
      zpow_natCast, ← hQ, pow_card_eq_one', one_zpow]
  rw [ht, ← zpow_natCast, ← zpow_mul, show (m : ℤ) * t = m + m * (t - 1) by ring, zpow_add, h4,
    mul_one]

theorem odd_orderOf_of_mem_cyclic {G : Type*} [Group G] {Q : Subgroup G} [Finite Q]
    (hQ : IsCyclic Q) {u : G} (hu : u ∈ Subgroup.normalizer (Q : Set G))
    (huo : Odd (orderOf u)) {s : G} (hs : s⁻¹ * (u⁻¹ * s * u) ∈ Q) :
    Odd (orderOf (s⁻¹ * (u⁻¹ * s * u))) := by
  let _ : CommGroup Q := IsCyclic.commGroup
  set j := orderOf u with hjdef
  have hconj : ∀ q ∈ Q, u⁻¹ * q * u ∈ Q := fun q hq => by
    have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hu) q).mp hq
    rwa [inv_inv] at h
  let α : Q →* Q :=
    { toFun := fun q => ⟨u⁻¹ * q * u, hconj q q.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun q q' => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hαit : ∀ (i : ℕ) (q : Q), ((α^[i] q : Q) : G) = (u ^ i)⁻¹ * q * u ^ i := by
    intro i
    induction i with
    | zero => intro q; simp
    | succ i ih =>
      intro q
      rw [Function.iterate_succ_apply']
      change u⁻¹ * ((α^[i] q : Q) : G) * u = (u ^ (i + 1))⁻¹ * q * u ^ (i + 1)
      rw [ih]
      group
  have hαj : ∀ q, α^[j] q = q := fun q => Subtype.ext (by
    rw [hαit, hjdef, pow_orderOf_eq_one, inv_one, one_mul, mul_one])
  set c : Q := ⟨_, hs⟩ with hcdef
  obtain ⟨e, m, hm, hQcard⟩ := Nat.exists_eq_two_pow_mul_odd (Nat.card_pos (α := Q)).ne'
  have hfix := fixes_pow_odd_part huo hαj hQcard
  have hsc : u⁻¹ * s * u = s * (c : G) := by
    rw [hcdef]
    group
  have key : ∀ i : ℕ, ∃ P : Q, (u ^ i)⁻¹ * s * u ^ i = s * (P : G) ∧ P ^ m = (c ^ m) ^ i := by
    intro i
    induction i with
    | zero => exact ⟨1, by simp, by simp⟩
    | succ i ih =>
      obtain ⟨P, hP1, hP2⟩ := ih
      refine ⟨c * α P, ?_, ?_⟩
      · calc (u ^ (i + 1))⁻¹ * s * u ^ (i + 1) = u⁻¹ * ((u ^ i)⁻¹ * s * u ^ i) * u := by group
          _ = u⁻¹ * (s * (P : G)) * u := by rw [hP1]
          _ = (u⁻¹ * s * u) * (u⁻¹ * (P : G) * u) := by group
          _ = s * ((c * α P : Q) : G) := by
            rw [hsc, Subgroup.coe_mul, mul_assoc]
            rfl
      · rw [mul_pow, ← map_pow, hP2, map_pow, hfix, pow_succ, mul_comm]
  obtain ⟨P, hP1, hP2⟩ := key j
  rw [hjdef, pow_orderOf_eq_one, inv_one, one_mul, mul_one, left_eq_mul] at hP1
  have hP : P = 1 := Subtype.ext hP1
  have h1 : c ^ (m * j) = 1 := by rw [pow_mul, ← hP2, hP, one_pow]
  have h2 : Odd (orderOf c) := Odd.of_dvd_nat (hm.mul huo) (orderOf_dvd_of_pow_eq_one h1)
  rwa [← Subgroup.orderOf_coe] at h2

end Cyclic

section Coordinates

open CFSG.ComponentClassification.CatalogueSchreierLinearTwo

variable {K : Type} [Field K] [Finite K]

theorem sq_mem_coordinateG {d : Equiv.Perm (Omega K)} (hd : d ∈ coordinateD K) :
    d ^ 2 ∈ coordinateG K := by
  rw [← (CFSG.LinearGroups.linear_two_projective_identification K).2.2.2.2.1] at hd
  obtain ⟨A, rfl⟩ := hd
  set c : Kˣ := (Matrix.GeneralLinearGroup.det A)⁻¹
  have hX : Matrix.GeneralLinearGroup.det
      (A ^ 2 * Matrix.GeneralLinearGroup.scalar (Fin 2) c) = 1 := by
    apply Units.ext
    simp [c, pow_two]
  have hact : coordinateGLAction K (A ^ 2 * Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
      coordinateGLAction K (A ^ 2) := by
    rw [map_mul, (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.coordinateGLAction_eq_one_iff
      _).mpr ⟨c, rfl⟩, mul_one]
  rw [← map_pow, ← hact]
  exact CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.coordinateGLAction_mem_G hX

theorem mem_coordinateG_of_odd {d : Equiv.Perm (Omega K)} (hd : d ∈ coordinateD K)
    (hodd : Odd (orderOf d)) : d ∈ coordinateG K := by
  obtain ⟨n, hn⟩ := hodd
  have h1 : d = (d ^ 2) ^ (n + 1) := by
    rw [← pow_mul, show 2 * (n + 1) = orderOf d + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  rw [h1]
  exact Subgroup.pow_mem _ (sq_mem_coordinateG hd) _

theorem commutatorElement_mem_coordinateD {x y : Equiv.Perm (Omega K)}
    (hx : x ∈ coordinateE K) (hy : y ∈ coordinateE K) : ⁅x, y⁆ ∈ coordinateD K := by
  obtain ⟨-, -, -, hDn, -, hcyc, -⟩ := CFSG.LinearGroups.linear_two_semilinear_quotients K
  let _ : CommGroup (coordinateE K ⧸ (coordinateD K).subgroupOf (coordinateE K)) :=
    IsCyclic.commGroup
  set x' : coordinateE K := ⟨x, hx⟩
  set y' : coordinateE K := ⟨y, hy⟩
  have h2 : QuotientGroup.mk' ((coordinateD K).subgroupOf (coordinateE K)) ⁅x', y'⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h2
  exact h2

theorem conj_mem_coordinateG {g y : Equiv.Perm (Omega K)} (hg : g ∈ coordinateE K)
    (hy : y ∈ coordinateG K) : g * y * g⁻¹ ∈ coordinateG K := by
  have h := (coordinateG_normal_in_E K).conj_mem ⟨y, coordinateD_le_E K (coordinateG_le_D K hy)⟩
    (Subgroup.mem_subgroupOf.mpr hy) ⟨g, hg⟩
  rw [Subgroup.mem_subgroupOf] at h
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h

theorem conj_mem_coordinateD {g y : Equiv.Perm (Omega K)} (hg : g ∈ coordinateE K)
    (hy : y ∈ coordinateD K) : g * y * g⁻¹ ∈ coordinateD K := by
  have h := (coordinateD_normal_in_E K).conj_mem ⟨y, coordinateD_le_E K hy⟩
    (Subgroup.mem_subgroupOf.mpr hy) ⟨g, hg⟩
  rw [Subgroup.mem_subgroupOf] at h
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h

end Coordinates

section Outer

open CFSG.ComponentClassification.CatalogueSchreierLinearTwo CFSG.RankThree.LinearTwo
open CFSG.ComponentClassification.CatalogueBLinearTwoDescent (fixedSubfield)

variable {K : Type} [Field K] [Finite K]

theorem outer_centralizer_simple {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hp3 : 3 < p) {x y : Equiv.Perm (Omega K)}
    (hxE : x ∈ coordinateE K) (hxD : x ∉ coordinateD K) (hxo : orderOf x = p)
    (hyD : y ∈ coordinateD K) (hyo : orderOf y = p) (hxy : y * x = x * y) :
    IsSimpleGroup (coordinateG K ⊓ Subgroup.centralizer {x} : Subgroup (Equiv.Perm (Omega K))) ∧
      y ∈ coordinateG K ⊓ Subgroup.centralizer {x} ∧
      ∀ r ∈ coordinateE K, (∀ g ∈ coordinateG K ⊓ Subgroup.centralizer {x}, r * g = g * r) →
        r ∈ Subgroup.zpowers x := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hyG : y ∈ coordinateG K :=
    mem_coordinateG_of_odd hyD (hyo ▸ hp.odd_of_ne_two (by omega))
  have hyH : y ∈ coordinateG K ⊓ Subgroup.centralizer {x} :=
    ⟨hyG, Subgroup.mem_centralizer_singleton_iff.mpr hxy⟩
  obtain ⟨-, σ, hσ, ⟨h, hhD, rfl⟩, -⟩ :=
    linear_two_prime_semilinear_field_descent hℓ hp hf K hK hxE hxD hxo
  obtain ⟨-, hinj, -, hGcent, hCcent, -⟩ := linear_two_odd_field_fixed_group_and_centralizer K σ
    (hp.odd_of_ne_two (by omega)) hσ
  set k := fixedSubfield K σ
  have e : (coordinateG K ⊓ Subgroup.centralizer {h * fieldExtension K σ * h⁻¹} :
      Subgroup (Equiv.Perm (Omega K))) ≃* coordinateG k :=
    (MulEquiv.subgroupCongr (coordinateG_inf_centralizer_conj hhD _)).trans
      (((Subgroup.equivMapOfInjective _ _ (MulAut.conj h).injective).symm.trans
        (MulEquiv.subgroupCongr hGcent)).trans
      ((Subgroup.equivMapOfInjective _ _
        (fun x y hxy => hinj (Subtype.ext hxy))).symm.trans
        (Subgroup.subgroupOfEquivOfLe (coordinateG_le_D k))))
  have hk4 : 4 ≤ Nat.card k := by
    by_contra hk3
    push Not at hk3
    have hpH : p ∣ Nat.card (coordinateG K ⊓ Subgroup.centralizer
        {h * fieldExtension K σ * h⁻¹} : Subgroup (Equiv.Perm (Omega K))) := by
      have h0 := orderOf_dvd_natCard (⟨y, hyH⟩ : (coordinateG K ⊓ Subgroup.centralizer
        {h * fieldExtension K σ * h⁻¹} : Subgroup (Equiv.Perm (Omega K))))
      rwa [Subgroup.orderOf_mk, hyo] at h0
    rw [Nat.card_congr e.toEquiv] at hpH
    have h1 : Nat.card (coordinateG k) ∣ Nat.card (Equiv.Perm (Omega k)) :=
      Subgroup.card_subgroup_dvd_card _
    have h2 : Nat.card (Equiv.Perm (Omega k)) ∣ 2 ^ 3 * 3 := by
      rw [Nat.card_perm, Finite.card_option, show (2 : ℕ) ^ 3 * 3 = Nat.factorial 4 by decide]
      exact Nat.factorial_dvd_factorial (by omega)
    rcases (Nat.Prime.dvd_mul hp).mp ((hpH.trans h1).trans h2) with h3 | h3
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h3)
      omega
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3
      omega
  have hsimple : IsSimpleGroup (coordinateG K ⊓ Subgroup.centralizer
      {h * fieldExtension K σ * h⁻¹} : Subgroup (Equiv.Perm (Omega K))) := by
    have : Fintype k := Fintype.ofFinite k
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset k)) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; omega)
    have := (CFSG.LinearGroups.linear_projective_simple (K := k) (n := 2) le_rfl
      (Or.inr ⟨s, hs⟩)).2.1
    exact (e.trans (pslEquivCoordinateG k).symm).isSimpleGroup
  refine ⟨hsimple, hyH, fun r hrE hr => ?_⟩
  have hhE : h ∈ coordinateE K := coordinateD_le_E K hhD
  have hr'E : h⁻¹ * r * h ∈ coordinateE K :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hhE) hrE) hhE
  have hr'C : h⁻¹ * r * h ∈ Subgroup.centralizer
      ((((coordinateG k).subgroupOf (coordinateD k)).map
        ((coordinateD K).subtype.comp
          (CFSG.ComponentClassification.UnbalancedGS.SubfieldCentralizer.subfieldD k)) :
        Subgroup (Equiv.Perm (Omega K))) : Set (Equiv.Perm (Omega K))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [SetLike.mem_coe, ← hGcent] at hg
    have hg' : h * g * h⁻¹ ∈
        coordinateG K ⊓ Subgroup.centralizer {h * fieldExtension K σ * h⁻¹} := by
      rw [coordinateG_inf_centralizer_conj hhD]
      exact ⟨g, hg, rfl⟩
    have h1 := hr _ hg'
    calc g * (h⁻¹ * r * h) = h⁻¹ * ((h * g * h⁻¹) * r) * h := by group
      _ = h⁻¹ * (r * (h * g * h⁻¹)) * h := by rw [h1]
      _ = h⁻¹ * r * h * g := by group
  have hr' : h⁻¹ * r * h ∈ Subgroup.zpowers (fieldExtension K σ) := by
    rw [← hCcent]
    exact ⟨hr'C, hr'E⟩
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hr'
  refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
  rw [conj_zpow, hn]
  group

theorem outer_normal_coprime_eq_bot {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hp3 : 3 < p) {B : Subgroup (Equiv.Perm (Omega K))}
    (hGB : coordinateG K ≤ B) (hBE : B ≤ coordinateE K) {x y : Equiv.Perm (Omega K)}
    (hxB : x ∈ B) (hxD : x ∉ coordinateD K) (hxo : orderOf x = p)
    (hyD : y ∈ coordinateD K) (hyo : orderOf y = p) (hxy : y * x = x * y)
    (R : Subgroup (Equiv.Perm (Omega K))) (hR : R ≤ B ⊓ Subgroup.centralizer {x})
    (hRn : (R.subgroupOf (B ⊓ Subgroup.centralizer {x})).Normal)
    (hcop : Nat.Coprime (Nat.card R) p) : R = ⊥ := by
  classical
  obtain ⟨hsimple, hyH, hC⟩ :=
    outer_centralizer_simple hℓ hf hK hp hp3 (hBE hxB) hxD hxo hyD hyo hxy
  have := hsimple
  set H : Subgroup (Equiv.Perm (Omega K)) := coordinateG K ⊓ Subgroup.centralizer {x}
  set M : Subgroup (Equiv.Perm (Omega K)) := B ⊓ Subgroup.centralizer {x}
  have hHM : H ≤ M := inf_le_inf_right _ hGB
  have hRnorm : ∀ m ∈ M, ∀ r ∈ R, m * r * m⁻¹ ∈ R := by
    intro m hm r hr
    have h := hRn.conj_mem ⟨r, hR hr⟩ (Subgroup.mem_subgroupOf.mpr hr) ⟨m, hm⟩
    rw [Subgroup.mem_subgroupOf] at h
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h
  have hHnorm : ∀ m ∈ M, ∀ g ∈ H, m * g * m⁻¹ ∈ H := by
    intro m hm g hg
    rw [Subgroup.mem_inf] at hm hg
    refine Subgroup.mem_inf.mpr ⟨conj_mem_coordinateG (hBE hm.1) hg.1, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : Commute m x := Subgroup.mem_centralizer_singleton_iff.mp hm.2
    have h2 : Commute g x := Subgroup.mem_centralizer_singleton_iff.mp hg.2
    exact (h1.mul_left h2).mul_left h1.inv_left
  have hRH : ∀ g ∈ R, g ∈ H → g = 1 := by
    have hn : (R.subgroupOf H).Normal := ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hRnorm g (hHM g.2) n hn⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (R.subgroupOf H) with h | h
    · intro g hgR hgH
      have h1 : (⟨g, hgH⟩ : H) ∈ R.subgroupOf H := Subgroup.mem_subgroupOf.mpr hgR
      rw [h, Subgroup.mem_bot] at h1
      exact congrArg Subtype.val h1
    · exfalso
      have h1 : (⟨y, hyH⟩ : H) ∈ R.subgroupOf H := by rw [h]; exact Subgroup.mem_top _
      have hyR : y ∈ R := Subgroup.mem_subgroupOf.mp h1
      have h2 := Subgroup.orderOf_dvd_natCard R hyR
      rw [hyo] at h2
      have h3 := Nat.dvd_gcd h2 (dvd_refl p)
      rw [hcop.gcd_eq_one, Nat.dvd_one] at h3
      exact hp.one_lt.ne' h3
  have hcomm : ∀ r ∈ R, ∀ g ∈ H, r * g = g * r := by
    intro r hr g hg
    have h1 : r * g * r⁻¹ * g⁻¹ ∈ R := by
      rw [show r * g * r⁻¹ * g⁻¹ = r * (g * r⁻¹ * g⁻¹) by group]
      exact R.mul_mem hr (hRnorm g (hHM hg) r⁻¹ (R.inv_mem hr))
    have h2 : r * g * r⁻¹ * g⁻¹ ∈ H :=
      Subgroup.mul_mem _ (hHnorm r (hR hr) g hg) (H.inv_mem hg)
    have h3 := hRH _ h1 h2
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h3
    exact h3
  rw [eq_bot_iff]
  intro r hr
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hC r (hBE (hR hr).1) (hcomm r hr))
  have h1 : orderOf (x ^ n) ∣ p := orderOf_dvd_of_pow_eq_one (by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hxo, pow_orderOf_eq_one,
      one_zpow])
  have h2 := Subgroup.orderOf_dvd_natCard R hr
  have h3 := Nat.dvd_gcd h2 h1
  rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h3
  rw [Subgroup.mem_bot]
  exact h3

end Outer

section Transport

variable {G : Type*} [Group G] {B : Subgroup G}

theorem map_subtype_normal {x : B} {R : Subgroup B} (hR : R ≤ Subgroup.centralizer {x})
    (hRn : (R.subgroupOf (Subgroup.centralizer {x})).Normal) :
    R.map B.subtype ≤ B ⊓ Subgroup.centralizer {(x : G)} ∧
      ((R.map B.subtype).subgroupOf (B ⊓ Subgroup.centralizer {(x : G)})).Normal := by
  have hle : R.map B.subtype ≤ B ⊓ Subgroup.centralizer {(x : G)} := by
    rintro _ ⟨r, hr, rfl⟩
    refine ⟨r.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have h := Subgroup.mem_centralizer_singleton_iff.mp (hR hr)
    exact congrArg Subtype.val h
  refine ⟨hle, ⟨fun n hn g => ?_⟩⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨r, hr, hrn⟩ := hn
  have hg : (⟨(g : G), (Subgroup.mem_inf.mp g.2).1⟩ : B) ∈ Subgroup.centralizer {x} := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp g.2).2)
  have h := hRn.conj_mem ⟨r, hR hr⟩ (Subgroup.mem_subgroupOf.mpr hr) ⟨_, hg⟩
  rw [Subgroup.mem_subgroupOf] at h
  refine ⟨_, h, ?_⟩
  rw [Subgroup.subtype_apply] at hrn
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.subtype_apply]
  rw [hrn]

theorem thetaCore_props {p : ℕ} (hp : p.Prime) [Finite G] (x : B) :
    inSubgroup (CFSG.RankThree.LocalRank.aschbacherSolvableCore p)
        (Subgroup.centralizer ({x} : Set B)) ≤ Subgroup.centralizer {x} ∧
      ((inSubgroup (CFSG.RankThree.LocalRank.aschbacherSolvableCore p)
        (Subgroup.centralizer ({x} : Set B))).subgroupOf (Subgroup.centralizer {x})).Normal ∧
      Nat.Coprime (Nat.card (inSubgroup (CFSG.RankThree.LocalRank.aschbacherSolvableCore p)
        (Subgroup.centralizer ({x} : Set B)))) p := by
  obtain ⟨-, hchar, hpd, -⟩ :=
    CFSG.RankThree.LocalRank.solvable_prime_complement_core_characterization
      (H := Subgroup.centralizer ({x} : Set B)) hp
  refine ⟨Subgroup.map_subtype_le _, ?_, ?_⟩
  · rw [inSubgroup, ← Subgroup.comap_subtype,
      Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _)]
    infer_instance
  · rw [inSubgroup, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpd)

end Transport

section Main

open CFSG.ComponentClassification.CatalogueSchreierLinearTwo CFSG.RankThree.LinearTwo
open CFSG.RankThree.LocalRank (aschbacherSolvableCore thetaT)
open scoped Pointwise

theorem linear_two_plane_local_core_product_odd {ℓ f : ℕ} (hℓ : ℓ.Prime) {K : Type} [Field K]
    (hK : Nat.card K = ℓ ^ f) {B : Subgroup (Equiv.Perm (Omega K))} (hGB : coordinateG K ≤ B)
    (hBE : B ≤ coordinateE K) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {A : Subgroup B}
    (hA : CFSG.Assembly.IsElemAbelian p A) (hAcard : Nat.card A = p ^ 2) {a : B} (haA : a ∈ A)
    (ha1 : a ≠ 1) :
    ((⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({a} : Set B)), A⁆ ⊔
        thetaT p A : Subgroup B) : Set B) =
      ((⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({a} : Set B)), A⁆ :
        Subgroup B) : Set B) * (thetaT p A : Set B) ∧
    Odd (Nat.card (⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({a} : Set B)),
      A⁆ ⊔ thetaT p A : Subgroup B)) ∧
    (p = ℓ → ∀ x ∈ A, x ≠ 1 →
      inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({x} : Set B)) = ⊥) ∧
    (p ≠ ℓ → Nat.card (A ⊓ (coordinateD K).subgroupOf B : Subgroup B) = p ∧ p ∣ f ∧
      thetaT p A = ⊥) ∧
    ∀ x ∈ A, (x : Equiv.Perm (Omega K)) ∉ coordinateD K →
      ∀ R : Subgroup B, R ≤ Subgroup.centralizer ({x} : Set B) →
        (R.subgroupOf (Subgroup.centralizer ({x} : Set B))).Normal →
          Nat.Coprime (Nat.card R) p → R = ⊥ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hKfin : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ hℓ.ne_zero)
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · rw [h, pow_zero] at hK
      exact absurd hK (Finite.one_lt_card (α := K)).ne'
    · exact h
  have hchar : ringChar K = ℓ := by
    have := Fintype.ofFinite K
    have : CharP K ℓ := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
    exact ringChar.eq K ℓ
  have hp2 : p ≠ 2 := by omega
  set θC : B → Subgroup B := fun x =>
    inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({x} : Set B)) with hθC
  have hθ : ∀ x : B, θC x ≤ Subgroup.centralizer {x} ∧
      ((θC x).subgroupOf (Subgroup.centralizer {x})).Normal ∧
      Nat.Coprime (Nat.card (θC x)) p := fun x => thetaCore_props hp x
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hAord : ∀ x ∈ A, x ≠ 1 → orderOf (x : Equiv.Perm (Omega K)) = p := by
    intro x hx hx1
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime (hA.2 x hx) hx1
  have hy : ∃ y ∈ A, y ≠ 1 ∧ (y : Equiv.Perm (Omega K)) ∈ coordinateD K := by
    by_contra hne
    push Not at hne
    obtain ⟨-, -, -, -, -, hcyc, -⟩ := CFSG.LinearGroups.linear_two_semilinear_quotients K
    let φ : A →* (coordinateE K ⧸ (coordinateD K).subgroupOf (coordinateE K)) :=
      (QuotientGroup.mk' _).comp
        ((Subgroup.inclusion hBE).comp A.subtype)
    have hφ : Function.Injective φ := by
      rw [injective_iff_map_eq_one]
      intro z hz
      rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
        Subgroup.mem_subgroupOf] at hz
      by_contra hz1
      exact hne z z.2 (fun h => hz1 (Subtype.ext h)) hz
    have : IsCyclic A := isCyclic_of_injective φ hφ
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := A)
    have h1 : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one (Subtype.ext (hA.2 g g.2))
    rw [hg, hAcard] at h1
    have h2 := Nat.le_of_dvd hp.pos h1
    have h3 : p < p ^ 2 := by nlinarith [hp.two_le]
    omega
  obtain ⟨y, hyA, hy1, hyD⟩ := hy
  have hyo := hAord y hyA hy1
  have hiii : ∀ x ∈ A, (x : Equiv.Perm (Omega K)) ∉ coordinateD K →
      ∀ R : Subgroup B, R ≤ Subgroup.centralizer ({x} : Set B) →
        (R.subgroupOf (Subgroup.centralizer ({x} : Set B))).Normal →
          Nat.Coprime (Nat.card R) p → R = ⊥ := by
    intro x hxA hxD R hR hRn hcop
    have hx1 : x ≠ 1 := by
      rintro rfl
      exact hxD (Subgroup.one_mem _)
    obtain ⟨hle, hn⟩ := map_subtype_normal hR hRn
    have h := outer_normal_coprime_eq_bot hℓ hf hK hp hp3 hGB hBE x.2 hxD (hAord x hxA hx1) hyD
      hyo (congrArg Subtype.val (hAcomm y hyA x hxA)) (R.map B.subtype) hle hn
      (by rwa [Subgroup.card_map_of_injective B.subtype_injective])
    exact (Subgroup.map_eq_bot_iff_of_injective R B.subtype_injective).mp h
  have hθouter : ∀ x ∈ A, (x : Equiv.Perm (Omega K)) ∉ coordinateD K → θC x = ⊥ :=
    fun x hxA hxD => hiii x hxA hxD _ (hθ x).1 (hθ x).2.1 (hθ x).2.2
  have hIle : ∀ x ∈ A, x ≠ 1 → thetaT p A ≤ θC x := fun x hxA hx1 =>
    (iInf_le _ x).trans ((iInf_le _ hxA).trans (iInf_le _ hx1))
  have hi : p = ℓ → ∀ x ∈ A, x ≠ 1 → θC x = ⊥ := by
    intro hpℓ x hxA hx1
    by_cases hxD : (x : Equiv.Perm (Omega K)) ∈ coordinateD K
    · obtain ⟨-, hpgrp⟩ := linear_two_inner_prime_centralizer_alternatives K hp hp3 hxD
        (hAord x hxA hx1)
      obtain ⟨-, -, -, -, -, -, -, -, hcore⟩ := hpgrp (by rw [hchar, hpℓ])
      obtain ⟨hle, hn⟩ := map_subtype_normal (hθ x).1 (hθ x).2.1
      have h := hcore B hGB hBE x.2 ((θC x).map B.subtype) hle hn
        (by rw [Subgroup.card_map_of_injective B.subtype_injective]; exact (hθ x).2.2)
      exact (Subgroup.map_eq_bot_iff_of_injective _ B.subtype_injective).mp h
    · exact hθouter x hxA hxD
  have hii : p ≠ ℓ → Nat.card (A ⊓ (coordinateD K).subgroupOf B : Subgroup B) = p ∧ p ∣ f ∧
      thetaT p A = ⊥ := by
    intro hpℓ
    have hpchar : p ≠ ringChar K := by rw [hchar]; exact hpℓ
    have hcyc := (linear_two_inner_prime_centralizer_alternatives K hp hp3 hyD hyo).1 hpchar
    set A₀ : Subgroup B := A ⊓ (coordinateD K).subgroupOf B with hA₀
    have hA₀cyc : IsCyclic A₀ := by
      let φ : A₀ →* (coordinateD K ⊓ Subgroup.centralizer {(y : Equiv.Perm (Omega K))} :
          Subgroup (Equiv.Perm (Omega K))) :=
        { toFun := fun z => ⟨((z : B) : Equiv.Perm (Omega K)),
            Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp z.2).2,
              Subgroup.mem_centralizer_singleton_iff.mpr
                (congrArg Subtype.val (hAcomm _ (Subgroup.mem_inf.mp z.2).1 y hyA))⟩⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
      refine isCyclic_of_injective φ (fun z z' h => ?_)
      have h' := congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext h')
    have hA₀card : Nat.card A₀ = p := by
      obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := A₀)
      have h1 : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one
        (Subtype.ext (hA.2 _ (Subgroup.mem_inf.mp g.2).1))
      rw [hg] at h1
      rcases (Nat.dvd_prime hp).mp h1 with h | h
      · exfalso
        have hyA₀ : y ∈ A₀ := Subgroup.mem_inf.mpr ⟨hyA, Subgroup.mem_subgroupOf.mpr hyD⟩
        have := Subgroup.card_eq_one.mp h
        have h2 : y ∈ (⊥ : Subgroup B) := by rw [← this]; exact hyA₀
        exact hy1 ((Subgroup.mem_bot).mp h2)
      · exact h
    have hx : ∃ x ∈ A, (x : Equiv.Perm (Omega K)) ∉ coordinateD K := by
      by_contra hne
      push Not at hne
      have hle : A ≤ A₀ := fun x hx => Subgroup.mem_inf.mpr ⟨hx, Subgroup.mem_subgroupOf.mpr
        (hne x hx)⟩
      have h1 := Subgroup.card_le_of_le hle
      rw [hAcard, hA₀card] at h1
      have h3 : p < p ^ 2 := by nlinarith [hp.two_le]
      omega
    obtain ⟨x, hxA, hxD⟩ := hx
    have hx1 : x ≠ 1 := by
      rintro rfl
      exact hxD (Subgroup.one_mem _)
    refine ⟨hA₀card, (linear_two_prime_semilinear_field_descent hℓ hp hf K hK (hBE x.2) hxD
      (hAord x hxA hx1)).1, ?_⟩
    rw [eq_bot_iff, ← hθouter x hxA hxD]
    exact hIle x hxA hx1
  refine ⟨(CFSG.RankThree.GroupTheory.SteinbergBY.section_nine_residual_to_intersection hp hp2
    A).1 a haA ha1, ?_, hi, hii, hiii⟩
  by_cases hpℓ : p = ℓ
  · have hθa := hi hpℓ a haA ha1
    have hI : thetaT p A = ⊥ := by
      rw [eq_bot_iff, ← hθa]
      exact hIle a haA ha1
    change Odd (Nat.card (⁅θC a, A⁆ ⊔ thetaT p A : Subgroup B))
    rw [hθa, hI, Subgroup.commutator_bot_left, sup_bot_eq, Subgroup.card_bot]
    exact odd_one
  obtain ⟨-, -, hI⟩ := hii hpℓ
  change Odd (Nat.card (⁅θC a, A⁆ ⊔ thetaT p A : Subgroup B))
  rw [hI, sup_bot_eq]
  by_cases haD : (a : Equiv.Perm (Omega K)) ∉ coordinateD K
  · rw [hθouter a haA haD, Subgroup.commutator_bot_left, Subgroup.card_bot]
    exact odd_one
  push Not at haD
  set ā : Equiv.Perm (Omega K) := (a : Equiv.Perm (Omega K)) with hādef
  set Q : Subgroup (Equiv.Perm (Omega K)) := coordinateD K ⊓ Subgroup.centralizer {ā} with hQ
  have hQcyc : IsCyclic Q := (linear_two_inner_prime_centralizer_alternatives K hp hp3 haD
    (hAord a haA ha1)).1 (by rw [hchar]; exact hpℓ)
  have hQcomm : ∀ q ∈ Q, ∀ q' ∈ Q, Commute q q' := by
    let _ : CommGroup Q := IsCyclic.commGroup
    intro q hq q' hq'
    exact congrArg Subtype.val (mul_comm (⟨q, hq⟩ : Q) ⟨q', hq'⟩)
  let Qodd : Subgroup (Equiv.Perm (Omega K)) :=
    { carrier := {q | q ∈ Q ∧ Odd (orderOf q)}
      one_mem' := ⟨Q.one_mem, by rw [orderOf_one]; exact odd_one⟩
      mul_mem' := fun {q q'} hq hq' => ⟨Q.mul_mem hq.1 hq'.1,
        Odd.of_dvd_nat (hq.2.mul hq'.2) (((hQcomm q hq.1 q' hq'.1).orderOf_mul_dvd_lcm).trans
          (Nat.lcm_dvd_mul _ _))⟩
      inv_mem' := fun {q} hq => ⟨Q.inv_mem hq.1, by rw [orderOf_inv]; exact hq.2⟩ }
  have hQodd : Odd (Nat.card Qodd) := by
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp hev)
    have h1 := g.2.2
    rw [Subgroup.orderOf_coe, hg] at h1
    exact (Nat.not_odd_iff_even.mpr even_two) h1
  have hconjQ : ∀ g ∈ coordinateE K, g * ā = ā * g → ∀ q ∈ Q, g * q * g⁻¹ ∈ Q := by
    intro g hgE hga q hq
    rw [Subgroup.mem_inf] at hq
    refine Subgroup.mem_inf.mpr ⟨conj_mem_coordinateD hgE hq.1, ?_⟩
    have h1 : Commute g ā := hga
    have h2 : Commute q ā := Subgroup.mem_centralizer_singleton_iff.mp hq.2
    exact Subgroup.mem_centralizer_singleton_iff.mpr ((h1.mul_left h2).mul_left h1.inv_left)
  have hle : (⁅θC a, A⁆).map B.subtype ≤ Qodd := by
    rw [Subgroup.map_commutator, Subgroup.commutator_le]
    rintro _ ⟨s, hs, rfl⟩ _ ⟨u, hu, rfl⟩
    simp only [Subgroup.subtype_apply]
    have hsa : (s : Equiv.Perm (Omega K)) * ā = ā * s :=
      congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp ((hθ a).1 hs))
    have hua : (u : Equiv.Perm (Omega K)) * ā = ā * u :=
      congrArg Subtype.val (hAcomm u hu a haA)
    have hcQ : ⁅(s : Equiv.Perm (Omega K)), (u : Equiv.Perm (Omega K))⁆ ∈ Q := by
      refine Subgroup.mem_inf.mpr ⟨commutatorElement_mem_coordinateD (hBE s.2) (hBE u.2), ?_⟩
      rw [commutatorElement_def]
      have h1 : Commute (s : Equiv.Perm (Omega K)) ā := hsa
      have h2 : Commute (u : Equiv.Perm (Omega K)) ā := hua
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (((h1.mul_left h2).mul_left h1.inv_left).mul_left h2.inv_left)
    have hc : ⁅(s : Equiv.Perm (Omega K)), (u : Equiv.Perm (Omega K))⁆ =
        (s : Equiv.Perm (Omega K))⁻¹⁻¹ * ((u : Equiv.Perm (Omega K))⁻¹⁻¹ *
          (s : Equiv.Perm (Omega K))⁻¹ * (u : Equiv.Perm (Omega K))⁻¹) := by
      rw [commutatorElement_def]
      group
    have hunorm : (u : Equiv.Perm (Omega K))⁻¹ ∈ Subgroup.normalizer (Q : Set _) := by
      rw [Subgroup.mem_normalizer_iff]
      intro q
      have huE := hBE u.2
      have hua' : (u : Equiv.Perm (Omega K))⁻¹ * ā = ā * (u : Equiv.Perm (Omega K))⁻¹ :=
        (show Commute (u : Equiv.Perm (Omega K)) ā from hua).inv_left
      constructor
      · intro hq
        exact hconjQ _ (Subgroup.inv_mem _ huE) hua' q hq
      · intro hq
        have h := hconjQ _ huE hua _ hq
        rwa [show (u : Equiv.Perm (Omega K)) * ((u : Equiv.Perm (Omega K))⁻¹ * q *
          (u : Equiv.Perm (Omega K))⁻¹⁻¹) * (u : Equiv.Perm (Omega K))⁻¹ = q by group] at h
    have huo : Odd (orderOf (u : Equiv.Perm (Omega K))⁻¹) := by
      rw [orderOf_inv, Subgroup.orderOf_coe]
      exact Odd.of_dvd_nat (hp.odd_of_ne_two hp2) (orderOf_dvd_of_pow_eq_one (hA.2 u hu))
    refine ⟨hcQ, ?_⟩
    rw [hc] at hcQ ⊢
    exact odd_orderOf_of_mem_cyclic hQcyc hunorm huo hcQ
  rw [← Subgroup.card_map_of_injective B.subtype_injective]
  exact Odd.of_dvd_nat hQodd (Subgroup.card_dvd_of_le hle)

end Main

end CFSG.RankThree.LinearTwoPlaneCore
