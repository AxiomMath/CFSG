module

public import CFSG.Quasithin.H13.NQBlockRadicalR2Inputs
public import CFSG.Quasithin.H13.NQBlockThreeDivisible
public import CFSG.Quasithin.H13.NQCoreT2Holds

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem reducedAggregate_le_omegaOneCenterOf (H : Subgroup G) :
    reducedAggregate H ≤ omegaOneCenterOf 2 (pCoreOf 2 H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ : (CFSG.pCore 2 ↥H).map H.subtype = pCoreOf 2 H := by
    unfold pCoreOf
    try with_reducible rfl
  rintro _ ⟨v, hv, rfl⟩
  have hv' := (CFSG.Quasithin.qt_prime_reduced_aggregate_characteristic_maximal ↥H 2
    ).2.2.2.2.2.2.2.2.2 hv
  obtain ⟨hvQ, hvc, hv2⟩ := CFSG.Quasithin.BlueprintB2.mem_centerTorsion_iff.mp hv'
  refine mem_omegaOneCenterOf_iff.mpr ⟨hQ ▸ mem_map_of_mem _ hvQ, fun q hq => ?_, ?_⟩
  · rw [← hQ] at hq
    obtain ⟨q', hq', rfl⟩ := hq
    exact congrArg Subtype.val (hvc q' hq').symm
  · change (v : G) ^ 2 = 1
    exact congrArg Subtype.val hv2

theorem pCoreOf_le_centralizer_reducedAggregate (H : Subgroup G) :
    pCoreOf 2 H ≤ centralizer (reducedAggregate H : Set G) := fun p hp =>
  mem_centralizer_iff.mpr fun _ hu =>
    (mem_omegaOneCenterOf_iff.mp (reducedAggregate_le_omegaOneCenterOf H hu)).2.1 p hp

theorem isTwoReducedIn_reducedAggregate (H : Subgroup G) :
    IsTwoReducedIn H (reducedAggregate H) := by
  have h := A4.isTwoReducedIn_twoReducedJoin H
  rwa [← primeReducedAggregate_map_subtype_eq_twoReducedJoin] at h

omit [Finite G] in
theorem le_centralizer_of_oTwoUpper_le [Finite G] {H D V : Subgroup G}
    (hV : IsTwoReducedIn H V) (hDH : D ≤ H) (hHD : H ≤ normalizer (D : Set G))
    (hO : oTwoUpper D ≤ centralizer (V : Set G)) : D ≤ centralizer (V : Set G) :=
  hV.2.2.2 D hDH hHD fun _ hd =>
    (exists_pow_mem_oTwoUpper D hd).imp fun _ hk => hO hk

theorem mem_of_forall_prime_power {S : Subgroup G} {x : G}
    (h : ∀ y ∈ zpowers x, (∃ p k : ℕ, p.Prime ∧ orderOf y = p ^ k) → y ∈ S) : x ∈ S := by
  classical
  induction hn : orderOf x using Nat.strong_induction_on generalizing x with
  | _ n ih =>
  by_cases hn1 : n = 1
  · subst hn1
    exact h x (mem_zpowers x) ⟨2, 0, Nat.prime_two, by rw [hn, pow_zero]⟩
  · have hpos : 0 < n := hn ▸ orderOf_pos x
    obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd hn1
    obtain ⟨a, m, hm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hpos.ne' p hp.ne_one
    by_cases hm1 : m = 1
    · exact h x (mem_zpowers x) ⟨p, a, hp, by rw [hn, hnm, hm1, mul_one]⟩
    · have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hnm; omega)
      have ha0 : 0 < a := by
        rcases Nat.eq_zero_or_pos a with ha | ha
        · subst ha
          simp only [pow_zero, one_mul] at hnm
          exact absurd (hnm ▸ hpn) hm
        · exact ha
      have hcop : Nat.Coprime (p ^ a) m := Nat.Coprime.pow_left a
        ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm)
      have h1 : orderOf (x ^ (p ^ a)) = m := by
        rw [orderOf_pow' x (pow_ne_zero a hp.ne_zero), hn, hnm, Nat.gcd_mul_right_left,
          Nat.mul_div_cancel_left m (pow_pos hp.pos a)]
      have h2 : orderOf (x ^ m) = p ^ a := by
        rw [orderOf_pow' x hm0.ne', hn, hnm, Nat.gcd_mul_left_left,
          Nat.mul_div_cancel _ hm0]
      have hmn : m < n := by
        rw [hnm]
        calc m = 1 * m := (one_mul m).symm
          _ < p ^ a * m := Nat.mul_lt_mul_of_pos_right (Nat.one_lt_pow ha0.ne' hp.one_lt) hm0
      have hx1 : x ^ (p ^ a) ∈ S := ih m hmn (fun y hy => h y
        (zpowers_le.mpr (pow_mem (mem_zpowers x) (p ^ a)) hy)) h1
      have hx2 : x ^ m ∈ S := h _ (pow_mem (mem_zpowers x) _) ⟨p, a, hp, h2⟩
      obtain ⟨u, v, huv⟩ : ∃ u v : ℤ, u * ((p ^ a : ℕ) : ℤ) + v * (m : ℤ) = 1 := by
        have := Nat.gcd_eq_gcd_ab (p ^ a) m
        rw [Nat.Coprime.gcd_eq_one hcop, Nat.cast_one] at this
        exact ⟨Nat.gcdA (p ^ a) m, Nat.gcdB (p ^ a) m, by linear_combination this.symm⟩
      have hx : x = (x ^ ((p ^ a : ℕ) : ℤ)) ^ u * (x ^ (m : ℤ)) ^ v := by
        rw [← zpow_mul, ← zpow_mul, ← zpow_add, mul_comm ((p ^ a : ℕ) : ℤ) u,
          mul_comm (m : ℤ) v, huv, zpow_one]
      rw [hx, zpow_natCast, zpow_natCast]
      exact mul_mem (zpow_mem hx1 u) (zpow_mem hx2 v)

omit [Finite G] in
theorem exists_modO2_equiv [Finite G] {H D : Subgroup G} (hD : D ∈ cComp H) :
    ∃ e : ↥D ⧸ CFSG.pCore 2 ↥D ≃* ↥(modO2Image H D),
      ∀ d : ↥D, ((e (d : ↥D ⧸ CFSG.pCore 2 ↥D) : ↥(modO2Image H D)) : ↥H ⧸ CFSG.pCore 2 ↥H) =
        ((Subgroup.inclusion (le_of_mem_cComp hD) d : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) := by
  have hDH := le_of_mem_cComp hD
  set ψ : ↥D →* ↥H ⧸ CFSG.pCore 2 ↥H :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥H)).comp (Subgroup.inclusion hDH) with hψdef
  have hψr : ψ.range = modO2Image H D := by
    rw [hψdef, MonoidHom.range_comp, Subgroup.inclusion_range]
    rfl
  have hψk : ψ.ker = CFSG.pCore 2 ↥D := by
    ext x
    rw [MonoidHom.mem_ker, hψdef, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, mem_pCore_iff_mem_pCoreOf, mem_pCore_iff_mem_pCoreOf]
    exact ⟨fun h => (mem_pCore_iff_mem_pCoreOf x).mp (mem_pCore_of_mem_pCoreOf hDH x h),
      fun h => CFSG.Quasithin.A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hD) h⟩
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hψk.symm).trans
    (QuotientGroup.quotientKerEquivRange ψ)).trans (MulEquiv.subgroupCongr hψr), fun _ => rfl⟩

omit [Finite G] in
theorem pow_prime_eq_one_of_elem {p n : ℕ} [Fact p.Prime] (v : Multiplicative (Fin n → ZMod p)) :
    v ^ p = 1 := by
  apply Multiplicative.toAdd.injective
  funext i
  simp [toAdd_pow, nsmul_eq_mul]

omit [Finite G] in
theorem pow_prime_eq_one_of_homocyclic_one {p : ℕ} [Fact p.Prime]
    (v : Multiplicative (ZMod (p ^ 1)) × Multiplicative (ZMod (p ^ 1))) : v ^ p = 1 := by
  have hp : ((p : ℕ) : ZMod (p ^ 1)) = 0 := by rw [pow_one, ZMod.natCast_self]
  refine Prod.ext ?_ ?_
  · apply Multiplicative.toAdd.injective
    rw [Prod.pow_fst, toAdd_pow, nsmul_eq_mul, hp, zero_mul]
    rfl
  · apply Multiplicative.toAdd.injective
    rw [Prod.pow_snd, toAdd_pow, nsmul_eq_mul, hp, zero_mul]
    rfl

theorem a36_prime_element {Q : Type} [Group Q] [Finite Q] {L : Subgroup Q}
    (hA : QuasithinUnique.Vol2Native.A36CoreCat L) (hq : ¬ CFSG.IsQuasisimple ↥L) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {x : ↥L} (hx : x ∈ CFSG.solvableRadical ↥L) (hx1 : x ≠ 1)
    {k : ℕ} (hk : orderOf x = p ^ k) :
    5 ≤ p ∧ x ∈ CFSG.pCore p ↥L ∧
      ((∀ y ∈ CFSG.pCore p ↥L, y ^ p = 1) ∨
        ∃ e : ℕ, 1 < e ∧ Nonempty (↥(CFSG.pCore p ↥L) ≃*
          (Multiplicative (ZMod (p ^ e)) × Multiplicative (ZMod (p ^ e))))) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hcases, ⟨-, -, hFR, -⟩, -⟩ := hA
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hk
    exact hx1 hk
  have hodd : Odd (orderOf x) := by
    rw [hk]
    exact (hp.odd_of_ne_two hp2).pow
  have hxF : x ∈ CFSG.fittingSubgroup ↥L := by
    rcases hFR with ⟨-, h2⟩ | ⟨-, hFeq, -⟩
    · have hFR' : CFSG.fittingSubgroup ↥L ≤ CFSG.solvableRadical ↥L :=
        CFSG.Quasithin.A36B.fitting_le_radical
      have hidx : ((CFSG.fittingSubgroup ↥L).subgroupOf (CFSG.solvableRadical ↥L)).index = 2 := h2
      have hsq := Subgroup.sq_mem_of_index_two hidx ⟨x, hx⟩
      have hx2 : x ^ 2 ∈ CFSG.fittingSubgroup ↥L := hsq
      obtain ⟨m, hm⟩ := hodd
      have hxm : x = (x ^ 2) ^ (m + 1) := by
        rw [← pow_mul, show 2 * (m + 1) = orderOf x + 1 by omega, pow_succ, pow_orderOf_eq_one,
          one_mul]
      rw [hxm]
      exact pow_mem hx2 _
    · rw [hFeq]
      exact hx
  have hxP : x ∈ CFSG.pCore p ↥L := NQRigid.mem_pCore_of_mem_fitting hxF hk
  have hpF : p ∣ Nat.card (CFSG.fittingSubgroup ↥L) := by
    have h1 : orderOf (⟨x, hxF⟩ : ↥(CFSG.fittingSubgroup ↥L)) = p ^ k := by
      rw [Subgroup.orderOf_mk, hk]
    have h2 := orderOf_dvd_natCard (⟨x, hxF⟩ : ↥(CFSG.fittingSubgroup ↥L))
    rw [h1] at h2
    exact (dvd_pow_self p hk0).trans h2
  have hPF : CFSG.pCore p ↥L ≤ CFSG.fittingSubgroup ↥L :=
    CFSG.LocalCores.fitting_characteristic.2.2 _ CFSG.pCore_normal
      (CFSG.pCore_isPGroup (p := p) (G := ↥L)).isNilpotent
  refine ⟨?_, hxP, ?_⟩
  · rcases hcases with hc | ⟨p₀, hp₀, hp₀3, -, ⟨eF⟩, -⟩ | ⟨-, -, -, hprimes⟩
    · exact absurd hc.1 hq
    · have : Fact p₀.Prime := ⟨hp₀⟩
      have h1 : x ^ p₀ = 1 := by
        have := pow_prime_eq_one_of_elem (eF ⟨x, hxF⟩)
        rw [← map_pow, MulEquiv.map_eq_one_iff] at this
        exact congrArg Subtype.val this
      have h2 : p ^ k ∣ p₀ := hk ▸ orderOf_dvd_of_pow_eq_one h1
      have h3 : p = p₀ := (Nat.prime_dvd_prime_iff_eq hp hp₀).mp ((dvd_pow_self p hk0).trans h2)
      have h4 : p₀ ≠ 4 := fun h => by rw [h] at hp₀; norm_num at hp₀
      omega
    · obtain ⟨h5, -⟩ := hprimes p hp hpF
      have h2 := hp.two_le
      have h4 : p ≠ 4 := fun h => by rw [h] at hp; norm_num at hp
      have h3 : p ≠ 3 := fun h => by rw [h] at h5; omega
      omega
  · rcases hcases with hc | ⟨p₀, hp₀, -, -, ⟨eF⟩, -⟩ | ⟨-, -, -, hprimes⟩
    · exact absurd hc.1 hq
    · have : Fact p₀.Prime := ⟨hp₀⟩
      have h1 : x ^ p₀ = 1 := by
        have := pow_prime_eq_one_of_elem (eF ⟨x, hxF⟩)
        rw [← map_pow, MulEquiv.map_eq_one_iff] at this
        exact congrArg Subtype.val this
      have h2 : p ^ k ∣ p₀ := hk ▸ orderOf_dvd_of_pow_eq_one h1
      have h3 : p = p₀ := (Nat.prime_dvd_prime_iff_eq hp hp₀).mp ((dvd_pow_self p hk0).trans h2)
      subst h3
      left
      intro y hy
      have := pow_prime_eq_one_of_elem (eF ⟨y, hPF hy⟩)
      rw [← map_pow, MulEquiv.map_eq_one_iff] at this
      exact congrArg Subtype.val this
    · obtain ⟨-, hshape⟩ := hprimes p hp hpF
      rcases hshape with ⟨-, -, hexp⟩ | ⟨n, hn, ⟨eP⟩⟩
      · left
        intro y hy
        exact congrArg Subtype.val (hexp ⟨y, hy⟩)
      · rcases Nat.lt_or_ge 1 n with hn1 | hn1
        · exact Or.inr ⟨n, hn1, ⟨eP⟩⟩
        · obtain rfl : n = 1 := le_antisymm hn1 hn
          left
          intro y hy
          have := pow_prime_eq_one_of_homocyclic_one (eP ⟨y, hy⟩)
          rw [← map_pow, MulEquiv.map_eq_one_iff] at this
          exact congrArg Subtype.val this

theorem radical_le_centralizer_of_maximalLocal
    (hb : Lemma3_2_13Consumed)
    (hc : Lemma3_2_14HomocyclicConsumed)
    {T D : Subgroup G} (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (hQ : QuasithinUnique.quasithinIsQTKECat G) (hT : quasithinIsSylowTwo T)
    (hDm : quasithinIsMaximalLocal T D) (hDf : quasithinIsFaithfulLocal T D)
    (hTD : T ≤ normalizer (D : Set G)) (hDq : ¬ CFSG.IsQuasisimple (↥D ⧸ CFSG.pCore 2 ↥D)) :
    (CFSG.solvableRadical ↥D).map D.subtype ≤
      centralizer (reducedAggregate (D ⊔ T) : Set G) := by
  classical
  have := hs
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hDH : D ≤ D ⊔ T := le_sup_left
  have hHD : D ⊔ T ≤ normalizer (D : Set G) := sup_le le_normalizer hTD
  have hDc : D ∈ cComp (D ⊔ T) := CFSG.Quasithin.cComp_of_isLocal hDm.1
  have hO2 : pCoreOf 2 (D ⊔ T) ≠ ⊥ := hDm.1.2.2.2
  have hloc : QuasithinUnique.LocalSQTK G := (QuasithinUnique.qtkeCore_of_cat hnab hQ).1
  have hPV := pCoreOf_le_centralizer_reducedAggregate (D ⊔ T)
  have hDP : pCoreOf 2 D ≤ pCoreOf 2 (D ⊔ T) := fun x hx =>
    CFSG.Quasithin.A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hDc) hx
  obtain ⟨-, -, hcan⟩ :=
    NQCore.sylow_normalized_maximal_nonquasisimple_canonical_residual_structure
      NQCore.sylowNormalizedMaximalLocalUniqueNormalizer_holds
      sylowNormalizedLocalNormalComponent_proved hnab hQ hT hDm hDf hTD hDq
  have hQs := QuasithinUnique.Vol2Native.sqtkHypCat_quotient_of_pCoreOf_ne_bot hloc hO2
  have hA := QuasithinUnique.Vol2Native.a36CoreForSQTKCat_proved _ hQs _
    (modO2Image_mem_cComp hDc)
  obtain ⟨e, -⟩ := exists_modO2_equiv hDc
  have hDbq : ¬ CFSG.IsQuasisimple ↥(modO2Image (D ⊔ T) D) := fun h =>
    hDq (CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm h)
  have key : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ x ∈ (CFSG.solvableRadical ↥D).map D.subtype,
      ∀ k : ℕ, orderOf x = p ^ k → x ∈ centralizer (reducedAggregate (D ⊔ T) : Set G) := by
    intro p hp hp2 x hxR k hk
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨r, hr, rfl⟩ := hxR
    by_cases hr1 : (r : ↥D ⧸ CFSG.pCore 2 ↥D) = 1
    · have h1 := (QuotientGroup.eq_one_iff r).mp hr1
      rw [mem_pCore_iff_mem_pCoreOf] at h1
      exact hPV (hDP h1)
    have hxR' : e (r : ↥D ⧸ CFSG.pCore 2 ↥D) ∈ CFSG.solvableRadical ↥(modO2Image (D ⊔ T) D) := by
      rw [← CFSG.LieType.SteinbergBR.solvableRadical_map_equiv e]
      exact mem_map_of_mem _
        (CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot.map_solvableRadical_le
          (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥D)) (mem_map_of_mem _ hr))
    have hx1 : e (r : ↥D ⧸ CFSG.pCore 2 ↥D) ≠ 1 := fun h => hr1 (e.map_eq_one_iff.mp h)
    obtain ⟨j, -, hj⟩ : ∃ j, j ≤ k ∧ orderOf (e (r : ↥D ⧸ CFSG.pCore 2 ↥D)) = p ^ j := by
      rw [MulEquiv.orderOf_eq]
      have h1 : orderOf (r : ↥D ⧸ CFSG.pCore 2 ↥D) ∣ p ^ k := by
        rw [← hk]
        have h2 : orderOf (D.subtype r) = orderOf r := orderOf_coe r
        rw [h2]
        exact orderOf_map_dvd (QuotientGroup.mk' (CFSG.pCore 2 ↥D)) r
      exact (Nat.dvd_prime_pow hp).mp h1
    obtain ⟨hp5, hxP, hshape⟩ := a36_prime_element hA hDbq hp hp2 hxR' hx1 hj
    have hPe := CFSG.LieType.SteinbergBR.pCore_map_equiv p e
    have hrP : (r : ↥D ⧸ CFSG.pCore 2 ↥D) ∈ CFSG.pCore p (↥D ⧸ CFSG.pCore 2 ↥D) := by
      rw [← hPe] at hxP
      obtain ⟨z, hz, hze⟩ := hxP
      rwa [← e.injective hze]
    have hCp : CFSG.pCore p (↥D ⧸ CFSG.pCore 2 ↥D) ≠ ⊥ := fun h => by
      rw [h, mem_bot] at hrP
      exact hr1 hrP
    rcases hshape with hexp | ⟨n, hn, ⟨eP⟩⟩
    ·
      have hrp : (r : ↥D ⧸ CFSG.pCore 2 ↥D) ^ p = 1 := by
        have h1 := hexp _ hxP
        rw [← map_pow, MulEquiv.map_eq_one_iff] at h1
        exact h1
      have hmem : (r : ↥D ⧸ CFSG.pCore 2 ↥D) ∈
          ((nqPrimeResidualX D p).subgroupOf D).map (QuotientGroup.mk' (CFSG.pCore 2 ↥D)) := by
        rw [(hcan p hp hp5 hCp).image]
        exact subset_closure ⟨hrP, hrp⟩
      obtain ⟨y, hy, hyr⟩ := hmem
      have hz : y⁻¹ * r ∈ CFSG.pCore 2 ↥D := QuotientGroup.eq.mp hyr
      rw [mem_pCore_iff_mem_pCoreOf] at hz
      have hrr : (r : G) = (y : G) * ((y⁻¹ * r : ↥D) : G) := by
        rw [coe_mul, coe_inv, mul_inv_cancel_left]
      change ((r : ↥D) : G) ∈ _
      rw [hrr]
      exact mul_mem (hb G T D hs hnab hQ hT hDm hDf hTD hDq p hp hp5 hCp (mem_subgroupOf.mp hy))
        (hPV (hDP hz))
    ·
      have eP' : ↥(CFSG.pCore p (↥D ⧸ CFSG.pCore 2 ↥D)) ≃*
          (Multiplicative (ZMod (p ^ n)) × Multiplicative (ZMod (p ^ n))) :=
        ((CFSG.pCore p (↥D ⧸ CFSG.pCore 2 ↥D)).equivMapOfInjective e.toMonoidHom
          e.injective).trans ((MulEquiv.subgroupCongr hPe).trans eP)
      refine hc G T D hs hnab hQ hT hDm hDf hTD hDq p hp hp5 n hn ⟨eP'⟩
        (subset_closure ⟨mem_map_of_mem _ hr, k, ?_⟩)
      rw [← hk]
      exact pow_orderOf_eq_one _
  have hodd : ∀ x ∈ (CFSG.solvableRadical ↥D).map D.subtype, Odd (orderOf x) →
      x ∈ centralizer (reducedAggregate (D ⊔ T) : Set G) := by
    intro x hx ho
    refine mem_of_forall_prime_power fun y hy ⟨q, k, hq, hyk⟩ => ?_
    have hyR : y ∈ (CFSG.solvableRadical ↥D).map D.subtype := zpowers_le.mpr hx hy
    by_cases hk0 : k = 0
    · subst hk0
      rw [pow_zero, orderOf_eq_one_iff] at hyk
      rw [hyk]
      exact one_mem _
    · have hq2 : q ≠ 2 := by
        rintro rfl
        have h1 : orderOf y ∣ orderOf x := orderOf_dvd_of_mem_zpowers hy
        rw [hyk] at h1
        exact (Nat.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr ((dvd_pow_self 2 hk0).trans h1))
      exact key q hq hq2 y hyR k hyk
  have hO : oTwoUpper ((CFSG.solvableRadical ↥D).map D.subtype) ≤
      centralizer (reducedAggregate (D ⊔ T) : Set G) :=
    (closure_le _).mpr fun x hx => hodd x hx.1 hx.2
  exact le_centralizer_of_oTwoUpper_le (isTwoReducedIn_reducedAggregate (D ⊔ T))
    ((map_subtype_le _).trans hDH)
    (hHD.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)) hO

end CFSG.Quasithin.H13.NQBlock
