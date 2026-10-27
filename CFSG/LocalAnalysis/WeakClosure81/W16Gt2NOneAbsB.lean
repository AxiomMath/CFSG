module

public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2NOneAbs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin Subgroup
open scoped Pointwise

namespace NOne

variable {Ω : Type} [Group Ω] [Finite Ω]

private theorem conj_mem_commutator_of_normalizes {O : Subgroup Ω} {r : Ω}
    (hr : ∀ o ∈ O, r * o * r⁻¹ ∈ O) {d : Ω} (hd : d ∈ ⁅O, O⁆) :
    r * d * r⁻¹ ∈ ⁅O, O⁆ := by
  rw [Subgroup.commutator_def] at hd ⊢
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hd
  · rintro x ⟨a, ha, b, hb, rfl⟩
    exact Subgroup.subset_closure
      ⟨r * a * r⁻¹, hr a ha, r * b * r⁻¹, hr b hb, by
        simp only [commutatorElement_def]; group⟩
  · simp
  · intro x y _ _ hpx hpy
    have hxy : r * (x * y) * r⁻¹ = (r * x * r⁻¹) * (r * y * r⁻¹) := by group
    rw [hxy]
    exact Subgroup.mul_mem _ hpx hpy
  · intro x _ hpx
    have hx : r * x⁻¹ * r⁻¹ = (r * x * r⁻¹)⁻¹ := by group
    rw [hx]
    exact Subgroup.inv_mem _ hpx

private theorem eq_top_of_exists_sylow_le {G : Type*} [Group G] [Finite G] (H : Subgroup G)
    (hSyl : ∀ p : ℕ, p ∈ (Nat.card G).primeFactors → ∀ [Fact p.Prime],
      ∃ P : Sylow p G, (P : Subgroup G) ≤ H) :
    H = ⊤ := by
  rw [← Subgroup.card_eq_iff_eq_top]
  apply Nat.eq_of_factorization_eq Nat.card_pos.ne' Nat.card_pos.ne'
  intro p
  by_cases hp : p.Prime
  · let : Fact p.Prime := ⟨hp⟩
    by_cases hd : p ∈ (Nat.card G).primeFactors
    · obtain ⟨P, hPle⟩ := hSyl p hd
      refine le_antisymm
        (Nat.factorization_le_factorization_of_dvd_right
          (Subgroup.card_subgroup_dvd_card H) Nat.card_pos.ne' Nat.card_pos.ne') ?_
      rw [← pow_le_pow_iff_right₀ (Nat.Prime.one_lt hp), ← Sylow.card_eq_multiplicity P]
      have hc : Nat.card P = Nat.card (P.subgroupOf H) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPle).symm
      have hpP : IsPGroup p (P.subgroupOf H) := by
        refine IsPGroup.of_card (n := (Nat.card G).factorization p) ?_
        rw [← hc, ← Sylow.card_eq_multiplicity P]
      rcases IsPGroup.exists_le_sylow hpP with ⟨P', hP'⟩
      rw [← Sylow.card_eq_multiplicity P', hc]
      exact Subgroup.card_le_of_le hP'
    · have hnpG : ¬ p ∣ Nat.card G := by
        intro hpG
        exact hd ((Nat.mem_primeFactors).2 ⟨hp, hpG, Nat.card_pos.ne'⟩)
      have hnpH : ¬ p ∣ Nat.card H := by
        intro hpH
        exact hnpG (dvd_trans hpH (Subgroup.card_subgroup_dvd_card H))
      simp [Nat.factorization_eq_zero_of_not_dvd hnpG, Nat.factorization_eq_zero_of_not_dvd hnpH]
  · simp [Nat.factorization_eq_zero_of_not_prime (n := Nat.card G) (p := p) hp,
      Nat.factorization_eq_zero_of_not_prime (n := Nat.card H) (p := p) hp]

theorem exists_isPGroup_of_minimal {R O : Subgroup Ω} {t : Ω} (hR2 : IsPGroup 2 R)
    (hOodd : Odd (Nat.card O)) (hRO : ∀ r ∈ R, ∀ o ∈ O, r * o * r⁻¹ ∈ O)
    (hmin : ∀ N : Subgroup Ω, N ≤ O → (∀ r ∈ R, ∀ n ∈ N, r * n * r⁻¹ ∈ N) →
      (∃ x ∈ N, t * x ≠ x * t) → N = O)
    (hnc : ∃ o ∈ O, t * o ≠ o * t) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ IsPGroup p O := by
  classical
  have hObot : O ≠ ⊥ := by
    rintro hbot
    obtain ⟨o, ho, hne⟩ := hnc
    rw [hbot, Subgroup.mem_bot] at ho
    subst ho
    exact hne (by simp)
  by_contra hcon
  have hRO' : R ≤ Subgroup.normalizer O := fun r hr =>
    Subgroup.mem_normalizer_iff.mpr fun o =>
      ⟨fun ho => hRO r hr o ho, fun ho => by
        have h := hRO r⁻¹ (R.inv_mem hr) (r * o * r⁻¹) ho
        rwa [show r⁻¹ * (r * o * r⁻¹) * r⁻¹⁻¹ = o from by group] at h⟩
  letI : MulDistribMulAction ↥R ↥O := Subgroup.conjMulDistribMulActionOfLeNormalizer R O hRO'
  haveI : Fact (IsPGroup 2 ↥R) := ⟨hR2⟩
  have hcop : Nat.Coprime 2 (Nat.card ↥O) := Nat.coprime_two_left.mpr hOodd
  have hHtop : (Subgroup.centralizer ({t} : Set Ω)).subgroupOf O = ⊤ := by
    refine eq_top_of_exists_sylow_le _ ?_
    intro p hp hpp
    haveI : Fact p.Prime := hpp
    obtain ⟨P, hPinv⟩ :=
      CFSG.exists_invariant_sylow (G := ↥O) (A := ↥R) (p := 2) (q := p) hcop
    refine ⟨P, ?_⟩
    by_contra hnot
    obtain ⟨x, hxP, hxH⟩ := Set.not_subset.mp hnot
    have hxne : t * (x : Ω) ≠ (x : Ω) * t := by
      intro hc
      apply hxH
      change x ∈ (Subgroup.centralizer ({t} : Set Ω)).subgroupOf O
      rw [Subgroup.mem_subgroupOf]
      exact Subgroup.mem_centralizer_iff.mpr fun h hh => by
        rw [Set.mem_singleton_iff] at hh
        subst hh
        exact hc
    have hQinv : ∀ r ∈ R, ∀ n ∈ (P : Subgroup ↥O).map O.subtype,
        r * n * r⁻¹ ∈ (P : Subgroup ↥O).map O.subtype := by
      intro r hr n hn
      obtain ⟨y, hyP, rfl⟩ := Subgroup.mem_map.mp hn
      let w : ↥O := (⟨r, hr⟩ : ↥R) • y
      refine ⟨w, (hPinv.invariant (⟨r, hr⟩ : ↥R) y).mp hyP, ?_⟩
      exact Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe_explicit R O hRO'
        (⟨r, hr⟩ : ↥R) y
    have hQeq : (P : Subgroup ↥O).map O.subtype = O :=
      hmin _ (Subgroup.map_subtype_le _) hQinv ⟨(x : Ω), ⟨x, hxP, rfl⟩, hxne⟩
    have hmap : IsPGroup p ((P : Subgroup ↥O).map O.subtype) :=
      IsPGroup.map P.isPGroup' O.subtype
    exact hcon ⟨p, (Nat.mem_primeFactors.mp hp).1,
      Odd.ne_two_of_dvd_nat hOodd (Nat.mem_primeFactors.mp hp).2.1, hQeq ▸ hmap⟩
  obtain ⟨o, ho, hne⟩ := hnc
  apply hne
  have hmem : (⟨o, ho⟩ : ↥O) ∈ (Subgroup.centralizer ({t} : Set Ω)).subgroupOf O := by
    rw [hHtop]; exact Subgroup.mem_top _
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at hmem
  exact hmem t (Set.mem_singleton t)

theorem commute_of_isPGroup {Hh K R O : Subgroup Ω} {t : Ω} (hK : IsConjClosure Hh K t)
    (hRH : R ≤ Hh) (hOK : O ≤ K) (hOn : ∀ x ∈ Hh, ∀ o ∈ O, x * o * x⁻¹ ∈ O)
    {p : ℕ} [Fact p.Prime] (hOp : IsPGroup p O)
    (hmin : ∀ N : Subgroup Ω, N ≤ O → (∀ r ∈ R, ∀ n ∈ N, r * n * r⁻¹ ∈ N) →
      (∃ x ∈ N, t * x ≠ x * t) → N = O)
    (hnc : ∃ o ∈ O, t * o ≠ o * t)
    (hZ : ∀ z ∈ K, (∀ k ∈ K, z * k = k * z) → z = 1) :
    ∀ x ∈ O, ∀ y ∈ O, x * y = y * x := by
  have hObot : O ≠ ⊥ := by
    rintro hbot
    obtain ⟨o, ho, hne⟩ := hnc
    rw [hbot, Subgroup.mem_bot] at ho
    subst ho
    exact hne (by simp)
  haveI : Nontrivial ↥O := (Subgroup.nontrivial_iff_ne_bot O).mpr hObot
  haveI : Group.IsNilpotent ↥O := hOp.isNilpotent
  have hDne : ⁅O, O⁆ ≠ O := by
    have hlt : ⁅O, O⁆ < O := by
      have hcommtop : _root_.commutator ↥O < ⊤ :=
        Group.IsSolvable.commutator_lt_top_of_nontrivial ↥O
      have h := (Subgroup.map_subtype_lt_map_subtype (G' := O)).mpr hcommtop
      rw [Subgroup.map_subtype_commutator O, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype] at h
      exact h
    exact hlt.ne
  have hDR : ∀ r ∈ R, ∀ d ∈ ⁅O, O⁆, r * d * r⁻¹ ∈ ⁅O, O⁆ :=
    fun r hr d hd =>
      conj_mem_commutator_of_normalizes (fun o ho => hOn r (hRH hr) o ho) hd
  have hDcomm : ∀ d ∈ ⁅O, O⁆, t * d = d * t := by
    intro d hd
    by_contra hne
    exact absurd (hmin _ (Subgroup.commutator_le_self O) hDR ⟨d, hd, hne⟩) hDne
  have hDHh : ∀ x ∈ Hh, ∀ d ∈ ⁅O, O⁆,
      (x⁻¹ * t * x) * d = d * (x⁻¹ * t * x) := by
    intro x hx d hd
    have hdx : x * d * x⁻¹ ∈ ⁅O, O⁆ :=
      conj_mem_commutator_of_normalizes (fun o ho => hOn x hx o ho) hd
    calc (x⁻¹ * t * x) * d = x⁻¹ * (t * (x * d * x⁻¹)) * x := by group
      _ = x⁻¹ * ((x * d * x⁻¹) * t) * x := by rw [hDcomm (x * d * x⁻¹) hdx]
      _ = d * (x⁻¹ * t * x) := by group
  have hKD : K ≤ Subgroup.centralizer (⁅O, O⁆ : Subgroup Ω) := by
    refine hK.gen _ ?_
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact (hDHh x hx d hd).symm
  have hDbot : ⁅O, O⁆ = ⊥ := by
    rw [eq_bot_iff]
    intro d hd
    have hdK : d ∈ K := hOK (Subgroup.commutator_le_self O hd)
    have hz : ∀ k ∈ K, d * k = k * d := by
      intro k hk
      have hkD := hKD hk
      rw [Subgroup.mem_centralizer_iff] at hkD
      exact hkD d hd
    rw [hZ d hdK hz]
    exact Subgroup.one_mem ⊥
  have hcent : O ≤ Subgroup.centralizer (O : Set Ω) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hDbot
  intro x hx y hy
  have hmem := hcent hx
  rw [Subgroup.mem_centralizer_iff] at hmem
  exact (hmem y hy).symm

theorem inv_eq_of_commute {R O : Subgroup Ω} {t : Ω} (htR : t ∈ R) (ht2 : t * t = 1)
    (hRt : ∀ r ∈ R, r * t = t * r) (hOodd : Odd (Nat.card O))
    (hRO : ∀ r ∈ R, ∀ o ∈ O, r * o * r⁻¹ ∈ O) (hab : ∀ x ∈ O, ∀ y ∈ O, x * y = y * x)
    (hmin : ∀ N : Subgroup Ω, N ≤ O → (∀ r ∈ R, ∀ n ∈ N, r * n * r⁻¹ ∈ N) →
      (∃ x ∈ N, t * x ≠ x * t) → N = O)
    (hnc : ∃ o ∈ O, t * o ≠ o * t) :
    ∀ o ∈ O, t * o * t⁻¹ = o⁻¹ := by
  have htO : ∀ o ∈ O, t * o * t⁻¹ ∈ O := fun o ho => hRO t htR o ho
  let δ : ↥O →* ↥O :=
    { toFun := fun x => ⟨(x : Ω)⁻¹ * (t * (x : Ω) * t⁻¹),
        O.mul_mem (O.inv_mem x.2) (htO x x.2)⟩
      map_one' := by ext; simp
      map_mul' := by
        intro x y
        ext
        change ((x : Ω) * (y : Ω))⁻¹ * (t * ((x : Ω) * (y : Ω)) * t⁻¹)
            = ((x : Ω)⁻¹ * (t * (x : Ω) * t⁻¹))
              * ((y : Ω)⁻¹ * (t * (y : Ω) * t⁻¹))
        calc ((x : Ω) * (y : Ω))⁻¹ * (t * ((x : Ω) * (y : Ω)) * t⁻¹)
            = (y : Ω)⁻¹ * ((x : Ω)⁻¹ * (t * (x : Ω) * t⁻¹))
                * (t * (y : Ω) * t⁻¹) := by group
          _ = ((x : Ω)⁻¹ * (t * (x : Ω) * t⁻¹))
                * ((y : Ω)⁻¹ * (t * (y : Ω) * t⁻¹)) := by
              rw [hab (y : Ω)⁻¹ (O.inv_mem y.2)
                    ((x : Ω)⁻¹ * (t * (x : Ω) * t⁻¹))
                    (O.mul_mem (O.inv_mem x.2) (htO x x.2))]
              group }
  have hδinv : ∀ x : ↥O,
      t * ((δ x : ↥O) : Ω) * t⁻¹ = (((δ x : ↥O) : Ω))⁻¹ := by
    intro x
    change t * ((x : Ω)⁻¹ * (t * (x : Ω) * t⁻¹)) * t⁻¹
        = ((x : Ω)⁻¹ * (t * (x : Ω) * t⁻¹))⁻¹
    have h2i : t⁻¹ * t⁻¹ = 1 := by rw [← mul_inv_rev, ht2, inv_one]
    have hx : t * (t * (x : Ω) * t⁻¹) * t⁻¹ = (x : Ω) := by
      calc t * (t * (x : Ω) * t⁻¹) * t⁻¹
          = (t * t) * (x : Ω) * (t⁻¹ * t⁻¹) := by group
        _ = (x : Ω) := by rw [ht2, h2i, one_mul, mul_one]
    calc t * ((x : Ω)⁻¹ * (t * (x : Ω) * t⁻¹)) * t⁻¹
        = (t * (x : Ω)⁻¹ * t⁻¹) * (t * (t * (x : Ω) * t⁻¹) * t⁻¹) := by group
      _ = ((t * (x : Ω) * t⁻¹)⁻¹) * (x : Ω) := by rw [hx]; group
      _ = ((x : Ω)⁻¹ * (t * (x : Ω) * t⁻¹))⁻¹ := by group
  let N : Subgroup Ω := (O.subtype.comp δ).range
  have hNle : N ≤ O := by
    intro n hn
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hn
    exact (δ x).2
  have hδconj : ∀ (r : Ω) (hr : r ∈ R) (x : ↥O),
      (δ ⟨r * (x : Ω) * r⁻¹, hRO r hr x x.2⟩ : Ω) = r * (δ x : Ω) * r⁻¹ := by
    intro r hr x
    change (r * (x : Ω) * r⁻¹)⁻¹ * (t * (r * (x : Ω) * r⁻¹) * t⁻¹)
        = r * ((x : Ω)⁻¹ * (t * (x : Ω) * t⁻¹)) * r⁻¹
    have hcomm' : r⁻¹ * t⁻¹ = t⁻¹ * r⁻¹ := by
      simpa [mul_inv_rev] using congrArg Inv.inv (hRt r hr).symm
    have hstep : t * (r * (x : Ω) * r⁻¹) * t⁻¹
        = r * (t * (x : Ω) * t⁻¹) * r⁻¹ := by
      calc t * (r * (x : Ω) * r⁻¹) * t⁻¹
          = (t * r) * (x : Ω) * (r⁻¹ * t⁻¹) := by group
        _ = (r * t) * (x : Ω) * (r⁻¹ * t⁻¹) := by rw [hRt r hr]
        _ = (r * t) * (x : Ω) * (t⁻¹ * r⁻¹) := by rw [hcomm']
        _ = r * (t * (x : Ω) * t⁻¹) * r⁻¹ := by group
    rw [show (r * (x : Ω) * r⁻¹)⁻¹ = r * (x : Ω)⁻¹ * r⁻¹ from by group, hstep]
    group
  have hNinv : ∀ r ∈ R, ∀ n ∈ N, r * n * r⁻¹ ∈ N := by
    intro r hr n hn
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hn
    refine MonoidHom.mem_range.mpr ⟨⟨r * (x : Ω) * r⁻¹, hRO r hr x x.2⟩, ?_⟩
    exact hδconj r hr x
  obtain ⟨o, ho, hne⟩ := hnc
  let x₀ : ↥O := ⟨o, ho⟩
  have hx0 : t * (x₀ : Ω) ≠ (x₀ : Ω) * t := hne
  let y : ↥O := δ x₀
  have hyne1 : y ≠ 1 := by
    intro hy1
    apply hx0
    have hval : (y : Ω) = 1 := by rw [hy1]; rfl
    have h : (x₀ : Ω)⁻¹ * (t * (x₀ : Ω) * t⁻¹) = 1 := hval
    have hconj : t * (x₀ : Ω) * t⁻¹ = (x₀ : Ω) := by
      have := congrArg (fun w => (x₀ : Ω) * w) h
      simpa [mul_assoc] using this
    calc t * (x₀ : Ω) = t * (x₀ : Ω) * t⁻¹ * t := by group
      _ = (x₀ : Ω) * t := by rw [hconj]
  have hyodd : Odd (orderOf (y : Ω)) :=
    Odd.of_dvd_nat hOodd (Subgroup.orderOf_dvd_natCard O y.2)
  have hyy : (y : Ω) * (y : Ω) ≠ 1 := by
    intro h2
    have hdvd : orderOf (y : Ω) ∣ 2 :=
      orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact h2)
    have h1 : orderOf (y : Ω) = 1 := by
      rcases hyodd with ⟨m, hm⟩
      rw [hm] at hdvd
      have := Nat.le_of_dvd (by norm_num) hdvd
      omega
    exact hyne1 (Subtype.ext (orderOf_eq_one_iff.mp h1))
  have hyinv_ne : (y : Ω)⁻¹ ≠ (y : Ω) := by
    intro hinv
    apply hyy
    have h2 : (y : Ω) * (y : Ω) = 1 := by
      have h := congrArg (fun w => w * (y : Ω)) hinv
      rw [inv_mul_cancel] at h
      exact h.symm
    exact h2
  have hex : ∃ z ∈ N, t * z ≠ z * t := by
    refine ⟨(y : Ω), ?_, ?_⟩
    · exact MonoidHom.mem_range.mpr ⟨x₀, rfl⟩
    · intro hcomm
      apply hyinv_ne
      rw [← hδinv x₀]
      calc t * (y : Ω) * t⁻¹ = (y : Ω) * t * t⁻¹ := by rw [hcomm]
        _ = (y : Ω) := by group
  have hNeqO : N = O := hmin N hNle hNinv hex
  intro o ho
  have hmem : o ∈ N := by rw [hNeqO]; exact ho
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hmem
  rw [← hx]
  exact hδinv x

theorem eq_zpowers_sup_of_isCyclic {K R O : Subgroup Ω} {t : Ω}
    (hKO : K = Subgroup.zpowers t ⊔ O) (ht2 : t * t = 1) (hOodd : Odd (Nat.card O))
    (hRO : ∀ r ∈ R, ∀ o ∈ O, r * o * r⁻¹ ∈ O) (hOcyc : IsCyclic ↥O)
    (hinv : ∀ o ∈ O, t * o * t⁻¹ = o⁻¹)
    (hmin : ∀ N : Subgroup Ω, N ≤ O → (∀ r ∈ R, ∀ n ∈ N, r * n * r⁻¹ ∈ N) →
      (∃ x ∈ N, t * x ≠ x * t) → N = O)
    {k : Ω} (hk : k ∈ K) (hkt : k⁻¹ * t * k ≠ t) :
    K = Subgroup.zpowers t ⊔ Subgroup.zpowers (k⁻¹ * t * k) := by
  have ht2inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have ht_norm : t ∈ Subgroup.normalizer O := by
    rw [Subgroup.mem_normalizer_iff]
    intro o
    constructor
    · intro ho; rw [hinv o ho]; exact O.inv_mem ho
    · intro ho
      have h2 : t * (t * o * t⁻¹) * t⁻¹ ∈ O := by
        rw [hinv (t * o * t⁻¹) ho]; exact O.inv_mem ho
      have h3 : t * (t * o * t⁻¹) * t⁻¹ = o := by
        have h2i : t⁻¹ * t⁻¹ = 1 := by rw [← mul_inv_rev, ht2, inv_one]
        calc t * (t * o * t⁻¹) * t⁻¹ = (t * t) * o * (t⁻¹ * t⁻¹) := by group
          _ = o := by rw [ht2, h2i, one_mul, mul_one]
      rwa [h3] at h2
  have hnorm : Subgroup.zpowers t ≤ Subgroup.normalizer O :=
    Subgroup.zpowers_le.mpr ht_norm
  have hkK : k ∈ (Subgroup.zpowers t ⊔ O : Subgroup Ω) := by rw [← hKO]; exact hk
  have hkprod : k ∈ ((Subgroup.zpowers t : Set Ω) * (O : Set Ω)) := by
    change k ∈ (↑(Subgroup.zpowers t ⊔ O) : Set Ω) at hkK
    rwa [Subgroup.coe_mul_of_left_le_normalizer_right (Subgroup.zpowers t) O hnorm] at hkK
  obtain ⟨a, ha, o, ho, hao⟩ := hkprod
  let y₀ : Ω := o ^ 2
  have hyO : y₀ ∈ O := O.pow_mem ho 2
  have hky : k⁻¹ * t * k = t * y₀ := by
    rw [← hao]
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hc : Commute (t ^ n) t := (Commute.refl t).zpow_left n
    have htn : (t ^ n)⁻¹ * t * t ^ n = t := by
      rw [hc.inv_left.eq]; group
    calc (t ^ n * o)⁻¹ * t * (t ^ n * o)
        = o⁻¹ * ((t ^ n)⁻¹ * t * t ^ n) * o := by group
      _ = o⁻¹ * t * o := by rw [htn]
      _ = t * y₀ := by
            rw [show o⁻¹ = t * o * t⁻¹ from (hinv o ho).symm]
            rw [show y₀ = o * o from by rw [show y₀ = o ^ 2 from rfl, pow_two]]
            group
  have hy0ne1 : y₀ ≠ 1 := by
    intro h
    apply hkt
    rw [hky, h]
    group
  have hy0odd : Odd (orderOf y₀) :=
    Odd.of_dvd_nat hOodd (Subgroup.orderOf_dvd_natCard O hyO)
  have hy0sq : y₀ * y₀ ≠ 1 := by
    intro h2
    have hdvd : orderOf y₀ ∣ 2 :=
      orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact h2)
    have h1 : orderOf y₀ = 1 := by
      rcases hy0odd with ⟨m, hm⟩
      rw [hm] at hdvd
      have := Nat.le_of_dvd (by norm_num) hdvd
      omega
    exact hy0ne1 (orderOf_eq_one_iff.mp h1)
  have hty0inv : t * y₀ * t⁻¹ = y₀⁻¹ := by
    have h1 : t * y₀ * t⁻¹ = (t * o * t⁻¹) ^ 2 := by
      rw [show y₀ = o ^ 2 from rfl]
      rw [show t * o ^ 2 * t⁻¹ = (MulAut.conj t) (o ^ 2) from rfl, map_pow]
      rfl
    rw [h1, hinv o ho, inv_pow]
  have hty0ne : t * y₀ ≠ y₀ * t := by
    intro h
    apply hy0sq
    have h2 : y₀ * y₀ = 1 := by
      have hh : y₀⁻¹ = y₀ := by
        rw [← hty0inv, h]; group
      have := congrArg (fun w => w * y₀) hh
      rw [inv_mul_cancel] at this
      exact this.symm
    exact h2
  have hzy_eq : ∀ r ∈ R, Subgroup.zpowers (r * y₀ * r⁻¹) = Subgroup.zpowers y₀ := by
    intro r hr
    have hryO : r * y₀ * r⁻¹ ∈ O := hRO r hr y₀ hyO
    have hle1 : Subgroup.zpowers (r * y₀ * r⁻¹) ≤ O := Subgroup.zpowers_le.mpr hryO
    have hle2 : Subgroup.zpowers y₀ ≤ O := Subgroup.zpowers_le.mpr hyO
    have hcard1 : Nat.card ↥((Subgroup.zpowers (r * y₀ * r⁻¹)).subgroupOf O)
        = orderOf (r * y₀ * r⁻¹) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle1).toEquiv, Nat.card_zpowers]
    have hcard2 : Nat.card ↥((Subgroup.zpowers y₀).subgroupOf O) = orderOf y₀ := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle2).toEquiv, Nat.card_zpowers]
    have hooo : orderOf (r * y₀ * r⁻¹) = orderOf y₀ := by
      have := orderOf_injective (MulAut.conj r).toMonoidHom (MulAut.conj r).injective y₀
      simpa [MulAut.conj_apply] using this
    have heq : (Subgroup.zpowers (r * y₀ * r⁻¹)).subgroupOf O
        = (Subgroup.zpowers y₀).subgroupOf O := by
      refine (IsCyclic.subgroup_eq_iff_card_eq (G := ↥O)).mpr ?_
      rw [hcard1, hcard2, hooo]
    have hmap := congrArg (fun S : Subgroup ↥O => S.map O.subtype) heq
    rw [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype] at hmap
    rwa [inf_eq_left.mpr hle1, inf_eq_left.mpr hle2] at hmap
  have hzy_inv : ∀ r ∈ R, ∀ z ∈ Subgroup.zpowers y₀,
      r * z * r⁻¹ ∈ Subgroup.zpowers y₀ := by
    intro r hr z hz
    rw [← hzy_eq r hr]
    have h : (MulAut.conj r) z ∈ (Subgroup.zpowers y₀).map (MulAut.conj r).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hz
    rw [MonoidHom.map_zpowers, MulAut.conj_apply] at h
    exact h
  have hzp_eq_O : Subgroup.zpowers y₀ = O :=
    hmin (Subgroup.zpowers y₀) (Subgroup.zpowers_le.mpr hyO) hzy_inv
      ⟨y₀, Subgroup.mem_zpowers y₀, hty0ne⟩
  have hysup : Subgroup.zpowers t ⊔ Subgroup.zpowers y₀
      = Subgroup.zpowers t ⊔ Subgroup.zpowers (t * y₀) := by
    apply le_antisymm
    · apply sup_le le_sup_left
      apply Subgroup.zpowers_le.mpr
      have hy0eq : y₀ = t * (t * y₀)⁻¹ := by
        have h1 : t * (t * y₀)⁻¹ = t * y₀⁻¹ * t⁻¹ := by rw [mul_inv_rev]; group
        rw [h1, show t * y₀⁻¹ * t⁻¹ = (t * y₀ * t⁻¹)⁻¹ from by group, hty0inv, inv_inv]
      have hmem : t * (t * y₀)⁻¹ ∈ Subgroup.zpowers t ⊔ Subgroup.zpowers (t * y₀) :=
        Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))
          (Subgroup.inv_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers (t * y₀))))
      rwa [← hy0eq] at hmem
    · apply sup_le le_sup_left
      apply Subgroup.zpowers_le.mpr
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers y₀))
  rw [hKO, ← hzp_eq_O, hky]
  exact hysup

end NOne

end CFSG.LocalAnalysis.WeakClosure81
