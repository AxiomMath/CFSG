module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommFieldFusionDefs
public import CFSG.LocalAnalysis.EvenBN.Common.FreeSeries

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SingleCommParts

open Subgroup GomiFusion
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis

theorem sixFF_ff9_aux_lt_two_pow (m : ℕ) : m < 2 ^ m := by
  induction m with
  | zero => norm_num
  | succ m ih => rw [pow_succ]; omega

theorem sixFF_ff9_aux_sq_inj {a b : ℕ} (h : a ^ 2 = b ^ 2) : a = b :=
  Nat.pow_left_injective (show (2 : ℕ) ≠ 0 by norm_num) h

theorem sixFF_ff9_aux_arith (q m n : ℕ) (hq : q = 2 ^ n) (hm : m ≤ n)
    (h : 2 * q ^ 5 ≤ 2 * q ^ 4 * m) : False := by
  have hlt : n < q := by rw [hq]; exact sixFF_ff9_aux_lt_two_pow n
  have hmq : m < q := lt_of_le_of_lt hm hlt
  have hqpos : 0 < q := lt_of_le_of_lt (Nat.zero_le n) hlt
  have hq4 : 0 < q ^ 4 := pow_pos hqpos 4
  have h1 : q ^ 4 * m < q ^ 4 * q := mul_lt_mul_of_pos_left hmq hq4
  have h2 : q ^ 5 = q ^ 4 * q := by ring
  nlinarith

theorem sixFF_ff9_aux_two_mul_le {G : Type} [Group G] [Finite G] (S A : Subgroup G) (t : G)
    (hAS : A ≤ S) (htS : t ∉ S) :
    2 * Nat.card A ≤ Nat.card ↥(A ⊔ Subgroup.zpowers t) := by
  have key : ∀ x ∈ S, ∀ y ∈ S, x = y * t → False := by
    intro x hx y hy h
    apply htS
    have h' : y⁻¹ * x = t := by rw [h]; group
    rw [← h']
    exact S.mul_mem (S.inv_mem hy) hx
  let f : A × Fin 2 → ↥(A ⊔ Subgroup.zpowers t) := fun p =>
    ⟨(p.1 : G) * t ^ (p.2 : ℕ), (A ⊔ Subgroup.zpowers t).mul_mem
      (Subgroup.mem_sup_left p.1.2)
      (pow_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers t)) _)⟩
  have hf : Function.Injective f := by
    rintro ⟨a, ⟨j, hj⟩⟩ ⟨b, ⟨k, hk⟩⟩ hab
    have hab' : (a : G) * t ^ j = (b : G) * t ^ k := congrArg Subtype.val hab
    interval_cases j <;> interval_cases k
    · have e : a = b := Subtype.ext (by simpa using hab')
      subst e
      rfl
    · exact (key _ (hAS a.2) _ (hAS b.2) (by simpa using hab')).elim
    · exact (key _ (hAS b.2) _ (hAS a.2) (by simpa using hab'.symm)).elim
    · have h2 : (a : G) * t = (b : G) * t := by simpa using hab'
      have e : a = b := Subtype.ext (mul_right_cancel h2)
      subst e
      rfl
  have hle := Nat.card_le_card_of_injective f hf
  have hcp : Nat.card (↥A × Fin 2) = Nat.card ↥A * 2 := by
    rw [Nat.card_prod]
    simp
  rw [hcp] at hle
  omega

theorem sixFF_ff9_aux_map_pgroup {G : Type} [Group G] (k : G) (Z : Subgroup G)
    (hZ : IsPGroup 2 Z) : IsPGroup 2 (Z.map (MulAut.conj k).toMonoidHom) := by
  intro x
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp x.2
  obtain ⟨m, hm⟩ := hZ ⟨y, hy⟩
  have hm' : y ^ 2 ^ m = 1 := by
    have h := congrArg Subtype.val hm
    simpa using h
  refine ⟨m, Subtype.ext ?_⟩
  rw [Subgroup.coe_pow, Subgroup.coe_one, ← hyx, ← map_pow, hm', map_one]

theorem sixFF_ff9_aux_map_centralizer {G : Type} [Group G] (x v₀ t : G)
    (hxv : x * v₀ * x⁻¹ = t) (R : Subgroup G)
    (hR : R ≤ Subgroup.centralizer ({v₀} : Set G)) :
    R.map (MulAut.conj x).toMonoidHom ≤ Subgroup.centralizer ({t} : Set G) := by
  intro y hy
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
  have hzv : z * v₀ = v₀ * z := mem_centralizer_singleton_iff.mp (hR hz)
  rw [mem_centralizer_singleton_iff]
  change x * z * x⁻¹ * t = t * (x * z * x⁻¹)
  rw [← hxv]
  calc x * z * x⁻¹ * (x * v₀ * x⁻¹) = x * (z * v₀) * x⁻¹ := by group
    _ = x * (v₀ * z) * x⁻¹ := by rw [hzv]
    _ = x * v₀ * x⁻¹ * (x * z * x⁻¹) := by group

section Steps

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {L : Subgroup G} {K : Type} [Field K]
  [CharP K 2] [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G} {i : Axis}

theorem sixFF_ff9
    (hS : SCSetting L K n φ t i) (hH : SixHConclusion φ t i) (hE : EmbConclusion φ t i)
    (hK : SixKConclusion φ t i) (f5 : FF5Concl n φ t) (f6 : FF6Concl n φ t i)
    (f7 : FF7Concl φ t i) (f8 : FF8Concl n φ t i) : ∀ g : G, g⁻¹ * t * g ∈ normalizer (Tplus φ t i : Set G) → g⁻¹ * t * g ∈ Tplus φ t i := by
  intro g hg
  by_contra hcon
  have ht2 : orderOf t = 2 := hS.fc.setup.order_t
  have htt : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [ht2, pow_two] at h
    exact h
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht2
    norm_num at ht2
  have htS : t ∉ S φ t i := by
    intro htS
    have h : t ∈ S φ t i ⊓ Subgroup.zpowers t :=
      Subgroup.mem_inf.mpr ⟨htS, Subgroup.mem_zpowers t⟩
    rw [hH.inf_t, Subgroup.mem_bot] at h
    exact ht1 h
  have hSle : S φ t i ≤ Tplus φ t i := by
    rw [← hH.sup_t]
    exact le_sup_left
  have htT : t ∈ Tplus φ t i := by
    rw [← hH.sup_t]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hT2 : IsPGroup 2 (Tplus φ t i) := hH.isPGroup_Tplus
  have hcardK : Nat.card K = 2 ^ n := hS.fc.setup.card_K
  have hn2 : 2 ≤ n := hS.fc.setup.two_le
  have hn0 : n ≠ 0 := by omega
  obtain ⟨-, f7L, f7EA, -, -, -, -, -, -⟩ := f7
  have hNormI : ∀ k : Fin 6,
      ((ffSeries φ t i k.castSucc).subgroupOf (ffSeries φ t i k.succ)).Normal :=
    fun k => (f7EA k).elim fun hN _ => hN
  have hEAI : ∀ k : Fin 6, IsElementaryAbelian 2 (↥(ffSeries φ t i k.succ) ⧸
      (ffSeries φ t i k.castSucc).subgroupOf (ffSeries φ t i k.succ)) :=
    fun k => (f7EA k).elim fun _ h => h
  obtain ⟨u, hu⟩ : ∃ u : G, u = g⁻¹ * t * g := ⟨_, rfl⟩
  rw [← hu] at hg hcon
  have huu1 : u * u = 1 := by
    rw [hu]
    calc g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
      _ = 1 := by rw [htt]; group
  have huS : u * u ∈ S φ t i := by
    rw [huu1]
    exact (S φ t i).one_mem
  have hu1 : u ≠ 1 := by
    intro h
    apply hcon
    rw [h]
    exact (Tplus φ t i).one_mem
  obtain ⟨hEven, v, d, -, -, hvv, hv1, -, hFr, hcl, hw⟩ := f6 u hg hcon huS
  have hv0sq : d⁻¹ * v * d * (d⁻¹ * v * d) = 1 := by
    calc d⁻¹ * v * d * (d⁻¹ * v * d) = d⁻¹ * (v * v) * d := by group
      _ = 1 := by rw [hvv]; group
  have hv0ne : d⁻¹ * v * d ≠ 1 := by
    intro h
    apply hv1
    calc v = d * (d⁻¹ * v * d) * d⁻¹ := by group
      _ = 1 := by rw [h]; group
  have hv0ord : orderOf (d⁻¹ * v * d) = 2 := by
    apply orderOf_eq_prime
    · rw [pow_two]
      exact hv0sq
    · exact hv0ne
  have hv0C : d⁻¹ * v * d ∈ centralizer ({t} : Set G) :=
    (hcl (d⁻¹ * v * d) (Set.mem_insert_of_mem _ (Set.mem_singleton _))).2.2.1
  obtain ⟨hNorm, hcardC⟩ := f8 (d⁻¹ * v * d) hv0sq hv0C hFr hEven
  have hcoset := CFSG.LocalAnalysis.EvenBN.Common.involution_coset_eq_conj_orbit_of_card_sq
    (W := S φ t i) (a := d⁻¹ * v * d) (r := 6) hv0ord (ffSeries φ t i) rfl rfl f7L hNorm hcardC
  have hu'sq : d⁻¹ * u * d * (d⁻¹ * u * d) = 1 := by
    calc d⁻¹ * u * d * (d⁻¹ * u * d) = d⁻¹ * (u * u) * d := by group
      _ = 1 := by rw [huu1]; group
  have hu'ne : d⁻¹ * u * d ≠ 1 := by
    intro h
    apply hu1
    calc u = d * (d⁻¹ * u * d) * d⁻¹ := by group
      _ = 1 := by rw [h]; group
  have hu'ord : orderOf (d⁻¹ * u * d) = 2 := by
    apply orderOf_eq_prime
    · rw [pow_two]
      exact hu'sq
    · exact hu'ne
  have hmem : d⁻¹ * u * d ∈
      {x : G | (∃ w ∈ S φ t i, x = d⁻¹ * v * d * w) ∧ orderOf x = 2} := by
    rw [Set.mem_setOf_eq]
    exact ⟨⟨((d⁻¹ * u * d)⁻¹ * (d⁻¹ * v * d))⁻¹, (S φ t i).inv_mem hw, by group⟩, hu'ord⟩
  have hmem' := (Set.ext_iff.mp hcoset (d⁻¹ * u * d)).mp hmem
  rw [Set.mem_setOf_eq] at hmem'
  obtain ⟨m, hmS, hm⟩ := hmem'
  have hv0' : d⁻¹ * v * d = m * (d⁻¹ * u * d) * m⁻¹ := by
    rw [hm]
    group
  have hxv : g * d * m⁻¹ * (d⁻¹ * v * d) * (g * d * m⁻¹)⁻¹ = t := by
    rw [hv0', hu]
    group
  have hv0t : t ∈ centralizer ({d⁻¹ * v * d} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp hv0C).symm
  have hA : Nat.card ↥(S φ t i ⊓ centralizer ({d⁻¹ * v * d} : Set G)) = Nat.card K ^ 5 := by
    have hc5 : Nat.card ↥(S φ t i ⊓ centralizer ({d⁻¹ * v * d} : Set G)) ^ 2 =
        Nat.card ↥(S φ t i) := hcardC 5
    apply sixFF_ff9_aux_sq_inj
    rw [hc5, hH.card_S]
    ring
  have hAS : S φ t i ⊓ centralizer ({d⁻¹ * v * d} : Set G) ≤ S φ t i := inf_le_left
  have hAT : S φ t i ⊓ centralizer ({d⁻¹ * v * d} : Set G) ≤ Tplus φ t i :=
    inf_le_left.trans hSle
  have hR0C : (S φ t i ⊓ centralizer ({d⁻¹ * v * d} : Set G)) ⊔ Subgroup.zpowers t ≤
      centralizer ({d⁻¹ * v * d} : Set G) :=
    sup_le inf_le_right (Subgroup.zpowers_le.mpr hv0t)
  have hR0P : IsPGroup 2 ↥((S φ t i ⊓ centralizer ({d⁻¹ * v * d} : Set G)) ⊔
      Subgroup.zpowers t) :=
    IsPGroup.to_le hT2 (sup_le hAT (Subgroup.zpowers_le.mpr htT))
  have hAR0 := sixFF_ff9_aux_two_mul_le (S φ t i)
    (S φ t i ⊓ centralizer ({d⁻¹ * v * d} : Set G)) t hAS htS
  have hRcard : Nat.card ↥(((S φ t i ⊓ centralizer ({d⁻¹ * v * d} : Set G)) ⊔
      Subgroup.zpowers t).map (MulAut.conj (g * d * m⁻¹)).toMonoidHom) =
      Nat.card ↥((S φ t i ⊓ centralizer ({d⁻¹ * v * d} : Set G)) ⊔ Subgroup.zpowers t) :=
    Subgroup.card_map_of_injective (MulAut.conj (g * d * m⁻¹)).injective
  have hR1C := sixFF_ff9_aux_map_centralizer (g * d * m⁻¹) (d⁻¹ * v * d) t hxv _ hR0C
  have hR1P := sixFF_ff9_aux_map_pgroup (g * d * m⁻¹) _ hR0P
  have hfR1 := f5 _ hR1P hR1C
  have hbig : 2 * Nat.card K ^ 5 ≤ 2 * Nat.card K ^ 4 * 2 ^ (n.factorization 2) := by
    have h1 := hAR0
    rw [hA] at h1
    have h2 := hfR1
    rw [hRcard] at h2
    exact h1.trans h2
  exact sixFF_ff9_aux_arith (Nat.card K) (2 ^ (n.factorization 2)) n hcardK
    (Nat.ordProj_le 2 hn0) hbig

end Steps

end SingleCommParts

end CFSG.LocalAnalysis.SymplecticFourStandard
