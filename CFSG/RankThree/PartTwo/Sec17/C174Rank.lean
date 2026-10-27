module

public import CFSG.GH74.GLS.Stage1.Thm6.Lift
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.GroupTheory.CyclicSylowNormalOddComplement
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.UniquenessCase.UC1K31
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear

public section

namespace CFSG.RankThree.PartTwo.Sec17.C174

open CFSG CFSG.Open

theorem a1_isElemAbelian_map {H K : Type*} [Group H] [Group K] {p : ℕ} {S : Subgroup H}
    (hS : IsElemAbelian p S) (f : H →* K) : IsElemAbelian p (S.map f) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · rcases a with ⟨a, ha⟩
    rcases b with ⟨b, hb⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hb
    apply Subtype.ext
    show f x * f y = f y * f x
    rw [← map_mul, ← map_mul, hS.comm hx hy]
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    rw [← map_pow, hS.2 y hy, map_one]

theorem a1_card_map_eq {H K : Type*} [Group H] [Group K] (f : H →* K) (S : Subgroup H)
    (hS : S ⊓ f.ker = ⊥) : Nat.card (S.map f) = Nat.card S := by
  have hinj : Function.Injective (f.comp S.subtype) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h : (a : H) ∈ S ⊓ f.ker := ⟨a.2, MonoidHom.mem_ker.mpr ha⟩
    rw [hS, Subgroup.mem_bot] at h
    exact Subtype.ext h
  have hmap : (⊤ : Subgroup S).map (f.comp S.subtype) = S.map f := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.mp hx
      exact Subgroup.mem_map.mpr ⟨y, y.2, rfl⟩
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      exact Subgroup.mem_map.mpr ⟨⟨y, hy⟩, Subgroup.mem_top _, rfl⟩
  rw [← hmap, Subgroup.card_map_of_injective hinj, Subgroup.card_top]

theorem a1_inf_eq_bot {G : Type*} [Group G] [Finite G] {r : ℕ} [Fact r.Prime]
    {Q S : Subgroup G} (hQr : ¬ r ∣ Nat.card Q) (hS : ∀ x ∈ S, x ^ r = 1) : S ⊓ Q = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxS, hxQ⟩
  rw [Subgroup.mem_bot]
  have hdvd : orderOf x ∣ r := orderOf_dvd_of_pow_eq_one (hS x hxS)
  have hr : r.Prime := Fact.out
  rcases (Nat.dvd_prime hr).mp hdvd with h1 | h1
  · exact orderOf_eq_one_iff.mp h1
  · exfalso
    apply hQr
    have h2 : orderOf (⟨x, hxQ⟩ : Q) = r := (Subgroup.orderOf_coe _).symm.trans h1
    rw [← h2]
    exact orderOf_dvd_natCard _

theorem a1_core {G : Type*} [Group G] [Finite G] {r : ℕ} [Fact r.Prime]
    {Q C E F P : Subgroup G} (hQr : ¬ r ∣ Nat.card Q) (hQC : Q ≤ C) (hEC : E ≤ C)
    (hFC : F ⊓ C = ⊥) (hE : IsElemAbelian r E) (hF : IsElemAbelian r F)
    (hEP : E ≤ P) (hFP : F ≤ P) (hQP : Q ≤ P) (hPN : P ≤ Subgroup.normalizer (Q : Set G))
    (hcomm : ∀ e ∈ E, ∀ f ∈ F, e * f * e⁻¹ * f⁻¹ ∈ Q) :
    ∃ R : Subgroup G, R ≤ P ∧ IsElemAbelian r R ∧ Nat.card E * Nat.card F = Nat.card R := by
  haveI hQ'N : (Q.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQP).mpr hPN
  have hEQ : E ⊓ Q = ⊥ := a1_inf_eq_bot hQr (fun x hx => hE.2 x hx)
  have hFQ : F ⊓ Q = ⊥ := a1_inf_eq_bot hQr (fun x hx => hF.2 x hx)
  obtain ⟨ψ, hψ⟩ : ∃ ψ : P →* P ⧸ Q.subgroupOf P, ψ = QuotientGroup.mk' (Q.subgroupOf P) :=
    ⟨_, rfl⟩
  have hker : ψ.ker = Q.subgroupOf P := by
    rw [hψ]
    exact QuotientGroup.ker_mk' _
  have hψQ : ∀ x : P, ψ x = 1 ↔ x ∈ Q.subgroupOf P := by
    intro x
    rw [← MonoidHom.mem_ker, hker]
  have hψmk : ∀ x : P, ψ x = (x : P ⧸ Q.subgroupOf P) := by
    intro x
    rw [hψ]
    rfl
  have hEker : E.subgroupOf P ⊓ ψ.ker = ⊥ := by
    rw [hker, eq_bot_iff]
    rintro x ⟨hxE, hxQ⟩
    have h : (x : G) ∈ E ⊓ Q :=
      ⟨Subgroup.mem_subgroupOf.mp hxE, Subgroup.mem_subgroupOf.mp hxQ⟩
    rw [hEQ, Subgroup.mem_bot] at h
    rw [Subgroup.mem_bot]
    exact Subtype.ext h
  have hFker : F.subgroupOf P ⊓ ψ.ker = ⊥ := by
    rw [hker, eq_bot_iff]
    rintro x ⟨hxF, hxQ⟩
    have h : (x : G) ∈ F ⊓ Q :=
      ⟨Subgroup.mem_subgroupOf.mp hxF, Subgroup.mem_subgroupOf.mp hxQ⟩
    rw [hFQ, Subgroup.mem_bot] at h
    rw [Subgroup.mem_bot]
    exact Subtype.ext h
  obtain ⟨Eb, hEb⟩ : ∃ Eb : Subgroup (P ⧸ Q.subgroupOf P), Eb = (E.subgroupOf P).map ψ :=
    ⟨_, rfl⟩
  obtain ⟨Fb, hFb⟩ : ∃ Fb : Subgroup (P ⧸ Q.subgroupOf P), Fb = (F.subgroupOf P).map ψ :=
    ⟨_, rfl⟩
  have hEbcard : Nat.card Eb = Nat.card E := by
    rw [hEb, a1_card_map_eq ψ (E.subgroupOf P) hEker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEP).toEquiv
  have hFbcard : Nat.card Fb = Nat.card F := by
    rw [hFb, a1_card_map_eq ψ (F.subgroupOf P) hFker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFP).toEquiv
  have hEbel : IsElemAbelian r Eb := by
    rw [hEb]
    exact a1_isElemAbelian_map (hE.comap P.subtype_injective) ψ
  have hFbel : IsElemAbelian r Fb := by
    rw [hFb]
    exact a1_isElemAbelian_map (hF.comap P.subtype_injective) ψ
  have hcommb : ∀ a ∈ Eb, ∀ b ∈ Fb, a * b = b * a := by
    intro a ha b hb
    rw [hEb] at ha
    rw [hFb] at hb
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hb
    rw [← map_mul, ← map_mul, hψmk, hψmk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    show ((x : G) * (y : G))⁻¹ * ((y : G) * (x : G)) ∈ Q
    have key : ((x : G) * (y : G))⁻¹ * ((y : G) * (x : G)) =
        ((x : G)⁻¹ * (y : G)⁻¹ * ((x : G)⁻¹)⁻¹ * ((y : G)⁻¹)⁻¹)⁻¹ := by
      group
    rw [key]
    exact Q.inv_mem (hcomm (x : G)⁻¹ (E.inv_mem (Subgroup.mem_subgroupOf.mp hx))
      (y : G)⁻¹ (F.inv_mem (Subgroup.mem_subgroupOf.mp hy)))
  have hbot : Eb ⊓ Fb = ⊥ := by
    rw [eq_bot_iff]
    rintro a ⟨ha, hb⟩
    rw [hEb] at ha
    rw [hFb] at hb
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp hb
    have hxy' : (x : P)⁻¹ * y ∈ Q.subgroupOf P := by
      rw [← hψQ, map_mul, map_inv, hxy, inv_mul_cancel]
    have h2 : (x : G)⁻¹ * (y : G) ∈ Q := by
      have h3 := Subgroup.mem_subgroupOf.mp hxy'
      simpa using h3
    have hyC : (y : G) ∈ C := by
      have h4 := C.mul_mem (hEC (Subgroup.mem_subgroupOf.mp hx)) (hQC h2)
      simpa using h4
    have hy1 : (y : G) = 1 := by
      have hyF : (y : G) ∈ F ⊓ C := ⟨Subgroup.mem_subgroupOf.mp hy, hyC⟩
      rw [hFC, Subgroup.mem_bot] at hyF
      exact hyF
    have hy1' : y = 1 := Subtype.ext hy1
    rw [Subgroup.mem_bot]
    rw [hy1', map_one] at hxy
    exact hxy.symm
  have hsup_el : IsElemAbelian r (Eb ⊔ Fb) := IsElemAbelian.sup_of_commute hEbel hFbel hcommb
  have hsupcard : Nat.card ↥(Eb ⊔ Fb) = Nat.card E * Nat.card F := by
    obtain ⟨h1, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute Eb Fb hcommb
    rw [hbot, Subgroup.card_bot, mul_one, hEbcard, hFbcard] at h1
    exact h1
  have hPG : IsPGroup r ↥(Eb ⊔ Fb) := by
    refine fun g => ⟨1, ?_⟩
    rw [pow_one]
    exact Subtype.ext (by simpa using hsup_el.2 _ g.2)
  have hr' : ¬ r ∣ Nat.card (Q.subgroupOf P) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQP).toEquiv]
    exact hQr
  obtain ⟨A, -, hAmap, hAinf⟩ :=
    CFSG.GH74.GLS.Stage1.Thm6.exists_lift_pSubgroup (Q.subgroupOf P) hr' (Eb ⊔ Fb) hPG
  have hAmap' : A.map ψ = Eb ⊔ Fb := by
    rw [hψ]
    exact hAmap
  have hAker : A ⊓ ψ.ker = ⊥ := by
    rw [hker]
    exact hAinf
  have hAcard : Nat.card A = Nat.card ↥(Eb ⊔ Fb) := by
    rw [← hAmap', a1_card_map_eq ψ A hAker]
  have hmemA : ∀ x ∈ A, ψ x ∈ Eb ⊔ Fb := by
    intro x hx
    rw [← hAmap']
    exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  have hA_el : IsElemAbelian r A := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      have hc : ψ (a : P) * ψ (b : P) = ψ (b : P) * ψ (a : P) :=
        hsup_el.comm (hmemA _ a.2) (hmemA _ b.2)
      have hmem : ((b : P) * (a : P))⁻¹ * ((a : P) * (b : P)) ∈ A ⊓ Q.subgroupOf P := by
        rw [Subgroup.mem_inf]
        refine ⟨A.mul_mem (A.inv_mem (A.mul_mem b.2 a.2)) (A.mul_mem a.2 b.2), ?_⟩
        rw [← hψQ]
        simp only [map_mul, map_inv]
        rw [hc, inv_mul_cancel]
      rw [hAinf, Subgroup.mem_bot] at hmem
      exact (inv_mul_eq_one.mp hmem).symm
    · have hpow : x ^ r ∈ A ⊓ Q.subgroupOf P := by
        rw [Subgroup.mem_inf]
        refine ⟨A.pow_mem hx r, ?_⟩
        rw [← hψQ, map_pow]
        exact hsup_el.2 _ (hmemA x hx)
      rw [hAinf, Subgroup.mem_bot] at hpow
      exact hpow
  refine ⟨A.map P.subtype, Subgroup.map_subtype_le A, a1_isElemAbelian_map hA_el P.subtype, ?_⟩
  rw [Subgroup.card_map_of_injective P.subtype_injective, hAcard, hsupcard]

theorem exists_isElemAbelian_card_le_of_commute_mod
    {G : Type*} [Group G] [Finite G] {r : ℕ} [Fact r.Prime]
    {Q C E F : Subgroup G} (hQr : ¬ r ∣ Nat.card Q) (hQC : Q ≤ C)
    (hEC : E ≤ C) (hFC : F ⊓ C = ⊥) (hE : IsElemAbelian r E) (hF : IsElemAbelian r F)
    (hQE : E ≤ Subgroup.normalizer (Q : Set G)) (hQF : F ≤ Subgroup.normalizer (Q : Set G))
    (hcomm : ∀ e ∈ E, ∀ f ∈ F, e * f * e⁻¹ * f⁻¹ ∈ Q) :
    ∃ R : Subgroup G, R ≤ E ⊔ F ⊔ Q ∧ IsElemAbelian r R ∧
      Nat.card E * Nat.card F ≤ Nat.card R := by
  obtain ⟨R, hRP, hR, hcard⟩ := a1_core (P := E ⊔ F ⊔ Q) hQr hQC hEC hFC hE hF
    (le_trans le_sup_left le_sup_left) (le_trans le_sup_right le_sup_left) le_sup_right
    (sup_le (sup_le hQE hQF) Subgroup.le_normalizer) hcomm
  exact ⟨R, hRP, hR, hcard.le⟩


theorem pow_dvd_sub_one_of_pow_dvd_pow_sub_one {p : ℕ} [hp : Fact p.Prime] {a : ℤ} {q j : ℕ}
    (ha : (p : ℤ) ∣ a - 1) (hq : ¬ p ∣ q) (hpow : (p : ℤ) ^ j ∣ a ^ q - 1) :
    (p : ℤ) ^ j ∣ a - 1 := by
  have hS : ∀ m : ℕ, (p : ℤ) ∣ (∑ i ∈ Finset.range m, a ^ i) - (m : ℤ) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have h1 : (p : ℤ) ∣ a ^ m - 1 := by
        simpa using dvd_trans ha (sub_dvd_pow_sub_pow a 1 m)
      have h2 : (∑ i ∈ Finset.range (m + 1), a ^ i) - ((m + 1 : ℕ) : ℤ)
          = ((∑ i ∈ Finset.range m, a ^ i) - (m : ℤ)) + (a ^ m - 1) := by
        rw [Finset.sum_range_succ]
        push_cast
        ring
      rw [h2]
      exact dvd_add ih h1
  have hfac : a ^ q - 1 = (∑ i ∈ Finset.range q, a ^ i) * (a - 1) :=
    (geom_sum_mul a q).symm
  have hnd : ¬ (p : ℤ) ∣ ∑ i ∈ Finset.range q, a ^ i := by
    intro h
    apply hq
    have h2 : (p : ℤ) ∣ (q : ℤ) := by
      have h3 := dvd_sub h (hS q)
      rwa [sub_sub_cancel] at h3
    exact Int.natCast_dvd_natCast.mp h2
  have hprime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have hcop : IsCoprime ((p : ℤ) ^ j) (∑ i ∈ Finset.range q, a ^ i) :=
    IsCoprime.pow_left ((Prime.coprime_iff_not_dvd hprime).mpr hnd)
  rw [hfac] at hpow
  exact hcop.dvd_of_dvd_mul_left hpow

theorem normalizer_le_centralizer_of_cyclic_sylow
    {D : Type*} [Group D] [Finite D] {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (P : Sylow p D) (hP : IsCyclic (P : Subgroup D)) {z : D} (hzP : z ∈ (P : Subgroup D))
    (hzp : orderOf z = p) (hzc : ∀ g : D, g * z = z * g) :
    Subgroup.normalizer ((P : Subgroup D) : Set D) ≤ Subgroup.centralizer ((P : Subgroup D) : Set D) := by
  obtain ⟨x, hxP, hPx⟩ : ∃ x : D, x ∈ (P : Subgroup D) ∧
      ∀ y ∈ (P : Subgroup D), ∃ i : ℤ, x ^ i = y := by
    obtain ⟨g, hg⟩ : ∃ g : (P : Subgroup D), ∀ w : (P : Subgroup D),
        w ∈ Subgroup.zpowers g := IsCyclic.exists_generator
    refine ⟨(g : D), g.2, fun y hy => ?_⟩
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨y, hy⟩)
    exact ⟨i, congrArg Subtype.val hi⟩
  obtain ⟨j, hj⟩ : ∃ j : ℕ, orderOf x = p ^ j := by
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨x, hxP⟩
    have hk' : x ^ (p ^ k) = 1 := congrArg Subtype.val hk
    obtain ⟨j, -, hj⟩ :=
      (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp (orderOf_dvd_of_pow_eq_one hk')
    exact ⟨j, hj⟩
  have hPN : (P : Subgroup D) ≤ Subgroup.normalizer ((P : Subgroup D) : Set D) :=
    Subgroup.le_normalizer
  have hrel : ¬ p ∣ (P : Subgroup D).relIndex (Subgroup.normalizer ((P : Subgroup D) : Set D)) := by
    intro hdvd
    apply Sylow.not_dvd_index P
    exact dvd_trans hdvd (Dvd.intro _ (Subgroup.relIndex_mul_index hPN))
  have hpowN : ∀ m ∈ Subgroup.normalizer ((P : Subgroup D) : Set D),
      m ^ (P : Subgroup D).relIndex (Subgroup.normalizer ((P : Subgroup D) : Set D)) ∈
        (P : Subgroup D) := by
    intro m hm
    have h := Subgroup.pow_index_mem
      ((P : Subgroup D).subgroupOf (Subgroup.normalizer ((P : Subgroup D) : Set D))) ⟨m, hm⟩
    have h2 := Subgroup.mem_subgroupOf.mp h
    simpa [Subgroup.relIndex] using h2
  set q := (P : Subgroup D).relIndex (Subgroup.normalizer ((P : Subgroup D) : Set D)) with hqdef
  intro n hn
  have hnx : n * x * n⁻¹ ∈ (P : Subgroup D) := (Subgroup.mem_normalizer_iff.mp hn x).mp hxP
  obtain ⟨a, ha⟩ := hPx _ hnx
  have hconj : ∀ c : ℤ, n * x ^ c * n⁻¹ = (n * x * n⁻¹) ^ c := fun c => conj_zpow.symm
  obtain ⟨c, hc⟩ := hPx z hzP
  have hzpow : n * z * n⁻¹ = z ^ a := by
    rw [← hc, hconj, ← ha, ← zpow_mul, ← zpow_mul, mul_comm]
  have hzfix : n * z * n⁻¹ = z := by
    rw [hzc n]
    simp
  have hza : ((orderOf z : ℕ) : ℤ) ∣ a - 1 := by
    rw [orderOf_dvd_iff_zpow_eq_one, zpow_sub_one, ← hzpow, hzfix, mul_inv_cancel]
  rw [hzp] at hza
  have hiter : ∀ m : ℕ, n ^ m * x * (n ^ m)⁻¹ = x ^ (a ^ m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have e1 : n ^ (m + 1) * x * (n ^ (m + 1))⁻¹ = n * (n ^ m * x * (n ^ m)⁻¹) * n⁻¹ := by
        rw [pow_succ']
        group
      rw [e1, ih, hconj, ← ha, ← zpow_mul]
      congr 1
      ring
  obtain ⟨t, ht⟩ := hPx _ (hpowN n hn)
  have hcomm : n ^ q * x * (n ^ q)⁻¹ = x := by
    rw [← ht]
    group
  have hxaq : x ^ (a ^ q) = x := by
    rw [← hiter q, hcomm]
  have hdvd1 : ((orderOf x : ℕ) : ℤ) ∣ a ^ q - 1 := by
    rw [orderOf_dvd_iff_zpow_eq_one, zpow_sub_one, hxaq, mul_inv_cancel]
  rw [hj] at hdvd1
  have hdvd2 : (p : ℤ) ^ j ∣ a - 1 := by
    apply pow_dvd_sub_one_of_pow_dvd_pow_sub_one hza hrel
    exact_mod_cast hdvd1
  have hxa : x ^ (a - 1) = 1 := by
    apply orderOf_dvd_iff_zpow_eq_one.mp
    rw [hj]
    exact_mod_cast hdvd2
  rw [zpow_sub_one] at hxa
  have hxa2 : x ^ a = x := mul_inv_eq_one.mp hxa
  have hxa' : n * x * n⁻¹ = x := by
    rw [← ha, hxa2]
  have hcommx : n * x = x * n := mul_inv_eq_iff_eq_mul.mp hxa'
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  obtain ⟨e, rfl⟩ := hPx h hh
  exact ((show Commute x n from hcommx.symm).zpow_left e).eq

theorem isSolvable_core_central_order_three
    {Γ : Type*} [Group Γ] [Finite Γ] (hO : CFSG.pPrimeCore 3 Γ = ⊥)
    {D₀ : Subgroup Γ} (hD₀N : D₀.Normal) {z : Γ} (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1)
    (hzD₀ : z ∈ D₀) (hzc : ∀ g ∈ D₀, g * z = z * g) (hrk : CFSG.Open.pRank 3 D₀ ≤ 1) :
    Group.IsSolvable D₀ := by
  have hz : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  let z' : D₀ := ⟨z, hzD₀⟩
  have hz'o : orderOf z' = 3 := by
    rw [Subgroup.orderOf_mk z hzD₀]
    exact hz
  have hz'c : ∀ g : D₀, g * z' = z' * g := fun g => Subtype.ext (hzc g.1 g.2)
  have hzs : IsPGroup 3 (Subgroup.zpowers z') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz'o, pow_one])
  obtain ⟨P, hPz⟩ := IsPGroup.exists_le_sylow hzs
  have hz'P : z' ∈ (P : Subgroup D₀) := hPz (Subgroup.mem_zpowers z')
  have hPrk : CFSG.Open.pRank 3 (P : Subgroup D₀) ≤ 1 := by
    calc CFSG.Open.pRank 3 (P : Subgroup D₀)
        ≤ CFSG.Open.pRank 3 ((P : Subgroup D₀).map D₀.subtype) :=
          CFSG.SectionRank.pRank_le_map (by norm_num) D₀.subtype D₀.subtype_injective _
      _ ≤ CFSG.Open.pRank 3 D₀ :=
          CFSG.SectionRank.pRank_mono (by norm_num) (Subgroup.map_subtype_le _)
      _ ≤ 1 := hrk
  have hPcyc : IsCyclic (P : Subgroup D₀) :=
    CFSG.LocalAnalysis.UniquenessCase.UCK.K31.isCyclic_of_pRank_le_one Nat.prime_three
      (by norm_num) P.isPGroup' hPrk
  have hnorm := normalizer_le_centralizer_of_cyclic_sylow (D := ↥D₀) (p := 3) (by norm_num) P
    hPcyc hz'P hz'o hz'c
  have hcomp := MonoidHom.ker_transferSylow_isComplement' P hnorm
  have hcard3 := MonoidHom.not_dvd_card_ker_transferSylow P hnorm
  set φ := MonoidHom.transferSylow P hnorm with hφ
  have hKcop : Nat.Coprime 3 (Nat.card φ.ker) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hcard3
  have hB : ∀ x : D₀, Nat.Coprime 3 (orderOf x) → x ∈ φ.ker := by
    intro x hx
    have h1 : orderOf (φ x) ∣ orderOf x := orderOf_map_dvd φ x
    have h2 : Nat.Coprime (orderOf (φ x)) 3 := Nat.Coprime.coprime_dvd_left h1 hx.symm
    obtain ⟨k, hk⟩ := P.isPGroup' (φ x)
    have h3 : orderOf (φ x) ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk
    have h4 : orderOf (φ x) = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right k h2) h3
    exact MonoidHom.mem_ker.mpr (orderOf_eq_one_iff.mp h4)
  have hK'N : (φ.ker.map D₀.subtype).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hn
    have hconj : g * (k : Γ) * g⁻¹ ∈ D₀ := hD₀N.conj_mem (k : Γ) k.2 g
    have hord : orderOf (⟨g * (k : Γ) * g⁻¹, hconj⟩ : D₀) = orderOf k := by
      have h1 := Subgroup.orderOf_coe (⟨g * (k : Γ) * g⁻¹, hconj⟩ : D₀)
      have h2 : orderOf (g * (k : Γ) * g⁻¹) = orderOf (k : Γ) :=
        orderOf_injective (MulAut.conj g).toMonoidHom (MulEquiv.injective _) (k : Γ)
      have h3 := Subgroup.orderOf_coe k
      rw [← h1, ← h3]
      exact h2
    have hkdvd : orderOf k ∣ Nat.card φ.ker := by
      rw [← Subgroup.orderOf_mk k hk]
      exact orderOf_dvd_natCard _
    have hcopk : Nat.Coprime 3 (orderOf (⟨g * (k : Γ) * g⁻¹, hconj⟩ : D₀)) := by
      rw [hord]
      exact Nat.Coprime.coprime_dvd_right hkdvd hKcop
    exact Subgroup.mem_map.mpr ⟨⟨g * (k : Γ) * g⁻¹, hconj⟩, hB _ hcopk, rfl⟩
  have hK'card : Nat.card (φ.ker.map D₀.subtype) = Nat.card φ.ker :=
    Subgroup.card_map_of_injective D₀.subtype_injective
  have hK'le : φ.ker.map D₀.subtype ≤ CFSG.pPrimeCore 3 Γ :=
    CFSG.le_pPrimeCore_of_normal_coprime hK'N (by rw [hK'card]; exact hKcop)
  rw [hO, le_bot_iff] at hK'le
  have hKone : Nat.card φ.ker = 1 := by
    rw [← hK'card, hK'le, Subgroup.card_bot]
  have hTcard : Nat.card D₀ = Nat.card (P : Subgroup D₀) := by
    have h := hcomp.card_mul_card
    rw [hKone, one_mul] at h
    exact h.symm
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp P.isPGroup'
  have hT3 : IsPGroup 3 D₀ := IsPGroup.of_card (n := n) (hTcard.trans hn)
  haveI := hT3.isNilpotent
  infer_instance

theorem isSolvable_of_normal_pRank_le_one
    {Γ : Type*} [Group Γ] [Finite Γ] (hO : CFSG.pPrimeCore 3 Γ = ⊥)
    {z : Γ} (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) (hzN : (Subgroup.zpowers z).Normal)
    {D : Subgroup Γ} (hDN : D.Normal) (hzD : z ∈ D) (hrk : CFSG.Open.pRank 3 D ≤ 1) :
    Group.IsSolvable D := by
  obtain ⟨D₀, hD₀⟩ : ∃ D₀ : Subgroup Γ,
      D₀ = D ⊓ Subgroup.centralizer ((Subgroup.zpowers z : Subgroup Γ) : Set Γ) := ⟨_, rfl⟩
  have hD₀N : D₀.Normal := by rw [hD₀]; infer_instance
  have hmem : ∀ g : Γ, g ∈ D₀ ↔ g ∈ D ∧ ∀ h ∈ Subgroup.zpowers z, h * g = g * h := by
    intro g
    rw [hD₀, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    exact Iff.rfl
  have hD₀D : D₀ ≤ D := fun g hg => ((hmem g).mp hg).1
  have hzD₀ : z ∈ D₀ := (hmem z).mpr ⟨hzD, fun h hh => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact ((Commute.refl z).zpow_left k).eq⟩
  have hzc : ∀ g ∈ D₀, g * z = z * g := fun g hg =>
    (((hmem g).mp hg).2 z (Subgroup.mem_zpowers z)).symm
  have hrk₀ : CFSG.Open.pRank 3 D₀ ≤ 1 :=
    le_trans (CFSG.SectionRank.pRank_mono (by norm_num) hD₀D) hrk
  haveI : Group.IsSolvable D₀ :=
    isSolvable_core_central_order_three hO hD₀N hz3 hz1 hzD₀ hzc hrk₀
  haveI : Group.IsSolvable (MulAut ↥(Subgroup.zpowers z)) :=
    CFSG.ComponentClassification.CatalogueBHeldSmallCore.cyclic_automorphism_solvable
      (H := ↥(Subgroup.zpowers z))
  refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion hD₀D)
    ((MulAut.conjNormal (H := Subgroup.zpowers z)).comp D.subtype) ?_
  intro d hd
  have hd1 : MulAut.conjNormal (H := Subgroup.zpowers z) (d : Γ) = 1 :=
    MonoidHom.mem_ker.mp hd
  have hfix : (d : Γ) * z * (d : Γ)⁻¹ = z := by
    have h1 : MulAut.conjNormal (H := Subgroup.zpowers z) (d : Γ) ⟨z, Subgroup.mem_zpowers z⟩
        = ⟨z, Subgroup.mem_zpowers z⟩ := by
      rw [hd1]
      rfl
    have h2 := congrArg Subtype.val h1
    rw [MulAut.conjNormal_apply] at h2
    exact h2
  have hcomm : Commute z (d : Γ) := (mul_inv_eq_iff_eq_mul.mp hfix).symm
  have hdD₀ : (d : Γ) ∈ D₀ := (hmem _).mpr ⟨d.2, fun h hh => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact (hcomm.zpow_left k).eq⟩
  exact MonoidHom.mem_range.mpr ⟨⟨(d : Γ), hdD₀⟩, rfl⟩


theorem b3_map_eq_bot_of_not_three_dvd {G Γ : Type*} [Group G] [Group Γ] [IsSimpleGroup Γ]
    (h3 : 3 ∣ Nat.card Γ) {f : G →* Γ} (hf : Function.Surjective f) {M : Subgroup G} [M.Normal]
    (hM : ¬ 3 ∣ Nat.card M) : M.map f = ⊥ := by
  have hn : (M.map f).Normal := Subgroup.Normal.map inferInstance f hf
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M.map f) with h | h
  · exact h
  · exfalso
    apply hM
    have h1 : Nat.card (M.map f) ∣ Nat.card M := Subgroup.card_map_dvd M f
    rw [h, Subgroup.card_top] at h1
    exact dvd_trans h3 h1

theorem b3_isSolvable_of_surjective_of_ker_le {D S Γ : Type*} [Group D] [Group S] [Group Γ]
    [Group.IsSolvable S] (ψ : D →* S) (f : D →* Γ) (hf : Function.Surjective f)
    (hk : ψ.ker ≤ f.ker) : Group.IsSolvable Γ := by
  let q : D ⧸ ψ.ker →* Γ := QuotientGroup.lift ψ.ker f hk
  have hq : Function.Surjective q := by
    intro γ
    obtain ⟨d, rfl⟩ := hf γ
    exact ⟨(d : D ⧸ ψ.ker), rfl⟩
  have hDker : Group.IsSolvable (D ⧸ ψ.ker) :=
    Group.isSolvable_of_surjective (f := (QuotientGroup.quotientKerEquivRange ψ).symm.toMonoidHom)
      (QuotientGroup.quotientKerEquivRange ψ).symm.surjective
  exact Group.isSolvable_of_surjective hq

theorem false_of_simple_image_solvable_mod
    {X Γ S : Type*} [Group X] [Finite X] [Group Γ] [Finite Γ] [IsSimpleGroup Γ]
    (hna : ∃ a b : Γ, a * b ≠ b * a) (h3 : 3 ∣ Nat.card Γ)
    (φ : X →* Γ) (hφ : Function.Surjective φ)
    {N' D : Subgroup X} [N'.Normal] (hN3 : ¬ 3 ∣ Nat.card N') (hND : N' ⊔ D = ⊤)
    [Group S] (ψ : D →* S) [Group.IsSolvable S] (hψ : ¬ 3 ∣ Nat.card ψ.ker) : False := by
  have hN'bot : N'.map φ = ⊥ := b3_map_eq_bot_of_not_three_dvd h3 hφ hN3
  have hkillN : ∀ n ∈ N', φ n = 1 := by
    intro n hn
    have hmem : φ n ∈ N'.map φ := Subgroup.mem_map_of_mem φ hn
    rw [hN'bot, Subgroup.mem_bot] at hmem
    exact hmem
  have hφD : Function.Surjective (φ.comp D.subtype) := by
    intro γ
    obtain ⟨x, rfl⟩ := hφ γ
    have hx : x ∈ N' ⊔ D := by
      rw [hND]
      exact Subgroup.mem_top x
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hx
    refine ⟨⟨z, hz⟩, ?_⟩
    show φ z = φ (y * z)
    rw [map_mul, hkillN y hy, one_mul]
  have hkerψ : ψ.ker ≤ (φ.comp D.subtype).ker := by
    have hbot : (ψ.ker).map (φ.comp D.subtype) = ⊥ :=
      b3_map_eq_bot_of_not_three_dvd h3 hφD hψ
    intro k hk
    have hmem : (φ.comp D.subtype) k ∈ (ψ.ker).map (φ.comp D.subtype) :=
      Subgroup.mem_map_of_mem (φ.comp D.subtype) hk
    rw [hbot, Subgroup.mem_bot] at hmem
    exact MonoidHom.mem_ker.mpr hmem
  have hsolv : Group.IsSolvable Γ :=
    b3_isSolvable_of_surjective_of_ker_le ψ (φ.comp D.subtype) hφD hkerψ
  obtain ⟨a, b, hab⟩ := hna
  exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr hsolv a b)


theorem pCoreOf_le_pCoreOf_aux {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    {M Y : Subgroup G} (hY : Y ≤ M) (hO : CFSG.Open.pCoreOf p M ≤ Y) :
    CFSG.Open.pCoreOf p M ≤ CFSG.Open.pCoreOf p Y := by
  have hOp : IsPGroup p ↥(CFSG.Open.pCoreOf p M) :=
    (CFSG.pCore_isPGroup (p := p) (G := ↥M)).map M.subtype
  have hOn : ∀ m ∈ M, ∀ x ∈ CFSG.Open.pCoreOf p M,
      m * x * m⁻¹ ∈ CFSG.Open.pCoreOf p M := by
    rintro m hm x hx
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mem_map_of_mem M.subtype
      ((CFSG.pCore_normal (p := p) (G := ↥M)).conj_mem n hn ⟨m, hm⟩)
  have hKn : ((CFSG.Open.pCoreOf p M).subgroupOf Y).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hO]
    intro h k hh hk
    exact hOn k (hY hk) h hh
  have hKp : IsPGroup p ↥((CFSG.Open.pCoreOf p M).subgroupOf Y) :=
    hOp.of_injective (Subgroup.subgroupOfEquivOfLe hO).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hO).injective
  intro x hx
  have hxY : x ∈ Y := hO hx
  have hS : (CFSG.Open.pCoreOf p M).subgroupOf Y ∈ {K : Subgroup ↥Y | K.Normal ∧ IsPGroup p K} :=
    ⟨hKn, hKp⟩
  have hle : (CFSG.Open.pCoreOf p M).subgroupOf Y ≤ CFSG.pCore p ↥Y := le_sSup hS
  have hxmem : x ∈ CFSG.Open.pCoreOf p M := hx
  have hmem : (⟨x, hxY⟩ : ↥Y) ∈ CFSG.pCore p ↥Y :=
    hle (Subgroup.mem_subgroupOf.mpr hxmem)
  exact Subgroup.mem_map_of_mem Y.subtype hmem

theorem generalizedFitting_eq_pCore_of_le
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {M Y : Subgroup G}
    (hM : generalizedFitting ↥M = CFSG.pCore p ↥M) (hY : Y ≤ M)
    (hO : CFSG.Open.pCoreOf p M ≤ Y) :
    generalizedFitting ↥Y = CFSG.pCore p ↥Y := by
  refine (CFSG.isCharacteristicP_iff_generalizedFitting_eq_pCore ↥Y p).mp ?_
  have hchM : CFSG.IsCharacteristicP p ↥M :=
    (CFSG.isCharacteristicP_iff_generalizedFitting_eq_pCore ↥M p).mpr hM
  have hOY : CFSG.Open.pCoreOf p M ≤ CFSG.Open.pCoreOf p Y :=
    pCoreOf_le_pCoreOf_aux hY hO
  unfold CFSG.IsCharacteristicP
  intro z hz
  have hcent : (⟨(z : G), hY z.2⟩ : ↥M) ∈
      Subgroup.centralizer ((CFSG.pCore p ↥M : Subgroup ↥M) : Set ↥M) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hh' : h ∈ CFSG.pCore p ↥M := hh
    have hh2 : (h : G) ∈ CFSG.Open.pCoreOf p M := Subgroup.mem_map_of_mem M.subtype hh'
    obtain ⟨q, hq, hqh⟩ := Subgroup.mem_map.mp (hOY hh2)
    have hcomm : q * z = z * q := Subgroup.mem_centralizer_iff.mp hz q hq
    have h1 : (q : G) * (z : G) = (z : G) * (q : G) := congrArg Subtype.val hcomm
    have h2 : (q : G) = (h : G) := hqh
    apply Subtype.ext
    show (h : G) * (z : G) = (z : G) * (h : G)
    rw [← h2]
    exact h1
  have hzM : (⟨(z : G), hY z.2⟩ : ↥M) ∈ CFSG.pCore p ↥M := hchM hcent
  have hz' : (z : G) ∈ CFSG.Open.pCoreOf p M := Subgroup.mem_map_of_mem M.subtype hzM
  obtain ⟨q, hq, hqz⟩ := Subgroup.mem_map.mp (hOY hz')
  have hqz' : q = z := Subtype.ext hqz
  rw [← hqz']
  exact hq


end CFSG.RankThree.PartTwo.Sec17.C174
