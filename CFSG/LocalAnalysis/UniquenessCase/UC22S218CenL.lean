module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S218Cen
import CFSG.LocalAnalysis.UniquenessCase.UC6S846c
import CFSG.GroupTheory.PGroup.ElemAbelianSq
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def uc22s218_barAutK {L : Subgroup G} (K : Subgroup ↥L) [K.Characteristic] :
    MulAut ↥L →* MulAut (↥L ⧸ K) where
  toFun φ := QuotientGroup.congr K K φ (Subgroup.characteristic_iff_map_eq.mp inferInstance φ)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => rfl
  map_mul' φ ψ := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => rfl

@[expose] noncomputable def uc22s218_rhoK (L : Subgroup G) (K : Subgroup ↥L) [K.Characteristic] :
    ↥(normalizer (L : Set G)) →* MulAut (↥L ⧸ K) :=
  (uc22s218_barAutK K).comp (Subgroup.normalizerMonoidHom L)

omit [Finite G] in
theorem uc22s218_rhoK_mk (L : Subgroup G) (K : Subgroup ↥L) [K.Characteristic]
    (m : ↥(normalizer (L : Set G))) (x : ↥L) :
    uc22s218_rhoK L K m (QuotientGroup.mk x) =
      QuotientGroup.mk (Subgroup.normalizerMonoidHom L m x) := rfl

omit [Finite G] in
theorem uc22s218_map_subtype_subgroupOf (L : Subgroup G) (K : Subgroup ↥L) :
    (K.map L.subtype).subgroupOf L = K :=
  Subgroup.comap_map_eq_self_of_injective L.subtype_injective K

omit [Finite G] in
theorem uc22s218_le_normalizer_map_subtype (L : Subgroup G) (K : Subgroup ↥L) [K.Normal] :
    L ≤ normalizer ((K.map L.subtype : Subgroup G) : Set G) := by
  have h : ((K.map L.subtype).subgroupOf L).Normal := by
    rw [uc22s218_map_subtype_subgroupOf]
    infer_instance
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le K)).1 h

omit [Finite G] in
theorem uc22s218_normalizer_le_normalizer_map_subtype (L : Subgroup G) (K : Subgroup ↥L)
    [K.Characteristic] :
    normalizer (L : Set G) ≤ normalizer ((K.map L.subtype : Subgroup G) : Set G) := by
  have key : ∀ t ∈ normalizer (L : Set G), ∀ x ∈ K.map L.subtype,
      t * x * t⁻¹ ∈ K.map L.subtype := by
    intro t ht x hx
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨Subgroup.normalizerMonoidHom L ⟨t, ht⟩ y, ?_, by simp⟩
    have hfix : K.map (Subgroup.normalizerMonoidHom L ⟨t, ht⟩).toMonoidHom = K :=
      Subgroup.characteristic_iff_map_eq.mp inferInstance _
    rw [← hfix]
    exact Subgroup.mem_map_of_mem _ hy
  intro t ht
  rw [mem_normalizer_iff]
  intro x
  refine ⟨key t ht x, fun hx => ?_⟩
  have h1 := key t⁻¹ (inv_mem ht) _ hx
  rwa [show t⁻¹ * (t * x * t⁻¹) * t⁻¹⁻¹ = x by group] at h1

theorem uc22s218_exists_mem_kernel_of_pRank {L M : Subgroup G} (hLM : L ≤ M)
    [(L.subgroupOf M).Normal] (K : Subgroup ↥L) [K.Characteristic] {p : ℕ} (hp : p.Prime)
    (haut : CFSG.Open.pRank p (⊤ : Subgroup (MulAut (↥L ⧸ K))) ≤ 3)
    (hrank : 4 ≤ CFSG.Open.pRank p M) :
    ∃ (x : G) (hx : x ∈ M), x ≠ 1 ∧ x ^ p = 1 ∧
      uc22s218_rhoK L K ⟨x, le_normalizer_of_normal_subgroupOf hLM hx⟩ = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hML : M ≤ normalizer (L : Set G) := le_normalizer_of_normal_subgroupOf hLM
  obtain ⟨A, hAM, hAel, hAc⟩ := UC6S846.exists_elemAbelian_card_of_le_pRank hp hrank
  let ρA : ↥A →* MulAut (↥L ⧸ K) := (uc22s218_rhoK L K).comp (Subgroup.inclusion (hAM.trans hML))
  have : IsMulCommutative ↥A := hAel.1
  have hnotinj : ¬ Function.Injective ρA := fun hinj => by
    have h4 := CFSG.SectionRank.le_pRank_of_injective hp.one_lt (fun a b => mul_comm' a b)
      (fun a => Subtype.ext (hAel.2 _ a.2)) hAc ρA hinj (H := ⊤) le_top
    omega
  obtain ⟨a, ha1, hρa⟩ : ∃ a : ↥A, a ≠ 1 ∧ ρA a = 1 := by
    by_contra h
    exact hnotinj ((injective_iff_map_eq_one ρA).2 fun a ha =>
      by_contra fun h' => h ⟨a, h', ha⟩)
  refine ⟨(a : G), hAM a.2, fun h => ha1 (Subtype.ext h), hAel.2 _ a.2, ?_⟩
  exact hρa

omit [Finite G] in
theorem uc22s218_conj_mul_inv_mem_of_rhoK_eq_one {L : Subgroup G} (K : Subgroup ↥L)
    [K.Characteristic] {m : ↥(normalizer (L : Set G))} (hm : uc22s218_rhoK L K m = 1) (l : ↥L) :
    (m : G) * (l : G) * (m : G)⁻¹ * (l : G)⁻¹ ∈ K.map L.subtype := by
  have h1 : uc22s218_rhoK L K m (QuotientGroup.mk l) = QuotientGroup.mk l := by
    rw [hm]
    rfl
  rw [uc22s218_rhoK_mk] at h1
  have h2 : (Subgroup.normalizerMonoidHom L m l)⁻¹ * l ∈ K := QuotientGroup.eq.1 h1
  have h3 : Subgroup.normalizerMonoidHom L m l * l⁻¹ ∈ K := by
    have h4 := K.inv_mem h2
    have h5 := Subgroup.Normal.conj_mem inferInstance _ h4 l
    simpa using h5
  refine ⟨_, h3, ?_⟩
  simp

omit [Finite G] in
theorem uc22s218_rhoK_zpow_eq_one {L M : Subgroup G} (K : Subgroup ↥L) [K.Characteristic]
    (hML : M ≤ normalizer (L : Set G)) {x : G} (hx : x ∈ M) (hρ : uc22s218_rhoK L K ⟨x, hML hx⟩ = 1)
    (j : ℤ) : uc22s218_rhoK L K ⟨x ^ j, hML (zpow_mem hx j)⟩ = 1 := by
  have h : (⟨x ^ j, hML (zpow_mem hx j)⟩ : ↥(normalizer (L : Set G))) =
      (⟨x, hML hx⟩ : ↥(normalizer (L : Set G))) ^ j := Subtype.ext (by simp)
  rw [h, map_zpow, hρ, one_zpow]

theorem uc22s218_exists_lift_centralizer {L M : Subgroup G} (hML : M ≤ normalizer (L : Set G))
    (K : Subgroup ↥L) [K.Characteristic] {p : ℕ} [Fact p.Prime] (hpK : ¬ p ∣ Nat.card K)
    {x : G} (hx : x ∈ M) (hxo : orderOf x = p) (hρ : uc22s218_rhoK L K ⟨x, hML hx⟩ = 1)
    (P : Subgroup (↥L ⧸ K)) (hcop : Nat.Coprime (Nat.card P) (Nat.card K)) :
    ∃ β : P →* ↥L, (∀ a, ∀ x' ∈ zpowers x, x' * (β a : G) = (β a : G) * x') ∧
      ∀ a, QuotientGroup.mk' K (β a) = a := by
  have hXp : IsPGroup p (zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxo, pow_one])
  have hNL : K.map L.subtype ≤ L := Subgroup.map_subtype_le K
  have hpN : ¬ p ∣ Nat.card (K.map L.subtype) := by
    rwa [Subgroup.card_map_of_injective L.subtype_injective]
  have hXN : zpowers x ≤ normalizer ((K.map L.subtype : Subgroup G) : Set G) :=
    (Subgroup.zpowers_le.2 (hML hx)).trans (uc22s218_normalizer_le_normalizer_map_subtype L K)
  have hXL : ∀ x' ∈ zpowers x, ∀ l ∈ L, x' * l * x'⁻¹ * l⁻¹ ∈ K.map L.subtype := by
    intro x' hx' l hl
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx'
    exact uc22s218_conj_mul_inv_mem_of_rhoK_eq_one K
      (uc22s218_rhoK_zpow_eq_one K hML hx hρ j) ⟨l, hl⟩
  let Cx : Subgroup ↥L := (centralizer ((zpowers x : Subgroup G) : Set G)).subgroupOf L
  have hC : ∀ l : ↥L, ∃ c ∈ Cx, c⁻¹ * l ∈ K := by
    intro l
    obtain ⟨c, hc, hcl⟩ := uc22s218_exists_mem_centralizer_of_comm_mod hpN hXp hXN
      (uc22s218_le_normalizer_map_subtype L K) hNL hXL l.2
    rw [mem_inf] at hc
    refine ⟨⟨c, hc.1⟩, hc.2, ?_⟩
    have h : ((⟨c, hc.1⟩⁻¹ * l : ↥L) : G) ∈ K.map L.subtype := by simpa using hcl
    exact (Subgroup.mem_map_iff_mem L.subtype_injective).1 h
  obtain ⟨β, hβC, hβ⟩ := uc22s218_exists_lift_hom_of_coprime K Cx hC P hcop
  exact ⟨β, fun a x' hx' => (mem_centralizer_iff.1 (hβC a)) x' hx', hβ⟩

theorem uc22s218_exists_pair_of_kernel_elem {L M : Subgroup G} (hLM : L ≤ M)
    [(L.subgroupOf M).Normal] (K : Subgroup ↥L) [K.Characteristic] {p r : ℕ} (hp : p.Prime)
    (hr : r.Prime) (hpr : p ≠ r) (hpK : ¬ p ∣ Nat.card K) (hrK : ¬ r ∣ Nat.card K) {x : G}
    (hxM : x ∈ M) (hx1 : x ≠ 1) (hxp : x ^ p = 1)
    (hρ : uc22s218_rhoK L K ⟨x, le_normalizer_of_normal_subgroupOf hLM hxM⟩ = 1)
    {E₀ : Subgroup (↥L ⧸ K)} (hE₀ : IsElemAbelian r E₀)
    (hE₀c : Nat.card E₀ = r ^ 2) {y : ↥L ⧸ K} (hy : orderOf y = p)
    (hyE : ∀ e ∈ E₀, y * e = e * y) (hyZ : ∃ w : ↥L ⧸ K, w * y ≠ y * w) :
    ∃ E Q : Subgroup G, E ≤ L ∧ IsElemAbelian r E ∧ Nat.card E = r ^ 2 ∧ Q ≤ M ∧
      IsElemAbelian p Q ∧ Nat.card Q = p ^ 2 ∧
      ∀ x ∈ Q, ∃ k : ℕ, ∀ e ∈ E, x * e * x⁻¹ = e ^ k := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact r.Prime := ⟨hr⟩
  have : IsMulCommutative ↥E₀ := hE₀.1
  have hML : M ≤ normalizer (L : Set G) := le_normalizer_of_normal_subgroupOf hLM
  have hxo : orderOf x = p := orderOf_eq_prime hxp hx1
  have hYcard : Nat.card (zpowers y) = p := by rw [Nat.card_zpowers, hy]
  have hYcent : zpowers y ≤ centralizer (E₀ : Set (↥L ⧸ K)) :=
    Subgroup.zpowers_le.2 (mem_centralizer_iff.2 fun e he => (hyE e he).symm)
  have hdisj : Disjoint E₀ (zpowers y) :=
    Subgroup.disjoint_of_coprime_natCard (by
      rw [hE₀c, hYcard]
      exact Nat.Coprime.pow_left 2 ((Nat.coprime_primes hr hp).2 hpr.symm))
  have hPcard : Nat.card (E₀ ⊔ zpowers y : Subgroup (↥L ⧸ K)) = r ^ 2 * p := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer E₀ (zpowers y)
      (hYcent.trans (centralizer_le_normalizer _)) hdisj, hE₀c, hYcard]
  have hcop : Nat.Coprime (Nat.card (E₀ ⊔ zpowers y : Subgroup (↥L ⧸ K))) (Nat.card K) := by
    rw [hPcard]
    exact Nat.Coprime.mul_left (Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd hr).2 hrK))
      ((Nat.Prime.coprime_iff_not_dvd hp).2 hpK)
  obtain ⟨β, hβc, hβ⟩ := uc22s218_exists_lift_centralizer hML K hpK hxM hxo hρ _ hcop
  have hβinj : Function.Injective β := fun a b hab =>
    Subtype.ext ((hβ a).symm.trans ((congrArg (QuotientGroup.mk' K) hab).trans (hβ b)))
  have hyP : y ∈ E₀ ⊔ zpowers y := mem_sup_right (Subgroup.mem_zpowers y)
  have hE₀P : E₀ ≤ E₀ ⊔ zpowers y := le_sup_left
  let χ : ↥E₀ →* G := (L.subtype.comp β).comp (Subgroup.inclusion hE₀P)
  have hχinj : Function.Injective χ :=
    L.subtype_injective.comp (hβinj.comp (Subgroup.inclusion_injective hE₀P))
  let yL : ↥L := β ⟨y, hyP⟩
  have hyLmk : QuotientGroup.mk' K yL = y := hβ ⟨y, hyP⟩
  have hEel : IsElemAbelian r χ.range := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun z hz => ?_⟩
    · obtain ⟨u, hu⟩ := MonoidHom.mem_range.1 a.2
      obtain ⟨v, hv⟩ := MonoidHom.mem_range.1 b.2
      apply Subtype.ext
      change (a : G) * b = b * a
      rw [← hu, ← hv, ← map_mul, ← map_mul, mul_comm' u v]
    · obtain ⟨u, rfl⟩ := MonoidHom.mem_range.1 hz
      rw [← map_pow]
      have : u ^ r = 1 := Subtype.ext (hE₀.2 _ u.2)
      rw [this, map_one]
  have hEc : Nat.card χ.range = r ^ 2 := by
    rw [← hE₀c]
    exact (Nat.card_congr (MonoidHom.ofInjective hχinj).toEquiv).symm
  have hEL : χ.range ≤ L := by
    rintro _ ⟨u, rfl⟩
    exact (β (Subgroup.inclusion hE₀P u)).2
  have hyo : orderOf (yL : G) = p := by
    have h1 : orderOf (yL : G) = orderOf (⟨y, hyP⟩ : ↥(E₀ ⊔ zpowers y)) :=
      orderOf_injective (L.subtype.comp β) (L.subtype_injective.comp hβinj) _
    rw [h1, Subgroup.orderOf_mk, hy]
  have hyEc : ∀ e ∈ χ.range, e * (yL : G) = (yL : G) * e := by
    rintro _ ⟨u, rfl⟩
    have h1 : (⟨y, hyP⟩ : ↥(E₀ ⊔ zpowers y)) * Subgroup.inclusion hE₀P u =
        Subgroup.inclusion hE₀P u * ⟨y, hyP⟩ := Subtype.ext (hyE _ u.2)
    have h2 := congrArg (L.subtype.comp β) h1
    rw [map_mul, map_mul] at h2
    exact h2.symm
  have hxEc : ∀ e ∈ χ.range, e * x = x * e := by
    rintro _ ⟨u, rfl⟩
    exact (hβc (Subgroup.inclusion hE₀P u) x (Subgroup.mem_zpowers x)).symm
  have hxyc : ∀ a ∈ zpowers x, a * (yL : G) = (yL : G) * a := fun a ha => hβc ⟨y, hyP⟩ a ha
  have hyX : (yL : G) ∉ zpowers x := by
    intro h
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 h
    obtain ⟨w, hw⟩ := hyZ
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective w
    have hρy : uc22s218_rhoK L K ⟨(yL : G), hML (hLM yL.2)⟩ = 1 := by
      have := uc22s218_rhoK_zpow_eq_one K hML hxM hρ j
      rwa [show (⟨x ^ j, hML (zpow_mem hxM j)⟩ : ↥(normalizer (L : Set G))) =
        ⟨(yL : G), hML (hLM yL.2)⟩ from Subtype.ext hj] at this
    have h1 := uc22s218_conj_mul_inv_mem_of_rhoK_eq_one K hρy l
    have h2 : yL * l * yL⁻¹ * l⁻¹ ∈ K := by
      have h3 : (((yL * l * yL⁻¹ * l⁻¹ : ↥L)) : G) ∈ K.map L.subtype := by simpa using h1
      exact (Subgroup.mem_map_iff_mem L.subtype_injective).1 h3
    have h4 : QuotientGroup.mk' K (yL * l * yL⁻¹ * l⁻¹) = 1 :=
      (QuotientGroup.eq_one_iff _).2 h2
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hyLmk] at h4
    apply hw
    have h5 : y * (QuotientGroup.mk' K) l * y⁻¹ * ((QuotientGroup.mk' K) l)⁻¹ = 1 := h4
    have h6 : y * (QuotientGroup.mk' K) l = (QuotientGroup.mk' K) l * y := by
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h5
      exact h5
    exact h6.symm
  obtain ⟨hQel, hQc⟩ := CFSG.GroupTheory.isElemAbelian_sup_zpowers_of_commute (r := p)
    (X := zpowers x) (by rw [Nat.card_zpowers, hxo]) hyo hyX hxyc
  refine ⟨χ.range, zpowers x ⊔ zpowers (yL : G), hEL, hEel, hEc,
    sup_le (Subgroup.zpowers_le.2 hxM) (Subgroup.zpowers_le.2 (hLM yL.2)), hQel, hQc, ?_⟩
  have hQcent : zpowers x ⊔ zpowers (yL : G) ≤ centralizer (χ.range : Set G) :=
    sup_le (Subgroup.zpowers_le.2 (mem_centralizer_iff.2 fun e he => hxEc e he))
      (Subgroup.zpowers_le.2 (mem_centralizer_iff.2 fun e he => hyEc e he))
  intro q hq
  refine ⟨1, fun e he => ?_⟩
  have h := mem_centralizer_iff.1 (hQcent hq) e he
  rw [pow_one, mul_inv_eq_iff_eq_mul]
  exact h.symm

theorem uc22s218_exists_pair_of_kernel {L M : Subgroup G} (hLM : L ≤ M) [(L.subgroupOf M).Normal]
    (K : Subgroup ↥L) [K.Characteristic] {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hpr : p ≠ r)
    (hpK : ¬ p ∣ Nat.card K) (hrK : ¬ r ∣ Nat.card K)
    (haut : CFSG.Open.pRank p (⊤ : Subgroup (MulAut (↥L ⧸ K))) ≤ 3)
    (hrank : 4 ≤ CFSG.Open.pRank p M) {E₀ : Subgroup (↥L ⧸ K)} (hE₀ : IsElemAbelian r E₀)
    (hE₀c : Nat.card E₀ = r ^ 2) {y : ↥L ⧸ K} (hy : orderOf y = p)
    (hyE : ∀ e ∈ E₀, y * e = e * y) (hyZ : ∃ w : ↥L ⧸ K, w * y ≠ y * w) :
    ∃ E Q : Subgroup G, E ≤ L ∧ IsElemAbelian r E ∧ Nat.card E = r ^ 2 ∧ Q ≤ M ∧
      IsElemAbelian p Q ∧ Nat.card Q = p ^ 2 ∧
      ∀ x ∈ Q, ∃ k : ℕ, ∀ e ∈ E, x * e * x⁻¹ = e ^ k := by
  obtain ⟨x, hxM, hx1, hxp, hρ⟩ := uc22s218_exists_mem_kernel_of_pRank hLM K hp haut hrank
  exact uc22s218_exists_pair_of_kernel_elem hLM K hp hr hpr hpK hrK hxM hx1 hxp hρ hE₀ hE₀c hy hyE
    hyZ

end CFSG.LocalAnalysis.UniquenessCase.UC22
