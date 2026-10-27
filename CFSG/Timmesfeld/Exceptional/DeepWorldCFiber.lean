module

public import CFSG.Timmesfeld.Exceptional.DeepWorldCBasic
public import CFSG.Timmesfeld.Bridge.RootStructTwoLocalCount

public section

namespace CFSG.Timmesfeld.Moufang.Deep

open CFSG.Timmesfeld CFSG.Timmesfeld.Moufang CFSG.Certificates

theorem ncard_range_le_index {A β : Type*} [Group A] [Finite A] (K : Subgroup A) (f : A → β)
    (hf : ∀ a, ∀ k ∈ K, f (a * k) = f a) : (Set.range f).ncard ≤ K.index := by
  let F : A ⧸ K → β := Quotient.lift f fun a b hab => by
    have h := QuotientGroup.leftRel_apply.1 hab
    calc f a = f (a * (a⁻¹ * b)) := (hf a _ h).symm
      _ = f b := by rw [mul_inv_cancel_left]
  have hrange : Set.range f = Set.range F := by
    ext y
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨(a : A ⧸ K), rfl⟩
    · rintro ⟨q, rfl⟩
      induction q using QuotientGroup.induction_on with
      | H a => exact ⟨a, rfl⟩
  rw [hrange, Subgroup.index, ← Set.image_univ]
  exact (Set.ncard_image_le (Set.toFinite _)).trans (Set.ncard_univ _).le

theorem two_mul_card_le_of_lt' {G : Type*} [Group G] [Finite G] {H K : Subgroup G}
    (hle : H ≤ K) (hne : H ≠ K) : 2 * Nat.card H ≤ Nat.card K :=
  Bridge.two_mul_card_le_of_lt hle hne

variable {G : Type*} [Group G] {D : Set G}

theorem conj_eq_of_pow_three {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (h : (a * b) ^ 3 = 1) : (a * b) * a * (a * b)⁻¹ = b := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have h' : a * (b * (a * (b * (a * b)))) = 1 := by
    rw [← h]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  calc (a * b) * a * (a * b)⁻¹ = a * (b * (a * (b * a))) := by
        simp only [mul_inv_rev, hai, hbi, mul_assoc]
    _ = a * (b * (a * (b * (a * b)))) * b := by simp only [mul_assoc, hb, mul_one]
    _ = b := by rw [h', one_mul]

theorem conj_eq_of_pow_five {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (h : (a * b) ^ 5 = 1) : (a * b) ^ 2 * a * ((a * b) ^ 2)⁻¹ = b := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have h' : a * (b * (a * (b * (a * (b * (a * (b * (a * b)))))))) = 1 := by
    rw [← h]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  calc (a * b) ^ 2 * a * ((a * b) ^ 2)⁻¹ =
        a * (b * (a * (b * (a * (b * (a * (b * a))))))) := by
        simp only [sq, mul_inv_rev, hai, hbi, mul_assoc]
    _ = a * (b * (a * (b * (a * (b * (a * (b * (a * b)))))))) * b := by
        simp only [mul_assoc, hb, mul_one]
    _ = b := by rw [h', one_mul]

@[expose] def lineSub (p c : G) (x : Fin 2 → G) : Subgroup G :=
  Subgroup.closure (insert p (insert c (Set.range x)))

@[expose] def lineOrbit (p c : G) (x : Fin 2 → G) : Set G :=
  {y | ∃ g ∈ lineSub p c x, g * p * g⁻¹ = y}

theorem p_mem_lineSub (p c : G) (x : Fin 2 → G) : p ∈ lineSub p c x :=
  Subgroup.subset_closure (Set.mem_insert _ _)

theorem c_mem_lineSub (p c : G) (x : Fin 2 → G) : c ∈ lineSub p c x :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))

theorem x_mem_lineSub (p c : G) (x : Fin 2 → G) (i : Fin 2) : x i ∈ lineSub p c x :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ ⟨i, rfl⟩))

theorem card_lineSub_le {p c : G} {x : Fin 2 → G} (hcfg : LineConfig p c x) :
    Nat.card (lineSub p c x) ≤ 1080 := by
  have hfin := A6.card_pres_le.1
  set φ : A6.Pres →* G := wordsHom (lineRels 2 false) (lineGens p c x)
    (hcfg.signedProd_lineRels (by simp))
  have hφ : φ.range = lineSub p c x := by
    rw [range_wordsHom, range_lineGens]
    rfl
  rw [← hφ]
  exact (Nat.card_le_card_of_surjective _ φ.rangeRestrict_surjective).trans A6.card_pres_le.2

theorem commute_zEl_of_mem {p c : G} {x : Fin 2 → G} (hcfg : LineConfig p c x) {g : G}
    (hg : g ∈ lineSub p c x) : Commute (zEl p c x) g := by
  obtain ⟨hzp, hzc, hzx, -⟩ := zEl_facts hcfg
  have hle : lineSub p c x ≤ Subgroup.centralizer {zEl p c x} := by
    refine Subgroup.closure_le _ |>.2 ?_
    rintro y (rfl | rfl | ⟨i, rfl⟩) <;> rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    · exact hzp.eq.symm
    · exact hzc.eq.symm
    · exact (hzx i).eq.symm
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hg)).symm

theorem mem_lineOrbit_of_mem_lines {p c : G} {x : Fin 2 → G} (hcfg : LineConfig p c x)
    (i : Fin 2) : x i ∈ lineOrbit p c x ∧ p * x i ∈ lineOrbit p c x := by
  have hpc : (p * c) ^ 2 * p * ((p * c) ^ 2)⁻¹ = c :=
    conj_eq_of_pow_five hcfg.d_sq hcfg.c_sq hcfg.dc_pow
  have hpxsq : p * x i * (p * x i) = 1 := by
    rw [mul_assoc, ← mul_assoc (x i), ← (hcfg.d_comm i).eq, mul_assoc, hcfg.x_sq i, mul_one,
      hcfg.d_sq]
  have hp := p_mem_lineSub p c x
  have hc := c_mem_lineSub p c x
  have hx := x_mem_lineSub p c x i
  refine ⟨⟨c * x i * (p * c) ^ 2, ?_, ?_⟩, ⟨(c * (p * x i)) ^ 2 * (p * c) ^ 2, ?_, ?_⟩⟩
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hc hx)
      (Subgroup.pow_mem _ (Subgroup.mul_mem _ hp hc) 2)
  · rw [show c * x i * (p * c) ^ 2 * p * (c * x i * (p * c) ^ 2)⁻¹ =
      (c * x i) * ((p * c) ^ 2 * p * ((p * c) ^ 2)⁻¹) * (c * x i)⁻¹ by group, hpc]
    exact conj_eq_of_pow_three hcfg.c_sq (hcfg.x_sq i) (hcfg.cx_pow i)
  · exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.mul_mem _ hc
      (Subgroup.mul_mem _ hp hx)) 2) (Subgroup.pow_mem _ (Subgroup.mul_mem _ hp hc) 2)
  · rw [show (c * (p * x i)) ^ 2 * (p * c) ^ 2 * p * ((c * (p * x i)) ^ 2 * (p * c) ^ 2)⁻¹ =
      (c * (p * x i)) ^ 2 * ((p * c) ^ 2 * p * ((p * c) ^ 2)⁻¹) * ((c * (p * x i)) ^ 2)⁻¹ by
      group, hpc]
    exact conj_eq_of_pow_five hcfg.c_sq hpxsq (hcfg.cdx_pow i)

theorem zEl_mem_lineSub {p c : G} {x : Fin 2 → G} (hcfg : LineConfig p c x) :
    zEl p c x ∈ lineSub p c x := by
  set φ : A6.Pres →* G := wordsHom (lineRels 2 false) (lineGens p c x)
    (hcfg.signedProd_lineRels (by simp))
  have hφ : φ.range = lineSub p c x := by
    rw [range_wordsHom, range_lineGens]
    rfl
  rw [← hφ]
  exact ⟨signedProd PresentedGroup.of zw, wordsHom_signedProd _ _ _ _⟩

theorem mem_lineOrbit_of_commute (hconj : ∀ g : G, ∀ x ∈ D, g * x * g⁻¹ ∈ D) {p c : G}
    {x : Fin 2 → G} (hcfg : LineConfig p c x)
    (hW : ∀ q ∈ offLines D p x, ¬ Commute (zEl p c x) q) {y q : G} (hy : y ∈ lineOrbit p c x)
    (hq : q ∈ collinearSet D y) (hzq : Commute (zEl p c x) q) : q ∈ lineOrbit p c x := by
  obtain ⟨g, hg, rfl⟩ := hy
  have hzg := commute_zEl_of_mem hcfg hg
  have hq' : g⁻¹ * q * g ∈ collinearSet D p := by
    have := conj_mem_collinearSet hconj g⁻¹ hq
    rwa [show g⁻¹ * (g * p * g⁻¹) * g⁻¹⁻¹ = p by group, inv_inv] at this
  have hzq' : Commute (zEl p c x) (g⁻¹ * q * g) := (hzg.inv_right.mul_right hzq).mul_right hzg
  have hon : ∃ i, g⁻¹ * q * g = x i ∨ g⁻¹ * q * g = p * x i := by
    by_contra hno
    push Not at hno
    exact hW _ ⟨hq', fun i => hno i⟩ hzq'
  obtain ⟨i, hi⟩ := hon
  have hmem := mem_lineOrbit_of_mem_lines hcfg i
  obtain ⟨g', hg', e⟩ : g⁻¹ * q * g ∈ lineOrbit p c x := by
    rcases hi with hi | hi <;> rw [hi]
    exacts [hmem.1, hmem.2]
  refine ⟨g * g', Subgroup.mul_mem _ hg hg', ?_⟩
  rw [show g * g' * p * (g * g')⁻¹ = g * (g' * p * g'⁻¹) * g⁻¹ by group, e]
  group

theorem le_card_closure [Finite G] {p c : G} {x : Fin 2 → G} (hcfg : LineConfig p c x) (hp1 : p ≠ 1)
    (hz1 : zEl p c x ≠ 1) :
    24 ≤ Nat.card (Subgroup.closure ({zEl p c x * (x 0 * x 1), x 0} : Set G)) := by
  obtain ⟨-, -, hzx, hz3⟩ := zEl_facts hcfg
  set z := zEl p c x
  set g₁₂ := z * (x 0 * x 1)
  set K₀ := Subgroup.closure ({g₁₂, x 0} : Set G)
  have hx01 : (x 0 * x 1) ^ 2 = p := hcfg.sq_eq 0 1 (by decide)
  have ho4 : orderOf (x 0 * x 1) = 4 := by
    have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := x 0 * x 1)
      (by rw [pow_one, hx01]; exact hp1)
      (by rw [show 2 ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, hx01, sq, hcfg.d_sq])
    simpa using this
  have ho3 : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  have hzx01 : Commute z (x 0 * x 1) := (hzx 0).mul_right (hzx 1)
  have ho12 : orderOf g₁₂ = 12 := by
    rw [hzx01.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [ho3, ho4]; decide), ho3, ho4]
  have hg₁₂ : g₁₂ ∈ K₀ := Subgroup.subset_closure (Set.mem_insert _ _)
  have hx0K : x 0 ∈ K₀ := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hx0 : x 0 ∉ Subgroup.zpowers g₁₂ := by
    intro hx0
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hx0
    have hc : Commute (x 0) (g₁₂ ^ 9) := by
      rw [← hk]
      exact (Commute.refl g₁₂).zpow_left k |>.pow_right 9
    rw [hzx01.mul_pow, show z ^ 9 = (z ^ 3) ^ 3 by rw [← pow_mul], hz3, one_pow, one_mul,
      show (x 0 * x 1) ^ 9 = ((x 0 * x 1) ^ 2) ^ 4 * (x 0 * x 1) by
        rw [← pow_mul, ← pow_succ], hx01, show p ^ 4 = (p * p) ^ 2 by
        rw [← sq, ← pow_mul], hcfg.d_sq, one_pow, one_mul] at hc
    have hc' : Commute (x 0) (x 1) := by
      have := (Commute.refl (x 0)).inv_right.mul_right hc
      rwa [inv_mul_cancel_left] at this
    have h1 : (x 0 * x 1) ^ 2 = 1 := by
      rw [sq, mul_assoc, ← mul_assoc (x 1), ← hc'.eq, mul_assoc, hcfg.x_sq 1, mul_one,
        hcfg.x_sq 0]
    exact hp1 (hx01.symm.trans h1)
  have hlt : Subgroup.zpowers g₁₂ ≠ K₀ := fun h => hx0 (h ▸ hx0K)
  have h24 := two_mul_card_le_of_lt' ((Subgroup.zpowers_le).2 hg₁₂) hlt
  rw [Nat.card_zpowers, ho12] at h24
  exact h24

theorem ncard_lineOrbit_le [Finite G] {p c : G} {x : Fin 2 → G} (hcfg : LineConfig p c x)
    (hp1 : p ≠ 1) (hz1 : zEl p c x ≠ 1) : (lineOrbit p c x).ncard ≤ 45 := by
  obtain ⟨hzp, -, -, -⟩ := zEl_facts hcfg
  set z := zEl p c x
  set H := lineSub p c x
  set K₀ := Subgroup.closure ({z * (x 0 * x 1), x 0} : Set G)
  have hx01p : Commute (x 0 * x 1) p := (hcfg.d_comm 0).symm.mul_left (hcfg.d_comm 1).symm
  have hK₀p : ∀ k ∈ K₀, Commute k p := by
    intro k hk
    have hle : K₀ ≤ Subgroup.centralizer {p} := by
      refine Subgroup.closure_le _ |>.2 ?_
      rintro y (rfl | rfl) <;> rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      · exact (hzp.mul_left hx01p).eq
      · exact (hcfg.d_comm 0).symm.eq
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hk)
  have hK₀H : K₀ ≤ H := by
    refine Subgroup.closure_le _ |>.2 ?_
    rintro y (rfl | rfl)
    · exact Subgroup.mul_mem _ (zEl_mem_lineSub hcfg)
        (Subgroup.mul_mem _ (x_mem_lineSub p c x 0) (x_mem_lineSub p c x 1))
    · exact x_mem_lineSub p c x 0
  set K := K₀.subgroupOf H
  have hrange : lineOrbit p c x = Set.range fun g : H => (g : G) * p * (g : G)⁻¹ := by
    ext y
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, rfl⟩
    · rintro ⟨g, rfl⟩
      exact ⟨g, g.2, rfl⟩
  have hidx := ncard_range_le_index K (fun g : H => (g : G) * p * (g : G)⁻¹) (by
    intro a k hk
    have hkp := hK₀p _ (Subgroup.mem_subgroupOf.1 hk)
    simp only [Subgroup.coe_mul, mul_inv_rev]
    rw [mul_assoc (a : G) (k : G) p, hkp.eq]
    group)
  rw [← hrange] at hidx
  have hcardK : Nat.card K = Nat.card K₀ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK₀H).toEquiv
  have h24 := le_card_closure hcfg hp1 hz1
  have hmul := K.index_mul_card
  have hH := card_lineSub_le hcfg
  rw [hcardK] at hmul
  have : K.index * 24 ≤ 1080 := by
    calc K.index * 24 ≤ K.index * Nat.card K₀ := Nat.mul_le_mul_left _ h24
      _ = Nat.card H := hmul
      _ ≤ 1080 := hH
  omega

theorem conj_ne_of_pow_three {z e : G} (hz3 : z ^ 3 = 1) (hze : ¬ Commute z e) :
    z * e * z⁻¹ ≠ e ∧ z * (z * e * z⁻¹) * z⁻¹ ≠ z * e * z⁻¹ ∧ z * (z * e * z⁻¹) * z⁻¹ ≠ e := by
  have h1 : z * e * z⁻¹ ≠ e := fun h => hze (mul_inv_eq_iff_eq_mul.1 h)
  refine ⟨h1, fun h => h1 ?_, fun h => h1 ?_⟩
  · have := congrArg (fun t => z⁻¹ * t * z) h
    simpa [mul_assoc] using this
  · have := congrArg (fun t => z * t * z⁻¹) h
    have hz3' : z * z * z = 1 := by rw [mul_assoc, ← pow_three]; exact hz3
    have e3 : z * (z * (z * e * z⁻¹) * z⁻¹) * z⁻¹ = z * z * z * e * (z * z * z)⁻¹ := by group
    rw [e3, hz3', one_mul, inv_one, mul_one] at this
    exact this.symm

namespace FiveLineSetting

variable (S : FiveLineSetting G D)
include S

theorem mem_lineOrbit_of_far {p c : G} {x : Fin 2 → G} (hp : p ∈ D) (hcfg : LineConfig p c x)
    (hW : ∀ q ∈ offLines D p x, ¬ Commute (zEl p c x) q) {c' : G} (hc' : c' ∈ D)
    (hp4 : p ∈ nbhd D c' 4) (hp3 : p ∉ nbhd D c' 3) (hzc : Commute (zEl p c x) c') :
    c' ∈ lineOrbit p c x := by
  have hD := S.root
  have hconj : ∀ g : G, ∀ x ∈ D, g * x * g⁻¹ ∈ D := fun g x hx => S.conj g hx
  obtain ⟨hzp, -, -, hz3⟩ := zEl_facts hcfg
  set z := zEl p c x
  obtain ⟨-, e, he3, hpe⟩ := (mem_nbhd_succ_iff hc').1 hp4
  have heD := nbhd_subset hc' 3 he3
  have he : e ∈ collinearSet D p :=
    (S.mem_collinearSet_iff hp).2 ⟨heD, hpe, fun h => hp3 (h ▸ he3)⟩
  have he2 : e ∉ nbhd D c' 2 := fun h => hp3 (mem_nbhd_succ_of_commute hp h hpe)
  have hze : Commute z e := by
    by_contra hne
    obtain ⟨h1, h2, h3⟩ := conj_ne_of_pow_three hz3 hne
    have hl : ∀ y ∈ collinearSet D p, z * y * z⁻¹ ∈ collinearSet D p := fun y hy =>
      conj_mem_collinearSet_of_commute hconj hzp hy
    have hn : ∀ y ∈ nbhd D c' 3, z * y * z⁻¹ ∈ nbhd D c' 3 := fun y hy =>
      conj_mem_nbhd_of_commute hconj hzc hy
    refine S.noThreeNear c' hc' p hp hp3 (S.threeNear_of_three hc' hp hp3
      (y := ![e, z * e * z⁻¹, z * (z * e * z⁻¹) * z⁻¹]) (fun i => ?_) (fun i => ?_)
      (fun i j hij => ?_))
    · fin_cases i
      exacts [he, hl _ he, hl _ (hl _ he)]
    · fin_cases i
      exacts [he3, hn _ he3, hn _ (hn _ he3)]
    · fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  obtain ⟨-, u, hu2, heu⟩ := (mem_nbhd_succ_iff hc').1 he3
  have huD := nbhd_subset hc' 2 hu2
  have hu : u ∈ collinearSet D e :=
    (S.mem_collinearSet_iff heD).2 ⟨huD, heu, fun h => he2 (h ▸ hu2)⟩
  have hpe' : p ∈ collinearSet D e := mem_collinearSet_symm hp he
  have hzu : Commute z u := by
    have hu' := conj_mem_collinearSet_of_commute hconj hze hu
    have hu'2 := conj_mem_nbhd_of_commute hconj hzc hu2
    have e1 := S.eq_of_mem_two_of_far hc' he3 he2 hpe' hp3 hu hu2 hu' hu'2
    exact mul_inv_eq_iff_eq_mul.1 e1
  have hu1 : u ∉ nbhd D c' 1 := fun h => he2 (mem_nbhd_succ_of_commute heD h heu)
  have h4 := S.orderOf_eq_four_of_mem_two hc' hu2 hu1
  obtain ⟨hvD, huv, hcv, -⟩ := sq_mem_of_orderOf_eq_four hD huD hc' h4
  have huc : ¬ Commute u c' := fun h => hu1 ((mem_nbhd_one_iff hc').2 ⟨huD, h⟩)
  have hv : (u * c') ^ 2 ∈ collinearSet D u :=
    (S.mem_collinearSet_iff huD).2 ⟨hvD, huv, fun h => huc (h ▸ hcv.symm)⟩
  have hcv' : c' ∈ collinearSet D ((u * c') ^ 2) :=
    (S.mem_collinearSet_iff hvD).2 ⟨hc', hcv.symm, fun h => huc (h ▸ huv)⟩
  have hzv : Commute z ((u * c') ^ 2) := (hzu.mul_right hzc).pow_right 2
  have h0 : p ∈ lineOrbit p c x := ⟨1, Subgroup.one_mem _, by group⟩
  have h1 := mem_lineOrbit_of_commute hconj hcfg hW h0 he hze
  have h2 := mem_lineOrbit_of_commute hconj hcfg hW h1 hu hzu
  have h3 := mem_lineOrbit_of_commute hconj hcfg hW h2 hv hzv
  exact mem_lineOrbit_of_commute hconj hcfg hW h3 hcv' hzc

end FiveLineSetting

end CFSG.Timmesfeld.Moufang.Deep
