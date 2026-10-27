module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5R2Omega
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a

public section

namespace CFSG.Quasithin.H13.R2

open CFSG.Open
open scoped commutatorElement

variable {P : Type} [Group P] [Finite P]

@[expose] def omegaSecond (P : Type) [Group P] : Subgroup P where
  carrier := {g | g ^ 3 = 1 ∧ ∀ k : P, ⁅g, k⁆ ∈ Subgroup.center P}
  mul_mem' := by
    rintro g g' ⟨hg3, hg⟩ ⟨hg'3, hg'⟩
    have hcen : ∀ (u : P), (∀ k, ⁅u, k⁆ ∈ Subgroup.center P) → ∀ l k : P,
        ⁅u, l⁆ * k = k * ⁅u, l⁆ := fun u hu l k => (Subgroup.mem_center_iff.mp (hu l) k).symm
    refine ⟨?_, fun k => ?_⟩
    · rw [mul_pow_of_central (hcen g' hg' g), show Nat.choose 3 2 = 3 from rfl,
        ← comm_pow_right_of_central (hcen g' hg'), hg3, hg'3, commutatorElement_one_right,
        mul_one, mul_one]
    · have e : ⁅g * g', k⁆ = g * ⁅g', k⁆ * g⁻¹ * ⁅g, k⁆ := by
        simp only [commutatorElement_def]; group
      rw [e, ← hcen g' hg' k g, mul_inv_cancel_right]
      exact Subgroup.mul_mem _ (hg' k) (hg k)
  one_mem' := ⟨one_pow 3, fun k => by rw [commutatorElement_one_left]; exact Subgroup.one_mem _⟩
  inv_mem' := by
    rintro g ⟨hg3, hg⟩
    refine ⟨by rw [inv_pow, hg3, inv_one], fun k => ?_⟩
    rw [comm_inv_left_of_central fun l => (Subgroup.mem_center_iff.mp (hg k) l).symm]
    exact Subgroup.inv_mem _ (hg k)

omit [Finite P] in
theorem mem_omegaSecond_of_mulAut (φ : MulAut P) {g : P} (hg : g ∈ omegaSecond P) :
    φ g ∈ omegaSecond P := by
  refine ⟨by rw [← map_pow, hg.1, map_one], fun k => ?_⟩
  have e : ⁅φ g, k⁆ = φ ⁅g, φ.symm k⁆ := by rw [map_commutatorElement]; simp
  rw [e]
  exact mem_center_of_mulAut φ (hg.2 _)

omit [Finite P] in
theorem comm_mem_omegaCenter {g : P} (hg : g ∈ omegaSecond P) (k : P) :
    ⁅g, k⁆ ∈ omegaCenter P := by
  refine ⟨hg.2 k, ?_⟩
  have hc : ∀ l : P, ⁅g, k⁆ * l = l * ⁅g, k⁆ := fun l =>
    (Subgroup.mem_center_iff.mp (hg.2 k) l).symm
  rw [← comm_pow_left_of_central hc 3, hg.1, commutatorElement_one_left]

omit [Finite P] in
@[expose] noncomputable def commHomZ (g : P) (hg : ∀ k : P, ⁅g, k⁆ ∈ omegaCenter P) :
    P →* omegaCenter P :=
  (commHom g fun l k => omegaCenter_central (hg l) k).codRestrict _ hg

omit [Finite P] in
theorem mem_ker_commHomZ {g : P} (hg : ∀ k : P, ⁅g, k⁆ ∈ omegaCenter P) {k : P} :
    k ∈ (commHomZ g hg).ker ↔ g * k = k * g := by
  rw [MonoidHom.mem_ker, ← commutatorElement_eq_one_iff_mul_comm]
  constructor
  · intro h1; exact congrArg Subtype.val h1
  · intro h1; exact Subtype.ext h1

theorem index_ker_commHomZ_le {g : P} (hg : ∀ k : P, ⁅g, k⁆ ∈ omegaCenter P) :
    (commHomZ g hg).ker.index ≤ Nat.card (omegaCenter P) := by
  rw [Subgroup.index_ker]
  exact Subgroup.card_le_card_group _

omit [Finite P] in
theorem omegaCenter_le_center : omegaCenter P ≤ Subgroup.center P := fun _ hz => hz.1

theorem sup_zpowers_eq_of_card {Z N : Subgroup P} (hZN : Z ≤ N) (hZ3 : Nat.card Z = 3)
    (hN9 : Nat.card N = 9) {n : P} (hn : n ∈ N) (hnZ : n ∉ Z) : Z ⊔ Subgroup.zpowers n = N := by
  have hle : Z ⊔ Subgroup.zpowers n ≤ N := sup_le hZN (Subgroup.zpowers_le.mpr hn)
  have hlt := Subgroup.card_lt_of_lt (lt_sup_zpowers hnZ)
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [hN9] at hdvd
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hN9]
  have hmem : Nat.card ↥(Z ⊔ Subgroup.zpowers n) ∈ Nat.divisors 9 :=
    Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  rw [show Nat.divisors 9 = {1, 3, 9} by decide] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  omega

omit [Finite P] in
theorem le_centralizer_of_gen {Z N : Subgroup P} (hZ : Z ≤ Subgroup.center P) {n : P}
    (hN : Z ⊔ Subgroup.zpowers n = N) {c : P} (hcn : n * c = c * n) :
    N ≤ Subgroup.centralizer ({c} : Set P) := by
  rw [← hN]
  refine sup_le (fun z hz => ?_) ?_
  · rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff.mp hw]
    exact Subgroup.mem_center_iff.mp (hZ hz) c
  · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff.mp hw]
    exact hcn.symm

omit [Finite P] in
theorem mem_centralizer_of_le {N : Subgroup P} {c : P}
    (h : N ≤ Subgroup.centralizer ({c} : Set P)) : c ∈ Subgroup.centralizer (N : Set P) := by
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have := h hw
  rw [Subgroup.mem_centralizer_iff] at this
  exact (this c (Set.mem_singleton c)).symm

omit [Finite P] in
theorem mem_centralizer_of_gens {Z N W : Subgroup P} (hZ : Z ≤ Subgroup.center P) {n g : P}
    (hN : Z ⊔ Subgroup.zpowers n = N) (hW : N ⊔ Subgroup.zpowers g = W) {c : P}
    (hcn : n * c = c * n) (hcg : g * c = c * g) : c ∈ Subgroup.centralizer (W : Set P) := by
  refine mem_centralizer_of_le ?_
  rw [← hW]
  refine sup_le (le_centralizer_of_gen hZ hN hcn) ?_
  rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
  intro w hw
  rw [Set.mem_singleton_iff.mp hw]
  exact hcg.symm

theorem exists_mem_not_mem_omegaCenter {N : Subgroup P} (hN9 : Nat.card N = 9)
    (h3Z : Nat.card (omegaCenter P) = 3) : ∃ n ∈ N, n ∉ omegaCenter P := by
  by_contra hcon
  push Not at hcon
  have := Subgroup.card_le_of_le (show N ≤ omegaCenter P from hcon)
  omega

theorem exists_normal_e9 {x y : P} {a s : MulAut P} (h : Hyp P x y a s)
    (h3Z : Nat.card (omegaCenter P) = 3) (hnc : ∃ g k : P, g * k ≠ k * g) :
    ∃ N : Subgroup P, N.Normal ∧ Nat.card N = 9 ∧ IsElemAbelian 3 N ∧ omegaCenter P ≤ N ∧
      ∀ m ∈ N, ∀ k : P, ⁅m, k⁆ ∈ omegaCenter P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (IsPGroup 3 P) := ⟨h.p3⟩
  have hncyc : ¬ IsCyclic P := by
    intro hcyc
    obtain ⟨g, k, hgk⟩ := hnc
    let _ := IsCyclic.commGroup (α := P)
    exact hgk (mul_comm g k)
  obtain ⟨N, hNn, hN9, hNe⟩ := CFSG.lemma_4_5_a (p := 3) (by norm_num) hncyc
  have hN9' : Nat.card N = 9 := by rw [hN9]; norm_num
  have hNE : IsElemAbelian 3 N := ⟨hNe.toIsMulCommutative, fun g hg => by
    have := hNe
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian g hg⟩
  have hZN : omegaCenter P ≤ N := fun z hz =>
    mem_of_commute_of_card_nine h hNE hN9' hz.2 fun e _ => omegaCenter_central hz e
  refine ⟨N, hNn, hN9', hNE, hZN, ?_⟩
  set π := QuotientGroup.mk' (omegaCenter P) with hπdef
  have hmemZ : ∀ g, π g = 1 → g ∈ omegaCenter P := fun g hg => (QuotientGroup.eq_one_iff _).mp hg
  obtain ⟨n, hnN, hnZ⟩ := exists_mem_not_mem_omegaCenter hN9' h3Z
  have : Group.IsNilpotent (P ⧸ omegaCenter P) := (h.p3.to_quotient _).isNilpotent
  have hMn : (N.map π).Normal := Subgroup.Normal.map hNn π (QuotientGroup.mk'_surjective _)
  have hMne : N.map π ≠ ⊥ := by
    intro hb
    have hn1 : π n ∈ N.map π := ⟨n, hnN, rfl⟩
    rw [hb, Subgroup.mem_bot] at hn1
    exact hnZ (hmemZ n hn1)
  obtain ⟨⟨q, hq⟩, hq1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hMne)
  obtain ⟨⟨n', hn'N, rfl⟩, hqC⟩ := Subgroup.mem_inf.mp hq
  have hn'Z : n' ∉ omegaCenter P := fun hz =>
    hq1 (Subtype.ext ((QuotientGroup.eq_one_iff _).mpr hz))
  have hNcen : N ≤ (Subgroup.center (P ⧸ omegaCenter P)).comap π := by
    rw [← sup_zpowers_eq_of_card hZN h3Z hN9' hn'N hn'Z]
    refine sup_le (fun z hz => ?_) (Subgroup.zpowers_le.mpr hqC)
    rw [Subgroup.mem_comap, show π z = 1 from (QuotientGroup.eq_one_iff _).mpr hz]
    exact Subgroup.one_mem _
  intro m hm k
  apply hmemZ
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact (Subgroup.mem_center_iff.mp (Subgroup.mem_comap.mp (hNcen hm)) (π k)).symm

theorem not_omegaSecond_le {x y : P} {a s : MulAut P} (h : Hyp P x y a s)
    (h3Z : Nat.card (omegaCenter P) = 3) {N : Subgroup P} (hN9 : Nat.card N = 9)
    (hZN : omegaCenter P ≤ N) (hNW2 : N ≤ omegaSecond P) : ¬ omegaSecond P ≤ N := by
  intro hW
  obtain ⟨n, hnN, hnZ⟩ := exists_mem_not_mem_omegaCenter hN9 h3Z
  have hNn := sup_zpowers_eq_of_card hZN h3Z hN9 hnN hnZ
  have hCinv : ∀ φ : MulAut P, ∀ c ∈ Subgroup.centralizer (omegaSecond P : Set P),
      φ c ∈ Subgroup.centralizer (omegaSecond P : Set P) := by
    intro φ c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro w hw
    have e := congrArg φ (hc (φ.symm w) (mem_omegaSecond_of_mulAut φ.symm hw))
    simpa using e
  have hnW2 : n ∈ omegaSecond P := hNW2 hnN
  have hnZ' : ∀ k, ⁅n, k⁆ ∈ omegaCenter P := comm_mem_omegaCenter hnW2
  rcases le_frattini_or_eq_top h (hCinv a) (hCinv s) with hle | htop
  · have hker : (commHomZ n hnZ').ker ≤ frattini P := fun k hk =>
      hle (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hW) (mem_centralizer_of_le
        (le_centralizer_of_gen omegaCenter_le_center hNn ((mem_ker_commHomZ hnZ').mp hk))))
    have h1 := Subgroup.index_dvd_of_le hker
    rw [h.index] at h1
    have h2 := index_ker_commHomZ_le hnZ'
    rw [h3Z] at h2
    have h3 : (commHomZ n hnZ').ker.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    obtain ⟨t, ht⟩ := h1
    omega
  · apply hnZ
    refine ⟨Subgroup.mem_center_iff.mpr fun k => ?_, hnW2.1⟩
    have hk : k ∈ Subgroup.centralizer (omegaSecond P : Set P) := htop ▸ Subgroup.mem_top k
    exact (Subgroup.mem_centralizer_iff.mp hk n hnW2).symm

theorem case2 {x y : P} {a s : MulAut P} (h : Hyp P x y a s)
    (h3Z : Nat.card (omegaCenter P) = 3) (hnc : ∃ g k : P, g * k ≠ k * g) :
    Nat.card P = 27 ∧ ∀ g : P, g ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (IsPGroup 3 P) := ⟨h.p3⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp h.p3
  obtain ⟨N, -, hN9, hNE, hZN, hNZ⟩ := exists_normal_e9 h h3Z hnc
  have hNW2 : N ≤ omegaSecond P := fun l hl => ⟨hNE.2 l hl, fun k => (hNZ l hl k).1⟩
  obtain ⟨g, hgW2, hgN⟩ := IsConcreteLE.not_le_iff_exists.mp
    (not_omegaSecond_le h h3Z hN9 hZN hNW2)
  obtain ⟨n, hnN, hnZ⟩ := exists_mem_not_mem_omegaCenter hN9 h3Z
  have hNn := sup_zpowers_eq_of_card hZN h3Z hN9 hnN hnZ
  obtain ⟨W, hWdef⟩ : ∃ W : Subgroup P, N ⊔ Subgroup.zpowers g = W := ⟨_, rfl⟩
  have hNW : N < W := by rw [← hWdef]; exact lt_sup_zpowers hgN
  have hWW2 : W ≤ omegaSecond P := by
    rw [← hWdef]; exact sup_le hNW2 (Subgroup.zpowers_le.mpr hgW2)
  have hW27 : 27 ≤ Nat.card W := by
    have hlt := Subgroup.card_lt_of_lt hNW
    rw [hN9] at hlt
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
      (hm ▸ Subgroup.card_subgroup_dvd_card W)
    rw [hi] at hlt ⊢
    have h3i : 3 ≤ i := by
      by_contra hc
      have := Nat.pow_le_pow_right (by norm_num : 0 < 3) (show i ≤ 2 by omega)
      norm_num at this
      omega
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ i := Nat.pow_le_pow_right (by norm_num) h3i
  have hgZ : ∀ k, ⁅g, k⁆ ∈ omegaCenter P := comm_mem_omegaCenter hgW2
  have hnZ' : ∀ k, ⁅n, k⁆ ∈ omegaCenter P := comm_mem_omegaCenter (hNW2 hnN)
  obtain ⟨f, hf⟩ : ∃ f : P →* ↥(omegaCenter P) × ↥(omegaCenter P),
      f = (commHomZ n hnZ').prod (commHomZ g hgZ) := ⟨_, rfl⟩
  have hKC : ∀ k ∈ f.ker, k ∈ Subgroup.centralizer (W : Set P) := by
    intro k hk
    rw [MonoidHom.mem_ker, hf, MonoidHom.prod_apply, Prod.mk_eq_one] at hk
    exact mem_centralizer_of_gens omegaCenter_le_center hNn hWdef
      ((mem_ker_commHomZ hnZ').mp (MonoidHom.mem_ker.mpr hk.1))
      ((mem_ker_commHomZ hgZ).mp (MonoidHom.mem_ker.mpr hk.2))
  have hΦK : frattini P ≤ f.ker :=
    CFSG.SectionRank.Ccomm.frattini_le_ker_of_elementary (p := 3) f
      (fun u v => Prod.ext (Subtype.ext (omegaCenter_central u.1.2 v.1))
        (Subtype.ext (omegaCenter_central u.2.2 v.2)))
      (fun u => Prod.ext (Subtype.ext u.1.2.2) (Subtype.ext u.2.2.2))
  obtain ⟨ρ, hρ⟩ : ∃ ρ : W →* P ⧸ f.ker, ρ = (QuotientGroup.mk' f.ker).comp W.subtype :=
    ⟨_, rfl⟩
  have hρw : ∀ w : W, ρ w = ((w : P) : P ⧸ f.ker) := fun w => by rw [hρ]; rfl
  have hker3 : Nat.card ρ.ker ≤ 3 := by
    have hEW : ρ.ker.map W.subtype ≤ W := by
      rintro _ ⟨w, -, rfl⟩
      exact w.2
    have hEC : ∀ e ∈ ρ.ker.map W.subtype, e ∈ Subgroup.centralizer (W : Set P) := by
      rintro _ ⟨w, hw, rfl⟩
      apply hKC
      have hw' : ρ w = 1 := hw
      rw [hρw, QuotientGroup.eq_one_iff] at hw'
      exact hw'
    have hEab : IsElemAbelian 3 (ρ.ker.map W.subtype) := by
      refine ⟨⟨⟨fun u v => Subtype.ext ?_⟩⟩, fun e he => (hWW2 (hEW he)).1⟩
      exact Subgroup.mem_centralizer_iff.mp (hEC v v.2) u (hEW u.2)
    have hE9 := h.m3 _ hEab
    have hEne9 : Nat.card (ρ.ker.map W.subtype) ≠ 9 := by
      intro hE9'
      have hWE : W ≤ ρ.ker.map W.subtype := fun w hw =>
        mem_of_commute_of_card_nine h hEab hE9' (hWW2 hw).1
          fun e he => Subgroup.mem_centralizer_iff.mp (hEC e he) w hw
      have := Subgroup.card_le_of_le hWE
      omega
    rw [← Subgroup.card_map_of_injective (K := ρ.ker) (f := W.subtype) Subtype.val_injective]
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
      (hm ▸ Subgroup.card_subgroup_dvd_card (ρ.ker.map W.subtype))
    rw [hi] at hE9 hEne9 ⊢
    have hi2 : i ≤ 2 := by
      by_contra hc
      have := Nat.pow_le_pow_right (by norm_num : 0 < 3) (show 3 ≤ i by omega)
      norm_num at this
      omega
    interval_cases i
    · norm_num
    · norm_num
    · exact absurd (by norm_num) hEne9
  have hρcard : Nat.card ρ.ker * Nat.card ρ.range = Nat.card W := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  have hK9 : f.ker.index ≤ 9 := by
    have := Subgroup.index_dvd_of_le hΦK
    rw [h.index] at this
    exact Nat.le_of_dvd (by norm_num) this
  have hrange : Nat.card ρ.range ≤ f.ker.index := Subgroup.card_le_card_group ρ.range
  have hr9 : 9 ≤ Nat.card ρ.range := by
    have h1 : 27 ≤ Nat.card ρ.ker * Nat.card ρ.range := by rw [hρcard]; exact hW27
    have h2 : Nat.card ρ.ker * Nat.card ρ.range ≤ 3 * Nat.card ρ.range :=
      Nat.mul_le_mul_right _ hker3
    omega
  have hKidx : f.ker.index = 9 := by omega
  have hρtop : ρ.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    show Nat.card ρ.range = f.ker.index
    omega
  have hWK : W ⊔ f.ker = ⊤ := by
    rw [eq_top_iff]
    intro p _
    obtain ⟨w, hw⟩ : (p : P ⧸ f.ker) ∈ ρ.range := hρtop ▸ Subgroup.mem_top _
    rw [hρw] at hw
    have hwp : (w : P)⁻¹ * p ∈ f.ker := QuotientGroup.eq.mp hw
    simpa using Subgroup.mul_mem_sup w.2 hwp
  have hKΦ : frattini P = f.ker := by
    refine Subgroup.eq_of_le_of_card_ge hΦK ?_
    have e1 := Subgroup.card_mul_index f.ker
    have e2 := Subgroup.card_mul_index (frattini P)
    rw [hKidx] at e1
    rw [h.index] at e2
    omega
  have hWtop : W = ⊤ := frattini_nongenerating (by rw [hKΦ]; exact hWK)
  have hall : ∀ q : P, q ∈ W := fun q => hWtop ▸ Subgroup.mem_top q
  refine ⟨?_, fun q => (hWW2 (hall q)).1⟩
  have hΦZ : frattini P ≤ omegaCenter P := by
    intro q hq
    have hqC := hKC q (hΦK hq)
    exact ⟨Subgroup.mem_center_iff.mpr fun l => Subgroup.mem_centralizer_iff.mp hqC l (hall l),
      (hWW2 (hall q)).1⟩
  have e1 := Subgroup.card_mul_index (frattini P)
  rw [h.index] at e1
  have e2 := Subgroup.card_le_of_le hΦZ
  rw [h3Z] at e2
  have e3 := Subgroup.card_le_card_group W
  omega

end CFSG.Quasithin.H13.R2
