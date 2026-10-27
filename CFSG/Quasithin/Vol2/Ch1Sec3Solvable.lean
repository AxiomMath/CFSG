module

public import CFSG.Quasithin.Vol2.Ch1Sec3Basic
public import CFSG.Quasithin.Background.A1cA132
import CFSG.Quasithin.Background.OrderingMax
import CFSG.LocalAnalysis.QuasithinUnique.CharTwoInheritance

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits
open scoped commutatorElement

namespace Ch1Sec3

section General

variable {Γ : Type*} [Group Γ]

theorem commutator_mem_centralizer_of_isCyclic {C : Subgroup Γ} [C.Normal] (hC : IsCyclic C)
    (a b : Γ) : ⁅a, b⁆ ∈ Subgroup.centralizer (C : Set Γ) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := C)
  have hconj : ∀ h : Γ, ∃ k : ℤ, h * (g : Γ) * h⁻¹ = (g : Γ) ^ k := by
    intro h
    have hmem : h * (g : Γ) * h⁻¹ ∈ C := ‹C.Normal›.conj_mem _ g.2 h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨_, hmem⟩)
    exact ⟨k, by rw [← Subgroup.coe_zpow, hk]⟩
  have hswap : ∀ x y : Γ,
      (x * y) * (g : Γ) * (x * y)⁻¹ = (y * x) * (g : Γ) * (y * x)⁻¹ := by
    intro x y
    obtain ⟨i, hi⟩ := hconj x
    obtain ⟨j, hj⟩ := hconj y
    have e1 : (x * y) * (g : Γ) * (x * y)⁻¹ = x * (y * (g : Γ) * y⁻¹) * x⁻¹ := by group
    have e2 : (y * x) * (g : Γ) * (y * x)⁻¹ = y * (x * (g : Γ) * x⁻¹) * y⁻¹ := by group
    rw [e1, e2, hi, hj, ← conj_zpow, ← conj_zpow, hi, hj, ← zpow_mul, ← zpow_mul, mul_comm]
  have hcomm : ⁅a, b⁆ * (g : Γ) = (g : Γ) * ⁅a, b⁆ := by
    have h1 := hswap a⁻¹ b⁻¹
    rw [commutatorElement_def]
    have e : a * b * a⁻¹ * b⁻¹ * (g : Γ) =
        a * b * ((a⁻¹ * b⁻¹) * (g : Γ) * (a⁻¹ * b⁻¹)⁻¹) * a⁻¹ * b⁻¹ := by group
    rw [e, h1]
    group
  rw [Subgroup.mem_centralizer_iff]
  intro c hc
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨c, hc⟩)
  have hck : c = (g : Γ) ^ k := by rw [← Subgroup.coe_zpow, hk]
  rw [hck]
  exact ((Commute.zpow_left hcomm.symm k)).eq

theorem commutator_le_centralizer_of_isCyclic {C : Subgroup Γ} [C.Normal] (hC : IsCyclic C) :
    commutator Γ ≤ Subgroup.centralizer (C : Set Γ) := by
  rw [commutator_def, Subgroup.commutator_le]
  exact fun a _ b _ => commutator_mem_centralizer_of_isCyclic hC a b

theorem normal_map_of_characteristic {R : Subgroup Γ} [R.Normal] (Y : Subgroup R)
    [Y.Characteristic] : (Y.map R.subtype).Normal := by
  rw [← Subgroup.normalizer_eq_top_iff]
  refine eq_top_iff.2 ?_
  rw [← Subgroup.normalizer_eq_top R]
  exact normalizer_le_normalizer_map_of_characteristic Y

variable [Finite Γ]

theorem classLeTwo_of_card_le {p : ℕ} [hp : Fact p.Prime] {P : Subgroup Γ} (hP : IsPGroup p P)
    (hc : Nat.card P ≤ p ^ 3) : ClassLeTwo P := by
  by_cases hcomm : ∀ a b : P, a * b = b * a
  · have h1 : ⁅P, P⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact congrArg Subtype.val (hcomm ⟨b, hb⟩ ⟨a, ha⟩)
    unfold ClassLeTwo
    rw [h1, Subgroup.commutator_bot_left]
  · obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hP
    have hk3 : k ≤ 3 := (Nat.pow_le_pow_iff_right hp.out.one_lt).1 (hk ▸ hc)
    have hk3' : k = 3 := by
      by_contra hne
      exact hcomm (commutative_of_card_le_prime_sq hP
        (hk ▸ Nat.pow_le_pow_right hp.out.pos (by omega)))
    have hnc : ∃ a b : P, a * b ≠ b * a := by
      push Not at hcomm
      exact hcomm
    obtain ⟨hcz, -⟩ := CFSG.SectionRank.Ccomm.nonabelian_prime_cube_central_structure
      (hk3' ▸ hk) hnc
    have h2 : ⁅⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆, (⊤ : Subgroup P)⁆ = ⊥ := by
      rw [← commutator_def, hcz, Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact Subgroup.center_le_centralizer _
    have h3 := congrArg (Subgroup.map P.subtype) h2
    rw [Subgroup.map_commutator, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype, Subgroup.map_bot] at h3
    exact h3

theorem two_le_pRank_of_pow_eq_one {p : ℕ} [hp : Fact p.Prime] {P : Subgroup Γ}
    (hexp : ∀ x ∈ P, x ^ p = 1) (hc : p ^ 2 ≤ Nat.card P) : 2 ≤ Open.pRank p P := by
  have hP : IsPGroup p P := fun x => ⟨1, Subtype.ext (by simpa using hexp x x.2)⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hP
  have hk2 : 2 ≤ k := (Nat.pow_le_pow_iff_right hp.out.one_lt).1 (hk ▸ hc)
  obtain ⟨E, hE⟩ := Sylow.exists_subgroup_card_pow_prime (G := P) p (n := 2)
    (hk ▸ pow_dvd_pow p hk2)
  have hEc : IsMulCommutative E := IsPGroup.isMulCommutative_of_card_eq_prime_sq hE
  have hEel : IsElemAbelian p E :=
    ⟨hEc, fun x _ => Subtype.ext (by simpa using hexp (x : Γ) x.2)⟩
  refine CFSG.SectionRank.le_pRank hp.out.one_lt (Subgroup.map_subtype_le E)
    (CFSG.SectionRank.isElemAbelian_map hEel P.subtype) ?_
  rw [Subgroup.card_map_of_injective P.subtype_injective, hE]

theorem isCyclic_of_pRank_le_one {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hΓ : IsPGroup p Γ)
    (h : Open.pRank p (⊤ : Subgroup Γ) ≤ 1) : IsCyclic Γ := by
  by_contra hnc
  have : Fact (IsPGroup p Γ) := ⟨hΓ⟩
  obtain ⟨S, -, hScard, hSel⟩ := CFSG.lemma_4_5_a hp2 hnc
  have hE : IsElemAbelian p S :=
    ⟨hSel.toIsMulCommutative, fun x hx => CFSG.elemPow_eq_one_of_isElementaryAbelian x hx⟩
  have := CFSG.SectionRank.le_pRank hp.out.one_lt le_top hE hScard
  omega

theorem le_pCore_of_le_fittingSubgroup {p : ℕ} [hp : Fact p.Prime] {P : Subgroup Γ}
    (hP : IsPGroup p P) (h : P ≤ CFSG.fittingSubgroup Γ) : P ≤ CFSG.pCore p Γ := by
  set F := CFSG.fittingSubgroup Γ
  have hP' : IsPGroup p (P.subgroupOf F) := hP.of_equiv (Subgroup.subgroupOfEquivOfLe h).symm
  obtain ⟨S, hS⟩ := hP'.exists_le_sylow
  have h1 := Sylow.map_le_pCore (CFSG.fittingSubgroup_normal) (CFSG.fittingSubgroup_nilpotent) p S
  calc P = (P.subgroupOf F).map F.subtype := (Subgroup.map_subgroupOf_eq_of_le h).symm
    _ ≤ (S : Subgroup F).map F.subtype := Subgroup.map_mono hS
    _ ≤ CFSG.pCore p Γ := h1

end General

section Transfer

variable {A B : Type*} [Group A] [Group B]

theorem irreducible_map (φ : A →* B) {P S : Subgroup A}
    (hSP : S ≤ Subgroup.normalizer (P : Set A))
    (hirr : ∀ U : Subgroup A, ⁅P, P⁆ ≤ U → U ≤ P → S ≤ Subgroup.normalizer (U : Set A) →
      U = ⁅P, P⁆ ∨ U = P) :
    ∀ U : Subgroup B, ⁅P.map φ, P.map φ⁆ ≤ U → U ≤ P.map φ →
      S.map φ ≤ Subgroup.normalizer (U : Set B) → U = ⁅P.map φ, P.map φ⁆ ∨ U = P.map φ := by
  intro U hU1 hU2 hU3
  set V := U.comap φ ⊓ P with hV
  have hPP : ⁅P, P⁆ ≤ P := commutator_le_left_of_le_normalizer Subgroup.le_normalizer
  have hV1 : ⁅P, P⁆ ≤ V := by
    refine le_inf ?_ hPP
    rw [← Subgroup.map_le_iff_le_comap, Subgroup.map_commutator]
    exact hU1
  have hV3 : S ≤ Subgroup.normalizer (V : Set A) := by
    intro s hs
    have hsU : φ s ∈ Subgroup.normalizer (U : Set B) := hU3 ⟨s, hs, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := Subgroup.mem_normalizer_iff.mp hsU (φ x)
    have h2 := Subgroup.mem_normalizer_iff.mp (hSP hs) x
    simp only [hV, Subgroup.mem_inf, Subgroup.mem_comap, map_mul, map_inv]
    rw [← h1, ← h2]
  have hUV : U = V.map φ := by
    refine le_antisymm (fun y hy => ?_) ?_
    · obtain ⟨x, hx, rfl⟩ := hU2 hy
      exact ⟨x, ⟨hy, hx⟩, rfl⟩
    · rw [Subgroup.map_le_iff_le_comap]
      exact inf_le_left
  rcases hirr V hV1 inf_le_right hV3 with h | h
  · left
    rw [hUV, h, Subgroup.map_commutator]
  · right
    rw [hUV, h]

theorem irreducible_of_map {ι : A →* B} (hι : Function.Injective ι) {P S : Subgroup A}
    (hirr : ∀ U : Subgroup B, ⁅P.map ι, P.map ι⁆ ≤ U → U ≤ P.map ι →
      S.map ι ≤ Subgroup.normalizer (U : Set B) → U = ⁅P.map ι, P.map ι⁆ ∨ U = P.map ι) :
    ∀ U : Subgroup A, ⁅P, P⁆ ≤ U → U ≤ P → S ≤ Subgroup.normalizer (U : Set A) →
      U = ⁅P, P⁆ ∨ U = P := by
  intro U hU1 hU2 hU3
  have hinj := Subgroup.map_injective hι
  have h1 : ⁅P.map ι, P.map ι⁆ ≤ U.map ι := by
    rw [← Subgroup.map_commutator]
    exact Subgroup.map_mono hU1
  have h3 : S.map ι ≤ Subgroup.normalizer (U.map ι : Set B) :=
    (Subgroup.map_mono hU3).trans (Subgroup.le_normalizer_map ι)
  rcases hirr (U.map ι) h1 (Subgroup.map_mono hU2) h3 with h | h
  · left
    apply hinj
    rw [h, Subgroup.map_commutator]
  · right
    exact hinj h

theorem card_map_of_inf_ker_eq_bot {φ : A →* B} {P : Subgroup A} (h : P ⊓ φ.ker = ⊥) :
    Nat.card (P.map φ) = Nat.card P := by
  have hinj : Function.Injective (φ.comp P.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hx' : (x : A) ∈ P ⊓ φ.ker := ⟨x.2, hx⟩
    rw [h, Subgroup.mem_bot] at hx'
    exact (Subgroup.mem_bot).2 (Subtype.ext hx')
  rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, MonoidHom.range_comp,
    Subgroup.range_subtype]

end Transfer

section Core

variable {Γ : Type*} [Group Γ]

theorem isSupercritical_map {r : ℕ} {R₀ : Subgroup Γ} {Y : Subgroup R₀} (hR₀ : IsPGroup r R₀)
    (hY : IsSupercritical r Y) :
    IsPGroup r (Y.map R₀.subtype) ∧ (∀ x ∈ Y.map R₀.subtype, x ^ r = 1) ∧
      ClassLeTwo (Y.map R₀.subtype) := by
  refine ⟨(hR₀.to_subgroup Y).map R₀.subtype, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    rw [← map_pow, hY.pow_eq_one y hy, map_one]
  · have h := hY.classLeTwo
    unfold ClassLeTwo at h ⊢
    rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, h, Subgroup.map_bot]

theorem closure_pow_eq {r : ℕ} {R : Subgroup Γ} (h : ∀ x ∈ R, x ^ r = 1) :
    Subgroup.closure {x | x ∈ R ∧ x ^ r = 1} = R :=
  le_antisymm ((Subgroup.closure_le R).2 fun _ hx => hx.1)
    fun x hx => Subgroup.subset_closure ⟨hx, h x hx⟩

variable [Finite Γ]

theorem normal_of_solvable_quotient (hsolv : Group.IsSolvable Γ) (hO2 : CFSG.pCore 2 Γ = ⊥)
    (hrank : ∀ r : ℕ, r.Prime → r ≠ 2 → Open.pRank r (⊤ : Subgroup Γ) ≤ 2)
    {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {P S : Subgroup Γ} (hPp : IsPGroup p P)
    (hexp : ∀ x ∈ P, x ^ p = 1) (hc2 : p ^ 2 ≤ Nat.card P) (hc3 : Nat.card P ≤ p ^ 3)
    (hSP : S ≤ Subgroup.normalizer (P : Set Γ))
    (hirr : ∀ U : Subgroup Γ, ⁅P, P⁆ ≤ U → U ≤ P → S ≤ Subgroup.normalizer (U : Set Γ) →
      U = ⁅P, P⁆ ∨ U = P)
    (hPc : P ≤ commutator Γ) : P.Normal := by
  have hp1 := hp.out.one_lt
  have hPΩ : Subgroup.closure {x | x ∈ P ∧ x ^ p = 1} = P := closure_pow_eq hexp
  have hPcl : ClassLeTwo P := classLeTwo_of_card_le hPp hc3
  have hPrk2 : 2 ≤ Open.pRank p P := two_le_pRank_of_pow_eq_one hexp hc2
  have hPrk : Open.pRank p P = 2 := le_antisymm
    ((CFSG.SectionRank.pRank_mono hp1 le_top).trans (hrank p hp.out hp2)) hPrk2
  have hΦ : frattiniIn P = ⁅P, P⁆ := frattiniIn_eq_commutator hPp hexp
  have hPne : P ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hc2
    have : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero hp1
    omega
  have hirrN : A1c.IsNormalizerIrreducible P := by
    refine ⟨frattiniIn_ne_of_ne_bot hPne, fun U hU1 hU2 hU3 => ?_⟩
    rw [hΦ] at hU1 ⊢
    exact hirr U hU1 hU2 (hSP.trans hU3)
  by_contra hN
  have hA : ∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ p →
      P ≤ Subgroup.centralizer (CFSG.pCore r Γ : Set Γ) := by
    intro r hr hr2 hrp
    have : Fact r.Prime := ⟨hr⟩
    set R₀ := CFSG.pCore r Γ with hR₀
    have hR₀p : IsPGroup r R₀ := CFSG.pCore_isPGroup
    obtain ⟨Y, hY, hYf⟩ := exists_isSupercritical_faithful hr2 hR₀p
    have : Y.Characteristic := hY.characteristic
    have : (Y.map R₀.subtype).Normal := normal_map_of_characteristic Y
    obtain ⟨hRr, hRexp, hRcl⟩ := isSupercritical_map hR₀p hY
    have hRrk : Open.pRank r (Y.map R₀.subtype) ≤ 2 :=
      (CFSG.SectionRank.pRank_mono hr.one_lt le_top).trans (hrank r hr hr2)
    rcases A1c.commutator_eq_bot_or_isPOnePlusTwo hr2 hp2 hRr (closure_pow_eq hRexp) hRcl hRrk
      hPp hPΩ hPcl hPrk hirrN with h | ⟨hpr, -⟩
    · intro x hx
      have hxY : ∀ y : R₀, y ∈ Y → x * (y : Γ) = y * x := fun y hy => by
        have hyR : (y : Γ) ∈ Y.map R₀.subtype := ⟨y, hy, rfl⟩
        have h1 := Subgroup.commutator_mem_commutator hyR hx
        rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
        exact h1.symm
      have hα : (MulAut.conjNormal x : MulAut R₀) = 1 := by
        refine hYf _ ?_ fun y hy => ?_
        · have h1 : (MulAut.conjNormal x : MulAut R₀) ^ p = 1 := by
            rw [← map_pow, hexp x hx, map_one]
          exact Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one h1)
            ((Nat.coprime_primes hp.out hr).2 (Ne.symm hrp))
        · have h2 : (MulAut.conjNormal x : MulAut R₀) y = y := by
            apply Subtype.ext
            rw [MulAut.conjNormal_apply, hxY y hy, mul_inv_cancel_right]
          rw [h2, inv_mul_cancel]
          exact Subgroup.one_mem _
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (A1c.mul_comm_of_conjNormal_eq_one hα hy).symm
    · exact absurd hpr (Ne.symm hrp)
  have hB : P ≤ Subgroup.centralizer (CFSG.pCore p Γ : Set Γ) ∧
      Open.pRank p (CFSG.pCore p Γ) ≤ 1 := by
    set R₀ := CFSG.pCore p Γ with hR₀
    have hR₀p : IsPGroup p R₀ := CFSG.pCore_isPGroup
    by_cases hbot : R₀ = ⊥
    · refine ⟨fun x _ => ?_, ?_⟩
      · rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [hbot, Subgroup.coe_bot, Set.mem_singleton_iff] at hy
        rw [hy, one_mul, mul_one]
      · rw [hbot]
        refine CFSG.SectionRank.pRank_le hp1 fun E hE _ => ?_
        rw [le_bot_iff.1 hE, Subgroup.card_bot, pow_one]
        exact hp1.le
    · have : Nontrivial R₀ := (Subgroup.nontrivial_iff_ne_bot R₀).2 hbot
      obtain ⟨Y, hY⟩ := exists_isSupercritical hp2 hR₀p
      have : Y.Characteristic := hY.characteristic
      have : (Y.map R₀.subtype).Normal := normal_map_of_characteristic Y
      obtain ⟨hRp, hRexp, hRcl⟩ := isSupercritical_map hR₀p hY
      have hRrk : Open.pRank p (Y.map R₀.subtype) ≤ 2 :=
        (CFSG.SectionRank.pRank_mono hp1 le_top).trans (hrank p hp.out hp2)
      have hR1 : Y.map R₀.subtype ≠ ⊥ := fun h =>
        hY.ne_bot hR₀p ((Subgroup.map_eq_bot_iff_of_injective _ R₀.subtype_injective).1 h)
      have hG : Open.pRank p (⊤ : Subgroup Γ) = 2 :=
        le_antisymm (hrank p hp.out hp2) (hPrk2.trans (CFSG.SectionRank.pRank_mono hp1 le_top))
      rcases A1c.eq_or_eq_centerOf_of_pRank_eq_two hp2 hp2 rfl hR1 hRp (closure_pow_eq hRexp)
        hRcl hRrk hPp hPΩ hPcl hPrk hirrN hG with hRP | ⟨⟨e⟩, -, -⟩
      · exact (hN (hRP ▸ (inferInstance : (Y.map R₀.subtype).Normal))).elim
      · have hcardR : Nat.card (Y.map R₀.subtype) = p := by
          rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
          simp
        have hcardY : Nat.card Y = p := by
          rw [← hcardR, Subgroup.card_map_of_injective R₀.subtype_injective]
        have hYrk : Open.pRank p Y ≤ 1 := CFSG.SectionRank.pRank_le hp1 fun E hE _ => by
          rw [pow_one, ← hcardY]
          exact Subgroup.card_le_of_le hE
        have hR₀rk : Open.pRank p (⊤ : Subgroup R₀) ≤ 1 := by
          by_contra h
          push Not at h
          have := hY.one_lt_pRank hR₀p h
          omega
        refine ⟨hPc.trans (commutator_le_centralizer_of_isCyclic
          (isCyclic_of_pRank_le_one hp2 hR₀p hR₀rk)), ?_⟩
        rw [← pRank_top_subtype]
        exact hR₀rk
  have hC : P ≤ Subgroup.centralizer (CFSG.fittingSubgroup Γ : Set Γ) := by
    refine CFSG.subgroup_le_centralizer_fitting_of_le_centralizer_pCores fun q => ?_
    have hq : (q : ℕ).Prime := Nat.prime_of_mem_primeFactors q.1.2
    by_cases hq2 : (q : ℕ) = 2
    · rw [hq2, hO2]
      intro x _
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hy
      rw [hy, one_mul, mul_one]
    · by_cases hqp : (q : ℕ) = p
      · rw [hqp]
        exact hB.1
      · exact hA q hq hq2 hqp
  have hF : P ≤ CFSG.fittingSubgroup Γ :=
    hC.trans (CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv)
  have hPO : P ≤ CFSG.pCore p Γ := le_pCore_of_le_fittingSubgroup hPp hF
  have := hPrk2.trans (CFSG.SectionRank.pRank_mono hp1 hPO)
  have := hB.2
  omega

end Core

end Ch1Sec3

open Ch1Sec3

theorem normal_of_isXi_of_isSolvable {G : Type*} [Group G] [Finite G] {T X H : Subgroup G}
    (hT : CFSG.Open.quasithinIsSylowTwo T) (hX : IsXi T X) (hH : InH (X ⊔ T) H)
    (hsolv : Group.IsSolvable H) (hSQT : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p H ≤ 2) :
    H ≤ Subgroup.normalizer (X : Set G) := by
  obtain ⟨p, hp, hp2, hpX, -, -⟩ := hX.exists_prime_sup_eq
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hP, -⟩ := exists_isSylowIn_ge p (bot_le : ⊥ ≤ X) IsPGroup.of_bot
  have hXH : X ≤ H := le_sup_left.trans hH.1
  have hTH : T ≤ H := le_sup_right.trans hH.1
  have hPH : P ≤ H := hP.le.trans hXH
  set S := T ⊓ Subgroup.normalizer (P : Set G) with hS
  have hSH : S ≤ H := inf_le_left.trans hTH
  have hSP : S ≤ Subgroup.normalizer (P : Set G) := inf_le_right
  have hexp : ∀ a ∈ P, a ^ p = 1 := fun _ ha => hX.pow_eq_one hp2 hpX hP ha
  have hc2 : p ^ 2 ≤ Nat.card P := hX.sq_le_card_sylow hp2 hpX hP
  have hc3 : Nat.card P ≤ p ^ 3 := by
    rw [hX.card_sylow hp2 hpX hP]
    obtain ⟨k, -, hk3, hk⟩ := hX.relIndex_eq hp hp2 hpX
    rw [hk]
    exact Nat.pow_le_pow_right hp.pos hk3
  have hΦ : frattiniIn P = ⁅P, P⁆ := (hX.frattiniIn_eq hp2 hpX hP).1
  have hirrG : ∀ U : Subgroup G, ⁅P, P⁆ ≤ U → U ≤ P → S ≤ Subgroup.normalizer (U : Set G) →
      U = ⁅P, P⁆ ∨ U = P := by
    intro U h1 h2 h3
    rw [← hΦ] at h1 ⊢
    exact (hX.irreducible hT hp2 hpX hP).2 U h1 h2 h3
  have hPS : P ≤ ⁅P, S⁆ := (hX.eq_commutator_normalizer hT hp2 hpX hP).le
  set P₁ := P.subgroupOf H with hP₁def
  set S₁ := S.subgroupOf H with hS₁def
  have hP₁ : P₁.map H.subtype = P := Subgroup.map_subgroupOf_eq_of_le hPH
  have hS₁ : S₁.map H.subtype = S := Subgroup.map_subgroupOf_eq_of_le hSH
  have hP₁p : IsPGroup p P₁ := hP.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hPH).symm
  have hcard₁ : Nat.card P₁ = Nat.card P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPH).toEquiv
  have hirr₁ := irreducible_of_map H.subtype_injective (P := P₁) (S := S₁)
    (by rw [hP₁, hS₁]; exact hirrG)
  have hS₁P₁ : S₁ ≤ Subgroup.normalizer (P₁ : Set H) := fun s hs =>
    Subgroup.le_normalizer_comap H.subtype (hSP hs)
  have hP₁S₁ : P₁ ≤ ⁅P₁, S₁⁆ := by
    rw [← Subgroup.map_le_map_iff_of_injective H.subtype_injective, Subgroup.map_commutator, hP₁,
      hS₁]
    exact hPS
  set N := CFSG.Open.pCore 2 H with hN
  have : N.Normal := CFSG.LieType.BorelTits.pCore_normal 2
  set π := QuotientGroup.mk' N with hπ
  have hN2 : IsPGroup 2 N := CFSG.LieType.BorelTits.pCore_isPGroup 2
  have hinf : P₁ ⊓ π.ker = ⊥ := by
    rw [QuotientGroup.ker_mk']
    exact (IsPGroup.disjoint_of_ne p 2 hp2 _ _ hP₁p hN2).eq_bot
  set Pb := P₁.map π with hPb
  set Sb := S₁.map π with hSb
  have hcardb : Nat.card Pb = Nat.card P := (card_map_of_inf_ker_eq_bot hinf).trans hcard₁
  have hexpb : ∀ x ∈ Pb, x ^ p = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_pow, show y ^ p = 1 from Subtype.ext (by simpa using hexp _ hy), map_one]
  have hirrb := irreducible_map π hS₁P₁ hirr₁
  have hSbPb : Sb ≤ Subgroup.normalizer (Pb : Set (H ⧸ N)) :=
    (Subgroup.map_mono hS₁P₁).trans (Subgroup.le_normalizer_map π)
  have hPbc : Pb ≤ commutator (H ⧸ N) := by
    calc Pb ≤ ⁅P₁, S₁⁆.map π := Subgroup.map_mono hP₁S₁
      _ = ⁅Pb, Sb⁆ := Subgroup.map_commutator _ _ _
      _ ≤ commutator (H ⧸ N) := Subgroup.commutator_mono le_top le_top
  have hO2 : CFSG.pCore 2 (H ⧸ N) = ⊥ := by
    exact B6.pCore_quotient_pCore
  have hrank : ∀ r : ℕ, r.Prime → r ≠ 2 → Open.pRank r (⊤ : Subgroup (H ⧸ N)) ≤ 2 := by
    intro r hr hr2
    have : Fact r.Prime := ⟨hr⟩
    have hrN : ¬ r ∣ Nat.card N := by
      obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 hN2
      rw [ha]
      intro h
      exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h))
    rw [CFSG.SectionRank.pRank_quotient_eq N hrN, pRank_top_subtype]
    exact hSQT r hr hr2
  have hsolvb : Group.IsSolvable (H ⧸ N) := inferInstance
  have hnorm : Pb.Normal := normal_of_solvable_quotient hsolvb hO2 hrank hp2
    (hP₁p.map π) hexpb (hcardb ▸ hc2) (hcardb ▸ hc3) hSbPb hirrb hPbc
  set B := pCoreOf 2 H with hB
  set M := B ⊔ P with hM
  have hconjP : ∀ h ∈ H, ∀ z ∈ P, h * z * h⁻¹ ∈ M := by
    intro h hh z hz
    have hz₁ : (⟨z, hPH hz⟩ : H) ∈ P₁ := hz
    have hmem : π (⟨h, hh⟩ * ⟨z, hPH hz⟩ * (⟨h, hh⟩ : H)⁻¹) ∈ Pb := by
      rw [map_mul, map_mul, map_inv]
      exact hnorm.conj_mem _ ⟨_, hz₁, rfl⟩ _
    obtain ⟨w, hw, hwe⟩ := hmem
    have hker : (⟨h, hh⟩ * ⟨z, hPH hz⟩ * (⟨h, hh⟩ : H)⁻¹) * w⁻¹ ∈ N := by
      rw [← QuotientGroup.eq_one_iff]
      change π _ = 1
      rw [map_mul, map_inv, ← hwe, mul_inv_cancel]
    have e : h * z * h⁻¹ =
        H.subtype ((⟨h, hh⟩ * ⟨z, hPH hz⟩ * (⟨h, hh⟩ : H)⁻¹) * w⁻¹) * H.subtype w := by
      simp only [map_mul, map_inv, Subgroup.coe_subtype]
      group
    rw [e]
    exact M.mul_mem (Subgroup.mem_sup_left ⟨_, hker, rfl⟩) (Subgroup.mem_sup_right hw)
  have hHM : H ≤ Subgroup.normalizer (M : Set G) := by
    have key : ∀ {h : G}, h ∈ H → M.map (MulAut.conj h).toMonoidHom ≤ M := by
      intro h hh
      rw [hM, Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rw [map_conj_eq_of_mem_normalizer (le_normalizer_pCoreOf 2 H hh)]
        exact le_sup_left
      · rintro _ ⟨z, hz, rfl⟩
        exact hconjP h hh z hz
    exact fun h hh => mem_normalizer_of_map_conj_le (key hh) (key (H.inv_mem hh))
  have hXM : X ≤ M := by
    rw [(hX.eq_conjClosure hp2 hpX hP).1]
    exact conjClosure_le fun x hx z hz => hconjP x (hXH hx) z hz
  have hBX : B ⊔ X = M := le_antisymm (sup_le le_sup_left hXM) (sup_le_sup_left hP.le B)
  have h5 : X = oTwoUpper (B ⊔ X) := hX.eq_oTwoUpper_sup hT hH
  calc H ≤ Subgroup.normalizer (oTwoUpper M : Set G) :=
        hHM.trans (normalizer_le_normalizer_oTwoUpper M)
    _ = Subgroup.normalizer (X : Set G) := by rw [← hBX, ← h5]

theorem Ch1Sec3.exists_maxTwoLocal_ge_of_isTwoLocal {G : Type*} [Group G] [Finite G]
    {H : Subgroup G} (hH : IsTwoLocal H) : ∃ M : Subgroup G, quasithinIsMaxTwoLocal M ∧ H ≤ M := by
  classical
  obtain ⟨M, ⟨hM2, hHM⟩, hmax⟩ :=
    (Set.toFinite {K : Subgroup G | IsTwoLocal K ∧ H ≤ K}).exists_maximal ⟨H, hH, le_rfl⟩
  exact ⟨M, ⟨hM2, fun K hK hMK => (hmax ⟨hK, hHM.trans hMK⟩ hMK).antisymm hMK⟩, hHM⟩

theorem isUniqueM_normalizer_of_isXi_of_solvable {G : Type*} [Group G] [Finite G]
    {T X : Subgroup G} (hT : CFSG.Open.quasithinIsSylowTwo T) (hqt : CFSG.Open.evenRank G ≤ 2)
    (hX : IsXi T X) (hQ : pCoreOf 2 X ≠ ⊥)
    (hsolv : ∀ M : Subgroup G, InM (X ⊔ T) M → Group.IsSolvable M) :
    IsUniqueM (X ⊔ T) (Subgroup.normalizer (X : Set G)) := by
  set L := Subgroup.normalizer (pCoreOf 2 X : Set G) with hL
  have hL2 : IsTwoLocal L := ⟨pCoreOf 2 X, hQ, pCoreOf_isPGroup 2 X, rfl⟩
  have hXTN : X ⊔ T ≤ Subgroup.normalizer (X : Set G) := sup_le Subgroup.le_normalizer hX.2.1
  have hNL : Subgroup.normalizer (X : Set G) ≤ L := normalizer_le_normalizer_pCoreOf 2 X
  have hkey : ∀ M : Subgroup G, InM (X ⊔ T) M → M ≤ Subgroup.normalizer (X : Set G) := by
    intro M hM
    refine normal_of_isXi_of_isSolvable hT hX ⟨hM.2, pCoreOf_ne_bot_of_isTwoLocal hM.1.1⟩
      (hsolv M hM) fun p hp hp2 => ?_
    exact (CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank p hp hp2 M hM.1.1).trans hqt
  obtain ⟨M₀, hM₀, hLM₀⟩ := exists_maxTwoLocal_ge_of_isTwoLocal hL2
  have hM₀XT : InM (X ⊔ T) M₀ := ⟨hM₀, (hXTN.trans hNL).trans hLM₀⟩
  have hM₀N : M₀ = Subgroup.normalizer (X : Set G) :=
    le_antisymm (hkey M₀ hM₀XT) (hNL.trans hLM₀)
  refine ⟨hM₀N ▸ hM₀XT, fun M' hM' => ?_⟩
  have hM'L : M' ≤ L := (hkey M' hM').trans hNL
  have h1 : L = M' := hM'.1.2 L hL2 hM'L
  have h2 : L = M₀ := hM₀.2 L hL2 (hM₀N ▸ hNL)
  rw [← h1, h2, hM₀N]

theorem IsXi.pCoreOf_ne_bot {G : Type*} [Group G] [Finite G] {T X : Subgroup G}
    (hEven : CFSG.Open.quasithinEvenCharacteristic G) (hT : CFSG.Open.quasithinIsSylowTwo T)
    (hX : IsXi T X) : pCoreOf 2 X ≠ ⊥ := by
  obtain ⟨S, rfl⟩ := exists_sylow_of_quasithinIsSylowTwo hT
  have hn : (X.subgroupOf (X ⊔ (S : Subgroup G))).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (sup_le Subgroup.le_normalizer hX.2.1)
  have hc : CFSG.QuasithinUnique.CharTwo X :=
    (charTwo_of_inH hEven S ⟨le_sup_right, hX.2.2.1⟩).of_normal le_sup_left hn
  intro hQ
  have hXbot : X = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    have hxC : x ∈ Subgroup.centralizer (pCoreOf 2 X : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [hQ, Subgroup.coe_bot, Set.mem_singleton_iff] at hy
      rw [hy, one_mul, mul_one]
    have := hc ⟨hx, hxC⟩
    rwa [hQ] at this
  obtain ⟨p, hp, -, hpX, -, -⟩ := hX.exists_prime_sup_eq
  rw [hXbot, Subgroup.card_bot] at hpX
  exact hp.one_lt.ne' (Nat.dvd_one.1 hpX)

theorem isUniqueM_normalizer_of_isXi_of_solvable_of_evenCharacteristic {G : Type*} [Group G]
    [Finite G] {T X : Subgroup G} (hT : CFSG.Open.quasithinIsSylowTwo T)
    (hqt : CFSG.Open.evenRank G ≤ 2) (hX : IsXi T X)
    (hEven : CFSG.Open.quasithinEvenCharacteristic G)
    (hsolv : ∀ M : Subgroup G, InM (X ⊔ T) M → Group.IsSolvable M) :
    IsUniqueM (X ⊔ T) (Subgroup.normalizer (X : Set G)) :=
  isUniqueM_normalizer_of_isXi_of_solvable hT hqt hX (hX.pCoreOf_ne_bot hEven hT) hsolv

end CFSG.Quasithin
