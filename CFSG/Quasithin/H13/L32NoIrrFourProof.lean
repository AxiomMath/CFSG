module

public import CFSG.Quasithin.H13.L1332Inputs

public section

namespace CFSG.Quasithin.H13.L32NoIrrFourProof

open MulAction

variable {V : Type} [CommGroup V]

def fixSub (f : MulAut V) : Subgroup V where
  carrier := {v | f v = v}
  mul_mem' {a b} (ha : f a = a) (hb : f b = b) := show f (a * b) = a * b by
    rw [map_mul, ha, hb]
  one_mem' := map_one f
  inv_mem' {a} (ha : f a = a) := show f a⁻¹ = a⁻¹ by rw [map_inv, ha]

theorem mem_fixSub {f : MulAut V} {v : V} : v ∈ fixSub f ↔ f v = v := Iff.rfl

theorem smul_eq_apply {H : Subgroup (MulAut V)} (h : H) (v : V) : h • v = (h : MulAut V) v :=
  rfl

theorem pow_apply_of_apply_eq {f : MulAut V} {v : V} (hv : f v = v) (n : ℕ) : (f ^ n) v = v := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, MulAut.mul_apply, hv, ih]

variable [Finite V]

theorem card_fixSub_eq_two (hV : Nat.card V = 2 ^ 4) {H : Subgroup (MulAut V)} (g : H)
    (hg : orderOf g = 7) : Nat.card (fixSub (g : MulAut V)) = 2 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hP : IsPGroup 7 (Subgroup.zpowers g) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hg, pow_one])
  have hmod := hP.card_modEq_card_fixedPoints V
  have hfix : Nat.card (fixedPoints (Subgroup.zpowers g) V) =
      Nat.card (fixSub (g : MulAut V)) := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun v => ?_)
    rw [mem_fixedPoints, mem_fixSub]
    constructor
    · intro h
      exact h ⟨g, Subgroup.mem_zpowers g⟩
    · intro h p
      have hle : Subgroup.zpowers g ≤ stabilizer H v :=
        Subgroup.zpowers_le.2 (by rw [mem_stabilizer_iff, smul_eq_apply]; exact h)
      exact hle p.2
  rw [hfix, hV] at hmod
  have hdvd : Nat.card (fixSub (g : MulAut V)) ∣ 2 ^ 4 :=
    hV ▸ Subgroup.card_subgroup_dvd_card _
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  interval_cases k
  · rw [hk'] at hmod
    exact absurd hmod (by decide)
  · rw [hk', pow_one]
  · rw [hk'] at hmod
    exact absurd hmod (by decide)
  · rw [hk'] at hmod
    exact absurd hmod (by decide)
  · exfalso
    have htop : fixSub (g : MulAut V) = ⊤ := by
      rw [← Subgroup.card_eq_iff_eq_top, hk', hV]
    have hg1 : g = 1 := by
      apply Subtype.ext
      ext v
      have hv : v ∈ fixSub (g : MulAut V) := htop ▸ Subgroup.mem_top v
      exact hv
    rw [hg1, orderOf_one] at hg
    exact absurd hg (by norm_num)

theorem exists_invariant_of_card_eq_168 (hV2 : ∀ v : V, v ^ 2 = 1) (hV : Nat.card V = 2 ^ 4)
    (H : Subgroup (MulAut V)) (hH : Nat.card H = 168) :
    ∃ W : Subgroup V, W ≠ ⊥ ∧ W ≠ ⊤ ∧ ∀ h ∈ H, ∀ w ∈ W, (h : MulAut V) w ∈ W := by
  classical
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Finite (MulAut V) :=
    Finite.of_injective (fun f : MulAut V => (f : V → V)) DFunLike.coe_injective
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := H) 7 (by rw [hH]; norm_num)
  set γ : MulAut V := (g : MulAut V) with hγ
  have hγ7 : orderOf γ = 7 := by rw [hγ, Subgroup.orderOf_coe, hg]
  obtain ⟨⟨u, hu⟩, hu1, huniq⟩ :=
    (Nat.card_eq_two_iff' (1 : fixSub γ)).1 (card_fixSub_eq_two hV g hg)
  have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
  have hgu : γ u = u := hu
  have hfixγ : ∀ w : V, w ≠ 1 → γ w = w → w = u := fun w hw1 hw =>
    congrArg Subtype.val (huniq ⟨w, hw⟩ fun h => hw1 (congrArg Subtype.val h))
  by_cases hA : ∃ v : V, v ≠ 1 ∧ ∀ h ∈ H, (h : MulAut V) v = v
  ·
    obtain ⟨v, hv1, hvH⟩ := hA
    refine ⟨Subgroup.zpowers v, Subgroup.zpowers_ne_bot.2 hv1, fun htop => ?_, ?_⟩
    · have h2 : orderOf v = 2 := orderOf_eq_prime (hV2 v) hv1
      have hc := Nat.card_zpowers v
      rw [htop, Subgroup.card_top, hV, h2] at hc
      norm_num at hc
    · intro h hh w hw
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
      rw [map_zpow, hvH h hh]
      exact Subgroup.zpow_mem_zpowers v k
  push Not at hA
  have hV16 : Nat.card V = 16 := by rw [hV]; norm_num
  have huO : u ∈ orbit H u := mem_orbit_self u
  have h1O : (1 : V) ∉ orbit H u := by
    rintro ⟨h, hh⟩
    have hh' : (h : MulAut V) u = 1 := hh
    rw [EmbeddingLike.map_eq_one_iff] at hh'
    exact hu1' hh'
  have hOdvd : (orbit H u).ncard ∣ 168 := by
    rw [← index_stabilizer, ← hH]
    exact Subgroup.index_dvd_card _
  have hOmod : (orbit H u).ncard ≡ 1 [MOD 7] := by
    have hP : IsPGroup 7 (Subgroup.zpowers g) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hg, pow_one])
    have hm := hP.card_modEq_card_fixedPoints (orbit H u)
    have hfixO : Nat.card (fixedPoints (Subgroup.zpowers g) (orbit H u)) = 1 := by
      rw [Nat.card_eq_one_iff_exists]
      have hux : (⟨u, huO⟩ : orbit H u) ∈ fixedPoints (Subgroup.zpowers g) (orbit H u) := by
        intro p
        have hle : Subgroup.zpowers g ≤ stabilizer H u :=
          Subgroup.zpowers_le.2 (by rw [mem_stabilizer_iff, smul_eq_apply]; exact hgu)
        exact Subtype.ext (hle p.2)
      refine ⟨⟨⟨u, huO⟩, hux⟩, ?_⟩
      rintro ⟨⟨x, hxO⟩, hx⟩
      have hgx : γ x = x := congrArg Subtype.val (hx ⟨g, Subgroup.mem_zpowers g⟩)
      have hx1 : x ≠ 1 := fun h => h1O (h ▸ hxO)
      exact Subtype.ext (Subtype.ext (hfixγ x hx1 hgx))
    rwa [hfixO, Nat.card_coe_set_eq] at hm
  have hOlt : (orbit H u).ncard < 16 := by
    have hss : orbit H u ⊂ Set.univ := Set.ssubset_univ_iff.2 fun h => h1O (h ▸ Set.mem_univ 1)
    calc (orbit H u).ncard < (Set.univ : Set V).ncard := Set.ncard_lt_ncard hss
      _ = 16 := by rw [Set.ncard_univ, hV16]
  have hO1 : (orbit H u).ncard ≠ 1 := by
    intro h1
    obtain ⟨a, ha⟩ := Set.ncard_eq_one.1 h1
    obtain ⟨h, hh, hne⟩ := hA u hu1'
    have hmem : (⟨h, hh⟩ : H) • u ∈ orbit H u := mem_orbit u (⟨h, hh⟩ : H)
    rw [ha, Set.mem_singleton_iff, smul_eq_apply] at hmem
    have hua : u = a := by rw [← Set.mem_singleton_iff, ← ha]; exact huO
    exact hne (hmem.trans hua.symm)
  have hO8 : (orbit H u).ncard = 8 := by
    have key : ∀ n : ℕ, n < 16 → n % 7 = 1 % 7 → n ≠ 1 → n ∣ 168 → n = 8 := by decide
    exact key _ hOlt hOmod hO1 hOdvd
  set R : Set V := (orbit H u)ᶜ \ {1} with hR
  have hmemR : ∀ r, r ∈ R ↔ r ∉ orbit H u ∧ r ≠ 1 := fun r => by
    rw [hR, Set.mem_sdiff, Set.mem_compl_iff, Set.mem_singleton_iff]
  have hRcard : R.ncard = 7 := by
    have h1 : (1 : V) ∈ (orbit H u)ᶜ := h1O
    have hc := Set.ncard_add_ncard_compl (orbit H u)
    rw [hO8, hV16] at hc
    rw [hR, Set.ncard_sdiff_singleton_of_mem h1]
    omega
  have hRinv : ∀ h ∈ H, ∀ r ∈ R, (h : MulAut V) r ∈ R := by
    intro h hh r hr
    rw [hmemR] at hr ⊢
    refine ⟨fun hhr => hr.1 ?_, fun h1 => hr.2 (EmbeddingLike.map_eq_one_iff.1 h1)⟩
    obtain ⟨k, hk⟩ := hhr
    have hk' : k • u = (h : MulAut V) r := hk
    refine ⟨(⟨h, hh⟩ : H)⁻¹ * k, ?_⟩
    show ((⟨h, hh⟩ : H)⁻¹ * k) • u = r
    rw [mul_smul, hk', smul_eq_apply]
    show ((h : MulAut V)⁻¹) ((h : MulAut V) r) = r
    exact (h : MulAut V).symm_apply_apply r
  have hγR : ∀ r ∈ R, γ r ∈ R := fun r hr => hRinv γ g.2 r hr
  have hγpowR : ∀ (n : ℕ), ∀ r ∈ R, (γ ^ n) r ∈ R := by
    intro n
    induction n with
    | zero => exact fun r hr => hr
    | succ n ih =>
      intro r hr
      rw [pow_succ, MulAut.mul_apply]
      exact ih _ (hγR r hr)
  have hγfree : ∀ r ∈ R, γ r ≠ r := by
    intro r hr hγr
    rw [hmemR] at hr
    apply hr.1
    rw [hfixγ r hr.2 hγr]
    exact huO
  have hinj : ∀ r ∈ R, Function.Injective fun i : Fin 7 => (γ ^ (i : ℕ)) r := by
    have hstep : ∀ r ∈ R, ∀ d : ℕ, 0 < d → d < 7 → (γ ^ d) r ≠ r := by
      intro r hr d hd0 hd7 hdr
      have hgcd : d.gcd (orderOf γ) = 1 := by
        rw [hγ7]
        interval_cases d <;> decide
      have hmem : γ ∈ Subgroup.zpowers (γ ^ d) := mem_zpowers_pow_iff.2 hgcd
      have hle : Subgroup.zpowers (γ ^ d) ≤ stabilizer (MulAut V) r :=
        Subgroup.zpowers_le.2 (by rw [mem_stabilizer_iff, MulAut.smul_def]; exact hdr)
      have := hle hmem
      rw [mem_stabilizer_iff, MulAut.smul_def] at this
      exact hγfree r hr this
    intro r hr i j hij
    simp only at hij
    have hi7 := i.isLt
    have hj7 := j.isLt
    by_contra hne
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
    · have hs := hγpowR i r hr
      apply hstep _ hs (j - i) (by omega) (by omega)
      rw [← MulAut.mul_apply, ← pow_add, Nat.sub_add_cancel hlt.le]
      exact hij.symm
    · have hs := hγpowR j r hr
      apply hstep _ hs (i - j) (by omega) (by omega)
      rw [← MulAut.mul_apply, ← pow_add, Nat.sub_add_cancel hlt.le]
      exact hij
  have hRfin : R.Finite := R.toFinite
  have himg : ∀ r ∈ R, Finset.univ.image (fun i : Fin 7 => (γ ^ (i : ℕ)) r) = hRfin.toFinset := by
    intro r hr
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨i, -, rfl⟩ := hx
      rw [Set.Finite.mem_toFinset]
      exact hγpowR i r hr
    · rw [Finset.card_image_of_injective _ (hinj r hr), Finset.card_univ, Fintype.card_fin,
        ← Set.ncard_eq_toFinset_card R hRfin, hRcard]
  set S : V := ∏ x ∈ hRfin.toFinset, x with hS
  have hSfix : ∀ h ∈ H, (h : MulAut V) S = S := by
    intro h hh
    rw [hS, map_prod]
    have hmap : hRfin.toFinset.map (h : MulAut V).toEquiv.toEmbedding = hRfin.toFinset := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        rw [Finset.mem_map] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        rw [Set.Finite.mem_toFinset] at hy ⊢
        exact hRinv h hh y hy
      · rw [Finset.card_map]
    calc ∏ x ∈ hRfin.toFinset, (h : MulAut V) x
        = ∏ x ∈ hRfin.toFinset.map (h : MulAut V).toEquiv.toEmbedding, x := by
          rw [Finset.prod_map]; rfl
      _ = ∏ x ∈ hRfin.toFinset, x := by rw [hmap]
  have hS1 : S = 1 := by
    by_contra hS1
    obtain ⟨h, hh, hne⟩ := hA S hS1
    exact hne (hSfix h hh)
  set φ : V →* V := ∏ i : Fin 7, (γ ^ (i : ℕ)).toMonoidHom with hφdef
  have hφ : ∀ v, φ v = ∏ i : Fin 7, (γ ^ (i : ℕ)) v := fun v => by
    rw [hφdef, MonoidHom.finsetProd_apply]
    rfl
  have hφR : ∀ r ∈ R, φ r = 1 := by
    intro r hr
    rw [hφ, ← hS1, hS, ← himg r hr, Finset.prod_image fun i _ j _ hij => hinj r hr hij]
  have hφu : φ u = u := by
    rw [hφ]
    simp only [pow_apply_of_apply_eq hgu, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [show (7 : ℕ) = 2 * 3 + 1 by norm_num, pow_succ, pow_mul, hV2 u, one_pow, one_mul]
  refine ⟨Subgroup.closure R, ?_, ?_, ?_⟩
  · obtain ⟨r, hr⟩ : R.Nonempty := Set.nonempty_of_ncard_ne_zero (by rw [hRcard]; norm_num)
    intro hbot
    have hrc : r ∈ Subgroup.closure R := Subgroup.subset_closure hr
    rw [hbot, Subgroup.mem_bot] at hrc
    exact ((hmemR r).1 hr).2 hrc
  · intro htop
    have hle : Subgroup.closure R ≤ φ.ker := (Subgroup.closure_le _).2 fun r hr => hφR r hr
    have hu : u ∈ φ.ker := hle (htop ▸ Subgroup.mem_top u)
    rw [MonoidHom.mem_ker, hφu] at hu
    exact hu1' hu
  · intro h hh w hw
    induction hw using Subgroup.closure_induction with
    | mem x hx => exact Subgroup.subset_closure (hRinv h hh x hx)
    | one => rw [map_one]; exact one_mem _
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
    | inv x _ hx => rw [map_inv]; exact inv_mem hx

end CFSG.Quasithin.H13.L32NoIrrFourProof

namespace CFSG.Quasithin.H13

theorem l32NoIrrFour_holds : L32NoIrrFour := by
  intro V _ _ hV2 hV H ⟨e⟩
  exact L32NoIrrFourProof.exists_invariant_of_card_eq_168 hV2 hV H
    ((Nat.card_congr e.toEquiv).trans card_sl_three_zmod_two)

end CFSG.Quasithin.H13
