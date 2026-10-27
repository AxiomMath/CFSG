module

public import CFSG.RankThree.PartOne.KF.SymNormalizer
public import CFSG.RankThree.PartOne.KF.D8Normalizer
public import Mathlib.Order.CompletePartialOrder

public section

namespace CFSG.RankThree.PartOne.KFU

variable {K : Type} [Field K]

abbrev Heart (K : Type) [Field K] : Type := torusVec 5 5 K ⧸ scalarSub 5 5 K

@[expose] noncomputable def heartMk : torusVec 5 5 K →* Heart K := QuotientGroup.mk' _

theorem heartMk_surjective : Function.Surjective (heartMk (K := K)) :=
  QuotientGroup.mk_surjective

theorem map_scalarSub_symAut (σ : Equiv.Perm (Fin 5)) :
    (scalarSub 5 5 K).map (symAut 5 K σ).toMonoidHom = scalarSub 5 5 K := by
  apply le_antisymm
  · rintro _ ⟨d, hd, rfl⟩ i j
    exact hd (σ.symm i) (σ.symm j)
  · intro d hd
    refine ⟨symAct 5 K σ⁻¹ d, fun i j => hd ((σ⁻¹).symm i) ((σ⁻¹).symm j), ?_⟩
    show symAct 5 K σ (symAct 5 K σ⁻¹ d) = d
    rw [← symAct_mul, mul_inv_cancel, symAct_one]

@[expose] noncomputable def heartAct (K : Type) [Field K] :
    Equiv.Perm (Fin 5) →* MulAut (Heart K) where
  toFun σ := QuotientGroup.congr (scalarSub 5 5 K) (scalarSub 5 5 K) (symAut 5 K σ)
    (map_scalarSub_symAut σ)
  map_one' := by
    refine MulEquiv.ext fun x => ?_
    obtain ⟨d, rfl⟩ := heartMk_surjective x
    rfl
  map_mul' σ τ := by
    refine MulEquiv.ext fun x => ?_
    obtain ⟨d, rfl⟩ := heartMk_surjective x
    rfl

theorem heartAct_mk (σ : Equiv.Perm (Fin 5)) (d : torusVec 5 5 K) :
    heartAct K σ (heartMk d) = heartMk (symAct 5 K σ d) := rfl

theorem card_heart [Finite K] (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ 5) :
    Nat.card (Heart K) = 5 ^ 3 := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (scalarSub 5 5 K)
  have h2 : Nat.card (torusVec 5 5 K) = 5 ^ 4 := card_torusVec_eq (by norm_num) hζ 4
  have h3 : Nat.card (scalarSub 5 5 K) = 5 :=
    card_scalarSub Nat.prime_five (by norm_num) (dvd_refl 5) hζ
  rw [h2, h3] at h1
  exact Nat.eq_of_mul_eq_mul_right (show 0 < 5 by norm_num) (h1.symm.trans (by norm_num))

theorem mem_scalarSub_five_iff {d : torusVec 5 5 K} :
    d ∈ scalarSub 5 5 K ↔ ∀ i j, (d : Fin 5 → Kˣ) i = (d : Fin 5 → Kˣ) j := Iff.rfl

theorem heartMk_eq_one_iff {d : torusVec 5 5 K} :
    heartMk d = 1 ↔ d ∈ scalarSub 5 5 K := QuotientGroup.eq_one_iff d

theorem heartMk_eq_iff {x y : torusVec 5 5 K} :
    heartMk x = heartMk y ↔ ∀ i j, (x : Fin 5 → Kˣ) i * ((y : Fin 5 → Kˣ) i)⁻¹ =
      (x : Fin 5 → Kˣ) j * ((y : Fin 5 → Kˣ) j)⁻¹ := by
  rw [← mul_inv_eq_one, ← map_inv, ← map_mul, heartMk_eq_one_iff]
  exact Iff.rfl

theorem exists_fresh_fin_five (a b c d : Fin 5) : ∃ k : Fin 5, k ≠ a ∧ k ≠ b ∧ k ≠ c ∧ k ≠ d := by
  by_contra h
  have hsub : (Finset.univ : Finset (Fin 5)) ⊆ {a, b, c, d} := by
    intro k _
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_contra hk
    push Not at hk
    exact h ⟨k, hk.1, hk.2.1, hk.2.2.1, hk.2.2.2⟩
  have h1 := Finset.card_le_card hsub
  have h2 : ({a, b, c, d} : Finset (Fin 5)).card ≤ 4 := Finset.card_le_four
  rw [Finset.card_univ, Fintype.card_fin] at h1
  omega

theorem exists_generator_root_five (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ 5) :
    ∃ z : rootsOfUnity 5 K, IsPrimitiveRoot (z : Kˣ) 5 ∧ (z : Kˣ) ≠ 1 ∧
      (z : Kˣ) ≠ (z : Kˣ)⁻¹ ∧ ∀ v : rootsOfUnity 5 K, ∃ m : ℕ, v = z ^ m := by
  obtain ⟨ζ, hζ'⟩ := hζ
  have : NeZero 5 := ⟨by norm_num⟩
  refine ⟨⟨ζ, (mem_rootsOfUnity 5 _).mpr hζ'.pow_eq_one⟩, hζ', hζ'.ne_one (by norm_num), ?_, ?_⟩
  · intro h
    have h2 : ζ ^ 2 = 1 := by
      rw [sq]
      nth_rewrite 1 [show ζ = ζ⁻¹ from h]
      exact inv_mul_cancel ζ
    have := hζ'.dvd_of_pow_eq_one 2 h2
    omega
  · intro v
    obtain ⟨m, hm⟩ := exists_unit_pow_eq hζ' (v := (v : Kˣ)) ((mem_rootsOfUnity 5 _).mp v.2)
    exact ⟨m, Subtype.ext hm.symm⟩

theorem heartAct_injective (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ 5) :
    Function.Injective (heartAct K) := by
  obtain ⟨z, -, hz1, hz2, -⟩ := exists_generator_root_five hζ
  rw [injective_iff_map_eq_one]
  intro σ hσ
  refine Equiv.ext fun a => ?_
  rw [Equiv.Perm.coe_one, id_eq]
  by_contra hne
  obtain ⟨b, hb⟩ := exists_ne a
  have hab : a ≠ b := hb.symm
  have h1 : heartMk (symAct 5 K σ (torusEltV 5 hab z)) = heartMk (torusEltV 5 hab z) := by
    rw [← heartAct_mk, hσ]
    rfl
  obtain ⟨k, hka, hkb, hkσa, hkσb⟩ := exists_fresh_fin_five a b (σ a) (σ b)
  have hk1 : σ.symm k ≠ a := fun h => hkσa (σ.symm_apply_eq.mp h)
  have hk2 : σ.symm k ≠ b := fun h => hkσb (σ.symm_apply_eq.mp h)
  have h2 := heartMk_eq_iff.mp h1 a k
  rw [coe_symAct, coe_symAct, coe_torusEltV, torusElt_apply_other hk1 hk2,
    torusElt_apply_other hka hkb, torusElt_apply_left hab] at h2
  have hsa : σ.symm a ≠ a := fun h => hne (σ.symm_apply_eq.mp h).symm
  by_cases hsb : σ.symm a = b
  · rw [hsb, torusElt_apply_right hab] at h2
    have h3 : (z : Kˣ)⁻¹ * (z : Kˣ)⁻¹ = 1 := by rw [h2]; simp
    have h4 := mul_eq_one_iff_eq_inv.mp h3
    rw [inv_inv] at h4
    exact hz2 h4.symm
  · rw [torusElt_apply_other hsa hsb] at h2
    have h3 : (z : Kˣ)⁻¹ = 1 := by simpa using h2
    exact hz1 (inv_eq_one.mp h3)

theorem movedV_heartAct (σ : Equiv.Perm (Fin 5)) :
    movedV (heartAct K σ) = (movedSub 5 K σ).map heartMk := by
  unfold movedV movedSub
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨d, rfl⟩ := heartMk_surjective y
    exact ⟨symAct 5 K σ d * d⁻¹, ⟨d, rfl⟩, by simp only [map_mul, map_inv, heartAct_mk]⟩
  · rintro ⟨_, ⟨d, rfl⟩, rfl⟩
    exact ⟨heartMk d, by simp only [map_mul, map_inv, heartAct_mk]⟩

theorem eq_one_of_heartMk_torusEltV {a b : Fin 5} (hab : a ≠ b) (u : rootsOfUnity 5 K)
    (h : heartMk (torusEltV 5 hab u) = 1) : u = 1 := by
  obtain ⟨k, hka, hkb, -, -⟩ := exists_fresh_fin_five a b a b
  have h1 := mem_scalarSub_five_iff.mp (heartMk_eq_one_iff.mp h) a k
  rw [coe_torusEltV, torusElt_apply_left hab, torusElt_apply_other hka hkb] at h1
  exact Subtype.ext h1

theorem movedV_heartAct_swap {a b : Fin 5} (hab : a ≠ b) :
    movedV (heartAct K (Equiv.swap a b)) = (heartMk.comp (torusEltV 5 hab)).range := by
  rw [movedV_heartAct, movedSub_swap Nat.prime_five (by norm_num) hab, MonoidHom.map_range]

theorem card_movedV_heartAct_swap (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ 5) {a b : Fin 5}
    (hab : a ≠ b) : Nat.card (movedV (heartAct K (Equiv.swap a b))) = 5 := by
  obtain ⟨ζ, hζ'⟩ := hζ
  have : NeZero 5 := ⟨by norm_num⟩
  have hinj : Function.Injective
      (heartMk.comp (torusEltV 5 hab) : rootsOfUnity 5 K →* Heart K) := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact eq_one_of_heartMk_torusEltV hab u hu
  rw [movedV_heartAct_swap hab, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm]
  exact IsPrimitiveRoot.card_rootsOfUnity (IsPrimitiveRoot.coe_units_iff.mpr hζ')

theorem torusEltV_mem_movedSub_of_swap {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (σ : Equiv.Perm (Fin n)) {i j : Fin n} (hij : i ≠ j) (hσij : σ i = j) (hσji : σ j = i)
    (u : rootsOfUnity p K) : torusEltV p hij u ∈ movedSub p K σ := by
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
  have hz : ∀ (z : Kˣ), z ^ p = 1 → ∃ w : Kˣ, w ^ p = 1 ∧ w⁻¹ * w⁻¹ = z := by
    intro z hz
    refine ⟨(z ^ (k + 1))⁻¹, by rw [inv_pow, ← pow_mul, mul_comm, pow_mul, hz, one_pow, inv_one],
      ?_⟩
    rw [inv_inv, ← pow_add, show k + 1 + (k + 1) = p + 1 by omega, pow_succ, hz, one_mul]
  obtain ⟨w, hw, hww⟩ := hz (u : Kˣ) ((mem_rootsOfUnity p _).mp u.2)
  apply Subgroup.subset_closure
  refine ⟨torusEltV p hij ⟨w, (mem_rootsOfUnity p _).mpr hw⟩, ?_⟩
  apply Subtype.ext
  funext m
  rw [moved_coord σ hij]
  show torusElt i j w (σ.symm m) * (torusElt i j w m)⁻¹ = torusElt i j (u : Kˣ) m
  by_cases hmi : m = i
  · subst hmi
    have h5 : σ.symm m = j := by rw [Equiv.symm_apply_eq]; exact hσji.symm
    rw [h5, torusElt_apply_right hij, torusElt_apply_left hij, torusElt_apply_left hij, ← hww]
  · by_cases hmj : m = j
    · subst hmj
      have h5 : σ.symm m = i := by rw [Equiv.symm_apply_eq]; exact hσij.symm
      rw [h5, torusElt_apply_left hij, torusElt_apply_right hij, torusElt_apply_right hij, ← hww]
      simp
    · have h6 : σ.symm m ≠ i := fun h => hmj (by
        have := congrArg σ h
        rw [Equiv.apply_symm_apply] at this
        rw [this, hσij])
      have h7 : σ.symm m ≠ j := fun h => hmi (by
        have := congrArg σ h
        rw [Equiv.apply_symm_apply] at this
        rw [this, hσji])
      rw [torusElt_apply_other h6 h7, torusElt_apply_other hmi hmj, torusElt_apply_other hmi hmj]
      simp

theorem heartMk_not_mem_zpowers {x y : torusVec 5 5 K} {e f : Fin 5}
    (hxe : (x : Fin 5 → Kˣ) e = 1) (hxf : (x : Fin 5 → Kˣ) f = 1)
    (hy : (y : Fin 5 → Kˣ) e ≠ (y : Fin 5 → Kˣ) f) :
    heartMk y ∉ Subgroup.zpowers (heartMk x) := by
  intro hmem
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hm' : heartMk (x ^ m) = heartMk y := by rw [map_zpow]; exact hm
  have h1 := heartMk_eq_iff.mp hm' e f
  have hxm : ∀ i, (x : Fin 5 → Kˣ) i = 1 → ((x ^ m : torusVec 5 5 K) : Fin 5 → Kˣ) i = 1 := by
    intro i hi
    rw [Subgroup.coe_zpow]
    have h := map_zpow (Pi.evalMonoidHom (fun _ : Fin 5 => Kˣ) i) (x : Fin 5 → Kˣ) m
    simp only [Pi.evalMonoidHom_apply] at h
    rw [h, hi, one_zpow]
  rw [hxm e hxe, hxm f hxf, one_mul, one_mul, inv_inj] at h1
  exact hy h1

theorem card_movedV_heartAct_ne_five_of_double_swap
    (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ 5) (σ : Equiv.Perm (Fin 5)) {a b c d : Fin 5}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hcd : c ≠ d)
    (h1 : σ a = b) (h2 : σ b = a) (h3 : σ c = d) (h4 : σ d = c) :
    Nat.card (movedV (heartAct K σ)) ≠ 5 := by
  obtain ⟨z, -, hz1, hz2, -⟩ := exists_generator_root_five hζ
  have hda : d ≠ a := fun h => hbc (by
    have := congrArg σ h
    rw [h4, h1] at this
    exact this.symm)
  have hdb : d ≠ b := fun h => hac (by
    have := congrArg σ h
    rw [h4, h2] at this
    exact this.symm)
  have hx : heartMk (torusEltV 5 hab z) ∈ movedV (heartAct K σ) := by
    rw [movedV_heartAct]
    exact Subgroup.mem_map_of_mem _
      (torusEltV_mem_movedSub_of_swap Nat.prime_five (by norm_num) σ hab h1 h2 z)
  have hy : heartMk (torusEltV 5 hcd z) ∈ movedV (heartAct K σ) := by
    rw [movedV_heartAct]
    exact Subgroup.mem_map_of_mem _
      (torusEltV_mem_movedSub_of_swap Nat.prime_five (by norm_num) σ hcd h3 h4 z)
  have hx1 : heartMk (torusEltV 5 hab z) ≠ 1 := by
    intro h
    have h5 := mem_scalarSub_five_iff.mp (heartMk_eq_one_iff.mp h) a c
    rw [coe_torusEltV, torusElt_apply_left hab, torusElt_apply_other hac.symm hbc.symm] at h5
    exact hz1 h5
  have hy' : heartMk (torusEltV 5 hcd z) ∉ Subgroup.zpowers (heartMk (torusEltV 5 hab z)) := by
    refine heartMk_not_mem_zpowers (e := c) (f := d) ?_ ?_ ?_
    · rw [coe_torusEltV, torusElt_apply_other hac.symm hbc.symm]
    · rw [coe_torusEltV, torusElt_apply_other hda hdb]
    · rw [coe_torusEltV, torusElt_apply_left hcd, torusElt_apply_right hcd]
      exact hz2
  exact card_ne_prime_of_two_independent Nat.prime_five _ hx hy hx1 hy'

theorem exists_orbit_four_of_pow_five (π : Equiv.Perm (Fin 5)) (hπ : π ≠ 1) (hπ5 : π ^ 5 = 1) :
    ∃ a, π a ≠ a ∧ π (π a) ≠ a ∧ π (π (π a)) ≠ a := by
  have hfix : ∀ x, π (π (π (π (π x)))) = x := by
    intro x
    have h := congrArg (fun τ : Equiv.Perm (Fin 5) => τ x) hπ5
    simp only [pow_succ, pow_zero, one_mul, Equiv.Perm.mul_apply, Equiv.Perm.coe_one,
      id_eq] at h
    exact h
  obtain ⟨a, ha⟩ : ∃ a, π a ≠ a := by
    by_contra h
    push Not at h
    exact hπ (Equiv.ext h)
  have key : π (π a) ≠ a := by
    intro h2
    have h := hfix a
    simp only [h2] at h
    exact ha h
  refine ⟨a, ha, key, fun h3 => key ?_⟩
  have h := hfix a
  simp only [h3] at h
  exact h

theorem card_movedV_heartAct_ne_five_of_pow_five
    (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ 5) (π : Equiv.Perm (Fin 5)) (hπ : π ≠ 1)
    (hπ5 : π ^ 5 = 1) : Nat.card (movedV (heartAct K π)) ≠ 5 := by
  obtain ⟨z, -, hz1, hz2, -⟩ := exists_generator_root_five hζ
  obtain ⟨a, h1, h2, h3⟩ := exists_orbit_four_of_pow_five π hπ hπ5
  obtain ⟨b, hb⟩ : ∃ b, π a = b := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, π b = c := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e, π c = e := ⟨_, rfl⟩
  rw [hb] at h1 h2 h3
  rw [hc] at h2 h3
  rw [he] at h3
  have hab : a ≠ b := h1.symm
  have hbc : b ≠ c := fun h => h1 (π.injective ((hc.trans h.symm).trans hb.symm))
  have hac : a ≠ c := h2.symm
  have hae : a ≠ e := h3.symm
  have hbe : b ≠ e := fun h => h2 (π.injective ((he.trans h.symm).trans hb.symm))
  have hce : c ≠ e := fun h => hbc (π.injective ((he.trans h.symm).trans hc.symm)).symm
  obtain ⟨f, hfa, hfb, hfc, hfe⟩ := exists_fresh_fin_five a b c e
  have hs1 : π.symm a ≠ a := fun h => hab ((π.symm_apply_eq.mp h).trans hb)
  have hs2 : π.symm a ≠ b := fun h => hac ((π.symm_apply_eq.mp h).trans hc)
  have hse : π.symm e = c := by rw [← he]; simp
  have hsf1 : π.symm f ≠ a := fun h => hfb ((π.symm_apply_eq.mp h).trans hb)
  have hsf2 : π.symm f ≠ b := fun h => hfc ((π.symm_apply_eq.mp h).trans hc)
  have hsf3 : π.symm f ≠ c := fun h => hfe ((π.symm_apply_eq.mp h).trans he)
  have hx : symAct 5 K π (torusEltV 5 hab z) * (torusEltV 5 hab z)⁻¹ ∈ movedSub 5 K π :=
    Subgroup.subset_closure ⟨_, rfl⟩
  have hy : symAct 5 K π (torusEltV 5 hbc z) * (torusEltV 5 hbc z)⁻¹ ∈ movedSub 5 K π :=
    Subgroup.subset_closure ⟨_, rfl⟩
  have hxa := moved_coord π hab z a
  have hxe := moved_coord π hab z e
  have hxf := moved_coord π hab z f
  have hye := moved_coord π hbc z e
  have hyf := moved_coord π hbc z f
  rw [torusElt_apply_other hs1 hs2, torusElt_apply_left hab] at hxa
  rw [hse, torusElt_apply_other hac.symm hbc.symm, torusElt_apply_other hae.symm hbe.symm] at hxe
  rw [torusElt_apply_other hsf1 hsf2, torusElt_apply_other hfa hfb] at hxf
  rw [hse, torusElt_apply_right hbc, torusElt_apply_other hbe.symm hce.symm] at hye
  rw [torusElt_apply_other hsf2 hsf3, torusElt_apply_other hfb hfc] at hyf
  have hmx : heartMk (symAct 5 K π (torusEltV 5 hab z) * (torusEltV 5 hab z)⁻¹) ∈
      movedV (heartAct K π) := by
    rw [movedV_heartAct]
    exact Subgroup.mem_map_of_mem _ hx
  have hmy : heartMk (symAct 5 K π (torusEltV 5 hbc z) * (torusEltV 5 hbc z)⁻¹) ∈
      movedV (heartAct K π) := by
    rw [movedV_heartAct]
    exact Subgroup.mem_map_of_mem _ hy
  have hx1 : heartMk (symAct 5 K π (torusEltV 5 hab z) * (torusEltV 5 hab z)⁻¹) ≠ 1 := by
    intro h
    have h5 := mem_scalarSub_five_iff.mp (heartMk_eq_one_iff.mp h) a e
    rw [hxa, hxe] at h5
    have h6 : (z : Kˣ)⁻¹ = 1 := by simpa using h5
    exact hz1 (inv_eq_one.mp h6)
  have hy' : heartMk (symAct 5 K π (torusEltV 5 hbc z) * (torusEltV 5 hbc z)⁻¹) ∉
      Subgroup.zpowers
        (heartMk (symAct 5 K π (torusEltV 5 hab z) * (torusEltV 5 hab z)⁻¹)) := by
    refine heartMk_not_mem_zpowers (e := e) (f := f) ?_ ?_ ?_
    · rw [hxe]; simp
    · rw [hxf]; simp
    · rw [hye, hyf]
      intro h
      apply hz1
      simpa using h
  exact card_ne_prime_of_two_independent Nat.prime_five _ hmx hmy hx1 hy'

theorem heart_irreducible [Finite K] (B : Subgroup (Heart K))
    (hB : ∀ σ : Equiv.Perm (Fin 5), ∀ x ∈ B, heartAct K σ x ∈ B) : B = ⊥ ∨ B = ⊤ := by
  have hB' : ∀ σ : Equiv.Perm (Fin 5), ∀ d ∈ B.comap heartMk,
      symAct 5 K σ d ∈ B.comap heartMk := by
    intro σ d hd
    have h := hB σ (heartMk d) hd
    rwa [heartAct_mk] at h
  rcases le_scalarSub_or_eq_top Nat.prime_five (B.comap heartMk) hB' with h | h
  · left
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨d, rfl⟩ := heartMk_surjective x
    have hd : d ∈ B.comap heartMk := hx
    rw [Subgroup.mem_bot]
    exact heartMk_eq_one_iff.mpr (h hd)
  · right
    rw [eq_top_iff]
    intro x _
    obtain ⟨d, rfl⟩ := heartMk_surjective x
    have hd : d ∈ B.comap heartMk := by rw [h]; trivial
    exact hd

theorem coe_pow_apply_torusVec (x : torusVec 5 5 K) (n : ℕ) (i : Fin 5) :
    ((x ^ n : torusVec 5 5 K) : Fin 5 → Kˣ) i = ((x : Fin 5 → Kˣ) i) ^ n := by
  rw [Subgroup.coe_pow, Pi.pow_apply]

theorem eq_of_mul_self_eq_of_pow_five {u v : Kˣ} (hu : u ^ 5 = 1) (hv : v ^ 5 = 1)
    (h : u * u = v * v) : u = v := by
  have h6 : ∀ w : Kˣ, w ^ 5 = 1 → w = (w * w) ^ 3 := fun w hw => by
    calc w = w ^ 5 * w := by rw [hw, one_mul]
      _ = (w * w) ^ 3 := by rw [← sq, ← pow_mul, ← pow_succ]
  calc u = (u * u) ^ 3 := h6 u hu
    _ = (v * v) ^ 3 := by rw [h]
    _ = v := (h6 v hv).symm

theorem exists_eq_heartMk_of_swap_inv {i j : Fin 5} (hij : i ≠ j) (y : Heart K)
    (hy : heartAct K (Equiv.swap i j) y = y⁻¹) :
    ∃ u : rootsOfUnity 5 K, y = heartMk (torusEltV 5 hij u) := by
  obtain ⟨d, rfl⟩ := heartMk_surjective y
  rw [heartAct_mk, ← map_inv, heartMk_eq_iff] at hy
  obtain ⟨k₀, hk0i, hk0j, -, -⟩ := exists_fresh_fin_five i j i j
  have hd5 : ∀ k, d.1 k ^ 5 = 1 := d.2.1
  have hy' : ∀ k l, d.1 (Equiv.swap i j k) * d.1 k = d.1 (Equiv.swap i j l) * d.1 l := by
    intro k l
    have h := hy k l
    rw [coe_symAct, coe_symAct, Equiv.symm_swap] at h
    simpa using h
  have hother : ∀ k, k ≠ i → k ≠ j → d.1 k = d.1 k₀ := by
    intro k hki hkj
    have h := hy' k k₀
    rw [Equiv.swap_apply_of_ne_of_ne hki hkj, Equiv.swap_apply_of_ne_of_ne hk0i hk0j] at h
    exact eq_of_mul_self_eq_of_pow_five (hd5 k) (hd5 k₀) h
  have hij' : d.1 j * d.1 i = d.1 k₀ * d.1 k₀ := by
    have h := hy' i k₀
    rwa [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hk0i hk0j] at h
  obtain ⟨u0, hu0⟩ : ∃ u0 : Kˣ, u0 = d.1 i * (d.1 k₀)⁻¹ := ⟨_, rfl⟩
  have hu5 : u0 ^ 5 = 1 := by
    rw [hu0, mul_pow, inv_pow, hd5 i, hd5 k₀]
    simp
  refine ⟨⟨u0, (mem_rootsOfUnity 5 _).mpr hu5⟩, ?_⟩
  have hall : ∀ k, d.1 k * (torusElt i j u0 k)⁻¹ = d.1 k₀ := by
    intro k
    by_cases hki : k = i
    · rw [hki, torusElt_apply_left hij, hu0, mul_inv, inv_inv, mul_inv_cancel_left]
    · by_cases hkj : k = j
      · rw [hkj, torusElt_apply_right hij, inv_inv, hu0]
        calc d.1 j * (d.1 i * (d.1 k₀)⁻¹) = (d.1 j * d.1 i) * (d.1 k₀)⁻¹ := (mul_assoc _ _ _).symm
          _ = (d.1 k₀ * d.1 k₀) * (d.1 k₀)⁻¹ := by rw [hij']
          _ = d.1 k₀ := mul_inv_cancel_right _ _
      · rw [torusElt_apply_other hki hkj, inv_one, mul_one]
        exact hother k hki hkj
  rw [heartMk_eq_iff]
  intro k l
  rw [coe_torusEltV]
  exact (hall k).trans (hall l).symm

theorem exists_pow_of_commutes_heart (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ 5)
    (φ' : MulAut (Heart K))
    (hcomm : ∀ σ : Equiv.Perm (Fin 5), φ' * heartAct K σ = heartAct K σ * φ') :
    ∃ e : ℕ, ∀ x : Heart K, φ' x = x ^ e := by
  obtain ⟨z, -, -, -, hzgen⟩ := exists_generator_root_five hζ
  have hij : (0 : Fin 5) ≠ 1 := by decide
  have h3 : heartAct K (Equiv.swap 0 1) (heartMk (torusEltV 5 hij z)) =
      (heartMk (torusEltV 5 hij z))⁻¹ := by
    rw [heartAct_mk, symAct_swap_torusEltV, map_inv]
  have h2 : heartAct K (Equiv.swap 0 1) (φ' (heartMk (torusEltV 5 hij z))) =
      (φ' (heartMk (torusEltV 5 hij z)))⁻¹ := by
    have h := congrArg (fun m : MulAut (Heart K) => m (heartMk (torusEltV 5 hij z)))
      (hcomm (Equiv.swap 0 1))
    simp only [MulAut.mul_apply] at h
    rw [h3, map_inv] at h
    exact h.symm
  obtain ⟨u, hu⟩ := exists_eq_heartMk_of_swap_inv hij _ h2
  obtain ⟨e, he⟩ := hzgen u
  have hφx₀ : φ' (heartMk (torusEltV 5 hij z)) = (heartMk (torusEltV 5 hij z)) ^ e := by
    rw [hu, he, map_pow, map_pow]
  have hpair : ∀ (k l : Fin 5) (hkl : k ≠ l) (v : rootsOfUnity 5 K),
      φ' (heartMk (torusEltV 5 hkl v)) = (heartMk (torusEltV 5 hkl v)) ^ e := by
    intro k l hkl v
    obtain ⟨τ, rfl, rfl⟩ := exists_perm_pair hij hkl
    obtain ⟨m, hm⟩ := hzgen v
    have hτ : heartMk (torusEltV 5 hkl z) = heartAct K τ (heartMk (torusEltV 5 hij z)) := by
      rw [heartAct_mk, symAct_torusEltV]
    have hc : φ' (heartAct K τ (heartMk (torusEltV 5 hij z))) =
        heartAct K τ (φ' (heartMk (torusEltV 5 hij z))) := by
      have h := congrArg (fun m : MulAut (Heart K) => m (heartMk (torusEltV 5 hij z))) (hcomm τ)
      simpa only [MulAut.mul_apply] using h
    have hg : φ' (heartMk (torusEltV 5 hkl z)) = (heartMk (torusEltV 5 hkl z)) ^ e := by
      rw [hτ, hc, hφx₀, map_pow]
    rw [hm, map_pow, map_pow, map_pow, hg, ← pow_mul, ← pow_mul, mul_comm]
  refine ⟨e, fun x => ?_⟩
  obtain ⟨d, rfl⟩ := heartMk_surjective x
  have hd : d ∈ torusSpan 5 5 K := by rw [torusSpan_eq_top]; trivial
  unfold torusSpan at hd
  induction hd using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨i, j, hij, u, rfl⟩ := hy
    exact hpair i j hij u
  | one => simp
  | mul y w _ _ hy hw =>
    rw [map_mul, map_mul, hy, hw]
    exact (mul_pow (heartMk y) (heartMk w) e).symm
  | inv y _ hy => rw [map_inv, map_inv, hy, inv_pow]

theorem iter_pow_apply_heart (π : Equiv.Perm (Fin 5)) (e : ℕ) (φ φ' : MulAut (Heart K))
    (hφ : φ = heartAct K π * φ') (hφ' : ∀ x, φ' x = x ^ e) (k : ℕ) (x : Heart K) :
    (φ ^ k) x = (heartAct K (π ^ k) x) ^ (e ^ k) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', MulAut.mul_apply, ih, hφ, MulAut.mul_apply, hφ', map_pow, map_pow,
      ← MulAut.mul_apply, ← map_mul, ← pow_mul, ← pow_succ', ← pow_succ]

theorem exists_heartAct_of_normalizes (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ 5)
    (hinner : ∀ α : Equiv.Perm (Fin 5) →* Equiv.Perm (Fin 5), Function.Injective α →
      (∀ a b : Fin 5, a ≠ b → ∃ c d : Fin 5, c ≠ d ∧ α (Equiv.swap a b) = Equiv.swap c d) →
      ∃ π : Equiv.Perm (Fin 5), ∀ σ, α σ = π * σ * π⁻¹)
    (φ : MulAut (Heart K)) (hφ : φ ^ 5 = 1)
    (hnorm : ∀ σ : Equiv.Perm (Fin 5), ∃ τ : Equiv.Perm (Fin 5),
      φ * heartAct K σ * φ⁻¹ = heartAct K τ) :
    ∃ π : Equiv.Perm (Fin 5), π ^ 5 = 1 ∧ φ = heartAct K π := by
  classical
  have hinj := heartAct_injective (K := K) hζ
  choose α hα using hnorm
  let αh : Equiv.Perm (Fin 5) →* Equiv.Perm (Fin 5) :=
    { toFun := α
      map_one' := hinj (by rw [← hα 1, map_one, mul_one, mul_inv_cancel])
      map_mul' := fun σ τ => hinj (by
        rw [map_mul (heartAct K) (α σ) (α τ), ← hα σ, ← hα τ, ← hα (σ * τ), map_mul]
        group) }
  have hαinj : Function.Injective αh := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    apply hinj
    have h1 := hα σ
    have h2 : α σ = 1 := hσ
    rw [h2, map_one] at h1
    rw [map_one]
    calc heartAct K σ = φ⁻¹ * (φ * heartAct K σ * φ⁻¹) * φ := by group
      _ = 1 := by rw [h1]; group
  have hαtrans : ∀ a b : Fin 5, a ≠ b → ∃ c d : Fin 5, c ≠ d ∧
      α (Equiv.swap a b) = Equiv.swap c d := by
    intro a b hab
    have hsw1 : Equiv.swap a b * Equiv.swap a b = 1 := Equiv.swap_mul_self a b
    have hτ1 : α (Equiv.swap a b) * α (Equiv.swap a b) = 1 := by
      have : αh (Equiv.swap a b * Equiv.swap a b) = 1 := by rw [hsw1, map_one]
      rw [map_mul] at this
      exact this
    have hτne : α (Equiv.swap a b) ≠ 1 := by
      intro h
      have : αh (Equiv.swap a b) = αh 1 := by rw [map_one]; exact h
      have := hαinj this
      have h2 := congrArg (fun τ : Equiv.Perm (Fin 5) => τ a) this
      simp [Equiv.swap_apply_left] at h2
      exact hab h2.symm
    have hcardτ : Nat.card (movedV (heartAct K (α (Equiv.swap a b)))) = 5 := by
      rw [← hα (Equiv.swap a b), movedV_conj, Subgroup.card_map_of_injective φ.injective]
      exact card_movedV_heartAct_swap hζ hab
    rcases involution_cases _ hτ1 hτne with ⟨c, d, hcd, h⟩ | ⟨a', b', c', d', hab', hac', hada,
        hbc', hbd', hcd', h1, h2, h3, h4⟩
    · exact ⟨c, d, hcd, h⟩
    · exact absurd hcardτ (card_movedV_heartAct_ne_five_of_double_swap hζ _ hab' hac' hbc' hcd'
        h1 h2 h3 h4)
  obtain ⟨π, hπ⟩ := hinner αh hαinj hαtrans
  set φ' : MulAut (Heart K) := (heartAct K π)⁻¹ * φ with hφ'def
  have hφdef : φ = heartAct K π * φ' := by rw [hφ'def, mul_inv_cancel_left]
  have hcomm : ∀ σ, φ' * heartAct K σ = heartAct K σ * φ' := by
    intro σ
    have h1 := hα σ
    have h2 : α σ = π * σ * π⁻¹ := hπ σ
    rw [h2, map_mul, map_mul, map_inv] at h1
    calc (heartAct K π)⁻¹ * φ * heartAct K σ
        = (heartAct K π)⁻¹ * (φ * heartAct K σ * φ⁻¹) * φ := by group
      _ = (heartAct K π)⁻¹ * (heartAct K π * heartAct K σ * (heartAct K π)⁻¹) * φ := by rw [h1]
      _ = heartAct K σ * ((heartAct K π)⁻¹ * φ) := by group
  obtain ⟨e, he⟩ := exists_pow_of_commutes_heart hζ φ' hcomm
  have hiter := iter_pow_apply_heart π e φ φ' hφdef he
  obtain ⟨z, hzprim, hz1, -, -⟩ := exists_generator_root_five hζ
  have hπp : π ^ 5 = 1 := by
    have hρ : ∀ x : Heart K, (heartAct K (π ^ 5) x) ^ (e ^ 5) = x := fun x => by
      have h := hiter 5 x
      rw [hφ, MulAut.one_apply] at h
      exact h.symm
    have key : ∀ i j : Fin 5, i ≠ j → (π ^ 5) i = i ∨ (π ^ 5) j = i := by
      intro i j hij
      by_contra hcon
      push Not at hcon
      obtain ⟨k, hk1, hk2, hk3, hk4⟩ := exists_fresh_fin_five i j ((π ^ 5) i) ((π ^ 5) j)
      have h1 := hρ (heartMk (torusEltV 5 hij z))
      rw [heartAct_mk, symAct_torusEltV, ← map_pow] at h1
      have h2 := heartMk_eq_iff.mp h1 i k
      rw [coe_pow_apply_torusVec, coe_pow_apply_torusVec, coe_torusEltV, coe_torusEltV,
        torusElt_apply_other hcon.1.symm hcon.2.symm, torusElt_apply_left hij,
        torusElt_apply_other hk3 hk4, torusElt_apply_other hk1 hk2] at h2
      have h3 : (z : Kˣ)⁻¹ = 1 := by simpa using h2
      exact hz1 (inv_eq_one.mp h3)
    by_contra hne
    obtain ⟨i, hi⟩ : ∃ i, (π ^ 5) i ≠ i := by
      by_contra h
      push Not at h
      exact hne (Equiv.ext h)
    obtain ⟨j₁, hj₁, -, -, -⟩ := exists_fresh_fin_five i i i i
    obtain ⟨j₂, hj₂, hj₂₁, -, -⟩ := exists_fresh_fin_five i j₁ i j₁
    have e1 := (key i j₁ hj₁.symm).resolve_left hi
    have e2 := (key i j₂ hj₂.symm).resolve_left hi
    exact hj₂₁ ((π ^ 5).injective (e2.trans e1.symm))
  have hdp : ∀ x : Heart K, x ^ 5 = 1 := by
    intro x
    obtain ⟨d, rfl⟩ := heartMk_surjective x
    have h : d ^ 5 = 1 := Subtype.ext (funext fun i => d.2.1 i)
    rw [← map_pow, h, map_one]
  have hep : ∀ x : Heart K, x ^ (e ^ 5) = x := fun x => by
    have h := hiter 5 x
    simp only [hφ, MulAut.one_apply, hπp, map_one] at h
    exact h.symm
  have hij₀ : (0 : Fin 5) ≠ 1 := by decide
  obtain ⟨k₀, hk01, hk02, -, -⟩ := exists_fresh_fin_five 0 1 0 1
  have h1 : heartMk ((torusEltV 5 hij₀ z) ^ (e ^ 5)) = heartMk (torusEltV 5 hij₀ z) := by
    rw [map_pow]
    exact hep _
  have h2 := heartMk_eq_iff.mp h1 0 k₀
  rw [coe_pow_apply_torusVec, coe_pow_apply_torusVec, coe_torusEltV, torusElt_apply_left hij₀,
    torusElt_apply_other hk01 hk02] at h2
  have h2' : (z : Kˣ) ^ (e ^ 5) = z := by
    have h3 : (z : Kˣ) ^ (e ^ 5) * (z : Kˣ)⁻¹ = 1 := by rw [h2]; simp
    exact mul_inv_eq_one.mp h3
  have hpos : 1 ≤ e ^ 5 := by
    by_contra h
    have h0 : e ^ 5 = 0 := by omega
    rw [h0, pow_zero] at h2'
    exact hz1 h2'.symm
  have hdvd : 5 ∣ e ^ 5 - 1 := by
    rw [← hzprim.pow_eq_one_iff_dvd]
    have h3 : (z : Kˣ) ^ (e ^ 5 - 1) * z = 1 * z := by
      rw [← pow_succ, Nat.sub_add_cancel hpos, h2', one_mul]
    exact mul_right_cancel h3
  have hmod : 1 ≡ e ^ 5 [MOD 5] := (Nat.modEq_iff_dvd' hpos).mpr hdvd
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hz1' : ((e : ℕ) : ZMod 5) = 1 := by
    have h4 : ((1 : ℕ) : ZMod 5) = ((e ^ 5 : ℕ) : ZMod 5) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
    rw [Nat.cast_pow, ZMod.pow_card, Nat.cast_one] at h4
    exact h4.symm
  have hmod1 : e ≡ 1 [MOD 5] := (ZMod.natCast_eq_natCast_iff _ _ _).mp (by rw [hz1', Nat.cast_one])
  have hemod : e % 5 = 1 := by
    have h5 : e % 5 = 1 % 5 := hmod1
    omega
  have hφ'1 : φ' = 1 := MulEquiv.ext fun x => by
    rw [he, pow_eq_pow_mod e (hdp x), hemod, pow_one]
    rfl
  refine ⟨π, hπp, ?_⟩
  rw [hφdef, hφ'1, mul_one]

end CFSG.RankThree.PartOne.KFU
