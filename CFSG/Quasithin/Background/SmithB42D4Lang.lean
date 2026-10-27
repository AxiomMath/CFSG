module

public import CFSG.RankThree.Chevalley.SteinbergCDTrialityTwelveTorus

public section

namespace CFSG.Quasithin.B42D4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.Lattice CFSG.RankThree.Chevalley

section Group

variable {G : Type*} [Group G]

@[expose] def twistProd (Φ : G →* G) (n : G) : ℕ → G
  | 0 => 1
  | j + 1 => twistProd Φ n j * Φ^[j] n

theorem twistProd_succ (Φ : G →* G) (n : G) (j : ℕ) :
    twistProd Φ n (j + 1) = twistProd Φ n j * Φ^[j] n := rfl

theorem twistProd_conj (Φ : G →* G) {n u : G} (hu : n * Φ u * n⁻¹ = u) (j : ℕ) :
    twistProd Φ n j * Φ^[j] u * (twistProd Φ n j)⁻¹ = u := by
  induction j with
  | zero => simp [twistProd]
  | succ j ih =>
    have h1 : Φ^[j] n * Φ^[j + 1] u * (Φ^[j] n)⁻¹ = Φ^[j] u := by
      rw [Function.iterate_succ_apply, ← iterate_map_inv Φ j n, ← iterate_map_mul Φ j,
        ← iterate_map_mul Φ j, hu]
    calc twistProd Φ n (j + 1) * Φ^[j + 1] u * (twistProd Φ n (j + 1))⁻¹ =
        twistProd Φ n j * (Φ^[j] n * Φ^[j + 1] u * (Φ^[j] n)⁻¹) * (twistProd Φ n j)⁻¹ := by
          rw [twistProd_succ]; group
      _ = u := by rw [h1, ih]

theorem mul_map_twistProd (Φ : G →* G) (n : G) (j : ℕ) :
    n * Φ (twistProd Φ n j) = twistProd Φ n j * Φ^[j] n := by
  induction j with
  | zero => simp [twistProd]
  | succ j ih =>
    rw [twistProd_succ, map_mul, ← mul_assoc, ih, Function.iterate_succ_apply']

end Group

section Iterate

variable {L : Type} [Field L]

theorem units_map_entrywiseHom_weylElt_one' (F : L →+* L) (i : Fin TwistTag.D4.tag.rank) :
    Units.map (entrywiseHom F) (weylElt TwistTag.D4.tag L i 1) = weylElt TwistTag.D4.tag L i 1 := by
  rw [weylElt_eq_xUnit_mul, map_mul, map_mul, units_map_entrywiseHom_xUnit,
    units_map_entrywiseHom_yUnit, inv_one, Units.val_one]
  simp only [map_one, map_neg]

theorem trialityFrob_iterate_six (F : L →+* L) (g : ModGL TwistTag.D4.tag L) :
    (trialityFrob L F)^[6] g = Units.map (entrywiseHom (F ^ 6)) g := by
  have hfun : (⇑(trialityFrob L F)) = twistHom TwistTag.D4 L F :=
    funext fun y => by rw [trialityFrob_apply, twistHom_apply]
  rw [hfun, twistHom_iterate, show (6 : ℕ) = TwistTag.D4.order * 2 from rfl, pow_mul,
    diagramMap_pow_order, one_pow, inv_one, one_mul, mul_one]

theorem trialityFrob_iterate_six_twistN (F : L →+* L) :
    (trialityFrob L F)^[6] (trialityTwistN L) = trialityTwistN L := by
  rw [trialityFrob_iterate_six, map_mul, units_map_entrywiseHom_weylElt_one',
    units_map_entrywiseHom_weylElt_one']

theorem trialityFrob_iterate_mem (F : L →+* L) {g : ModGL TwistTag.D4.tag L}
    (hg : g ∈ adjointGroup TwistTag.D4.tag L) (j : ℕ) :
    (trialityFrob L F)^[j] g ∈ adjointGroup TwistTag.D4.tag L := by
  induction j with
  | zero => exact hg
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    have h := twistHom_mem_adjointGroup TwistTag.D4 L F ih
    rwa [twistHom_apply, ← trialityFrob_apply] at h

theorem twistProd_mem (F : L →+* L) {n : ModGL TwistTag.D4.tag L}
    (hn : n ∈ adjointGroup TwistTag.D4.tag L) (j : ℕ) :
    twistProd (trialityFrob L F) n j ∈ adjointGroup TwistTag.D4.tag L := by
  induction j with
  | zero => exact one_mem _
  | succ j ih => exact mul_mem ih (trialityFrob_iterate_mem F hn j)

end Iterate

section Main


theorem exists_involution_inverting {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hpd : p ∣ (ℓ ^ f) ^ 4 - (ℓ ^ f) ^ 2 + 1) :
    ∃ y t : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      y * y = 1 ∧ y * t * y⁻¹ = t⁻¹ ∧ orderOf t = p := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  have : Fintype K := Fintype.ofFinite K
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fact p.Prime := ⟨hp⟩
  have hK3 : Nat.card K = ℓ ^ (f * 3) := by rw [hK, pow_mul]
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ (by omega) hK3
  set q := ℓ ^ f with hq
  set d := q ^ 4 - q ^ 2 + 1 with hd
  have hdZ : (d : ℤ) = (q : ℤ) ^ 4 - (q : ℤ) ^ 2 + 1 := twelve_cast q
  let L := AlgebraicClosure K
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  set F : L →+* L := iterateFrobenius L ℓ f with hFdef
  have hF : ∀ c : L, F c = c ^ q := fun c => by rw [hFdef, iterateFrobenius_def]
  obtain ⟨-, hfix, -, -, -⟩ := triality_both_field_orientations_simple_full_ambient_fixed_group ℓ f
    hℓ hf K hK L 1 (Or.inl rfl) σ.toRingHom (fun c => by rw [pow_one]; exact hσ c) F hF
  obtain ⟨S, hS, hLang⟩ :=
    (exceptional_all_characteristic_field_Lang_surjectivity ℓ L f hf).2 TwistTag.D4 1
  have hnG : trialityTwistN L ∈ adjointGroup TwistTag.D4.tag L :=
    mul_mem (weylElt_mem_adjointGroup 2 1) (weylElt_mem_adjointGroup 0 1)
  obtain ⟨g₀, hg₀⟩ := hLang ⟨trialityTwistN L, hnG⟩
  set g : ModGL TwistTag.D4.tag L := (g₀ : ModGL TwistTag.D4.tag L) with hgdef
  have hgG : g ∈ adjointGroup TwistTag.D4.tag L := g₀.2
  have hFg : trialityFrob L F g = g * trialityTwistN L := by
    have h := congrArg Subtype.val hg₀
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h
    rw [hS, zpow_one] at h
    rw [trialityFrob_apply, h, mul_inv_cancel_left]
  set T₀ := twelveTorus L q d with hT₀
  have hT₀H : T₀ ≤ torusGroup TwistTag.D4.tag L := twelveTorus_le_torusGroup q d
  have hHG := torusGroup_le_adjointGroup_triality (L := L)
  have hchar : ∀ u ∈ torusGroup TwistTag.D4.tag L,
      (trialityTwistN L * trialityFrob L F u * (trialityTwistN L)⁻¹ = u ↔ u ∈ T₀) := by
    intro u hu
    obtain ⟨c, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hu
    rw [trialityTwist_rootDiagUnit_eq_iff F hF, rootDiagUnit_mem_twelveTorus_iff, ← hdZ,
      zpow_natCast]
  have hqK : ((q : ℕ) : K) = 0 := by
    rw [hq, Nat.cast_pow, CharP.cast_eq_zero, zero_pow (by omega)]
  have hdK : (d : K) = 1 := by
    have h := congrArg (Int.cast : ℤ → K) hdZ
    push_cast at h
    rw [h, hqK]
    ring
  have : NeZero (d : K) := ⟨by rw [hdK]; exact one_ne_zero⟩
  have : NeZero d := ⟨fun h => by simp [h] at hdK⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.prim (M := L) (n := d)
  have hcardT₀ : Nat.card T₀ = d := by
    rw [hT₀, twelveTorus, Subgroup.card_map_of_injective (injective_twelveTorus_map q),
      hζ.card_rootsOfUnity]
  set C := graphFixedRootGroup TwistTag.D4 K σ.toRingHom with hC
  obtain ⟨ι, hι⟩ : ∃ ι : C →* ModGL TwistTag.D4.tag L,
      ι = (baseChangeGL (algebraMap K L)).comp C.subtype := ⟨_, rfl⟩
  have hιinj : Function.Injective ι := by
    rw [hι]
    exact (baseChangeGL_injective (τ := TwistTag.D4.tag) (algebraMap K L)).comp
      Subtype.val_injective
  have hrange : ι.range = adjointGroup TwistTag.D4.tag L ⊓
      (trialityFrob L F).eqLocus (MonoidHom.id _) := by
    rw [hι, MonoidHom.range_comp, Subgroup.range_subtype]
    refine SetLike.coe_injective ?_
    rw [← hfix]
    ext x
    simp only [pow_one, Set.mem_ofPred_eq, SetLike.mem_coe, Subgroup.mem_inf]
    rfl
  have hconjF : ∀ u : ModGL TwistTag.D4.tag L, trialityFrob L F (g * u * g⁻¹) =
      g * (trialityTwistN L * trialityFrob L F u * (trialityTwistN L)⁻¹) * g⁻¹ := fun u => by
    rw [map_mul, map_mul, map_inv, hFg]
    group
  set Tc := T₀.map (MulAut.conj g).toMonoidHom with hTc
  have hTcι : Tc ≤ ι.range := by
    rintro _ ⟨u, hu, rfl⟩
    rw [hrange]
    refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hgG (hHG (hT₀H hu))) (inv_mem hgG), ?_⟩
    change trialityFrob L F (g * u * g⁻¹) = g * u * g⁻¹
    rw [hconjF, (hchar u (hT₀H hu)).2 hu]
  set T := Tc.comap ι with hT
  have eT : T ≃* T₀ :=
    ((Subgroup.equivMapOfInjective T ι hιinj).trans
      (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hTcι))).trans
      (Subgroup.equivMapOfInjective T₀ (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).symm
  have hcardT : Nat.card T = d := by rw [Nat.card_congr eT.toEquiv, hcardT₀]
  set Φ := trialityFrob L F with hΦ
  set n := trialityTwistN L with hn
  set m := twistProd Φ n 6 with hm
  have hmfix : n * Φ m * n⁻¹ = m := by
    rw [hm, mul_map_twistProd, hn, hΦ, trialityFrob_iterate_six_twistN, mul_inv_cancel_right]
  have hmG : m ∈ adjointGroup TwistTag.D4.tag L := twistProd_mem F hnG 6
  have hy₀ : g * m * g⁻¹ ∈ ι.range := by
    rw [hrange]
    refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hgG hmG) (inv_mem hgG), ?_⟩
    change Φ (g * m * g⁻¹) = g * m * g⁻¹
    rw [hconjF, hmfix]
  obtain ⟨y, hy⟩ := hy₀
  have hF6 : ∀ c : L, (F ^ 6) c = c ^ (q ^ 6) := fun c => by
    rw [RingHom.coe_pow]
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id, hF,
      ← pow_mul]
    ring_nf
  have hminv : ∀ u ∈ T₀, m * u * m⁻¹ = u⁻¹ := by
    intro u hu
    have hfixu : n * Φ u * n⁻¹ = u := (hchar u (hT₀H hu)).2 hu
    have h1 := twistProd_conj Φ hfixu 6
    obtain ⟨b, hb, rfl⟩ := hu
    have hbd : b ^ d = 1 := (mem_rootsOfUnity d b).1 hb
    set c := twelveTuple (L := L) q b
    have hcd : c ^ d = 1 := by rw [← map_pow, hbd, map_one]
    have hΦ6 : Φ^[6] (rootDiagUnit TwistTag.D4.tag c) = (rootDiagUnit TwistTag.D4.tag c)⁻¹ := by
      rw [hΦ, trialityFrob_iterate_six, entrywise_frob_rootDiagUnit (F ^ 6) hF6]
      have e : q ^ 6 + 1 = (q ^ 2 + 1) * d := by
        have h2 : q ^ 2 ≤ q ^ 4 := Nat.pow_le_pow_right (Nat.one_le_pow _ _ hℓ.pos) (by norm_num)
        rw [hd]
        zify [h2]
        ring
      have hc6 : c ^ (q ^ 6) * c = 1 := by
        rw [← pow_succ, e, pow_mul', hcd, one_pow]
      rw [eq_inv_iff_mul_eq_one, ← rootDiagUnit_mul, hc6, rootDiagUnit_one]
    change m * Φ^[6] (rootDiagUnit TwistTag.D4.tag c) * m⁻¹ = rootDiagUnit TwistTag.D4.tag c at h1
    rw [hΦ6] at h1
    change m * rootDiagUnit TwistTag.D4.tag c * m⁻¹ = (rootDiagUnit TwistTag.D4.tag c)⁻¹
    calc m * rootDiagUnit TwistTag.D4.tag c * m⁻¹ = (m * (rootDiagUnit TwistTag.D4.tag c)⁻¹ *
          m⁻¹)⁻¹ := by group
      _ = _ := by rw [h1]
  have hyinv : ∀ t ∈ T, y * t * y⁻¹ = t⁻¹ := by
    intro t ht
    obtain ⟨u, hu, hut⟩ := ht
    apply hιinj
    rw [map_mul, map_mul, map_inv, map_inv, hy, ← hut]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * m * g⁻¹ * (g * u * g⁻¹) * (g * m * g⁻¹)⁻¹ = g * (m * u * m⁻¹) * g⁻¹ := by group
      _ = g * u⁻¹ * g⁻¹ := by rw [hminv u hu]
      _ = (g * u * g⁻¹)⁻¹ := by group
  have : Finite T := Nat.finite_of_card_ne_zero (by rw [hcardT]; exact NeZero.ne d)
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := T) p (by rw [hcardT]; exact hpd)
  have hto : orderOf (t : C) = p := by rw [Subgroup.orderOf_coe, ht]
  have hyt := hyinv t t.2
  obtain ⟨T', -, -, hcent⟩ :=
    triality_cyclotomic_twelve_torus_and_prime_centralizers hℓ hf K hK σ hσ
  obtain ⟨-, -, -, -, hodd⟩ := ((hcent p hp hp3 hpd).2.2) (t : C) hto
  have hy2 : y * y ∈ Subgroup.centralizer ({(t : C)} : Set C) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have e1 : y * y * (t : C) * (y * y)⁻¹ = (t : C) := by
      calc y * y * (t : C) * (y * y)⁻¹ = y * (y * t * y⁻¹) * y⁻¹ := by group
        _ = y * (t : C)⁻¹ * y⁻¹ := by rw [hyt]
        _ = (y * t * y⁻¹)⁻¹ := by group
        _ = t := by rw [hyt, inv_inv]
    calc y * y * (t : C) = y * y * (t : C) * (y * y)⁻¹ * (y * y) := by group
      _ = (t : C) * (y * y) := by rw [e1]
  set k := orderOf (y * y) with hk
  have hkodd : Odd k := by
    have hdvd : k ∣ Nat.card (Subgroup.centralizer ({(t : C)} : Set C)) := by
      rw [hk, ← Subgroup.orderOf_mk (y * y) hy2]
      exact orderOf_dvd_natCard _
    exact hodd.of_dvd_nat hdvd
  obtain ⟨i, hi⟩ := hkodd
  refine ⟨y ^ k, t, ?_, ?_, hto⟩
  · rw [← pow_add, ← two_mul, pow_mul, sq, hk, pow_orderOf_eq_one]
  · have hcomm : (y * y) ^ i * (t : C) = (t : C) * (y * y) ^ i :=
      Subgroup.mem_centralizer_singleton_iff.1 (pow_mem hy2 i)
    have hyk : y ^ k = (y * y) ^ i * y := by
      rw [hi, pow_succ, pow_mul, ← sq, sq]
    rw [hyk]
    calc (y * y) ^ i * y * (t : C) * ((y * y) ^ i * y)⁻¹ =
        (y * y) ^ i * (y * t * y⁻¹) * ((y * y) ^ i)⁻¹ := by group
      _ = (y * y) ^ i * (t : C)⁻¹ * ((y * y) ^ i)⁻¹ := by rw [hyt]
      _ = ((y * y) ^ i * (t : C) * ((y * y) ^ i)⁻¹)⁻¹ := by group
      _ = (t : C)⁻¹ := by rw [hcomm, mul_inv_cancel_right]

end Main

end CFSG.Quasithin.B42D4
