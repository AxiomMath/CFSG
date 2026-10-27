module

public import CFSG.Quasithin.Background.SmithC27AltSetup
public import CFSG.Quasithin.Background.SmithC27Perm3
public import CFSG.Quasithin.Background.SmithC27Sylow

public section

namespace CFSG.Quasithin.SmithC27

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin Equiv Equiv.Perm C124 C124.YZ
open scoped Pointwise

theorem apply_eq_of_pow_three {W : Type*} [CommGroup W] (hW : ∀ w : W, w ^ 2 = 1)
    {T : MulAut W} (hT : T ^ 3 = 1) {u : W} (h : T (T u * u⁻¹) = T u * u⁻¹) : T u = u := by
  set v := T u * u⁻¹ with hv
  have h1 : T u = v * u := by rw [hv]; group
  have h2 : T (T u) = u := by
    rw [h1, map_mul, h, h1, ← mul_assoc, ← pow_two, hW, one_mul]
  have h3 : T (T (T u)) = u := by
    have := congrArg (fun f : MulAut W => f u) hT
    simpa [pow_succ, MulAut.mul_apply] using this
  rw [h2] at h3
  exact h3

theorem coreMod_inv_eq {n : ℕ} (x : ↥(G6.coreMod n)) : x⁻¹ = x := by
  apply Subtype.ext
  apply Multiplicative.toAdd.injective
  funext i
  show -(Multiplicative.toAdd (x : G6.PermMod n) i) = Multiplicative.toAdd (x : G6.PermMod n) i
  exact ZMod.neg_eq_self_mod_two _

section K2

variable {G : Type} [Group G] [Finite G] {H R M K : Subgroup G} {n k : ℕ} [NeZero n]

namespace AltCtx

variable (C : AltCtx H R M K n k)
include C

theorem fix_of_cycle {P : Subgroup (MulAut (Wc R K))} (hPX : P ≤ starOf R K (K ⊔ R))
    {τ : MulAut (Wc R K)} (hτK : τ ∈ starOf R K K) (hτ3 : τ ^ 3 = 1)
    (hτP : ∀ p ∈ P, τ * p * τ⁻¹ ∈ P)
    (hfin : ∀ x y : ↥(G6.coreMod n),
      (∀ (p : MulAut (Wc R K)) (hp : p ∈ P), G6.coreAct n (C.ι ⟨p, hPX hp⟩) x = x) →
      x = y * G6.coreAct n (C.ι ⟨τ, star_le le_sup_left hτK⟩) y → x = 1)
    {w : Wc R K} (hw : w ∈ fixV P) : τ w = w := by
  have hW : ∀ v : Wc R K, v ^ 2 = 1 := IntMod.sq_eq_one
  have hτX : τ ∈ starOf R K (K ⊔ R) := star_le le_sup_left hτK
  have hτinv : τ⁻¹ = τ * τ := by
    have : τ ^ 3 = τ * τ * τ := by rw [pow_succ, pow_two]
    rw [this] at hτ3
    exact (eq_inv_of_mul_eq_one_left hτ3).symm
  have hτP' : ∀ p ∈ P, τ⁻¹ * p * τ ∈ P := by
    intro p hp
    have h1 := hτP _ (hτP p hp)
    have : τ * (τ * p * τ⁻¹) * τ⁻¹ = τ⁻¹ * p * τ := by
      rw [hτinv]
      have h3 : τ * τ * τ = 1 := by
        have := hτ3
        rw [pow_succ, pow_two] at this
        exact this
      calc τ * (τ * p * (τ * τ)) * (τ * τ) = τ * τ * p * (τ * τ * τ) * τ := by group
        _ = τ * τ * p * τ := by rw [h3, mul_one]
    rw [this] at h1
    exact h1
  have hfixP : ∀ v ∈ fixV P, τ v ∈ fixV P := by
    intro v hv p hp
    have h1 := hv _ (hτP' p hp)
    have : p (τ v) = τ ((τ⁻¹ * p * τ) v) := by
      simp [MulAut.mul_apply]
    rw [this, h1]
  have hcomm : ∀ v : Wc R K, τ v * v⁻¹ ∈ commV (starOf R K K) := fun v =>
    Subgroup.subset_closure ⟨τ, hτK, v, rfl⟩
  have hcommU : ∀ v ∈ commV (starOf R K K), τ v ∈ commV (starOf R K K) := fun v hv =>
    apply_mem_commV (Subgroup.le_normalizer hτK) hv
  have hstep : ∀ v ∈ fixV P, τ (τ v * v⁻¹) = τ v * v⁻¹ := by
    intro v hvP
    set u := τ v * v⁻¹ with hu
    have huP : u ∈ fixV P := (fixV P).mul_mem (hfixP v hvP) ((fixV P).inv_mem hvP)
    have huU : u ∈ commV (starOf R K K) := hcomm v
    set u' := τ u * u⁻¹ with hu'
    have hu'P : u' ∈ fixV P := (fixV P).mul_mem (hfixP u huP) ((fixV P).inv_mem huP)
    have hu'U : u' ∈ commV (starOf R K K) := hcomm u
    have hβ : C.β ⟨u', hu'U⟩ = C.β ⟨u, huU⟩ *
        G6.coreAct n (C.ι ⟨τ, hτX⟩) (C.β ⟨u, huU⟩) := by
      have e1 : (⟨u', hu'U⟩ : ↥(commV (starOf R K K))) =
          ⟨τ u, hcommU u huU⟩ * (⟨u, huU⟩ : ↥(commV (starOf R K K)))⁻¹ := Subtype.ext rfl
      rw [e1, map_mul, map_inv, coreMod_inv_eq, mul_comm]
      congr 1
      exact C.β_equiv ⟨τ, hτX⟩ ⟨u, huU⟩ (hcommU u huU)
    have hβfix : ∀ (p : MulAut (Wc R K)) (hp : p ∈ P),
        G6.coreAct n (C.ι ⟨p, hPX hp⟩) (C.β ⟨u', hu'U⟩) = C.β ⟨u', hu'U⟩ := by
      intro p hp
      have hpu : p u' ∈ commV (starOf R K K) := by rw [hu'P p hp]; exact hu'U
      have := C.β_equiv ⟨p, hPX hp⟩ ⟨u', hu'U⟩ hpu
      rw [← this]
      congr 1
      exact Subtype.ext (hu'P p hp)
    have h1 := hfin _ _ hβfix hβ
    have h2 : u' ∈ fixV (starOf R K K) := C.β_ker _ h1
    exact apply_eq_of_pow_three hW hτ3 (h2 τ hτK)
  exact apply_eq_of_pow_three hW hτ3 (hstep w hw)

end AltCtx

theorem pts012_five : (0 : Fin 5) ≠ 1 ∧ (2 : Fin 5) ≠ 0 ∧ (2 : Fin 5) ≠ 1 := by decide

theorem pts012_seven : (0 : Fin 7) ≠ 1 ∧ (2 : Fin 7) ≠ 0 ∧ (2 : Fin 7) ≠ 1 := by decide

theorem pts012 {n : ℕ} [NeZero n] (hn : n = 5 ∨ n = 7) :
    (0 : Fin n) ≠ 1 ∧ (2 : Fin n) ≠ 0 ∧ (2 : Fin n) ≠ 1 := by
  rcases hn with rfl | rfl
  · exact pts012_five
  · exact pts012_seven

namespace AltCtx

theorem kJ_le_MK (C : AltCtx H R M K n 2) : kJ (stdT2 n) ≤ C.bar (M ⊓ K) := by
  have h := C.star_alt
  rwa [alt_inf_normalizer_eq_kJ_stdT2 C.n57 (J := swapGroupOf (stdInv n 2) C.inv_sq)
    (fun g => Iff.rfl)] at h

theorem MK_cases (C : AltCtx H R M K n 2) :
    C.bar (M ⊓ K) = kJ (stdT2 n) ∨ C.bar (M ⊓ K) = quadStab n := by
  rcases kJ_stdT2_overgroups C.n57 C.kJ_le_MK C.MK_le_alt with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd h C.MK_ne_alt

theorem MK_ne_kJ (C : AltCtx H R M K n 2) :
    C.bar (M ⊓ K) ≠ kJ (stdT2 n) := by
  intro hMK
  obtain ⟨h01, h20, h21⟩ := pts012 C.n57
  set Xs := starOf R K (K ⊔ R) with hXs
  have hV4R : V4 n ≤ C.bar R := by
    refine C.le_R_of_normal ?_ ?_ (isPGroup_V4 C.n57)
    · rw [hMK]
      exact V4_le_kJ_stdT2 C.n57
    · rw [hMK]
      exact kJ_stdT2_le_normalizer_V4 C.n57
  set c : Perm (Fin n) := swap 0 2 * swap 0 1 with hc
  obtain ⟨hcfix, hc3, hcA, -⟩ := threeCycle01_facts h01 h20 h21
  obtain ⟨y, hyK, hyc⟩ := C.exists_lift hcA
  have hyX : y ∈ K ⊔ R := Subgroup.mem_sup_left hyK
  set τg : ↥Xs := starHom C.X_le_N ⟨y, hyX⟩ with hτg
  have hιτ : C.ι τg = c := hyc
  have hτK : (τg : MulAut (Wc R K)) ∈ starOf R K K :=
    (mem_autI _).2 ⟨Subgroup.inclusion C.X_le_N ⟨y, hyX⟩, hyK, rfl⟩
  have hτ3 : (τg : MulAut (Wc R K)) ^ 3 = 1 := by
    have h1 : C.ι (τg ^ 3) = 1 := by
      rw [map_pow, hιτ, ← hc3.orderOf, pow_orderOf_eq_one]
    have h2 : τg ^ 3 = 1 := C.inj (h1.trans (map_one _).symm)
    have := congrArg Subtype.val h2
    simpa using this
  set P : Subgroup (MulAut (Wc R K)) := ((V4 n).comap C.ι).map Xs.subtype with hP
  have hPX : P ≤ Xs := Subgroup.map_subtype_le _
  have hmemP : ∀ g : ↥Xs, (g : MulAut (Wc R K)) ∈ P ↔ C.ι g ∈ V4 n := by
    intro g
    constructor
    · rintro ⟨g', hg', hgg'⟩
      have : g' = g := Subtype.ext hgg'
      rw [← this]
      exact hg'
    · intro hg
      exact ⟨g, hg, rfl⟩
  have hτP : ∀ p ∈ P, (τg : MulAut (Wc R K)) * p * (τg : MulAut (Wc R K))⁻¹ ∈ P := by
    intro p hp
    have hpX := hPX hp
    have h1 := (hmemP ⟨p, hpX⟩).1 hp
    have hcN := quadStab_le_normalizer_V4 C.n57 (threeCycle012_mem_quadStab C.n57)
    have h2 := (Subgroup.mem_normalizer_iff.1 hcN (C.ι ⟨p, hpX⟩)).1 h1
    have hmem : (τg : MulAut (Wc R K)) * p * (τg : MulAut (Wc R K))⁻¹ ∈ Xs :=
      Xs.mul_mem (Xs.mul_mem τg.2 hpX) (Xs.inv_mem τg.2)
    refine (hmemP ⟨_, hmem⟩).2 ?_
    have e : (⟨_, hmem⟩ : ↥Xs) = τg * ⟨p, hpX⟩ * τg⁻¹ := Subtype.ext rfl
    rw [e, map_mul, map_mul, map_inv, hιτ]
    exact h2
  have hfin : ∀ x y' : ↥(G6.coreMod n),
      (∀ (p : MulAut (Wc R K)) (hp : p ∈ P), G6.coreAct n (C.ι ⟨p, hPX hp⟩) x = x) →
      x = y' * G6.coreAct n (C.ι ⟨τg, star_le le_sup_left hτK⟩) y' → x = 1 := by
    intro x y' hx hxy
    have hτ' : C.ι ⟨τg, star_le le_sup_left hτK⟩ = c := hιτ
    rw [hτ'] at hxy
    have hgen : ∀ σ ∈ V4 n, G6.coreAct n σ x = x := by
      intro σ hσ
      obtain ⟨g, rfl⟩ := C.surj σ
      exact hx g ((hmemP g).2 hσ)
    exact eq_one_of_coreFix_V4 C.n57 hcfix hxy
      (hgen _ (Subgroup.subset_closure (by simp)))
      (hgen _ (Subgroup.subset_closure (by simp)))
  have hcent : ∀ z ∈ omegaOneCenterOf R, y * z * y⁻¹ = z := by
    intro z hz
    have hzV : z ∈ Vc R K := C.hyp.omegaOneCenterOf_le hz
    set wz : Wc R K := IntMod.mk _ ⟨z, hzV⟩ with hwz
    have hwP : wz ∈ fixV P := by
      intro p hp
      have hpX := hPX hp
      have hpR : p ∈ starOf R K R :=
        (mem_Bmap_iff_of_injective C.inj ⟨p, hpX⟩).1 (hV4R ((hmemP ⟨p, hpX⟩).1 hp))
      obtain ⟨r, hrR, rfl⟩ := (mem_autI _).1 hpR
      apply IntMod.val_injective
      rw [convI_apply_val]
      have hzc : z ∈ centerOf R := C1GN.omegaOneCenterOf_le_centerOf R hz
      have := (Subgroup.mem_centralizer_iff.1 hzc.2 (r : G) hrR)
      show (r : G) * z * (r : G)⁻¹ = z
      rw [this, mul_inv_cancel_right]
    have h1 := C.fix_of_cycle hPX hτK hτ3 hτP hfin hwP
    have h2 := congrArg IntMod.val h1
    rw [show (τg : MulAut (Wc R K)) = convI _ (Subgroup.inclusion C.X_le_N ⟨y, hyX⟩) from rfl,
      convI_apply_val] at h2
    exact h2
  have hyM : y ∈ M := by
    have hO1R : omegaOneCenterOf R ≤ R := (C1GN.omegaOneCenterOf_le_centerOf R).trans inf_le_left
    have hne : omegaOneCenterOf R ≠ ⊥ :=
      Setup.omegaOneCenterOf_ne_bot C.hyp.isPGroup C.hyp.R_ne_bot
    have hchar := Setup.characteristic_omegaOneCenterOf R
    have hle : H ⊓ Subgroup.normalizer (omegaOneCenterOf R : Set G) ≤ cgsIn H R :=
      le_iSup_of_le _ (le_iSup_of_le hO1R (le_iSup_of_le hne (le_iSup_of_le hchar le_rfl)))
    have hyN : y ∈ Subgroup.normalizer (omegaOneCenterOf R : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro z
      constructor
      · intro hz
        rw [hcent z hz]
        exact hz
      · intro hz
        have h3 := hcent _ hz
        have h4 : y * z * y⁻¹ = z := by
          calc y * z * y⁻¹ = y⁻¹ * (y * (y * z * y⁻¹) * y⁻¹) * y := by group
            _ = y⁻¹ * (y * z * y⁻¹) * y := by rw [h3]
            _ = z := by group
        rw [← h4]
        exact hz
    exact C.hyp.hyp.cgs (hle ⟨C.hyp.K_le hyK, hyN⟩)
  have hcM : c ∈ C.bar (M ⊓ K) := by
    rw [hc, ← hyc]
    exact C.φ_mem_bar MK_le ⟨hyM, hyK⟩
  rw [hMK] at hcM
  exact threeCycle012_not_mem_kJ_stdT2 C.n57 hcM

theorem MK_eq_quadStab (C : AltCtx H R M K n 2) : C.bar (M ⊓ K) = quadStab n :=
  C.MK_cases.resolve_left C.MK_ne_kJ

theorem closure_conj_le (C : AltCtx H R M K n 2) :
    Subgroup.closure {x | ∃ y ∈ quadStab n, x = y * swap 0 1 * y⁻¹} ≤
      conjClosure (C.bar R) (C.bar (M ⊓ K)) := by
  rw [Subgroup.closure_le]
  rintro x ⟨y, hy, rfl⟩
  have h01 : swap 0 1 ∈ C.bar R := C.J_le_R C.swap_mem_std
  rw [← C.MK_eq_quadStab] at hy
  exact mem_conjClosure hy h01

theorem three_of_k2_five (C : AltCtx H R M K 5 2) (hchi : IsChiBlock2 H K)
    (htype : IsAltType K 5) : C27Three H R M K (Vc R K) := by
  have hM := C.MK_eq_quadStab
  have h8 : 2 ^ 3 ∣ Nat.card (C.bar R) :=
    two_pow_dvd_of_isSylowTwoOf C.sylow_closure C.closure_conj_le
      (eight_dvd_card_closure_conj_quadStab (Or.inl rfl))
  have hRS : IsSylowTwoOf (C.bar R) ⊤ := sylow_five_of_eight_dvd C.R_pgroup h8
  have hS : IsSylowTwoOf R (K ⊔ R) := C.sylow_iff.2 hRS
  have hB : IsBorelIn (starOf R K K) (starOf R K (M ⊓ K)) := by
    refine C.isBorelIn_of_bar le_sup_left MK_le ?_
    have hK : C.bar K = alternatingGroup (Fin 5) := C.K_map
    rw [hK, hM]
    exact isBorelIn_quadStab_five
  exact Or.inl ⟨hchi, Or.inr (Or.inl ⟨htype, hS, ⟨MulEquiv.ofBijective C.ι C.bij⟩, hB⟩)⟩

omit [Finite G] in
theorem card_quot_of_isAltType {K : Subgroup G} {m : ℕ} (h : IsAltType K m) :
    Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = Nat.card (alternatingGroup (Fin m)) := by
  obtain ⟨α, hα, hker, -⟩ := h
  exact Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective α hα)).toEquiv

theorem centralizer_z2_le_stabilizer_quad :
    Subgroup.centralizer {z2 7} ≤
      MulAction.stabilizer (Perm (Fin 7)) ((quad 7 : Finset (Fin 7)) : Set (Fin 7)) := by
  intro g hg
  have hc : g * z2 7 = z2 7 * g := Subgroup.mem_centralizer_singleton_iff.1 hg
  have hq : ∀ x : Fin 7, x ∈ quad 7 ↔ z2 7 x ≠ x := by decide
  have hcx : ∀ x, g (z2 7 x) = z2 7 (g x) := fun x => by
    have := congrArg (fun p : Perm (Fin 7) => p x) hc
    simpa using this
  rw [MulAction.mem_stabilizer_iff]
  ext y
  rw [Set.mem_smul_set_iff_inv_smul_mem, Finset.mem_coe, Finset.mem_coe, hq, hq]
  have hcy : g⁻¹ (z2 7 y) = z2 7 (g⁻¹ y) := by
    have := hcx (g⁻¹ y)
    rw [show g (g⁻¹ y) = y by simp] at this
    rw [← this, show g⁻¹ (g (z2 7 (g⁻¹ y))) = z2 7 (g⁻¹ y) by simp]
  show z2 7 (g⁻¹ y) ≠ g⁻¹ y ↔ z2 7 y ≠ y
  rw [← hcy]
  exact not_congr g⁻¹.injective.eq_iff

theorem three_of_k2_seven (hC129 : ASC129Statement G) (C : AltCtx H R M K 7 2)
    (hchi : IsChiBlock2 H K) (htype : IsAltType K 7) : C27Three H R M K (Vc R K) := by
  have hM := C.MK_eq_quadStab
  have hcard : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 2520 := by
    rw [card_quot_of_isAltType htype, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
    decide
  have hns : ¬ IsSylowTwoOf R (K ⊔ R) :=
    not_sylow_of_not_chi0 hC129 C.hyp (not_isChi0Block_of_card hcard)
  set Y := conjClosure (C.bar R) (C.bar (M ⊓ K)) with hYdef
  have hRz : C.bar R ≤ Subgroup.centralizer {z2 7} := by
    have h := C.R_le_normalizer
    rwa [normalizer_swapGroupOf] at h
  have hY1 : Y ≤ MulAction.stabilizer (Perm (Fin 7)) ((quad 7 : Finset (Fin 7)) : Set (Fin 7)) := by
    refine conjClosure_le fun h hh r hr => ?_
    have hh' : h ∈ MulAction.stabilizer (Perm (Fin 7)) ((quad 7 : Finset (Fin 7)) : Set (Fin 7)) :=
      by rw [hM] at hh; exact hh.2
    have hr' := centralizer_z2_le_stabilizer_quad (hRz hr)
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hh' hr') (Subgroup.inv_mem _ hh')
  have hY3 : ¬ 16 ∣ Nat.card Y := by
    intro h16
    have h16' : 2 ^ 4 ∣ Nat.card (C.bar R) :=
      two_pow_dvd_of_isSylowTwoOf C.sylow_closure le_rfl h16
    exact hns (C.sylow_iff.2 (sylow_seven_of_sixteen_dvd C.R_pgroup h16'))
  obtain ⟨eD⟩ := nonempty_dihedral_of_sylow hY1 C.closure_conj_le hY3 C.sylow_closure
  obtain ⟨eR⟩ := C.nonempty_equiv_bar (A := R) le_sup_right
  refine Or.inl ⟨hchi, Or.inr (Or.inr (Or.inl ⟨htype, ⟨eR.trans eD⟩,
    MulEquiv.ofBijective C.ι C.bij, part43, isPartitionOfType_part43, ?_⟩))⟩
  show C.bar (M ⊓ K) = _
  rw [hM, quadStab_seven_eq]

end AltCtx

end K2

end CFSG.Quasithin.SmithC27
