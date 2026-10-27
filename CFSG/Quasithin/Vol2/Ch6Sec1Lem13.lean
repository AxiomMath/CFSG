module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem10

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative

section Field

variable {F : Type} [Field F] [Finite F]

theorem card_fixed_le_fix_mul_self (g : (Fin 2 → F) ≃+ (Fin 2 → F)) (σ : F ≃+* F)
    (hσ : ∀ (a : F) (v : Fin 2 → F), g (a • v) = σ a • g v) :
    Nat.card {v : Fin 2 → F // g v = v} ≤
      Nat.card {c : F // σ c = c} * Nat.card {c : F // σ c = c} := by
  classical
  have : Nonempty {c : F // σ c = c} := ⟨⟨0, map_zero σ⟩⟩
  have h1 : 1 ≤ Nat.card {c : F // σ c = c} := Nat.one_le_iff_ne_zero.mpr Finite.card_pos.ne'
  by_cases hind : ∃ x y : Fin 2 → F, g x = x ∧ g y = y ∧ det2 x y ≠ 0
  · obtain ⟨x, y, hx, hy, hxy⟩ := hind
    have hgv : ∀ a b : F, g (a • x + b • y) = σ a • x + σ b • y := by
      intro a b
      rw [map_add, hσ, hσ, hx, hy]
    have hd : ∀ a' b' : F, a' • x + b' • y = 0 → a' = 0 ∧ b' = 0 := by
      intro a' b' h0
      have e0 := congrFun h0 0
      have e1 := congrFun h0 1
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e0 e1
      have hdet : det2 x y ≠ 0 := hxy
      simp only [det2] at hdet
      constructor
      · have : a' * (x 0 * y 1 - x 1 * y 0) = 0 := by linear_combination y 1 * e0 - y 0 * e1
        exact (mul_eq_zero.mp this).resolve_right hdet
      · have : b' * (x 0 * y 1 - x 1 * y 0) = 0 := by linear_combination x 0 * e1 - x 1 * e0
        exact (mul_eq_zero.mp this).resolve_right hdet
    have hfix : ∀ v : {v : Fin 2 → F // g v = v},
        σ ((v.1 0 * y 1 - v.1 1 * y 0) / det2 x y) = (v.1 0 * y 1 - v.1 1 * y 0) / det2 x y ∧
        σ ((x 0 * v.1 1 - x 1 * v.1 0) / det2 x y) = (x 0 * v.1 1 - x 1 * v.1 0) / det2 x y := by
      intro v
      have h1 := v.2
      rw [eq_add_of_det2_ne_zero hxy v.1, hgv] at h1
      set a := (v.1 0 * y 1 - v.1 1 * y 0) / det2 x y
      set b := (x 0 * v.1 1 - x 1 * v.1 0) / det2 x y
      have := hd (σ a - a) (σ b - b) (by
        rw [sub_smul, sub_smul]
        have e := h1
        rw [← sub_eq_zero] at e
        rw [← e]
        abel)
      exact ⟨sub_eq_zero.mp this.1, sub_eq_zero.mp this.2⟩
    rw [← Nat.card_prod]
    refine Nat.card_le_card_of_injective (fun v => (⟨_, (hfix v).1⟩, ⟨_, (hfix v).2⟩)) ?_
    intro v w hvw
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at hvw
    apply Subtype.ext
    rw [eq_add_of_det2_ne_zero hxy v.1, eq_add_of_det2_ne_zero hxy w.1, hvw.1, hvw.2]
  · push Not at hind
    by_cases h0 : ∃ w : Fin 2 → F, w ≠ 0 ∧ g w = w
    · obtain ⟨w, hw0, hw⟩ := h0
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hw0
      simp only [Pi.zero_apply] at hi
      have hc : ∀ v : {v : Fin 2 → F // g v = v}, v.1 = (v.1 i / w i) • w := by
        intro v
        obtain ⟨c, hc⟩ := exists_eq_smul_of_det2_eq_zero hw0 (hind w v.1 hw v.2)
        rw [hc]
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [mul_div_assoc, div_self hi, mul_one]
      have hcf : ∀ v : {v : Fin 2 → F // g v = v}, σ (v.1 i / w i) = v.1 i / w i := by
        intro v
        have h1 := v.2
        rw [hc v, hσ, hw] at h1
        have := congrFun h1 i
        simp only [Pi.smul_apply, smul_eq_mul] at this
        exact mul_right_cancel₀ hi this
      refine le_trans (Nat.card_le_card_of_injective (fun v => (⟨_, hcf v⟩ :
        {c : F // σ c = c})) ?_) (Nat.le_mul_of_pos_left _ h1)
      intro v v' hvv'
      apply Subtype.ext
      rw [hc v, hc v']
      exact congrArg (· • w) (congrArg Subtype.val hvv')
    · push Not at h0
      have hsub : Subsingleton {v : Fin 2 → F // g v = v} :=
        ⟨fun a b => Subtype.ext (by
          have ha : a.1 = 0 := by by_contra hne; exact h0 a.1 hne a.2
          have hb : b.1 = 0 := by by_contra hne; exact h0 b.1 hne b.2
          rw [ha, hb])⟩
      exact (Finite.card_le_one_iff_subsingleton.mpr hsub).trans (Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero (by omega) (by omega)))

theorem mul_self_eq_one_of_card (σ : F ≃+* F) {θ : F} (hθ : σ θ ≠ θ)
    (hcard : Nat.card {c : F // σ c = c} * Nat.card {c : F // σ c = c} = Nat.card F) :
    σ * σ = 1 := by
  classical
  let φ : {c : F // σ c = c} × {c : F // σ c = c} → F := fun p => p.1.1 + p.2.1 * θ
  have hinj : Function.Injective φ := by
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ hab
    simp only [φ] at hab
    have hbb : b = b' := by
      by_contra hne
      apply hθ
      have hθe : θ = (a' - a) / (b - b') := by
        have : b - b' ≠ 0 := sub_ne_zero.mpr hne
        field_simp
        linear_combination hab
      rw [hθe, map_div₀, map_sub, map_sub, ha, ha', hb, hb']
    have haa : a = a' := by rw [hbb] at hab; exact add_right_cancel hab
    subst hbb haa
    rfl
  have hbij : Function.Bijective φ :=
    hinj.bijective_of_nat_card_le (by rw [Nat.card_prod, hcard])
  obtain ⟨⟨⟨r, hr⟩, ⟨p, hp⟩⟩, hrp⟩ := hbij.2 (θ * θ)
  simp only [φ] at hrp
  have h1 : σ θ * σ θ = r + p * σ θ := by
    have := congrArg σ hrp
    rw [map_add, map_mul, map_mul, hr, hp] at this
    exact this.symm
  have h2 : (σ θ - θ) * (σ θ + θ - p) = 0 := by linear_combination h1 + hrp
  have h3 : σ θ = p - θ := by
    have := (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hθ)
    linear_combination this
  refine RingEquiv.ext fun c => ?_
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, rfl⟩ := hbij.2 c
  change σ (σ (a + b * θ)) = a + b * θ
  rw [map_add, map_mul, ha, hb, h3, map_add, map_mul, map_sub, ha, hb, hp, h3]
  ring

theorem exists_line_of_card_fixed (g : (Fin 2 → F) ≃+ (Fin 2 → F))
    (hlin : ∀ (a : F) (v : Fin 2 → F), g (a • v) = a • g v)
    (hcard : Nat.card {v : Fin 2 → F // g v = v} = Nat.card F) (hF : 1 < Nat.card F) :
    ∃ x : Fin 2 → F, x ≠ 0 ∧ ∀ w, g w = w ↔ ∃ c : F, w = c • x := by
  classical
  obtain ⟨x, hx0, hx⟩ : ∃ x : Fin 2 → F, x ≠ 0 ∧ g x = x := by
    by_contra hcon
    push Not at hcon
    have hsub : Subsingleton {v : Fin 2 → F // g v = v} :=
      ⟨fun a b => Subtype.ext (by
        have ha : a.1 = 0 := by by_contra hne; exact hcon a.1 hne a.2
        have hb : b.1 = 0 := by by_contra hne; exact hcon b.1 hne b.2
        rw [ha, hb])⟩
    have := (Finite.card_le_one_iff_subsingleton.mpr hsub)
    omega
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx0
  simp only [Pi.zero_apply] at hi
  let f : F → {v : Fin 2 → F // g v = v} := fun c => ⟨c • x, by rw [hlin, hx]⟩
  have hf : Function.Injective f := by
    intro c c' hcc'
    have := congrFun (congrArg Subtype.val hcc') i
    simp only [f, Pi.smul_apply, smul_eq_mul] at this
    exact mul_right_cancel₀ hi this
  have hbij := hf.bijective_of_nat_card_le hcard.le
  refine ⟨x, hx0, fun w => ⟨fun hw => ?_, ?_⟩⟩
  · obtain ⟨c, hc⟩ := hbij.2 ⟨w, hw⟩
    exact ⟨c, (congrArg Subtype.val hc).symm⟩
  · rintro ⟨c, rfl⟩
    rw [hlin, hx]

end Field

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G} {n : ℕ}

theorem Hyp611.pCoreOf_le_centralizer (h : Hyp611 G T M L V n) :
    pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ T) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans le_sup_left)
      (h.sup_le_normalizer_L.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
  rw [← h.centralizer_eq] at h1
  exact h1.trans inf_le_right

namespace Hyp611Nat

theorem toAdd_E_conj_rho (h : Hyp611Nat G T M L V n) (ℓ : ↥L) {u : G} (hu : u ∈ V)
    (hu' : (ℓ : G) * u * (ℓ : G)⁻¹ ∈ V) :
    Multiplicative.toAdd (h.data.E ⟨(ℓ : G) * u * (ℓ : G)⁻¹, hu'⟩) =
      ((h.data.rho ℓ : Matrix.SpecialLinearGroup (Fin 2) h.data.K) :
        Matrix (Fin 2) (Fin 2) h.data.K).mulVec (Multiplicative.toAdd (h.data.E ⟨u, hu⟩)) := by
  rw [← h.data.conj_eq_rho, h.data.conj_apply]
  congr 2

theorem exists_conj_ZS_of_line (h : Hyp611Nat G T M L V n) {U : Subgroup G} (hUV : U ≤ V)
    {x : Fin 2 → h.data.K} (hx : x ≠ 0)
    (hU : ∀ u (hu : u ∈ V),
      u ∈ U ↔ ∃ c : h.data.K, Multiplicative.toAdd (h.data.E ⟨u, hu⟩) = c • x) :
    ∃ l ∈ L, U = conjSubgroup (ch6ZS T L V) l := by
  obtain ⟨v, hv, hle⟩ := h.exists_line
  obtain ⟨A, hA⟩ := exists_sl2_mulVec_eq v x hv hx
  obtain ⟨ℓ, hℓ⟩ := h.data.rho_surjective A
  refine ⟨ℓ⁻¹, L.inv_mem ℓ.2, ?_⟩
  have hℓN : (ℓ : G) ∈ Subgroup.normalizer (V : Set G) := h.data.le_normalizer ℓ.2
  ext u
  rw [mem_conjSubgroup_iff, inv_inv]
  constructor
  · intro huU
    have huV := hUV huU
    obtain ⟨c, hc⟩ := (hU u huV).mp huU
    have hu' : (ℓ : G)⁻¹ * u * (ℓ : G)⁻¹⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hℓN) u).mp huV
    rw [inv_inv] at hu'
    refine (h.mem_ZS_iff_line hv hle ⟨_, hu'⟩).mpr ⟨c, ?_⟩
    have e := h.toAdd_E_conj_rho ℓ⁻¹ huV (by simpa using hu')
    simp only [Subgroup.coe_inv, inv_inv] at e
    rw [e, hc, Matrix.mulVec_smul, map_inv, hℓ, ← hA, inv_mulVec_mulVec]
  · intro hz
    have hz' : (ℓ : G)⁻¹ * u * ℓ ∈ V := hz.1
    have huV : u ∈ V := by
      have := (Subgroup.mem_normalizer_iff.mp hℓN _).mp hz'
      simpa [mul_assoc] using this
    obtain ⟨c, hc⟩ := (h.mem_ZS_iff_line hv hle ⟨_, hz'⟩).mp hz
    refine (hU u huV).mpr ⟨c, ?_⟩
    have e := h.toAdd_E_conj_rho ℓ hz' (by simpa [mul_assoc] using huV)
    have hu_eq : (ℓ : G) * ((ℓ : G)⁻¹ * u * ℓ) * (ℓ : G)⁻¹ = u := by group
    have : (⟨(ℓ : G) * ((ℓ : G)⁻¹ * u * ℓ) * (ℓ : G)⁻¹, by simpa [mul_assoc] using huV⟩ : ↥V) =
        ⟨u, huV⟩ := Subtype.ext hu_eq
    rw [this] at e
    rw [e, hc, Matrix.mulVec_smul, hℓ, hA]

end Hyp611Nat

theorem stmt6_1_13 (h432 : Stmt4_3_2) (h6110 : Stmt6_1_10) (hE612 : Ch6InE612) :
    Stmt6_1_13 := by
  classical
  intro G _ _ T M L V n h U hUV hmU
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE := h.hypE61 h432
  have hVcard : Nat.card V = 2 ^ n * 2 ^ n := h.natural.card_eq
  have h4 : 4 ≤ 2 ^ n :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h.two_le
  have hUcard : Nat.card U = 2 ^ n := by
    have hrel : U.relIndex V ∣ 2 ^ (n + n) := by
      rw [pow_add, ← hVcard]
      exact Subgroup.relIndex_dvd_card _ _
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hrel
    have hjn : j = n := by
      unfold mQuot at hmU
      rw [hj, padicValNat.prime_pow] at hmU
      exact hmU
    have h1 := card_mul_relIndex_of_le hUV
    rw [hj, hjn, hVcard] at h1
    exact Nat.eq_of_mul_eq_mul_right (by positivity) h1
  have hU1 : U ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hUcard
    omega
  by_cases hCM : M ⊓ Subgroup.centralizer (U : Set G) = M ⊓ Subgroup.centralizer (V : Set G)
  ·
    left
    by_contra hCU
    have hCUM : ¬ Subgroup.centralizer (U : Set G) ≤ M := fun hle => hCU fun c hc =>
      (h.normalizer_le hU1 hUV ⟨hle hc, Subgroup.centralizer_le_normalizer _ hc⟩).2
    have hr1 := (hE612 G T M V U hE hU1 hUV hCM hCUM).2
    have hr := (h6110 G T M L V n h).1
    rw [hr1] at hr
    have : n ≤ 1 := by exact_mod_cast hr
    have := h.two_le
    omega
  right
  have hle : M ⊓ Subgroup.centralizer (V : Set G) ≤ M ⊓ Subgroup.centralizer (U : Set G) :=
    inf_le_inf_left M (Subgroup.centralizer_le hUV)
  obtain ⟨m, ⟨hmM, hmU'⟩, hmV⟩ : ∃ m ∈ M ⊓ Subgroup.centralizer (U : Set G),
      m ∉ M ⊓ Subgroup.centralizer (V : Set G) := by
    by_contra hcon
    push Not at hcon
    exact hCM (le_antisymm hcon hle)
  have hmV' : m ∉ Subgroup.centralizer (V : Set G) := fun hc => hmV ⟨hmM, hc⟩
  have hmN : m ∈ Subgroup.normalizer (V : Set G) :=
    (h.normalizer_le hU1 hUV ⟨hmM, Subgroup.centralizer_le_normalizer _ hmU'⟩).2
  have hmL : m ∈ Subgroup.normalizer (L : Set G) := h.normal hmM
  set D := h.data with hD
  set mm : Subgroup.normalizer (V : Set G) := ⟨m, hmN⟩ with hmm
  obtain ⟨σ, hσ⟩ := D.exists_semilinear mm hmL
  have hUC : U = V ⊓ Subgroup.centralizer ({m} : Set G) := by
    have hsub : U ≤ V ⊓ Subgroup.centralizer ({m} : Set G) := fun u hu =>
      ⟨hUV hu, Subgroup.mem_centralizer_iff.mpr fun y hy => by
        rw [Set.mem_singleton_iff.mp hy]
        exact (Subgroup.mem_centralizer_iff.mp hmU' u hu).symm⟩
    exact Subgroup.eq_of_le_of_card_ge hsub
      (by rw [hUcard]; exact D.card_fixed_le_two_pow mm hmL hmV')
  have hfixcard : Nat.card {w : Fin 2 → D.K // D.conj mm w = w} = 2 ^ n := by
    rw [← Nat.card_congr (D.fixedEquiv mm), ← hUC, hUcard]
  have hmemU : ∀ u (hu : u ∈ V), u ∈ U ↔
      D.conj mm (Multiplicative.toAdd (D.E ⟨u, hu⟩)) = Multiplicative.toAdd (D.E ⟨u, hu⟩) := by
    intro u hu
    rw [hUC]
    constructor
    · rintro ⟨-, hc⟩
      exact D.conj_E_eq_of_commute mm ⟨u, hu⟩
        ((Subgroup.mem_centralizer_iff.mp hc m rfl))
    · intro hfix
      refine ⟨hu, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
      rw [Set.mem_singleton_iff.mp hy]
      rw [D.conj_apply] at hfix
      have h2 := congrArg Subtype.val (D.E.injective (Multiplicative.toAdd.injective hfix))
      rw [conjAct_apply_coe] at h2
      have h3 : m * u * m⁻¹ = u := h2
      calc m * u = (m * u * m⁻¹) * m := by group
        _ = u * m := by rw [h3]
  by_cases hσid : ∀ c, σ c = c
  ·
    left
    have hlin : ∀ (a : D.K) (w : Fin 2 → D.K), D.conj mm (a • w) = a • D.conj mm w :=
      fun a w => by rw [hσ, hσid]
    have hF : 1 < Nat.card D.K := by rw [D.card]; omega
    obtain ⟨x, hx0, hx⟩ := exists_line_of_card_fixed (D.conj mm) hlin
      (by rw [hfixcard, D.card]) hF
    exact h.exists_conj_ZS_of_line hUV hx0 fun u hu => (hmemU u hu).trans (hx _)
  ·
    right
    push Not at hσid
    obtain ⟨θ, hθ⟩ := hσid
    have hle1 := card_fixed_le_fix_mul_self (D.conj mm) σ hσ
    have hle2 := card_fixed_mul_self_le σ hθ
    rw [hfixcard] at hle1
    rw [D.card] at hle2
    have hF0 : Nat.card {c : D.K // σ c = c} * Nat.card {c : D.K // σ c = c} = 2 ^ n :=
      le_antisymm hle2 hle1
    have hEven : Even n := by
      have hdvd : Nat.card {c : D.K // σ c = c} ∣ 2 ^ n := Dvd.intro _ hF0
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      rw [hk, ← pow_add] at hF0
      exact ⟨k, (Nat.pow_right_injective (le_refl 2) hF0).symm⟩
    have hσ2 : σ * σ = 1 := mul_self_eq_one_of_card σ hθ (by rw [hF0, D.card])
    have hm2 : m * m ∈ Subgroup.centralizer (V : Set G) := by
      by_contra hc
      have hmm2 : mm * mm = ⟨m * m, (Subgroup.normalizer (V : Set G)).mul_mem hmN hmN⟩ := rfl
      have hlin2 : ∀ (a : D.K) (w : Fin 2 → D.K),
          D.conj (mm * mm) (a • w) = a • D.conj (mm * mm) w := by
        intro a w
        rw [D.conj_mul, D.conj_mul, hσ, hσ]
        change (σ * σ) a • _ = _
        rw [hσ2]
        rfl
      have hne : ∃ w, D.conj (mm * mm) w ≠ w := by
        by_contra hcon
        push Not at hcon
        exact hc (D.mem_centralizer_of_conj_eq (mm * mm) hcon)
      have hle3 := card_fixed_le_semilinear (D.conj (mm * mm)) (RingEquiv.refl D.K)
        (fun a w => hlin2 a w) hne
      rw [D.card] at hle3
      have hsubset : ∀ w, D.conj mm w = w → D.conj (mm * mm) w = w := fun w hw => by
        rw [D.conj_mul, hw, hw]
      have heq : ∀ w, D.conj (mm * mm) w = w → D.conj mm w = w := by
        intro w hw
        by_contra hw'
        have hinj : Function.Injective (fun v : {v : Fin 2 → D.K // D.conj mm v = v} =>
            (⟨v.1, hsubset v.1 v.2⟩ : {v : Fin 2 → D.K // D.conj (mm * mm) v = v})) :=
          fun a b hab => by
            have h1 := congrArg Subtype.val hab
            exact Subtype.ext h1
        have hnotsurj : ¬ Function.Surjective (fun v : {v : Fin 2 → D.K // D.conj mm v = v} =>
            (⟨v.1, hsubset v.1 v.2⟩ : {v : Fin 2 → D.K // D.conj (mm * mm) v = v})) := by
          intro hs
          obtain ⟨v, hv⟩ := hs ⟨w, hw⟩
          have h1 : v.1 = w := congrArg Subtype.val hv
          exact hw' (h1 ▸ v.2)
        apply hnotsurj
        exact (hinj.bijective_of_nat_card_le (by rw [hfixcard]; exact hle3)).2
      obtain ⟨x, hx0, hx⟩ : ∃ x : Fin 2 → D.K, x ≠ 0 ∧ D.conj mm x = x := by
        by_contra hcon
        push Not at hcon
        have hsub : Subsingleton {v : Fin 2 → D.K // D.conj mm v = v} :=
          ⟨fun a b => Subtype.ext (by
            have ha : a.1 = 0 := by by_contra hne; exact hcon a.1 hne a.2
            have hb : b.1 = 0 := by by_contra hne; exact hcon b.1 hne b.2
            rw [ha, hb])⟩
        have := Finite.card_le_one_iff_subsingleton.mpr hsub
        rw [hfixcard] at this
        omega
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hx0
      simp only [Pi.zero_apply] at hi
      apply hθ
      have h1 := heq (θ • x) (by rw [hlin2, hsubset x hx])
      rw [hσ, hx] at h1
      have := congrFun h1 i
      simp only [Pi.smul_apply, smul_eq_mul] at this
      exact mul_right_cancel₀ hi this
    refine ⟨hEven, m, hmM, ⟨hmL, ?_, ?_⟩, hUC⟩
    ·
      intro x hx
      have hxN : x ∈ Subgroup.normalizer (V : Set G) := D.le_normalizer hx
      refine h.toHyp5_0_1.inf_centralizer_le D.le_normalizer h.module.2.2 ⟨?_, ?_⟩
      · have h1 : m ^ 2 * x * (m ^ 2)⁻¹ ∈ L :=
          (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (L : Set G)).pow_mem hmL 2) x).mp
            hx
        exact L.mul_mem h1 (L.inv_mem hx)
      · have hm2' : m ^ 2 ∈ Subgroup.centralizer (V : Set G) := by rw [pow_two]; exact hm2
        have h1 : x * (m ^ 2)⁻¹ * x⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
          exact (Subgroup.mem_normalizer_iff.mp
            (F7.normalizer_le_normalizer_centralizer V hxN) ((m ^ 2)⁻¹)).mp
            (Subgroup.inv_mem _ hm2')
        have e : m ^ 2 * x * (m ^ 2)⁻¹ * x⁻¹ = m ^ 2 * (x * (m ^ 2)⁻¹ * x⁻¹) := by group
        rw [e]
        exact Subgroup.mul_mem _ hm2' h1
    ·
      rintro ⟨y, hyL, hy⟩
      have hyN : y ∈ Subgroup.normalizer (V : Set G) := D.le_normalizer hyL
      set m' : Subgroup.normalizer (V : Set G) := ⟨y⁻¹ * m, Subgroup.mul_mem _
        (Subgroup.inv_mem _ hyN) hmN⟩ with hm'
      have hcomm : ∀ g ∈ L, (m' : G) * g * (m' : G)⁻¹ * g⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
        intro g hg
        have h1 := hy g hg
        have h2 : y⁻¹ * ((m * g * m⁻¹) * (y * g * y⁻¹)⁻¹) * y ∈ pCoreOf 2 L := by
          have hN := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L (L.inv_mem hyL)
          have := (Subgroup.mem_normalizer_iff.mp hN _).mp h1
          simpa [mul_assoc] using this
        have e : (m' : G) * g * (m' : G)⁻¹ * g⁻¹ =
            y⁻¹ * ((m * g * m⁻¹) * (y * g * y⁻¹)⁻¹) * y := by
          simp only [hm']
          group
        rw [e]
        exact h.toHyp611.pCoreOf_le_centralizer h2
      obtain ⟨c, hc⟩ := D.exists_conj_eq_smul m' hcomm
      apply hθ
      have hmy : mm = ⟨y, hyN⟩ * m' := Subtype.ext (by simp [hm', hmm])
      obtain ⟨B, hB⟩ := D.exists_matrix_of_mem ⟨y, hyN⟩ hyL
      have hlin : ∀ (a : D.K) (w : Fin 2 → D.K), D.conj mm (a • w) = a • D.conj mm w := by
        intro a w
        rw [hmy, D.conj_mul, D.conj_mul, hc, hc, hB, hB, smul_smul, mul_comm, ← smul_smul,
          Matrix.mulVec_smul]
      have := semilinear_unique (D.conj mm) hσ (τ := RingEquiv.refl D.K) (fun a w => hlin a w)
      rw [this]
      rfl

end CFSG.Quasithin.H13
