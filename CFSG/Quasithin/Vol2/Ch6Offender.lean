module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem9
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesExtraBasic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped IsMulCommutative

section Field

variable {F : Type} [Field F]

theorem semilinear_unique (g : (Fin 2 → F) ≃+ (Fin 2 → F)) {σ τ : F ≃+* F}
    (hσ : ∀ (a : F) (w : Fin 2 → F), g (a • w) = σ a • g w)
    (hτ : ∀ (a : F) (w : Fin 2 → F), g (a • w) = τ a • g w) : σ = τ := by
  have hw : g ![1, 0] ≠ 0 := by
    intro h0
    have h1 : (![1, 0] : Fin 2 → F) = 0 := g.injective (h0.trans (map_zero g).symm)
    have := congrFun h1 0
    simp at this
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
  ext a
  have h1 := congrFun ((hσ a ![1, 0]).symm.trans (hτ a ![1, 0])) i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1 hi
  exact mul_right_cancel₀ hi h1

variable [Finite F]

theorem eq_one_of_pow_two_pow_eq_one_offender (hF : 2 ∣ Nat.card F) {x : F} {k : ℕ}
    (hx : x ^ 2 ^ k = 1) : x = 1 := by
  classical
  have := Fintype.ofFinite F
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [zero_pow (pow_ne_zero k two_ne_zero)] at hx
    exact zero_ne_one hx
  let u : Fˣ := Units.mk0 x hx0
  have hu : u ^ 2 ^ k = 1 := Units.ext (by simpa [u] using hx)
  have h1 : orderOf u ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hu
  have h2 : orderOf u ∣ Fintype.card Fˣ := orderOf_dvd_card
  rw [Fintype.card_units, ← Nat.card_eq_fintype_card] at h2
  have hodd : Odd (Nat.card F - 1) := by
    have hpos : 1 ≤ Nat.card F := Nat.one_le_iff_ne_zero.mpr Finite.card_pos.ne'
    obtain ⟨m, hm⟩ := hF
    rw [hm]
    have : 1 ≤ 2 * m := hm ▸ hpos
    exact ⟨m - 1, by omega⟩
  have hcop : Nat.Coprime (2 ^ k) (Nat.card F - 1) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  have hord : orderOf u = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  have := congrArg Units.val (orderOf_eq_one_iff.mp hord)
  simpa [u] using this

theorem card_fixed_mul_self_le (σ : F ≃+* F) {θ : F} (hθ : σ θ ≠ θ) :
    Nat.card {c : F // σ c = c} * Nat.card {c : F // σ c = c} ≤ Nat.card F := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective (fun p => p.1.1 + p.2.1 * θ) ?_
  rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ hab
  simp only at hab
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

theorem card_twisted_le (σ : F ≃+* F) {μ : F} (hμ : μ ≠ 0) (ν : F) :
    Nat.card {c : F // σ c * μ = ν * c} ≤ Nat.card {c : F // σ c = c} := by
  have : Nonempty {c : F // σ c = c} := ⟨⟨0, map_zero σ⟩⟩
  by_cases hex : ∃ c₀ : F, c₀ ≠ 0 ∧ σ c₀ * μ = ν * c₀
  · obtain ⟨c₀, hc₀, hc₀e⟩ := hex
    have hν : ν ≠ 0 := by
      rintro rfl
      rw [zero_mul] at hc₀e
      exact hc₀ (σ.injective (by rw [map_zero]; exact (mul_eq_zero.mp hc₀e).resolve_right hμ))
    refine Nat.card_le_card_of_injective (fun c => ⟨c.1 / c₀, ?_⟩) ?_
    · have hσc : σ c.1 = ν * c.1 / μ := by rw [eq_div_iff hμ]; exact c.2
      have hσc₀ : σ c₀ = ν * c₀ / μ := by rw [eq_div_iff hμ]; exact hc₀e
      rw [map_div₀, hσc, hσc₀]
      field_simp
    · intro c d hcd
      apply Subtype.ext
      have := congrArg Subtype.val hcd
      simp only at this
      exact (div_left_inj' hc₀).mp this
  · push Not at hex
    have hsub : Subsingleton {c : F // σ c * μ = ν * c} := by
      refine ⟨fun c d => Subtype.ext ?_⟩
      have hc : c.1 = 0 := by
        by_contra hne
        exact hex c.1 hne c.2
      have hd : d.1 = 0 := by
        by_contra hne
        exact hex d.1 hne d.2
      rw [hc, hd]
    exact (Finite.card_le_one_iff_subsingleton.mpr hsub).trans
      (Nat.one_le_iff_ne_zero.mpr Finite.card_pos.ne')

theorem ringEquiv_eq_of_mul_self_eq_one (hF : 2 ∣ Nat.card F) {σ₁ σ₂ : F ≃+* F}
    (h₁ : σ₁ * σ₁ = 1) (h₂ : σ₂ * σ₂ = 1) (h₁' : σ₁ ≠ 1) (h₂' : σ₂ ≠ 1) : σ₁ = σ₂ := by
  classical
  have := Fintype.ofFinite F
  have hchar : ringChar F = 2 := by
    rw [FiniteField.even_card_iff_char_two, ← Nat.card_eq_fintype_card]
    exact Nat.mod_eq_zero_of_dvd hF
  have : CharP F 2 := ringChar.of_eq hchar
  let _ : Algebra (ZMod 2) F := ZMod.algebra F 2
  have hcomm : ∀ σ : F ≃+* F, ∀ x : ZMod 2,
      σ (algebraMap (ZMod 2) F x) = algebraMap (ZMod 2) F x := by
    intro σ x
    have := RingHom.ext_zmod (σ.toRingHom.comp (algebraMap (ZMod 2) F)) (algebraMap (ZMod 2) F)
    exact congrArg (fun f => f x) this
  let τ : (F ≃+* F) →* (F ≃ₐ[ZMod 2] F) :=
    { toFun := fun σ => AlgEquiv.ofRingEquiv (f := σ) (hcomm σ)
      map_one' := by ext; rfl
      map_mul' := by intro a b; ext; rfl }
  have hτ : Function.Injective τ := by
    intro a b hab
    ext x
    exact congrArg (fun f : F ≃ₐ[ZMod 2] F => f x) hab
  by_contra hne
  have hcard := IsCyclic.card_pow_eq_one_le (α := F ≃ₐ[ZMod 2] F) (n := 2) (by norm_num)
  have hsub : ({1, τ σ₁, τ σ₂} : Finset (F ≃ₐ[ZMod 2] F)) ⊆
      Finset.univ.filter (fun a => a ^ 2 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl
    · simp
    · rw [pow_two, ← map_mul, h₁, map_one]
    · rw [pow_two, ← map_mul, h₂, map_one]
  have h3 : ({1, τ σ₁, τ σ₂} : Finset (F ≃ₐ[ZMod 2] F)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair]
    · intro h
      exact hne (hτ h)
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => h₁' (hτ (by rw [← h, map_one])),
        fun h => h₂' (hτ (by rw [← h, map_one]))⟩
  have := Finset.card_le_card hsub
  omega

end Field

section NatData

variable {G : Type} [Group G] {L V : Subgroup G} {n : ℕ}

namespace NatL2Data

variable (D : NatL2Data L V n)

theorem conj_E_eq_of_commute (m : Subgroup.normalizer (V : Set G)) (z : ↥V)
    (hz : (m : G) * z = z * m) :
    D.conj m (Multiplicative.toAdd (D.E z)) = Multiplicative.toAdd (D.E z) := by
  have hc : conjAct V m z = z := by
    apply Subtype.ext
    rw [conjAct_apply_coe, hz]
    group
  rw [D.conj_apply, hc]

end NatL2Data

end NatData

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G} {n : ℕ}

namespace Hyp611Nat

theorem T_le_normalizer_L (h : Hyp611Nat G T M L V n) : T ≤ Subgroup.normalizer (L : Set G) :=
  fun _ ht => h.normal (h.T_le ht)

theorem exists_conj_eq_smul_of_mem_T (h : Hyp611Nat G T M L V n) {v : Fin 2 → h.data.K}
    (hv : v ≠ 0) (hle : h.rhoTL ≤ sl2Stab v) {t : G} (ht : t ∈ T) :
    ∃ μ : h.data.K, h.data.conj ⟨t, h.toHyp611.T_le_normalizer ht⟩ v = μ • v := by
  set m : Subgroup.normalizer (V : Set G) := ⟨t, h.toHyp611.T_le_normalizer ht⟩ with hm
  set z : ↥V := h.data.E.symm (Multiplicative.ofAdd v) with hzdef
  have hEz : Multiplicative.toAdd (h.data.E z) = v := by simp [hzdef]
  have hz : (z : G) ∈ ch6ZS T L V :=
    (h.mem_ZS_iff_line hv hle z).mpr ⟨1, by rw [hEz, one_smul]⟩
  have hz' : ((conjAct V m z : ↥V) : G) ∈ ch6ZS T L V := by
    rw [conjAct_apply_coe]
    exact (Subgroup.mem_normalizer_iff.mp (h.T_le_normalizer_ZS ht) z).mp hz
  obtain ⟨μ, hμ⟩ := (h.mem_ZS_iff_line hv hle (conjAct V m z)).mp hz'
  refine ⟨μ, ?_⟩
  calc h.data.conj m v = h.data.conj m (Multiplicative.toAdd (h.data.E z)) := by rw [hEz]
    _ = Multiplicative.toAdd (h.data.E (conjAct V m z)) := h.data.conj_apply m z
    _ = μ • v := hμ

theorem mem_centralizer_ZS_of_linear (h : Hyp611Nat G T M L V n) {v : Fin 2 → h.data.K}
    (hv : v ≠ 0) (hle : h.rhoTL ≤ sl2Stab v) {t : G} (ht : t ∈ T)
    (hlin : ∀ (c : h.data.K) (w : Fin 2 → h.data.K),
      h.data.conj ⟨t, h.toHyp611.T_le_normalizer ht⟩ (c • w) =
        c • h.data.conj ⟨t, h.toHyp611.T_le_normalizer ht⟩ w) :
    t ∈ Subgroup.centralizer (ch6ZS T L V : Set G) := by
  obtain ⟨μ, hμ⟩ := h.exists_conj_eq_smul_of_mem_T hv hle ht
  set m : Subgroup.normalizer (V : Set G) := ⟨t, h.toHyp611.T_le_normalizer ht⟩ with hm
  obtain ⟨k, hk⟩ := h.sylow.1 ⟨t, ht⟩
  have htk : t ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hiter : ∀ j : ℕ, (h.data.conj m)^[j] v = μ ^ j • v := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [Function.iterate_succ_apply', ih, hlin, hμ, smul_smul, pow_succ]
  have hpow : (h.data.conj m)^[2 ^ k] v = v := by
    rw [← h.data.conj_pow]
    have : m ^ 2 ^ k = 1 := Subtype.ext (by simpa [hm] using htk)
    rw [this]
    exact h.data.conj_eq_of_mem_centralizer 1 (Subgroup.one_mem _) v
  have hμk : μ ^ 2 ^ k = 1 := by
    rw [hiter] at hpow
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
    have h1 := congrFun hpow i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1 hi
    have h2 : (μ ^ 2 ^ k - 1) * v i = 0 := by rw [sub_mul, h1, one_mul, sub_self]
    exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right hi)
  have hμ1 : μ = 1 := eq_one_of_pow_two_pow_eq_one_offender h.two_dvd_card_K hμk
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  obtain ⟨c, hc⟩ := (h.mem_ZS_iff_line hv hle ⟨z, hz.1⟩).mp hz
  have h1 : h.data.conj m (Multiplicative.toAdd (h.data.E ⟨z, hz.1⟩)) =
      Multiplicative.toAdd (h.data.E ⟨z, hz.1⟩) := by
    rw [hc, hlin, hμ, hμ1, one_smul]
  rw [h.data.conj_apply] at h1
  have h2 := congrArg Subtype.val (h.data.E.injective (Multiplicative.toAdd.injective h1))
  rw [conjAct_apply_coe] at h2
  have h3 : t * z * t⁻¹ = z := h2
  calc z * t = (t * z * t⁻¹) * t := by rw [h3]
    _ = t * z := by group

theorem semilinear_of_not_mem (h : Hyp611Nat G T M L V n) {v : Fin 2 → h.data.K}
    (hv : v ≠ 0) (hle : h.rhoTL ≤ sl2Stab v) {A : Subgroup G} (hAT : A ≤ T)
    (hA : IsElemAbelian 2 A) {a : G} (ha : a ∈ A)
    (haZ : a ∉ Subgroup.centralizer (ch6ZS T L V : Set G)) {σ : h.data.K ≃+* h.data.K}
    (hσ : ∀ (c : h.data.K) (w : Fin 2 → h.data.K),
      h.data.conj ⟨a, h.toHyp611.T_le_normalizer (hAT ha)⟩ (c • w) =
        σ c • h.data.conj ⟨a, h.toHyp611.T_le_normalizer (hAT ha)⟩ w) :
    σ ≠ 1 ∧ σ * σ = 1 := by
  set m : Subgroup.normalizer (V : Set G) := ⟨a, h.toHyp611.T_le_normalizer (hAT ha)⟩ with hm
  refine ⟨fun h1 => haZ (h.mem_centralizer_ZS_of_linear hv hle (hAT ha) fun c w => ?_), ?_⟩
  · rw [hσ, h1]
    rfl
  · have hmm : m * m = 1 := Subtype.ext (by
      have := hA.2 a ha
      rw [pow_two] at this
      exact this)
    refine semilinear_unique (h.data.conj (m * m)) (fun c w => ?_) (fun c w => ?_)
    · rw [h.data.conj_mul, h.data.conj_mul, hσ, hσ]
      rfl
    · rw [hmm, h.data.conj_eq_of_mem_centralizer 1 (Subgroup.one_mem _),
        h.data.conj_eq_of_mem_centralizer 1 (Subgroup.one_mem _)]
      rfl

theorem mul_mem_centralizer_ZS (h : Hyp611Nat G T M L V n) {A : Subgroup G} (hAT : A ≤ T)
    (hA : IsElemAbelian 2 A) {x y : G} (hx : x ∈ A) (hy : y ∈ A)
    (hxZ : x ∉ Subgroup.centralizer (ch6ZS T L V : Set G))
    (hyZ : y ∉ Subgroup.centralizer (ch6ZS T L V : Set G)) :
    x * y ∈ Subgroup.centralizer (ch6ZS T L V : Set G) := by
  obtain ⟨v, hv, hle⟩ := h.exists_line
  have hTN : ∀ {t : G}, t ∈ T → t ∈ Subgroup.normalizer (V : Set G) :=
    fun ht => h.toHyp611.T_le_normalizer ht
  obtain ⟨σx, hσx⟩ := h.data.exists_semilinear ⟨x, hTN (hAT hx)⟩ (h.T_le_normalizer_L (hAT hx))
  obtain ⟨σy, hσy⟩ := h.data.exists_semilinear ⟨y, hTN (hAT hy)⟩ (h.T_le_normalizer_L (hAT hy))
  obtain ⟨hx1, hx2⟩ := h.semilinear_of_not_mem hv hle hAT hA hx hxZ hσx
  obtain ⟨hy1, hy2⟩ := h.semilinear_of_not_mem hv hle hAT hA hy hyZ hσy
  have hxy : σx = σy := ringEquiv_eq_of_mul_self_eq_one h.two_dvd_card_K hx2 hy2 hx1 hy1
  refine h.mem_centralizer_ZS_of_linear hv hle (T.mul_mem (hAT hx) (hAT hy)) fun c w => ?_
  have e : (⟨x * y, hTN (T.mul_mem (hAT hx) (hAT hy))⟩ : Subgroup.normalizer (V : Set G)) =
      ⟨x, hTN (hAT hx)⟩ * ⟨y, hTN (hAT hy)⟩ := rfl
  rw [e, h.data.conj_mul, h.data.conj_mul, hσy, hσx, ← hxy]
  change (σx * σx) c • _ = _
  rw [hx2]
  rfl

theorem card_le_two_mul_inf_ZS (h : Hyp611Nat G T M L V n) {A : Subgroup G} (hAT : A ≤ T)
    (hA : IsElemAbelian 2 A) :
    Nat.card A ≤ 2 * Nat.card ↥(A ⊓ Subgroup.centralizer (ch6ZS T L V : Set G)) := by
  set A₁ := A ⊓ Subgroup.centralizer (ch6ZS T L V : Set G) with hA₁
  by_cases hAZ : A ≤ Subgroup.centralizer (ch6ZS T L V : Set G)
  · rw [hA₁, inf_eq_left.mpr hAZ]
    omega
  obtain ⟨a₀, ha₀A, ha₀Z⟩ := Set.not_subset.mp hAZ
  have hidx : (A₁.subgroupOf A).index ∣ 2 := by
    rw [Subgroup.index_dvd_two_iff]
    refine ⟨⟨a₀, ha₀A⟩, fun b => ?_⟩
    by_cases hb : (b : G) ∈ Subgroup.centralizer (ch6ZS T L V : Set G)
    · exact Or.inr (Subgroup.mem_subgroupOf.mpr ⟨b.2, hb⟩)
    · exact Or.inl (Subgroup.mem_subgroupOf.mpr
        ⟨(b * ⟨a₀, ha₀A⟩ : ↥A).2, h.mul_mem_centralizer_ZS hAT hA b.2 ha₀A hb ha₀Z⟩)
  have h1 := Subgroup.card_mul_index (A₁.subgroupOf A)
  have h2 : Nat.card (A₁.subgroupOf A) = Nat.card A₁ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have h3 : (A₁.subgroupOf A).index ≤ 2 := Nat.le_of_dvd two_pos hidx
  rw [h2] at h1
  calc Nat.card A = Nat.card A₁ * (A₁.subgroupOf A).index := h1.symm
    _ ≤ Nat.card A₁ * 2 := Nat.mul_le_mul_left _ h3
    _ = 2 * Nat.card A₁ := mul_comm _ _

omit [Finite G] in
theorem exists_det2_ne_zero {K : Type} [Field K] {v : Fin 2 → K} (hv : v ≠ 0) :
    ∃ w₀ : Fin 2 → K, det2 v w₀ ≠ 0 := by
  by_cases h0 : v 0 = 0
  · refine ⟨![1, 0], ?_⟩
    have h1 : v 1 ≠ 0 := by
      intro h1
      apply hv
      funext i
      fin_cases i <;> simp [h0, h1]
    simp [det2, h1]
  · exact ⟨![0, 1], by simp [det2, h0]⟩

theorem card_inf_ZS_le (h : Hyp611Nat G T M L V n) {A : Subgroup G} (hAT : A ≤ T)
    (hA : IsElemAbelian 2 A) {a₀ : G} (ha₀A : a₀ ∈ A) {σ₀ : h.data.K ≃+* h.data.K}
    (hσ₀ : ∀ (c : h.data.K) (w : Fin 2 → h.data.K),
      h.data.conj ⟨a₀, h.toHyp611.T_le_normalizer (hAT ha₀A)⟩ (c • w) =
        σ₀ c • h.data.conj ⟨a₀, h.toHyp611.T_le_normalizer (hAT ha₀A)⟩ w) :
    Nat.card ↥(A ⊓ Subgroup.centralizer (ch6ZS T L V : Set G)) ≤
      Nat.card {c : h.data.K // σ₀ c = c} * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) := by
  classical
  obtain ⟨v, hv, hle⟩ := h.exists_line
  set A₁ := A ⊓ Subgroup.centralizer (ch6ZS T L V : Set G) with hA₁
  set m₀ : Subgroup.normalizer (V : Set G) := ⟨a₀, h.toHyp611.T_le_normalizer (hAT ha₀A)⟩
    with hm₀
  obtain ⟨κ₀, hκ₀⟩ := h.exists_conj_eq_smul_of_mem_T hv hle (hAT ha₀A)
  have hκ₀0 : κ₀ ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hκ₀
    exact hv ((h.data.conj m₀).injective (hκ₀.trans (map_zero _).symm))
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hv
  simp only [Pi.zero_apply] at hi₀
  obtain ⟨w₀, hdet⟩ := exists_det2_ne_zero hv
  obtain ⟨α', β', hαβ⟩ : ∃ α' β' : h.data.K, h.data.conj m₀ w₀ = α' • v + β' • w₀ :=
    ⟨_, _, eq_add_of_det2_ne_zero hdet _⟩
  have hxS : ∀ x : ↥A₁, (x : G) ∈ ch6S T L V := fun x => ⟨hAT x.2.1, x.2.2⟩
  let mx : ↥A₁ → Subgroup.normalizer (V : Set G) := fun x =>
    ⟨x, h.toHyp611.T_le_normalizer (hxS x).1⟩
  have hmat : ∀ x : ↥A₁, ∃ B ∈ sl2Stab v, ∀ w, h.data.conj (mx x) w =
      (B : Matrix (Fin 2) (Fin 2) h.data.K).mulVec w :=
    fun x => h.exists_stab_of_mem_S hv hle (hxS x)
  have hfixv : ∀ x : ↥A₁, h.data.conj (mx x) v = v := by
    intro x
    obtain ⟨B, hB, hBeq⟩ := hmat x
    rw [hBeq]
    exact hB
  have hlinx : ∀ (x : ↥A₁) (c : h.data.K) (w : Fin 2 → h.data.K),
      h.data.conj (mx x) (c • w) = c • h.data.conj (mx x) w := by
    intro x c w
    obtain ⟨B, -, hBeq⟩ := hmat x
    rw [hBeq, hBeq, Matrix.mulVec_smul]
  let cf : ↥A₁ → h.data.K := fun x => (h.data.conj (mx x) w₀ - w₀) i₀ / v i₀
  have hcf : ∀ x : ↥A₁, h.data.conj (mx x) w₀ = w₀ + cf x • v := by
    intro x
    obtain ⟨B, hB, hBeq⟩ := hmat x
    obtain ⟨c, hc⟩ := sub_mem_line_of_mem_sl2Stab hv hB w₀
    rw [← hBeq] at hc
    have hcx : cf x = c := by
      simp only [cf, hc, Pi.smul_apply, smul_eq_mul]
      rw [mul_div_assoc, div_self hi₀, mul_one]
    rw [hcx, ← hc]
    abel
  have hmul : ∀ x y : ↥A₁, mx (x * y) = mx x * mx y := fun _ _ => rfl
  have hcf_mul : ∀ x y : ↥A₁, cf (x * y) = cf x + cf y := by
    intro x y
    have h1 : h.data.conj (mx (x * y)) w₀ - w₀ = (cf x + cf y) • v := by
      rw [hmul, h.data.conj_mul, hcf y, map_add, hlinx, hfixv, hcf x, add_smul]
      abel
    simp only [cf]
    rw [h1]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [mul_div_assoc, div_self hi₀, mul_one]
  have hcf_one : cf 1 = 0 := by
    have h1 : h.data.conj (mx 1) w₀ = w₀ :=
      h.data.conj_eq_of_mem_centralizer (mx 1) (Subgroup.one_mem _) w₀
    simp only [cf, h1, sub_self, Pi.zero_apply, zero_div]
  let φ : ↥A₁ →* Multiplicative h.data.K :=
    { toFun := fun x => Multiplicative.ofAdd (cf x)
      map_one' := by rw [hcf_one, ofAdd_zero]
      map_mul' := fun x y => by rw [hcf_mul, ofAdd_add] }
  have hker : ∀ x : ↥A₁, φ x = 1 → (x : G) ∈ Subgroup.centralizer (V : Set G) := by
    intro x hx
    have hx0 : cf x = 0 := by
      have : Multiplicative.ofAdd (cf x) = Multiplicative.ofAdd 0 := hx.trans ofAdd_zero.symm
      exact Multiplicative.ofAdd.injective this
    have hw₀ : h.data.conj (mx x) w₀ = w₀ := by rw [hcf x, hx0, zero_smul, add_zero]
    apply h.data.mem_centralizer_of_conj_eq (mx x)
    intro w
    rw [eq_add_of_det2_ne_zero hdet w, map_add, hlinx, hlinx, hfixv, hw₀]
  have hrange : ∀ x : ↥A₁, σ₀ (cf x) * κ₀ = β' * cf x := by
    intro x
    have hcomm : m₀ * mx x = mx x * m₀ :=
      Subtype.ext (B2F.isElemAbelian_comm hA ha₀A x.2.1)
    have h1 : h.data.conj (m₀ * mx x) w₀ = h.data.conj (mx x * m₀) w₀ := by rw [hcomm]
    rw [h.data.conj_mul, h.data.conj_mul, hcf x, map_add, hσ₀, hκ₀, hαβ, map_add, hlinx,
      hlinx, hfixv, hcf x, smul_smul] at h1
    have h2 := congrFun h1 i₀
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h2
    have h3 : (σ₀ (cf x) * κ₀ - β' * cf x) * v i₀ = 0 := by linear_combination h2
    exact sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_right hi₀)
  have hcardA₁ : Nat.card A₁ = Nat.card φ.ker * Nat.card φ.range := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  have hk : Nat.card φ.ker ≤ Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) := by
    refine Nat.card_le_card_of_injective (fun x =>
      ⟨((x : ↥A₁) : G), (x : ↥A₁).2.1, hker x (MonoidHom.mem_ker.mp x.2)⟩) ?_
    intro x y hxy
    have h1 := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext h1)
  have hr : Nat.card φ.range ≤ Nat.card {c : h.data.K // σ₀ c = c} := by
    refine le_trans ?_ (card_twisted_le σ₀ hκ₀0 β')
    refine Nat.card_le_card_of_injective (fun y => ⟨Multiplicative.toAdd (y : _), ?_⟩) ?_
    · obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp y.2
      rw [← hx]
      exact hrange x
    · intro y y' hyy'
      have h1 := congrArg Subtype.val hyy'
      exact Subtype.ext (Multiplicative.toAdd.injective h1)
  rw [hcardA₁, mul_comm]
  exact Nat.mul_le_mul hr hk

theorem card_le_two_pow_mul (h : Hyp611Nat G T M L V n) {A : Subgroup G} (hAT : A ≤ T)
    (hA : IsElemAbelian 2 A) :
    Nat.card A ≤ 2 ^ n * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) := by
  classical
  obtain ⟨v, hv, hle⟩ := h.exists_line
  by_cases hAZ : A ≤ Subgroup.centralizer (ch6ZS T L V : Set G)
  ·
    have h1 := h.card_inf_ZS_le hAT hA A.one_mem (σ₀ := RingEquiv.refl h.data.K)
      (fun c w => by
        rw [h.data.conj_eq_of_mem_centralizer _ (Subgroup.one_mem _),
          h.data.conj_eq_of_mem_centralizer _ (Subgroup.one_mem _)]
        rfl)
    have h2 : Nat.card {c : h.data.K // (RingEquiv.refl h.data.K) c = c} = 2 ^ n := by
      rw [← h.data.card]
      exact Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => rfl)
    rw [inf_eq_left.mpr hAZ, h2] at h1
    exact h1
  · obtain ⟨a₀, ha₀A, ha₀Z⟩ := Set.not_subset.mp hAZ
    obtain ⟨σ₀, hσ₀⟩ := h.data.exists_semilinear ⟨a₀, h.toHyp611.T_le_normalizer (hAT ha₀A)⟩
      (h.T_le_normalizer_L (hAT ha₀A))
    obtain ⟨hσ1, -⟩ := h.semilinear_of_not_mem hv hle hAT hA ha₀A ha₀Z hσ₀
    obtain ⟨θ, hθ⟩ : ∃ θ, σ₀ θ ≠ θ := by
      by_contra hcon
      push Not at hcon
      exact hσ1 (RingEquiv.ext hcon)
    have hF0 := card_fixed_mul_self_le σ₀ hθ
    rw [h.data.card] at hF0
    have h2 : 2 ≤ Nat.card {c : h.data.K // σ₀ c = c} := by
      have : Nontrivial {c : h.data.K // σ₀ c = c} :=
        ⟨⟨⟨0, map_zero σ₀⟩, ⟨1, map_one σ₀⟩, fun h0 => zero_ne_one (congrArg Subtype.val h0)⟩⟩
      exact Finite.one_lt_card_iff_nontrivial.mpr this
    have h3 := h.card_le_two_mul_inf_ZS hAT hA
    have h4 := h.card_inf_ZS_le hAT hA ha₀A hσ₀
    calc Nat.card A ≤ 2 * Nat.card ↥(A ⊓ Subgroup.centralizer (ch6ZS T L V : Set G)) := h3
      _ ≤ 2 * (Nat.card {c : h.data.K // σ₀ c = c} *
          Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G))) := Nat.mul_le_mul_left _ h4
      _ = 2 * Nat.card {c : h.data.K // σ₀ c = c} *
          Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) := by ring
      _ ≤ Nat.card {c : h.data.K // σ₀ c = c} * Nat.card {c : h.data.K // σ₀ c = c} *
          Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h2)
      _ ≤ 2 ^ n * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) :=
          Nat.mul_le_mul_right _ hF0

theorem le_S_of_card (h : Hyp611Nat G T M L V n) {A : Subgroup G} (hAT : A ≤ T)
    (hA : IsElemAbelian 2 A)
    (hcard : Nat.card V * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) ≤
      Nat.card A * Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G))) :
    A ≤ ch6S T L V := by
  classical
  obtain ⟨v, hv, hle⟩ := h.exists_line
  have hTN : ∀ {t : G}, t ∈ T → t ∈ Subgroup.normalizer (V : Set G) :=
    fun ht => h.toHyp611.T_le_normalizer ht
  have hCV : Subgroup.centralizer (V : Set G) ≤
      Subgroup.centralizer (ch6ZS T L V : Set G) := Subgroup.centralizer_le h.ZS_le
  by_contra hnot
  obtain ⟨a₀, ha₀A, ha₀S⟩ := Set.not_subset.mp hnot
  have ha₀T : a₀ ∈ T := hAT ha₀A
  have ha₀Z : a₀ ∉ Subgroup.centralizer (ch6ZS T L V : Set G) := fun hc => ha₀S ⟨ha₀T, hc⟩
  have ha₀V : a₀ ∉ Subgroup.centralizer (V : Set G) := fun hc => ha₀Z (hCV hc)
  set A₁ := A ⊓ Subgroup.centralizer (ch6ZS T L V : Set G) with hA₁
  have hclaim1 : Nat.card A ≤ 2 * Nat.card A₁ := h.card_le_two_mul_inf_ZS hAT hA
  have hclaim2 : Nat.card A₁ * Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) ≤
      2 ^ n * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) := by
    by_cases hcase : A₁ ≤ Subgroup.centralizer (V : Set G)
    · have e1 : Nat.card A₁ ≤ Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) :=
        Subgroup.card_le_of_le (le_inf inf_le_left hcase)
      have e2 : Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) ≤ 2 ^ n :=
        le_trans (Subgroup.card_le_of_le (inf_le_inf_left V
          (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha₀A))))
          (h.data.card_fixed_le_two_pow ⟨a₀, hTN ha₀T⟩ (h.T_le_normalizer_L ha₀T) ha₀V)
      calc Nat.card A₁ * Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) ≤
          Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) * 2 ^ n := Nat.mul_le_mul e1 e2
        _ = _ := mul_comm _ _
    · obtain ⟨x₁, hx₁A₁, hx₁V⟩ := Set.not_subset.mp hcase
      have hx₁S : x₁ ∈ ch6S T L V := ⟨hAT hx₁A₁.1, hx₁A₁.2⟩
      obtain ⟨B₁, hB₁, hB₁eq⟩ := h.exists_stab_of_mem_S hv hle hx₁S
      have hB₁1 : B₁ ≠ 1 := by
        rintro rfl
        apply hx₁V
        apply h.data.mem_centralizer_of_conj_eq ⟨x₁, h.toHyp611.T_le_normalizer hx₁S.1⟩
        intro w
        rw [hB₁eq]
        simp
      set m₀ : Subgroup.normalizer (V : Set G) := ⟨a₀, hTN ha₀T⟩ with hm₀
      obtain ⟨σ₀, hσ₀⟩ := h.data.exists_semilinear m₀ (h.T_le_normalizer_L ha₀T)
      obtain ⟨κ₀, hκ₀⟩ := h.exists_conj_eq_smul_of_mem_T hv hle ha₀T
      have hκ₀0 : κ₀ ≠ 0 := by
        intro h0
        rw [h0, zero_smul] at hκ₀
        exact hv ((h.data.conj m₀).injective (hκ₀.trans (map_zero _).symm))
      obtain ⟨θ, hθ⟩ : ∃ θ, σ₀ θ ≠ θ := by
        by_contra hcon
        push Not at hcon
        exact ha₀Z (h.mem_centralizer_ZS_of_linear hv hle ha₀T fun c w => by rw [hσ₀, hcon])
      have hF0 := card_fixed_mul_self_le σ₀ hθ
      rw [h.data.card] at hF0
      obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hv
      simp only [Pi.zero_apply] at hi₀
      have hb1 : Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) ≤
          Nat.card {c : h.data.K // σ₀ c = c} := by
        refine le_trans ?_ (card_twisted_le σ₀ hκ₀0 1)
        have hline : ∀ z : ↥(V ⊓ Subgroup.centralizer (A : Set G)),
            ∃ c : h.data.K, Multiplicative.toAdd (h.data.E ⟨z, z.2.1⟩) = c • v ∧
              σ₀ c * κ₀ = 1 * c := by
          intro z
          have hcomm : ∀ a ∈ A, a * (z : G) = z * a := fun a ha =>
            Subgroup.mem_centralizer_iff.mp z.2.2 a ha
          have hfx := h.data.conj_E_eq_of_commute ⟨x₁, h.toHyp611.T_le_normalizer hx₁S.1⟩
            ⟨z, z.2.1⟩ (hcomm x₁ hx₁A₁.1)
          rw [hB₁eq] at hfx
          obtain ⟨c, hc⟩ := fixed_eq_line (Subgroup.zpowers B₁)
            (fun h0 => hB₁1 (Subgroup.zpowers_eq_bot.mp h0)) hv
            (fun B hB => (Subgroup.zpowers_le.mpr hB₁ : Subgroup.zpowers B₁ ≤ sl2Stab v) hB)
            (w := Multiplicative.toAdd (h.data.E ⟨z, z.2.1⟩))
            (fun B hB => (Subgroup.zpowers_le.mpr (show B₁ ∈ sl2Stab _ from hfx) :
              Subgroup.zpowers B₁ ≤ sl2Stab _) hB)
          refine ⟨c, hc, ?_⟩
          have hf0 := h.data.conj_E_eq_of_commute m₀ ⟨z, z.2.1⟩ (hcomm a₀ ha₀A)
          rw [hc, hσ₀, hκ₀, smul_smul] at hf0
          have := congrFun hf0 i₀
          simp only [Pi.smul_apply, smul_eq_mul] at this
          rw [one_mul]
          exact mul_right_cancel₀ hi₀ this
        refine Nat.card_le_card_of_injective (fun z =>
          ⟨Multiplicative.toAdd (h.data.E ⟨z, z.2.1⟩) i₀ / v i₀, ?_⟩) ?_
        · obtain ⟨c, hc, hce⟩ := hline z
          rw [hc]
          simp only [Pi.smul_apply, smul_eq_mul]
          rw [mul_div_assoc, div_self hi₀, mul_one]
          exact hce
        · intro z z' hzz'
          obtain ⟨c, hc, -⟩ := hline z
          obtain ⟨c', hc', -⟩ := hline z'
          have h1 := congrArg Subtype.val hzz'
          simp only [hc, hc', Pi.smul_apply, smul_eq_mul] at h1
          rw [mul_div_assoc, div_self hi₀, mul_one, mul_div_assoc, div_self hi₀,
            mul_one] at h1
          have h2 : h.data.E ⟨z, z.2.1⟩ = h.data.E ⟨z', z'.2.1⟩ := by
            apply Multiplicative.toAdd.injective
            rw [hc, hc', h1]
          have h3 := congrArg Subtype.val (h.data.E.injective h2)
          exact Subtype.ext h3
      have hb2 := h.card_inf_ZS_le hAT hA ha₀A hσ₀
      calc Nat.card A₁ * Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) ≤
          (Nat.card {c : h.data.K // σ₀ c = c} *
            Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G))) *
              Nat.card {c : h.data.K // σ₀ c = c} := Nat.mul_le_mul hb2 hb1
        _ = (Nat.card {c : h.data.K // σ₀ c = c} * Nat.card {c : h.data.K // σ₀ c = c}) *
            Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) := by ring
        _ ≤ 2 ^ n * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) :=
            Nat.mul_le_mul_right _ hF0
  have hVcard : Nat.card V = 2 ^ n * 2 ^ n := h.natural.card_eq
  have hpos : 0 < Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) := Nat.card_pos
  have h4 : 4 ≤ 2 ^ n :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h.two_le
  have key : 2 ^ n * 2 ^ n * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) ≤
      2 * 2 ^ n * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) :=
    calc 2 ^ n * 2 ^ n * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) =
        Nat.card V * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) := by rw [hVcard]
      _ ≤ Nat.card A * Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) := hcard
      _ ≤ 2 * Nat.card A₁ * Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) :=
          Nat.mul_le_mul_right _ hclaim1
      _ = 2 * (Nat.card A₁ * Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G))) := by ring
      _ ≤ 2 * (2 ^ n * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G))) :=
          Nat.mul_le_mul_left _ hclaim2
      _ = 2 * 2 ^ n * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) := by ring
  have hq : 2 ^ n * 2 ^ n ≤ 2 * 2 ^ n := Nat.le_of_mul_le_mul_right key hpos
  have hq' : 2 ^ n ≤ 2 := Nat.le_of_mul_le_mul_right hq (by positivity)
  omega

theorem thompsonJ_le_S (h : Hyp611Nat G T M L V n) : thompsonJ T ≤ ch6S T L V := by
  refine GammaExtra.thompsonJ_le fun A hA => h.le_S_of_card hA.1 hA.2.1 ?_
  have hV := h.toHyp611.isElemAbelian
  have hcomm : ∀ a ∈ A ⊓ Subgroup.centralizer (V : Set G), ∀ b ∈ V, a * b = b * a :=
    fun a ha b hb => (Subgroup.mem_centralizer_iff.mp ha.2 b hb).symm
  have hDe : IsElemAbelian 2 ((A ⊓ Subgroup.centralizer (V : Set G)) ⊔ V) :=
    B2F.isElemAbelian_sup_of_commute (B2F.isElemAbelian_mono inf_le_left hA.2.1) hV hcomm
  have hDT : (A ⊓ Subgroup.centralizer (V : Set G)) ⊔ V ≤ T :=
    sup_le (inf_le_left.trans hA.1) h.toHyp611.le_T
  have hDA : Nat.card ↥((A ⊓ Subgroup.centralizer (V : Set G)) ⊔ V) ≤ Nat.card A :=
    hA.2.2 _ hDT hDe
  have hcard := B2F.card_sup_mul_card_inf_of_commute hcomm
  have hinf : Nat.card ↥((A ⊓ Subgroup.centralizer (V : Set G)) ⊓ V) ≤
      Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) := by
    refine Subgroup.card_le_of_le fun x hx => ⟨hx.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro a ha
    exact B2F.isElemAbelian_comm hA.2.1 ha hx.1.1
  calc Nat.card V * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) =
      Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) * Nat.card V := mul_comm _ _
    _ = Nat.card ↥((A ⊓ Subgroup.centralizer (V : Set G)) ⊔ V) *
        Nat.card ↥((A ⊓ Subgroup.centralizer (V : Set G)) ⊓ V) := hcard.symm
    _ ≤ Nat.card A * Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) := Nat.mul_le_mul hDA hinf

theorem thompsonJ_eq (h : Hyp611Nat G T M L V n) : thompsonJ T = thompsonJ (ch6S T L V) :=
  (GammaExtra.thompsonJ_eq_of_le h.thompsonJ_le_S inf_le_left).symm

theorem ZS_le_omegaOneCenter_thompsonJ (h : Hyp611Nat G T M L V n) :
    ch6ZS T L V ≤ omegaOneCenterOf (thompsonJ T) := by
  have hJS := h.thompsonJ_le_S
  obtain ⟨A, hA⟩ := GammaExtra.exists_isMaxElemAbelian T
  have hAJ : A ≤ thompsonJ T := GammaExtra.le_thompsonJ hA
  have hcomm : ∀ a ∈ A, ∀ z ∈ ch6ZS T L V, a * z = z * a := fun a ha z hz =>
    (Subgroup.mem_centralizer_iff.mp (hJS (hAJ ha)).2 z hz).symm
  have hZe : IsElemAbelian 2 (ch6ZS T L V) :=
    B2F.isElemAbelian_mono h.ZS_le h.toHyp611.isElemAbelian
  have hAZ : IsElemAbelian 2 (A ⊔ ch6ZS T L V) :=
    B2F.isElemAbelian_sup_of_commute hA.2.1 hZe hcomm
  have hAZT : A ⊔ ch6ZS T L V ≤ T := sup_le hA.1 (h.ZS_le.trans h.toHyp611.le_T)
  have heq : A = A ⊔ ch6ZS T L V := Subgroup.eq_of_le_of_card_ge le_sup_left (hA.2.2 _ hAZT hAZ)
  intro z hz
  have hzA : z ∈ A := by
    rw [heq]
    exact Subgroup.mem_sup_right hz
  refine Subgroup.subset_closure ⟨⟨hAJ hzA, Subgroup.mem_centralizer_iff.mpr ?_⟩,
    h.toHyp611.isElemAbelian.2 z (h.ZS_le hz)⟩
  intro y hy
  exact (Subgroup.mem_centralizer_iff.mp (hJS hy).2 z hz).symm

theorem baum_eq (h : Hyp611Nat G T M L V n) : baum T = baum (ch6S T L V) := by
  have hJ := h.thompsonJ_eq
  unfold baum
  rw [← hJ]
  apply le_antisymm
  · intro x hx
    refine ⟨⟨hx.1, ?_⟩, hx.2⟩
    exact Subgroup.centralizer_le h.ZS_le_omegaOneCenter_thompsonJ hx.2
  · exact inf_le_inf_right _ inf_le_left

end Hyp611Nat

end CFSG.Quasithin.H13
