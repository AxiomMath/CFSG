module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Inspection15418IndexTwo
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.ConfinedInvolution

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def InvolutionCentralizerPSL2 : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (K : Type) [Field K] [Finite K], Nat.card K = p ^ 2 →
    ∀ x : CFSG.GorensteinWalter.PSL2 K, x ^ 2 = 1 → x ≠ 1 →
      oddCoreIn (Subgroup.centralizer ({x} : Set (CFSG.GorensteinWalter.PSL2 K))) ≠ ⊥

namespace Insp15418

section OddNormal

variable {X : Type*} [Group X]

@[expose] def HasOddNormal (H : Subgroup X) : Prop :=
  ∃ Y : Subgroup X, Y ≤ H ∧ H ≤ Subgroup.normalizer (Y : Set X) ∧ Odd (Nat.card Y) ∧ Y ≠ ⊥

theorem oddCoreIn_ne_bot_of_hasOddNormal [Finite X] {H : Subgroup X} (h : HasOddNormal H) :
    oddCoreIn H ≠ ⊥ := by
  obtain ⟨Y, hYH, hN, hodd, hne⟩ := h
  have hn : (Y.subgroupOf H).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hYH).mpr hN
  have hc : Odd (Nat.card ↥(Y.subgroupOf H)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYH).toEquiv]
  have hle : Y.subgroupOf H ≤ fusionOddCore ↥H := le_sSup ⟨hn, hc⟩
  have hY : Y ≤ oddCoreIn H := by
    have := Subgroup.map_mono (f := H.subtype) hle
    rwa [Subgroup.map_subgroupOf_eq_of_le hYH] at this
  intro hbot
  exact hne (le_bot_iff.mp (hbot ▸ hY))

theorem hasOddNormal_of_oddCoreIn_ne_bot [Finite X] {H : Subgroup X} (h : oddCoreIn H ≠ ⊥) :
    HasOddNormal H :=
  ⟨oddCoreIn H, oddCoreIn_le H, le_normalizer_oddCoreIn H, odd_card_oddCoreIn H, h⟩

theorem HasOddNormal.of_map_equiv {X' : Type*} [Group X'] (e : X ≃* X') {H : Subgroup X}
    (h : HasOddNormal (H.map e.toMonoidHom)) : HasOddNormal H := by
  obtain ⟨Y, hYH, hN, hodd, hne⟩ := h
  refine ⟨Y.map e.symm.toMonoidHom, fun y hy => ?_, fun g hg => ?_, ?_, ?_⟩
  · rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm] at hy
    have := hYH hy
    rw [Subgroup.mem_map_equiv] at this
    simpa using this
  · have hg' : e g ∈ Subgroup.normalizer (Y : Set X') := hN ⟨g, hg, rfl⟩
    rw [Subgroup.mem_normalizer_iff] at hg' ⊢
    intro z
    rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv]
    simpa using hg' (e z)
  · rwa [Subgroup.card_map_of_injective e.symm.injective]
  · intro h
    apply hne
    rw [eq_bot_iff] at h ⊢
    intro y hy
    have : e.symm y ∈ Y.map e.symm.toMonoidHom := ⟨y, hy, rfl⟩
    have h1 := h this
    rw [Subgroup.mem_bot] at h1 ⊢
    simpa using congrArg e h1

theorem HasOddNormal.map_subtype {M : Subgroup X} {H : Subgroup ↥M} (h : HasOddNormal H) :
    HasOddNormal (H.map M.subtype) := by
  obtain ⟨Y, hYH, hN, hodd, hne⟩ := h
  refine ⟨Y.map M.subtype, Subgroup.map_mono hYH, ?_, ?_, ?_⟩
  · rintro _ ⟨g, hg, rfl⟩
    have hg' := hN hg
    rw [Subgroup.mem_normalizer_iff] at hg' ⊢
    intro z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨g * y * g⁻¹, (hg' y).mp hy, by simp⟩
    · rintro ⟨y, hy, hyz⟩
      simp only [Subgroup.coe_subtype] at hyz
      have hzM : z ∈ M := by
        have : z = (g : X)⁻¹ * (y : X) * g := by rw [hyz]; group
        rw [this]
        exact M.mul_mem (M.mul_mem (M.inv_mem g.2) y.2) g.2
      refine ⟨⟨z, hzM⟩, (hg' _).mpr ?_, rfl⟩
      have : g * ⟨z, hzM⟩ * g⁻¹ = y := Subtype.ext (by simpa using hyz.symm)
      rw [this]
      exact hy
  · rwa [Subgroup.card_map_of_injective M.subtype_injective]
  · intro h
    apply hne
    exact (Subgroup.map_eq_bot_iff_of_injective _ M.subtype_injective).mp h

theorem map_centralizer_singleton {X' : Type*} [Group X'] (e : X ≃* X') (x : X) :
    (Subgroup.centralizer ({x} : Set X)).map e.toMonoidHom =
      Subgroup.centralizer ({e x} : Set X') := by
  ext y
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have := congrArg e h
    simpa using this
  · intro h
    apply e.injective
    simpa using h

theorem inf_centralizer_eq_map (M : Subgroup X) (x : ↥M) :
    M ⊓ Subgroup.centralizer ({(x : X)} : Set X) =
      (Subgroup.centralizer ({x} : Set ↥M)).map M.subtype := by
  ext y
  constructor
  · rintro ⟨hyM, hy⟩
    refine ⟨⟨y, hyM⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_, rfl⟩
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hy)
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hy))⟩

end OddNormal

theorem cycleType_of_involution {σ : Equiv.Perm (Fin 7)} (hA : σ ∈ alternatingGroup (Fin 7))
    (h2 : σ ^ 2 = 1) (h1 : σ ≠ 1) : σ.cycleType = Multiset.replicate 2 2 := by
  have hall : ∀ n ∈ σ.cycleType, n = 2 := by
    intro n hn
    have hd := Equiv.Perm.dvd_of_mem_cycleType hn
    have ho : orderOf σ ∣ 2 := orderOf_dvd_of_pow_eq_one h2
    have h2le := Equiv.Perm.two_le_of_mem_cycleType hn
    have := Nat.le_of_dvd (by norm_num) (hd.trans ho)
    omega
  have hrep : σ.cycleType = Multiset.replicate (Multiset.card σ.cycleType) 2 :=
    Multiset.eq_replicate.mpr ⟨rfl, hall⟩
  set k := Multiset.card σ.cycleType with hk
  have hsum : σ.cycleType.sum = 2 * k := by
    rw [hrep, Multiset.sum_replicate, smul_eq_mul, mul_comm]
  have hle : σ.cycleType.sum ≤ 7 := by
    have := Equiv.Perm.sum_cycleType_le σ
    simpa using this
  have hk0 : k ≠ 0 := by
    intro h0
    apply h1
    rw [← Equiv.Perm.cycleType_eq_zero, hrep, h0, Multiset.replicate_zero]
  have hsign : Equiv.Perm.sign σ = 1 := (Equiv.Perm.mem_alternatingGroup).mp hA
  rw [Equiv.Perm.sign_of_cycleType, hsum, ← hk] at hsign
  have hk3 : k ≤ 3 := by omega
  have hk2 : k = 2 := by
    interval_cases k
    · omega
    · exfalso
      revert hsign
      decide
    · rfl
    · exfalso
      revert hsign
      decide
  rw [hrep, hk2]

@[expose] def s7x : Equiv.Perm (Fin 7) := Equiv.swap 0 1 * Equiv.swap 2 3

@[expose] def s7y : Equiv.Perm (Fin 7) := Equiv.swap 4 5 * Equiv.swap 5 6

theorem s7_facts : s7x ∈ alternatingGroup (Fin 7) ∧ s7x ^ 2 = 1 ∧ s7x ≠ 1 ∧
    s7y ∈ alternatingGroup (Fin 7) ∧ s7y ^ 3 = 1 ∧ s7y ≠ 1 ∧ s7y * s7x = s7x * s7y := by
  simp only [Equiv.Perm.mem_alternatingGroup]
  decide

theorem s7_fix : ∀ a : Fin 7, s7x a = a ↔ (a = 4 ∨ a = 5 ∨ a = 6) := by decide

theorem s7_y_fix : ∀ a : Fin 7, ¬ (a = 4 ∨ a = 5 ∨ a = 6) → s7y a = a := by decide

theorem s7_key : ∀ u v w : Fin 7, (u = 4 ∨ u = 5 ∨ u = 6) → (v = 4 ∨ v = 5 ∨ v = 6) →
    (w = 4 ∨ w = 5 ∨ w = 6) → u ≠ v → v ≠ w → u ≠ w →
    ((v = s7y u ∧ w = s7y v ∧ u = s7y w) ∨ (v = s7y⁻¹ u ∧ w = s7y⁻¹ v ∧ u = s7y⁻¹ w)) ∧
    ∀ t : Fin 7, (t = 4 ∨ t = 5 ∨ t = 6) → t = u ∨ t = v ∨ t = w := by
  decide

theorem s7_y_vals : s7y 4 = 5 ∧ s7y 5 = 6 ∧ s7y 6 = 4 ∧ s7y⁻¹ 4 = 6 ∧ s7y⁻¹ 5 = 4 ∧
    s7y⁻¹ 6 = 5 := by decide

theorem s7_conj_y (h : Equiv.Perm (Fin 7)) (hh : h * s7x = s7x * h) :
    h * s7y * h⁻¹ = s7y ∨ h * s7y * h⁻¹ = s7y⁻¹ := by
  have hF : ∀ b : Fin 7, (b = 4 ∨ b = 5 ∨ b = 6) → (h b = 4 ∨ h b = 5 ∨ h b = 6) := by
    intro b hb
    have hx : s7x b = b := (s7_fix b).mpr hb
    have := congrArg (fun f : Equiv.Perm (Fin 7) => f b) hh
    simp only [Equiv.Perm.mul_apply, hx] at this
    exact (s7_fix (h b)).mp this.symm
  have h4 := hF 4 (by simp)
  have h5 := hF 5 (by simp)
  have h6 := hF 6 (by simp)
  have hne : ∀ a b : Fin 7, a ≠ b → h a ≠ h b := fun a b hab => h.injective.ne hab
  obtain ⟨hcase, hall⟩ := s7_key (h 4) (h 5) (h 6) h4 h5 h6 (hne 4 5 (by decide))
    (hne 5 6 (by decide)) (hne 4 6 (by decide))
  have hout : ∀ b : Fin 7, ¬ (b = 4 ∨ b = 5 ∨ b = 6) → ¬ (h b = 4 ∨ h b = 5 ∨ h b = 6) := by
    intro b hb hhb
    rcases hall (h b) hhb with e | e | e
    · exact hb (Or.inl (h.injective e))
    · exact hb (Or.inr (Or.inl (h.injective e)))
    · exact hb (Or.inr (Or.inr (h.injective e)))
  obtain ⟨y4, y5, y6, -, -, -⟩ := s7_y_vals
  have hinv : ∀ b, h⁻¹ (h b) = b := fun b => h.symm_apply_apply b
  rcases hcase with ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩
  · left
    ext a
    obtain ⟨b, rfl⟩ := h.surjective a
    simp only [Equiv.Perm.mul_apply, hinv]
    by_cases hb : b = 4 ∨ b = 5 ∨ b = 6
    · rcases hb with rfl | rfl | rfl
      · rw [y4, e1]
      · rw [y5, e2]
      · rw [y6, e3]
    · rw [s7_y_fix b hb, s7_y_fix (h b) (hout b hb)]
  · right
    ext a
    obtain ⟨b, rfl⟩ := h.surjective a
    simp only [Equiv.Perm.mul_apply, hinv]
    by_cases hb : b = 4 ∨ b = 5 ∨ b = 6
    · rcases hb with rfl | rfl | rfl
      · rw [y4, e1]
      · rw [y5, e2]
      · rw [y6, e3]
    · rw [s7_y_fix b hb]
      have : s7y⁻¹ (h b) = h b := by
        rw [Equiv.Perm.inv_eq_iff_eq]
        exact (s7_y_fix (h b) (hout b hb)).symm
      rw [this]

theorem hasOddNormal_alternating_seven {σ : Equiv.Perm (Fin 7)}
    (hA : σ ∈ alternatingGroup (Fin 7)) (h2 : σ ^ 2 = 1) (h1 : σ ≠ 1) :
    HasOddNormal (alternatingGroup (Fin 7) ⊓
      Subgroup.centralizer ({σ} : Set (Equiv.Perm (Fin 7)))) := by
  obtain ⟨hxA, hx2, hx1, hyA, hy3, hy1, hyx⟩ := s7_facts
  have hct : s7x.cycleType = σ.cycleType := by
    rw [cycleType_of_involution hxA hx2 hx1, cycleType_of_involution hA h2 h1]
  obtain ⟨g, hg⟩ := isConj_iff.mp (Equiv.Perm.isConj_iff_cycleType_eq.mpr hct)
  set y := g * s7y * g⁻¹ with hy
  have hyA' : y ∈ alternatingGroup (Fin 7) :=
    (inferInstance : (alternatingGroup (Fin 7)).Normal).conj_mem s7y hyA g
  have hyσ : y * σ = σ * y := by
    rw [hy, ← hg]
    calc g * s7y * g⁻¹ * (g * s7x * g⁻¹) = g * (s7y * s7x) * g⁻¹ := by group
      _ = g * (s7x * s7y) * g⁻¹ := by rw [hyx]
      _ = g * s7x * g⁻¹ * (g * s7y * g⁻¹) := by group
  refine ⟨Subgroup.zpowers y, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.zpowers_le]
    exact ⟨hyA', Subgroup.mem_centralizer_singleton_iff.mpr hyσ⟩
  · refine le_normalizer_of_forall fun h hh z hz => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hhσ : h * σ = σ * h := Subgroup.mem_centralizer_singleton_iff.mp hh.2
    have hh' : (g⁻¹ * h * g) * s7x = s7x * (g⁻¹ * h * g) := by
      have e1 : s7x = g⁻¹ * σ * g := by rw [← hg]; group
      rw [e1]
      calc g⁻¹ * h * g * (g⁻¹ * σ * g) = g⁻¹ * (h * σ) * g := by group
        _ = g⁻¹ * (σ * h) * g := by rw [hhσ]
        _ = g⁻¹ * σ * g * (g⁻¹ * h * g) := by group
    have hconj : h * y * h⁻¹ = g * ((g⁻¹ * h * g) * s7y * (g⁻¹ * h * g)⁻¹) * g⁻¹ := by
      rw [hy]; group
    have hmem : h * y * h⁻¹ ∈ Subgroup.zpowers y := by
      rw [hconj]
      rcases s7_conj_y _ hh' with e | e
      · rw [e]
        exact Subgroup.mem_zpowers y
      · rw [e]
        have : g * s7y⁻¹ * g⁻¹ = y⁻¹ := by rw [hy]; group
        rw [this]
        exact (Subgroup.zpowers y).inv_mem (Subgroup.mem_zpowers y)
    have : h * y ^ k * h⁻¹ = (h * y * h⁻¹) ^ k := by
      rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply]
    rw [this]
    exact (Subgroup.zpowers y).zpow_mem hmem k
  · rw [Nat.card_zpowers]
    have hy3' : y ^ 3 = 1 := by rw [hy, ← MulAut.conj_apply, ← map_pow, hy3, map_one]
    have hy1' : y ≠ 1 := by
      intro h
      apply hy1
      have : s7y = g⁻¹ * y * g := by rw [hy]; group
      rw [this, h]
      group
    rw [orderOf_eq_prime hy3' hy1']
    decide
  · intro h
    have : y ∈ Subgroup.zpowers y := Subgroup.mem_zpowers y
    rw [h, Subgroup.mem_bot] at this
    apply hy1
    have e : s7y = g⁻¹ * y * g := by rw [hy]; group
    rw [e, this]
    group

theorem involution_perm_seven {D : Type} [Group D] [Finite D] (e : D ≃* Equiv.Perm (Fin 7))
    {M : Subgroup D} (hM : CFSG.IsComponent M) {x : D} (hxM : x ∈ M) (hx2 : x ^ 2 = 1)
    (hx1 : x ≠ 1) : oddCoreIn (M ⊓ Subgroup.centralizer ({x} : Set D)) ≠ ⊥ := by
  refine oddCoreIn_ne_bot_of_hasOddNormal (HasOddNormal.of_map_equiv e ?_)
  have hMe : M.map e.toMonoidHom = alternatingGroup (Fin 7) :=
    eq_alternating_of_isComponent (CFSG.LocalCores.isComponent_map_mulEquiv e hM)
  rw [Subgroup.map_inf_eq _ _ _ e.injective, hMe, map_centralizer_singleton]
  have hxA : e x ∈ alternatingGroup (Fin 7) := hMe ▸ ⟨x, hxM, rfl⟩
  refine hasOddNormal_alternating_seven hxA (by rw [← map_pow, hx2, map_one]) ?_
  rw [Ne, map_eq_one_iff e e.injective]
  exact hx1

theorem involution_hatSym_seven {D : Type} [Group D] [Finite D] (h : F6.IsHatSym 7 D)
    {M : Subgroup D} (hM : CFSG.IsComponent M) {x : D} (hxM : x ∈ M) :
    oddCoreIn (M ⊓ Subgroup.centralizer ({x} : Set D)) ≠ ⊥ := by
  obtain ⟨φ, -, -, hhat⟩ := h
  have hker : (Equiv.Perm.sign.comp φ).ker = (alternatingGroup (Fin 7)).comap φ := by
    rw [← MonoidHom.comap_ker]
    rfl
  have hq : CFSG.IsQuasisimple ↥(Equiv.Perm.sign.comp φ).ker := by
    rw [hker]
    exact isQuasisimple_of_open hhat.1
  have hMN : M = (alternatingGroup (Fin 7)).comap φ := by
    rw [eq_of_isComponent_of_ker units_int_comm _ hq hM, hker]
  set N := (alternatingGroup (Fin 7)).comap φ with hN
  refine oddCoreIn_ne_bot_of_hasOddNormal ⟨(Subgroup.center ↥N).map N.subtype, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨c, hc, rfl⟩
    refine ⟨hMN ▸ c.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have hxN : x ∈ N := hMN ▸ hxM
    have := Subgroup.mem_center_iff.mp hc ⟨x, hxN⟩
    exact (congrArg Subtype.val this).symm
  · rintro m ⟨hmM, -⟩
    have hmN : m ∈ N := hMN ▸ hmM
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · rintro ⟨c, hc, rfl⟩
      have hcm := Subgroup.mem_center_iff.mp hc ⟨m, hmN⟩
      have h1 : (m : D) * c * m⁻¹ = c := by
        have h := congrArg Subtype.val hcm
        simp only [Subgroup.coe_mul] at h
        rw [h]
        group
      refine ⟨c, hc, ?_⟩
      simp [h1]
    · rintro ⟨c, hc, hcz⟩
      have hcm := Subgroup.mem_center_iff.mp hc ⟨m, hmN⟩
      have h1 : (m : D) * c * m⁻¹ = c := by
        have h := congrArg Subtype.val hcm
        simp only [Subgroup.coe_mul] at h
        rw [h]
        group
      simp only [Subgroup.coe_subtype] at hcz
      have h2 : m * z * m⁻¹ = m * c * m⁻¹ := by rw [← hcz, h1]
      exact ⟨c, hc, (mul_left_cancel (mul_right_cancel h2)).symm⟩
  · rw [Subgroup.card_map_of_injective N.subtype_injective, hhat.2.1]
    decide
  · intro hbot
    have h3 := hhat.2.1
    rw [(Subgroup.map_eq_bot_iff_of_injective _ N.subtype_injective).mp hbot,
      Subgroup.card_bot] at h3
    omega

open CFSG.GorensteinWalter in
theorem involution_l2FieldExt (hPSL : InvolutionCentralizerPSL2) {p : ℕ} (hp : p.Prime)
    (h5 : 5 ≤ p) (K : Type) [Field K] [Finite K] (hK : Nat.card K = p ^ 2) {D : Type} [Group D]
    [Finite D] (e : D ≃* ↥(F6.PSigmaL2 K)) {M : Subgroup D} (hM : CFSG.IsComponent M) {x : D}
    (hxM : x ∈ M) (hx2 : x ^ 2 = 1) (hx1 : x ≠ 1) :
    oddCoreIn (M ⊓ Subgroup.centralizer ({x} : Set D)) ≠ ⊥ := by
  have : Finite ↥(F6.PSigmaL2 K) := Finite.of_equiv D e.toEquiv
  refine oddCoreIn_ne_bot_of_hasOddNormal (HasOddNormal.of_map_equiv e ?_)
  set L := (pGammaL2PSLRange K).subgroupOf (F6.PSigmaL2 K) with hL
  have hMe : M.map e.toMonoidHom = L :=
    eq_psl_of_isComponent hp K hK (CFSG.LocalCores.isComponent_map_mulEquiv e hM)
  have hxL : e x ∈ L := hMe ▸ ⟨x, hxM, rfl⟩
  rw [Subgroup.map_inf_eq _ _ _ e.injective, hMe, map_centralizer_singleton]
  set x₁ : ↥L := ⟨e x, hxL⟩ with hx₁
  have hx₁' : ((x₁ : ↥(F6.PSigmaL2 K))) = e x := rfl
  rw [← hx₁', inf_centralizer_eq_map L x₁]
  refine HasOddNormal.map_subtype (HasOddNormal.of_map_equiv (pslEquivPSigma K).symm ?_)
  rw [map_centralizer_singleton]
  refine hasOddNormal_of_oddCoreIn_ne_bot (hPSL p hp h5 K hK _ ?_ ?_)
  · rw [← map_pow]
    have : x₁ ^ 2 = 1 := Subtype.ext (by
      change e x ^ 2 = 1
      rw [← map_pow, hx2, map_one])
    rw [this, map_one]
  · rw [Ne, map_eq_one_iff _ (pslEquivPSigma K).symm.injective]
    intro h
    apply hx1
    have : e x = 1 := congrArg Subtype.val h
    exact (map_eq_one_iff e e.injective).mp this

end Insp15418

open Insp15418

theorem involutionCentralizer15418_of (hPSL : InvolutionCentralizerPSL2) :
    InvolutionCentralizer15418 := by
  intro D _ _ hD M hM x hxM hx2 hx1
  rcases hD with he | h | ⟨p, h5, hp, K, _, _, hK, he⟩
  · obtain ⟨e⟩ := he
    exact involution_perm_seven e hM hxM hx2 hx1
  · exact involution_hatSym_seven h hM hxM
  · obtain ⟨e⟩ := he
    exact involution_l2FieldExt hPSL hp h5 K hK e hM hxM hx2 hx1

end CFSG.Quasithin.EmptyFaithfulMultiple
