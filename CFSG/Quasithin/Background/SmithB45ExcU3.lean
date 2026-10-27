module

public import CFSG.Quasithin.Background.SmithB45ExcBlocks
public import CFSG.Quasithin.Background.SmithB45ExcL2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyU3Top

public section

namespace CFSG.Quasithin.B45Exc

section Swap

open Module CFSG.QuasithinUnique.Setup.Family

variable {K : Type*} [Field K] [Fintype K] {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  {ρ : K × K → (E ≃ₗ[ZMod 2] E)} (h : IsVAct ρ) (hodd : Odd (Fintype.card K))

include h hodd

theorem ord_mul_card_le_finrank_range_sub1_swap [Module.Finite (ZMod 2) E] {p : ℕ} [Fact p.Prime]
    (hpK : Fintype.card K = p)
    (hK : ∀ k : K, ∃ n : ℕ, (n : K) = k) {s : E ≃ₗ[ZMod 2] E} (hs : s * s = 1)
    {τ : K × K → K × K} (hτ2 : ∀ x, τ (τ x) = x)
    (hτk : ∀ (k : K) (x : K × K), τ (k • x) = k • τ x)
    (hsρ : ∀ x, s * ρ x * s = ρ (τ x)) (U : Finset (K × K))
    (hself : ∀ u ∈ U, det2 u (τ u) ≠ 0)
    (hpair : ∀ u ∈ U, ∀ v ∈ U, u ≠ v → det2 u v ≠ 0 ∧ det2 u (τ v) ≠ 0 ∧
      det2 (τ u) v ≠ 0 ∧ det2 (τ u) (τ v) ≠ 0)
    (hne : ∀ u ∈ U, lineProj ρ u ≠ 0) :
    orderOf (2 : ZMod p) * U.card ≤ finrank (ZMod 2) (LinearMap.range (sub1 s)) := by
  classical
  set π : K × K → Module.End (ZMod 2) E := fun u => lineProj ρ u + lineProj ρ (τ u) with hπdef
  have hs' : (s : Module.End (ZMod 2) E) * (s : Module.End (ZMod 2) E) = 1 :=
    congrArg (fun f : E ≃ₗ[ZMod 2] E => (f : E →ₗ[ZMod 2] E)) hs
  have hsw : ∀ u, (s : Module.End (ZMod 2) E) * lineProj ρ u =
      lineProj ρ (τ u) * (s : Module.End (ZMod 2) E) := by
    intro u
    calc (s : Module.End (ZMod 2) E) * lineProj ρ u
        = (s : Module.End (ZMod 2) E) * lineProj ρ u * ((s : Module.End (ZMod 2) E) *
            (s : Module.End (ZMod 2) E)) := by rw [hs', mul_one]
      _ = ((s : Module.End (ZMod 2) E) * lineProj ρ u * (s : Module.End (ZMod 2) E)) *
            (s : Module.End (ZMod 2) E) := by simp only [mul_assoc]
      _ = lineProj ρ (τ u) * (s : Module.End (ZMod 2) E) := by
          rw [lineProj_swap hs hτ2 hτk hsρ u]
  have hπ : ∀ u ∈ U, π u * π u = π u := by
    intro u hu
    have h1 := lineProj_mul_self h hodd u
    have h2 := lineProj_mul_self h hodd (τ u)
    have h3 := lineProj_mul_of_indep h hodd (hself u hu)
    have h4 := lineProj_mul_of_indep h hodd (show det2 (τ u) u ≠ 0 by
      rw [det2_swap]; exact neg_ne_zero.2 (hself u hu))
    simp only [hπdef, add_mul, mul_add, h1, h2, h3, h4]
    simp
  have horth : ∀ u ∈ U, ∀ v ∈ U, u ≠ v → π u * π v = 0 := by
    intro u hu v hv huv
    obtain ⟨d1, d2, d3, d4⟩ := hpair u hu v hv huv
    simp only [hπdef, add_mul, mul_add,
      lineProj_mul_of_indep h hodd d1, lineProj_mul_of_indep h hodd d2,
      lineProj_mul_of_indep h hodd d3, lineProj_mul_of_indep h hodd d4]
    simp
  have hcomm : ∀ u ∈ U, (s : Module.End (ZMod 2) E) * π u = π u * (s : Module.End (ZMod 2) E) := by
    intro u hu
    simp only [hπdef, mul_add, add_mul, hsw u, hsw (τ u), hτ2 u]
    abel
  have hc : ∀ u ∈ U, orderOf (2 : ZMod p) ≤
      finrank (ZMod 2) ((LinearMap.range (π u)).map (sub1 s)) := by
    intro u hu
    have hu0 : u ≠ 0 := by
      rintro rfl
      exact hself 0 hu (by simp [det2])
    obtain ⟨w, hw⟩ := exists_det_ne u hu0
    set X := LinearMap.range (lineProj ρ u) with hX
    have hX2 : orderOf (2 : ZMod p) ≤ finrank (ZMod 2) X := by
      have hXne : X ≠ ⊥ := fun h0 => hne u hu (LinearMap.range_eq_bot.1 h0)
      have hXpos : 1 ≤ finrank (ZMod 2) X := Submodule.one_le_finrank_iff.2 hXne
      have hvp : (ρ w) ^ p = 1 := by
        rw [← map_nsmul_eq_pow h, ← hpK]
        have : (Fintype.card K) • w = 0 := by
          rw [← Nat.cast_smul_eq_nsmul K, FiniteField.cast_card_eq_zero, zero_smul]
        rw [this, h.map_zero]
      have hvX : ∀ x ∈ X, (ρ w) x ∈ X := by
        rintro _ ⟨y, rfl⟩
        refine ⟨ρ w y, ?_⟩
        have := LinearMap.congr_fun (opE_mul_lineProj_comm h w u) y
        simpa [Module.End.mul_apply, opE] using this.symm
      have hfpf : ∀ x ∈ X, (ρ w) x = x → x = 0 := fun x hx hwx =>
        fpf_of_mem_range h hodd hw hK hx hwx
      exact Nat.le_of_dvd (by omega) (orderOf_two_dvd_finrank_of_fpf hvp X hvX hfpf)
    have hXle : X ≤ LinearMap.range (π u) := by
      rintro _ ⟨y, rfl⟩
      refine ⟨lineProj ρ u y, ?_⟩
      have h1 := lineProj_mul_self h hodd u
      have h4 := lineProj_mul_of_indep h hodd (show det2 (τ u) u ≠ 0 by
        rw [det2_swap]; exact neg_ne_zero.2 (hself u hu))
      simp only [hπdef, LinearMap.add_apply]
      have e1 : lineProj ρ u (lineProj ρ u y) = lineProj ρ u y := by
        rw [← Module.End.mul_apply, h1]
      have e2 : lineProj ρ (τ u) (lineProj ρ u y) = 0 := by
        rw [← Module.End.mul_apply, h4]; rfl
      rw [e1, e2, add_zero]
    have hinj : Function.Injective ((sub1 s).domRestrict X) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      rintro ⟨x, hxX⟩ hx0
      obtain ⟨y, rfl⟩ := hxX
      have hsx : s (lineProj ρ u y) = lineProj ρ u y := by
        have := hx0
        simp only [LinearMap.domRestrict_apply, sub1_apply'] at this
        exact e_eq_of_add_eq_zero this
      have h4 := lineProj_mul_of_indep h hodd (show det2 (τ u) u ≠ 0 by
        rw [det2_swap]; exact neg_ne_zero.2 (hself u hu))
      have h1 := lineProj_mul_self h hodd u
      have hxa : lineProj ρ (τ u) (lineProj ρ u y) = 0 := by
        rw [← Module.End.mul_apply, h4]; rfl
      have hxa' : lineProj ρ (τ u) (lineProj ρ u y) = lineProj ρ u y := by
        have := lineProj_swap hs hτ2 hτk hsρ u
        have h5 := LinearMap.congr_fun this (lineProj ρ u y)
        simp only [Module.End.mul_apply, LinearEquiv.coe_coe] at h5
        have e1 : lineProj ρ u (s (lineProj ρ u y)) = lineProj ρ u y := by
          rw [hsx]
          rw [← Module.End.mul_apply, h1]
        rw [e1, hsx] at h5
        exact h5.symm
      apply Subtype.ext
      show lineProj ρ u y = 0
      rw [← hxa', hxa]
    have hrk : finrank (ZMod 2) (LinearMap.range ((sub1 s).domRestrict X)) =
        finrank (ZMod 2) X := LinearMap.finrank_range_of_inj hinj
    rw [LinearMap.range_domRestrict] at hrk
    have hmono := Submodule.finrank_mono (Submodule.map_mono (f := sub1 s) hXle)
    omega
  have := sum_le_finrank_range_sub1 s U π hπ horth hcomm (fun _ => orderOf (2 : ZMod p)) hc
  simpa [Finset.sum_const, mul_comm] using this


end Swap

theorem orderOf_two_zmod_5 : orderOf (2 : ZMod 5) = 4 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm0 => ?_⟩
  interval_cases m <;> decide

theorem seven_le_ord_mul {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p) :
    7 ≤ orderOf (2 : ZMod p) * ((p - 1) / 2) := by
  rcases eq_or_lt_of_le hp5 with h5 | h5
  · subst h5
    rw [orderOf_two_zmod_5]
    norm_num
  · have h3 := three_le_orderOf_two (p := p) hp5
    have h6 : p ≠ 6 := by
      rintro rfl
      exact absurd hp.out (by norm_num)
    have h7 : 3 ≤ (p - 1) / 2 := by omega
    calc 7 ≤ 3 * 3 := by norm_num
      _ ≤ orderOf (2 : ZMod p) * ((p - 1) / 2) := Nat.mul_le_mul h3 h7

section Rank

open Matrix Module CFSG.LieType.Universal.Unitary CFSG.QuasithinUnique.Setup.Family

variable {K : Type} [Field K] {σ : K ≃+* K}

theorem negT_rank2 {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    [Module.Finite (ZMod 2) E] {p : ℕ} [Fact p.Prime] [CharP K p] (hp5 : 5 ≤ p)
    {F : Type} [Field F] [Fintype F] [CharP F p] (hFcard : Fintype.card F = p)
    (hFK : ∀ k : F, ∃ n : ℕ, (n : F) = k) (ι : F →+* K) (hι : ∀ x : F, σ (ι x) = ι x)
    (hσ : ∀ x, σ (σ x) = x) {ω : K} (hω : σ ω = -ω) (hω0 : ω ≠ 0)
    (ρ : SU σ 3 →* (E ≃ₗ[ZMod 2] E))
    (hρ : ∀ g : SU σ 3, ρ g = 1 →
      ∃ r : Kˣ, (g : GL (Fin 3) K) = GeneralLinearGroup.scalar (Fin 3) r) :
    orderOf (2 : ZMod p) * ((p - 1) / 2) ≤
      finrank (ZMod 2) (LinearMap.range (sub1 (ρ (negT σ)))) := by
  classical
  have hp := (Fact.out : p.Prime)
  have hp2 : p ≠ 2 := by omega
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K p]; exact hp2)
  let vS : F → F → SU σ 3 := fun x y => ⟨vH σ ι ω x y, vH_mem h2 hσ hι hω x y⟩
  have hvS_mul : ∀ x y x' y', vS x y * vS x' y' = vS (x + x') (y + y') := fun x y x' y' =>
    Subtype.ext (vH_mul h2 hι x y x' y')
  have hvS_zero : vS 0 0 = 1 := Subtype.ext vH_zero
  let ρ' : F × F → (E ≃ₗ[ZMod 2] E) := fun z => ρ (vS z.1 z.2)
  have hV : IsVAct ρ' :=
    ⟨by simp [ρ', hvS_zero], fun a b => by
      show ρ (vS (a.1 + b.1) (a.2 + b.2)) = ρ (vS a.1 a.2) * ρ (vS b.1 b.2)
      rw [← map_mul, hvS_mul]⟩
  have hodd : Odd (Fintype.card F) := by rw [hFcard]; exact hpodd
  have hfaith : ∀ z, ρ' z = 1 → z = 0 := by
    intro z hz
    obtain ⟨r, hr⟩ := hρ _ hz
    obtain ⟨hx, hy⟩ := vH_not_scalar hω0 hr
    exact Prod.ext hx hy
  let τ : F × F → F × F := fun z => (-z.1, z.2)
  have hτ2 : ∀ z, τ (τ z) = z := fun z => by simp [τ]
  have hτk : ∀ (k : F) (z : F × F), τ (k • z) = k • τ z := by
    intro k z
    simp [τ, Prod.smul_mk]
  have hs : ρ (negT σ) * ρ (negT σ) = 1 := by rw [← map_mul, negT_mul_self, map_one]
  have hsρ : ∀ z, ρ (negT σ) * ρ' z * ρ (negT σ) = ρ' (τ z) := by
    intro z
    have h1 : negT σ * vS z.1 z.2 = vS (-z.1) z.2 * negT σ := Subtype.ext (negT_mul_vH z.1 z.2)
    calc ρ (negT σ) * ρ' z * ρ (negT σ) = ρ (negT σ * vS z.1 z.2 * negT σ) := by
          simp only [ρ', map_mul]
      _ = ρ (vS (-z.1) z.2 * (negT σ * negT σ)) := by rw [h1, mul_assoc]
      _ = ρ' (τ z) := by rw [negT_mul_self, mul_one]
  have htrans : ∀ u : F × F, u.1 ≠ 0 → ∃ (γ : F × F → F × F)
      (g : E ≃ₗ[ZMod 2] E), Function.Bijective γ ∧
      (∀ (k : F) (x : F × F), γ (k • x) = k • γ x) ∧ γ (1, 0) = u ∧
        ∀ x, g * ρ' x * g⁻¹ = ρ' (γ x) := by
    intro u hu
    obtain ⟨u1, u2⟩ := u
    simp only at hu
    have hdK : ι u1 ≠ 0 := fun h0 => hu (ι.injective (by rw [map_zero]; exact h0))
    let tS : SU σ 3 := ⟨torGL hdK, torGL_mem_SU σ hdK (hι u1)⟩
    let sS : SU σ 3 := ⟨shearGL σ ι ω (u2 / u1), shearGL_mem h2 hσ hι hω (u2 / u1)⟩
    refine ⟨fun z => (u1 * z.1, u1 ^ 2 * z.2 + (u2 / u1) * (u1 * z.1)), ρ sS * ρ tS, ?_, ?_, ?_,
      ?_⟩
    · rw [Function.bijective_iff_has_inverse]
      refine ⟨fun w => (w.1 / u1, (w.2 - (u2 / u1) * w.1) / u1 ^ 2), fun z => ?_, fun w => ?_⟩
      · refine Prod.ext ?_ ?_
        · simp only; field_simp
        · simp only; field_simp; ring
      · refine Prod.ext ?_ ?_
        · simp only; field_simp
        · simp only; field_simp; ring
    · rintro k ⟨a, b⟩
      simp only [Prod.smul_mk, smul_eq_mul]
      refine Prod.ext ?_ ?_ <;> simp only <;> ring
    · refine Prod.ext (by simp) ?_
      simp only [mul_zero, zero_add, mul_one]
      field_simp
    · intro x
      have h1 : tS * vS x.1 x.2 = vS (u1 * x.1) (u1 ^ 2 * x.2) * tS :=
        Subtype.ext (torGL_mul_vH hdK (hι u1) x.1 x.2 (u1 * x.1) (u1 ^ 2 * x.2)
          (by rw [map_mul]) (by rw [map_mul, map_pow]))
      have h2' : sS * vS (u1 * x.1) (u1 ^ 2 * x.2) =
          vS (u1 * x.1) (u1 ^ 2 * x.2 + (u2 / u1) * (u1 * x.1)) * sS :=
        Subtype.ext (shearGL_mul_vH h2 hι hω (u2 / u1) _ _)
      rw [mul_inv_eq_iff_eq_mul]
      show ρ sS * ρ tS * ρ (vS x.1 x.2) =
        ρ (vS (u1 * x.1) (u1 ^ 2 * x.2 + (u2 / u1) * (u1 * x.1))) * (ρ sS * ρ tS)
      rw [← map_mul, ← map_mul, ← map_mul, mul_assoc, h1, ← mul_assoc, h2', mul_assoc]
  have hne := lineProj_ne_zero_of_trans_excl hV hodd hfaith htrans
  let U : Finset (F × F) :=
    (Finset.Icc 1 ((p - 1) / 2)).image (fun n : ℕ => ((1 : F), (n : F)))
  have hmem : ∀ u ∈ U, ∃ n : ℕ, 1 ≤ n ∧ n ≤ (p - 1) / 2 ∧ u = ((1 : F), (n : F)) := by
    intro u hu
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hu
    exact ⟨n, (Finset.mem_Icc.1 hn).1, (Finset.mem_Icc.1 hn).2, rfl⟩
  have hself : ∀ u ∈ U, det2 u (τ u) ≠ 0 := by
    intro u hu
    obtain ⟨n, hn1, hn2, rfl⟩ := hmem u hu
    have : det2 ((1 : F), (n : F)) (τ ((1 : F), (n : F))) = ((2 * n : ℕ) : F) := by
      simp only [det2, τ]
      push_cast
      ring
    rw [this]
    exact natCast_ne_zero_of_lt (by omega) (by omega)
  have hpair : ∀ u ∈ U, ∀ v ∈ U, u ≠ v → det2 u v ≠ 0 ∧ det2 u (τ v) ≠ 0 ∧
      det2 (τ u) v ≠ 0 ∧ det2 (τ u) (τ v) ≠ 0 := by
    intro u hu v hv huv
    obtain ⟨n, hn1, hn2, rfl⟩ := hmem u hu
    obtain ⟨n', hn1', hn2', rfl⟩ := hmem v hv
    have hnn : n ≠ n' := fun h => huv (by rw [h])
    have hsum : ((n + n' : ℕ) : F) ≠ 0 := natCast_ne_zero_of_lt (by omega) (by omega)
    have hdiff : (n' : F) - n ≠ 0 := by
      intro h0
      exact hnn (natCast_inj_of_lt (F := F) (p := p) (by omega) (by omega) (sub_eq_zero.1 h0).symm)
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [det2]
      intro h0
      apply hdiff
      linear_combination h0
    · simp only [det2, τ]
      intro h0
      apply hsum
      push_cast
      linear_combination h0
    · simp only [det2, τ]
      intro h0
      apply hsum
      push_cast
      linear_combination -h0
    · simp only [det2, τ]
      intro h0
      apply hdiff
      linear_combination -h0
  have hUne : ∀ u ∈ U, lineProj ρ' u ≠ 0 := by
    intro u hu
    obtain ⟨n, -, -, rfl⟩ := hmem u hu
    exact hne _ one_ne_zero
  have hUcard : U.card = (p - 1) / 2 := by
    rw [Finset.card_image_of_injOn, Nat.card_Icc]
    · omega
    · intro n hn n' hn' h
      have h' : (n : F) = n' := congrArg Prod.snd h
      have := (Finset.mem_Icc.1 hn).2
      have := (Finset.mem_Icc.1 hn').2
      exact natCast_inj_of_lt (F := F) (p := p) (by omega) (by omega) h'
  have := ord_mul_card_le_finrank_range_sub1_swap hV hodd hFcard hFK hs hτ2 hτk hsρ U hself hpair
    hUne
  rw [hUcard] at this
  exact this


end Rank

section All

open Matrix Module CFSG.LieType.Universal.Unitary CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique.Setup.Family

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Finite K] [CharP K p]

theorem inner_rank_unitary2 (hp5 : 5 ≤ p) (hK : Nat.card K = (p ^ 1) ^ 2) {E : Type*}
    [AddCommGroup E] [Module (ZMod 2) E] [Module.Finite (ZMod 2) E]
    (ρ₀ : ↥(StatedSU 3 (p ^ 1) K) →* (E ≃ₗ[ZMod 2] E))
    (hρ₀ : ∀ g, ρ₀ g = 1 →
      ∃ r : Kˣ, (g : GL (Fin 3) K) = GeneralLinearGroup.scalar (Fin 3) r)
    {g : ↥(StatedSU 3 (p ^ 1) K)} (hg2 : g * g = 1) (hg1 : g ≠ 1) :
    7 ≤ finrank (ZMod 2) (LinearMap.range (sub1 (ρ₀ g))) := by
  classical
  have hp := (Fact.out : p.Prime)
  have hp2 : p ≠ 2 := by omega
  have h : UnitaryFieldData p 1 K := ⟨hp, le_rfl, by rw [hK]; ring⟩
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K p]; exact hp2)
  let σ : K ≃+* K := CFSG.LieType.BorelTits.unitaryInvolution K p 1
  have hσ : ∀ x, σ (σ x) = x := CFSG.LieType.BorelTits.unitaryInvolution_involutive hK
  have hσbar : ∀ x, σ x = h.bar x := fun x => by
    show CFSG.LieType.BorelTits.unitaryInvolution K p 1 x = _
    rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, h.bar_apply]
  obtain ⟨c, hc⟩ := h.exists_bar_ne
  have hω : σ (c - h.bar c) = -(c - h.bar c) := by
    rw [map_sub, hσbar c, hσbar (h.bar c), h.bar_bar]
    ring
  have hω0 : c - h.bar c ≠ 0 := fun h0 => hc (sub_eq_zero.1 h0).symm
  obtain ⟨P, hP⟩ := exists_wittMatrix hK 3
  let Ξ : SU σ 3 ≃* StatedSU 3 (p ^ 1) K :=
    (conjEquiv P hP).trans (MulEquiv.subgroupCongr (SUid_eq_statedSU hK 3))
  let ρ : SU σ 3 →* (E ≃ₗ[ZMod 2] E) := ρ₀.comp Ξ.toMonoidHom
  have hΞ : ∀ g' : SU σ 3, ((Ξ g' : ↥(StatedSU 3 (p ^ 1) K)) : GL (Fin 3) K) =
      P * g' * P⁻¹ := fun g' => rfl
  have hρ : ∀ g' : SU σ 3, ρ g' = 1 →
      ∃ r : Kˣ, (g' : GL (Fin 3) K) = GeneralLinearGroup.scalar (Fin 3) r := by
    intro g' hg'
    obtain ⟨r, hr⟩ := hρ₀ (Ξ g') hg'
    refine ⟨r, ?_⟩
    rw [hΞ] at hr
    calc (g' : GL (Fin 3) K) = P⁻¹ * (P * g' * P⁻¹) * P := by group
      _ = P⁻¹ * GeneralLinearGroup.scalar (Fin 3) r * P := by rw [hr]
      _ = GeneralLinearGroup.scalar (Fin 3) r := by
        rw [mul_assoc, ← (commute_scalar r P).eq, inv_mul_cancel_left]
  let ι : ZMod p →+* K := ZMod.castHom (dvd_refl p) K
  have hFK : ∀ k : ZMod p, ∃ n : ℕ, (n : ZMod p) = k := fun k => ⟨k.val, ZMod.natCast_zmod_val k⟩
  have hι : ∀ x : ZMod p, σ (ι x) = ι x := by
    intro x
    obtain ⟨n, rfl⟩ := hFK x
    simp [ι, map_natCast]
  have hrk : 7 ≤ finrank (ZMod 2) (LinearMap.range (sub1 (ρ (negT σ)))) :=
    (seven_le_ord_mul hp5).trans (negT_rank2 hp5 (ZMod.card p) hFK ι hι hσ hω hω0 ρ hρ)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hneg2 : Ξ (negT σ) * Ξ (negT σ) = 1 := by rw [← map_mul, negT_mul_self, map_one]
  have hneg1 : Ξ (negT σ) ≠ 1 := by
    intro h1
    have h3 : negT σ = 1 := Ξ.injective (by rw [h1, map_one])
    have e := congrArg (fun M : SU σ 3 => ((M : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0) h3
    simp [negT, coe_torGL, torMat] at e
    apply h2
    linear_combination -e
  have hog : orderOf g = 2 := orderOf_eq_prime (by rw [pow_two]; exact hg2) hg1
  have hon : orderOf (Ξ (negT σ)) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hneg2) hneg1
  have c1 := CFSG.RankThree.Classical.isConj_unitaryInvT_of_orderOf h hp2 hog
  have c2 := CFSG.RankThree.Classical.isConj_unitaryInvT_of_orderOf h hp2 hon
  obtain ⟨u, hu⟩ := isConj_iff.1 (c2.symm.trans c1)
  have hgu : ρ₀ g = ρ₀ u * ρ₀ (Ξ (negT σ)) * (ρ₀ u)⁻¹ := by
    rw [← hu]
    simp [map_mul, map_inv]
  rw [hgu, finrank_range_sub1_conj]
  exact hrk


end All

section OuterRank

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.QuasithinUnique.Setup.Family

variable {p : ℕ} [Fact p.Prime] {K F : Type} [Field K] [Field F] [Fintype F] [DecidableEq F]
  [CharP F p] {h : UnitaryFieldData p 1 K} {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
  (D : CoverDataU h L)

theorem outer_rank_unitary2 [Finite W] [Fact (∀ w : W, w * w = 1)] (ι : F →+* K)
    (hFcard : Fintype.card F = p) (hp5 : 5 ≤ p) (hι : ∀ x, h.bar (ι x) = ι x)
    (hfix : ∀ m : K, h.bar m = m → ∃ x : F, ι x = m)
    (hFK : ∀ k : F, ∃ n : ℕ, (n : F) = k) (hperf : Group.IsPerfect ↥(SUI h)) {b : MulAut W}
    (hb : b ∈ Subgroup.normalizer (L : Set (MulAut W))) (hb2 : b * b = 1) (A : UI h)
    (hAs : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ =
      ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
    (hAA : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map h.bar = 1)
    (hβ : D.beta hb = primeFormConjHom h _ A * primeFormFieldHom h
      (isPrimeFormGram_one : IsPrimeFormGram (1 : GL (Fin 3) K)) (barEquiv h)) :
    4 ≤ Module.finrank (ZMod 2) (LinearMap.range (sub1 (binaryLin b))) := by
  classical
  have hFpr : (Fintype.card F).Prime := by rw [hFcard]; exact Fact.out
  have hFp5 : 5 ≤ Fintype.card F := by rw [hFcard]; exact hp5
  obtain ⟨v, hv0, hvadd, hvinv, hvfaith⟩ :=
    exists_unitary_inverted_vgroup h ι hFcard hp5 hι hfix A hAs hAA
  have hrel : ∀ x : ↥(SUI h), b * ((D.φ x : ↥L) : MulAut W) * b⁻¹ =
      ((D.φ (tauU h A (barEquiv h) x) : ↥L) : MulAut W) :=
    D.conj_eq hperf hb (tauU h A (barEquiv h)) (fun x => by rw [hβ]; exact conjField_mk h A _ x)
  have hvneg : ∀ a, v (-a) = (v a)⁻¹ := by
    intro a
    apply eq_inv_of_mul_eq_one_right
    rw [← hvadd, add_neg_cancel, hv0]
  let ρ' : F × F → (Additive W ≃ₗ[ZMod 2] Additive W) := fun a =>
    binaryLin ((D.φ (v a) : ↥L) : MulAut W)
  have hV : IsVAct ρ' := ⟨by simp [ρ', hv0], fun x y => by simp [ρ', hvadd]⟩
  have hodd : Odd (Fintype.card F) := by
    rw [hFcard]
    exact (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hfaith : ∀ x, ρ' x = 1 → x = 0 := by
    intro x hx
    have h1 : ((D.φ (v x) : ↥L) : MulAut W) = 1 :=
      binaryLin_injective (by rw [map_one]; exact hx)
    have h2' : D.φ (v x) = 1 := Subtype.ext h1
    obtain ⟨r, hr⟩ := D.ker_scalar _ (MonoidHom.mem_ker.2 h2')
    exact hvfaith x r hr
  have hs : binaryLin b * binaryLin b = 1 := by rw [← map_mul, hb2, map_one]
  have hsρ : ∀ a, binaryLin b * ρ' a * binaryLin b = ρ' (-a) := by
    intro a
    have h1 : b * ((D.φ (v a) : ↥L) : MulAut W) * b = ((D.φ (v (-a)) : ↥L) : MulAut W) := by
      have := hrel (v a)
      have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
      rw [hvinv, hbinv] at this
      rw [this, hvneg, map_inv, Subgroup.coe_inv]
    show binaryLin b * binaryLin ((D.φ (v a) : ↥L) : MulAut W) * binaryLin b =
      binaryLin ((D.φ (v (-a)) : ↥L) : MulAut W)
    rw [← map_mul, ← map_mul, h1]
  obtain ⟨o, o', hne, ho, ho'⟩ := exists_two_lines hV hodd hfaith
  have hdet : det2 (lineRep o) (lineRep o') ≠ 0 := det2_lineRep hne
  have hdet' : det2 (lineRep o') (lineRep o) ≠ 0 := det2_lineRep hne.symm
  have hne' : lineRep o ≠ lineRep o' := fun h => hdet (by rw [h]; simp [det2]; ring)
  have := two_mul_card_le_finrank_range_sub1 hV hodd hFpr hFp5 hFK hs hsρ {lineRep o, lineRep o'}
    (by
      intro u hu
      rcases Finset.mem_insert.1 hu with rfl | hu
      · exact lineRep_ne_zero _
      · rw [Finset.mem_singleton.1 hu]; exact lineRep_ne_zero _)
    (by
      intro u hu w hw huw
      rcases Finset.mem_insert.1 hu with rfl | hu <;>
        rcases Finset.mem_insert.1 hw with rfl | hw
      · exact absurd rfl huw
      · rw [Finset.mem_singleton.1 hw]; exact hdet
      · rw [Finset.mem_singleton.1 hu]
        exact hdet'
      · rw [Finset.mem_singleton.1 hu, Finset.mem_singleton.1 hw] at huw
        exact absurd rfl huw)
    (by
      intro u hu
      rcases Finset.mem_insert.1 hu with rfl | hu
      · exact ho
      · rw [Finset.mem_singleton.1 hu]; exact ho')
  rwa [Finset.card_pair hne'] at this


end OuterRank

section Final

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank CFSG.Quasithin
  CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.Family

open CFSG.SectionRank.OddCover in
theorem primeUnitaryThreeExclusion2F (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (W : Type)
    [CommGroup W] [Finite W] (hW : ∀ w : W, w * w = 1) (Lb : Subgroup (MulAut W))
    (hperf : Group.IsPerfect ↥Lb) (hirr : X1.IsIrrOn Lb)
    (hmod : StatedClassicalModel (CQ Lb) .PSU 3 p 1) (B : Subgroup (MulAut W))
    (hBN : B ≤ Subgroup.normalizer (Lb : Set (MulAut W))) (hB1 : B ≠ ⊥)
    (hB2 : IsElemAbelian2 B) : Nat.card B ^ 2 * Nat.card (fixV B) < Nat.card W := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (∀ w : W, w * w = 1) := ⟨hW⟩
  have : Nontrivial W := hirr.1
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  have hp2 : p ≠ 2 := by omega
  have hodd := odd_card_center_of_irreducible hW hirr.2
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmod
  have hK2 : Nat.card K = p ^ 2 := by rw [hK, pow_one]
  have : Fintype K := Fintype.ofFinite K
  have hKcard : Fintype.card K = p ^ 2 := by rw [← Nat.card_eq_fintype_card]; exact hK2
  have : CharP K p := charP_of_card_eq_prime_pow (p := p) (f := 2) hKcard
  have h : UnitaryFieldData p 1 K := ⟨hp, le_rfl, by rw [hK]; ring⟩
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K p]; exact hp2)
  have hH : ((-1 : ℤ) = 1 ∧ Nat.card K = p ∧ StatedSU 3 (p ^ 1) K = StatedSL 3 K) ∨
      ((-1 : ℤ) = -1 ∧ Nat.card K = p ^ 2 ∧ StatedSU 3 (p ^ 1) K = StatedSU 3 p K) :=
    Or.inr ⟨rfl, hK2, by rw [pow_one]⟩
  obtain ⟨φ, hφs, hφc, hφk⟩ := exists_cover_hom (ε := -1) (H := StatedSU 3 (p ^ 1) K) hp hp2 hH
    hperf hodd e
  have hperfSU : Group.IsPerfect ↥(StatedSU 3 (p ^ 1) K) := isPerfect_prime_three hp hp2 hH
  have hperfSUI : Group.IsPerfect ↥(SUI h) :=
    Group.IsPerfect.ofSurjective (f := (eSU h).toMonoidHom) (eSU h).surjective
  let D : CoverDataU h Lb := coverDataU_of_cover h e φ hφs hφc hφk
  have hkerodd : Odd (Nat.card φ.ker) := by
    have hdvd := Subgroup.card_dvd_of_le hφk
    rw [(CFSG.LinearGroups.unitary_scalar_kernel hp hK (n := 3) (by norm_num)).2.2] at hdvd
    exact Odd.of_dvd_nat (by decide : Odd 3) (hdvd.trans (Nat.gcd_dvd_left 3 _))
  have hkerc : ∀ g ∈ φ.ker, ∀ x : ↥(StatedSU 3 (p ^ 1) K), g * x = x * g := by
    intro g hg x
    have h1 := hφk hg
    rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at h1
    obtain ⟨r, hr⟩ := h1
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hr]
    exact ((commute_scalar r (x : GL (Fin 3) K)).eq).symm
  let ρ₀ : ↥(StatedSU 3 (p ^ 1) K) →* (Additive W ≃ₗ[ZMod 2] Additive W) :=
    binaryLin.comp (Lb.subtype.comp φ)
  have hρ₀ : ∀ g, ρ₀ g = 1 →
      ∃ r : Kˣ, (g : GL (Fin 3) K) = GeneralLinearGroup.scalar (Fin 3) r := by
    intro g hg
    have h1 : ((φ g : ↥Lb) : MulAut W) = 1 := binaryLin_injective (by rw [map_one]; exact hg)
    have h2' : φ g = 1 := Subtype.ext h1
    have h3 := hφk (MonoidHom.mem_ker.2 h2')
    rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at h3
    obtain ⟨r, hr⟩ := h3
    exact ⟨r, hr.symm⟩
  have hB2' : ∀ a ∈ B, a * a = 1 := fun a ha => by
    have := hB2.2 a ha
    rwa [pow_two] at this
  have hbN : ∀ a ∈ B, a ∈ Subgroup.normalizer (Lb : Set (MulAut W)) := fun a ha => hBN ha
  have hin : ∀ t ∈ B, t ∈ Lb → t ≠ 1 →
      7 ≤ Module.finrank (ZMod 2) (LinearMap.range (sub1 (binaryLin t))) := by
    intro t htB htL ht1
    obtain ⟨g, hg2, hgt⟩ := exists_involution_lift φ hkerodd (t := (⟨t, htL⟩ : ↥Lb))
      (Subtype.ext (hB2' t htB)) (MonoidHom.mem_range.2 (hφs _))
    have hg1 : g ≠ 1 := fun h' => ht1 (by
      have := hgt
      rw [h', map_one] at this
      exact congrArg Subtype.val this.symm)
    have h4 := inner_rank_unitary2 hp5 hK ρ₀ hρ₀ hg2 hg1
    have e1 : ρ₀ g = binaryLin t := by simp [ρ₀, hgt]
    rwa [e1] at h4
  have hcard : ∀ T : Subgroup (MulAut W), T ≤ B → T ≤ Lb → Nat.card T ≤ 4 := by
    intro T hTB hTL
    have hcT : Nat.card (T.subgroupOf Lb) ≤ 4 := by
      refine card_le_of_lifts φ hkerc hkerodd 4
        (fun T' hT' => card_le_four_of_det_one h2 (H := StatedSU 3 (p ^ 1) K)
          (fun x hx => CFSG.LieType.Universal.Unitary.det_eq_one_of_mem_statedSU hx) T' hT')
        (T.subgroupOf Lb) (fun x _ => MonoidHom.mem_range.2 (hφs x)) (fun x hx => ?_)
        (fun x hx y hy => ?_)
      · exact Subtype.ext (hB2' _ (hTB hx))
      · exact Subtype.ext (hB2.1 _ (hTB hx) _ (hTB hy))
    have : Nat.card (T.subgroupOf Lb) = Nat.card T :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTL).toEquiv
    omega
  let F := ↥(CFSG.LieType.Steinberg.fixedSubfield K p 1)
  have : Finite F := inferInstance
  have : Fintype F := Fintype.ofFinite F
  have hFcardN : Nat.card F = p := by
    have := CFSG.LieType.Steinberg.card_fixedSubfield (F := K) (p := p) (f := 1) hK
    rwa [pow_one] at this
  have hFcard : Fintype.card F = p := by rw [← Nat.card_eq_fintype_card]; exact hFcardN
  have : CharP F p := charP_of_card_eq_prime_pow (p := p) (f := 1) (by rw [pow_one]; exact hFcard)
  let ι : F →+* K := (CFSG.LieType.Steinberg.fixedSubfield K p 1).subtype
  have hι : ∀ x : F, h.bar (ι x) = ι x := fun x => by
    have h1 := x.2
    rw [CFSG.LieType.Steinberg.mem_fixedSubfield,
      CFSG.LieType.BorelTits.unitaryInvolution_apply] at h1
    rw [h.bar_apply]
    exact h1
  have hfix : ∀ m : K, h.bar m = m → ∃ x : F, ι x = m := fun m hm =>
    ⟨⟨m, by
      rw [CFSG.LieType.Steinberg.mem_fixedSubfield,
        CFSG.LieType.BorelTits.unitaryInvolution_apply, ← h.bar_apply]
      exact hm⟩, rfl⟩
  have hFK : ∀ k : F, ∃ n : ℕ, (n : F) = k := natCast_surjective_of_card_prime hFcardN
  have hout : ∀ a ∈ B, a ∉ Lb →
      3 ≤ Module.finrank (ZMod 2) (LinearMap.range (sub1 (binaryLin a))) := by
    intro a haB haL
    rcases D.dichotomy hp5 hperfSUI hW hirr.2 hodd (hbN a haB) (hB2' a haB) with
      h' | ⟨A, hAs, hAA, hβ⟩
    · exact absurd h' haL
    · have h4 := outer_rank_unitary2 D ι hFcard hp5 hι hfix hFK hperfSUI (hbN a haB) (hB2' a haB)
        A hAs hAA hβ
      omega
  have hidx : ∀ a ∈ B, ∀ a' ∈ B, a ∉ Lb → a' ∉ Lb → a * a' ∈ Lb := by
    intro a haB a' ha'B haL ha'L
    rcases D.dichotomy hp5 hperfSUI hW hirr.2 hodd (hbN a haB) (hB2' a haB) with
      h' | ⟨A, -, -, hβ⟩
    · exact absurd h' haL
    rcases D.dichotomy hp5 hperfSUI hW hirr.2 hodd (hbN a' ha'B) (hB2' a' ha'B) with
      h'' | ⟨A', -, -, hβ'⟩
    · exact absurd h'' ha'L
    have hsq : a * a' * (a * a') = 1 := by
      calc a * a' * (a * a') = a * (a' * a) * a' := by group
        _ = a * (a * a') * a' := by rw [hB2.1 a' ha'B a haB]
        _ = (a * a) * (a' * a') := by group
        _ = 1 := by rw [hB2' a haB, hB2' a' ha'B, one_mul]
    exact D.mul_mem hperfSUI hW hirr.2 hodd (hbN a haB) (hbN a' ha'B) hβ hβ' hsq
  by_contra hne
  push Not at hne
  let Fx : Submodule (ZMod 2) (Additive W) :=
    { carrier := {x | ∀ a ∈ B, binaryLin a x = x}
      add_mem' := fun {x y} hx hy a ha => by rw [map_add, hx a ha, hy a ha]
      zero_mem' := fun a _ => map_zero _
      smul_mem' := fun c x hx a ha => by rw [map_smul, hx a ha] }
  have hfixc : Nat.card Fx = Nat.card (fixV B) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨Additive.toMul x.1, fun a ha => congrArg Additive.toMul (x.2 a ha)⟩
        invFun := fun w => ⟨Additive.ofMul w.1, fun a ha => congrArg Additive.ofMul (w.2 a ha)⟩
        left_inv := fun x => Subtype.ext rfl
        right_inv := fun w => Subtype.ext rfl }
  have hpgrp : IsPGroup 2 B := fun a => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hB2.2 a a.2)⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1 hpgrp
  have hcardE : Nat.card (Additive W) = Nat.card W := Nat.card_congr Additive.toMul
  have hoff : Module.finrank (ZMod 2) (Additive W) - Module.finrank (ZMod 2) Fx ≤
      2 * Nat.log 2 (Nat.card B) := by
    refine finrank_sub_le_two_log_of_card_le Fx hk ?_
    rw [hcardE, hfixc]
    exact hne
  exact no_offender2_of_ranks binaryLin Lb B hB1 Fx (fun a ha x hx => hx a ha) hin hcard hout hidx
    hoff


end Final

end CFSG.Quasithin.B45Exc
