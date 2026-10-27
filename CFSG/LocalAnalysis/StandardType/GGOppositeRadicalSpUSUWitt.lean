module

public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalSpUSUBasis

public section

namespace CFSG.StandardType

namespace GGOppRadSpU

open Matrix CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary GGOppRad

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}

@[expose] def IsMid {n : ℕ} (m : ℕ) (x : Fin n → F) : Prop :=
  ∀ a : Fin n, (a.val < m ∨ n - m ≤ a.val) → x a = 0

omit [Finite F] [CharP F 2] in
theorem IsMid.add {n m : ℕ} {x y : Fin n → F} (hx : IsMid m x) (hy : IsMid m y) :
    IsMid m (x + y) := fun a ha => by rw [Pi.add_apply, hx a ha, hy a ha, add_zero]

omit [Finite F] [CharP F 2] in
theorem IsMid.smul {n m : ℕ} {x : Fin n → F} (hx : IsMid m x) (c : F) : IsMid m (c • x) :=
  fun a ha => by rw [Pi.smul_apply, hx a ha, smul_zero]

omit [Finite F] [CharP F 2] in
theorem IsMid.sub {n m : ℕ} {x y : Fin n → F} (hx : IsMid m x) (hy : IsMid m y) :
    IsMid m (x - y) := fun a ha => by rw [Pi.sub_apply, hx a ha, hy a ha, sub_zero]

omit [Finite F] [CharP F 2] in
theorem isMid_single {n m : ℕ} {a : Fin n} (ha : m ≤ a.val) (ha' : a.val < n - m) :
    IsMid m (Pi.single a (1 : F) : Fin n → F) := fun b hb => by
  have : b ≠ a := by
    rintro rfl
    omega
  simp [this]

omit [Finite F] [CharP F 2] in
theorem suForm_mid_single (σ : F ≃+* F) (hσ : ∀ c, σ (σ c) = c) {n m : ℕ} {x : Fin n → F}
    (hx : IsMid m x) {b : Fin n} (hb : b.val < m) :
    (suForm σ hσ n).β x (Pi.single b 1) = 0 := by
  rw [suForm_symm σ hσ, suForm_single, hx (Fin.rev b) (Or.inr (by rw [Fin.val_rev]; omega)),
    map_zero]

omit [Finite F] [CharP F 2] in
theorem fixes_of_mid (σ : F ≃+* F) (hσ : ∀ c, σ (σ c) = c) {n m : ℕ}
    {g : SU σ n} {x w p q : Fin n → F} (hx : IsMid m x) (hw : IsMid m w)
    (hg : ∀ v, natRep (SU σ n) g v = v + (suForm σ hσ n).β x v • p + (suForm σ hσ n).β w v • q)
    {b : Fin n} (hb : b.val < m) : natRep (SU σ n) g (Pi.single b 1) = Pi.single b 1 := by
  rw [hg, suForm_mid_single σ hσ hx hb, suForm_mid_single σ hσ hw hb, zero_smul, zero_smul,
    add_zero, add_zero]

theorem exists_SU_map_mid_of_ne (hF : Nat.card F = (2 ^ f) ^ 2) {n m : ℕ}
    (hmn : 2 * (m + 1) ≤ n) {y : Fin n → F} (hy : IsMid m y)
    (hyy : (suForm (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF) n).β y y = 0)
    (hα : y ⟨m, by omega⟩ ≠ 0) :
    ∃ (g : SU (unitaryInvolution F 2 f) n) (c : F),
      (∀ b : Fin n, b.val < m →
        natRep (SU (unitaryInvolution F 2 f) n) g (Pi.single b 1) = Pi.single b 1) ∧
      natRep (SU (unitaryInvolution F 2 f) n) g (Pi.single ⟨m, by omega⟩ 1) = c • y := by
  have hσ := unitaryInvolution_involutive hF
  set B := suForm (unitaryInvolution F 2 f) hσ n with hB
  set e : Fin n := ⟨m, by omega⟩ with he
  have hfi : (Fin.rev e).val = n - 1 - m := by rw [Fin.val_rev]; simp [e]; omega
  have hef : e ≠ Fin.rev e := fun h => by
    have := congrArg Fin.val h
    rw [hfi] at this
    simp [e] at this
    omega
  set ev : Fin n → F := Pi.single e 1 with hev
  set fv : Fin n → F := Pi.single (Fin.rev e) 1 with hfv
  have hβe : ∀ v, B.β ev v = v (Fin.rev e) := fun v => suForm_single _ hσ e v
  have hβf : ∀ v, B.β fv v = v e := fun v => by rw [hfv, suForm_single, Fin.rev_rev]
  have hev_e : ev e = 1 := by simp [ev]
  have hev_f : ev (Fin.rev e) = 0 := by simp [ev, Ne.symm hef]
  have hfv_e : fv e = 0 := by simp [fv, hef]
  have hfv_f : fv (Fin.rev e) = 1 := by simp [fv]
  have hevmid : IsMid m ev := isMid_single (by simp [e]) (by simp [e]; omega)
  have hfvmid : IsMid m fv := isMid_single (by rw [hfi]; omega) (by rw [hfi]; omega)
  set α := y e with hαdef
  set β := y (Fin.rev e) with hβdef
  set w₀ := y - α • ev - β • fv with hw₀
  have hy_eq : y = w₀ + α • ev + β • fv := by rw [hw₀]; abel
  have hw₀_e : w₀ e = 0 := by simp [hw₀, hev_e, hfv_e, ← hαdef]
  have hw₀_f : w₀ (Fin.rev e) = 0 := by simp [hw₀, hev_f, hfv_f, ← hβdef]
  have hw₀mid : IsMid m w₀ := (hy.sub (hevmid.smul α)).sub (hfvmid.smul β)
  set w := α⁻¹ • w₀ with hw
  have hwmid : IsMid m w := hw₀mid.smul _
  set c := α⁻¹ * β with hc
  have hff : B.β fv fv = 0 := by rw [hβf, hfv_e]
  have hfw : B.β fv w = 0 := by rw [hβf, hw, Pi.smul_apply, hw₀_e, smul_zero]
  have hwev : B.β w ev = 0 := by
    rw [suForm_symm _ hσ, hβe, hw, Pi.smul_apply, hw₀_f, smul_zero, map_zero]
  have hfev : B.β fv ev = 1 := by rw [hβf, hev_e]
  have h0 : B.β w₀ w₀ + (unitaryInvolution F 2 f) α * β +
      (unitaryInvolution F 2 f) β * α = 0 := by
    have h1 := hyy
    rw [hy_eq, ReflForm.β_expand3] at h1
    have e1 : B.β w₀ ev = 0 := by rw [suForm_symm _ hσ, hβe, hw₀_f, map_zero]
    have e2 : B.β w₀ fv = 0 := by rw [suForm_symm _ hσ, hβf, hw₀_e, map_zero]
    have e3 : B.β ev w₀ = 0 := by rw [hβe, hw₀_f]
    have e4 : B.β ev ev = 0 := by rw [hβe, hev_f]
    have e5 : B.β ev fv = 1 := by rw [hβe, hfv_f]
    have e6 : B.β fv w₀ = 0 := by rw [hβf, hw₀_e]
    rw [e1, e2, e3, e4, e5, e6, hfev, hff, suForm_σ] at h1
    linear_combination h1
  have hcσ : c + (unitaryInvolution F 2 f) c = B.β w w := by
    have hσα : (unitaryInvolution F 2 f) α ≠ 0 := (map_ne_zero _).mpr hα
    rw [hw, B.smul_left, B.smul_right, suForm_σ, hc, map_mul, map_inv₀]
    have ht : B.β w₀ w₀ =
        -((unitaryInvolution F 2 f) α * β + (unitaryInvolution F 2 f) β * α) := by
      linear_combination h0
    rw [ht]
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    field_simp
    linear_combination (β * (unitaryInvolution F 2 f) α + (unitaryInvolution F 2 f) β * α) * h2
  obtain ⟨g, hg⟩ := exists_SU_eichler (unitaryInvolution F 2 f) hσ hff hfw hcσ
  refine ⟨g, α⁻¹, fun b hb => fixes_of_mid _ hσ hfvmid hwmid hg hb, ?_⟩
  rw [hg, hfev, hwev, one_smul, zero_smul, add_zero, hy_eq, smul_add, smul_add, smul_smul,
    smul_smul, inv_mul_cancel₀ hα, one_smul]
  abel

theorem exists_SU_map_mid (hF : Nat.card F = (2 ^ f) ^ 2) {n m : ℕ}
    (hmn : 2 * (m + 1) ≤ n) {y : Fin n → F} (hy : IsMid m y) (hy0 : y ≠ 0)
    (hyy : (suForm (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF) n).β y y = 0) :
    ∃ (g : SU (unitaryInvolution F 2 f) n) (c : F),
      (∀ b : Fin n, b.val < m →
        natRep (SU (unitaryInvolution F 2 f) n) g (Pi.single b 1) = Pi.single b 1) ∧
      natRep (SU (unitaryInvolution F 2 f) n) g (Pi.single ⟨m, by omega⟩ 1) = c • y := by
  have hσ := unitaryInvolution_involutive hF
  set B := suForm (unitaryInvolution F 2 f) hσ n with hB
  set e : Fin n := ⟨m, by omega⟩ with he
  by_cases hα : y e ≠ 0
  · exact exists_SU_map_mid_of_ne hF hmn hy hyy hα
  push Not at hα
  have hfi : (Fin.rev e).val = n - 1 - m := by rw [Fin.val_rev]; simp [e]; omega
  have hef : e ≠ Fin.rev e := fun h => by
    have := congrArg Fin.val h
    rw [hfi] at this
    simp [e] at this
    omega
  set ev : Fin n → F := Pi.single e 1 with hev
  have hβe : ∀ v, B.β ev v = v (Fin.rev e) := fun v => suForm_single _ hσ e v
  have hev_e : ev e = 1 := by simp [ev]
  have hev_f : ev (Fin.rev e) = 0 := by simp [ev, Ne.symm hef]
  have hevmid : IsMid m ev := isMid_single (by simp [e]) (by simp [e]; omega)
  have hee : B.β ev ev = 0 := by rw [hβe, hev_f]
  obtain ⟨k, hkfix, hky, hkmid⟩ : ∃ k : SU (unitaryInvolution F 2 f) n,
      (∀ b : Fin n, b.val < m →
        natRep (SU (unitaryInvolution F 2 f) n) k (Pi.single b 1) = Pi.single b 1) ∧
      natRep (SU (unitaryInvolution F 2 f) n) k y e ≠ 0 ∧
      IsMid m (natRep (SU (unitaryInvolution F 2 f) n) k y) := by
    by_cases hβ : y (Fin.rev e) ≠ 0
    · obtain ⟨k, hk⟩ := exists_SU_transvection (unitaryInvolution F 2 f) hσ hee
      refine ⟨k, fun b hb => ?_, ?_, ?_⟩
      · rw [hk, suForm_mid_single _ hσ hevmid hb, zero_smul, add_zero]
      · rw [hk, Pi.add_apply, Pi.smul_apply, hβe, hev_e, hα, zero_add, smul_eq_mul, mul_one]
        exact hβ
      · rw [hk]
        exact hy.add (hevmid.smul _)
    push Not at hβ
    obtain ⟨a, ha⟩ : ∃ a, y a ≠ 0 := by
      by_contra h
      push Not at h
      exact hy0 (funext h)
    have hamid : m ≤ a.val ∧ a.val < n - m := by
      by_contra h
      apply ha
      apply hy a
      omega
    set w : Fin n → F := Pi.single (Fin.rev a) 1 with hw
    have hwmid : IsMid m w := isMid_single (by rw [Fin.val_rev]; omega)
      (by rw [Fin.val_rev]; omega)
    have hae : a ≠ e := fun h => ha (h ▸ hα)
    have hew : B.β ev w = 0 := by
      rw [hβe, hw, Pi.single_apply, ite_eq_right]
      intro h
      exact hae (Fin.rev_injective h.symm)
    have hfix : unitaryInvolution F 2 f (B.β w w) = B.β w w := by
      rw [← suForm_symm]
    obtain ⟨c, hc⟩ := exists_add_unitaryInvolution_eq hF hfix
    obtain ⟨k, hk⟩ := exists_SU_eichler (unitaryInvolution F 2 f) hσ hee hew hc
    have hwy : B.β w y = y a := by rw [hw, suForm_single, Fin.rev_rev]
    refine ⟨k, fun b hb => fixes_of_mid _ hσ hevmid hwmid hk hb, ?_, ?_⟩
    · rw [hk, hβe, hβ, zero_smul, add_zero, hwy, Pi.add_apply, Pi.smul_apply, hev_e, hα,
        zero_add, smul_eq_mul, mul_one]
      exact ha
    · rw [hk]
      exact (hy.add ((hwmid.add (hevmid.smul c)).smul _)).add (hevmid.smul _)
  have hkyy : B.β (natRep (SU (unitaryInvolution F 2 f) n) k y)
      (natRep (SU (unitaryInvolution F 2 f) n) k y) = 0 := by
    rw [isIsometric_natRep_SU _ hσ n k y y]
    exact hyy
  obtain ⟨g', c, hg'fix, hg'⟩ := exists_SU_map_mid_of_ne hF hmn hkmid hkyy hky
  refine ⟨k⁻¹ * g', c, fun b hb => ?_, ?_⟩
  · rw [map_mul, Module.End.mul_apply, hg'fix b hb]
    conv_lhs => rw [← hkfix b hb]
    exact rep_inv_apply_rep _ k _
  · rw [map_mul, Module.End.mul_apply, hg', map_smul, rep_inv_apply_rep]

omit [Finite F] [CharP F 2] in
theorem natRep_eq_of_fix {σ : F ≃+* F} {n m : ℕ} {g : SU σ n}
    (hg : ∀ b : Fin n, b.val < m → natRep (SU σ n) g (Pi.single b 1) = Pi.single b 1)
    {v : Fin n → F} (hv : v ∈ stdFlag (fun a : Fin n => a.val) m) : natRep (SU σ n) g v = v := by
  have hv' : v = ∑ b, v b • (Pi.single b (1 : F) : Fin n → F) := by
    conv_lhs => rw [← (Pi.basisFun F (Fin n)).sum_repr v]
    simp
  rw [hv', map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_smul]
  by_cases hb : b.val < m
  · rw [hg b hb]
  · rw [hv b (not_lt.mp hb), zero_smul, zero_smul]

omit [Finite F] [CharP F 2] in
theorem map_stdFlag_val_of_fix {σ : F ≃+* F} {n m : ℕ} {g : SU σ n}
    (hg : ∀ b : Fin n, b.val < m → natRep (SU σ n) g (Pi.single b 1) = Pi.single b 1)
    {i : ℕ} (hi : i ≤ m) :
    (stdFlag (fun a : Fin n => a.val) i).map (natRep (SU σ n) g) =
      stdFlag (K := F) (fun a : Fin n => a.val) i := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [natRep_eq_of_fix hg (stdFlag_mono _ hi hw)]
    exact hw
  · intro hv
    exact ⟨v, hv, natRep_eq_of_fix hg (stdFlag_mono _ hi hv)⟩

omit [Finite F] [CharP F 2] in
theorem map_map_natRep {σ : F ≃+* F} {n : ℕ} (g h : SU σ n) (X : Submodule F (Fin n → F)) :
    (X.map (natRep (SU σ n) h)).map (natRep (SU σ n) g) = X.map (natRep (SU σ n) (g * h)) := by
  rw [← Submodule.map_comp, map_mul, Module.End.mul_eq_comp]

theorem ggSUWittChainAt (hF : Nat.card F = (2 ^ f) ^ 2) (n : ℕ) : GGSUWittChainAt F f n hF := by
  have hσ := unitaryInvolution_involutive hF
  set B := suForm (unitaryInvolution F 2 f) hσ n with hB
  have hiso := isIsometric_natRep_SU (unitaryInvolution F 2 f) hσ n
  intro m
  induction m with
  | zero =>
    intro X _ hX _
    refine ⟨1, fun i hi => ?_⟩
    obtain rfl : i = 0 := by omega
    rw [stdFlag_zero, Submodule.map_bot]
    exact Submodule.finrank_eq_zero.mp (hX 0 le_rfl)
  | succ m ih =>
    intro X hXmono hXdim hXiso
    obtain ⟨g₀, hg₀⟩ := ih X hXmono (fun i hi => hXdim i (by omega))
      (hXiso.mono (hXmono (Nat.le_succ m)))
    set ρ := natRep (SU (unitaryInvolution F 2 f) n) with hρ
    set E : ℕ → Submodule F (Fin n → F) := stdFlag (fun a : Fin n => a.val) with hE
    set Y := (X (m + 1)).map (ρ g₀⁻¹) with hY
    have hEm : (X m).map (ρ g₀⁻¹) = E m := by
      rw [hg₀ m le_rfl, map_map_natRep, inv_mul_cancel, map_one]
      exact Submodule.map_id _
    have hEY : E m ≤ Y := hEm ▸ Submodule.map_mono (hXmono (Nat.le_succ m))
    have hinj : ∀ g : SU (unitaryInvolution F 2 f) n, Function.Injective (ρ g) :=
      natRep_injective_apply_su
    have hYdim : Module.finrank F Y = m + 1 := by
      have h1 := LinearEquiv.finrank_eq
        (Submodule.equivMapOfInjective _ (hinj g₀⁻¹) (X (m + 1)))
      rw [hY, ← h1]
      exact hXdim (m + 1) le_rfl
    have hYiso : B.IsTotallyIsotropic Y := by
      rintro _ ⟨u, hu, rfl⟩
      exact hiso.apply_mem_perp g₀⁻¹ (hXiso hu)
    have hdimn : Module.finrank F (Fin n → F) = n := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    have hmn : 2 * (m + 1) ≤ n := by
      have h1 := B.finrank_perp Y
      have h2 := Submodule.finrank_mono hYiso
      omega
    have hEdim : ∀ k ≤ n, Module.finrank F (E k) = k := fun k hk => by
      rw [hE, finrank_stdFlag]
      exact Fintype.card_fin_lt_of_le hk
    obtain ⟨y₀, hy₀Y, hy₀E⟩ : ∃ y₀ ∈ Y, y₀ ∉ E m := by
      by_contra h
      push Not at h
      have hle : Y ≤ E m := fun v hv => h v hv
      have := Submodule.finrank_mono hle
      rw [hYdim, hEdim m (by omega)] at this
      omega
    set y : Fin n → F := fun a => if a.val < m then 0 else y₀ a with hydef
    have hy₀y : y₀ - y ∈ E m := fun a ha => by
      have ha' : m ≤ a.val := ha
      have : ¬ a.val < m := by omega
      simp [hydef, this]
    have hyY : y ∈ Y := by
      have := sub_mem hy₀Y (hEY hy₀y)
      rwa [sub_sub_cancel] at this
    have hyE : y ∉ E m := fun h => hy₀E (by
      have := add_mem hy₀y h
      rwa [sub_add_cancel] at this)
    have hy0 : y ≠ 0 := fun h => hyE (h ▸ zero_mem _)
    have hyy : B.β y y = 0 := hYiso hyY y hyY
    have hymid : IsMid m y := by
      intro a ha
      rcases ha with ha | ha
      · simp [hydef, ha]
      · have hm : ¬ a.val < m := by omega
        simp only [hydef, hm, ↓reduceIte]
        have hra : (Fin.rev a).val < m := by rw [Fin.val_rev]; omega
        have h1 : (Pi.single (Fin.rev a) (1 : F) : Fin n → F) ∈ Y :=
          hEY (single_mem_stdFlag.mpr hra)
        have h2 := hYiso hy₀Y _ h1
        rwa [suForm_single, Fin.rev_rev] at h2
    obtain ⟨g₁, c, hg₁fix, hg₁⟩ := exists_SU_map_mid hF hmn hymid hy0 hyy
    refine ⟨g₀ * g₁, fun i hi => ?_⟩
    rcases Nat.lt_or_ge i (m + 1) with hi' | hi'
    · rw [← map_map_natRep, map_stdFlag_val_of_fix hg₁fix (by omega)]
      exact hg₀ i (by omega)
    · obtain rfl : i = m + 1 := by omega
      set em : Fin n := ⟨m, by omega⟩ with hem
      have hle : (E (m + 1)).map (ρ g₁) ≤ Y := by
        rintro _ ⟨v, hv, rfl⟩
        have hv' : v - v em • (Pi.single em (1 : F) : Fin n → F) ∈ E m := by
          intro a ha
          by_cases hae : a = em
          · subst hae
            simp
          · have ha' : m + 1 ≤ a.val := by
              have ha0 : m ≤ a.val := ha
              have : a.val ≠ m := fun h => hae (Fin.ext h)
              omega
            simp [hv a ha', hae]
        have hsplit : ρ g₁ v = ρ g₁ (v - v em • (Pi.single em (1 : F) : Fin n → F)) +
            v em • ρ g₁ (Pi.single em 1) := by
          rw [← map_smul, ← map_add, sub_add_cancel]
        rw [hsplit, natRep_eq_of_fix hg₁fix hv', hg₁]
        exact add_mem (hEY hv') (Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hyY))
      have heq : (E (m + 1)).map (ρ g₁) = Y := by
        refine Submodule.eq_of_le_of_finrank_eq hle ?_
        have h1 := LinearEquiv.finrank_eq
          (Submodule.equivMapOfInjective _ (hinj g₁) (E (m + 1)))
        rw [hYdim, ← h1]
        exact hEdim (m + 1) (by omega)
      rw [← map_map_natRep, heq, hY, map_map_natRep, mul_inv_cancel, map_one]
      exact (Submodule.map_id _).symm

end GGOppRadSpU

end CFSG.StandardType
