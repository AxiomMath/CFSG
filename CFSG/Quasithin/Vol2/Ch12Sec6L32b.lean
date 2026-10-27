module

public import CFSG.Quasithin.Vol2.Ch12Sec6L32a
public import CFSG.Quasithin.Background.B4Models

public section

namespace CFSG.Quasithin.H13.L1232

open CFSG.Quasithin CFSG.Assembly.LowTwoRank
open scoped Matrix Pointwise

variable {F : Type} [Field F] {W : Type*} [CommGroup W] {X : Subgroup (MulAut W)}
  {U : Subgroup W} {π : ↥(StatedSL 3 F) →* ↥X}

abbrev vecOf (x : (FFModel.nat (StatedSL 3 F)).Amb) : Fin 3 → F := Multiplicative.toAdd x

section Coord

variable (hR : (FFModel.nat (StatedSL 3 F)).RealizesVia X U ⊥ π)
include hR

theorem invariant_of_nat : ∀ f ∈ X, ∀ u ∈ U, f u ∈ U :=
  fun f hf u hu => hR.2.2.2.1 ⟨f, hf⟩ u hu

noncomputable def bv (u : ↥U) : Fin 3 → F :=
  vecOf ((Classical.choose (QuotientGroup.mk_surjective (hR.2.2.2.2.2.2.2.choose u)) :
    ↥(FFModel.nat (StatedSL 3 F)).sec) : (FFModel.nat (StatedSL 3 F)).Amb)

theorem mk_bv (u : ↥U) :
    (QuotientGroup.mk (⟨Multiplicative.ofAdd (bv hR u), Subgroup.mem_top _⟩ :
      ↥(FFModel.nat (StatedSL 3 F)).sec) : _ ⧸ _) = hR.2.2.2.2.2.2.2.choose u :=
  Classical.choose_spec (QuotientGroup.mk_surjective (hR.2.2.2.2.2.2.2.choose u))

theorem bv_injective : Function.Injective (bv hR) := by
  intro u₁ u₂ h
  obtain ⟨-, hk, -⟩ := hR.2.2.2.2.2.2.2.choose_spec
  have h1 : hR.2.2.2.2.2.2.2.choose u₁ = hR.2.2.2.2.2.2.2.choose u₂ := by
    rw [← mk_bv hR u₁, ← mk_bv hR u₂, h]
  have h2 : hR.2.2.2.2.2.2.2.choose (u₁⁻¹ * u₂) = 1 := by
    rw [map_mul, map_inv, h1, inv_mul_cancel]
  have h3 := (hk _).1 h2
  rw [Subgroup.mem_bot, Subgroup.coe_mul, Subgroup.coe_inv] at h3
  exact Subtype.ext (inv_mul_eq_one.1 h3)

theorem bv_surjective : Function.Surjective (bv hR) := by
  intro v
  obtain ⟨hs, -, -⟩ := hR.2.2.2.2.2.2.2.choose_spec
  obtain ⟨u, hu⟩ := hs (QuotientGroup.mk (⟨Multiplicative.ofAdd v, Subgroup.mem_top _⟩ :
    ↥(FFModel.nat (StatedSL 3 F)).sec))
  refine ⟨u, ?_⟩
  have h1 := (mk_bv hR u).trans hu
  rw [QuotientGroup.eq] at h1
  have h2 := Subgroup.mem_bot.1 (Subgroup.mem_subgroupOf.1 h1)
  rw [Subgroup.coe_mul, Subgroup.coe_inv] at h2
  have h3 := congrArg vecOf (inv_mul_eq_one.1 h2)
  exact h3

theorem bv_apply (γ : ↥(StatedSL 3 F)) (u : ↥U) (hu : ((π γ : ↥X) : MulAut W) (u : W) ∈ U) :
    bv hR ⟨_, hu⟩ = ((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ bv hR u := by
  obtain ⟨-, hk, hi⟩ := hR.2.2.2.2.2.2.2.choose_spec
  have h1 := hi γ u ⟨Multiplicative.ofAdd (bv hR u), Subgroup.mem_top _⟩ hu (Subgroup.mem_top _)
    (mk_bv hR u).symm
  have h2 := (mk_bv hR ⟨_, hu⟩).trans h1
  rw [QuotientGroup.eq] at h2
  have h3 := Subgroup.mem_bot.1 (Subgroup.mem_subgroupOf.1 h2)
  rw [Subgroup.coe_mul, Subgroup.coe_inv] at h3
  have h4 := congrArg vecOf (inv_mul_eq_one.1 h3)
  exact h4

theorem bv_apply' {γ : ↥(StatedSL 3 F)} {u v : ↥U}
    (h : ((π γ : ↥X) : MulAut W) (u : W) = v) :
    bv hR v = ((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ bv hR u := by
  have hu : ((π γ : ↥X) : MulAut W) (u : W) ∈ U := h ▸ v.2
  have e : v = ⟨_, hu⟩ := Subtype.ext h.symm
  rw [e]
  exact bv_apply hR γ u hu

theorem injective_of_nat : Function.Injective π := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro γ hγ
  rw [MonoidHom.mem_ker] at hγ
  have hfix : ∀ v : Fin 3 → F, ((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v := by
    intro v
    obtain ⟨u, rfl⟩ := bv_surjective hR v
    have h := bv_apply' hR (γ := γ) (u := u) (v := u) (by rw [hγ]; rfl)
    exact h.symm
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  apply Units.ext
  ext i j
  have := congrFun (hfix (Pi.single j 1)) i
  simpa [Matrix.mulVec_single, Matrix.one_apply, Pi.single_apply, eq_comm] using this

theorem card_of_nat [Fintype F] (hF : Fintype.card F = 4) : Nat.card ↥X = 60480 := by
  rw [← card_SL3 hF]
  exact (Nat.card_congr (Equiv.ofBijective π ⟨injective_of_nat hR, hR.1⟩)).symm

end Coord

section Sylow

variable [Fintype F]

theorem isPGroup_Uni (hF : Fintype.card F = 4) : IsPGroup 2 ↥(Uni F) := by
  refine IsPGroup.of_card (n := 6) ?_
  rw [card_Uni, Nat.card_eq_fintype_card, hF]
  norm_num

variable (hR : (FFModel.nat (StatedSL 3 F)).RealizesVia X U ⊥ π) (hF : Fintype.card F = 4)
include hR hF

theorem exists_conj {S : Subgroup (MulAut W)} (hSX : S ≤ X) (hS : Nat.card S = 64) :
    ∃ g : ↥X, (∀ γ ∈ Uni F, ((g⁻¹ * π γ * g : ↥X) : MulAut W) ∈ S) ∧
      ∀ s ∈ S, ∃ γ ∈ Uni F, ((g⁻¹ * π γ * g : ↥X) : MulAut W) = s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXc := card_of_nat hR hF
  have : Finite ↥X := Nat.finite_of_card_ne_zero (by rw [hXc]; norm_num)
  have hfac : (Nat.card ↥X).factorization 2 = 6 := by
    rw [hXc]
    have hne : (60480 : ℕ) ≠ 0 := by norm_num
    have h1 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).1
      (show 2 ^ 6 ∣ 60480 by norm_num)
    have h2 : ¬ 7 ≤ (60480 : ℕ).factorization 2 := fun h7 => by
      have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).2 h7
      norm_num at this
    omega
  have hS' : Nat.card ↥(S.subgroupOf X) = 2 ^ (Nat.card ↥X).factorization 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSX).toEquiv, hS, hfac]
    norm_num
  set SS : Sylow 2 ↥X := Sylow.ofCard _ hS'
  obtain ⟨Q₀, hQ₀⟩ := ((isPGroup_Uni hF).map π).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥X SS Q₀
  have hmem : ∀ x : ↥X, x ∈ (Q₀ : Subgroup ↥X) → g⁻¹ * x * g ∈ S.subgroupOf X := by
    intro x hx
    have h1 : x ∈ MulAut.conj g • (SS : Subgroup ↥X) := by
      rw [← Sylow.coe_subgroup_smul, hg]
      exact hx
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
      MulAut.conj_inv_apply] at h1
    exact h1
  have hcU : Nat.card ↥((Uni F).map π) = 64 := by
    rw [Subgroup.card_map_of_injective (injective_of_nat hR), card_Uni, Nat.card_eq_fintype_card,
      hF]
    norm_num
  have hcQ : Nat.card ↥(Q₀ : Subgroup ↥X) = 64 := by
    rw [Sylow.card_eq_multiplicity, hfac]
    norm_num
  have hQeq : (Uni F).map π = (Q₀ : Subgroup ↥X) :=
    Subgroup.eq_of_le_of_card_ge hQ₀ (by rw [hcU, hcQ])
  refine ⟨g, fun γ hγ => ?_, fun s hs => ?_⟩
  · exact Subgroup.mem_subgroupOf.1 (hmem _ (hQeq ▸ Subgroup.mem_map_of_mem π hγ))
  ·
    have hsS : (⟨s, hSX hs⟩ : ↥X) ∈ S.subgroupOf X := hs
    have h1 : g * ⟨s, hSX hs⟩ * g⁻¹ ∈ (Q₀ : Subgroup ↥X) := by
      rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
        MulAut.smul_def, MulAut.conj_inv_apply]
      have e : g⁻¹ * (g * ⟨s, hSX hs⟩ * g⁻¹) * g = ⟨s, hSX hs⟩ := by group
      rw [e]
      exact hsS
    rw [← hQeq] at h1
    obtain ⟨γ, hγ, hγe⟩ := h1
    refine ⟨γ, hγ, ?_⟩
    rw [hγe]
    simp [mul_assoc]

theorem card_fix_le {S : Subgroup (MulAut W)} (hSX : S ≤ X) (hS : Nat.card S = 64) :
    Nat.card {w : ↥U // ∀ f ∈ S, f (w : W) = w} ≤ 4 := by
  obtain ⟨g, hg, -⟩ := exists_conj hR hF hSX hS
  have hgU : ∀ w : ↥U, ((g : ↥X) : MulAut W) (w : W) ∈ U := fun w =>
    invariant_of_nat hR _ g.2 _ w.2
  let gw : ↥U → ↥U := fun w => ⟨_, hgU w⟩
  have hfix : ∀ w : ↥U, (∀ f ∈ S, f (w : W) = w) → ∀ γ ∈ Uni F,
      ((π γ : ↥X) : MulAut W) ((gw w : ↥U) : W) = (gw w : W) := by
    intro w hw γ hγ
    have h1 := hw _ (hg γ hγ)
    have e : ((π γ : ↥X) : MulAut W) = (g : MulAut W) * ((g⁻¹ * π γ * g : ↥X) : MulAut W) *
        (g : MulAut W)⁻¹ := by
      simp [mul_assoc]
    show ((π γ : ↥X) : MulAut W) ((g : MulAut W) (w : W)) = (g : MulAut W) (w : W)
    rw [e, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, h1]
  have hzero : ∀ w : ↥U, (∀ f ∈ S, f (w : W) = w) → bv hR (gw w) 1 = 0 ∧ bv hR (gw w) 2 = 0 := by
    intro w hw
    refine eq_of_fix_Uni fun γ hγ => ?_
    exact (bv_apply' hR (hfix w hw γ hγ)).symm
  have hinj : Function.Injective fun w : {w : ↥U // ∀ f ∈ S, f (w : W) = w} =>
      bv hR (gw w.1) 0 := by
    rintro ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ h
    have h1 : bv hR (gw w₁) = bv hR (gw w₂) := by
      obtain ⟨a1, a2⟩ := hzero w₁ hw₁
      obtain ⟨b1, b2⟩ := hzero w₂ hw₂
      ext i
      fin_cases i
      · exact h
      · simp [a1, b1]
      · simp [a2, b2]
    have h2 := congrArg Subtype.val (bv_injective hR h1)
    exact Subtype.ext (Subtype.ext ((g : MulAut W).injective h2))
  calc Nat.card {w : ↥U // ∀ f ∈ S, f (w : W) = w} ≤ Nat.card F :=
        Nat.card_le_card_of_injective _ hinj
    _ = 4 := by rw [Nat.card_eq_fintype_card, hF]

theorem exists_five {S : Subgroup (MulAut W)} (hSX : S ≤ X) (hS : Nat.card S = 64) {w : W}
    (hwU : w ∈ U) (hw : ∀ f ∈ S, f w = w) :
    ∃ f ∈ X, f w = w ∧ f ^ 5 = 1 ∧ f ≠ 1 := by
  obtain ⟨g, hg, -⟩ := exists_conj hR hF hSX hS
  have h2 : (2 : F) = 0 := two_eq_zero hF
  obtain ⟨ω, hω⟩ := exists_omega hF
  have hgU : (g : MulAut W) w ∈ U := invariant_of_nat hR _ g.2 _ hwU
  have hfixg : ∀ γ ∈ Uni F,
      ((π γ : ↥X) : MulAut W) ((g : MulAut W) w) = (g : MulAut W) w := by
    intro γ hγ
    have h1 := hw _ (hg γ hγ)
    have e : ((π γ : ↥X) : MulAut W) = (g : MulAut W) * ((g⁻¹ * π γ * g : ↥X) : MulAut W) *
        (g : MulAut W)⁻¹ := by
      simp [mul_assoc]
    rw [e, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, h1]
  have hz := eq_of_fix_Uni (v := bv hR ⟨_, hgU⟩) fun γ hγ =>
    (bv_apply' hR (u := ⟨_, hgU⟩) (v := ⟨_, hgU⟩) (hfixg γ hγ)).symm
  have hv : bv hR ⟨_, hgU⟩ = ![bv hR ⟨_, hgU⟩ 0, 0, 0] := by
    ext i
    fin_cases i <;> simp [hz.1, hz.2]
  have hdU : ((π (dSL h2 ω) : ↥X) : MulAut W) ((g : MulAut W) w) ∈ U :=
    invariant_of_nat hR _ (π (dSL h2 ω)).2 _ hgU
  have hd : ((π (dSL h2 ω) : ↥X) : MulAut W) ((g : MulAut W) w) = (g : MulAut W) w := by
    have h1 := bv_apply hR (dSL h2 ω) ⟨_, hgU⟩ hdU
    rw [hv, dSL_fix] at h1
    have := bv_injective hR (h1.trans hv.symm)
    exact congrArg Subtype.val this
  refine ⟨((g⁻¹ * π (dSL h2 ω) * g : ↥X) : MulAut W), (g⁻¹ * π (dSL h2 ω) * g).2, ?_, ?_, ?_⟩
  · simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.mul_apply, hd, MulAut.inv_apply_self]
  · have e : (g⁻¹ * π (dSL h2 ω) * g) ^ 5 = 1 := by
      rw [show g⁻¹ * π (dSL h2 ω) * g = g⁻¹ * π (dSL h2 ω) * g⁻¹⁻¹ by rw [inv_inv], conj_pow,
        ← map_pow, dSL_pow_five h2 hω, map_one, mul_one, mul_inv_cancel]
    rw [← Subgroup.coe_pow, e, Subgroup.coe_one]
  · intro h1
    have h3 : (g⁻¹ * π (dSL h2 ω) * g : ↥X) = 1 := Subtype.ext h1
    have h4 : π (dSL h2 ω) = 1 := by
      have : π (dSL h2 ω) = g * (g⁻¹ * π (dSL h2 ω) * g) * g⁻¹ := by group
      rw [this, h3, mul_one, mul_inv_cancel]
    exact dSL_ne_one h2 (injective_of_nat hR (h4.trans (map_one π).symm))

theorem eq_one_of_five {S : Subgroup (MulAut W)} (hSX : S ≤ X) (hS : Nat.card S = 64)
    {f : MulAut W} (hfX : f ∈ X) (hf5 : f ^ 5 = 1) (hfS : ∀ s ∈ S, f * s * f⁻¹ ∈ S) :
    f = 1 := by
  obtain ⟨g, hg, hg'⟩ := exists_conj hR hF hSX hS
  set e := MulEquiv.ofBijective π ⟨injective_of_nat hR, hR.1⟩ with he
  set m := e.symm (g * ⟨f, hfX⟩ * g⁻¹) with hmdef
  have hm : π m = g * ⟨f, hfX⟩ * g⁻¹ := e.apply_symm_apply _
  have hmU : ∀ u ∈ Uni F, m * u * m⁻¹ ∈ Uni F := by
    intro u hu
    obtain ⟨γ, hγ, hγe⟩ := hg' _ (hfS _ (hg u hu))
    have hπ : π γ = π (m * u * m⁻¹) := by
      rw [map_mul, map_mul, map_inv, hm]
      apply Subtype.ext
      have h1 : ((π γ : ↥X) : MulAut W) = (g : MulAut W) *
          ((g⁻¹ * π γ * g : ↥X) : MulAut W) * (g : MulAut W)⁻¹ := by
        simp [mul_assoc]
      rw [h1, hγe]
      simp [mul_assoc]
    rw [← injective_of_nat hR hπ]
    exact hγ
  have hm5 : m ^ 5 = 1 := by
    apply injective_of_nat hR
    rw [map_pow, hm, map_one]
    rw [show g * ⟨f, hfX⟩ * g⁻¹ = g * (⟨f, hfX⟩ : ↥X) * g⁻¹ from rfl, conj_pow]
    have : (⟨f, hfX⟩ : ↥X) ^ 5 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hf5)
    rw [this, mul_one, mul_inv_cancel]
  have h1 := eq_one_of_normalizes hF hmU hm5
  have h2 : g * (⟨f, hfX⟩ : ↥X) * g⁻¹ = 1 := by rw [← hm, h1, map_one]
  have h3 : (⟨f, hfX⟩ : ↥X) = 1 := by
    have : (⟨f, hfX⟩ : ↥X) = g⁻¹ * (g * ⟨f, hfX⟩ * g⁻¹) * g := by group
    rw [this, h2, mul_one, inv_mul_cancel]
  exact congrArg Subtype.val h3

end Sylow

end CFSG.Quasithin.H13.L1232
