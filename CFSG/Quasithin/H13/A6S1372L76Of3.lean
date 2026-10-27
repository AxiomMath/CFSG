module

public import CFSG.Quasithin.H13.A6S1372L76Of2

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (unitriangular)
open scoped Pointwise IsMulCommutative Matrix

namespace A6L76Of

section Semi

variable {W : Type*} [CommGroup W] {Y : Subgroup (MulAut W)} {F : Type} [Field F]

@[expose] def IsSemi (β : ↥(commV Y) →* Multiplicative (Fin 3 → F)) (b : MulAut W)
    (σ : F →+* F) : Prop :=
  ∀ (u u' : ↥(commV Y)) (hu : b (u : W) ∈ commV Y) (hu' : b (u' : W) ∈ commV Y) (μ : F),
    Multiplicative.toAdd (β u') = μ • Multiplicative.toAdd (β u) →
      Multiplicative.toAdd (β ⟨b u', hu'⟩) = σ μ • Multiplicative.toAdd (β ⟨b u, hu⟩)

variable {β : ↥(commV Y) →* Multiplicative (Fin 3 → F)} {b c : MulAut W} {σ τ : F →+* F}

theorem isSemi_of_lift {f : Multiplicative (Fin 3 → F) →* Multiplicative (Fin 3 → F)}
    (hf : ∀ (u : ↥(commV Y)) (hu : b (u : W) ∈ commV Y), f (β u) = β ⟨b u, hu⟩)
    (hσ : ∀ (μ : F) (x : Fin 3 → F),
      Multiplicative.toAdd (f (Multiplicative.ofAdd (μ • x))) =
        σ μ • Multiplicative.toAdd (f (Multiplicative.ofAdd x))) : IsSemi β b σ := by
  intro u u' hu hu' μ h
  rw [← hf u' hu', ← hf u hu]
  have h1 : β u' = Multiplicative.ofAdd (μ • Multiplicative.toAdd (β u)) := by
    rw [← h, ofAdd_toAdd]
  rw [h1, hσ, ofAdd_toAdd]

theorem isSemi_one : IsSemi β 1 (RingHom.id F) := fun _ _ _ _ _ h => h

theorem IsSemi.mul (hb : IsSemi β b σ) (hc : IsSemi β c τ)
    (hcU : ∀ u ∈ commV Y, c u ∈ commV Y) : IsSemi β (b * c) (σ.comp τ) := by
  intro u u' hu hu' μ h
  exact hb ⟨c u, hcU _ u.2⟩ ⟨c u', hcU _ u'.2⟩ hu hu' (τ μ)
    (hc u u' (hcU _ u.2) (hcU _ u'.2) μ h)

theorem IsSemi.eq (hβs : Function.Surjective β)
    (hβk : ∀ u, β u = 1 ↔ (u : W) ∈ fixV Y ⊓ commV Y) (hbY : ∀ y ∈ Y, b * y * b⁻¹ ∈ Y)
    (hσ : IsSemi β b σ) (hτ : IsSemi β b τ) (x : F) : σ x = τ x := by
  obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd (Pi.single 0 1))
  have hbu := apply_mem_commV_of_conj hbY u.2
  have hne : Multiplicative.toAdd (β ⟨b u, hbu⟩) ≠ 0 := by
    intro h0
    have h1 := (hβk _).1 (toAdd_eq_zero.1 h0)
    have h2 : β u = 1 := by
      rw [hβk]
      refine ⟨fun y hy => ?_, u.2⟩
      have h3 := h1.1 _ (hbY y hy)
      rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self] at h3
      exact b.injective h3
    rw [hu] at h2
    have h4 := congrFun (ofAdd_eq_one.1 h2) 0
    simp at h4
  obtain ⟨u', hu'⟩ := hβs (Multiplicative.ofAdd (x • Multiplicative.toAdd (β u)))
  have h : Multiplicative.toAdd (β u') = x • Multiplicative.toAdd (β u) := by rw [hu', toAdd_ofAdd]
  have hbu' := apply_mem_commV_of_conj hbY u'.2
  have h1 := hσ u u' hbu hbu' x h
  have h2 := hτ u u' hbu hbu' x h
  exact smul_left_injective F hne (h1.symm.trans h2)

theorem IsSemi.pow (hσ : IsSemi β b σ) (hbU : ∀ u ∈ commV Y, b u ∈ commV Y) (k : ℕ) :
    ∃ τ : F →+* F, IsSemi β (b ^ k) τ ∧ ∀ x, τ x = (⇑σ)^[k] x := by
  have hpowU : ∀ k : ℕ, ∀ u ∈ commV Y, (b ^ k) u ∈ commV Y := by
    intro k
    induction k with
    | zero => intro u hu; rw [pow_zero]; exact hu
    | succ k ih =>
      intro u hu
      rw [pow_succ', MulAut.mul_apply]
      exact hbU _ (ih u hu)
  induction k with
  | zero => exact ⟨RingHom.id F, by rw [pow_zero]; exact isSemi_one, fun x => rfl⟩
  | succ k ih =>
    obtain ⟨τ, hτ, hτx⟩ := ih
    refine ⟨σ.comp τ, ?_, fun x => ?_⟩
    · rw [pow_succ']
      exact hσ.mul hτ (hpowU k)
    · rw [RingHom.comp_apply, hτx, Function.iterate_succ_apply']

variable [Finite F] {π : ↥(StatedSL 3 F) →* ↥Y}

theorem exists_isSemi (hs : Function.Surjective π) (hβs : Function.Surjective β)
    (hβk : ∀ u, β u = 1 ↔ (u : W) ∈ fixV Y ⊓ commV Y)
    (hβe : ∀ (γ : ↥(StatedSL 3 F)) (u : ↥(commV Y))
      (hu : ((π γ : ↥Y) : MulAut W) (u : W) ∈ commV Y), β ⟨_, hu⟩ = natHom γ (β u))
    (hbY : ∀ y ∈ Y, b * y * b⁻¹ ∈ Y) (hbY' : ∀ y ∈ Y, b⁻¹ * y * b ∈ Y) :
    ∃ σ : F →+* F, IsSemi β b σ := by
  obtain ⟨f, hf⟩ := exists_lift hβs hβk hbY hbY'
  obtain ⟨σ, hσ⟩ := lift_semilinear hβe hs hβs hβk hbY hbY' hf
  exact ⟨σ, isSemi_of_lift hf hσ⟩

theorem eq_id_of_isSemi [CharP F 2] {n : ℕ} (hn : Odd n) (hF : Nat.card F = 2 ^ n)
    (hs : Function.Surjective π) (hβs : Function.Surjective β)
    (hβk : ∀ u, β u = 1 ↔ (u : W) ∈ fixV Y ⊓ commV Y)
    (hβe : ∀ (γ : ↥(StatedSL 3 F)) (u : ↥(commV Y))
      (hu : ((π γ : ↥Y) : MulAut W) (u : W) ∈ commV Y), β ⟨_, hu⟩ = natHom γ (β u))
    {a t : MulAut W} (haY : ∀ y ∈ Y, a * y * a⁻¹ ∈ Y) (htY : ∀ y ∈ Y, t * y * t⁻¹ ∈ Y)
    (htY' : ∀ y ∈ Y, t⁻¹ * y * t ∈ Y) {j : ℕ} (hr : (t * a * t⁻¹ * a) ^ (2 ^ j) = 1)
    (hσ : IsSemi β a σ) (x : F) : σ x = x := by
  have hU : ∀ {b : MulAut W}, (∀ y ∈ Y, b * y * b⁻¹ ∈ Y) → ∀ u ∈ commV Y, b u ∈ commV Y :=
    fun hb u hu => apply_mem_commV_of_conj hb hu
  have htY'' : ∀ y ∈ Y, t⁻¹ * y * t⁻¹⁻¹ ∈ Y := fun y hy => by rw [inv_inv]; exact htY' y hy
  have htY''' : ∀ y ∈ Y, t⁻¹⁻¹ * y * t⁻¹ ∈ Y := fun y hy => by rw [inv_inv]; exact htY y hy
  obtain ⟨σt, hσt⟩ := exists_isSemi hs hβs hβk hβe htY htY'
  obtain ⟨σt', hσt'⟩ := exists_isSemi hs hβs hβk hβe htY'' htY'''
  have h1Y : ∀ y ∈ Y, (1 : MulAut W) * y * 1⁻¹ ∈ Y := fun y hy => by simpa using hy
  have htt : ∀ x, σt (σt' x) = x := by
    have h1 := hσt.mul hσt' (hU htY'')
    rw [mul_inv_cancel] at h1
    exact fun x => IsSemi.eq hβs hβk h1Y h1 isSemi_one x
  have hr' := ((hσt.mul hσ (hU haY)).mul hσt' (hU htY'')).mul hσ (hU haY)
  have hrU : ∀ u ∈ commV Y, (t * a * t⁻¹ * a) u ∈ commV Y := fun u hu =>
    hU htY _ (hU haY _ (hU htY'' _ (hU haY _ hu)))
  obtain ⟨τ, hτ, hτx⟩ := hr'.pow hrU (2 ^ j)
  rw [hr] at hτ
  have hτ1 : ∀ x, τ x = x := fun x => IsSemi.eq hβs hβk h1Y hτ isSemi_one x
  have hsq : (⇑σ)^[2] = ⇑(((σt.comp σ).comp σt').comp σ) := by
    funext y
    show σ (σ y) = σt (σ (σt' (σ y)))
    rw [ringHom_comm σt σ, htt]
  have hit : ∀ y, (⇑σ)^[2 ^ (j + 1)] y = y := by
    intro y
    rw [pow_succ', Function.iterate_mul, hsq, ← hτx, hτ1]
  exact ringHom_eq_id_of_iterate hF σ hit ((Nat.coprime_two_left.2 hn).pow_left (j + 1)) x

end Semi

theorem false_of_natSL3 {W : Type*} [CommGroup W] {Y : Subgroup (MulAut W)}
    (hY : Group.IsPerfect ↥Y) {F : Type} [Field F] [Finite F] {n : ℕ} (hn : Odd n)
    (hn3 : 3 ≤ n) (hF : Nat.card F = 2 ^ n) {π : ↥(StatedSL 3 F) →* ↥Y}
    (hπ : (FFModel.nat (StatedSL 3 F)).RealizesVia Y (commV Y) (fixV Y ⊓ commV Y) π)
    {a : MulAut W} (haY : ∀ y ∈ Y, a * y * a⁻¹ ∈ Y)
    {P : Subgroup (MulAut W)} (hP2 : IsPGroup 2 ↥P)
    (hPodd : Odd (P.subgroupOf Y).index) {v₂ : W} (hPv : ∀ p ∈ P, p v₂ = v₂)
    (hPa : ∀ p ∈ P, p (a v₂) = a v₂ ∨ p (a v₂) = v₂ * a v₂)
    (ha2 : a (a v₂) = v₂ * a v₂) (hv : v₂ ∉ fixV Y)
    {t : MulAut W} (htY : ∀ y ∈ Y, t * y * t⁻¹ ∈ Y) {j : ℕ}
    (hr : (t * a * t⁻¹ * a) ^ (2 ^ j) = 1) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) hF
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨hs, -, β, hβs, hβk, hβe0⟩ := A6L76Z.natRealizes_clean hπ
  have hβe : ∀ (γ : ↥(StatedSL 3 F)) (u : ↥(commV Y))
      (hu : ((π γ : ↥Y) : MulAut W) (u : W) ∈ commV Y), β ⟨_, hu⟩ = natHom γ (β u) :=
    fun γ u hu => hβe0 γ u hu
  have hinj : Function.Injective π :=
    FFC.injective_of_faithful_sec (FFModel.nat_faithful _) hπ
  have hβk' : ∀ u : ↥(commV Y), β u = 1 → (u : W) ∈ fixV Y := fun u hu => ((hβk u).1 hu).1
  have : Finite ↥Y := Finite.of_surjective π hs
  have haY' := inv_conj_mem haY
  have htY' := inv_conj_mem htY
  set P' : Subgroup ↥(StatedSL 3 F) := (P.subgroupOf Y).comap π with hP'
  have hP'2 : IsPGroup 2 ↥P' :=
    (hP2.comap_of_injective Y.subtype Y.subtype_injective).comap_of_injective π hinj
  have hP'odd : Odd P'.index := by
    rw [hP', Subgroup.index_comap_of_surjective _ hs]
    exact hPodd
  have h2 : ∀ m : Multiplicative (Fin 3 → F), m * m = 1 := fun m => by
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_one]
    funext i
    exact CharTwo.add_self_eq_zero _
  obtain ⟨m₁, hm₁⟩ := exists_coboundary_of_odd_index h2 natHom (f := cocyc π β v₂)
    (fun g h => cocyc_mul hβe v₂ g h) hP'odd
    (fun δ hδ => cocyc_eq_one_of_fix π β (hPv _ hδ))
  have hm₁P : ∀ δ ∈ P', natHom δ m₁ = m₁ := by
    intro δ hδ
    have h := hm₁ δ
    rw [cocyc_eq_one_of_fix π β (hPv _ hδ)] at h
    exact mul_inv_eq_one.1 h.symm
  have hm₁1 : m₁ ≠ 1 := by
    intro h1
    apply hv
    refine mem_fixV_of_cocyc_eq_one hY hs hβk' fun γ => ?_
    rw [hm₁, h1, map_one, mul_inv_cancel]
  obtain ⟨f, hf⟩ := exists_lift hβs hβk haY haY'
  obtain ⟨σ, hσ⟩ := lift_semilinear hβe hs hβs hβk haY haY' hf
  have hσ1 : ∀ x, σ x = x :=
    eq_id_of_isSemi hn hF hs hβs hβk hβe haY htY htY' hr (isSemi_of_lift hf hσ)
  obtain ⟨m₂, hm₂⟩ : ∃ m, m = f m₁ := ⟨_, rfl⟩
  have hcoc₂ : ∀ γ, cocyc π β (a v₂) γ = natHom γ m₂ * m₂⁻¹ := by
    rw [hm₂]
    exact cocyc_lift hβe hs hβs haY haY' hf hm₁
  have hcoc₃ : ∀ γ, cocyc π β (a (a v₂)) γ = natHom γ (f m₂) * (f m₂)⁻¹ :=
    cocyc_lift hβe hs hβs haY haY' hf hcoc₂
  have hfm₂ : f m₂ = m₁ * m₂ := by
    refine eq_of_natCoboundary_eq fun γ => ?_
    rw [← hcoc₃, ha2, cocyc_mul_left, hm₁, hcoc₂, map_mul, mul_inv_rev]
    ac_rfl
  obtain ⟨g, hg⟩ := exists_conj_unitriangular_stated hP'2 (fun h => by
    obtain ⟨k, hk⟩ := hP'odd
    omega)
  have hgU : ∀ u : Matrix.SpecialLinearGroup (Fin 3) F,
      specialLinearGroupEquivStatedSL 3 F u * g =
        g * (g⁻¹ * specialLinearGroupEquivStatedSL 3 F u * g) := fun u => by group
  obtain ⟨x₁, hx₁⟩ : ∃ x, Multiplicative.toAdd (natHom g m₁) = x := ⟨_, rfl⟩
  obtain ⟨x₂, hx₂⟩ : ∃ x, Multiplicative.toAdd (natHom g m₂) = x := ⟨_, rfl⟩
  have hx₁fix : ∀ u ∈ unitriangular 3 F, (u : Matrix (Fin 3) (Fin 3) F) *ᵥ x₁ = x₁ := by
    intro u hu
    have h3 : natHom (specialLinearGroupEquivStatedSL 3 F u) (natHom g m₁) = natHom g m₁ := by
      rw [← MulAut.mul_apply, ← map_mul, hgU u, map_mul, MulAut.mul_apply, hm₁P _ (hg u hu)]
    have h4 := congrArg Multiplicative.toAdd h3
    rw [natHom_apply (specialLinearGroupEquivStatedSL 3 F u) (natHom g m₁), hx₁] at h4
    exact h4
  obtain ⟨hx₁1, hx₁2⟩ := unitriangular_fix hx₁fix
  have hx₁0 : x₁ ≠ 0 := by
    intro h0
    apply hm₁1
    rw [← hx₁, toAdd_eq_zero, MulEquiv.map_eq_one_iff] at h0
    exact h0
  have hx₂mov : ∀ u ∈ unitriangular 3 F, (u : Matrix (Fin 3) (Fin 3) F) *ᵥ x₂ - x₂ = 0 ∨
      (u : Matrix (Fin 3) (Fin 3) F) *ᵥ x₂ - x₂ = x₁ := by
    intro u hu
    have hsP : ((π (g⁻¹ * specialLinearGroupEquivStatedSL 3 F u * g) : ↥Y) : MulAut W) ∈ P :=
      hg u hu
    have hcs : ∀ γ, cocyc π β (((π (g⁻¹ * specialLinearGroupEquivStatedSL 3 F u * g) : ↥Y) :
        MulAut W) (a v₂)) γ =
        natHom γ (natHom (g⁻¹ * specialLinearGroupEquivStatedSL 3 F u * g) m₂) *
          (natHom (g⁻¹ * specialLinearGroupEquivStatedSL 3 F u * g) m₂)⁻¹ := by
      intro γ
      rw [cocyc_conj hβe, hcoc₂, map_mul, map_inv, natHom_conj]
    have hb1 : natHom (specialLinearGroupEquivStatedSL 3 F u) (natHom g m₂) =
        natHom g (natHom (g⁻¹ * specialLinearGroupEquivStatedSL 3 F u * g) m₂) := by
      rw [← MulAut.mul_apply, ← map_mul, hgU u, map_mul, MulAut.mul_apply]
    rcases hPa _ hsP with h | h
    · left
      have h3 : natHom (g⁻¹ * specialLinearGroupEquivStatedSL 3 F u * g) m₂ = m₂ := by
        refine eq_of_natCoboundary_eq fun γ => ?_
        rw [← hcs, h, hcoc₂]
      rw [← hx₂]
      show Multiplicative.toAdd (natHom (specialLinearGroupEquivStatedSL 3 F u) (natHom g m₂)) -
        Multiplicative.toAdd (natHom g m₂) = 0
      rw [hb1, h3, sub_self]
    · right
      have h3 : natHom (g⁻¹ * specialLinearGroupEquivStatedSL 3 F u * g) m₂ = m₁ * m₂ := by
        refine eq_of_natCoboundary_eq fun γ => ?_
        rw [← hcs, h, cocyc_mul_left, hm₁, hcoc₂, map_mul, mul_inv_rev]
        ac_rfl
      rw [← hx₂, ← hx₁]
      show Multiplicative.toAdd (natHom (specialLinearGroupEquivStatedSL 3 F u) (natHom g m₂)) -
        Multiplicative.toAdd (natHom g m₂) = Multiplicative.toAdd (natHom g m₁)
      rw [hb1, h3, map_mul, toAdd_mul, add_sub_cancel_right]
  have hq : 2 < Nat.card F := by
    rw [hF]
    calc 2 < 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
  obtain ⟨hx₂1, hx₂2⟩ := unitriangular_comm hq hx₁0 ⟨hx₁1, hx₁2⟩ hx₂mov
  have hx₁00 : x₁ 0 ≠ 0 := by
    intro h0
    apply hx₁0
    funext i
    fin_cases i
    · exact h0
    · exact hx₁1
    · exact hx₁2
  obtain ⟨l, hl⟩ : ∃ l : F, l = x₂ 0 / x₁ 0 := ⟨_, rfl⟩
  have hx₂l : x₂ = l • x₁ := by
    funext i
    fin_cases i
    · show x₂ 0 = l * x₁ 0
      rw [hl, div_mul_cancel₀ _ hx₁00]
    · show x₂ 1 = l * x₁ 1
      rw [hx₂1, hx₁1, mul_zero]
    · show x₂ 2 = l * x₁ 2
      rw [hx₂2, hx₁2, mul_zero]
  have hginv : ∀ m, natHom g⁻¹ (natHom g m) = m := fun m => by
    rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
  have hm₂l : Multiplicative.toAdd m₂ = l • Multiplicative.toAdd m₁ := by
    have h1 : natHom g m₂ = Multiplicative.ofAdd (l • Multiplicative.toAdd (natHom g m₁)) := by
      rw [hx₁, ← hx₂l, ← hx₂, ofAdd_toAdd]
    calc Multiplicative.toAdd m₂ = Multiplicative.toAdd (natHom g⁻¹ (natHom g m₂)) := by
          rw [hginv]
      _ = Multiplicative.toAdd (natHom g⁻¹
            (Multiplicative.ofAdd (l • Multiplicative.toAdd (natHom g m₁)))) := by rw [h1]
      _ = l • Multiplicative.toAdd (natHom g⁻¹
            (Multiplicative.ofAdd (Multiplicative.toAdd (natHom g m₁)))) := natHom_smul _ _ _
      _ = l • Multiplicative.toAdd m₁ := by rw [ofAdd_toAdd, hginv]
  have hx0 : Multiplicative.toAdd m₁ ≠ 0 := fun h0 => hm₁1 (toAdd_eq_zero.1 h0)
  have key : (l * l) • Multiplicative.toAdd m₁ = (1 + l) • Multiplicative.toAdd m₁ := by
    have h1 := hσ l (Multiplicative.toAdd m₁)
    rw [ofAdd_toAdd, ← hm₂, ← hm₂l, ofAdd_toAdd, hfm₂, toAdd_mul, hm₂l, hσ1] at h1
    rw [mul_smul, ← h1, add_smul, one_smul]
  exact mul_self_ne_one_add hn hF l (smul_left_injective F hx0 key)

end A6L76Of

end CFSG.Quasithin.H13.A6
