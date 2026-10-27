module

public import CFSG.Quasithin.H13.NQCatT513L35Defs
public import CFSG.Quasithin.H13.NQCatT513PSL2
public import CFSG.RankThree.PartOne.AUTSL.Interface
public import Certificates.Certificate7155
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt

public section

namespace CFSG.Quasithin.H13.NQCat.T513

open CFSG.Quasithin CFSG.Quasithin.H13 L35 Matrix
open CFSG.ComponentClassification

theorem center_G35 : Subgroup.center G35 = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin] at hr
  have h3 : ∀ r : ZMod 5, r ^ 3 = 1 → r = 1 := by decide
  have hr1 : r = 1 := h3 r hr
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hrA, hr1, map_one, Matrix.SpecialLinearGroup.coe_one]

theorem graph_conj (n : ℕ) (K : Type) [Field K] (A : GL (Fin n) K) :
    CatalogueBGraphForm.slGraphAut n K * CatalogueBHigherLinearAction.slConjugation n K A *
        CatalogueBGraphForm.slGraphAut n K =
      CatalogueBHigherLinearAction.slConjugation n K (CatalogueBGraphForm.glGraphAut n K A) := by
  ext g : 1
  apply Matrix.SpecialLinearGroup.toGL_injective
  simp only [MulAut.mul_apply]
  rw [CatalogueBGraphForm.toGL_slGraphAut, CatalogueBHigherLinearAction.toGL_slConjugation,
    CatalogueBGraphForm.toGL_slGraphAut, CatalogueBHigherLinearAction.toGL_slConjugation,
    map_mul, map_mul, map_inv]
  have h2 : CatalogueBGraphForm.glGraphAut n K
      (CatalogueBGraphForm.glGraphAut n K (Matrix.SpecialLinearGroup.toGL g)) =
      Matrix.SpecialLinearGroup.toGL g := by
    have := DFunLike.congr_fun (CatalogueBGraphForm.glGraphAut_sq n K)
      (Matrix.SpecialLinearGroup.toGL g)
    rwa [pow_two, MulAut.mul_apply, MulAut.one_apply] at this
  rw [h2]

theorem slConjugation_toGL_eq (n : ℕ) (K : Type) [Field K] (g : SpecialLinearGroup (Fin n) K) :
    CatalogueBHigherLinearAction.slConjugation n K (Matrix.SpecialLinearGroup.toGL g) =
      MulAut.conj g := by
  ext h : 1
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [CatalogueBHigherLinearAction.toGL_slConjugation, MulAut.conj_apply, map_mul, map_mul,
    map_inv]

theorem inner_of_odd_sl35 (β : MulAut G35) (hβ : Odd (orderOf β)) :
    ∃ x : G35, β = MulAut.conj x := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨k, hk⟩ := hβ
  set γ := β ^ (k + 1) with hγdef
  have hγ : γ * γ = β := by
    rw [hγdef, ← pow_add, show k + 1 + (k + 1) = orderOf β + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  obtain ⟨A, σ, ε, hε, hA⟩ :=
    CFSG.RankThree.PartOne.AUTSL.exists_eq_std_of_mulAut_sl (n := 3) (K := ZMod 5)
      (by norm_num) γ
  have hσ : σ = 1 := RingEquiv.ext fun x => by
    have := RingHom.ext_zmod σ.toRingHom (RingHom.id (ZMod 5))
    exact DFunLike.congr_fun this x
  rw [hσ, map_one, mul_one] at hA
  obtain ⟨C, hC⟩ : ∃ C : GL (Fin 3) (ZMod 5),
      β = CatalogueBHigherLinearAction.slConjugation 3 (ZMod 5) C := by
    interval_cases ε
    · refine ⟨A * A, ?_⟩
      rw [← hγ, hA, pow_zero, mul_one, map_mul]
    · refine ⟨A * CatalogueBGraphForm.glGraphAut 3 (ZMod 5) A, ?_⟩
      rw [← hγ, hA, pow_one, map_mul, ← graph_conj]
      have hδ := CatalogueBGraphForm.slGraphAut_sq 3 (ZMod 5)
      rw [pow_two] at hδ
      calc CatalogueBHigherLinearAction.slConjugation 3 (ZMod 5) A *
            CatalogueBGraphForm.slGraphAut 3 (ZMod 5) *
            (CatalogueBHigherLinearAction.slConjugation 3 (ZMod 5) A *
              CatalogueBGraphForm.slGraphAut 3 (ZMod 5))
          = CatalogueBHigherLinearAction.slConjugation 3 (ZMod 5) A *
              (CatalogueBGraphForm.slGraphAut 3 (ZMod 5) *
                CatalogueBHigherLinearAction.slConjugation 3 (ZMod 5) A *
                CatalogueBGraphForm.slGraphAut 3 (ZMod 5)) *
              (CatalogueBGraphForm.slGraphAut 3 (ZMod 5) *
                CatalogueBGraphForm.slGraphAut 3 (ZMod 5)) := by
            rw [hδ, mul_one]
            group
        _ = _ := by rw [hδ, mul_one]
  set u : (ZMod 5)ˣ := Matrix.GeneralLinearGroup.det C with hu
  have hu4 : u ^ 4 = 1 := by
    have := ZMod.pow_card_sub_one_eq_one (p := 5) (a := (u : ZMod 5)) u.ne_zero
    exact Units.ext (by simpa using this)
  set lu := u ^ 3 with hlu
  set C' := Matrix.GeneralLinearGroup.scalar (Fin 3) lu⁻¹ * C with hC'
  have hdet : Matrix.GeneralLinearGroup.det C' = 1 := by
    rw [hC', map_mul, ← hu]
    have : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 3) lu⁻¹) =
        lu⁻¹ ^ 3 := by
      apply Units.ext
      simp [Matrix.GeneralLinearGroup.scalar]
    rw [this, hlu, show (u ^ 3)⁻¹ ^ 3 * u = (u ^ 4)⁻¹ ^ 2 by group, hu4, inv_one, one_pow]
  let x : G35 := ⟨(C' : Matrix (Fin 3) (Fin 3) (ZMod 5)), by
    have := congrArg Units.val hdet
    simpa using this⟩
  refine ⟨x, ?_⟩
  have hCx :
      C = Matrix.GeneralLinearGroup.scalar (Fin 3) lu * Matrix.SpecialLinearGroup.toGL x := by
    apply Units.ext
    show (C : Matrix (Fin 3) (Fin 3) (ZMod 5)) =
      ((Matrix.GeneralLinearGroup.scalar (Fin 3) lu * C' : GL (Fin 3) (ZMod 5)) :
        Matrix (Fin 3) (Fin 3) (ZMod 5))
    rw [hC', ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  rw [hC, hCx, map_mul, CatalogueBHigherLinearAction.slConjugation_scalar, one_mul,
    slConjugation_toGL_eq]

theorem core_sl35 {D₁ B₁ : Subgroup G35} (T : Sylow 2 G35)
    (hDc : IsCyclic D₁) (hDo : Odd (Nat.card D₁))
    (hperm : ∀ t ∈ (T : Subgroup G35), ∀ x ∈ D₁, ∃ x' ∈ D₁,
      ∃ t' ∈ (T : Subgroup G35), t * x = x' * t')
    (hB3 : Nat.card B₁ = 3) (hBD : B₁ ≤ Subgroup.normalizer (D₁ : Set G35)) :
    D₁ ≤ B₁ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hcT⟩ := MulAction.exists_smul_eq G35 T T0Sylow
  have hmap : (T : Subgroup G35).map (MulAut.conj c).toMonoidHom = T0 := by
    have h1 := congrArg (fun P : Sylow 2 G35 => (P : Subgroup G35)) hcT
    simp only [Sylow.coe_subgroup_smul, coe_T0Sylow] at h1
    rw [← h1, Subgroup.pointwise_smul_def]
    rfl
  have hmemT0 : ∀ t₀ ∈ T0, c⁻¹ * t₀ * c ∈ (T : Subgroup G35) := by
    intro t₀ ht₀
    rw [← hmap] at ht₀
    obtain ⟨t, ht, rfl⟩ := ht₀
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show c⁻¹ * (c * t * c⁻¹) * c = t by group]
    exact ht
  have hT0mem : ∀ t ∈ (T : Subgroup G35), c * t * c⁻¹ ∈ T0 := by
    intro t ht
    rw [← hmap]
    exact ⟨t, ht, rfl⟩
  set m := Nat.card D₁ with hmdef
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := D₁)
  have hgo : orderOf (g : G35) = m := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg]
  set g₀ := c * (g : G35) * c⁻¹ with hg₀
  have hg₀o : orderOf g₀ = m := by
    rw [hg₀, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hgo]
  have hm11625 : m ∣ 11625 := by
    have h1 : m ∣ 32 * 11625 := by
      rw [← hgo, show 32 * 11625 = 372000 by norm_num, ← card_G35]
      exact orderOf_dvd_natCard _
    have hcop : Nat.Coprime m 32 := by
      rw [show (32 : ℕ) = 2 ^ 5 by norm_num]
      exact Nat.Coprime.pow_right 5 (Nat.coprime_two_right.mpr hDo)
    exact hcop.dvd_of_dvd_mul_left h1
  have hg₀pow : g₀ ^ 11625 = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hg₀o]
    exact hm11625
  have hperm₀ : ∀ t ∈ T0, ∃ a : ℤ, ∃ t' ∈ T0, t * g₀ = g₀ ^ a * t' := by
    intro t₀ ht₀
    obtain ⟨x', hx', t', ht', he⟩ := hperm _ (hmemT0 t₀ ht₀) _ g.2
    obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x', hx'⟩)
    have hx'g : x' = (g : G35) ^ a := by
      have := congrArg Subtype.val ha
      simpa using this.symm
    refine ⟨a, c * t' * c⁻¹, hT0mem t' ht', ?_⟩
    have hg₀a : g₀ ^ a = c * (g : G35) ^ a * c⁻¹ := by
      rw [hg₀, ← MulAut.conj_apply, ← map_zpow, MulAut.conj_apply]
    rw [hg₀a, ← hx'g]
    calc t₀ * g₀ = c * (c⁻¹ * t₀ * c * (g : G35)) * c⁻¹ := by rw [hg₀]; group
      _ = c * (x' * t') * c⁻¹ := by rw [he]
      _ = c * x' * c⁻¹ * (c * t' * c⁻¹) := by group
  have h3 := Certificates.certificate7155 _ hg₀pow hperm₀
  have hm3 : m ∣ 3 := by
    rw [← hg₀o]
    exact orderOf_dvd_of_pow_eq_one h3
  have hD3 : IsPGroup 3 D₁ := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hm3 with h1 | h1
    · exact IsPGroup.of_card (n := 0) (by rw [← hmdef, h1, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [← hmdef, h1, pow_one])
  have hB3' : IsPGroup 3 B₁ := IsPGroup.of_card (n := 1) (by rw [hB3, pow_one])
  have hBD3 : IsPGroup 3 ↥(B₁ ⊔ D₁) := IsPGroup.to_sup_of_normal_right' hB3' hD3 hBD
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hBD3
  have hdvd : 3 ^ a ∣ 372000 := by
    rw [← ha, ← card_G35]
    exact Subgroup.card_subgroup_dvd_card _
  have ha1 : a ≤ 1 := by
    by_contra h
    push Not at h
    have : 3 ^ 2 ∣ 372000 := (Nat.pow_dvd_pow 3 h).trans hdvd
    norm_num at this
  have hle : Nat.card ↥(B₁ ⊔ D₁) ≤ Nat.card B₁ := by
    rw [ha, hB3]
    calc 3 ^ a ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) ha1
      _ = 3 := by norm_num
  have heq : B₁ ⊔ D₁ = B₁ := (Subgroup.eq_of_le_of_card_ge le_sup_left hle).symm
  rw [← heq]
  exact le_sup_right

section Case

variable {A : Type} [Group A] [Finite A] {Q R S B D : Subgroup A}

theorem normalizer_of_sl35_of_check (h : Star513 Q R S B D)
    (e : ↥Q ⧸ Subgroup.center ↥Q ≃* G35) (hZ : Subgroup.center ↥Q = ⊥) :
    D ≤ Subgroup.normalizer (R : Set A) := by
  have hinn : ∀ α : MulAut G35, Odd (orderOf α) → ∃ x, α = MulAut.conj x := inner_of_odd_sl35
  obtain ⟨hDc, hDo⟩ := iPart_D e hinn h center_G35
  obtain ⟨hT2, hTi⟩ := pImg_SQ e h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinj : Function.Injective (toP Q e) := by
    rw [← MonoidHom.ker_eq_bot_iff, ker_toP, hZ]
  have hBQ : B ≤ Q := fun b hb => h.R_le (h.hall_B.1 hb).1
  have hB3 : Nat.card (pImg Q e B) = 3 := by
    rw [pImg, Subgroup.card_map_of_injective hinj,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBQ).toEquiv, card_B h]
  have hBD : pImg Q e B ≤ Subgroup.normalizer (iPart Q e D : Set G35) := by
    intro y hy
    obtain ⟨b, hbQ, hb, rfl⟩ := (mem_pImg Q e).1 hy
    exact toP_mem_normalizer_iPart e h hb
  have hle := core_sl35 (hT2.toSylow hTi) hDc hDo (perm_D e hinn h center_G35) hB3 hBD
  apply le_normalizer_of_iPart e hinn h
  intro x hx
  exact Subgroup.le_normalizer (pImg_mono Q e (fun b hb => (h.hall_B.1 hb).1) (hle hx))

theorem normalizer_of_psl35 (h : Star513 Q R S B D)
    (hQ : IsPSLEps3 true 5 1 ↥Q ∨ IsSLEps3 true 5 ↥Q) :
    D ≤ Subgroup.normalizer (R : Set A) := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hmodel : ∀ e₁ : ↥Q ≃* G35, D ≤ Subgroup.normalizer (R : Set A) := by
    intro e₁
    have hZ : Subgroup.center ↥Q = ⊥ := by
      have h1 := Subgroup.map_center_eq e₁
      rw [center_G35] at h1
      exact (Subgroup.map_eq_bot_iff_of_injective _ e₁.injective).mp h1
    exact normalizer_of_sl35_of_check h
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans e₁)) hZ
  have hK5 : ∀ (K : Type) [Field K] [Finite K], Nat.card K = 5 → Nonempty (K ≃+* ZMod 5) := by
    intro K _ _ hK
    let _ : Fintype K := Fintype.ofFinite K
    exact ⟨FiniteField.ringEquivOfCardEq (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, Nat.card_zmod])⟩
  rcases hQ with hQ | hQ
  · obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ := hQ
    obtain ⟨σ⟩ := hK5 K (by rw [hK, pow_one])
    let e₂ : Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 5) ≃* G35 :=
      (QuotientGroup.quotientMulEquivOfEq center_G35).trans QuotientGroup.quotientBot
    exact hmodel (e₀.trans
      ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K).symm.trans
        ((CFSG.Adapters.RankTwoModelTransports.projectiveSpecialLinearGroupCongr (Fin 3) σ).trans
          e₂)))
  · obtain ⟨K, _, _, hK, ⟨e₀⟩⟩ := hQ
    obtain ⟨σ⟩ := hK5 K hK
    exact hmodel (e₀.trans
      ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).symm.trans
        (CFSG.Adapters.RankTwoModelTransports.specialLinearGroupCongr (Fin 3) σ)))

end Case

end CFSG.Quasithin.H13.NQCat.T513
