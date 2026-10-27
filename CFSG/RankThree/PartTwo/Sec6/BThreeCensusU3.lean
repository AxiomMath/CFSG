module

public import CFSG.RankThree.PartTwo.Sec6.BThreeCensusSL3
public import CFSG.RankThree.PartTwo.KFacts.K72L3Unitary
import CFSG.RankThree.PartTwo.KFacts.K71IdentSU3

public section

namespace CFSG.RankThree.PartTwo.Sec6.BThreeCensus

open CFSG.RankThree.PartTwo.KFacts CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial Matrix
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)

variable {p f : ℕ} {K : Type} [Field K]

theorem pow_three_eq_one_of_mem_unitaryScalars {h : UnitaryFieldData p f K}
    {z : unitarySU p f K 3} (hz : z ∈ unitaryScalars h 3) : z ^ 3 = 1 := by
  obtain ⟨c, -, hc3, hzc⟩ := hz
  apply Subtype.ext
  rw [Subgroup.coe_pow, hzc, ← map_pow, hc3, map_one, Subgroup.coe_one]

theorem coprime_card_unitaryScalars [Finite K] (h : UnitaryFieldData p f K) {m : ℕ}
    (hm : ¬ 3 ∣ m) : Nat.Coprime (Nat.card (unitaryScalars h 3)) m := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 (unitaryScalars h 3) := by
    rw [IsPGroup.iff_orderOf]
    intro z
    have h1 : orderOf z ∣ 3 := orderOf_dvd_of_pow_eq_one (Subtype.ext (by
      simpa using pow_three_eq_one_of_mem_unitaryScalars z.2))
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
    · exact ⟨0, by rw [h, pow_zero]⟩
    · exact ⟨1, by rw [h, pow_one]⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
  rw [hk]
  exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm)

theorem cycThree_mem_unitarySU (h : UnitaryFieldData p f K) :
    SpecialLinearGroup.toGL (cycThree K) ∈ unitarySU p f K 3 := by
  refine (mem_unitarySU_iff h).mpr ⟨(cycThree K).2, ?_⟩
  change ((cycThreeMat K).map h.bar)ᵀ * cycThreeMat K = 1
  have hbar : (cycThreeMat K).map h.bar = cycThreeMat K := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [cycThreeMat]
  rw [hbar]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cycThreeMat, Matrix.mul_apply, Fin.sum_univ_three]

noncomputable def cycThreeSU (h : UnitaryFieldData p f K) : unitarySU p f K 3 :=
  ⟨SpecialLinearGroup.toGL (cycThree K), cycThree_mem_unitarySU h⟩

theorem cycThreeSU_pow_three (h : UnitaryFieldData p f K) : cycThreeSU h ^ 3 = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_pow, cycThreeSU, ← map_pow, cycThree_pow_three, map_one, Subgroup.coe_one]

theorem cycThreeSU_not_mem_unitaryScalars (h : UnitaryFieldData p f K) :
    cycThreeSU h ∉ unitaryScalars h 3 := by
  rintro ⟨c, -, -, hc⟩
  have h1 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 0 2) hc
  change cycThreeMat K 0 2 =
    ((Matrix.GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 2
    at h1
  simp [cycThreeMat, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at h1

theorem eq_bot_of_le_of_isSubnormal_su3 [Finite K] (h : UnitaryFieldData p f K)
    (hq2 : 2 < p ^ f) {V V₁ : Subgroup (unitarySU p f K 3)} (h3 : ¬ 3 ∣ Nat.card V)
    (hVV₁ : V ≤ V₁) (hV₁ : V₁ ≤ V ⊔ unitaryScalars h 3) (hsn : V₁.IsSubnormal) : V = ⊥ := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hsimple : IsSimpleGroup (unitaryPSU h 3) := by
    have hK : Nat.card K = (p ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
    have := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K p f hK 3 le_rfl
      (by
        intro h32
        have := congrArg Prod.snd h32
        simp only at this
        omega)
    exact (unitaryPSUEquiv h (by norm_num)).isSimpleGroup
  rcases (hsn.map (unitaryProj_surjective h 3)).eq_bot_or_top_of_isSimpleGroup hsimple with
    hb | ht
  · rw [eq_bot_iff]
    intro v hv
    have hv1 : unitaryProj h 3 v = 1 := by
      have : unitaryProj h 3 v ∈ V₁.map (unitaryProj h 3) := ⟨v, hVV₁ hv, rfl⟩
      rw [hb] at this
      exact this
    rw [← MonoidHom.mem_ker, ker_unitaryProj] at hv1
    exact eq_one_of_pow_three_of_not_three_dvd h3 hv (pow_three_eq_one_of_mem_unitaryScalars hv1)
  · exfalso
    have hc : unitaryProj h 3 (cycThreeSU h) ∈ V₁.map (unitaryProj h 3) := ht ▸ Subgroup.mem_top _
    obtain ⟨v₁, hv₁, hv₁t⟩ := hc
    have hz : (cycThreeSU h)⁻¹ * v₁ ∈ unitaryScalars h 3 := by
      rw [← ker_unitaryProj, MonoidHom.mem_ker, map_mul, map_inv, hv₁t, inv_mul_cancel]
    obtain ⟨v, hv, z', hz', hvz'⟩ := Subgroup.mem_sup_of_normal_right.mp (hV₁ hv₁)
    set z := (cycThreeSU h)⁻¹ * v₁ * z'⁻¹ with hzdef
    have hzs : z ∈ unitaryScalars h 3 := mul_mem hz (inv_mem hz')
    have hvz : v = cycThreeSU h * z := by
      rw [hzdef, ← hvz']
      group
    have hcomm : Commute (cycThreeSU h) z :=
      ((unitaryScalars_le_center h 3 hzs).comm (cycThreeSU h)).symm
    have hv3 : v ^ 3 = 1 := by
      rw [hvz, hcomm.mul_pow, cycThreeSU_pow_three, pow_three_eq_one_of_mem_unitaryScalars hzs,
        one_mul]
    have hv1 := eq_one_of_pow_three_of_not_three_dvd h3 hv hv3
    apply cycThreeSU_not_mem_unitaryScalars h
    have : cycThreeSU h = z⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← hvz, hv1]
    rw [this]
    exact inv_mem hzs

theorem eq_bot_of_isPerfect_su3_two [Finite K] (h : UnitaryFieldData p f K) (hq : p ^ f = 2)
    (V : Subgroup (unitarySU p f K 3)) (hVp : Group.IsPerfect V) (h3 : ¬ 3 ∣ Nat.card V) :
    V = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (unitarySU p f K 3) = 216 := by
    rw [card_unitarySU_three h, hq]
    norm_num
  have hdvd : Nat.card V ∣ 2 ^ 3 := by
    have h1 : Nat.card V ∣ 2 ^ 3 * 3 ^ 3 := by
      rw [show 2 ^ 3 * 3 ^ 3 = 216 by norm_num, ← hcard]
      exact Subgroup.card_subgroup_dvd_card V
    exact (Nat.Coprime.pow_left 3 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3)
      ).symm.dvd_of_dvd_mul_right h1
  have hp : IsPGroup 2 V := IsPGroup.of_card_dvd_pow hdvd
  have : Finite V := Subtype.finite
  have : Group.IsNilpotent V := hp.isNilpotent
  have : Group.IsSolvable V := inferInstance
  exact eq_bot_of_isPerfect_of_isSolvable hVp this

theorem unitaryProj_apply (h : UnitaryFieldData p f K) (g : unitarySU p f K 3) :
    unitaryProj h 3 g = (g : unitaryPSU h 3) := rfl

theorem threePrimeB3_unitaryPSU_three_all [Finite K]
    (h3 : (3 : K) ≠ 0) (h : UnitaryFieldData p f K) (hq2 : 2 < p ^ f) :
    ThreePrimeB3 (unitaryPSU h 3) := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hsimple : IsSimpleGroup (unitaryPSU h 3) := by
    have hK : Nat.card K = (p ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
    have := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K p f hK 3 le_rfl
      (by
        intro h32
        have := congrArg Prod.snd h32
        simp only at this
        omega)
    exact (unitaryPSUEquiv h (by norm_num)).isSimpleGroup
  have hcen : Subgroup.center (unitarySU p f K 3) = unitaryScalars h 3 :=
    center_unitarySU_three (h := h) hq2
  have hkerc : Nat.card (unitaryProj h 3).ker = Nat.card (unitaryScalars h 3) := by
    rw [ker_unitaryProj]
  intro β hβ C Y R hC hYC hsn hYp hY3 hRY hRn hRs _
  by_cases hD : β ∈ (psuConj h).range
  ·
    obtain ⟨A, rfl⟩ := hD
    obtain ⟨-, d, -, hd⟩ := eq_one_of_psuConj_mul_psuField_eq_one (A ^ 3) 1
      (by rw [map_one, mul_one, map_pow, hβ])
    have hA3 : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ 3 = (d : K) • 1 := by
      rw [← Units.val_pow_eq_pow_val, ← Subgroup.coe_pow, hd, Matrix.GeneralLinearGroup.coe_scalar,
        Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
    by_cases hAs : ∃ a : K, ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = a • 1
    ·
      obtain ⟨a, ha⟩ := hAs
      have ha0 : a ≠ 0 := by
        rintro rfl
        have hdet := ((A : GL (Fin 3) K)).isUnit.map Matrix.detMonoidHom
        rw [ha, zero_smul] at hdet
        simp at hdet
      have hAeq : (A : GL (Fin 3) K) =
          Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 a ha0) := by
        apply Units.ext
        rw [ha, Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0, Matrix.scalar_apply,
          Matrix.smul_one_eq_diagonal]
      have hβ1 : psuConj h A = 1 := by
        have hmem : Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 a ha0) ∈ unitaryIsom3 h :=
          hAeq ▸ A.2
        have := psuConj_scalar hmem
        rwa [show (⟨_, hmem⟩ : unitaryIsom3 h) = A from Subtype.ext hAeq.symm] at this
      have hCtop : C = ⊤ := by
        ext z
        simp [hC z, hβ1]
      have hsimp : IsSimpleGroup C :=
        ((MulEquiv.subgroupCongr hCtop).trans Subgroup.topEquiv).isSimpleGroup
      exact commutator_eq_bot_of_isSimpleGroup_or_isSolvable (Or.inl hsimp) hYC hsn hYp hRY hRn
        hRs
    · push Not at hAs
      suffices hY : Y = ⊥ by rw [hY, Subgroup.commutator_bot_right]
      obtain ⟨Y', hY'map, hY'disj⟩ := exists_lift_of_coprime (unitaryProj_surjective h 3) Y
        (by rw [hkerc]; exact coprime_card_unitaryScalars h hY3)
      obtain ⟨hY'card, hY'p⟩ := lift_card_and_perfect hY'map hY'disj
      have hfix : ∀ y ∈ Y', suConj h A y = y := by
        refine eq_of_mul_inv_mem_center (hY'p hYp) (suConj h A).toMonoidHom fun y hy => ?_
        rw [hcen, ← ker_unitaryProj, MonoidHom.mem_ker, map_mul, map_inv]
        have hyY : unitaryProj h 3 y ∈ Y := hY'map ▸ ⟨y, hy, rfl⟩
        have h1 := (hC _).mp (hYC hyY)
        rw [unitaryProj_apply, psuConj_mk] at h1
        change unitaryProj h 3 (suConj h A y) * (unitaryProj h 3 y)⁻¹ = 1
        rw [unitaryProj_apply, unitaryProj_apply, h1, mul_inv_cancel]
      set Y'' : Subgroup (GL (Fin 3) K) := Y'.map (unitarySU p f K 3).subtype with hY''
      have hY''bot : Y'' = ⊥ := by
        refine eq_bot_of_commute_glThree_of_pow_three_eq_smul h3 hA3 hAs Y'' ?_ ?_ ?_
        · rintro _ ⟨y, hy, rfl⟩
          have h1 := congrArg (fun z : unitarySU p f K 3 => (z : GL (Fin 3) K)) (hfix y hy)
          simp only [coe_suConj, Subgroup.coe_inv] at h1
          change (y : GL (Fin 3) K) * (A : GL (Fin 3) K) = (A : GL (Fin 3) K) * (y : GL (Fin 3) K)
          calc (y : GL (Fin 3) K) * (A : GL (Fin 3) K) =
              (A : GL (Fin 3) K) * (y : GL (Fin 3) K) * (A : GL (Fin 3) K)⁻¹ *
                (A : GL (Fin 3) K) := by rw [h1]
            _ = (A : GL (Fin 3) K) * (y : GL (Fin 3) K) := by group
        · have := hY'p hYp
          exact Group.IsPerfect.map _
        · rwa [Subgroup.card_map_of_injective (unitarySU p f K 3).subtype_injective, hY'card]
      have hY'bot : Y' = ⊥ :=
        (Subgroup.map_eq_bot_iff_of_injective Y' (unitarySU p f K 3).subtype_injective).mp
          hY''bot
      rw [← hY'map, hY'bot, Subgroup.map_bot]
  ·
    obtain ⟨σ, hσ3, H, hβH⟩ := unitary_order_three_field_descent hq2 β hβ hD
    suffices hY : Y = ⊥ by rw [hY, Subgroup.commutator_bot_right]
    set τ := psuConj h H with hτ
    set C₀ : Subgroup (unitaryPSU h 3) := (psuField h σ).toMonoidHom.eqLocus (MonoidHom.id _)
      with hC₀
    set Y₀ : Subgroup (unitaryPSU h 3) := Y.map (τ⁻¹ : MulAut (unitaryPSU h 3)).toMonoidHom
      with hY₀
    have hβτ : ∀ z, β z = z ↔ psuField h σ (τ⁻¹ z) = τ⁻¹ z := by
      intro z
      rw [hβH, MulAut.mul_apply, MulAut.mul_apply]
      constructor
      · intro h'
        have := congrArg (τ⁻¹ : MulAut (unitaryPSU h 3)) h'
        rwa [show τ⁻¹ (τ (psuField h σ (τ⁻¹ z))) = psuField h σ (τ⁻¹ z) from
          τ.symm_apply_apply _] at this
      · intro h'
        rw [h']
        exact τ.apply_symm_apply z
    have hY₀C₀ : Y₀ ≤ C₀ := by
      rintro _ ⟨y, hy, rfl⟩
      exact (hβτ y).mp ((hC y).mp (hYC hy))
    have hsn₀ : (Y₀.subgroupOf C₀).IsSubnormal := by
      let ρ : C →* C₀ :=
        ((τ⁻¹ : MulAut (unitaryPSU h 3)).toMonoidHom.comp C.subtype).codRestrict C₀ fun c =>
          (hβτ c).mp ((hC c).mp c.2)
      have hρ : Function.Surjective ρ := by
        rintro ⟨z, hz⟩
        have hτz : τ⁻¹ (τ z) = z := τ.symm_apply_apply z
        refine ⟨⟨τ z, (hC _).mpr ((hβτ _).mpr ?_)⟩, ?_⟩
        · rw [hτz]
          exact hz
        · apply Subtype.ext
          exact hτz
      have hmap : (Y.subgroupOf C).map ρ = Y₀.subgroupOf C₀ := by
        ext ⟨z, hz⟩
        rw [Subgroup.mem_subgroupOf]
        constructor
        · rintro ⟨c, hc, hcz⟩
          exact ⟨c, hc, congrArg Subtype.val hcz⟩
        · rintro ⟨y, hy, rfl⟩
          exact ⟨⟨y, hYC hy⟩, hy, rfl⟩
      rw [← hmap]
      exact hsn.map hρ
    have hY₀3 : ¬ 3 ∣ Nat.card Y₀ := by
      rwa [hY₀, Subgroup.card_map_of_injective
        (f := (τ⁻¹ : MulAut (unitaryPSU h 3)).toMonoidHom) (MulEquiv.injective _)]
    have hY₀p : Group.IsPerfect Y₀ := by
      have := hYp
      exact Group.IsPerfect.map _
    obtain ⟨Y', hY'map, hY'disj⟩ := exists_lift_of_coprime (unitaryProj_surjective h 3) Y₀
      (by rw [hkerc]; exact coprime_card_unitaryScalars h hY₀3)
    obtain ⟨hY'card, hY'p⟩ := lift_card_and_perfect hY'map hY'disj
    have hfix : ∀ y ∈ Y', suField h σ y = y := by
      refine eq_of_mul_inv_mem_center (hY'p hY₀p) (suField h σ).toMonoidHom fun y hy => ?_
      rw [hcen, ← ker_unitaryProj, MonoidHom.mem_ker, map_mul, map_inv]
      have hyY : unitaryProj h 3 y ∈ C₀ := hY₀C₀ (hY'map ▸ ⟨y, hy, rfl⟩)
      have h1 : psuField h σ (unitaryProj h 3 y) = unitaryProj h 3 y := hyY
      rw [unitaryProj_apply, psuField_mk] at h1
      change unitaryProj h 3 (suField h σ y) * (unitaryProj h 3 y)⁻¹ = 1
      rw [unitaryProj_apply, unitaryProj_apply, h1, mul_inv_cancel]
    obtain ⟨f₀, hf, hf₀, hcard₀⟩ := exists_card_fixedField_of_orderOf_eq_three h hσ3
    have h₀ : UnitaryFieldData p f₀ (CFSG.GH74.GLS.IVK.fixedField σ) := ⟨h.prime, hf₀, hcard₀⟩
    have hbar := bar_coe_fixedField h hf h₀
    have : Finite (CFSG.GH74.GLS.IVK.fixedField σ) := Subtype.finite
    set ψ := suIncl h h₀ hbar with hψ
    have hψi : Function.Injective ψ := suIncl_injective h h₀ hbar
    have hY'ψ : Y' ≤ ψ.range := fun y hy => (mem_range_suIncl_iff h h₀ hbar y).mpr (hfix y hy)
    set V := Y'.comap ψ with hV
    have hVmap : V.map ψ = Y' := Subgroup.map_comap_eq_self hY'ψ
    have hVcard : Nat.card V = Nat.card Y₀ := by
      rw [← Subgroup.card_map_of_injective hψi, hVmap, hY'card]
    have hV3 : ¬ 3 ∣ Nat.card V := by rw [hVcard]; exact hY₀3
    have hVbot : V = ⊥ := by
      by_cases hq₀ : p ^ f₀ = 2
      · refine eq_bot_of_isPerfect_su3_two h₀ hq₀ V ?_ hV3
        have hVe : V ≃* Y' :=
          (MonoidHom.ofInjective (f := ψ.comp V.subtype) (hψi.comp V.subtype_injective)).trans
            (MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp, Subgroup.range_subtype, hVmap]))
        have := hY'p hY₀p
        exact Group.IsPerfect.ofSurjective (f := hVe.symm.toMonoidHom) hVe.symm.surjective
      · have hq₀2 : 2 < p ^ f₀ := by
          have h1 : 2 ≤ p ^ f₀ := le_trans h.prime.two_le (Nat.le_self_pow (by omega) p)
          omega
        set V₁ := Y₀.comap ((unitaryProj h 3).comp ψ) with hV₁
        have hVV₁ : V ≤ V₁ := fun s hs => by
          change unitaryProj h 3 (ψ s) ∈ Y₀
          rw [← hY'map]
          exact ⟨ψ s, hs, rfl⟩
        have hV₁V : V₁ ≤ V ⊔ unitaryScalars h₀ 3 := by
          intro s hs
          have hs' : unitaryProj h 3 (ψ s) ∈ Y'.map (unitaryProj h 3) := by
            rw [hY'map]; exact hs
          obtain ⟨y, hy, hys⟩ := hs'
          obtain ⟨t, ht⟩ := hY'ψ hy
          have htV : t ∈ V := by
            change ψ t ∈ Y'
            rw [ht]
            exact hy
          have hz : ψ (t⁻¹ * s) ∈ unitaryScalars h 3 := by
            rw [← ker_unitaryProj, MonoidHom.mem_ker, map_mul, map_mul, map_inv, ht, map_inv, hys,
              inv_mul_cancel]
          have hzs : t⁻¹ * s ∈ unitaryScalars h₀ 3 := by
            obtain ⟨c, -, -, hcz⟩ := hz
            set w := t⁻¹ * s with hw
            have hdiag : ((w : GL (Fin 3) (CFSG.GH74.GLS.IVK.fixedField σ)) :
                Matrix (Fin 3) (Fin 3) (CFSG.GH74.GLS.IVK.fixedField σ)) =
                ((w : GL (Fin 3) (CFSG.GH74.GLS.IVK.fixedField σ)) :
                  Matrix (Fin 3) (Fin 3) (CFSG.GH74.GLS.IVK.fixedField σ)) 0 0 • 1 := by
              apply eq_smul_one_of_map_eq_smul_one (CFSG.GH74.GLS.IVK.fixedField σ).subtype
                (a := (c : K))
              have h2 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K)) hcz
              simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at h2
              rw [← Matrix.smul_one_eq_diagonal] at h2
              ext i j
              have h3 := congrFun (congrFun h2 i) j
              rw [coe_suIncl_apply h h₀ hbar] at h3
              rw [Matrix.map_apply]
              exact h3
            have hdet := ((mem_unitarySU_iff h₀).mp w.2).1
            rw [hdiag, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hdet
            have hw0 : ((w : GL (Fin 3) (CFSG.GH74.GLS.IVK.fixedField σ)) :
                Matrix (Fin 3) (Fin 3) (CFSG.GH74.GLS.IVK.fixedField σ)) 0 0 ≠ 0 := by
              intro h0
              rw [h0, zero_pow (by norm_num)] at hdet
              exact zero_ne_one hdet
            rw [unitaryScalars_eq h₀ (by norm_num), Subgroup.mem_subgroupOf]
            refine ⟨Units.mk0 _ hw0, Units.ext ?_⟩
            rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0, Matrix.scalar_apply,
              ← Matrix.smul_one_eq_diagonal]
            exact hdiag.symm
          have : s = t * (t⁻¹ * s) := by group
          rw [this]
          exact Subgroup.mul_mem_sup htV hzs
        have hsn₁ : V₁.IsSubnormal := by
          let θ : unitarySU p f₀ (CFSG.GH74.GLS.IVK.fixedField σ) 3 →* C₀ :=
            ((unitaryProj h 3).comp ψ).codRestrict C₀ fun s => by
              change psuField h σ (unitaryProj h 3 (ψ s)) = unitaryProj h 3 (ψ s)
              rw [unitaryProj_apply, psuField_mk,
                (mem_range_suIncl_iff h h₀ hbar (ψ s)).mp ⟨s, rfl⟩]
          have hcomap : (Y₀.subgroupOf C₀).comap θ = V₁ := by
            ext s
            rfl
          rw [← hcomap]
          exact hsn₀.comap θ
        exact eq_bot_of_le_of_isSubnormal_su3 h₀ hq₀2 hV3 hVV₁ hV₁V hsn₁
    have hY'bot : Y' = ⊥ := by rw [← hVmap, hVbot, Subgroup.map_bot]
    have hY₀bot : Y₀ = ⊥ := by rw [← hY'map, hY'bot, Subgroup.map_bot]
    exact (Subgroup.map_eq_bot_iff_of_injective Y
      (τ⁻¹ : MulAut (unitaryPSU h 3)).injective).mp hY₀bot

@[expose] noncomputable def suDescend (h : UnitaryFieldData p f K) (hq2 : 2 < p ^ f) :
    MulAut (unitarySU p f K 3) →* MulAut (unitaryPSU h 3) :=
  (MulAut.congr (suCenterEquiv h hq2)).toMonoidHom.comp (centerDescend _)

theorem suDescend_apply (h : UnitaryFieldData p f K) (hq2 : 2 < p ^ f)
    (β : MulAut (unitarySU p f K 3)) (g : unitarySU p f K 3) :
    suDescend h hq2 β (g : unitaryPSU h 3) = ((β g : unitarySU p f K 3) : unitaryPSU h 3) :=
  rfl

theorem eq_of_suDescend_eq [Finite K] (h : UnitaryFieldData p f K) (hq2 : 2 < p ^ f)
    {e₁ e₂ : MulAut (unitarySU p f K 3)} (he : suDescend h hq2 e₁ = suDescend h hq2 e₂) :
    e₁ = e₂ := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hK : Nat.card K = (p ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  have hq := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hK le_rfl
    (by
      intro h32
      have := congrArg Prod.snd h32
      simp only at this
      omega)
  have hperf : Group.IsPerfect (⊤ : Subgroup (unitarySU p f K 3)) := by
    have := hq.1.1
    exact Group.IsPerfect.ofSurjective
      (f := (Subgroup.topEquiv (G := unitarySU p f K 3)).symm.toMonoidHom) (MulEquiv.surjective _)
  have hfix := eq_of_mul_inv_mem_center hperf (e₂⁻¹ * e₁ : MulAut _).toMonoidHom fun y _ => by
    have h1 := congrArg (fun φ : MulAut (unitaryPSU h 3) => φ (y : unitaryPSU h 3)) he
    simp only [suDescend_apply] at h1
    have h2 : e₂ ((e₂⁻¹ * e₁) y) = e₁ y := e₂.apply_symm_apply _
    have hw : (((e₂⁻¹ * e₁) y : unitarySU p f K 3) : unitaryPSU h 3) = (y : unitaryPSU h 3) := by
      apply (suDescend h hq2 e₂).injective
      rw [suDescend_apply, suDescend_apply, h2, h1]
    rw [center_unitarySU_three (h := h) hq2, ← ker_unitaryProj, MonoidHom.mem_ker, map_mul,
      map_inv]
    change (((e₂⁻¹ * e₁) y : unitarySU p f K 3) : unitaryPSU h 3) * (y : unitaryPSU h 3)⁻¹ = 1
    rw [hw, mul_inv_cancel]
  ext y
  have := hfix y (Subgroup.mem_top y)
  change e₂⁻¹ (e₁ y) = y at this
  have h2 := congrArg e₂ this
  rw [show e₂ (e₂⁻¹ (e₁ y)) = e₁ y from e₂.apply_symm_apply _] at h2
  rw [h2]

theorem suDescend_suConj (h : UnitaryFieldData p f K) (hq2 : 2 < p ^ f) (A : unitaryIsom3 h) :
    suDescend h hq2 (suConj h A) = psuConj h A := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H g => rfl

theorem suDescend_suField (h : UnitaryFieldData p f K) (hq2 : 2 < p ^ f) (σ : K ≃+* K) :
    suDescend h hq2 (suField h σ) = psuField h σ := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H g => rfl

theorem threePrimeB3_unitarySU_three_all [Finite K]
    (h3 : (3 : K) ≠ 0) (h : UnitaryFieldData p f K) (hq2 : 2 < p ^ f) :
    ThreePrimeB3 (unitarySU p f K 3) := by
  intro β hβ C Y R hC hYC hsn hYp hY3 hRY hRn hRs _
  suffices hY : Y = ⊥ by rw [hY, Subgroup.commutator_bot_right]
  set β' := suDescend h hq2 β with hβ'
  have hβ'3 : β' ^ 3 = 1 := by rw [hβ', ← map_pow, hβ, map_one]
  by_cases hD : β' ∈ (psuConj h).range
  · obtain ⟨A, hA⟩ := hD
    have hβA : β = suConj h A := eq_of_suDescend_eq h hq2 (by rw [suDescend_suConj, hA])
    obtain ⟨-, d, -, hd⟩ := eq_one_of_psuConj_mul_psuField_eq_one (A ^ 3) 1
      (by rw [map_one, mul_one, map_pow, hA, hβ'3])
    have hA3 : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ 3 = (d : K) • 1 := by
      rw [← Units.val_pow_eq_pow_val, ← Subgroup.coe_pow, hd, Matrix.GeneralLinearGroup.coe_scalar,
        Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
    have hfix : ∀ y ∈ Y, (A : GL (Fin 3) K) * (y : GL (Fin 3) K) * (A : GL (Fin 3) K)⁻¹ = y := by
      intro y hy
      have h1 := (hC y).mp (hYC hy)
      rw [hβA] at h1
      have h2 := congrArg (fun z : unitarySU p f K 3 => (z : GL (Fin 3) K)) h1
      simpa only [coe_suConj, Subgroup.coe_inv] using h2
    by_cases hAs : ∃ a : K, ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = a • 1
    · obtain ⟨a, ha⟩ := hAs
      have hCtop : C = ⊤ := by
        rw [eq_top_iff]
        intro z _
        rw [hC z, hβA]
        apply Subtype.ext
        rw [coe_suConj]
        apply Units.ext
        have hcomm : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
            ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
            ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
              ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
          rw [ha, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one]
        rw [Units.val_mul, Units.val_mul, hcomm, mul_assoc, ← Units.val_mul, Subgroup.coe_inv,
          mul_inv_cancel, Units.val_one, mul_one]
      subst hCtop
      have hYsn : Y.IsSubnormal := by
        have := hsn.map (f := (⊤ : Subgroup (unitarySU p f K 3)).subtype)
          (fun z => ⟨⟨z, Subgroup.mem_top z⟩, rfl⟩)
        rwa [Subgroup.subgroupOf_map_subtype, inf_top_eq] at this
      exact eq_bot_of_le_of_isSubnormal_su3 h hq2 hY3 le_rfl le_sup_left hYsn
    · push Not at hAs
      have hY'' := eq_bot_of_commute_glThree_of_pow_three_eq_smul h3 hA3 hAs
        (Y.map (unitarySU p f K 3).subtype) (by
          rintro _ ⟨y, hy, rfl⟩
          change (y : GL (Fin 3) K) * (A : GL (Fin 3) K) = (A : GL (Fin 3) K) * (y : GL (Fin 3) K)
          calc (y : GL (Fin 3) K) * (A : GL (Fin 3) K) =
              (A : GL (Fin 3) K) * (y : GL (Fin 3) K) * (A : GL (Fin 3) K)⁻¹ *
                (A : GL (Fin 3) K) := by rw [hfix y hy]
            _ = (A : GL (Fin 3) K) * (y : GL (Fin 3) K) := by group)
        (by
          have := hYp
          exact Group.IsPerfect.map _)
        (by rwa [Subgroup.card_map_of_injective (unitarySU p f K 3).subtype_injective])
      exact (Subgroup.map_eq_bot_iff_of_injective Y (unitarySU p f K 3).subtype_injective).mp hY''
  · obtain ⟨σ, hσ3, H, hβ'H⟩ := unitary_order_three_field_descent hq2 β' hβ'3 hD
    set τ := suConj h H with hτ
    have hβH : β = τ * suField h σ * τ⁻¹ := eq_of_suDescend_eq h hq2 (by
      rw [map_mul, map_mul, map_inv, hτ, suDescend_suConj, suDescend_suField, ← hβ'H])
    set C₀ : Subgroup (unitarySU p f K 3) := (suField h σ).toMonoidHom.eqLocus (MonoidHom.id _)
      with hC₀
    set Y₀ : Subgroup (unitarySU p f K 3) := Y.map (τ⁻¹ : MulAut (unitarySU p f K 3)).toMonoidHom
      with hY₀
    have hβτ : ∀ z, β z = z ↔ suField h σ (τ⁻¹ z) = τ⁻¹ z := by
      intro z
      rw [hβH, MulAut.mul_apply, MulAut.mul_apply]
      constructor
      · intro h'
        have := congrArg (τ⁻¹ : MulAut (unitarySU p f K 3)) h'
        rwa [show τ⁻¹ (τ (suField h σ (τ⁻¹ z))) = suField h σ (τ⁻¹ z) from
          τ.symm_apply_apply _] at this
      · intro h'
        rw [h']
        exact τ.apply_symm_apply z
    have hY₀C₀ : Y₀ ≤ C₀ := by
      rintro _ ⟨y, hy, rfl⟩
      exact (hβτ y).mp ((hC y).mp (hYC hy))
    have hsn₀ : (Y₀.subgroupOf C₀).IsSubnormal := by
      let ρ : C →* C₀ :=
        ((τ⁻¹ : MulAut (unitarySU p f K 3)).toMonoidHom.comp C.subtype).codRestrict C₀ fun c =>
          (hβτ c).mp ((hC c).mp c.2)
      have hρ : Function.Surjective ρ := by
        rintro ⟨z, hz⟩
        have hτz : τ⁻¹ (τ z) = z := τ.symm_apply_apply z
        refine ⟨⟨τ z, (hC _).mpr ((hβτ _).mpr ?_)⟩, ?_⟩
        · rw [hτz]
          exact hz
        · apply Subtype.ext
          exact hτz
      have hmap : (Y.subgroupOf C).map ρ = Y₀.subgroupOf C₀ := by
        ext ⟨z, hz⟩
        rw [Subgroup.mem_subgroupOf]
        constructor
        · rintro ⟨c, hc, hcz⟩
          exact ⟨c, hc, congrArg Subtype.val hcz⟩
        · rintro ⟨y, hy, rfl⟩
          exact ⟨⟨y, hYC hy⟩, hy, rfl⟩
      rw [← hmap]
      exact hsn.map hρ
    have hY₀3 : ¬ 3 ∣ Nat.card Y₀ := by
      rwa [hY₀, Subgroup.card_map_of_injective
        (f := (τ⁻¹ : MulAut (unitarySU p f K 3)).toMonoidHom) (MulEquiv.injective _)]
    have hY₀p : Group.IsPerfect Y₀ := by
      have := hYp
      exact Group.IsPerfect.map _
    obtain ⟨f₀, hf, hf₀, hcard₀⟩ := exists_card_fixedField_of_orderOf_eq_three h hσ3
    have h₀ : UnitaryFieldData p f₀ (CFSG.GH74.GLS.IVK.fixedField σ) := ⟨h.prime, hf₀, hcard₀⟩
    have hbar := bar_coe_fixedField h hf h₀
    have : Finite (CFSG.GH74.GLS.IVK.fixedField σ) := Subtype.finite
    set ψ := suIncl h h₀ hbar with hψ
    have hψi : Function.Injective ψ := suIncl_injective h h₀ hbar
    have hY₀ψ : Y₀ ≤ ψ.range := fun y hy => (mem_range_suIncl_iff h h₀ hbar y).mpr (hY₀C₀ hy)
    set V := Y₀.comap ψ with hV
    have hVmap : V.map ψ = Y₀ := Subgroup.map_comap_eq_self hY₀ψ
    have hV3 : ¬ 3 ∣ Nat.card V := by
      rw [← Subgroup.card_map_of_injective hψi, hVmap]
      exact hY₀3
    have hVbot : V = ⊥ := by
      by_cases hq₀ : p ^ f₀ = 2
      · refine eq_bot_of_isPerfect_su3_two h₀ hq₀ V ?_ hV3
        have hVe : V ≃* Y₀ :=
          (MonoidHom.ofInjective (f := ψ.comp V.subtype) (hψi.comp V.subtype_injective)).trans
            (MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp, Subgroup.range_subtype, hVmap]))
        have := hY₀p
        exact Group.IsPerfect.ofSurjective (f := hVe.symm.toMonoidHom) hVe.symm.surjective
      · have hq₀2 : 2 < p ^ f₀ := by
          have h1 : 2 ≤ p ^ f₀ := le_trans h.prime.two_le (Nat.le_self_pow (by omega) p)
          omega
        have hsnV : V.IsSubnormal := by
          let θ : unitarySU p f₀ (CFSG.GH74.GLS.IVK.fixedField σ) 3 →* C₀ :=
            ψ.codRestrict C₀ fun s => (mem_range_suIncl_iff h h₀ hbar (ψ s)).mp ⟨s, rfl⟩
          have hcomap : (Y₀.subgroupOf C₀).comap θ = V := by
            ext s
            rfl
          rw [← hcomap]
          exact hsn₀.comap θ
        exact eq_bot_of_le_of_isSubnormal_su3 h₀ hq₀2 hV3 le_rfl le_sup_left hsnV
    have hY₀bot : Y₀ = ⊥ := by rw [← hVmap, hVbot, Subgroup.map_bot]
    exact (Subgroup.map_eq_bot_iff_of_injective Y
      (τ⁻¹ : MulAut (unitarySU p f K 3)).injective).mp hY₀bot

theorem not_suzukiOrder_dvd_216 {a : ℕ} (ha : 1 ≤ a) : ¬ suzukiOrder a ∣ 216 := by
  intro hd
  have haB := le_of_suzukiOrder_dvd (M := 216) (B := 1) (by norm_num) (by norm_num) hd
  obtain rfl : a = 1 := by omega
  exact absurd hd (by decide)

open CFSG.Assembly.RankThreeEven (projSU) in
theorem threePrimeB3_projSU_three_galoisField
    {p e : ℕ} [Fact p.Prime] (hp3 : p ≠ 3) (he : 1 ≤ e) :
    ThreePrimeB3 (projSU 3 p e) := by
  have h : UnitaryFieldData p e (GaloisField p (2 * e)) :=
    ⟨Fact.out, he, GaloisField.card p (2 * e) (by omega)⟩
  obtain ⟨φ⟩ := nonempty_unitaryPSU_mulEquiv_projSU h
  by_cases hq2 : 2 < p ^ e
  · exact threePrimeB3_of_mulEquiv φ.symm
      (threePrimeB3_unitaryPSU_three_all (three_ne_zero_of_charP hp3) h hq2)
  · have hq : p ^ e = 2 :=
      le_antisymm (not_lt.mp hq2)
        (le_trans (Fact.out : p.Prime).two_le (Nat.le_self_pow (by omega) p))
    have hcard : Nat.card (projSU 3 p e) ∣ 216 := by
      have h216 : Nat.card (unitarySU p e (GaloisField p (2 * e)) 3) = 216 := by
        rw [card_unitarySU_three h, hq]
        norm_num
      rw [← Nat.card_congr φ.toEquiv, ← h216]
      exact Subgroup.card_quotient_dvd_card _
    have : Finite (projSU 3 p e) := Nat.finite_of_card_ne_zero (fun h0 => by
      rw [h0] at hcard
      exact absurd hcard (by norm_num))
    exact threePrimeB3_of_suzukiOrder_not_dvd fun a ha hd =>
      not_suzukiOrder_dvd_216 ha (hd.trans hcard)

theorem threePrimeB3_statedSU_three_all
    {K : Type} [Field K] [Finite K] {p n : ℕ} [Fact p.Prime]
    (hp3 : p ≠ 3) (hn : 1 ≤ n) (hK : Nat.card K = (p ^ n) ^ 2) :
    ThreePrimeB3 (CFSG.Assembly.LowTwoRank.StatedSU 3 (p ^ n) K) := by
  have : Fintype K := Fintype.ofFinite K
  have : CharP K p := charP_of_card_eq_prime_pow (f := 2 * n)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul, mul_comm])
  have h : UnitaryFieldData p n K := ⟨Fact.out, hn, by rw [hK, ← pow_mul, mul_comm]⟩
  by_cases hq2 : 2 < p ^ n
  · exact threePrimeB3_unitarySU_three_all (three_ne_zero_of_charP hp3) h hq2
  · have hq : p ^ n = 2 :=
      le_antisymm (not_lt.mp hq2)
        (le_trans (Fact.out : p.Prime).two_le (Nat.le_self_pow (by omega) p))
    have hcard : Nat.card (CFSG.Assembly.LowTwoRank.StatedSU 3 (p ^ n) K) = 216 := by
      rw [show CFSG.Assembly.LowTwoRank.StatedSU 3 (p ^ n) K = unitarySU p n K 3 from rfl,
        card_unitarySU_three h, hq]
      norm_num
    have : Finite (CFSG.Assembly.LowTwoRank.StatedSU 3 (p ^ n) K) :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
    exact threePrimeB3_of_suzukiOrder_not_dvd fun a ha hd =>
      not_suzukiOrder_dvd_216 ha (hcard ▸ hd)

end CFSG.RankThree.PartTwo.Sec6.BThreeCensus
