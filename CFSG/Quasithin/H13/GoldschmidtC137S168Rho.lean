module

public import CFSG.Quasithin.H13.GoldschmidtC137S168Lab
public import CFSG.LocalAnalysis.SeitzReduction.RankOneDegreeEightPerm
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.Open.Defs
public import CFSG.Quasithin.H13.GoldschmidtC137SQFrat
public import CFSG.Quasithin.H13.GoldschmidtC137SQKg
public import CFSG.Quasithin.H13.GoldschmidtC137SQSyl7

public section

namespace CFSG.Quasithin.H13.U3.GC137.SQ.S168

open MulAction CFSG.SeitzReduction.RankOne.DegreeEight

namespace Frame

variable {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (F : Frame S)

@[expose] noncomputable def eEquiv (hcard : Nat.card S = 168) : Option (ZMod 7) ≃ Sylow 7 S :=
  Equiv.ofBijective F.e (F.e_bijective hcard)

@[expose] noncomputable def rho (hcard : Nat.card S = 168) : S →* Equiv.Perm (Option (ZMod 7)) :=
  (F.eEquiv hcard).symm.permCongrHom.toMonoidHom.comp (MulAction.toPermHom S (Sylow 7 S))

theorem rho_eq_iff (hcard : Nat.card S = 168) (g : S) (z w : Option (ZMod 7)) :
    F.rho hcard g z = w ↔ g • F.eEquiv hcard z = F.eEquiv hcard w := by
  change (F.eEquiv hcard).symm (g • F.eEquiv hcard z) = w ↔ _
  rw [Equiv.symm_apply_eq]

theorem rho_injective (hcard : Nat.card S = 168) : Function.Injective (F.rho hcard) := by
  have hker : (F.rho hcard).ker = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (F.rho hcard).ker with h | h
    · exact h
    · exfalso
      have hP : Subgroup.normalizer (F.P : Set S) = ⊤ := by
        rw [eq_top_iff]
        intro g _
        have hg : F.rho hcard g = 1 :=
          MonoidHom.mem_ker.1 (h ▸ Subgroup.mem_top g)
        have := (F.rho_eq_iff hcard g none none).1 (by rw [hg]; rfl)
        exact Sylow.smul_eq_iff_mem_normalizer.1 this
      have h21 := card_normalizer hcard F.P
      rw [hP, Subgroup.card_top, hcard] at h21
      omega
  exact (MonoidHom.ker_eq_bot_iff _).1 hker

theorem rho_x (hcard : Nat.card S = 168) : F.rho hcard F.x = shift := by
  refine Equiv.ext fun z => ?_
  cases z with
  | none =>
    rw [shift_none]
    refine (F.rho_eq_iff hcard F.x none none).2 ?_
    exact Sylow.smul_eq_iff_mem_normalizer.2 (Subgroup.le_normalizer F.hx)
  | some i =>
    rw [shift_some]
    exact (F.rho_eq_iff hcard F.x (some i) (some (i + 1))).2 (F.x_smul_pt i)

theorem rho_y (hcard : Nat.card S = 168) : F.rho hcard F.y = dbl := by
  refine Equiv.ext fun z => ?_
  cases z with
  | none =>
    rw [dbl_none]
    refine (F.rho_eq_iff hcard F.y none none).2 ?_
    exact Sylow.smul_eq_iff_mem_normalizer.2 F.hy
  | some i =>
    rw [dbl_some]
    exact (F.rho_eq_iff hcard F.y (some i) (some (2 * i))).2 (F.y_smul_pt i)

theorem rho_none_iff (hcard : Nat.card S = 168) (g : S) :
    F.rho hcard g none = none ↔ g ∈ Subgroup.normalizer (F.P : Set S) := by
  rw [F.rho_eq_iff hcard g none none]
  exact Sylow.smul_eq_iff_mem_normalizer

omit [Finite S] [IsSimpleGroup S] in
theorem pow_smul_pt (n : ℕ) (d : ZMod 7) : F.x ^ n • F.pt d = F.pt (n + d) := by
  conv_lhs => unfold pt
  rw [← mul_smul, ← pow_add, F.pow_smul_eq]
  have : ((n + d.val : ℕ) : ZMod 7) = n + d := by push_cast [ZMod.natCast_zmod_val]; rfl
  rw [this]

omit [IsSimpleGroup S] in
theorem zpowers_x (hcard : Nat.card S = 168) : Subgroup.zpowers F.x = (F.P : Subgroup S) :=
  Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 F.hx)
    (by rw [Nat.card_zpowers, F.hxo, card_sylow hcard F.P])

omit [IsSimpleGroup S] in
theorem exists_conj_pow (hcard : Nat.card S = 168) {g : S}
    (hg : g ∈ Subgroup.normalizer (F.P : Set S)) : ∃ m : ℕ, g * F.x * g⁻¹ = F.x ^ m := by
  have hconj : g * F.x * g⁻¹ ∈ Subgroup.zpowers F.x := by
    rw [F.zpowers_x hcard]
    exact (Subgroup.mem_normalizer_iff.1 hg F.x).1 F.hx
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hconj
  refine ⟨(k % 7).toNat, ?_⟩
  have hnn : (0 : ℤ) ≤ k % 7 := Int.emod_nonneg k (by norm_num)
  rw [← hk, ← zpow_mod_orderOf, F.hxo, ← zpow_natCast, Int.toNat_of_nonneg hnn]
  rfl

theorem rho_isAffine (hcard : Nat.card S = 168) {g : S}
    (hg : g ∈ Subgroup.normalizer (F.P : Set S)) : IsAffine (F.rho hcard g) := by
  refine ⟨(F.rho_none_iff hcard g).2 hg, ?_⟩
  obtain ⟨d, hd⟩ : ∃ d : ZMod 7, g • F.Q₀ = F.pt d := by
    obtain ⟨z, hz⟩ := (F.eEquiv hcard).surjective (g • F.Q₀)
    cases z with
    | none =>
      exfalso
      apply F.hQP
      have hinv : g⁻¹ • F.P = F.P := Sylow.smul_eq_iff_mem_normalizer.2 (inv_mem hg)
      have h1 : F.P = g • F.Q₀ := hz
      calc F.Q₀ = g⁻¹ • (g • F.Q₀) := (inv_smul_smul g F.Q₀).symm
        _ = g⁻¹ • F.P := by rw [h1]
        _ = F.P := hinv
    | some d => exact ⟨d, hz.symm⟩
  obtain ⟨m, hm⟩ := F.exists_conj_pow hcard hg
  refine ⟨(m : ZMod 7), d, ?_, ?_⟩
  · have hg21 : g ^ 21 = 1 := by
      have hdvd : orderOf g ∣ 21 := by
        have := Subgroup.orderOf_dvd_natCard (Subgroup.normalizer (F.P : Set S)) hg
        rwa [card_normalizer hcard F.P] at this
      exact orderOf_dvd_iff_pow_eq_one.1 hdvd
    have h21 := conj_pow_nat hm 21
    rw [hg21, one_mul, inv_one, mul_one] at h21
    have h1 : F.x ^ 1 = F.x ^ (m ^ 21) := by rw [pow_one]; exact h21
    have h2 := (pow_eq_pow_iff_modEq).1 h1
    rw [F.hxo] at h2
    have h3 : ((m ^ 21 : ℕ) : ZMod 7) = 1 := by
      have := (ZMod.natCast_eq_natCast_iff _ _ 7).2 h2.symm
      simpa using this
    push_cast at h3
    exact (by decide : ∀ c : ZMod 7, c ^ 21 = 1 → c ^ 3 = 1) _ h3
  · intro z
    refine (F.rho_eq_iff hcard g (some z) (some (m * z + d))).2 ?_
    change g • F.pt z = F.pt (m * z + d)
    have h1 : g * F.x ^ z.val = (F.x ^ (m * z.val)) * g := by
      have h2 : g * F.x ^ z.val * g⁻¹ = F.x ^ (m * z.val) := by
        rw [← conj_pow, hm, ← pow_mul]
      rw [← h2]
      group
    have h3 : g • F.pt z = F.x ^ (m * z.val) • F.pt d := by
      conv_lhs => unfold pt
      rw [← mul_smul, h1, mul_smul, hd]
    rw [h3, F.pow_smul_pt]
    congr 1
    push_cast [ZMod.natCast_zmod_val]
    rfl

theorem exists_swap (hcard : Nat.card S = 168) :
    ∃ g : S, F.rho hcard g none = some 0 ∧ F.rho hcard g (some 0) = none := by
  obtain ⟨g₁, hg₁⟩ := exists_smul_eq S F.P F.Q₀
  obtain ⟨z, hz⟩ := (F.eEquiv hcard).surjective (g₁⁻¹ • F.P)
  cases z with
  | none =>
    exfalso
    apply F.hQP
    have h1 : F.P = g₁⁻¹ • F.P := hz
    calc F.Q₀ = g₁ • F.P := hg₁.symm
      _ = g₁ • (g₁⁻¹ • F.P) := by rw [← h1]
      _ = F.P := smul_inv_smul g₁ F.P
  | some j =>
    refine ⟨g₁ * F.x ^ j.val, ?_, ?_⟩
    · rw [F.rho_eq_iff hcard]
      have hxP : F.x ^ j.val • F.P = F.P :=
        Sylow.smul_eq_iff_mem_normalizer.2 (Subgroup.pow_mem _ (Subgroup.le_normalizer F.hx) _)
      change (g₁ * F.x ^ j.val) • F.P = F.pt 0
      rw [mul_smul, hxP, hg₁, F.pt_zero]
    · rw [F.rho_eq_iff hcard]
      change (g₁ * F.x ^ j.val) • F.pt 0 = F.P
      have hj : F.pt j = g₁⁻¹ • F.P := hz
      rw [mul_smul, F.pt_zero]
      change g₁ • F.pt j = F.P
      rw [hj]
      exact smul_inv_smul g₁ F.P

end Frame

end CFSG.Quasithin.H13.U3.GC137.SQ.S168
