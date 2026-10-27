module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.AltModel
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.OrthModel
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SLModel
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SpModel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Matrix CFSG.Quasithin CFSG.Open
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem s16c13bc_transfer {W : Type} [CommGroup W] {H : Subgroup (MulAut W)} {J : Subgroup W}
    (D : FFModel) (hR : D.Realizes H J ⊥)
    (hγ : ∀ m ∈ D.sec, m ∉ D.ker → ∃ γ : D.Gam, orderOf γ = 3 ∧ D.act γ m = m ∧
      ∃ m' ∈ D.sec, m'⁻¹ * D.act γ m' ∉ D.ker) :
    ∀ w ∈ J, w ≠ 1 → ∃ ψ ∈ H, orderOf ψ = 3 ∧ ψ w = w := by
  intro w hw hw1
  obtain ⟨π, -, -, -, hUinv, -, hsecinv, -, β, hβs, hβk, hβeq⟩ := hR
  let u : ↥J := ⟨w, hw⟩
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β u)
  have hmk : (m : D.Amb) ∉ D.ker := by
    intro hmk
    have h1 : β u = 1 := by
      rw [← hm, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hmk
    have h2 : (u : W) ∈ (⊥ : Subgroup W) := (hβk u).mp h1
    exact hw1 (Subgroup.mem_bot.mp h2)
  obtain ⟨γ, hγ3, hγm, m', hm's, hm'k⟩ := hγ m m.2 hmk
  have hord : orderOf (π γ) ∣ 3 := by
    rw [← hγ3]
    exact orderOf_map_dvd π γ
  have hne : π γ ≠ 1 := by
    intro hπ1
    obtain ⟨v, hv⟩ := hβs (QuotientGroup.mk ⟨m', hm's⟩)
    have hact : D.act γ m' ∈ D.sec := hsecinv γ m' hm's
    have hvv : ((π γ : ↥H) : MulAut W) (v : W) ∈ J := hUinv (π γ) v v.2
    have h := hβeq γ v ⟨m', hm's⟩ hvv hact hv
    have e : (⟨((π γ : ↥H) : MulAut W) (v : W), hvv⟩ : ↥J) = v :=
      Subtype.ext (by
        show ((π γ : ↥H) : MulAut W) (v : W) = (v : W)
        rw [hπ1]
        rfl)
    rw [e, hv] at h
    have h' := QuotientGroup.eq.mp h
    rw [Subgroup.mem_subgroupOf] at h'
    exact hm'k h'
  have hordγ : orderOf (π γ) = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 hord with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) hne
    · exact h3
  have hfixw : ((π γ : ↥H) : MulAut W) w = w := by
    have hwv : ((π γ : ↥H) : MulAut W) (u : W) ∈ J := hUinv (π γ) u u.2
    have hact : D.act γ (m : D.Amb) ∈ D.sec := hsecinv γ m m.2
    have h := hβeq γ u m hwv hact hm.symm
    have e : (⟨D.act γ (m : D.Amb), hact⟩ : ↥D.sec) = m := Subtype.ext hγm
    rw [e, hm] at h
    have h3 : β (⟨_, hwv⟩ * u⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
    have h4 := (hβk _).mp h3
    rw [Subgroup.mem_bot] at h4
    exact mul_inv_eq_one.mp h4
  exact ⟨π γ, (π γ).2, by rw [Subgroup.orderOf_coe]; exact hordγ, hfixw⟩

theorem s16c13bc_fix3_nat {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)} (hΓ : ThreeFixedModel Γ (ι → K))
    {W : Type} [CommGroup W] {H : Subgroup (MulAut W)} {J : Subgroup W}
    (hR : (FFModel.nat Γ).Realizes H J ⊥) :
    ∀ w ∈ J, w ≠ 1 → ∃ ψ ∈ H, orderOf ψ = 3 ∧ ψ w = w := by
  refine s16c13bc_transfer (FFModel.nat Γ) hR ?_
  intro m _ _
  obtain ⟨g, hg3, hgv⟩ := hΓ (Multiplicative.toAdd m)
  have hg1 : g ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hg3
    omega
  have hgv' : ((g : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) *ᵥ Multiplicative.toAdd m =
      Multiplicative.toAdd m := hgv
  refine ⟨g, hg3, ?_, ?_⟩
  · show natAct Γ g m = m
    simp only [natAct, hgv']
    rfl
  · by_contra hcon
    push Not at hcon
    apply hg1
    have hmat : ((g : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) = 1 := by
      apply Matrix.ext_iff_mulVec.mpr
      intro x
      have h1 : (Multiplicative.ofAdd x)⁻¹ * natAct Γ g (Multiplicative.ofAdd x) ∈
          (⊥ : Subgroup (Multiplicative (ι → K))) :=
        hcon (Multiplicative.ofAdd x) (Subgroup.mem_top _)
      rw [Subgroup.mem_bot, inv_mul_eq_one] at h1
      have h2 := congrArg Multiplicative.toAdd h1
      simpa [natAct] using h2.symm
    exact Subtype.ext (Units.ext hmat)

theorem s16c13bc_fix3_alt {W : Type} [CommGroup W] {H : Subgroup (MulAut W)} {J : Subgroup W}
    {n : ℕ} (hn : 5 ≤ n) (hN : AlternatingNatural H J ⊥ n) :
    ∀ w ∈ J, w ≠ 1 → ∃ ψ ∈ H, orderOf ψ = 3 ∧ ψ w = w := by
  refine s16c13bc_transfer (FFModel.altDn n) hN ?_
  intro m _ _
  obtain ⟨g, hg3, hgv⟩ := threeFixedModel_altPerm hn (Multiplicative.toAdd m)
  have hg1 : g ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hg3
    omega
  refine ⟨g, hg3, ?_, ?_⟩
  · show G6.permAct n (g : Equiv.Perm (Fin n)) m = m
    apply Multiplicative.toAdd.injective
    funext i
    exact congrFun hgv i
  · by_contra hcon
    push Not at hcon
    obtain ⟨a, ha⟩ : ∃ a : Fin n, (g : Equiv.Perm (Fin n)) a ≠ a := by
      by_contra h
      push Not at h
      exact hg1 (Subtype.ext (Equiv.ext h))
    obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin n), (g : Equiv.Perm (Fin n)) = σ := ⟨_, rfl⟩
    rw [hσ] at ha
    have hσ3 : σ ^ 3 = 1 := by
      have : g ^ 3 = 1 := hg3 ▸ pow_orderOf_eq_one g
      rw [← hσ]
      exact congrArg Subtype.val this
    have h3a : σ (σ (σ a)) = a := by
      have := congrArg (fun f : Equiv.Perm (Fin n) => f a) hσ3
      simpa [pow_succ, Equiv.Perm.mul_apply] using this
    obtain ⟨b, hb⟩ : ∃ b, σ a = b := ⟨_, rfl⟩
    obtain ⟨c, hc⟩ : ∃ c, σ b = c := ⟨_, rfl⟩
    have hba : b ≠ a := hb ▸ ha
    have hσc : σ c = a := by rw [← hc, ← hb]; exact h3a
    have hca : c ≠ a := by
      intro h
      rw [h] at hσc
      exact ha hσc
    obtain ⟨d, hda, hdb, hdc⟩ : ∃ d : Fin n, d ≠ a ∧ d ≠ b ∧ d ≠ c := by
      by_contra hcon'
      push Not at hcon'
      have hsub : (Finset.univ : Finset (Fin n)) ⊆ {a, b, c} := by
        intro d _
        by_cases h1 : d = a
        · simp [h1]
        by_cases h2 : d = b
        · simp [h2]
        simp [hcon' d h1 h2]
      have h1 := Finset.card_le_card hsub
      rw [Finset.card_univ, Fintype.card_fin] at h1
      have h2 := Finset.card_le_three (a := a) (b := b) (c := c)
      omega
    have hm'core : Multiplicative.ofAdd ((Pi.single a 1 + Pi.single b 1 : Fin n → ZMod 2)) ∈
        G6.coreMod n := by
      rw [G6.mem_coreMod]
      have hab : (1 : ZMod 2) + 1 = 0 := by decide
      simp [Finset.sum_add_distrib, hab]
    have hmem : (Multiplicative.ofAdd ((Pi.single a 1 + Pi.single b 1 : Fin n → ZMod 2)) :
        G6.PermMod n)⁻¹ * G6.permAct n (g : Equiv.Perm (Fin n))
          (Multiplicative.ofAdd ((Pi.single a 1 + Pi.single b 1 : Fin n → ZMod 2))) ∈
        Subgroup.zpowers (G6.allOnes n) ⊓ G6.coreMod n :=
      hcon _ hm'core
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_inf.mp hmem).1
    have hka := congrArg (fun x : G6.PermMod n => Multiplicative.toAdd x a) hk
    have hkd := congrArg (fun x : G6.PermMod n => Multiplicative.toAdd x d) hk
    rw [hσ] at hka hkd
    have e1 : σ.symm a ≠ a := by
      rw [Ne, Equiv.symm_apply_eq]
      exact fun h => ha h.symm
    have e2 : σ.symm a ≠ b := by
      rw [Ne, Equiv.symm_apply_eq, hc]
      exact fun h => hca h.symm
    have e3 : σ.symm d ≠ a := by
      rw [Ne, Equiv.symm_apply_eq, hb]
      exact fun h => hdb h
    have e4 : σ.symm d ≠ b := by
      rw [Ne, Equiv.symm_apply_eq, hc]
      exact fun h => hdc h
    simp [G6.permAct_apply, G6.allOnes, Pi.single_apply, e1, e2, e3, e4, hba, hda, hdb,
      hba.symm] at hka hkd
    have h01 : (-1 : ZMod 2) = -0 := hka.symm.trans hkd
    revert h01
    decide

theorem s16c13bc_fix3_sl {W : Type} [CommGroup W] {H : Subgroup (MulAut W)} {J : Subgroup W}
    {m a : ℕ} (hm : 3 ≤ m) (hN : BinaryNaturalSL H J ⊥ m a) :
    ∀ w ∈ J, w ≠ 1 → ∃ ψ ∈ H, orderOf ψ = 3 ∧ ψ w = w := by
  obtain ⟨K, hKf, -, -, hR⟩ := hN
  letI := hKf
  exact s16c13bc_fix3_nat (threeFixedModel_statedSL hm) hR

theorem s16c13bc_fix3_sp {W : Type} [CommGroup W] {H : Subgroup (MulAut W)} {J : Subgroup W}
    {n a : ℕ} (hn : 4 ≤ n) (hN : NatSpn H J ⊥ n a) :
    ∀ w ∈ J, w ≠ 1 → ∃ ψ ∈ H, orderOf ψ = 3 ∧ ψ w = w := by
  obtain ⟨-, K, hKf, -, -, hR⟩ := hN
  letI := hKf
  exact s16c13bc_fix3_nat (threeFixedModel_statedSp (by omega)) hR

theorem s16c13bc_fix3_omegaMinus {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    {J : Subgroup W} {n a : ℕ} (hn : 6 ≤ n) (ha : 1 ≤ a) (hN : NatOmegaMinus H J ⊥ n a) :
    ∀ w ∈ J, w ≠ 1 → ∃ ψ ∈ H, orderOf ψ = 3 ∧ ψ w = w := by
  obtain ⟨-, K, hKf, hKfin, b, c, hcard, hbc, hR⟩ := hN
  letI := hKf
  letI := hKfin
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := a)
    (by rw [← Nat.card_eq_fintype_card, hcard])
  exact s16c13bc_fix3_nat (threeFixedModel_statedOmegaMinus (by omega) b c hbc) hR

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
