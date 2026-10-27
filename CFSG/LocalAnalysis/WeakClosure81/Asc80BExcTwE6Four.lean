module

public import CFSG.LocalAnalysis.WeakClosure81.Asc80BExcTwE6Outer
import CFSG.LocalAnalysis.WeakClosure81.Asc80BExcC4Native
import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6InF4Cont
import CFSG.GH74.GLS.Stage1.Main.BrTwoClassE

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.Burgoyne.E2 (twE6SignAut)
open CFSG.ComponentClassification.Burgoyne.E2 (twE6SignU)

private theorem fixed_of_generators_twE6 {G : Type} [Group G] [Finite G] [Finite (MulAut G)]
    (E : Subgroup (MulAut G))
    {x : MulAut G} {h : G} (hxE : x ∈ E) (hhE : MulAut.conj h ∈ E)
    (hx2 : x * x = 1) (hconj2 : MulAut.conj h * MulAut.conj h = 1)
    (hcomm : x * MulAut.conj h = MulAut.conj h * x)
    (hxne : x ≠ 1) (hhne : MulAut.conj h ≠ 1) (hne : MulAut.conj h ≠ x)
    (h4 : Nat.card E = 4) {a : G} (hfixx : x a = a) (hfixh : MulAut.conj h a = a) :
    ∀ e ∈ E, e a = a := by
  obtain ⟨hmem, -, -, hcard⟩ :=
    CFSG.GH74.GLS.Stage1.Main.four_of_invols (u₁ := MulAut.conj h) (u₂ := x)
      hconj2 hx2 hcomm.symm hhne hxne hne
  have hEeq : zpowers (MulAut.conj h) ⊔ zpowers x = E :=
    Subgroup.eq_of_le_of_card_ge
      (sup_le (zpowers_le.2 hhE) (zpowers_le.2 hxE))
      (by rw [hcard, h4])
  intro e he
  rw [← hEeq] at he
  rcases hmem e he with rfl | rfl | rfl | rfl
  · rfl
  · exact hfixh
  · exact hfixx
  · rw [MulAut.mul_apply, hfixx, hfixh]


theorem exists_fixed_rElement_four_twistedE6 {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (q : ℕ) (hσ : ∀ c, σ c = c ^ q) (hK : Nat.card K = q ^ 2) (hK2 : ringChar K ≠ 2)
    (E : Subgroup (MulAut ↥(twistedE6RootGroup K σ))) (hE : CFSG.Open.IsElemAbelian 2 E)
    (h4 : Nat.card E = 4) :
    ∃ y : ↥(twistedE6RootGroup K σ), y ≠ 1 ∧ (∃ n : ℕ, y ^ (ringChar K ^ n) = 1) ∧
      ∀ e ∈ E, e y = y := by
  classical
  rcases exists_fixed_rElement_four_twistedE6_or_signedGraph σ q hσ hK hK2 E hE h4 with
    h | ⟨x, h, δ, δ', hxE, hhE, hh1, hh2, hxh, hδ, hδ'⟩
  · exact h
  · have hK1 : 1 < Nat.card K := Finite.one_lt_card
    have hq2 : 2 ≤ q := by
      by_contra h
      push Not at h
      interval_cases q <;> norm_num at hK <;> omega
    obtain ⟨hpr, f, hf1, hqf⟩ :=
      CFSG.LieType.SeitzGeneration.ExcHighThree.exists_pow_ringChar_of_card_sq K q hK hq2
    set p := ringChar K with hp_def
    have hp2 : p ≠ 2 := hK2
    have hK' : Nat.card K = (p ^ f) ^ 2 := by rw [hK, hqf]
    have hσ' : ∀ c, σ c = c ^ (p ^ f) := fun c => by rw [hσ c, hqf]
    obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -, -, -, -, -⟩, -, -, hcenter, -, -⟩ :=
      twisted_E6_odd_exact_automorphism_normal_form hpr hp2 hf1 K hK' σ hσ'
    have hσne : σ ≠ 1 := by
      intro hσid
      let : Fintype K := Fintype.ofFinite K
      have hq1 : 1 ≤ q := by omega
      have hone : ∀ x : Kˣ, x ^ (q - 1) = 1 := by
        intro x
        have hxq : x ^ q = x := by
          apply Units.ext
          have h2 := hσ (x : K)
          rw [hσid] at h2
          simpa using h2.symm
        have h3 : x ^ (q - 1) * x = x := by
          rw [← pow_succ, Nat.sub_add_cancel hq1]
          exact hxq
        have h4' := congrArg (fun z : Kˣ => z * x⁻¹) h3
        simpa [mul_assoc] using h4'
      have hdvd : Fintype.card K - 1 ∣ q - 1 :=
        (FiniteField.forall_pow_eq_one_iff K (q - 1)).1 hone
      have hcard : Fintype.card K = q ^ 2 := by
        rw [← Nat.card_eq_fintype_card, hK]
      rw [hcard] at hdvd
      have hle : q ^ 2 - 1 ≤ q - 1 := Nat.le_of_dvd (by omega) hdvd
      have hsq : q ^ 2 ≤ q := by
        have h1 : q ^ 2 - 1 + 1 ≤ q - 1 + 1 := Nat.add_le_add_right hle 1
        rw [Nat.sub_add_cancel (by nlinarith : 1 ≤ q ^ 2), Nat.sub_add_cancel hq1] at h1
        exact h1
      nlinarith
    have hα2ne : twE6SignAut σ ≠ 1 := by
      intro hα1
      have hΘα : Θ (twE6SignAut σ) = σ :=
        hΘ (twE6SignAut σ) 1 (twE6SignU σ) σ (by rw [twE6SignAut, map_one, one_mul])
      rw [hα1, map_one] at hΘα
      exact hσne hΘα.symm
    have hh'2 : (δ h) ^ 2 = 1 := by rw [← map_pow, hh2, map_one]
    have hαh' : twE6SignAut σ (δ h) = δ h := by
      have h1 : (δ * x * δ⁻¹) (δ h) = δ h := by
        simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply, hxh]
      rwa [hδ] at h1
    obtain ⟨u, hu1, ⟨n, hun⟩, hucomm, huσ⟩ :=
      exists_rElement_fixed_twE6SignAut_inv σ q hσ hK hK2 (δ h) hh'2 hαh'
    have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
    have : Finite ↥(twistedE6RootGroup K σ) := Subtype.finite
    have : Finite (MulAut ↥(twistedE6RootGroup K σ)) :=
      Finite.of_injective (fun e : MulAut ↥(twistedE6RootGroup K σ) => (e : _ → _))
        DFunLike.coe_injective
    have hE2 : ∀ e ∈ E, e ^ 2 = 1 := hE.2
    have hx2 : x * x = 1 := by rw [← sq]; exact hE2 x hxE
    have hconj2 : MulAut.conj h * MulAut.conj h = 1 := by
      rw [← sq, ← map_pow, hh2, map_one]
    have hcomm : x * MulAut.conj h = MulAut.conj h * x :=
      congrArg Subtype.val (hE.1.is_comm.comm (⟨x, hxE⟩ : E) (⟨MulAut.conj h, hhE⟩ : E))
    have hx1 : x ≠ 1 := by
      intro hxeq
      apply hα2ne
      calc twE6SignAut σ = δ * x * δ⁻¹ := hδ.symm
        _ = δ * 1 * δ⁻¹ := by rw [hxeq]
        _ = 1 := by group
    have hch1 : MulAut.conj h ≠ 1 := by
      intro hce
      apply hh1
      have hcZ : h ∈ Subgroup.center ↥(twistedE6RootGroup K σ) := by
        rw [Subgroup.mem_center_iff]
        intro g
        have h1 : h * g * h⁻¹ = g := by
          have h2 := congrArg (fun φ : MulAut ↥(twistedE6RootGroup K σ) => φ g) hce
          simpa only [MulAut.conj_apply, MulAut.one_apply] using h2
        calc g * h = h * g * h⁻¹ * h := by rw [h1]
          _ = h * g := by group
      rwa [hcenter, Subgroup.mem_bot] at hcZ
    have hne : MulAut.conj h ≠ x := by
      intro hxe
      apply hα2ne
      have h2 : x * MulAut.conj h = 1 := by rw [← hxe, hconj2]
      calc twE6SignAut σ = δ' * (x * MulAut.conj h) * δ'⁻¹ := hδ'.symm
        _ = δ' * 1 * δ'⁻¹ := by rw [h2]
        _ = 1 := by group
    have hy1 : (δ⁻¹ u : ↥(twistedE6RootGroup K σ)) ≠ 1 := by
      intro hc
      apply hu1
      have h1 := congrArg δ hc
      rwa [MulAut.apply_inv_self, map_one] at h1
    have hyn : ∃ n : ℕ, (δ⁻¹ u : ↥(twistedE6RootGroup K σ)) ^ (ringChar K ^ n) = 1 :=
      ⟨n, by rw [← map_pow, hun, map_one]⟩
    have hxy : x (δ⁻¹ u) = δ⁻¹ u := by
      apply δ.injective
      rw [MulAut.apply_inv_self]
      have h1 : (δ * x * δ⁻¹) u = u := by rw [hδ]; exact huσ
      simpa only [MulAut.mul_apply, MulAut.inv_apply] using h1
    have hhy : MulAut.conj h (δ⁻¹ u) = δ⁻¹ u := by
      have hcommh : δ⁻¹ u * h = h * δ⁻¹ u := by
        have h1 := congrArg δ.symm hucomm.eq
        simpa only [map_mul, MulEquiv.symm_apply_apply, MulAut.inv_apply] using h1
      rw [MulAut.conj_apply, ← hcommh, mul_inv_cancel_right]
    exact ⟨δ⁻¹ u, hy1, hyn, fixed_of_generators_twE6 E hxE hhE hx2 hconj2 hcomm hx1 hch1
      hne h4 hxy hhy⟩

theorem exists_normalized_rSubgroup_four_twistedE6 {K : Type} [Field K] [Finite K]
    (σ : K ≃+* K) (q : ℕ) (hσ : ∀ c, σ c = c ^ q) (hK : Nat.card K = q ^ 2)
    (hK2 : ringChar K ≠ 2) (E : Subgroup (MulAut ↥(twistedE6RootGroup K σ)))
    (hE : CFSG.Open.IsElemAbelian 2 E) (h4 : Nat.card E = 4) :
    ∃ R : Subgroup ↥(twistedE6RootGroup K σ), R ≠ ⊥ ∧ IsPGroup (ringChar K) R ∧
      ∀ e ∈ E, R.map e.toMonoidHom = R := by
  obtain ⟨y, hy1, ⟨n, hyn⟩, hyE⟩ :=
    exists_fixed_rElement_four_twistedE6 σ q hσ hK hK2 E hE h4
  refine ⟨zpowers y, fun h => hy1 ?_, ?_, fun e he => ?_⟩
  · have hmem : y ∈ zpowers y := mem_zpowers y
    rwa [h, Subgroup.mem_bot] at hmem
  · rintro ⟨g, hg⟩
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hg
    refine ⟨n, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hyn, one_zpow]
  · rw [MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, hyE e he]

end CFSG.LocalAnalysis.WeakClosure81
