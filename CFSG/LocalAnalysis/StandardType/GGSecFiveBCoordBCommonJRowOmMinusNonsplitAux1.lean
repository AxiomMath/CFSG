module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJNativeConj
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorus
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.GroupTheory.SupCommute
import CFSG.GroupTheory.WeirSylow.OrthogonalOrders
import CFSG.LocalAnalysis.GLTheoremA.CatA.T173UniRank
import CFSG.LocalAnalysis.StandardType.GGTableBOrthogonalBasic
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentSplit

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace CommonJOmMinusNonsplit

@[expose] def GGOmMinusNonsplitSignedNormalizer {K : Type} [Field K] {p m : ℕ} {b c : K}
    (τ : (Fin m → Multiplicative (ZMod p)) →* OrthRest.RMinus K m b c) : Prop :=
  ∀ g : OrthRest.RMinus K m b c, (∀ s ∈ τ.range, g * s * g⁻¹ ∈ τ.range) →
    ∃ u : (Fin m → Multiplicative (ZMod p)) → (Fin m → Multiplicative (ZMod p)),
      SpCoord.IsSignedPerm u ∧ ∀ f, g * τ f * g⁻¹ = τ (u f)

theorem ggCommonJRowOmMinusNonsplit_sc {K : Type} [Field K] [Finite K] {p m f : ℕ}
    (hK : Nat.card K = 2 ^ f) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ f + 1)
    (hm : 3 ≤ m) (hmo : Odd m) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {T : Subgroup (OrthRest.RMinus K m b c)} (hT : IsElemAbelian p T)
    (hcard : Nat.card T = p ^ m) :
    ∀ g : OrthRest.RMinus K m b c, (∀ x ∈ T, g * x = x * g) → g ^ p = 1 → g ∈ T := by
  classical
  haveI : CharP K 2 := by
    haveI := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  haveI : Fact p.Prime := ⟨hp⟩
  intro g hgc hgp
  by_contra hgT
  have hg1 : g ≠ 1 := fun h1 => hgT (h1 ▸ T.one_mem)
  have hgord : orderOf g = p := orderOf_eq_prime hgp hg1
  have hcommT : ∀ a ∈ T, Commute a g := fun a ha => (hgc a ha).symm
  have hcomm : ∀ a ∈ T, ∀ b ∈ Subgroup.zpowers g, Commute a b := by
    intro a ha b hb
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb
    rw [← hk]
    exact (hcommT a ha).zpow_right k
  have hS : Nat.card (Subgroup.zpowers g) = p := by rw [Nat.card_zpowers, hgord]
  have hdisj : T ⊓ Subgroup.zpowers g = ⊥ := by
    have hdvd : Nat.card (T ⊓ Subgroup.zpowers g : Subgroup _) ∣ p := by
      have h1 := Subgroup.card_dvd_of_le
        (inf_le_right : T ⊓ Subgroup.zpowers g ≤ Subgroup.zpowers g)
      rwa [hS] at h1
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have hEq : T ⊓ Subgroup.zpowers g = Subgroup.zpowers g :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hS, h1])
      have hgmem : g ∈ T ⊓ Subgroup.zpowers g := by
        rw [hEq]
        exact Subgroup.mem_zpowers g
      exact hgT hgmem.1
  have hBea : IsElemAbelian p (T ⊔ Subgroup.zpowers g) :=
    CFSG.Open.IsElemAbelian.sup_of_commute hT (CFSG.Open.isElemAbelian_zpowers hgp)
      fun a ha b hb => (hcomm a ha b hb).eq
  have hBcard : Nat.card ↥(T ⊔ Subgroup.zpowers g) = p ^ (m + 1) := by
    rw [CFSG.card_sup_eq_mul_of_commute T (Subgroup.zpowers g) hcomm hdisj, hcard, hS,
      pow_succ]
  set E : Subgroup ↥(CFSG.RankThree.Classical2.orthDerived (TableBOrth.qMinusForm K m b c)) :=
    (T ⊔ Subgroup.zpowers g).map (OrthTorus.rMinusEquiv K m b c).toMonoidHom with hEdef
  have hEea : IsElemAbelian p E := by
    rw [hEdef]
    exact CFSG.Open.IsElemAbelian.map hBea _
  have hEcard : Nat.card E = p ^ (m + 1) := by
    rw [hEdef, Subgroup.card_map_of_injective (OrthTorus.rMinusEquiv K m b c).injective,
      hBcard]
  have hdim : Module.finrank K (LargeEvenMinusIdx m → K) = 2 * (m + 1) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum,
      Fintype.card_fin, Fintype.card_fin]
    ring
  have hnotplus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType (TableBOrth.qMinusForm K m b c) := by
    intro hp'
    exact CFSG.GroupTheory.WeirSylow.not_isPlusType_quadMinus (n := m + 1) (by omega) hirr
      ((CFSG.GroupTheory.WeirSylow.isPlusType_congr (TableBOrth.qMinusIsometry m b c)).mp hp')
  have htype : CFSG.GroupTheory.WeirSylow.IsPlusType (TableBOrth.qMinusForm K m b c) ↔
      Odd (m + 1) :=
    ⟨fun h => absurd h hnotplus, fun ho => absurd ho (Nat.not_odd_iff_even.2 hmo.add_one)⟩
  have hpq' : p ∣ Nat.card K + 1 := by rw [hK]; exact hpq
  have hle := CFSG.LocalAnalysis.GLTheoremA.T173U.card_le_pow_pred_of_isElemAbelian_of_type
    (F := K) (V := LargeEvenMinusIdx m → K) (Q := TableBOrth.qMinusForm K m b c) (p := p)
    (n := m + 1) (TableBOrth.nondegenerate_qMinusForm m hirr) hdim htype hp hp2 hpq' hEea
  rw [hEcard] at hle
  have hle' : p ^ (m + 1) ≤ p ^ m := by simpa using hle
  have := (Nat.pow_le_pow_iff_right hp.one_lt).mp hle'
  omega

theorem ggCommonJRowOmMinusNonsplit_compareTorus {K : Type} [Field K] [Finite K] {p m : ℕ}
    {b c : K} {τ τ₀ : (Fin m → Multiplicative (ZMod p)) →* OrthRest.RMinus K m b c}
    (hτ : Function.Injective τ) (hτ₀ : Function.Injective τ₀) (hrange : τ.range = τ₀.range)
    (hsgn : ∀ i : Fin m, ∃ w : OrthRest.RMinus K m b c,
      ∀ f, w * τ f * w⁻¹ = τ (SpCoord.sgnAut i f))
    (hperm : ∀ σ : Equiv.Perm (Fin m), ∃ w : OrthRest.RMinus K m b c,
      ∀ f, w * τ f * w⁻¹ = τ (SpCoord.permAut σ f))
    (hsign₀ : GGOmMinusNonsplitSignedNormalizer τ₀) :
    ∃ φ : MulAut (Fin m → Multiplicative (ZMod p)),
      (∀ f, τ f = τ₀ (φ f)) ∧
      ∀ u : MulAut (Fin m → Multiplicative (ZMod p)),
        SpCoord.IsSignedPerm ⇑u → SpCoord.IsSignedPerm ⇑(φ * u * φ⁻¹) := by
  classical
  let eτ : (Fin m → Multiplicative (ZMod p)) ≃* ↥τ.range := MonoidHom.ofInjective hτ
  let eτ₀ : (Fin m → Multiplicative (ZMod p)) ≃* ↥τ₀.range := MonoidHom.ofInjective hτ₀
  let φ : MulAut (Fin m → Multiplicative (ZMod p)) :=
    eτ.trans ((MulEquiv.subgroupCongr hrange).trans eτ₀.symm)
  have hφ : ∀ f, τ f = τ₀ (φ f) := by
    intro f
    change τ f = τ₀ (eτ₀.symm ((MulEquiv.subgroupCongr hrange) (eτ f)))
    rw [MonoidHom.apply_ofInjective_symm, MulEquiv.subgroupCongr_apply]
    exact (MonoidHom.ofInjective_apply hτ).symm
  haveI : Finite ↥τ.range := Finite.of_injective (Subtype.val) Subtype.val_injective
  let H : Subgroup (MulAut (Fin m → Multiplicative (ZMod p))) :=
    { carrier := {u | ∃ w : OrthRest.RMinus K m b c,
          (∀ s ∈ τ.range, w * s * w⁻¹ ∈ τ.range) ∧ ∀ f, w * τ f * w⁻¹ = τ (u f)}
      one_mem' := ⟨1, by intro s hs; simpa using hs, by intro f; simp⟩
      mul_mem' := by
        rintro u₁ u₂ ⟨w₁, hn₁, h₁⟩ ⟨w₂, hn₂, h₂⟩
        refine ⟨w₁ * w₂, ?_, ?_⟩
        · intro s hs
          rw [mul_inv_rev]
          simpa only [mul_assoc] using hn₁ _ (hn₂ s hs)
        · intro f
          rw [mul_inv_rev, MulAut.mul_apply]
          calc w₁ * w₂ * τ f * (w₂⁻¹ * w₁⁻¹)
              = w₁ * (w₂ * τ f * w₂⁻¹) * w₁⁻¹ := by group
            _ = w₁ * τ (u₂ f) * w₁⁻¹ := by rw [h₂ f]
            _ = τ (u₁ (u₂ f)) := h₁ _
      inv_mem' := by
        rintro u ⟨w, hn, h⟩
        let f : ↥τ.range → ↥τ.range :=
          fun s => ⟨w * (s : OrthRest.RMinus K m b c) * w⁻¹, hn s s.2⟩
        have hfinj : Function.Injective f := by
          intro s t hst
          have hval : w * (s : OrthRest.RMinus K m b c) * w⁻¹ =
              w * (t : OrthRest.RMinus K m b c) * w⁻¹ := congrArg Subtype.val hst
          exact Subtype.ext (mul_left_cancel (mul_right_cancel hval))
        have hfsurj : Function.Surjective f := Finite.injective_iff_surjective.mp hfinj
        refine ⟨w⁻¹, ?_, ?_⟩
        · intro s hs
          obtain ⟨s', hs'⟩ := hfsurj ⟨s, hs⟩
          have hcoe : w * (s' : OrthRest.RMinus K m b c) * w⁻¹ = s :=
            congrArg Subtype.val hs'
          show w⁻¹ * s * (w⁻¹)⁻¹ ∈ τ.range
          rw [show (w⁻¹)⁻¹ = w by group, ← hcoe]
          rw [show w⁻¹ * (w * (s' : OrthRest.RMinus K m b c) * w⁻¹) * w =
            (s' : OrthRest.RMinus K m b c) by group]
          exact s'.2
        · intro g
          have h2 : w * τ (u⁻¹ g) * w⁻¹ = τ g := by rw [h (u⁻¹ g)]; simp
          show w⁻¹ * τ g * (w⁻¹)⁻¹ = τ (u⁻¹ g)
          rw [show (w⁻¹)⁻¹ = w by group, ← h2]
          group }
  have hsgnH : ∀ i : Fin m, SpCoord.sgnAut i ∈ H := by
    intro i
    obtain ⟨w, hw⟩ := hsgn i
    refine ⟨w, ?_, hw⟩
    intro s hs
    obtain ⟨g, rfl⟩ := hs
    rw [hw g]
    exact ⟨SpCoord.sgnAut i g, rfl⟩
  have hpermH : ∀ a b : Fin m, a ≠ b → SpCoord.permAut (Equiv.swap a b) ∈ H := by
    intro a b _
    obtain ⟨w, hw⟩ := hperm (Equiv.swap a b)
    refine ⟨w, ?_, hw⟩
    intro s hs
    obtain ⟨g, rfl⟩ := hs
    rw [hw g]
    exact ⟨SpCoord.permAut (Equiv.swap a b) g, rfl⟩
  refine ⟨φ, hφ, ?_⟩
  intro u hu
  obtain ⟨w, hn, hw⟩ := SpCoord.mem_of_isSignedPerm hsgnH hpermH hu
  have hn₀ : ∀ s ∈ τ₀.range, w * s * w⁻¹ ∈ τ₀.range := by
    intro s hs
    have hs' : s ∈ τ.range := by rwa [← hrange] at hs
    have h := hn s hs'
    rwa [hrange] at h
  obtain ⟨u', hu', hw'⟩ := hsign₀ w hn₀
  have hEq : ∀ g, u' g = (φ * u * φ⁻¹) g := by
    intro g
    apply hτ₀
    rw [← hw' g]
    have h1 : τ₀ g = τ (φ⁻¹ g) := by rw [hφ (φ⁻¹ g)]; simp
    rw [h1]
    calc w * τ (φ⁻¹ g) * w⁻¹ = τ (u (φ⁻¹ g)) := hw _
      _ = τ₀ (φ (u (φ⁻¹ g))) := hφ _
      _ = τ₀ ((φ * u * φ⁻¹) g) := rfl
  have hcoe : ⇑(φ * u * φ⁻¹) = u' := funext fun g => (hEq g).symm
  rw [hcoe]
  exact hu'

end CommonJOmMinusNonsplit

end CFSG.StandardType

end
