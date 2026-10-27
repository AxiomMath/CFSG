module

public import CFSG.RankThree.PartTwo.Sec11.LSSolvableProofWeights

public section

namespace CFSG.RankThree.PartTwo.Sec11

namespace LSSolvableProof

open Module
open scoped TensorProduct

@[expose] def IsIrreducibleRep {p : ℕ} {Y V : Type*} [Group Y] [AddCommGroup V]
    [Module (ZMod p) V] (ρ : Y →* (V →ₗ[ZMod p] V)) : Prop :=
  ∀ W : Submodule (ZMod p) V, (∀ y, ∀ v ∈ W, ρ y v ∈ W) → W = ⊥ ∨ W = ⊤

section Irreducible

variable {p : ℕ} [hp : Fact p.Prime] {Y : Type*} [Group Y] [Finite Y]
  {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
  {ρ : Y →* (V →ₗ[ZMod p] V)}

omit [Finite Y] in
theorem eq_bot_of_isPGroup_of_normal (hρ : Function.Injective ρ) (hirr : IsIrreducibleRep ρ)
    [Nontrivial V] (P : Subgroup Y) [P.Normal] (hP : IsPGroup p P) : P = ⊥ := by
  classical
  set W : Submodule (ZMod p) V := ⨅ g : P, LinearMap.ker (ρ g - 1) with hW
  have hmemW : ∀ v, v ∈ W ↔ ∀ g ∈ P, ρ g v = v := by
    intro v
    simp only [hW, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      Module.End.one_apply, sub_eq_zero]
    exact ⟨fun h g hg => h ⟨g, hg⟩, fun h g => h g g.2⟩
  let _ : MulAction P V := MulAction.compHom V (ρ.comp P.subtype)
  have hsmul : ∀ (g : P) (v : V), g • v = ρ g v := fun _ _ => rfl
  have : Finite V := Module.finite_of_finite (ZMod p)
  have hcong := hP.card_modEq_card_fixedPoints V
  have hcardV : Nat.card V = p ^ Module.finrank (ZMod p) V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
  have hpos : 0 < Module.finrank (ZMod p) V := Module.finrank_pos
  have hpV : p ∣ Nat.card V := by
    rw [hcardV]
    exact dvd_pow_self p hpos.ne'
  have hpF : p ∣ Nat.card (MulAction.fixedPoints P V) :=
    (Nat.ModEq.dvd_iff hcong (dvd_refl p)).mp hpV
  have h0 : (0 : V) ∈ MulAction.fixedPoints P V := fun g => by rw [hsmul, map_zero]
  have hF2 : 2 ≤ Nat.card (MulAction.fixedPoints P V) := by
    have : Finite (MulAction.fixedPoints P V) := Subtype.finite
    have hpos' : 0 < Nat.card (MulAction.fixedPoints P V) :=
      Nat.card_pos_iff.mpr ⟨⟨⟨0, h0⟩⟩, inferInstance⟩
    exact le_trans hp.out.two_le (Nat.le_of_dvd hpos' hpF)
  obtain ⟨v, hvF, hv0⟩ : ∃ v ∈ MulAction.fixedPoints P V, v ≠ 0 := by
    by_contra hall
    push Not at hall
    have : Nat.card (MulAction.fixedPoints P V) ≤ 1 := by
      have : Finite (MulAction.fixedPoints P V) := Subtype.finite
      rw [Finite.card_le_one_iff_subsingleton]
      constructor
      intro x y
      apply Subtype.ext
      rw [hall x.1 x.2, hall y.1 y.2]
    omega
  have hvW : v ∈ W := (hmemW v).mpr fun g hg => by rw [← hsmul ⟨g, hg⟩]; exact hvF ⟨g, hg⟩
  have hWinv : ∀ y, ∀ w ∈ W, ρ y w ∈ W := by
    intro y w hw
    rw [hmemW] at hw ⊢
    intro g hg
    have hconj : y⁻¹ * g * y ∈ P := by
      have := (inferInstance : P.Normal).conj_mem g hg y⁻¹
      rwa [inv_inv] at this
    have h1 : ρ g * ρ y = ρ y * ρ (y⁻¹ * g * y) := by
      rw [← map_mul, ← map_mul]
      congr 1
      group
    rw [← Module.End.mul_apply, h1, Module.End.mul_apply, hw _ hconj]
  rcases hirr W hWinv with hbot | htop
  · exfalso
    rw [hbot, Submodule.mem_bot] at hvW
    exact hv0 hvW
  · rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    apply hρ
    rw [map_one]
    apply LinearMap.ext
    intro w
    have hw : w ∈ W := by rw [htop]; exact Submodule.mem_top
    rw [Module.End.one_apply]
    exact (hmemW w).mp hw g hg

theorem not_dvd_card_of_comm_of_normal (hρ : Function.Injective ρ) (hirr : IsIrreducibleRep ρ)
    [Nontrivial V] (A : Subgroup Y) [A.Normal] (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) :
    ¬ p ∣ Nat.card A := by
  intro hdvd
  let Ap : Subgroup Y :=
    { carrier := {a | a ∈ A ∧ a ^ p = 1}
      one_mem' := ⟨A.one_mem, one_pow p⟩
      mul_mem' := fun {a b} ha hb => ⟨A.mul_mem ha.1 hb.1, by
        rw [(show Commute a b from hA a ha.1 b hb.1).mul_pow, ha.2, hb.2, one_mul]⟩
      inv_mem' := fun {a} ha => ⟨A.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  have hApN : Ap.Normal := ⟨fun a ha g => ⟨(inferInstance : A.Normal).conj_mem a ha.1 g, by
    rw [conj_pow, ha.2, mul_one, mul_inv_cancel]⟩⟩
  have hApP : IsPGroup p Ap := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact x.2.2)⟩
  have hbot := eq_bot_of_isPGroup_of_normal hρ hirr Ap hApP
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := A) p hdvd
  have haAp : (a : Y) ∈ Ap := ⟨a.2, by
    rw [← Subgroup.coe_pow, ← ha, pow_orderOf_eq_one, Subgroup.coe_one]⟩
  rw [hbot, Subgroup.mem_bot] at haAp
  have : a = 1 := Subtype.ext haAp
  rw [this, orderOf_one] at ha
  exact hp.out.one_lt.ne ha

omit [Finite Y] [Module.Finite (ZMod p) V] in
theorem ker_sub_one_eq_bot_of_mem_center (hρ : Function.Injective ρ)
    (hirr : IsIrreducibleRep ρ) {z : Y} (hz : z ∈ Subgroup.center Y) (hz1 : z ≠ 1) :
    LinearMap.ker (ρ z - 1) = ⊥ := by
  have hinv : ∀ y, ∀ v ∈ LinearMap.ker (ρ z - 1), ρ y v ∈ LinearMap.ker (ρ z - 1) := by
    intro y v hv
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hv ⊢
    have h1 : ρ z * ρ y = ρ y * ρ z := by
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz y]
    rw [← Module.End.mul_apply, h1, Module.End.mul_apply, hv]
  rcases hirr _ hinv with h | h
  · exact h
  · exfalso
    apply hz1
    apply hρ
    rw [map_one]
    have h2 : ρ z - 1 = 0 := LinearMap.ker_eq_top.mp h
    exact sub_eq_zero.mp h2

theorem le_center_of_comm_of_normal (hρ : Function.Injective ρ) (hirr : IsIrreducibleRep ρ)
    [Nontrivial V] (hdim : Module.finrank (ZMod p) V ≤ 6)
    (hsmall : ∀ J : Subgroup Y, J.Normal → J.index ≤ 720 → J = ⊤)
    (A : Subgroup Y) [A.Normal] (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) :
    A ≤ Subgroup.center Y := by
  classical
  set L := AlgebraicClosure (ZMod p)
  set σ : Y →* Module.End L (L ⊗[ZMod p] V) := CFSG.Theory.Representation.extendScalars L ρ
    with hσdef
  have hσ : Function.Injective σ :=
    (CFSG.Theory.Representation.extendScalars_faithful_iff L ρ).mp hρ
  have hdimL : Module.finrank L (L ⊗[ZMod p] V) ≤ 6 := by
    rw [finrank_baseChange_eq]; exact hdim
  have hnormal : ∀ y : Y, ∀ a ∈ A, y⁻¹ * a * y ∈ A := by
    intro y a ha
    have := (inferInstance : A.Normal).conj_mem a ha y⁻¹
    rwa [inv_inv] at this
  have hstab : ∀ v : L ⊗[ZMod p] V, v ≠ 0 → ∀ χ : Y → L, (∀ a ∈ A, σ a v = χ a • v) →
      ∀ y : Y, ∀ a ∈ A, χ (y⁻¹ * a * y) = χ a := by
    intro v hv0 χ hv
    let S : Subgroup Y :=
      { carrier := {y | ∀ a ∈ A, χ (y⁻¹ * a * y) = χ a}
        one_mem' := fun a _ => by simp
        mul_mem' := fun {y y'} hy hy' a ha => by
          have h1 := hy' _ (hnormal y a ha)
          rw [hy a ha] at h1
          rw [← h1]
          congr 1
          group
        inv_mem' := fun {y} hy a ha => by
          have h1 := hy (y * a * y⁻¹) (by
            have := (inferInstance : A.Normal).conj_mem a ha y
            exact this)
          simp only [inv_inv]
          rw [← h1]
          congr 1
          group }
    have hSmem : ∀ y, y ∈ S ↔ ∀ a ∈ A, χ (y⁻¹ * a * y) = χ a := fun _ => Iff.rfl
    have hindex : S.index ≤ 6 := by
      have h := card_le_finrank_of_weights σ A hA (ι := Y ⧸ S) (fun q => Quotient.out q)
        (fun q a ha => hnormal _ a ha) hv0 hv (fun q₁ q₂ h => by
          rw [← Quotient.out_eq q₁, ← Quotient.out_eq q₂]
          change ((Quotient.out q₁ : Y) : Y ⧸ S) = ((Quotient.out q₂ : Y) : Y ⧸ S)
          rw [QuotientGroup.eq, hSmem]
          intro a ha
          have h1 := h (Quotient.out q₁ * a * (Quotient.out q₁)⁻¹)
            ((inferInstance : A.Normal).conj_mem a ha _)
          have e1 : (Quotient.out q₁)⁻¹ * (Quotient.out q₁ * a * (Quotient.out q₁)⁻¹) *
              Quotient.out q₁ = a := by group
          have e2 : (Quotient.out q₂)⁻¹ * (Quotient.out q₁ * a * (Quotient.out q₁)⁻¹) *
              Quotient.out q₂ = ((Quotient.out q₁)⁻¹ * Quotient.out q₂)⁻¹ * a *
                ((Quotient.out q₁)⁻¹ * Quotient.out q₂) := by group
          rw [e1, e2] at h1
          exact h1.symm)
      rw [Subgroup.index]
      omega
    have hcore : S.normalCore = ⊤ := by
      refine hsmall _ inferInstance (le_trans (Subgroup.index_normalCore_le_factorial_index S) ?_)
      calc Nat.factorial S.index ≤ Nat.factorial 6 := Nat.factorial_le hindex
        _ = 720 := by decide
    have hStop : S = ⊤ := by
      rw [eq_top_iff, ← hcore]
      exact Subgroup.normalCore_le S
    intro y a ha
    have hy : y ∈ S := by rw [hStop]; exact Subgroup.mem_top y
    exact hy a ha
  intro a ha
  rw [Subgroup.mem_center_iff]
  intro y
  set b := y * a * y⁻¹ * a⁻¹ with hb
  have hbA : b ∈ A := A.mul_mem ((inferInstance : A.Normal).conj_mem a ha y) (A.inv_mem ha)
  have hfixb : ∀ v : L ⊗[ZMod p] V, v ≠ 0 → ∀ χ : Y → L, (∀ c ∈ A, σ c v = χ c • v) →
      σ b v = v := by
    intro v hv0 χ hv
    have hyay : y * a * y⁻¹ ∈ A := (inferInstance : A.Normal).conj_mem a ha y
    have h1 : χ (y * a * y⁻¹) = χ a := by
      have := hstab v hv0 χ hv y⁻¹ a ha
      rwa [inv_inv] at this
    have h2 : χ b = 1 := by
      rw [hb, weight_mul σ hv0 hv hyay (A.inv_mem ha), h1, ← weight_mul σ hv0 hv ha (A.inv_mem ha),
        mul_inv_cancel, weight_one σ hv0 hv]
    rw [hv b hbA, h2, one_smul]
  by_contra hne
  have hb1 : b ≠ 1 := by
    intro h1
    apply hne
    have : y * a * y⁻¹ = a := by
      rw [hb] at h1
      exact mul_inv_eq_one.mp h1
    calc y * a = y * a * y⁻¹ * y := by group
      _ = a * y := by rw [this]
  have hσb : σ b - 1 ≠ 0 := by
    intro h0
    apply hb1
    apply hσ
    rw [map_one]
    exact sub_eq_zero.mp h0
  set U := LinearMap.range (σ b - 1) with hU
  have hU0 : U ≠ ⊥ := by
    intro h0
    apply hσb
    exact LinearMap.range_eq_bot.mp h0
  have hcomm : ∀ c d : A, Commute (σ c) (σ d) := fun c d => by
    change σ c * σ d = σ d * σ c
    rw [← map_mul, ← map_mul, hA c c.2 d d.2]
  have hUinv : ∀ c : A, ∀ u ∈ U, σ c u ∈ U := by
    rintro c _ ⟨w, rfl⟩
    refine ⟨σ c w, ?_⟩
    have h1 : σ b * σ c = σ c * σ b := by rw [← map_mul, ← map_mul, hA b hbA c c.2]
    simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub]
    rw [← Module.End.mul_apply, h1, Module.End.mul_apply]
  obtain ⟨w, hwU, hw0, χ, hχ⟩ := exists_common_eigenvector_of_isAlgClosed
    (fun c : A => σ c) hcomm U hUinv hU0
  set χY : Y → L := fun g => if h : g ∈ A then χ ⟨g, h⟩ else 0 with hχY
  have hχY : ∀ c ∈ A, σ c w = χY c • w := by
    intro c hc
    rw [hχY]
    simp only [hc, ↓reduceDIte]
    exact hχ ⟨c, hc⟩
  have hwfix := hfixb w hw0 χY hχY
  have hpA := not_dvd_card_of_comm_of_normal hρ hirr A hA
  have horder : (orderOf b : L) ≠ 0 := by
    intro h0
    rw [CharP.cast_eq_zero_iff L p] at h0
    apply hpA
    have h1 : orderOf (⟨b, hbA⟩ : A) = orderOf b := Subgroup.orderOf_mk b hbA
    exact h0.trans (h1 ▸ orderOf_dvd_natCard (⟨b, hbA⟩ : A))
  have hbe : σ b ^ orderOf b = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
  have hker := ker_inf_range_eq_bot hbe horder
  have hwker : w ∈ LinearMap.ker (σ b - 1) := by
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, hwfix, sub_self]
  have : w ∈ LinearMap.ker (σ b - 1) ⊓ LinearMap.range (σ b - 1) := ⟨hwker, hwU⟩
  rw [hker, Submodule.mem_bot] at this
  exact hw0 this

end Irreducible

end LSSolvableProof

end CFSG.RankThree.PartTwo.Sec11
