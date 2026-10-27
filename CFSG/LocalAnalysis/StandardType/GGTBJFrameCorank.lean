module

public import CFSG.LocalAnalysis.StandardType.GGTBJFrameBs
public import CFSG.LocalAnalysis.StandardType.GGTBJTypeDDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly SpCoord Multiplicative

namespace FrameBs

variable {p r : ℕ}

theorem permAut_swap_fix {S : Finset (Fin r)} {f : Fin r → Multiplicative (ZMod p)}
    (hf : ∀ i ∈ S, f i = 1) {a b : Fin r} (ha : a ∈ S) (hb : b ∈ S) :
    permAut (p := p) (Equiv.swap a b) f = f := by
  funext i
  rw [permAut_apply]
  simp only [Function.comp_apply, Equiv.swap_inv]
  by_cases hia : i = a
  · subst hia
    rw [Equiv.swap_apply_left, hf _ hb, hf _ ha]
  · by_cases hib : i = b
    · subst hib
      rw [Equiv.swap_apply_right, hf _ ha, hf _ hb]
    · rw [Equiv.swap_apply_of_ne_of_ne hia hib]

theorem sgnAut_fix {S : Finset (Fin r)} {f : Fin r → Multiplicative (ZMod p)}
    (hf : ∀ i ∈ S, f i = 1) {a : Fin r} (ha : a ∈ S) : sgnAut (p := p) a f = f := by
  rw [sgnAut_apply, hf a ha]
  funext i
  by_cases hi : i = a
  · subst hi
    simp [hf _ ha]
  · simp [Function.update_of_ne hi]

theorem signedSupportedAut_fix {S : Finset (Fin r)} {f : Fin r → Multiplicative (ZMod p)}
    (hf : ∀ i ∈ S, f i = 1) : ∀ τ ∈ TypeBDatum.signedSupportedAut r p S, τ f = f := by
  intro τ hτ
  have h : TypeBDatum.signedSupportedAut r p S ≤ MulAction.stabilizer (MulAut _) f := by
    unfold TypeBDatum.signedSupportedAut
    rw [Subgroup.closure_le]
    rintro _ (⟨i, hi, rfl⟩ | ⟨a, ha, b, hb, -, rfl⟩)
    · exact sgnAut_fix hf hi
    · exact permAut_swap_fix hf ha hb
  exact h hτ

theorem evenSignedSupportedAut_fix {S : Finset (Fin r)} {f : Fin r → Multiplicative (ZMod p)}
    (hf : ∀ i ∈ S, f i = 1) : ∀ τ ∈ TypeDDatum.evenSignedSupportedAut r p S, τ f = f := by
  intro τ hτ
  have h : TypeDDatum.evenSignedSupportedAut r p S ≤ MulAction.stabilizer (MulAut _) f := by
    unfold TypeDDatum.evenSignedSupportedAut
    rw [Subgroup.closure_le]
    rintro _ (⟨a, ha, b, hb, -, rfl⟩ | ⟨a, ha, b, hb, -, rfl⟩)
    · exact permAut_swap_fix hf ha hb
    · change (sgnAut (p := p) a * sgnAut (p := p) b) f = f
      rw [MulAut.mul_apply, sgnAut_fix hf hb, sgnAut_fix hf ha]
  exact h hτ

theorem diagAut_inv_eq {s : Fin r → ZMod p} (hs : ∀ i, s i * s i = 1) :
    (diagAut s hs)⁻¹ = diagAut s hs := rfl

theorem permAut_swap_fix_const {S : Finset (Fin r)} {f : Fin r → Multiplicative (ZMod p)}
    {m : ZMod p} (hf : ∀ i ∈ S, f i = ofAdd m) {a b : Fin r} (ha : a ∈ S) (hb : b ∈ S) :
    permAut (p := p) (Equiv.swap a b) f = f := by
  funext i
  rw [permAut_apply]
  simp only [Function.comp_apply, Equiv.swap_inv]
  by_cases hia : i = a
  · subst hia
    rw [Equiv.swap_apply_left, hf _ hb, hf _ ha]
  · by_cases hib : i = b
    · subst hib
      rw [Equiv.swap_apply_right, hf _ ha, hf _ hb]
    · rw [Equiv.swap_apply_of_ne_of_ne hia hib]

theorem twistedPermAut_fix {S : Finset (Fin r)} {s : Fin r → ZMod p} (hs : ∀ i, s i * s i = 1)
    {f : Fin r → Multiplicative (ZMod p)} {m : ZMod p}
    (hf : ∀ i ∈ S, toAdd (f i) = m * s i) : ∀ τ ∈ TypeBDatum.twistedPermAut r p S s hs, τ f = f := by
  intro τ hτ
  obtain ⟨τ₀, hτ₀, rfl⟩ := Subgroup.mem_map.mp hτ
  set d : MulAut (Fin r → Multiplicative (ZMod p)) := diagAut s hs with hd
  have hdf : ∀ i ∈ S, (d f) i = ofAdd m := by
    intro i hi
    rw [hd, diagAut_apply, hf i hi, mul_left_comm, hs i, mul_one]
  have h1 : τ₀ (d f) = d f := by
    have h : TypeBDatum.permSupportedAut r p S ≤ MulAction.stabilizer (MulAut _) (d f) := by
      unfold TypeBDatum.permSupportedAut
      rw [Subgroup.closure_le]
      rintro _ ⟨a, ha, b, hb, -, rfl⟩
      exact permAut_swap_fix_const hdf ha hb
    exact h hτ₀
  change (MulAut.conj d τ₀) f = f
  rw [MulAut.conj_apply, MulAut.mul_apply, MulAut.mul_apply]
  have h2 : d⁻¹ f = d f := by rw [hd, diagAut_inv_eq]
  rw [h2, h1]
  funext i
  rw [hd, diagAut_apply, diagAut_apply, toAdd_ofAdd, ← mul_assoc, hs i, one_mul, ofAdd_toAdd]

theorem card_frame_trivial_on (S : Finset (Fin r)) :
    Nat.card {f : Fin r → Multiplicative (ZMod p) // ∀ i ∈ S, f i = 1} = p ^ (r - S.card) := by
  classical
  have e : {f : Fin r → Multiplicative (ZMod p) // ∀ i ∈ S, f i = 1} ≃
      ({i : Fin r // i ∉ S} → Multiplicative (ZMod p)) :=
    { toFun := fun f i => f.1 i.1
      invFun := fun g => ⟨fun i => if h : i ∈ S then 1 else g ⟨i, h⟩, fun i hi => by simp [hi]⟩
      left_inv := fun f => by
        apply Subtype.ext
        funext i
        by_cases hi : i ∈ S
        · simp [hi, f.2 i hi]
        · simp [hi]
      right_inv := fun g => by
        funext i
        simp [i.2] }
  rw [Nat.card_congr e, Nat.card_fun, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod,
    Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe]

variable {G : Type} [Group G] {X Bs J : Subgroup G}

theorem sq_mul_card_le_of_inf {B C Bs : Subgroup G} [Finite G] (hB : B ≤ Bs) (hC : C ≤ Bs)
    (hB4 : p ^ 4 ≤ Nat.card ↥B) (hD : Nat.card ↥(B ⊓ C) = p ^ 2) :
    p ^ 2 * Nat.card ↥C ≤ Nat.card ↥Bs := by
  have h1 := Subgroup.relIndex_mul_card B C
  have h2 := Subgroup.relIndex_mul_card B Bs
  rw [inf_of_le_left hB] at h2
  haveI : B.IsFiniteRelIndex Bs := ⟨Subgroup.index_ne_zero_of_finite⟩
  have h3 : B.relIndex C ≤ B.relIndex Bs :=
    Subgroup.relIndex_le_of_le_right hC Subgroup.relIndex_ne_zero
  rw [hD] at h1
  calc p ^ 2 * Nat.card ↥C = p ^ 2 * (B.relIndex C * p ^ 2) := by rw [h1]
    _ ≤ p ^ 2 * (B.relIndex Bs * p ^ 2) := by gcongr
    _ = p ^ 4 * B.relIndex Bs := by ring
    _ ≤ Nat.card ↥B * B.relIndex Bs := by gcongr
    _ = Nat.card ↥Bs := by rw [mul_comm]; exact h2

private theorem theta_one {Θ : ((Fin r → Multiplicative (ZMod p)) ×
      ↥(Bs ⊓ Subgroup.centralizer (X : Set G))) ≃* ↥Bs}
    {σ : (Fin r → Multiplicative (ZMod p)) →* ↥X}
    (hΘ : ∀ w c, ((Θ (w, c) : ↥Bs) : G) = ((σ w : ↥X) : G) * c)
    (hmem : ∀ f, ((σ f : ↥X) : G) ∈ Bs) (f : Fin r → Multiplicative (ZMod p)) :
    (⟨((σ f : ↥X) : G), hmem f⟩ : ↥Bs) = Θ (f, 1) := by
  apply Subtype.ext
  rw [hΘ]
  simp

private theorem fixed_of_frame_fixed {Θ : ((Fin r → Multiplicative (ZMod p)) ×
      ↥(Bs ⊓ Subgroup.centralizer (X : Set G))) ≃* ↥Bs}
    {σ : (Fin r → Multiplicative (ZMod p)) →* ↥X}
    (hΘ : ∀ w c, ((Θ (w, c) : ↥Bs) : G) = ((σ w : ↥X) : G) * c)
    (hmem : ∀ f, ((σ f : ↥X) : G) ∈ Bs)
    {Γ : Subgroup (MulAut (Fin r → Multiplicative (ZMod p)))}
    (hAut : ggAutomizer J Bs = Γ.map (TypeBDatum.liftBs Θ))
    {f : Fin r → Multiplicative (ZMod p)} (hf : ∀ τ ∈ Γ, τ f = f) :
    ∀ a ∈ ggAutomizer J Bs, a ⟨((σ f : ↥X) : G), hmem f⟩ = ⟨((σ f : ↥X) : G), hmem f⟩ := by
  intro a ha
  rw [hAut] at ha
  obtain ⟨τ, hτ, rfl⟩ := Subgroup.mem_map.mp ha
  rw [theta_one hΘ hmem f, TypeBDatum.liftBs_apply, hf τ hτ]

theorem corank_le_three_of_supported [Finite G] [Fact p.Prime]
    {Θ : ((Fin r → Multiplicative (ZMod p)) × ↥(Bs ⊓ Subgroup.centralizer (X : Set G))) ≃*
      ↥Bs} {σ : (Fin r → Multiplicative (ZMod p)) →* ↥X}
    (hΘ : ∀ w c, ((Θ (w, c) : ↥Bs) : G) = ((σ w : ↥X) : G) * c)
    (hmem : ∀ f, ((σ f : ↥X) : G) ∈ Bs)
    {Γ : Subgroup (MulAut (Fin r → Multiplicative (ZMod p)))} {S : Finset (Fin r)}
    (hΓ : ∀ f : Fin r → Multiplicative (ZMod p), (∀ i ∈ S, f i = 1) → ∀ τ ∈ Γ, τ f = f)
    (hAut : ggAutomizer J Bs = Γ.map (TypeBDatum.liftBs Θ))
    (hcentral : ∀ b : ↥Bs, (∀ a ∈ ggAutomizer J Bs, a b = b) →
      (b : G) ∈ Subgroup.centralizer (J : Set G))
    (hCJ : Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≤ p ^ 3) : r - S.card ≤ 3 := by
  classical
  let Φ : {f : Fin r → Multiplicative (ZMod p) // ∀ i ∈ S, f i = 1} →
      ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) := fun f =>
    ⟨((σ f.1 : ↥X) : G), Subgroup.mem_inf.mpr ⟨hmem f.1,
      hcentral ⟨_, hmem f.1⟩ (fixed_of_frame_fixed hΘ hmem hAut (hΓ f.1 f.2))⟩⟩
  have hΦ : Function.Injective Φ := by
    intro f f' h
    have h0 : ((σ f.1 : ↥X) : G) = ((σ f'.1 : ↥X) : G) :=
      congrArg (fun z : ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) => (z : G)) h
    have h1 : (⟨((σ f.1 : ↥X) : G), hmem f.1⟩ : ↥Bs) = ⟨((σ f'.1 : ↥X) : G), hmem f'.1⟩ :=
      Subtype.ext h0
    rw [theta_one hΘ hmem, theta_one hΘ hmem] at h1
    exact Subtype.ext (congrArg Prod.fst (Θ.injective h1))
  have h2 := Nat.card_le_card_of_injective Φ hΦ
  rw [card_frame_trivial_on] at h2
  exact (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp (h2.trans hCJ)

theorem corank_le_three_of_twisted [Finite G] [Fact p.Prime]
    {Θ : ((Fin r → Multiplicative (ZMod p)) × ↥(Bs ⊓ Subgroup.centralizer (X : Set G))) ≃*
      ↥Bs} {σ : (Fin r → Multiplicative (ZMod p)) →* ↥X}
    (hΘ : ∀ w c, ((Θ (w, c) : ↥Bs) : G) = ((σ w : ↥X) : G) * c)
    (hmem : ∀ f, ((σ f : ↥X) : G) ∈ Bs)
    {Γ : Subgroup (MulAut (Fin r → Multiplicative (ZMod p)))} {S : Finset (Fin r)}
    {s : Fin r → ZMod p} (hs : ∀ i, s i * s i = 1) (hS : 1 ≤ S.card)
    (hΓ : ∀ (f : Fin r → Multiplicative (ZMod p)) (m : ZMod p),
      (∀ i ∈ S, toAdd (f i) = m * s i) → ∀ τ ∈ Γ, τ f = f)
    (hAut : ggAutomizer J Bs = Γ.map (TypeBDatum.liftBs Θ))
    (hcentral : ∀ b : ↥Bs, (∀ a ∈ ggAutomizer J Bs, a b = b) →
      (b : G) ∈ Subgroup.centralizer (J : Set G))
    (hCJ : Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≤ p ^ 3) :
    r - S.card + 1 ≤ 3 := by
  classical
  let fm : ZMod p × ({i : Fin r // i ∉ S} → ZMod p) → (Fin r → Multiplicative (ZMod p)) :=
    fun mg i => if h : i ∈ S then ofAdd (mg.1 * s i) else ofAdd (mg.2 ⟨i, h⟩)
  have hfm : ∀ mg : ZMod p × ({i : Fin r // i ∉ S} → ZMod p), ∀ i ∈ S,
      toAdd (fm mg i) = mg.1 * s i := fun mg i hi => by simp [fm, hi]
  let Ψ : ZMod p × ({i : Fin r // i ∉ S} → ZMod p) →
      ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) := fun mg =>
    ⟨((σ (fm mg) : ↥X) : G), Subgroup.mem_inf.mpr ⟨hmem _,
      hcentral ⟨_, hmem _⟩ (fixed_of_frame_fixed hΘ hmem hAut
        (fun τ hτ => hΓ (fm mg) mg.1 (hfm mg) τ hτ))⟩⟩
  have hΨ : Function.Injective Ψ := by
    intro mg mg' h
    have h0 : ((σ (fm mg) : ↥X) : G) = ((σ (fm mg') : ↥X) : G) :=
      congrArg (fun z : ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) => (z : G)) h
    have h1 : (⟨((σ (fm mg) : ↥X) : G), hmem _⟩ : ↥Bs) =
        ⟨((σ (fm mg') : ↥X) : G), hmem _⟩ := Subtype.ext h0
    rw [theta_one hΘ hmem, theta_one hΘ hmem] at h1
    have h2 : fm mg = fm mg' := congrArg Prod.fst (Θ.injective h1)
    obtain ⟨i₀, hi₀⟩ : ∃ i₀, i₀ ∈ S := Finset.card_pos.mp hS
    have hsi : s i₀ ≠ 0 := fun h0 => by
      have := hs i₀
      rw [h0, zero_mul] at this
      exact zero_ne_one this
    refine Prod.ext ?_ (funext fun i => ?_)
    · have h3 := congrArg (fun f => toAdd (f i₀)) h2
      simp only [hfm mg i₀ hi₀, hfm mg' i₀ hi₀] at h3
      exact mul_right_cancel₀ hsi h3
    · have h3 := congrArg (fun f => toAdd (f i.1)) h2
      simp only [fm, i.2, dif_neg, not_false_eq_true, toAdd_ofAdd] at h3
      exact h3
  have h2 := Nat.card_le_card_of_injective Ψ hΨ
  rw [Nat.card_prod, Nat.card_zmod, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
    Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe] at h2
  have h3 : p ^ (r - S.card + 1) ≤ p ^ 3 := by
    calc p ^ (r - S.card + 1) = p * p ^ (r - S.card) := by ring
      _ ≤ _ := h2.trans hCJ
  exact (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp h3

end FrameBs

end CFSG.StandardType

end
