module

public import CFSG.LocalAnalysis.StandardType.GGTBJTypeBDatum
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRestDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyReflInner
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGenLift
public import CFSG.LocalAnalysis.StandardType.GGTBTorDatum

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

namespace FrameBs

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def sectionFrameAut {G : Type} [Group G] {p r : ℕ}
    (Θ₁ : (Fin r → Multiplicative (ZMod p)) →* G) (H : Subgroup G) :
    Subgroup (MulAut (Fin r → Multiplicative (ZMod p))) where
  carrier := {τ | ∃ n ∈ H, ∀ f, n * Θ₁ f * n⁻¹ = Θ₁ (τ f)}
  mul_mem' := by
    rintro τ τ' ⟨n, hn, hnτ⟩ ⟨n', hn', hnτ'⟩
    refine ⟨n * n', H.mul_mem hn hn', fun f => ?_⟩
    calc n * n' * Θ₁ f * (n * n')⁻¹ = n * (n' * Θ₁ f * n'⁻¹) * n⁻¹ := by group
      _ = Θ₁ (τ (τ' f)) := by rw [hnτ' f, hnτ (τ' f)]
      _ = Θ₁ ((τ * τ') f) := rfl
  one_mem' := ⟨1, H.one_mem, fun f => by simp⟩
  inv_mem' := by
    rintro τ ⟨n, hn, h⟩
    refine ⟨n⁻¹, H.inv_mem hn, fun f => ?_⟩
    have h1 := h (τ⁻¹ f)
    rw [MulAut.apply_inv_self] at h1
    rw [inv_inv, ← h1]
    group

theorem eq_of_conj_eq_of_center_prime {X : Type} [Group X] {p : ℕ}
    (hZ : ∀ z ∈ Subgroup.center X, z ^ p = 1 → z = 1) {a b : X} (ha : a ^ p = 1)
    (hb : b ^ p = 1) (h : MulAut.conj a = MulAut.conj b) : a = b := by
  have hc : a⁻¹ * b ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 := congrArg (fun φ : MulAut X => φ g) h
    simp only [MulAut.conj_apply] at h1
    calc g * (a⁻¹ * b) = a⁻¹ * (a * g * a⁻¹) * b := by group
      _ = a⁻¹ * (b * g * b⁻¹) * b := by rw [h1]
      _ = a⁻¹ * b * g := by group
  have hcomm : Commute a (a⁻¹ * b) := Subgroup.mem_center_iff.mp hc a
  have hp : (a⁻¹ * b) ^ p = 1 := by
    have hb' : b = a * (a⁻¹ * b) := by group
    have h2 : b ^ p = a ^ p * (a⁻¹ * b) ^ p := by
      conv_lhs => rw [hb']
      exact hcomm.mul_pow p
    rw [hb, ha, one_mul] at h2
    exact h2.symm
  have h3 := hZ _ hc hp
  calc a = a * (a⁻¹ * b) := by rw [h3, mul_one]
    _ = b := by group

theorem ggTorusWeylElt_of_sectionFrame {Y : Type} [Group Y] {p r : ℕ}
    {A : Subgroup (MulAut Y)} (hA : IsElemAbelian p A)
    (σ : (Fin r → Multiplicative (ZMod p)) →* Y)
    (Θ : (Fin r → Multiplicative (ZMod p)) ≃* A)
    (hΘ : ∀ f, ((Θ f : A) : MulAut Y) = MulAut.conj (σ f))
    {n : Y} (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut Y))) :
    GGTorusWeylElt p A n := by
  have hinn : ∀ a ∈ A, ∃ x : Y, a = MulAut.conj x := by
    intro a ha
    obtain ⟨f, hf⟩ := Θ.surjective ⟨a, ha⟩
    exact ⟨σ f, (congrArg Subtype.val hf).symm.trans (hΘ f)⟩
  have hcomm : ∀ x y : Y, MulAut.conj x ∈ A → MulAut.conj y ∈ A → x * y = y * x := by
    intro x y hx hy
    obtain ⟨f, hf⟩ := Θ.surjective ⟨MulAut.conj x, hx⟩
    obtain ⟨g, hg⟩ := Θ.surjective ⟨MulAut.conj y, hy⟩
    have hxσ : MulAut.conj x = MulAut.conj (σ f) :=
      (congrArg Subtype.val hf).symm.trans (hΘ f)
    have hyσ : MulAut.conj y = MulAut.conj (σ g) :=
      (congrArg Subtype.val hg).symm.trans (hΘ g)
    have hσ : σ g * σ f = σ f * σ g := by rw [← map_mul, ← map_mul, mul_comm]
    have hyf := congrArg (fun a : MulAut Y => a (σ f)) hyσ
    change y * σ f * y⁻¹ = σ g * σ f * (σ g)⁻¹ at hyf
    rw [hσ, mul_inv_cancel_right] at hyf
    have hfy : σ f * y = y * σ f := (mul_inv_eq_iff_eq_mul.mp hyf).symm
    have hxy := congrArg (fun a : MulAut Y => a y) hxσ
    change x * y * x⁻¹ = σ f * y * (σ f)⁻¹ at hxy
    rw [hfy, mul_inv_cancel_right] at hxy
    exact mul_inv_eq_iff_eq_mul.mp hxy
  exact ggTorusWeylElt_of_conj_mem_normalizer hA hinn hcomm hn

variable {G : Type} [Group G] {p r : ℕ} {X Bs : Subgroup G}

theorem sectionFrame_model (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hBsN : Bs ≤ Subgroup.normalizer (X : Set G))
    (σ : (Fin r → Multiplicative (ZMod p)) →* ↥X)
    (ΘA : (Fin r → Multiplicative (ZMod p)) ≃* ↥(ggGamma X hBsN).range)
    (hΘA : ∀ f, ((ΘA f : ↥(ggGamma X hBsN).range) : MulAut ↥X) = MulAut.conj (σ f)) :
    (∀ f, ((σ f : ↥X) : G) ∈ Bs) ∧
      ∃ Θ : ((Fin r → Multiplicative (ZMod p)) × ↥(Bs ⊓ Subgroup.centralizer (X : Set G))) ≃*
          ↥Bs, ∀ w c, ((Θ (w, c) : ↥Bs) : G) = ((σ w : ↥X) : G) * c := by
  classical
  have hact : ∀ b ∈ Bs, ∃ w, ∀ g ∈ X, b * g * b⁻¹ = ((σ w : ↥X) : G) * g * ((σ w : ↥X) : G)⁻¹ := by
    intro b hb
    obtain ⟨w, hw⟩ := ΘA.surjective ⟨ggGamma X hBsN ⟨b, hb⟩, ⟨_, rfl⟩⟩
    refine ⟨w, fun g hg => ?_⟩
    have h1 : MulAut.conj (σ w) = ggGamma X hBsN ⟨b, hb⟩ := by
      rw [← hΘA w, hw]
    have h2 := congrArg (fun φ : MulAut ↥X => ((φ ⟨g, hg⟩ : ↥X) : G)) h1
    simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv, ggGamma_coe] at h2
    exact h2.symm
  have hmem : ∀ f, ((σ f : ↥X) : G) ∈ Bs := by
    intro f
    refine hSC _ ?_ ?_
    · rw [Subgroup.mem_centralizer_iff]
      intro b hb
      obtain ⟨w, hw⟩ := hact b hb
      have h1 := hw ((σ f : ↥X) : G) (σ f).2
      have h2 : ((σ w : ↥X) : G) * ((σ f : ↥X) : G) * ((σ w : ↥X) : G)⁻¹ =
          ((σ f : ↥X) : G) := by
        have : σ w * σ f = σ f * σ w := by rw [← map_mul, ← map_mul, mul_comm]
        have h3 := congrArg Subtype.val this
        simp only [Subgroup.coe_mul] at h3
        rw [h3]
        group
      rw [h2] at h1
      calc b * ((σ f : ↥X) : G) = b * ((σ f : ↥X) : G) * b⁻¹ * b := by group
        _ = ((σ f : ↥X) : G) * b := by rw [h1]
    · rw [← Subgroup.coe_pow, ← map_pow, ReflInner.pow_eq_one_of_zmod f, map_one,
        Subgroup.coe_one]
  refine ⟨hmem, ?_⟩
  let Θ₁ : (Fin r → Multiplicative (ZMod p)) →* G := X.subtype.comp σ
  have hΘ₁inj : Function.Injective Θ₁ := by
    intro f f' hff'
    have h1 : σ f = σ f' := Subtype.ext hff'
    apply ΘA.injective
    apply Subtype.ext
    rw [hΘA f, hΘA f', h1]
  have hdisj : ∀ w, Θ₁ w ∈ Subgroup.centralizer (X : Set G) → w = 1 := by
    intro w hw
    have h1 : MulAut.conj (σ w) = 1 := by
      refine MulEquiv.ext fun g => Subtype.ext ?_
      have := Subgroup.mem_centralizer_iff.mp hw (g : G) g.2
      simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv, MulAut.one_apply]
      change (Θ₁ w) * (g : G) * (Θ₁ w)⁻¹ = g
      rw [← this]
      group
    have h2 : ΘA w = 1 := by
      apply Subtype.ext
      rw [hΘA w, h1]
      rfl
    exact (map_eq_one_iff ΘA ΘA.injective).mp h2
  obtain ⟨Θ, hΘ⟩ := TypeBDatum.exists_prodEquiv_of_frame_centralizer hBs Θ₁ hΘ₁inj hmem hdisj hact
  exact ⟨Θ, hΘ⟩

theorem ggGamma_liftBs_eq {G : Type} [Group G] {p r : ℕ} {X Bs : Subgroup G}
    (hBsN : Bs ≤ Subgroup.normalizer (X : Set G))
    (σ : (Fin r → Multiplicative (ZMod p)) →* ↥X)
    (ΘA : (Fin r → Multiplicative (ZMod p)) ≃* ↥(ggGamma X hBsN).range)
    (hΘA : ∀ f, ((ΘA f : ↥(ggGamma X hBsN).range) : MulAut ↥X) = MulAut.conj (σ f))
    (Θ : ((Fin r → Multiplicative (ZMod p)) ×
      ↥(Bs ⊓ Subgroup.centralizer (X : Set G))) ≃* ↥Bs)
    (hΘ : ∀ w c, ((Θ (w, c) : ↥Bs) : G) = ((σ w : ↥X) : G) * c)
    (w : Fin r → Multiplicative (ZMod p))
    (c : ↥(Bs ⊓ Subgroup.centralizer (X : Set G))) :
    ggGamma X hBsN (Θ (w, c)) = ((ΘA w : ↥(ggGamma X hBsN).range) : MulAut ↥X) := by
  ext g
  rw [ggGamma_coe, hΘ, hΘA w, MulAut.conj_apply]
  have hc : (g : G) * (c : G) = (c : G) * (g : G) :=
    Subgroup.mem_centralizer_iff.mp c.2.2 (g : G) g.2
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [mul_inv_rev]
  calc ((σ w : ↥X) : G) * (c : G) * (g : G) * ((c : G)⁻¹ * ((σ w : ↥X) : G)⁻¹)
      = ((σ w : ↥X) : G) * ((c : G) * (g : G)) *
          ((c : G)⁻¹ * ((σ w : ↥X) : G)⁻¹) := by group
    _ = ((σ w : ↥X) : G) * ((g : G) * (c : G)) *
          ((c : G)⁻¹ * ((σ w : ↥X) : G)⁻¹) := by rw [← hc]
    _ = ((σ w : ↥X) : G) * (g : G) * ((σ w : ↥X) : G)⁻¹ := by group

theorem ggGamma_liftBs_symm {G : Type} [Group G] {p r : ℕ} {X Bs : Subgroup G}
    (hBsN : Bs ≤ Subgroup.normalizer (X : Set G))
    (σ : (Fin r → Multiplicative (ZMod p)) →* ↥X)
    (ΘA : (Fin r → Multiplicative (ZMod p)) ≃* ↥(ggGamma X hBsN).range)
    (hΘA : ∀ f, ((ΘA f : ↥(ggGamma X hBsN).range) : MulAut ↥X) = MulAut.conj (σ f))
    (Θ : ((Fin r → Multiplicative (ZMod p)) ×
      ↥(Bs ⊓ Subgroup.centralizer (X : Set G))) ≃* ↥Bs)
    (hΘ : ∀ w c, ((Θ (w, c) : ↥Bs) : G) = ((σ w : ↥X) : G) * c)
    (b : ↥Bs) :
    ΘA.symm ⟨ggGamma X hBsN b, ⟨b, rfl⟩⟩ = (Θ.symm b).1 := by
  obtain ⟨⟨w, c⟩, rfl⟩ := Θ.surjective b
  rw [MulEquiv.symm_apply_apply]
  apply ΘA.injective
  rw [MulEquiv.apply_symm_apply]
  exact Subtype.ext (ggGamma_liftBs_eq hBsN σ ΘA hΘA Θ hΘ w c)

theorem sectionFrameAut_subtype_comp {G : Type} [Group G] {X : Subgroup G} {p r : ℕ}
    (σ : (Fin r → Multiplicative (ZMod p)) →* ↥X) {H : Subgroup G} (hHX : H ≤ X) :
    sectionFrameAut (X.subtype.comp σ) H = sectionFrameAut σ (H.subgroupOf X) := by
  ext τ
  constructor
  · rintro ⟨n, hn, h⟩
    refine ⟨⟨n, hHX hn⟩, Subgroup.mem_subgroupOf.mpr hn, fun f => Subtype.ext ?_⟩
    simpa using h f
  · rintro ⟨n, hn, h⟩
    refine ⟨(n : G), Subgroup.mem_subgroupOf.mp hn, fun f => ?_⟩
    have := congrArg Subtype.val (h f)
    simpa using this

theorem exists_sectionFrameAut (hBsN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hZ : ∀ z ∈ Subgroup.center ↥X, z ^ p = 1 → z = 1)
    (σ : (Fin r → Multiplicative (ZMod p)) →* ↥X)
    (ΘA : (Fin r → Multiplicative (ZMod p)) ≃* ↥(ggGamma X hBsN).range)
    (hΘA : ∀ f, ((ΘA f : ↥(ggGamma X hBsN).range) : MulAut ↥X) = MulAut.conj (σ f))
    {x : G} (hxX : x ∈ X) (hxN : x ∈ Subgroup.normalizer (Bs : Set G)) :
    ∃ τ : MulAut (Fin r → Multiplicative (ZMod p)),
      ∀ v, x * ((σ v : ↥X) : G) * x⁻¹ = ((σ (τ v) : ↥X) : G) := by
  classical
  have hnorm := conj_mem_normalizer_range_ggGamma hBsN hxX hxN
  let x' : ↥X := ⟨x, hxX⟩
  let ψ : MulAut ↥(ggGamma X hBsN).range := ggConjAut _ hnorm
  let τ : MulAut (Fin r → Multiplicative (ZMod p)) := (ΘA.trans ψ).trans ΘA.symm
  refine ⟨τ, fun v => ?_⟩
  have hτv : ΘA (τ v) = ψ (ΘA v) := by
    change ΘA (ΘA.symm (ψ (ΘA v))) = _
    exact ΘA.apply_symm_apply _
  have h1 : MulAut.conj x' * MulAut.conj (σ v) * (MulAut.conj x')⁻¹ =
      MulAut.conj (σ (τ v)) := by
    rw [← hΘA (τ v), hτv, ← hΘA v]
    exact (ggConjAut_apply (ggGamma X hBsN).range hnorm (ΘA v)).symm
  have hpσ : ∀ w, (σ w) ^ p = 1 := fun w => by
    rw [← map_pow, ReflInner.pow_eq_one_of_zmod w, map_one]
  have h2 : x' * σ v * x'⁻¹ = σ (τ v) := by
    refine eq_of_conj_eq_of_center_prime hZ ?_ (hpσ _) ?_
    · rw [conj_pow, hpσ, mul_one, mul_inv_cancel]
    · rw [← h1, map_mul, map_mul, map_inv]
  have h3 := congrArg Subtype.val h2
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h3

theorem mem_normalizer_of_sectionFrameAut
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hBsN : Bs ≤ Subgroup.normalizer (X : Set G)) [Finite G]
    (σ : (Fin r → Multiplicative (ZMod p)) →* ↥X)
    (ΘA : (Fin r → Multiplicative (ZMod p)) ≃* ↥(ggGamma X hBsN).range)
    (hΘA : ∀ f, ((ΘA f : ↥(ggGamma X hBsN).range) : MulAut ↥X) = MulAut.conj (σ f))
    (hWeyl : ∀ n : ↥X, MulAut.conj n ∈ Subgroup.normalizer ((ggGamma X hBsN).range :
        Set (MulAut ↥X)) → GGTorusWeylElt p (ggGamma X hBsN).range n)
    {n : G} (hnX : n ∈ X) (τ : MulAut (Fin r → Multiplicative (ZMod p)))
    (hτ : ∀ v, n * ((σ v : ↥X) : G) * n⁻¹ = ((σ (τ v) : ↥X) : G)) :
    n ∈ Subgroup.normalizer (Bs : Set G) := by
  classical
  let n' : ↥X := ⟨n, hnX⟩
  have hτ' : ∀ v, n' * σ v * n'⁻¹ = σ (τ v) := fun v => Subtype.ext (by
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hτ v)
  have hτinv : ∀ v, n'⁻¹ * σ v * n' = σ (τ⁻¹ v) := by
    intro v
    have h := hτ' (τ⁻¹ v)
    rw [MulAut.apply_inv_self] at h
    rw [← h]
    group
  have hnorm : MulAut.conj n' ∈ Subgroup.normalizer
      ((ggGamma X hBsN).range : Set (MulAut ↥X)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      obtain ⟨f, hf⟩ := ΘA.surjective ⟨a, ha⟩
      have haf : a = MulAut.conj (σ f) := by
        rw [← hΘA f, hf]
      have h1 : MulAut.conj n' * a * (MulAut.conj n')⁻¹ = MulAut.conj (σ (τ f)) := by
        rw [haf, ← hτ' f, map_mul, map_mul, map_inv]
      rw [h1, ← hΘA (τ f)]
      exact (ΘA (τ f)).2
    · intro ha
      obtain ⟨g, hg⟩ := ΘA.surjective ⟨MulAut.conj n' * a * (MulAut.conj n')⁻¹, ha⟩
      have hag : MulAut.conj n' * a * (MulAut.conj n')⁻¹ = MulAut.conj (σ g) := by
        rw [← hΘA g, hg]
      have h1 : a = MulAut.conj (σ (τ⁻¹ g)) := by
        rw [← hτinv g, map_mul, map_mul, map_inv]
        calc a = (MulAut.conj n')⁻¹ * (MulAut.conj n' * a * (MulAut.conj n')⁻¹) *
              MulAut.conj n' := by group
          _ = _ := by rw [hag]
      rw [h1, ← hΘA (τ⁻¹ g)]
      exact (ΘA (τ⁻¹ g)).2
  exact mem_normalizer_of_ggTorusWeylElt hBsN hSC (hWeyl n' hnorm)

theorem ggAutomizer_eq_map_liftBs_sectionFrameAut (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hBsN : Bs ≤ Subgroup.normalizer (X : Set G)) [Finite G]
    (hZ : ∀ z ∈ Subgroup.center ↥X, z ^ p = 1 → z = 1)
    (σ : (Fin r → Multiplicative (ZMod p)) →* ↥X)
    (ΘA : (Fin r → Multiplicative (ZMod p)) ≃* ↥(ggGamma X hBsN).range)
    (hΘA : ∀ f, ((ΘA f : ↥(ggGamma X hBsN).range) : MulAut ↥X) = MulAut.conj (σ f)) :
    ∃ Θ : ((Fin r → Multiplicative (ZMod p)) × ↥(Bs ⊓ Subgroup.centralizer (X : Set G))) ≃*
        ↥Bs, (∀ w c, ((Θ (w, c) : ↥Bs) : G) = ((σ w : ↥X) : G) * c) ∧
      ∀ H : Subgroup G, H ≤ X →
        ggAutomizer H Bs = (sectionFrameAut (X.subtype.comp σ) H).map (TypeBDatum.liftBs Θ) := by
  classical
  have hA : IsElemAbelian p (ggGamma X hBsN).range := ggTD_elemAb hBsN hBs
  have hWeyl : ∀ n : ↥X, MulAut.conj n ∈ Subgroup.normalizer
      ((ggGamma X hBsN).range : Set (MulAut ↥X)) →
      GGTorusWeylElt p (ggGamma X hBsN).range n :=
    fun _ hn => ggTorusWeylElt_of_sectionFrame hA σ ΘA hΘA hn
  obtain ⟨hmem, Θ, hΘ⟩ := sectionFrame_model hBs hSC hBsN σ ΘA hΘA
  refine ⟨Θ, hΘ, fun H hHX => ?_⟩
  have key : ∀ x ∈ H, ∀ τ : MulAut (Fin r → Multiplicative (ZMod p)),
      (∀ v, x * ((σ v : ↥X) : G) * x⁻¹ = ((σ (τ v) : ↥X) : G)) → ∀ b : ↥Bs,
        ((TypeBDatum.liftBs Θ τ b : ↥Bs) : G) = x * b * x⁻¹ := by
    intro x hx τ hτ b
    obtain ⟨⟨w, c⟩, rfl⟩ := Θ.surjective b
    rw [TypeBDatum.liftBs_apply, hΘ, hΘ]
    have hxc : x * (c : G) * x⁻¹ = c := by
      have h := Subgroup.mem_centralizer_iff.mp c.2.2 x (hHX hx)
      rw [h]
      group
    calc ((σ (τ w) : ↥X) : G) * (c : G) =
        (x * ((σ w : ↥X) : G) * x⁻¹) * (x * (c : G) * x⁻¹) := by rw [hτ, hxc]
      _ = x * (((σ w : ↥X) : G) * c) * x⁻¹ := by group
  refine le_antisymm ?_ ?_
  · intro φ hφ
    obtain ⟨x, hx, hxN, hxφ⟩ := mem_ggAutomizer_iff.mp hφ
    obtain ⟨τ, hτ⟩ := exists_sectionFrameAut hBsN hZ σ ΘA hΘA (hHX hx) hxN
    refine Subgroup.mem_map.mpr ⟨τ, ⟨x, hx, hτ⟩, ?_⟩
    refine MulEquiv.ext fun b => Subtype.ext ?_
    rw [hxφ b]
    exact key x hx τ hτ b
  · rintro _ ⟨τ, ⟨x, hx, hτ⟩, rfl⟩
    have hxN := mem_normalizer_of_sectionFrameAut hSC hBsN σ ΘA hΘA hWeyl (hHX hx) τ hτ
    refine mem_ggAutomizer_iff.mpr ⟨x, hx, hxN, fun b => ?_⟩
    exact key x hx τ hτ b

theorem mem_centralizer_of_automizer_fixed
    (Θ : ((Fin r → Multiplicative (ZMod p)) × ↥(Bs ⊓ Subgroup.centralizer (X : Set G))) ≃*
      ↥Bs) (σ : (Fin r → Multiplicative (ZMod p)) →* ↥X)
    (hΘ : ∀ w c, ((Θ (w, c) : ↥Bs) : G) = ((σ w : ↥X) : G) * c)
    {H : Subgroup G} (hHX : H ≤ X)
    (hAut : ggAutomizer H Bs = (sectionFrameAut (X.subtype.comp σ) H).map (TypeBDatum.liftBs Θ))
    (hfrm : ∀ f, (∀ τ ∈ sectionFrameAut (X.subtype.comp σ) H, τ f = f) →
      ∀ j ∈ H, ((σ f : ↥X) : G) * j = j * ((σ f : ↥X) : G))
    (b : ↥Bs) (hb : ∀ a ∈ ggAutomizer H Bs, a b = b) :
    (b : G) ∈ Subgroup.centralizer (H : Set G) := by
  obtain ⟨⟨f, c⟩, rfl⟩ := Θ.surjective b
  have hfix : ∀ τ ∈ sectionFrameAut (X.subtype.comp σ) H, τ f = f := by
    intro τ hτ
    have h1 := hb (TypeBDatum.liftBs Θ τ) (hAut ▸ Subgroup.mem_map_of_mem _ hτ)
    rw [TypeBDatum.liftBs_apply] at h1
    exact congrArg Prod.fst (Θ.injective h1)
  rw [hΘ, Subgroup.mem_centralizer_iff]
  intro j hj
  have h1 := hfrm f hfix j hj
  have h2 : (c : G) * j = j * (c : G) := by
    have := Subgroup.mem_centralizer_iff.mp c.2.2 j (hHX hj)
    exact this.symm
  calc j * (((σ f : ↥X) : G) * c) = (j * ((σ f : ↥X) : G)) * c := by group
    _ = (((σ f : ↥X) : G) * j) * c := by rw [h1]
    _ = ((σ f : ↥X) : G) * (j * c) := by group
    _ = ((σ f : ↥X) : G) * (c * j) := by rw [← h2]
    _ = ((σ f : ↥X) : G) * c * j := by group

theorem card_zmodFrame (p r : ℕ) :
    Nat.card (Fin r → Multiplicative (ZMod p)) = p ^ r := by
  rw [Nat.card_fun, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod,
    Nat.card_eq_fintype_card, Fintype.card_fin]

theorem card_centralizer_frame
    (Θ : ((Fin r → Multiplicative (ZMod p)) × ↥(Bs ⊓ Subgroup.centralizer (X : Set G))) ≃*
      ↥Bs) (σ : (Fin r → Multiplicative (ZMod p)) →* ↥X)
    (hΘ : ∀ w c, ((Θ (w, c) : ↥Bs) : G) = ((σ w : ↥X) : G) * c)
    (hmem : ∀ f, ((σ f : ↥X) : G) ∈ Bs) {H : Subgroup G} (hHX : H ≤ X) :
    Nat.card ↥Bs = p ^ r * Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) ∧
      Nat.card ↥(Bs ⊓ Subgroup.centralizer (H : Set G)) =
        Nat.card {f : Fin r → Multiplicative (ZMod p) //
          ∀ j ∈ H, ((σ f : ↥X) : G) * j = j * ((σ f : ↥X) : G)} *
        Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) := by
  classical
  refine ⟨?_, ?_⟩
  · rw [← card_zmodFrame p r, ← Nat.card_prod]
    exact Nat.card_congr Θ.toEquiv.symm
  · have hc : ∀ (f : Fin r → Multiplicative (ZMod p))
        (c : ↥(Bs ⊓ Subgroup.centralizer (X : Set G))),
        ((σ f : ↥X) : G) * (c : G) ∈ Subgroup.centralizer (H : Set G) ↔
          ((σ f : ↥X) : G) ∈ Subgroup.centralizer (H : Set G) := by
      intro f c
      have hcH : (c : G) ∈ Subgroup.centralizer (H : Set G) :=
        Subgroup.centralizer_le (Set.image_subset_iff.mpr (fun _ hj => hHX hj) |> fun _ => hHX) c.2.2
      constructor
      · intro h
        have := (Subgroup.centralizer (H : Set G)).mul_mem h ((Subgroup.centralizer (H : Set G)).inv_mem hcH)
        simpa using this
      · intro h
        exact (Subgroup.centralizer (H : Set G)).mul_mem h hcH
    rw [← Nat.card_prod]
    refine Nat.card_congr (Equiv.symm ?_)
    exact
      { toFun := fun fc => ⟨((σ fc.1.1 : ↥X) : G) * (fc.2 : G), Subgroup.mem_inf.mpr
          ⟨Bs.mul_mem (hmem _) fc.2.2.1, (hc _ _).mpr (by
            rw [Subgroup.mem_centralizer_iff]
            exact fun j hj => (fc.1.2 j hj).symm)⟩⟩
        invFun := fun b => (⟨(Θ.symm ⟨b, b.2.1⟩).1, fun j hj => by
          have h1 : ((σ (Θ.symm ⟨b, b.2.1⟩).1 : ↥X) : G) * ((Θ.symm ⟨b, b.2.1⟩).2 : G) ∈
              Subgroup.centralizer (H : Set G) := by
            rw [← hΘ]
            simpa using b.2.2
          have h2 := Subgroup.mem_centralizer_iff.mp ((hc _ _).mp h1) j hj
          exact h2.symm⟩, (Θ.symm ⟨b, b.2.1⟩).2)
        left_inv := fun fc => by
          obtain ⟨⟨f, hf⟩, c⟩ := fc
          have h : (⟨((σ f : ↥X) : G) * (c : G), Bs.mul_mem (hmem _) c.2.1⟩ : ↥Bs) =
              Θ (f, c) := Subtype.ext (hΘ f c).symm
          simp only [h, MulEquiv.symm_apply_apply]
        right_inv := fun b => by
          apply Subtype.ext
          have h := hΘ (Θ.symm ⟨b, b.2.1⟩).1 (Θ.symm ⟨b, b.2.1⟩).2
          rw [Prod.mk.eta, MulEquiv.apply_symm_apply] at h
          exact h.symm }

end FrameBs

end CFSG.StandardType

end
