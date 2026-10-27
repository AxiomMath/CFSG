module

public import CFSG.RankThree.PartOne.S13K.N135Lin
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.GroupTheory.Nilpotent

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartOne.S13K.N135

variable {V : Type} [CommGroup V]

theorem comm_of_invariant_line {W R : Subgroup (MulAut V)}
    (hirr : ∀ S : Subgroup V, (∀ w ∈ W, ∀ s ∈ S, w s ∈ S) → S = ⊥ ∨ S = ⊤)
    (hRn : ∀ w ∈ W, ∀ r ∈ R, w * r * w⁻¹ ∈ R)
    {e₀ : V} (he₀ : e₀ ≠ 1) (hline : ∀ r ∈ R, r e₀ ∈ Subgroup.zpowers e₀) :
    ∀ ρ ∈ R, ∀ σ ∈ R, ρ * σ = σ * ρ := by
  intro ρ hρ σ hσ
  set S : Subgroup V := Subgroup.closure (Set.range fun w : W => (w : MulAut V) e₀) with hS
  have hSinv : ∀ w ∈ W, ∀ s ∈ S, w s ∈ S := by
    intro w hw s hs
    have hle : S ≤ S.comap (w : V →* V) := by
      rw [hS, Subgroup.closure_le]
      rintro _ ⟨w', rfl⟩
      exact Subgroup.subset_closure ⟨⟨w * w', W.mul_mem hw w'.2⟩, rfl⟩
    exact hle hs
  have he₀S : e₀ ∈ S := Subgroup.subset_closure ⟨⟨1, W.one_mem⟩, rfl⟩
  have hSne : S ≠ ⊥ := fun h => he₀ (by rw [h] at he₀S; exact Subgroup.mem_bot.1 he₀S)
  have hStop : S = ⊤ := (hirr S hSinv).resolve_left hSne
  have hpow : ∀ r ∈ R, ∀ w ∈ W, ∃ k : ℤ, r (w e₀) = (w e₀) ^ k := by
    intro r hr w hw
    have h1 : w⁻¹ * r * w ∈ R := by
      have := hRn w⁻¹ (W.inv_mem hw) r hr
      rwa [inv_inv] at this
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hline _ h1)
    refine ⟨k, ?_⟩
    have h3 : w * (w⁻¹ * r * w) = r * w := by group
    have h2 : r (w e₀) = w ((w⁻¹ * r * w) e₀) :=
      (congrArg (fun m : MulAut V => m e₀) h3).symm
    rw [h2, ← hk, map_zpow]
  let T : Subgroup V :=
    MonoidHom.eqLocus ((ρ : V →* V).comp (σ : V →* V)) ((σ : V →* V).comp (ρ : V →* V))
  have hT : S ≤ T := by
    rw [hS, Subgroup.closure_le]
    rintro _ ⟨w, rfl⟩
    obtain ⟨k₁, hk₁⟩ := hpow ρ hρ w w.2
    obtain ⟨k₂, hk₂⟩ := hpow σ hσ w w.2
    have e1 : ρ (σ ((w : MulAut V) e₀)) = ((w : MulAut V) e₀) ^ (k₁ * k₂) := by
      rw [hk₂, map_zpow, hk₁, ← zpow_mul]
    have e2 : σ (ρ ((w : MulAut V) e₀)) = ((w : MulAut V) e₀) ^ (k₂ * k₁) := by
      rw [hk₁, map_zpow, hk₂, ← zpow_mul]
    show ρ (σ ((w : MulAut V) e₀)) = σ (ρ ((w : MulAut V) e₀))
    rw [e1, e2, mul_comm]
  refine MulEquiv.ext fun v => ?_
  have hv : v ∈ T := hT (by rw [hStop]; trivial)
  exact hv

theorem comm_of_cyclic {Z R : Subgroup (MulAut V)} (hRZ : ∀ r ∈ R, ∀ z ∈ Z, r * z = z * r)
    (hZc : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) {c : V}
    (hgen : Subgroup.closure (Set.range fun z : Z => (z : MulAut V) c) = ⊤) :
    ∀ ρ ∈ R, ∀ σ ∈ R, ρ * σ = σ * ρ := by
  intro ρ hρ σ hσ
  let C : Set (V →* V) := {f | ∀ z ∈ Z, ∀ v : V, f ((z : MulAut V) v) = (z : MulAut V) (f v)}
  let C' : Set (V →* V) := {ψ | ∀ f ∈ C, ∀ v : V, f (ψ v) = ψ (f v)}
  have hZC : ∀ z ∈ Z, ((z : MulAut V) : V →* V) ∈ C' := fun z hz f hf v => hf z hz v
  have hC'C : ∀ ψ ∈ C', ψ ∈ C := by
    intro ψ hψ z hz v
    have hzC : ((z : MulAut V) : V →* V) ∈ C := by
      intro z' hz' v'
      have := congrArg (fun m : MulAut V => m v') (hZc z hz z' hz')
      exact this
    exact (hψ _ hzC v).symm
  have hspan : ∀ v : V, ∃ ψ ∈ C', ψ c = v := by
    intro v
    have hv : v ∈ Subgroup.closure (Set.range fun z : Z => (z : MulAut V) c) := by
      rw [hgen]; trivial
    induction hv using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨z, rfl⟩ := hx
      exact ⟨((z : MulAut V) : V →* V), hZC z z.2, rfl⟩
    | one =>
      refine ⟨1, ?_, rfl⟩
      intro f _ w
      simp
    | mul x y _ _ hx hy =>
      obtain ⟨ψ₁, h₁, e₁⟩ := hx
      obtain ⟨ψ₂, h₂, e₂⟩ := hy
      refine ⟨ψ₁ * ψ₂, ?_, ?_⟩
      · intro f hf w
        simp only [MonoidHom.mul_apply, map_mul]
        rw [h₁ f hf, h₂ f hf]
      · simp only [MonoidHom.mul_apply, e₁, e₂]
    | inv x _ hx =>
      obtain ⟨ψ, h, e⟩ := hx
      refine ⟨ψ⁻¹, ?_, ?_⟩
      · intro f hf w
        simp only [MonoidHom.inv_apply, map_inv]
        rw [h f hf]
      · simp only [MonoidHom.inv_apply, e]
  have hρC : (ρ : V →* V) ∈ C := by
    intro z hz v
    have := congrArg (fun m : MulAut V => m v) (hRZ ρ hρ z hz)
    exact this
  have hσC : (σ : V →* V) ∈ C := by
    intro z hz v
    have := congrArg (fun m : MulAut V => m v) (hRZ σ hσ z hz)
    exact this
  have key : ρ (σ c) = σ (ρ c) := by
    obtain ⟨ψρ, hψρ, eρ⟩ := hspan (ρ c)
    obtain ⟨ψσ, hψσ, eσ⟩ := hspan (σ c)
    have h1 : ρ (σ c) = ψσ (ψρ c) := by
      rw [← eσ]
      have := hψσ _ hρC c
      show (ρ : V →* V) (ψσ c) = _
      rw [this, eρ]; rfl
    have h2 : σ (ρ c) = ψρ (ψσ c) := by
      rw [← eρ]
      have := hψρ _ hσC c
      show (σ : V →* V) (ψρ c) = _
      rw [this, eσ]; rfl
    rw [h1, h2]
    exact (hψσ _ (hC'C ψρ hψρ) c).symm
  let T : Subgroup V :=
    MonoidHom.eqLocus ((ρ : V →* V).comp (σ : V →* V)) ((σ : V →* V).comp (ρ : V →* V))
  have hT : Subgroup.closure (Set.range fun z : Z => (z : MulAut V) c) ≤ T := by
    rw [Subgroup.closure_le]
    rintro _ ⟨z, rfl⟩
    have hρz := fun v : V => congrArg (fun m : MulAut V => m v) (hRZ ρ hρ z z.2)
    have hσz := fun v : V => congrArg (fun m : MulAut V => m v) (hRZ σ hσ z z.2)
    show ρ (σ ((z : MulAut V) c)) = σ (ρ ((z : MulAut V) c))
    have e1 : σ ((z : MulAut V) c) = (z : MulAut V) (σ c) := hσz c
    have e2 : ρ ((z : MulAut V) c) = (z : MulAut V) (ρ c) := hρz c
    have e3 : ρ ((z : MulAut V) (σ c)) = (z : MulAut V) (ρ (σ c)) := hρz _
    have e4 : σ ((z : MulAut V) (ρ c)) = (z : MulAut V) (σ (ρ c)) := hσz _
    rw [e1, e3, e2, e4, key]
  refine MulEquiv.ext fun v => ?_
  have hv : v ∈ T := hT (by rw [hgen]; trivial)
  exact hv

section Det

variable [Finite V] {p : ℕ} [hpp : Fact p.Prime] [hexpF : Fact (∀ v : V, v ^ p = 1)]

noncomputable instance zmodModuleOfExp : Module (ZMod p) (Additive V) :=
  haveI : NeZero p := ⟨hpp.out.ne_zero⟩
  AddCommGroup.zmodModule (n := p) (fun x => by
    apply Additive.toMul.injective
    exact hexpF.out (Additive.toMul x))

@[expose] noncomputable def linOf (z : MulAut V) : Additive V →ₗ[ZMod p] Additive V :=
  (MonoidHom.toAdditive (z : V →* V)).toZModLinearMap p

@[expose] noncomputable def detOf (z : MulAut V) : ZMod p := LinearMap.det (linOf (p := p) z)

theorem linOf_mul (z w : MulAut V) :
    linOf (p := p) (z * w) = (linOf (p := p) z).comp (linOf (p := p) w) := LinearMap.ext fun _ => rfl

theorem detOf_mul (z w : MulAut V) : detOf (p := p) (z * w) = detOf (p := p) z * detOf (p := p) w := by
  show LinearMap.det (linOf (p := p) (z * w)) =
    LinearMap.det (linOf (p := p) z) * LinearMap.det (linOf (p := p) w)
  rw [linOf_mul, LinearMap.det_comp]

theorem linOf_one : linOf (p := p) (1 : MulAut V) = LinearMap.id := LinearMap.ext fun _ => rfl

theorem detOf_one : detOf (p := p) (1 : MulAut V) = 1 := by
  show LinearMap.det (linOf (p := p) (1 : MulAut V)) = 1
  rw [linOf_one, LinearMap.det_id]

theorem detOf_scalar (hcard : Nat.card V = p ^ 4) {z : MulAut V} {k : ℤ} (hz : ∀ e, z e = e ^ k) :
    detOf (p := p) z = (k : ZMod p) ^ 4 := by
  have h1 : linOf (p := p) z = (k : ZMod p) • (LinearMap.id : Additive V →ₗ[ZMod p] Additive V) := by
    ext v
    show Additive.ofMul (z (Additive.toMul v)) = (k : ZMod p) • v
    rw [Int.cast_smul_eq_zsmul, hz]
    rfl
  have hfin : Module.finrank (ZMod p) (Additive V) = 4 := by
    have : Module.Finite (ZMod p) (Additive V) := Module.Finite.of_finite
    have h2 := Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive V)
    have h3 : Nat.card (Additive V) = Nat.card V := Nat.card_congr Additive.toMul
    rw [h3, hcard, Nat.card_zmod] at h2
    exact (Nat.pow_right_injective hpp.out.two_le h2).symm
  show LinearMap.det (linOf (p := p) z) = _
  rw [h1, LinearMap.det_smul, LinearMap.det_id, hfin, mul_one]

end Det

theorem comm_aux (a b r : MulAut V) (h1 : r * a = a * r) (h2 : r * b = b * r) :
    r * (a * b) = a * b * r := by
  calc r * (a * b) = (r * a) * b := (mul_assoc _ _ _).symm
    _ = (a * r) * b := by rw [h1]
    _ = a * (r * b) := mul_assoc _ _ _
    _ = a * (b * r) := by rw [h2]
    _ = a * b * r := (mul_assoc _ _ _).symm

theorem comm_of_nilpotent_normal [Finite V] {p : ℕ} [hpp : Fact p.Prime]
    (hexp : ∀ v : V, v ^ p = 1) (hcard : Nat.card V = p ^ 4)
    {W Λ : Subgroup (MulAut V)} (hΛW : Λ ≤ W)
    (hirr : ∀ S : Subgroup V, (∀ w ∈ W, ∀ s ∈ S, w s ∈ S) → S = ⊥ ∨ S = ⊤)
    {c : V} (hc1 : c ≠ 1) (hΛc : ∀ g ∈ Λ, g c = c)
    (hfourc : ∀ S : Subgroup V, (∀ g ∈ Λ, ∀ s ∈ S, g s ∈ S) → c ∈ S →
      S = Subgroup.zpowers c ∨ S = ⊤)
    {R : Subgroup (MulAut V)} (hRn : ∀ w ∈ W, ∀ r ∈ R, w * r * w⁻¹ ∈ R)
    [Group.IsNilpotent R] (hRodd : ∀ r ∈ R, Odd (orderOf r)) :
    ∀ ρ ∈ R, ∀ σ ∈ R, ρ * σ = σ * ρ := by
  have : Fact (∀ v : V, v ^ p = 1) := ⟨hexp⟩
  by_contra hnc
  push Not at hnc
  obtain ⟨ρ₀, hρ₀, σ₀, hσ₀, hne⟩ := hnc
  let R₁ : Subgroup R :=
    { carrier := {r | detOf (p := p) (r : MulAut V) = 1}
      mul_mem' := by
        intro a b ha hb
        have ha' : detOf (p := p) (a : MulAut V) = 1 := ha
        have hb' : detOf (p := p) (b : MulAut V) = 1 := hb
        show detOf (p := p) ((a * b : R) : MulAut V) = 1
        rw [Subgroup.coe_mul, detOf_mul, ha', hb', mul_one]
      one_mem' := by
        show detOf (p := p) (((1 : R) : MulAut V)) = 1
        rw [Subgroup.coe_one, detOf_one]
      inv_mem' := by
        intro a ha
        have ha' : detOf (p := p) (a : MulAut V) = 1 := ha
        show detOf (p := p) ((a⁻¹ : R) : MulAut V) = 1
        have h1 := detOf_mul (p := p) (a : MulAut V) ((a⁻¹ : R) : MulAut V)
        rw [← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, detOf_one, ha', one_mul] at h1
        exact h1.symm }
  have hR₁n : R₁.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn' : detOf (p := p) (n : MulAut V) = 1 := hn
    show detOf (p := p) ((g * n * g⁻¹ : R) : MulAut V) = 1
    have h1 := detOf_mul (p := p) (g : MulAut V) ((g⁻¹ : R) : MulAut V)
    rw [← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, detOf_one] at h1
    calc detOf (p := p) ((g * n * g⁻¹ : R) : MulAut V)
        = detOf (p := p) (g : MulAut V) * detOf (p := p) (n : MulAut V) *
            detOf (p := p) ((g⁻¹ : R) : MulAut V) := by
          rw [Subgroup.coe_mul, Subgroup.coe_mul, detOf_mul, detOf_mul]
      _ = 1 := by rw [hn', mul_one]; exact h1.symm
  have hR₁ne : R₁ ≠ ⊥ := by
    intro hbot
    let ρ' : R := ⟨ρ₀, hρ₀⟩
    let σ' : R := ⟨σ₀, hσ₀⟩
    have hcomm : ρ' * σ' * ρ'⁻¹ * σ'⁻¹ ∈ R₁ := by
      show detOf (p := p) ((ρ' * σ' * ρ'⁻¹ * σ'⁻¹ : R) : MulAut V) = 1
      have a1 := detOf_mul (p := p) (ρ' : MulAut V) ((ρ'⁻¹ : R) : MulAut V)
      have b1 := detOf_mul (p := p) (σ' : MulAut V) ((σ'⁻¹ : R) : MulAut V)
      rw [← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, detOf_one] at a1 b1
      calc detOf (p := p) ((ρ' * σ' * ρ'⁻¹ * σ'⁻¹ : R) : MulAut V)
          = detOf (p := p) (ρ' : MulAut V) * detOf (p := p) (σ' : MulAut V) *
              detOf (p := p) ((ρ'⁻¹ : R) : MulAut V) * detOf (p := p) ((σ'⁻¹ : R) : MulAut V) := by
            simp only [Subgroup.coe_mul, detOf_mul]
        _ = (detOf (p := p) (ρ' : MulAut V) * detOf (p := p) ((ρ'⁻¹ : R) : MulAut V)) *
              (detOf (p := p) (σ' : MulAut V) * detOf (p := p) ((σ'⁻¹ : R) : MulAut V)) := by ring
        _ = 1 := by rw [← a1, ← b1, mul_one]
    rw [hbot, Subgroup.mem_bot] at hcomm
    apply hne
    have h1 : ρ' * σ' * ρ'⁻¹ = σ' := mul_inv_eq_one.1 hcomm
    have h2 : ρ' * σ' = σ' * ρ' := by
      calc ρ' * σ' = ρ' * σ' * ρ'⁻¹ * ρ' := by group
        _ = σ' * ρ' := by rw [h1]
    exact congrArg Subtype.val h2
  obtain ⟨z', hz'⟩ : ∃ z' : R, z' ∈ R₁ ⊓ Subgroup.center R ∧ z' ≠ 1 := by
    have h := Group.IsNilpotent.inf_center_ne_bot_of_normal hR₁ne
    obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 h
    exact ⟨a.1, a.2, fun h' => ha (Subtype.ext h')⟩
  let Z₂ : Subgroup (MulAut V) :=
    { carrier := {z | z ∈ R ∧ detOf (p := p) z = 1 ∧ ∀ r ∈ R, r * z = z * r}
      mul_mem' := by
        rintro a b ⟨haR, hadet, hacomm⟩ ⟨hbR, hbdet, hbcomm⟩
        exact ⟨R.mul_mem haR hbR, by rw [detOf_mul, hadet, hbdet, mul_one],
          fun r hr => comm_aux a b r (hacomm r hr) (hbcomm r hr)⟩
      one_mem' := ⟨R.one_mem, detOf_one, fun r _ => by rw [mul_one, one_mul]⟩
      inv_mem' := by
        rintro a ⟨haR, hadet, hacomm⟩
        refine ⟨R.inv_mem haR, ?_, fun r hr => ?_⟩
        · have h1 := detOf_mul (p := p) a a⁻¹
          rw [mul_inv_cancel, detOf_one, hadet, one_mul] at h1
          exact h1.symm
        · have h1 := hacomm r hr
          calc r * a⁻¹ = a⁻¹ * (a * r) * a⁻¹ := by group
            _ = a⁻¹ * (r * a) * a⁻¹ := by rw [h1]
            _ = a⁻¹ * r := by group }
  have hZ₂R : ∀ z ∈ Z₂, z ∈ R := fun z hz => hz.1
  have hRZ : ∀ r ∈ R, ∀ z ∈ Z₂, r * z = z * r := fun r hr z hz => hz.2.2 r hr
  have hZ₂c : ∀ a ∈ Z₂, ∀ b ∈ Z₂, a * b = b * a := fun a ha b hb => hb.2.2 a ha.1
  have hZ₂Λ : ∀ g ∈ Λ, ∀ z ∈ Z₂, g * z * g⁻¹ ∈ Z₂ := by
    intro g hg z hz
    have hgW : g ∈ W := hΛW hg
    refine ⟨hRn g hgW z hz.1, ?_, fun r hr => ?_⟩
    · have h1 := detOf_mul (p := p) g g⁻¹
      rw [mul_inv_cancel, detOf_one] at h1
      rw [detOf_mul, detOf_mul, hz.2.1, mul_one, ← h1]
    · have hr' : g⁻¹ * r * g ∈ R := by
        have := hRn g⁻¹ (W.inv_mem hgW) r hr
        rwa [inv_inv] at this
      have h1 := hz.2.2 _ hr'
      calc r * (g * z * g⁻¹) = g * ((g⁻¹ * r * g) * z) * g⁻¹ := by group
        _ = g * (z * (g⁻¹ * r * g)) * g⁻¹ := by rw [h1]
        _ = g * z * g⁻¹ * r := by group
  have hz₀ : (z' : MulAut V) ∈ Z₂ := by
    obtain ⟨h1, h2⟩ := hz'.1
    refine ⟨z'.2, h1, fun r hr => ?_⟩
    have := Subgroup.mem_center_iff.1 h2 ⟨r, hr⟩
    exact congrArg Subtype.val this
  have hz₀ne : (z' : MulAut V) ≠ 1 := fun h => hz'.2 (Subtype.ext h)
  let Vc : Subgroup V := Subgroup.closure (Set.range fun z : Z₂ => (z : MulAut V) c)
  have hginv : ∀ g ∈ Λ, g⁻¹ c = c := by
    intro g hg
    have h1 := MulAut.inv_apply_self V g c
    rwa [hΛc g hg] at h1
  have hVc_inv : ∀ g ∈ Λ, ∀ s ∈ Vc, g s ∈ Vc := by
    intro g hg s hs
    have hle : Vc ≤ Vc.comap (g : V →* V) := by
      rw [Subgroup.closure_le]
      rintro _ ⟨z, rfl⟩
      show g ((z : MulAut V) c) ∈ Vc
      have h1 : g ((z : MulAut V) c) = (g * z * g⁻¹ : MulAut V) c := by
        show g ((z : MulAut V) c) = g ((z : MulAut V) (g⁻¹ c))
        rw [hginv g hg]
      rw [h1]
      exact Subgroup.subset_closure ⟨⟨g * z * g⁻¹, hZ₂Λ g hg z z.2⟩, rfl⟩
    exact hle hs
  have hc_Vc : c ∈ Vc := Subgroup.subset_closure ⟨⟨1, Z₂.one_mem⟩, rfl⟩
  rcases hfourc Vc hVc_inv hc_Vc with hVc | hVc
  swap
  ·
    exact hne (comm_of_cyclic hRZ hZ₂c hVc ρ₀ hρ₀ σ₀ hσ₀)
  have hzc : ∀ z ∈ Z₂, z c ∈ Subgroup.zpowers c := by
    intro z hz
    have h1 : (z : MulAut V) c ∈ Vc := Subgroup.subset_closure ⟨⟨z, hz⟩, rfl⟩
    rwa [hVc] at h1
  let Veig : Subgroup V :=
    { carrier := {e | ∀ z ∈ Z₂, ∀ k : ℤ, (z : MulAut V) c = c ^ k → (z : MulAut V) e = e ^ k}
      mul_mem' := by
        intro a b ha hb z hz k hk
        rw [map_mul, ha z hz k hk, hb z hz k hk, mul_zpow]
      one_mem' := by
        intro z hz k hk
        rw [map_one, one_zpow]
      inv_mem' := by
        intro a ha z hz k hk
        rw [map_inv, ha z hz k hk, inv_zpow] }
  have hcVeig : c ∈ Veig := fun z _ k hk => hk
  have hVeigR : ∀ r ∈ R, ∀ e ∈ Veig, r e ∈ Veig := by
    intro r hr e he z hz k hk
    have h1 : (z : MulAut V) (r e) = r ((z : MulAut V) e) :=
      (congrArg (fun m : MulAut V => m e) (hRZ r hr z hz)).symm
    rw [h1, he z hz k hk, map_zpow]
  have hVeigΛ : ∀ g ∈ Λ, ∀ e ∈ Veig, g e ∈ Veig := by
    intro g hg e he z hz k hk
    have hz' : g⁻¹ * z * g ∈ Z₂ := by
      have := hZ₂Λ g⁻¹ (Λ.inv_mem hg) z hz
      rwa [inv_inv] at this
    have hz'c : (g⁻¹ * z * g : MulAut V) c = c ^ k := by
      show g⁻¹ ((z : MulAut V) (g c)) = c ^ k
      rw [hΛc g hg, hk, map_zpow, hginv g hg]
    have h1 := he _ hz' k hz'c
    have h2 : (g⁻¹ * z * g : MulAut V) e = g⁻¹ ((z : MulAut V) (g e)) := rfl
    rw [h2] at h1
    have h3 := congrArg g h1
    rw [MulAut.apply_inv_self, map_zpow] at h3
    exact h3
  rcases hfourc Veig hVeigΛ hcVeig with hV | hV
  ·
    have hline : ∀ r ∈ R, r c ∈ Subgroup.zpowers c := by
      intro r hr
      have := hVeigR r hr c hcVeig
      rwa [hV] at this
    exact hne (comm_of_invariant_line hirr hRn hc1 hline ρ₀ hρ₀ σ₀ hσ₀)
  ·
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hzc _ hz₀)
    have hall : ∀ e : V, (z' : MulAut V) e = e ^ k := by
      intro e
      have he : e ∈ Veig := by rw [hV]; trivial
      exact he _ hz₀ k hk.symm
    have hdet := detOf_scalar (p := p) hcard hall
    have hdet1 : detOf (p := p) (z' : MulAut V) = 1 := hz₀.2.1
    rw [hdet1] at hdet
    have hcord : orderOf c = p := orderOf_eq_prime (hexp c) hc1
    have hm : (k : ZMod p) ^ orderOf (z' : MulAut V) = 1 := by
      have hpow : ∀ n : ℕ, ∀ e : V, ((z' : MulAut V) ^ n) e = e ^ (k ^ n) := by
        intro n e
        induction n with
        | zero => simp
        | succ n ih =>
          have e1 : (z' : MulAut V) ^ (n + 1) = (z' : MulAut V) ^ n * (z' : MulAut V) := pow_succ _ _
          have e2 : k ^ (n + 1) = k ^ n * k := pow_succ k n
          rw [e1, MulAut.mul_apply, hall e, map_zpow, ih, ← zpow_mul, e2]
      have h1 := hpow (orderOf (z' : MulAut V)) c
      rw [pow_orderOf_eq_one, MulAut.one_apply] at h1
      have h2 : c ^ (k ^ orderOf (z' : MulAut V) - 1) = 1 := by
        rw [zpow_sub_one, ← h1, mul_inv_cancel]
      have h3 : ((orderOf c : ℕ) : ℤ) ∣ k ^ orderOf (z' : MulAut V) - 1 :=
        orderOf_dvd_iff_zpow_eq_one.2 h2
      rw [hcord] at h3
      have h4 : (((k ^ orderOf (z' : MulAut V) - 1 : ℤ)) : ZMod p) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 h3
      push_cast at h4
      exact sub_eq_zero.1 h4
    have hodd := hRodd _ (hZ₂R _ hz₀)
    have hcop : Nat.Coprime 4 (orderOf (z' : MulAut V)) := by
      have h2 : Nat.Coprime 2 (orderOf (z' : MulAut V)) := Nat.coprime_two_left.2 hodd
      simpa using Nat.Coprime.pow_left 2 h2
    have hκ : (k : ZMod p) = 1 :=
      (pow_eq_one_iff_of_coprime hcop).1 ⟨hdet.symm, hm⟩
    apply hz₀ne
    refine MulEquiv.ext fun e => ?_
    rw [hall e, MulAut.one_apply]
    have h1 : ((p : ℤ)) ∣ k - 1 := by
      have : (((k - 1 : ℤ)) : ZMod p) = 0 := by
        push_cast
        rw [hκ, sub_self]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 this
    obtain ⟨j, hj⟩ := h1
    have h2 : e ^ (k - 1) = 1 := by
      have h3 : e ^ (p : ℤ) = 1 := by rw [zpow_natCast]; exact hexp e
      rw [hj, zpow_mul, h3, one_zpow]
    calc e ^ k = e ^ (k - 1) * e := by rw [zpow_sub_one, inv_mul_cancel_right]
      _ = e := by rw [h2, one_mul]

end CFSG.RankThree.PartOne.S13K.N135
