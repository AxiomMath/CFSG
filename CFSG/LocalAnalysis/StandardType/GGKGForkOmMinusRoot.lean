module

public import CFSG.LocalAnalysis.StandardType.GGRealKGModelRoot
public import CFSG.LocalAnalysis.StandardType.GGRealKGSignedRefl
public import CFSG.LocalAnalysis.StandardType.GGKGForkLayerGen
public import CFSG.LocalAnalysis.StandardType.GGKGForkOmMinusRoot1
public import CFSG.LocalAnalysis.StandardType.GGKGForkOmMinusRoot2
public import CFSG.LocalAnalysis.StandardType.GGKGForkLatticeElt
public import CFSG.LocalAnalysis.StandardType.GGOmegaMinusRootGenAvoid
public import CFSG.LocalAnalysis.StandardType.GGOmegaMinusRootGenWeyl
public import CFSG.LocalAnalysis.StandardType.GGOmegaMinusRootGenComp
public import CFSG.LocalAnalysis.StandardType.GGOmegaMinusRootGenConj
public import CFSG.LocalAnalysis.StandardType.GGOmegaMinusRootGenIso

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.SeitzReduction CFSG.SeitzReduction.SymplecticPilot
  CFSG.LocalAnalysis.ComponentInitial

private theorem ggKGOmM_map_conj_centralizer {G : Type} [Group G] (C : Set G) (g : G) :
    (Subgroup.centralizer C).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ((MulAut.conj g) '' C) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : ∀ c ∈ C, c * y = y * c := Subgroup.mem_centralizer_iff.mp hy
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨c, hc, rfl⟩
    calc (g * c * g⁻¹) * (g * y * g⁻¹) = g * (c * y) * g⁻¹ := by group
      _ = g * (y * c) * g⁻¹ := by rw [hy' c hc]
      _ = (g * y * g⁻¹) * (g * c * g⁻¹) := by group
  · intro hx
    have hx' : ∀ c ∈ C, (g * c * g⁻¹) * x = x * (g * c * g⁻¹) := by
      intro c hc
      exact Subgroup.mem_centralizer_iff.mp hx (g * c * g⁻¹) ⟨c, hc, rfl⟩
    refine ⟨g⁻¹ * x * g, ?_, ?_⟩
    · change g⁻¹ * x * g ∈ Subgroup.centralizer C
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      have h := hx' c hc
      have h2 := congrArg (fun w => g⁻¹ * w * g) h
      simpa [mul_assoc] using h2
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

private theorem ggKGOmM_permAut_mul_sgnAut {p m : ℕ} {a b : Fin m} :
    (SpCoord.permAut (p := p) (Equiv.swap a b) : MulAut (Fin m → Multiplicative (ZMod p))) *
        SpCoord.sgnAut (p := p) b =
      SpCoord.sgnAut (p := p) a * SpCoord.permAut (p := p) (Equiv.swap a b) := by
  have h := SpCoord.IsSignedPerm.mul_sgnAut
    (u := SpCoord.permAut (p := p) (Equiv.swap a b)) (π := Equiv.swap a b)
    (ε := fun _ => (1 : ZMod p))
    (fun f i => by simp [SpCoord.permAut_apply, Function.comp_apply]) b
  rwa [Equiv.swap_apply_right] at h

private theorem ggKGOmM_negswap_id {p m : ℕ} {a b : Fin m} :
    (SpCoord.sgnAut (p := p) b * SpCoord.permAut (p := p) (Equiv.swap a b) *
        SpCoord.sgnAut (p := p) b) =
      (SpCoord.sgnAut (p := p) a * SpCoord.sgnAut (p := p) b *
        SpCoord.permAut (p := p) (Equiv.swap a b) :
          MulAut (Fin m → Multiplicative (ZMod p))) := by
  let V := Fin m → Multiplicative (ZMod p)
  let A : MulAut V := SpCoord.sgnAut a
  let B : MulAut V := SpCoord.sgnAut b
  let P : MulAut V := SpCoord.permAut (Equiv.swap a b)
  have hPB : P * B = A * P := ggKGOmM_permAut_mul_sgnAut (p := p) (a := a) (b := b)
  have hAB : A * B = B * A := SpCoord.sgnAut_mul_comm (p := p) a b
  have hAA : A * A = 1 := by
    have := SpCoord.sgnAut_sq (p := p) a
    simpa [sq] using this
  have hBB : B * B = 1 := by
    have := SpCoord.sgnAut_sq (p := p) b
    simpa [sq] using this
  have hBPB : B * P * B = A * B * P := by
    calc B * P * B = B * (P * B) := by group
      _ = B * (A * P) := by rw [hPB]
      _ = (B * A) * P := by group
      _ = (A * B) * P := by rw [← hAB]
      _ = A * B * P := by group
  change B * P * B = A * B * P
  exact hBPB

private theorem ggKGOmM_fix_negswap {p m : ℕ} {a b : Fin m} :
    (SpCoord.sgnAut (p := p) b : MulAut (Fin m → Multiplicative (ZMod p))) ''
        {f | SpCoord.permAut (p := p) (Equiv.swap a b) f = f} =
      {f | (SpCoord.sgnAut (p := p) a * SpCoord.sgnAut (p := p) b *
        SpCoord.permAut (p := p) (Equiv.swap a b) :
          MulAut (Fin m → Multiplicative (ZMod p))) f = f} := by
  let V := Fin m → Multiplicative (ZMod p)
  let A : MulAut V := SpCoord.sgnAut a
  let B : MulAut V := SpCoord.sgnAut b
  let P : MulAut V := SpCoord.permAut (Equiv.swap a b)
  have hPB : P * B = A * P := ggKGOmM_permAut_mul_sgnAut (p := p) (a := a) (b := b)
  have hAB : A * B = B * A := SpCoord.sgnAut_mul_comm (p := p) a b
  have hAA : A * A = 1 := by
    have := SpCoord.sgnAut_sq (p := p) a
    simpa [sq] using this
  have hBB : B * B = 1 := by
    have := SpCoord.sgnAut_sq (p := p) b
    simpa [sq] using this
  have hBPB : B * P * B = A * B * P := by
    calc B * P * B = B * (P * B) := by group
      _ = B * (A * P) := by rw [hPB]
      _ = (B * A) * P := by group
      _ = (A * B) * P := by rw [← hAB]
      _ = A * B * P := by group
  have hAPB : A * B * P * B = B * P := by
    calc A * B * P * B = A * (B * P * B) := by group
      _ = A * (A * B * P) := by rw [hBPB]
      _ = (A * A) * (B * P) := by group
      _ = B * P := by rw [hAA, one_mul]
  change B '' {f | P f = f} = {f | (A * B * P) f = f}
  ext f
  constructor
  · rintro ⟨g, hg, rfl⟩
    change (A * B * P * B) g = B g
    rw [hAPB]
    change B (P g) = B g
    rw [hg]
  · intro hf
    refine ⟨B f, ?_, ?_⟩
    · have h1 : B (P f) = A f := by
        have h := congrArg (fun x => A x) hf
        have h' : (A * A) (B (P f)) = A f := h
        rw [hAA, MulAut.one_apply] at h'
        exact h'
      have h2 : P f = A (B f) := by
        have h := congrArg (fun x => B x) h1
        have h' : (B * B) (P f) = B (A f) := h
        rw [hBB, MulAut.one_apply] at h'
        calc P f = B (A f) := h'
          _ = (B * A) f := rfl
          _ = (A * B) f := by rw [← hAB]
          _ = A (B f) := rfl
      calc P (B f) = (P * B) f := rfl
        _ = (A * P) f := by rw [hPB]
        _ = A (P f) := rfl
        _ = A (A (B f)) := by rw [h2]
        _ = (A * A) (B f) := rfl
        _ = B f := by rw [hAA, MulAut.one_apply]
    · change (B * B) f = f
      rw [hBB, MulAut.one_apply]

private theorem ggKGOmM_negWeyl {K : Type} [Field K] [Finite K] [CharP K 2] {m p : ℕ} {β γ : K}
    {ζ : Kˣ} (hζ : ζ ^ p = 1) {i j : Fin m}
    {xb : StatedOmega (StatedQuadMinus (m + 1) K β γ)}
    (hxb : ∀ f, xb * omMinusTorus (m := m) (p := p) β γ hζ f * xb⁻¹ =
      omMinusTorus (m := m) (p := p) β γ hζ (SpCoord.sgnAut (p := p) j f))
    {wab : StatedOmega (StatedQuadMinus (m + 1) K β γ)}
    (hwab : ∀ f, wab * omMinusTorus (m := m) (p := p) β γ hζ f * wab⁻¹ =
      omMinusTorus (m := m) (p := p) β γ hζ (SpCoord.permAut (p := p) (Equiv.swap i j) f))
    (f : Fin m → Multiplicative (ZMod p)) :
    (xb * wab * xb⁻¹) * omMinusTorus (m := m) (p := p) β γ hζ f * (xb * wab * xb⁻¹)⁻¹ =
      omMinusTorus (m := m) (p := p) β γ hζ
        ((SpCoord.sgnAut (p := p) i * SpCoord.sgnAut (p := p) j *
          SpCoord.permAut (p := p) (Equiv.swap i j) :
            MulAut (Fin m → Multiplicative (ZMod p))) f) := by
  have hxb_inv : ∀ g, xb⁻¹ * omMinusTorus (m := m) (p := p) β γ hζ g * xb =
      omMinusTorus (m := m) (p := p) β γ hζ (SpCoord.sgnAut (p := p) j g) := by
    intro g
    have hss : SpCoord.sgnAut (p := p) j (SpCoord.sgnAut (p := p) j g) = g := by
      have hB : (SpCoord.sgnAut (p := p) j : MulAut (Fin m → Multiplicative (ZMod p))) *
          SpCoord.sgnAut (p := p) j = 1 := by
        have := SpCoord.sgnAut_sq (p := p) j
        simpa [sq] using this
      have h1 : ((SpCoord.sgnAut (p := p) j : MulAut (Fin m → Multiplicative (ZMod p))) *
          SpCoord.sgnAut (p := p) j) g = g := by rw [hB, MulAut.one_apply]
      simpa only [MulAut.mul_apply] using h1
    have h := hxb (SpCoord.sgnAut (p := p) j g)
    rw [hss] at h
    calc xb⁻¹ * omMinusTorus (m := m) (p := p) β γ hζ g * xb
        = xb⁻¹ * (xb * omMinusTorus (m := m) (p := p) β γ hζ
            (SpCoord.sgnAut (p := p) j g) * xb⁻¹) * xb := by rw [← h]
      _ = omMinusTorus (m := m) (p := p) β γ hζ (SpCoord.sgnAut (p := p) j g) := by group
  have hneg := ggKGOmM_negswap_id (p := p) (a := i) (b := j)
  calc (xb * wab * xb⁻¹) * omMinusTorus (m := m) (p := p) β γ hζ f * (xb * wab * xb⁻¹)⁻¹
      = xb * (wab * (xb⁻¹ * omMinusTorus (m := m) (p := p) β γ hζ f * xb) * wab⁻¹) * xb⁻¹ := by
        group
    _ = xb * (wab * omMinusTorus (m := m) (p := p) β γ hζ (SpCoord.sgnAut (p := p) j f) *
          wab⁻¹) * xb⁻¹ := by rw [hxb_inv f]
    _ = xb * omMinusTorus (m := m) (p := p) β γ hζ
          (SpCoord.permAut (p := p) (Equiv.swap i j) (SpCoord.sgnAut (p := p) j f)) *
          xb⁻¹ := by rw [hwab]
    _ = omMinusTorus (m := m) (p := p) β γ hζ
          (SpCoord.sgnAut (p := p) j (SpCoord.permAut (p := p) (Equiv.swap i j)
            (SpCoord.sgnAut (p := p) j f))) := hxb _
    _ = omMinusTorus (m := m) (p := p) β γ hζ
          ((SpCoord.sgnAut (p := p) i * SpCoord.sgnAut (p := p) j *
            SpCoord.permAut (p := p) (Equiv.swap i j) :
              MulAut (Fin m → Multiplicative (ZMod p))) f) := by
        congr 1
        rw [← MulAut.mul_apply, ← MulAut.mul_apply, hneg]

private theorem ggKGOmM_isComponentOf_negShort {K : Type} [Field K] [Finite K] [CharP K 2]
    {m p : ℕ} {β γ : K} (hK : 4 ≤ Nat.card K)
    (hirr : ∀ s : K, s ^ 2 + β * s + γ ≠ 0) (hp : p.Prime) (hp2 : p ≠ 2)
    {ζ : Kˣ} (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p) {i j : Fin m} (hij : i ≠ j)
    (xb : StatedOmega (StatedQuadMinus (m + 1) K β γ))
    (hxb : ∀ f, xb * omMinusTorus (m := m) (p := p) β γ hζ f * xb⁻¹ =
      omMinusTorus (m := m) (p := p) β γ hζ (SpCoord.sgnAut (p := p) j f)) :
    Assembly.IsComponentOf
      (((omMinusShortBlock K i j).subgroupOf
        (StatedOmega (StatedQuadMinus (m + 1) K β γ))).map
          (MulAut.conj xb).toMonoidHom)
      (Subgroup.centralizer ((omMinusTorus (m := m) (p := p) β γ hζ) ''
        {f | (SpCoord.sgnAut (p := p) i * SpCoord.sgnAut (p := p) j *
          SpCoord.permAut (p := p) (Equiv.swap i j) :
            MulAut (Fin m → Multiplicative (ZMod p))) f = f})) := by
  have hcomp := isComponentOf_omMinusShortBlock hK hirr hp hp2 hζ hζo hij
  have hconj := isComponentOf_map_conj hcomp xb
  have hset : (MulAut.conj xb) '' ((omMinusTorus (m := m) (p := p) β γ hζ) ''
        {f | SpCoord.permAut (p := p) (Equiv.swap i j) f = f}) =
      (omMinusTorus (m := m) (p := p) β γ hζ) ''
        {f | (SpCoord.sgnAut (p := p) i * SpCoord.sgnAut (p := p) j *
          SpCoord.permAut (p := p) (Equiv.swap i j) :
            MulAut (Fin m → Multiplicative (ZMod p))) f = f} := by
    have hfun : ∀ f, (MulAut.conj xb) (omMinusTorus (m := m) (p := p) β γ hζ f) =
        omMinusTorus (m := m) (p := p) β γ hζ (SpCoord.sgnAut (p := p) j f) := by
      intro f
      have h := hxb f
      rwa [show xb * omMinusTorus (m := m) (p := p) β γ hζ f * xb⁻¹ =
          (MulAut.conj xb) (omMinusTorus (m := m) (p := p) β γ hζ f) from
        (MulAut.conj_apply xb _).symm] at h
    ext y
    constructor
    · rintro ⟨z, ⟨f, hf, rfl⟩, rfl⟩
      exact ⟨SpCoord.sgnAut (p := p) j f,
        (ggKGOmM_fix_negswap (p := p) (a := i) (b := j)).le ⟨f, hf, rfl⟩, (hfun f).symm⟩
    · intro hy
      obtain ⟨g, hg, rfl⟩ := hy
      rw [← ggKGOmM_fix_negswap (p := p) (a := i) (b := j)] at hg
      obtain ⟨f, hf, rfl⟩ := hg
      exact ⟨(omMinusTorus (m := m) (p := p) β γ hζ) f, ⟨f, hf, rfl⟩, hfun f⟩
  have hcd : (Subgroup.centralizer ((omMinusTorus (m := m) (p := p) β γ hζ) ''
        {f | SpCoord.permAut (p := p) (Equiv.swap i j) f = f})).map
          (MulAut.conj xb).toMonoidHom =
      Subgroup.centralizer ((omMinusTorus (m := m) (p := p) β γ hζ) ''
        {f | (SpCoord.sgnAut (p := p) i * SpCoord.sgnAut (p := p) j *
          SpCoord.permAut (p := p) (Equiv.swap i j) :
            MulAut (Fin m → Multiplicative (ZMod p))) f = f}) := by
    rw [ggKGOmM_map_conj_centralizer, hset]
  rwa [hcd] at hconj

private theorem ggKGOmM_dvd_card_negShort {K : Type} [Field K] [Finite K] [CharP K 2]
    {m p : ℕ} {β γ : K} (hK : 4 ≤ Nat.card K) (hpq : p ∣ Nat.card K - 1)
    {i j : Fin m} (hij : i ≠ j) (xb : StatedOmega (StatedQuadMinus (m + 1) K β γ)) :
    p ∣ Nat.card ((((omMinusShortBlock K i j).subgroupOf
      (StatedOmega (StatedQuadMinus (m + 1) K β γ))).map
        (MulAut.conj xb).toMonoidHom)) := by
  have h := dvd_card_omMinusShortBlock (b := β) (c := γ) hK hpq hij
  rw [← Nat.card_congr (Subgroup.equivMapOfInjective
      ((omMinusShortBlock K i j).subgroupOf (StatedOmega (StatedQuadMinus (m + 1) K β γ)))
      (MulAut.conj xb).toMonoidHom (MulAut.conj xb).injective).toEquiv]
  exact h

theorem ggKGRootDatumAt_omMinusTorus
    {K : Type} [Field K] [Finite K] [CharP K 2] {m p : ℕ} (hm : 3 ≤ m)
    (hp : p.Prime) (hp2 : p ≠ 2) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {ζ : Kˣ}
    (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1) :
    GGKGRootDatumAt p (omMinusTorus (m := m) b c hζ).range := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hpq : p ∣ Nat.card K - 1 := by
    have h : orderOf ζ ∣ Nat.card Kˣ := orderOf_dvd_natCard ζ
    rwa [hζo, Nat.card_units] at h
  have hK : 4 ≤ Nat.card K := by
    have h1 : p ≤ Nat.card K - 1 := Nat.le_of_dvd (by
      have h2K : 2 ≤ Nat.card K := by
        haveI : Fintype K := Fintype.ofFinite K
        rw [Nat.card_eq_fintype_card]
        exact Fintype.one_lt_card
      omega) hpq
    have h2 : 2 ≤ p := hp.two_le
    omega
  have hτ : Function.Injective (omMinusTorus (m := m) b c hζ) := by
    intro x y h
    apply omMinusTorusGL_injective hζ hζo
    simpa only [coe_omMinusTorus] using congrArg Subtype.val h
  have hW₁ : ∀ l : Fin m, ∃ w : StatedOmega (StatedQuadMinus (m + 1) K b c),
      (w : GL (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K) ∈ omMinusLongBlock K b c l ∧
        ∀ f, w * omMinusTorus b c hζ f * w⁻¹ = omMinusTorus b c hζ (SpCoord.sgnAut l f) := by
    intro l
    obtain ⟨w, hw, hwx⟩ := exists_sgn_mem_omMinusLongBlock (K := K) (m := m) hirr hζ l
    exact ⟨⟨w, omMinusLongBlock_le hirr l hw⟩, hw, fun f => Subtype.ext (hwx f)⟩
  have hW₂ : ∀ i j : Fin m, i ≠ j → ∃ w : StatedOmega (StatedQuadMinus (m + 1) K b c),
      (w : GL (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K) ∈ omMinusShortBlock K i j ∧
        ∀ f, w * omMinusTorus b c hζ f * w⁻¹ =
          omMinusTorus b c hζ (SpCoord.permAut (Equiv.swap i j) f) := by
    intro i j hij
    obtain ⟨w, hw, hwx⟩ := exists_swap_mem_omMinusShortBlock (K := K) (m := m) hζ i j
    exact ⟨⟨w, omMinusShortBlock_le hK hij hw⟩, hw, fun f => Subtype.ext (hwx f)⟩
  choose w₁ hw₁ hw₁' using hW₁
  choose w₂ hw₂ hw₂' using hW₂
  let Idx := Fin m ⊕ {q : Fin m × Fin m // q.1 ≠ q.2} ⊕ {q : Fin m × Fin m // q.1 ≠ q.2}
  let s : Idx → MulAut (Fin m → Multiplicative (ZMod p)) :=
    Sum.elim (fun i => SpCoord.sgnAut i)
      (Sum.elim (fun q => SpCoord.permAut (Equiv.swap q.1.1 q.1.2))
        (fun q => SpCoord.sgnAut q.1.1 * SpCoord.sgnAut q.1.2 *
          SpCoord.permAut (Equiv.swap q.1.1 q.1.2)))
  let w : Idx → StatedOmega (StatedQuadMinus (m + 1) K b c) :=
    Sum.elim (fun i => w₁ i)
      (Sum.elim (fun q => w₂ q.1.1 q.1.2 q.2)
        (fun q => w₁ q.1.2 * w₂ q.1.1 q.1.2 q.2 * (w₁ q.1.2)⁻¹))
  let S : Idx → Subgroup (StatedOmega (StatedQuadMinus (m + 1) K b c)) :=
    Sum.elim (fun i => (omMinusLongBlock K b c i).subgroupOf
        (StatedOmega (StatedQuadMinus (m + 1) K b c)))
      (Sum.elim (fun q => (omMinusShortBlock K q.1.1 q.1.2).subgroupOf
          (StatedOmega (StatedQuadMinus (m + 1) K b c)))
        (fun q => ((omMinusShortBlock K q.1.1 q.1.2).subgroupOf
            (StatedOmega (StatedQuadMinus (m + 1) K b c))).map
          (MulAut.conj (w₁ q.1.2)).toMonoidHom))
  have hS : IsSimpleGroup (StatedOmega (StatedQuadMinus (m + 1) K b c)) := by
    have hproj : IsSimpleGroup (StatedProj (StatedOmega (StatedQuadMinus (m + 1) K b c))) :=
      CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_statedProj_statedOmega_quadMinus
        (n := m + 1) (by omega) hirr
    have hZ : Subgroup.center (StatedOmega (StatedQuadMinus (m + 1) K b c)) = ⊥ :=
      center_statedOmega_quadMinus_eq_bot (by omega) hirr
    have hscal_center : (StatedScalars (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K).subgroupOf
        (StatedOmega (StatedQuadMinus (m + 1) K b c)) ≤
        Subgroup.center (StatedOmega (StatedQuadMinus (m + 1) K b c)) := by
      intro x hx
      rw [Subgroup.mem_subgroupOf] at hx
      rw [StatedScalars, ← Matrix.GeneralLinearGroup.center_eq_range_scalar] at hx
      rw [Subgroup.mem_center_iff] at hx
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (by simpa using hx (y : GL _ K))
    have hscal : (StatedScalars (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K).subgroupOf
        (StatedOmega (StatedQuadMinus (m + 1) K b c)) = ⊥ := by
      rw [eq_bot_iff]
      exact hscal_center.trans (le_of_eq hZ)
    have eProj : StatedProj (StatedOmega (StatedQuadMinus (m + 1) K b c)) ≃*
        StatedOmega (StatedQuadMinus (m + 1) K b c) :=
      (QuotientGroup.quotientMulEquivOfEq hscal).trans QuotientGroup.quotientBot
    haveI : IsSimpleGroup (StatedProj (StatedOmega (StatedQuadMinus (m + 1) K b c))) := hproj
    exact eProj.symm.isSimpleGroup
  have hnc : ∃ a b : StatedOmega (StatedQuadMinus (m + 1) K b c), a * b ≠ b * a := by
    by_contra h
    push Not at h
    haveI := hS
    have htop : Subgroup.center (StatedOmega (StatedQuadMinus (m + 1) K b c)) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [Subgroup.mem_center_iff]
      intro y
      exact (h x y).symm
    have hZ : Subgroup.center (StatedOmega (StatedQuadMinus (m + 1) K b c)) = ⊥ :=
      center_statedOmega_quadMinus_eq_bot (by omega) hirr
    have h1 : (1 : StatedOmega (StatedQuadMinus (m + 1) K b c)) = 1 := rfl
    have hbot : (⊤ : Subgroup (StatedOmega (StatedQuadMinus (m + 1) K b c))) = ⊥ := by
      rw [← htop, hZ]
    obtain ⟨x, y, hxy⟩ := exists_pair_ne (StatedOmega (StatedQuadMinus (m + 1) K b c))
    refine hxy ?_
    have hx1 : x = 1 := by
      have hxmem : x ∈ (⊥ : Subgroup (StatedOmega (StatedQuadMinus (m + 1) K b c))) := by
        rw [← hbot]; exact Subgroup.mem_top x
      simpa using hxmem
    have hy1 : y = 1 := by
      have hymem : y ∈ (⊥ : Subgroup (StatedOmega (StatedQuadMinus (m + 1) K b c))) := by
        rw [← hbot]; exact Subgroup.mem_top y
      simpa using hymem
    rw [hx1, hy1]
  have hchev := ggKGOmM_isChevSimple_statedOmega (K := K) (n := m + 1) (by omega) hirr
  refine RealKGModelRoot.ggKGRootDatumAt_of_model hp hτ rfl w s S ?_ ?_ ?_ ?_ ?_ ?_
  · rintro (i | q | q) f
    · exact hw₁' i f
    · exact hw₂' q.1.1 q.1.2 q.2 f
    · exact ggKGOmM_negWeyl hζ (hw₁' q.1.2) (hw₂' q.1.1 q.1.2 q.2) f
  · rintro (i | q | q)
    · exact Subgroup.mem_subgroupOf.mpr (hw₁ i)
    · exact Subgroup.mem_subgroupOf.mpr (hw₂ q.1.1 q.1.2 q.2)
    · refine Subgroup.mem_map_of_mem (MulAut.conj (w₁ q.1.2)).toMonoidHom ?_
      exact Subgroup.mem_subgroupOf.mpr (hw₂ q.1.1 q.1.2 q.2)
  · rintro (i | q | q)
    · exact isComponentOf_omMinusLongBlock hK hirr hp hp2 hζ hζo i
    · exact isComponentOf_omMinusShortBlock hK hirr hp hp2 hζ hζo q.2
    · exact ggKGOmM_isComponentOf_negShort hK hirr hp hp2 hζ hζo q.2 (w₁ q.1.2) (hw₁' q.1.2)
  · rintro (i | q | q)
    · exact dvd_card_omMinusLongBlock hirr hpq i
    · exact dvd_card_omMinusShortBlock hK hpq q.2
    · exact ggKGOmM_dvd_card_negShort hK hpq q.2 (w₁ q.1.2)
  · intro g u huact hu2 hcard
    have hcomm : ∀ f, ((g : StatedOmega (StatedQuadMinus (m + 1) K b c)) :
        GL (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K) * omMinusTorusGL hζ f =
        omMinusTorusGL hζ (u f) * ((g : StatedOmega (StatedQuadMinus (m + 1) K b c)) :
          GL (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K) := by
      intro f
      have h := congrArg (fun x : StatedOmega (StatedQuadMinus (m + 1) K b c) =>
        (x : GL (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K)) (huact f)
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_omMinusTorus] at h
      rw [← h]
      group
    obtain ⟨j, ε, hε, hrel⟩ :=
      ggKGOmM_monomial_tail hp hζ hζo ((g : StatedOmega (StatedQuadMinus (m + 1) K b c)) :
        GL (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K) u hcomm
    have husp : SpCoord.IsSignedPerm ⇑u := ggKGOmM_isSignedPerm_of_monomial hp hε hrel
    rcases RealKGSignedRefl.signedRefl_cases hp hp2 husp hu2 hcard with ⟨a, ha⟩ | ⟨x, hx⟩
    · exact ⟨Sum.inl a, ha.symm⟩
    · rcases x with ⟨⟨⟨i, j⟩, hij⟩, b⟩
      cases b
      · exact ⟨Sum.inr (Sum.inl ⟨(i, j), hij.ne⟩), hx.symm⟩
      · exact ⟨Sum.inr (Sum.inr ⟨(i, j), hij.ne⟩), hx.symm⟩
  · intro a ha J hJ hJa
    obtain ⟨f, rfl⟩ := ha
    have hap : (omMinusTorus (m := m) b c hζ f) ^ p = 1 := by
      rw [← map_pow, ← map_one (omMinusTorus (m := m) b c hζ)]
      congr 1
      funext j
      apply Multiplicative.toAdd.injective
      rw [SpCoord.toAdd_pow_apply, ZMod.natCast_self, zero_mul]
      simp
    exact ggKG_layer_of_chevSimple hS hnc hchev hp hp2 hap hJ hJa

theorem ggKGRootDatum_statedOmegaMinus
    {K : Type} [Field K] [Finite K] [CharP K 2] {m p : ℕ} (hm : 3 ≤ m)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    GGKGRootDatum p m (StatedOmega (StatedQuadMinus (m + 1) K b c)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζo⟩ := exists_prime_orderOf_dvd_card' p (by rw [Nat.card_units (α := K)]; exact hpq)
  have hζ : ζ ^ p = 1 := by rw [← hζo]; exact pow_orderOf_eq_one ζ
  intro E hEab h3 hmE hsc
  obtain ⟨α, hα⟩ := exists_mulEquiv_eq_map_omMinusTorus hp2 hirr hζ hζo (E := E) hEab hmE
  have hroot := ggKGRootDatumAt_omMinusTorus (m := m) hm hp hp2 hirr hζo hζ
  refine ggKGRootDatumAt_of_mulEquiv α.symm ?_
  rw [hα, Subgroup.map_map]
  simpa using hroot

end CFSG.StandardType

end
