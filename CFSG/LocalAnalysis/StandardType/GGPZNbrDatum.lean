module

public import CFSG.LocalAnalysis.StandardType.GGPZTrivJ
public import CFSG.LocalAnalysis.StandardType.GGResXDatumSurj
public import CFSG.LocalAnalysis.StandardType.GGPZWeylType
public import CFSG.LocalAnalysis.StandardType.GGPZCartanRank
public import CFSG.LocalAnalysis.StandardType.GGPZFixA
public import CFSG.LocalAnalysis.StandardType.GGPZFixTwA
public import CFSG.LocalAnalysis.StandardType.GGPZFixD4
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGPZNbrDatum : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (y : G) (K : Subgroup G) (labJ labX : LargeEvenLabel)
    (X : Subgroup G) (m : ℕ) (z : ↥Bs), GGPZPrem p B Bs x L D J y K labJ labX X m z →
    ∀ Y : Subgroup G, LargeEvenPComponent p (Subgroup.centralizer ({(z : G)} : Set G)) Y →
      J ≤ Y → Bs ≤ Subgroup.normalizer (Y : Set G) → GGNbr p B x D J (z : G) Y →
      GGResXDatumSurj p Bs Y

theorem ggWeylTypeData_card_ne_zero {r n c : ℕ} (h : GGWeylTypeData r n c) : n ≠ 0 := by
  rcases h with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ |
    ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ <;> positivity

theorem ggPZ_prem_p_ne_two {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    {labJ labX : LargeEvenLabel} {X : Subgroup G} {m : ℕ} {z : ↥Bs}
    (h : GGPZPrem p B Bs x L D J y K labJ labX X m z) : p ≠ 2 := by
  obtain ⟨-, -, hΛJ, -, -, -, hrow, -⟩ := h
  have hn1 : 1 ≤ labJ.n := hΛJ.1
  obtain ⟨hrowTN, -⟩ := hrow
  rcases hrowTN with ⟨-, hpq, -, -⟩ | ⟨-, hpq, -, -⟩ | ⟨-, hp3, -, -⟩ | ⟨-, hp3, -, -⟩
  · rintro rfl
    obtain ⟨k, hk⟩ := hpq
    obtain ⟨j, hj⟩ : 2 ∣ 2 ^ labJ.n := dvd_pow_self 2 (by omega)
    have : 0 < 2 ^ labJ.n := by positivity
    omega
  · rintro rfl
    obtain ⟨k, hk⟩ := hpq
    obtain ⟨j, hj⟩ : 2 ∣ 2 ^ labJ.n := dvd_pow_self 2 (by omega)
    have : 0 < 2 ^ labJ.n := by positivity
    omega
  · intro h2
    rw [hp3] at h2
    omega
  · intro h2
    rw [hp3] at h2
    omega

theorem ggPZ_fixed_trivial {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    {labJ labX : LargeEvenLabel} {X : Subgroup G} {m : ℕ} {z : ↥Bs}
    (hZ : ¬ p ∣ Nat.card ↥(Subgroup.center ↥J))
    (h : GGPZPrem p B Bs x L D J y K labJ labX X m z) :
    ∀ a ∈ Bs ⊓ J, (∀ g ∈ J, g ∈ Subgroup.normalizer ((Bs ⊓ J : Subgroup G) : Set G) →
      g * a * g⁻¹ = a) → a = 1 := by
  have hp2 : p ≠ 2 := ggPZ_prem_p_ne_two h
  obtain ⟨hE, hDBs, hDcent, hint, hprod, hmr, hrank2, -, hJcard⟩ := ggPZ_prem_facts hZ h
  obtain ⟨hH, -, hΛJ, -, hJlab, -, hrow, -⟩ := h
  have hDJ : LargeEvenStdSub p B x L D J := hH.1.2.2
  have hJq : CFSG.IsQuasisimple ↥J :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥J).1
      hDJ.1.2.2.2.2.2.1.2.2
  have hEJabel : IsElemAbelian p (Bs ⊓ J) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun g hg => hE.2 g hg.1⟩
    have h1 := hE.1.is_comm.comm ⟨a, a.2.1⟩ ⟨b, b.2.1⟩
    exact Subtype.ext (congrArg (fun t : ↥Bs => (t : G)) h1)
  obtain ⟨hrowTN, -⟩ := hrow
  rcases hrowTN with ⟨hJt, hpq, hpl, -⟩ | ⟨hJt, hpq, hpl, -⟩ | ⟨hJe, hp3, hpq, -⟩ |
      ⟨hJe, hp3, hpq, -⟩
  · have hJlab' : GGHasLabel ⟨.A, labJ.rank, labJ.n⟩ (↥J ⧸ Subgroup.center ↥J) := by
      cases labJ
      simp only at hJt hJlab ⊢
      subst hJt
      exact hJlab
    exact ggPZ_fixed_trivial_typeA hp2 hrank2 hpq hpl hJlab' hJq hZ inf_le_right hEJabel hJcard
  · have hJlab' : GGHasLabel ⟨.twA, labJ.rank, labJ.n⟩ (↥J ⧸ Subgroup.center ↥J) := by
      cases labJ
      simp only at hJt hJlab ⊢
      subst hJt
      exact hJlab
    exact ggPZ_fixed_trivial_twA hp2 hrank2 hpq hpl hJlab' hJq hZ inf_le_right hEJabel hJcard
  · subst hp3
    have hrk4 : labJ.rank = 4 := congrArg LargeEvenLabel.rank hJe
    have hJlab' : GGHasLabel ⟨.D, 4, labJ.n⟩ (↥J ⧸ Subgroup.center ↥J) := hJe ▸ hJlab
    exact ggPZ_fixed_trivial_D4 (Or.inl hpq) hJlab' hJq hZ inf_le_right hEJabel (hrk4 ▸ hJcard)
  · subst hp3
    have hrk4 : labJ.rank = 4 := congrArg LargeEvenLabel.rank hJe
    have hJlab' : GGHasLabel ⟨.D, 4, labJ.n⟩ (↥J ⧸ Subgroup.center ↥J) := hJe ▸ hJlab
    exact ggPZ_fixed_trivial_D4 (Or.inr hpq) hJlab' hJq hZ inf_le_right hEJabel (hrk4 ▸ hJcard)

theorem ggPZEndpointNbr_of_datum
    (hM : GGPZMultInput) (hD : GGPZNbrDatum) : GGPZEndpointNbr := by
  classical
  intro G _ _ p _ B Bs x L D J y K labJ labX X m z h Y hY hJY hBsY hnbr
  have hZ : ¬ p ∣ Nat.card ↥(Subgroup.center ↥J) := hM G p B Bs x L D J y K labJ labX X m z h
  have hp2 : p ≠ 2 := ggPZ_prem_p_ne_two h
  obtain ⟨hE, hDBs, hDcent, hint, hprod, hmr, hrank2, -, hJcard⟩ := ggPZ_prem_facts hZ h
  have hfix := ggPZ_fixed_trivial hZ h
  have hdat := hD G p B Bs x L D J y K labJ labX X m z h Y hY hJY hBsY hnbr
  obtain ⟨-, -, -, -, -, -, -, -, hBscard, -, -, -, hzx, -⟩ := h
  have hz1 : z ≠ 1 := fun hz1 => hzx (by simp [hz1])
  have hYz : Y ≤ Subgroup.centralizer ({(z : G)} : Set G) := hY.1
  obtain ⟨Λ, hΛF, hΛD, M, C, V, hVg, hVm, ι, φ, hh, α, hMw, hC, hlin, hrefl, hαh, f, hfs,
    hf⟩ := hdat
  have hclos : ggAutomizer Y Bs = Subgroup.closure (Set.range φ) :=
    ggAutomizer_eq_closure_of_surj f hfs hf
  have : Finite V := Finite.of_equiv ↥Bs (Additive.ofMul.trans ι.toEquiv)
  have : Module.Finite (ZMod p) V := Module.Finite.of_finite
  have hcardV : Nat.card V = p ^ m := (card_eq_of_ggLin ι).symm.trans hBscard
  have hfr : Module.finrank (ZMod p) V = m := by
    have h1 : Nat.card V = Nat.card (ZMod p) ^ Module.finrank (ZMod p) V :=
      Module.natCard_eq_pow_finrank
    rw [Nat.card_zmod, hcardV] at h1
    exact (Nat.pow_right_injective (Nat.Prime.two_le Fact.out) h1).symm
  have hAfix : ∀ φ' ∈ ggAutomizer Y Bs, φ' z = z := by
    intro φ' hφ'
    obtain ⟨g, hgY, hgN, hg⟩ := mem_ggAutomizer_iff.mp hφ'
    refine Subtype.ext ?_
    rw [hg z]
    have hc : (z : G) * g = g * (z : G) := Subgroup.mem_centralizer_iff.mp (hYz hgY) z rfl
    rw [← hc, mul_assoc, mul_inv_cancel, mul_one]
  have hφmem : ∀ i, φ i ∈ ggAutomizer Y Bs := fun i => by
    have h1 := (f (M.simple i)).2
    rwa [hf i] at h1
  set z' : V := ι (Additive.ofMul z) with hz'
  have hz'0 : z' ≠ 0 := by
    intro h0
    have h1 : Additive.ofMul z = 0 := ι.injective (h0.trans (map_zero ι).symm)
    exact hz1 (ofMul_eq_zero.mp h1)
  have hh_ne : ∀ i, hh i ≠ 0 := by
    intro i hi
    have h1 : φ i = 1 := by
      refine ggLin_injective (p := p) ι (LinearEquiv.ext fun w => ?_)
      rw [hlin i w, hi, smul_zero, sub_zero, map_one]
      rfl
    obtain ⟨-, hcard⟩ := hrefl i
    have h2 : Nat.card {b : ↥Bs // φ i b = b} = Nat.card ↥Bs :=
      Nat.card_congr (Equiv.subtypeUnivEquiv fun b => by rw [h1]; rfl)
    rw [h2] at hcard
    have hpos : 0 < Nat.card ↥Bs := Nat.card_pos
    have : p = 1 := by
      have h3 : Nat.card ↥Bs * p = Nat.card ↥Bs * 1 := by rw [mul_one]; exact hcard
      exact Nat.eq_of_mul_eq_mul_left hpos h3
    exact (Nat.Prime.one_lt Fact.out).ne' this
  have hα0 : ∀ i, α i z' = 0 := by
    intro i
    have h1 : ggLin (p := p) ι (φ i) z' = z' := (ggLin_fix_iff ι (φ i) z).mp (hAfix (φ i) (hφmem i))
    rw [hlin i z'] at h1
    have h2 : α i z' • hh i = 0 := sub_eq_self.mp h1
    exact (smul_eq_zero.mp h2).resolve_right (hh_ne i)
  have hrle : Fintype.card Λ ≤ m := by
    have := ggPZ_card_le_finrank hp2 hMw hC hh α hαh hz'0 hα0
    rwa [hfr] at this
  let F : Subgroup ↥Bs :=
    { carrier := {b | ∀ φ' ∈ ggAutomizer Y Bs, φ' b = b}
      one_mem' := fun φ' _ => map_one φ'
      mul_mem' := fun {a b} ha hb φ' hφ' => by rw [map_mul, ha φ' hφ', hb φ' hφ']
      inv_mem' := fun {a} ha φ' hφ' => by rw [map_inv, ha φ' hφ'] }
  let a : V →ₗ[ZMod p] (Λ → ZMod p) := LinearMap.pi α
  have hFix : ∀ v ∈ LinearMap.ker a, Additive.toMul (ι.symm v) ∈ F := by
    intro v hv φ' hφ'
    have hα : ∀ i, α i v = 0 := fun i => congrFun (LinearMap.mem_ker.mp hv) i
    rw [hclos] at hφ'
    have hgen : ∀ i, φ i (Additive.toMul (ι.symm v)) = Additive.toMul (ι.symm v) := by
      intro i
      refine (ggLin_fix_iff (p := p) ι (φ i) _).mpr ?_
      rw [ofMul_toMul, ι.apply_symm_apply, hlin i v, hα i, zero_smul, sub_zero]
    have hle : Subgroup.closure (Set.range φ) ≤
        MulAction.stabilizer (MulAut ↥Bs) (Additive.toMul (ι.symm v)) := by
      rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact MulAction.mem_stabilizer_iff.mpr (by simpa [MulAut.smul_def] using hgen i)
    simpa [MulAut.smul_def] using MulAction.mem_stabilizer_iff.mp (hle hφ')
  have hkerF : p ^ (m - Fintype.card Λ) ≤ Nat.card F := by
    have h1 : Nat.card (LinearMap.ker a) =
        p ^ Module.finrank (ZMod p) (LinearMap.ker a) := by
      have := Module.natCard_eq_pow_finrank (K := ZMod p) (V := LinearMap.ker a)
      rwa [Nat.card_zmod] at this
    have h2 : m - Fintype.card Λ ≤ Module.finrank (ZMod p) (LinearMap.ker a) := by
      have h3 := LinearMap.finrank_range_add_finrank_ker a
      have h4 : Module.finrank (ZMod p) (LinearMap.range a) ≤ Fintype.card Λ := by
        have := Submodule.finrank_le (LinearMap.range a)
        simpa using this
      omega
    have h5 : Nat.card (LinearMap.ker a) ≤ Nat.card F := by
      refine Nat.card_le_card_of_injective
        (fun v : LinearMap.ker a => (⟨Additive.toMul (ι.symm v.1), hFix v.1 v.2⟩ : F)) ?_
      intro v w hvw
      have := congrArg Subtype.val hvw
      exact Subtype.ext (ι.symm.injective (Additive.toMul.injective this))
    calc p ^ (m - Fintype.card Λ) ≤ p ^ Module.finrank (ZMod p) (LinearMap.ker a) :=
          Nat.pow_le_pow_right (Nat.Prime.pos Fact.out) h2
      _ = Nat.card (LinearMap.ker a) := h1.symm
      _ ≤ Nat.card F := h5
  have hDc : ∀ g ∈ J, ∀ d ∈ D, g * d * g⁻¹ = d := fun g hg d hd => by
    have hc : g * d = d * g := Subgroup.mem_centralizer_iff.mp (hDcent hd) g hg
    rw [hc]
    group
  have hsplit : ∀ g d a' : G, g ∈ J → d ∈ D → g * (a' * d) * g⁻¹ = (g * a' * g⁻¹) * d := by
    intro g d a' hg hd
    calc g * (a' * d) * g⁻¹ = (g * a' * g⁻¹) * (g * d * g⁻¹) := by group
      _ = (g * a' * g⁻¹) * d := by rw [hDc g hg d hd]
  have hBsmem : ∀ g ∈ J, g ∈ Subgroup.normalizer ((Bs ⊓ J : Subgroup G) : Set G) →
      ∀ x ∈ Bs, g * x * g⁻¹ ∈ Bs := by
    intro g hgJ hgN x hx
    obtain ⟨a', ha', d', hd', rfl⟩ := hprod x hx
    rw [hsplit g d' a' hgJ hd']
    exact Bs.mul_mem ((Subgroup.mem_normalizer_iff.mp hgN a').mp ha').1 (hDBs hd')
  have hFD : ∀ b : ↥Bs, b ∈ F → (b : G) ∈ D := by
    intro b hb
    obtain ⟨a', ha', d', hd', hbad⟩ := hprod b b.2
    have ha1 : a' = 1 := by
      refine hfix a' ha' ?_
      intro g hgJ hgN
      have hgBs : g ∈ Subgroup.normalizer (Bs : Set G) := by
        rw [Subgroup.mem_normalizer_iff]
        intro x
        refine ⟨fun hx => hBsmem g hgJ hgN x hx, fun hx => ?_⟩
        have hgN' : g⁻¹ ∈ Subgroup.normalizer ((Bs ⊓ J : Subgroup G) : Set G) :=
          Subgroup.inv_mem _ hgN
        have := hBsmem g⁻¹ (J.inv_mem hgJ) hgN' _ hx
        simpa [mul_assoc] using this
      have hφ : ggConjAut Bs hgBs ∈ ggAutomizer Y Bs :=
        ggAutomizer_mono Bs hJY (ggConjAut_mem_ggAutomizer hgJ hgBs)
      have h1 := congrArg Subtype.val (hb _ hφ)
      rw [ggConjAut_apply, hbad, hsplit g d' a' hgJ hd'] at h1
      exact mul_right_cancel h1
    rw [hbad, ha1, one_mul]
    exact hd'
  have hDcard : Nat.card ↥D ≤ p ^ (m - labJ.rank) := by
    have hinj : Function.Injective (fun x : ↥(Bs ⊓ J) × ↥D =>
        (⟨(x.1 : G) * (x.2 : G), Bs.mul_mem x.1.2.1 (hDBs x.2.2)⟩ : ↥Bs)) := by
      intro x y hxy
      have h1 : (x.1 : G) * x.2 = y.1 * y.2 := congrArg Subtype.val hxy
      have h2 : ((y.1 : G)⁻¹ * x.1) = y.2 * (x.2 : G)⁻¹ := by
        calc ((y.1 : G)⁻¹ * x.1) = (y.1 : G)⁻¹ * (x.1 * x.2) * (x.2 : G)⁻¹ := by group
          _ = (y.1 : G)⁻¹ * (y.1 * y.2) * (x.2 : G)⁻¹ := by rw [h1]
          _ = y.2 * (x.2 : G)⁻¹ := by group
      have h3 : ((y.1 : G)⁻¹ * x.1) ∈ (Bs ⊓ J) ⊓ D :=
        ⟨(Bs ⊓ J).mul_mem ((Bs ⊓ J).inv_mem y.1.2) x.1.2, h2 ▸ D.mul_mem y.2.2 (D.inv_mem x.2.2)⟩
      rw [hint, Subgroup.mem_bot] at h3
      have h4 : (x.1 : G) = y.1 := by
        have := congrArg (fun t => (y.1 : G) * t) h3
        simpa using this
      have h5 : (x.2 : G) = y.2 := by
        have h6 := h1
        rw [h4] at h6
        exact mul_left_cancel h6
      exact Prod.ext (Subtype.ext h4) (Subtype.ext h5)
    have h1 := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_prod, hJcard, hBscard] at h1
    have hml : p ^ m = p ^ labJ.rank * p ^ (m - labJ.rank) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hml] at h1
    exact Nat.le_of_mul_le_mul_left h1 (pow_pos (Nat.Prime.pos Fact.out) _)
  have hFcard : Nat.card F ≤ Nat.card ↥D := by
    refine Nat.card_le_card_of_injective
      (fun b : F => (⟨(b.1 : G), hFD b.1 b.2⟩ : ↥D)) ?_
    intro b b' h
    have h' : ((b.1 : ↥Bs) : G) = ((b'.1 : ↥Bs) : G) := congrArg (fun d : ↥D => (d : G)) h
    exact Subtype.ext (Subtype.ext h')
  have hlr : labJ.rank ≤ Fintype.card Λ := by
    have h1 : p ^ (m - Fintype.card Λ) ≤ p ^ (m - labJ.rank) :=
      hkerF.trans (hFcard.trans hDcard)
    have h2 := (Nat.pow_le_pow_iff_right (Nat.Prime.one_lt (Fact.out : p.Prime))).mp h1
    omega
  have hWT := ggWeylTypeData_of_isWeylMatrix hMw
  have : Finite M.Group := Nat.finite_of_card_ne_zero (ggWeylTypeData_card_ne_zero hWT)
  let f' : M.Group →* MulAut ↥Bs := (ggAutomizer Y Bs).subtype.comp f
  have hrange : ggAutomizer Y Bs ≤ f'.range := by
    intro φ' hφ'
    obtain ⟨w, hw⟩ := hfs ⟨φ', hφ'⟩
    exact ⟨w, by simpa [f'] using congrArg Subtype.val hw⟩
  exact ⟨Fintype.card Λ, Nat.card M.Group, Nat.card ↥(Subgroup.center M.Group), M.Group,
    inferInstance, inferInstance, f', hWT, hlr, hrle, rfl, rfl, hrange⟩

end CFSG.StandardType

end
