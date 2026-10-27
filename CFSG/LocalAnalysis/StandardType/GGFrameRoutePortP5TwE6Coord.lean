module

public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP10E6Real
import CFSG.Mathlib.RingTheory.UnitOrderOf
import CFSG.LocalAnalysis.StandardType.GGTwE6EndNodeThreeTorus

public section

namespace CFSG.StandardType.FrameRoute.TwE6Model

open CFSG CFSG.Assembly CFSG.Open CFSG.StandardType CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Universal
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Lang.E6Descent
  CFSG.RankThree.Classical2 CFSG.StandardType.NoOffTwE6Three
  CFSG.StandardType.TableBExc.E6Three CFSG.StandardType.TwE6DD2

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem coord_of_mulEquiv {G M : Type} [Group G] [Group M] {Bs : Subgroup G}
    (γ : ↥Bs →* M) {S : Subgroup M} (hS : γ.range = S)
    (e : Multiplicative (Fin Tag.E6.rank → ZMod 3) ≃* ↥S) :
    ∃ u : G → Fin Tag.E6.rank → ZMod 3,
      (∀ b (hb : b ∈ Bs), ((e (Multiplicative.ofAdd (u b)) : ↥S) : M) =
        (γ ⟨b, hb⟩)⁻¹) ∧
      (∀ b ∈ Bs, ∀ b' ∈ Bs, u (b * b') = u b + u b') ∧
      (∀ b (hb : b ∈ Bs), u b = 0 ↔ γ ⟨b, hb⟩ = 1) ∧ ∀ v, ∃ b ∈ Bs, u b = v := by
  classical
  have hmem : ∀ (b : G) (hb : b ∈ Bs), γ ⟨b, hb⟩ ∈ S := fun b hb =>
    hS ▸ ⟨⟨b, hb⟩, rfl⟩
  let u : G → Fin Tag.E6.rank → ZMod 3 := fun b =>
    if hb : b ∈ Bs then -Multiplicative.toAdd (e.symm ⟨γ ⟨b, hb⟩, hmem b hb⟩) else 0
  have hu : ∀ (b : G) (hb : b ∈ Bs),
      u b = -Multiplicative.toAdd (e.symm ⟨γ ⟨b, hb⟩, hmem b hb⟩) := fun b hb => by
    dsimp only [u]
    rw [dif_pos hb]
  refine ⟨u, ?_, ?_, ?_, ?_⟩
  · intro b hb
    have h1 : e (Multiplicative.ofAdd (u b)) = (⟨γ ⟨b, hb⟩, hmem b hb⟩ : ↥S)⁻¹ := by
      rw [hu b hb, ofAdd_neg, map_inv]
      congr 1
      simp
    simpa using congrArg (fun x : ↥S => (x : M)) h1
  · intro b hb b' hb'
    have hbb' : b * b' ∈ Bs := Bs.mul_mem hb hb'
    have h1 : (⟨γ ⟨b * b', hbb'⟩, hmem _ hbb'⟩ : ↥S) =
        ⟨γ ⟨b, hb⟩, hmem b hb⟩ * ⟨γ ⟨b', hb'⟩, hmem b' hb'⟩ := by
      refine Subtype.ext ?_
      change γ ⟨b * b', hbb'⟩ = γ ⟨b, hb⟩ * γ ⟨b', hb'⟩
      rw [show (⟨b * b', hbb'⟩ : ↥Bs) = ⟨b, hb⟩ * ⟨b', hb'⟩ from Subtype.ext rfl, map_mul]
    rw [hu (b * b') hbb', hu b hb, hu b' hb', h1, map_mul, toAdd_mul]
    abel
  · intro b hb
    rw [hu b hb, neg_eq_zero, toAdd_eq_zero, MulEquiv.map_eq_one_iff]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  · intro v
    have hx : ((e (Multiplicative.ofAdd (-v)) : ↥S) : M) ∈ γ.range := by
      rw [hS]
      exact (e (Multiplicative.ofAdd (-v))).2
    rw [MonoidHom.mem_range] at hx
    obtain ⟨b, hbγ⟩ := hx
    refine ⟨(b : G), b.2, ?_⟩
    have h1 : (⟨γ ⟨(b : G), b.2⟩, hmem _ b.2⟩ : ↥S) = e (Multiplicative.ofAdd (-v)) :=
      Subtype.ext hbγ
    rw [hu (b : G) b.2, h1, MulEquiv.symm_apply_apply, toAdd_ofAdd, neg_neg]

section LangCube


theorem conj_rootDiagUnit_zeta_mem_Rgrp {Ω : Type} [Field Ω] [IsAlgClosed Ω] {q : ℕ}
    {Fr : Ω →+* Ω} (hFr : ∀ c, Fr c = c ^ q) (h3 : 3 ∣ q + 1) {g : ModGL Tag.E6 Ω}
    (hg : g ∈ adjointGroup Tag.E6 Ω) (hgn : g⁻¹ * twistE6 Ω Fr g = TwistedDiag.n0 Ω)
    {ζ : Ωˣ} (hζ : ζ ^ 3 = 1) (w : Fin Tag.E6.rank → ZMod 3) :
    g * rootDiagUnit Tag.E6 (fun i => ζ ^ (w i).val) * g⁻¹ ∈ TwistedDiag.Rgrp Ω Fr :=
  conj_cubeTorus_le_Rgrp Fr hFr h3 hg hgn
    ⟨_, ⟨_, mem_cubeRootTuples.2 fun i => by
      rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow], rfl⟩, rfl⟩

theorem exists_mulEquiv_langCube {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (Fr : Ω →+* Ω)
    (hFr : ∀ c, Fr c = c ^ 2 ^ n) (h3 : 3 ∣ 2 ^ n + 1) {g : ModGL Tag.E6 Ω}
    (hg : g ∈ adjointGroup Tag.E6 Ω) (hgn : g⁻¹ * twistE6 Ω Fr g = TwistedDiag.n0 Ω)
    {ζ : Ωˣ} (hζ : orderOf ζ = 3) :
    ∃ e : Multiplicative (Fin Tag.E6.rank → ZMod 3) ≃* ↥(langCube hn hK σ hσ Fr hFr g),
      ∀ v, ∃ hv : g * rootDiagUnit Tag.E6 (fun i => ζ ^ (Multiplicative.toAdd v i).val) * g⁻¹ ∈
          TwistedDiag.Rgrp Ω Fr,
        ((e v : ↥(langCube hn hK σ hσ Fr hFr g)) :
            MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) =
          rgrpConjAut hn hK σ hσ Fr hFr ⟨_, hv⟩ := by
  have hζ3 : ζ ^ 3 = 1 := by rw [← hζ, pow_orderOf_eq_one]
  obtain ⟨Ψ, hΨinj, hΨrange, hΨ⟩ :=
    TwE6EndNode3.exists_cubeHom hn hK σ hσ Fr hFr h3 hg hgn hζ3 hζ
  have hrange : Ψ.range = langCube hn hK σ hσ Fr hFr g := by
    refine le_antisymm ?_ ?_
    · rintro y ⟨x, rfl⟩
      obtain ⟨hx, hΨx⟩ := hΨ x
      rw [hΨx, mem_langCube]
      exact ⟨zetaVec ζ hζ3 (Multiplicative.toAdd x), fun i => by
        rw [zetaVec_apply, ← pow_mul, mul_comm, pow_mul, hζ3, one_pow], hx, rfl⟩
    · intro y hy
      obtain ⟨x, hx⟩ := hΨrange y hy
      exact ⟨x, hx⟩
  refine ⟨(MonoidHom.ofInjective hΨinj).trans (MulEquiv.subgroupCongr hrange), ?_⟩
  intro v
  obtain ⟨hx, hΨv⟩ := hΨ v
  refine ⟨hx, ?_⟩
  change (Ψ v : MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) =
    rgrpConjAut hn hK σ hσ Fr hFr ⟨_, hx⟩
  exact hΨv

end LangCube

theorem exists_twE6Coord
    {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G} {n : ℕ}
    (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ n) (hn : 7 ≤ n) (hx : x ∈ Bs)
    (hx1 : x ≠ 1) (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hBstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hL : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twE6, 0, 1⟩) 3 Bs L) :
    n = 7 ∧ commutator ↥L = ⊤ ∧
      ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K ≃+* K)
        (hK : Nat.card K = (2 ^ 1) ^ 2) (hσ : ∀ c, σ c = c ^ 2 ^ 1)
        (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ 2 ^ 1)
        (θ : ↥L ⧸ Subgroup.center ↥L ≃* ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom))
        (g : ModGL Tag.E6 (AlgebraicClosure K)) (ζ : (AlgebraicClosure K)ˣ)
        (u : G → Fin Tag.E6.rank → ZMod 3),
        g ∈ adjointGroup Tag.E6 (AlgebraicClosure K) ∧
        g⁻¹ * twistE6 (AlgebraicClosure K) Fr g = TwistedDiag.n0 (AlgebraicClosure K) ∧
        orderOf ζ = 3 ∧
        (∀ b ∈ Bs, ∃ hb : g * rootDiagUnit Tag.E6 (fun i => ζ ^ (u b i).val) * g⁻¹ ∈
            TwistedDiag.Rgrp (AlgebraicClosure K) Fr,
          LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b)
            (rgrpConjAut le_rfl hK σ hσ Fr hFr ⟨_, hb⟩)) ∧
        (∀ b ∈ Bs, ∀ b' ∈ Bs, u (b * b') = u b + u b') ∧
        (∀ b ∈ Bs, u b = 0 ↔ b ∈ Subgroup.zpowers x) ∧
        ∀ v : Fin Tag.E6.rank → ZMod 3, ∃ b ∈ Bs, u b = v := by
  obtain ⟨hn7, hperf, F, instF, instFin, σ, hF, hσ, Fr, hFr, θ, D, g, hDinj, hDγ, hg, hgn,
    hS⟩ := p10real_langCube hBs hcard hn hx hx1 hN hker hBstar hL
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := charP_two_of_card (m := 2) (by rw [hF]; norm_num)
  haveI : CharP (AlgebraicClosure F) 2 :=
    charP_of_injective_algebraMap (algebraMap F (AlgebraicClosure F)).injective 2
  haveI : IsAlgClosed (AlgebraicClosure F) := AlgebraicClosure.isAlgClosed F
  have h3 : 3 ∣ 2 ^ 1 + 1 := by norm_num
  have h30 : (3 : AlgebraicClosure F) ≠ 0 :=
    three_ne_zero_of_dvd_card_add_one (ℓ := 2) le_rfl h3
  obtain ⟨ζ, hζ⟩ := CFSG.exists_unit_orderOf_eq_of_isAlgClosed (n := 3) h30
  obtain ⟨e, he⟩ := exists_mulEquiv_langCube (n := 1) le_rfl hF σ hσ Fr hFr h3 hg hgn hζ
  have hS' : (D.comp (ggGamma L hN)).range = langCube le_rfl hF σ hσ Fr hFr g := by
    rw [MonoidHom.range_comp, hS]
  obtain ⟨u, hu, hadd, hkeru, hsurj⟩ :=
    coord_of_mulEquiv (D.comp (ggGamma L hN)) hS' e
  have hInd : ∀ b ∈ Bs, ∃ hb : g * rootDiagUnit Tag.E6 (fun i => ζ ^ (u b i).val) * g⁻¹ ∈
      TwistedDiag.Rgrp (AlgebraicClosure F) Fr,
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b)
        (rgrpConjAut le_rfl hF σ hσ Fr hFr ⟨_, hb⟩) := by
    intro b hb
    obtain ⟨hv, hev⟩ := he (Multiplicative.ofAdd (u b))
    simp only [toAdd_ofAdd] at hv hev
    refine ⟨hv, ?_⟩
    have h1 : rgrpConjAut le_rfl hF σ hσ Fr hFr ⟨_, hv⟩ =
        ggLAut L θ ⟨b⁻¹, inv_mem (hN hb)⟩ := by
      rw [← hev, hu b hb]
      change (D (ggGamma L hN ⟨b, hb⟩))⁻¹ = ggLAut L θ ⟨b⁻¹, inv_mem (hN hb)⟩
      rw [show D (ggGamma L hN ⟨b, hb⟩) = ggLAut L θ ⟨b, hN hb⟩ by
        rw [hDγ ⟨b, hb⟩, ggBeta_eq], ← map_inv]
      congr 1
    rw [h1]
    intro l l' hll'
    rw [ggLAut_apply]
    congr 2
    apply Subtype.ext
    rw [normalizerMonoidHom_coe, hll', inv_inv]
  have hker' : ∀ b ∈ Bs, u b = 0 ↔ b ∈ Subgroup.zpowers x := by
    intro b hb
    rw [hkeru b hb, MonoidHom.comp_apply]
    have hD1 : D (ggGamma L hN ⟨b, hb⟩) = 1 ↔ ggGamma L hN ⟨b, hb⟩ = 1 := by
      rw [← map_one D, hDinj.eq_iff]
    rw [hD1, ggGamma_eq_one_iff L hN ⟨b, hb⟩, ← hker, Subgroup.mem_inf]
    exact ⟨fun h => ⟨hb, h⟩, fun h => h.2⟩
  exact ⟨hn7, hperf, F, instF, instFin, σ, hF, hσ, Fr, hFr, θ, g, ζ, u, hg, hgn,
    hζ, hInd, hadd, hker', hsurj⟩

end CFSG.StandardType.FrameRoute.TwE6Model

end
