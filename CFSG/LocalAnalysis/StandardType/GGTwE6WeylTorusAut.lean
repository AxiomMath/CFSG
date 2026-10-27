module

public import CFSG.LocalAnalysis.StandardType.GGTwE6WeylRealize
public import CFSG.LieType.Chevalley.RootDiagonalWeylTransporter
public import CFSG.RankThree.Chevalley.SteinbergBUF4CyclotomicFourDescent
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTwistedNormalForm
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE6ThreeWeylDiagGen
public import CFSG.LocalAnalysis.StandardType.GGNoTransvectionAutFrame
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutPSLRestField
public import CFSG.RankThree.Chevalley.SteinbergBNG2QPlusLocalCore
public import CFSG.RankThree.Chevalley.SteinbergBNF4NativeB2
public import CFSG.RankThree.Chevalley.SteinbergBUF4B2QuarticDescent
public import CFSG.RankThree.Chevalley.SteinbergBUF4CyclotomicFourTools

public section

namespace CFSG.StandardType

namespace ExcFrames

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Diag


theorem rootDiagUnit_mem_adjointGroup {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    (a : Fin τ.rank → Lˣ) : rootDiagUnit τ a ∈ adjointGroup τ L :=
  CFSG.RankThree.Chevalley.torusGroup_le_adjointGroup_of_any (rootDiagUnit_mem_torusGroup a)

end Diag

private theorem frameCoord_nsmul {τ : Tag} {p : ℕ} (m : ℕ) (s : Fin τ.rank → ZMod p) :
    frameCoord τ p (m • s) = m • frameCoord τ p s := by
  induction m with
  | zero => rw [zero_nsmul, zero_nsmul, frameCoord_zero]
  | succ m ih => rw [succ_nsmul, frameCoord_add, ih, succ_nsmul]

private theorem torusAct_nsmul_gen {τ : Tag} {p : ℕ} [NeZero p] (u : WeylGroup τ) (n : ℕ)
    (x : Fin τ.rank → ZMod p) :
    TableBExc.torusAct τ p u (n • x) = n • TableBExc.torusAct τ p u x := by
  rw [← NoTvAut.torusActHom_apply, ← NoTvAut.torusActHom_apply]
  exact map_nsmul (NoTvAut.torusActHom τ p u) n x

private theorem zmod_natCast_smul_eq_nsmul {ι : Type} {p : ℕ} (m : ℕ) (x : ι → ZMod p) :
    (m : ZMod p) • x = m • x := by
  funext i
  rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, nsmul_eq_mul]

private theorem units_map_entrywiseHom_frameDiag_of_nsmul
    {L : Type} [Field L] {p : ℕ} [NeZero p] {τ : Tag} {ζ : Lˣ} (hζ : ζ ^ p = 1)
    {δL : L ≃+* L} (m : ℕ) (hδLζ : Units.map (δL : L →+* L).toMonoidHom ζ = ζ ^ m)
    (s : Fin τ.rank → ZMod p) :
    Units.map (entrywiseHom (δL : L →+* L)) (frameDiag (τ := τ) ζ hζ s) =
      frameDiag (τ := τ) ζ hζ (m • s) := by
  rw [CFSG.RankThree.Chevalley.units_map_entrywiseHom_eq_baseChangeGL_self]
  rw [frameDiag, CFSG.LieType.Chevalley.baseChangeGL_rootDiagUnit]
  congr 1
  funext i
  show Units.map (δL : L →+* L).toMonoidHom
      (TableBExc.E6Three.zetaVec ζ hζ (frameCoord τ p s) i) =
    TableBExc.E6Three.zetaVec ζ hζ (frameCoord τ p (m • s)) i
  rw [TableBExc.E6Three.zetaVec_apply, TableBExc.E6Three.zetaVec_apply, map_pow, hδLζ, ← pow_mul]
  have hfc : frameCoord τ p (m • s) i = m • (frameCoord τ p s i) := by
    rw [congrFun (frameCoord_nsmul (τ := τ) (p := p) m s) i, Pi.smul_apply]
  have hB : (m • (frameCoord τ p s i)).val = m * (frameCoord τ p s i).val % p := by
    have h1 : m • (frameCoord τ p s i) = ((m * (frameCoord τ p s i).val : ℕ) : ZMod p) := by
      rw [nsmul_eq_mul, Nat.cast_mul, ZMod.natCast_zmod_val]
    rw [h1, ZMod.val_natCast]
  rw [hfc, hB, pow_eq_pow_mod (m * (frameCoord τ p s i).val) hζ]

private theorem exists_normalForm_twistedE6_sharp
    {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f)
    {θ : K →+* K} (hθ : σ.toRingHom = θ) {n : ℕ}
    (α : MulAut ↥(graphFixedRootGroup TwistTag.E6 K θ)) (hα : α ^ n = 1) :
    ∃ (g : ↥(graphFixedRootGroup TwistTag.E6 K θ)) (b : Fin TwistTag.E6.tag.rank → Kˣ)
      (δ : K ≃+* K), δ ^ n = 1 ∧
      ∀ h : ↥(graphFixedRootGroup TwistTag.E6 K θ),
        (α h : ModGL TwistTag.E6.tag K) =
          ((g : ModGL TwistTag.E6.tag K) * rootDiagUnit TwistTag.E6.tag b) *
            Units.map (entrywiseHom δ.toRingHom) (h : ModGL TwistTag.E6.tag K) *
            ((g : ModGL TwistTag.E6.tag K) * rootDiagUnit TwistTag.E6.tag b)⁻¹ := by
  subst hθ
  obtain ⟨-, -, -, -, -, hΔ, hfa, hex, ⟨Θ, hΘ, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hf K hK σ hσ
  obtain ⟨g, u, δ, hgαu⟩ := hex α
  have hδn : δ ^ n = 1 := by
    have h1 : (Θ α) ^ n = 1 := by rw [← map_pow, hα, map_one]
    rwa [hΘ α g u δ hgαu] at h1
  refine ⟨g, compatDiag TwistTag.E6 σ.toRingHom u, δ, hδn, ?_⟩
  intro h
  have h1 : ((fieldActor σ δ h : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) :
      ModGL TwistTag.E6.tag K) = Units.map (entrywiseHom δ.toRingHom)
        (h : ModGL TwistTag.E6.tag K) := hfa δ h
  have h2 := hΔ u (fieldActor σ δ h)
  rw [hgαu]
  simp only [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [h2, h1]
  simp only [mul_inv_rev, mul_assoc]

private theorem langFrame_core
    {f p : ℕ} [Fact p.Prime] [NeZero p] (hp5 : 5 ≤ p) (hf : 1 ≤ f)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K)
    (hσ : ∀ c, σ c = c ^ (2 ^ f)) (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L]
    [CharP L 2] {ζK : Kˣ} (hζKord : orderOf ζK = p)
    (hζ : (Units.map (algebraMap K L).toMonoidHom ζK) ^ p = 1)
    {g₀ : ModGL TwistTag.E6.tag L} (hg₀C : g₀ ∈ adjointGroup TwistTag.E6.tag L)
    (ι₀ : Multiplicative (Fin TwistTag.E6.tag.rank → ZMod p) →*
      ↥(graphFixedRootGroup TwistTag.E6 K σ))
    (hbase : ∀ s : Fin TwistTag.E6.tag.rank → ZMod p,
      baseChangeGL (algebraMap K L)
        ((ι₀ (Multiplicative.ofAdd s) : _) : ModGL TwistTag.E6.tag K) =
        g₀ * frameDiag (τ := TwistTag.E6.tag) (Units.map (algebraMap K L).toMonoidHom ζK) hζ s *
          g₀⁻¹)
    (β : MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ))
    (hstab : ∀ b ∈ ι₀.range, β b ∈ ι₀.range)
    (g : ↥(graphFixedRootGroup TwistTag.E6 K σ)) (b : Fin TwistTag.E6.tag.rank → Kˣ) (δ : K ≃+* K)
    (hnf : ∀ h : ↥(graphFixedRootGroup TwistTag.E6 K σ),
      (β h : ModGL TwistTag.E6.tag K) =
        ((g : ModGL TwistTag.E6.tag K) * rootDiagUnit TwistTag.E6.tag b) *
          Units.map (entrywiseHom δ.toRingHom) (h : ModGL TwistTag.E6.tag K) *
          ((g : ModGL TwistTag.E6.tag K) * rootDiagUnit TwistTag.E6.tag b)⁻¹)
    (m : ℕ) (hcop : Nat.Coprime m p) (hδm : Units.map δ.toMonoidHom ζK = ζK ^ m) :
    ∃ w : WeylGroup TwistTag.E6.tag,
      ∀ s : Fin TwistTag.E6.tag.rank → ZMod p,
        β (ι₀ (Multiplicative.ofAdd s)) =
          ι₀ (Multiplicative.ofAdd ((m : ZMod p) • TableBExc.torusAct TwistTag.E6.tag p w s)) := by
  classical
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  let δL : L ≃+* L := IsAlgClosure.equivOfEquiv _ _ δ
  have hδL : ∀ c : K, δL (algebraMap K L c) = algebraMap K L (δ c) :=
    fun c => IsAlgClosure.equivOfEquiv_algebraMap _ _ δ c
  have hδLζ : Units.map (δL : L →+* L).toMonoidHom
      (Units.map (algebraMap K L).toMonoidHom ζK) =
      (Units.map (algebraMap K L).toMonoidHom ζK) ^ m := by
    refine Units.ext ?_
    change δL (algebraMap K L (ζK : K)) = (algebraMap K L (ζK : K)) ^ m
    rw [hδL, ← map_pow]
    congr 1
    simpa using congrArg Units.val hδm
  have hfixFrame : ∀ s : Fin TwistTag.E6.tag.rank → ZMod p,
      Units.map (entrywiseHom (δL : L →+* L))
        (frameDiag (τ := TwistTag.E6.tag) (Units.map (algebraMap K L).toMonoidHom ζK) hζ s) =
      frameDiag (τ := TwistTag.E6.tag) (Units.map (algebraMap K L).toMonoidHom ζK) hζ (m • s) :=
    fun s => units_map_entrywiseHom_frameDiag_of_nsmul hζ m hδLζ s
  let xK : ModGL TwistTag.E6.tag K :=
    (g : ModGL TwistTag.E6.tag K) * rootDiagUnit TwistTag.E6.tag b
  let xL : ModGL TwistTag.E6.tag L := baseChangeGL (algebraMap K L) xK
  let δg : ModGL TwistTag.E6.tag L := Units.map (entrywiseHom δL.toRingHom) g₀
  let y : ModGL TwistTag.E6.tag L := g₀⁻¹ * xL * δg
  have hxL_adj : xL ∈ adjointGroup TwistTag.E6.tag L := by
    dsimp only [xL, xK]
    rw [map_mul, CFSG.LieType.Chevalley.baseChangeGL_rootDiagUnit]
    refine mul_mem ?_ (rootDiagUnit_mem_adjointGroup _)
    exact CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup (algebraMap K L)
      (twistedFixedGroup_le_adjointGroup TwistTag.E6 K σ
        (graphFixedRootGroup_le TwistTag.E6 K σ g.2))
  have hδg_adj : δg ∈ adjointGroup TwistTag.E6.tag L :=
    CFSG.RankThree.Chevalley.SteinbergBN.units_map_entrywiseHom_mem_adjointGroup
      δL.toRingHom hg₀C
  have hyC : y ∈ adjointGroup TwistTag.E6.tag L :=
    mul_mem (mul_mem (inv_mem hg₀C) hxL_adj) hδg_adj
  have hbaseβ : ∀ s : Fin TwistTag.E6.tag.rank → ZMod p,
      baseChangeGL (algebraMap K L)
        ((β (ι₀ (Multiplicative.ofAdd s)) : _) : ModGL TwistTag.E6.tag K) =
        g₀ * (y * frameDiag (τ := TwistTag.E6.tag)
          (Units.map (algebraMap K L).toMonoidHom ζK) hζ (m • s) * y⁻¹) * g₀⁻¹ := by
    intro s
    have h1 := congrArg (baseChangeGL (algebraMap K L)) (hnf (ι₀ (Multiplicative.ofAdd s)))
    rw [map_mul, map_mul, map_inv] at h1
    rw [CFSG.RankThree.Chevalley.SteinbergBN.baseChangeGL_entrywise_comm δ δL hδL,
      hbase s] at h1
    simp only [map_mul, map_inv] at h1
    rw [hfixFrame s] at h1
    rw [h1]
    have hxL : xL = (baseChangeGL (algebraMap K L)) ↑g *
        (baseChangeGL (algebraMap K L)) (rootDiagUnit TwistTag.E6.tag b) := by
      dsimp only [xL, xK]
      rw [map_mul]
    rw [← hxL]
    have hD : g₀ * (y * frameDiag (τ := TwistTag.E6.tag)
        (Units.map (algebraMap K L).toMonoidHom ζK) hζ (m • s) * y⁻¹) * g₀⁻¹ =
        (g₀ * y) * frameDiag (τ := TwistTag.E6.tag)
          (Units.map (algebraMap K L).toMonoidHom ζK) hζ (m • s) * (g₀ * y)⁻¹ := by
      group
    have hz : g₀ * y = xL * δg := by
      rw [show y = g₀⁻¹ * xL * δg from rfl]
      group
    rw [hD, hz]
    simp only [mul_inv_rev, inv_inv, mul_assoc]
    rfl
  have himage : ∀ s : Fin TwistTag.E6.tag.rank → ZMod p,
      ∃ t : Fin TwistTag.E6.tag.rank → ZMod p,
        y * frameDiag (τ := TwistTag.E6.tag)
          (Units.map (algebraMap K L).toMonoidHom ζK) hζ (m • s) * y⁻¹ =
        frameDiag (τ := TwistTag.E6.tag)
          (Units.map (algebraMap K L).toMonoidHom ζK) hζ t := by
    intro s
    obtain ⟨t, ht⟩ := hstab _ ⟨Multiplicative.ofAdd s, rfl⟩
    refine ⟨Multiplicative.toAdd t, ?_⟩
    have h1 : baseChangeGL (algebraMap K L)
        ((β (ι₀ (Multiplicative.ofAdd s)) : _) : ModGL TwistTag.E6.tag K) =
        g₀ * frameDiag (τ := TwistTag.E6.tag)
          (Units.map (algebraMap K L).toMonoidHom ζK) hζ (Multiplicative.toAdd t) * g₀⁻¹ := by
      rw [← ht]
      exact hbase (Multiplicative.toAdd t)
    rw [hbaseβ s] at h1
    exact mul_left_cancel (mul_right_cancel h1)
  have hm_surj : ∀ t : Fin TwistTag.E6.tag.rank → ZMod p, ∃ s, m • s = t := by
    intro t
    let u : (ZMod p)ˣ := ZMod.unitOfCoprime m hcop
    have hu : (u : ZMod p) = (m : ZMod p) := ZMod.coe_unitOfCoprime m hcop
    refine ⟨(↑u⁻¹ : ZMod p) • t, ?_⟩
    calc m • ((↑u⁻¹ : ZMod p) • t)
        = (m : ZMod p) • ((↑u⁻¹ : ZMod p) • t) := by rw [zmod_natCast_smul_eq_nsmul]
      _ = (↑u : ZMod p) • ((↑u⁻¹ : ZMod p) • t) := by rw [hu]
      _ = ((↑u : ZMod p) * (↑u⁻¹ : ZMod p)) • t := by rw [smul_smul]
      _ = t := by
        rw [show (↑u : ZMod p) * (↑u⁻¹ : ZMod p) = 1 by
          rw [← Units.val_mul, mul_inv_cancel, Units.val_one], one_smul]
  have hVD : ∀ z ∈ Set.range (fun s : Fin TwistTag.E6.tag.rank → ZMod p =>
      frameDiag (τ := TwistTag.E6.tag) (Units.map (algebraMap K L).toMonoidHom ζK) hζ s),
      ∃ a : Fin TwistTag.E6.tag.rank → Lˣ, z = rootDiagUnit TwistTag.E6.tag a := by
    rintro z ⟨s, rfl⟩
    exact ⟨TableBExc.E6Three.zetaVec _ hζ (frameCoord TwistTag.E6.tag p s), rfl⟩
  have hgV : ∀ z ∈ Set.range (fun s : Fin TwistTag.E6.tag.rank → ZMod p =>
      frameDiag (τ := TwistTag.E6.tag) (Units.map (algebraMap K L).toMonoidHom ζK) hζ s),
      y * z * y⁻¹ ∈ Set.range (fun s : Fin TwistTag.E6.tag.rank → ZMod p =>
        frameDiag (τ := TwistTag.E6.tag) (Units.map (algebraMap K L).toMonoidHom ζK) hζ s) := by
    rintro z ⟨t, rfl⟩
    obtain ⟨s, rfl⟩ := hm_surj t
    obtain ⟨t', ht'⟩ := himage s
    exact ⟨t', ht'.symm⟩
  obtain ⟨w, hw⟩ :=
    NoOffE6Three.exists_conj_eq_canonicalRep_of_mem_normalizer_rootDiag
      (τ := TwistTag.E6.tag) (k := L) hVD hyC hgV
  refine ⟨w, fun s => ?_⟩
  apply Subtype.ext
  apply CFSG.LieType.Chevalley.baseChangeGL_injective (τ := TwistTag.E6.tag) (algebraMap K L)
  rw [hbaseβ s]
  have h1 := hw (frameDiag (τ := TwistTag.E6.tag)
    (Units.map (algebraMap K L).toMonoidHom ζK) hζ (m • s)) ⟨m • s, rfl⟩
  rw [h1, canonicalRep_conj_frameDiag, torusAct_nsmul_gen,
    zmod_natCast_smul_eq_nsmul m (TableBExc.torusAct TwistTag.E6.tag p w s)]
  exact (hbase (m • TableBExc.torusAct TwistTag.E6.tag p w s)).symm

section Aut


theorem langFrame_aut {f p : ℕ} [Fact p.Prime] [NeZero p] (hp5 : 5 ≤ p) (hf : 1 ≤ f)
    (K : Type) [Field K] (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K)
    (hσ : ∀ c, σ c = c ^ (2 ^ f)) (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L]
    [CharP L 2] {ζK : Kˣ} (hζKord : orderOf ζK = p)
    (hζ : (Units.map (algebraMap K L).toMonoidHom ζK) ^ p = 1)
    {g₀ : ModGL TwistTag.E6.tag L} (hg₀C : g₀ ∈ adjointGroup TwistTag.E6.tag L)
    (ι₀ : Multiplicative (Fin TwistTag.E6.tag.rank → ZMod p) →*
      ↥(graphFixedRootGroup TwistTag.E6 K σ))
    (hι₀ : Function.Injective ι₀)
    (hbase : ∀ s : Fin TwistTag.E6.tag.rank → ZMod p,
      baseChangeGL (algebraMap K L)
        ((ι₀ (Multiplicative.ofAdd s) : _) : ModGL TwistTag.E6.tag K) =
        g₀ * frameDiag (τ := TwistTag.E6.tag) (Units.map (algebraMap K L).toMonoidHom ζK) hζ s *
          g₀⁻¹) :
    ∀ β : MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ), (∀ b ∈ ι₀.range, β b ∈ ι₀.range) →
      ∃ (w : WeylGroup TwistTag.E6.tag) (c : ZMod p), c ≠ 0 ∧ (β ^ p = 1 → c = 1) ∧
        ∀ s : Fin TwistTag.E6.tag.rank → ZMod p, β (ι₀ (Multiplicative.ofAdd s)) =
          ι₀ (Multiplicative.ofAdd (c • TableBExc.torusAct TwistTag.E6.tag p w s)) := by
  intro β hstab
  classical
  have hp : p.Prime := Fact.out
  haveI hFinK : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  let σ' : K ≃+* K := RingEquiv.ofBijective σ (Finite.injective_iff_bijective.mp σ.injective)
  have hσθ : σ'.toRingHom = σ := rfl
  have hσ' : ∀ c, σ' c = c ^ (2 ^ f) := fun c => hσ c
  have hζK_unit : ζK ^ p = 1 := by rw [← hζKord, pow_orderOf_eq_one]
  have hζKp : (ζK : K) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, hζK_unit, Units.val_one]
  by_cases hβp : β ^ p = 1
  ·
    obtain ⟨g, b, δ, hδp, hnf⟩ :=
      exists_normalForm_twistedE6_sharp (f := f) hf hK σ' hσ' (θ := σ) hσθ (n := p) β hβp
    have hm : ∀ c' : Kˣ, c' ^ p = 1 → Units.map δ.toMonoidHom c' = c' ^ 1 := by
      intro c' hc'
      rw [pow_one]
      refine Units.ext ?_
      change δ (c' : K) = (c' : K)
      have hc'K : (c' : K) ^ p = 1 := by
        rw [← Units.val_pow_eq_pow_val, hc', Units.val_one]
      exact OrdPRest.ringAut_fix_of_pow_eq_one hp hδp hc'K
    have hδm : Units.map δ.toMonoidHom ζK = ζK ^ 1 := hm ζK hζK_unit
    obtain ⟨w, hw⟩ :=
      langFrame_core (p := p) hp5 hf K hK σ hσ L hζKord hζ hg₀C ι₀ hbase β hstab g b δ hnf 1
        (Nat.coprime_one_left p) hδm
    refine ⟨w, ((1 : ℕ) : ZMod p), by norm_num, fun _ => by norm_num, fun s => ?_⟩
    exact hw s
  ·
    obtain ⟨g, b, δ, -, hnf⟩ :=
      exists_normalForm_twistedE6_sharp (f := f) hf hK σ' hσ' (θ := σ) hσθ
        (n := orderOf β) β (pow_orderOf_eq_one β)
    obtain ⟨m, hm⟩ := NoTvAut.exists_units_map_eq_pow hζKord δ.toRingHom
    have hcop : Nat.Coprime m p := NoTvAut.coprime_of_units_map_eq_pow hp hζKord δ.toRingHom hm
    have hmp : ¬ p ∣ m := by
      rw [← Nat.Prime.coprime_iff_not_dvd hp]
      exact Nat.coprime_comm.mpr hcop
    have hδm : Units.map δ.toMonoidHom ζK = ζK ^ m := hm ζK hζK_unit
    obtain ⟨w, hw⟩ :=
      langFrame_core (p := p) hp5 hf K hK σ hσ L hζKord hζ hg₀C ι₀ hbase β hstab g b δ hnf m hcop hδm
    have hcne : (m : ZMod p) ≠ 0 := fun h0 => hmp ((ZMod.natCast_eq_zero_iff m p).mp h0)
    refine ⟨w, (m : ZMod p), hcne, fun h => absurd h hβp, fun s => ?_⟩
    exact hw s

end Aut

end ExcFrames

end CFSG.StandardType
