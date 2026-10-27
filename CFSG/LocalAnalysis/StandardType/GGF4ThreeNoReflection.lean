module

public import CFSG.LocalAnalysis.StandardType.GGReflCentralLift
public import CFSG.LocalAnalysis.StandardType.GGF4ThreeToral
public import CFSG.LocalAnalysis.StandardType.GGReflA2Toral
public import CFSG.LocalAnalysis.StandardType.GGIrred937F4BCover
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcF4Nons

public section

namespace CFSG.StandardType

open CFSG CFSG.Open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


theorem exists_fixed_a2a2_of_nontoral_three
    {K : Type} [Field K] [Finite K] [CharP K 2] (hq : 3 ∣ Nat.card K + 1)
    {E : Subgroup (adjointGroup .F4 K)} (hE : IsElemAbelian 3 E)
    (hcard : 3 ^ 3 ≤ Nat.card E)
    (hnt : ¬ ∃ g ∈ adjointGroup .F4 (AlgebraicClosure K), ∀ x ∈ E,
      g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((x : adjointGroup .F4 K) : ModGL .F4 K) * g ∈ torusGroup .F4 (AlgebraicClosure K))
    {w : adjointGroup .F4 K} (hr : GGKGIsReflAt 3 E w) :
    ∃ x ∈ E, x ≠ 1 ∧ w * x * w⁻¹ = x ∧ ggF4Sh_A2A2 x := by
  obtain ⟨x, hx, hx1, hxw⟩ := hr.exists_fixed_ne_one Nat.prime_three hcard
  refine ⟨x, hx, hx1, hxw, ?_⟩
  by_contra hA2
  exact hnt (ggF4Sh_toral_of_notA2A2 K hq E hE x hx hx1 hA2)

theorem exists_twelve_root_centralizer_of_nontoral_three
    {K : Type} [Field K] [Finite K] [CharP K 2] (hq : 3 ∣ Nat.card K + 1)
    {E : Subgroup (adjointGroup .F4 K)} (hE : IsElemAbelian 3 E)
    (hcard : 3 ^ 3 ≤ Nat.card E)
    (hnt : ¬ ∃ g ∈ adjointGroup .F4 (AlgebraicClosure K), ∀ x ∈ E,
      g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((x : adjointGroup .F4 K) : ModGL .F4 K) * g ∈ torusGroup .F4 (AlgebraicClosure K))
    {w : adjointGroup .F4 K} (hr : GGKGIsReflAt 3 E w) :
    ∃ (g : ModGL .F4 (AlgebraicClosure K)) (a : Fin Tag.F4.rank → (AlgebraicClosure K)ˣ)
      (θ : adjointGroup .F4 K →* ModGL .F4 (AlgebraicClosure K)),
      g ∈ adjointGroup .F4 (AlgebraicClosure K) ∧ (∀ i, a i ^ 3 = 1) ∧
      (rootCharKernel a).ncard = 12 ∧ Function.Injective θ ∧
      (∀ z, θ z = g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (z : ModGL .F4 K) * g) ∧
      E.map θ ≤ toralCentralizer .F4 (AlgebraicClosure K) a ∧
      θ w ∈ toralCentralizer .F4 (AlgebraicClosure K) a ∧
      GGKGIsReflAt 3 (E.map θ) (θ w) ∧ rootDiagUnit .F4 a ∈ E.map θ ∧
      rootDiagUnit .F4 a ≠ 1 := by
  classical
  obtain ⟨x, hxE, hx1, hxw, g, hg, a, ha, h12, hxa⟩ :=
    exists_fixed_a2a2_of_nontoral_three hq hE hcard hnt hr
  let θ : adjointGroup .F4 K →* ModGL .F4 (AlgebraicClosure K) :=
    (MulAut.conj g⁻¹).toMonoidHom.comp
      ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp (adjointGroup .F4 K).subtype)
  have hθ : ∀ z, θ z = g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (z : ModGL .F4 K) * g := fun z => by rfl
  have hinj : Function.Injective θ :=
    (MulAut.conj g⁻¹).injective.comp
      ((baseChangeGL_injective (algebraMap K (AlgebraicClosure K))).comp Subtype.val_injective)
  have hxθ : θ x = rootDiagUnit .F4 a := by
    rw [hθ, hxa]
    group
  have hadj : ∀ z, θ z ∈ adjointGroup .F4 (AlgebraicClosure K) := fun z => by
    rw [hθ]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hg)
      (baseChangeGL_mem_adjointGroup _ z.2)) hg
  have hcent : ∀ z, z * x = x * z → θ z ∈ toralCentralizer .F4 (AlgebraicClosure K) a := by
    intro z hzx
    refine ⟨hadj z, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    rw [← hxθ, ← map_mul, ← map_mul, hzx]
  have hEcent : E.map θ ≤ toralCentralizer .F4 (AlgebraicClosure K) a := by
    rintro _ ⟨z, hz, rfl⟩
    exact hcent z (congrArg Subtype.val (hE.1.is_comm.comm
      (⟨z, hz⟩ : E) (⟨x, hxE⟩ : E)))
  have hwcent : θ w ∈ toralCentralizer .F4 (AlgebraicClosure K) a :=
    hcent w (mul_inv_eq_iff_eq_mul.mp hxw)
  refine ⟨g, a, θ, hg, ha, h12, hinj, hθ, hEcent, hwcent, hr.map θ hinj, ?_, ?_⟩
  · rw [← hxθ]
    exact Subgroup.mem_map_of_mem θ hxE
  · intro h1
    apply hx1
    exact hinj (hxθ.trans h1 |>.trans (map_one θ).symm)

theorem toral_of_twelve_root_centralizer_cover
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {E : Subgroup (adjointGroup .F4 K)} (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 3)
    (g : ModGL .F4 (AlgebraicClosure K)) (hg : g ∈ adjointGroup .F4 (AlgebraicClosure K))
    (a : Fin Tag.F4.rank → (AlgebraicClosure K)ˣ)
    (θ : adjointGroup .F4 K →* ModGL .F4 (AlgebraicClosure K))
    (hinj : Function.Injective θ)
    (hθ : ∀ z, θ z = g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (z : ModGL .F4 K) * g)
    (hEC : E.map θ ≤ toralCentralizer .F4 (AlgebraicClosure K) a)
    {w : adjointGroup .F4 K} (hwC : θ w ∈ toralCentralizer .F4 (AlgebraicClosure K) a)
    (hr : GGKGIsReflAt 3 (E.map θ) (θ w))
    (haE : rootDiagUnit .F4 a ∈ E.map θ) (ha1 : rootDiagUnit .F4 a ≠ 1)
    {ψ ψ' : Matrix.SpecialLinearGroup (Fin 3) (AlgebraicClosure K) →*
      ModGL .F4 (AlgebraicClosure K)}
    {σ σ' : Fin 3 → Fin 3 → Fin Tag.F4.rank → ℤ}
    (hψ : CFSG.RankThree.PartOne.KF4.IsA2Frame ψ σ)
    (hψ' : CFSG.RankThree.PartOne.KF4.IsA2Frame ψ' σ')
    (hc : ∀ A B, Commute (ψ A) (ψ' B))
    (hC : toralCentralizer .F4 (AlgebraicClosure K) a = (ψ.noncommCoprod ψ' hc).range) :
    ∃ z ∈ adjointGroup .F4 (AlgebraicClosure K), ∀ x ∈ E,
      z⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((x : adjointGroup .F4 K) : ModGL .F4 K) * z ∈ torusGroup .F4 (AlgebraicClosure K) := by
  classical
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  let : Finite (E.map θ) := Finite.of_equiv E (E.equivMapOfInjective θ hinj).toEquiv
  have h9 : ((9 : ℕ) : AlgebraicClosure K) ≠ 0 := by
    have h : ((9 : ℕ) : AlgebraicClosure K) = ((1 : ℕ) : AlgebraicClosure K) :=
      (CharP.natCast_eq_natCast (AlgebraicClosure K) 2).mpr (by decide)
    rw [h, Nat.cast_one]
    exact one_ne_zero
  have : NeZero ((9 : ℕ) : AlgebraicClosure K) := ⟨h9⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure K) 9
  have hcommCentral : rootDiagUnit .F4 a ∈
      Subgroup.centralizer ((ψ.noncommCoprod ψ' hc).range : Set (ModGL .F4 (AlgebraicClosure K))) := by
    rw [← hC, Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_singleton_iff.mp hy.2)
  have hcard' : Nat.card (E.map θ) ≤ 3 ^ 3 := by
    rw [Subgroup.card_map_of_injective hinj, hcard]
  obtain ⟨z, hz, hzE⟩ := exists_conj_torus_of_a2_frames_of_reflection
    hψ hψ' hc hζ (hE.map θ) hcard' (hEC.trans hC.le) (hC ▸ hwC) hr haE ha1 hcommCentral
  have hzG : z ∈ adjointGroup .F4 (AlgebraicClosure K) := (hC.symm ▸ hz).1
  refine ⟨g * z, Subgroup.mul_mem _ hg hzG, fun x hx => ?_⟩
  have h := hzE (θ x) (Subgroup.mem_map_of_mem θ hx)
  rw [hθ] at h
  simpa only [mul_inv_rev, mul_assoc] using h

theorem not_ggKGIsReflAt_of_nontoral_three
    {K : Type} [Field K] [Finite K] [CharP K 2] (hq : 3 ∣ Nat.card K + 1)
    {E : Subgroup (adjointGroup .F4 K)} (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 3)
    (hnt : ¬ ∃ g ∈ adjointGroup .F4 (AlgebraicClosure K), ∀ x ∈ E,
      g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((x : adjointGroup .F4 K) : ModGL .F4 K) * g ∈ torusGroup .F4 (AlgebraicClosure K))
    (w : adjointGroup .F4 K) : ¬ GGKGIsReflAt 3 E w := by
  intro hr
  obtain ⟨g, a, θ, hg, ha, h12, hinj, hθ, hEC, hwC, hr', haE, ha1⟩ :=
    exists_twelve_root_centralizer_of_nontoral_three hq hE hcard.ge hnt hr
  obtain ⟨σ, σ', κ, κ', ψ, ψ', hc, -, hψ, hψ', hC, -⟩ :=
    Irred937.f4_a2a2_exists_cover a ha h12
  exact hnt (toral_of_twelve_root_centralizer_cover hE hcard g hg a θ hinj hθ hEC
    hwC hr' haE ha1 hψ hψ' hc hC)

theorem three_pow_four_le_card_of_reflection
    {K : Type} [Field K] [Finite K] [CharP K 2] (hq : 3 ∣ Nat.card K + 1)
    {E : Subgroup (adjointGroup .F4 K)} (hE : IsElemAbelian 3 E)
    (h3 : 3 ^ 3 ≤ Nat.card E)
    (hSC : ∀ x ∈ Subgroup.centralizer (E : Set (adjointGroup .F4 K)), x ^ 3 = 1 → x ∈ E)
    {w : adjointGroup .F4 K} (hr : GGKGIsReflAt 3 E w) : 3 ^ 4 ≤ Nat.card E := by
  by_contra h4
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := hE.isPGroup.exists_card_eq
  have hk3 : 3 ≤ k := by
    rw [hk] at h3
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h3
  have hk4 : k < 4 := by
    rw [hk] at h4
    exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).mp (Nat.lt_of_not_ge h4)
  have hcard : Nat.card E = 3 ^ 3 := by
    have : k = 3 := by omega
    simpa only [this] using hk
  have hnt : ¬ ∃ g ∈ adjointGroup .F4 (AlgebraicClosure K), ∀ x ∈ E,
      g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((x : adjointGroup .F4 K) : ModGL .F4 K) * g ∈ torusGroup .F4 (AlgebraicClosure K) := by
    intro htor
    exact h4 (Irred937.card_ge_of_toral_F4_gen K hq E hE htor h3 hSC)
  exact not_ggKGIsReflAt_of_nontoral_three hq hE hcard hnt w hr

theorem exists_excFrame_of_selfCentralizing_of_reflection_three
    {K : Type} [Field K] [Finite K] [CharP K 2] (hq : 3 ∣ Nat.card K + 1)
    {E : Subgroup (adjointGroup .F4 K)} (hE : IsElemAbelian 3 E)
    (h3 : 3 ^ 3 ≤ Nat.card E)
    (hSC : ∀ x ∈ Subgroup.centralizer (E : Set (adjointGroup .F4 K)), x ^ 3 = 1 → x ∈ E)
    {w : adjointGroup .F4 K} (hr : GGKGIsReflAt 3 E w) :
    ∃ F : ExcFrame .F4 K 3 E, ExcIsLongest .F4 F.w := by
  have h4 := three_pow_four_le_card_of_reflection hq hE h3 hSC hr
  obtain ⟨F, -, hF⟩ := excSCTorusInput_nons_of_L0
    (Or.inr (Or.inr ⟨rfl, rfl⟩)) Nat.prime_three (by norm_num) hq E hE h3 h4
    (fun g hg hgp => hSC g (Subgroup.mem_centralizer_iff.mpr fun e he => (hg e he).symm) hgp)
  exact ⟨F, hF hq⟩

end CFSG.StandardType

end
