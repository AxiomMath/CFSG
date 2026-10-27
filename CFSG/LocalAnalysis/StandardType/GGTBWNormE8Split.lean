module

public import CFSG.LocalAnalysis.StandardType.GGTBWNormFrame
public import CFSG.LocalAnalysis.StandardType.GGTBWNormE6Five
public import CFSG.LocalAnalysis.StandardType.GGTBTorE8Split
public import CFSG.LocalAnalysis.StandardType.GGTwE6WeylTorusTransferCore
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLLine
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplit
public import CFSG.LocalAnalysis.StandardType.GGOuterInvAtE6OddToral2
public import CFSG.LocalAnalysis.StandardType.GGNoTransvectionAutForm
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneHeightRigidityAut
public import CFSG.LocalAnalysis.StandardType.GGL45NtE8Five

public noncomputable section

namespace CFSG.StandardType.E8WNorm

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.CentralCover CFSG.StandardType.TableBExc
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


theorem _root_.CFSG.StandardType.ExcFrames.exists_scalar_weyl_of_mulAut_torusPow_E7E8
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} [NeZero p] (hp : p.Prime) {ζ : Kˣ} (hζo : orderOf ζ = p)
    (ι : Multiplicative (Fin τ.rank → ZMod p) →* adjointGroup τ K)
    (hrange : ι.range = torusPow τ K p)
    (hnorm : ∀ g ∈ Subgroup.normalizer ((torusPow τ K p) : Set (adjointGroup τ K)),
      ∃ w : WeylGroup τ, ∀ s, g * ι (Multiplicative.ofAdd s) * g⁻¹ =
        ι (Multiplicative.ofAdd (torusAct τ p w s)))
    (β : MulAut (adjointGroup τ K))
    (hβ : ∀ x, β x ∈ torusPow τ K p ↔ x ∈ torusPow τ K p) :
    ∃ (c : (ZMod p)ˣ) (u : WeylGroup τ), ∀ v,
      β (ι (Multiplicative.ofAdd v)) =
        ι (Multiplicative.ofAdd ((c : ZMod p) • torusAct τ p u v)) := by
  classical
  obtain ⟨g, hg, a, -, δ, -, hβx⟩ :=
    CFSG.SeitzReduction.mem_diagonalFieldActors_E7_E8 hτ β
  obtain ⟨m, hm⟩ := NoTvAut.exists_units_map_eq_pow hζo δ.toRingHom
  have hcop : Nat.Coprime m p := NoTvAut.coprime_of_units_map_eq_pow hp hζo δ.toRingHom hm
  have hda : rootDiagUnit τ a ∈ torusGroup τ K := full_of_E7_E8 hτ a
  have hform : ∀ x ∈ torusPow τ K p,
      (β x : ModGL τ K) = g * (x : ModGL τ K) ^ m * g⁻¹ := by
    intro x hx
    rw [hβx x, NoTvAut.units_map_entrywise_eq_pow δ.toRingHom hm
      (ExcFrames.mem_torusPow_iff_coe.mp hx)]
    have hxm : (x : ModGL τ K) ^ m ∈ torusGroup τ K := pow_mem hx.1 m
    have hc : rootDiagUnit τ a * (x : ModGL τ K) ^ m =
        (x : ModGL τ K) ^ m * rootDiagUnit τ a :=
      CFSG.LieType.Chevalley.RootTorus.torusGroup_mul_comm hda hxm
    calc g * rootDiagUnit τ a * (x : ModGL τ K) ^ m * (rootDiagUnit τ a)⁻¹ * g⁻¹ =
        g * (rootDiagUnit τ a * (x : ModGL τ K) ^ m) * (rootDiagUnit τ a)⁻¹ * g⁻¹ := by
          group
      _ = g * (x : ModGL τ K) ^ m * g⁻¹ := by rw [hc]; group
  let g' : adjointGroup τ K := ⟨g, hg⟩
  obtain ⟨k, hk⟩ : ∃ k : ℕ, m * k % p = 1 := by
    obtain ⟨k, -, hk⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
    exact ⟨k, hk⟩
  have hpow : ∀ x ∈ torusPow τ K p, (x ^ k) ^ m = x := by
    intro x hx
    rw [← pow_mul, mul_comm, ← Nat.div_add_mod (m * k) p, hk, pow_add, pow_mul, hx.2, one_pow,
      one_mul, pow_one]
  have hgN : g' ∈ Subgroup.normalizer ((torusPow τ K p) : Set (adjointGroup τ K)) := by
    apply Subgroup.mem_normalizer_fintype
    intro x hx
    have hxk : x ^ k ∈ torusPow τ K p := pow_mem hx k
    have hβk := (hβ (x ^ k)).mpr hxk
    have he : β (x ^ k) = g' * x * g'⁻¹ := by
      apply Subtype.ext
      rw [hform _ hxk, ← Subgroup.coe_pow, hpow x hx]
      rfl
    rw [← he]
    exact hβk
  obtain ⟨w, hw⟩ := hnorm g' hgN
  refine ⟨ZMod.unitOfCoprime m hcop, w, fun v => ?_⟩
  have hιv : ι (Multiplicative.ofAdd v) ∈ torusPow τ K p := hrange ▸ ⟨_, rfl⟩
  have hlin : torusAct τ p w (m • v) = m • torusAct τ p w v := by
    rw [← NoTvAut.torusActHom_apply w (m • v), ← NoTvAut.torusActHom_apply w v]
    exact map_nsmul _ m _
  have hmv : ι (Multiplicative.ofAdd (m • v)) = ι (Multiplicative.ofAdd v) ^ m := by
    rw [← map_pow, ofAdd_nsmul]
  apply Subtype.ext
  rw [hform _ hιv, ZMod.coe_unitOfCoprime, Nat.cast_smul_eq_nsmul (ZMod p), ← hlin, ← hw,
    hmv]
  rfl


theorem eq_torusPow_of_conj_le_of_selfCent {τ : Tag} {K : Type} [Field K]
    {p : ℕ} (E : Subgroup (adjointGroup τ K))
    (hsc : ∀ g, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E)
    (c : adjointGroup τ K)
    (hct : ∀ x ∈ E, c * x * c⁻¹ ∈ torusPow τ K p) :
    E.map (MulAut.conj c).toMonoidHom = torusPow τ K p := by
  let E' := E.map (MulAut.conj c).toMonoidHom
  have hle : E' ≤ torusPow τ K p := by
    rintro y ⟨x, hx, rfl⟩
    exact hct x hx
  have hback : torusPow τ K p ≤ E' := by
    intro t ht
    have hx : c⁻¹ * t * c ∈ E := by
      apply hsc
      · intro e he
        have hc := CFSG.LieType.Chevalley.RootTorus.torusGroup_mul_comm ht.1 (hct e he).1
        have hc' : t * (c * e * c⁻¹) = (c * e * c⁻¹) * t := Subtype.ext hc
        calc (c⁻¹ * t * c) * e = c⁻¹ * (t * (c * e * c⁻¹)) * c := by group
          _ = e * (c⁻¹ * t * c) := by rw [hc']; group
      · change (c⁻¹ * t * (c⁻¹)⁻¹) ^ p = 1
        rw [conj_pow, ht.2]; group
    exact ⟨c⁻¹ * t * c, hx, by change c * (c⁻¹ * t * c) * c⁻¹ = t; group⟩
  have hEq : E' = torusPow τ K p := le_antisymm hle hback
  exact hEq

theorem exists_conj_le_torusPow_five_of_toral {K : Type} [Field K] [Finite K]
    [CharP K 2] (hpq : 5 ∣ Nat.card K - 1)
    (E : Subgroup (adjointGroup .E8 K)) (hE : IsElemAbelian 5 E)
    (hcard : 125 ≤ Nat.card E)
    (hT : ExcFramesHalf.IsToralSubgroup .E8 (AlgebraicClosure K)
      (E.map ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
        (adjointGroup .E8 K).subtype))) :
    ∃ c : adjointGroup .E8 K, ∀ x ∈ E,
      c * x * c⁻¹ ∈ torusPow .E8 K 5 := by
  let L := AlgebraicClosure K
  let φ : adjointGroup .E8 K →* ModGL .E8 L :=
    (baseChangeGL (algebraMap K L)).comp (adjointGroup .E8 K).subtype
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective _
  obtain ⟨g, hg, hgt⟩ := hT
  refine ExcElemToral.exists_conj_le_torusPow_of_toralWitness Nat.prime_five hpq E hE
    g hg ?_ ?_
  · intro x
    exact hgt _ (Subgroup.mem_map_of_mem φ x.2)
  · intro a hainj ha
    apply CFSG.HardMathSupport.C14Lattice.familyCentralizer_eq_familyGroup_E8_five a ha
    rw [Set.ncard_range_of_injective hainj]
    omega

theorem card_eq_eight_of_selfCent {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) (hpq : p ∣ Nat.card K - 1)
    (E : Subgroup (adjointGroup .E8 K)) (hE : IsElemAbelian p E)
    (hsc : ∀ g, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E) :
    Nat.card E = p ^ 8 := by
  obtain ⟨c, hct⟩ := ExcElemToral.exists_conj_le_torusPow_of_nonTorsion hp (by omega)
    (fun _ => by omega) (fun _ => by omega) hpq E hE
  let E' := E.map (MulAut.conj c).toMonoidHom
  have hEq : E' = torusPow .E8 K p :=
    eq_torusPow_of_conj_le_of_selfCent E hsc c hct
  have hcard : Nat.card E' = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.conj c).injective
  rw [← hcard, hEq]
  exact card_torusPow_E8 hp hpq


theorem ggTorusWNormSC_recipe_E8_split {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) (hpq : p ∣ Nat.card K - 1) :
    GGTorusWNormSC p (RecipeGroup .E8 K) (RecipeID .E8 K) := by
  classical
  intro L _ _ ψ hψ hker hperf A hA hAI h3 hsc
  let : Fact p.Prime := ⟨hp⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  have hIp : GGOutdiagPrime p (RecipeGroup .E8 K) (RecipeID .E8 K) := by
    intro φ hφ _
    obtain ⟨x, rfl⟩ := idImage_subset_inn_E8 K hφ
    exact ⟨x, rfl⟩
  obtain ⟨Λ₀, hΛeq, hΛinj, -, hAΛ, hE, hEc, hEsc⟩ :=
    TwE6TB.exists_innerModel hp (center_recipeGroup_eq_bot .E8 K) hIp
      (ExcSplitL.ggCenterPrime_recipe_E8 hp hp2) ψ hψ hker hperf hA hAI hsc
  let ε := recipeEquiv .E8 K
  let E := (A.comap Λ₀).map ε.toMonoidHom
  have hEg : IsElemAbelian p E := TableB.isElemAbelian_map hE _
  have hEgs : ∀ g, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E := by
    intro g hg hgp
    have hg' : ε.symm g ∈ A.comap Λ₀ := by
      apply hEsc
      · intro e he
        apply ε.injective
        rw [map_mul, map_mul, ε.apply_symm_apply]
        exact hg (ε e) (Subgroup.mem_map_of_mem _ he)
      · rw [← map_pow, hgp, map_one]
    exact ⟨ε.symm g, hg', ε.apply_symm_apply g⟩
  have hcard := card_eq_eight_of_selfCent hp hp7 hpq E hEg hEgs
  obtain ⟨g, hg⟩ := ggExcToralRankInput_E8_of_ne_three hp hp2 hp3 hpq E hEg
    (by rw [hcard]; exact le_rfl)
  let c : adjointGroup .E8 K ≃* adjointGroup .E8 K := MulAut.conj g
  let ψ₁ : L →* adjointGroup .E8 K := c.toMonoidHom.comp (ε.toMonoidHom.comp ψ)
  have hψ₁ : Function.Surjective ψ₁ := c.surjective.comp (ε.surjective.comp hψ)
  have hker₁ : ψ₁.ker ≤ Subgroup.center L := by
    intro l hl
    apply hker
    rw [MonoidHom.mem_ker] at hl ⊢
    have h1 : c (ε (ψ l)) = 1 := hl
    rw [c.map_eq_one_iff, ε.map_eq_one_iff] at h1
    exact h1
  let Λ₁ : adjointGroup .E8 K →* MulAut L :=
    Λ₀.comp (ε.symm.toMonoidHom.comp c.symm.toMonoidHom)
  have hΛ₁ : Function.Injective Λ₁ := hΛinj.comp (ε.symm.injective.comp c.symm.injective)
  have hΛ₁ψ : ∀ l, Λ₁ (ψ₁ l) = MulAut.conj l := by
    intro l
    change Λ₀ (ε.symm (c.symm (c (ε (ψ l))))) = MulAut.conj l
    rw [c.symm_apply_apply, ε.symm_apply_apply]
    exact hΛeq rfl
  have hEA : (torusPow .E8 K p).map Λ₁ = A := by
    have hmapc : E.map c.toMonoidHom = torusPow .E8 K p := hg
    rw [← hmapc, Subgroup.map_map]
    have hcomp : Λ₁.comp c.toMonoidHom = Λ₀.comp ε.symm.toMonoidHom := by
      refine MonoidHom.ext fun x => ?_
      change Λ₀ (ε.symm (c.symm (c x))) = Λ₀ (ε.symm x)
      rw [c.symm_apply_apply]
    rw [hcomp]
    change ((A.comap Λ₀).map ε.toMonoidHom).map (Λ₀.comp ε.symm.toMonoidHom) = A
    rw [Subgroup.map_map]
    have hcomp' : (Λ₀.comp ε.symm.toMonoidHom).comp ε.toMonoidHom = Λ₀ := by
      refine MonoidHom.ext fun x => ?_
      change Λ₀ (ε.symm (ε x)) = Λ₀ x
      rw [ε.symm_apply_apply]
    rw [hcomp']
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hx
    · intro a ha
      obtain ⟨x, hx⟩ := hAΛ a ha
      exact ⟨x, show Λ₀ x ∈ A by rw [hx]; exact ha, hx⟩
  obtain ⟨ζ, hζ, ι, hζo, hι, hrange, hact, hnorm⟩ := E8SplitTorus.exists_frame hp hp2 hpq
  have hn : ∀ i, E8SplitTorus.simpleRep (K := K) i ∈
      Subgroup.normalizer ((torusPow .E8 K p) : Set (adjointGroup .E8 K)) := by
    intro i
    apply Subgroup.mem_normalizer_fintype
    intro x hx
    rw [← hrange] at hx ⊢
    obtain ⟨s, rfl⟩ := hx
    exact ⟨_, (hact i (Multiplicative.toAdd s)).symm⟩
  have hAut : ∀ β : MulAut (adjointGroup .E8 K),
      (∀ x, β x ∈ torusPow .E8 K p ↔ x ∈ torusPow .E8 K p) →
      ∃ (c : (ZMod p)ˣ) (u : WeylGroup .E8), ∀ v,
        β (ι (Multiplicative.ofAdd v)) =
          ι (Multiplicative.ofAdd ((c : ZMod p) • torusAct .E8 p u v)) :=
    fun β hβ => ExcFrames.exists_scalar_weyl_of_mulAut_torusPow_E7E8 (Or.inr rfl) hp hζo ι
      hrange hnorm β hβ
  intro _ Γ _ _ M C V _ _ ι' φ h α _ _ _ _ hgen s hs
  exact ggWNormConcl_of_centralCover_weylFrame ψ₁ hψ₁ hker₁ center_adjointGroup_eq_bot
    Λ₁ hΛ₁ hΛ₁ψ (torusPow .E8 K p) A hEA ι hι hrange (E8SplitTorus.simpleRep (K := K)) hn
    hact hnorm hAut (by decide)
    (ExcFrames.isUnit_det_symmetrizedCartan (Or.inr (Or.inr rfl)) hp2) ι' φ h α hgen hs

theorem largeEvenLabelAll_wnorm_E8_split {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    {lab : LargeEvenLabel} (htag : lab.tag = .E8) (hpq : p ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSC p R I := by
  obtain ⟨t, r, f⟩ := lab
  dsimp only at htag hpq ⊢
  subst htag
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQK⟩ := hQ
  let : CharP K 2 := charP_two_of_card hK
  refine ⟨K, i1, i2, hK, hQK, ?_⟩
  exact ggTorusWNormSC_recipe_E8_split hp hp7 (by rw [hK]; exact hpq)

end CFSG.StandardType.E8WNorm
