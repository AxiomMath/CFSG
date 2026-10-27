module

public import CFSG.RankThree.PartOne.KE6.Tw6Solvable
public import CFSG.RankThree.PartOne.KE6.Phi3Core
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedE6DescendedRootSL2

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.E6 CFSG.RankThree.Chevalley
  CFSG.RankThree.GroupTheory CFSG.RankThree.LocalRank CFSG.RankThree.PartOne
  CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Classical2
open CFSG.RankThree.PartOne.KE (twistedTorusOf mem_twistedTorusOf twistedFixedPoints
  mem_twistedFixedPoints aut_mul_conj_mul_inv fixes_of_commute_conj conj_injective_of_center_eq_bot
  twE6Emb twE6Emb_injective twE6Emb_mem twE6Emb_apply)
open scoped Matrix MatrixGroups Pointwise commutatorElement

theorem tw6_perx_core {ℓ f : ℕ} [Fact ℓ.Prime] (K : Type) [Field K] [Finite K] [CharP K ℓ]
    (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 - ((ℓ ^ f : ℕ) : ℤ) + 1)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    {g0 : ModGL Tag.E6 L} (hg0C : g0 ∈ adjointGroup Tag.E6 L)
    (hg0 : twistE6 L (iterateFrobenius L ℓ f) g0 = g0 * tw6N L)
    (hperf : ∀ P : Subgroup (ModGL Tag.E6 L), Finite P → P ≤ adjointGroup Tag.E6 L →
      (∀ x ∈ P, twistE6 L (iterateFrobenius L ℓ f) x = x) → ⁅P, P⁆ = P →
        P ≤ (twE6Emb K σ L).range)
    {B : Subgroup (MulAut (twistedE6RootGroup K σ))}
    (hB : (MulAut.conj : twistedE6RootGroup K σ →* MulAut (twistedE6RootGroup K σ)).range ≤ B)
    {x : twistedE6RootGroup K σ} (hx : orderOf x = p) (c : twistedE6RootGroup K σ)
    (hh : g0⁻¹ * twE6Emb K σ L (c * x * c⁻¹) * g0 ∈
      twistedTorusOf (tw6N L) (twistE6 L (iterateFrobenius L ℓ f)))
    {η : MulAut (twistedE6RootGroup K σ)}
    (hη : η ∈ inSubgroup (aschbacherSolvableCore p) (B ⊓ Subgroup.centralizer
      ({(MulAut.conj x : MulAut (twistedE6RootGroup K σ))} :
        Set (MulAut (twistedE6RootGroup K σ))))) :
    (∀ N : ModGL Tag.E6 L,
      (∀ d : twistedE6RootGroup K σ,
        twE6Emb K σ L (η d) = N * twE6Emb K σ L d * N⁻¹) →
      ∀ α ∈ torusRootKernel (g0⁻¹ * twE6Emb K σ L (c * x * c⁻¹) * g0), ∀ t : L,
        Commute (((twE6Emb K σ L c)⁻¹ * g0)⁻¹ * N * ((twE6Emb K σ L c)⁻¹ * g0))
          (pinnedX Tag.E6 L α t)) ∧
    ((torusRootKernel (g0⁻¹ * twE6Emb K σ L (c * x * c⁻¹) * g0)).Nonempty →
      ∃ N : ModGL Tag.E6 L, ∀ u : twistedE6RootGroup K σ,
        twE6Emb K σ L (η u) = N * twE6Emb K σ L u * N⁻¹) := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have : Fintype K := Fintype.ofFinite K
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  obtain ⟨ι', KL, ψ, hψinj, hψdef, hψHQ, hψfix, hPψ, -⟩ :=
    tw6_perx K hf hK σ hσ hp hp3 hpq L hg0C hg0 hperf hx c hh
  have hC : Subgroup.center (twistedE6RootGroup K σ) = ⊥ :=
    exceptional_fixed_center_trivial TwistTag.E6 K σ
  have hfix : ∀ (i : ι') (d : Subgroup.centralizer ({x} : Set (twistedE6RootGroup K σ))),
      ψ d ∈ KL.P i → η (d : twistedE6RootGroup K σ) = d := by
    intro i d hd
    set P' : Subgroup (twistedE6RootGroup K σ) :=
      ((KL.P i).comap ψ).map
        (Subgroup.centralizer ({x} : Set (twistedE6RootGroup K σ))).subtype
      with hP'
    have hPD : P' ≤ Subgroup.centralizer ({x} : Set (twistedE6RootGroup K σ)) :=
      Subgroup.map_subtype_le _
    have hPn : ∀ e ∈ Subgroup.centralizer ({x} : Set (twistedE6RootGroup K σ)), ∀ u ∈ P',
        e * u * e⁻¹ ∈ P' := by
      rintro e he _ ⟨u, hu, rfl⟩
      refine ⟨⟨e, he⟩ * u * ⟨e, he⟩⁻¹, ?_, rfl⟩
      change ψ (⟨e, he⟩ * u * ⟨e, he⟩⁻¹) ∈ KL.P i
      rw [map_mul ψ, map_mul ψ, map_inv ψ]
      exact KL.norm i (ψ ⟨e, he⟩) (hψHQ _) (mem_twistedFixedPoints.2 (hψfix _)) (ψ u) hu
    have hmapeq : ((KL.P i).comap ψ).map ψ = KL.P i := by
      rw [Subgroup.map_comap_eq, inf_of_le_right (hPψ i)]
    have hPq : CFSG.IsQuasisimple P' :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv
        ((((Subgroup.equivMapOfInjective ((KL.P i).comap ψ) ψ hψinj).trans
          (MulEquiv.subgroupCongr hmapeq)).symm).trans
          (Subgroup.equivMapOfInjective ((KL.P i).comap ψ)
            (Subgroup.centralizer ({x} : Set (twistedE6RootGroup K σ))).subtype
            (Subgroup.centralizer ({x} : Set (twistedE6RootGroup K σ))).subtype_injective))
        (KL.quasi i)
    exact core_fixes_normal_quasisimple hp hC hB hPD hPn hPq hη
      (d : twistedE6RootGroup K σ) ⟨d, hd, rfl⟩
  set T : ModGL Tag.E6 L := (twE6Emb K σ L c)⁻¹ * g0 with hT
  have hιψ : ∀ d : Subgroup.centralizer ({x} : Set (twistedE6RootGroup K σ)),
      twE6Emb K σ L (d : twistedE6RootGroup K σ) = T * ψ d * T⁻¹ := by
    intro d
    rw [hψdef d, hT]
    simp only [map_mul, map_inv]
    group
  refine ⟨fun N hN α hα t => ?_, fun hne => ?_⟩
  · have hcomm : ∀ (i : ι'), ∀ u ∈ KL.P i,
        Commute (((T⁻¹ * N * T : ModGL Tag.E6 L) : Module.End L (RootModule Tag.E6 L)))
          (u : Module.End L (RootModule Tag.E6 L)) := by
      intro i u hu
      obtain ⟨d, hdu⟩ := hPψ i hu
      have hdi : ψ d ∈ KL.P i := hdu ▸ hu
      have hηd := hfix i d hdi
      have hNd := hN (d : twistedE6RootGroup K σ)
      rw [hηd] at hNd
      have hcomm' : N * twE6Emb K σ L (d : twistedE6RootGroup K σ) =
          twE6Emb K σ L (d : twistedE6RootGroup K σ) * N := by
        calc N * twE6Emb K σ L (d : twistedE6RootGroup K σ)
            = (N * twE6Emb K σ L (d : twistedE6RootGroup K σ) * N⁻¹) * N := by group
          _ = twE6Emb K σ L (d : twistedE6RootGroup K σ) * N := by rw [← hNd]
      have hgrp : (T⁻¹ * N * T) * ψ d = ψ d * (T⁻¹ * N * T) := by
        calc (T⁻¹ * N * T) * ψ d = T⁻¹ * (N * (T * ψ d * T⁻¹)) * T := by group
          _ = T⁻¹ * ((T * ψ d * T⁻¹) * N) * T := by rw [← hιψ d, hcomm']
          _ = ψ d * (T⁻¹ * N * T) := by group
      rw [← hdu]
      show ((T⁻¹ * N * T : ModGL Tag.E6 L) : Module.End L (RootModule Tag.E6 L)) *
        ((ψ d : ModGL Tag.E6 L) : Module.End L (RootModule Tag.E6 L)) =
          ((ψ d : ModGL Tag.E6 L) : Module.End L (RootModule Tag.E6 L)) *
            ((T⁻¹ * N * T : ModGL Tag.E6 L) : Module.End L (RootModule Tag.E6 L))
      rw [← Units.val_mul, ← Units.val_mul, hgrp]
    have hKLc := KL.comm _ hcomm (pinnedX Tag.E6 L α t) (pinnedX_mem_rootSpan hα t)
    exact Units.ext hKLc.eq
  · obtain ⟨α₀, hα₀⟩ := hne
    obtain ⟨i₀, m, h₀, hh₀⟩ := KL.sl2 ⟨α₀, hα₀⟩
    set h'' : ModGL Tag.E6 L := (twE6Emb K σ L c)⁻¹ * g0 * h₀ with hh''
    have hKey : ∀ Y : SL2 (fixSubfield σ),
        ∃ y : Subgroup.centralizer ({x} : Set (twistedE6RootGroup K σ)),
        ψ y ∈ KL.P i₀ ∧
        twE6Emb K σ L (y : twistedE6RootGroup K σ) = h'' * simpleRootSL2 Tag.E6 L m
          (Matrix.SpecialLinearGroup.map ((algebraMap K L).comp (fixSubfield σ).subtype) Y) *
            h''⁻¹ := by
      intro Y
      have hmem := hh₀ Y
      obtain ⟨y, hy⟩ := hPψ i₀ hmem
      refine ⟨y, hy ▸ hmem, ?_⟩
      rw [hιψ y, hy, hh'', hT]
      change _ = _ * simpleRootSL2 Tag.E6 L m
        (Matrix.SpecialLinearGroup.map (algebraMap (fixSubfield σ) L) Y) * _
      group
    have hU : ∀ Y : SL2 (fixSubfield σ), h'' * simpleRootSL2 Tag.E6 L m
        (conjGL (1 : GL (Fin 2) L) (Matrix.SpecialLinearGroup.map
          ((algebraMap K L).comp (fixSubfield σ).subtype) Y)) * h''⁻¹ ∈
        (twistedE6RootGroup K σ).map (baseChangeGL (algebraMap K L)) := by
      intro Y
      obtain ⟨y, -, hy⟩ := hKey Y
      rw [phi3_conjGL_one, ← hy]
      exact ⟨(y : twistedE6RootGroup K σ), (y : twistedE6RootGroup K σ).2, rfl⟩
    have hηU : ∀ (u : twistedE6RootGroup K σ) (Y : SL2 (fixSubfield σ)),
        baseChangeGL (algebraMap K L) (u : ModGL TwistTag.E6.tag K) =
          h'' * simpleRootSL2 Tag.E6 L m (conjGL (1 : GL (Fin 2) L)
            (Matrix.SpecialLinearGroup.map ((algebraMap K L).comp (fixSubfield σ).subtype) Y)) *
              h''⁻¹ → η u = u := by
      intro u Y hu
      obtain ⟨y, hyP, hy⟩ := hKey Y
      rw [phi3_conjGL_one, ← hy] at hu
      have hu' : twE6Emb K σ L u = twE6Emb K σ L y := hu
      rw [twE6Emb_injective hu']
      exact hfix i₀ y hyP
    obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -⟩, -⟩ :=
      twisted_E6_all_characteristic_exact_automorphism_normal_form hℓ hf K hK σ hσ
    obtain ⟨-, a₀, -, -, ε, -, hae⟩ :=
      twisted_E6_descended_root_SL2_pointwise_actors_relative_field_free hℓ hf K hK σ hσ Θ hΘ L
        Fr hFr L m 1 h'' hU η hηU
    let a : ModGL Tag.E6 L := a₀
    have hae' : ∀ u : twistedE6RootGroup K σ, twE6Emb K σ L (η u) =
        a * tw6P L ^ ε * twE6Emb K σ L u * (tw6P L ^ ε)⁻¹ * a⁻¹ := hae
    refine ⟨a * tw6P L ^ ε, fun u => ?_⟩
    rw [hae' u]
    simp only [mul_inv_rev, mul_assoc]

end CFSG.RankThree.PartOne.KE6
