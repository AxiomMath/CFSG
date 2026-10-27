module

public import CFSG.RankThree.PartOne.KE6.EqpPerx
public import CFSG.RankThree.PartOne.KE6.Phi3Core

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.E6 CFSG.RankThree.Chevalley
  CFSG.RankThree.GroupTheory CFSG.RankThree.LocalRank CFSG.RankThree.PartOne
  CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE (twistedTorus mem_twistedTorus adjEmb adjEmb_apply adjEmb_injective
  adjEmb_mem twistedFixedPoints mem_twistedFixedPoints aut_mul_conj_mul_inv fixes_of_commute_conj
  conj_injective_of_center_eq_bot
  ordinary_E_descended_root_SL2_pointwise_automorphisms_field_free)
open CFSG.RankThree.Classical2 (torusRootKernel)
open scoped Matrix MatrixGroups Pointwise commutatorElement

theorem eqp_perx_core (K : Type) [Field K] [Finite K] [CharP K 2] {f : ℕ}
    (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : (p : ℤ) ∣ (Nat.card K : ℤ) + 1)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L 2]
    {g0 : ModGL Tag.E6 L} (hg0C : g0 ∈ adjointGroup Tag.E6 L)
    (hg0 : Units.map (entrywiseHom (iterateFrobenius L 2 f)) g0 = g0 * eqpN L)
    (hperf : ∀ P : Subgroup (ModGL Tag.E6 L), Finite P → P ≤ adjointGroup Tag.E6 L →
      (∀ x ∈ P, Units.map (entrywiseHom (iterateFrobenius L 2 f)) x = x) → ⁅P, P⁆ = P →
        P ≤ (adjEmb Tag.E6 K L).range)
    {B : Subgroup (MulAut (adjointGroup Tag.E6 K))}
    (hB : (MulAut.conj : adjointGroup Tag.E6 K →* MulAut (adjointGroup Tag.E6 K)).range ≤ B)
    {x : adjointGroup Tag.E6 K} (hx : orderOf x = p) (c : adjointGroup Tag.E6 K)
    (hh : g0⁻¹ * adjEmb Tag.E6 K L (c * x * c⁻¹) * g0 ∈
      twistedTorus (eqpN L) (iterateFrobenius L 2 f))
    {η : MulAut (adjointGroup Tag.E6 K)}
    (hη : η ∈ inSubgroup (aschbacherSolvableCore p) (B ⊓ Subgroup.centralizer
      ({(MulAut.conj x : MulAut (adjointGroup Tag.E6 K))} :
        Set (MulAut (adjointGroup Tag.E6 K))))) :
    (∀ N : ModGL Tag.E6 L,
      (∀ d : adjointGroup Tag.E6 K,
        adjEmb Tag.E6 K L (η d) = N * adjEmb Tag.E6 K L d * N⁻¹) →
      ∀ α ∈ torusRootKernel (g0⁻¹ * adjEmb Tag.E6 K L (c * x * c⁻¹) * g0), ∀ t : L,
        Commute (((adjEmb Tag.E6 K L c)⁻¹ * g0)⁻¹ * N * ((adjEmb Tag.E6 K L c)⁻¹ * g0))
          (pinnedX Tag.E6 L α t)) ∧
    ((∃ α ∈ torusRootKernel (g0⁻¹ * adjEmb Tag.E6 K L (c * x * c⁻¹) * g0),
        permLattice e6Rho α = α) →
      ∀ (g : adjointGroup Tag.E6 K) (a : Fin Tag.E6.rank → Kˣ) (σ : K ≃+* K)
        (ε : Fin (exactE Tag.E6)),
        (∀ y : adjointGroup Tag.E6 K, (η y : ModGL Tag.E6 K) =
          (g : ModGL Tag.E6 K) * rootDiagUnit Tag.E6 a * exactQ Tag.E6 K ε *
            Units.map (entrywiseHom σ.toRingHom) (y : ModGL Tag.E6 K) *
              (exactQ Tag.E6 K ε)⁻¹ * (rootDiagUnit Tag.E6 a)⁻¹ * (g : ModGL Tag.E6 K)⁻¹) →
        σ = 1) := by
  classical
  obtain ⟨ι', KL, ψ, hψinj, hψdef, hψHQ, hψfix, hPψ, -⟩ :=
    eqp_perx K hf hK hp hp3 hpq L hg0C hg0 hperf hx c hh
  have hC : Subgroup.center (adjointGroup Tag.E6 K) = ⊥ := center_adjointGroup_eq_bot
  have hfix : ∀ (i : ι') (d : Subgroup.centralizer ({x} : Set (adjointGroup Tag.E6 K))),
      ψ d ∈ KL.P i → η (d : adjointGroup Tag.E6 K) = d := by
    intro i d hd
    set P' : Subgroup (adjointGroup Tag.E6 K) :=
      ((KL.P i).comap ψ).map (Subgroup.centralizer ({x} : Set (adjointGroup Tag.E6 K))).subtype
      with hP'
    have hPD : P' ≤ Subgroup.centralizer ({x} : Set (adjointGroup Tag.E6 K)) :=
      Subgroup.map_subtype_le _
    have hPn : ∀ e ∈ Subgroup.centralizer ({x} : Set (adjointGroup Tag.E6 K)), ∀ u ∈ P',
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
            (Subgroup.centralizer ({x} : Set (adjointGroup Tag.E6 K))).subtype
            (Subgroup.centralizer ({x} : Set (adjointGroup Tag.E6 K))).subtype_injective))
        (KL.quasi i)
    exact core_fixes_normal_quasisimple hp hC hB hPD hPn hPq hη (d : adjointGroup Tag.E6 K)
      ⟨d, hd, rfl⟩
  set T : ModGL Tag.E6 L := (adjEmb Tag.E6 K L c)⁻¹ * g0 with hT
  have hιψ : ∀ d : Subgroup.centralizer ({x} : Set (adjointGroup Tag.E6 K)),
      adjEmb Tag.E6 K L (d : adjointGroup Tag.E6 K) = T * ψ d * T⁻¹ := by
    intro d
    rw [hψdef d, hT]
    simp only [map_mul, map_inv]
    group
  refine ⟨fun N hN α hα t => ?_, fun hne g a σ ε hexpr => ?_⟩
  · have hcomm : ∀ (i : ι'), ∀ u ∈ KL.P i,
        Commute (((T⁻¹ * N * T : ModGL Tag.E6 L) : Module.End L (RootModule Tag.E6 L)))
          (u : Module.End L (RootModule Tag.E6 L)) := by
      intro i u hu
      obtain ⟨d, hdu⟩ := hPψ i hu
      have hdi : ψ d ∈ KL.P i := hdu ▸ hu
      have hηd := hfix i d hdi
      have hNd := hN (d : adjointGroup Tag.E6 K)
      rw [hηd] at hNd
      have hcomm' : N * adjEmb Tag.E6 K L (d : adjointGroup Tag.E6 K) =
          adjEmb Tag.E6 K L (d : adjointGroup Tag.E6 K) * N := by
        calc N * adjEmb Tag.E6 K L (d : adjointGroup Tag.E6 K)
            = (N * adjEmb Tag.E6 K L (d : adjointGroup Tag.E6 K) * N⁻¹) * N := by group
          _ = adjEmb Tag.E6 K L (d : adjointGroup Tag.E6 K) * N := by rw [← hNd]
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
  · obtain ⟨i₀, m, h₀, hh₀⟩ := KL.sl2 hne
    set h'' : ModGL Tag.E6 L := (adjEmb Tag.E6 K L c)⁻¹ * g0 * h₀ with hh''
    have hKey : ∀ Y : SL2 K, ∃ y : Subgroup.centralizer ({x} : Set (adjointGroup Tag.E6 K)),
        ψ y ∈ KL.P i₀ ∧
        adjEmb Tag.E6 K L (y : adjointGroup Tag.E6 K) = h'' * simpleRootSL2 Tag.E6 L m
          (Matrix.SpecialLinearGroup.map (algebraMap K L) Y) * h''⁻¹ := by
      intro Y
      have hmem := hh₀ Y
      obtain ⟨y, hy⟩ := hPψ i₀ hmem
      refine ⟨y, hy ▸ hmem, ?_⟩
      rw [hιψ y, hy, hh'', hT]
      group
    let Z : Subgroup (MulAut (adjointGroup Tag.E6 K)) :=
      { carrier := {η' | ∀ y : Subgroup.centralizer ({x} : Set (adjointGroup Tag.E6 K)),
          ψ y ∈ KL.P i₀ → η' (y : adjointGroup Tag.E6 K) = y}
        mul_mem' := fun {a b} ha hb y hy => by
          rw [MulAut.mul_apply, hb y hy, ha y hy]
        one_mem' := fun y _ => rfl
        inv_mem' := fun {a} ha y hy => by
          have := ha y hy
          calc a⁻¹ (y : adjointGroup Tag.E6 K) = a⁻¹ (a (y : adjointGroup Tag.E6 K)) := by
                rw [this]
            _ = y := by rw [← MulAut.mul_apply, inv_mul_cancel]; rfl }
    have hηZ : η ∈ Z := fun y hy => hfix i₀ y hy
    have hZ : ∀ η' ∈ Z, ∀ (u : adjointGroup Tag.E6 K) (Y : SL2 K),
        baseChangeGL (algebraMap K L) (u : ModGL Tag.E6 K) =
          h'' * simpleRootSL2 Tag.E6 L m (CFSG.RankThree.Chevalley.conjGL (1 : GL (Fin 2) L)
            (Matrix.SpecialLinearGroup.map (algebraMap K L) Y)) * h''⁻¹ → η' u = u := by
      intro η' hη'Z u Y hu
      obtain ⟨y, hyP, hy⟩ := hKey Y
      rw [phi3_conjGL_one, ← hy] at hu
      have hu' : adjEmb Tag.E6 K L u = adjEmb Tag.E6 K L (y : adjointGroup Tag.E6 K) := by
        rw [adjEmb_apply, hu]
      rw [adjEmb_injective hu']
      exact hη'Z y hyP
    have hU : ∀ Y : SL2 K, h'' * simpleRootSL2 Tag.E6 L m
        (CFSG.RankThree.Chevalley.conjGL (1 : GL (Fin 2) L)
          (Matrix.SpecialLinearGroup.map (algebraMap K L) Y)) * h''⁻¹ ∈
        (adjointGroup Tag.E6 K).map (baseChangeGL (algebraMap K L)) := by
      intro Y
      obtain ⟨y, -, hy⟩ := hKey Y
      rw [phi3_conjGL_one, ← hy]
      exact ⟨((y : adjointGroup Tag.E6 K) : ModGL Tag.E6 K), (y : adjointGroup Tag.E6 K).2, rfl⟩
    exact (ordinary_E_descended_root_SL2_pointwise_automorphisms_field_free Tag.E6
      (Or.inl rfl) K L m 1 h'' hU Z hZ).1 η hηZ g a σ ε hexpr

end CFSG.RankThree.PartOne.KE6
