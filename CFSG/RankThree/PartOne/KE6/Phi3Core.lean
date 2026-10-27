module

public import CFSG.RankThree.PartOne.KE6.Phi3Solvable
public import CFSG.RankThree.PartOne.KE.CoreInner

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

theorem core_fixes_normal_quasisimple {C : Type*} [Group C] [Finite C] {p : ℕ}
    (hp : p.Prime) (hC : Subgroup.center C = ⊥) {B : Subgroup (MulAut C)}
    (hB : (MulAut.conj : C →* MulAut C).range ≤ B) {x : C} {P : Subgroup C}
    (hPD : P ≤ Subgroup.centralizer ({x} : Set C))
    (hPn : ∀ d ∈ Subgroup.centralizer ({x} : Set C), ∀ u ∈ P, d * u * d⁻¹ ∈ P)
    (hPq : CFSG.IsQuasisimple P) {η : MulAut C}
    (hη : η ∈ inSubgroup (aschbacherSolvableCore p)
      (B ⊓ Subgroup.centralizer ({(MulAut.conj x : MulAut C)} : Set (MulAut C)))) :
    ∀ d ∈ P, η d = d := by
  classical
  have hinj : Function.Injective (MulAut.conj : C →* MulAut C) :=
    conj_injective_of_center_eq_bot hC
  set Int : C →* MulAut C := MulAut.conj with hInt
  set D : Subgroup C := Subgroup.centralizer ({x} : Set C) with hD
  obtain ⟨M, hM⟩ : ∃ M : Subgroup (MulAut C), M =
      B ⊓ Subgroup.centralizer ({(MulAut.conj x : MulAut C)} : Set (MulAut C)) := ⟨_, rfl⟩
  rw [← hM] at hη
  obtain ⟨S, hS⟩ : ∃ S : Subgroup (MulAut C), S = inSubgroup (aschbacherSolvableCore p) M :=
    ⟨_, rfl⟩
  rw [← hS] at hη
  have hSM : S ≤ M := by
    rw [hS]
    exact Subgroup.map_subtype_le _
  have hSnorm : ∀ m ∈ M, ∀ s ∈ S, m * s * m⁻¹ ∈ S := by
    intro m hm s hs
    rw [hS] at hs ⊢
    obtain ⟨s', hs', rfl⟩ := hs
    refine ⟨⟨m, hm⟩ * s' * ⟨m, hm⟩⁻¹, ?_, rfl⟩
    exact (aschbacherSolvableCore_normal p M).conj_mem s' hs' ⟨m, hm⟩
  have hSsol : Group.IsSolvable S := by
    have h := (solvable_prime_complement_core_characterization (H := M) hp).1
    rw [hS, inSubgroup]
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.equivMapOfInjective (aschbacherSolvableCore p M) M.subtype
        M.subtype_injective).symm.toMonoidHom) (MulEquiv.injective _)
  have hmx : ∀ m ∈ M, m x = x := by
    intro m hm
    rw [hM] at hm
    refine fixes_of_commute_conj hC m x ?_
    have h := Subgroup.mem_centralizer_iff.1 hm.2 (MulAut.conj x) rfl
    exact h.symm
  have hmD : ∀ m ∈ M, ∀ d ∈ D, m d ∈ D := by
    intro m hm d hd
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    have h := Subgroup.mem_centralizer_singleton_iff.1 hd
    calc m d * x = m d * m x := by rw [hmx m hm]
      _ = m (d * x) := (map_mul m d x).symm
      _ = m (x * d) := by rw [h]
      _ = m x * m d := map_mul m x d
      _ = x * m d := by rw [hmx m hm]
  have hIntD : ∀ d ∈ D, Int d ∈ M := by
    intro d hd
    rw [hM]
    refine Subgroup.mem_inf.2 ⟨hB ⟨d, rfl⟩, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
    rw [Set.mem_singleton_iff] at hh
    subst hh
    rw [← map_mul, ← map_mul]
    exact congrArg Int (Subgroup.mem_centralizer_singleton_iff.1 hd).symm
  have hPM : P.map Int ≤ M := by
    rintro _ ⟨d, hd, rfl⟩
    exact hIntD d (hPD hd)
  have hDM : D.map Int ≤ M := by
    rintro _ ⟨d, hd, rfl⟩
    exact hIntD d hd
  let K : Subgroup M := (P.map Int).subgroupOf M
  let D' : Subgroup M := (D.map Int).subgroupOf M
  have hKD' : K ≤ D' := fun m hm => by
    obtain ⟨d, hd, hdm⟩ := hm
    exact ⟨d, hPD hd, hdm⟩
  have hD'norm : D'.Normal := ⟨fun n hn g => by
    obtain ⟨d, hd, hdn⟩ := hn
    refine ⟨(g : MulAut C) d, hmD g g.2 d hd, ?_⟩
    have h1 := aut_mul_conj_mul_inv (g : MulAut C) d
    have hdn' : Int d = (n : MulAut C) := hdn
    change Int ((g : MulAut C) d) = (g : MulAut C) * (n : MulAut C) * (g : MulAut C)⁻¹
    rw [← hdn']
    exact h1.symm⟩
  have hKnorm : (K.subgroupOf D').Normal := ⟨fun n hn g => by
    obtain ⟨u, hu, hun⟩ := hn
    obtain ⟨e, he, heg⟩ := g.2
    refine ⟨e * u * e⁻¹, hPn e he u hu, ?_⟩
    change Int (e * u * e⁻¹) = ((g : M) : MulAut C) * (((n : D') : M) : MulAut C) *
      (((g : D') : M) : MulAut C)⁻¹
    rw [map_mul, map_mul, map_inv, heg, hun]
    rfl⟩
  have hKsub : K.IsSubnormal :=
    Subgroup.IsSubnormal.trans hKD' hKnorm.isSubnormal hD'norm.isSubnormal
  have hKq : CFSG.IsQuasisimple K :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((Subgroup.equivMapOfInjective P Int hinj).trans
        (Subgroup.subgroupOfEquivOfLe hPM).symm) hPq
  let R : Subgroup M := S.subgroupOf M
  have hRn : R.Normal := ⟨fun s hs m => by
    change (m : MulAut C) * (s : MulAut C) * (m : MulAut C)⁻¹ ∈ S
    exact hSnorm m m.2 s hs⟩
  have hRsol : Group.IsSolvable R := by
    have e : R ≃* S := Subgroup.subgroupOfEquivOfLe hSM
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  have hcomm := (CFSG.LocalCores.component_solvable_centralizer hRsol hRn.isSubnormal).1 K
    ⟨hKq, hKsub⟩
  intro d hd
  have hηR : (⟨η, hSM hη⟩ : M) ∈ R := hη
  have hdK : (⟨Int d, hPM ⟨d, hd, rfl⟩⟩ : M) ∈ K := ⟨d, hd, rfl⟩
  have h1 : ⁅(⟨Int d, hPM ⟨d, hd, rfl⟩⟩ : M), (⟨η, hSM hη⟩ : M)⁆ ∈ (⁅K, R⁆ : Subgroup M) :=
    Subgroup.commutator_mem_commutator hdK hηR
  rw [hcomm, Subgroup.mem_bot, commutatorElement_def, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
  have h2 : (MulAut.conj d : MulAut C) * η = η * (MulAut.conj d : MulAut C) :=
    congrArg Subtype.val h1
  apply hinj
  rw [← aut_mul_conj_mul_inv, ← h2, mul_assoc, mul_inv_cancel, mul_one]


theorem phi3_conjGL_one {M : Type*} [Field M] (Z : SL2 M) :
    CFSG.RankThree.Chevalley.conjGL (1 : GL (Fin 2) M) Z = Z :=
  Subtype.ext (by simp [CFSG.RankThree.Chevalley.conjGL])

theorem phi3_perx_core (K : Type) [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime]
    [CharP K ℓ] (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + (Nat.card K : ℤ) + 1)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    {g0 : ModGL Tag.E6 L} (hg0C : g0 ∈ adjointGroup Tag.E6 L)
    (hg0 : Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g0 = g0 * phi3N L)
    (hperf : ∀ P : Subgroup (ModGL Tag.E6 L), Finite P → P ≤ adjointGroup Tag.E6 L →
      (∀ x ∈ P, Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x = x) → ⁅P, P⁆ = P →
        P ≤ (adjEmb Tag.E6 K L).range)
    {B : Subgroup (MulAut (adjointGroup Tag.E6 K))}
    (hB : (MulAut.conj : adjointGroup Tag.E6 K →* MulAut (adjointGroup Tag.E6 K)).range ≤ B)
    {x : adjointGroup Tag.E6 K} (hx : orderOf x = p) (c : adjointGroup Tag.E6 K)
    (hh : g0⁻¹ * adjEmb Tag.E6 K L (c * x * c⁻¹) * g0 ∈
      twistedTorus (phi3N L) (iterateFrobenius L ℓ f))
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
    ((torusRootKernel (g0⁻¹ * adjEmb Tag.E6 K L (c * x * c⁻¹) * g0)).Nonempty →
      ∀ (g : adjointGroup Tag.E6 K) (a : Fin Tag.E6.rank → Kˣ) (σ : K ≃+* K)
        (ε : Fin (exactE Tag.E6)),
        (∀ y : adjointGroup Tag.E6 K, (η y : ModGL Tag.E6 K) =
          (g : ModGL Tag.E6 K) * rootDiagUnit Tag.E6 a * exactQ Tag.E6 K ε *
            Units.map (entrywiseHom σ.toRingHom) (y : ModGL Tag.E6 K) *
              (exactQ Tag.E6 K ε)⁻¹ * (rootDiagUnit Tag.E6 a)⁻¹ * (g : ModGL Tag.E6 K)⁻¹) →
        σ = 1) := by
  classical
  obtain ⟨ι', KL, ψ, hψinj, hψdef, hψHQ, hψfix, hPψ, -⟩ :=
    phi3_perx K hf hK hp hp3 hpq L hg0C hg0 hperf hx c hh
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
  · obtain ⟨α₀, hα₀⟩ := hne
    obtain ⟨i₀, m, h₀, hh₀⟩ := KL.sl2 ⟨α₀, hα₀⟩
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
