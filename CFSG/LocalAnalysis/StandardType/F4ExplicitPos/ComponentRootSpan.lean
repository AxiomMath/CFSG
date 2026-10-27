module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.ActualSetupPart1
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.CyclicFinish
public import CFSG.LocalAnalysis.ComponentInitial.BlockCentralQuotient
public import CFSG.LieType.Chevalley.SylowOpposition

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.StandardType.F4ExplicitPos.AmbientAction
  CFSG.StandardType.F4ExplicitPos.ComponentAttach


theorem frobRootMap_of_frobenius {K Ω : Type} [Field K] [Finite K] [Field Ω] [Algebra K Ω]
    (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ Nat.card K) (hFrsurj : Function.Surjective Fr)
    (Δ : LangDatum .F4 Ω) (hΦ : Δ.Φ = Units.map (entrywiseHom Fr))
    (hq : Δ.q = Nat.card K) :
    ∃ w : WeylGroup .F4, Δ.n = canonicalRep (coxeterSystem .F4) Ω w ∧
      FrobRootMap Δ (MulAction.toPerm w) := by
  obtain ⟨w, hw⟩ := Δ.n_weyl
  have hg : ((frobF4 (K := K) (L := Ω) Fr hFr ⟨Δ.g0, Δ.g0_mem⟩ :
      adjointGroup .F4 Ω) : ModGL .F4 Ω) =
      Δ.g0 * canonicalRep (coxeterSystem .F4) Ω w := by
    rw [frobF4_coe_eq_unitsMap, ← hΦ, Δ.lang, hw]
  have hΔ : Δ = langDatumF4 Fr hFr w Δ.g0_mem hg := by
    cases Δ
    dsimp only at hΦ hq hw
    subst_vars
    rfl
  refine ⟨w, hw, ?_⟩
  rw [hΔ]
  exact ActualSetup.frobRootMap_langDatumF4 Fr hFr hFrsurj w Δ.g0_mem hg

theorem component_le_rationalRootSpan_of_frobenius
    {K Ω : Type} [Field K] [Finite K] [Field Ω] [Algebra K Ω]
    (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ Nat.card K) (hFrsurj : Function.Surjective Fr)
    (Δ : LangDatum .F4 Ω) (hΦ : Δ.Φ = Units.map (entrywiseHom Fr))
    (hq : Δ.q = Nat.card K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (u : adjointGroup .F4 K) (hup : u ^ p = 1) (hu : u ≠ 1)
    (Q : Subgroup (adjointGroup .F4 K))
    (hQ : IsComponentOf Q (Subgroup.centralizer ({u} : Set (adjointGroup .F4 K))))
    (hT : ((jF4 (K := K) (L := Ω) u : adjointGroup .F4 Ω) : ModGL .F4 Ω) ∈
      Δ.torus.map (MulAut.conj Δ.g0).toMonoidHom) :
    ∃ η : adjointGroup .F4 K →* ModGL .F4 Ω,
      (∀ v, η v = Δ.g0⁻¹ *
        ((jF4 (K := K) (L := Ω) v : adjointGroup .F4 Ω) : ModGL .F4 Ω) * Δ.g0) ∧
      Function.Injective η ∧ η.range = Δ.model ∧
      ∃ a : Fin Tag.F4.rank → Ωˣ, η u = rootDiagUnit .F4 a ∧
        (∀ i, a i ^ p = 1) ∧ a ≠ 1 ∧ rootDiagUnit .F4 a ∈ Δ.torus ∧
        ∃ w : WeylGroup .F4, Δ.n = canonicalRep (coxeterSystem .F4) Ω w ∧
          FrobRootMap Δ (MulAction.toPerm w) ∧
          ∃ i : KernelComponent (rootCharHom a),
            IsComponentOf (Q.map η) (Δ.Γ ⊓ Subgroup.centralizer {rootDiagUnit .F4 a}) ∧
            Q.map η ≤ rootSpan .F4 Ω (rationalRoots (MulAction.toPerm w) (rootCharHom a) i) := by
  classical
  let η₀ : adjointGroup .F4 K →* ModGL .F4 Ω :=
    (adjointGroup .F4 Ω).subtype.comp (jF4 (K := K) (L := Ω))
  let η := (MulAut.conj Δ.g0⁻¹).toMonoidHom.comp η₀
  have hη₀ : Function.Injective η₀ :=
    (adjointGroup .F4 Ω).subtype_injective.comp (jF4_injective (K := K) (L := Ω))
  have hη : Function.Injective η := (MulAut.conj Δ.g0⁻¹).injective.comp hη₀
  have hfix : η₀.range = Δ.fix := by
    change ((adjointGroup .F4 Ω).subtype.comp (jF4 (K := K) (L := Ω))).range = Δ.fix
    rw [MonoidHom.range_comp, jF4_range_eq,
      FixedImage.f4_finite_field_fixed_eq_map (K := K) (Ω := Ω) Fr hFr]
    rw [LangDatum.fix, hΦ]
  have hrange : η.range = Δ.model := by
    change ((MulAut.conj Δ.g0⁻¹).toMonoidHom.comp η₀).range = Δ.model
    rw [MonoidHom.range_comp, hfix]
    exact (LangDescent.model_eq Δ).symm
  letI : Finite (ModGL .F4 K) := CFSG.LieType.Chevalley.finite_modGL
  letI : Finite (adjointGroup .F4 K) := inferInstance
  have hfin : Finite Δ.model := by
    rw [← hrange]
    have hset : (η.range : Set (ModGL .F4 Ω)).Finite := by
      change (Set.range η).Finite
      exact Set.finite_range η
    exact hset.to_subtype
  letI := hfin
  obtain ⟨v, hvT, hv⟩ := hT
  change Δ.g0 * v * Δ.g0⁻¹ = η₀ u at hv
  obtain ⟨a, hva⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hvT.1
  have hua : η u = rootDiagUnit .F4 a := by
    change Δ.g0⁻¹ * η₀ u * Δ.g0 = rootDiagUnit .F4 a
    rw [← hv, hva]
    group
  have haT : rootDiagUnit .F4 a ∈ Δ.torus := hva ▸ hvT
  have hap : a ^ p = 1 := by
    apply CFSG.HardMathSupport.Timmesfeld.CrossChar.rootDiagUnit_injective
    rw [rootDiagUnit_one]
    change (rootDiagUnitHom .F4 Ω) (a ^ p) = 1
    rw [map_pow]
    change rootDiagUnit .F4 a ^ p = 1
    rw [← hua, ← map_pow, hup, map_one]
  have ha1 : a ≠ 1 := by
    intro ha
    apply hu
    apply hη
    rw [hua, ha, rootDiagUnit_one, map_one]
  have hC : (Subgroup.centralizer ({u} : Set (adjointGroup .F4 K))).map η =
      Δ.model ⊓ Subgroup.centralizer ({rootDiagUnit .F4 a} : Set (ModGL .F4 Ω)) := by
    rw [← hrange, ← hua]
    ext y
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨⟨v, rfl⟩, ?_⟩
      have hc : v * u = u * v := Subgroup.mem_centralizer_singleton_iff.mp hv
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      rw [← map_mul, hc, map_mul]
    · rintro ⟨⟨v, rfl⟩, hv⟩
      refine ⟨v, ?_, rfl⟩
      have hc : η v * η u = η u * η v := Subgroup.mem_centralizer_singleton_iff.mp hv
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      exact hη (by rw [map_mul, hc, map_mul])
  have hM := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_of_injective hQ η hη
  rw [hC] at hM
  have hperf : Group.IsPerfect (Q.map η) := ⟨hM.2.2.1⟩
  letI := hperf
  have hMQM : Q.map η ≤ Δ.model := hM.1.trans inf_le_left
  have hMQΓ : Q.map η ≤ Δ.Γ := by
    calc
      Q.map η = ⁅Q.map η, Q.map η⁆ := (Subgroup.commutator_eq_self (H := Q.map η)).symm
      _ ≤ ⁅Δ.model, Δ.model⁆ := Subgroup.commutator_mono hMQM hMQM
  have hMΓ : IsComponentOf (Q.map η)
      (Δ.Γ ⊓ Subgroup.centralizer ({rootDiagUnit .F4 a} : Set (ModGL .F4 Ω))) :=
    hM.of_le_of_le (le_inf hMQΓ (hM.1.trans inf_le_right))
      (inf_le_inf (Subgroup.commutator_le_self _) le_rfl)
  obtain ⟨w, hw, hρ⟩ := frobRootMap_of_frobenius Fr hFr hFrsurj Δ hΦ hq
  obtain ⟨i, hi⟩ := CyclicFinish.f4_component_le_rationalRootSpan Δ (MulAction.toPerm w) hρ
    hp hp2 a (fun j => congrFun hap j) haT (Q.map η) hMΓ
  exact ⟨η, fun _ => rfl, hη, hrange, a, hua, fun j => congrFun hap j, ha1, haT,
    w, hw, hρ, i, hMΓ, hi⟩

end CFSG.StandardType.F4ExplicitPos
