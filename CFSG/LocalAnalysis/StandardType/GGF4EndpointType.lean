module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveRest
public import CFSG.LocalAnalysis.StandardType.GGSecFiveDataResDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
public import CFSG.LocalAnalysis.StandardType.GGF4TypeCards
import CFSG.LocalAnalysis.StandardType.GGF4LinFour
import CFSG.LocalAnalysis.StandardType.GGF4OrigRep
import CFSG.LocalAnalysis.StandardType.GGF4RankFour
import CFSG.LocalAnalysis.StandardType.GGF4RankLow
import CFSG.LocalAnalysis.StandardType.GGF4ReflGroup
import CFSG.LocalAnalysis.StandardType.GGF4ReflLin
import CFSG.LocalAnalysis.StandardType.GGF4CoxeterSystem
import CFSG.LocalAnalysis.StandardType.GGF4ReflOrbit
import CFSG.LocalAnalysis.StandardType.GGSecFiveRootRefl
import CFSG.LocalAnalysis.StandardType.GGSpJoinReflAlgebra
import CFSG.LocalAnalysis.StandardType.GGSpJoinCoxeterCard
import CFSG.LocalAnalysis.StandardType.GGSpFrameCoxeterCard
import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofRefl
import CFSG.LocalAnalysis.StandardType.GGTypeANbrWeylA
import TauCeti.GroupTheory.Coxeter.Geometric

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.StandardType.F4Model

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}

private theorem ggF4Endpoint_setup (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs)
    (hNT : GGNoTransvection p Bs)
    {A : Subgroup (MulAut ↥Bs)} (hAind : ∀ φ ∈ A, φ ∈ ggInduced ⊤ Bs)
    {ι : Type} (e' : Fin 4 ≃ ι) {e : (CoxeterMatrix.F₄.reindex e').Group ≃* ↥A}
    (hP : GGCoxeterPres p A (CoxeterMatrix.F₄.reindex e') e) :
    ∃ R : F4Rep ↥A,
      (∀ i, R.s i = (ggF4CoxeterSystem e' e).simple i) ∧
      (∀ (φ : MulAut ↥Bs) (hφ : φ ∈ A), GGIsReflection p φ →
        (ggF4CoxeterSystem e' e).IsReflection ⟨φ, hφ⟩) := by
  obtain ⟨R, hRs⟩ := exists_f4Rep (ggF4CoxeterSystem e' e)
  exact ⟨R, hRs, fun φ hφ hr =>
    (ggF4CoxeterSystem_isReflection_iff Fact.out hp2 hBs hNT hAind e' hP ⟨φ, hφ⟩).2 hr⟩

omit [Finite G] [Fact (Nat.Prime p)] in
private theorem ggF4Endpoint_hdata
    {n : ℕ} {A : Subgroup (MulAut ↥Bs)} {X : Subgroup (MulAut ↥Bs)} (hXA : X ≤ A)
    (R : F4Rep ↥A) (cs : CoxeterSystem CoxeterMatrix.F₄ ↥A) (hRs : ∀ i, R.s i = cs.simple i)
    (hconv : ∀ (φ : MulAut ↥Bs) (hφ : φ ∈ A), GGIsReflection p φ →
      cs.IsReflection ⟨φ, hφ⟩)
    (T : CoxeterMatrix (Fin n)) (hT : GGWeylOfType p T X) :
    ∃ (a : Fin n → ↥A) (eT : T.Group ≃* ↥X),
      (∀ i, a i = Subgroup.inclusion hXA (eT (T.simple i))) ∧
      (∀ i, R.IsRefl (a i)) ∧ (∀ i, (a i : ↥A) ∈ X.comap A.subtype) ∧
      (∀ i, GGIsReflection p ((a i : ↥A) : MulAut ↥Bs)) ∧
      ∀ i j, orderOf (a i * a j) = T.M i j := by
  obtain ⟨eT, heT⟩ := hT
  obtain ⟨a, ha_def⟩ : ∃ a : Fin n → ↥A, ∀ i,
      a i = Subgroup.inclusion hXA (eT (T.simple i)) :=
    ⟨fun i => Subgroup.inclusion hXA (eT (T.simple i)), fun i => rfl⟩
  refine ⟨a, eT, ha_def, ?_, ?_, ?_, ?_⟩
  · intro i
    refine (F4Rep.isRefl_iff hRs).2 ?_
    rw [ha_def i]
    exact hconv (eT (T.simple i) : MulAut ↥Bs) (hXA (eT (T.simple i)).2) (heT i)
  · intro i
    rw [ha_def i]
    exact (eT (T.simple i)).2
  · intro i
    rw [ha_def i]
    exact heT i
  · intro i j
    have h1 : a i * a j = Subgroup.inclusion hXA (eT (T.simple i * T.simple j)) := by
      rw [ha_def i, ha_def j, map_mul, map_mul]
    rw [h1, orderOf_injective (Subgroup.inclusion hXA) (Subgroup.inclusion_injective hXA),
      MulEquiv.orderOf_eq eT]
    simpa using T.toCoxeterSystem.orderOf_simple_mul_simple i j

omit [Finite G] in
private theorem ggF4Endpoint_hgen {n : ℕ} {A : Subgroup (MulAut ↥Bs)} {X : Subgroup (MulAut ↥Bs)}
    (hXA : X ≤ A) {T : CoxeterMatrix (Fin n)} {eT : T.Group ≃* ↥X}
    (a : Fin n → ↥A) (ha_def : ∀ i, a i = Subgroup.inclusion hXA (eT (T.simple i))) :
    Subgroup.closure (Set.range (fun i => ((a i : ↥A) : MulAut ↥Bs))) = X := by
  have h1 : Set.range (fun i => ((a i : ↥A) : MulAut ↥Bs)) = A.subtype '' Set.range a := by
    ext x
    simp [Set.range, Subgroup.subtype]
  rw [h1, ← MonoidHom.map_closure]
  have h2 : Subgroup.closure (Set.range a) = X.comap A.subtype := by
    have h3 : Set.range a = Subgroup.inclusion hXA '' Set.range (fun i => eT (T.simple i)) := by
      ext x
      simp [ha_def, Subgroup.inclusion]
    rw [h3, ← MonoidHom.map_closure]
    have h4 : Subgroup.closure (Set.range (fun i => eT (T.simple i))) = ⊤ := by
      have h : Subgroup.closure (Set.range T.simple) = ⊤ :=
        T.toCoxeterSystem.subgroup_closure_range_simple
      have hmap : Subgroup.map eT.toMonoidHom (Subgroup.closure (Set.range T.simple)) = ⊤ := by
        rw [h, Subgroup.map_top_of_surjective _ eT.surjective]
      rw [MonoidHom.map_closure, ← Set.range_comp] at hmap
      exact hmap
    rw [h4, Subgroup.map_top]
    ext x
    constructor
    · rintro ⟨y, h⟩
      have h' : (y : MulAut ↥Bs) = x := congrArg Subtype.val h
      have hyx : (y : MulAut ↥Bs) ∈ X := y.2
      rw [h'] at hyx
      exact hyx
    · intro hx
      rw [MonoidHom.mem_range]
      exact ⟨⟨x.val, by simpa [Subgroup.comap] using hx⟩, Subtype.ext rfl⟩
  rw [h2]
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_map] at hx
    rcases hx with ⟨y, hy, hxy⟩
    have hyx : y.val ∈ X := by simpa [Subgroup.comap] using hy
    have h' : (y : MulAut ↥Bs) = x := by simpa using hxy
    rw [h'] at hyx
    exact hyx
  · intro hx
    rw [Subgroup.mem_map]
    exact ⟨⟨x, hXA hx⟩, by simpa [Subgroup.comap] using hx, rfl⟩

omit [Finite G] [Fact (Nat.Prime p)] in
private theorem ggF4Endpoint_htrefl_of {A : Subgroup (MulAut ↥Bs)} {a : Fin 4 → ↥A}
    (harefl : ∀ i, GGIsReflection p ((a i : ↥A) : MulAut ↥Bs))
    {t : Fin 4 → ↥A}
    (htconj : ∀ k, ∃ (g : ↥A) (j : Fin 4), t k = g * a j * g⁻¹) :
    ∀ k, GGIsReflection p ((t k : ↥A) : MulAut ↥Bs) := by
  intro k
  obtain ⟨g, j, hg⟩ := htconj k
  rw [hg]
  exact (harefl j).conj ((g : ↥A) : MulAut ↥Bs)

private theorem ggF4Endpoint_contra_quad
    (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs) (hcard : Nat.card ↥Bs ≤ p ^ 4)
    {A : Subgroup (MulAut ↥Bs)} {X : Subgroup (MulAut ↥Bs)} {u : G} (hu : u ∈ Bs)
    (hu1 : u ≠ 1)
    (hfixX : ∀ b : ↥Bs, (∀ φ ∈ X, φ b = b) ↔ (b : G) ∈ Subgroup.zpowers u) :
    (∃ t : Fin 4 → ↥A, (∀ k, (t k : ↥A) ∈ X.comap A.subtype) ∧
      (∀ k, GGIsReflection p ((t k : ↥A) : MulAut ↥Bs)) ∧
      (∀ j k, t j * t k = t k * t j) ∧ Function.Injective t) → False := by
  rintro ⟨t, htX, htrefl, hcomm, hinj⟩
  have hx'1 : (⟨u, hu⟩ : ↥Bs) ≠ 1 := fun h => hu1 (Subtype.ext_iff.mp h)
  have hfixXu : ∀ φ ∈ X, φ ⟨u, hu⟩ = ⟨u, hu⟩ :=
    (hfixX ⟨u, hu⟩).2 (Subgroup.mem_zpowers u)
  have hfix : ∀ k, ((t k : ↥A) : MulAut ↥Bs) ⟨u, hu⟩ = ⟨u, hu⟩ := fun k =>
    hfixXu ((t k : ↥A)) (htX k)
  exact hx'1 (ggF4Orig_fix_four hp2 hBs hcard (fun k => ((t k : ↥A) : MulAut ↥Bs))
    htrefl (fun j k => congrArg Subtype.val (hcomm j k)) (fun j k h => hinj (Subtype.ext h))
    ⟨u, hu⟩ hfix)

omit [Finite G] [Fact (Nat.Prime p)] in
private theorem ggF4Endpoint_isRefl_of_R
    {A : Subgroup (MulAut ↥Bs)} {ι : Type} (e' : Fin 4 ≃ ι)
    {e : (CoxeterMatrix.F₄.reindex e').Group ≃* ↥A}
    (hP : GGCoxeterPres p A (CoxeterMatrix.F₄.reindex e') e)
    (R : F4Rep ↥A)
    (hRs : ∀ i, R.s i = (ggF4CoxeterSystem e' e).simple i)
    {t : ↥A} (ht : R.IsRefl t) : GGIsReflection p (t : MulAut ↥Bs) := by
  obtain ⟨g, j, hg⟩ := (F4Rep.isRefl_iff hRs).1 ht
  have hsimple : GGIsReflection p (((ggF4CoxeterSystem e' e).simple j : ↥A) : MulAut ↥Bs) := by
    rw [ggF4CoxeterSystem_simple e' e j]
    exact hP.2 (e' j)
  rw [hg]
  exact hsimple.conj ((g : ↥A) : MulAut ↥Bs)

private theorem ggF4Endpoint_inv_of_endpoint
    (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs)
    {A : Subgroup (MulAut ↥Bs)} {u : G} (hu : u ∈ Bs) (hu1 : u ≠ 1)
    {X : Subgroup (MulAut ↥Bs)}
    (hfixX : ∀ b : ↥Bs, (∀ φ ∈ X, φ b = b) ↔ (b : G) ∈ Subgroup.zpowers u)
    {tA : ↥A} (htRefl : GGIsReflection p (tA : MulAut ↥Bs))
    {a : Fin 3 → ↥A}
    (harefl : ∀ i, GGIsReflection p ((a i : ↥A) : MulAut ↥Bs))
    (hgen : Subgroup.closure (Set.range (fun i => ((a i : ↥A) : MulAut ↥Bs))) = X)
    (hne0 : tA ≠ a 0) (hne1 : tA ≠ a 1) (hne2 : tA ≠ a 2)
    (hcomm0 : Commute tA (a 0)) (hcomm1 : Commute tA (a 1)) (hcomm2 : Commute tA (a 2)) :
    (tA : MulAut ↥Bs) ⟨u, hu⟩ = ⟨u, hu⟩⁻¹ := by
  have hS : ∀ φ ∈ Set.range (fun i => ((a i : ↥A) : MulAut ↥Bs)),
      GGIsReflection p φ ∧ φ * (tA : MulAut ↥Bs) = (tA : MulAut ↥Bs) * φ ∧ φ ≠ tA := by
    rintro _ ⟨i, rfl⟩
    refine ⟨harefl i, ?_, ?_⟩
    · fin_cases i
      · exact (congrArg Subtype.val hcomm0).symm
      · exact (congrArg Subtype.val hcomm1).symm
      · exact (congrArg Subtype.val hcomm2).symm
    · fin_cases i
      · exact fun h => hne0 (Subtype.val_injective h).symm
      · exact fun h => hne1 (Subtype.val_injective h).symm
      · exact fun h => hne2 (Subtype.val_injective h).symm
  refine GGIsReflection.apply_eq_inv_of_fix hp2 hBs htRefl
    (S := Set.range (fun i => ((a i : ↥A) : MulAut ↥Bs))) hS hu hu1 ?_
  intro b hb
  refine (hfixX b).1 ?_
  intro φ hφ
  rw [← hgen] at hφ
  exact hb φ hφ

private theorem ggF4Endpoint_exists_t
    (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs)
    {A : Subgroup (MulAut ↥Bs)} {ι : Type} (e' : Fin 4 ≃ ι)
    {e : (CoxeterMatrix.F₄.reindex e').Group ≃* ↥A}
    (hP : GGCoxeterPres p A (CoxeterMatrix.F₄.reindex e') e) (R : F4Rep ↥A)
    (hRs : ∀ i, R.s i = (ggF4CoxeterSystem e' e).simple i)
    {u : G} (hu : u ∈ Bs) (hu1 : u ≠ 1)
    {X : Subgroup (MulAut ↥Bs)}
    (hfixX : ∀ b : ↥Bs, (∀ φ ∈ X, φ b = b) ↔ (b : G) ∈ Subgroup.zpowers u)
    (a : Fin 3 → ↥A) (haR : ∀ i, R.IsRefl (a i))
    (harefl : ∀ i, GGIsReflection p ((a i : ↥A) : MulAut ↥Bs))
    (hgen : Subgroup.closure (Set.range (fun i => ((a i : ↥A) : MulAut ↥Bs))) = X)
    (h01 : orderOf (a 0 * a 1) = 3) (h02 : orderOf (a 0 * a 2) = 2)
    (h12 : orderOf (a 1 * a 2) = 3 ∨ orderOf (a 1 * a 2) = 4) :
    ∃ t ∈ A, GGIsReflection p t ∧ t ⟨u, hu⟩ = ⟨u, hu⟩⁻¹ ∧ (∀ φ ∈ X, φ * t = t * φ) := by
  obtain ⟨tA, ht, hne0, hne1, hne2, hcomm0, hcomm1, hcomm2⟩ :=
    R.exists_endpoint (haR 0) (haR 1) (haR 2) h01 h02 h12
  have htRefl : GGIsReflection p (tA : MulAut ↥Bs) :=
    ggF4Endpoint_isRefl_of_R e' hP R hRs ht
  have hcommX : ∀ φ ∈ X, φ * (tA : MulAut ↥Bs) = (tA : MulAut ↥Bs) * φ := by
    have hsub : X ≤ Subgroup.centralizer ({(tA : MulAut ↥Bs)} : Set (MulAut ↥Bs)) := by
      rw [← hgen, Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact Subgroup.mem_centralizer_iff.mpr (fun y hy => by
          simp only [Set.mem_singleton_iff] at hy; subst hy
          exact congrArg Subtype.val hcomm0)
      · exact Subgroup.mem_centralizer_iff.mpr (fun y hy => by
          simp only [Set.mem_singleton_iff] at hy; subst hy
          exact congrArg Subtype.val hcomm1)
      · exact Subgroup.mem_centralizer_iff.mpr (fun y hy => by
          simp only [Set.mem_singleton_iff] at hy; subst hy
          exact congrArg Subtype.val hcomm2)
    intro φ hφ
    exact (Subgroup.mem_centralizer_iff.mp (hsub hφ) (tA : MulAut ↥Bs)
      (Set.mem_singleton _)).symm
  have htu : (tA : MulAut ↥Bs) ⟨u, hu⟩ = ⟨u, hu⟩⁻¹ :=
    ggF4Endpoint_inv_of_endpoint hp2 hBs hu hu1 hfixX htRefl harefl hgen hne0 hne1 hne2
      hcomm0 hcomm1 hcomm2
  exact ⟨(tA : MulAut ↥Bs), tA.2, htRefl, htu, hcommX⟩

private theorem ggF4Endpoint_B4_false
    (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs) (hcard : Nat.card ↥Bs ≤ p ^ 4)
    {A : Subgroup (MulAut ↥Bs)} {X : Subgroup (MulAut ↥Bs)} (hXA : X ≤ A)
    (R : F4Rep ↥A) (cs : CoxeterSystem CoxeterMatrix.F₄ ↥A) (hRs : ∀ i, R.s i = cs.simple i)
    (hconv : ∀ (φ : MulAut ↥Bs) (hφ : φ ∈ A), GGIsReflection p φ → cs.IsReflection ⟨φ, hφ⟩)
    {u : G} (hu : u ∈ Bs) (hu1 : u ≠ 1)
    (hfixX : ∀ b : ↥Bs, (∀ φ ∈ X, φ b = b) ↔ (b : G) ∈ Subgroup.zpowers u)
    (hT : GGWeylOfType p (CoxeterMatrix.B 4) X) : False := by
  obtain ⟨a, eT, ha_def, haR, haH, harefl, hord⟩ :=
    ggF4Endpoint_hdata hXA R cs hRs hconv (CoxeterMatrix.B 4) hT
  obtain ⟨t, htH, htconj, htcomm, htinj⟩ := R.rank_four_B (X.comap A.subtype) haR haH
    (by rw [hord 0 1]; decide)
    (by rw [hord 1 2]; decide)
    (by rw [hord 2 3]; decide)
    (by rw [hord 0 2]; decide)
    (by rw [hord 0 3]; decide)
    (by rw [hord 1 3]; decide)
  exact ggF4Endpoint_contra_quad hp2 hBs hcard hu hu1 hfixX
    ⟨t, htH, ggF4Endpoint_htrefl_of harefl htconj, htcomm, htinj⟩

private theorem ggF4Endpoint_D4_false
    (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs) (hcard : Nat.card ↥Bs ≤ p ^ 4)
    {A : Subgroup (MulAut ↥Bs)} {X : Subgroup (MulAut ↥Bs)} (hXA : X ≤ A)
    (R : F4Rep ↥A) (cs : CoxeterSystem CoxeterMatrix.F₄ ↥A) (hRs : ∀ i, R.s i = cs.simple i)
    (hconv : ∀ (φ : MulAut ↥Bs) (hφ : φ ∈ A), GGIsReflection p φ → cs.IsReflection ⟨φ, hφ⟩)
    {u : G} (hu : u ∈ Bs) (hu1 : u ≠ 1)
    (hfixX : ∀ b : ↥Bs, (∀ φ ∈ X, φ b = b) ↔ (b : G) ∈ Subgroup.zpowers u)
    (hT : GGWeylOfType p (ggCoxeterMatrixD 4) X) : False := by
  obtain ⟨a, eT, ha_def, haR, haH, harefl, hord⟩ :=
    ggF4Endpoint_hdata hXA R cs hRs hconv (ggCoxeterMatrixD 4) hT
  obtain ⟨t, htH, htconj, htcomm, htinj⟩ := R.rank_four_D (X.comap A.subtype) haR haH
    (by rw [hord 0 1]; decide)
    (by rw [hord 1 2]; decide)
    (by rw [hord 1 3]; decide)
    (by rw [hord 0 2]; decide)
    (by rw [hord 0 3]; decide)
    (by rw [hord 2 3]; decide)
  exact ggF4Endpoint_contra_quad hp2 hBs hcard hu hu1 hfixX
    ⟨t, htH, ggF4Endpoint_htrefl_of harefl htconj, htcomm, htinj⟩

omit [Fact (Nat.Prime p)] in
private theorem ggF4Endpoint_F4_false
    {A : Subgroup (MulAut ↥Bs)} (hcardA : Nat.card ↥A = 1152)
    (hfixA : ∀ b : ↥Bs, (∀ ψ ∈ A, ψ b = b) → b = 1)
    {X : Subgroup (MulAut ↥Bs)} (hXA : X ≤ A) {u : G} (hu : u ∈ Bs) (hu1 : u ≠ 1)
    (hfixX : ∀ b : ↥Bs, (∀ φ ∈ X, φ b = b) ↔ (b : G) ∈ Subgroup.zpowers u)
    (hT : GGWeylOfType p CoxeterMatrix.F₄ X) : False := by
  have hcardX := ggF4Orig_card_weylOfType_F4 hT
  have hEq : X = A := Subgroup.eq_of_le_of_card_ge hXA (le_of_eq (by rw [hcardA, hcardX]))
  have hfix_u : ∀ ψ ∈ A, ψ ⟨u, hu⟩ = ⟨u, hu⟩ := by
    intro ψ hψ
    exact (hfixX ⟨u, hu⟩).2 (Subgroup.mem_zpowers u) ψ (hEq.symm ▸ hψ)
  have h1 : (⟨u, hu⟩ : ↥Bs) = 1 := hfixA ⟨u, hu⟩ hfix_u
  exact hu1 (Subtype.ext_iff.mp h1)

omit [Fact (Nat.Prime p)] in
private theorem ggF4Endpoint_G2_false
    (hp : p.Prime) (hBs : IsElemAbelian p Bs) {u : G} (hu : u ∈ Bs)
    (h4 : p ^ 4 ≤ Nat.card ↥Bs) {X : Subgroup (MulAut ↥Bs)}
    (hT : GGWeylOfType p CoxeterMatrix.G₂ X)
    (hfixX : ∀ b : ↥Bs, (∀ φ ∈ X, φ b = b) → (b : G) ∈ Subgroup.zpowers u) : False := by
  have hr := ggF4Orig_three_le_card hp hBs hu h4 hT hfixX
  rw [Fintype.card_fin] at hr
  omega

theorem ggF4_weylOfType_A3_or_B3
    (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs) (h4 : p ^ 4 ≤ Nat.card ↥Bs)
    (hNT : GGNoTransvection p Bs) {A : Subgroup (MulAut ↥Bs)}
    (hAind : ∀ φ ∈ A, φ ∈ ggInduced ⊤ Bs) {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥A}
    (hP : GGCoxeterPres p A M e) (hF4 : GGIsWeylMatrixF4 M)
    (hfixA : ∀ b : ↥Bs, (∀ ψ ∈ A, ψ b = b) → b = 1) {X : Subgroup (MulAut ↥Bs)} (hXA : X ≤ A)
    (hWX : GGWeylReflectionGroup p X) {u : G} (hu : u ∈ Bs) (hu1 : u ≠ 1)
    (hfixX : ∀ b : ↥Bs, (∀ φ ∈ X, φ b = b) ↔ (b : G) ∈ Subgroup.zpowers u) :
    GGWeylOfType p (CoxeterMatrix.A 3) X ∨ GGWeylOfType p (CoxeterMatrix.B 3) X := by
  obtain ⟨e', rfl⟩ := hF4
  let inst : Fintype ι := Fintype.ofEquiv (Fin 4) e'
  obtain ⟨R, hRs, hconv⟩ := ggF4Endpoint_setup hp2 hBs hNT hAind e' hP
  let cs := ggF4CoxeterSystem e' e
  have hW : GGWeylOfType p (CoxeterMatrix.F₄.reindex e') A := ⟨e, hP.2⟩
  have hcardA : Nat.card ↥A = 1152 :=
    ggF4Orig_card_weylOfType_F4 (GGWeylOfType.of_reindex (M := CoxeterMatrix.F₄) hW)
  have hdvdX : Nat.card ↥X ∣ 1152 := by
    have h1 := Subgroup.card_dvd_of_le hXA
    rwa [hcardA] at h1
  have hcard4 : Nat.card ↥Bs ≤ p ^ 4 := by
    have h := @SpJoinRefl.card_le_pow_of_weylOfType G _ _ p Bs ι inst (CoxeterMatrix.F₄.reindex e') A hW hfixA
    rwa [← @Fintype.card_congr (Fin 4) ι (by infer_instance) inst e', Fintype.card_fin] at h
  rcases ggF4Orig_type_cases hWX hdvdX with ⟨n, hn1, hn3, hT⟩ | ⟨n, hn2, hn4, hT⟩ | hT | hT | hT
  · have hr := ggF4Orig_three_le_card Fact.out hBs hu h4 hT (fun b => (hfixX b).1)
    rw [Fintype.card_fin] at hr
    obtain rfl : n = 3 := by omega
    exact Or.inl hT
  · have hr := ggF4Orig_three_le_card Fact.out hBs hu h4 hT (fun b => (hfixX b).1)
    rw [Fintype.card_fin] at hr
    by_cases hn : n = 3
    · subst hn
      exact Or.inr hT
    · obtain rfl : n = 4 := by omega
      exact (ggF4Endpoint_B4_false hp2 hBs hcard4 hXA R cs hRs hconv hu hu1 hfixX hT).elim
  · exact (ggF4Endpoint_D4_false hp2 hBs hcard4 hXA R cs hRs hconv hu hu1 hfixX hT).elim
  · exact (ggF4Endpoint_F4_false hcardA hfixA hXA hu hu1 hfixX hT).elim
  · exact (ggF4Endpoint_G2_false Fact.out hBs hu h4 hT (fun b => (hfixX b).1)).elim

theorem ggF4_exists_endpointRefl
    (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs) (h4 : p ^ 4 ≤ Nat.card ↥Bs)
    (hNT : GGNoTransvection p Bs) {A : Subgroup (MulAut ↥Bs)}
    (hAind : ∀ φ ∈ A, φ ∈ ggInduced ⊤ Bs) {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥A}
    (hP : GGCoxeterPres p A M e) (hF4 : GGIsWeylMatrixF4 M)
    (hfixA : ∀ b : ↥Bs, (∀ ψ ∈ A, ψ b = b) → b = 1) {X : Subgroup (MulAut ↥Bs)} (hXA : X ≤ A)
    (hWX : GGWeylReflectionGroup p X) {u : G} (hu : u ∈ Bs) (hu1 : u ≠ 1)
    (hfixX : ∀ b : ↥Bs, (∀ φ ∈ X, φ b = b) ↔ (b : G) ∈ Subgroup.zpowers u) :
    ∃ t ∈ A, GGIsReflection p t ∧ t ⟨u, hu⟩ = ⟨u, hu⟩⁻¹ ∧ (∀ φ ∈ X, φ * t = t * φ) ∧
      (Nat.card ↥X = 24 ∨ Nat.card ↥X = 48) := by
  obtain ⟨e', rfl⟩ := hF4
  obtain ⟨R, hRs, hconv⟩ := ggF4Endpoint_setup hp2 hBs hNT hAind e' hP
  let cs := ggF4CoxeterSystem e' e
  have hcardA : Nat.card ↥A = 1152 :=
    ggF4Orig_card_weylOfType_F4 (GGWeylOfType.of_reindex (M := CoxeterMatrix.F₄) ⟨e, hP.2⟩)
  have htype := ggF4_weylOfType_A3_or_B3 hp2 hBs h4 hNT hAind hP ⟨e', rfl⟩ hfixA hXA hWX hu hu1 hfixX
  rcases htype with hTA3 | hTB3
  · obtain ⟨a, eT, ha_def, haR, haH, harefl, hord⟩ :=
      ggF4Endpoint_hdata hXA R cs hRs hconv (CoxeterMatrix.A 3) hTA3
    have hgen := ggF4Endpoint_hgen hXA a ha_def
    have h01 : orderOf (a 0 * a 1) = 3 := by rw [hord 0 1]; decide
    have h02 : orderOf (a 0 * a 2) = 2 := by rw [hord 0 2]; decide
    have h12 : orderOf (a 1 * a 2) = 3 ∨ orderOf (a 1 * a 2) = 4 :=
      Or.inl (by rw [hord 1 2]; decide)
    obtain ⟨t, htA, htRefl, htu, hcommX⟩ :=
      ggF4Endpoint_exists_t hp2 hBs e' hP R hRs hu hu1 hfixX a haR harefl hgen h01 h02 h12
    have hcardX : Nat.card ↥X = 24 := by
      rw [ggWeylOfType_A_card hTA3]; norm_num
    exact ⟨t, htA, htRefl, htu, hcommX, Or.inl hcardX⟩
  · obtain ⟨a, eT, ha_def, haR, haH, harefl, hord⟩ :=
      ggF4Endpoint_hdata hXA R cs hRs hconv (CoxeterMatrix.B 3) hTB3
    have hgen := ggF4Endpoint_hgen hXA a ha_def
    have h01 : orderOf (a 0 * a 1) = 3 := by rw [hord 0 1]; decide
    have h02 : orderOf (a 0 * a 2) = 2 := by rw [hord 0 2]; decide
    have h12 : orderOf (a 1 * a 2) = 3 ∨ orderOf (a 1 * a 2) = 4 :=
      Or.inr (by rw [hord 1 2]; decide)
    obtain ⟨t, htA, htRefl, htu, hcommX⟩ :=
      ggF4Endpoint_exists_t hp2 hBs e' hP R hRs hu hu1 hfixX a haR harefl hgen h01 h02 h12
    have hcardX : Nat.card ↥X = 48 := by
      obtain ⟨eB, -⟩ := hTB3
      rw [← Nat.card_congr eB.toEquiv]
      have h : Nat.card (CoxeterMatrix.B 3).Group = 2 ^ 3 * (3).factorial :=
        le_antisymm (card_coxeterB_le 3) (SpFrame.card_coxeterB_ge 3 (by norm_num))
      norm_num at h
      exact h
    exact ⟨t, htA, htRefl, htu, hcommX, Or.inr hcardX⟩

omit [Finite G] in
private theorem ggF4Endpoint_centralizer_map {A : Subgroup (MulAut ↥Bs)} (x : ↥A) :
    (Subgroup.centralizer ({x} : Set ↥A)).map A.subtype =
      A ⊓ Subgroup.centralizer ({(x : MulAut ↥Bs)} : Set (MulAut ↥Bs)) := by
  ext y
  constructor
  · intro hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    have hz' : z * x = x * z := Subgroup.mem_centralizer_singleton_iff.mp hz
    rw [Subgroup.mem_inf]
    refine ⟨z.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    change (z : MulAut ↥Bs) * ↑x = ↑x * (z : MulAut ↥Bs)
    simpa only [Subgroup.coe_mul] using congrArg Subtype.val hz'
  · rintro hy
    rw [Subgroup.mem_inf] at hy
    obtain ⟨hyA, hy⟩ := hy
    have hy' : y * (x : MulAut ↥Bs) = (x : MulAut ↥Bs) * y :=
      Subgroup.mem_centralizer_singleton_iff.mp hy
    rw [Subgroup.mem_map]
    exact ⟨⟨y, hyA⟩, Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext hy'), rfl⟩

omit [Finite G] in
private theorem ggF4Endpoint_hgen_pullback {A : Subgroup (MulAut ↥Bs)} {κ : Type*}
    (S : Finset κ) {tL : ↥A} {t : κ → ↥A}
    (hgen : A ≤ (A ⊓ Subgroup.centralizer ({(tL : MulAut ↥Bs)} : Set (MulAut ↥Bs))) ⊔
      ⨆ i ∈ S, (A ⊓ Subgroup.centralizer ({(t i : MulAut ↥Bs)} : Set (MulAut ↥Bs)))) :
    Subgroup.centralizer ({tL} : Set ↥A) ⊔
        ⨆ i ∈ S, Subgroup.centralizer ({t i} : Set ↥A) = ⊤ := by
  have hmap : Subgroup.map A.subtype
      (Subgroup.centralizer ({tL} : Set ↥A) ⊔
        ⨆ i ∈ S, Subgroup.centralizer ({t i} : Set ↥A)) =
      (A ⊓ Subgroup.centralizer ({(tL : MulAut ↥Bs)} : Set (MulAut ↥Bs))) ⊔
        ⨆ i ∈ S, (A ⊓ Subgroup.centralizer ({(t i : MulAut ↥Bs)} : Set (MulAut ↥Bs))) := by
    rw [Subgroup.map_sup, Subgroup.map_iSup, ggF4Endpoint_centralizer_map tL]
    congr 1
    refine iSup_congr fun i => ?_
    rw [Subgroup.map_iSup]
    exact iSup_congr fun _ => ggF4Endpoint_centralizer_map (t i)
  have htop : (⊤ : Subgroup ↥A).map A.subtype = A := by
    rw [Subgroup.map_top, Subgroup.range_subtype]
  have hle : (⊤ : Subgroup ↥A) ≤
      Subgroup.centralizer ({tL} : Set ↥A) ⊔
        ⨆ i ∈ S, Subgroup.centralizer ({t i} : Set ↥A) := by
    refine (Subgroup.map_le_map_iff_of_injective (Subgroup.subtype_injective A)).1 ?_
    rw [htop, hmap]
    exact hgen
  exact top_le_iff.mp hle

omit [Finite G] in
private theorem ggF4Endpoint_hgen_amb {A : Subgroup (MulAut ↥Bs)} {κ : Type*} (S : Finset κ)
    {tL : MulAut ↥Bs} (tL' : ↥A) (hLval : (tL' : MulAut ↥Bs) = tL)
    {t : κ → MulAut ↥Bs} (t' : κ → ↥A) (ht'val : ∀ i ∈ S, (t' i : MulAut ↥Bs) = t i)
    (hgen : A ≤ (A ⊓ Subgroup.centralizer ({tL} : Set (MulAut ↥Bs))) ⊔
      ⨆ i ∈ S, (A ⊓ Subgroup.centralizer ({t i} : Set (MulAut ↥Bs)))) :
    A ≤ (A ⊓ Subgroup.centralizer ({(tL' : MulAut ↥Bs)} : Set (MulAut ↥Bs))) ⊔
      ⨆ i ∈ S, (A ⊓ Subgroup.centralizer ({(t' i : MulAut ↥Bs)} : Set (MulAut ↥Bs))) := by
  have h1 : (A ⊓ Subgroup.centralizer ({(tL' : MulAut ↥Bs)} : Set (MulAut ↥Bs))) =
      A ⊓ Subgroup.centralizer ({tL} : Set (MulAut ↥Bs)) := by rw [hLval]
  have h2 : (⨆ i ∈ S, (A ⊓ Subgroup.centralizer ({(t' i : MulAut ↥Bs)} :
      Set (MulAut ↥Bs)))) = ⨆ i ∈ S, (A ⊓ Subgroup.centralizer ({t i} :
      Set (MulAut ↥Bs))) := by
    refine iSup_congr fun i => iSup_congr fun hi => ?_
    rw [ht'val i hi]
  rw [h1, h2]
  exact hgen

omit [Finite G] in
private theorem ggF4Endpoint_hcomm' {A : Subgroup (MulAut ↥Bs)} {κ : Type*} (S : Finset κ)
    {tL : MulAut ↥Bs} (tL' : ↥A) (hLval : (tL' : MulAut ↥Bs) = tL)
    {t : κ → MulAut ↥Bs} (t' : κ → ↥A) (ht'val : ∀ i ∈ S, (t' i : MulAut ↥Bs) = t i)
    (hcomm : ∀ i ∈ S, ∀ j ∈ S, Commute tL (t i) → Commute tL (t j) → t i = t j) :
    ∀ i ∈ S, ∀ j ∈ S, Commute tL' (t' i) → Commute tL' (t' j) → t' i = t' j := by
  intro i hi j hj hci hcj
  apply Subtype.ext
  rw [ht'val i hi, ht'val j hj]
  refine hcomm i hi j hj ?_ ?_
  · have h := congrArg Subtype.val hci.eq
    simp only [Subgroup.coe_mul, hLval, ht'val i hi] at h
    exact h
  · have h := congrArg Subtype.val hcj.eq
    simp only [Subgroup.coe_mul, hLval, ht'val j hj] at h
    exact h

omit [Finite G] [Fact (Nat.Prime p)] in
private theorem ggF4Endpoint_hplane'
    {A : Subgroup (MulAut ↥Bs)} {κ : Type*} (S : Finset κ) {ι : Type} (e' : Fin 4 ≃ ι)
    {e : (CoxeterMatrix.F₄.reindex e').Group ≃* ↥A}
    (hP : GGCoxeterPres p A (CoxeterMatrix.F₄.reindex e') e) (R : F4Rep ↥A)
    (hRs : ∀ i, R.s i = (ggF4CoxeterSystem e' e).simple i)
    {tL tK : MulAut ↥Bs} (tL' : ↥A) (hLval : (tL' : MulAut ↥Bs) = tL)
    (hKA : tK ∈ A) {t : κ → MulAut ↥Bs} (t' : κ → ↥A)
    (ht'val : ∀ i ∈ S, (t' i : MulAut ↥Bs) = t i)
    (hplane : ∀ i ∈ S, ¬ Commute tL (t i) → ∀ s ∈ A, GGIsReflection p s → Commute s tL →
      Commute s (t i) → Commute s tK) :
    ∀ i ∈ S, ¬ Commute tL' (t' i) → ∀ s : ↥A, R.IsRefl s → Commute s tL' →
      Commute s (t' i) → Commute s ⟨tK, hKA⟩ := by
  intro i hi hni s hs hsL hsI
  have hni' : ¬ Commute tL (t i) := by
    intro hc
    refine hni (Subtype.ext ?_)
    simpa only [Subgroup.coe_mul, hLval, ht'val i hi] using hc.eq
  have hsL' : Commute (s : MulAut ↥Bs) tL := by
    have h := congrArg Subtype.val hsL.eq
    simp only [Subgroup.coe_mul, hLval] at h
    exact h
  have hsI' : Commute (s : MulAut ↥Bs) (t i) := by
    have h := congrArg Subtype.val hsI.eq
    simp only [Subgroup.coe_mul, ht'val i hi] at h
    exact h
  have hs' := hplane i hi hni' (s : MulAut ↥Bs) s.2
    (ggF4Endpoint_isRefl_of_R e' hP R hRs hs) hsL' hsI'
  exact Subtype.ext hs'.eq

theorem ggF4_exists_conj_of_cover
    (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs) (hNT : GGNoTransvection p Bs)
    {A : Subgroup (MulAut ↥Bs)} (hAind : ∀ φ ∈ A, φ ∈ ggInduced ⊤ Bs) {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥A} (hP : GGCoxeterPres p A M e)
    (hF4 : GGIsWeylMatrixF4 M) {κ : Type*} (S : Finset κ) {tL tK : MulAut ↥Bs}
    {t : κ → MulAut ↥Bs} (hLA : tL ∈ A) (hKA : tK ∈ A) (htA : ∀ i ∈ S, t i ∈ A)
    (hL : GGIsReflection p tL) (hK : GGIsReflection p tK)
    (ht : ∀ i ∈ S, GGIsReflection p (t i))
    (hcomm : ∀ i ∈ S, ∀ j ∈ S, Commute tL (t i) → Commute tL (t j) → t i = t j)
    (hplane : ∀ i ∈ S, ¬ Commute tL (t i) → ∀ s ∈ A, GGIsReflection p s → Commute s tL →
      Commute s (t i) → Commute s tK)
    (hgen : A ≤ (A ⊓ Subgroup.centralizer ({tL} : Set (MulAut ↥Bs))) ⊔
      ⨆ i ∈ S, (A ⊓ Subgroup.centralizer ({t i} : Set (MulAut ↥Bs)))) :
    ∃ w ∈ A, w * tK * w⁻¹ = tL ∨ ∃ i ∈ S, w * tK * w⁻¹ = t i := by
  classical
  obtain ⟨e', rfl⟩ := hF4
  obtain ⟨R, hRs, hconv⟩ := ggF4Endpoint_setup hp2 hBs hNT hAind e' hP
  let tL' : ↥A := ⟨tL, hLA⟩
  let tK' : ↥A := ⟨tK, hKA⟩
  let t' : κ → ↥A := fun i => if h : t i ∈ A then ⟨t i, h⟩ else 1
  have hLval : (tL' : MulAut ↥Bs) = tL := rfl
  have ht'val : ∀ i ∈ S, (t' i : MulAut ↥Bs) = t i := by
    intro i hi
    rw [show t' i = ⟨t i, htA i hi⟩ from dif_pos (htA i hi)]
  have hL' : R.IsRefl tL' := (F4Rep.isRefl_iff hRs).2 (hconv tL hLA hL)
  have hK' : R.IsRefl tK' := (F4Rep.isRefl_iff hRs).2 (hconv tK hKA hK)
  have ht' : ∀ i ∈ S, R.IsRefl (t' i) := by
    intro i hi
    rw [show t' i = ⟨t i, htA i hi⟩ from dif_pos (htA i hi)]
    exact (F4Rep.isRefl_iff hRs).2 (hconv (t i) (htA i hi) (ht i hi))
  have hcomm' := ggF4Endpoint_hcomm' S tL' hLval t' ht'val hcomm
  have hplane' :=
    ggF4Endpoint_hplane' S e' hP R hRs tL' hLval hKA t' ht'val hplane
  have hgen' := ggF4Endpoint_hgen_pullback S
    (ggF4Endpoint_hgen_amb S tL' hLval t' ht'val hgen)
  obtain ⟨w, hw | ⟨i, hi, hwi⟩⟩ := R.exists_conj_of_cover S hL' hK' ht' hcomm' hplane' hgen'
  · exact ⟨(w : MulAut ↥Bs), w.2, Or.inl (by simpa using congrArg Subtype.val hw)⟩
  · have hwi' : (w : MulAut ↥Bs) * tK * (w : MulAut ↥Bs)⁻¹ = t i := by
      simpa [t', htA i hi] using congrArg Subtype.val hwi
    exact ⟨(w : MulAut ↥Bs), w.2, Or.inr ⟨i, hi, hwi'⟩⟩

theorem ggF4_exists_conj_of_not_conj
    (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs) (hNT : GGNoTransvection p Bs)
    {A : Subgroup (MulAut ↥Bs)} (hAind : ∀ φ ∈ A, φ ∈ ggInduced ⊤ Bs) {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥A} (hP : GGCoxeterPres p A M e)
    (hF4 : GGIsWeylMatrixF4 M) {tL tK tA : MulAut ↥Bs} (hLA : tL ∈ A) (hKA : tK ∈ A)
    (hAA : tA ∈ A) (hL : GGIsReflection p tL) (hK : GGIsReflection p tK)
    (hA : GGIsReflection p tA) (hnot : ∀ w ∈ A, w * tA * w⁻¹ ≠ tL) :
    ∃ w ∈ A, w * tK * w⁻¹ = tL ∨ w * tK * w⁻¹ = tA := by
  obtain ⟨e', rfl⟩ := hF4
  obtain ⟨R, hRs, hconv⟩ := ggF4Endpoint_setup hp2 hBs hNT hAind e' hP
  have hL' : R.IsRefl ⟨tL, hLA⟩ := (F4Rep.isRefl_iff hRs).2 (hconv tL hLA hL)
  have hK' : R.IsRefl ⟨tK, hKA⟩ := (F4Rep.isRefl_iff hRs).2 (hconv tK hKA hK)
  have hA' : R.IsRefl ⟨tA, hAA⟩ := (F4Rep.isRefl_iff hRs).2 (hconv tA hAA hA)
  have hAL : R.cls ⟨tA, hAA⟩ ≠ R.cls ⟨tL, hLA⟩ := by
    intro h
    obtain ⟨g, hg⟩ := R.exists_conj_of_cls_eq hA' hL' h
    exact hnot g g.2 (by simpa using congrArg Subtype.val hg)
  by_cases hKL : R.cls ⟨tK, hKA⟩ = R.cls ⟨tL, hLA⟩
  · obtain ⟨g, hg⟩ := R.exists_conj_of_cls_eq hK' hL' hKL
    exact ⟨g, g.2, Or.inl (by simpa using congrArg Subtype.val hg)⟩
  · have hKA' : R.cls ⟨tK, hKA⟩ = R.cls ⟨tA, hAA⟩ := by
      rcases R.cls_eq_one_or_two hK' with h1 | h1 <;>
        rcases R.cls_eq_one_or_two hL' with h2 | h2 <;>
          rcases R.cls_eq_one_or_two hA' with h3 | h3 <;> simp_all
    obtain ⟨g, hg⟩ := R.exists_conj_of_cls_eq hK' hA' hKA'
    exact ⟨g, g.2, Or.inr (by simpa using congrArg Subtype.val hg)⟩

theorem ggF4_card_inf_centralizer_le
    (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs) (hNT : GGNoTransvection p Bs)
    {A : Subgroup (MulAut ↥Bs)} (hAind : ∀ φ ∈ A, φ ∈ ggInduced ⊤ Bs) {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥A} (hP : GGCoxeterPres p A M e)
    (hF4 : GGIsWeylMatrixF4 M) {t : MulAut ↥Bs} (htA : t ∈ A) (ht : GGIsReflection p t) :
    Nat.card ↥(A ⊓ Subgroup.centralizer ({t} : Set (MulAut ↥Bs))) ≤ 96 := by
  obtain ⟨e', rfl⟩ := hF4
  obtain ⟨R, hRs, hconv⟩ := ggF4Endpoint_setup hp2 hBs hNT hAind e' hP
  have hcardA : Nat.card ↥A = 1152 :=
    ggF4Orig_card_weylOfType_F4 (GGWeylOfType.of_reindex (M := CoxeterMatrix.F₄) ⟨e, hP.2⟩)
  have hR : R.IsRefl ⟨t, htA⟩ := (F4Rep.isRefl_iff hRs).2 (hconv t htA ht)
  have hcard := Subgroup.card_map_of_injective (K := Subgroup.centralizer ({⟨t, htA⟩} :
    Set ↥A)) (Subgroup.subtype_injective A)
  rw [ggF4Endpoint_centralizer_map (A := A) ⟨t, htA⟩] at hcard
  rw [hcard]
  exact R.card_centralizer_le hcardA hR

end CFSG.StandardType

end
