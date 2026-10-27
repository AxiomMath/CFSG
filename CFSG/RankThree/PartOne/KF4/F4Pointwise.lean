module

public import CFSG.RankThree.PartOne.KF4.F4Traces
public import CFSG.RankThree.PartOne.KE.CoreInner
public import CFSG.RankThree.PartOne.KE.CommutatorFactor
public import CFSG.RankThree.PartOne.KE.PlaneOdd
public import CFSG.RankThree.PartOne.KF4.CoreStep
public import CFSG.LieType.Chevalley.OddF4CosetDescent

public noncomputable section

namespace CFSG.RankThree.PartOne.KF4

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.Chevalley CFSG.LieType.Chevalley
open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.LocalRank CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.RankThree.PartOne.KE


theorem ringEquiv_eq_one_of_fixes_F4_root_SL2_traces {K : Type} [Field K] [Finite K]
    (M : Type) [Field M] [Algebra K M] (i : Fin Tag.F4.rank)
    (hi : (i = f4Index 0 ∨ i = f4Index 1) ∨ (i = f4Index 2 ∨ i = f4Index 3))
    (A : GL (Fin 2) M) (h : ModGL Tag.F4 M) (σ : K ≃+* K)
    (hσ : ∀ B : SL2 K, ∃ y : K, σ y = y ∧ algebraMap K M y = LinearMap.trace M
      (RootModule Tag.F4 M)
      ((h * simpleRootSL2 Tag.F4 M i (conjGL A (Matrix.SpecialLinearGroup.map (algebraMap K M) B)) *
        h⁻¹ : ModGL Tag.F4 M) : Module.End M (RootModule Tag.F4 M))) :
    σ = 1 := by
  have hcl : Subfield.closure {x : M | ∃ B : SL2 K, x = LinearMap.trace M (RootModule Tag.F4 M)
      ((h * simpleRootSL2 Tag.F4 M i (conjGL A (Matrix.SpecialLinearGroup.map (algebraMap K M) B)) *
        h⁻¹ : ModGL Tag.F4 M) : Module.End M (RootModule Tag.F4 M))} =
      (algebraMap K M).fieldRange := by
    rcases hi with hl | hs
    · exact closure_trace_F4_long i hl K M A h
    · exact closure_trace_F4_short i hs K M A h
  have hS : {x : M | ∃ B : SL2 K, x = LinearMap.trace M (RootModule Tag.F4 M)
      ((h * simpleRootSL2 Tag.F4 M i (conjGL A (Matrix.SpecialLinearGroup.map (algebraMap K M) B)) *
        h⁻¹ : ModGL Tag.F4 M) : Module.End M (RootModule Tag.F4 M))} ⊆
      (((RingHom.eqLocusField σ.toRingHom (RingHom.id K)).map (algebraMap K M) :
        Subfield M) : Set M) := by
    rintro _ ⟨B, rfl⟩
    obtain ⟨y, hy, hyB⟩ := hσ B
    exact ⟨y, hy, hyB⟩
  have hle := Subfield.closure_le.2 hS
  rw [hcl] at hle
  refine RingEquiv.ext fun c => ?_
  obtain ⟨y, hy, hyc⟩ := hle ⟨c, rfl⟩
  have hyc' : y = c := (algebraMap K M).injective hyc
  subst hyc'
  exact hy

theorem trace_apply_of_F4_expression {K : Type} [Field K] (η : MulAut (adjointGroup Tag.F4 K))
    (g : adjointGroup Tag.F4 K) (σ : K ≃+* K)
    (hexpr : ∀ x : adjointGroup Tag.F4 K, (η x : ModGL Tag.F4 K) = (g : ModGL Tag.F4 K) *
      Units.map (entrywiseHom σ.toRingHom) (x : ModGL Tag.F4 K) * (g : ModGL Tag.F4 K)⁻¹)
    (x : adjointGroup Tag.F4 K) :
    LinearMap.trace K (RootModule Tag.F4 K)
        ((η x : ModGL Tag.F4 K) : Module.End K (RootModule Tag.F4 K)) =
      σ (LinearMap.trace K (RootModule Tag.F4 K)
        ((x : ModGL Tag.F4 K) : Module.End K (RootModule Tag.F4 K))) := by
  rw [hexpr x, Units.val_mul, Units.val_mul, LinearMap.trace_conj,
    units_map_entrywiseHom_eq_baseChangeGL, trace_baseChangeGL]
  rfl

theorem F4_descended_root_SL2_pointwise_inner (K : Type) [Field K] [Finite K] {ℓ f : ℕ}
    (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    (M : Type) [Field M] [Algebra K M] (i : Fin Tag.F4.rank)
    (hi : (i = f4Index 0 ∨ i = f4Index 1) ∨ (i = f4Index 2 ∨ i = f4Index 3))
    (A : GL (Fin 2) M) (h : ModGL Tag.F4 M)
    (hU : ∀ B : SL2 K, h * simpleRootSL2 Tag.F4 M i (conjGL A
        (Matrix.SpecialLinearGroup.map (algebraMap K M) B)) * h⁻¹ ∈
          (adjointGroup Tag.F4 K).map (baseChangeGL (algebraMap K M)))
    (Z : Subgroup (MulAut (adjointGroup Tag.F4 K)))
    (hZ : ∀ η ∈ Z, ∀ (u : adjointGroup Tag.F4 K) (B : SL2 K),
      baseChangeGL (algebraMap K M) (u : ModGL Tag.F4 K) =
        h * simpleRootSL2 Tag.F4 M i (conjGL A (Matrix.SpecialLinearGroup.map (algebraMap K M) B)) *
          h⁻¹ → η u = u) :
    ∀ η ∈ Z, η ∈ (MulAut.conj : adjointGroup Tag.F4 K →* MulAut (adjointGroup Tag.F4 K)).range := by
  intro η hη
  obtain ⟨huniq, Θ, hΘ, -, hker, -⟩ := odd_F4_and_nonexceptional_G2_automorphism_normal_form hℓ
    hℓ2 hf K hK .F4 (Or.inl rfl)
  obtain ⟨⟨g, σ⟩, hgσ, -⟩ := huniq η
  have hexpr : ∀ x : adjointGroup Tag.F4 K, (η x : ModGL Tag.F4 K) = (g : ModGL Tag.F4 K) *
      Units.map (entrywiseHom σ.toRingHom) (x : ModGL Tag.F4 K) * (g : ModGL Tag.F4 K)⁻¹ := hgσ
  have hΘη : Θ η = σ := hΘ η g σ hexpr
  have hσ : σ = 1 := by
    refine ringEquiv_eq_one_of_fixes_F4_root_SL2_traces M i hi A h σ fun B => ?_
    obtain ⟨y, hyC, hy⟩ := hU B
    have hfix : η ⟨y, hyC⟩ = ⟨y, hyC⟩ := hZ η hη ⟨y, hyC⟩ B hy
    have h1 := trace_apply_of_F4_expression η g σ hexpr ⟨y, hyC⟩
    rw [hfix] at h1
    refine ⟨LinearMap.trace K (RootModule Tag.F4 K)
      ((y : ModGL Tag.F4 K) : Module.End K (RootModule Tag.F4 K)), h1.symm, ?_⟩
    rw [← hy, trace_baseChangeGL]
  have : η ∈ Θ.ker := by
    rw [MonoidHom.mem_ker, hΘη, hσ]
  rwa [hker] at this

theorem conjGL_one' {M : Type*} [Field M] (Z : SL2 M) : conjGL (1 : GL (Fin 2) M) Z = Z :=
  Subtype.ext (by simp [conjGL])

theorem f4_core_le_range_conj (K : Type) [Field K] [Finite K] {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (M : Type) [Field M] [Algebra K M]
    {p : ℕ} (hp : p.Prime) {B : Subgroup (MulAut (adjointGroup .F4 K))}
    (hB : (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range ≤ B)
    {x : adjointGroup .F4 K}
    (hq : CFSG.IsQuasisimple (⁅Subgroup.centralizer ({x} : Set (adjointGroup .F4 K)),
      Subgroup.centralizer ({x} : Set (adjointGroup .F4 K))⁆ : Subgroup (adjointGroup .F4 K)))
    (i : Fin Tag.F4.rank) (hi : (i = f4Index 0 ∨ i = f4Index 1) ∨ (i = f4Index 2 ∨ i = f4Index 3))
    (A : GL (Fin 2) M) (h : ModGL .F4 M)
    (hU : ∀ Y : SL2 K, h * simpleRootSL2 .F4 M i (conjGL A
        (Matrix.SpecialLinearGroup.map (algebraMap K M) Y)) * h⁻¹ ∈
          (adjointGroup .F4 K).map (baseChangeGL (algebraMap K M)))
    (hmem : ∀ (u : adjointGroup .F4 K) (Y : SL2 K),
      baseChangeGL (algebraMap K M) (u : ModGL .F4 K) =
        h * simpleRootSL2 .F4 M i (conjGL A
          (Matrix.SpecialLinearGroup.map (algebraMap K M) Y)) * h⁻¹ →
        u ∈ (⁅Subgroup.centralizer ({x} : Set (adjointGroup .F4 K)),
          Subgroup.centralizer ({x} : Set (adjointGroup .F4 K))⁆ :
            Subgroup (adjointGroup .F4 K))) :
    inSubgroup (aschbacherSolvableCore p)
      (B ⊓ Subgroup.centralizer ({(MulAut.conj x : MulAut (adjointGroup .F4 K))} :
        Set (MulAut (adjointGroup .F4 K)))) ≤
        (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range := by
  refine core_le_range_conj_of_quasisimple hp center_adjointGroup_eq_bot hB hq fun η hη => ?_
  let Z : Subgroup (MulAut (adjointGroup .F4 K)) :=
    { carrier := {η | ∀ d ∈ (⁅Subgroup.centralizer ({x} : Set (adjointGroup .F4 K)),
        Subgroup.centralizer ({x} : Set (adjointGroup .F4 K))⁆ :
          Subgroup (adjointGroup .F4 K)), η d = d}
      mul_mem' := fun {a b} ha hb d hd => by
        rw [MulAut.mul_apply, hb d hd, ha d hd]
      one_mem' := fun d _ => rfl
      inv_mem' := fun {a} ha d hd => by
        have := ha d hd
        calc a⁻¹ d = a⁻¹ (a d) := by rw [this]
          _ = d := by rw [← MulAut.mul_apply, inv_mul_cancel]; rfl }
  have hη' : η ∈ Z := hη
  exact F4_descended_root_SL2_pointwise_inner K hℓ hℓ2 hf hK M i hi A h hU Z
    (fun η' hη'Z u Y hu => hη'Z u (hmem u Y hu)) η hη'

theorem f4_core_le_range_conj_of_embedding (K : Type) [Field K] [Finite K] {ℓ f : ℕ}
    (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (L : Type) [Field L]
    [Algebra K L] {p : ℕ} (hp : p.Prime) {B : Subgroup (MulAut (adjointGroup .F4 K))}
    (hB : (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range ≤ B)
    {x : adjointGroup .F4 K} (c : adjointGroup .F4 K) (g0 : ModGL .F4 L)
    (ψ : Subgroup.centralizer ({x} : Set (adjointGroup .F4 K)) →* ModGL .F4 L)
    (hψinj : Function.Injective ψ)
    (hψ : ∀ y, ψ y = g0⁻¹ * adjEmb .F4 K L (c * (y : adjointGroup .F4 K) * c⁻¹) * g0)
    {Pt : Subgroup (ModGL .F4 L)} (hPq : CFSG.IsQuasisimple Pt) (hcomm : ⁅ψ.range, ψ.range⁆ = Pt)
    (i : Fin Tag.F4.rank) (hi : (i = f4Index 0 ∨ i = f4Index 1) ∨ (i = f4Index 2 ∨ i = f4Index 3))
    (h₀ : ModGL .F4 L)
    (hh₀ : ∀ Y : SL2 K, h₀ * simpleRootSL2 .F4 L i
      (Matrix.SpecialLinearGroup.map (algebraMap K L) Y) * h₀⁻¹ ∈ Pt) :
    inSubgroup (aschbacherSolvableCore p)
      (B ⊓ Subgroup.centralizer ({(MulAut.conj x : MulAut (adjointGroup .F4 K))} :
        Set (MulAut (adjointGroup .F4 K)))) ≤
        (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range := by
  obtain ⟨hq, h2, h1⟩ := isQuasisimple_commutator_of_embedding ψ hψinj hPq hcomm
  set h'' : ModGL .F4 L := (adjEmb .F4 K L c)⁻¹ * g0 * h₀ with hh''
  have hKey : ∀ Y : SL2 K, ∃ y ∈ (⁅Subgroup.centralizer ({x} : Set (adjointGroup .F4 K)),
      Subgroup.centralizer ({x} : Set (adjointGroup .F4 K))⁆ : Subgroup (adjointGroup .F4 K)),
        adjEmb .F4 K L y = h'' * simpleRootSL2 .F4 L i
          (Matrix.SpecialLinearGroup.map (algebraMap K L) Y) * h''⁻¹ := by
    intro Y
    have hmem := hh₀ Y
    rw [← h2] at hmem
    obtain ⟨y', hy', hy'ψ⟩ := hmem
    refine ⟨(y' : adjointGroup .F4 K), ?_, ?_⟩
    · rw [← h1]
      exact ⟨y', hy', rfl⟩
    · have h3 := hψ y'
      rw [hy'ψ] at h3
      have h4 : adjEmb .F4 K L (c * (y' : adjointGroup .F4 K) * c⁻¹) =
          g0 * (h₀ * simpleRootSL2 .F4 L i (Matrix.SpecialLinearGroup.map (algebraMap K L) Y) *
            h₀⁻¹) * g0⁻¹ := by
        rw [h3]
        group
      rw [map_mul, map_mul, map_inv] at h4
      rw [hh'']
      calc adjEmb .F4 K L (y' : adjointGroup .F4 K)
          = (adjEmb .F4 K L c)⁻¹ * (adjEmb .F4 K L c * adjEmb .F4 K L (y' : adjointGroup .F4 K) *
              (adjEmb .F4 K L c)⁻¹) * adjEmb .F4 K L c := by group
        _ = _ := by rw [h4]; group
  refine f4_core_le_range_conj K hℓ hℓ2 hf hK L hp hB hq i hi 1 h'' (fun Y => ?_)
    (fun u Y hu => ?_)
  · obtain ⟨y, -, hy⟩ := hKey Y
    rw [conjGL_one', ← hy]
    exact ⟨(y : ModGL .F4 K), y.2, rfl⟩
  · obtain ⟨y, hyD, hy⟩ := hKey Y
    rw [conjGL_one', ← hy] at hu
    have hu' : adjEmb .F4 K L u = adjEmb .F4 K L y := by rw [adjEmb_apply, hu]
    rw [adjEmb_injective hu']
    exact hyD

theorem f4_odd_core_step (K : Type) [Field K] [Finite K] {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (L : Type)
    [Field L] [Algebra K L] : F4CoreStep K p L := by
  intro B hB x c g0 _ ψ hψinj hψ Pt hPq hcomm i hi h₀ _ hh₀ hsolv
  have hle := f4_core_le_range_conj_of_embedding K hℓ hℓ2 hf hK L hp hB c g0 ψ hψinj hψ hPq hcomm
    i hi h₀ hh₀
  have hsx := odd_card_inf_range_of_solvable (B := B) hp center_adjointGroup_eq_bot hB hsolv
  rwa [inf_eq_left.2 hle] at hsx

end CFSG.RankThree.PartOne.KF4
