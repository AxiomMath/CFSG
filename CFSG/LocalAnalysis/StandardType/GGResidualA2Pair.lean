module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.CompactA2Pair
public import CFSG.LocalAnalysis.StandardType.GGOrthFrameTransport
public import CFSG.LocalAnalysis.StandardType.GGFixedTwoKernelTransport
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerSUBasic
public import CFSG.RankThree.PartOne.KE.E8TwoA2Family
public import CFSG.LocalAnalysis.StandardType.GGFinModelIndex
public import CFSG.LocalAnalysis.StandardType.GGFamCentralizerTwoPower
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSAPairAux2
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRankOneConj

public section

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE8F CFSG.RankThree.PartOne.CTP
  CFSG.LieType.Universal.Unitary CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Phan
  CFSG.Open CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.StandardType.CompactA2Pair
open Matrix
open scoped MatrixGroups
namespace CFSG.StandardType

theorem ggRankOneIn_map_of_central_odd_kernel
    {G : Type} {V : Type*} [Group G] [Finite G] [Group V]
    (X Bs : Subgroup G) (hBN : Bs ≤ Subgroup.normalizer (X : Set G))
    (π : ↥X →* V) (hπ : π.ker ≤ Subgroup.center ↥X)
    (hodd : Odd (Nat.card π.ker)) (β : ↥Bs →* MulAut V)
    (hcompat : ∀ b x, π (ggGamma X hBN b x) = β b (π x)) (r : MulAut ↥Bs) :
    ((ggRankOneIn X Bs r).subgroupOf X).map π =
      ggOTwoPrime (π.range ⊓ ⨅ b : ↥(MonoidHom.eqLocus
        (r : ↥Bs →* ↥Bs) (MonoidHom.id ↥Bs)),
        MonoidHom.eqLocus (β (b : Bs)).toMonoidHom (MonoidHom.id V)) := by
  let Hr := MonoidHom.eqLocus (r : ↥Bs →* ↥Bs) (MonoidHom.id ↥Bs)
  let α : ↥Hr → MulAut ↥X := fun b => ggGamma X hBN (b : Bs)
  have hC : (X ⊓ Subgroup.centralizer (ggHyperplane Bs r : Set G)).subgroupOf X =
      ⊤ ⊓ ⨅ b : ↥Hr, MonoidHom.eqLocus (α b).toMonoidHom (MonoidHom.id ↥X) := by
    ext x
    change ((x : G) ∈ X ∧ (x : G) ∈ Subgroup.centralizer (ggHyperplane Bs r : Set G)) ↔
      x ∈ (⊤ : Subgroup ↥X) ⊓ ⨅ b : ↥Hr,
        MonoidHom.eqLocus (α b).toMonoidHom (MonoidHom.id ↥X)
    constructor
    · intro hx
      refine ⟨Subgroup.mem_top _, Subgroup.mem_iInf.mpr fun b => ?_⟩
      change ggGamma X hBN (b : Bs) x = x
      apply Subtype.ext
      rw [ggGamma_coe]
      have hb : ((b : Bs) : G) ∈ ggHyperplane Bs r := ⟨b, b.2, rfl⟩
      rw [Subgroup.mem_centralizer_iff.mp hx.2 _ hb, mul_inv_cancel_right]
    · intro hx
      refine ⟨x.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
      rintro _ ⟨b, hb, rfl⟩
      have hfix := Subgroup.mem_iInf.mp hx.2 (⟨b, hb⟩ : Hr)
      change ggGamma X hBN b x = x at hfix
      have hfixG := congrArg Subtype.val hfix
      rw [ggGamma_coe] at hfixG
      exact (mul_inv_eq_iff_eq_mul.mp hfixG)
  have hR : (ggRankOneIn X Bs r).subgroupOf X =
      ggOTwoPrime ((X ⊓ Subgroup.centralizer (ggHyperplane Bs r : Set G)).subgroupOf X) := by
    apply Subgroup.map_injective X.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le
        (show ggRankOneIn X Bs r ≤ X from (ggOTwoPrime_le _).trans inf_le_left),
      ggOTwoPrime_map_of_injective X.subtype X.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le inf_le_left]
    rfl
  rw [hR, hC]
  simpa only [← MonoidHom.range_eq_map] using
    ggOTwoPrime_map_fixedFamily_of_central_odd_kernel π hπ hodd ⊤ α
      (fun b : ↥Hr => β (b : Bs)) (fun b x => hcompat (b : Bs) x)

end CFSG.StandardType

namespace CFSG.StandardType.ResidualA2Pair
section OrthogonalFamilies

theorem commutation_of_orthogonal_families
    {τ : Tag} {L : Type} [Field L] [CharP L 2]
    [Algebra (ZMod 2) L] [Algebra.IsAlgebraic (ZMod 2) L]
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {I₀ I₁ : Type*} [Finite I₀] [Finite I₁]
    (a₀ : I₀ → Fin τ.rank → Lˣ) (a₁ : I₁ → Fin τ.rank → Lˣ)
    (ha₀ : ∀ i, ∃ k : ℕ, a₀ i ^ (p ^ k) = 1)
    (ha₁ : ∀ i, ∃ k : ℕ, a₁ i ^ (p ^ k) = 1)
    (Y : Subgroup (ModGL τ L)) (hY : Y ≤ adjointGroup τ L)
    (horth : ∀ α ∈ famKernel (Set.range a₀), ∀ β ∈ famKernel (Set.range a₁),
      α ⬝ᵥ (τ.symmetrizedCartan *ᵥ β) = 0) :
    ∀ x ∈ ggOTwoPrime (Y ⊓ Subgroup.centralizer (Set.range fun i => rootDiagUnit τ (a₀ i))),
      ∀ y ∈ ggOTwoPrime (Y ⊓ Subgroup.centralizer (Set.range fun i => rootDiagUnit τ (a₁ i))),
        x * y = y * x := by
  intro x hx y hy
  exact CFSG.RankThree.PartOne.KE.rootSpan_commute_of_orth hτ
    (fun _ h => h.1) (fun _ h => h.1) horth x
    (LayerSixE.oTwoPrime_famCentralizer_le_rootSpan_of_algebraic hp hp2 a₀ ha₀ Y hY hx).1 y
    (LayerSixE.oTwoPrime_famCentralizer_le_rootSpan_of_algebraic hp hp2 a₁ ha₁ Y hY hy).1

theorem commutation_of_orthogonal_families_normalizer_action
    {τ : Tag} {L : Type} [Field L] [CharP L 2]
    [Algebra (ZMod 2) L] [Algebra.IsAlgebraic (ZMod 2) L]
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {I₀ I₁ : Type*} [Finite I₀] [Finite I₁]
    (a₀ : I₀ → Fin τ.rank → Lˣ) (a₁ : I₁ → Fin τ.rank → Lˣ)
    (ha₀ : ∀ i, ∃ k : ℕ, a₀ i ^ (p ^ k) = 1)
    (ha₁ : ∀ i, ∃ k : ℕ, a₁ i ^ (p ^ k) = 1)
    (Y : Subgroup (ModGL τ L)) (hY : Y ≤ adjointGroup τ L)
    (horth : ∀ α ∈ famKernel (Set.range a₀), ∀ β ∈ famKernel (Set.range a₁),
      α ⬝ᵥ (τ.symmetrizedCartan *ᵥ β) = 0)
    {G A : Type} [Group G] [Group A]
    (ψ : ↥Y →* G) (hψinj : Function.Injective ψ)
    (η : A →* G) (β : A →* ModGL τ L)
    (hpres : ∀ (a : A) (y : ↥Y), β a * (y : ModGL τ L) * (β a)⁻¹ ∈ Y)
    (hcompat : ∀ (a : A) (y : ↥Y),
      ψ ⟨β a * (y : ModGL τ L) * (β a)⁻¹, hpres a y⟩ = η a * ψ y * (η a)⁻¹)
    (H₀ H₁ : Subgroup A)
    (hH₀ : Subgroup.closure (Set.range fun i => rootDiagUnit τ (a₀ i)) = H₀.map β)
    (hH₁ : Subgroup.closure (Set.range fun i => rootDiagUnit τ (a₁ i)) = H₁.map β) :
    ∀ x ∈ ggOTwoPrime (ψ.range ⊓ Subgroup.centralizer (H₀.map η : Set G)),
      ∀ y ∈ ggOTwoPrime (ψ.range ⊓ Subgroup.centralizer (H₁.map η : Set G)), x * y = y * x := by
  have h0 := map_oTwoPrime_centralizer_of_normalizer_action ψ hψinj η β hpres hcompat H₀
  have h1 := map_oTwoPrime_centralizer_of_normalizer_action ψ hψinj η β hpres hcompat H₁
  rw [← hH₀, Subgroup.centralizer_closure] at h0
  rw [← hH₁, Subgroup.centralizer_closure] at h1
  intro x hx y hy
  rw [← h0] at hx
  rw [← h1] at hy
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
  obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hy
  have hcomm : (u : ModGL τ L) * (v : ModGL τ L) = (v : ModGL τ L) * (u : ModGL τ L) :=
    commutation_of_orthogonal_families hτ hp hp2 a₀ a₁ ha₀ ha₁ Y hY horth _ hu _ hv
  have hcommY : u * v = v * u := Subtype.ext hcomm
  simpa only [map_mul] using congrArg ψ hcommY

theorem commutation_of_orthogonal_families_original_member
    {G : Type} [Group G] {X Bs : Subgroup G}
    {τ : Tag} {L : Type} [Field L] [CharP L 2]
    [Algebra (ZMod 2) L] [Algebra.IsAlgebraic (ZMod 2) L]
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {I₀ I₁ : Type*} [Finite I₀] [Finite I₁]
    (a₀ : I₀ → Fin τ.rank → Lˣ) (a₁ : I₁ → Fin τ.rank → Lˣ)
    (ha₀ : ∀ i, ∃ k : ℕ, a₀ i ^ (p ^ k) = 1)
    (ha₁ : ∀ i, ∃ k : ℕ, a₁ i ^ (p ^ k) = 1)
    (Y : Subgroup (ModGL τ L)) (hY : Y ≤ adjointGroup τ L)
    (horth : ∀ α ∈ famKernel (Set.range a₀), ∀ β ∈ famKernel (Set.range a₁),
      α ⬝ᵥ (τ.symmetrizedCartan *ᵥ β) = 0)
    (ψ : ↥Y →* G) (hψinj : Function.Injective ψ) (hX : ψ.range = X)
    (β : ↥Bs →* ModGL τ L)
    (hpres : ∀ (b : ↥Bs) (y : ↥Y), β b * (y : ModGL τ L) * (β b)⁻¹ ∈ Y)
    (hcompat : ∀ (b : ↥Bs) (y : ↥Y),
      ψ ⟨β b * (y : ModGL τ L) * (β b)⁻¹, hpres b y⟩ = (b : G) * ψ y * (b : G)⁻¹)
    (r s : MulAut ↥Bs)
    (hH₀ : ∀ z : ModGL τ L,
      z ∈ Subgroup.closure (Set.range fun i => rootDiagUnit τ (a₀ i)) ↔
        ∃ b : ↥Bs, r b = b ∧ β b = z)
    (hH₁ : ∀ z : ModGL τ L,
      z ∈ Subgroup.closure (Set.range fun i => rootDiagUnit τ (a₁ i)) ↔
        ∃ b : ↥Bs, s b = b ∧ β b = z) :
    ∀ x ∈ ggRankOneIn X Bs r, ∀ y ∈ ggRankOneIn X Bs s, x * y = y * x := by
  let Hr : Subgroup ↥Bs := (r : ↥Bs →* ↥Bs).eqLocus (MonoidHom.id ↥Bs)
  let Hs : Subgroup ↥Bs := (s : ↥Bs →* ↥Bs).eqLocus (MonoidHom.id ↥Bs)
  have hfixr : ∀ b : ↥Bs, b ∈ Hr ↔ r b = b := by
    intro b
    change r b = b ↔ r b = b
    rfl
  have hfixs : ∀ b : ↥Bs, b ∈ Hs ↔ s b = b := by
    intro b
    change s b = b ↔ s b = b
    rfl
  have hHr : Subgroup.closure (Set.range fun i => rootDiagUnit τ (a₀ i)) = Hr.map β := by
    ext z
    rw [Subgroup.mem_map]
    simpa only [hfixr] using hH₀ z
  have hHs : Subgroup.closure (Set.range fun i => rootDiagUnit τ (a₁ i)) = Hs.map β := by
    ext z
    rw [Subgroup.mem_map]
    simpa only [hfixs] using hH₁ z
  have hc := commutation_of_orthogonal_families_normalizer_action hτ hp hp2
    a₀ a₁ ha₀ ha₁ Y hY horth ψ hψinj Bs.subtype β hpres hcompat Hr Hs hHr hHs
  rw [hX] at hc
  exact hc

end OrthogonalFamilies

theorem pair_of_matched_frame
    {t : StatedLieTag} {f p : ℕ} {ht : GGExcFive t}
    (M : GGDatumModel t f p ht) {n : ℕ}
    (hf : 1 ≤ f) (hp : p.Prime) (hp2 : p ≠ 2) (hreg : GGExcRegime p f)
    (ρF : Equiv.Perm (Fin (langTag t).rank → ℤ)) (hFrob : FrobRootMap M.D ρF)
    (j : Matrix.SpecialLinearGroup (Fin 3) GGL →* ModGL (langTag t) GGL)
    (σ : Fin 3 → Fin 3 → Fin (langTag t).rank → ℤ)
    (hpair : CFSG.RankThree.PartOne.KF4.IsA2Frame j σ)
    (hrev : ∀ i k : Fin 3, i ≠ k → ρF (σ i k) = σ k i)
    (F : Subfield GGL) [Fact (Nat.Prime 2)] [CharP F 2] [Finite F]
    (hF : ∀ c : GGL, c ∈ F ↔ c ^ (2 ^ f) ^ 2 = c)
    (hFcard : Nat.card F = (2 ^ f) ^ 2)
    {I₀ I₁ : Type*} [Finite I₀] [Finite I₁]
    (a₀ : I₀ → Fin (langTag t).rank → GGLˣ)
    (a₁ : I₁ → Fin (langTag t).rank → GGLˣ)
    (ha₀ : ∀ i, ∃ k : ℕ, a₀ i ^ (p ^ k) = 1)
    (ha₁ : ∀ i, ∃ k : ℕ, a₁ i ^ (p ^ k) = 1)
    (hk₀ : famKernel (Set.range a₀) = {σ 0 1, -σ 0 1})
    (hk₁ : famKernel (Set.range a₁) = {σ 1 2, -σ 1 2}) :
    ∃ θ : Su F 2 f 3 →* ModGL (langTag t) GGL,
      Function.Injective θ ∧ θ.range ≤ M.D.Γ ∧
      θ.range = rootSpan (langTag t) GGL (frameRoots σ) ⊓ M.D.Γ ∧
      θ.range ≤ Subgroup.centralizer
        ((Subgroup.closure (Set.range fun i => rootDiagUnit (langTag t) (a₀ i)) ⊓
          Subgroup.closure (Set.range fun i => rootDiagUnit (langTag t) (a₁ i)) :
            Subgroup (ModGL (langTag t) GGL)) : Set (ModGL (langTag t) GGL)) ∧
      ggOTwoPrime (M.D.Γ ⊓ Subgroup.centralizer (Set.range fun i => rootDiagUnit (langTag t) (a₀ i))) =
        (B12 F 2 f).map θ ∧
      ggOTwoPrime (M.D.Γ ⊓ Subgroup.centralizer (Set.range fun i => rootDiagUnit (langTag t) (a₁ i))) =
        (B23 F 2 f).map θ ∧
      UnitaryBlockStandardPair F 2 f θ.range
        (ggOTwoPrime (M.D.Γ ⊓ Subgroup.centralizer (Set.range fun i => rootDiagUnit (langTag t) (a₀ i))))
        (ggOTwoPrime (M.D.Γ ⊓ Subgroup.centralizer (Set.range fun i => rootDiagUnit (langTag t) (a₁ i)))) := by
  obtain ⟨θ, hθinj, hθrange, hB₀, hB₁⟩ :=
    compactA2Pair_of_LangDatum hf j σ hpair M.D ρF hFrob hrev M.hq F hF hFcard
  have hθΓ : θ.range ≤ M.D.Γ :=
    M.ggSu_range_le_model_Γ (n := n) hf hp hp2 hreg hFcard θ (hθrange.le.trans inf_le_right)
  have hΓmodel : M.D.Γ ≤ M.D.model := Subgroup.commutator_le_self M.D.model
  have hΓadj : M.D.Γ ≤ adjointGroup (langTag t) GGL := hΓmodel.trans inf_le_left
  have hB₀Γ : (B12 F 2 f).map θ ≤ M.D.Γ := by
    rintro x ⟨y, _, rfl⟩
    exact hθΓ ⟨y, rfl⟩
  have hB₁Γ : (B23 F 2 f).map θ ≤ M.D.Γ := by
    rintro x ⟨y, _, rfl⟩
    exact hθΓ ⟨y, rfl⟩
  have hB₀' : (B12 F 2 f).map θ = rootSpan (langTag t) GGL {σ 0 1, -σ 0 1} ⊓ M.D.Γ := by
    refine le_antisymm (le_inf (hB₀.le.trans inf_le_left) hB₀Γ) ?_
    intro x hx
    exact hB₀.ge ⟨hx.1, hΓmodel hx.2⟩
  have hB₁' : (B23 F 2 f).map θ = rootSpan (langTag t) GGL {σ 1 2, -σ 1 2} ⊓ M.D.Γ := by
    refine le_antisymm (le_inf (hB₁.le.trans inf_le_left) hB₁Γ) ?_
    intro x hx
    exact hB₁.ge ⟨hx.1, hΓmodel hx.2⟩
  let θ₀ := θ.comp (CFSG.LieType.Steinberg.embSUid (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) 2)
  let θ₁ := θ.comp (CFSG.LieType.Steinberg.embSUid (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) 0)
  have hr₀ : θ₀.range = (B12 F 2 f).map θ := by
    dsimp [θ₀]
    rw [MonoidHom.range_comp]
    rfl
  have hr₁ : θ₁.range = (B23 F 2 f).map θ := by
    dsimp [θ₁]
    rw [MonoidHom.range_comp]
    rfl
  have hres₀ : ggOTwoPrime (M.D.Γ ⊓ Subgroup.centralizer
      (Set.range fun i => rootDiagUnit (langTag t) (a₀ i))) = (B12 F 2 f).map θ := by
    rw [← hr₀]
    apply LayerSixE.oTwoPrime_famCentralizer_eq_su_range_of_rootSpan hp hp2 a₀ ha₀ M.D.Γ hΓadj
      hFcard (by norm_num : 2 ≤ 2) θ₀
    rw [hr₀, hk₀]
    exact hB₀'
  have hres₁ : ggOTwoPrime (M.D.Γ ⊓ Subgroup.centralizer
      (Set.range fun i => rootDiagUnit (langTag t) (a₁ i))) = (B23 F 2 f).map θ := by
    rw [← hr₁]
    apply LayerSixE.oTwoPrime_famCentralizer_eq_su_range_of_rootSpan hp hp2 a₁ ha₁ M.D.Γ hΓadj
      hFcard (by norm_num : 2 ≤ 2) θ₁
    rw [hr₁, hk₁]
    exact hB₁'
  have hθspan : θ.range = rootSpan (langTag t) GGL (frameRoots σ) ⊓ M.D.Γ := by
    refine le_antisymm (le_inf (hθrange.le.trans inf_le_left) hθΓ) ?_
    intro x hx
    exact hθrange.ge ⟨hx.1, hΓmodel hx.2⟩
  have hθcommon : θ.range ≤ Subgroup.centralizer
      ((Subgroup.closure (Set.range fun i => rootDiagUnit (langTag t) (a₀ i)) ⊓
        Subgroup.closure (Set.range fun i => rootDiagUnit (langTag t) (a₁ i)) :
          Subgroup (ModGL (langTag t) GGL)) : Set (ModGL (langTag t) GGL)) := by
    have h0 : rootDiagUnit (langTag t) '' Set.range a₀ =
        Set.range (fun i => rootDiagUnit (langTag t) (a₀ i)) :=
      (Set.range_comp (rootDiagUnit (langTag t)) a₀).symm
    have h1 : rootDiagUnit (langTag t) '' Set.range a₁ =
        Set.range (fun i => rootDiagUnit (langTag t) (a₁ i)) :=
      (Set.range_comp (rootDiagUnit (langTag t)) a₁).symm
    have h := IsA2Frame.frameSpan_le_centralizer_of_two_family_kernels hpair
      (Set.range a₀) (Set.range a₁) hk₀ hk₁
    rw [h0, h1] at h
    exact (hθspan.le.trans inf_le_left).trans h
  refine ⟨θ, hθinj, hθΓ, hθspan, hθcommon, hres₀, hres₁, ?_⟩
  have hθker : θ.ker ≤ Subgroup.center (Su F 2 f 3) := by
    rw [(MonoidHom.ker_eq_bot_iff θ).mpr hθinj]
    exact bot_le
  exact CFSG.GH74.L5U5.unitaryBlockStandardPair_of_blocks hθker hres₀.symm hres₁.symm

theorem pair_of_matched_frame_normalizer_action
    {G A : Type} [Group G] [Finite G] [Group A] {X : Subgroup G}
    {t : StatedLieTag} {f p : ℕ} {ht : GGExcFive t}
    (M : GGDatumModel t f p ht) {n : ℕ}
    (hf : 1 ≤ f) (hp : p.Prime) (hp2 : p ≠ 2) (hreg : GGExcRegime p f)
    (ρF : Equiv.Perm (Fin (langTag t).rank → ℤ)) (hFrob : FrobRootMap M.D ρF)
    (j : Matrix.SpecialLinearGroup (Fin 3) GGL →* ModGL (langTag t) GGL)
    (σ : Fin 3 → Fin 3 → Fin (langTag t).rank → ℤ)
    (hpair : CFSG.RankThree.PartOne.KF4.IsA2Frame j σ)
    (hrev : ∀ i k : Fin 3, i ≠ k → ρF (σ i k) = σ k i)
    (F : Subfield GGL) [Fact (Nat.Prime 2)] [CharP F 2] [Finite F]
    (hF : ∀ c : GGL, c ∈ F ↔ c ^ (2 ^ f) ^ 2 = c)
    (hFcard : Nat.card F = (2 ^ f) ^ 2)
    {I₀ I₁ : Type*} [Finite I₀] [Finite I₁]
    (a₀ : I₀ → Fin (langTag t).rank → GGLˣ)
    (a₁ : I₁ → Fin (langTag t).rank → GGLˣ)
    (ha₀ : ∀ i, ∃ k : ℕ, a₀ i ^ (p ^ k) = 1)
    (ha₁ : ∀ i, ∃ k : ℕ, a₁ i ^ (p ^ k) = 1)
    (hk₀ : famKernel (Set.range a₀) = {σ 0 1, -σ 0 1})
    (hk₁ : famKernel (Set.range a₁) = {σ 1 2, -σ 1 2})
    (ψ : ↥M.D.Γ →* G) (hψinj : Function.Injective ψ) (hX : ψ.range = X)
    (η : A →* G) (β : A →* ModGL (langTag t) GGL)
    (hpres : ∀ (a : A) (y : ↥M.D.Γ), β a * (y : ModGL (langTag t) GGL) * (β a)⁻¹ ∈ M.D.Γ)
    (hcompat : ∀ (a : A) (y : ↥M.D.Γ),
      ψ ⟨β a * (y : ModGL (langTag t) GGL) * (β a)⁻¹, hpres a y⟩ =
        η a * ψ y * (η a)⁻¹)
    (H₀ H₁ : Subgroup A)
    (hH₀ : Subgroup.closure (Set.range fun i => rootDiagUnit (langTag t) (a₀ i)) = H₀.map β)
    (hH₁ : Subgroup.closure (Set.range fun i => rootDiagUnit (langTag t) (a₁ i)) = H₁.map β) :
    ∃ θG : Su F 2 f 3 →* G,
      Function.Injective θG ∧ θG.range ≤ X ∧
      θG.range ≤ Subgroup.centralizer ((H₀ ⊓ H₁).map η : Set G) ∧
      (B12 F 2 f).map θG = ggOTwoPrime (X ⊓ Subgroup.centralizer (H₀.map η : Set G)) ∧
      (B23 F 2 f).map θG = ggOTwoPrime (X ⊓ Subgroup.centralizer (H₁.map η : Set G)) ∧
      UnitaryBlockStandardPair F 2 f θG.range
        (ggOTwoPrime (X ⊓ Subgroup.centralizer (H₀.map η : Set G)))
        (ggOTwoPrime (X ⊓ Subgroup.centralizer (H₁.map η : Set G))) := by
  obtain ⟨θ, hθinj, hθΓ, _hθspan, hθcommon, hres₀, hres₁, _hpair⟩ :=
    pair_of_matched_frame M (n := n) hf hp hp2 hreg ρF hFrob j σ hpair hrev
      F hF hFcard a₀ a₁ ha₀ ha₁ hk₀ hk₁
  let θΓ : Su F 2 f 3 →* ↥M.D.Γ := θ.codRestrict M.D.Γ (fun x => hθΓ ⟨x, rfl⟩)
  let θG : Su F 2 f 3 →* G := ψ.comp θΓ
  have hθΓinj : Function.Injective θΓ := by
    intro x y hxy
    exact hθinj (congrArg Subtype.val hxy)
  have hθGinj : Function.Injective θG := hψinj.comp hθΓinj
  have hθGX : θG.range ≤ X := by
    rintro _ ⟨x, rfl⟩
    rw [← hX]
    exact ⟨θΓ x, rfl⟩
  have hθGC : θG.range ≤ Subgroup.centralizer ((H₀ ⊓ H₁).map η : Set G) := by
    rintro _ ⟨x, rfl⟩
    apply Subgroup.mem_centralizer_iff.mpr
    rintro _ ⟨a, ha, rfl⟩
    apply (normalizer_action_commute_iff ψ hψinj η β hpres hcompat a (θΓ x)).mpr
    have hβa : β a ∈
        Subgroup.closure (Set.range fun i => rootDiagUnit (langTag t) (a₀ i)) ⊓
        Subgroup.closure (Set.range fun i => rootDiagUnit (langTag t) (a₁ i)) := by
      rw [hH₀, hH₁]
      exact ⟨Subgroup.mem_map.mpr ⟨a, ha.1, rfl⟩, Subgroup.mem_map.mpr ⟨a, ha.2, rfl⟩⟩
    exact Subgroup.mem_centralizer_iff.mp (hθcommon ⟨x, rfl⟩) (β a) hβa
  have hmap : ∀ U : Subgroup (Su F 2 f 3), U.map θΓ = (U.map θ).subgroupOf M.D.Γ := by
    intro U
    apply Subgroup.map_injective (f := M.D.Γ.subtype) M.D.Γ.subtype_injective
    have hU : U.map θ ≤ M.D.Γ := by
      rintro _ ⟨x, _hx, rfl⟩
      exact hθΓ ⟨x, rfl⟩
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hU, Subgroup.map_map]
    rfl
  have hR₀ : ggOTwoPrime (X ⊓ Subgroup.centralizer (H₀.map η : Set G)) =
      ((ggOTwoPrime (M.D.Γ ⊓ Subgroup.centralizer
        (Set.range fun i => rootDiagUnit (langTag t) (a₀ i)))).subgroupOf M.D.Γ).map ψ := by
    have h := map_oTwoPrime_centralizer_of_normalizer_action ψ hψinj η β hpres hcompat H₀
    rw [hX, ← hH₀, Subgroup.centralizer_closure] at h
    exact h.symm
  have hR₁ : ggOTwoPrime (X ⊓ Subgroup.centralizer (H₁.map η : Set G)) =
      ((ggOTwoPrime (M.D.Γ ⊓ Subgroup.centralizer
        (Set.range fun i => rootDiagUnit (langTag t) (a₁ i)))).subgroupOf M.D.Γ).map ψ := by
    have h := map_oTwoPrime_centralizer_of_normalizer_action ψ hψinj η β hpres hcompat H₁
    rw [hX, ← hH₁, Subgroup.centralizer_closure] at h
    exact h.symm
  have hmarked₀ : (B12 F 2 f).map θG =
      ggOTwoPrime (X ⊓ Subgroup.centralizer (H₀.map η : Set G)) := by
    rw [hR₀, hres₀]
    change (B12 F 2 f).map (ψ.comp θΓ) = _
    rw [← Subgroup.map_map, hmap]
  have hmarked₁ : (B23 F 2 f).map θG =
      ggOTwoPrime (X ⊓ Subgroup.centralizer (H₁.map η : Set G)) := by
    rw [hR₁, hres₁]
    change (B23 F 2 f).map (ψ.comp θΓ) = _
    rw [← Subgroup.map_map, hmap]
  refine ⟨θG, hθGinj, hθGX, hθGC, hmarked₀, hmarked₁, ?_⟩
  have hker : θG.ker ≤ Subgroup.center (Su F 2 f 3) := by
    rw [(MonoidHom.ker_eq_bot_iff θG).mpr hθGinj]
    exact bot_le
  exact CFSG.GH74.L5U5.unitaryBlockStandardPair_of_blocks hker hmarked₀ hmarked₁

theorem pair_of_matched_frame_original_member
    {G : Type} [Group G] [Finite G] {X Bs : Subgroup G}
    {t : StatedLieTag} {f p : ℕ} {ht : GGExcFive t}
    (M : GGDatumModel t f p ht) {n : ℕ}
    (hf : 1 ≤ f) (hp : p.Prime) (hp2 : p ≠ 2) (hreg : GGExcRegime p f)
    (ρF : Equiv.Perm (Fin (langTag t).rank → ℤ)) (hFrob : FrobRootMap M.D ρF)
    (j : Matrix.SpecialLinearGroup (Fin 3) GGL →* ModGL (langTag t) GGL)
    (σ : Fin 3 → Fin 3 → Fin (langTag t).rank → ℤ)
    (hpair : CFSG.RankThree.PartOne.KF4.IsA2Frame j σ)
    (hrev : ∀ i k : Fin 3, i ≠ k → ρF (σ i k) = σ k i)
    (F : Subfield GGL) [Fact (Nat.Prime 2)] [CharP F 2] [Finite F]
    (hF : ∀ c : GGL, c ∈ F ↔ c ^ (2 ^ f) ^ 2 = c)
    (hFcard : Nat.card F = (2 ^ f) ^ 2)
    {I₀ I₁ : Type*} [Finite I₀] [Finite I₁]
    (a₀ : I₀ → Fin (langTag t).rank → GGLˣ)
    (a₁ : I₁ → Fin (langTag t).rank → GGLˣ)
    (ha₀ : ∀ i, ∃ k : ℕ, a₀ i ^ (p ^ k) = 1)
    (ha₁ : ∀ i, ∃ k : ℕ, a₁ i ^ (p ^ k) = 1)
    (hk₀ : famKernel (Set.range a₀) = {σ 0 1, -σ 0 1})
    (hk₁ : famKernel (Set.range a₁) = {σ 1 2, -σ 1 2})
    (ψ : ↥M.D.Γ →* G) (hψinj : Function.Injective ψ) (hX : ψ.range = X)
    (β : ↥Bs →* ModGL (langTag t) GGL)
    (hpres : ∀ (b : ↥Bs) (y : ↥M.D.Γ), β b * (y : ModGL (langTag t) GGL) * (β b)⁻¹ ∈ M.D.Γ)
    (hcompat : ∀ (b : ↥Bs) (y : ↥M.D.Γ),
      ψ ⟨β b * (y : ModGL (langTag t) GGL) * (β b)⁻¹, hpres b y⟩ =
        (b : G) * ψ y * (b : G)⁻¹)
    (r s : MulAut ↥Bs)
    (hH₀ : ∀ z : ModGL (langTag t) GGL,
      z ∈ Subgroup.closure (Set.range fun i => rootDiagUnit (langTag t) (a₀ i)) ↔
        ∃ b : ↥Bs, r b = b ∧ β b = z)
    (hH₁ : ∀ z : ModGL (langTag t) GGL,
      z ∈ Subgroup.closure (Set.range fun i => rootDiagUnit (langTag t) (a₁ i)) ↔
        ∃ b : ↥Bs, s b = b ∧ β b = z) :
    ∃ θG : Su F 2 f 3 →* G,
      Function.Injective θG ∧ θG.range ≤ X ∧
      (B12 F 2 f).map θG = ggRankOneIn X Bs r ∧
      (B23 F 2 f).map θG = ggRankOneIn X Bs s ∧
      UnitaryBlockStandardPair F 2 f θG.range (ggRankOneIn X Bs r) (ggRankOneIn X Bs s) := by
  let Hr : Subgroup ↥Bs := (r : ↥Bs →* ↥Bs).eqLocus (MonoidHom.id ↥Bs)
  let Hs : Subgroup ↥Bs := (s : ↥Bs →* ↥Bs).eqLocus (MonoidHom.id ↥Bs)
  have hfixr : ∀ b : ↥Bs, b ∈ Hr ↔ r b = b := by
    intro b
    change r b = b ↔ r b = b
    rfl
  have hfixs : ∀ b : ↥Bs, b ∈ Hs ↔ s b = b := by
    intro b
    change s b = b ↔ s b = b
    rfl
  have hHr : Subgroup.closure (Set.range fun i => rootDiagUnit (langTag t) (a₀ i)) = Hr.map β := by
    ext z
    rw [Subgroup.mem_map]
    simpa only [hfixr] using hH₀ z
  have hHs : Subgroup.closure (Set.range fun i => rootDiagUnit (langTag t) (a₁ i)) = Hs.map β := by
    ext z
    rw [Subgroup.mem_map]
    simpa only [hfixs] using hH₁ z
  obtain ⟨θG, hθinj, hθX, _hθC, hB₀, hB₁, hstd⟩ :=
    pair_of_matched_frame_normalizer_action M (n := n) hf hp hp2 hreg ρF hFrob
      j σ hpair hrev F hF hFcard a₀ a₁ ha₀ ha₁ hk₀ hk₁
      ψ hψinj hX Bs.subtype β hpres hcompat Hr Hs hHr hHs
  exact ⟨θG, hθinj, hθX, hB₀, hB₁, hstd⟩

end CFSG.StandardType.ResidualA2Pair

end
