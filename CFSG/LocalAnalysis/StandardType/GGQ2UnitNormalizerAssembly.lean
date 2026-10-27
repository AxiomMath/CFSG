module

public import CFSG.LocalAnalysis.StandardType.GGQ2UnitAssembly
public import CFSG.LocalAnalysis.StandardType.GGQ2UnitNormalizerStatements
public import CFSG.LocalAnalysis.StandardType.GGQ2UnitRealization
public import CFSG.LocalAnalysis.StandardType.GGQ2AmbModelOfLin
import CFSG.LocalAnalysis.StandardType.GGQ2SpRealization

public section

namespace CFSG.StandardType.GGQ2Frame.UnitPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Open (IsElemAbelian)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

variable {G : Type} [Group G] {H E : Subgroup G} {N : ℕ} {K : Type} [Field K]
  {hEN : E ≤ Subgroup.normalizer (H : Set G)} {ζ : Multiplicative (ZMod 3) →* Kˣ}

theorem projConj_diagOf_mem_blockPSU (w : UnitRaw.W N)
    (hD : diagOf ζ w ∈ Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K)))
    {S : Finset (Fin N)} {y : LargeEvenProj (unitarySU 2 1 K N)}
    (hy : y ∈ blockPSU (K := K) S) :
    TableB.projConj _ ⟨diagOf ζ w, hD⟩ y ∈ blockPSU (K := K) S := by
  obtain ⟨B, hB, rfl⟩ := Subgroup.mem_map.mp hy
  refine Subgroup.mem_map.mpr ⟨(unitarySU 2 1 K N).normalizerMonoidHom ⟨diagOf ζ w, hD⟩ B, ?_,
    (TableB.projConj_mk _ _ B).symm⟩
  have hc : ((((unitarySU 2 1 K N).normalizerMonoidHom ⟨diagOf ζ w, hD⟩ B :
      ↥(unitarySU 2 1 K N)) : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) =
      Matrix.diagonal (fun i => ((ζ (Multiplicative.ofAdd (w i)) : Kˣ) : K)) *
        ((B : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *
          Matrix.diagonal (fun i => ((ζ (Multiplicative.ofAdd ((-w) i)) : Kˣ) : K)) := by
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    change ((diagOf ζ w * (B : GL (Fin N) K) * (diagOf ζ w)⁻¹ : GL (Fin N) K) :
      Matrix (Fin N) (Fin N) K) = _
    rw [← diagOf_neg, Units.val_mul, Units.val_mul, coe_diagOf, coe_diagOf]
  rw [TableBUE.mem_blockSU]
  intro i j hij
  rw [hc, Matrix.mul_diagonal, Matrix.diagonal_mul, TableBUE.mem_blockSU.mp hB i j hij]
  by_cases hij' : i = j
  · subst hij'
    simp only [Matrix.one_apply_eq, mul_one, Pi.neg_apply, ofAdd_neg, map_inv, Units.mul_inv]
  · simp only [Matrix.one_apply_ne hij', mul_zero, zero_mul]

theorem UnitFrame.derived_comap_blockPSU_stable (fr : UnitFrame H E hEN K N ζ)
    (S : Finset (Fin N)) (b : ↥E) (x : ↥H)
    (hx : x ∈ ⁅(blockPSU (K := K) S).comap fr.π, (blockPSU (K := K) S).comap fr.π⁆) :
    H.normalizerMonoidHom ⟨b, hEN b.2⟩ x ∈
      ⁅(blockPSU (K := K) S).comap fr.π, (blockPSU (K := K) S).comap fr.π⁆ := by
  have hP : ((blockPSU (K := K) S).comap fr.π).map
      (H.normalizerMonoidHom ⟨b, hEN b.2⟩).toMonoidHom ≤ (blockPSU (K := K) S).comap fr.π := by
    rw [Subgroup.map_le_iff_le_comap]
    intro z hz
    change fr.π (H.normalizerMonoidHom ⟨b, hEN b.2⟩ z) ∈ blockPSU (K := K) S
    rw [fr.pi_conj_eq_rhoFun]
    exact projConj_diagOf_mem_blockPSU (fr.rep b) (fr.rep_mem_normalizer b) hz
  have h1 : H.normalizerMonoidHom ⟨b, hEN b.2⟩ x ∈
      (⁅(blockPSU (K := K) S).comap fr.π, (blockPSU (K := K) S).comap fr.π⁆).map
        (H.normalizerMonoidHom ⟨b, hEN b.2⟩).toMonoidHom :=
    Subgroup.mem_map_of_mem _ hx
  rw [Subgroup.map_commutator] at h1
  exact Subgroup.commutator_mono hP hP h1

theorem UnitCtx.mem_map_ggAutomizer_iff [Finite G] (hAct : AutomizerActEq)
    (ctx : UnitCtx H E hEN K N ζ) {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (c : Additive ↥E ≃+ V) (X : Subgroup ↥H)
    (hX : ∀ (b : ↥E) (x : ↥H), x ∈ X → H.normalizerMonoidHom ⟨b, hEN b.2⟩ x ∈ X)
    (ψ : V ≃ₗ[ZMod 3] V) :
    ψ ∈ (ggAutomizer (X.map H.subtype) E).map (ggLin (p := 3) c) ↔
      ∃ y ∈ X.map ctx.fr.π, ∀ b : ↥E,
        ctx.fr.rho (ggLinInv c ψ b) = MulAut.conj y * ctx.fr.rho b * (MulAut.conj y)⁻¹ := by
  have hact := hAct hEN ctx.fr.π ctx.fr.rho ctx.fr.surj ctx.fr.ker_le ctx.hHp ctx.hEab ctx.hC3
    ctx.fr.equivariantAut X hX
  constructor
  · intro hψ
    obtain ⟨φ, hφ, rfl⟩ := Subgroup.mem_map.mp hψ
    have hφ' : ggLinInv c (ggLin (p := 3) c φ) = φ :=
      ggLin_injective (p := 3) c (ggLin_ggLinInv c _)
    rw [hφ']
    exact (hact φ).1 hφ
  · intro hy
    exact Subgroup.mem_map.mpr ⟨ggLinInv c ψ, (hact _).2 hy, ggLin_ggLinInv c ψ⟩

theorem UnitCtx.mem_map_ggAutomizer_full_iff [Finite G] (hAct : AutomizerActEq)
    (ctx : UnitCtx H E hEN K N ζ) (h : ctx.fr.ι.range = ⊤) (X : Subgroup ↥H)
    (hX : ∀ (b : ↥E) (x : ↥H), x ∈ X → H.normalizerMonoidHom ⟨b, hEN b.2⟩ x ∈ X)
    (ψ : UnitRaw.Vfull N ≃ₗ[ZMod 3] UnitRaw.Vfull N) :
    ψ ∈ (ggAutomizer (X.map H.subtype) E).map (ggLin (p := 3) (ctx.fr.coordFull h)) ↔
      ψ ∈ unitTorusAut ζ N (X.map ctx.fr.π) := by
  rw [ctx.mem_map_ggAutomizer_iff hAct _ X hX ψ]
  have hc : ∀ b : ↥E, ctx.fr.coordFull h (Additive.ofMul b) = ctx.fr.ι (Additive.ofMul b) :=
    fun _ => rfl
  have hψ : ∀ b : ↥E, ctx.fr.ι (Additive.ofMul (ggLinInv (ctx.fr.coordFull h) ψ b)) =
      ψ (ctx.fr.ι (Additive.ofMul b)) := by
    intro b
    rw [← hc, ← hc, ← ggLin_apply_ofMul (p := 3) (ctx.fr.coordFull h)
      (ggLinInv (ctx.fr.coordFull h) ψ) b, ggLin_ggLinInv]
  constructor
  · rintro ⟨y, hy, hyρ⟩
    refine ⟨y, hy, fun w w' hD hD' hww' => ?_⟩
    obtain ⟨b, hb⟩ : ∃ b : ↥E, ctx.fr.ι (Additive.ofMul b) = (UnitRaw.oneLine N).mkQ w := by
      have hw : (UnitRaw.oneLine N).mkQ w ∈ ctx.fr.ι.range := by
        rw [h]
        exact AddSubgroup.mem_top _
      obtain ⟨a, ha⟩ := hw
      exact ⟨Additive.toMul a, ha⟩
    have h1 : ctx.fr.rho b = TableB.projConj _ ⟨diagOf ζ w, hD⟩ := ctx.fr.rho_eq b hb.symm hD
    have h2 : ctx.fr.rho (ggLinInv (ctx.fr.coordFull h) ψ b) =
        TableB.projConj _ ⟨diagOf ζ w', hD'⟩ :=
      ctx.fr.rho_eq _ (by rw [hww', ← hb, hψ]) hD'
    rw [← h1, ← h2, hyρ b]
  · rintro ⟨y, hy, hyw⟩
    refine ⟨y, hy, fun b => ?_⟩
    have hyb := hyw (ctx.fr.rep b) (ctx.fr.rep (ggLinInv (ctx.fr.coordFull h) ψ b))
      (ctx.fr.rep_mem_normalizer b) (ctx.fr.rep_mem_normalizer _)
      (by rw [ctx.fr.mkQ_rep, ctx.fr.mkQ_rep, hψ])
    rw [ctx.fr.rho_apply, ctx.fr.rho_apply]
    exact hyb.symm

theorem UnitCtx.mem_map_ggAutomizer_heart_iff [Finite G] (hAct : AutomizerActEq)
    (ctx : UnitCtx H E hEN K N ζ) (h : ctx.fr.ι.range = (UnitRaw.heart N).toAddSubgroup)
    (X : Subgroup ↥H)
    (hX : ∀ (b : ↥E) (x : ↥H), x ∈ X → H.normalizerMonoidHom ⟨b, hEN b.2⟩ x ∈ X)
    (ψ : ↥(UnitRaw.heart N) ≃ₗ[ZMod 3] ↥(UnitRaw.heart N)) :
    ψ ∈ (ggAutomizer (X.map H.subtype) E).map (ggLin (p := 3) (ctx.fr.coordHeart h)) ↔
      ψ ∈ unitTorusAutH ζ N (X.map ctx.fr.π) := by
  rw [ctx.mem_map_ggAutomizer_iff hAct _ X hX ψ]
  have hc : ∀ b : ↥E, ((ctx.fr.coordHeart h (Additive.ofMul b) : ↥(UnitRaw.heart N)) :
      UnitRaw.Vfull N) = ctx.fr.ι (Additive.ofMul b) := fun _ => rfl
  have hψ : ∀ b : ↥E, ctx.fr.coordHeart h (Additive.ofMul (ggLinInv (ctx.fr.coordHeart h) ψ b)) =
      ψ (ctx.fr.coordHeart h (Additive.ofMul b)) := by
    intro b
    rw [← ggLin_apply_ofMul (p := 3) (ctx.fr.coordHeart h) (ggLinInv (ctx.fr.coordHeart h) ψ) b,
      ggLin_ggLinInv]
  constructor
  · rintro ⟨y, hy, hyρ⟩
    refine ⟨y, hy, fun w w' hD hD' hw hw' hww' => ?_⟩
    obtain ⟨b, hb⟩ : ∃ b : ↥E,
        ctx.fr.coordHeart h (Additive.ofMul b) = ⟨(UnitRaw.oneLine N).mkQ w, hw⟩ :=
      ⟨Additive.toMul ((ctx.fr.coordHeart h).symm ⟨_, hw⟩), by
        rw [ofMul_toMul, AddEquiv.apply_symm_apply]⟩
    have h1 : ctx.fr.rho b = TableB.projConj _ ⟨diagOf ζ w, hD⟩ :=
      ctx.fr.rho_eq b (by rw [← hc, hb]) hD
    have h2 : ctx.fr.rho (ggLinInv (ctx.fr.coordHeart h) ψ b) =
        TableB.projConj _ ⟨diagOf ζ w', hD'⟩ :=
      ctx.fr.rho_eq _ (by rw [← hc, hψ, hb, ← hww']) hD'
    rw [← h1, ← h2, hyρ b]
  · rintro ⟨y, hy, hyw⟩
    refine ⟨y, hy, fun b => ?_⟩
    have hmem : ∀ a : ↥E, (UnitRaw.oneLine N).mkQ (ctx.fr.rep a) ∈ UnitRaw.heart N := fun a => by
      rw [ctx.fr.mkQ_rep, ← hc]
      exact (ctx.fr.coordHeart h (Additive.ofMul a)).2
    have hrep : ∀ a : ↥E, (⟨(UnitRaw.oneLine N).mkQ (ctx.fr.rep a), hmem a⟩ : ↥(UnitRaw.heart N)) =
        ctx.fr.coordHeart h (Additive.ofMul a) :=
      fun a => Subtype.ext (by rw [hc]; exact ctx.fr.mkQ_rep a)
    have hyb := hyw (ctx.fr.rep b) (ctx.fr.rep (ggLinInv (ctx.fr.coordHeart h) ψ b))
      (ctx.fr.rep_mem_normalizer b) (ctx.fr.rep_mem_normalizer _) (hmem b) (hmem _)
      (by rw [hrep, hrep]; exact hψ b)
    rw [ctx.fr.rho_apply, ctx.fr.rho_apply]
    exact hyb.symm

private theorem una_map_top_subtype : (⊤ : Subgroup ↥H).map H.subtype = H := by
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]

private theorem una_map_top_pi (fr : UnitFrame H E hEN K N ζ) :
    (⊤ : Subgroup ↥H).map fr.π = ⊤ := by
  rw [← MonoidHom.range_eq_map]
  exact MonoidHom.range_eq_top.mpr fr.surj

private theorem una_map_component (hM4 : UnitBlockPerfect) [Finite K] (ctx : UnitCtx H E hEN K N ζ)
    {S : Finset (Fin N)} (hS : UnitRaw.admissible S) :
    (⁅(blockPSU (K := K) S).comap ctx.fr.π, (blockPSU (K := K) S).comap ctx.fr.π⁆).map ctx.fr.π =
      blockPSU (K := K) S :=
  (SpPlacement.derived_comap_perfect ctx.fr.π ctx.fr.surj ctx.fr.ker_le
    (hM4 N ctx.hK ctx.hN S hS)).1

theorem unitNormalizerEqsFull_of_pieces [Finite G] [Finite K] (hAct : AutomizerActEq)
    (hAmb : UnitAmbientTorusAut) (hComp : UnitComponentTorusAut) (hM4 : UnitBlockPerfect)
    (hOcc : UnitComponentOccursIff) (hCent : UnitComponentCentEq) (hIn : UnitComponentInsideEq)
    (hMk : UnitComponentMarked) (ctx : UnitCtx H E hEN K N ζ) (h : ctx.fr.ι.range = ⊤) :
    (unitRealizationCoreFull hOcc hCent hIn hMk ctx h).NormalizerEqs := by
  refine ⟨fun S hS => ?_, ?_⟩
  · ext ψ
    have hk := ctx.mem_map_ggAutomizer_full_iff hAct h _
      (ctx.fr.derived_comap_blockPSU_stable S) ψ
    rw [una_map_component hM4 ctx hS.2] at hk
    exact hk.trans (Set.ext_iff.mp (hComp ζ N ctx.hK ctx.hζ ctx.hN S hS.2) ψ)
  · ext ψ
    have hk := ctx.mem_map_ggAutomizer_full_iff hAct h ⊤ (fun _ _ _ => Subgroup.mem_top _) ψ
    rw [una_map_top_subtype, una_map_top_pi] at hk
    exact hk.trans (Set.ext_iff.mp (hAmb ζ N ctx.hK ctx.hζ ctx.hN) ψ)

theorem unitNormalizerEqsHeart_of_pieces [Finite G] [Finite K] (hAct : AutomizerActEq)
    (hAmbH : UnitAmbientTorusAutH) (hCompH : UnitComponentTorusAutH) (hM4 : UnitBlockPerfect)
    (hOcc : UnitComponentOccursIff) (hCent : UnitComponentCentEq) (hIn : UnitComponentInsideEq)
    (hMk : UnitComponentMarked) (ctx : UnitCtx H E hEN K N ζ) (h3 : 3 ∣ N)
    (h : ctx.fr.ι.range = (UnitRaw.heart N).toAddSubgroup) :
    (unitRealizationCoreHeart hOcc hCent hIn hMk ctx h3 h).NormalizerEqs := by
  refine ⟨fun S hS => ?_, ?_⟩
  · ext ψ
    have hk := ctx.mem_map_ggAutomizer_heart_iff hAct h _
      (ctx.fr.derived_comap_blockPSU_stable S) ψ
    rw [una_map_component hM4 ctx hS.2.2] at hk
    exact hk.trans (Set.ext_iff.mp (hCompH ζ N ctx.hK ctx.hζ ctx.hN h3 S hS.2.2) ψ)
  · ext ψ
    have hk := ctx.mem_map_ggAutomizer_heart_iff hAct h ⊤ (fun _ _ _ => Subgroup.mem_top _) ψ
    rw [una_map_top_subtype, una_map_top_pi] at hk
    exact hk.trans (Set.ext_iff.mp (hAmbH ζ N ctx.hK ctx.hζ ctx.hN h3) ψ)

theorem unitPlacement_of_pieces (hD : UnitInnerDiagData) (hF : ExistsUnitFrame)
    (hR : UnitFrameRange) (hOcc : UnitComponentOccursIff) (hCent : UnitComponentCentEq)
    (hIn : UnitComponentInsideEq) (hMk : UnitComponentMarked) (hAct : AutomizerActEq)
    (hAmb : UnitAmbientTorusAut) (hAmbH : UnitAmbientTorusAutH) (hComp : UnitComponentTorusAut)
    (hCompH : UnitComponentTorusAutH) (hM4 : UnitBlockPerfect)
    {G : Type} [Group G] [Finite G] {H E : Subgroup G} {N : ℕ}
    (hInn : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twA, N - 1, 1⟩) 3 E H)
    (hEab : IsElemAbelian 3 E) (hSC : ∀ g ∈ Subgroup.centralizer (E : Set G), g ^ 3 = 1 → g ∈ E)
    (hC3 : ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (H : Set G))) (hcard : 3 ^ 4 ≤ Nat.card E)
    (hrk : 3 ∣ N → 3 ^ (N - 3) ≤ Nat.card E) :
    Nonempty (Realization H E (unitFullEntry N)) ∨
      Nonempty (Realization H E (unitHeartEntry N)) := by
  obtain ⟨K, _, _, ζ, hEN, ⟨ctx⟩⟩ := unitCtx_of_pieces hD hF hR hInn hEab hSC hC3 hcard hrk
  rcases ctx.range with h | ⟨h3, h⟩
  · exact Or.inl ⟨Realization.ofCore _
      (unitNormalizerEqsFull_of_pieces hAct hAmb hComp hM4 hOcc hCent hIn hMk ctx h)⟩
  · exact Or.inr ⟨Realization.ofCore _
      (unitNormalizerEqsHeart_of_pieces hAct hAmbH hCompH hM4 hOcc hCent hIn hMk ctx h3 h)⟩

end

end CFSG.StandardType.GGQ2Frame.UnitPlacement

end
