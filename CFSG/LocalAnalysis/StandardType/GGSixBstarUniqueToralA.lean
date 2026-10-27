module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarUniqueRootPlaneA
public import CFSG.LocalAnalysis.StandardType.GGPGLTorality
public import CFSG.LocalAnalysis.StandardType.GGHypSixTypeA
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATorus
public import CFSG.LocalAnalysis.StandardType.GGTableBRank

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace RootPlaneA

section Hom

variable {m : ℕ} {F : Type} [Field F] {G : Type*} [Group G]
  {ψ : SpecialLinearGroup (Fin (m + 1)) F →* G}

theorem slConjugation_eq_conjSL (A : GL (Fin (m + 1)) F) (y : SpecialLinearGroup (Fin (m + 1)) F) :
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation (m + 1) F A y =
      InnerDiagA.conjSL A y := by
  apply SpecialLinearGroup.toGL_injective
  rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation, toGL_conjSL]

theorem conjSL_mul (A A' : GL (Fin (m + 1)) F) (y : SpecialLinearGroup (Fin (m + 1)) F) :
    InnerDiagA.conjSL (A * A') y = InnerDiagA.conjSL A (InnerDiagA.conjSL A' y) := by
  apply SpecialLinearGroup.toGL_injective
  rw [toGL_conjSL, toGL_conjSL, toGL_conjSL]
  group

theorem conjSL_one (y : SpecialLinearGroup (Fin (m + 1)) F) :
    InnerDiagA.conjSL (1 : GL (Fin (m + 1)) F) y = y := by
  apply SpecialLinearGroup.toGL_injective
  rw [toGL_conjSL]
  group

theorem conjAut_eq_of_psi_eq
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F))
    {A A' : GL (Fin (m + 1)) F}
    (h : ∀ y, ψ (InnerDiagA.conjSL A y) = ψ (InnerDiagA.conjSL A' y)) :
    conjAut (m + 1) F A = conjAut (m + 1) F A' := by
  ext z
  obtain ⟨y, rfl⟩ := proj_surjective (m + 1) F z
  rw [conjAut_proj, conjAut_proj, slConjugation_eq_conjSL, slConjugation_eq_conjSL,
    proj_eq_proj_iff, scalars_eq_center]
  apply hker
  rw [MonoidHom.mem_ker, map_mul, map_inv, h y, inv_mul_cancel]

theorem ggBstarToralA_of_card [Finite F] {p : ℕ} (hm : 2 ≤ m)
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {Bs : Subgroup G}
    (hBs : IsElemAbelian p Bs)
    (hinn : ∀ b ∈ Bs, ∃ A : GL (Fin (m + 1)) F, ∀ u, b⁻¹ * ψ u * b = ψ (InnerDiagA.conjSL A u))
    (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card F - 1)
    (hc1 : p ^ (m + 1 - 2) ≤ Nat.card Bs) (hc3 : p ^ 3 ≤ Nat.card Bs) :
    GGBstarToralA m F ψ Bs := by
  choose! Ab hAb using hinn
  have hrep : ∀ b ∈ Bs, ∀ A : GL (Fin (m + 1)) F,
      (∀ u, b⁻¹ * ψ u * b = ψ (InnerDiagA.conjSL A u)) →
        conjAut (m + 1) F A = conjAut (m + 1) F (Ab b) := fun b hb A hA =>
    conjAut_eq_of_psi_eq hker fun y => by rw [← hA y, ← hAb b hb y]
  have hprod : ∀ x ∈ Bs, ∀ y ∈ Bs,
      conjAut (m + 1) F (Ab (x * y)) = conjAut (m + 1) F (Ab y) * conjAut (m + 1) F (Ab x) := by
    intro x hx y hy
    rw [← map_mul]
    refine (hrep (x * y) (Bs.mul_mem hx hy) (Ab y * Ab x) fun u => ?_).symm
    rw [conjSL_mul, ← hAb y hy, ← hAb x hx]
    group
  let θ : ↥Bs →* MulAut (projectiveSL (m + 1) F) :=
    MonoidHom.mk' (fun b => conjAut (m + 1) F (Ab b)) fun x y => by
      change conjAut (m + 1) F (Ab ((x : G) * y)) =
        conjAut (m + 1) F (Ab x) * conjAut (m + 1) F (Ab y)
      rw [TableB.IsElemAbelian.comm hBs x.2 y.2, hprod y y.2 x x.2]
  have hθ : ∀ b : ↥Bs, θ b = conjAut (m + 1) F (Ab b) := fun _ => rfl
  have hinj : Function.Injective θ := by
    rw [injective_iff_map_eq_one]
    intro b hb1
    rw [hθ] at hb1
    have hcen : ∀ y, y⁻¹ * InnerDiagA.conjSL (Ab b) y ∈
        Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F) := by
      intro y
      have h2 := congrArg (fun α : MulAut (projectiveSL (m + 1) F) => α (proj (m + 1) F y)) hb1
      simp only [MulAut.one_apply] at h2
      rw [conjAut_proj, slConjugation_eq_conjSL] at h2
      have h3 := proj_eq_proj_iff.mp h2.symm
      rwa [scalars_eq_center] at h3
    have hn : 3 ≤ m + 1 := by omega
    have hperf : ⁅(⊤ : Subgroup (SpecialLinearGroup (Fin (m + 1)) F)), ⊤⁆ = ⊤ :=
      (CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect hn).commutator_eq_top
    have hφ₂ : ∀ y, ((MulAut.conj (b : G)⁻¹).toMonoidHom.comp ψ) y =
        ψ (InnerDiagA.conjSL (Ab b) y) := fun y => by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      exact hAb b b.2 y
    have heq := HypSixTypeA.eq_of_inv_mul_comm hperf (H := ψ.range) ψ
      ((MulAut.conj (b : G)⁻¹).toMonoidHom.comp ψ) (fun y => ⟨y, rfl⟩)
      (fun y => ⟨InnerDiagA.conjSL (Ab b) y, (hφ₂ y).symm⟩)
      (fun y k hk => by
        obtain ⟨v, rfl⟩ := hk
        rw [hφ₂, ← map_inv, ← map_mul, ← map_mul, ← map_mul,
          ← (Subgroup.mem_center_iff.mp (hcen y) v)])
    have hbC : (b : G) ∈ Subgroup.centralizer (ψ.range : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨y, rfl⟩
      have h1 := congrArg (fun φ : SpecialLinearGroup (Fin (m + 1)) F →* G => φ y) heq
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        inv_inv] at h1
      calc ψ y * (b : G) = (b : G) * ((b : G)⁻¹ * ψ y * (b : G)) := by group
        _ = (b : G) * ψ y := by rw [← h1]
    rw [hC, Subgroup.mem_bot] at hbC
    exact Subtype.ext hbC
  have hXel : IsElemAbelian p θ.range := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨_, x, rfl⟩ := a
      obtain ⟨_, y, rfl⟩ := b
      apply Subtype.ext
      change θ x * θ y = θ y * θ x
      rw [← map_mul, ← map_mul, hBs.1.is_comm.comm x y]
    · rintro _ ⟨x, rfl⟩
      have hx : x ^ p = 1 := Subtype.ext (by simpa using hBs.2 x x.2)
      rw [← map_pow, hx, map_one]
  have hXI : (θ.range : Set (MulAut (projectiveSL (m + 1) F))) ⊆ Set.range (conjAut (m + 1) F) := by
    rintro _ ⟨b, rfl⟩
    exact ⟨Ab b, rfl⟩
  have hXcard : Nat.card θ.range = Nat.card Bs :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  obtain ⟨A₀, hA₀⟩ := TypeA.ggPGLTorality_holds (K := F) (d := m + 1) hp hp2 hpK θ.range hXel
    hXI (hXcard ▸ hc1) (hXcard ▸ hc3)
  refine ⟨A₀, fun b hb A hA => ?_⟩
  have hmem : conjAut (m + 1) F A ∈ θ.range := by
    rw [hrep b hb A hA]
    exact ⟨⟨b, hb⟩, rfl⟩
  intro i j hij
  have h := hA₀ A hmem i j hij
  rwa [Units.val_mul, Units.val_mul]

end Hom

section Rank

variable {G : Type} [Group G] [Finite G] {m : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
  {ψ : SpecialLinearGroup (Fin (m + 1)) F →* G}

theorem sub_one_le_twoLocalRank {p : ℕ} (hp : p.Prime) (hpK : p ∣ Nat.card F - 1) (hm : 1 ≤ m)
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F)) :
    m - 1 ≤ LargeEvenTwoLocalRank p G := by
  have hd : 2 ≤ m + 1 := by omega
  set E₀ : Subgroup (SpecialLinearGroup (Fin (m + 1)) F) :=
    (TypeA.evalOne (p := p) (K := F) hd).ker.map (TypeA.diagSL p (m + 1) F) with hE₀
  have hE₀el : IsElemAbelian p E₀ := TypeA.isElemAbelian_map_diagSL _
  have hE₀card : Nat.card E₀ = p ^ (m + 1 - 2) := by
    rw [hE₀, Subgroup.card_map_of_injective TypeA.diagSL_injective,
      TypeA.card_ker_evalOne hp hpK hd]
  have hscal : ∀ g ∈ E₀, g ∈ scalars (m + 1) F → g = 1 := by
    rintro _ ⟨u, hu, rfl⟩ hgs
    obtain ⟨c, -, hc⟩ := mem_scalars.mp hgs
    have hu1 : (u : Fin (m + 1) → rootsOfUnity p F) ⟨1, by omega⟩ = 1 := hu
    have h1 := congrArg
      (fun M : Matrix (Fin (m + 1)) (Fin (m + 1)) F => M ⟨1, by omega⟩ ⟨1, by omega⟩) hc
    simp only [TypeA.coe_diagSL, diagonal_apply_eq, scalar_apply, TypeA.rootEnt, hu1] at h1
    have hc1 : (c : F) = 1 := by rw [← h1]; rfl
    ext i j
    rw [hc, hc1, map_one]
    rfl
  have hinj : Function.Injective (ψ.comp E₀.subtype) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    exact Subtype.ext (hscal g g.2 (by rw [scalars_eq_center]; exact hker hg))
  have hEcard : Nat.card (E₀.map ψ) = p ^ (m + 1 - 2) := by
    have hrange : (ψ.comp E₀.subtype).range = E₀.map ψ := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← hrange, ← hE₀card]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hEel : IsElemAbelian p (E₀.map ψ) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨_, x, hx, rfl⟩ := a
      obtain ⟨_, y, hy, rfl⟩ := b
      apply Subtype.ext
      change ψ x * ψ y = ψ y * ψ x
      rw [← map_mul, ← map_mul, TableB.IsElemAbelian.comm hE₀el hx hy]
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hE₀el.2 x hx, map_one]
  have h01 : (⟨0, by omega⟩ : Fin (m + 1)) ≠ ⟨1, by omega⟩ := by simp
  set U₀ : Subgroup (SpecialLinearGroup (Fin (m + 1)) F) :=
    (SpecialLinearGroup.transvectionHom h01 : Multiplicative F →* _).range with hU₀
  have hN : E₀ ≤ Subgroup.normalizer (U₀ : Set (SpecialLinearGroup (Fin (m + 1)) F)) :=
    TypeA.le_normalizer_rootGroup (TypeA.diagonal_of_mem_map_diagSL _) h01
  have hU2 : IsPGroup 2 (U₀.map ψ) := by
    refine IsPGroup.map (fun g => ⟨1, ?_⟩) ψ
    obtain ⟨_, c, rfl⟩ := g
    apply Subtype.ext
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [SpecialLinearGroup.transvectionHom_apply, pow_two,
      ← SpecialLinearGroup.transvection_add, CharTwo.add_self_eq_zero,
      SpecialLinearGroup.transvection_coeff_zero]
  have hU1 : U₀.map ψ ≠ ⊥ := by
    intro hbot
    have hmem : ψ (SpecialLinearGroup.transvection h01 (1 : F)) ∈ U₀.map ψ :=
      ⟨_, ⟨Multiplicative.ofAdd 1, by rw [SpecialLinearGroup.transvectionHom_apply, toAdd_ofAdd]⟩,
        rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact one_ne_zero (InnerDiagA.eq_zero_of_transvection_mem_center h01 (hker hmem))
  have hEN : E₀.map ψ ≤ Subgroup.normalizer ((U₀.map ψ : Subgroup G) : Set G) :=
    (Subgroup.map_mono hN).trans (Subgroup.le_normalizer_map ψ)
  have hk := TableB.le_pRank_of_le hp.one_lt hEN hEel hEcard
  have h := TableB.le_twoLocalRank hp.one_lt ⟨U₀.map ψ, hU1, hU2, rfl⟩ hk
  have hmm : m + 1 - 2 = m - 1 := by omega
  rwa [hmm] at h

end Rank

end RootPlaneA

section Family

theorem ggBstarToralPSLInput_holds : GGBstarToralPSLInput := by
  intro G _ _ p B Bs x L D J m f ψ hctx hC hpq
  have hm : 2 ≤ m := hctx.2.2.2.1.2
  have hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)) :=
    hctx.2.2.2.2.1.2
  have hf : 1 ≤ f := hctx.2.2.2.1.1.2.1
  have hp := hctx.prime
  have hpK : p ∣ Nat.card (GaloisField 2 f) - 1 := by
    rw [GaloisField.card 2 f (by omega)]
    exact hpq
  have hCψ : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hctx.range_eq]
    exact hC
  have hinn : ∀ b ∈ Bs, ∃ A : GL (Fin (m + 1)) (GaloisField 2 f),
      ∀ u, b⁻¹ * ψ u * b = ψ (InnerDiagA.conjSL A u) := fun b hb =>
    RootPlaneA.exists_gl_of_psiInnerDiag hm hker (hctx.2.2.2.2.2.2.1.2 b hb)
  have hBcard : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hctx.sstar.1.2.1
  have hBBs : Nat.card B ≤ Nat.card Bs := Subgroup.card_le_of_le hctx.bstar.1
  have hr4 : 4 ≤ LargeEvenTwoLocalRank p G := hctx.beta.2.2.2
  have hrm : m - 1 ≤ LargeEvenTwoLocalRank p G :=
    RootPlaneA.sub_one_le_twoLocalRank (F := GaloisField 2 f) hp hpK (by omega) hker
  refine RootPlaneA.ggBstarToralA_of_card hm hker hCψ hctx.bstar.2.1 hinn hp hctx.ne_two hpK
    ?_ ?_
  · calc p ^ (m + 1 - 2) ≤ p ^ LargeEvenTwoLocalRank p G :=
          Nat.pow_le_pow_right hp.pos (by omega)
      _ = Nat.card B := hBcard.symm
      _ ≤ Nat.card Bs := hBBs
  · calc p ^ 3 ≤ p ^ LargeEvenTwoLocalRank p G := Nat.pow_le_pow_right hp.pos (by omega)
      _ = Nat.card B := hBcard.symm
      _ ≤ Nat.card Bs := hBBs

theorem ggRootPlaneInputOn_pslSplit_holds : GGRootPlaneInputOn GGPSLSplit :=
  ggRootPlaneInputOn_pslSplit ggBstarToralPSLInput_holds

theorem ggRootPlaneInput_of_notPSLSplit
    (hrest : GGRootPlaneInputOn fun t n f p => ¬ GGPSLSplit t n f p) : GGRootPlaneInput :=
  ggRootPlaneInput_of_pslSplit ggBstarToralPSLInput_holds hrest

end Family

end CFSG.StandardType
