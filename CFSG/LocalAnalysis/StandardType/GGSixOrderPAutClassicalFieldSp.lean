module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutClassicalInnerSp
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutGraphSp
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinberg
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldSpUSp
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutPSLRestField

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank Matrix CFSG.LieType.Universal.Symplectic
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

namespace OrdPFieldSp

variable {n : ℕ} {F : Type} [Field F]

theorem pow_eq_one_of_frameDiag {A₀ : StatedSp n F} {t : Fin n → Fˣ} {p : ℕ}
    (h : RestSp.frameDiag A₀ t ^ p = 1) (i : Fin n) : t i ^ p = 1 := by
  have h1 : ((RestSp.frameDiag A₀ t ^ p : StatedSp n F) : GL (Fin n ⊕ Fin n) F) = 1 := by
    rw [h]
    rfl
  have h2 : ((RestSp.frameDiag A₀ t : StatedSp n F) : GL (Fin n ⊕ Fin n) F) =
      (A₀ : GL (Fin n ⊕ Fin n) F) * TauCeti.diagGL (TableBSymp.pairedUnits t) *
        (A₀ : GL (Fin n ⊕ Fin n) F)⁻¹ := by
    simp only [RestSp.frameDiag, Subgroup.coe_mul, Subgroup.coe_inv, RestSp.coe_equiv_diagonal]
  rw [Subgroup.coe_pow, h2, conj_pow, ← map_pow] at h1
  have h3 : TauCeti.diagGL (TableBSymp.pairedUnits t ^ p) = 1 := by
    calc TauCeti.diagGL (TableBSymp.pairedUnits t ^ p) =
        (A₀ : GL (Fin n ⊕ Fin n) F)⁻¹ * ((A₀ : GL (Fin n ⊕ Fin n) F) *
          TauCeti.diagGL (TableBSymp.pairedUnits t ^ p) * (A₀ : GL (Fin n ⊕ Fin n) F)⁻¹) *
            (A₀ : GL (Fin n ⊕ Fin n) F) := by group
      _ = 1 := by rw [h1]; group
  have h4 := congrFun (TauCeti.diagGL_injective (h3.trans (map_one _).symm)) (Sum.inl i)
  simpa [TableBSymp.pairedUnits] using h4

theorem fieldSp_equiv_diagonal {σ : F ≃+* F} {t : Fin n → Fˣ} (ht : ∀ i, σ (t i) = t i) :
    fieldSp n F σ (equivStatedSp n F (TauCeti.GLSymplecticFin.diagonal t)) =
      equivStatedSp n F (TauCeti.GLSymplecticFin.diagonal t) := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_fieldSp, RestSp.coe_equiv_diagonal, TauCeti.diagGL_coe,
    Matrix.diagonal_map (map_zero σ)]
  congr 1
  funext x
  rcases x with i | i
  · exact ht i
  · change σ (((t i)⁻¹ : Fˣ) : F) = (((t i)⁻¹ : Fˣ) : F)
    rw [Units.val_inv_eq_inv_val, map_inv₀, ht i]

variable {f : ℕ}

theorem exists_conj_mem_centralizer_split {G : Type} [Group G] [Finite G] {p : ℕ}
    {Bs G₀ : Subgroup G} {ψ : StatedSp n (GaloisField 2 f) →* G}
    (hS : GGSixFusionSetting p Bs G₀ (Symplectic.rootDatum n (GaloisField 2 f)) .PSp n f ψ)
    (hp : p ∣ 2 ^ f - 1) {y : G} (hyM : y ∈ Subgroup.normalizer (G₀ : Set G)) (hyp : y ^ p = 1)
    (hyI : ¬ GGPsiInnerDiag (Symplectic.rootDatum n (GaloisField 2 f)) ψ y) :
    ∃ m ∈ Subgroup.normalizer (G₀ : Set G), m⁻¹ * y * m ∈ Subgroup.centralizer (Bs : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨hadm, hrank⟩, ⟨hrange, hker⟩, -, -⟩ := hS.presents
  have hf : 1 ≤ f := hadm.2.1
  have hrk : 2 ≤ n := hrank
  have hpp := hS.prime
  have hp2 := hS.ne_two
  have hC : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hrange]
    exact hS.centralizer_eq_bot
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hz := hker ha
    rw [Symplectic.center_eq,
      CFSG.LieType.SteinbergBR.EvenSp.statedScalars_subgroupOf_statedSp (by omega)] at hz
    exact Subgroup.mem_bot.mp hz
  have hπker : (proj n (GaloisField 2 f)).ker = Subgroup.center (StatedSp n (GaloisField 2 f)) := by
    rw [ker_proj]
    exact (Symplectic.center_eq n _).symm
  have hk : (proj n (GaloisField 2 f)).ker = ψ.ker :=
    hπker.trans (AutSt.ker_eq_center hker hC).symm
  set Θ : StatedProj (StatedSp n (GaloisField 2 f)) ≃* ψ.range :=
    AutSt.modelEquiv ψ (proj n (GaloisField 2 f)) proj_surjective hk with hΘdef
  have hΘ : ∀ x, ((Θ (proj n (GaloisField 2 f) x) : ψ.range) : G) = ψ x :=
    AutSt.modelEquiv_apply ψ _ proj_surjective hk
  have hyM' : y ∈ Subgroup.normalizer (ψ.range : Set G) := by
    rw [hrange]
    exact hyM
  set a : MulAut ψ.range := ψ.range.normalizerMonoidHom ⟨y⁻¹, inv_mem hyM'⟩ with hadef
  have ha : ∀ x : ψ.range, ((a x : ψ.range) : G) = y⁻¹ * x * y :=
    OrdPGraph.normalizerMonoidHom_inv_apply hyM'
  have hap : a ^ p = 1 := by
    rw [hadef, ← map_pow]
    have e : (⟨y⁻¹, inv_mem hyM'⟩ : Subgroup.normalizer (ψ.range : Set G)) ^ p = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow, inv_pow, hyp, inv_one]; rfl)
    rw [e, map_one]
  set β : MulAut (StatedProj (StatedSp n (GaloisField 2 f))) := MulAut.congr Θ.symm a with hβdef
  have hβ : ∀ x, Θ (β x) = a (Θ x) := fun x => by
    rw [hβdef, MulAut.congr_apply]
    simp
  have hβp : β ^ p = 1 := by
    rw [hβdef, ← map_pow, hap, map_one]
  have hrel : ∀ x x' : StatedSp n (GaloisField 2 f),
      β (proj n (GaloisField 2 f) x) = proj n (GaloisField 2 f) x' → y⁻¹ * ψ x * y = ψ x' := by
    intro x x' hxx'
    have e := congrArg (fun z => ((Θ z : ψ.range) : G)) hxx'
    simp only [hβ, ha, hΘ] at e
    exact e
  obtain ⟨A, σ, hAσ⟩ : ∃ (A : gsp n (GaloisField 2 f)) (σ : GaloisField 2 f ≃+* GaloisField 2 f),
      β = conjAut n (GaloisField 2 f) A * fieldAut n (GaloisField 2 f) σ := by
    rcases (show 3 ≤ n ∨ n = 2 by omega) with h3 | rfl
    · exact (automorphism_generation (K := GaloisField 2 f) h3).2 β
    · exact RootDetectSp.sp_two_form_of_pow_eq_one (hpp.odd_of_ne_two hp2) β hβp
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    rw [map_one, mul_one] at hAσ
    obtain ⟨g, hg⟩ := RootDetectSp.exists_sp_conj_eq A
    apply hyI
    have hcent : y * ψ g ∈ Subgroup.centralizer (ψ.range : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨x, rfl⟩
      have e := hrel x (g * x * g⁻¹) (by rw [hAσ, conjAut_proj, hg])
      rw [map_mul, map_mul, map_inv] at e
      calc ψ x * (y * ψ g) = y * (y⁻¹ * ψ x * y) * ψ g := by group
        _ = y * (ψ g * ψ x * (ψ g)⁻¹) * ψ g := by rw [e]
        _ = y * ψ g * ψ x := by group
    rw [hC, Subgroup.mem_bot] at hcent
    have hy : y = ψ g⁻¹ := by
      rw [map_inv]
      exact eq_inv_of_mul_eq_one_left hcent
    refine ⟨y⁻¹, ψ.range.inv_mem ⟨g⁻¹, hy.symm⟩, fun γ _ => ⟨1, one_mem _, fun z _ => ?_⟩⟩
    simp
  obtain ⟨hσo, H, hH⟩ := RecipeFieldSpU.conjAut_mul_fieldAut_of_pow_eq_one
    (K := GaloisField 2 f) (by omega) hpp A σ hσ1 (by rw [← hAσ]; exact hβp)
  have hσp : σ ^ p = 1 := hσo ▸ pow_orderOf_eq_one σ
  obtain ⟨h, hh⟩ := RootDetectSp.exists_sp_conj_eq H
  obtain ⟨A₀, hA₀⟩ := spFrame_core hf hrk ψ hker hC hpp hp2 hS.elem hS.innerDiag hp
  refine ⟨ψ (h * A₀⁻¹), Subgroup.le_normalizer (hrange ▸ ⟨_, rfl⟩), ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  obtain ⟨t, rfl⟩ := hA₀ b hb
  have hbp : RestSp.frameDiag A₀ t ^ p = 1 :=
    hinj (by rw [map_pow, map_one]; exact hS.elem.2 _ hb)
  have ht : ∀ i, σ (t i) = t i := fun i => OrdPRest.ringAut_fix_of_pow_eq_one hpp hσp
    (by rw [← Units.val_pow_eq_pow_val, pow_eq_one_of_frameDiag hbp i, Units.val_one])
  obtain ⟨D, hD⟩ : ∃ D : StatedSp n (GaloisField 2 f),
      D = equivStatedSp n (GaloisField 2 f) (TauCeti.GLSymplecticFin.diagonal t) := ⟨_, rfl⟩
  have hfix : β (proj n (GaloisField 2 f) (h * D * h⁻¹)) =
      proj n (GaloisField 2 f) (h * D * h⁻¹) := by
    have e0 : conjAut n (GaloisField 2 f) H (proj n (GaloisField 2 f) D) =
        proj n (GaloisField 2 f) (h * D * h⁻¹) := by
      rw [conjAut_proj, hh]
    have e1 : (conjAut n (GaloisField 2 f) H)⁻¹ (proj n (GaloisField 2 f) (h * D * h⁻¹)) =
        proj n (GaloisField 2 f) D := by
      rw [← e0, ← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
    rw [hAσ, hH, MulAut.mul_apply, MulAut.mul_apply, e1, fieldAut_proj, hD,
      fieldSp_equiv_diagonal ht, ← hD, e0]
  have hcomm : y * ψ (h * D * h⁻¹) = ψ (h * D * h⁻¹) * y := by
    calc y * ψ (h * D * h⁻¹) = y * (y⁻¹ * ψ (h * D * h⁻¹) * y) := by rw [hrel _ _ hfix]
      _ = ψ (h * D * h⁻¹) * y := by group
  have hb' : ψ (RestSp.frameDiag A₀ t) =
      (ψ (h * A₀⁻¹))⁻¹ * ψ (h * D * h⁻¹) * ψ (h * A₀⁻¹) := by
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    rw [RestSp.frameDiag, ← hD]
    group
  rw [hb']
  calc (ψ (h * A₀⁻¹))⁻¹ * ψ (h * D * h⁻¹) * ψ (h * A₀⁻¹) *
        ((ψ (h * A₀⁻¹))⁻¹ * y * ψ (h * A₀⁻¹)) =
      (ψ (h * A₀⁻¹))⁻¹ * (ψ (h * D * h⁻¹) * y) * ψ (h * A₀⁻¹) := by group
    _ = (ψ (h * A₀⁻¹))⁻¹ * (y * ψ (h * D * h⁻¹)) * ψ (h * A₀⁻¹) := by rw [hcomm]
    _ = (ψ (h * A₀⁻¹))⁻¹ * y * ψ (h * A₀⁻¹) *
        ((ψ (h * A₀⁻¹))⁻¹ * ψ (h * D * h⁻¹) * ψ (h * A₀⁻¹)) := by group

end OrdPFieldSp

section Family

theorem ggOrdPFieldConj_PSp_split : ∀ (G : Type) [Group G] [Finite G] (p : ℕ)
    (Bs G₀ : Subgroup G) (n f : ℕ) (ψ : (ggU .PSp n f).K →* G),
    GGSixFusionSetting p Bs G₀ (ggU .PSp n f).D .PSp n f ψ → p ∣ 2 ^ f - 1 →
    ∀ y ∈ Subgroup.normalizer (G₀ : Set G), orderOf y = p →
      ¬ GGPsiInnerDiag (ggU .PSp n f).D ψ y →
      ∃ m ∈ Subgroup.normalizer (G₀ : Set G), m⁻¹ * y * m ∈ Subgroup.centralizer (Bs : Set G) := by
  intro G _ _ p Bs G₀ n f ψ hS hp y hyM hyo hyI
  have hyp : y ^ p = 1 := hyo ▸ pow_orderOf_eq_one y
  exact OrdPFieldSp.exists_conj_mem_centralizer_split hS hp hyM hyp hyI

@[expose] def GGOrdPFieldConjPSpNonsplit : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (Bs G₀ : Subgroup G) (n f : ℕ)
    (ψ : (ggU .PSp n f).K →* G),
    GGSixFusionSetting p Bs G₀ (ggU .PSp n f).D .PSp n f ψ →
    GGTwoLocalRankFour p (Subgroup.normalizer (G₀ : Set G)) → ¬ p ∣ 2 ^ f - 1 →
    ∀ y ∈ Subgroup.normalizer (G₀ : Set G), orderOf y = p → GGPsiDiagField (ggU .PSp n f).D ψ y →
      ¬ GGPsiInnerDiag (ggU .PSp n f).D ψ y →
      ∃ m ∈ Subgroup.normalizer (G₀ : Set G), m⁻¹ * y * m ∈ Subgroup.centralizer (Bs : Set G)

theorem ggOrdPFieldConjAt_PSp_of_nonsplit (h : GGOrdPFieldConjPSpNonsplit) :
    GGOrdPFieldConjAt .PSp := by
  intro G _ _ p Bs G₀ n f ψ hS h24 y hyM hyo hDF hyI
  by_cases hpq : p ∣ 2 ^ f - 1
  · exact ggOrdPFieldConj_PSp_split G p Bs G₀ n f ψ hS hpq y hyM hyo hyI
  · exact h G p Bs G₀ n f ψ hS h24 hpq y hyM hyo hDF hyI

end Family

end CFSG.StandardType
