module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_2.SmallSetup
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_2.SmallSixteen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_2.SmallEighteen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_2.SmallNoGraph
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_2.SmallTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_2.GraphLift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_2.Statement

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_2

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.ComponentInitial CFSG.QuasithinUnique.Setup
open scoped MatrixGroups Matrix

private theorem phi_eq_of_intertwines {I : Type} [CommGroup I]
    {F : Type} [Field F] {U : Type} [AddCommGroup U] [Module (ZMod 2) U]
    {L : Subgroup (MulAut I)} (θ : I ≃* Multiplicative U) (φ : SL(3, F) →* ↥L)
    (ρ : Representation (ZMod 2) SL(3, F) U)
    (hρ : ∀ g u, ρ g u = Layer.binPsi θ ((φ g : ↥L) : MulAut I) u)
    {x : MulAut I} {s s' : SL(3, F)}
    (h : X7a.Intertwines ρ (Layer.binPsi θ x) s s') :
    ((φ s' : ↥L) : MulAut I) = x * ((φ s : ↥L) : MulAut I) * x⁻¹ := by
  have hρs : ρ s = Layer.binPsi θ ((φ s : ↥L) : MulAut I) := LinearMap.ext fun u => hρ s u
  have hρs' : ρ s' = Layer.binPsi θ ((φ s' : ↥L) : MulAut I) :=
    LinearMap.ext fun u => hρ s' u
  have key : Layer.binPsi θ x * Layer.binPsi θ ((φ s : ↥L) : MulAut I) =
      Layer.binPsi θ ((φ s' : ↥L) : MulAut I) * Layer.binPsi θ x := by
    ext u
    have h' := h u
    rw [hρs, hρs'] at h'
    simpa [LinearEquiv.mul_apply] using h'
  have key' : x * ((φ s : ↥L) : MulAut I) = ((φ s' : ↥L) : MulAut I) * x := by
    have h' := key
    rw [← map_mul, ← map_mul] at h'
    exact (Layer.binPsi θ).injective h'
  calc ((φ s' : ↥L) : MulAut I)
      = ((φ s' : ↥L) : MulAut I) * x * x⁻¹ := by group
    _ = x * ((φ s : ↥L) : MulAut I) * x⁻¹ := by rw [key']

private theorem k14_2Small_aux
    {I : Type} [CommGroup I] [Finite I] (hI : ∀ w : I, w ^ 2 = 1)
    {X L : Subgroup (MulAut I)} (hLX : L ≤ X) (hLn : (L.subgroupOf X).Normal)
    (hirr : IsIrrOn L ⊤ ⊥) {e : ℕ} (he : e = 2 ∨ e = 4) (hS : IsSL3 ↥L e)
    (hm4 : E3.mParam X ≤ 4) :
    (∀ (S : Subgroup (MulAut I)) (x : MulAut I), IsSylowIn 2 S L →
      x ∈ Subgroup.normalizer (L : Set (MulAut I)) →
      x ∈ Subgroup.normalizer (S : Set (MulAut I)) →
      ∀ P : Subgroup (MulAut I), S17.IsMaxParabolicOver L S P →
        P.map (MulAut.conj x).toMonoidHom = P) ∧
    (E3.mParam X ≤ 2 →
      CFSG.LocalAnalysis.UniquenessCase.UC22.IsSL3 ↥L 2 ∧ Subgroup.center ↥L ≠ ⊥ ∧
        rk ↥(⊤ : Subgroup I) = 6 ∧ E3.mParam X = 2 ∧
        ∀ c : MulAut I, (∀ l ∈ L, c * l = l * c) → c ^ 3 = 1) := by
  classical
  haveI : Finite (MulAut I) :=
    Finite.of_injective (fun f : MulAut I => (f : I → I)) DFunLike.coe_injective
  haveI hperfL : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hS.1.1
  have hperfQ : Group.IsPerfect (↥L ⧸ Subgroup.center ↥L) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (Subgroup.center ↥L))
  haveI hsimpleQ : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hS.1.2
  have hnaQ : ∃ a b : (↥L ⧸ Subgroup.center ↥L), a * b ≠ b * a := by
    by_contra h
    push Not at h
    exact Group.IsPerfect.not_isMulCommutative (↥L ⧸ Subgroup.center ↥L) ⟨⟨h⟩⟩
  have hevQ : Even (Nat.card (↥L ⧸ Subgroup.center ↥L)) :=
    CFSG.GH74.even_card_of_nonabelian_simple hnaQ
  have hev : Even (Nat.card ↥X) := by
    have h1 : 2 ∣ Nat.card (↥L ⧸ Subgroup.center ↥L) := even_iff_two_dvd.mp hevQ
    have h2 : 2 ∣ Nat.card ↥L := h1.trans (Subgroup.card_quotient_dvd_card _)
    exact even_iff_two_dvd.mpr (h2.trans (Subgroup.card_dvd_of_le hLX))
  obtain ⟨F, iF, iFt, iFC, U, iU1, iU2, iUF, θ, φ, ρ, hF, hφ, hodd, hρ, hirrρ, hN, t, htX,
    htt, ht1, htrk⟩ := exists_rep_of_isSL3 hI hirr hS hev
  have hker : ∀ x : SL(3, F), ρ x = 1 → x ∈ LinearFlag.scalars 3 F := by
    intro x hx
    have h1 : ((Layer.binPsi θ) ((φ x : ↥L) : MulAut I) : U →ₗ[ZMod 2] U) = 1 := by
      have h2 : ρ x = ((Layer.binPsi θ) ((φ x : ↥L) : MulAut I) : U →ₗ[ZMod 2] U) :=
        LinearMap.ext fun u => hρ x u
      rw [← h2]
      exact hx
    have h1' : (Layer.binPsi θ) ((φ x : ↥L) : MulAut I) = 1 :=
      LinearEquiv.toLinearMap_injective h1
    exact hφ.ker_le x (Subtype.ext ((Layer.binPsi θ).injective (h1'.trans (map_one _).symm)))
  have hnt : ∃ x : SL(3, F), ρ x ≠ 1 := by
    refine ⟨X7a.up3 0 0 1, fun hx => ?_⟩
    have hφne : φ (X7a.up3 (0 : F) 0 1) ≠ 1 := by
      intro h
      obtain ⟨c, -, hc⟩ := hφ.ker_le _ h
      have h01 := congrFun (congrFun hc 0) 1
      simp [X7a.up3_coe, X7a.upMat, Matrix.scalar_apply] at h01
    have h1 : ((Layer.binPsi θ) ((φ (X7a.up3 0 0 1) : ↥L) : MulAut I) :
        U →ₗ[ZMod 2] U) = 1 := by
      have h2 : ρ (X7a.up3 0 0 1) =
          ((Layer.binPsi θ) ((φ (X7a.up3 0 0 1) : ↥L) : MulAut I) : U →ₗ[ZMod 2] U) :=
        LinearMap.ext fun u => hρ _ u
      rw [← h2]
      exact hx
    have h1' : (Layer.binPsi θ) ((φ (X7a.up3 0 0 1) : ↥L) : MulAut I) = 1 :=
      LinearEquiv.toLinearMap_injective h1
    exact hφne (Subtype.ext ((Layer.binPsi θ).injective (h1'.trans (map_one _).symm)))
  have ha2 : Layer.binPsi θ t * Layer.binPsi θ t = 1 := by
    rw [← map_mul, htt, map_one]
  have ha1 : Layer.binPsi θ t ≠ 1 := fun h =>
    ht1 ((Layer.binPsi θ).injective (h.trans (map_one _).symm))
  have hXN : X ≤ Subgroup.normalizer (L : Set (MulAut I)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLX).mp hLn
  have haN : ∀ s : SL(3, F), ∃ s', X7a.Intertwines ρ (Layer.binPsi θ t) s s' :=
    fun s => hN t (hXN htX) s
  have hrk : Module.finrank (ZMod 2) (LinearMap.range ((Layer.binPsi θ t).toLinearMap - 1)) ≤
      4 := by
    rw [htrk]
    exact hm4
  have hcase : IsTwistedNatural ρ ∨ IsTwistedHerm ρ := by
    rcases he with rfl | rfl
    · rcases sl3Four_cases_of_rank_le hF ρ hirrρ hnt hker (Layer.binPsi θ t) ha2 ha1 haN hrk
        with hnat | hherm | ⟨hdim, hz⟩ | ⟨hdim, hz, hR⟩
      · exact Or.inl hnat
      · exact Or.inr hherm
      · exfalso
        exact absurd
          (five_le_rank_of_finrank_sixteen hF ρ hirrρ hz hdim (Layer.binPsi θ t) ha2 ha1 haN)
          (by omega)
      · exfalso
        exact absurd
          (five_le_rank_of_finrank_eighteen hF ρ hirrρ hker hz hdim hR (Layer.binPsi θ t) ha2
            ha1 haN) (by omega)
    · exact Or.inl
        (Thm14_5.natural_of_rank_le hF (by norm_num) ρ hirrρ hnt hker (Layer.binPsi θ t) ha2
          ha1 haN (by omega))
  constructor
  ·
    intro S x hSyl hxL hxS P hP
    by_contra hmove
    obtain ⟨ν, hν, hgraph⟩ :=
      exists_graphType_of_moves (G := MulAut I) (L := L) (S := S) (P := P) (K := F) φ
        hφ.surjective (fun y hy => hφ.ker_le y hy) hodd hSyl hxL hxS hP hmove
    have hb : ∀ s : SL(3, F), X7a.Intertwines ρ (Layer.binPsi θ x) s (ν s) := by
      intro s
      obtain ⟨s', hs'⟩ := hN x hxL s
      have hφeq : ((φ s' : ↥L) : MulAut I) = ((φ (ν s) : ↥L) : MulAut I) := by
        rw [phi_eq_of_intertwines θ φ ρ hρ hs']
        exact (hν s).symm
      have hρeq : ρ s' = ρ (ν s) := by
        have h1 : ρ s' = ((Layer.binPsi θ) ((φ s' : ↥L) : MulAut I) : U →ₗ[ZMod 2] U) :=
          LinearMap.ext fun u => hρ s' u
        have h2 : ρ (ν s) =
            ((Layer.binPsi θ) ((φ (ν s) : ↥L) : MulAut I) : U →ₗ[ZMod 2] U) :=
          LinearMap.ext fun u => hρ (ν s) u
        rw [h1, h2, hφeq]
      intro u
      have hu := hs' u
      rw [hρeq] at hu
      exact hu
    exact not_isGraphType_of_intertwines ρ hcase (Layer.binPsi θ x) ν hb hgraph
  ·
    intro hm2
    rcases hcase with hnat | hherm
    · exact k14_2Small_two hI hLX hLn hirr he hS θ φ ρ hF hφ hρ hnat hm2
    · exfalso
      obtain ⟨hK, ψ, hψ, E, hE⟩ := hherm
      have h3 := Thm14_5.three_mul_le_finrank_range_of_herm (m := 1) le_rfl hK ρ ψ hψ E hE
        (Layer.binPsi θ t) ha2 ha1 haN
      have h3' : 3 ≤ E3.mParam X := by
        rw [← htrk]
        simpa using h3
      omega

theorem k14_2Small_holds :
    K14_2Small := by
  intro I _ _ hI X L hLX hLn hirr hS hm4
  rcases hS with hS | hS
  · exact k14_2Small_aux hI hLX hLn hirr (Or.inl rfl) hS hm4
  · exact k14_2Small_aux hI hLX hLn hirr (Or.inr rfl) hS hm4

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_2
