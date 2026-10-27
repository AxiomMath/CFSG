module

public import CFSG.RankThree.PartTwo.Sec15.F153L3KOutNatCore
public import CFSG.RankThree.PartTwo.Sec15.F153L3KOutRed
public import CFSG.Quasithin.Background.SmithB42SL3Key
public import CFSG.Quasithin.Background.SmithB42SL3Base
public import CFSG.Adapters.RankThreeOutcomesReverse

open scoped MatrixGroups Matrix

public section

namespace CFSG.RankThree.PartTwo.Sec15.F153L3K.Out

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Setup.X7Sec CFSG.LocalAnalysis.ComponentInitial

theorem noOuterIrr_L3big
    {f : ℕ} (hf : 2 ≤ f) {Y : Type} [Group Y]
    (hY : Nonempty (Y ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 f))) :
    NoOuterIrrFFOffender Y := by
  classical
  intro W _ _ hW L E hq hirr ⟨e⟩ hN hne hel hquad hEL h4
  by_contra hcon
  have hEboff : Nat.card W ≤ Nat.card E * Nat.card (fixV E) := not_lt.1 hcon
  have hV' : ∀ w : W, w * w = 1 := hW
  haveI : Finite (MulAut W) :=
    Finite.of_injective (fun g : MulAut W => (g : W → W)) DFunLike.coe_injective
  have hodd : Odd (Nat.card (Subgroup.center ↥L)) :=
    Family.odd_card_center_of_irreducible hV' hirr.2
  have hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL 3 2 f :=
    CFSG.Assembly.RankThreeEven.statedClassicalModel_of_projSL (n := 3) (p := 2) (f := f)
      ⟨Nat.prime_two, by omega, by norm_num, by simp, by simp⟩ (e.trans hY.some)
  obtain ⟨F, iF, iFin, φ₀, hFc, hcov⟩ := X7Sec.exists_cover_of_model hq.1 hodd (by omega) hmodel
  obtain ⟨W₂, _, _, _, ⟨θ⟩⟩ := Layer.Actor.exists_binModel_of_binary hV'
  haveI : Nontrivial W := hirr.1
  haveI : Nontrivial W₂ := (θ.toEquiv.trans Multiplicative.toAdd).symm.nontrivial
  haveI : Fintype F := Fintype.ofFinite F
  have hFcard : Fintype.card F = 2 ^ f := by rw [Fintype.card_eq_nat_card]; exact hFc
  haveI hchar : CharP F 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hFc
  set A := E.map (binPsi θ).toMonoidHom with hAdef
  have hoff : Nat.card W₂ ≤ Nat.card ↥A * Nat.card {u : W₂ // ∀ a ∈ A, a u = u} := by
    rw [B42SL3.card_fix_map, Subgroup.card_map_of_injective (binPsi θ).injective,
      ← Layer.Actor.natCard_eq θ]
    exact hEboff
  haveI hAel : CFSG.IsElementaryAbelian 2 ↥A := (Layer.Actor.isElemAbelian2_iff_map θ E).1 hel
  have hA1 : A ≠ ⊥ := by
    rw [Ne, hAdef, Subgroup.map_eq_bot_iff_of_injective E (binPsi θ).injective]
    exact hne
  obtain ⟨ψ, hψ, E', hE'⟩ := B42SL3.natural_of_offender (B42SL3.repOf θ φ₀)
    (B42SL3.repOf_ker θ hcov) A (B42SL3.intertwines_map θ hcov.surjective hN) hf hFcard
    (B42SL3.repOf_irreducible θ hirr.2 hcov.surjective) hA1 (B42SL3.quad_map θ hquad) hoff
  have hAcard : Nat.card ↥A ≤ 4 := by
    rw [hAdef, Subgroup.card_map_of_injective (binPsi θ).injective]
    exact h4
  have hint := B42SL3.intertwines_map θ hcov.surjective hN
  have hall : ∀ g ∈ E, g = 1 := by
    intro g hg
    set a : W₂ ≃ₗ[ZMod 2] W₂ := binPsi θ g with hadef
    have haA : a ∈ A := Subgroup.mem_map_of_mem _ hg
    have haa : ∀ w, a (a w) = w := by
      intro w
      have h1 : g * g = 1 := by rw [← pow_two]; exact hel.2 g hg
      have h2 : a * a = 1 := by rw [hadef, ← map_mul, h1, map_one]
      exact LinearEquiv.congr_fun h2 w
    let a' : (Fin 3 → F) ≃+ (Fin 3 → F) := E'.symm.trans (a.toAddEquiv.trans E')
    have ha'apply : ∀ u, a' u = E' (a (E'.symm u)) := fun u => rfl
    have ha2 : ∀ u, a' (a' u) = u := by
      intro u
      rw [ha'apply, ha'apply, E'.symm_apply_apply, haa, E'.apply_symm_apply]
    have hnorm : ∀ s : Matrix.SpecialLinearGroup (Fin 3) F,
        ∃ s' : Matrix.SpecialLinearGroup (Fin 3) F,
          ∀ u, a' ((s : Matrix (Fin 3) (Fin 3) F) *ᵥ u) =
            (s' : Matrix (Fin 3) (Fin 3) F) *ᵥ a' u := by
      intro s
      obtain ⟨y, hy⟩ := hint a haA (ψ s)
      refine ⟨ψ y, fun u => ?_⟩
      have h1 : E' (B42SL3.repOf θ φ₀ (ψ s) (E'.symm u)) =
          (s : Matrix (Fin 3) (Fin 3) F) *ᵥ u := by
        rw [hE', hψ, E'.apply_symm_apply]
      have h2 : E'.symm ((s : Matrix (Fin 3) (Fin 3) F) *ᵥ u) =
          B42SL3.repOf θ φ₀ (ψ s) (E'.symm u) := by
        rw [← h1, E'.symm_apply_apply]
      rw [ha'apply, h2, hy (E'.symm u), hE']
      rfl
    have hrange : (Set.range fun u => a' u - u) = E' '' (Set.range fun w => a w - w) := by
      ext y
      constructor
      · rintro ⟨u, rfl⟩
        refine ⟨a (E'.symm u) - E'.symm u, ⟨E'.symm u, rfl⟩, ?_⟩
        show E' (a (E'.symm u) - E'.symm u) = a' u - u
        rw [map_sub, E'.apply_symm_apply, ha'apply]
      · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
        refine ⟨E' w, ?_⟩
        show a' (E' w) - E' w = E' (a w - w)
        rw [ha'apply, E'.symm_apply_apply, map_sub]
    have hrank : (Set.range fun u => a' u - u).ncard ≤ 4 := by
      rw [hrange, Set.ncard_image_of_injective _ E'.injective]
      exact (NatR.ncard_range_le_of_offender A haA hoff).trans hAcard
    obtain ⟨M, hM⟩ := NatCore.eq_matrix_of_natural_offender hf hFcard ha2 hnorm hrank
    have hmat : a = binPsi θ ((φ₀ (ψ M) : ↥L) : MulAut W) := by
      refine LinearEquiv.ext fun w => ?_
      apply E'.injective
      have h3 : E' (a w) = a' (E' w) := by rw [ha'apply, E'.symm_apply_apply]
      rw [h3, hM, ← hψ M, ← hE' (ψ M) w, hψ M]
      rfl
    have hgL : g = ((φ₀ (ψ M) : ↥L) : MulAut W) := (binPsi θ).injective hmat
    have hmem : g ∈ E ⊓ L := Subgroup.mem_inf.2 ⟨hg, by rw [hgL]; exact (φ₀ (ψ M)).2⟩
    rw [hEL] at hmem
    exact Subgroup.mem_bot.1 hmem
  exact hne (eq_bot_iff.2 fun g hg => Subgroup.mem_bot.2 (hall g hg))

end CFSG.RankThree.PartTwo.Sec15.F153L3K.Out
