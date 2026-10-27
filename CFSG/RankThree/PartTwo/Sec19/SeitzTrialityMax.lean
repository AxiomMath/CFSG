module

public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityAB
public import CFSG.RankThree.PartOne.SEITZ7.D4Odd

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
open CFSG.RankThree.PartTwo.Sec11

namespace CFSG.RankThree.PartTwo.Sec19

section Generic

theorem maximal_of_equiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) {L : Subgroup G}
    (hmax : ∀ N : Subgroup H, L.map e.toMonoidHom ≤ N → N = L.map e.toMonoidHom ∨ N = ⊤) :
    ∀ N : Subgroup G, L ≤ N → N = L ∨ N = ⊤ := by
  intro N hN
  have hinj : Function.Injective e.toMonoidHom := e.injective
  have hsurj : Function.Surjective e.toMonoidHom := e.surjective
  rcases hmax (N.map e.toMonoidHom) (Subgroup.map_mono hN) with h | h
  · left
    exact Subgroup.map_injective hinj h
  · right
    apply Subgroup.map_injective hinj
    rw [h, Subgroup.map_top_of_surjective _ hsurj]

end Generic

section Max

variable {n : ℕ} {X : Type} [Field X] [Finite X] {σ : X ≃+* X}

theorem map_eC_Asub (P : D4Par n X σ) :
    (Asub σ).map (eC P).toMonoidHom =
      CFSG.RankThree.PartOne.SEITZ7.Asub σ.toRingHom P.sigma_cube_hom := by
  rw [← iotaA_range P]
  ext y
  constructor
  · rintro ⟨x, ⟨g, rfl⟩, rfl⟩
    exact ⟨g, ((eC P).apply_symm_apply _).symm⟩
  · rintro ⟨g, rfl⟩
    exact ⟨iotaA P g, ⟨g, rfl⟩, (eC P).apply_symm_apply _⟩

theorem map_eC_Bsub (P : D4Par n X σ) :
    (Bsub σ).map (eC P).toMonoidHom =
      CFSG.RankThree.PartOne.SEITZ7.Bsub σ.toRingHom P.sigma_cube_hom := by
  rw [Bsub_eq_range_etaB P]
  ext y
  constructor
  · rintro ⟨x, ⟨g, rfl⟩, rfl⟩
    exact ⟨g, ((eC P).apply_symm_apply _).symm⟩
  · rintro ⟨g, rfl⟩
    exact ⟨etaB P g, ⟨g, rfl⟩, (eC P).apply_symm_apply _⟩

theorem card_twisted (P : D4Par n X σ) :
    Nat.card (CFSG.LieType.Steinberg.TwistedD4.twistedGroup σ.toRingHom) =
      CFSG.RankThree.PartOne.SEITZ7.d4Order n := by
  rw [← Nat.card_congr (eC P).toEquiv]
  exact (triality_both_orientations_exact_finite_order 2 n Nat.prime_two P.one_le X P.card 1
    (Or.inl rfl) σ.toRingHom (fun c => by rw [pow_one]; exact P.frob c)).1

theorem ab_maximal (hgold : CFSG.Goldschmidt.TopStatement) (P : D4Par n X σ) (hn : 2 ≤ n) :
    ∀ N : Subgroup (C0 σ), Asub σ ⊔ Bsub σ ≤ N → N = Asub σ ⊔ Bsub σ ∨ N = ⊤ := by
  haveI := P.charP
  refine maximal_of_equiv (eC P) ?_
  rw [Subgroup.map_sup, map_eC_Asub P, map_eC_Bsub P]
  intro N' hN'
  exact CFSG.RankThree.PartOne.SEITZ7.core_max_tw hgold P.sigma_cube_hom hn P.card P.card_fix N'
    hN' ((Subgroup.card_subgroup_dvd_card N').trans (dvd_of_eq (card_twisted P)))
    (fun R _ hRn hodd =>
      CFSG.RankThree.PartOne.SEITZ7.odd_core_trivial_tw P.sigma_cube_hom hn P.card P.card_fix hN'
        hRn hodd)

end Max

end CFSG.RankThree.PartTwo.Sec19
