module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosDefs
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairChevalley
public import CFSG.ClassicalInvolution.WeakCT.Main

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.ModelFacts CFSG.Timmesfeld

open scoped MatrixGroups

section TagPairE

private theorem linearBlockStandardPair_map_rankOne {K : Type} [Group K]
    {D : UniversalRootDatum K} {F : Type} [Field F] [Finite F]
    {x : (Fin D.rank → ℤ) → F → K}
    {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : Steinberg.CommOrder (Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}
    (hE : Steinberg.ChevalleyExtras D F x C O) (hdiv : D.divisible = ∅) {i j k : Fin D.rank}
    (hij : i ≠ j) (hcij : D.cartan i j = -1) (hcji : D.cartan j i = -1)
    (hk : ¬ (3 : ℤ) ∣ D.cartan i k + 2 * D.cartan j k)
    {G : Type} [Group G] (ψ : K →* G) (hψ : ψ.ker ≤ Subgroup.center K) :
    ∃ W : Subgroup G, LinearBlockStandardPair F W
      ((ggRootLevi D (Pi.single i 1)).map ψ) ((ggRootLevi D (Pi.single j 1)).map ψ) := by
  obtain ⟨emb, hinj, -, hx⟩ := exists_sl3Levi hE hdiv hij hcij hcji hk
  have hset : ∀ γ ∈ D.roots, (D.rootGroup γ : Set K) = Set.range (x γ) := fun γ hγ =>
    Set.ext fun g => (hE.param γ hγ).1 g
  have hΦ := isCTRootSystem D.isFiniteType D.divisible
  have hneg : ∀ l : Fin D.rank, -Pi.single l 1 ∈ D.roots := fun l =>
    CFSG.LieType.Steinberg.OfCartan.neg_mem_roots D.isFiniteType (hΦ.single_mem l)
  have hker : (ψ.comp emb).ker ≤ Subgroup.center SL(3, F) := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro g
    have hmem : emb z ∈ ψ.ker := by
      show ψ (emb z) = 1
      exact hz
    have hcent : emb z ∈ Subgroup.center K := hψ hmem
    apply hinj
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.mp hcent (emb g)
  have hmap : ∀ γ ∈ D.roots,
      (((D.rootGroup γ).map ψ : Subgroup G) : Set G) = Set.range (fun c => ψ (x γ c)) := by
    intro γ hγ
    ext g
    constructor
    · intro hg
      change g ∈ Subgroup.map ψ (D.rootGroup γ) at hg
      rw [Subgroup.mem_map] at hg
      obtain ⟨y, hy, rfl⟩ := hg
      obtain ⟨c, hc⟩ := (Set.ext_iff.mp (hset γ hγ) y).mp hy
      exact ⟨c, by show ψ (x γ c) = ψ y; rw [hc]⟩
    · rintro ⟨c, rfl⟩
      change ψ (x γ c) ∈ Subgroup.map ψ (D.rootGroup γ)
      rw [Subgroup.mem_map]
      exact ⟨x γ c, (Set.ext_iff.mp (hset γ hγ) (x γ c)).mpr ⟨c, rfl⟩, rfl⟩
  have hbridge : ∀ c, (ψ.comp emb) (tv 0 1 c) = ψ (x (Pi.single i 1) c) ∧
      (ψ.comp emb) (tv 1 0 c) = ψ (x (-Pi.single i 1) c) ∧
      (ψ.comp emb) (tv 1 2 c) = ψ (x (Pi.single j 1) c) ∧
      (ψ.comp emb) (tv 2 1 c) = ψ (x (-Pi.single j 1) c) := by
    intro c
    exact ⟨by rw [MonoidHom.comp_apply, (hx c).1],
      by rw [MonoidHom.comp_apply, (hx c).2.1],
      by rw [MonoidHom.comp_apply, (hx c).2.2.1],
      by rw [MonoidHom.comp_apply, (hx c).2.2.2]⟩
  have h := linearBlockStandardPair_rankOne
    (X := fun γ => (D.rootGroup γ).map ψ) (x := fun γ c => ψ (x γ c))
    (hmap _ (hΦ.single_mem i)) (hmap _ (hneg i))
    (hmap _ (hΦ.single_mem j)) (hmap _ (hneg j))
    (ψ.comp emb) hker hbridge
  exact ⟨(ψ.comp emb).range, by
    simpa only [rankOne, ggRootLevi, Subgroup.map_sup] using h⟩

theorem ggTagE_adjStdPair {t : StatedLieTag} {n f : ℕ} (ht : t = .E6 ∨ t = .E7 ∨ t = .E8)
    (hadm : StatedLieAdmissible t n 2 f) :
    ∃ a b : Fin (ggU t n f).D.rank,
      (coxeterMatrix (ggU t n f).D.isFiniteType).M a b = 3 ∧
        ∀ {G : Type} [Group G] (ψ : (ggU t n f).K →* G),
          ψ.ker ≤ Subgroup.center (ggU t n f).K →
            ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 2 f) W
              ((ggRootLevi (ggU t n f).D (Pi.single a 1)).map ψ)
              ((ggRootLevi (ggU t n f).D (Pi.single b 1)).map ψ) := by
  rcases ht with rfl | rfl | rfl
  ·
    have hD : (ggU .E6 n f).D = Steinberg.Minuscule.e6Datum (GaloisField 2 f) := rfl
    rw [hD]
    have hcij : Blueprint.Chevalley.Tag.cartan .E6
        ⟨0, by show 0 < 6; decide⟩ ⟨2, by show 2 < 6; decide⟩ = -1 := by decide
    have hcji : Blueprint.Chevalley.Tag.cartan .E6
        ⟨2, by show 2 < 6; decide⟩ ⟨0, by show 0 < 6; decide⟩ = -1 := by decide
    have hM : (coxeterMatrix (Steinberg.Minuscule.e6Datum (GaloisField 2 f)).isFiniteType).M
        ⟨0, by show 0 < 6; decide⟩ ⟨2, by show 2 < 6; decide⟩ = 3 := by
      simp only [coxeterMatrix, TauCeti.coxeterMatrixOfCartanMatrix_apply, hcij, hcji]
      norm_num
    obtain ⟨O⟩ := Steinberg.nonempty_commOrder_ofCartan
      (Steinberg.Minuscule.e6Datum (GaloisField 2 f)).isFiniteType
      (Dv := (Steinberg.Minuscule.e6Datum (GaloisField 2 f)).divisible) rfl
    have hE := Steinberg.Minuscule.e6_chevalleyExtras (GaloisField 2 f) O _
      (Steinberg.Minuscule.e6Data_valid.commutatorFormula_commC (GaloisField 2 f)
        Steinberg.Minuscule.posDef_cartan_E6 _
        (Steinberg.Minuscule.roots_eq Steinberg.Minuscule.isFiniteType_cartan_E6) O)
    refine ⟨⟨0, by show 0 < 6; decide⟩, ⟨2, by show 2 < 6; decide⟩, hM, ?_⟩
    intro G _ ψ hψ
    exact linearBlockStandardPair_map_rankOne hE rfl (i := ⟨0, by show 0 < 6; decide⟩)
      (j := ⟨2, by show 2 < 6; decide⟩) (k := ⟨3, by show 3 < 6; decide⟩)
      (by intro h; have := congrArg Fin.val h; simp at this) hcij hcji
      (by
        show ¬ (3 : ℤ) ∣ Blueprint.Chevalley.Tag.cartan .E6 ⟨0, by decide⟩ ⟨3, by decide⟩ +
          2 * Blueprint.Chevalley.Tag.cartan .E6 ⟨2, by decide⟩ ⟨3, by decide⟩
        decide) ψ hψ
  ·
    have hD : (ggU .E7 n f).D = Steinberg.Minuscule.e7Datum (GaloisField 2 f) := rfl
    rw [hD]
    have hcij : Blueprint.Chevalley.Tag.cartan .E7
        ⟨0, by show 0 < 7; decide⟩ ⟨2, by show 2 < 7; decide⟩ = -1 := by decide
    have hcji : Blueprint.Chevalley.Tag.cartan .E7
        ⟨2, by show 2 < 7; decide⟩ ⟨0, by show 0 < 7; decide⟩ = -1 := by decide
    have hM : (coxeterMatrix (Steinberg.Minuscule.e7Datum (GaloisField 2 f)).isFiniteType).M
        ⟨0, by show 0 < 7; decide⟩ ⟨2, by show 2 < 7; decide⟩ = 3 := by
      simp only [coxeterMatrix, TauCeti.coxeterMatrixOfCartanMatrix_apply, hcij, hcji]
      norm_num
    obtain ⟨O⟩ := Steinberg.nonempty_commOrder_ofCartan
      (Steinberg.Minuscule.e7Datum (GaloisField 2 f)).isFiniteType
      (Dv := (Steinberg.Minuscule.e7Datum (GaloisField 2 f)).divisible) rfl
    have hE := Steinberg.Minuscule.e7_chevalleyExtras (GaloisField 2 f) O _
      (Steinberg.Minuscule.e7Data_valid.commutatorFormula_commC (GaloisField 2 f)
        Steinberg.Minuscule.posDef_cartan_E7 _
        (Steinberg.Minuscule.roots_eq Steinberg.Minuscule.isFiniteType_cartan_E7) O)
    refine ⟨⟨0, by show 0 < 7; decide⟩, ⟨2, by show 2 < 7; decide⟩, hM, ?_⟩
    intro G _ ψ hψ
    exact linearBlockStandardPair_map_rankOne hE rfl (i := ⟨0, by show 0 < 7; decide⟩)
      (j := ⟨2, by show 2 < 7; decide⟩) (k := ⟨3, by show 3 < 7; decide⟩)
      (by intro h; have := congrArg Fin.val h; simp at this) hcij hcji
      (by
        show ¬ (3 : ℤ) ∣ Blueprint.Chevalley.Tag.cartan .E7 ⟨0, by decide⟩ ⟨3, by decide⟩ +
          2 * Blueprint.Chevalley.Tag.cartan .E7 ⟨2, by decide⟩ ⟨3, by decide⟩
        decide) ψ hψ
  ·
    have hD : (ggU .E8 n f).D = Steinberg.Adjoint.e8Datum (GaloisField 2 f) := rfl
    rw [hD]
    have hcij : Blueprint.Chevalley.Tag.cartan .E8
        ⟨0, by show 0 < 8; decide⟩ ⟨2, by show 2 < 8; decide⟩ = -1 := by decide
    have hcji : Blueprint.Chevalley.Tag.cartan .E8
        ⟨2, by show 2 < 8; decide⟩ ⟨0, by show 0 < 8; decide⟩ = -1 := by decide
    have hM : (coxeterMatrix (Steinberg.Adjoint.e8Datum (GaloisField 2 f)).isFiniteType).M
        ⟨0, by show 0 < 8; decide⟩ ⟨2, by show 2 < 8; decide⟩ = 3 := by
      simp only [coxeterMatrix, TauCeti.coxeterMatrixOfCartanMatrix_apply, hcij, hcji]
      norm_num
    obtain ⟨O⟩ := Steinberg.nonempty_commOrder_ofCartan
      (Steinberg.Adjoint.e8Datum (GaloisField 2 f)).isFiniteType
      (Dv := (Steinberg.Adjoint.e8Datum (GaloisField 2 f)).divisible) rfl
    have hE := Steinberg.Adjoint.e8_chevalleyExtras (GaloisField 2 f) O _
      (Steinberg.Adjoint.commutatorFormula_commC Steinberg.Adjoint.e8Data_valid
        Steinberg.Adjoint.noG2_E8 _ (Steinberg.Adjoint.adjDatum_roots _ (GaloisField 2 f)) O)
    refine ⟨⟨0, by show 0 < 8; decide⟩, ⟨2, by show 2 < 8; decide⟩, hM, ?_⟩
    intro G _ ψ hψ
    exact linearBlockStandardPair_map_rankOne hE rfl (i := ⟨0, by show 0 < 8; decide⟩)
      (j := ⟨2, by show 2 < 8; decide⟩) (k := ⟨3, by show 3 < 8; decide⟩)
      (by intro h; have := congrArg Fin.val h; simp at this) hcij hcji
      (by
        show ¬ (3 : ℤ) ∣ Blueprint.Chevalley.Tag.cartan .E8 ⟨0, by decide⟩ ⟨3, by decide⟩ +
          2 * Blueprint.Chevalley.Tag.cartan .E8 ⟨2, by decide⟩ ⟨3, by decide⟩
        decide) ψ hψ

end TagPairE

end CFSG.StandardType
