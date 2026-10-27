module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddQ7U3Core
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8R95B0U5
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8R95B0E1
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8R95B0E2
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8R95B0U1
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8R95B0U3
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.U3OddModel
import CFSG.Adapters.LieModelSimple

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg
  CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.U3
  CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.L3Leaves
  CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.Q7U3
open CFSG.Blueprint (LieModel)

private theorem r95_isSL2Cover_prime_eq {X : Type} [Group X] {p q f : ℕ} (hpq : p = q)
    (h : IsSL2Cover X p f) : IsSL2Cover X q f := by
  rw [← hpq]
  exact h

theorem r95_u3_main_SU {F : Type} [Field F] [Finite F] {p f : ℕ}
    [Fact p.Prime] [CharP F p] (hF : Nat.card F = (p ^ f) ^ 2)
    [IsSimpleGroup (SU (unitaryInvolution F p f) 3)]
    (hst : CFSG.Open.StatedClassicalModel (SU (unitaryInvolution F p f) 3) .PSU 3 p f)
    (hp2 : p ≠ 2) (hq3 : p ^ f % 3 = 1)
    (hcyc : ∀ P : Subgroup (SU (unitaryInvolution F p f) 3), IsPGroup 3 P → IsCyclic P)
    {E : Subgroup (SU (unitaryInvolution F p f) 3)} (hE : HasL32Quot E)
    {D R : Subgroup (SU (unitaryInvolution F p f) 3)} (hDE : D ≤ E) (hRE : R ≤ E)
    (hD : Nat.card D = 3) (hR7 : IsPGroup 7 R) (hR1 : R ≠ ⊥)
    (hDR : D ≤ Subgroup.normalizer (R : Set (SU (unitaryInvolution F p f) 3)))
    {W : Subgroup (SU (unitaryInvolution F p f) 3)} (hEW : E ≤ W)
    (hND : Subgroup.normalizer (D : Set (SU (unitaryInvolution F p f) 3)) ≤ W) (hW : W ≠ ⊤) :
    p = 7 ∧ IsSL2Cover ↥(Opp 3 W) 7 f ∧ ¬ 2 ∣ W.index := by
  classical
  have hq2 : 2 ≤ p ^ f := two_le_prime_pow_of_card hF
  obtain ⟨ω, hω⟩ := exists_unit_orderOf_three hF hq2 hq3
  have hA0 : Nat.card (Subgroup.zpowers (tSU hF ω)) = 3 := by
    rw [Nat.card_zpowers, orderOf_injective _ (tSU_injective hF) ω, hω]
  obtain ⟨g, hg⟩ := exists_conj_eq_of_card_eq_three hcyc hD hA0
  have hEW' : E.map (MulAut.conj g).toMonoidHom ≤ W.map (MulAut.conj g).toMonoidHom :=
    Subgroup.map_mono hEW
  have hE' : HasL32Quot (E.map (MulAut.conj g).toMonoidHom) :=
    r95_hasL32Quot_map (MulAut.conj g) hE
  have hns : ¬ Group.IsSolvable ↥(W.map (MulAut.conj g).toMonoidHom) :=
    r95_not_isSolvable_of_hasL32Quot hE' hEW'
  have hW' : W.map (MulAut.conj g).toMonoidHom ≠ ⊤ := by
    intro htop
    apply hW
    have htop' : (⊤ : Subgroup (SU (unitaryInvolution F p f) 3)).map
        (MulAut.conj g).toMonoidHom = ⊤ :=
      Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective
    exact Subgroup.map_injective (MulAut.conj g).injective (htop.trans htop'.symm)
  have hNW' : normA0 hF ω ≤ W.map (MulAut.conj g).toMonoidHom := by
    show Subgroup.normalizer ((Subgroup.zpowers (tSU hF ω) : Subgroup _) : Set _) ≤
      W.map (MulAut.conj g).toMonoidHom
    rw [hg, ← Subgroup.map_equiv_normalizer_eq D (MulAut.conj g)]
    exact Subgroup.map_mono hND
  have hR7' : IsPGroup 7 (R.map (MulAut.conj g).toMonoidHom) :=
    hR7.map (MulAut.conj g).toMonoidHom
  have hR1' : R.map (MulAut.conj g).toMonoidHom ≠ ⊥ := by
    intro hbot
    exact hR1 ((Subgroup.map_eq_bot_iff_of_injective R (MulAut.conj g).injective).mp hbot)
  have hdR' : tSU hF ω ∈ Subgroup.normalizer
      ((R.map (MulAut.conj g).toMonoidHom : Subgroup (SU (unitaryInvolution F p f) 3)) :
        Set _) := by
    have hmap : D.map (MulAut.conj g).toMonoidHom ≤
        (Subgroup.normalizer (R : Set (SU (unitaryInvolution F p f) 3))).map
          (MulAut.conj g).toMonoidHom :=
      Subgroup.map_mono hDR
    rw [Subgroup.map_equiv_normalizer_eq R (MulAut.conj g)] at hmap
    exact hmap (hg ▸ Subgroup.mem_zpowers (tSU hF ω))
  have hcase : 13 ≤ p ^ f ∨ (p ^ f = 7 ∧ ∃ R' : Subgroup (SU (unitaryInvolution F p f) 3),
      R' ≤ W.map (MulAut.conj g).toMonoidHom ∧ IsPGroup p R' ∧ R' ≠ ⊥ ∧
      tSU hF ω ∈ Subgroup.normalizer (R' : Set (SU (unitaryInvolution F p f) 3))) := by
    by_cases hq13 : 13 ≤ p ^ f
    · exact Or.inl hq13
    · right
      have hlt : p ^ f < 13 := Nat.lt_of_not_le hq13
      have h7 : p ^ f = 7 := by
        obtain ⟨m, hm⟩ := odd_prime_pow (p := p) (f := f) hp2
        omega
      have hp7 : p = 7 := by
        have hf0 : f ≠ 0 := fun h0 => by
          rw [h0, pow_zero] at hq2
          omega
        exact (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_seven).1
          (h7 ▸ dvd_pow_self p hf0)
      refine ⟨h7, R.map (MulAut.conj g).toMonoidHom, Subgroup.map_mono (hRE.trans hEW), ?_,
        hR1', hdR'⟩
      exact hp7.symm ▸ hR7'
  have h5 : 5 ≤ p ^ f := by
    rcases hcase with h13 | ⟨h7, -⟩
    · omega
    · omega
  have hL := r95_isSL2Cover_range_embSU hF hp2 h5
  have hWz : W.map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ({zSU hF} : Set (SU (unitaryInvolution F p f) 3)) :=
    r95_u3_eq_centralizer hF hst hp2 hq3 hω hNW' hW' hns hcase
  have hEz : E.map (MulAut.conj g).toMonoidHom ≤
      Subgroup.centralizer ({zSU hF} : Set (SU (unitaryInvolution F p f) 3)) :=
    hEW'.trans (le_of_eq hWz)
  have hp7 := r95_u3_char_seven_of_le_centralizer hF hp2 hL hEz hE'
  have hLs : IsSL2Cover ↥(Opp 3 (W.map (MulAut.conj g).toMonoidHom)) p f := by
    rw [hWz, r95_u3_opp_centralizer hF hp2 hq3 hL hω]
    exact hL
  have hcov : IsSL2Cover ↥(Opp 3 (W.map (MulAut.conj g).toMonoidHom)) 7 f :=
    r95_isSL2Cover_prime_eq hp7 hLs
  have hindex : (W.map (MulAut.conj g).toMonoidHom).index = W.index :=
    Subgroup.index_map_equiv W (MulAut.conj g)
  have hodd : ¬ 2 ∣ W.index := by
    rw [← hindex, hWz]
    exact r95_u3_index_centralizer_odd hF hp2
  exact ⟨hp7, r95_isSL2Cover_opp_map (MulAut.conj g) W hcov, hodd⟩

theorem r95_gB_U3 {Q : Type} [Group Q] [Finite Q] {p f : ℕ}
    (hpf : p ^ f % 3 = 1) (hQ : LieModel Q .PSU 3 p f)
    (hcyc : ∀ P : Subgroup Q, IsPGroup 3 P → IsCyclic P) {E : Subgroup Q} (hE : HasL32Quot E)
    {W : Subgroup Q} (hEW : E ≤ W)
    (hNW : ∀ D : Subgroup Q, D ≤ E → Nat.card D = 3 → Subgroup.normalizer (D : Set Q) ≤ W)
    (hW : W ≠ ⊤) : p = 7 ∧ IsSL2Cover ↥(Opp 3 W) 7 f ∧ ¬ 2 ∣ W.index := by
  classical
  by_cases hp2 : p = 2
  · subst hp2
    exact (r95_gB_U3_even hQ hE).elim
  · have hst := hQ.statedClassicalModel_of_ne_zero (by norm_num : (3 : ℕ) ≠ 0)
    obtain ⟨F, _, _, _, _, hF, ⟨e⟩⟩ :=
      CFSG.AGLEmbeddingD2.McLaughlin.OddIndex.exists_mulEquiv_SU3 hst hpf
    have hstG := CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e hst
    haveI := CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hstG
    have hcycG : ∀ P : Subgroup (SU (unitaryInvolution F p f) 3), IsPGroup 3 P → IsCyclic P := by
      intro P hP
      have h2 := hcyc _ (hP.map e.symm.toMonoidHom)
      have e' := P.equivMapOfInjective e.symm.toMonoidHom e.symm.injective
      exact isCyclic_of_surjective e'.symm.toMonoidHom e'.symm.surjective
    obtain ⟨D, R, hDE, hRE, hD3, hR7, hR1, hDR⟩ := r95_exists_seven_normalizer hE
    have hND : Subgroup.normalizer (D : Set Q) ≤ W := hNW D hDE hD3
    have hDE' : D.map e.toMonoidHom ≤ E.map e.toMonoidHom := Subgroup.map_mono hDE
    have hRE' : R.map e.toMonoidHom ≤ E.map e.toMonoidHom := Subgroup.map_mono hRE
    have hD3' : Nat.card (D.map e.toMonoidHom) = 3 := by
      rw [Subgroup.card_map_of_injective e.injective, hD3]
    have hR7' : IsPGroup 7 (R.map e.toMonoidHom) := hR7.map e.toMonoidHom
    have hR1' : R.map e.toMonoidHom ≠ ⊥ := by
      intro hbot
      exact hR1 ((Subgroup.map_eq_bot_iff_of_injective R e.injective).mp hbot)
    have hDR' : D.map e.toMonoidHom ≤ Subgroup.normalizer
        ((R.map e.toMonoidHom : Subgroup (SU (unitaryInvolution F p f) 3)) : Set _) := by
      have hmap : D.map e.toMonoidHom ≤
          (Subgroup.normalizer (R : Set Q)).map e.toMonoidHom := Subgroup.map_mono hDR
      rwa [Subgroup.map_equiv_normalizer_eq R e] at hmap
    have hEW' : E.map e.toMonoidHom ≤ W.map e.toMonoidHom := Subgroup.map_mono hEW
    have hND' : Subgroup.normalizer
        ((D.map e.toMonoidHom : Subgroup (SU (unitaryInvolution F p f) 3)) : Set _) ≤
        W.map e.toMonoidHom := by
      have hmap : (Subgroup.normalizer (D : Set Q)).map e.toMonoidHom ≤
          W.map e.toMonoidHom := Subgroup.map_mono hND
      rwa [Subgroup.map_equiv_normalizer_eq D e] at hmap
    have hW' : W.map e.toMonoidHom ≠ ⊤ := by
      intro htop
      apply hW
      have htop' : (⊤ : Subgroup Q).map e.toMonoidHom = ⊤ :=
        Subgroup.map_top_of_surjective _ e.surjective
      exact Subgroup.map_injective (f := e.toMonoidHom) e.injective (htop.trans htop'.symm)
    have hE' : HasL32Quot (E.map e.toMonoidHom) := r95_hasL32Quot_map e hE
    obtain ⟨hp7, hcov, hodd⟩ :=
      r95_u3_main_SU hF hstG hp2 hpf hcycG hE' hDE' hRE' hD3' hR7' hR1' hDR' hEW' hND' hW'
    refine ⟨hp7, r95_isSL2Cover_opp_map e W hcov, ?_⟩
    have hindex : (W.map e.toMonoidHom).index = W.index := Subgroup.index_map_equiv W e
    rwa [hindex] at hodd

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
