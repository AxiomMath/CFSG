module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLCx
public import CFSG.LocalAnalysis.StandardType.GGTableBUnit63Main
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorus
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenVac

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly CFSG.Blueprint CFSG.Open CFSG.ClassicalInvolution.Phan

variable {G : Type} [Group G] [Finite G]

theorem qTwoFrontRank_innerDiagOnLab_six {B Bs L D J : Subgroup G} {x : G}
    (hconf : GGConfig 3 B Bs x L D J)
    {F0 : Type} [Field F0] [Finite F0] (hcard : Nat.card F0 = 4)
    (e : L ⧸ Subgroup.center L ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin 6) F0 (2 ^ 1)))
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    GGInnerDiagOnLab GGUnitDvd63Label 3 Bs L := by
  classical
  obtain ⟨hthm, hstar, -⟩ := hconf
  obtain ⟨-, -, -, -, -, -, -, hstd⟩ := hthm
  obtain ⟨hL, lab', hlab', hraw'⟩ := hstd.1
  obtain ⟨R', instR', I', F', hsimple', hna', θ', -⟩ := largeEvenRawDatum_exists hraw'
  let R := LargeEvenProj (LargeEvenSUGroup (Fin 6) F0 (2 ^ 1))
  have hK : Nat.card F0 = (2 ^ 1) ^ 2 := by rw [hcard]; norm_num
  have hsimple : IsSimpleGroup R := by
    letI : Group R' := instR'
    haveI : IsSimpleGroup R' := hsimple'
    exact MulEquiv.isSimpleGroup (e.symm.trans θ')
  have hna : ∃ a b : R, a * b ≠ b * a := by
    obtain ⟨a', b', hab'⟩ := hna'
    refine ⟨(e.symm.trans θ').symm a', (e.symm.trans θ').symm b', ?_⟩
    intro h
    exact hab' (by simpa only [map_mul, MulEquiv.apply_symm_apply]
      using congrArg (e.symm.trans θ') h)
  refine ⟨hL, ⟨.twA, 5, 1⟩, ?_, ?_⟩
  · exact ⟨by norm_num, by norm_num, by decide⟩
  · refine ⟨F0, inferInstance, inferInstance, hK, ?_⟩
    refine ⟨hsimple, hna, e, ?_, ?_, hBsN, ?_⟩
    · exact ⟨⟨rfl, by norm_num, by norm_num, by norm_num⟩, rfl, rfl⟩
    · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
    · intro b hb
      let g : Subgroup.normalizer (L : Set G) := ⟨b⁻¹, hBsN (Bs.inv_mem hb)⟩
      refine ⟨ggLAut L e g, ?_, ?_⟩
      · apply CorFourTwoOpen.mem_conjImage_of_pow_unitary
          (K := F0) (n := 1) (d := 6) (p := 3) hK (by norm_num) (by norm_num)
          (by norm_num) Nat.prime_three (by norm_num) (by norm_num)
        have hb3 : b ^ 3 = 1 := hstar.2.1.2 b hb
        have hg3 : g ^ 3 = 1 := by
          apply Subtype.ext
          simp [g, hb3]
        rw [← map_pow, hg3, map_one]
      · intro l l' hll
        rw [ggLAut_apply L e g l]
        have hL' : L.normalizerMonoidHom g l = l' := by
          apply Subtype.ext
          rw [normalizerMonoidHom_coe]
          simpa [g] using hll.symm
        rw [hL']

theorem qTwoFrameL_rank {B Bs L D J : Subgroup G} {x : G} {𝒦 : Finset (Subgroup G)} {m : ℕ}
    (hm : 5 ≤ m) (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦)
    {F0 : Type} [Field F0] [Finite F0] (hcard : Nat.card F0 = 4)
    (e : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin m) F0 (2 ^ 1)))
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    3 ^ (m / 3 + 2) ≤ Nat.card (ggGamma L hBsN).range := by
  have hconf : GGConfig 3 B Bs x L D J := hcfg.1.1
  obtain ⟨hthm, -, -⟩ := id hconf
  obtain ⟨-, -, -, -, -, -, -, hstd⟩ := hthm
  have hL : commutator L = ⊤ := hstd.1.1
  have hK : Nat.card F0 = (2 ^ 1) ^ 2 := by rw [hcard]; norm_num
  by_cases hm6 : m = 6
  · subst m
    have hM : GGInnerDiagOnLab GGUnitDvd63Label 3 Bs L :=
      qTwoFrontRank_innerDiagOnLab_six hconf hcard e hBsN
    simpa using (card_range_ggGamma_unitDvd63 hconf hM hBsN).1
  · have hneq : (m, 2 ^ 1) ≠ (3, 2) := by
      rintro h
      have h1 : m = 3 := by simpa using congrArg Prod.fst h
      omega
    have hlift : GGTorusLift 3 (ggUnitaryTorusRank 3 m)
        (LargeEvenProj (LargeEvenSUGroup (Fin m) F0 (2 ^ 1))) :=
      ggTorusLift_unitary (K := F0) (n := 1) (d := m) (p := 3) hK le_rfl
        (by omega : 3 ≤ m) hneq
        Nat.prime_three (by norm_num)
    have hle := (card_range_ggGamma_bstar_ge hconf hL e hBsN hlift).1
    have hrank : m / 3 + 2 ≤ ggUnitaryTorusRank 3 m := by
      rw [ggUnitaryTorusRank]
      split_ifs with h3
      · omega
      · omega
    exact (Nat.pow_le_pow_right (by norm_num : 0 < 3) hrank).trans hle

end CFSG.StandardType.QTwo
