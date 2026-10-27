module

public import CFSG.RankThree.PartTwo.Sec12.Hering129KR1
import CFSG.RankThree.PartTwo.Sec13.Item134Dichotomy
public import CFSG.RankThree.PartTwo.Sec12.Hering129HMirror

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo


theorem gap129SymG2In_of (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (hKK : Gap129KFK)
    (hKL : Gap129KFLieIn) :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (b a : G)
      (K S : Subgroup G), Cfg129 G A c L b a K S → GTwoType129 L K →
      ∀ x ∈ D129 a b, x ∉ Subgroup.zpowers b →
        ∀ Y : Subgroup G, Core129 A c x Y → HasLieParamInRange Y →
        x ∈ L ∧ ∃ J : Subgroup G, JData129 A c L Y J ∧ b ∈ J ∧
          (Typ129I K Y → Nonempty (J ⧸ aschbacherSolvableCore 3 J ≃*
            L ⧸ aschbacherSolvableCore 3 L)) ∧
          (∀ r : TauCeti.PrimePower, Sec4.IsoGTwo (Y ⧸ CFSG.pCore 2 Y) r →
            Sec4.IsSLThreePiAt (J ⧸ aschbacherSolvableCore 3 J) r.card) ∧
          (∀ (r : TauCeti.PrimePower) (hr : (TauCeti.LieTypeIndex.trialityD4 r).Valid),
            Nonempty (Y ⧸ CFSG.pCore 2 Y ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 r, hr⟩).Group) →
            Sec4.IsSLThreePiAt (J ⧸ aschbacherSolvableCore 3 J) r.card) := by
  intro G _ _ A c L b a K S cfg hty x hxD hxb Y hY hrange
  obtain ⟨hcX, -, hXq⟩ := hKK G A c L b a K S cfg hty x hxD hxb
  have hXY := resCent_le_of_core h48 cfg hxD hxb hcX hXq hY
  obtain ⟨hD, -, hiso1, hiso2, hiso3⟩ :=
    hKL G A c L b a K S cfg hty x hxD hxb Y hY hXY hrange
  obtain ⟨J, hJ, hIJ, hJL, hJeq, hCeq, hxL, hbJ, hAJ, -⟩ :=
    sym_core h45 h48 cfg hxD hxb hY.1 hD
  obtain ⟨eIJ⟩ := Sec13.nonempty_quotTheta_equiv_of_eq_sup hIJ hJeq
  refine ⟨hxL, J, ⟨hJ, hJL, hIJ hD.mem, hAJ, hCeq, ?_⟩, hbJ, fun hI1 => ?_,
    fun r hr => isSLThreePiAt_congr eIJ (hiso2 r hr),
    fun r hr hr' => isSLThreePiAt_congr eIJ (hiso3 r hr hr')⟩
  · rw [inSubgroup_perfectResidual_normalizer_zpowers]
    exact hJeq
  · obtain ⟨e1⟩ := hiso1 hI1
    exact ⟨eIJ.symm.trans e1⟩

theorem gap129SymII_of_in (h1 : Sec4.Item4_1LargePrime) (h45 : Sec4.Item4_5)
    (h48 : Sec4.Item4_8) (hK : KFacts.KS12NormalizerMoves) (h125 : Item125BarC9)
    (hCl : Gap129ClaimG2M) (hKK : Gap129KFK) (hKL : Gap129KFLieIn) (hNI : KFNonIsoG2D4) :
    Gap129SymII := by
  intro G _ _ A c L b a K S cfg hty x hxD hxb hxL Y hY hII
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hrange := hasLieParamInRange_of_typ129II h1 cfg hII
  obtain ⟨q', ⟨hq', ⟨e1⟩⟩, ⟨hq'', ⟨e2⟩⟩⟩ := hII
  set r₀ : TauCeti.PrimePower :=
    ⟨q'.p, 3 * q'.exponent, q'.prime_p, Nat.mul_pos (by norm_num) q'.exponent_pos⟩ with hr₀
  obtain ⟨hcX, hSX, hXq⟩ := hKK G A c L b a K S cfg hty x hxD hxb
  have hXY := resCent_le_of_core h48 cfg hxD hxb hcX hXq hY
  obtain ⟨hD, hlt, -, hiso2, -⟩ := hKL G A c L b a K S cfg hty x hxD hxb Y hY hXY hrange
  have hIr : Sec4.IsSLThreePiAt (↥(resCent Y c) ⧸ aschbacherSolvableCore 3 ↥(resCent Y c))
      r₀.card := hiso2 r₀ ⟨hq'', ⟨e2⟩⟩
  obtain ⟨J, hcfg, hty', hbJ⟩ :=
    mirror_of_symData h45 h48 hK cfg hxD hxb hY.1 hD hlt (hSX.trans hXY) hIr ⟨hq'', ⟨e2⟩⟩
  obtain ⟨hbA, haA, haL, hb1, ha1, haB, hbL, hab, haD, -⟩ := cfg.point_facts
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := cfg.std.isE27.1
  have hDA : D129 a b ≤ A :=
    sup_le (Subgroup.zpowers_le.mpr haA) (Subgroup.zpowers_le.mpr hbA)
  have hxA : x ∈ A := hDA hxD
  have hx1 : x ≠ 1 := fun h => hxb (h ▸ Subgroup.one_mem _)
  have hbD' : b ∈ D129 b x := Subgroup.mem_sup_left (Subgroup.mem_zpowers b)
  have hbx : b ∉ Subgroup.zpowers x := fun h =>
    hxb (mem_of_mem_zpowers_of_ne_one (orderOf_eq_prime (hAe.2 x hxA) hx1) h hb1
      (Subgroup.mem_zpowers b))
  obtain ⟨Y'', hY''1, hY''c, htyp⟩ := hCl G A c J x b Y S hcfg r₀ hty' b hbD' hbx
  have hcore'' : Core129 A c b Y'' := core129_of h45 hK hcfg.std hcfg.list hbA hb1 hY''1 hY''c
  obtain ⟨hcX', -, hXq'⟩ := hKK G A c J x b Y S hcfg ⟨r₀, hty'⟩ b hbD' hbx
  have hXb'' : resCent Y b ≤ Y'' := resCent_le_of_core h48 hcfg hbD' hbx hcX' hXq' hcore''
  have hKb : K ≤ Subgroup.centralizer ({b} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt cfg.hK
  have hXp := isPerfect_resCent K x
  have hX1 : resCent K x ≠ ⊥ := fun h0 =>
    cfg.std.ne_one (Subgroup.mem_bot.mp (h0 ▸ hcX : c ∈ (⊥ : Subgroup G)))
  have hXb : resCent K x ≤ resCent Y b :=
    le_inSubgroup_perfectResidual_of_isPerfect (le_inf hXY ((resCent_le K x).trans
      (inf_le_left.trans hKb))) hXp
  have hYK : Y'' = K :=
    CFSG.RankThree.PartOne.EmbeddingFixedResidual.eq_of_perfect_le_of_mem_thetaComponentsAt
      Nat.prime_three hY''1 cfg.hK hX1 hXp (hXb.trans hXb'') ((resCent_le K x).trans inf_le_left)
  subst hYK
  rcases htyp with h1' | ⟨q₁, ⟨hq₁, ⟨e3⟩⟩, -⟩ | ⟨h4, -⟩ | h3
  · obtain ⟨e⟩ := h1'
    exact (hNI _ q' hq'' hq').false (e2.symm.trans (e.symm.trans e1))
  · exact (hNI _ q₁ hq'' hq₁).false (e2.symm.trans e3)
  · have hcard : r₀.card = q'.p ^ (3 * q'.exponent) := TauCeti.PrimePower.card_def r₀
    have hp2 : 2 ≤ q'.p := q'.prime_p.two_le
    have h3e : 3 ≤ 3 * q'.exponent := by have := q'.exponent_pos; omega
    have h8 : 2 ^ 3 ≤ q'.p ^ (3 * q'.exponent) :=
      (Nat.pow_le_pow_left hp2 3).trans (Nat.pow_le_pow_right (by omega) h3e)
    rcases h4 with h | h <;> omega
  · exact gap129NotIiiLcMinus_of h45 h125 G A c J x b Y S hcfg ⟨r₀, hty'⟩ b hbD' hbx hbJ _
      hcore'' h3

end CFSG.RankThree.PartTwo.Sec12
