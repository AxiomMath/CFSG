module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusSympSplit
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusSympNonsplit
import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticTorus
import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticBstar
import CFSG.LocalAnalysis.StandardType.KGLangS1ALinTypeDet
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGCentInnerDiagConcl
import CFSG.LocalAnalysis.ComponentInitial.DerivedFixedLayer
import CFSG.LocalAnalysis.ComponentInitial.BlockCentralQuotient

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial


private theorem q2cSp_torusLift {p : ℕ} {lab : LargeEvenLabel}
    (hΛ : LargeEvenInLambda2 lab) (htag : lab.tag = .B ∨ lab.tag = .C)
    (hp : p.Prime) (hp2 : p ≠ 2) (hsplit : LargeEvenSplit p lab) :
    LargeEvenLabelAll lab (fun R _ _ _ => 2 ≤ lab.n → GGTorusLift p lab.rank R) := by
  intro Q hQ
  obtain ⟨t, l, n⟩ := lab
  rcases htag with h | h <;> dsimp only at h <;> subst h
  all_goals
    dsimp only [LargeEvenRawDatum, LargeEvenRecipeSymplectic] at hQ ⊢
    obtain ⟨K, i1, i2, hK, hq⟩ := hQ
    refine ⟨K, i1, i2, hK, hq, ?_⟩
    intro h2n
    have hpq : p ∣ 2 ^ n - 1 := by
      rcases hsplit with hh | hh | hh | hh
      · exact hh.2
      · exact (hh.1 trivial).elim
      · rcases hh.1 with h' | h' <;> cases h'
      · have hn1 : n = 1 := hh.1
        exact absurd h2n (by rw [hn1]; norm_num)
    have hchar : CharP K 2 := charP_two_of_card hK
    have hpqK : p ∣ Nat.card K - 1 := by rw [hK]; exact hpq
    exact TableBSymp.ggTorusLift_symplectic (m := l) hp hp2 hpqK
      (le_trans (by norm_num : 1 ≤ 2) hΛ.2.1)

theorem q2cSp_block_structure {p d m : ℕ} {lab : LargeEvenLabel} (hd : 3 ≤ d)
    (hΛ : LargeEvenInLambda2 lab) (htag : lab.tag = .B ∨ lab.tag = .C)
    (hp : p.Prime) (hp2 : p ≠ 2) (hsplit : LargeEvenSplit p lab) :
    LargeEvenLabelAll lab (fun R _ I _ =>
      ∀ A : Subgroup (MulAut R), IsElemAbelian p A → (∀ a ∈ A, a ∈ I) →
      (∀ r : ℕ, GGTorusLift p r R → p ^ r ≤ Nat.card A) →
      p ^ 3 ≤ Nat.card A → p ^ (d - 1) ≤ Nat.card A → Nat.card A ≤ p ^ d →
      ∀ u ∈ A, orderOf u = p →
      ∀ J : Subgroup R, CFSG.Open.IsComponentOf J (ggAutFixedSubgroup u) →
        (∀ J' : Subgroup R, CFSG.Open.IsComponentOf J' (ggAutFixedSubgroup u) → J' = J) →
        (∀ a ∈ A, ∀ j ∈ J, a j ∈ J) →
        ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ m →
          Nonempty (↥J ⧸ Subgroup.center ↥J ≃*
            LargeEvenProj (LargeEvenSLGroup (Fin d) K)) →
          (2 ≤ lab.n →
            (∃ (a : ℕ) (F : Type) (_ : Field F) (_ : Finite F),
                Nat.card F = 2 ^ lab.n ∧ 2 ≤ a ∧ a ≤ lab.rank ∧
                Nonempty (↥J ⧸ Subgroup.center ↥J ≃*
                  LargeEvenProj (LargeEvenSLGroup (Fin a) F)))
            ∨ (∃ (b : ℕ) (F : Type) (_ : Field F) (_ : Finite F),
                Nat.card F = 2 ^ lab.n ∧ 2 ≤ b ∧ b ≤ lab.rank ∧
                Nonempty (↥J ⧸ Subgroup.center ↥J ≃* LargeEvenSpGroup F b))) ∧
          (lab.n = 1 → False)) := by
  intro Q hQ
  obtain ⟨t, l, n⟩ := lab
  rcases htag with h | h <;> dsimp only at h <;> subst h
  all_goals
    dsimp only [LargeEvenRawDatum, LargeEvenRecipeSymplectic] at hQ ⊢
    obtain ⟨K₀, iF, iFin, hK₀, hq⟩ := hQ
    refine ⟨K₀, iF, iFin, hK₀, hq, ?_⟩
    intro A hA hAI hbig h3 hlo hup u hu huo J hJ huniq hAJ K iK iFinK hK hne
    haveI : CharP K₀ 2 := charP_two_of_card hK₀
    have hl2 : 2 ≤ l := hΛ.2.1
    haveI : NeZero l := ⟨by omega⟩
    let R : Type := LargeEvenProj (if false = true then
      ⁅LargeEvenSpGroup K₀ l, LargeEvenSpGroup K₀ l⁆ else LargeEvenSpGroup K₀ l)
    have hAinn : (A : Set (MulAut R)) ⊆ Set.range (MulAut.conj : R →* _) :=
      fun a ha => TableBSymp.sp_I_subset_inn (K := K₀) (m := l) (hAI a ha)
    obtain ⟨s, hs⟩ := hAinn hu
    have hconj : Function.Injective (MulAut.conj : R →* _) :=
      mulAut_conj_injective (TableBSymp.center_spProj_eq_bot (K := K₀) (m := l))
    have hord : orderOf u = orderOf s := by
      rw [← hs]; exact orderOf_injective _ hconj s
    have hsp : s ^ p = 1 := by
      have hordp : orderOf s = p := by rw [← hord, huo]
      simpa [hordp] using pow_orderOf_eq_one s
    have hs1 : s ≠ 1 := by
      intro h1
      have hu1 : u = 1 := by rw [← hs, h1, map_one]
      have : orderOf u = 1 := by rw [hu1]; exact orderOf_one
      have hp2le : 2 ≤ p := hp.two_le
      omega
    have hfix : ggAutFixedSubgroup u = Subgroup.centralizer ({s} : Set R) := by
      rw [← hs]; exact ggAutFixedSubgroup_mulAut_conj s
    let e := TableBSymp.spProjEquivSp (K := K₀) (m := l)
    let C : Subgroup ↥(CFSG.Open.StatedSp l K₀) := J.map e.toMonoidHom
    have hJO : CFSG.Assembly.IsComponentOf J
        (Subgroup.centralizer ({s} : Set R)) := by
      rw [← hfix]
      exact CFSG.Assembly.isComponentOf_iff_open.mpr hJ
    have hC : CFSG.Open.IsComponentOf C
        (Subgroup.centralizer ({e s} : Set ↥(CFSG.Open.StatedSp l K₀))) := by
      have hmap : CFSG.Assembly.IsComponentOf (J.map e.toMonoidHom)
          ((Subgroup.centralizer ({s} : Set R)).map e.toMonoidHom) :=
        (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff
          (f := e.toMonoidHom) e.injective).mpr hJO
      have hcentmap : (Subgroup.centralizer ({s} : Set R)).map e.toMonoidHom =
          Subgroup.centralizer ({e s} : Set ↥(CFSG.Open.StatedSp l K₀)) :=
        CFSG.LocalAnalysis.ComponentInitial.map_centralizer_singleton_mulEquiv e s
      rw [hcentmap] at hmap
      exact CFSG.Assembly.isComponentOf_iff_open.mp hmap
    have hesp : (e s) ^ p = 1 := by rw [← map_pow, hsp, map_one]
    have hes1 : e s ≠ 1 := by
      intro h1
      have hs_eq : s = 1 := e.injective (by rw [h1, map_one])
      have hu1 : u = 1 := by rw [← hs, hs_eq, map_one]
      have : orderOf u = 1 := by rw [hu1]; exact orderOf_one
      have hp2le : 2 ≤ p := hp.two_le
      omega
    have hcenter : (Subgroup.center ↥J).map (e.subgroupMap J).toMonoidHom =
        Subgroup.center ↥C := Subgroup.map_center_eq (e.subgroupMap J)
    let eQ : (↥J ⧸ Subgroup.center ↥J) ≃* (↥C ⧸ Subgroup.center ↥C) :=
      QuotientGroup.congr (Subgroup.center ↥J) (Subgroup.center ↥C) (e.subgroupMap J) hcenter
    have hneC : Nonempty (↥C ⧸ Subgroup.center ↥C ≃*
        LargeEvenProj (LargeEvenSLGroup (Fin d) K)) := by
      obtain ⟨f⟩ := hne
      exact ⟨eQ.symm.trans f⟩
    refine ⟨fun h2n => ?_, fun hn1 => ?_⟩
    · have hpF : p ∣ Nat.card K₀ - 1 := by
        have hp2n : p ∣ 2 ^ n - 1 := by
          rcases hsplit with hh | hh | hh | hh
          · exact hh.2
          · exact (hh.1 trivial).elim
          · rcases hh.1 with h' | h' <;> cases h'
          · exact absurd h2n (by have hn1' : n = 1 := hh.1; omega)
        rw [hK₀]; exact hp2n
      obtain ⟨hd2, hdle, hfield⟩ := q2cSp_statedSp_split_component_psl (F := K₀) (ℓ := l)
        hp hp2 hpF hesp hes1 hC hK hneC
      exact Or.inl ⟨d, K, iK, iFinK, hfield.trans hK₀, hd2, hdle, hne⟩
    · have hn1' : n = 1 := hn1
      have hF2 : Nat.card K₀ = 2 := by rw [hK₀, hn1']; norm_num
      have hp3 : p = 3 := by
        rcases hsplit with hh | hh | hh | hh
        · exact absurd (Nat.dvd_one.mp (by simpa [hn1'] using hh.2)) hp.ne_one
        · exact (hh.1 trivial).elim
        · rcases hh.1 with h' | h' <;> cases h'
        · exact hh.2
      have hs3 : (e s) ^ 3 = 1 := by rw [← hp3]; exact hesp
      exact q2cSp_statedSp_nonsplit_component_psl (F := K₀) (ℓ := l) hd hF2 hs3 hes1 hC hK hneC

private theorem q2cSp_labelIso_BA_false {b n d m : ℕ} :
    ¬ GGLabelIso (⟨.B, b, n⟩ : LargeEvenLabel) ⟨.A, d - 1, m⟩ := by
  intro h
  unfold GGLabelIso at h
  rcases h with h | h | h | h | h | h | h | h <;> simp_all [LargeEvenLabel.mk.injEq]

theorem q2c_rLevel_symplectic :
    Q2CensusRLevel (fun lab => lab.tag = .B ∨ lab.tag = .C) (fun kind => kind = .symplectic) := by
  intro p d m lab hp hp2 hΛ hsplit hS hd hm hpd hpm Q hQ
  have hstruct := q2cSp_block_structure (p := p) (d := d) (m := m) hd hΛ hS hp hp2 hsplit
  have htor := q2cSp_torusLift (p := p) hΛ hS hp hp2 hsplit
  have hall := largeEvenLabelAll_and hstruct htor
  refine largeEvenRawDatum_mono ?_ (hall Q hQ)
  rintro R _ I F ⟨hq, hstruct', htor'⟩
  refine ⟨hq, fun A hA hAI hbig h3 hlo hup u hu huo J hJ huniq hAJ K _ _ hK hne => ?_⟩
  have hne' : ↥J ⧸ Subgroup.center ↥J ≃*
      LargeEvenProj (LargeEvenSLGroup (Fin d) K) := hne.some
  have hconj := hstruct' A hA hAI hbig h3 hlo hup u hu huo J hJ huniq hAJ K hK hne
  by_cases h2n : 2 ≤ lab.n
  · have hdisj := hconj.1 h2n
    rcases hdisj with hpsl | hsp
    · rcases hpsl with ⟨a, F, iF, iFin, hF, ha2, hale, hJiso⟩
      obtain ⟨hJiso'⟩ := hJiso
      by_cases ha : a = 2
      · exfalso
        subst ha
        have hψ : LinearFlag.projectiveSL d K ≃*
            LargeEvenProj (LargeEvenSLGroup (Fin 2) F) :=
          (TypeA.recipeEquiv d K).symm.trans (hne'.symm.trans hJiso')
        obtain ⟨hd2, -⟩ := kgLangS1A_psl_typeDet (d := d) (d₁ := 2) (m := m)
          (F₀ := K) (E := F) hd hm hK hψ
        omega
      · have ha3 : 3 ≤ a := by omega
        have hψ : LinearFlag.projectiveSL a F ≃*
            LargeEvenProj (LargeEvenSLGroup (Fin d) K) :=
          (TypeA.recipeEquiv a F).symm.trans (hJiso'.symm.trans hne')
        obtain ⟨hda, hcardKF⟩ := kgLangS1A_psl_typeDet (d := a) (d₁ := d) (m := lab.n)
          (F₀ := F) (E := K) ha3 h2n hF hψ
        have hrank_le : lab.rank ≤ d := by
          have hlift : GGTorusLift p lab.rank R := htor' h2n
          have hpow : p ^ lab.rank ≤ Nat.card A := hbig lab.rank hlift
          exact (Nat.pow_le_pow_iff_right hp.one_lt).mp (hpow.trans hup)
        have hd_le : d ≤ lab.rank := by rw [hda]; exact hale
        have hrank_eq : lab.rank = d := le_antisymm hrank_le hd_le
        have hfield : 2 ^ m = 2 ^ lab.n := by rw [← hK, hcardKF, hF]
        exact ⟨.symplectic, rfl, hp, hp2, hpd, hpm, hS, hrank_eq, hfield⟩
    · exfalso
      rcases hsp with ⟨b, F, iF, iFin, hF, hb2, hble, hJiso⟩
      obtain ⟨hJiso'⟩ := hJiso
      haveI : CharP F 2 := charP_two_of_card hF
      haveI : NeZero b := ⟨by omega⟩
      have hhasB : GGHasLabel (⟨.B, b, lab.n⟩ : LargeEvenLabel)
          (↥J ⧸ Subgroup.center ↥J) := by
        unfold GGHasLabel
        dsimp only [LargeEvenRawDatum, LargeEvenRecipeSymplectic]
        refine ⟨F, inferInstance, inferInstance, hF, ?_⟩
        show Nonempty (↥J ⧸ Subgroup.center ↥J ≃* LargeEvenProj (LargeEvenSpGroup F b))
        exact ⟨hJiso'.trans (TableBSymp.spProjEquivSp (K := F) (m := b)).symm⟩
      have hd1 : d - 1 + 1 = d := by omega
      have hhasA : GGHasLabel (⟨.A, d - 1, m⟩ : LargeEvenLabel)
          (↥J ⧸ Subgroup.center ↥J) := by
        unfold GGHasLabel
        dsimp only [LargeEvenRawDatum, LargeEvenRecipeLinear]
        rw [hd1]
        exact ⟨K, inferInstance, inferInstance, hK, ⟨hne'⟩⟩
      have hΛB : LargeEvenInLambda2 (⟨.B, b, lab.n⟩ : LargeEvenLabel) :=
        ⟨hΛ.1, hb2, fun _ => h2n⟩
      have hΛA : LargeEvenInLambda2 (⟨.A, d - 1, m⟩ : LargeEvenLabel) :=
        ⟨le_trans (by norm_num : 1 ≤ 2) hm,
          Nat.le_sub_one_of_lt (lt_of_lt_of_le (by norm_num : 1 < 3) hd),
          fun h => by
            have h' : d - 1 = 1 := h
            have h2 : 2 ≤ d - 1 :=
              Nat.le_sub_one_of_lt (lt_of_lt_of_le (by norm_num : 2 < 3) hd)
            rw [h'] at h2
            norm_num at h2⟩
      exact (q2cSp_labelIso_BA_false
        (ggLabelRigidInput_holds (⟨.B, b, lab.n⟩ : LargeEvenLabel)
          (⟨.A, d - 1, m⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J)
          hΛB hΛA hhasB hhasA)).elim
  · have hn1 : lab.n = 1 := le_antisymm (Nat.lt_succ_iff.mp (not_le.1 h2n)) hΛ.1
    exact (hconj.2 hn1).elim

end CFSG.StandardType
