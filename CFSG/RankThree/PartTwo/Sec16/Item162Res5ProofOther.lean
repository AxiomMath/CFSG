module

public import CFSG.RankThree.PartTwo.Sec16.Item162Res4ProofChoice
import CFSG.RankThree.PartTwo.Sec16.Item162ResProofTools
import CFSG.RankThree.PartTwo.Sec16.Item162StepsProofTools
import CFSG.RankThree.PartTwo.Sec16.Item163StepsQProof
import CFSG.RankThree.PartTwo.Sec15.Item1515ResProofCover
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.PartTwo.Sec6.Item612Core

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS

@[expose] def Step162A7OtherFree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y₁ Y₂ S : Subgroup G, MaxCE162 A (lB A) Y₁ Y₂ S S → L ≤ Y₁ →
      MeetsY4 A (lB A) L Y₁ →
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) →
      WStarS4 A → TransOmegaThree A c →
      Nonempty (↥Y₁ ⧸ CFSG.pCore 2 ↥Y₁ ≃* alternatingGroup (Fin 7)) →
      (¬ ∃ g ∈ Subgroup.normalizer (A : Set G), Y₂ = Y₁.map (MulAut.conj g).toMonoidHom) →
      Choice162 A c S →
      ∀ (b : G) (Lb : Subgroup G), Subgroup.zpowers b ∈ omegaA A → Lb ∈ lA A b →
        Subgroup.zpowers b ≠ Subgroup.zpowers c → MeetsY4 A (lB A) Lb Y₂ →
        Nonempty (↥Y₂ ⧸ CFSG.pCore 2 ↥Y₂ ≃* alternatingGroup (Fin 7)) →
        Late.sectionCentralizer A Y₂ (CFSG.Open.pCoreOf 2 Y₂) = (Subgroup.zpowers b : Set G) →
        CFSG.Open.pCoreOf 2 (Y₂ ⊔ S) ⊓ Subgroup.normalizer (Subgroup.zpowers b : Set G) = ⊥ →
          False

namespace Res162Five

variable {G : Type} [Group G] [Finite G]

theorem false_of_fix {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    (h155 : Item155 A (lB A)) (h153 : Item153Main A (lB A))
    (hW : ∀ Y : Subgroup G, Y = delta A (lB A) Y → Y ∈ scriptY A → ¬ Group.IsSolvable ↥Y →
      TransOn A (lB A) (Subgroup.normalizer (A : Set G)) Y)
    (h142 : Concl142 A (lB A)) {Y₁ Y₂ S : Subgroup G} (hmax : MaxCE162 A (lB A) Y₁ Y₂ S S)
    (hLY₁ : L ≤ Y₁) (hT : TransOmegaThree A c)
    (hnW : ¬ ∃ g ∈ Subgroup.normalizer (A : Set G), Y₂ = Y₁.map (MulAut.conj g).toMonoidHom)
    (hch : Choice162 A c S) {b : G} {Lb : Subgroup G} (hb : Subgroup.zpowers b ∈ omegaA A)
    (hLb : Lb ∈ lA A b) (hm₂ : MeetsY4 A (lB A) Lb Y₂)
    (φ₂ : ↥Y₂ ⧸ CFSG.pCore 2 ↥Y₂ ≃* alternatingGroup (Fin 7))
    (hfix : CFSG.Open.pCoreOf 2 (Y₂ ⊔ S) ⊓ Subgroup.normalizer (Subgroup.zpowers b : Set G) ≠
      ⊥) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := h.toSec13Data
  have hb' : Sec15R G A b Lb := sec15R_of_point h hb hLb
  have hY₁ := hmax.1.mem₁
  have hY₂ := hmax.1.mem₂
  have hY₂4 : Y₂ ∈ scriptY4 A (lB A) := hY₂.prop.1
  have hbA : b ∈ A := (zpowers_mem_omegaA_iff.mp hb).1
  have hb1 : b ≠ 1 := by
    intro h1
    have h3 := (zpowers_mem_omegaA_iff.mp hb).2.1
    rw [h1, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at h3
    omega
  set Hb := Subgroup.normalizer (Subgroup.zpowers b : Set G) with hHb
  have hCb : Subgroup.centralizer ({b} : Set G) ≤ Hb :=
    centralizer_singleton_le_normalizer_zpowers b
  have hLbC : Lb ≤ Subgroup.centralizer ({b} : Set G) := hb'.toSec13Data.le_centralizer
  have hHbL : Hb ≤ Subgroup.normalizer (Lb : Set G) :=
    normalizer_zpowers_le_normalizer_L hb' (three_dvd_card_of_mem_lA h hb hLb)
  have hAb : A ≤ Subgroup.centralizer ({b} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hD.commute ha hbA)
  obtain ⟨g, hg, hbg⟩ := hT.2 _ hb
  have hLg : L.map (MulAut.conj g).toMonoidHom = Lb :=
    map_conj_eq_of_zpowers hb' h.zpowers_mem_omegaA h.mem_lA hg hbg
  have hSb : (S ⊓ Subgroup.centralizer ({c} : Set G)).map (MulAut.conj g).toMonoidHom ∈
      scriptQPiStar A (lB A) Hb (piOf 2) := by
    have h1 := Sec17.HeadProof.map_conj_mem_scriptQPiStar hg hch
    rwa [Subgroup.map_equiv_normalizer_eq, ← hbg] at h1
  set R := CFSG.Open.pCoreOf 2 (Y₂ ⊔ S) with hR
  set Q := R ⊓ Hb with hQ
  have hSY₂ : S ≤ Subgroup.normalizer (Y₂ : Set G) := hmax.1.s₂.prop.1.2
  have hY₂S : Y₂ ⊔ S ≤ Subgroup.normalizer (Y₂ : Set G) := sup_le Subgroup.le_normalizer hSY₂
  have hRY₂S : R ≤ Y₂ ⊔ S := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hQ2 : IsPGroup 2 Q :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) (Y₂ ⊔ S)).to_le inf_le_left
  have hAY₂ : A ≤ Subgroup.normalizer (Y₂ : Set G) := hY₂.prop.1.1.2
  have hAS : A ≤ Subgroup.normalizer (S : Set G) := hmax.1.s₂.prop.1.1.1.2.2
  have hAR : A ≤ Subgroup.normalizer (R : Set G) :=
    (le_normalizer_sup hAY₂ hAS).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
  have hAQ : A ≤ Subgroup.normalizer (Q : Set G) :=
    (le_inf hAR ((hAb.trans hCb).trans Subgroup.le_normalizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hQ3 : ¬ 3 ∣ Nat.card Q := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQ2
    rw [hn]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hQQ : Q ∈ scriptQ A (lB A) := mem_scriptQ_of_concl142 h142 hb
    ⟨inf_le_right, (isPiSubgroup_piCompl_iff Nat.prime_three Q).mpr hQ3, hAQ⟩
  have hQmem : Q ∈ scriptQPi A (lB A) Hb (piOf 2) :=
    ⟨⟨hQQ, inf_le_right⟩, (isPiSubgroup_piOf_iff Nat.prime_two Q).mpr hQ2⟩
  obtain ⟨Q', hQQ', hQ'⟩ := Finite.exists_le_maximal
    (p := (· ∈ scriptQPi A (lB A) Hb (piOf 2))) hQmem
  set M := Y₂ ⊓ Lb with hM
  set E := oPrimeResidualOf 3 M with hE
  have hEM : E ≤ M := Subgroup.map_subtype_le _
  have hEY₂ : E ≤ Y₂ := hEM.trans inf_le_left
  have hELb : E ≤ Lb := hEM.trans inf_le_right
  have hcovY₂ : Y₂ = (Y₂ ⊓ Lb) ⊔ CFSG.Open.pCoreOf 2 Y₂ := by
    have hcov := Res162b.eq_top_of_seven hb' hY₂ hm₂ φ₂
    refine Res162.eq_sup_of_forall_mem fun y hy => ?_
    obtain ⟨d, hd, hdy⟩ := hcov y hy
    exact ⟨d, ⟨hd.2, hd.1⟩, hdy⟩
  have hcovE : Y₂ ≤ E ⊔ CFSG.Open.pCoreOf 2 Y₂ :=
    Proof1515Res.le_oRes3_sup hY₂4.2.1 inf_le_left (CFSG.LieType.BorelTits.pCoreOf_le 2 Y₂)
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y₂) hcovY₂.le
  have hAE : A ≤ Subgroup.normalizer (E : Set G) :=
    Proof1515Res.le_normalizer_oRes3 (Late.le_normalizer_inf hAY₂ hLb.2.1)
  have hmemE : ∀ R' : Subgroup G, R' ≤ E → ¬ 3 ∣ Nat.card R' →
      A ≤ Subgroup.normalizer (R' : Set G) → R' ∈ scriptQ A (lB A) := fun R' hR'E hR'3 hAR' =>
    mem_scriptQ_of_concl142 h142 hb ⟨(hR'E.trans (hELb.trans hLbC)).trans hCb,
      (isPiSubgroup_piCompl_iff Nat.prime_three R').mpr hR'3, hAR'⟩
  have hE4 : E ∈ scriptY4 A (lB A) := Proof1515Res.mem_scriptY4_of_le_cover hY₂4 hEY₂ hcovE hAE
    (Proof1515Res.oRes3_idem M).symm hmemE
  set Dl := delta A (lB A) Hb with hDl
  have hEDl : E ≤ Dl :=
    hE4.2.2.1.le.trans (delta_mono (hELb.trans (hLbC.trans hCb)))
  have hDlC : Dl ≤ Subgroup.centralizer ({b} : Set G) :=
    sSup_le fun Q₀ hQ₀ => le_centralizer_of_le_normalizer_zpowers h.toSec14Std.isE27 hbA hQ₀.1
      hQ₀.2
  have hDlY : Dl ∈ scriptY A :=
    ⟨fun htop => Sec6.centralizer_ne_top_of_ne_one h.toTheoremFourHyp hb1
      (top_le_iff.mp (htop ▸ hDlC)), le_normalizer_sSup fun Q₀ hQ₀ => hQ₀.1.1.2.2⟩
  have hDlΔ : Dl = delta A (lB A) Dl := (delta_delta _).symm
  have hDlsol : ¬ Group.IsSolvable ↥Dl := fun hs => by
    have := hs
    exact Proof162.not_isSolvable_of_mem_scriptY4 hE4
      (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hEDl))
  have htr := hW Dl hDlΔ hDlY hDlsol
  have hSbD : (S ⊓ Subgroup.centralizer ({c} : Set G)).map (MulAut.conj g).toMonoidHom ∈
      scriptQPiStar A (lB A) Dl (piOf 2) := by
    rw [hDl, scriptQPiStar_delta]
    exact hSb
  have hQ'D : Q' ∈ scriptQPiStar A (lB A) Dl (piOf 2) := by
    rw [hDl, scriptQPiStar_delta]
    exact hQ'
  obtain ⟨x, hx, hxQ'⟩ := htr _ hSbD _ hQ'D
  have hxW : x ∈ Subgroup.normalizer (A : Set G) := (Subgroup.mem_inf.mp hx).1
  have hxHb : x ∈ Hb := delta_le Hb (Subgroup.mem_inf.mp hx).2
  set w := x * g with hw
  have hwW : w ∈ Subgroup.normalizer (A : Set G) := mul_mem hxW hg
  have hQSw : Q ≤ S.map (MulAut.conj w).toMonoidHom := by
    refine hQQ'.trans ?_
    rw [hxQ', Late.map_conj_map_conj]
    exact Subgroup.map_mono inf_le_left
  have hLw : L.map (MulAut.conj w).toMonoidHom = Lb := by
    rw [hw, ← Late.map_conj_map_conj, hLg, Late.map_conj_eq_of_mem_normalizer (hHbL hxHb)]
  set Y₁w := Y₁.map (MulAut.conj w).toMonoidHom with hY₁wdef
  have hY₁w : Y₁w ∈ scriptY0Star A (lB A) := map_conj_mem_scriptY0Star hwW hY₁
  have hLbY₁w : Lb ≤ Y₁w := hLw ▸ Subgroup.map_mono hLY₁
  have hSwN : S.map (MulAut.conj w).toMonoidHom ≤ Subgroup.normalizer (Y₁w : Set G) := by
    rw [hY₁wdef, ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hmax.1.s₁.prop.1.2
  have hQE : Q ≤ Subgroup.normalizer (E : Set G) := by
    refine Proof1515Res.le_normalizer_oRes3 ?_
    exact (le_inf ((inf_le_left.trans hRY₂S).trans hY₂S) (inf_le_right.trans hHbL)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hEQ : E ≤ Subgroup.normalizer (Q : Set G) := by
    refine (le_inf ?_ ?_).trans Subgroup.inf_normalizer_le_normalizer_inf
    · exact (hEY₂.trans le_sup_left).trans
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y₂ ⊔ S))
    · exact ((hELb.trans hLbC).trans hCb).trans Subgroup.le_normalizer
  set Y' := E ⊔ Q with hY'def
  have hY'Q : Y' ≤ Subgroup.normalizer (Q : Set G) := sup_le hEQ Subgroup.le_normalizer
  have hQO : Q ≤ CFSG.Open.pCoreOf 2 Y' :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_sup_right hY'Q hQ2
  have hO2 : CFSG.Open.pCoreOf 2 Y' ≠ ⊥ := fun h0 => hfix (le_bot_iff.mp (h0 ▸ hQO))
  have hY'Δ : Y' = delta A (lB A) Y' :=
    le_antisymm (sup_le (hE4.2.2.1.le.trans (delta_mono le_sup_left)) (le_delta hQQ le_sup_right))
      (delta_le _)
  have hY'c : Y' ≤ Subgroup.centralizer ({b} : Set G) :=
    sup_le (hELb.trans hLbC)
      (le_centralizer_of_le_normalizer_zpowers h.toSec14Std.isE27 hbA hQQ inf_le_right)
  have hY'top : Y' ≠ ⊤ := fun htop =>
    Sec6.centralizer_ne_top_of_ne_one h.toTheoremFourHyp hb1 (top_le_iff.mp (htop ▸ hY'c))
  have hY'3 : Y' ∈ scriptY3 A (lB A) := ⟨⟨⟨hY'top, le_normalizer_sup hAE hAQ⟩, hO2⟩, hY'Δ⟩
  have hres : oPrimeResidualOf 3 Y' = E :=
    ((oPrimeResidualOf_eq_of_le le_sup_left fun z hz k hk =>
      mem_of_pow_three_of_mem_sup hQE hQ2 hz hk).symm.trans hE4.2.1.symm)
  have hX4 : oPrimeResidualOf 3 Y' ∈ scriptY4 A (lB A) := by
    rw [hres]
    exact hE4
  have hY'eq : Y' = oPrimeResidualOf 3 Y' ⊔ CFSG.Open.pCoreOf 2 Y' := by
    rw [hres]
    exact le_antisymm (sup_le le_sup_left (hQO.trans le_sup_right))
      (sup_le le_sup_left (CFSG.LieType.BorelTits.pCoreOf_le 2 Y'))
  have hΓ₁ : Y₁w ∈ gam155 A (lB A) Y' (oPrimeResidualOf 3 Y') := by
    rw [hres]
    exact ⟨hY₁w, hELb.trans hLbY₁w,
      sup_le ((hELb.trans hLbY₁w).trans Subgroup.le_normalizer) (hQSw.trans hSwN)⟩
  have hΓ₂ : Y₂ ∈ gam155 A (lB A) Y' (oPrimeResidualOf 3 Y') := by
    rw [hres]
    exact ⟨hY₂, hEY₂, sup_le (hEY₂.trans Subgroup.le_normalizer)
      ((inf_le_left.trans hRY₂S).trans hY₂S)⟩
  have hside : Y₂ = oPrimeResidualOf 3 Y' ⊔ CFSG.Open.pCoreOf 2 Y₂ := by
    rw [hres]
    exact le_antisymm hcovE (sup_le hEY₂ (CFSG.LieType.BorelTits.pCoreOf_le 2 Y₂))
  have heq := Proof162.eq_of_mem_gam155 h155 h153 hY'3 hX4 hY'eq hΓ₁ hΓ₂ (Or.inr hside)
  exact hnW ⟨w, hwW, heq.symm⟩

end Res162Five

theorem step162A7OtherSevenC_of_free (h155 : Item155R) (h153 : Item153MainR)
    (hWloc : Claim1411NonsolvWR) (h142 : Concl142R) (hF : Step162A7OtherFree) :
    Step162A7OtherSevenC := by
  intro G _ _ A c L h Y₁ Y₂ S hmax hLY₁ hm₁ h7 hW4 hT hY₁7 hnW hch b Lb hb hLb hbc hm₂ hY₂7 hsc
  by_cases hfix : CFSG.Open.pCoreOf 2 (Y₂ ⊔ S) ⊓
      Subgroup.normalizer (Subgroup.zpowers b : Set G) = ⊥
  · exact hF G A c L h Y₁ Y₂ S hmax hLY₁ hm₁ h7 hW4 hT hY₁7 hnW hch b Lb hb hLb hbc hm₂ hY₂7 hsc
      hfix
  · obtain ⟨φ₂⟩ := hY₂7
    exact Res162Five.false_of_fix h (h155 G A c L h) (h153 G A c L h) (hWloc G A c L h)
      (h142 G A c L h) hmax hLY₁ hT hnW hch hb hLb hm₂ φ₂ hfix

end CFSG.RankThree.PartTwo.Sec16
