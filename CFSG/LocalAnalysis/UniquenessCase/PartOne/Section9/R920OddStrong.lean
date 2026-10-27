module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddChain
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09b
public import CFSG.LocalAnalysis.UniquenessCase.UC7P3Defs
import CFSG.LocalAnalysis.UniquenessCase.UC6R869T3
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1Aux
import CFSG.LocalAnalysis.GLTheoremB.ComponentTools
import CFSG.LocalAnalysis.GLTheoremB.SchreierTools

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (StronglyEmbeddedThree)

variable {G : Type} [Group G] [Finite G]

theorem L9_le_of_le {Y H : Subgroup G} (hYH : Y ≤ H) : F09.L9 Y H ≤ H := by
  refine iSup_le fun h => ?_
  rintro _ ⟨x, hx, rfl⟩
  exact H.mul_mem (H.mul_mem h.2 ((opp_le 3 Y).trans hYH hx)) (H.inv_mem h.2)

theorem le_normalizer_L9 (Y H : Subgroup G) : H ≤ normalizer (F09.L9 Y H : Set G) := by
  have key : ∀ g : ↥H, (F09.L9 Y H).map (MulAut.conj (g : G)).toMonoidHom ≤ F09.L9 Y H := by
    intro g
    unfold F09.L9
    rw [Subgroup.map_iSup]
    refine iSup_le fun h => ?_
    rw [Subgroup.map_map]
    have e : (MulAut.conj (g : G)).toMonoidHom.comp (MulAut.conj (h : G)).toMonoidHom =
        (MulAut.conj ((g * h : ↥H) : G)).toMonoidHom := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rw [e]
    exact le_iSup (fun h : ↥H => (Opp 3 Y).map (MulAut.conj (h : G)).toMonoidHom) (g * h)
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact key ⟨g, hg⟩ (Subgroup.mem_map.2 ⟨x, hx, rfl⟩)
  · intro hx
    have := key ⟨g⁻¹, H.inv_mem hg⟩ (Subgroup.mem_map.2 ⟨g * x * g⁻¹, hx, rfl⟩)
    simpa [MulAut.conj_apply, mul_assoc] using this

theorem exists_surjective_map_pPrimeCore_bar2 {p : ℕ} (hp : p.Prime) {H X : Subgroup G}
    (hXH : X ≤ H) (hs : IsSimpleGroup (Bar2 X)) (hpX : p ∣ Nat.card (Bar2 X)) :
    ∃ f : ↥((X.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H))) →* Bar2 X,
      Function.Surjective f := by
  haveI : Fact p.Prime := ⟨hp⟩
  set I : Subgroup ↥H := CFSG.pPrimeCore p ↥H with hI
  set img := (X.subgroupOf H).map (QuotientGroup.mk' I) with himg
  haveI hIn : I.Normal := CFSG.pPrimeCore_normal
  have hmem : ∀ x : ↥X, (QuotientGroup.mk' I) (Subgroup.inclusion hXH x) ∈ img := fun x =>
    Subgroup.mem_map.2 ⟨Subgroup.inclusion hXH x, Subgroup.mem_subgroupOf.2 x.2, rfl⟩
  let ψ : ↥X →* ↥img :=
    ((QuotientGroup.mk' I).comp (Subgroup.inclusion hXH)).codRestrict img hmem
  have hψ : Function.Surjective ψ := by
    rintro ⟨z, hz⟩
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hz
    exact ⟨⟨y, Subgroup.mem_subgroupOf.1 hy⟩, Subtype.ext rfl⟩
  set π : ↥X →* Bar2 X := QuotientGroup.mk' (CFSG.pCore 2 ↥X) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  set J : Subgroup ↥X := I.comap (Subgroup.inclusion hXH) with hJ
  haveI hJn : J.Normal := hIn.comap _
  have hJcard : Nat.card J ∣ Nat.card I :=
    Subgroup.card_comap_dvd_of_injective I (Subgroup.inclusion hXH)
      (Subgroup.inclusion_injective hXH)
  have hpI : ¬ p ∣ Nat.card I :=
    (hp.coprime_iff_not_dvd).mp (CFSG.pPrimeCore_coprime_card (G := ↥H) (p := p))
  haveI : (J.map π).Normal := hJn.map π hπs
  have hker : ψ.ker ≤ π.ker := by
    have hψJ : ψ.ker = J := by
      ext x
      rw [MonoidHom.mem_ker, hJ, Subgroup.mem_comap, ← QuotientGroup.eq_one_iff,
        ← Subtype.coe_inj]
      rfl
    rw [hψJ]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (J.map π) with hbot | htop
    · intro x hx
      have : π x ∈ J.map π := Subgroup.mem_map_of_mem π hx
      rw [hbot] at this
      exact Subgroup.mem_bot.1 this
    · exfalso
      have hsurj : Function.Surjective (π.comp J.subtype) := by
        intro b
        have hb : b ∈ J.map π := by rw [htop]; trivial
        obtain ⟨j, hj, hjb⟩ := Subgroup.mem_map.1 hb
        exact ⟨⟨j, hj⟩, hjb⟩
      exact hpI (hpX.trans ((Subgroup.card_dvd_of_surjective hsurj).trans hJcard))
  let f : ↥img →* Bar2 X :=
    ψ.liftOfRightInverse (Function.surjInv hψ) (Function.rightInverse_surjInv hψ) ⟨π, hker⟩
  have hfψ : ∀ x : ↥X, f (ψ x) = π x := fun x =>
    MonoidHom.liftOfRightInverse_comp_apply ψ _ _ ⟨π, hker⟩ x
  refine ⟨f, fun b => ?_⟩
  obtain ⟨x, rfl⟩ := hπs b
  exact ⟨ψ x, hfψ x⟩

namespace SliceCore

variable {D : Data G} {L D₃ Y H : Subgroup G}

theorem two_le_pRank_inf_M (S : SliceCore D L D₃ Y H) (hK : 2 ≤ CFSG.Open.pRank 3 (F09.L9 Y H)) :
    2 ≤ CFSG.Open.pRank 3 (H ⊓ D.M) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E, hEX, hEcard, hEU⟩ := S.exists_order_three_le_opp
  obtain ⟨P, hP, -, hPM⟩ := S.exists_sylow_le_M hEX (IsPGroup.of_card (n := 1) (by simpa using hEcard)) hEU
  have hKP : CFSG.ABGLocalTools.IsSylowOf 3 (P ⊓ F09.L9 Y H) (F09.L9 Y H) :=
    hP.inf_of_le_normalizer (L9_le_of_le S.Y_le_H) (le_normalizer_L9 Y H)
  have hr : CFSG.Open.pRank 3 (P ⊓ F09.L9 Y H) = CFSG.Open.pRank 3 (F09.L9 Y H) :=
    CFSG.LocalAnalysis.RankThreeTheoremC.pRank_eq_of_isSylowOf3 Nat.prime_three hKP
  have hle : P ⊓ F09.L9 Y H ≤ H ⊓ D.M := le_inf (inf_le_left.trans hP.le) (inf_le_left.trans hPM)
  exact hK.trans (hr ▸ CFSG.RankThreeCoreUniqueness.Helpers.pRank_mono 3 (by norm_num) hle)

theorem isSimpleGroup_bar2_opp (S : SliceCore D L D₃ Y H) : IsSimpleGroup (Bar2 (Opp 3 Y)) :=
  S.facts_opp.simple

theorem three_dvd_card_bar2_opp (S : SliceCore D L D₃ Y H) : 3 ∣ Nat.card (Bar2 (Opp 3 Y)) := by
  obtain ⟨e⟩ := S.nonempty_bar2_opp_equiv
  rw [← Nat.card_congr e.toEquiv]
  exact S.three_dvd_card_bar2

theorem not_isSolvable_bar2_opp (S : SliceCore D L D₃ Y H) :
    ¬ Group.IsSolvable (Bar2 (Opp 3 Y)) := by
  intro hs
  obtain ⟨e⟩ := S.nonempty_bar2_L_opp_equiv
  haveI : Group.IsSolvable (Bar2 L) :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  exact uc22p22a_qs_not_solvable S.L_mem.2.2 this

theorem pRank_L9_le_one_of_isStronglyPEmbedded (hK3 : StronglyEmbeddedThree)
    (S : SliceCore D L D₃ Y H) (hsp : IsStronglyPEmbedded 3 D.M) :
    CFSG.Open.pRank 3 (F09.L9 Y H) ≤ 1 := by
  by_contra hrank
  have hrM : 2 ≤ CFSG.Open.pRank 3 (H ⊓ D.M) := S.two_le_pRank_inf_M (by omega)
  have hHK : CFSG.Open.IsKGroup ↥H :=
    CFSG.LocalAnalysis.GLTheoremB.isKGroup_of_isKProper D.standing.kProper S.H_ne_top
  haveI hsolv : Group.IsSolvable ↥(((H ⊓ D.M).subgroupOf H).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H))) :=
    (hK3 _ (CFSG.LocalAnalysis.GLTheoremB.isKGroup_quotient' hHK (CFSG.pPrimeCore 3 ↥H))
      (CFSG.pPrimeCore_quotient_eq_bot Nat.prime_three)
      (UC6.R869S.two_le_pRank_quotient_pPrimeCore Nat.prime_three hrM) _
      (UC6.R869S.isStronglyPEmbedded_map_quotient_pPrimeCore Nat.prime_three hsp S.not_H_le_M
        hrM)).2.2.2
  have hXH : Opp 3 Y ≤ H := (opp_le 3 Y).trans S.Y_le_H
  have hle : ((Opp 3 Y).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H)) ≤
      ((H ⊓ D.M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H)) :=
    Subgroup.map_mono (Subgroup.comap_mono (le_inf hXH S.opp_le_M))
  haveI : Group.IsSolvable ↥(((Opp 3 Y).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H))) :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  obtain ⟨f, hf⟩ := exists_surjective_map_pPrimeCore_bar2 Nat.prime_three hXH
    S.isSimpleGroup_bar2_opp S.three_dvd_card_bar2_opp
  exact S.not_isSolvable_bar2_opp (solvable_of_surjective hf)

end SliceCore

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9
