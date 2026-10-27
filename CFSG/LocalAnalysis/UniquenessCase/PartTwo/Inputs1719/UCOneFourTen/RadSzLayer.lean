module

import CFSG.Quasithin.Background.F918V5GComp
import CFSG.GroupTheory.IsComponentOfMap
import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaQCount
import CFSG.GroupTheory.ABGLocalTools.PStabilitySignalizer
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Background.E1Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410

open Subgroup
open scoped Pointwise

variable {S : Type} [Group S] [Finite S]

theorem exists_normal_threePrime_layer {G : Type} [Group G] [Finite G] {B : Subgroup G}
    (hB : CFSG.Open.IsComponentOf B ⊤) (hB3 : ¬ 3 ∣ Nat.card B) :
    ∃ E : Subgroup G, B ≤ E ∧ E.Normal ∧ ¬ 3 ∣ Nat.card E := by
  classical
  let ι := {C : Subgroup G // CFSG.Open.IsComponentOf C ⊤ ∧ ¬ 3 ∣ Nat.card C}
  have : Fintype ι := Fintype.ofFinite ι
  let E : Subgroup G := ⨆ i : ι, i.1
  have hBE : B ≤ E := le_iSup (fun i : ι => i.1) ⟨B, hB, hB3⟩
  have hcomm : Pairwise fun i j : ι => ∀ x y : G, x ∈ i.1 → y ∈ j.1 → Commute x y := by
    intro i j hij x y hx hy
    rcases CFSG.Quasithin.F918V5G.isComponentOf_eq_or_commute i.2.1 j.2.1 with h | h
    · exact absurd (Subtype.ext h) hij
    · exact h x hx y hy
  have hmap : ∀ g : G, E.map (MulAut.conj g).toMonoidHom ≤ E := by
    intro g
    have hE : E = ⨆ i : ι, i.1 := rfl
    rw [hE, Subgroup.map_iSup]
    refine iSup_le fun i => ?_
    have hcomp : CFSG.Open.IsComponentOf (i.1.map (MulAut.conj g).toMonoidHom) ⊤ := by
      have h := CFSG.isComponentOf_map_mulEquiv (MulAut.conj g) i.2.1
      rwa [Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective] at h
    have hcard : ¬ 3 ∣ Nat.card ↥(i.1.map (MulAut.conj g).toMonoidHom) := by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact i.2.2
    exact le_iSup (fun j : ι => j.1) ⟨_, hcomp, hcard⟩
  refine ⟨E, hBE, Subgroup.Normal.mk fun n hn g => ?_, ?_⟩
  · have h := hmap g (Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hn)
    simpa [MulAut.conj_apply] using h
  · have hφ := Subgroup.card_range_dvd (Subgroup.noncommPiCoprod hcomm)
    have hrange : (Subgroup.noncommPiCoprod hcomm).range = E :=
      Subgroup.noncommPiCoprod_range
    rw [hrange] at hφ
    rw [Nat.card_pi] at hφ
    intro h3
    have h3prod : 3 ∣ ∏ i : ι, Nat.card ↥i.1 := h3.trans hφ
    have key : ∀ s : Finset ι, (∀ i ∈ s, ¬ 3 ∣ Nat.card (↥i.1)) →
        ¬ 3 ∣ ∏ i ∈ s, Nat.card (↥i.1) := by
      intro s
      induction s using Finset.induction_on with
      | empty => intro _; simp
      | insert a s ha ih =>
        intro hs
        rw [Finset.prod_insert ha]
        intro h
        rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h1 | h2
        · exact hs a (Finset.mem_insert_self a s) h1
        · exact ih (fun i hi => hs i (Finset.mem_insert_of_mem hi)) h2
    exact key Finset.univ (fun i _ => i.2.2) h3prod

theorem exists_threePrime_sylow_overgroup {U : Subgroup S} (T : Sylow 2 S)
    (hTU : normalizer ((T : Subgroup S) : Set S) ≤ normalizer (U : Set S))
    {B : Subgroup (↥(normalizer (U : Set S)) ⧸ CFSG.pCore 2 ↥(normalizer (U : Set S)))}
    (hB : CFSG.Open.IsComponentOf B ⊤) (hBs : IsSimpleGroup ↥B) (hB2 : 2 ∣ Nat.card B)
    (hB3 : ¬ 3 ∣ Nat.card B) :
    ∃ J₀ : Subgroup S, (T : Subgroup S) ≤ J₀ ∧ J₀ ≤ normalizer (U : Set S) ∧
      normalizer ((T : Subgroup S) : Set S) ≤ normalizer (J₀ : Set S) ∧
      ¬ J₀ ≤ normalizer ((T : Subgroup S) : Set S) ∧ ¬ 3 ∣ Nat.card J₀ := by
  classical
  let P : Subgroup S := normalizer (U : Set S)
  let V : Subgroup ↥P := CFSG.pCore 2 ↥P
  have hVn : V.Normal := CFSG.pCore_normal (p := 2) (G := ↥P)
  let Q := ↥P ⧸ V
  let π : ↥P →* Q := QuotientGroup.mk' V
  have hTP : (T : Subgroup S) ≤ P := Subgroup.le_normalizer.trans hTU
  obtain ⟨E, hBE, hEnorm, hE3⟩ := exists_normal_threePrime_layer (G := Q) hB hB3
  let E' : Subgroup ↥P := E.comap π
  let Etilde : Subgroup S := E'.map P.subtype
  have hE'norm : E'.Normal := hEnorm.comap π
  have hE'map : E'.map π = E := by
    rw [Subgroup.map_comap_eq, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective V),
      top_inf_eq]
  let TQ : Sylow 2 Q := Sylow.mapSurjective (f := π) (QuotientGroup.mk'_surjective V)
    (T.subtype hTP)
  have hTQcoe : ((TQ : Sylow 2 Q) : Subgroup Q) = ((T : Subgroup S).subgroupOf P).map π := by
    rw [Sylow.coe_mapSurjective, Sylow.coe_subtype]
  refine ⟨Etilde ⊔ (T : Subgroup S), le_sup_right, ?_, ?_, ?_, ?_⟩
  · exact sup_le (Subgroup.map_subtype_le E') hTP
  ·
    intro g hg
    have hgP : g ∈ P := hTU hg
    have hgE : Etilde.map (MulAut.conj g).toMonoidHom = Etilde :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp
        (CFSG.ABGLocalTools.le_normalizer_map_subtype P E' hgP)
    have hgT : (T : Subgroup S).map (MulAut.conj g).toMonoidHom = (T : Subgroup S) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hgoal : (Etilde ⊔ (T : Subgroup S)).map (MulAut.conj g).toMonoidHom
        = Etilde ⊔ (T : Subgroup S) :=
      (Subgroup.map_sup _ _ _).trans (by rw [hgE, hgT])
    exact hgoal
  ·
    intro hJN
    have hBnorm : B ≤ Subgroup.normalizer ((TQ : Sylow 2 Q) : Set Q) := by
      intro b hb
      have hbE : b ∈ E := hBE hb
      rw [← hE'map] at hbE
      obtain ⟨x, hxE', hxb⟩ := Subgroup.mem_map.mp hbE
      subst hxb
      have hxJ : ((x : ↥P) : S) ∈ Etilde ⊔ (T : Subgroup S) :=
        Subgroup.mem_sup_left (Subgroup.mem_map_of_mem P.subtype hxE')
      have hxN : ((x : ↥P) : S) ∈ Subgroup.normalizer ((T : Subgroup S) : Set S) := hJN hxJ
      have hxT : (T : Subgroup S).map (MulAut.conj ((x : ↥P) : S)).toMonoidHom =
          (T : Subgroup S) :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hxN
      have hxTP : ((T : Subgroup S).subgroupOf P).map (MulAut.conj x).toMonoidHom =
          (T : Subgroup S).subgroupOf P := by
        have h1 : (MulAut.conj ((x : ↥P) : S) : MulAut S) • (T : Subgroup S) =
            (T : Subgroup S) := by
          rw [Subgroup.pointwise_smul_def]
          exact hxT
        have h2 := Subgroup.conj_smul_subgroupOf (P := (T : Subgroup S)) (H := P) hTP x
        rw [h1] at h2
        rw [Subgroup.pointwise_smul_def] at h2
        exact h2
      have hcomp : (MulAut.conj (π x)).toMonoidHom.comp π =
          π.comp (MulAut.conj x).toMonoidHom := by
        ext y
        simp [MulAut.conj_apply]
      have hgoal : ((TQ : Subgroup Q)).map (MulAut.conj (π x)).toMonoidHom = (TQ : Subgroup Q) := by
        rw [hTQcoe]
        calc (((T : Subgroup S).subgroupOf P).map π).map (MulAut.conj (π x)).toMonoidHom
            = ((T : Subgroup S).subgroupOf P).map
                ((MulAut.conj (π x)).toMonoidHom.comp π) := Subgroup.map_map _ _ _
          _ = ((T : Subgroup S).subgroupOf P).map (π.comp (MulAut.conj x).toMonoidHom) := by
              rw [hcomp]
          _ = (((T : Subgroup S).subgroupOf P).map (MulAut.conj x).toMonoidHom).map π :=
              (Subgroup.map_map _ _ _).symm
          _ = ((T : Subgroup S).subgroupOf P).map π := by rw [hxTP]
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hgoal
    let M : Subgroup Q := B ⊔ (TQ : Subgroup Q)
    have hBM : B ≤ M := le_sup_left
    have hTM : (TQ : Subgroup Q) ≤ M := le_sup_right
    have hMnorm : M ≤ Subgroup.normalizer ((TQ : Sylow 2 Q) : Set Q) :=
      sup_le hBnorm Subgroup.le_normalizer
    have hTbarNormal : ((TQ : Subgroup Q).subgroupOf M).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hTM).mpr hMnorm
    have : ((TQ : Subgroup Q).subgroupOf M).Normal := hTbarNormal
    let TM : Sylow 2 ↥M := TQ.subtype hTM
    have hTMcoe : ((TM : Sylow 2 ↥M) : Subgroup ↥M) = (TQ : Subgroup Q).subgroupOf M :=
      Sylow.coe_subtype ..
    have hTp : IsPGroup 2 ↥(Subgroup.subgroupOf (TQ : Subgroup Q) M) := by
      have h := TM.isPGroup'
      rwa [hTMcoe] at h
    obtain ⟨BSyl⟩ := Sylow.nonempty (p := 2) (G := ↥B)
    have hBSylne : (BSyl : Subgroup ↥B) ≠ ⊥ := Sylow.ne_bot_of_dvd_card BSyl hB2
    let P₂ : Subgroup ↥M := (BSyl : Subgroup ↥B).map (Subgroup.inclusion hBM)
    have hP₂p : IsPGroup 2 ↥P₂ := BSyl.isPGroup'.map (Subgroup.inclusion hBM)
    obtain ⟨Q₂, hP₂Q₂⟩ := IsPGroup.exists_le_sylow hP₂p
    have hP₂TM : P₂ ≤ Subgroup.subgroupOf (TQ : Subgroup Q) M := by
      have hle : ((TM : Sylow 2 ↥M) : Subgroup ↥M) ≤ (Q₂ : Subgroup ↥M) := by
        rw [hTMcoe]
        exact IsPGroup.le_sylow_of_normal hTp Q₂
      have hQ₂ : (Q₂ : Subgroup ↥M) = ((TM : Sylow 2 ↥M) : Subgroup ↥M) :=
        Sylow.is_maximal' TM Q₂.isPGroup' hle
      rw [hQ₂, hTMcoe] at hP₂Q₂
      exact hP₂Q₂
    have hmeet : B ⊓ (TQ : Subgroup Q) ≠ ⊥ := by
      have hlt : (⊥ : Subgroup ↥B) < (BSyl : Subgroup ↥B) :=
        lt_of_le_of_ne bot_le (Ne.symm hBSylne)
      obtain ⟨x, hx, hx0⟩ := SetLike.exists_of_lt hlt
      intro hbot
      have hxT : (Subgroup.inclusion hBM x : ↥M) ∈ (TQ : Subgroup Q).subgroupOf M :=
        hP₂TM (Subgroup.mem_map_of_mem (Subgroup.inclusion hBM) hx)
      have hmem : (x : Q) ∈ B ⊓ (TQ : Subgroup Q) := ⟨x.2, hxT⟩
      rw [hbot] at hmem
      have hx1 : (x : Q) = 1 := Subgroup.mem_bot.mp hmem
      exact hx0 (Subgroup.mem_bot.mpr (Subtype.ext hx1))
    let ψ : ↥B →* ↥M ⧸ (TQ : Subgroup Q).subgroupOf M :=
      (QuotientGroup.mk' ((TQ : Subgroup Q).subgroupOf M)).comp (Subgroup.inclusion hBM)
    have hker : ψ.ker = Subgroup.subgroupOf (B ⊓ (TQ : Subgroup Q)) B := by
      ext x
      show ψ x = 1 ↔ (x : Q) ∈ B ⊓ (TQ : Subgroup Q)
      rw [Subgroup.mem_inf]
      constructor
      · intro hx
        have hx' : (Subgroup.inclusion hBM x : ↥M) ∈ Subgroup.subgroupOf (TQ : Subgroup Q) M :=
          (QuotientGroup.eq_one_iff (Subgroup.inclusion hBM x)).mp hx
        exact ⟨x.2, hx'⟩
      · rintro ⟨-, hx⟩
        exact (QuotientGroup.eq_one_iff (Subgroup.inclusion hBM x)).mpr hx
    have hker_ne_bot : ψ.ker ≠ ⊥ := by
      intro hbot
      have hlt : (⊥ : Subgroup Q) < B ⊓ (TQ : Subgroup Q) :=
        lt_of_le_of_ne bot_le (Ne.symm hmeet)
      obtain ⟨y, hy, hy0⟩ := SetLike.exists_of_lt hlt
      have hmem : (⟨y, hy.1⟩ : ↥B) ∈ ψ.ker := by
        have h2 : (QuotientGroup.mk' (Subgroup.subgroupOf (TQ : Subgroup Q) M))
            (Subgroup.inclusion hBM ⟨y, hy.1⟩) = 1 :=
          (QuotientGroup.eq_one_iff (Subgroup.inclusion hBM ⟨y, hy.1⟩)).mpr hy.2
        exact h2
      rw [hbot] at hmem
      have hy1 : (⟨y, hy.1⟩ : ↥B) = 1 := by simpa using hmem
      exact hy0 (Subgroup.mem_bot.mpr (congrArg Subtype.val hy1))
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ψ.ker with hbot | htop
    · exact hker_ne_bot hbot
    ·
      have hBleT : B ≤ (TQ : Subgroup Q) := by
        intro b hb
        have hmem : (⟨b, hb⟩ : ↥B) ∈ ψ.ker := htop ▸ Subgroup.mem_top (⟨b, hb⟩ : ↥B)
        have hmem' : Subgroup.inclusion hBM ⟨b, hb⟩ ∈
            Subgroup.subgroupOf (TQ : Subgroup Q) M :=
          (QuotientGroup.eq_one_iff (Subgroup.inclusion hBM ⟨b, hb⟩)).mp hmem
        exact hmem'
      have hBp : IsPGroup 2 ↥B := TQ.isPGroup'.to_le hBleT
      have hcenter : Subgroup.center ↥B = ⊥ ∨ Subgroup.center ↥B = ⊤ :=
        IsSimpleGroup.eq_bot_or_eq_top_of_normal (G := ↥B) (Subgroup.center ↥B)
      have hcenter_ne_bot : Subgroup.center ↥B ≠ ⊥ := by
        intro hcb
        have hnt : Nontrivial ↥(Subgroup.center ↥B) := hBp.center_nontrivial
        rw [hcb] at hnt
        exact (not_nontrivial_iff_subsingleton.mpr inferInstance) hnt
      have hcenter_top : Subgroup.center ↥B = ⊤ := hcenter.resolve_left hcenter_ne_bot
      have hcomm : ⁅(⊤ : Subgroup ↥B), (⊤ : Subgroup ↥B)⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro x _
        rw [Subgroup.mem_centralizer_iff]
        intro y _
        have hx' : x ∈ Subgroup.center ↥B := hcenter_top ▸ Subgroup.mem_top x
        exact Subgroup.mem_center_iff.mp hx' y
      have hbot_top : (⊥ : Subgroup ↥B) = ⊤ := by
        rw [← hcomm, ← _root_.commutator_def, hB.2.2.1]
      exact bot_ne_top hbot_top
  ·
    have hV2 : IsPGroup 2 V := CFSG.pCore_isPGroup
    have hV3 : ¬ 3 ∣ Nat.card ↥V := by
      obtain ⟨n, hn⟩ := hV2.exists_card_eq
      rw [hn]
      intro h3
      have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
      omega
    have hEtilde3 : ¬ 3 ∣ Nat.card Etilde := by
      have hcard : Nat.card ↥E' = Nat.card ↥V * Nat.card ↥E :=
        CFSG.ABGLocalTools.card_comap_mk' V E
      rw [show Nat.card Etilde = Nat.card ↥E' from
        Subgroup.card_map_of_injective P.subtype_injective, hcard]
      intro h3
      rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h | h
      · exact hV3 h
      · exact hE3 h
    have hT3 : ¬ 3 ∣ Nat.card (T : Subgroup S) := by
      obtain ⟨n, hn⟩ := T.isPGroup'.exists_card_eq
      rw [hn]
      intro h3
      have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
      omega
    have hnorm : (T : Subgroup S) ≤ Subgroup.normalizer (Etilde : Set S) :=
      Subgroup.le_normalizer.trans (hTU.trans (CFSG.ABGLocalTools.le_normalizer_map_subtype P E'))
    have hformula :=
      CFSG.EvenSmallLie.UnitarySix.YamadaQ.card_sup_mul_card_inf_of_normalizes
        (X := (T : Subgroup S)) (N := Etilde) hnorm
    rw [sup_comm] at hformula
    intro h3
    have h3' : 3 ∣ Nat.card ↥(Etilde ⊔ (T : Subgroup S)) *
        Nat.card ↥((T : Subgroup S) ⊓ Etilde) := dvd_mul_of_dvd_left h3 _
    rw [hformula] at h3'
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3' with h | h
    · exact hT3 h
    · exact hEtilde3 h


end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410
