module

public import CFSG.RankThree.PartTwo.Sec17.C174Para2
public import CFSG.RankThree.PartTwo.Sec17.C174Delta
public import CFSG.RankThree.PartTwo.Sec17.Item17Res13ProofKb
public import CFSG.RankThree.PartTwo.Sec17.Item17Res14ProofKF

public section

namespace CFSG.RankThree.PartTwo.Sec17.C174

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec17
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}


theorem not_three_dvd_delta_centralizer_of_item143 (h143 : Item143 A (lB A))
    (h : Sec17Std G A c L Y₀)
    (hΩ : omegaA A = {Subgroup.zpowers c})
    (hJ : ¬ Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {b : G} (hb : b ∈ A) (hb1 : b ≠ 1) (hbΩ : Subgroup.zpowers b ∉ omegaA A) :
    ¬ 3 ∣ Nat.card ↥(delta A (lB A) (Subgroup.centralizer ({b} : Set G))) := by

  have hbot : (⊥ : Subgroup G) ∈
      invariantPiSubgroups (delta A (lB A) (Subgroup.centralizer ({b} : Set G))) A (piCompl 3) := by
    simp only [invariantPiSubgroups, Set.mem_setOf_eq]
    refine ⟨bot_le, ?_, ?_⟩
    · intro p hp
      simp at hp
      exact absurd hp p.prop.ne_one
    · intro a _
      rw [Subgroup.mem_normalizer_iff]
      intro g
      simp
  obtain ⟨Q, -, hQ⟩ := Finite.exists_le_maximal (p := fun X : Subgroup G =>
    X ∈ invariantPiSubgroups (delta A (lB A) (Subgroup.centralizer ({b} : Set G))) A (piCompl 3))
    hbot
  have hmain := h143 b hb hb1 hbΩ Q hQ
  rcases hmain.2 with hEq | ⟨b', d, Lb, hb', hLb, hJb, -⟩
  · rw [hEq]
    have hCle : pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ≤
        Subgroup.centralizer ({b} : Set G) :=
      (CFSG.RankThree.PartTwo.Sec14.pPrimeCoreOf_le 3 _).trans
        (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hb))
    have hnorm : pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔
        pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ≤
        Subgroup.normalizer ((pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) :
          Subgroup G) : Set G) :=
      sup_le Subgroup.le_normalizer
        (hCle.trans (CFSG.RankThree.PartTwo.Sec14.le_normalizer_pPrimeCoreOf 3 _))
    exact not_three_dvd_of_normal_sup rfl le_sup_left le_sup_right hnorm
      (CFSG.RankThree.PartTwo.Sec14.coprime_card_pPrimeCoreOf 3 _)
      (CFSG.RankThree.PartTwo.Sec14.coprime_card_pPrimeCoreOf 3 _)
  · exfalso
    have hLL : Lb = L := eq_L_of_mem_lA h.toSec14Std hΩ hb' hLb
    rw [hLL] at hJb
    exact hJ hJb


theorem step174KbM_of_item143
    (h135 : Item135)
    (h143 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec14Std G A c L → Item143 A (lB A))
    (h146 : Item146S14) (h166 : Item166S17) : Step174KbM := by

  intro G _ _ A c L Y₀ h X hXΔ hX3 K hK ⟨n, hn⟩ hθ hcen hAK hY3 b hb hb1 hO2
  have hA : IsE27 A := h.isE27
  have h146' : Item146 A (lB A) := h146 G A c L h.toSec14Std
  have h166' : Item166 A (lB A) := h166 G A c L Y₀ h
  have hKX : K ≤ X := le_of_mem_thetaComponentsIn hK
  have hAX : A ≤ Subgroup.normalizer (X : Set G) := by
    have hN := CFSG.RankThree.PartTwo.Sec14.le_normalizer_delta (A := A) (LB := lB A) X
    rw [← hXΔ] at hN
    exact hN
  have hXQ : X ∈ scriptQ A (lB A) :=
    CFSG.RankThree.PartTwo.Sec16.Proof165.mem_scriptQ_of_three hA h146' hXΔ hAX hX3
  rcases h.a10_or_omega with hA10 | hΩ
  · exact absurd (five_dvd_card_cQuot_of_suzuki h166' h hXΔ hX3 hK ⟨n, hn⟩)
      (not_five_dvd_cQuot_of_a10 h hA10)
  by_cases hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)
  · exact absurd (five_dvd_card_cQuot_of_suzuki h166' h hXΔ hX3 hK ⟨n, hn⟩)
      (not_five_dvd_cQuot_of_j2 h135 h hJ)
  have hbΩ : Subgroup.zpowers b ∉ omegaA A := zpowers_not_mem_omegaA_of_mem_inf h hΩ hb
  have hD3 : ¬ 3 ∣ Nat.card ↥(delta A (lB A) (Subgroup.centralizer ({b} : Set G))) :=
    not_three_dvd_delta_centralizer_of_item143 (h143 G A c L h.toSec14Std) h hΩ hJ hb.1 hb1 hbΩ
  have hDns : ¬ Group.IsSolvable ↥(delta A (lB A) (Subgroup.centralizer ({b} : Set G))) :=
    not_isSolvable_delta_centralizer h hXQ hθ hcen hAK hK hb hb1
  set D := delta A (lB A) (Subgroup.centralizer ({b} : Set G)) with hD
  have hDtop : D ≠ ⊤ := fun htop =>
    CFSG.RankThree.PartTwo.Sec17.Proof17Res12.centralizer_ne_top h hb1
      (eq_top_iff.mpr (htop ▸ CFSG.RankThree.PartTwo.Sec14.delta_le _))
  have hDΔ : D = delta A (lB A) D := (CFSG.RankThree.PartTwo.Sec14.delta_delta _).symm
  have hDM : D ≤ Subgroup.normalizer (Y₀ : Set G) := by
    obtain ⟨J, hJm, m, hm⟩ := kFact174_holds G A c L Y₀ h D hDΔ hD3 hDns
    exact delta_le_of_suzuki_member h h166' h146' hDtop hDΔ hD3 hJm hm hY3
  have hKC : K ⊓ Subgroup.centralizer ({b} : Set G) ≤ X := inf_le_left.trans hKX
  have hAb : A ≤ Subgroup.centralizer ({b} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr (h.toSec13Data.commute ha hb.1)
  have hAKC : A ≤ Subgroup.normalizer
      ((K ⊓ Subgroup.centralizer ({b} : Set G) : Subgroup G) : Set G) :=
    Late.le_normalizer_inf hAK (hAb.trans Subgroup.le_normalizer)
  have hQ : K ⊓ Subgroup.centralizer ({b} : Set G) ∈ scriptQ A (lB A) :=
    CFSG.RankThree.PartTwo.Sec14.mem_scriptQ_of_le hXQ hKC hAKC
  have hKCD : K ⊓ Subgroup.centralizer ({b} : Set G) ≤ D :=
    CFSG.RankThree.PartTwo.Sec14.le_delta hQ inf_le_right
  have hJD : inSubgroup perfectResidual (K ⊓ Subgroup.centralizer ({b} : Set G)) ≤ D :=
    (Subgroup.map_subtype_le _).trans hKCD
  have hDcop : Nat.Coprime 3 (Nat.card ↥D) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hD3
  have hTop : (⊤ : Subgroup ↥D) ≤ CFSG.pPrimeCore 3 ↥D :=
    CFSG.le_pPrimeCore_of_normal_coprime (N := (⊤ : Subgroup ↥D)) inferInstance
      (by rw [Subgroup.card_top]; exact hDcop)
  have hDpc : D ≤ pPrimeCoreOf 3 D := by
    intro x hx
    exact ⟨⟨x, hx⟩, hTop (Subgroup.mem_top _), rfl⟩
  refine ⟨hJD.trans hDpc, fun d hd => ?_⟩
  intro y hy
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
  have hzD : z ∈ D := hJD hz
  exact hDM (show (MulAut.conj d).toMonoidHom z ∈ D from
    D.mul_mem (D.mul_mem hd hzD) (D.inv_mem hd))


end CFSG.RankThree.PartTwo.Sec17.C174
