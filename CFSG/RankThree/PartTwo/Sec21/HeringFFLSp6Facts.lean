module

public import CFSG.RankThree.PartTwo.Sec21.HeringFFLKE9
public import CFSG.RankThree.PartTwo.Sec21.HeringFFLE27
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalModelFactsCharTwo
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.ClassicalEA

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG.Open (IsElemAbelian)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

variable {Y : Type} [Group Y]

theorem center_eq_bot_of_sp6Model (h : StatedClassicalModel Y .PSp 3 2 1) :
    Subgroup.center Y = ⊥ := by
  have hS : IsSimpleGroup Y :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp Y 3 2 1 h
  obtain ⟨e⟩ := nonempty_mulEquiv_H6_of_stated h
  have hcard : Nat.card Y = 1451520 := by
    rw [Nat.card_congr e.toEquiv, CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two.card_H6]
  rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center Y) with hb | ht
  · exact hb
  ·
    haveI : IsMulCommutative Y := Subgroup.center_eq_top_iff.mp ht
    have hp : (Nat.card Y).Prime := Group.is_simple_iff_prime_card.mp hS
    rw [hcard] at hp
    norm_num at hp

theorem exists_eq_conj_of_sp6Model (h : StatedClassicalModel Y .PSp 3 2 1) (α : MulAut Y) :
    ∃ y : Y, α = MulAut.conj y := by
  obtain ⟨e⟩ := nonempty_mulEquiv_H6_of_stated h
  obtain ⟨y', hy'⟩ := CFSG.LocalAnalysis.GLTheoremB.MovingAround.ClassicalEA.statedSp_aut_inner
    (n := 3) le_rfl ((e.symm.trans α).trans e)
  refine ⟨e.symm y', MulEquiv.ext fun x => ?_⟩
  apply e.injective
  have h1 := DFunLike.congr_fun hy' (e x)
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.conj_apply] at h1
  simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, MulAut.conj_apply]
  exact h1

theorem exists_e27_of_sp6Model (h : StatedClassicalModel Y .PSp 3 2 1) :
    ∃ E : Subgroup Y, IsElemAbelian 3 E ∧ Nat.card E = 27 := by
  obtain ⟨e⟩ := nonempty_mulEquiv_H6_of_stated h
  obtain ⟨E6, hE6, hE627⟩ := CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two.exists_e27_H6
  have hE' : IsElemAbelian 3 (E6.map e.symm.toMonoidHom) :=
    CFSG.Open.IsElemAbelian.map hE6 _
  refine ⟨E6.map e.symm.toMonoidHom, hE', ?_⟩
  rw [Subgroup.card_map_of_injective (f := e.symm.toMonoidHom) e.symm.injective]
  exact hE627

theorem exists_moved_two_of_sp6Model [Finite Y] (h : StatedClassicalModel Y .PSp 3 2 1)
    {F T₁ : Subgroup Y} (hF : IsPGroup 3 F) (hF1 : F ≠ ⊥) (hT₁ : IsPGroup 2 T₁) (hT₁1 : T₁ ≠ ⊥)
    (hFT : F ≤ Subgroup.normalizer (T₁ : Set Y)) :
    ∃ T : Subgroup Y, IsPGroup 2 T ∧ F ≤ Subgroup.normalizer (T : Set Y) ∧
      ¬ F ≤ Subgroup.centralizer (T : Set Y) := by
  by_cases hC : F ≤ Subgroup.centralizer (T₁ : Set Y)
  ·
    have hcard : Nat.card T₁ ≠ 1 := fun h1 => hT₁1 ((Subgroup.eq_bot_iff_card T₁).mpr h1)
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥T₁) 2
      ((hT₁.card_eq_or_dvd).resolve_left hcard)
    have hu : orderOf (x : Y) = 2 := (Subgroup.orderOf_coe x).trans hx
    have hFM : F ≤ Subgroup.centralizer ({(x : Y)} : Set Y) := fun f hf =>
      Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp (hC hf) (x : Y) x.2).symm
    have hCP : CFSG.IsCharacteristicP 2 (Subgroup.centralizer ({(x : Y)} : Set Y)) :=
      CFSG.ComponentClassification.RankTwoClassical.isCharacteristicP_centralizer_of_psp_model
        h (x : Y) hu
    set M := Subgroup.centralizer ({(x : Y)} : Set Y) with hMdef
    set P := CFSG.pCore 2 M with hPdef
    have hPn : P.Normal := CFSG.pCore_normal
    have hPp : IsPGroup 2 P := CFSG.pCore_isPGroup
    have hTp : IsPGroup 2 (P.map M.subtype) := hPp.map M.subtype
    have hconj : ∀ g : Y, g ∈ M → ∀ n ∈ P.map M.subtype, g * n * g⁻¹ ∈ P.map M.subtype := by
      rintro g hg _ ⟨y, hyP, rfl⟩
      exact ⟨⟨g, hg⟩ * y * ⟨g, hg⟩⁻¹, hPn.conj_mem y hyP _, rfl⟩
    refine ⟨P.map M.subtype, hTp, ?_, ?_⟩
    · intro f hf
      have hfM : f ∈ M := hFM hf
      rw [Subgroup.mem_set_normalizer_iff]
      intro n
      constructor
      · exact hconj f hfM n
      · intro hn
        have h1 := hconj f⁻¹ (M.inv_mem hfM) (f * n * f⁻¹) hn
        rwa [show f⁻¹ * (f * n * f⁻¹) * f⁻¹⁻¹ = n by group] at h1
    ·
      intro hFc
      obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hF1
      have hfa : (a : Y) ≠ 1 := fun h' => ha1 (Subtype.ext h')
      have hFa : (a : Y) ∈ F := a.2
      have hMa : (a : Y) ∈ M := hFM hFa
      have hgc : (⟨(a : Y), hMa⟩ : M) ∈ Subgroup.centralizer (P : Set M) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hyT : (y : Y) ∈ P.map M.subtype := ⟨y, hy, rfl⟩
        exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hFc hFa) (y : Y) hyT)
      have hgP : (⟨(a : Y), hMa⟩ : M) ∈ P :=
        (show Subgroup.centralizer (P : Set M) ≤ P from hCP) hgc
      have haT : (a : Y) ∈ P.map M.subtype := ⟨_, hgP, rfl⟩
      obtain ⟨j, hj⟩ := hTp ⟨(a : Y), haT⟩
      obtain ⟨k, hk⟩ := hF ⟨(a : Y), hFa⟩
      have hj' : (a : Y) ^ 2 ^ j = 1 := congrArg Subtype.val hj
      have hk' : (a : Y) ^ 3 ^ k = 1 := congrArg Subtype.val hk
      have hcop : Nat.Coprime (2 ^ j) (3 ^ k) := Nat.Coprime.pow j k (by norm_num)
      have hord : orderOf (a : Y) = 1 :=
        Nat.Coprime.eq_one_of_dvd
          (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hj') hcop)
          (orderOf_dvd_of_pow_eq_one hk')
      exact hfa (orderOf_eq_one_iff.mp hord)
  · exact ⟨T₁, hT₁, hFT, hC⟩

end CFSG.RankThree.PartTwo.Sec21
