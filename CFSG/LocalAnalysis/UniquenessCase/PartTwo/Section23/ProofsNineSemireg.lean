module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsNineK
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.SemiregularBar

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem barImage_sup_pCoreOf {M Q : Subgroup G} (hQM : Q ≤ M) :
    barImage M (pCoreOf 2 M ⊔ Q) = barImage M Q := by
  have h : barImage M (pCoreOf 2 M) = ⊥ := uc22p22u_barImage_pCore M
  unfold barImage at h ⊢
  rw [Subgroup.subgroupOf_sup (uc22p21c_pCoreOf_le M) hQM, Subgroup.map_sup, h, bot_sup_eq]

theorem injective_barImage_map {M Q : Subgroup G} {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hQM : Q ≤ M) (hQq : IsPGroup q Q) :
    Function.Injective ((uc22p21cPi M).comp (Subgroup.inclusion hQM)) := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  have hdisj : Q ⊓ pCoreOf 2 M = ⊥ :=
    disjoint_iff.1 (IsPGroup.disjoint_of_ne q 2 hq2 Q (pCoreOf 2 M) hQq
      (uc22p21c_isPGroup_pCoreOf M))
  intro x y hxy
  have h1 : ((uc22p21cPi M).comp (Subgroup.inclusion hQM)) (x * y⁻¹) = 1 := by
    rw [map_mul, map_inv, hxy, mul_inv_cancel]
  have h2 : ((x * y⁻¹ : ↥Q) : G) ∈ pCoreOf 2 M := by
    refine ⟨⟨((x * y⁻¹ : ↥Q) : G), hQM (x * y⁻¹).2⟩, ?_, rfl⟩
    have h1' : uc22p21cPi M ⟨((x * y⁻¹ : ↥Q) : G), hQM (x * y⁻¹).2⟩ = 1 := by
      simpa [Subgroup.inclusion] using h1
    exact (QuotientGroup.eq_one_iff _).1 h1'
  have h3 : ((x * y⁻¹ : ↥Q) : G) = 1 := by
    have hmem : ((x * y⁻¹ : ↥Q) : G) ∈ (⊥ : Subgroup G) := by
      rw [← hdisj]
      exact Subgroup.mem_inf.2 ⟨(x * y⁻¹).2, h2⟩
    exact Subgroup.mem_bot.1 hmem
  have h4 : x * y⁻¹ = 1 := Subtype.ext h3
  calc x = x * y⁻¹ * y := by group
    _ = y := by rw [h4, one_mul]

private theorem triple_commutator_barImage {M Q : Subgroup G} {f : ↥Q →* Bar2 M}
    (hfr : (⊤ : Subgroup ↥Q).map f = barImage M Q) (hQcl : ⁅⁅Q, Q⁆, Q⁆ = ⊥) :
    ⁅⁅barImage M Q, barImage M Q⁆, barImage M Q⁆ = ⊥ := by
  have htopcl :
      ⁅⁅(⊤ : Subgroup ↥Q), (⊤ : Subgroup ↥Q)⁆, (⊤ : Subgroup ↥Q)⁆ = ⊥ := by
    refine (Subgroup.map_eq_bot_iff_of_injective
      (⁅⁅(⊤ : Subgroup ↥Q), (⊤ : Subgroup ↥Q)⁆, (⊤ : Subgroup ↥Q)⁆)
      Q.subtype_injective).mp ?_
    rw [Subgroup.map_commutator, Subgroup.map_commutator, Subgroup.map_top,
      Subgroup.range_subtype, hQcl]
  rw [← hfr, ← Subgroup.map_commutator, ← Subgroup.map_commutator, htopcl,
    Subgroup.map_bot]

private theorem barImage_Q_props {M Q : Subgroup G} {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hQM : Q ≤ M) (hQq : IsPGroup q Q) (hQnc : ¬ IsCyclic Q)
    (hQexp : ∀ x ∈ Q, x ^ q = 1) (hQcl : ⁅⁅Q, Q⁆, Q⁆ = ⊥)
    (hnorm : M ≤ Subgroup.normalizer ((pCoreOf 2 M ⊔ Q : Subgroup G) : Set G)) :
    (barImage M Q).Normal ∧ IsPGroup q (barImage M Q) ∧ ¬ IsCyclic (barImage M Q) ∧
      (∀ y ∈ barImage M Q, y ^ q = 1) ∧
        ⁅⁅barImage M Q, barImage M Q⁆, barImage M Q⁆ = ⊥ := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  let f : ↥Q →* Bar2 M := (uc22p21cPi M).comp (Subgroup.inclusion hQM)
  let Dbar : Subgroup (Bar2 M) := barImage M Q
  have hfr : (⊤ : Subgroup ↥Q).map f = Dbar := by
    ext y
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨x, -, rfl⟩
      exact uc22p21c_mem_barImage.2 ⟨⟨x, hQM x.2⟩, x.2, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨⟨(m : G), hm⟩, Subgroup.mem_top _, rfl⟩
  have hDn : Dbar.Normal := by
    have h := uc22p22u_barImage_normal (M := M) (X := pCoreOf 2 M ⊔ Q) hnorm
    rwa [barImage_sup_pCoreOf hQM] at h
  let f' : ↥Q →* ↥Dbar := f.codRestrict Dbar fun x => by
    rw [← hfr]
    exact Subgroup.mem_map_of_mem f (Subgroup.mem_top x)
  have hf' : Function.Surjective f' := by
    intro y
    have hy : (y : Bar2 M) ∈ (⊤ : Subgroup ↥Q).map f := by
      rw [hfr]
      exact y.2
    obtain ⟨x, -, hx⟩ := Subgroup.mem_map.1 hy
    exact ⟨x, Subtype.ext hx⟩
  have hf'_inj : Function.Injective f' := fun x y hxy =>
    injective_barImage_map hq hq2 hQM hQq (congrArg Subtype.val hxy)
  refine ⟨hDn, hQq.of_surjective f' hf', ?_, ?_,
    triple_commutator_barImage hfr hQcl⟩
  · intro hc
    exact hQnc (isCyclic_of_injective (G' := ↥Dbar) (G := ↥Q) f' hf'_inj)
  · intro y hy
    change y ∈ Dbar at hy
    rw [← hfr] at hy
    obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.1 hy
    have hxq : x ^ q = 1 := Subtype.ext (hQexp x x.2)
    rw [← map_pow, hxq, map_one]

theorem s23_9_Semireg_of (D : Data G) (Ch : Choice2011 G) (h71 : S23_7_1 D Ch)
    (hsig : D.sig.Nonempty) : S23_9_Semireg D Ch := by
  classical
  intro h1930 c q hq hq2 Q hQM hQq hQnc hQexp hQcl hnorm e _heM hXhyp
  by_contra hXne
  let X : Subgroup G := Q ⊓ Subgroup.centralizer ({e} : Set G)
  have hXle : X ≤ D.M ⊓ Subgroup.centralizer ({e} : Set G) :=
    le_inf (inf_le_left.trans hQM) inf_le_right
  have hXq : IsPGroup q ↥X := hQq.to_inf_left
  have hXfacts := hXhyp X hXne hXq hXle
  have hXU : X ∉ uniqueSet D.M := hXfacts.1
  have hqsig : q ∉ D.sig := hXfacts.2
  obtain ⟨p, hp⟩ := hsig
  obtain ⟨hDn, hDq, hDnc, hDexp, hDcl⟩ :=
    barImage_Q_props hq hq2 hQM hQq hQnc hQexp hQcl hnorm
  have hXP : X ≤ barPreimage D.M (barImage D.M Q) := by
    intro x hx
    rw [uc22p21c_mem_barPreimage]
    exact ⟨hQM hx.1, uc22p21c_mem_barImage.2 ⟨⟨x, hQM hx.1⟩, hx.1, rfl⟩⟩
  exact hXU (Ctx23L.mem_uniqueSet_of_le_barPreimage c h1930 h71 hp hq hq2 hqsig hDn hDq hDnc
    hDexp hDcl hXne hXq hXP)

end CFSG.LocalAnalysis.UniquenessCase.UC22
