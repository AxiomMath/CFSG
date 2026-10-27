module

public import CFSG.Quasithin.Background.InternalSecData
public import CFSG.Quasithin.Vol2.Ch10SecA1012Five
public import CFSG.Quasithin.Vol2.Ch10SecA1012Two

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem pCoreOf_eq_bot_of_simple {V : Type} [CommGroup V] [Finite V] {K : Subgroup (MulAut V)}
    [hs : IsSimpleGroup ↥K] (hnc : ∃ a b : ↥K, a * b ≠ b * a) : pCoreOf 2 K = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcen := Six.center_eq_bot hnc
  have hP : CFSG.Open.pCore 2 ↥K = ⊥ := by
    rcases hs.eq_bot_or_eq_top_of_normal (CFSG.Open.pCore 2 ↥K) with h | h
    · exact h
    · exfalso
      have hp : IsPGroup 2 ↥K := by
        have hpc := CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥K) 2
        rw [h] at hpc
        exact hpc.of_equiv Subgroup.topEquiv
      have : Nontrivial ↥K := hs.toNontrivial
      have hnt := hp.center_nontrivial
      rw [hcen] at hnt
      exact (not_nontrivial_iff_subsingleton.mpr inferInstance) hnt
  unfold pCoreOf
  rw [hP, Subgroup.map_bot]

theorem commutator_fsuUL_eq (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hyp : Ch10.Hyp10 G T L I) (hUI : fsuUL T L I = I) : ⁅fsuUL T L I, L⁆ = fsuUL T L I := by
  obtain ⟨t, ht, htn⟩ : ∃ t ∈ T, t ∉ Subgroup.normalizer (L : Set G) := by
    by_contra hne
    push Not at hne
    exact hyp.not_normal hne
  obtain ⟨_, -, -, ha, -⟩ := hyp.three
  have hUt := (ha t ht htn).2.2
  have hL0I : fsuL0 T L ≤ Subgroup.normalizer (I : Set G) := hyp.fsu.irrPlus.2.2.1
  have h0 : ⁅I, CFSG.conjugate L t⁆ = ⊥ :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr (hUI ▸ hUt)
  have hsup := commutator_sup_left_of_le (X := fsuL0 T L ⊔ I) le_sup_right
    ((le_fsuL0 T L).trans le_sup_left) ((conjugate_le_fsuL0 ht).trans le_sup_left)
    (sup_le hL0I Subgroup.le_normalizer)
  rw [← fsuL0_eq_sup h37 h38 hyp ht htn, h0, sup_bot_eq] at hsup
  rw [hUI, ← hsup]
  exact hyp.fsu.irrPlus.2.2.2.1

theorem inf_centralizer_fsuUL_eq (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h322 : TmpL6_3_2_2_two) (hyp : Ch10.Hyp10 G T L I)
    (hne : ⁅fsuUL T L I, L⁆ ≠ ⊥) :
    L ⊓ Subgroup.centralizer (fsuUL T L I : Set G) = pCoreOf 2 L := by
  have hLV : L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    (le_fsuL0 T L).trans (fsuL0_le_normalizer_fsuVM T L I)
  have hUV : fsuUL T L I ≤ fsuVM T L I := Subgroup.le_normalizer_iff_commutator_le_left.mp hLV
  have hLU : L ≤ Subgroup.normalizer (fsuUL T L I : Set G) :=
    le_normalizer_commutator hLV Subgroup.le_normalizer
  exact le_antisymm (inf_centralizer_le_pCoreOf h37 h38 hyp hLU hne)
    (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 L)
      ((pCoreOf_le_centralizer_fsuVM h322 hyp).trans (Subgroup.centralizer_le hUV)))

theorem autOn_sup_eq_autOn_inf (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hyp : Ch10.Hyp10 G T L I) :
    autOn (fsuL0 T L ⊔ T) (fsuUL T L I) =
      autOn ((fsuL0 T L ⊔ T) ⊓ Subgroup.normalizer (L : Set G)) (fsuUL T L I) := by
  obtain ⟨t, ht, htn⟩ : ∃ t ∈ T, t ∉ Subgroup.normalizer (L : Set G) := by
    by_contra hne
    push Not at hne
    exact hyp.not_normal hne
  refine le_antisymm (fun φ hφ => ?_) (A4.autOn_mono inf_le_left)
  obtain ⟨g, hgX, rfl⟩ := mem_autOn_iff'.mp hφ
  refine mem_autOn_iff'.mpr ⟨g, ⟨hgX, ?_⟩, rfl⟩
  have hgM : (g : G) ∈ fsuM T L := sup_le (fsuL0_le_fsuM T L) (le_fsuM T L) hgX
  rcases conjugate_eq_or h37 h38 hyp ht htn hgM with h | h
  · exact conjugate_eq_self_iff.mp h
  · exfalso
    apply fsuUL_ne_conjugate h37 h38 hyp ht htn
    have h1 : CFSG.conjugate (fsuUL T L I) g = fsuUL T L I := conjugate_eq_self_iff.mpr g.2
    rw [conjugate_commutator_fsuVM hgM, h, ← conjugate_commutator_fsuVM (le_fsuM T L ht)] at h1
    exact h1.symm

theorem isec_of_one
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h322 : TmpL6_3_2_2_two) (hyp : Ch10.Hyp10 G T L I) (hUI : fsuUL T L I = I) :
    InternalSec.ISec (fsuUL T L I) ((fsuL0 T L ⊔ T) ⊓ Subgroup.normalizer (L : Set G)) L
      (Subgroup.centralizer (fsuL0 T L : Set G)) := by
  obtain ⟨t, ht, htn⟩ : ∃ t ∈ T, t ∉ Subgroup.normalizer (L : Set G) := by
    by_contra hne
    push Not at hne
    exact hyp.not_normal hne
  obtain ⟨_, -, -, ha, -⟩ := hyp.three
  have hUt := (ha t ht htn).2.2
  have hel := isElemAbelian_fsuVM hyp
  have hLV : L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    (le_fsuL0 T L).trans (fsuL0_le_normalizer_fsuVM T L I)
  have hHN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    sup_le (fsuL0_le_normalizer_fsuVM T L I) (le_normalizer_fsuVM T L I)
  have hUV : fsuUL T L I ≤ fsuVM T L I := Subgroup.le_normalizer_iff_commutator_le_left.mp hLV
  have hHM : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuL0 T L : Set G) :=
    sup_le (fsuL0_le_fsuM T L) (le_fsuM T L)
  have hcomm := commutator_fsuUL_eq h37 h38 hyp hUI
  have hne : ⁅fsuUL T L I, L⁆ ≠ ⊥ := by
    rw [hcomm, hUI]
    exact hyp.fsu.irrPlus.2.1
  have hYU : (fsuL0 T L ⊔ T) ⊓ Subgroup.normalizer (L : Set G) ≤
      Subgroup.normalizer (fsuUL T L I : Set G) :=
    le_normalizer_commutator (inf_le_left.trans hHN) inf_le_right
  have hLU : L ≤ Subgroup.normalizer (fsuUL T L I : Set G) :=
    le_normalizer_commutator hLV Subgroup.le_normalizer
  have hCU := inf_centralizer_fsuUL_eq h37 h38 h322 hyp hne
  have hs := isSimpleGroup_of_not_normal h37 h38 hyp.fsu.simple hyp.fsu.nonabelian hyp.fsu.qtke
    hyp.fsu.faithful hyp.not_normal
  set e := autOnEquivQuotOf hLU hCU
  have hsU : IsSimpleGroup ↥(autOn L (fsuUL T L I)) := e.isSimpleGroup
  have hncU : ∃ a b : ↥(autOn L (fsuUL T L I)), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := exists_ne_of_isQuasisimple hyp.fsu.quasisimple
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    simpa using congrArg e h
  have hUab : IsMulCommutative ↥(fsuUL T L I) := isMulCommutative_of_le hUV
  refine ⟨fun u hu => hel.2 u (hUV hu), hYU, le_inf ((le_fsuL0 T L).trans le_sup_left)
    Subgroup.le_normalizer, inf_le_right, fun y hy => ?_, ?_, ?_, hcomm, ?_, ?_,
    pCoreOf_eq_bot_of_simple hncU, isQuasisimple_of_simple' hncU⟩
  ·
    obtain ⟨e', he'⟩ := InternalSec.two_of_sup hyp.fsu.sylow.1 (le_fsuM T L) y hy.1
    refine ⟨e', ?_⟩
    rw [fsuL0_eq_sup h37 h38 hyp ht htn] at he'
    exact sup_le_sup_left (Subgroup.le_centralizer_iff.mp hUt) L he'
  ·
    intro y hy
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hYU hy, le_normalizer_centralizer (inf_le_left.trans hHM) hy⟩
  ·
    exact inf_le_right.trans (Subgroup.centralizer_le (le_fsuL0 T L))
  ·
    intro hle
    apply hne
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hle.trans (Subgroup.centralizer_le (le_fsuL0 T L))
  ·
    intro J hCJ hJU hLJ
    have hL0J : fsuL0 T L ≤ Subgroup.normalizer (J : Set G) := by
      rw [fsuL0_eq_sup h37 h38 hyp ht htn]
      refine sup_le hLJ fun x hx => ?_
      have hxJ : x ∈ Subgroup.centralizer (J : Set G) :=
        Subgroup.centralizer_le hJU (Subgroup.le_centralizer_iff.mp hUt hx)
      rw [Subgroup.mem_normalizer_iff]
      intro j
      constructor
      · intro hj
        rw [← Subgroup.mem_centralizer_iff.mp hxJ j hj, mul_inv_cancel_right]
        exact hj
      · intro hj
        have h := Subgroup.mem_centralizer_iff.mp hxJ _ hj
        have e2 : j = x * j * x⁻¹ := by
          calc j = x⁻¹ * (x * j * x⁻¹ * x) := by group
            _ = x⁻¹ * (x * (x * j * x⁻¹)) := by rw [h]
            _ = x * j * x⁻¹ := by group
        rw [e2]
        exact hj
    rw [hUI] at hCJ hJU ⊢
    exact hyp.fsu.irrPlus.2.2.2.2.2.1 J hCJ hJU hL0J

end CFSG.Quasithin.Vol2.Ch10.SecA
