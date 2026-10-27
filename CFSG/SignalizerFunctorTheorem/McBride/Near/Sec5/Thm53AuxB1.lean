module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec5.Thm51
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec4.Thm41AuxBasic
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec5.Thm52AuxK

public section

open CFSG.Open
open scoped commutatorElement

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

namespace Thm53B

variable {G : Type u} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {θ : G → Subgroup G}

structure BotData (p : ℕ) (A : Subgroup G) (θ : G → Subgroup G) : Prop where
  nearFunctor : NearFunctor p A θ
  bot_mem : (⊥ : Subgroup G) ∈ dset p A θ
  thetaLG_eq : thetaLG p A θ ⊥ = ⊥

theorem bot_facts
    (h : Counterexample p A θ)
    (h58 : ∃ Y ∈ dset p A θ, thetaMG p A θ Y ∉ assoc p A θ) :
    (⊥ : Subgroup G) ∈ dset p A θ ∧ thetaMG p A θ ⊥ ∉ assoc p A θ ∧
      thetaLG p A θ ⊥ = ⊥ := by
  have hθ := h.hyp.nearFunctor
  obtain ⟨Y, hY, hMG⟩ := h58
  have hL : thetaLG p A θ Y = ⊥ := (h.thetaMG_mem_or_thetaLG_eq_bot hY).resolve_left hMG
  have hY0 : Y = ⊥ := by
    obtain ⟨P, hP, rfl⟩ := hY
    have hXm : P.1 ⊔ dsub A θ ∈ mtil p A θ := sup_dsub_mem_mtil hθ hP.1
    have hPY : P ∈ pairsYX p A θ (dsub A θ ⊓ P.2) (P.1 ⊔ dsub A θ) :=
      ⟨⟨hP, inf_comm _ _⟩, le_sup_left⟩
    have hc : P.1 ⊔ dsub A θ ∈ cset p A θ (dsub A θ ⊓ P.2) := ⟨hXm, P, hPY⟩
    have h2 : P.2 ≤ thetaLG p A θ (dsub A θ ⊓ P.2) :=
      (le_iSup₂_of_le (f := fun P' (_ : P' ∈ pairsYX p A θ (dsub A θ ⊓ P.2)
        (P.1 ⊔ dsub A θ)) => P'.2) P hPY le_rfl).trans
        (le_iSup₂ (f := fun X (_ : X ∈ cset p A θ (dsub A θ ⊓ P.2)) =>
          thetaL p A θ (dsub A θ ⊓ P.2) X) _ hc)
    rw [hL] at h2
    rw [le_bot_iff.mp h2, inf_bot_eq]
  subst hY0
  exact ⟨hY, hMG, hL⟩

section Bot

variable (hb : BotData p A θ)

include hb

omit [Finite G] in
theorem thetaL_bot_eq_bot {X : Subgroup G} (hX : X ∈ cset p A θ ⊥) : thetaL p A θ ⊥ X = ⊥ :=
  le_bot_iff.mp ((le_iSup₂_of_le (f := fun X (_ : X ∈ cset p A θ ⊥) => thetaL p A θ ⊥ X) X hX
    le_rfl).trans hb.thetaLG_eq.le)

theorem thetaM_bot_pair
    {X : Subgroup G} (hX : X ∈ cset p A θ ⊥) :
    (thetaM p A θ ⊥ X, (⊥ : Subgroup G)) ∈ pairsP p A θ ∧ thetaM p A θ ⊥ X ≤ X := by
  have hP := thetaM_thetaL_mem_pairsYX hb.nearFunctor hb.bot_mem hX
  rw [thetaL_bot_eq_bot hb hX] at hP
  exact ⟨hP.1.1, hP.2⟩

omit hb in
theorem not_isSolvable_of_mem_cset (hθ : NearFunctor p A θ) {Y X : Subgroup G}
    (hX : X ∈ cset p A θ Y) : ¬ Group.IsSolvable X := by
  obtain ⟨hXm, P, hP⟩ := hX
  have hP' : P ∈ iPairs A X := by
    have : P ∈ iPairsY A X Y := by
      rw [← pairsYX_eq_iPairsY hθ hXm]
      exact hP
    exact this.1
  intro hsol
  have hP1 : Group.IsSolvable ↥P.1 :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hP.2)
  obtain ⟨n, hn⟩ := hP1.solvable
  exact Thm33a.not_isSolvableSection_of_mem_iPairs hP' ⟨n, (le_of_eq hn).trans bot_le⟩

omit hb in
theorem kOf_ne_bot_of_not_isSolvable {X : Subgroup G} (hX : ¬ Group.IsSolvable X) :
    kOf X ≠ ⊥ := by
  refine Thm52Aux.kOf_ne_bot fun hbot => hX ?_
  rw [hbot]
  infer_instance

theorem thetaM_bot_eq_kOf
    {X : Subgroup G} (hX : X ∈ cset p A θ ⊥) :
    thetaM p A θ ⊥ X = kOf X := by
  have hθ := hb.nearFunctor
  obtain ⟨hP, hMX⟩ := thetaM_bot_pair hb hX
  have hns := not_isSolvable_of_mem_cset hθ hX
  have hXm : X ∈ mtil p A θ := hX.1
  have hKM : kOf X ≤ thetaM p A θ ⊥ X := kOf_le_thetaM hθ hb.bot_mem hX
  have hAX : Admits A X := hXm.1.1
  have hKn : IsNormalIn (kOf X) (thetaM p A θ ⊥ X ⊔ dsub A θ ⊔ A) := by
    refine ⟨hKM.trans (le_sup_left.trans le_sup_left), sup_le (sup_le ?_ ?_) ?_⟩
    · exact hMX.trans (Thm41Aux.le_normalizer_kOf X)
    · exact hXm.2.trans (Thm41Aux.le_normalizer_kOf X)
    · exact Thm41Aux.admits_kOf hAX
  exact ((hP.2.2.1.2.2.2 (kOf X) hKn bot_le hKM).resolve_left
    (kOf_ne_bot_of_not_isSolvable hns)).symm

theorem isChiefFactorOf_kOf
    {X : Subgroup G} (hX : X ∈ cset p A θ ⊥) :
    IsChiefFactorOf (kOf X ⊔ dsub A θ ⊔ A) (kOf X) ⊥ := by
  have := (thetaM_bot_pair hb hX).1.2.2.1
  rw [thetaM_bot_eq_kOf hb hX] at this
  exact this

theorem secCenIn_kOf
    {X : Subgroup G} (hX : X ∈ cset p A θ ⊥) :
    secCenIn (kOf X ⊔ dsub A θ) (kOf X) ⊥ = ⊥ := by
  have := (thetaM_bot_pair hb hX).1.2.2.2
  rw [thetaM_bot_eq_kOf hb hX] at this
  exact this

theorem not_isSolvable_kOf
    {X : Subgroup G} (hX : X ∈ cset p A θ ⊥) :
    ¬ Group.IsSolvable (kOf X) := by
  have hθ := hb.nearFunctor
  have hP := thetaM_thetaL_mem_pairsYX hθ hb.bot_mem hX
  have hiP : (thetaM p A θ ⊥ X, thetaL p A θ ⊥ X) ∈ iPairs A X := by
    have : (thetaM p A θ ⊥ X, thetaL p A θ ⊥ X) ∈ iPairsY A X ⊥ := by
      rw [← pairsYX_eq_iPairsY hθ hX.1]
      exact hP
    exact this.1
  rw [thetaL_bot_eq_bot hb hX, thetaM_bot_eq_kOf hb hX] at hiP
  intro hsol
  obtain ⟨n, hn⟩ := hsol.solvable
  exact Thm33a.not_isSolvableSection_of_mem_iPairs hiP ⟨n, (le_of_eq hn).trans bot_le⟩

theorem sol_eq_bot_of_mem_cset
    {X : Subgroup G} (hX : X ∈ cset p A θ ⊥) : sol X = ⊥ := by
  have hXm : X ∈ mtil p A θ := hX.1
  have hch := isChiefFactorOf_kOf hb hX
  have hAX : Admits A X := hXm.1.1
  have hsn : IsNormalIn (sol X) (kOf X ⊔ dsub A θ ⊔ A) := by
    refine ⟨(sol_le_kOf X).trans (le_sup_left.trans le_sup_left), sup_le (sup_le ?_ ?_) ?_⟩
    · exact (kOf_le X).trans (Thm41Aux.le_normalizer_sol X)
    · exact hXm.2.trans (Thm41Aux.le_normalizer_sol X)
    · exact fun a ha => Thm41Aux.mem_normalizer_sol_of_mem_normalizer (hAX ha)
  rcases hch.2.2.2 (sol X) hsn bot_le (sol_le_kOf X) with h0 | h1
  · exact h0
  · exact absurd (h1 ▸ isSolvable_sol X) (not_isSolvable_kOf hb hX)

theorem dsub_inf_centralizer_kOf
    {X : Subgroup G} (hX : X ∈ cset p A θ ⊥) :
    dsub A θ ⊓ Subgroup.centralizer (kOf X : Set G) = ⊥ := by
  have hsec := secCenIn_kOf hb hX
  rw [eq_bot_iff]
  rintro d ⟨hdD, hdC⟩
  have : d ∈ secCenIn (kOf X ⊔ dsub A θ) (kOf X) ⊥ := by
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_right hdD, ?_⟩
    refine ⟨?_, Thm41Aux.le_normalizer_kOf X (hX.1.2 hdD), fun y hy => ?_⟩
    · exact (Subgroup.normalizer_eq_top_iff.mpr (inferInstance : (⊥ : Subgroup G).Normal)) ▸
        Subgroup.mem_top d
    · have := Subgroup.mem_centralizer_iff.mp hdC y hy
      rw [commutatorElement_eq_one_iff_mul_comm.mpr this.symm]
      exact one_mem _
  rw [hsec] at this
  exact this

theorem exists_conj_eq_of_mem_lcal
    {X : Subgroup G} (hX : X ∈ cset p A θ ⊥) {J J' : Subgroup G}
    (hJ : J ∈ lcal X) (hJ' : J' ∈ lcal X) :
    ∃ g ∈ dsub A θ ⊔ A, J' = J.map (MulAut.conj g).toMonoidHom := by
  classical
  have hsol := sol_eq_bot_of_mem_cset hb hX
  have hdp := isDirectProduct_lcal_kOf hsol
  have hch := isChiefFactorOf_kOf hb hX
  have hXm : X ∈ mtil p A θ := hX.1
  have hDAX : dsub A θ ⊔ A ≤ Subgroup.normalizer (X : Set G) :=
    sup_le (hXm.2.trans Subgroup.le_normalizer) hXm.1.1
  have hDAN : dsub A θ ⊔ A ≤ Subgroup.normalizer (kOf X : Set G) :=
    sup_le (hXm.2.trans (Thm41Aux.le_normalizer_kOf X)) (Thm41Aux.admits_kOf hXm.1.1)
  set O : Set (Subgroup G) :=
    {J'' | ∃ g ∈ dsub A θ ⊔ A, J'' = J.map (MulAut.conj g).toMonoidHom} with hO
  have hOsub : O ⊆ lcal X := by
    rintro _ ⟨g, hg, rfl⟩
    exact map_conj_mem_lcal hJ (hDAX hg)
  have hJO : J ∈ O := ⟨1, one_mem _, by ext y; simp⟩
  have hJne : ∀ J'' ∈ lcal X, J'' ≠ ⊥ := by
    intro J'' hJ'' hbot
    obtain ⟨-, -, -, hnc⟩ := mem_lcal_iff.mp hJ''
    rw [hbot] at hnc
    exact hnc inferInstance
  set N : Subgroup G := sSup O with hN
  have hNK : N ≤ kOf X := sSup_le fun J'' hJ'' => hdp.le (hOsub hJ'')
  have hKN : kOf X ≤ Subgroup.normalizer (N : Set G) := by
    have : Admits (kOf X) N := by
      rw [hN, sSup_eq_iSup']
      exact Admits.iSup fun J'' => hdp.le_normalizer (hOsub J''.2)
    exact this
  have hconj : ∀ g ∈ dsub A θ ⊔ A, ∀ x ∈ N, g * x * g⁻¹ ∈ N := by
    intro g hg
    have : N ≤ N.comap (MulAut.conj g).toMonoidHom := by
      refine sSup_le fun J'' hJ'' y hy => ?_
      obtain ⟨g₀, hg₀, rfl⟩ := hJ''
      have hmem : (MulAut.conj g).toMonoidHom y ∈
          (J.map (MulAut.conj g₀).toMonoidHom).map (MulAut.conj g).toMonoidHom := ⟨y, hy, rfl⟩
      rw [Subgroup.map_map] at hmem
      have hO' : (J.map ((MulAut.conj g).toMonoidHom.comp (MulAut.conj g₀).toMonoidHom)) ∈ O := by
        refine ⟨g * g₀, mul_mem hg hg₀, ?_⟩
        ext z
        simp [mul_assoc]
      exact le_sSup hO' hmem
    intro x hx
    exact this hx
  have hDAN' : dsub A θ ⊔ A ≤ Subgroup.normalizer (N : Set G) := fun g hg =>
    Subgroup.mem_normalizer_iff.mpr fun x =>
      ⟨hconj g hg x, fun hx => by
        have := hconj g⁻¹ (inv_mem hg) _ hx
        have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
        rwa [e] at this⟩
  have hNn : IsNormalIn N (kOf X ⊔ dsub A θ ⊔ A) :=
    ⟨hNK.trans (le_sup_left.trans le_sup_left), sup_le (sup_le hKN
      (le_sup_left.trans hDAN')) (le_sup_right.trans hDAN')⟩
  have hNK' : N = kOf X := by
    refine (hch.2.2.2 N hNn bot_le hNK).resolve_left fun hbot => hJne J hJ ?_
    exact le_bot_iff.mp (hbot ▸ le_sSup hJO)
  have hJ'N : J' ≤ N := hNK' ▸ hdp.le hJ'
  by_contra hcon
  push Not at hcon
  have hJ'O : J' ∉ O := fun hmem => by
    obtain ⟨g, hg, hg'⟩ := hmem
    exact hcon g hg hg'
  have hle : N ≤ sSup (lcal X \ {J'}) := by
    refine sSup_le_sSup fun J'' hJ'' => ⟨hOsub hJ'', fun hh => hJ'O ?_⟩
    rw [Set.mem_singleton_iff] at hh
    rwa [← hh]
  have hdisj := disjoint_iff.mp (hdp.indep hJ')
  have : J' ≤ J' ⊓ sSup (lcal X \ {J'}) := le_inf le_rfl (hJ'N.trans hle)
  rw [hdisj] at this
  exact hJne J' hJ' (le_bot_iff.mp this)

end Bot

end Thm53B

end CFSG.SignalizerFunctorTheorem.McBride.Near
